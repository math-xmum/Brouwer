#!/usr/bin/env python3
"""Merge manual scores with model outputs and write a benchmark report."""

from __future__ import annotations

import argparse
import collections
import json
import statistics
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATASET = ROOT / "data" / "brouwerbench_v1.jsonl"
DEFAULT_RESULTS_DIR = ROOT / "results"
DEFAULT_SCORES_DIR = ROOT / "scores"


def read_jsonl(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open("r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise SystemExit(f"Invalid JSON on {path}:{line_no}: {exc}") from exc
    return rows


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(json.dumps(row, ensure_ascii=False) for row in rows) + "\n",
        encoding="utf-8",
    )


def require_unique_ids(rows: list[dict], path: Path) -> None:
    ids = [row.get("id") for row in rows]
    duplicates = sorted({item for item, count in collections.Counter(ids).items() if count > 1})
    if duplicates:
        raise SystemExit(f"Duplicate ids in {path}: {duplicates}")


def default_score_path_for(result_path: Path) -> Path:
    return DEFAULT_SCORES_DIR / f"{result_path.stem}.manual.jsonl"


def default_scored_path_for(result_path: Path) -> Path:
    return result_path.with_name(f"{result_path.stem}_scored.jsonl")


def default_report_path_for(result_path: Path) -> Path:
    return result_path.with_name(f"{result_path.stem}_report.md")


def load_scores(path: Path) -> dict[str, dict]:
    rows = read_jsonl(path)
    require_unique_ids(rows, path)
    scores: dict[str, dict] = {}
    for row in rows:
        task_id = row.get("id")
        score = row.get("score")
        if not isinstance(score, int) or score < 0 or score > 2:
            raise SystemExit(f"Score for {task_id!r} in {path} must be an integer in [0, 2].")
        scores[task_id] = row
    return scores


def merge_rows(dataset_rows: list[dict], result_rows: list[dict], score_rows: dict[str, dict]) -> list[dict]:
    dataset_by_id = {row["id"]: row for row in dataset_rows}
    result_by_id = {row["id"]: row for row in result_rows}

    dataset_ids = set(dataset_by_id)
    result_ids = set(result_by_id)
    score_ids = set(score_rows)
    missing_results = sorted(dataset_ids - result_ids)
    extra_results = sorted(result_ids - dataset_ids)
    missing_scores = sorted(dataset_ids - score_ids)
    extra_scores = sorted(score_ids - dataset_ids)
    if missing_results or extra_results or missing_scores or extra_scores:
        raise SystemExit(
            "ID mismatch:\n"
            f"  missing_results={missing_results}\n"
            f"  extra_results={extra_results}\n"
            f"  missing_scores={missing_scores}\n"
            f"  extra_scores={extra_scores}"
        )

    merged: list[dict] = []
    for dataset_row in dataset_rows:
        task_id = dataset_row["id"]
        result_row = dict(result_by_id[task_id])
        score_row = score_rows[task_id]
        result_row["score"] = score_row["score"]
        result_row["score_note"] = score_row.get("score_note") or score_row.get("note", "")
        result_row["score_max"] = 2
        result_row["rubric"] = dataset_row.get("rubric", {})
        result_row["evidence"] = dataset_row.get("evidence", [])
        merged.append(result_row)
    return merged


def summarize(scored_rows: list[dict]) -> dict:
    total_score = sum(row["score"] for row in scored_rows)
    total_max = sum(row.get("score_max", 2) for row in scored_rows)
    elapsed_s = sum(row.get("elapsed_s", 0.0) for row in scored_rows)
    eval_tokens = sum((row.get("ollama") or {}).get("eval_count") or 0 for row in scored_rows)
    eval_ns = sum((row.get("ollama") or {}).get("eval_duration") or 0 for row in scored_rows)
    by_section: dict[str, list[dict]] = collections.defaultdict(list)
    by_type: dict[str, list[dict]] = collections.defaultdict(list)
    for row in scored_rows:
        by_section[row["section"]].append(row)
        by_type[row["task_type"]].append(row)
    return {
        "tasks": len(scored_rows),
        "score": total_score,
        "score_max": total_max,
        "score_pct": total_score / total_max if total_max else 0,
        "elapsed_s": elapsed_s,
        "avg_elapsed_s": elapsed_s / len(scored_rows) if scored_rows else 0,
        "eval_tokens": eval_tokens,
        "decode_tokens_per_s": eval_tokens / (eval_ns / 1e9) if eval_ns else None,
        "by_section": by_section,
        "by_type": by_type,
    }


def score_table(rows_by_group: dict[str, list[dict]]) -> list[str]:
    lines = ["| Group | Tasks | Score | Percent |", "|---|---:|---:|---:|"]
    for group, rows in rows_by_group.items():
        score = sum(row["score"] for row in rows)
        max_score = sum(row.get("score_max", 2) for row in rows)
        pct = score / max_score if max_score else 0
        lines.append(f"| {group} | {len(rows)} | {score}/{max_score} | {pct:.1%} |")
    return lines


def write_report(path: Path, scored_rows: list[dict], result_path: Path, score_path: Path, dataset_path: Path) -> None:
    summary = summarize(scored_rows)
    model = scored_rows[0].get("model", "unknown") if scored_rows else "unknown"
    dataset_name = dataset_path.stem
    lines: list[str] = []
    lines.append(f"# {model} {dataset_name} Report")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Model: `{model}`")
    lines.append(f"- Dataset: `{dataset_path}`")
    lines.append(f"- Raw results: `{result_path}`")
    lines.append(f"- Manual scores: `{score_path}`")
    lines.append(f"- Tasks: {summary['tasks']}")
    lines.append(f"- Score: {summary['score']}/{summary['score_max']} ({summary['score_pct']:.1%})")
    lines.append(f"- Total elapsed: {summary['elapsed_s']:.2f}s")
    lines.append(f"- Average elapsed per task: {summary['avg_elapsed_s']:.2f}s")
    if summary["decode_tokens_per_s"] is not None:
        lines.append(f"- Decode speed: {summary['decode_tokens_per_s']:.2f} tokens/s")
    lines.append("")
    lines.append("## Scores By Section")
    lines.append("")
    lines.extend(score_table(summary["by_section"]))
    lines.append("")
    lines.append("## Scores By Task Type")
    lines.append("")
    lines.extend(score_table(summary["by_type"]))
    lines.append("")
    lines.append("## Item Scores")
    lines.append("")
    lines.append("| ID | Section | Type | Score | Note |")
    lines.append("|---|---|---|---:|---|")
    for row in scored_rows:
        note = row.get("score_note", "").replace("|", "\\|")
        lines.append(
            f"| `{row['id']}` | {row['section']} | {row['task_type']} | "
            f"{row['score']}/{row.get('score_max', 2)} | {note} |"
        )
    lines.append("")
    lines.append("## Takeaways")
    lines.append("")
    lines.append("- Definition-role questions are usually answered at the right abstraction level.")
    lines.append("- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.")
    lines.append("- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--scores", type=Path, default=None)
    parser.add_argument("--scored-output", type=Path, default=None)
    parser.add_argument("--report-output", type=Path, default=None)
    args = parser.parse_args()

    score_path = args.scores or default_score_path_for(args.results)
    scored_output = args.scored_output or default_scored_path_for(args.results)
    report_output = args.report_output or default_report_path_for(args.results)

    dataset_rows = read_jsonl(args.dataset)
    result_rows = read_jsonl(args.results)
    require_unique_ids(dataset_rows, args.dataset)
    require_unique_ids(result_rows, args.results)
    scores = load_scores(score_path)
    scored_rows = merge_rows(dataset_rows, result_rows, scores)
    write_jsonl(scored_output, scored_rows)
    write_report(report_output, scored_rows, args.results, score_path, args.dataset)

    summary = summarize(scored_rows)
    print(f"wrote {scored_output}")
    print(f"wrote {report_output}")
    print(f"score {summary['score']}/{summary['score_max']} ({summary['score_pct']:.1%})")


if __name__ == "__main__":
    main()
