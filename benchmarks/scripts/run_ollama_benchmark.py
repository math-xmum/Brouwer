#!/usr/bin/env python3
"""Run BrouwerBench JSONL tasks against a local Ollama model."""

from __future__ import annotations

import argparse
import hashlib
import json
import time
import urllib.error
import urllib.request
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATASET = ROOT / "data" / "brouwerbench_v1.jsonl"
DEFAULT_CONTEXT_DIR = ROOT / "context"
DEFAULT_RESULTS_DIR = ROOT / "results"


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


def write_jsonl_row(path: Path, row: dict) -> None:
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")


def section_prelude_path(context_dir: Path, section: str) -> Path:
    return context_dir / f"{section}.lean-snippet"


def read_section_prelude(context_dir: Path, row: dict) -> tuple[str, Path | None]:
    prelude = row.get("section_prelude")
    if prelude:
        path = Path(prelude)
        if not path.is_absolute():
            path = ROOT.parent / path
    else:
        path = section_prelude_path(context_dir, row["section"])
    if not path.exists():
        return "", None
    return path.read_text(encoding="utf-8").strip(), path


def digest_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def build_prompt(row: dict, section_prelude: str) -> str:
    prelude_block = ""
    if section_prelude:
        prelude_block = (
            "Section-level Lean context with relevant definitions, structures, and abbreviations:\n"
            "```lean\n"
            f"{section_prelude}\n"
            "```\n\n"
        )
    return (
        "You are answering a benchmark question about a Lean 4 formalization.\n"
        "Use only the provided section-level Lean context and task-specific context. "
        "Be concise but specific. Mention Lean names when relevant.\n\n"
        f"Section: {row['section']}\n"
        f"Task type: {row['task_type']}\n\n"
        f"{prelude_block}"
        "Task-specific context:\n"
        f"{row['context']}\n\n"
        "Question:\n"
        f"{row['question']}\n\n"
        "Answer:"
    )


def call_ollama(
    endpoint: str,
    model: str,
    prompt: str,
    temperature: float,
    num_predict: int,
    think: str,
    timeout: int,
) -> tuple[dict, float]:
    payload: dict = {
        "model": model,
        "prompt": prompt,
        "stream": False,
        "options": {
            "temperature": temperature,
            "num_predict": num_predict,
        },
    }
    if think != "omit":
        payload["think"] = think == "true"

    data = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        endpoint.rstrip("/") + "/api/generate",
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    start = time.perf_counter()
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            body = response.read().decode("utf-8")
    except urllib.error.URLError as exc:
        raise RuntimeError(f"Could not reach Ollama at {endpoint}: {exc}") from exc
    elapsed = time.perf_counter() - start
    return json.loads(body), elapsed


def result_path_for(model: str, dataset: Path, results_dir: Path) -> Path:
    safe_model = model.replace("/", "_").replace(":", "_")
    stem = dataset.stem
    return results_dir / f"{stem}__{safe_model}.jsonl"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", default="qwen3:8b", help="Ollama model name.")
    parser.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    parser.add_argument("--context-dir", type=Path, default=DEFAULT_CONTEXT_DIR)
    parser.add_argument(
        "--no-section-prelude",
        action="store_true",
        help="Do not prepend section-level Lean definition/structure snippets.",
    )
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--endpoint", default="http://127.0.0.1:11434")
    parser.add_argument("--limit", type=int, default=None, help="Run only the first N tasks.")
    parser.add_argument(
        "--ids",
        default="",
        help="Comma-separated task ids for a targeted rerun.",
    )
    parser.add_argument("--temperature", type=float, default=0.0)
    parser.add_argument("--num-predict", type=int, default=384)
    parser.add_argument(
        "--think",
        choices=["omit", "true", "false"],
        default="false",
        help="Pass Ollama's think flag when supported. Use omit for older servers.",
    )
    parser.add_argument("--timeout", type=int, default=240)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    rows = read_jsonl(args.dataset)
    if args.ids:
        requested_ids = {task_id.strip() for task_id in args.ids.split(",") if task_id.strip()}
        rows_by_id = {row["id"]: row for row in rows}
        missing_ids = sorted(requested_ids - set(rows_by_id))
        if missing_ids:
            raise SystemExit(f"Unknown task ids: {missing_ids}")
        rows = [row for row in rows if row["id"] in requested_ids]
    if args.limit is not None:
        rows = rows[: args.limit]

    output = args.output or result_path_for(args.model, args.dataset, DEFAULT_RESULTS_DIR)
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists() and args.overwrite:
        output.unlink()
    if output.exists():
        raise SystemExit(f"Output exists: {output}. Use --overwrite or choose --output.")

    print(f"model={args.model}")
    print(f"dataset={args.dataset}")
    print(f"context_dir={args.context_dir if not args.no_section_prelude else 'disabled'}")
    print(f"tasks={len(rows)}")
    print(f"output={output}")

    for index, row in enumerate(rows, start=1):
        if args.no_section_prelude:
            section_prelude, prelude_path = "", None
        else:
            section_prelude, prelude_path = read_section_prelude(args.context_dir, row)
        prompt = build_prompt(row, section_prelude)
        print(f"[{index}/{len(rows)}] {row['id']} {row['section']} ...", flush=True)
        raw, elapsed_s = call_ollama(
            endpoint=args.endpoint,
            model=args.model,
            prompt=prompt,
            temperature=args.temperature,
            num_predict=args.num_predict,
            think=args.think,
            timeout=args.timeout,
        )
        result = {
            "id": row["id"],
            "section": row["section"],
            "task_type": row["task_type"],
            "model": args.model,
            "question": row["question"],
            "gold_answer": row["gold_answer"],
            "response": raw.get("response", ""),
            "thinking": raw.get("thinking", ""),
            "context_prelude_path": str(prelude_path.relative_to(ROOT)) if prelude_path else "",
            "context_prelude_sha256": digest_text(section_prelude) if section_prelude else "",
            "elapsed_s": elapsed_s,
            "ollama": {
                key: raw.get(key)
                for key in [
                    "total_duration",
                    "load_duration",
                    "prompt_eval_count",
                    "prompt_eval_duration",
                    "eval_count",
                    "eval_duration",
                    "done_reason",
                ]
                if key in raw
            },
        }
        write_jsonl_row(output, result)

    print(f"done: {output}")


if __name__ == "__main__":
    main()
