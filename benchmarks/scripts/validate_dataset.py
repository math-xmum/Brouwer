#!/usr/bin/env python3
"""Validate BrouwerBench dataset rows and context snippets."""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path


BENCHMARKS_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = BENCHMARKS_ROOT.parent
DEFAULT_DATASET = BENCHMARKS_ROOT / "data" / "brouwerbench_v1.jsonl"
REQUIRED_FIELDS = {
    "id",
    "section",
    "task_type",
    "source",
    "section_prelude",
    "context",
    "question",
    "gold_answer",
    "evidence",
    "rubric",
}
RUBRIC_KEYS = {"score_0", "score_1", "score_2", "must_mention"}
SECTIONS = {"Scarf", "Brouwer", "Brouwer_product", "Nash"}

CONTEXT_LEAK_PATTERNS = [
    re.compile(pattern, re.IGNORECASE)
    for pattern in [
        r"\bproofs?\b",
        r"\bproves?\b",
        r"\buses?\b",
        r"\busing\b",
        r"\bderives?\b",
        r"\bobtains?\b",
        r"\bapplies?\b",
        r"\bshows?\b",
        r"\bcombines?\b",
    ]
]
LEAN_BODY_PATTERNS = [
    re.compile(pattern)
    for pattern in [
        r"\bsorry\b",
        r":=\s*by\b",
        r"\bexact\b",
        r"\bconstructor\b",
        r"\brw\b",
        r"\bsimp\b",
        r"\blinarith\b",
        r"\bnlinarith\b",
        r"\bomega\b",
    ]
]
SNIPPET_FORBIDDEN_PATTERNS = [
    re.compile(pattern, re.IGNORECASE)
    for pattern in [
        r"\bsorry\b",
        r":=\s*by\b",
        r"\bproofs?\b",
        r"\bproves?\b",
        r"\buses?\b",
        r"\busing\b",
    ]
]


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


def repo_path(path: str) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return REPO_ROOT / candidate


def require_unique_ids(rows: list[dict], dataset: Path) -> None:
    ids = [row.get("id") for row in rows]
    duplicates = sorted({item for item, count in collections.Counter(ids).items() if count > 1})
    if duplicates:
        raise SystemExit(f"Duplicate ids in {dataset}: {duplicates}")


def validate_evidence(row: dict) -> None:
    evidence = row.get("evidence")
    if not isinstance(evidence, list) or not evidence:
        raise SystemExit(f"{row.get('id')}: evidence must be a nonempty list")

    for anchor in evidence:
        if not isinstance(anchor, str):
            raise SystemExit(f"{row['id']}: evidence anchor must be a string: {anchor!r}")
        match = re.fullmatch(r"(.+):(\d+)", anchor)
        if match is None:
            raise SystemExit(f"{row['id']}: bad evidence anchor format: {anchor!r}")
        path = repo_path(match.group(1))
        if not path.exists():
            raise SystemExit(f"{row['id']}: evidence file does not exist: {anchor!r}")
        line_no = int(match.group(2))
        total_lines = sum(1 for _ in path.open("r", encoding="utf-8"))
        if line_no < 1 or line_no > total_lines:
            raise SystemExit(
                f"{row['id']}: evidence line {line_no} out of range for "
                f"{path.relative_to(REPO_ROOT)} with {total_lines} lines"
            )


def validate_context_text(row: dict) -> None:
    context = row.get("context")
    if not isinstance(context, str) or not context.strip():
        raise SystemExit(f"{row.get('id')}: context must be a nonempty string")

    for pattern in CONTEXT_LEAK_PATTERNS:
        if pattern.search(context):
            raise SystemExit(f"{row['id']}: context leaks proof-route word {pattern.pattern!r}")
    for pattern in LEAN_BODY_PATTERNS:
        if pattern.search(context):
            raise SystemExit(f"{row['id']}: context contains Lean proof-body token {pattern.pattern!r}")


def validate_row(row: dict) -> None:
    missing = sorted(REQUIRED_FIELDS - set(row))
    if missing:
        raise SystemExit(f"{row.get('id', '<missing id>')}: missing fields {missing}")

    if row["section"] not in SECTIONS:
        raise SystemExit(f"{row['id']}: unknown section {row['section']!r}")

    source = repo_path(row["source"])
    if not source.exists():
        raise SystemExit(f"{row['id']}: source does not exist: {row['source']}")

    prelude = repo_path(row["section_prelude"])
    if not prelude.exists():
        raise SystemExit(f"{row['id']}: section_prelude does not exist: {row['section_prelude']}")

    rubric = row.get("rubric")
    if not isinstance(rubric, dict) or set(rubric) != RUBRIC_KEYS:
        raise SystemExit(f"{row['id']}: rubric keys must be exactly {sorted(RUBRIC_KEYS)}")
    if not isinstance(rubric.get("must_mention"), list):
        raise SystemExit(f"{row['id']}: rubric.must_mention must be a list")

    validate_evidence(row)
    validate_context_text(row)


def validate_snippets() -> None:
    missing = [section for section in SECTIONS if not (BENCHMARKS_ROOT / "context" / f"{section}.lean-snippet").exists()]
    if missing:
        raise SystemExit(f"Missing context snippets: {missing}")

    for path in sorted((BENCHMARKS_ROOT / "context").glob("*.lean-snippet")):
        text = path.read_text(encoding="utf-8")
        for pattern in SNIPPET_FORBIDDEN_PATTERNS:
            if pattern.search(text):
                raise SystemExit(
                    f"{path.relative_to(REPO_ROOT)} contains forbidden declaration-context token "
                    f"{pattern.pattern!r}"
                )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    args = parser.parse_args()

    dataset = args.dataset
    if not dataset.is_absolute():
        dataset = (Path.cwd() / dataset).resolve()
    rows = read_jsonl(dataset)
    require_unique_ids(rows, dataset)
    for row in rows:
        validate_row(row)
    validate_snippets()
    print(f"dataset validation ok: {len(rows)} rows")


if __name__ == "__main__":
    main()
