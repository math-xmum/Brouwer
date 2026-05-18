# BrouwerBench v0

This directory contains a small benchmark dataset for the Lean formalization pipeline:

```text
Scarf -> Brouwer -> Product Brouwer -> Nash
```

The first dataset is `data/brouwerbench_v0.jsonl`. It is intentionally small and hand-checkable: 36 questions covering the main proof chain rather than only the Scarf core.

This is a context-provided proof-structure QA benchmark, not a Lean proof-synthesis benchmark. Each model prompt includes:

- a section-level Lean prelude from `context/` with the relevant `def`, `abbrev`, `structure`, `class`, and `inductive` declarations;
- a task-specific excerpt in the JSONL row;
- a natural-language question about the role of the named Lean objects in the formalized proof.

The current preludes are:

| Section | Prelude |
|---|---|
| Scarf | `context/Scarf.lean-snippet` |
| Brouwer | `context/Brouwer.lean-snippet` |
| Brouwer_product | `context/Brouwer_product.lean-snippet` |
| Nash | `context/Nash.lean-snippet` |

The `.lean-snippet` files are intentionally not standalone Lean modules. They are prompt context excerpts, so the Lean language server should not try to compile them.

Current section coverage:

| Section | Tasks |
|---|---:|
| Scarf | 12 |
| Brouwer | 10 |
| Brouwer_product | 7 |
| Nash | 7 |

## Schema

Each JSONL row has:

- `id`: stable task id.
- `section`: one of `Scarf`, `Brouwer`, `Brouwer_product`, or `Nash`.
- `task_type`: question category.
- `source`: source file.
- `section_prelude`: Lean-style snippet file prepended to the prompt.
- `context`: excerpt or compact statement shown to the model.
- `question`: prompt to answer.
- `gold_answer`: reference answer.
- `evidence`: file-line anchors used to create/check the item.
- `rubric`: lightweight 0-2 scoring guidance.

## Scoring

Use the rubric in each row:

```text
0 = incorrect, hallucinated, or only generic
1 = partially correct but misses a key proof role
2 = correct and explains the role in the formalized pipeline
```

## Suggested Model Run

Recommended first pass:

```text
qwen3:8b
```

For Qwen3, the runner defaults to `--think false` when measuring latency and short-answer quality. Use `--think true` when you explicitly want to evaluate reasoning traces.

## Run Locally

Make sure Ollama is running and the model is available:

```bash
ollama list
```

Run a quick smoke test:

```bash
python3 benchmarks/scripts/run_ollama_benchmark.py \
  --model qwen3:8b \
  --limit 2 \
  --overwrite
```

By default, the runner prepends the section prelude. Use `--no-section-prelude` only for ablations that intentionally omit the Lean definitions and structures.

Run the full v0 dataset:

```bash
make -C benchmarks qwen3
```

This runs the model, merges the manual scores in `scores/`, and writes a Markdown report under `results/`.

You can also run the steps separately:

```bash
python3 benchmarks/scripts/run_ollama_benchmark.py \
  --model qwen3:8b \
  --overwrite

python3 benchmarks/scripts/score_benchmark.py \
  --results benchmarks/results/brouwerbench_v0__qwen3_8b.jsonl
```

Results are written under `benchmarks/results/`.

The current scored `qwen3:8b` run contains 36 tasks and scores `44/72` (`61.1%`).

## Paper Artifacts

After scoring, the paper-ready pilot evaluation draft is:

```text
results/brouwerbench_v0_paper_section.md
```

LaTeX tables are in:

```text
results/brouwerbench_v0_tables.tex
```
