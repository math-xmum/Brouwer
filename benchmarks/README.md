# BrouwerBench

This directory contains a small benchmark dataset for the Lean formalization pipeline:

```text
Scarf -> Brouwer -> Product Brouwer -> Nash
```

The current dataset is `data/brouwerbench_v1.jsonl`: 80 hand-checkable questions covering the main proof chain rather than only the Scarf core. The original 36-question pilot dataset and its scored runs are archived under `archive/v0/` for reproducibility.

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
| Scarf | 24 |
| Brouwer | 20 |
| Brouwer_product | 18 |
| Nash | 18 |

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
- `rubric`: per-task 0-2 scoring guidance with `score_0`, `score_1`, `score_2`, and `must_mention`.

## Validation

Before running or reporting results, validate the dataset and prompt context:

```bash
make -C benchmarks validate
```

This checks JSONL parsing, unique ids, rubric keys, source/prelude links, evidence line anchors, declaration-only Lean snippets, and task contexts that do not leak proof routes or Lean proof-body tokens.

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

Run model outputs for the full current dataset:

```bash
make -C benchmarks run MODEL=qwen3:8b
```

This writes raw outputs under `results/`. After creating the matching manual score file under `scores/`, run:

```bash
make -C benchmarks score MODEL=qwen3:8b
```

To run and score in one command once the score file already exists:

```bash
make -C benchmarks qwen3
```

You can also run the steps separately:

```bash
python3 benchmarks/scripts/run_ollama_benchmark.py \
  --model qwen3:8b \
  --overwrite

python3 benchmarks/scripts/score_benchmark.py \
  --results benchmarks/results/brouwerbench_v1__qwen3_8b.jsonl
```

Results are written under `benchmarks/results/`.

Older `brouwerbench_v0_*` pilot artifacts are archived under `benchmarks/archive/v0/`. Use the reported v1 runs below for current comparisons.

## Reported v1 Runs

The current v1 comparison uses:

| Model | Raw result | Manual scores | Note |
|---|---|---|---|
| `gpt-oss:20b` | `results/brouwerbench_v1__gpt-oss_20b_np4096.jsonl` | `scores/brouwerbench_v1__gpt-oss_20b_np4096.manual.jsonl` | Uniform full run with `num_predict = 4096`; `product_008` exhausted the thinking budget, so its empty response is retained and scored as a failure. |
| `qwen3:8b` | `results/brouwerbench_v1__qwen3_8b.jsonl` | `scores/brouwerbench_v1__qwen3_8b.manual.jsonl` | Small baseline, default `num_predict = 384`. |
| `gemma3:12b` | `results/brouwerbench_v1__gemma3_12b.jsonl` | `scores/brouwerbench_v1__gemma3_12b.manual.jsonl` | Newer general open-weight control, default `num_predict = 384`. |
| `kimina-prover:7b` | `results/brouwerbench_v1__kimina-prover_7b.jsonl` | `scores/brouwerbench_v1__kimina-prover_7b.manual.jsonl` | Prover-style contrast model. |

The main comparison report is:

```text
results/brouwerbench_v1_model_comparison.md
```

The manual-score sanity review is:

```text
results/brouwerbench_v1_score_review.md
```

## Paper Artifacts

The paper-ready v1 evaluation draft is:

```text
results/brouwerbench_v1_paper_section.md
```

LaTeX tables for v1 are in:

```text
results/brouwerbench_v1_tables.tex
```

## Archived Pilot

The 36-task v0 pilot is retained only for reproducibility:

```text
archive/v0/data/brouwerbench_v0.jsonl
archive/v0/results/
archive/v0/scores/
```
