# BrouwerBench v0 Clean-Context Rerun Comparison

Dataset: `benchmarks/data/brouwerbench_v0.jsonl`

## Summary

| Model | Score | Percent | Runtime | Avg / Task | Completion Notes |
|---|---:|---:|---:|---:|---|
| `qwen3:8b` | 46/72 | 63.9% | 194.18s | 5.39s | 36/36 stopped normally |
| `qwen3:14b` | 44/72 | 61.1% | 302.93s | 8.41s | 36/36 stopped normally |
| `gpt-oss:20b` | 48/72 | 66.7% | 485.17s | 13.48s | 28/36 stopped normally; 8/36 hit length limit at `num_predict=768` |
| `kimina-prover:7b` | 25/72 | 34.7% | 697.00s | 19.36s | 31/36 hit length limit even at `num_predict=768` |

## By Section

| Model | Scarf | Brouwer | Brouwer Product | Nash |
|---|---:|---:|---:|---:|
| `qwen3:8b` | 15/24 | 13/20 | 9/14 | 9/14 |
| `qwen3:14b` | 17/24 | 12/20 | 8/14 | 7/14 |
| `gpt-oss:20b` | 19/24 | 12/20 | 10/14 | 7/14 |
| `kimina-prover:7b` | 7/24 | 6/20 | 5/14 | 7/14 |

## By Task Type

| Model | Definition | Dependency | Parity | Summary | Construction | Analysis | Endpoint |
|---|---:|---:|---:|---:|---:|---:|---:|
| `qwen3:8b` | 5/10 | 18/24 | 3/6 | 3/6 | 11/14 | 4/8 | 2/4 |
| `qwen3:14b` | 6/10 | 17/24 | 3/6 | 4/6 | 9/14 | 4/8 | 1/4 |
| `gpt-oss:20b` | 7/10 | 17/24 | 4/6 | 3/6 | 10/14 | 5/8 | 2/4 |
| `kimina-prover:7b` | 4/10 | 10/24 | 2/6 | 0/6 | 6/14 | 2/8 | 1/4 |

## Readout

`qwen3:8b` remains the best baseline model: it is the fastest reliable model in the run and scores close to `gpt-oss:20b`. It usually identifies the right definitions and construction roles, but often misses the exact mechanism in parity, endpoint, and analytic-limit questions.

`qwen3:14b` is useful as a scaling ablation, but it should not replace `qwen3:8b` as the baseline. It improves on Scarf definitions and summaries, but loses ground on Product and Nash mechanisms. The result suggests that increasing Qwen model size from 8B to 14B does not automatically improve proof-structure QA under this prompt.

`gpt-oss:20b` is the strongest local comparison in this run. It does especially well on Scarf definitions and Product construction questions, but it is slower, still truncates on some long answers, and remains weak on Nash endpoint questions.

`kimina-prover:7b` is not a good short-answer baseline for this dataset in its current prompt configuration. It is much slower, frequently truncated, and often drifts into generic or hallucinated proof scripts rather than answering the local Lean-structure question.

For the paper/project narrative, use `qwen3:8b` as the local baseline, `qwen3:14b` as the same-family scaling ablation, `gpt-oss:20b` as the stronger local comparison model, and `kimina-prover:7b` as a contrast model showing that theorem-prover branding alone does not guarantee better proof-structure QA performance.
