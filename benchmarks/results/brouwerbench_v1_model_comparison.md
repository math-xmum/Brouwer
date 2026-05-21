# BrouwerBench v1 Model Comparison

Dataset: `benchmarks/data/brouwerbench_v1.jsonl` (80 tasks, 160 max points).

## Overall

| Model | Score | Percent | Avg seconds/task | Notes |
|---|---:|---:|---:|---|
| `gpt-oss:20b np4096` | 122/160 | 76.2% | 18.10 | uniform longer-budget run; `product_008` empty response scored 0 |
| `qwen3:8b` | 101/160 | 63.1% | 5.35 | baseline |
| `gemma3:12b` | 89/160 | 55.6% | 10.29 | newer general open-weight control |
| `kimina-prover:7b` | 58/160 | 36.2% | 12.33 | prover-style contrast with frequent proof-script drift |

## By Section

| Section | gpt-oss:20b np4096 | qwen3:8b | gemma3:12b | kimina-prover:7b |
|---|---:|---:|---:|---:|
| Scarf | 40/48 (83.3%) | 30/48 (62.5%) | 25/48 (52.1%) | 14/48 (29.2%) |
| Brouwer | 25/40 (62.5%) | 22/40 (55.0%) | 21/40 (52.5%) | 12/40 (30.0%) |
| Brouwer_product | 29/36 (80.6%) | 25/36 (69.4%) | 24/36 (66.7%) | 14/36 (38.9%) |
| Nash | 28/36 (77.8%) | 24/36 (66.7%) | 19/36 (52.8%) | 18/36 (50.0%) |

## By Task Type

| Task type | gpt-oss:20b np4096 | qwen3:8b | gemma3:12b | kimina-prover:7b |
|---|---:|---:|---:|---:|
| definition_role | 9/14 (64.3%) | 8/14 (57.1%) | 5/14 (35.7%) | 6/14 (42.9%) |
| proof_dependency | 45/56 (80.4%) | 38/56 (67.9%) | 34/56 (60.7%) | 20/56 (35.7%) |
| parity_argument | 7/8 (87.5%) | 5/8 (62.5%) | 5/8 (62.5%) | 1/8 (12.5%) |
| theorem_summary | 6/6 (100.0%) | 4/6 (66.7%) | 4/6 (66.7%) | 1/6 (16.7%) |
| construction_role | 26/34 (76.5%) | 23/34 (67.6%) | 20/34 (58.8%) | 16/34 (47.1%) |
| analysis_step | 15/22 (68.2%) | 13/22 (59.1%) | 11/22 (50.0%) | 9/22 (40.9%) |
| endpoint_connection | 14/20 (70.0%) | 10/20 (50.0%) | 10/20 (50.0%) | 5/20 (25.0%) |

## Score Distribution

| Model | 0-point | 1-point | 2-point |
|---|---:|---:|---:|
| `gpt-oss:20b np4096` | 2 | 34 | 44 |
| `qwen3:8b` | 2 | 55 | 23 |
| `gemma3:12b` | 10 | 51 | 19 |
| `kimina-prover:7b` | 30 | 42 | 8 |

## Main Takeaways

- `gpt-oss:20b` is strongest on v1, especially theorem summaries, parity arguments, proof dependencies, and the product reduction, but it still loses points on formally wrong endpoint bridges.
- `qwen3:8b` remains a reasonable small baseline: much faster than GPT and steady across construction and proof-dependency questions, weaker on endpoint connections.
- `gemma3:12b` is a useful newer general open-weight control. It is strongest relative to Qwen on product questions, but it trails the baseline overall because it misses more definition roles and Nash dependencies.
- `kimina-prover:7b` is not competitive on this natural-language proof-structure QA setup. It often emits Lean-like or generic theorem-proving text that is unrelated to the provided formalization.
- The most discriminative task types are `endpoint_connection`, `analysis_step`, and `theorem_summary`; local `proof_dependency` questions are easier for all models except Kimi.
