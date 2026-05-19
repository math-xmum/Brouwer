# BrouwerBench v1 Model Comparison

Dataset: `benchmarks/data/brouwerbench_v1.jsonl` (54 tasks, 108 max points).

## Overall

| Model | Score | Percent | Avg seconds/task | Notes |
|---|---:|---:|---:|---|
| `gpt-oss:20b np1024` | 81/108 | 75.0% | 16.31 | rerun with `--num-predict 1024`; product_008 patched from single rerun |
| `qwen3:8b` | 69/108 | 63.9% | 4.75 | baseline |
| `gemma3:12b` | 63/108 | 58.3% | 8.50 | newer general open-weight control |
| `kimina-prover:7b` | 38/108 | 35.2% | 11.46 | many responses ended by length but nonempty |

## By Section

| Section | gpt-oss:20b np1024 | qwen3:8b | gemma3:12b | kimina-prover:7b |
|---|---:|---:|---:|---:|
| Scarf | 27/32 (84.4%) | 21/32 (65.6%) | 19/32 (59.4%) | 9/32 (28.1%) |
| Brouwer | 21/30 (70.0%) | 17/30 (56.7%) | 16/30 (53.3%) | 8/30 (26.7%) |
| Brouwer_product | 16/22 (72.7%) | 14/22 (63.6%) | 15/22 (68.2%) | 9/22 (40.9%) |
| Nash | 17/24 (70.8%) | 17/24 (70.8%) | 13/24 (54.2%) | 12/24 (50.0%) |

## By Task Type

| Task type | gpt-oss:20b np1024 | qwen3:8b | gemma3:12b | kimina-prover:7b |
|---|---:|---:|---:|---:|
| definition_role | 7/10 (70.0%) | 5/10 (50.0%) | 3/10 (30.0%) | 4/10 (40.0%) |
| proof_dependency | 27/34 (79.4%) | 26/34 (76.5%) | 24/34 (70.6%) | 13/34 (38.2%) |
| parity_argument | 5/6 (83.3%) | 3/6 (50.0%) | 3/6 (50.0%) | 1/6 (16.7%) |
| theorem_summary | 4/6 (66.7%) | 3/6 (50.0%) | 2/6 (33.3%) | 0/6 (0.0%) |
| construction_role | 19/22 (86.4%) | 16/22 (72.7%) | 14/22 (63.6%) | 10/22 (45.5%) |
| analysis_step | 10/16 (62.5%) | 9/16 (56.2%) | 9/16 (56.2%) | 6/16 (37.5%) |
| endpoint_connection | 9/14 (64.3%) | 7/14 (50.0%) | 8/14 (57.1%) | 4/14 (28.6%) |

## Score Distribution

| Model | 0-point | 1-point | 2-point |
|---|---:|---:|---:|
| `gpt-oss:20b np1024` | 1 | 25 | 28 |
| `qwen3:8b` | 2 | 35 | 17 |
| `gemma3:12b` | 5 | 35 | 14 |
| `kimina-prover:7b` | 19 | 32 | 3 |

## Main Takeaways

- `gpt-oss:20b` is strongest on v1, especially proof-dependency and construction-role questions, but still loses points when it states a formally wrong bridge such as a retraction identity in the wrong direction.
- `qwen3:8b` remains a reasonable small baseline: much faster than GPT and close on local proof-dependency questions, weaker on endpoint connections and theorem summaries.
- `gemma3:12b` is a useful newer general open-weight control. It is stronger than Kimi and competitive on product endpoint questions, but it trails Qwen because it often identifies local names without explaining the formal proof bridge.
- `kimina-prover:7b` is not competitive on this natural-language proof-structure QA setup. It often emits Lean-like or generic theorem-proving text that is unrelated to the provided formalization.
- The most discriminative task types are `endpoint_connection`, `analysis_step`, and `theorem_summary`; local `proof_dependency` questions are easier for all models except Kimi.
