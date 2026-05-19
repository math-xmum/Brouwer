## Evaluation: BrouwerBench v1

We evaluate proof-structure understanding with BrouwerBench v1, a 54-item benchmark derived from the Lean development. The dataset covers the full formalized pipeline from Scarf's theorem to Brouwer's fixed-point theorem, the product-of-simplices lift, and the Nash equilibrium endpoint. The section split is 16 Scarf tasks, 15 Brouwer tasks, 11 product Brouwer tasks, and 12 Nash tasks.

Each item provides section-level Lean context containing the relevant `def`, `abbrev`, `structure`, `class`, and `inductive` declarations, a task-specific Lean-grounded excerpt, a natural-language question, a gold answer, source evidence anchors, and a 0--2 scoring rubric. The benchmark is not proof synthesis: models answer natural-language questions about the role of named Lean objects in the proof pipeline. We score 0 for incorrect, hallucinated, or generic answers, 1 for partially correct answers that miss a key proof mechanism, and 2 for answers that correctly explain both the Lean object and its proof role.

All runs used Ollama on an Apple M4 Pro MacBook Pro with 24GB memory, deterministic decoding (`temperature = 0`), and section preludes enabled. `qwen3:8b` and `kimina-prover:7b` used the default `num_predict = 384`. `gpt-oss:20b` required `num_predict = 1024`: with the default generation length, 19 of 54 formal responses were empty because the model spent the budget in the thinking channel. The reported GPT run is therefore the `np1024` rerun; one remaining empty response (`product_008`) was replaced by a single-item rerun with a 2048-token budget. Intermediate smoke and failed-default runs are excluded from the reported results.

| Model | Score | Accuracy | Runtime | Avg. / task | Notes |
|---|---:|---:|---:|---:|---|
| `gpt-oss:20b` | 81/108 | 75.0% | 880.62s | 16.31s | strongest score |
| `qwen3:8b` | 69/108 | 63.9% | 256.40s | 4.75s | fast baseline |
| `kimina-prover:7b` | 38/108 | 35.2% | 619.10s | 11.46s | prover-style contrast |

The strongest model is `gpt-oss:20b`, scoring 81/108 (75.0%). `qwen3:8b` is substantially faster and remains a useful small-model baseline at 69/108 (63.9%). `kimina-prover:7b` scores only 38/108 (35.2%); despite its prover orientation, it frequently produces generic proof-script-like text or hallucinated Lean snippets rather than explaining the supplied formalization.

| Model | Scarf | Brouwer | Product Brouwer | Nash |
|---|---:|---:|---:|---:|
| `gpt-oss:20b` | 27/32 | 21/30 | 16/22 | 17/24 |
| `qwen3:8b` | 21/32 | 17/30 | 14/22 | 17/24 |
| `kimina-prover:7b` | 9/32 | 8/30 | 9/22 | 12/24 |

By section, GPT is strongest on Scarf (27/32) and Brouwer (21/30), while GPT and Qwen tie on Nash (17/24). The product section remains a useful stress test because models can state the high-level reduction while still missing the exact role of denominator positivity, zero deficit, or the projection-embedding identity.

| Model | Def. | Dep. | Parity | Summary | Constr. | Analysis | Endpoint |
|---|---:|---:|---:|---:|---:|---:|---:|
| `gpt-oss:20b` | 7/10 | 27/34 | 5/6 | 4/6 | 19/22 | 10/16 | 9/14 |
| `qwen3:8b` | 5/10 | 26/34 | 3/6 | 3/6 | 16/22 | 9/16 | 7/14 |
| `kimina-prover:7b` | 4/10 | 13/34 | 1/6 | 0/6 | 10/22 | 6/16 | 4/14 |

The most discriminative task types are endpoint-connection, analysis-step, and theorem-summary questions. Local proof-dependency questions are easier: GPT and Qwen both perform well when the question names a local Lean object and asks for its immediate proof role. Endpoint questions require connecting local lemmas to the final theorem, which exposes more hallucination and more formally wrong bridges.

Overall, BrouwerBench v1 separates general mathematical summarization from proof-aware understanding of a Lean development. Recent local models can often recover named local dependencies, but they still struggle with the exact mechanisms that make the formalized pipeline work, such as size-two fibers in Scarf parity, stabilized coordinate sets in Brouwer, denominator positivity in product projection, and the fixed-point contradiction used to rule out profitable Nash deviations.

### Limitations

The benchmark uses manual scores from a single evaluator and natural-language answers rather than Lean-checked proof repairs. The dataset is still modest at 54 items. Future versions should add inter-rater scoring, more endpoint tasks, and proof-repair or proof-gap tasks that can be checked by Lean.
