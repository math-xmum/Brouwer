## Evaluation: BrouwerBench v1

We evaluate proof-structure understanding with BrouwerBench v1, an 80-item benchmark derived from the Lean development. The dataset covers the full formalized pipeline from Scarf's theorem to Brouwer's fixed-point theorem, the product-of-simplices lift, and the Nash equilibrium endpoint. The section split is 24 Scarf tasks, 20 Brouwer tasks, 18 product Brouwer tasks, and 18 Nash tasks.

Each item provides section-level Lean context containing the relevant `def`, `abbrev`, `structure`, `class`, and `inductive` declarations, a task-specific Lean-grounded excerpt, a natural-language question, a gold answer, source evidence anchors, and a 0--2 scoring rubric. The benchmark is not proof synthesis: models answer natural-language questions about the role of named Lean objects in the proof pipeline. We score 0 for incorrect, hallucinated, or generic answers, 1 for partially correct answers that miss a key proof mechanism, and 2 for answers that correctly explain both the Lean object and its proof role.

All runs used Ollama on an Apple M4 Pro MacBook Pro with 24GB memory, deterministic decoding (`temperature = 0`), and section preludes enabled. `qwen3:8b`, `gemma3:12b`, and `kimina-prover:7b` used the default `num_predict = 384`. `gpt-oss:20b` used one uniform full run with `num_predict = 4096`; `product_008` still exhausted that thinking budget and its empty response is retained and scored as a failure. Intermediate smoke and failed-default runs are excluded from the reported results.

| Model | Score | Accuracy | Runtime | Avg. / task | Notes |
|---|---:|---:|---:|---:|---|
| `gpt-oss:20b` | 122/160 | 76.2% | 1448.12s | 18.10s | strongest score |
| `qwen3:8b` | 101/160 | 63.1% | 428.07s | 5.35s | fast baseline |
| `gemma3:12b` | 89/160 | 55.6% | 822.82s | 10.29s | newer general control |
| `kimina-prover:7b` | 58/160 | 36.2% | 986.41s | 12.33s | prover-style contrast |

The strongest model is `gpt-oss:20b`, scoring 122/160 (76.2%). `qwen3:8b` is substantially faster and remains a useful small-model baseline at 101/160 (63.1%). `gemma3:12b` scores 89/160 (55.6%): it is stronger than the prover-oriented Kimi run and often recovers product-level proof dependencies, but it misses more definition roles and Nash dependencies than Qwen. `kimina-prover:7b` scores only 58/160 (36.2%); despite its prover orientation, it frequently produces generic proof-script-like text or hallucinated Lean snippets rather than explaining the supplied formalization.

| Model | Scarf | Brouwer | Product Brouwer | Nash |
|---|---:|---:|---:|---:|
| `gpt-oss:20b` | 40/48 | 25/40 | 29/36 | 28/36 |
| `qwen3:8b` | 30/48 | 22/40 | 25/36 | 24/36 |
| `gemma3:12b` | 25/48 | 21/40 | 24/36 | 19/36 |
| `kimina-prover:7b` | 14/48 | 12/40 | 14/36 | 18/36 |

By section, GPT is strongest on Scarf (40/48) and product Brouwer (29/36). Gemma is closest to Qwen on product Brouwer (24/36 versus 25/36), but weaker on Nash and definition-heavy Scarf questions. The product section remains a useful stress test because models can state the high-level reduction while still missing the exact role of denominator positivity, zero deficit, or the projection-embedding identity.

| Model | Def. | Dep. | Parity | Summary | Constr. | Analysis | Endpoint |
|---|---:|---:|---:|---:|---:|---:|---:|
| `gpt-oss:20b` | 9/14 | 45/56 | 7/8 | 6/6 | 26/34 | 15/22 | 14/20 |
| `qwen3:8b` | 8/14 | 38/56 | 5/8 | 4/6 | 23/34 | 13/22 | 10/20 |
| `gemma3:12b` | 5/14 | 34/56 | 5/8 | 4/6 | 20/34 | 11/22 | 10/20 |
| `kimina-prover:7b` | 6/14 | 20/56 | 1/8 | 1/6 | 16/34 | 9/22 | 5/20 |

The most discriminative task types are endpoint-connection, analysis-step, and theorem-summary questions. Local proof-dependency questions are easier: GPT and Qwen both perform well when the question names a local Lean object and asks for its immediate proof role. Endpoint questions require connecting local lemmas to the final theorem, which exposes more hallucination and more formally wrong bridges.

Overall, BrouwerBench v1 separates general mathematical summarization from proof-aware understanding of a Lean development. Recent local models can often recover named local dependencies, but they still struggle with the exact mechanisms that make the formalized pipeline work, such as size-two fibers in Scarf parity, stabilized coordinate sets in Brouwer, denominator positivity in product projection, and the fixed-point contradiction used to rule out profitable Nash deviations.

### Limitations

The benchmark uses manual scores from a single evaluator and natural-language answers rather than Lean-checked proof repairs. The dataset is still modest at 80 items. Future versions should add inter-rater scoring, more endpoint tasks, and proof-repair or proof-gap tasks that can be checked by Lean.
