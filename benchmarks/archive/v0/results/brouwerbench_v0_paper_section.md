## Pilot Evaluation: BrouwerBench v0

To probe whether local language models can follow the proof structure of our formalization, we built a pilot benchmark, BrouwerBench v0, from the Lean development. The benchmark contains 36 hand-written question-answer tasks anchored to Lean definitions and theorem statements. The tasks cover the full pipeline of the development rather than only its combinatorial core: 12 tasks for Scarf's theorem, 10 tasks for the Brouwer fixed-point theorem on the simplex, 7 tasks for the product-of-simplices lift, and 7 tasks for the Nash equilibrium endpoint.

Each item consists of section-level Lean context, a task-specific Lean-grounded excerpt, a natural-language question, a gold answer, source evidence, and a 0-2 point scoring rubric. The section-level context is a compact prelude containing the relevant `def`, `abbrev`, `structure`, `class`, and `inductive` declarations for the corresponding part of the development. Thus, the benchmark does not ask the model to guess missing definitions or synthesize Lean proofs from an empty environment; it evaluates whether the model can explain the proof role of Lean objects when the relevant formal context is provided. We use the following rubric: 0 for incorrect, hallucinated, or generic answers; 1 for partially correct answers that miss a key proof mechanism; and 2 for answers that correctly explain both the Lean object and its role in the formalized proof pipeline.

We evaluated four local models through Ollama on an Apple M4 Pro MacBook Pro with 24GB memory. We used deterministic decoding (`temperature = 0`, `think = false`). The Qwen models were run with `num_predict = 384`; `gpt-oss:20b` and `kimina-prover:7b` were run with `num_predict = 768` because preliminary runs showed more frequent truncation. The benchmark measures proof-structure understanding, not proof synthesis: the models only answer natural-language questions about the formalization, and responses are scored manually against the rubric.

| Model | Score | Accuracy | Runtime | Notes |
|---|---:|---:|---:|---|
| `gpt-oss:20b` | 48/72 | 66.7% | 485.17s | strongest score; 8/36 outputs hit length limit |
| `qwen3:8b` | 46/72 | 63.9% | 194.18s | best baseline; fast and stable |
| `qwen3:14b` | 44/72 | 61.1% | 302.93s | same-family scaling ablation; stable but not better than 8B |
| `kimina-prover:7b` | 25/72 | 34.7% | 697.00s | prover-style contrast; 31/36 outputs hit length limit |

The strongest model by score is `gpt-oss:20b`, but its advantage over the much smaller `qwen3:8b` is modest. `qwen3:8b` is therefore the most practical baseline: it is substantially faster while remaining close in score. The `qwen3:14b` ablation is informative because it does not improve over `qwen3:8b`; it gains on Scarf-local questions but loses on Product and Nash mechanisms. This suggests that simply scaling within the same model family does not automatically improve proof-structure QA under the current prompt format. Finally, `kimina-prover:7b` performs poorly despite its theorem-prover orientation, mostly because it often produces long, generic, or hallucinated proof-script-style answers rather than concise explanations of the provided Lean objects.

| Model | Scarf | Brouwer | Product Brouwer | Nash |
|---|---:|---:|---:|---:|
| `gpt-oss:20b` | 19/24 | 12/20 | 10/14 | 7/14 |
| `qwen3:8b` | 15/24 | 13/20 | 9/14 | 9/14 |
| `qwen3:14b` | 17/24 | 12/20 | 8/14 | 7/14 |
| `kimina-prover:7b` | 7/24 | 6/20 | 5/14 | 7/14 |

The models perform best on local definition and construction questions, where the prompt names the relevant Lean objects. They struggle more with proof-specific mechanisms. In the Scarf portion, failures often omit the exact fiber mechanisms in the parity count. In the Brouwer portion, models recognize compactness, limits, and coordinate bounds, but often miss how grid rescaling, the stabilized color set, and vanishing room diameter transfer finite-grid inequalities to the limit point. In the product and Nash endpoints, models give plausible high-level summaries but often fail to explain inverse-indexing lemmas, the zero-deficit case in the projection construction, or the final fixed-point contradiction that rules out profitable pure deviations.

These results suggest that recent local models can recover much of the surface structure of a Lean formalization, but they still struggle with the precise proof mechanisms that make the formalized pipeline work. BrouwerBench v0 is therefore useful as a pilot diagnostic: it distinguishes general mathematical summarization from proof-aware understanding of a Lean development.

### Limitations and Next Steps

BrouwerBench v0 is intentionally small and should be treated as a pilot study. The current dataset has 36 natural-language QA tasks and manual scores from a single evaluator. A stronger benchmark would add more items, include inter-rater scoring, and introduce proof-repair tasks whose success can be checked by Lean. In the next version, we plan to expand the dataset to 50-80 tasks and add tasks that require exact Lean object names, local dependency tracing, and small proof-gap repairs.
