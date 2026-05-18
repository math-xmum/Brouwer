## Pilot Evaluation: BrouwerBench v0

To probe whether a small local language model can follow the proof structure of our formalization, we built a pilot benchmark, BrouwerBench v0, from the Lean development. The benchmark contains 36 hand-written question-answer tasks anchored to Lean definitions and theorem statements. The tasks cover the full pipeline of the development rather than only its combinatorial core: 12 tasks for Scarf's theorem, 10 tasks for the Brouwer fixed-point theorem on the simplex, 7 tasks for the product-of-simplices lift, and 7 tasks for the Nash equilibrium endpoint.

Each item consists of section-level Lean context, a task-specific Lean-grounded excerpt, a natural-language question, a gold answer, source evidence, and a 0-2 point scoring rubric. The section-level context is a compact prelude containing the relevant `def`, `abbrev`, `structure`, `class`, and `inductive` declarations for the corresponding part of the development. Thus, the benchmark does not ask the model to guess missing definitions or synthesize Lean proofs from an empty environment; it evaluates whether the model can explain the proof role of Lean objects when the relevant formal context is provided. We use the following rubric: 0 for incorrect, hallucinated, or generic answers; 1 for partially correct answers that miss a key proof mechanism; and 2 for answers that correctly explain both the Lean object and its role in the formalized proof pipeline.

We evaluated `qwen3:8b` locally through Ollama with deterministic decoding (`temperature = 0`, `think = false`, `num_predict = 384`). The model was served on an Apple M4 Pro MacBook Pro with 24GB memory. The benchmark measures proof-structure understanding, not proof synthesis: the model only answers natural-language questions about the formalization, and its responses are scored manually against the rubric.

| Section | Tasks | Score | Accuracy |
|---|---:|---:|---:|
| Scarf | 12 | 16/24 | 66.7% |
| Brouwer | 10 | 12/20 | 60.0% |
| Product Brouwer | 7 | 8/14 | 57.1% |
| Nash | 7 | 8/14 | 57.1% |
| **Total** | **36** | **44/72** | **61.1%** |

The model performs best on Scarf incidence-counting questions and local proof-dependency questions where the prompt names the relevant Lean objects. For example, it can explain that internal doors have two incident rooms and that typed nearly colorful door-room incidences split into typed nearly colorful rooms or colorful rooms. However, it often misses proof-specific mechanisms that are essential in the formalization. In the Scarf portion, failures still tend to omit some exact fiber mechanisms, such as the two nearly colorful doors of a non-colorful room. In the Brouwer portion, the model recognizes compactness, limits, and coordinate bounds but often misses how grid rescaling, the stabilized color set, and vanishing room diameter transfer finite-grid inequalities to the limit point. In the product and Nash endpoints, the model gives correct high-level summaries but often fails to explain inverse-indexing lemmas, the zero-deficit case in the projection construction, or the final fixed-point contradiction that rules out profitable pure deviations.

These results suggest that even a recent 8B local model can recover much of the surface structure of a Lean formalization, but it struggles with the precise proof mechanisms that make the formalized pipeline work. BrouwerBench v0 is therefore useful as a pilot diagnostic: it distinguishes general mathematical summarization from proof-aware understanding of a Lean development.

### Limitations and Next Steps

BrouwerBench v0 is intentionally small and should be treated as a pilot study. The current dataset has 36 natural-language QA tasks and manual scores from a single evaluator. A stronger benchmark would add more items, include inter-rater scoring, and introduce proof-repair tasks whose success can be checked by Lean. In the next version, we plan to expand the dataset to 50-80 tasks and add tasks that require exact Lean object names, local dependency tracing, and small proof-gap repairs.
