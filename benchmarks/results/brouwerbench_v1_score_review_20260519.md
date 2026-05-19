# BrouwerBench v1 Score Review

Manual scoring used the per-item 0--2 rubrics in `benchmarks/data/brouwerbench_v1.jsonl`. Borderline cases were scored conservatively: answers that named the right theorem but missed the formal bridge received 1, and answers that asserted a wrong formal mechanism received 0 even if the surrounding prose was plausible.

## Sanity Checks

- `gpt-oss:20b`: 81/108 (75.0%); score distribution 0=1, 1=25, 2=28.
- `qwen3:8b`: 69/108 (63.9%); score distribution 0=2, 1=35, 2=17.
- `kimina-prover:7b`: 38/108 (35.2%); score distribution 0=19, 1=32, 2=3.

## Borderline Policy

- 2 points: answer identifies the named Lean objects and explains the proof mechanism requested by the question.
- 1 point: answer is directionally correct but misses a key formal dependency, endpoint bridge, or count/fiber mechanism.
- 0 points: answer is generic, hallucinated, or explains a different theorem/proof route.

## Notable Scoring Decisions

- GPT often gave long answers. Long answers were not rewarded unless the formal mechanism was correct; for example, several GPT answers received 1 despite naming the right objects because they used a retraction identity in the wrong direction or missed zero-deficit reasoning.
- Kimi frequently produced Lean-like proof scripts or generic topology/game-theory explanations unrelated to the provided context. These were scored 0 when the requested Lean object role was absent.
- Qwen was comparatively concise. It received many 1s because it identified the right local lemma but did not connect it to the endpoint proof obligation.
