# BrouwerBench v1 Manual Score Review

Manual scoring used the per-item 0--2 rubrics in `benchmarks/data/brouwerbench_v1.jsonl`. Borderline cases were scored conservatively: answers that named the right theorem but missed the formal bridge received 1, and answers that asserted a wrong formal mechanism received 0 even if the surrounding prose was plausible. The expanded 80-item pass kept the same policy for the appended proof-role questions.

## Sanity Checks

- `gpt-oss:20b`: 122/160 (76.2%); score distribution 0=2, 1=34, 2=44. The uniform `np4096` run leaves `product_008` as an empty response after a thinking-budget exhaustion, so it is scored 0.
- `qwen3:8b`: 101/160 (63.1%); score distribution 0=2, 1=55, 2=23.
- `gemma3:12b`: 89/160 (55.6%); score distribution 0=10, 1=51, 2=19.
- `kimina-prover:7b`: 58/160 (36.2%); score distribution 0=30, 1=42, 2=8.

## Borderline Policy

- 2 points: answer identifies the named Lean objects and explains the proof mechanism requested by the question.
- 1 point: answer is directionally correct but misses a key formal dependency, endpoint bridge, or count/fiber mechanism.
- 0 points: answer is generic, hallucinated, or explains a different theorem/proof route.

## Notable Scoring Decisions

- GPT often gave long answers. Long answers were not rewarded unless the formal mechanism was correct; for example, several GPT answers received 1 despite naming the right objects because they used a retraction identity in the wrong direction or missed zero-deficit reasoning.
- Gemma usually identified local Lean names and definitions, but many answers received 1 because they stopped before the formal bridge: fixed-type parity, zero-deficit positivity, simplex sum forcing equality, or pure-to-mixed Nash deviation transfer.
- Kimi frequently produced Lean-like proof scripts or generic topology/game-theory explanations unrelated to the provided context. These were scored 0 when the requested Lean object role was absent.
- Qwen was comparatively concise. It received many 1s because it identified the right local lemma but did not connect it to the endpoint proof obligation.
