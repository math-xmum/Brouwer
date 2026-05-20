# gpt-oss:20b BrouwerBench v0 Report

## Summary

- Model: `gpt-oss:20b`
- Raw results: `benchmarks/results/brouwerbench_v0__gpt_oss_20b_cleanctx_rerun_20260519.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v0__gpt_oss_20b_cleanctx_rerun_20260519.manual.jsonl`
- Tasks: 36
- Score: 48/72 (66.7%)
- Total elapsed: 485.17s
- Average elapsed per task: 13.48s
- Decode speed: 52.54 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 12 | 19/24 | 79.2% |
| Brouwer | 10 | 12/20 | 60.0% |
| Brouwer_product | 7 | 10/14 | 71.4% |
| Nash | 7 | 7/14 | 50.0% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 7/10 | 70.0% |
| proof_dependency | 12 | 17/24 | 70.8% |
| parity_argument | 3 | 4/6 | 66.7% |
| theorem_summary | 3 | 3/6 | 50.0% |
| construction_role | 7 | 10/14 | 71.4% |
| analysis_step | 4 | 5/8 | 62.5% |
| endpoint_connection | 2 | 2/4 | 50.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 2/2 | Accurately explains dominance and the cell/room/door cardinality refinements. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Mentions minimum, image, and cardinality bound, but incorrectly overstates the image as a bijection/cardinality equality. |
| `scarf_003` | Scarf | definition_role | 1/2 | Correctly distinguishes point insertion and index insertion, but does not explain incidence counting. |
| `scarf_004` | Scarf | definition_role | 2/2 | Correctly distinguishes colorful, nearly colorful, and typed missing-color versions and connects typing to counting. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Identifies room_of_colorful as a prerequisite for pick_colorful_point, but gives an imprecise cardinality/nonempty explanation. |
| `scarf_006` | Scarf | parity_argument | 2/2 | Correctly explains typed door-room incidence and the odd/even partition supporting existence. |
| `scarf_007` | Scarf | proof_dependency | 2/2 | Correctly explains the singleton outside-door filter and odd cardinality. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Gets parity-to-existence, but misstates part of the parity equation and does not cleanly identify the outside/internal split. |
| `scarf_009` | Scarf | theorem_summary | 2/2 | Correctly states colorful Nonempty and explains Inhabited I/default as the selected missing type. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Correctly connects Fcolor, grid levels, Scarf, room_seq, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Recognizes finite-image subsequence extraction, but treats the stabilized object as a single color rather than the room color set C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Explains outside-C coordinates tending to zero, but does not state how this combines with coordinate inequalities. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and shrinking diameter, but misses the transfer-of-inequalities role. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Mentions limit, continuity, and coordinate inequality, but omits colored witnesses and overgeneralizes the inequality. |
| `brouwer_006` | Brouwer | theorem_summary | 0/2 | Output is truncated almost immediately and does not answer the proof-strategy question. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Explains deficit/tPush/pushTowardsZ broadly, but misses that the key purpose is positive blockSum for normalization and overstates exact block correction. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Explains projection-after-embedding as a retraction, but does not spell out the lifted map fixed-point conversion. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Starts a correct f_lifted/Brouwer/project-back summary, but truncates before the project_embed_id conclusion. |
| `nash_001` | Nash | definition_role | 1/2 | Explains finite mixed-game representation and expected payoff, but omits the unilateral-deviation Nash condition. |
| `nash_002` | Nash | construction_role | 1/2 | Explains normalization, continuity, and fixed point, but misses the payoff-improvement role of g_function. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Connects Brouwer.mixedGame, nash_map, and mixed_g_linear at a high level, but misses the pure-deviation contradiction. |
| `scarf_010` | Scarf | proof_dependency | 2/2 | Correctly explains internal doors having two incident rooms, fiber size two, and evenness. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Correctly explains the typed nearly colorful versus colorful partition with the same missing type. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Begins the two-doors explanation for nearly colorful rooms, but truncates before the fiber/evenness argument. |
| `brouwer_007` | Brouwer | construction_role | 2/2 | Correctly explains TT finite grids, division by l, and the indexed order for Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Recognizes quantitative bounds and diameter control, but misstates the lemmas and misses the outside-C role. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Explains stabilizing a constant color set, but omits outside-C vanishing and in-C coordinate inequalities. |
| `brouwer_010` | Brouwer | analysis_step | 2/2 | Correctly explains outside-C zero, sum-one forcing, coordinate inequality, and extensionality. |
| `product_004` | Brouwer_product | construction_role | 2/2 | Correctly explains flat/block indexing, inverse lemmas, and sum/projection/embedding uses. |
| `product_005` | Brouwer_product | construction_role | 2/2 | Correctly explains blockWeight scaling, sum-to-one, and project_embed_id recovery. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly explains division by blockSum, continuity of numerator/denominator, positive denominator, and Continuous.div. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Identifies the tPush case split and blockWeight formula, but truncates before the zero-deficit argument. |
| `nash_004` | Nash | proof_dependency | 2/2 | Correctly explains mixed_g_linear as the convex-combination bridge from pure to mixed deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Explains transport of fixed points between representations, but misses Fintype.equivFin/ProductSimplices specifics. |
| `nash_006` | Nash | construction_role | 0/2 | Output truncates immediately and does not explain g_function nonnegativity, sum bound, or normalization. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions profitable-deviation sum_g > 1, fixed point, and contradiction, but the fixed-point contradiction mechanism is confused. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
