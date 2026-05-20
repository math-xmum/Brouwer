# qwen3:8b BrouwerBench v0 Report

## Summary

- Model: `qwen3:8b`
- Raw results: `benchmarks/results/brouwerbench_v0__qwen3_8b_cleanctx_rerun_20260519.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v0__qwen3_8b_cleanctx_rerun_20260519.manual.jsonl`
- Tasks: 36
- Score: 46/72 (63.9%)
- Total elapsed: 194.18s
- Average elapsed per task: 5.39s
- Decode speed: 37.72 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 12 | 15/24 | 62.5% |
| Brouwer | 10 | 13/20 | 65.0% |
| Brouwer_product | 7 | 9/14 | 64.3% |
| Nash | 7 | 9/14 | 64.3% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 5/10 | 50.0% |
| proof_dependency | 12 | 18/24 | 75.0% |
| parity_argument | 3 | 3/6 | 50.0% |
| theorem_summary | 3 | 3/6 | 50.0% |
| construction_role | 7 | 11/14 | 78.6% |
| analysis_step | 4 | 4/8 | 50.0% |
| endpoint_connection | 2 | 2/4 | 50.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 1/2 | Gets the cell/room/door cardinality hierarchy mostly right, but states dominance imprecisely. |
| `scarf_002` | Scarf | proof_dependency | 2/2 | Correctly connects minima, image representation, and the cardinality bound. |
| `scarf_003` | Scarf | definition_role | 1/2 | Distinguishes point insertion and color insertion, but does not explain door-room incidence counting. |
| `scarf_004` | Scarf | definition_role | 1/2 | Explains image, missing color, and typed missing color, but only gestures at the parity role. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Identifies room_of_colorful as a prerequisite for pick_colorful_point, but misses the nonempty/cardinality sandwich. |
| `scarf_006` | Scarf | parity_argument | 1/2 | Recognizes typed door-room incidences and outside/internal parity, but omits the non-colorful room side and final odd colorful count. |
| `scarf_007` | Scarf | proof_dependency | 2/2 | Correctly explains singleton outside-door contribution and odd cardinality. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Identifies parity as the key, but misses the exact odd/even equation and nonempty colorful-room conclusion. |
| `scarf_009` | Scarf | theorem_summary | 1/2 | States colorful existence, but gives an imprecise explanation of Inhabited/default. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Correctly connects Fcolor, finite grids, Scarf, room_seq, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Understands finite-image constant subsequence extraction, but confuses the stabilized object with point/color constancy rather than the set C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Explains outside-C coordinates tending to zero, but misses the final coordinate inequality mechanism. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and shrinking diameter, but misses transfer of inequalities from room witnesses to the limit. |
| `brouwer_005` | Brouwer | proof_dependency | 2/2 | Correctly connects colorful witnesses, continuity, the limit, and coordinate inequalities. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Gives a broad sequence/subsequence/continuity story, but omits Scarf and diameter estimates in the actual strategy. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Explains deficit/tPush/pushTowardsZ as retraction machinery, but misses the positive blockSum denominator needed for normalization. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Identifies projection-after-embedding identity, but does not clearly explain the lifted-map fixed-point conversion. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Mentions f_lifted and continuity, but incorrectly describes the Brouwer step as happening in product space and omits project_embed_id. |
| `nash_001` | Nash | definition_role | 1/2 | Mentions FinGame and expected payoff, but misses mixedS details and unilateral-deviation condition. |
| `nash_002` | Nash | construction_role | 1/2 | Explains normalization, continuity, and fixed point, but misses the payoff-improvement role of g_function. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Correct high-level Brouwer-to-Nash connection, but misses pure-deviation contradiction and mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 1/2 | Explains two incident rooms and evenness, but omits the fiber-size formulation. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Correctly states the same-missing-type versus colorful dichotomy for typed incidences. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Gets two doors and even incidence count, but does not state the fiber argument precisely. |
| `brouwer_007` | Brouwer | construction_role | 2/2 | Correctly explains TT finite grids, division by l, and the indexed order for Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Recognizes coordinate bounds and diameter control, but misstates the roles of size_bound_in/out and misses outside-C rescaling. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Understands stabilization to a constant color set, but misses outside-C estimates and in-C inequalities. |
| `brouwer_010` | Brouwer | analysis_step | 1/2 | Names the final coordinate/sum lemmas, but includes incorrect claims about outside-C zero and strict inequality. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat versus block indexing, but misses inverse lemmas and sum transformations. |
| `product_005` | Brouwer_product | construction_role | 2/2 | Correctly explains blockWeight scaling, sum-to-one/block-sum behavior, and project_embed_id recovery. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly identifies division by blockSum, continuity of numerator/denominator, and positive denominator. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Recognizes the tPush case split, but misses the zero-deficit reason in the tPush = 0 case. |
| `nash_004` | Nash | proof_dependency | 2/2 | Correctly explains mixed_g_linear as weighted pure-deviation expansion for mixed deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Explains transport between representations, but misses Fintype.equivFin/map_simplex/ProductSimplices specifics. |
| `nash_006` | Nash | construction_role | 2/2 | Correctly explains g_function nonnegativity, sum lower bound, normalization, and nash_map_cert. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions the fixed-point contradiction idea, but misses the sum_g > 1 and positive-coordinate mechanism. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
