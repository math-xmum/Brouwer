# qwen3:14b BrouwerBench v0 Report

## Summary

- Model: `qwen3:14b`
- Raw results: `benchmarks/results/brouwerbench_v0__qwen3_14b_cleanctx_rerun_20260519.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v0__qwen3_14b_cleanctx_rerun_20260519.manual.jsonl`
- Tasks: 36
- Score: 44/72 (61.1%)
- Total elapsed: 302.93s
- Average elapsed per task: 8.41s
- Decode speed: 24.35 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 12 | 17/24 | 70.8% |
| Brouwer | 10 | 12/20 | 60.0% |
| Brouwer_product | 7 | 8/14 | 57.1% |
| Nash | 7 | 7/14 | 50.0% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 6/10 | 60.0% |
| proof_dependency | 12 | 17/24 | 70.8% |
| parity_argument | 3 | 3/6 | 50.0% |
| theorem_summary | 3 | 4/6 | 66.7% |
| construction_role | 7 | 9/14 | 64.3% |
| analysis_step | 4 | 4/8 | 50.0% |
| endpoint_connection | 2 | 1/4 | 25.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 2/2 | Correctly explains dominance and the cell/room/door cardinality refinements. |
| `scarf_002` | Scarf | proof_dependency | 2/2 | Correctly connects minimum-image characterization to the later cardinality bound. |
| `scarf_003` | Scarf | definition_role | 1/2 | Correctly distinguishes point insertion and index insertion, but omits door-room incidence counting. |
| `scarf_004` | Scarf | definition_role | 1/2 | Correctly distinguishes image, missing color, and typed missing color, but does not explain the parity-counting role. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Recognizes that room_of_colorful supplies the room/cardinality prerequisite, but misses nonempty and the cardinality sandwich. |
| `scarf_006` | Scarf | parity_argument | 1/2 | Identifies typed door-room incidences and parity lemmas, but omits the non-colorful room side and final odd colorful-room count. |
| `scarf_007` | Scarf | proof_dependency | 2/2 | Correctly explains singleton outside-door contribution and odd cardinality. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Recognizes parity-to-existence at a high level, but misses the exact odd/even incidence equation. |
| `scarf_009` | Scarf | theorem_summary | 1/2 | States colorful existence, but gives the wrong reason for Inhabited I and misses default as the chosen type. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Correctly connects Fcolor, grid levels, Scarf/colorful rooms, room_seq, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Recognizes finite-image subsequence extraction, but treats the stabilized object as a color/grid value rather than the set C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Explains outside-C coordinates tending to zero, but misses the coordinate inequality mechanism for fixedness. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and vanishing diameter, but misses transfer of inequalities from room witnesses to the limit. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | States the limiting coordinate inequality, but omits colored witnesses and the continuity/diameter transfer. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Gives the grid/subsequence/diameter strategy, but does not explicitly identify the Scarf step or continuity transfer. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Explains deficit/tPush/pushTowardsZ generally, but misses positive blockSum as the normalization denominator issue. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Identifies projection after embedding as a retraction, but does not explain the lifted-map fixed-point conversion. |
| `product_003` | Brouwer_product | theorem_summary | 2/2 | Correctly summarizes f_lifted, continuity, Brouwer, projection back, and project_embed_id. |
| `nash_001` | Nash | definition_role | 1/2 | Identifies mixedS as product of simplices, but omits expected payoff and unilateral-deviation condition. |
| `nash_002` | Nash | construction_role | 1/2 | Connects nash_map continuity to Brouwer fixed points, but misses payoff improvement and normalization. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Connects Brouwer.mixedGame to a nash_map fixed point, but misses pure-deviation contradiction and mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 2/2 | Correctly explains two incident rooms, fiber size two, and evenness of the internal-door side. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Correctly explains same-missing-type versus colorful partition for typed incidences. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Mentions a size-two fiber and even contribution, but omits the two nearly-colorful doors mechanism. |
| `brouwer_007` | Brouwer | construction_role | 2/2 | Correctly explains TT finite grids, division by l, and indexed order for Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Recognizes coordinate bounds and convergence use, but misstates size_bound_in/out and misses the outside-C estimate. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Explains stabilizing a constant color set along a subsequence, but misses outside-C and in-C coordinate inequalities. |
| `brouwer_010` | Brouwer | analysis_step | 1/2 | Mentions coordinate and sum constraints, but gives an imprecise outside-C/equality argument and omits extensionality. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Correctly explains flat versus block indexing and inverse maps, but misses the sum-transformation role. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Identifies blockWeight scaling and big-simplex compatibility, but misses sum-one detail and project_embed_id recovery. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly explains division by blockSum, positive denominator, and continuity through push/blockSum composition. |
| `product_007` | Brouwer_product | proof_dependency | 0/2 | Incorrectly says the case split is unnecessary and misses the zero-deficit argument when tPush = 0. |
| `nash_004` | Nash | proof_dependency | 2/2 | Correctly explains mixed_g_linear as weighted pure-deviation expansion for mixed deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Explains transport of fixed points through simplex equivalences, but misses Fintype.equivFin/ProductSimplices specifics. |
| `nash_006` | Nash | construction_role | 1/2 | Mentions g_function, nonnegativity, sum lower bound, and normalization, but does not clearly prove sum-one simplex membership. |
| `nash_007` | Nash | endpoint_connection | 0/2 | Gives an invalid contradiction from 1 < sum_g versus 1 <= sum_g and misses the fixed-point self-division mechanism. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
