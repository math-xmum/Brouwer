# kimina-prover:7b BrouwerBench v0 Report

## Summary

- Model: `kimina-prover:7b`
- Raw results: `benchmarks/results/brouwerbench_v0__kimina_prover_7b_cleanctx_rerun_20260519.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v0__kimina_prover_7b_cleanctx_rerun_20260519.manual.jsonl`
- Tasks: 36
- Score: 25/72 (34.7%)
- Total elapsed: 697.00s
- Average elapsed per task: 19.36s
- Decode speed: 43.39 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 12 | 7/24 | 29.2% |
| Brouwer | 10 | 6/20 | 30.0% |
| Brouwer_product | 7 | 5/14 | 35.7% |
| Nash | 7 | 7/14 | 50.0% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 4/10 | 40.0% |
| proof_dependency | 12 | 10/24 | 41.7% |
| parity_argument | 3 | 2/6 | 33.3% |
| theorem_summary | 3 | 0/6 | 0.0% |
| construction_role | 7 | 6/14 | 42.9% |
| analysis_step | 4 | 2/8 | 25.0% |
| endpoint_connection | 2 | 1/4 | 25.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 0/2 | Majorly swaps the cell/room/door cardinality conditions and repeats incorrect definitions. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Mentions minima and a cardinality bound, but misses the image characterization and gives a flawed explanation. |
| `scarf_003` | Scarf | definition_role | 1/2 | Partly identifies point insertion and color insertion, but garbles names and omits incidence counting. |
| `scarf_004` | Scarf | definition_role | 1/2 | Partly describes image/missing/typed missing color, but contains errors and misses the parity-fiber role. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Says room_of_colorful comes before picking a point, but misses nonempty and the cardinality argument. |
| `scarf_006` | Scarf | parity_argument | 0/2 | Hallucinates unrelated near-critical/square counting and does not describe dbcountingset correctly. |
| `scarf_007` | Scarf | proof_dependency | 0/2 | Replaces the singleton outside-door argument with an unrelated graph handshaking argument. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Understands that odd parity implies existence, but misses the exact colorful-room count equation. |
| `scarf_009` | Scarf | theorem_summary | 0/2 | States the theorem incorrectly and misses colorful Nonempty, default, and Inhabited I. |
| `brouwer_001` | Brouwer | construction_role | 0/2 | Gives an iterative f-orbit proof instead of the Scarf/Fcolor/grid/room_point_seq construction. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Recognizes finite constant-subsequence extraction, but applies it to the wrong iterative sequence rather than constant C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Mentions outside-C coordinates tending to zero, but misses coordinate inequalities and overstates the role. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and vanishing diameter, but not the transfer-inequality role. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Mentions colorful rooms, limits, continuity, and coordinate inequality, but remains generic and omits colored witnesses. |
| `brouwer_006` | Brouwer | theorem_summary | 0/2 | Describes a different contradiction/cycle strategy and misses the actual Scarf-subsequence-diameter proof. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Partly explains deficit/tPush/pushTowardsZ and blockSum, but does not clearly state positive normalization. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Explains projection/embedding as a retraction, but misses the lifted map and projected fixed-point argument. |
| `product_003` | Brouwer_product | theorem_summary | 0/2 | Hallucinates a Baire category proof instead of the Brouwer_Product construction. |
| `nash_001` | Nash | definition_role | 1/2 | Mentions product simplices and expected payoff, but misses mixedS/unilateral-deviation formal details. |
| `nash_002` | Nash | construction_role | 1/2 | Mentions payoff improvement, normalization, continuity, and fixed point, but incorrectly frames it as best-response/pure equilibrium. |
| `nash_003` | Nash | endpoint_connection | 0/2 | Mostly restates game definitions and does not connect Brouwer.mixedGame, nash_map fixed point, pure deviations, or mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 1/2 | States two incident rooms and evenness, but gives an unrelated hypergraph account and omits fiber size. |
| `scarf_011` | Scarf | proof_dependency | 0/2 | Hallucinates a pigeonhole/color argument and misses the typed nearly colorful versus colorful partition. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Recognizes evenness for non-colorful typed nearly colorful rooms, but gives the wrong mechanism and misses the two-door fiber. |
| `brouwer_007` | Brouwer | construction_role | 1/2 | Mentions TT, finite grid, and TT.ILO, but misses division by l and drifts into generic fixed-point discussion. |
| `brouwer_008` | Brouwer | analysis_step | 0/2 | Mischaracterizes size bounds as exhaustive finite search and misses dominance/diameter/outside-C roles. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Recognizes the need for a constant color pattern subsequence, but misses outside-C and in-C coordinate inequalities. |
| `brouwer_010` | Brouwer | analysis_step | 0/2 | Gives a generic Brouwer explanation and misses the actual coordinate/sum/extensionality argument. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat-to-block indexing and inverse functions, but omits sum transformations. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Mentions blockWeight as card/total_card, but confuses it with pushTowardsZ and misses sum-one/project recovery. |
| `product_006` | Brouwer_product | proof_dependency | 0/2 | Incorrectly claims the projection is not continuous in the product topology and misses Continuous.div/positive denominator. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Identifies the tPush case split and blockWeight formula, but the tPush = 0 reason is wrong and zero deficit is missing. |
| `nash_004` | Nash | proof_dependency | 2/2 | Correctly explains mixed_g_linear as linear expected payoff for mixed deviations as weighted pure outcomes. |
| `nash_005` | Nash | construction_role | 1/2 | Mentions reindex/map_simplex-style transport, but misses Fintype.equivFin/ProductSimplices/fixed-point pullback. |
| `nash_006` | Nash | construction_role | 1/2 | Mentions g_function nonnegativity and sum at least one, but does not clearly explain normalization to sum exactly one. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions H1 sum_g > 1, fixed point, and contradiction, but the actual positive-coordinate/self-division mechanism is confused. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
