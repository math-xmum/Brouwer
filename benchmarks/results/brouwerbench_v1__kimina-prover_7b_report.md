# kimina-prover:7b brouwerbench_v1 Report

## Summary

- Model: `kimina-prover:7b`
- Dataset: `benchmarks/data/brouwerbench_v1.jsonl`
- Raw results: `benchmarks/results/brouwerbench_v1__kimina-prover_7b.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v1__kimina-prover_7b.manual.jsonl`
- Tasks: 54
- Score: 38/108 (35.2%)
- Total elapsed: 619.10s
- Average elapsed per task: 11.46s
- Decode speed: 42.08 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 16 | 9/32 | 28.1% |
| Brouwer | 15 | 8/30 | 26.7% |
| Brouwer_product | 11 | 9/22 | 40.9% |
| Nash | 12 | 12/24 | 50.0% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 4/10 | 40.0% |
| proof_dependency | 17 | 13/34 | 38.2% |
| parity_argument | 3 | 1/6 | 16.7% |
| theorem_summary | 3 | 0/6 | 0.0% |
| construction_role | 11 | 10/22 | 45.5% |
| analysis_step | 8 | 6/16 | 37.5% |
| endpoint_connection | 7 | 4/14 | 28.6% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 0/2 | Misstates the dominance quantifier and confuses the cardinality conditions for isCell/isRoom/isDoor. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Mentions minima and the eventual cardinality bound, but misses the image-of-C mechanism and gives an incorrect proof story. |
| `scarf_003` | Scarf | definition_role | 1/2 | Recognizes point insertion versus index insertion, but confuses the constructors and misses incidence counting. |
| `scarf_004` | Scarf | definition_role | 1/2 | Partially distinguishes image/missing/typed variants, but confuses colors with dominance and misses the parity role. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Says room_of_colorful is used before picking a point, but misses the nonempty/cardinality sandwich. |
| `scarf_006` | Scarf | parity_argument | 0/2 | Hallucinates unrelated near-critical/square counts and does not describe dbcountingset incidences. |
| `scarf_007` | Scarf | proof_dependency | 0/2 | Replaces the outside-door singleton count with an unrelated handshaking-style graph argument. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Mentions odd/even reasoning and existence broadly, but misses the exact colorful-room count and nonempty-filter step. |
| `scarf_009` | Scarf | theorem_summary | 0/2 | States the wrong theorem conclusion and does not explain colorful nonemptiness or default/Inhabited I. |
| `brouwer_001` | Brouwer | construction_role | 0/2 | Describes iterating f and compactness rather than Scarf, Fcolor, finite grids, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Mentions a finite-image constant subsequence, but gives an incorrect iteration/cycle story and misses constant C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly says outside-C coordinates tend to zero, but misses the inside-C coordinate inequalities and final equality role. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness/convergent subsequence and vanishing diameter, but misses transfer of colored-point inequalities. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Recognizes finite rooms leading to coordinate inequalities at the limit, but misses colored witnesses and continuity details. |
| `brouwer_006` | Brouwer | theorem_summary | 0/2 | Gives a largely incorrect iterative/cycle proof rather than the grid, Scarf, subsequence, diameter, and continuity strategy. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Partially explains deficit, tPush, pushTowardsZ, and blockSum, but misses positive block sums as the normalization prerequisite. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Identifies projection/embedding as a retraction idea, but confuses directions and omits the lifted-map transfer. |
| `product_003` | Brouwer_product | theorem_summary | 0/2 | Hallucinates a Baire-category proof and misses the actual Brouwer_Product proof structure. |
| `nash_001` | Nash | definition_role | 1/2 | Describes mixed strategies as products of simplices and expected payoff, but omits mixedS details and unilateral deviations. |
| `nash_002` | Nash | construction_role | 1/2 | Mentions payoff-improvement/best-response intuition, normalization, continuity, and fixed point, but incorrectly frames pure equilibrium. |
| `nash_003` | Nash | endpoint_connection | 0/2 | Describes game structures but misses Brouwer.mixedGame, nash_map fixed point, pure deviations, and mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 1/2 | Gets the two-rooms-even intuition, but misses the fiber-over-internal-door packaging and adds unrelated hypergraph claims. |
| `scarf_011` | Scarf | proof_dependency | 0/2 | Hallucinates a pigeonhole/coloring argument and does not state the typed nearly colorful versus colorful partition. |
| `scarf_012` | Scarf | parity_argument | 0/2 | Does not explain two nearly colorful doors or the size-two fiber; gives an unrelated pairing argument. |
| `brouwer_007` | Brouwer | construction_role | 1/2 | Mentions TT finite grids and indexed order, but misses the division-by-l coercion and adds incorrect finite-repetition reasoning. |
| `brouwer_008` | Brouwer | analysis_step | 0/2 | Misstates the size-bound lemmas as finite-search bounds and misses dominance, diameter, and outside-C vanishing. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Mentions stabilizing a constant color pattern/subsequence, but misses outside-C and inside-C coordinate estimates. |
| `brouwer_010` | Brouwer | analysis_step | 0/2 | Gives a generic fixed-point statement and misses outside-C zero, sum one, coordinate inequalities, and extensionality. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat-to-block index translation and inverse functions, but misses the sum-changing/blockSum role. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Mentions blockWeight scaling and block-sum equality, but confuses the formula and misses sum-to-one/project_embed_id recovery. |
| `product_006` | Brouwer_product | proof_dependency | 0/2 | Incorrectly claims projection is not continuous in product topology and misses the Continuous.div denominator argument. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Recognizes the tPush case split and blockWeight positivity, but misses zero deficit and misstates the tPush=0 branch. |
| `nash_004` | Nash | proof_dependency | 1/2 | Explains linearity of expected payoff generally, but does not clearly state the convex weighted sum of pure deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Mentions reindex/map_simplex representation changes, but misses Fintype.equivFin, ProductSimplices, and fixed-point transport. |
| `nash_006` | Nash | construction_role | 1/2 | Mentions g_function, nonnegativity, and one_le_sum_g, but misses normalization to sum one and nash_map_cert. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions H1 and a fixed-point contradiction, but the mechanism is incorrect and omits sum_g=1 from self_div_lemma. |
| `scarf_013` | Scarf | proof_dependency | 2/2 | Correctly identifies outside doors as empty point set with singleton color and uniqueness up to the fixed type. |
| `scarf_014` | Scarf | proof_dependency | 0/2 | Hallucinates an unrelated parity/counting theorem and does not explain fiber_size_internal_door. |
| `scarf_015` | Scarf | proof_dependency | 1/2 | Partially identifies NC_of_outsidedoor and NC_or_C_of_door, but misclassifies the room alternatives and misses colorful partition. |
| `scarf_016` | Scarf | endpoint_connection | 0/2 | Incorrectly claims filters are automatically nonempty and misses odd positive cardinality, choice, and default. |
| `brouwer_011` | Brouwer | construction_role | 0/2 | Explains Fcolor via Brouwer fixed points rather than stdSimplex.pick and the x_i <= f(x)_i coordinate. |
| `brouwer_012` | Brouwer | proof_dependency | 0/2 | Gives an unrelated dense-grid/Borsuk-Ulam story and misses gpkg, fixed C, and g1. |
| `brouwer_013` | Brouwer | analysis_step | 2/2 | Correctly explains y_seq as selecting colored witnesses and using diameter control plus continuity to pass inequalities to the limit. |
| `brouwer_014` | Brouwer | analysis_step | 0/2 | Hallucinates Borsuk-Ulam/origin arguments and misses outside-C zero, nonnegativity, sum one, and coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 0/2 | Misdescribes C as a barrier/attracting region and misses the inside/outside coordinate split. |
| `product_008` | Brouwer_product | proof_dependency | 1/2 | Mentions tPush=0, deficit, blockWeight, and positivity, but the zero-deficit argument is wrong. |
| `product_009` | Brouwer_product | analysis_step | 1/2 | Recognizes a division-by-blockSum denominator issue, but incorrectly claims the denominator is always one. |
| `product_010` | Brouwer_product | construction_role | 1/2 | Mentions blockSum/blockWeight/deficit, but gives an incorrect construction and does not explain recovering y. |
| `product_011` | Brouwer_product | endpoint_connection | 1/2 | Mentions BigSimplex, f_lifted, and projecting back, but omits project_embed_id and has a loose endpoint equation. |
| `nash_008` | Nash | construction_role | 2/2 | Correctly explains the max term as positive payoff improvement from pure deviation and connects it to nash_map normalization. |
| `nash_009` | Nash | analysis_step | 1/2 | Explains denominator positivity and nonnegative normalized coordinates, but omits nash_map_cert and makes a false claim that each term is at least one. |
| `nash_010` | Nash | endpoint_connection | 1/2 | Gives the linearity-of-expectation intuition, but does not clearly formulate mixed_g_linear as a weighted sum of pure-deviation payoffs. |
| `nash_011` | Nash | endpoint_connection | 1/2 | Starts with the right sum_g=1 versus H1 contradiction, but then hallucinates a concrete counterexample and omits fixed-point/self_div details. |
| `nash_012` | Nash | construction_role | 1/2 | Broadly describes transporting to a product of simplices and fixed point, but misses reindexing, phi_inv, and ProductSimplices specifics. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
