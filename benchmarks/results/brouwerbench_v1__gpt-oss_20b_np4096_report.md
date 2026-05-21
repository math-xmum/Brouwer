# gpt-oss:20b brouwerbench_v1 Report

## Summary

- Model: `gpt-oss:20b`
- Dataset: `benchmarks/data/brouwerbench_v1.jsonl`
- Raw results: `benchmarks/results/brouwerbench_v1__gpt-oss_20b_np4096.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v1__gpt-oss_20b_np4096.manual.jsonl`
- Tasks: 80
- Score: 122/160 (76.2%)
- Total elapsed: 1448.12s
- Average elapsed per task: 18.10s
- Decode speed: 47.44 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 24 | 40/48 | 83.3% |
| Brouwer | 20 | 25/40 | 62.5% |
| Brouwer_product | 18 | 29/36 | 80.6% |
| Nash | 18 | 28/36 | 77.8% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 7 | 9/14 | 64.3% |
| proof_dependency | 28 | 45/56 | 80.4% |
| parity_argument | 4 | 7/8 | 87.5% |
| theorem_summary | 3 | 6/6 | 100.0% |
| construction_role | 17 | 26/34 | 76.5% |
| analysis_step | 11 | 15/22 | 68.2% |
| endpoint_connection | 10 | 14/20 | 70.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 1/2 | Correctly defines dominance and room/door cardinalities, but does not connect the hierarchy to the parity setup. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Identifies the minimum-image representation, but incorrectly upgrades the needed cardinality bound to equality/injectivity. |
| `scarf_003` | Scarf | definition_role | 1/2 | Distinguishes point and index insertion, but does not explain the door-room incidence-counting role. |
| `scarf_004` | Scarf | definition_role | 2/2 | Explains colorful, nearly colorful, typed missing color, and fixed-type parity bookkeeping. |
| `scarf_005` | Scarf | proof_dependency | 2/2 | Explains the colorful-to-room bridge, the cardinality sandwich, nonempty sigma, and why pick_colorful_point depends on it. |
| `scarf_006` | Scarf | parity_argument | 1/2 | Identifies incidence counting and odd/even ingredients, but does not clearly give both final partitions and the non-colorful-room side. |
| `scarf_007` | Scarf | proof_dependency | 2/2 | Explains the unique fixed-type outside door, singleton filter, and odd cardinality-one contribution. |
| `scarf_008` | Scarf | parity_argument | 2/2 | Correctly explains odd + even = colorful + even, yielding an odd positive colorful-room count. |
| `scarf_009` | Scarf | theorem_summary | 2/2 | Explains colorful Nonempty, use of default from Inhabited I, odd cardinality, and extraction of a colorful cell. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Covers Fcolor, grid-level Scarf, room_seq, and room_point_seq selection. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Mentions a finite image and constant subsequence, but treats it as a single color rather than the fixed color/index set C used later. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Explains outside-C coordinates tend to zero, but does not connect this to the inequalities on C that force the fixed point. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Explains compactness and shrinking diameter, but not the transfer of coordinate inequalities to the limit. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Mentions coordinate inequalities, continuity, and the limit, but does not identify the colored witnesses accurately. |
| `brouwer_006` | Brouwer | theorem_summary | 2/2 | Covers grid Scarf rooms, subsequences, shrinking diameter, continuity, and the final fixed point. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Explains pushing toward uniform and block correction, but does not clearly state positive block sums as the normalization precondition. |
| `product_002` | Brouwer_product | proof_dependency | 2/2 | Explains projection/embedding retraction and how project_embed_id converts the lifted fixed point to a product fixed point. |
| `product_003` | Brouwer_product | theorem_summary | 2/2 | Covers f_lifted, continuity, Brouwer on the big simplex, projection back, and project_embed_id. |
| `nash_001` | Nash | definition_role | 1/2 | Describes finite mixed profiles and expected payoff, but omits the no-profitable-unilateral-deviation condition. |
| `nash_002` | Nash | construction_role | 2/2 | Explains payoff improvement, normalization, continuity for Brouwer, and fixed point to Nash. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Connects product Brouwer and the nash_map fixed point, but omits the pure-to-mixed deviation step via mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 2/2 | Explains internal-door degree two, fiber size two, and evenness of the internal-door contribution. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Explains typed nearly colorful doors, preservation of the same missing type, colorful alternative, and room-side partition. |
| `scarf_012` | Scarf | parity_argument | 2/2 | Connects nearly colorful rooms, exactly two doors, size-two fibers, and even incidence count. |
| `brouwer_007` | Brouwer | construction_role | 1/2 | Identifies TT as the finite grid and the indexed order, but does not explain division by l into the simplex. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Mentions coordinate bounds and diameter control, but misses outside-C vanishing and misstates the size-bound roles. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Explains stabilizing a constant color set and subsequence, but not the outside-C and inside-C coordinate estimates. |
| `brouwer_010` | Brouwer | analysis_step | 2/2 | Explains outside-C zero, inequalities on C, sum-one constraints, coordinate equality, and extensionality. |
| `product_004` | Brouwer_product | construction_role | 2/2 | Explains flat index splitting/combining, inverse properties, and their use in block sums and projection/embedding. |
| `product_005` | Brouwer_product | construction_role | 2/2 | Explains blockWeight scaling, block sums, big-simplex normalization, and recovery by project_embed_id. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Explains normalized division, continuous numerator/denominator, positivity, and Continuous.div. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Explains the positive tPush case, but the zero branch is missing the zero-deficit/blockWeight lower-bound argument. |
| `nash_004` | Nash | proof_dependency | 2/2 | Explains mixed_g_linear as a convex combination of pure deviations and why pure bounds imply mixed bounds. |
| `nash_005` | Nash | construction_role | 1/2 | Mentions equivalences and fixed-point transport, but not the ProductSimplices/Fintype.equivFin interface accurately. |
| `nash_006` | Nash | construction_role | 2/2 | Explains nonnegative g_function, sum at least one, positive denominator, normalized sum one, and nash_map_cert. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions profitable deviation, H1, and contradiction, but misses the fixedness plus positive-coordinate argument that forces denominator one. |
| `scarf_013` | Scarf | proof_dependency | 2/2 | Explains outside doors as empty singleton-color doors and the fixed-type singleton count that gives oddness. |
| `scarf_014` | Scarf | proof_dependency | 2/2 | Explains that two-room incidence becomes a size-two fiber in dbcountingset, making the count even. |
| `scarf_015` | Scarf | proof_dependency | 2/2 | Explains outside doors entering typed nearly colorful counting and adjacent rooms classified as same-type nearly colorful or colorful. |
| `scarf_016` | Scarf | endpoint_connection | 0/2 | Misidentifies typed_colorful_room_odd as a set and does not explain odd cardinality giving a positive/nonempty filter and chosen element. |
| `brouwer_011` | Brouwer | construction_role | 1/2 | Explains stdSimplex.pick and the x_i <= f(x)_i color property, but gives the wrong reason for why the upidx witness exists. |
| `brouwer_012` | Brouwer | proof_dependency | 1/2 | Explains fixed C and subsequence g1, but misses their inside-C inequality and outside-C vanishing roles. |
| `brouwer_013` | Brouwer | analysis_step | 2/2 | Explains y_seq as the colored witness sequence, shrinking-diameter convergence to z, and continuity transfer. |
| `brouwer_014` | Brouwer | analysis_step | 2/2 | Explains outside-C zero, nonnegativity, sum-one mass splitting, and coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 1/2 | Mentions C and outside-C zero, but does not clearly connect both roles to extensional equality. |
| `product_008` | Brouwer_product | proof_dependency | 0/2 | Uniform np4096 run exhausted the thinking budget and produced an empty formal response. |
| `product_009` | Brouwer_product | analysis_step | 1/2 | Explains blockSum division and nonzero denominator, but omits the Continuous.div step. |
| `product_010` | Brouwer_product | construction_role | 2/2 | Explains embedded block sums, deficit zero, push identity, and division by blockWeight to recover y. |
| `product_011` | Brouwer_product | endpoint_connection | 2/2 | Correctly explains using single-simplex Brouwer on f_lifted in BigSimplex, then projecting back with project_embed_id. |
| `nash_008` | Nash | construction_role | 1/2 | Explains max 0 as profitable pure-deviation payoff improvement, but misses the later normalization role. |
| `nash_009` | Nash | analysis_step | 2/2 | Explains positive denominator, nonnegative quotients, sum-one normalization, and nash_map_cert packaging. |
| `nash_010` | Nash | endpoint_connection | 2/2 | Explains mixed_g_linear as weighted-sum pure-deviation payoffs, so pure bounds imply mixed bounds. |
| `nash_011` | Nash | endpoint_connection | 2/2 | Explains H1 sum_g > 1, fixedness giving sigma = sigma/sum_g, self_div_lemma forcing sum_g = 1, and contradiction. |
| `nash_012` | Nash | construction_role | 1/2 | Mentions reindexing, ProductSimplices, phi, and fixed-point transport, but misstates parts of the representation mismatch. |
| `scarf_017` | Scarf | proof_dependency | 2/2 | Correctly maps dominance monotonicity to the idoor subset step and odoor index-superset step. |
| `scarf_018` | Scarf | endpoint_connection | 2/2 | Correctly distinguishes the door-side cell conclusion from the room-side cardinality conclusion in an incidence pair. |
| `scarf_019` | Scarf | construction_role | 2/2 | Explains M_set as the extension-candidate set and m_element maximality as the dominance witness for adjacent rooms. |
| `scarf_020` | Scarf | proof_dependency | 1/2 | Links equal-minimum candidate sets and distinct neighbors, but overstates M_set disjointness as disjoint rooms. |
| `scarf_021` | Scarf | proof_dependency | 1/2 | States the two image-cardinality regimes but stops short of the injective-versus-collision door analysis. |
| `scarf_022` | Scarf | proof_dependency | 2/2 | Correctly explains propagation of the same missing type back to doors for the typed parity count. |
| `scarf_023` | Scarf | parity_argument | 2/2 | Correctly uses the two-door property of a nearly colorful room to explain even non-colorful incidences. |
| `scarf_024` | Scarf | proof_dependency | 2/2 | Correctly explains that idoor_determines_element reduces every inserted neighbor to one of the two m_element rooms. |
| `brouwer_016` | Brouwer | construction_role | 1/2 | Explains total-order tie breaking for Scarf, but omits the TT.Ilt_keyprop coordinate-order bridge. |
| `brouwer_017` | Brouwer | proof_dependency | 1/2 | Identifies a dominance-to-analysis bridge, but misstates size_bound_key as a direct distance bound and omits size_bound_in/out. |
| `brouwer_018` | Brouwer | construction_role | 1/2 | Explains the finite-grid to simplex conversion and analytic use sites, but does not mention rescaling by the grid denominator. |
| `brouwer_019` | Brouwer | analysis_step | 1/2 | Mentions outside-C bounds and growing denominators, but misstates size_bound_out as a distance estimate. |
| `brouwer_020` | Brouwer | analysis_step | 1/2 | Explains shrinking room geometry and representative convergence, but misses the colored-witness transfer role. |
| `product_012` | Brouwer_product | definition_role | 1/2 | Correctly distinguishes global and blockwise index representations, but does not connect that gap to single-simplex Brouwer via embed/project. |
| `product_013` | Brouwer_product | construction_role | 2/2 | Correctly explains tPush in [0,1] as the convex-combination guarantee preserving simplex and block positivity behavior. |
| `product_014` | Brouwer_product | proof_dependency | 2/2 | Correctly identifies the post-push block-mass formula as the positivity bridge before normalization. |
| `product_015` | Brouwer_product | proof_dependency | 2/2 | Correctly connects positive Nat+ block weights to positive pushed block mass and well-defined projection division. |
| `product_016` | Brouwer_product | construction_role | 2/2 | Correctly describes per-block extraction and normalization by blockSum to obtain simplex coordinates. |
| `product_017` | Brouwer_product | proof_dependency | 2/2 | Correctly composes projection, f, and embedding continuity to justify applying single-simplex Brouwer to f_lifted. |
| `product_018` | Brouwer_product | endpoint_connection | 1/2 | States the needed project-after-embed direction, but rewrites the endpoint through an unsupported embed representation of x_big. |
| `nash_013` | Nash | definition_role | 2/2 | Correctly specializes unilateral deviation to mixedS via Function.update and expected payoff mixed_g. |
| `nash_014` | Nash | construction_role | 1/2 | Identifies the mixed payoff package and endpoint interpretation, but incorrectly says the mixed game keeps the original strategy types. |
| `nash_015` | Nash | proof_dependency | 2/2 | Correctly uses cg for numerator continuity, finite-sum denominator continuity, nonzero division, and nash_map_cont. |
| `nash_016` | Nash | proof_dependency | 2/2 | Correctly explains the maximizing pure response as an upper bound for the mixed-deviation weighted average. |
| `nash_017` | Nash | analysis_step | 1/2 | Gets the nonzero coordinate witness, but reverses the payoff direction and misses the zero-improvement self-division step. |
| `nash_018` | Nash | endpoint_connection | 2/2 | Correctly explains conjugation by phi and phi_inv and the pullback of a ProductSimplices fixed point. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
