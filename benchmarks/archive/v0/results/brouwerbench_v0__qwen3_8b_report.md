# qwen3:8b BrouwerBench v0 Report

## Summary

- Model: `qwen3:8b`
- Raw results: `results/brouwerbench_v0__qwen3_8b.jsonl`
- Manual scores: `scores/brouwerbench_v0__qwen3_8b.manual.jsonl`
- Tasks: 36
- Score: 44/72 (61.1%)
- Total elapsed: 159.01s
- Average elapsed per task: 4.42s
- Decode speed: 40.42 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 12 | 16/24 | 66.7% |
| Brouwer | 10 | 12/20 | 60.0% |
| Brouwer_product | 7 | 8/14 | 57.1% |
| Nash | 7 | 8/14 | 57.1% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 5/10 | 50.0% |
| proof_dependency | 12 | 17/24 | 70.8% |
| parity_argument | 3 | 4/6 | 66.7% |
| theorem_summary | 3 | 3/6 | 50.0% |
| construction_role | 7 | 9/14 | 64.3% |
| analysis_step | 4 | 4/8 | 50.0% |
| endpoint_connection | 2 | 2/4 | 50.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 1/2 | Explains cell/room/door cardinalities, but states the dominance quantification imprecisely. |
| `scarf_002` | Scarf | proof_dependency | 2/2 | Correctly connects the mini-image characterization of sigma with later cardinality comparisons. |
| `scarf_003` | Scarf | definition_role | 1/2 | Correctly distinguishes point insertion and index insertion, but does not explain incidence counting. |
| `scarf_004` | Scarf | definition_role | 1/2 | Definitions are right, but the fixed-type parity-counting role is still only generic. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Explains that colorful cells must be rooms before point extraction, but misses the nonempty/cardinality-sandwich argument. |
| `scarf_006` | Scarf | parity_argument | 2/2 | Accurately explains typed door-room incidence and the odd/even partition. |
| `scarf_007` | Scarf | proof_dependency | 1/2 | Mentions cardinality one and oddness, but omits the fixed type and singleton outside-door construction. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Identifies parity as the key but does not spell out the odd + even = colorful + even equation. |
| `scarf_009` | Scarf | theorem_summary | 1/2 | States colorful existence, but gives the wrong reason for needing Inhabited I/default index. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Correctly explains Fcolor, Scarf at each grid level, room_seq, and room_point_seq extraction. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Understands finite-image subsequence extraction, but confuses the stabilized room color set with a constant point color. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly notes coordinates outside C vanish, but misses how this combines with inequalities to force equality. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and vanishing diameter, but misses the transfer-of-inequalities role. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Mentions coordinate inequality and continuity, but misses colored witnesses and vanishing-diameter transfer. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Gets the high-level sequence/subsequence structure but misses diameter estimates and the final sum argument. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Understands pushing toward uniformity and normalization, but misses the explicit positive-block-sum/denominator issue. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Identifies project-embed identity, but overstates it as a bijection and does not explain fixed-point conversion. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Mentions lifted map and continuity, but incorrectly describes where the Brouwer fixed point lives. |
| `nash_001` | Nash | definition_role | 1/2 | Explains FinGame, mixedS, and expected payoff, but does not spell out the no-profitable-deviation condition. |
| `nash_002` | Nash | construction_role | 1/2 | Explains normalization and continuity generally, but misses the payoff-improvement role of g_function. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Correct high-level connection, but misses pure-deviation contradiction and mixed_g_linear extension. |
| `scarf_010` | Scarf | proof_dependency | 2/2 | Correctly identifies internal doors as having exactly two incident rooms, giving fiber size two and evenness. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Correctly explains the same-missing-type versus colorful dichotomy for typed door-room incidences. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Gets the two-element fiber and evenness, but does not explicitly explain the two nearly-colorful doors mechanism. |
| `brouwer_007` | Brouwer | construction_role | 2/2 | Correctly explains TT grids, normalization into the simplex, and TT.ILO as the order structure for Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Mentions coordinate bounds and diameter shrinkage, but misses rescaling and outside-C vanishing details. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Correct about extracting a constant color-set subsequence, but does not connect it to outside-C and in-C limiting estimates. |
| `brouwer_010` | Brouwer | analysis_step | 1/2 | Names the final lemmas and extensionality, but explains the outside-C zero and sum-forcing argument imprecisely. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat versus block indexing, but misses inverse lemmas and sum/retraction uses. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Identifies blockWeight scaling, sum-one, and zero deficit, but misses projection recovery via project_embed_id. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly explains normalized division, denominator continuity, and positivity/nonzero denominator for continuity. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Understands the case split, but misses the zero-deficit argument when tPush is zero. |
| `nash_004` | Nash | proof_dependency | 2/2 | Correctly explains mixed_g_linear as a weighted pure-deviation expansion used to bound mixed deviations by best pure deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Gets transport to Fin-indexed product simplices, but omits the pullback of the fixed point to the original mixed space. |
| `nash_006` | Nash | construction_role | 1/2 | States that nash_map_cert gives a simplex point, but misses nonnegativity, denominator positivity, and sum-one details. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Identifies the sum_g = 1 contradiction, but omits sum_g > 1 from profitable deviation and the fixedness/positive-coordinate mechanism. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
