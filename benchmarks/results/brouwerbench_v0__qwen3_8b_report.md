# qwen3:8b BrouwerBench v0 Report

## Summary

- Model: `qwen3:8b`
- Raw results: `results/brouwerbench_v0__qwen3_8b.jsonl`
- Manual scores: `scores/brouwerbench_v0__qwen3_8b.manual.jsonl`
- Tasks: 36
- Score: 42/72 (58.3%)
- Total elapsed: 83.81s
- Average elapsed per task: 2.33s
- Decode speed: 41.08 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 12 | 16/24 | 66.7% |
| Brouwer | 10 | 11/20 | 55.0% |
| Brouwer_product | 7 | 8/14 | 57.1% |
| Nash | 7 | 7/14 | 50.0% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 6/10 | 60.0% |
| proof_dependency | 12 | 15/24 | 62.5% |
| parity_argument | 3 | 4/6 | 66.7% |
| theorem_summary | 3 | 3/6 | 50.0% |
| construction_role | 7 | 7/14 | 50.0% |
| analysis_step | 4 | 5/8 | 62.5% |
| endpoint_connection | 2 | 2/4 | 50.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 2/2 | Correctly explains dominance and the cell/room/door cardinality refinements. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Gets the cardinality role but states the image characterization imprecisely. |
| `scarf_003` | Scarf | definition_role | 1/2 | Correctly distinguishes idoor/odoor but does not explain incidence counting. |
| `scarf_004` | Scarf | definition_role | 1/2 | Definitions are right, but the fixed-type parity-counting role is underexplained. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Mentions colorful implies room, but misses the nonempty/cardinality-sandwich reason for choosing a point. |
| `scarf_006` | Scarf | parity_argument | 2/2 | Accurately explains typed door-room incidence and the odd/even partition. |
| `scarf_007` | Scarf | proof_dependency | 1/2 | Mentions cardinality one and oddness, but omits the fixed type and singleton outside-door construction. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Identifies parity as the key but does not spell out the odd + even = colorful + even equation. |
| `scarf_009` | Scarf | theorem_summary | 1/2 | States nonempty colorful room, but the reason for Inhabited I/default index is imprecise. |
| `brouwer_001` | Brouwer | construction_role | 1/2 | Captures colorful rooms by level, but misses the Fcolor coordinate choice and misattributes point picking. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Correct about finite-image constant subsequence, but does not explain the stabilized color set C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly notes coordinates outside C vanish, but misses how this combines with inequalities to force equality. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and diameter, but the transfer-of-inequalities role is too vague. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Mentions the coordinate inequality and continuity, but misses the colored witness and vanishing-diameter transfer mechanism. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Too terse; mentions the limit point but misses Scarf, grids, subsequences, and shrinking rooms. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Understands pushing toward uniformity, but misses positivity of block sums and division/normalization. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Gets projection after embedding, but does not fully explain converting the lifted fixed point back. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Mentions lifted map and continuity, but incorrectly describes where the fixed point lives/projection direction. |
| `nash_001` | Nash | definition_role | 1/2 | Explains mixed profiles and expected payoff, but misses no-profitable-deviation equilibrium condition. |
| `nash_002` | Nash | construction_role | 1/2 | Explains normalization and continuity generally, but misses payoff-improvement and Brouwer fixed-point role. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Correct high-level connection, but misses pure-deviation contradiction and mixed_g_linear extension. |
| `scarf_010` | Scarf | proof_dependency | 2/2 | Correctly identifies internal doors as having exactly two incident rooms, giving fiber size two and evenness. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Correctly explains the same-missing-type versus colorful dichotomy for typed door-room incidences. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Gets the two-element fiber and evenness, but does not explicitly explain the two nearly-colorful doors mechanism. |
| `brouwer_007` | Brouwer | construction_role | 1/2 | Explains the finite grid and simplex normalization, but misses the indexed orders needed to apply Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Mentions coordinate bounds and diameter shrinkage, but misses the rescaling and outside-C vanishing mechanism. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Correct about extracting a constant color-set subsequence, but does not connect it to outside-C and in-C limiting estimates. |
| `brouwer_010` | Brouwer | analysis_step | 2/2 | Names the outside-C zero, on-C inequality, sum, and extensionality steps well enough to recover the final equality argument. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat versus block indexing, but misses inverse lemmas and sum/retraction uses. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Identifies blockWeight scaling and zero deficit, but misses the full sum-one and projection-recovery argument. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly explains normalized division, denominator continuity, and positivity/nonzero denominator for continuity. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Understands the case split, but misses the zero-deficit argument when tPush is zero. |
| `nash_004` | Nash | proof_dependency | 1/2 | Mentions linearity and comparison with pure deviations, but phrases the pure-to-mixed Nash step imprecisely. |
| `nash_005` | Nash | construction_role | 1/2 | Gets the purpose of transporting to product simplices, but omits the Fin-indexed interface and pullback details. |
| `nash_006` | Nash | construction_role | 1/2 | States that nash_map_cert gives a simplex point, but misses nonnegativity, denominator positivity, and sum-one details. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Identifies the sum_g = 1 versus sum_g > 1 contradiction, but omits the fixedness and positive-coordinate mechanism. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
