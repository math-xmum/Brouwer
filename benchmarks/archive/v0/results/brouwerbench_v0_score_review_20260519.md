# BrouwerBench v0 Score Review

Date: 2026-05-19

## Scope

This review checks the clean-context rerun scores for:

- `qwen3:8b`
- `qwen3:14b`
- `gpt-oss:20b`
- `kimina-prover:7b`

The review is a consistency and second-pass scoring audit by the original evaluator, not an independent inter-rater evaluation.

## Mechanical Checks

All four model runs have:

- 36 raw result rows.
- 36 manual score rows.
- 36 scored result rows.
- Dataset IDs aligned with the benchmark order.
- No raw/manual/scored ID mismatches.
- No manual-score-to-scored-result copy mismatches.

Validation commands passed:

```text
make -C benchmarks validate
git diff --check
```

Current totals:

| Model | Score | Accuracy |
|---|---:|---:|
| `gpt-oss:20b` | 48/72 | 66.7% |
| `qwen3:8b` | 46/72 | 63.9% |
| `qwen3:14b` | 44/72 | 61.1% |
| `kimina-prover:7b` | 25/72 | 34.7% |

## Borderline Items Reviewed

The following items were reviewed because they had large cross-model score differences or looked sensitive to rubric interpretation:

| Item | Decision |
|---|---|
| `scarf_006` | Keep scores. `gpt-oss:20b` earns full credit because it identifies typed door-room incidences, outside/internal parity, and the colorful-room existence role; Qwen answers omit the non-colorful-room side. |
| `scarf_009` | Keep scores. `gpt-oss:20b` explicitly states colorful nonemptiness and the need for an inhabited/default index; Qwen answers give a generic inhabitedness explanation. |
| `product_003` | Keep scores. `qwen3:14b` mentions `f_lifted`, continuity, Brouwer, projection back, and `project_embed_id`; `gpt-oss:20b` truncates before completing the retraction conclusion. |
| `product_005` | Keep scores. `qwen3:8b` and `gpt-oss:20b` both connect block-weight scaling to block sums and `project_embed_id`; `qwen3:14b` omits recovery by projection. |
| `nash_006` | Keep scores. `qwen3:8b` covers nonnegativity, denominator lower bound, normalization, and `nash_map_cert`; `gpt-oss:20b` truncates immediately. |
| `nash_007` | Keep scores. All nonzero answers remain partial because they mention the contradiction shape but miss or confuse the positive-coordinate/self-division mechanism. |

## Review Conclusion

No score changes were made. The current comparison and paper-ready tables are internally consistent. The main residual risk is evaluator subjectivity on boundary cases scored 1 versus 2, especially when a model gives a correct high-level summary but omits one formal mechanism. A true paper submission should add at least one independent scorer or a small adjudicated sample.

