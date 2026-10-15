# Four small original analytic leaf candidates

- `OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg`: 3 original proof ASTs / 12 lines; no missing data and no unProved theorem boundary.
- `OAI.PiExponent.LiteralAnalytic.actualRowCount_pos`: 7 original proof ASTs / 53 lines; no missing data and no unProved theorem boundary.
- `OAI.PiExponent.LiteralAnalytic.sum_rowWeight_eq`: 9 original proof ASTs / 66 lines; no missing data and no unProved theorem boundary.
- `OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le`: 16 original proof ASTs / 138 lines; no missing data and no unProved theorem boundary.

Start with indexWeight_nonneg (3 ASTs / 12 lines), then actualRowCount_pos (7 / 53). Sum-row-weight can reuse a future certified public actual-row-count theorem to shorten its proof closure. Card-choice needs 16 / 138 and has two exact existing product API adaptations, on card_choiceFamily_le and RowTranslation.card_bounded_indices_le. All original and port commands, scopes, hashes and source commit are recorded.

These are source-only candidates. The candidate comparator preamble is not asserted equal to a published wire. Final standalone nodes wait for actual graph publication/readback, then require real bounded compilation and source/generated kernel type/ref/Std3 certification.
