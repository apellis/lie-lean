# Errata

Errata to the source texts found during the formalization. Codes: **M** misprint; **F→T** false as printed,
with a corrected statement proved; **G** gap in the proof of a true statement. These are what the formalization
turned up; they are not a complete review of the texts.

## [Lus] G. Lusztig, *Introduction to Quantum Groups*

1. **Proof of 40.1.1(e) [M].** In the computation of `T'_{j,−1}(x(i,j;2))`, the term printed as `− E_i x'(i,j;1)`
   should be `+ E_i x'(i,j;1)`; the conclusion of the proof is unaffected (`PBW/RankTwoInfinite.lean`,
   `alternatingWord_prod_E_mem_adjoin_of_four_le`).
