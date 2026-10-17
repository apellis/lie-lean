# Errata

Errata and proof clarifications arising during the formalization. Codes: **M** misprint; **F→T** false
as printed, with a corrected statement proved; **G** gap in the proof of a true statement. Notes not
established as errata are labelled separately. These entries are not a complete review of the texts.

## [Lus] G. Lusztig, *Introduction to Quantum Groups*

1. **Proof of 40.1.1(e) [M].** In the computation of `T'_{j,−1}(x(i,j;2))`, the term printed as `− E_i x'(i,j;1)`
   should be `+ E_i x'(i,j;1)`; the conclusion of the proof is unaffected (`PBW/RankTwoInfinite.lean`,
   `alternatingWord_prod_E_mem_adjoin_of_four_le`).

## [HK] J. Hong, S.-J. Kang, *Introduction to Quantum Groups and Crystal Bases*, GSM 42

1. **Proof of Prop. 5.3.9, via Lemmas 5.3.7–5.3.8: false auxiliary identification, local repair.**
   The bounded-depth identification asserted on p. 102 and used for the uniform denominator bound
   on p. 107 is required to commute with the ordinary operators `eᵢ`, `fᵢ`; compatibility with the
   Kashiwara operators is then inferred. The ordinary-action assertion is false already for
   `𝔰𝔩₂`: on a highest vector of `V(m)`, `e f v_m = [m] v_m`, so an identification of the highest
   lines commuting with both operators would force `[m] = [n]` for distinct large `m`, `n`.
   This does not refute compatibility of the truncated Kashiwara actions: in rank one their
   divided-power arrows agree on common top string segments whenever the arrows stay inside
   those segments. The earlier claim here that the rank-one `ẽ`-actions differ was incorrect.

   The defect is in this auxiliary justification, not in the conclusion of Prop. 5.3.9 (p. 109).
   Fix the depth and the target weight, and take the finite set consisting of that weight and
   the fundamental weights, as already introduced on p. 107. A maximum of finitely many
   denominator bounds supplies the initial exponent. The two tensor steps of Lemma 5.3.8
   (pp. 108–109) can be run on this finite set: the first improves the bound at the intermediate
   sums, and the second brings the improvement back to each selected weight, including the
   fundamental weights. No old bound on the intermediate sums is needed. Descending on the
   exponent gives `A(r)` for the arbitrary target weight, without an identification of distinct
   highest-weight modules. This is a local repair of the induction, implemented in
   `CrystalBasis/GrandLoop/PropA.lean` (`GrandLoop.eT_smul_mem_LL`, `GrandLoop.step₁`,
   `GrandLoop.step₂`, `GrandLoop.propA_add_two`); it does not disprove the numbered results.
2. **Lemma 5.3.15 and Exercise 5.13: proof clarification, not a confirmed erratum.** The proof
   on pp. 112–113 explicitly delegates its dual-lattice comparison to Exercise 5.13 (p. 117).
   Part (a) asks for a projection-image equality with the first highest weight sufficiently
   large; part (b) asks for a dual-membership equivalence with the second sufficiently large,
   using (a). An omitted exercise solution does not by itself establish a proof gap. No false
   assertion or circular argument has been established here. Reconstruction of the requested
   implication from (a) to (b), including the change of large factor using only inputs available
   at that induction stage, remains partial.

   The library supplies an independent stable-lattice argument in the finite-index,
   generic-parameter, discrete-valuation-ring setting. For `λ` large, the lattices
   `Λ_λ = {y ∈ U⁻_ν | y v_λ ∈ L(λ)}` stabilize (`GrandLoop.exists_stLat_eq`), as do their duals
   for the Shapovalov forms (`GrandLoop.exists_dual_stLat_eq`, using
   `VermaModule.exists_shapZ_sub_mem`). This gives the bounded-depth projection inclusion
   (`GrandLoop.tensorProj_tmul_hwv_mem`) and Lemma 5.3.15 (`GrandLoop.tensorProj_mem_lat_of_large`;
   `CrystalBasis/GrandLoop/{Stable,Dual,Purity,Projection}.lean`). The library reverses the book's
   tensor order and uses an inverse-parameter uniformizer; its large first factor corresponds
   to the book's large second factor. This independent proof does not certify the requested
   exercise derivation, nor does it make the exercise an erratum.

## [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*, Duke Math. J. 63 (1991)

1. **Proof of Prop. 7.4.1 [M].** The reduction to the case `n + ⟨hᵢ, λ − ν⟩ ≥ 0`, i.e. the
   equality `(fᵢⁿV(λ))^ℤ_{λ−ν} = (fᵢ^{n+1}V(λ))^ℤ_{λ−ν}` when `n + ⟨hᵢ, λ − ν⟩ < 0`, is attributed
   to "Proposition 7.1.3"; the result needed is Prop. 6.1.3. The argument is otherwise unchanged
   (`CrystalBasis/Global/StringFiltration.lean`, `hwFilt_le_succ`, using `mem_hwIntegral_wt_iff`
   for Prop. 6.1.3).
