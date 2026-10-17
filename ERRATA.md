# Errata

Errata to the source texts found during the formalization. Codes: **M** misprint; **F→T** false as printed,
with a corrected statement proved; **G** gap in the proof of a true statement. These are what the formalization
turned up; they are not a complete review of the texts.

## [Lus] G. Lusztig, *Introduction to Quantum Groups*

1. **Proof of 40.1.1(e) [M].** In the computation of `T'_{j,−1}(x(i,j;2))`, the term printed as `− E_i x'(i,j;1)`
   should be `+ E_i x'(i,j;1)`; the conclusion of the proof is unaffected (`PBW/RankTwoInfinite.lean`,
   `alternatingWord_prod_E_mem_adjoin_of_four_le`).

## [HK] J. Hong, S.-J. Kang, *Introduction to Quantum Groups and Crystal Bases*, GSM 42

1. **Proof of Prop. 5.3.9, via Lemmas 5.3.7–5.3.8 [G].** The descending induction on `N` in
   `ẽᵢ L(μ)_{depth r} ⊆ ϖ^{-N} L(μ)` is run for all sufficiently large `μ` at once, with a bound
   on `N` that is uniform in `μ`. The uniformity is justified by identifying `Σ_α V(λ)_{λ−α}`
   with `Σ_α V(μ)_{μ−α}` compatibly with `ẽᵢ`, `f̃ᵢ`.
   No such identification exists: the two `ẽᵢ`-actions differ already for `𝔰𝔩₂`. The statement of
   Prop. 5.3.9 is unaffected. The library runs the induction on a finite set of weights, the
   given weight together with the fundamental weights, which is all that the two steps of
   Lemma 5.3.8 use (`CrystalBasis/GrandLoop/PropA.lean`: `GrandLoop.eT_smul_mem_LL` for 5.3.7,
   `GrandLoop.step₁`, `GrandLoop.step₂` for 5.3.8, `GrandLoop.propA_add_two` for 5.3.9).
2. **Proof of Lemma 5.3.15 [G].** The printed proof relies on Exercise 5.13, whose solution is not
   given in the book. The library proves what the lemma needs: for `λ` large, the lattices
   `Λ_λ = {y ∈ U⁻_ν | y v_λ ∈ L(λ)}` do not depend on `λ` (`GrandLoop.exists_stLat_eq`), and neither
   do their duals for the Shapovalov forms `(x v_λ, y v_λ)` (`GrandLoop.exists_dual_stLat_eq`, via
   the limit of the Shapovalov form, `VermaModule.exists_shapZ_sub_mem`). From these it derives
   `Ψ(L(λ₁) ⊗ v_{λ₂}) ⊆ L(λ₁ + λ₂)` for `λ₁` large (`GrandLoop.tensorProj_tmul_hwv_mem`) and the
   lemma itself (`GrandLoop.tensorProj_mem_lat_of_large`; files
   `CrystalBasis/GrandLoop/{Stable,Dual,Purity,Projection}.lean`).

## [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*, Duke Math. J. 63 (1991)

1. **Proof of Prop. 7.4.1 [M].** The reduction to the case `n + ⟨hᵢ, λ − ν⟩ ≥ 0`, i.e. the
   equality `(fᵢⁿV(λ))^ℤ_{λ−ν} = (fᵢ^{n+1}V(λ))^ℤ_{λ−ν}` when `n + ⟨hᵢ, λ − ν⟩ < 0`, is attributed
   to "Proposition 7.1.3"; the result needed is Prop. 6.1.3. The argument is otherwise unchanged
   (`CrystalBasis/Global/StringFiltration.lean`, `hwFilt_le_succ`, using `mem_hwIntegral_wt_iff`
   for Prop. 6.1.3).
