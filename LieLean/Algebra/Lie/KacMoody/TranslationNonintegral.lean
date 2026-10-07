/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationSimple
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralWeylGroupFacet

/-!
# Translation of Verma modules for arbitrary weights

Humphreys, GSM 94, Lemma 7.5 and Theorem 7.6 (Verma part) for arbitrary, not necessarily
integral, weights. Let `λ`, `μ` be antidominant (`⟨λ + ρ, β^∨⟩ ∉ ℤ_{>0}` for all positive roots
`β`, `Matrix.Realization.IsAntidominant`) with `μ - λ` integral, and suppose that every positive
root `β` with `⟨λ + ρ, β^∨⟩ = 0` has `⟨μ + ρ, β^∨⟩ = 0` (for antidominant weights this says
that `μ♮` belongs to the closure of the facet containing `λ♮`, in the notation of Humphreys,
GSM 94, §7.4). Let `ν` be the dominant integral weight in `W (μ - λ)`.

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.weylDot_add_eq_weylDot_of_isAntidominant`
  (Lemma 7.5): if `ν'` is a weight of `L(ν)` and `w·λ + ν'` is linked to `μ` (`= x·μ`,
  `x ∈ W`), then `w·λ + ν' = w·μ`.
* `Matrix.Realization.KacMoodyAlgebra.translation_verma_of_isAntidominant` (Theorem 7.6, Verma
  part): for every `w ∈ W`, the `χ_μ`-block of `M(w·λ) ⊗ L(ν)` is isomorphic to `M(w·μ)`.
* `Matrix.Realization.KacMoodyAlgebra.translation_verma_equiv_of_isAntidominant`,
  `Matrix.Realization.KacMoodyAlgebra.translation_dualVerma_of_isAntidominant` (Theorem 7.6):
  `T_λ^μ M(w·λ) ≅ M(w·μ)` and `T_λ^μ M(w·λ)^∨ ≅ M(w·μ)^∨`.
* `Matrix.Realization.KacMoodyAlgebra.translation_irreducible_of_isAntidominant`
  (Proposition 7.7): `T_λ^μ L(w·λ)` is `0` or isomorphic to `L(w·μ)`.

Hypotheses: finite type, an algebraically closed field of characteristic zero (for the
translation functors), finite-dimensional `𝔥`.

The proofs are those of the integral case (`KacMoody/TranslationFacet.lean`,
`KacMoody/TranslationVerma.lean`), with the root-datum facet exclusion replaced by
`Matrix.Realization.apply_eq_of_add_eq_apply_integralWeylGroup`: the element `w⁻¹ x` lies in the
integral Weyl group of `μ + ρ`, and the norm argument runs over the positive integral roots.
Humphreys states Theorem 7.6 and Proposition 7.7 for `w ∈ W_[λ]`; the proofs here do not use
this restriction, and the statements hold for all `w ∈ W`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.4–7.6.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  {P : Realization A K H} (hA : A.IsFiniteCartan)

namespace IrreducibleModule

include hA

/-- **Facet exclusion for arbitrary weights** (Humphreys, GSM 94, Lemma 7.5). Let `λ`, `μ` be
antidominant with every positive root orthogonal to `λ + ρ` orthogonal to `μ + ρ`, and let
`ν = z (μ - λ)`, `z ∈ W`, be dominant integral. If `ν'` is a weight of `L(ν)` and
`w·λ + ν' = x·μ` for `w, x ∈ W`, then `w·λ + ν' = w·μ`. -/
theorem weylDot_add_eq_weylDot_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    {ν' : Dual K H} (hν' : weightSpace P (IrreducibleModule P ν) ν' ≠ ⊥)
    {w x : P.weylGroup hA.isGeneralizedCartan}
    (h : P.weylDot hA.isGeneralizedCartan w lam + ν' = P.weylDot hA.isGeneralizedCartan x μ) :
    P.weylDot hA.isGeneralizedCartan w lam + ν' = P.weylDot hA.isGeneralizedCartan w μ := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  have hνint : ∀ i, ∃ n : ℤ, ν (P.coroot i) = n := fun i ↦ by
    obtain ⟨n, hn⟩ := hν i; exact ⟨n, by rw [hn, Int.cast_natCast]⟩
  -- `μ - λ = z⁻¹ ν` is integral
  have hab : ∀ j, ∃ n : ℤ, ((μ + P.rho) - (lam + P.rho)) (P.coroot j) = n := by
    intro j
    obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA' (inv_mem hz) hνint
    obtain ⟨n, hn⟩ := hνint j
    have e : (μ + P.rho) - (lam + P.rho) = z⁻¹ ν := by
      rw [add_sub_add_right_eq_sub, ← hzν]
      exact (z.symm_apply_apply _).symm
    refine ⟨n + (A *ᵥ k) j, ?_⟩
    rw [e, hk, LinearMap.add_apply, hn, rootOf_apply_coroot]
    push_cast
    ring
  -- The weight `ν₁ = w⁻¹ ν'` and a dominant conjugate `ν₂ = u' ν₁`.
  set ν₁ := (w⁻¹ : P.weylGroup hA').val ν' with hν₁def
  have hν₁ : weightSpace P (IrreducibleModule P ν) ν₁ ≠ ⊥ :=
    weightSpace_apply_ne_bot hA' hν (w⁻¹).property hν'
  have hν₁int : ∀ i, ∃ n : ℤ, ν₁ (P.coroot i) = n := by
    obtain ⟨k, -, hk⟩ := exists_eq_sub_of_weightSpace_ne_bot hν₁
    intro i
    obtain ⟨n, hn⟩ := hν i
    refine ⟨n - (A *ᵥ k) i, ?_⟩
    rw [hk, LinearMap.sub_apply, hn, rootOf_apply_coroot]
    push_cast
    ring
  obtain ⟨u', hu'⟩ := P.exists_dominantIntegral_weylGroup hA' hν₁int
  have hν₂ : weightSpace P (IrreducibleModule P ν) (u'.val ν₁) ≠ ⊥ :=
    weightSpace_apply_ne_bot hA' hν u'.property hν₁
  obtain ⟨c, hc, hck⟩ := exists_eq_sub_of_weightSpace_ne_bot hν₂
  have hνc : z ((μ + P.rho) - (lam + P.rho)) - u'.val ν₁ = P.rootOf c := by
    rw [add_sub_add_right_eq_sub, hzν, hck]
    abel
  have hu : (u'⁻¹ : P.weylGroup hA').val (u'.val ν₁) = ν₁ := by
    change u'.val.symm (u'.val ν₁) = ν₁
    exact u'.val.symm_apply_apply ν₁
  -- Transport `h` by `w⁻¹`.
  have hwx : x.val (μ + P.rho) = w.val (lam + P.rho) + ν' := by
    have h' := h
    simp only [weylDot] at h'
    rw [sub_add_eq_add_sub, sub_left_inj] at h'
    exact h'.symm
  have hy : (lam + P.rho) + (u'⁻¹ : P.weylGroup hA').val (u'.val ν₁) =
      (w⁻¹ * x : P.weylGroup hA').val (μ + P.rho) := by
    rw [hu, hν₁def]
    change lam + P.rho + w.val.symm ν' = w.val.symm (x.val (μ + P.rho))
    rw [hwx, map_add, LinearEquiv.symm_apply_apply]
  -- `w⁻¹ x` lies in the integral Weyl group of `μ + ρ`
  have hyW : w⁻¹ * x ∈ P.integralWeylGroup hA' (μ + P.rho) := by
    rw [mem_integralWeylGroup, ← hy]
    have h1 : ν₁ - ν ∈ P.rootLattice := by
      obtain ⟨k, -, hk⟩ := exists_eq_sub_of_weightSpace_ne_bot hν₁
      rw [hk, sub_sub_cancel_left]
      exact neg_mem (P.rootOf_mem_rootLattice k)
    have h2 : ν - ((μ + P.rho) - (lam + P.rho)) ∈ P.rootLattice := by
      rw [← hzν, ← add_sub_add_right_eq_sub μ lam P.rho]
      exact P.apply_sub_mem_rootLattice_of_integral hA' hz hab
    have e : lam + P.rho + (u'⁻¹ : P.weylGroup hA').val (u'.val ν₁) - (μ + P.rho) =
        (ν₁ - ν) + (ν - ((μ + P.rho) - (lam + P.rho))) := by
      rw [hu]; abel
    rw [e]
    exact add_mem h1 h2
  have hfix := P.apply_eq_of_add_eq_apply_integralWeylGroup hA hab hlam hμ hfacet
    (z := ⟨z, hz⟩) (u := u'⁻¹) (by rw [add_sub_add_right_eq_sub, hzν]; exact hν) hu' hc hνc hyW hy
  have hxw : x.val (μ + P.rho) = w.val (μ + P.rho) := by
    have := congrArg w.val hfix
    change w.val (w.val.symm (x.val (μ + P.rho))) = _ at this
    rwa [LinearEquiv.apply_symm_apply] at this
  rw [h]
  simp only [weylDot, hxw]

end IrreducibleModule

open VermaModule TwistedDual

variable [IsAlgClosed K] (P)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **Translation of Verma modules for arbitrary weights** (Humphreys, GSM 94, Theorem 7.6,
Verma part). Let `λ`, `μ` be antidominant with every positive root orthogonal to `λ + ρ`
orthogonal to `μ + ρ`, and `ν = z (μ - λ)` dominant integral. Then for every `w ∈ W` the
`χ_μ`-block of `M(w·λ) ⊗ L(ν)` is isomorphic to `M(w·μ)`. -/
theorem translation_verma_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) ⊗[K]
        IrreducibleModule P ν) (centralCharacter P μ)) := by
  classical
  have hA' := hA.isGeneralizedCartan
  set Λ := P.weylDot hA' w lam with hΛdef
  set ν₀ := P.weylDot hA' w μ - Λ with hν₀def
  have : FiniteDimensional K (IrreducibleModule P ν) :=
    IrreducibleModule.finiteDimensional (P := P) hA hν
  have hZ : IsHDiagonalizable P (IrreducibleModule P ν) :=
    (IrreducibleModule.isCategoryO P ν).iSup_weightSpaceOfMap_eq_top
  obtain ⟨N, wt, -, -, -, -, hcount, hFmono, hF0, hFlast, -, hFstep, hret⟩ :=
    exists_centralTensorVermaFiltration P hZ Λ (centralCharacter P μ)
  set C := centralBlock P (VermaModule P Λ ⊗[K] IrreducibleModule P ν) (centralCharacter P μ)
  set F := fun k => N k ⊓ C with hFdef
  have hwμ : Λ + ν₀ = P.weylDot hA' w μ := by rw [hν₀def]; abel
  have hχ₀ : centralCharacter P (Λ + ν₀) = centralCharacter P μ := by
    rw [hwμ]
    exact centralCharacter_weyl P hA' w.property μ
  have hν₀ : ν₀ = (w.val * z⁻¹) ν := by
    rw [LinearEquiv.mul_apply]
    change _ = w.val (z.symm ν)
    rw [← hzν, LinearEquiv.symm_apply_apply, hν₀def, hΛdef]
    simp only [weylDot, map_sub, map_add]
    abel
  have hmult : finrank K (weightSpace P (IrreducibleModule P ν) ν₀) = 1 := by
    have hV := (IrreducibleModule.isIntegrable_iff P hA').mpr hν
    have hr := rank_weightSpace_weylGroup hA' hV (mul_mem w.property (inv_mem hz)) ν
    rw [hν₀]
    unfold Module.finrank
    rw [hr]
    exact IrreducibleModule.finrank_weightSpace_self P ν
  have hone := hret ν₀
  rw [ite_eq_left hχ₀, hmult] at hone
  obtain ⟨hsub, ⟨j₀, hj₀wt, hj₀χ⟩⟩ := Nat.card_eq_one_iff_unique.mp hone
  have hretained (j) (hj : centralCharacter P (Λ + wt j) = centralCharacter P μ) :
      wt j = ν₀ := by
    have hwtj : weightSpace P (IrreducibleModule P ν) (wt j) ≠ ⊥ := by
      intro hbot
      have hc := hcount (wt j)
      rw [hbot, finrank_bot] at hc
      have : Nonempty {j' // wt j' = wt j} := ⟨⟨j, rfl⟩⟩
      exact (Nat.card_pos (α := {j' // wt j' = wt j})).ne' hc
    obtain ⟨x, hx, hxe⟩ := (VermaModule.centralCharacter_eq_iff P hA μ (Λ + wt j)).mp hj.symm
    have h : P.weylDot hA' w lam + wt j = P.weylDot hA' ⟨x, hx⟩ μ := by
      simp only [weylDot]
      rw [hxe, hΛdef]
      simp only [weylDot]
      abel
    have := IrreducibleModule.weylDot_add_eq_weylDot_of_isAntidominant hA hlam hμ hfacet hν hz
      hzν hwtj h
    rw [hν₀def, ← this, hΛdef]
    abel
  have hstep_ne (j) (hj : j ≠ j₀) :
      (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) = ⊥ := by
    apply (hFstep j).2
    intro hχ
    apply hj
    have := hsub.elim ⟨j, hretained j hχ, hχ⟩ ⟨j₀, hj₀wt, hj₀χ⟩
    exact congrArg Subtype.val this
  obtain ⟨h1, h2⟩ := LieSubmodule.eq_bot_and_eq_last_of_single_step F hFmono hF0 j₀ hstep_ne
  obtain ⟨e⟩ := (hFstep j₀).1 hj₀χ
  have h2' : F j₀.succ = C := h2.trans hFlast
  rw [hj₀wt, hwμ] at e
  change VermaModule P _ ≃ₗ⁅K,𝔤⁆ (F j₀.succ).map (LieSubmodule.Quotient.mk' (F j₀.castSucc))
    at e
  rw [h1, h2'] at e
  exact ⟨e.trans (LieSubmodule.mapMkBotEquiv C).symm⟩

include hA in
/-- **Translation functors on Verma modules for arbitrary weights** (Humphreys, GSM 94,
Theorem 7.6, Verma part): with `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))` and the hypotheses of
`translation_verma_of_isAntidominant`, `T_λ^μ M(w·λ) ≅ M(w·μ)` for every `w ∈ W`. -/
theorem translation_verma_equiv_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,KacMoodyAlgebra P⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam) (centralCharacter P μ)
        (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  obtain ⟨e⟩ := translation_verma_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w
  have hχ : centralCharacter P (P.weylDot hA.isGeneralizedCartan w lam) =
      centralCharacter P lam := centralCharacter_weyl P hA.isGeneralizedCartan w.property lam
  have htop : centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
      (centralCharacter P lam) = ⊤ := hχ ▸ centralBlock_verma P _
  exact ⟨e.trans (centralBlockEquiv P (rTensorEquiv P (IrreducibleModule P ν)
    (equivCentralBlockOfEqTop P htop)).symm (centralCharacter P μ))⟩

include hA in
/-- **Translation of dual Verma modules for arbitrary weights** (Humphreys, GSM 94, Theorem 7.6,
dual Verma part): `T_λ^μ M(w·λ)^∨ ≅ M(w·μ)^∨` under the hypotheses of
`translation_verma_of_isAntidominant`. -/
theorem translation_dualVerma_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (restrictedDual P (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ))
      ≃ₗ⁅K,KacMoodyAlgebra P⁆ centralTranslation P (IrreducibleModule P ν)
        (centralCharacter P lam) (centralCharacter P μ)
        (restrictedDual P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)))) := by
  obtain ⟨e⟩ := translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w
  exact ⟨(restrictedDualEquiv P e).symm.trans
    (restrictedDualCentralTranslationEquiv P hA hν (VermaModule.isCategoryO P _) _ _)⟩

include hA in
/-- **Translation of simple modules for arbitrary weights, dichotomy** (Humphreys, GSM 94,
Proposition 7.7): under the hypotheses of `translation_verma_of_isAntidominant`,
`T_λ^μ L(w·λ)` is zero or isomorphic to `L(w·μ)`. The proof is that of
`translation_irreducible`. -/
theorem translation_irreducible_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) ∨
      Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,KacMoodyAlgebra P⁆
        centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
          (centralCharacter P μ)
          (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  set x := P.weylDot hA.isGeneralizedCartan w lam
  obtain ⟨e₁⟩ := translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w
  obtain ⟨e₂⟩ := translation_dualVerma_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w
  let π : VermaModule P x →ₗ⁅K,KacMoodyAlgebra P⁆ IrreducibleModule P x :=
    LieSubmodule.Quotient.mk' (maxSubmodule P x)
  have hπ : Function.Surjective π := LieSubmodule.Quotient.surjective_mk' _
  have hTπ : Function.Surjective (centralTranslationMap P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) π) := centralTranslationMap_surjective P
    (VermaModule.isCategoryO P x) (IrreducibleModule.isCategoryO P ν) _ _ π hπ
  have hTι : Function.Injective (centralTranslationMap P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) (IrreducibleModule.toRestrictedDual P x)) :=
    centralTranslationMap_injective P _ _ _ (IrreducibleModule.toRestrictedDual_injective P x)
  exact subsingleton_or_nonempty_equiv_irreducible P
    ((centralTranslationMap P (IrreducibleModule P ν) (centralCharacter P lam)
      (centralCharacter P μ) π).comp e₁.toLieModuleHom) (hTπ.comp e₁.surjective)
    (e₂.symm.toLieModuleHom.comp (centralTranslationMap P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) (IrreducibleModule.toRestrictedDual P x)))
    (e₂.symm.injective.comp hTι)

end Matrix.Realization.KacMoodyAlgebra
