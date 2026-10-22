/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ShapovalovElement.Basic
import LieLean.Algebra.Lie.KacMoody.VermaHomGeneralFiniteType

/-!
# Uniqueness of Shapovalov elements

For `𝔤` of finite type over an algebraically closed field of characteristic zero, a Shapovalov
element for `(γ, r)` is unique modulo `U(𝔟⁻)(h_γ + ρ(h_γ) - r)` ([HumO] Thm. 4.12, last
assertion). In the encoding of `VermaModule.IsShapovalovElement` (polynomial families
`λ ↦ θ(λ) ∈ U(𝔫⁻)`), this says that `θ - θ'` is `⟨λ + ρ, γ^∨⟩ - r` times a polynomial family
(`VermaModule.IsShapovalovElement.exists_sub_eq_smul`).

The proof follows [HumO] §4.13. On the hyperplane `⟨λ + ρ, γ^∨⟩ = r`, both `θ(λ) v_λ` and
`θ'(λ) v_λ` are maximal vectors of weight `λ - rγ` in `M(λ)`, and `dim Hom(M(λ - rγ), M(λ)) ≤ 1`
([HumO] Thm. 4.2 (b), `VermaModule.finrank_hom_le_one_of_finite_type`), so `θ'(λ) = c θ(λ)`;
comparing leading terms gives `c = 1` (`VermaModule.IsShapovalovElement.eq_of_corootPairing_eq`).
A polynomial family vanishing on a hyperplane is divisible by its equation
(`VermaModule.exists_sub_comp_eq_smul`).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.2, §4.12, §4.13.
-/

open Module Module.Dual LieModule UniversalEnvelopingAlgebra

noncomputable section

namespace Module.Dual

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

/-- `projSubst` is the identity modulo `λ(a) + c`. -/
lemma affPoly_dvd_sub_projSubst (a : H) (c : K) (δ : Dual K H) (F : MvPolynomial (PolyIdx K H) K) :
    affPoly K H a c ∣ F - projSubst K H a c δ F := by
  set I := Ideal.span {affPoly K H a c}
  have hmk : (Ideal.Quotient.mkₐ K I).comp (projSubst K H a c δ) = Ideal.Quotient.mkₐ K I := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    have hφ : Ideal.Quotient.mk I (affPoly K H a c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [AlgHom.comp_apply, projSubst, MvPolynomial.aeval_X, map_sub, map_mul]
    rw [Ideal.Quotient.mkₐ_eq_mk, hφ, zero_mul, sub_zero]
  have := congrArg (fun f ↦ f F) hmk
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  exact this.symm

end Module.Dual

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

local notation "𝒰⁻" => UniversalEnvelopingAlgebra K (nNeg P)

omit [CharZero K] in
/-- For a polynomial family `D`, `D(λ) - D(λ - (λ(a) + c) δ)` is `λ(a) + c` times a polynomial
family. -/
lemma exists_sub_comp_eq_smul {D : Dual K H → 𝒰⁻} (hD : D ∈ polyFam P) (a : H) (c : K)
    (δ : Dual K H) :
    ∃ G ∈ polyFam P, ∀ Λ, D Λ - D (Λ - (Λ a + c) • δ) = (Λ a + c) • G Λ := by
  induction hD using Submodule.span_induction with
  | mem D hD =>
    obtain ⟨p, u, rfl⟩ := hD
    obtain ⟨q, hq⟩ := affPoly_dvd_sub_projSubst a c δ p
    refine ⟨fun Λ ↦ evalPoly K H q Λ • u, Submodule.subset_span ⟨q, u, rfl⟩, fun Λ ↦ ?_⟩
    have h := congrFun (congrArg (evalPoly K H) hq) Λ
    rw [map_sub, map_mul, Pi.sub_apply, Pi.mul_apply, evalPoly_projSubst, evalPoly_affPoly] at h
    rw [← sub_smul, h, mul_smul]
  | zero => exact ⟨0, zero_mem _, fun Λ ↦ by simp⟩
  | add D E _ _ hD hE =>
    obtain ⟨G, hG, hDG⟩ := hD
    obtain ⟨G', hG', hEG⟩ := hE
    refine ⟨G + G', add_mem hG hG', fun Λ ↦ ?_⟩
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, smul_add, ← hDG, ← hEG]
    abel
  | smul b D _ hD =>
    obtain ⟨G, hG, hDG⟩ := hD
    refine ⟨b • G, Submodule.smul_mem _ b hG, fun Λ ↦ ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ← smul_sub, hDG, smul_comm]

namespace IsShapovalovElement

variable {hA : A.IsGeneralizedCartan} {v : P.weylGroup hA} {i : ι} {r : ℕ} {a : ι → ℕ}

/-- `θ(λ) v_λ` is a maximal vector of weight `λ - rγ` when `⟨λ + ρ, γ^∨⟩ = r`. -/
lemma equivEnvNNeg_mem_primitiveVectors {θ : Dual K H → 𝒰⁻}
    (h : IsShapovalovElement P hA v i r a θ) {Λ : Dual K H}
    (hΛ : P.corootPairing hA (Λ + P.rho) v i = r) :
    equivEnvNNeg P Λ (θ Λ) ∈
      primitiveVectors P (VermaModule P Λ) (Λ - r • P.rootOf fun j ↦ (a j : ℤ)) := by
  refine mem_primitiveVectors.mpr
    ⟨(equivEnvNNeg_mem_weightSpace_iff P Λ _ _).mpr (h.mem_negWeightSpace Λ), fun k ↦ ?_⟩
  have hk := h.actEnv_eq_zero Λ hΛ (e P k) (e_mem_nPos P k)
  rwa [← (equivEnvNNeg P Λ).map_eq_zero_iff, equivEnvNNeg_actEnv] at hk

/-- **Uniqueness on the hyperplane** ([HumO] §4.13): two Shapovalov elements for `(γ, r)` agree at
every `λ` with `⟨λ + ρ, γ^∨⟩ = r`. -/
theorem eq_of_corootPairing_eq [IsAlgClosed K] [FiniteDimensional K H] (hfin : A.IsFiniteCartan)
    {θ θ' : Dual K H → 𝒰⁻}
    (h : IsShapovalovElement P hA v i r a θ) (h' : IsShapovalovElement P hA v i r a θ')
    (hpos : 0 < r * ∑ j, a j) {Λ : Dual K H} (hΛ : P.corootPairing hA (Λ + P.rho) v i = r) :
    θ Λ = θ' Λ := by
  obtain ⟨S⟩ := isSymmetrizable_iff_nonempty_symmetrization.mp hfin.isSymmetrizable
  set W := primitiveVectors P (VermaModule P Λ) (Λ - r • P.rootOf fun j ↦ (a j : ℤ))
  have : FiniteDimensional K W := by
    haveI := finiteDimensional_weightSpace P Λ (Λ - r • P.rootOf fun j ↦ (a j : ℤ))
    exact Submodule.finiteDimensional_of_le inf_le_left
  have h1 : finrank K W ≤ 1 := by
    rw [← finrank_hom (V := VermaModule P Λ)]
    exact finrank_hom_le_one_of_finite_type P hfin S Λ _
  obtain ⟨w₀, hw₀⟩ := finrank_le_one_iff.mp h1
  obtain ⟨c, hc⟩ := hw₀ ⟨_, h.equivEnvNNeg_mem_primitiveVectors hΛ⟩
  obtain ⟨c', hc'⟩ := hw₀ ⟨_, h'.equivEnvNNeg_mem_primitiveVectors hΛ⟩
  have e1 := congrArg Subtype.val hc
  have e2 := congrArg Subtype.val hc'
  simp only [Submodule.coe_smul] at e1 e2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at e1
    exact h.ne_zero hpos Λ ((equivEnvNNeg P Λ).map_eq_zero_iff.mp e1.symm)
  have hk : θ' Λ = (c' / c) • θ Λ := by
    apply (equivEnvNNeg P Λ).injective
    rw [map_smul, ← e1, ← e2, smul_smul, div_mul_cancel₀ _ hc0]
  have hs := (h'.hasSymbol hpos Λ).unique
    (by rw [hk]; exact (h.hasSymbol hpos Λ).smul (c' / c))
  have hc1 : c' / c = 1 := by
    by_contra hne
    have h0 : (c' / c - 1) • ∏ j, fSym P j ^ (r * a j) = 0 := by
      rw [sub_smul, one_smul, ← hs, sub_self]
    exact prod_fSym_ne_zero r a ((smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne))
  rw [hk, hc1, one_smul]

/-- **Uniqueness of Shapovalov elements** ([HumO] Thm. 4.12): for `𝔤` of finite type, two
Shapovalov elements for `(γ, r)` differ by `⟨λ + ρ, γ^∨⟩ - r` times a polynomial family, i.e. they
agree modulo `U(𝔟⁻)(h_γ + ρ(h_γ) - r)`. -/
theorem exists_sub_eq_smul [IsAlgClosed K] [FiniteDimensional K H] (hfin : A.IsFiniteCartan)
    {θ θ' : Dual K H → 𝒰⁻}
    (h : IsShapovalovElement P hA v i r a θ) (h' : IsShapovalovElement P hA v i r a θ')
    (hpos : 0 < r * ∑ j, a j) :
    ∃ G ∈ polyFam P, ∀ Λ, θ Λ - θ' Λ = (P.corootPairing hA (Λ + P.rho) v i - r) • G Λ := by
  let φ : Dual K (Dual K H) := (Dual.eval K H (P.coroot i)).comp
    ((v⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H).toLinearMap
  obtain ⟨b, hb⟩ : ∃ b : H, ∀ Λ : Dual K H, Λ b = P.corootPairing hA Λ v i :=
    ⟨(Module.evalEquiv K H).symm φ, fun Λ ↦ Module.apply_evalEquiv_symm_apply Λ φ⟩
  obtain ⟨c, hc⟩ : ∃ c : K, c = P.corootPairing hA P.rho v i - r := ⟨_, rfl⟩
  have hbc : ∀ Λ : Dual K H, Λ b + c = P.corootPairing hA (Λ + P.rho) v i - r := by
    intro Λ
    rw [hb, hc, corootPairing_add]
    ring
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h2 := hb ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    rw [map_zero, corootPairing_apply, inv_mul_cancel, corootPairing_one,
      P.root_coroot_self hA] at h2
    exact two_ne_zero h2.symm
  obtain ⟨δ, hδ⟩ := exists_dual_apply_eq_one (K := K) hb0
  obtain ⟨G, hG, hDG⟩ := exists_sub_comp_eq_smul
    (sub_mem_polyFam h.mem_polyFam h'.mem_polyFam) b c δ
  refine ⟨G, hG, fun Λ ↦ ?_⟩
  have hΛ' : P.corootPairing hA ((Λ - (Λ b + c) • δ) + P.rho) v i = r := by
    have h3 := hbc (Λ - (Λ b + c) • δ)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hδ, smul_eq_mul, mul_one] at h3
    linear_combination -h3
  have heq := h.eq_of_corootPairing_eq hfin h' hpos hΛ'
  calc θ Λ - θ' Λ
      = (θ Λ - θ' Λ) - (θ (Λ - (Λ b + c) • δ) - θ' (Λ - (Λ b + c) • δ)) := by
        rw [heq, sub_self, sub_zero]
    _ = (Λ b + c) • G Λ := hDG Λ
    _ = _ := by rw [hbc]

end IsShapovalovElement

end Matrix.Realization.KacMoodyAlgebra.VermaModule
