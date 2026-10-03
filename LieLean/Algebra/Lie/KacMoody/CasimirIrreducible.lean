/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Casimir
import LieLean.Algebra.Lie.KacMoody.CategoryOSubmodule
import LieLean.Algebra.Lie.KacMoody.HighestWeightVector

/-!
# Integrable highest-weight modules are irreducible

Let `A` be a symmetrizable generalized Cartan matrix over a field `K` of characteristic zero, and
let `B` be a standard invariant form on `𝔤(A)` (`KacMoodyAlgebra.IsStandardForm`). Using the
Casimir operator we show that every integrable quotient `V` of a Verma module `M(Λ)` is
irreducible. Consequently, for `Λ` dominant integral the canonical surjection
`L̃(Λ) = M(Λ) / ∑ᵢ U(𝔤) fᵢ^{⟨Λ,αᵢ^∨⟩+1} v_Λ → L(Λ)` is an isomorphism ([Kac] Cor. 10.4).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.dualBilinForm_add_two_rho_ne`: for dominant integral
  `Λ`, `μ` with `Λ - μ ∈ Q₊ \ {0}`, `(Λ + 2ρ | Λ) ≠ (μ + 2ρ | μ)`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.eq_bot_or_eq_top_of_isIntegrable`,
  `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.isIrreducible_of_isIntegrable`: an integrable
  quotient of `M(Λ)` is irreducible.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.toIrreducibleModule_injective`,
  `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.fPowQuotientEquiv`: `L̃(Λ) ≅ L(Λ)` for `Λ`
  dominant integral ([Kac] Cor. 10.4).
* `Matrix.Realization.KacMoodyAlgebra.isIrreducible_of_isIntegrable`,
  `Matrix.Realization.KacMoodyAlgebra.FPowQuotient.toIrreducibleModule_injective`,
  `Matrix.Realization.KacMoodyAlgebra.FPowQuotient.equivIrreducibleModule`: the same for any
  symmetrizable generalized Cartan matrix, using the invariant form
  `Matrix.Realization.KacMoodyAlgebra.invForm` of [Kac] Thm. 2.2.

## Proof

Let `N ≠ 0` be a submodule of an integrable quotient `V` of `M(Λ)`. Since `N` lies in `𝒪`, it
contains a nonzero vector `w` of some weight `μ` killed by all the `eᵢ`; as `V` is integrable,
`μ` and `Λ` are dominant integral ([Kac] (3.2.4), as in the proof of Lemma 10.1), and
`μ = Λ - β` with `β ∈ Q₊`. The
Casimir operator acts on `V` by `(Λ + 2ρ | Λ)` and on `w` by `(μ + 2ρ | μ)`, so these agree. But
`(Λ + 2ρ | Λ) - (μ + 2ρ | μ) = (β | Λ + μ + 2ρ) = ∑ᵢ kᵢ (⟨Λ + μ, αᵢ^∨⟩ + 2) / εᵢ` for
`β = ∑ᵢ kᵢ αᵢ`, which is positive unless `β = 0`. Hence `μ = Λ`, `w` is a multiple of the image
of `v_Λ`, and `N = V`. [Kac] derives Cor. 10.4 from the character formula; the argument above is
the standard direct one via the Casimir operator (compare the proof of [Kac] Thm. 10.7),
written out by us.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.2, §2.5–2.6, §3.2,
  §9.1, §10.1–10.4, §10.7 (stated over `ℂ`).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- The weight space `V_Λ` of a quotient `V` of `M(Λ)` is spanned by the image of `v_Λ`. -/
lemma mem_span_map_hwv_of_mem_weightSpace [CharZero K] {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ) {w : V}
    (hw : w ∈ weightSpace P V Λ) : w ∈ K ∙ φ (VermaModule.hwv P Λ) := by
  have hmap (μ : Dual K H) : (VermaModule.weightSpace P Λ μ).map (φ : VermaModule P Λ →ₗ[K] V) ≤
      weightSpaceOfMap V (h P) μ := by
    rintro _ ⟨m, hm, rfl⟩
    exact map_mem_weightSpaceOfMap P φ hm
  have htop : w ∈ ⨆ μ, (VermaModule.weightSpace P Λ μ).map (φ : VermaModule P Λ →ₗ[K] V) := by
    rw [← Submodule.map_iSup]
    obtain ⟨m, rfl⟩ := hφ w
    refine Submodule.mem_map_of_mem ?_
    have hm : m ∈ ⨆ (k : ι → ℤ) (_ : 0 ≤ k), VermaModule.weightSpace P Λ (Λ - P.rootOf k) := by
      rw [VermaModule.iSup_weightSpace_eq_top]; trivial
    exact (iSup₂_le fun k _ ↦ le_iSup (VermaModule.weightSpace P Λ) _ :
      _ ≤ ⨆ μ, VermaModule.weightSpace P Λ μ) hm
  have := mem_of_mem_iSup_of_le (h P) _ hmap hw htop
  rwa [VermaModule.weightSpace_self, Submodule.map_span, Set.image_singleton] at this

/-! ### The values of the Casimir operator on dominant integral weights -/

omit [DecidableEq ι] in
/-- For dominant integral `Λ`, `μ` with `Λ - μ ∈ Q₊ \ {0}`, `(Λ + 2ρ | Λ) ≠ (μ + 2ρ | μ)`: indeed
`(Λ + 2ρ | Λ) - (μ + 2ρ | μ) = (Λ - μ | Λ + μ + 2ρ) > 0` ([Kac] Lemma 10.3, used in §10.4). -/
theorem dualBilinForm_add_two_rho_ne [CharZero K] [FiniteDimensional K H] (S : A.Symmetrization)
    {Λ μ : Dual K H} (hΛ : P.IsDominantIntegral Λ) (hμ : P.IsDominantIntegral μ) {k : ι → ℤ}
    (hk : k ∈ posCone ι) (hΛμ : Λ = μ + P.rootOf k) :
    P.dualBilinForm S (Λ + 2 • P.rho) Λ ≠ P.dualBilinForm S (μ + 2 • P.rho) μ := by
  choose n hn using hΛ
  choose m hm using hμ
  intro heq
  have hsymm := (P.isSymm_dualBilinForm S).eq
  have h1 : P.dualBilinForm S (P.rootOf k) (Λ + μ + 2 • P.rho) = 0 := by
    rw [hΛμ] at heq ⊢
    simp only [two_nsmul, map_add, LinearMap.add_apply] at heq ⊢
    rw [hsymm μ (P.rootOf k), hsymm P.rho (P.rootOf k)] at heq
    linear_combination heq
  have h2 : P.dualBilinForm S (P.rootOf k) (Λ + μ + 2 • P.rho) =
      ((∑ i, (k i : ℚ) * ((n i + m i + 2) / S.ε i) : ℚ) : K) := by
    rw [rootOf_apply, map_sum, LinearMap.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hsymm, dualBilinForm_root_right]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hn, hm, rho_coroot, nsmul_eq_mul]
    push_cast
    ring
  have hq : (0 : ℚ) < ∑ i, (k i : ℚ) * ((n i + m i + 2) / S.ε i) := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hk.2
    refine Finset.sum_pos' (fun i _ ↦ mul_nonneg (by exact_mod_cast hk.1 i)
      (div_nonneg (by positivity) (S.ε_pos i).le)) ⟨j, Finset.mem_univ j, mul_pos ?_
      (div_pos (by positivity) (S.ε_pos j))⟩
    have := hk.1 j
    simp only [Pi.zero_apply] at hj this
    exact_mod_cast lt_of_le_of_ne this (Ne.symm hj)
  rw [h2, Rat.cast_eq_zero] at h1
  exact hq.ne' h1

/-! ### Integrable quotients of Verma modules -/

variable [CharZero K] [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

namespace IsStandardForm

variable (hB : IsStandardForm P S B) (hA : A.IsGeneralizedCartan)
include hB hA

/-- For symmetrizable `A`, every submodule of an integrable quotient `V` of a Verma module `M(Λ)`
is `0` or `V` (see the module docstring for the proof via the Casimir operator). -/
theorem eq_bot_or_eq_top_of_isIntegrable {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (hV : IsIntegrable P V) (N : LieSubmodule K P.KacMoodyAlgebra V) : N = ⊥ ∨ N = ⊤ := by
  refine or_iff_not_imp_left.mpr fun hN ↦ ?_
  have hO : IsCategoryO P V := .of_surjective φ hφ
  have : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot K P.KacMoodyAlgebra V).mpr hN
  obtain ⟨μ, w, hw, hw0, he⟩ := (hO.lieSubmodule N).exists_lie_e_eq_zero
  have hw' : (w : V) ∈ weightSpace P V μ := mem_weightSpaceOfMap_lieSubmodule_iff.mp hw
  have he' (i : ι) : ⁅e P i, (w : V)⁆ = 0 := by
    have := congrArg Subtype.val (he i)
    rwa [LieSubmodule.coe_bracket] at this
  have hw0' : (w : V) ≠ 0 := fun h0 ↦ hw0 (Subtype.ext h0)
  have hv0 : φ (VermaModule.hwv P Λ) ≠ 0 := fun h0 ↦ hw0' (by
    have htop := VermaModule.lieSpan_map_hwv_eq_top φ hφ
    rw [h0] at htop
    have hle : LieSubmodule.lieSpan K P.KacMoodyAlgebra ({0} : Set V) ≤ ⊥ :=
      LieSubmodule.lieSpan_le.mpr (by simp)
    exact (LieSubmodule.mem_bot _).mp (hle (htop ▸ LieSubmodule.mem_top (w : V))))
  have hΛ := isDominantIntegral_of_isIntegrable hA hV
    (map_mem_weightSpaceOfMap P φ (VermaModule.hwv_mem_weightSpace P Λ))
    (fun i ↦ by rw [← LieModuleHom.map_lie, VermaModule.lie_e_hwv, map_zero]) hv0
  have hμ := isDominantIntegral_of_isIntegrable hA hV hw' he' hw0'
  obtain ⟨k, hk, hμΛ⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P Λ φ hφ hw' hw0'
  have hPF := hO.isPosFinite
  have hΩ : P.dualBilinForm S (Λ + 2 • P.rho) Λ = P.dualBilinForm S (μ + 2 • P.rho) μ :=
    smul_left_injective K hw0' ((hB.casimir_eq_smul_of_surjective hA hPF φ hφ (w : V)).symm.trans
      (hB.casimir_apply_of_lie_e_eq_zero hPF hw' he'))
  by_cases hk0 : k = 0
  · rw [hk0, map_zero, sub_zero] at hμΛ
    rw [hμΛ] at hw'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (mem_span_map_hwv_of_mem_weightSpace φ hφ hw')
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw0' hc.symm
    have hmem : φ (VermaModule.hwv P Λ) ∈ N := by
      have := N.smul_mem c⁻¹ w.2
      rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    rw [eq_top_iff, ← VermaModule.lieSpan_map_hwv_eq_top φ hφ, LieSubmodule.lieSpan_le]
    rintro _ rfl
    exact hmem
  · exact absurd hΩ (dualBilinForm_add_two_rho_ne S hΛ hμ ⟨hk, hk0⟩ (by rw [hμΛ, sub_add_cancel]))

/-- For symmetrizable `A`, every nonzero integrable quotient of a Verma module is irreducible,
hence isomorphic to `L(Λ)` ([Kac] Cor. 10.4). -/
theorem isIrreducible_of_isIntegrable [Nontrivial V] {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (hV : IsIntegrable P V) : IsIrreducible K P.KacMoodyAlgebra V :=
  IsIrreducible.mk fun N hN ↦ (hB.eq_bot_or_eq_top_of_isIntegrable hA φ hφ hV N).resolve_left hN

/-- **[Kac] Cor. 10.4**: for symmetrizable `A` and `Λ` dominant integral with
`nᵢ = ⟨Λ, αᵢ^∨⟩`, the canonical surjection `L̃(Λ) → L(Λ)` is injective, i.e. `L(Λ)` is the
quotient of `M(Λ)` by the submodule generated by the `fᵢ^{nᵢ+1} v_Λ`. -/
theorem toIrreducibleModule_injective {Λ : Dual K H} {n : ι → ℕ}
    (hn : ∀ i, Λ (P.coroot i) = n i) :
    Function.Injective (FPowQuotient.toIrreducibleModule P hA hn) := by
  rw [← LieModuleHom.ker_eq_bot]
  refine (hB.eq_bot_or_eq_top_of_isIntegrable hA (LieSubmodule.Quotient.mk' _)
    (LieSubmodule.Quotient.surjective_mk' _) (FPowQuotient.isIntegrable P Λ n hA)
    _).resolve_right fun htop ↦ ?_
  have : FPowQuotient.hwv P Λ n ∈ (FPowQuotient.toIrreducibleModule P hA hn).ker :=
    htop ▸ LieSubmodule.mem_top _
  rw [LieModuleHom.mem_ker, FPowQuotient.toIrreducibleModule_hwv] at this
  exact IrreducibleModule.hwv_ne_zero P Λ this

/-- **[Kac] Cor. 10.4**: for symmetrizable `A` and `Λ` dominant integral,
`L̃(Λ) = M(Λ) / ∑ᵢ U(𝔤) fᵢ^{⟨Λ,αᵢ^∨⟩+1} v_Λ` is isomorphic to `L(Λ)`. -/
def fPowQuotientEquiv {Λ : Dual K H} {n : ι → ℕ} (hn : ∀ i, Λ (P.coroot i) = n i) :
    FPowQuotient P Λ n ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ :=
  LieModuleEquiv.ofBijective (FPowQuotient.toIrreducibleModule P hA hn)
    ⟨hB.toIrreducibleModule_injective hA hn, FPowQuotient.toIrreducibleModule_surjective P hA hn⟩

@[simp] lemma fPowQuotientEquiv_apply {Λ : Dual K H} {n : ι → ℕ}
    (hn : ∀ i, Λ (P.coroot i) = n i) (x : FPowQuotient P Λ n) :
    hB.fPowQuotientEquiv hA hn x = FPowQuotient.toIrreducibleModule P hA hn x :=
  rfl

end IsStandardForm

/-! ### Versions for the invariant form `invForm` -/

variable (hS : A.IsSymmetrizable) (hA : A.IsGeneralizedCartan)
include hS hA

/-- For a symmetrizable generalized Cartan matrix, every nonzero integrable quotient of a Verma
module is irreducible ([Kac] Cor. 10.4). -/
theorem isIrreducible_of_isIntegrable [Nontrivial V] {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (hV : IsIntegrable P V) : IsIrreducible K P.KacMoodyAlgebra V :=
  have S := (isSymmetrizable_iff_nonempty_symmetrization.mp hS).some
  (isStandardForm_invForm P S).isIrreducible_of_isIntegrable hA φ hφ hV

/-- **[Kac] Cor. 10.4**: for a symmetrizable generalized Cartan matrix `A` and `Λ`
dominant integral with `nᵢ = ⟨Λ, αᵢ^∨⟩`, the canonical surjection `L̃(Λ) → L(Λ)` is injective. -/
theorem FPowQuotient.toIrreducibleModule_injective {Λ : Dual K H} {n : ι → ℕ}
    (hn : ∀ i, Λ (P.coroot i) = n i) :
    Function.Injective (FPowQuotient.toIrreducibleModule P hA hn) :=
  have S := (isSymmetrizable_iff_nonempty_symmetrization.mp hS).some
  (isStandardForm_invForm P S).toIrreducibleModule_injective hA hn

/-- **[Kac] Cor. 10.4**: for a symmetrizable generalized Cartan matrix `A` and `Λ`
dominant integral, `L(Λ)` is isomorphic to `L̃(Λ) = M(Λ) / ∑ᵢ U(𝔤) fᵢ^{⟨Λ,αᵢ^∨⟩+1} v_Λ`. -/
def FPowQuotient.equivIrreducibleModule {Λ : Dual K H} {n : ι → ℕ}
    (hn : ∀ i, Λ (P.coroot i) = n i) :
    FPowQuotient P Λ n ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ :=
  (isStandardForm_invForm P (isSymmetrizable_iff_nonempty_symmetrization.mp hS).some)
    |>.fPowQuotientEquiv hA hn

@[simp] lemma FPowQuotient.equivIrreducibleModule_apply {Λ : Dual K H} {n : ι → ℕ}
    (hn : ∀ i, Λ (P.coroot i) = n i) (x : FPowQuotient P Λ n) :
    FPowQuotient.equivIrreducibleModule hS hA hn x = FPowQuotient.toIrreducibleModule P hA hn x :=
  rfl

end Matrix.Realization.KacMoodyAlgebra
