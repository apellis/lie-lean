/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DualityExt
import LieLean.Algebra.Lie.KacMoody.DualVerma
import LieLean.Algebra.Lie.KacMoody.ExtHighestWeight

/-!
# Duals of highest weight modules

Humphreys, GSM 94, Theorem 3.3, for the duals `M(λ)^∨` of Verma modules. Part (a), `L(λ)^∨ ≅ L(λ)`,
is `IrreducibleModule.equivRestrictedDual`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.range_toRestrictedDual_le`: (b), every
  nonzero submodule of `M(λ)^∨` contains the image of `L(λ) ↪ M(λ)^∨`, so this image is the unique
  simple submodule;
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_restrictedDual_verma_self`,
  `Matrix.Realization.KacMoodyAlgebra.mem_cone_of_multiplicity_restrictedDual_verma_ne_zero`: (b),
  `[M(λ)^∨ : L(λ)] = 1` and the other composition factors `L(μ)` have `μ < λ`;
* `Matrix.Realization.KacMoodyAlgebra.finrank_hom_verma_restrictedDual_verma`,
  `Matrix.Realization.KacMoodyAlgebra.range_hom_verma_restrictedDual_verma`: (c),
  `dim Hom(M(μ), M(λ)^∨) = δ_{λμ}`, and a nonzero morphism `M(μ) → M(λ)^∨` has image `L(λ)`;
* `Matrix.Realization.KacMoodyAlgebra.extOne_verma_restrictedDual_verma_eq_zero`: (d),
  `Ext_𝒪(M(μ), M(λ)^∨) = 0`.

## Proof notes

For (b) Humphreys dualizes `0 → N(λ) → M(λ) → L(λ) → 0`. Here a nonzero submodule `N` of `M(λ)^∨`
receives a nonzero morphism from some `M(ν)`; by (c), `ν = λ` and its image is that of `L(λ)`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.3.
-/

noncomputable section

open Module LieModule

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

instance finiteDimensional_hom_verma_restrictedDual_verma (Λ μ : Dual K H) :
    FiniteDimensional K (VermaModule P μ →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P Λ)) := by
  have hR := isCategoryO_restrictedDual (VermaModule.isCategoryO P Λ)
  have := hR.finiteDimensional_weightSpaceOfMap μ
  have : FiniteDimensional K (primitiveVectors P (restrictedDual P (VermaModule P Λ)) μ) :=
    Submodule.finiteDimensional_of_le inf_le_left
  exact LinearEquiv.finiteDimensional (homEquiv P _ μ).symm

/-- **Humphreys, GSM 94, Theorem 3.3 (c)**, dimension part: `dim Hom(M(μ), M(λ)^∨) = δ_{λμ}`.
Humphreys states this for `𝔤` semisimple over `ℂ`. -/
theorem finrank_hom_verma_restrictedDual_verma [DecidableEq (Dual K H)] (Λ μ : Dual K H) :
    finrank K (VermaModule P μ →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P Λ)) =
      if Λ = μ then 1 else 0 := by
  rw [finrank_hom_restrictedDual_verma (VermaModule.isCategoryO P μ), VermaModule.coinvDim_top]

/-- A nonzero morphism `M(μ) → M(λ)^∨` forces `μ = λ`. -/
theorem eq_of_hom_verma_restrictedDual_verma_ne_zero {Λ μ : Dual K H}
    {f : VermaModule P μ →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P Λ)} (hf : f ≠ 0) : μ = Λ := by
  classical
  by_contra hne
  have h0 := finrank_hom_verma_restrictedDual_verma P Λ μ
  simp only [Ne.symm hne, ↓reduceIte, Module.finrank_zero_iff] at h0
  exact hf (Subsingleton.elim f 0)

/-- The image of `L(λ) ↪ M(λ)^∨` is the image of the Shapovalov map `M(λ) → M(λ)^∨`. -/
lemma IrreducibleModule.range_toRestrictedDual (Λ : Dual K H) :
    (IrreducibleModule.toRestrictedDual P Λ).range = (VermaModule.toRestrictedDual P Λ).range := by
  ext x
  simp only [LieModuleHom.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' (maxSubmodule P Λ) u
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨LieSubmodule.Quotient.mk' (maxSubmodule P Λ) v, rfl⟩

/-- **Humphreys, GSM 94, Theorem 3.3 (c)**, image part: a nonzero morphism `M(μ) → M(λ)^∨` has
`μ = λ`, and its image is the image of `L(λ) ↪ M(λ)^∨`. -/
theorem range_hom_verma_restrictedDual_verma {Λ μ : Dual K H}
    (f : VermaModule P μ →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P Λ)) (hf : f ≠ 0) :
    μ = Λ ∧ f.range = (IrreducibleModule.toRestrictedDual P Λ).range := by
  obtain rfl := eq_of_hom_verma_restrictedDual_verma_ne_zero P hf
  refine ⟨rfl, ?_⟩
  rw [IrreducibleModule.range_toRestrictedDual]
  have hφ := VermaModule.eq_smul_toTwistedDual P μ
    ((restrictedDual P (VermaModule P μ)).incl.comp f)
  set c := TwistedDual.toDual P _ (((restrictedDual P (VermaModule P μ)).incl.comp f)
    (VermaModule.hwv P μ)) (VermaModule.hwv P μ)
  have hfu : ∀ u, f u = c • VermaModule.toRestrictedDual P μ u := fun u ↦
    Subtype.ext (LieModuleHom.congr_fun hφ u)
  have hc : c ≠ 0 := by
    rintro hc
    exact hf (LieModuleHom.ext fun u ↦ by rw [hfu, hc, zero_smul, _root_.zero_apply])
  ext x
  simp only [LieModuleHom.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨c • u, by rw [hfu, map_smul]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨c⁻¹ • u, by rw [hfu, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

/-- **Humphreys, GSM 94, Theorem 3.3 (b)**, socle part: every nonzero submodule of `M(λ)^∨` contains
the image of `L(λ) ↪ M(λ)^∨`. Hence this image, isomorphic to `L(λ)`, is the unique simple
submodule of `M(λ)^∨`. Humphreys states this for `𝔤` semisimple over `ℂ`. -/
theorem IrreducibleModule.range_toRestrictedDual_le (Λ : Dual K H)
    {N : LieSubmodule K 𝔤 (restrictedDual P (VermaModule P Λ))} (hN : N ≠ ⊥) :
    (IrreducibleModule.toRestrictedDual P Λ).range ≤ N := by
  have hO := (isCategoryO_restrictedDual (VermaModule.isCategoryO P Λ)).lieSubmodule N
  have : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot K 𝔤 _).mpr hN
  obtain ⟨ν, φ, hφ⟩ := hO.exists_lieModuleHom_verma
  have hf : N.incl.comp φ ≠ 0 := fun h0 ↦ hφ (Subtype.ext
    (by simpa using LieModuleHom.congr_fun h0 (VermaModule.hwv P ν)))
  rw [← (range_hom_verma_restrictedDual_verma P _ hf).2]
  rintro _ ⟨u, rfl⟩
  exact (φ u).2

/-- **Humphreys, GSM 94, Theorem 3.3 (b)**, multiplicity of `L(λ)`: `[M(λ)^∨ : L(λ)] = 1`. -/
theorem multiplicity_restrictedDual_verma_self (Λ : Dual K H) :
    (isCategoryO_restrictedDual (VermaModule.isCategoryO P Λ)).multiplicity Λ = 1 := by
  rw [multiplicity_restrictedDual (VermaModule.isCategoryO P Λ), VermaModule.multiplicity_self]

/-- **Humphreys, GSM 94, Theorem 3.3 (b)**, other composition factors: if `[M(λ)^∨ : L(μ)] ≠ 0`
then `μ ≤ λ`. -/
theorem mem_cone_of_multiplicity_restrictedDual_verma_ne_zero {Λ μ : Dual K H}
    (h : (isCategoryO_restrictedDual (VermaModule.isCategoryO P Λ)).multiplicity μ ≠ 0) :
    μ ∈ cone P Λ := by
  rw [multiplicity_restrictedDual (VermaModule.isCategoryO P Λ)] at h
  exact VermaModule.mem_cone_of_multiplicity_ne_zero h

/-- The weights of `M(λ)^∨` lie in `λ - Q₊`. -/
lemma mem_cone_of_mem_weightSpace_restrictedDual_verma {Λ ν : Dual K H}
    {x : restrictedDual P (VermaModule P Λ)}
    (hx : x ∈ weightSpaceOfMap (restrictedDual P (VermaModule P Λ)) (h P) ν) (hx0 : x ≠ 0) :
    ν ∈ cone P Λ := by
  have hV := VermaModule.isCategoryO P Λ
  have := hV.finiteDimensional_weightSpaceOfMap ν
  have := (isCategoryO_restrictedDual hV).finiteDimensional_weightSpaceOfMap ν
  have hpos : 0 < finrank K (weightSpaceOfMap (VermaModule P Λ) (h P) ν) := by
    rw [← finrank_weightSpace_restrictedDual hV, Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨x, hx⟩, fun h0 ↦ hx0 (congrArg Subtype.val h0)⟩
  obtain ⟨⟨y, hy⟩, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  exact VermaModule.exists_eq_sub_of_mem_weightSpace P Λ LieModuleHom.id Function.surjective_id hy
    fun h0 ↦ hy0 (Subtype.ext h0)

/-- **Humphreys, GSM 94, Theorem 3.3 (d)**: `Ext_𝒪(M(μ), M(λ)^∨) = 0` for all `λ, μ`. Humphreys
states this for `𝔤` semisimple over `ℂ`. -/
theorem extOne_verma_restrictedDual_verma_eq_zero (Λ μ : Dual K H)
    (y : ExtOne (h P) (VermaModule P μ) (restrictedDual P (VermaModule P Λ))) : y = 0 := by
  have hV := VermaModule.isCategoryO P Λ
  have hW := VermaModule.isCategoryO P μ
  by_cases hc : μ ∈ cone P Λ ∧ μ ≠ Λ
  · -- `μ < λ`: dualize, using `M(λ)^∨∨ ≅ M(λ)` and `λ ≮ μ`
    have hΛ : ¬ (Λ ∈ cone P μ ∧ Λ ≠ μ) := fun h' ↦ hc.2 (eq_of_mem_cone_of_mem_cone hc.1 h'.1)
    have h0 : ExtOne.mapComap (h P) (LieModuleEquiv.refl).toLieModuleHom
        (restrictedDoubleDualEquiv hV).toLieModuleHom
        (extOneRestrictedDual P (VermaModule P μ) (restrictedDual P (VermaModule P Λ)) y) = 0 :=
      extOne_verma_eq_zero_of_mem_cone P (isCategoryO_restrictedDual hW).1
        (fun _ _ hx hx0 ↦ mem_cone_of_mem_weightSpace_restrictedDual_verma P hx hx0) hΛ _
    exact injective_extOneRestrictedDual hW (isCategoryO_restrictedDual hV)
      ((ExtOne.injective_mapComap (h P) LieModuleEquiv.refl (restrictedDoubleDualEquiv hV)
        (h0.trans (LinearMap.map_zero _).symm)).trans (LinearMap.map_zero _).symm)
  · exact extOne_verma_eq_zero_of_mem_cone P (isCategoryO_restrictedDual hV).1
      (fun _ _ hx hx0 ↦ mem_cone_of_mem_weightSpace_restrictedDual_verma P hx hx0) hc y

end Matrix.Realization.KacMoodyAlgebra
