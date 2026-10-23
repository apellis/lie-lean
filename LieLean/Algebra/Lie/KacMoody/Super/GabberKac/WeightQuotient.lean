/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.Weights

/-!
# Weight spaces of submodules and quotients

Let `V` be a `U(G̃(A, τ))`-module which is the sum of its weight spaces, and `N ⊆ V` a submodule.
The weight spaces of `N` are the intersections `N ∩ V_μ`, those of `V / N` are the images of the
`V_μ`, and, when `V_μ` is finite-dimensional, `dim V_μ = dim N_μ + dim (V / N)_μ`. These are the
additivity properties of formal characters used in the computation of the character of the Verma
module of `G(A, τ)` ([Kac78] §2, cf. [Kac] §9.7).

## Main results

* `Matrix.Realization.SuperEnveloping.map_modWeightSpace_submodule`: `N_μ = N ∩ V_μ`.
* `Matrix.Realization.SuperEnveloping.modWeightSpace_quotient`: `(V / N)_μ` is the image of `V_μ`.
* `Matrix.Realization.SuperEnveloping.finrank_modWeightSpace_eq_add`:
  `dim V_μ = dim N_μ + dim (V / N)_μ`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.7.
-/

open Module

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} {p : ι → ZMod 2}

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (P.SuperEnveloping p) V]
  [IsScalarTower K (P.SuperEnveloping p) V]

/-- A bounded module is the sum of its weight spaces. -/
lemma IsBounded.iSup_modWeightSpace_eq_top {Λs : Finset (Dual K H)} (hV : IsBounded P p V Λs) :
    ⨆ μ, modWeightSpace P p V μ = ⊤ := by
  refine eq_top_iff.2 fun v _ ↦ ?_
  refine Submodule.span_le.2 ?_ (hV v)
  rintro w ⟨Λ, -, d, -, hw⟩
  exact Submodule.mem_iSup_of_mem _ hw

variable (P p V) in
/-- The action of `𝔥` on `V`. -/
def hAct : H →ₗ[K] Module.End K V where
  toFun a := smulEnd P p V (h P p a)
  map_add' a b := by ext v; simp [smulEnd, add_smul]
  map_smul' c a := by ext v; simp [smulEnd, smul_assoc]

lemma modWeightSpace_eq_weightSpaceOf (μ : Dual K H) :
    modWeightSpace P p V μ = Module.End.weightSpaceOf (hAct P p V) μ := rfl

section Equiv

variable {W : Type*} [AddCommGroup W] [Module K W] [Module (P.SuperEnveloping p) W]
  [IsScalarTower K (P.SuperEnveloping p) W]

/-- Module isomorphisms preserve weight spaces. -/
lemma map_modWeightSpace_equiv (φ : V ≃ₗ[P.SuperEnveloping p] W) (μ : Dual K H) :
    (modWeightSpace P p V μ).map (φ.restrictScalars K).toLinearMap = modWeightSpace P p W μ := by
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩ a
    rw [← map_smul, hv a]; exact φ.toLinearMap.map_smul_of_tower _ _
  · intro hw
    refine ⟨φ.symm w, fun a ↦ ?_, φ.apply_symm_apply w⟩
    rw [← map_smul, hw a]; exact φ.symm.toLinearMap.map_smul_of_tower _ _

lemma finrank_modWeightSpace_equiv (φ : V ≃ₗ[P.SuperEnveloping p] W) (μ : Dual K H) :
    finrank K (modWeightSpace P p V μ) = finrank K (modWeightSpace P p W μ) := by
  rw [← map_modWeightSpace_equiv φ, LinearEquiv.finrank_map_eq]

end Equiv

variable (N : Submodule (P.SuperEnveloping p) V)

/-- The weight spaces of a submodule: `N_μ = N ∩ V_μ`. -/
lemma map_modWeightSpace_submodule (μ : Dual K H) :
    (modWeightSpace P p N μ).map (N.subtype.restrictScalars K) =
      modWeightSpace P p V μ ⊓ N.restrictScalars K := by
  ext v
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Submodule.coe_subtype,
    Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun a ↦ ?_, w.2⟩
    have := congr_arg Subtype.val (hw a)
    simpa using this
  · rintro ⟨hv, hvN⟩
    exact ⟨⟨v, hvN⟩, fun a ↦ Subtype.ext (by simpa using hv a), rfl⟩

/-- A submodule of a module which is the sum of its weight spaces is the sum of its weight
spaces. -/
lemma iSup_modWeightSpace_submodule (hV : ⨆ μ, modWeightSpace P p V μ = ⊤) :
    ⨆ μ, modWeightSpace P p N μ = ⊤ := by
  refine eq_top_iff.2 fun v _ ↦ ?_
  have hle := Module.End.inf_iSup_weightSpaceOf_le (hAct P p V) (N.restrictScalars K)
    fun a m hm ↦ N.smul_mem (h P p a) hm
  have hv : (v : V) ∈ N.restrictScalars K ⊓ ⨆ μ, Module.End.weightSpaceOf (hAct P p V) μ := by
    refine ⟨v.2, ?_⟩
    simp only [← modWeightSpace_eq_weightSpaceOf, hV]
    trivial
  have hmap : ⨆ μ, (N.restrictScalars K ⊓ Module.End.weightSpaceOf (hAct P p V) μ) =
      (⨆ μ, modWeightSpace P p N μ).map (N.subtype.restrictScalars K) := by
    rw [Submodule.map_iSup]
    refine iSup_congr fun μ ↦ ?_
    rw [map_modWeightSpace_submodule, inf_comm, modWeightSpace_eq_weightSpaceOf]
  obtain ⟨w, hw, hwv⟩ := hmap ▸ hle hv
  have : w = v := Subtype.ext hwv
  exact this ▸ hw

lemma finrank_modWeightSpace_submodule (μ : Dual K H) :
    finrank K (modWeightSpace P p N μ) =
      finrank K ↥(modWeightSpace P p V μ ⊓ N.restrictScalars K) := by
  rw [← map_modWeightSpace_submodule]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (fun x y h ↦ Subtype.ext h) _))

lemma map_modWeightSpace_le_quotient (μ : Dual K H) :
    (modWeightSpace P p V μ).map (N.mkQ.restrictScalars K) ≤ modWeightSpace P p (V ⧸ N) μ := by
  rintro _ ⟨v, hv, rfl⟩ a
  simp only [LinearMap.coe_restrictScalars, Submodule.mkQ_apply]
  rw [← Submodule.Quotient.mk_smul, hv a, Submodule.Quotient.mk_smul]

/-- The weight spaces of a quotient: `(V / N)_μ` is the image of `V_μ`. -/
lemma modWeightSpace_quotient (hV : ⨆ μ, modWeightSpace P p V μ = ⊤) (μ : Dual K H) :
    modWeightSpace P p (V ⧸ N) μ = (modWeightSpace P p V μ).map (N.mkQ.restrictScalars K) := by
  refine le_antisymm (fun x hx ↦ ?_) (map_modWeightSpace_le_quotient N μ)
  obtain ⟨v, rfl⟩ := N.mkQ_surjective x
  have hv : v ∈ ⨆ ν, modWeightSpace P p V ν := hV ▸ Submodule.mem_top
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hv
  have hsum : N.mkQ (c.sum fun _ x ↦ x) - N.mkQ (c μ) ∈
      ⨆ ν, ⨆ (_ : ν ≠ μ), modWeightSpace P p (V ⧸ N) ν := by
    have : N.mkQ (c.sum fun _ x ↦ x) - N.mkQ (c μ) =
        (c.erase μ).sum fun _ x ↦ N.mkQ x := by
      rw [← Finsupp.add_sum_erase' c μ (fun _ x ↦ x) (fun _ ↦ rfl), map_add, add_sub_cancel_left,
        map_finsuppSum]
    rw [this]
    refine Submodule.finsuppSum_mem _ _ _ _ fun ν hν ↦ ?_
    have hνμ : ν ≠ μ := fun h ↦ hν (h ▸ Finsupp.erase_same)
    rw [Finsupp.erase_ne hνμ]
    exact Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hνμ
      (map_modWeightSpace_le_quotient N ν ⟨c ν, hc ν, rfl⟩))
  have hmem : N.mkQ (c.sum fun _ x ↦ x) - N.mkQ (c μ) ∈ modWeightSpace P p (V ⧸ N) μ :=
    sub_mem hx (map_modWeightSpace_le_quotient N μ ⟨c μ, hc μ, rfl⟩)
  have h0 := Submodule.disjoint_def.1 ((iSupIndep_modWeightSpace (V ⧸ N)) μ) _ hmem hsum
  rw [sub_eq_zero] at h0
  rw [h0]
  exact ⟨c μ, hc μ, rfl⟩

/-- **Additivity of weight multiplicities**: `dim V_μ = dim N_μ + dim (V / N)_μ`. -/
theorem finrank_modWeightSpace_eq_add (hV : ⨆ μ, modWeightSpace P p V μ = ⊤) (μ : Dual K H)
    [FiniteDimensional K (modWeightSpace P p V μ)] :
    finrank K (modWeightSpace P p V μ) =
      finrank K (modWeightSpace P p N μ) + finrank K (modWeightSpace P p (V ⧸ N) μ) := by
  set f := (N.mkQ.restrictScalars K).domRestrict (modWeightSpace P p V μ)
  have hrange : LinearMap.range f = modWeightSpace P p (V ⧸ N) μ := by
    rw [modWeightSpace_quotient N hV, LinearMap.range_domRestrict]
  have hker : finrank K (LinearMap.ker f) =
      finrank K ↥(modWeightSpace P p V μ ⊓ N.restrictScalars K) := by
    refine LinearEquiv.finrank_eq
      ((Submodule.equivMapOfInjective ((modWeightSpace P p V μ).subtype)
        (Submodule.injective_subtype _) _).trans (LinearEquiv.ofEq _ _ ?_))
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf,
      Submodule.restrictScalars_mem, Submodule.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      simpa [f, Submodule.Quotient.mk_eq_zero] using hw
    · rintro ⟨hv, hvN⟩
      exact ⟨⟨v, hv⟩, by simpa [f, Submodule.Quotient.mk_eq_zero] using hvN, rfl⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hrange, hker,
    finrank_modWeightSpace_submodule, add_comm]

end Matrix.Realization.SuperEnveloping
