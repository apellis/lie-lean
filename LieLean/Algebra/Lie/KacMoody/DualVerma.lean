/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.StandardFiltration
import LieLean.Algebra.Lie.KacMoody.RestrictedDual
import LieLean.Algebra.Lie.KacMoody.Grothendieck

/-!
# Restricted duals and dual Verma modules

For a module `V ∈ 𝒪`, the restricted dual `V^∨ = ⨁ (V_μ)^*` (`restrictedDual`) lies in `𝒪` and has
the same character, hence the same composition multiplicities, as `V` (Humphreys, GSM 94, §3.2).
The primitive vectors of weight `μ` of `V^∨` are the functionals on `V_μ` killing `(𝔫₋V)_μ`, so
`dim Hom(M(μ), V^∨) = dim (V / 𝔫₋V)_μ`. Morphisms `A → B^∨` and `B → A^∨` correspond to each other
(both are contravariant pairings `A × B → K`), so `dim Hom(V, M(μ)^∨) = dim (V / 𝔫₋V)_μ`: with
the coinvariant form of Theorem 3.7 (`IsStdFiltered.count_eq_coinvDim`) this gives Humphreys'
Theorem 3.7, `(V : M(μ)) = dim Hom(V, M(μ)^∨)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.finrank_weightSpace_twistedDual`:
  `dim (V^{*σ})_μ = dim V_μ`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.restrictedDual`,
  `IsCategoryO.multiplicity_restrictedDual`: `V^∨ ∈ 𝒪` and `[V^∨ : L(ν)] = [V : L(ν)]`.
* `Matrix.Realization.KacMoodyAlgebra.finrank_primitiveVectors_restrictedDual`:
  `dim Hom(M(μ), V^∨) = dim (V / 𝔫₋V)_μ`.
* `Matrix.Realization.KacMoodyAlgebra.finrank_hom_restrictedDual_verma`:
  `dim Hom(V, M(μ)^∨) = dim (V / 𝔫₋V)_μ`.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.count_eq_finrank_hom`: **Theorem 3.7**,
  `(V : M(μ)) = dim Hom(V, M(μ)^∨)` for `V ∈ 𝒪` with a standard filtration.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.2, §3.3, §3.7.
-/

noncomputable section

open Module LieModule

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

local notation "𝔤" => KacMoodyAlgebra P

section Weight

variable {P}

omit [CharZero K] in
/-- For an `𝔥`-diagonalizable module, `V_κ` is complementary to the sum of the other weight
spaces. -/
theorem isCompl_weightSpaceOfMap (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) (κ : Dual K H) :
    IsCompl (weightSpaceOfMap V (h P) κ) (⨆ (ν) (_ : ν ≠ κ), weightSpaceOfMap V (h P) ν) := by
  refine ⟨(iSupIndep_weightSpaceOfMap (h P)) κ, codisjoint_iff.mpr (eq_top_iff.mpr ?_)⟩
  rw [← hV]
  refine iSup_le fun ν ↦ ?_
  by_cases hν : ν = κ
  · subst hν; exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le ν hν le_rfl)

variable (P) in
/-- The projection `V → V_κ` along the other weight spaces. -/
def weightProj (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) (κ : Dual K H) :
    V →ₗ[K] weightSpaceOfMap V (h P) κ :=
  Submodule.projectionOnto (weightSpaceOfMap V (h P) κ)
    (⨆ (ν) (_ : ν ≠ κ), weightSpaceOfMap V (h P) ν) (isCompl_weightSpaceOfMap hV κ)

omit [CharZero K] in
lemma weightProj_of_mem (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) {κ : Dual K H} {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) κ) : weightProj P hV κ v = ⟨v, hv⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hv

omit [CharZero K] in
lemma weightProj_of_mem_ne (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) {κ ν : Dual K H} {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) ν) (hν : ν ≠ κ) : weightProj P hV κ v = 0 :=
  (Submodule.projectionOnto_apply_eq_zero_iff _).mpr (Submodule.mem_iSup_of_mem ν
    (Submodule.mem_iSup_of_mem hν hv))

/-- A functional on `V_κ`, extended by zero on the other weight spaces, has weight `κ`. -/
theorem mem_weightSpace_twistedDual_comp (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (κ : Dual K H) (g : Module.Dual K (weightSpaceOfMap V (h P) κ)) :
    (TwistedDual.toDual P V).symm (g ∘ₗ weightProj P hV κ) ∈
      weightSpaceOfMap (TwistedDual P V) (h P) κ := by
  rw [TwistedDual.mem_weightSpaceOfMap_iff]
  intro a v
  simp only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
  have hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := hV ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem ν v hv =>
    by_cases hν : ν = κ
    · subst hν
      have hhv : ⁅h P a, v⁆ ∈ weightSpaceOfMap V (h P) ν := by
        rw [hv a]; exact Submodule.smul_mem _ _ hv
      rw [weightProj_of_mem hV hhv, weightProj_of_mem hV hv]
      have : (⟨⁅h P a, v⁆, hhv⟩ : weightSpaceOfMap V (h P) ν) = ν a • ⟨v, hv⟩ :=
        Subtype.ext (hv a)
      rw [this, map_smul, smul_eq_mul]
    · have hhv : ⁅h P a, v⁆ ∈ weightSpaceOfMap V (h P) ν := (hv a).symm ▸
        Submodule.smul_mem _ _ hv
      rw [weightProj_of_mem_ne hV hhv hν, weightProj_of_mem_ne hV hv hν, map_zero, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [lie_add, map_add, map_add, hx, hy, map_add, map_add, mul_add]

/-- A functional of weight `κ` vanishing on `V_κ` is zero. -/
theorem eq_zero_of_mem_weightSpace_twistedDual (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    {κ : Dual K H} {φ : TwistedDual P V} (hφ : φ ∈ weightSpaceOfMap (TwistedDual P V) (h P) κ)
    (h0 : ∀ v ∈ weightSpaceOfMap V (h P) κ, TwistedDual.toDual P V φ v = 0) : φ = 0 := by
  apply TwistedDual.ext
  intro v
  have hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := hV ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem ν v hv =>
    by_cases hν : ν = κ
    · subst hν; simpa using h0 v hv
    · simpa using TwistedDual.apply_eq_zero_of_ne hφ hv (Ne.symm hν)
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

end Weight

section Dual

variable {P}

/-- Restriction identifies the weight-`κ` functionals with the dual of `V_κ`. -/
def weightSpaceTwistedDualEquiv (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) (κ : Dual K H) :
    weightSpaceOfMap (TwistedDual P V) (h P) κ ≃ₗ[K]
      Module.Dual K (weightSpaceOfMap V (h P) κ) where
  toFun φ := TwistedDual.toDual P V φ.1 ∘ₗ (weightSpaceOfMap V (h P) κ).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨_, mem_weightSpace_twistedDual_comp hV κ g⟩
  left_inv φ := by
    refine Subtype.ext ?_
    have hmem : (TwistedDual.toDual P V).symm ((TwistedDual.toDual P V φ.1 ∘ₗ
        (weightSpaceOfMap V (h P) κ).subtype) ∘ₗ weightProj P hV κ) - φ.1 ∈
          weightSpaceOfMap (TwistedDual P V) (h P) κ :=
      Submodule.sub_mem _ (mem_weightSpace_twistedDual_comp hV κ _) φ.2
    refine sub_eq_zero.mp (eq_zero_of_mem_weightSpace_twistedDual hV hmem fun v hv ↦ ?_)
    simp [weightProj_of_mem hV hv]
  right_inv g := by
    ext ⟨v, hv⟩
    simp [weightProj_of_mem hV hv]

theorem finrank_weightSpace_twistedDual (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (κ : Dual K H) [FiniteDimensional K (weightSpaceOfMap V (h P) κ)] :
    finrank K (weightSpaceOfMap (TwistedDual P V) (h P) κ) =
      finrank K (weightSpaceOfMap V (h P) κ) :=
  (weightSpaceTwistedDualEquiv hV κ).finrank_eq.trans (Subspace.dual_finrank_eq)

/-- The weight spaces of `V^∨` are those of the twisted dual. -/
def weightSpaceRestrictedDualEquiv (κ : Dual K H) :
    weightSpaceOfMap (restrictedDual P V) (h P) κ ≃ₗ[K]
      weightSpaceOfMap (TwistedDual P V) (h P) κ where
  toFun φ := ⟨φ.1.1, mem_weightSpaceOfMap_lieSubmodule_iff.mp φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := ⟨⟨φ.1, Submodule.mem_iSup_of_mem κ φ.2⟩,
    mem_weightSpaceOfMap_lieSubmodule_iff.mpr φ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`V^∨ ∈ 𝒪`** for `V ∈ 𝒪` (Humphreys, GSM 94, §3.2). -/
theorem isCategoryO_restrictedDual (hV : IsCategoryO P V) :
    IsCategoryO P (restrictedDual P V) := by
  have hd := hV.iSup_weightSpaceOfMap_eq_top
  refine ⟨?_, fun μ ↦ ?_, ?_⟩
  · rw [eq_top_iff]
    rintro ⟨φ, hφ⟩ -
    have key : ∀ ψ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P V) (h P) μ,
        ∀ hψ : ψ ∈ restrictedDual P V,
        (⟨ψ, hψ⟩ : restrictedDual P V) ∈ ⨆ μ, weightSpaceOfMap (restrictedDual P V) (h P) μ := by
      intro ψ hψ
      induction hψ using Submodule.iSup_induction' with
      | mem μ ψ hψ =>
        intro h'
        exact Submodule.mem_iSup_of_mem μ (mem_weightSpaceOfMap_lieSubmodule_iff.mpr hψ)
      | zero => intro _; exact zero_mem _
      | add x y hx hy ihx ihy =>
        intro _
        exact add_mem (ihx hx) (ihy hy)
    exact key φ hφ hφ
  · have := hV.finiteDimensional_weightSpaceOfMap μ
    have : FiniteDimensional K (weightSpaceOfMap (TwistedDual P V) (h P) μ) :=
      LinearEquiv.finiteDimensional (weightSpaceTwistedDualEquiv hd μ).symm
    exact LinearEquiv.finiteDimensional (weightSpaceRestrictedDualEquiv μ).symm
  · obtain ⟨s, hs⟩ := hV.exists_finset
    refine ⟨s, fun μ hμ ↦ hs μ fun h0 ↦ hμ ?_⟩
    have : Subsingleton (Module.Dual K (weightSpaceOfMap V (h P) μ)) := by
      rw [h0]; infer_instance
    have := ((weightSpaceRestrictedDualEquiv μ).trans
      (weightSpaceTwistedDualEquiv hd μ)).toEquiv.subsingleton
    exact (Submodule.eq_bot_iff _).mpr fun x hx ↦ by
      simpa using congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ :
        weightSpaceOfMap (restrictedDual P V) (h P) μ) 0)

theorem finrank_weightSpace_restrictedDual (hV : IsCategoryO P V) (μ : Dual K H) :
    finrank K (weightSpaceOfMap (restrictedDual P V) (h P) μ) =
      finrank K (weightSpaceOfMap V (h P) μ) := by
  have := hV.finiteDimensional_weightSpaceOfMap μ
  rw [(weightSpaceRestrictedDualEquiv μ).finrank_eq,
    finrank_weightSpace_twistedDual hV.iSup_weightSpaceOfMap_eq_top μ]

/-- `V^∨` has the same composition multiplicities as `V` (Humphreys, GSM 94, §3.2: equal
characters). -/
theorem multiplicity_restrictedDual (hV : IsCategoryO P V) (μ : Dual K H) :
    (isCategoryO_restrictedDual hV).multiplicity μ = hV.multiplicity μ := by
  refine (IsCategoryO.character_eq_iff (isCategoryO_restrictedDual hV) hV).mp ?_ μ
  ext ν
  simp only [IsCategoryO.coeffAt_character]
  rw [finrank_weightSpace_restrictedDual hV]

end Dual

section Primitive

variable {P}

/-- `⁅eᵢ, φ⁆ = φ ∘ fᵢ` on the twisted dual. -/
lemma toDual_lie_e (i : ι) (φ : TwistedDual P V) (v : V) :
    TwistedDual.toDual P V ⁅e P i, φ⁆ v = TwistedDual.toDual P V φ ⁅f P i, v⁆ := by
  rw [TwistedDual.lie_apply, transpose_e]

/-- **The primitive vectors of `V^∨`** of weight `μ` are the functionals on `V_μ` killing
`(𝔫₋V)_μ`: `dim Hom(M(μ), V^∨) = dim (V / 𝔫₋V)_μ`. -/
theorem finrank_primitiveVectors_restrictedDual (hV : IsCategoryO P V) (μ : Dual K H) :
    finrank K (primitiveVectors P (restrictedDual P V) μ) =
      coinvDim P (⊤ : LieSubmodule K 𝔤 V) μ := by
  have hd := hV.iSup_weightSpaceOfMap_eq_top
  have := hV.finiteDimensional_weightSpaceOfMap μ
  set Wμ := weightSpaceOfMap V (h P) μ
  set S : Submodule K Wμ := (negSpan P (⊤ : Submodule K V)).comap Wμ.subtype
  let Θ : primitiveVectors P (restrictedDual P V) μ →ₗ[K] Module.Dual K Wμ :=
    (weightSpaceTwistedDualEquiv hd μ).toLinearMap ∘ₗ
      (weightSpaceRestrictedDualEquiv μ).toLinearMap ∘ₗ
        Submodule.inclusion (inf_le_left : primitiveVectors P (restrictedDual P V) μ ≤
          weightSpaceOfMap (restrictedDual P V) (h P) μ)
  have hΘ : Function.Injective Θ := by
    refine ((weightSpaceTwistedDualEquiv hd μ).injective.comp
      (weightSpaceRestrictedDualEquiv μ).injective).comp (Submodule.inclusion_injective _)
  have hrange : LinearMap.range Θ = S.dualAnnihilator := by
    ext g
    constructor
    · rintro ⟨φ, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      rintro ⟨s, hsμ⟩ hs
      change TwistedDual.toDual P V φ.1.1 s = 0
      have hprim := (mem_primitiveVectors.mp φ.2).2
      refine negSpan_induction P (p := fun x ↦ TwistedDual.toDual P V φ.1.1 x = 0)
        (fun i n _ ↦ ?_) (map_zero _) (fun x y hx hy ↦ by rw [map_add, hx, hy, add_zero]) hs
      rw [← toDual_lie_e]
      have := congrArg Subtype.val (hprim i)
      change ⁅e P i, φ.1.1⁆ = 0 at this
      rw [this, map_zero, LinearMap.zero_apply]
    · intro hg
      rw [Submodule.mem_dualAnnihilator] at hg
      set ψ := (TwistedDual.toDual P V).symm (g ∘ₗ weightProj P hd μ)
      have hψ : ψ ∈ weightSpaceOfMap (TwistedDual P V) (h P) μ :=
        mem_weightSpace_twistedDual_comp hd μ g
      let ψ' : restrictedDual P V := ⟨ψ, Submodule.mem_iSup_of_mem μ hψ⟩
      have hψ'w : ψ' ∈ weightSpaceOfMap (restrictedDual P V) (h P) μ :=
        mem_weightSpaceOfMap_lieSubmodule_iff.mpr hψ
      have hψ'e (i : ι) : ⁅e P i, ψ'⁆ = 0 := by
        refine Subtype.ext (TwistedDual.ext fun v ↦ ?_)
        change TwistedDual.toDual P V ⁅e P i, ψ⁆ v = TwistedDual.toDual P V 0 v
        rw [toDual_lie_e, map_zero, LinearMap.zero_apply]
        simp only [ψ, LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
        have hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := hd ▸ Submodule.mem_top
        induction hv using Submodule.iSup_induction' with
        | mem ν v hv =>
          have hfv := toEnd_f_mem_weightSpace i hv
          by_cases hν : ν - P.root i = μ
          · subst hν
            rw [show ⁅f P i, v⁆ = toEnd K 𝔤 V (f P i) v from rfl, weightProj_of_mem hd hfv]
            exact hg _ (toEnd_f_mem_negSpan P i Submodule.mem_top)
          · rw [show ⁅f P i, v⁆ = toEnd K 𝔤 V (f P i) v from rfl,
              weightProj_of_mem_ne hd hfv hν, map_zero]
        | zero => simp
        | add x y _ _ hx hy => rw [lie_add, map_add, map_add, hx, hy, add_zero]
      refine ⟨⟨ψ', mem_primitiveVectors.mpr ⟨hψ'w, hψ'e⟩⟩, ?_⟩
      exact (weightSpaceTwistedDualEquiv hd μ).apply_symm_apply g
  rw [← LinearMap.finrank_range_of_inj hΘ, hrange]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have h2 : finrank K S = finrank K ↥(negSpan P (⊤ : Submodule K V) ⊓ Wμ) := by
    rw [← Submodule.finrank_map_subtype_eq Wμ S, Submodule.map_comap_subtype, inf_comm]
  have h3 : finrank K ↥((⊤ : LieSubmodule K 𝔤 V).toSubmodule ⊓ Wμ) = finrank K Wμ :=
    (LinearEquiv.ofEq _ _ (by simp)).finrank_eq
  have h4 : finrank K ↥(negSpan P (⊤ : Submodule K V) ⊓ Wμ) =
      finrank K ↥(negSpan P (⊤ : Submodule K V) ⊓ weightSpaceOfMap V (h P) μ) := rfl
  have h5 : finrank K Wμ = finrank K (weightSpaceOfMap V (h P) μ) := rfl
  unfold coinvDim
  rw [h3, LieSubmodule.top_toSubmodule]
  omega

end Primitive

section Swap

variable {P}

/-- The functional `a ↦ (f a)(b)` on `V`, for `f : V → W^∨` and `b ∈ W`, as a linear map. -/
def dualSwapLin (f : V →ₗ⁅K,𝔤⁆ restrictedDual P W) : W →ₗ[K] TwistedDual P V :=
  (TwistedDual.toDual P V).symm.toLinearMap ∘ₗ
    ((TwistedDual.toDual P W).toLinearMap ∘ₗ (restrictedDual P W).subtype ∘ₗ f.toLinearMap).flip

omit [LieModule K P.KacMoodyAlgebra V] in
lemma toDual_dualSwapLin (f : V →ₗ⁅K,𝔤⁆ restrictedDual P W) (b : W) (a : V) :
    TwistedDual.toDual P V (dualSwapLin f b) a = TwistedDual.toDual P W (f a).1 b := rfl

/-- The functional `a ↦ (f a)(b)` on `V`, for `f : V → W^∨` and `b ∈ W`. -/
def dualSwapAux (f : V →ₗ⁅K,𝔤⁆ restrictedDual P W) : W →ₗ⁅K,𝔤⁆ TwistedDual P V :=
  { dualSwapLin f with
    map_lie' := fun {x b} ↦ by
      apply (TwistedDual.toDual P V).injective
      ext a
      change TwistedDual.toDual P V (dualSwapLin f ⁅x, b⁆) a =
        TwistedDual.toDual P V ⁅x, dualSwapLin f b⁆ a
      rw [toDual_dualSwapLin, TwistedDual.lie_apply, toDual_dualSwapLin, LieModuleHom.map_lie,
        LieSubmodule.coe_bracket, TwistedDual.lie_apply, transpose_transpose] }

lemma toDual_dualSwapAux (f : V →ₗ⁅K,𝔤⁆ restrictedDual P W) (b : W) (a : V) :
    TwistedDual.toDual P V (dualSwapAux f b) a = TwistedDual.toDual P W (f a).1 b := rfl

lemma dualSwapAux_mem (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤)
    (f : V →ₗ⁅K,𝔤⁆ restrictedDual P W) (b : W) : dualSwapAux f b ∈ restrictedDual P V := by
  have hb : b ∈ ⨆ μ, weightSpaceOfMap W (h P) μ := hW ▸ Submodule.mem_top
  induction hb using Submodule.iSup_induction' with
  | mem κ b hb =>
    refine Submodule.mem_iSup_of_mem κ (TwistedDual.mem_weightSpaceOfMap_iff.mpr fun a' v ↦ ?_)
    rw [toDual_dualSwapAux, toDual_dualSwapAux, LieModuleHom.map_lie, LieSubmodule.coe_bracket,
      TwistedDual.lie_apply, transpose_h, hb a', map_smul, smul_eq_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy

/-- **The swap `Hom(V, W^∨) → Hom(W, V^∨)`**, `f ↦ (b ↦ (a ↦ (f a)(b)))`: both sides are the
contravariant pairings `V × W → K`. -/
def dualSwap (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤) :
    (V →ₗ⁅K,𝔤⁆ restrictedDual P W) →ₗ[K] (W →ₗ⁅K,𝔤⁆ restrictedDual P V) where
  toFun f := LieModuleHom.codRestrict _ (dualSwapAux f) (dualSwapAux_mem hW f)
  map_add' f g := by
    ext b a
    simp [toDual_dualSwapAux]
  map_smul' c f := by
    ext b a
    simp [toDual_dualSwapAux]

lemma dualSwap_injective (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤) :
    Function.Injective (dualSwap (V := V) hW) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_bot]
  ext a b
  have := congrArg (fun g : W →ₗ⁅K,𝔤⁆ restrictedDual P V ↦ TwistedDual.toDual P V (g b).1 a) hf
  simpa [dualSwap, toDual_dualSwapAux] using this

/-- **Frobenius reciprocity for dual Verma modules**: `dim Hom(V, M(μ)^∨) = dim (V / 𝔫₋V)_μ` for
`V ∈ 𝒪`. -/
theorem finrank_hom_restrictedDual_verma (hV : IsCategoryO P V) (μ : Dual K H) :
    finrank K (V →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P μ)) =
      coinvDim P (⊤ : LieSubmodule K 𝔤 V) μ := by
  have hM := (VermaModule.isCategoryO P μ).iSup_weightSpaceOfMap_eq_top
  have hd := hV.iSup_weightSpaceOfMap_eq_top
  have hR := isCategoryO_restrictedDual hV
  have := hR.finiteDimensional_weightSpaceOfMap μ
  have : FiniteDimensional K (primitiveVectors P (restrictedDual P V) μ) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have : FiniteDimensional K (VermaModule P μ →ₗ⁅K,𝔤⁆ restrictedDual P V) :=
    LinearEquiv.finiteDimensional (homEquiv P _ μ).symm
  have : FiniteDimensional K (V →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P μ)) :=
    Module.Finite.of_injective _ (dualSwap_injective hM)
  have h1 := LinearMap.finrank_le_finrank_of_injective (dualSwap_injective (V := V) hM)
  have h2 := LinearMap.finrank_le_finrank_of_injective
    (dualSwap_injective (V := VermaModule P μ) (W := V) hd)
  rw [← finrank_primitiveVectors_restrictedDual hV, ← (homEquiv P _ μ).finrank_eq]
  omega

/-- **Humphreys, GSM 94, Theorem 3.7.** If `V ∈ 𝒪` has a standard filtration with weights `s`,
then the multiplicity of `M(μ)` in it is `dim Hom(V, M(μ)^∨)`. (Humphreys uses
`Ext¹_𝒪(M(ν), M(μ)^∨) = 0`; here it is the coinvariant form `IsStdFiltered.count_eq_coinvDim`
together with `finrank_hom_restrictedDual_verma`.) -/
theorem IsStdFiltered.count_eq_finrank_hom [DecidableEq (Dual K H)] (hV : IsCategoryO P V)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 V) s) (μ : Dual K H) :
    s.count μ = finrank K (V →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P μ)) := by
  rw [finrank_hom_restrictedDual_verma hV, hs.count_eq_coinvDim P hV]

end Swap

end Matrix.Realization.KacMoodyAlgebra
