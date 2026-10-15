/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.DirectSumUniqueness

/-!
# Automorphisms of `⊕ⱼ V(λⱼ)` and projections onto summands

Let `M = ⊕ⱼ V(λⱼ)` with `V(λ) = L_q(λ)`. This file collects the linear algebra of `M` used in the
uniqueness theorem for crystal bases ([HK] Thm. 5.2.1).

* `IrreducibleModule.hom_ext_hwv`: `U`-linear maps out of `L_q(Λ)` agreeing on `v_Λ` are equal.
* `GrandLoop.projDS`: the projection of `M` onto the summands with indices in a set, which
  commutes with the `ẽᵢ`, `f̃ᵢ` (`GrandLoop.eDS_projDS`, `GrandLoop.fDS_projDS`).
* `GrandLoop.hwSpan v Λ T`: the `k`-span of the highest weight vectors `v_{λⱼ}`, `j ∈ T`.
* `GrandLoop.autEquiv`: for `T` finite with `λⱼ = μ` for all `j ∈ T`, every `k`-linear automorphism
  `g` of `hwSpan v Λ T` extends to a `U`-linear automorphism of `M` which is the identity on the
  other summands (`GrandLoop.autMap_eq`, `GrandLoop.autMap_single_of_notMem`). It is defined
  summandwise by the universal property of `L_q(μ)`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.2.
-/

open Pointwise

noncomputable section

namespace LieLean.QuantumGroup

namespace IrreducibleModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} {Λ : Y →+ ℤ}

/-- Every vector of `L_q(Λ)` is `u v_Λ` for some `u ∈ U`. -/
lemma exists_smul_hwv_eq (x : IrreducibleModule R v Λ) :
    ∃ u : QuantumGroup R v, u • hwv R v Λ = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨u, ?_⟩
  rw [hwv, ← Submodule.Quotient.mk_smul, ← VermaModule.mk_eq_smul_hwv]

/-- `U`-linear maps out of `L_q(Λ)` agreeing on `v_Λ` are equal. -/
lemma hom_ext_hwv {N : Type*} [AddCommGroup N] [Module (QuantumGroup R v) N]
    {f g : IrreducibleModule R v Λ →ₗ[QuantumGroup R v] N}
    (h : f (hwv R v Λ) = g (hwv R v Λ)) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨u, rfl⟩ := exists_smul_hwv_eq x
  rw [map_smul, map_smul, h]

end IrreducibleModule

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {J : Type*} (Λ : J → Dom R)

omit [NeZero v] [CharZero k] in
/-- `U`-linear maps out of `⊕ⱼ V(λⱼ)` agreeing on the highest weight vectors are equal. -/
lemma ds_hom_ext [DecidableEq J] {N : Type*} [AddCommGroup N] [Module (QuantumGroup R v) N]
    {f g : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v] N}
    (h : ∀ j, f (DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1)) =
      g (DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1))) : f = g :=
  DFinsupp.lhom_ext' fun j ↦ IrreducibleModule.hom_ext_hwv (h j)

/-! ### Projections onto summands -/

section Proj

variable (p : J → Prop) [DecidablePred p]

/-- The projection of `⊕ⱼ V(λⱼ)` onto the summands with indices in `p`. -/
abbrev projDS : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v]
    Π₀ j, IrreducibleModule R v (Λ j).1 :=
  DFinsupp.filterLinearMap (QuantumGroup R v) (fun j ↦ IrreducibleModule R v (Λ j).1) p

omit [NeZero v] [CharZero k] in
lemma projDS_apply (x : Π₀ j, IrreducibleModule R v (Λ j).1) (j : J) :
    projDS Λ p x j = if p j then x j else 0 :=
  DFinsupp.filter_apply p j x

omit [NeZero v] [CharZero k] in
lemma projDS_add_projDS_not (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    projDS Λ p x + projDS Λ (fun j ↦ ¬p j) x = x :=
  DFinsupp.filter_add_filter_not x p

lemma eDS_projDS (i : I) (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    eDS hvt hR Λ i (projDS Λ p x) = projDS Λ p (eDS hvt hR Λ i x) := by
  ext j
  rw [eDS_apply, projDS_apply, projDS_apply, eDS_apply]
  split_ifs
  · rfl
  · exact map_zero _

lemma fDS_projDS (i : I) (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    fDS hvt hR Λ i (projDS Λ p x) = projDS Λ p (fDS hvt hR Λ i x) := by
  ext j
  rw [fDS_apply, projDS_apply, projDS_apply, fDS_apply]
  split_ifs
  · rfl
  · exact map_zero _

end Proj

/-! ### The span of the highest weight vectors -/

section HwSpan

variable [DecidableEq J] (T : Finset J)

variable (v) in
/-- The `k`-span of the highest weight vectors of the summands with indices in `T`. -/
abbrev hwSpan : Submodule k (Π₀ j, IrreducibleModule R v (Λ j).1) :=
  Submodule.span k ((fun j ↦ DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1)) '' ↑T)

variable {Λ T}

omit [NeZero v] [CharZero k] in
lemma single_hwv_mem_hwSpan {j : J} (hj : j ∈ T) :
    DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1) ∈ hwSpan v Λ T :=
  Submodule.subset_span (Set.mem_image_of_mem _ hj)

omit [NeZero v] [CharZero k] in
lemma apply_eq_zero_of_mem_hwSpan {x : Π₀ j, IrreducibleModule R v (Λ j).1}
    (hx : x ∈ hwSpan v Λ T) {j : J} (hj : j ∉ T) : x j = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact DFinsupp.single_eq_of_ne fun h ↦ hj (h ▸ hl)
  | zero => rfl
  | add a b _ _ ha hb => rw [DFinsupp.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [DFinsupp.smul_apply, ha, smul_zero]

omit [NeZero v] [CharZero k] in
lemma mem_weightSpace_of_mem_hwSpan {μ : Y →+ ℤ} (hT : ∀ j ∈ T, (Λ j).1 = μ)
    {x : Π₀ j, IrreducibleModule R v (Λ j).1} (hx : x ∈ hwSpan v Λ T) :
    x ∈ weightSpace R v _ μ := by
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, ← hT j hj]
  exact map_mem_weightSpace (DFinsupp.lsingle (R := QuantumGroup R v)
    (M := fun j ↦ IrreducibleModule R v (Λ j).1) j)
    (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := (Λ j).1))

omit [NeZero v] [CharZero k] in
lemma E_smul_eq_zero_of_mem_hwSpan {x : Π₀ j, IrreducibleModule R v (Λ j).1}
    (hx : x ∈ hwSpan v Λ T) (i : I) : E R v i • x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, -, rfl⟩ := hx
    rw [← DFinsupp.single_smul, IrreducibleModule.E_smul_hwv, DFinsupp.single_zero]
  | zero => exact smul_zero _
  | add a b _ _ ha hb =>
    rw [show E R v i • (a + b) = E R v i • a + E R v i • b from smul_add (E R v i) a b, ha, hb,
      add_zero]
  | smul c a _ ha =>
    rw [show E R v i • (c • a) = c • E R v i • a from smul_comm (E R v i) c a, ha, smul_zero]

omit [NeZero v] [CharZero k] in
lemma projDS_eq_self_of_mem_hwSpan (p : J → Prop) [DecidablePred p] (hp : ∀ j ∈ T, p j)
    {x : Π₀ j, IrreducibleModule R v (Λ j).1} (hx : x ∈ hwSpan v Λ T) : projDS Λ p x = x := by
  ext j
  rw [projDS_apply]
  split_ifs with h
  · rfl
  · exact (apply_eq_zero_of_mem_hwSpan hx fun hj ↦ h (hp j hj)).symm

end HwSpan

/-! ### Automorphisms -/

section Aut

variable [Finite I] [DecidableEq J] {T : Finset J} {μ : Y →+ ℤ} (hT : ∀ j ∈ T, (Λ j).1 = μ)

variable (hvt hR) in
/-- The `U`-linear endomorphism of `⊕ⱼ V(λⱼ)` which is the identity on the summands outside `T`
and maps `v_{λⱼ}` to `g(v_{λⱼ})` for `j ∈ T`, for a `k`-linear endomorphism `g` of `hwSpan v Λ T`
(defined by the universal property of `L_q(μ)`). -/
def autMap (g : hwSpan v Λ T →ₗ[k] hwSpan v Λ T) :
    (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1 :=
  DFinsupp.lsum ℕ fun j ↦ if hj : j ∈ T then
      IrreducibleModule.lift hvt hR (pow_ne_one_of_transcendental' hvt) (Λ j).2
        (isIntDS hvt hR Λ) (g ⟨_, single_hwv_mem_hwSpan hj⟩ : Π₀ l, IrreducibleModule R v (Λ l).1)
        (mem_weightSpace_of_mem_hwSpan (fun l hl ↦ (hT l hl).trans (hT j hj).symm) (g _).2)
        (fun i ↦ E_smul_eq_zero_of_mem_hwSpan (g _).2 i)
    else DFinsupp.lsingle (R := QuantumGroup R v) (M := fun j ↦ IrreducibleModule R v (Λ j).1) j

variable {Λ}

lemma autMap_single_hwv (g : hwSpan v Λ T →ₗ[k] hwSpan v Λ T) {j : J} (hj : j ∈ T) :
    autMap hvt hR Λ hT g (DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1)) =
      g ⟨_, single_hwv_mem_hwSpan hj⟩ := by
  rw [autMap, DFinsupp.lsum_single, dite_eq_left_of_eq_true (eq_true hj),
    IrreducibleModule.lift_hwv]

lemma autMap_single_of_notMem (g : hwSpan v Λ T →ₗ[k] hwSpan v Λ T) {j : J} (hj : j ∉ T)
    (y : IrreducibleModule R v (Λ j).1) :
    autMap hvt hR Λ hT g (DFinsupp.single j y) = DFinsupp.single j y := by
  rw [autMap, DFinsupp.lsum_single, dite_eq_right_of_eq_false (eq_false hj)]
  rfl

/-- `autMap g` extends `g`. -/
lemma autMap_eq (g : hwSpan v Λ T →ₗ[k] hwSpan v Λ T) {x : Π₀ j, IrreducibleModule R v (Λ j).1}
    (hx : x ∈ hwSpan v Λ T) : autMap hvt hR Λ hT g x = g ⟨x, hx⟩ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact autMap_single_hwv hT g hj
  | zero => rw [map_zero]; exact (congrArg Subtype.val (map_zero g)).symm
  | add a b ha hb iha ihb =>
    rw [map_add, iha, ihb]
    exact (congrArg Subtype.val (map_add g ⟨a, ha⟩ ⟨b, hb⟩)).symm
  | smul c a ha iha =>
    rw [LinearMap.map_smul_of_tower, iha]
    exact (congrArg Subtype.val (map_smul g c ⟨a, ha⟩)).symm

lemma autMap_mem_hwSpan (g : hwSpan v Λ T →ₗ[k] hwSpan v Λ T)
    {x : Π₀ j, IrreducibleModule R v (Λ j).1} (hx : x ∈ hwSpan v Λ T) :
    autMap hvt hR Λ hT g x ∈ hwSpan v Λ T := by
  rw [autMap_eq hT g hx]
  exact (g _).2

lemma autMap_comp (g h : hwSpan v Λ T →ₗ[k] hwSpan v Λ T) :
    (autMap hvt hR Λ hT g).comp (autMap hvt hR Λ hT h) = autMap hvt hR Λ hT (g.comp h) := by
  refine ds_hom_ext Λ fun j ↦ ?_
  rw [LinearMap.comp_apply]
  by_cases hj : j ∈ T
  · rw [autMap_single_hwv hT h hj, autMap_eq hT g (h _).2, autMap_single_hwv hT _ hj]
    rfl
  · rw [autMap_single_of_notMem hT h hj, autMap_single_of_notMem hT g hj,
      autMap_single_of_notMem hT _ hj]

lemma autMap_id : autMap hvt hR Λ hT LinearMap.id = LinearMap.id := by
  refine ds_hom_ext Λ fun j ↦ ?_
  by_cases hj : j ∈ T
  · rw [autMap_single_hwv hT _ hj]
    rfl
  · rw [autMap_single_of_notMem hT _ hj]
    rfl

variable (hvt hR Λ) in
/-- The `U`-linear automorphism of `⊕ⱼ V(λⱼ)` extending a `k`-linear automorphism `g` of
`hwSpan v Λ T` by the identity on the summands outside `T`. -/
def autEquiv (g : hwSpan v Λ T ≃ₗ[k] hwSpan v Λ T) :
    (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1 :=
  LinearEquiv.ofLinearMap (autMap hvt hR Λ hT g.toLinearMap)
    (autMap hvt hR Λ hT g.symm.toLinearMap)
    (by rw [autMap_comp, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self]; exact autMap_id hT)
    (by rw [autMap_comp, ← LinearEquiv.coe_trans, LinearEquiv.self_trans_symm]; exact autMap_id hT)

lemma autEquiv_apply (g : hwSpan v Λ T ≃ₗ[k] hwSpan v Λ T)
    (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    autEquiv hvt hR Λ hT g x = autMap hvt hR Λ hT g.toLinearMap x :=
  rfl

lemma autEquiv_symm_apply (g : hwSpan v Λ T ≃ₗ[k] hwSpan v Λ T)
    (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    (autEquiv hvt hR Λ hT g).symm x = autMap hvt hR Λ hT g.symm.toLinearMap x :=
  rfl

/-- `autMap g` commutes with the projection onto a set of summands containing `T`. -/
lemma projDS_autMap (g : hwSpan v Λ T →ₗ[k] hwSpan v Λ T) (p : J → Prop) [DecidablePred p]
    (hp : ∀ j ∈ T, p j) (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    projDS Λ p (autMap hvt hR Λ hT g x) = autMap hvt hR Λ hT g (projDS Λ p x) := by
  suffices h : (projDS Λ p).comp (autMap hvt hR Λ hT g) = (autMap hvt hR Λ hT g).comp
      (projDS Λ p) from LinearMap.congr_fun h x
  refine ds_hom_ext Λ fun j ↦ ?_
  simp only [LinearMap.comp_apply, DFinsupp.filterLinearMap_apply, DFinsupp.filter_single]
  by_cases hj : j ∈ T
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hp j hj)), autMap_single_hwv hT g hj]
    exact projDS_eq_self_of_mem_hwSpan p hp (g _).2
  · rw [autMap_single_of_notMem hT g hj, DFinsupp.filter_single]
    split_ifs
    · rw [autMap_single_of_notMem hT g hj]
    · rw [map_zero]

/-- `autMap g` is the identity on the summands outside `T`. -/
lemma autMap_projDS_of_notMem (g : hwSpan v Λ T →ₗ[k] hwSpan v Λ T) (p : J → Prop) [DecidablePred p]
    (hp : ∀ j ∈ T, ¬p j) (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    autMap hvt hR Λ hT g (projDS Λ p x) = projDS Λ p x := by
  suffices h : (autMap hvt hR Λ hT g).comp (projDS Λ p) = projDS Λ p from
    LinearMap.congr_fun h x
  refine ds_hom_ext Λ fun j ↦ ?_
  simp only [LinearMap.comp_apply, DFinsupp.filterLinearMap_apply, DFinsupp.filter_single]
  split_ifs with h
  · rw [autMap_single_of_notMem hT g fun hj ↦ hp j hj h]
  · rw [map_zero]

end Aut

end GrandLoop

end LieLean.QuantumGroup
