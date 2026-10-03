/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.FiniteConverse
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.Interior
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Interior points of the Tits cone have finite stabilizers

## Main results

* `Matrix.Realization.finite_stabilizer_of_mem_interior_titsCone`.

## References

Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 3.12(f).
The proof is our own. A negative perturbation
by `rho` bounds the coroots vanishing at the point. The stabilizer injects into tuples
of these coroots: injectivity is proved on the entire dual using chamber uniqueness
and a small strictly dominant perturbation, not assumed on a smaller span.
-/

open Module Filter Topology

namespace Matrix.Realization

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  [FiniteDimensional ℝ H] [TopologicalSpace (Dual ℝ H)]
  [IsTopologicalAddGroup (Dual ℝ H)] [ContinuousSMul ℝ (Dual ℝ H)]
  [T2Space (Dual ℝ H)] {A : Matrix ι ι ℤ} (P : Realization A ℝ H)
  (hA : A.IsGeneralizedCartan)

omit [FiniteDimensional ℝ H] [T2Space (Dual ℝ H)] in
private lemma exists_pos_add_smul_mem {s : Set (Dual ℝ H)} {μ : Dual ℝ H}
    (hμ : μ ∈ interior s) (ν : Dual ℝ H) : ∃ t : ℝ, 0 < t ∧ μ + t • ν ∈ s := by
  have hc : Continuous (fun t : ℝ ↦ μ + t • ν) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), μ + t • ν ∈ s := by
    exact hc.continuousAt (by simpa using mem_interior_iff_mem_nhds.mp hμ)
  have he' : ∀ᶠ t in 𝓝[>] (0 : ℝ), μ + t • ν ∈ s :=
    he.filter_mono nhdsWithin_le_nhds
  exact (he'.and self_mem_nhdsWithin).exists.imp fun t ht ↦ ⟨ht.2, ht.1⟩

omit [FiniteDimensional ℝ H] [T2Space (Dual ℝ H)] in
/-- An interior point annihilates only finitely many positive real coroots.
This perturbation step for Kac, third edition, Proposition 3.12(f), is reconstructed. -/
lemma finite_posRealCoroots_zero_of_mem_interior {μ : Dual ℝ H}
    (hμ : μ ∈ interior (P.titsCone hA)) :
    {x | x ∈ P.posRealCoroots hA ∧ μ x = 0}.Finite := by
  obtain ⟨t, ht, hν⟩ := exists_pos_add_smul_mem hμ (-P.rho)
  refine (P.finite_of_mem_titsCone hA hν).subset fun x hx ↦ ⟨hx.1, ?_⟩
  have hp := P.rho_pos_of_mem_posRealCoroots hA hx.1
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, hx.2,
    zero_add, smul_eq_mul]
  exact mul_neg_of_pos_of_neg ht (neg_neg_of_pos hp)

omit [FiniteDimensional ℝ H] [T2Space (Dual ℝ H)] in
/-- An interior point annihilates only finitely many real coroots, by the sign
alternative. This is a reconstructed step for Kac, third edition, Proposition 3.12(f). -/
lemma finite_realCoroots_zero_of_mem_interior {μ : Dual ℝ H}
    (hμ : μ ∈ interior (P.titsCone hA)) :
    {x | x ∈ P.realCoroots hA ∧ μ x = 0}.Finite := by
  have hf := P.finite_posRealCoroots_zero_of_mem_interior hA hμ
  refine (hf.union (hf.image fun x ↦ -x)).subset fun x hx ↦ ?_
  rcases P.mem_posRealCoroots_or_neg_mem hA hx.1 with hp | hn
  · exact Or.inl ⟨hp, hx.2⟩
  · exact Or.inr ⟨-x, ⟨hn, by simp [hx.2]⟩, neg_neg x⟩

/-- A chamber stabilizer element whose action on `rho` is positive on the zero
walls is the identity. The perturbation proves identity on the entire dual space. -/
lemma eq_one_of_stabilizes_of_pos_on_zero_walls {μ : Dual ℝ H}
    (hμ : μ ∈ P.dominantChamber) {w : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H}
    (hw : w ∈ P.weylGroup hA) (hfix : w μ = μ)
    (hzero : ∀ i, μ (P.coroot i) = 0 → 0 < w P.rho (P.coroot i)) : w = 1 := by
  classical
  let U : Set (Dual ℝ H) := {ν | ∀ i : {i // μ (P.coroot i) ≠ 0},
    0 < ν (P.coroot i.val)}
  have hU : IsOpen U := by
    change IsOpen {ν : Dual ℝ H | ∀ i : {i // μ (P.coroot i) ≠ 0},
      0 < ν (P.coroot i.val)}
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const
      (LinearMap.continuous_of_finiteDimensional (Dual.eval ℝ H (P.coroot i.val)))
  have hμU : μ ∈ U := fun i ↦ lt_of_le_of_ne (hμ i.val) (Ne.symm i.property)
  obtain ⟨t, ht, htU⟩ := exists_pos_add_smul_mem (hU.interior_eq.symm ▸ hμU) (w P.rho)
  have hpos : ∀ i, 0 < (μ + t • P.rho) (P.coroot i) := by
    intro i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, rho_coroot, smul_eq_mul, mul_one]
    exact add_pos_of_nonneg_of_pos (hμ i) ht
  have hdom : w (μ + t • P.rho) ∈ P.dominantChamber := by
    intro i
    rw [map_add, map_smul, hfix]
    by_cases hi : μ (P.coroot i) = 0
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, hi, zero_add, smul_eq_mul]
      exact (mul_pos ht (hzero i hi)).le
    · exact (htU ⟨i, hi⟩).le
  exact P.eq_one_of_apply_eq_self_of_forall_pos hA hpos hw
    (P.apply_eq_self_of_mem_dominantChamber hA (fun i ↦ (hpos i).le) hw hdom)

/-- Finite vanishing real coroots imply a finite actual Weyl stabilizer at a dominant
point. Tuple injectivity is proved, rather than assuming faithfulness on their span. -/
theorem finite_stabilizer_of_dominant_of_finite_zero_realCoroots {μ : Dual ℝ H}
    (hμ : μ ∈ P.dominantChamber)
    (hf : {x | x ∈ P.realCoroots hA ∧ μ x = 0}.Finite) :
    Finite (MulAction.stabilizer (P.weylGroup hA) μ) := by
  classical
  let S := MulAction.stabilizer (P.weylGroup hA) μ
  let Z := {x | x ∈ P.realCoroots hA ∧ μ x = 0}
  let _ := hf.fintype
  choose u hu hpair using fun w : S ↦ P.exists_coweylGroup_apply_apply hA w.val.property
  have hfix (w : S) : w.val.val μ = μ := w.property
  let f : S → ({i // μ (P.coroot i) = 0} → Z) := fun w i ↦
    ⟨u w (P.coroot i.val), P.apply_mem_realCoroots hA (hu w)
      (P.coroot_mem_realCoroots hA i.val), by rw [← hpair, hfix]; exact i.property⟩
  apply Finite.of_injective f
  intro w v heq
  have hcoroot (i : ι) (hi : μ (P.coroot i) = 0) :
      u w (P.coroot i) = u v (P.coroot i) :=
    congrArg Subtype.val (congrFun heq ⟨i, hi⟩)
  have hqfix : (v.val.val * w.val.val⁻¹) μ = μ := by
    change v.val.val (w.val.val⁻¹ μ) = μ
    rw [show w.val.val⁻¹ μ = μ from (w.val.val.symm_apply_eq.mpr (hfix w).symm), hfix]
  have hone : v.val.val * w.val.val⁻¹ = 1 :=
    P.eq_one_of_stabilizes_of_pos_on_zero_walls hA hμ
      (mul_mem v.val.property (inv_mem w.val.property)) hqfix (by
        intro i hi
        change 0 < v.val.val (w.val.val⁻¹ P.rho) (P.coroot i)
        rw [hpair v, ← hcoroot i hi, ← hpair w]
        simp)
  exact Subtype.ext (Subtype.ext (mul_inv_eq_one.mp hone).symm)

/-- An interior point of the actual Tits cone has finite actual Weyl stabilizer.
This is Kac, third edition, Proposition 3.12(f), in the dual-space convention, with
finite-dimensional Hausdorff real vector-space topology. The proof is reconstructed. -/
theorem finite_stabilizer_of_mem_interior_titsCone {μ : Dual ℝ H}
    (hμ : μ ∈ interior (P.titsCone hA)) :
    Finite (MulAction.stabilizer (P.weylGroup hA) μ) := by
  obtain ⟨v, hv, ν, hν, rfl⟩ := interior_subset hμ
  have himage : v.symm '' P.titsCone hA ⊆ P.titsCone hA := by
    rintro _ ⟨x, hx, rfl⟩
    exact P.apply_mem_titsCone hA (inv_mem hv) hx
  have hνint : ν ∈ interior (P.titsCone hA) := by
    have h : v.symm (v ν) ∈ interior (v.symm '' P.titsCone hA) := by
      change v.symm (v ν) ∈ interior
        (v.symm.toContinuousLinearEquiv.toHomeomorph '' P.titsCone hA)
      rw [← v.symm.toContinuousLinearEquiv.toHomeomorph.image_interior]
      exact ⟨v ν, hμ, rfl⟩
    simpa using interior_mono himage h
  let _ := P.finite_stabilizer_of_dominant_of_finite_zero_realCoroots hA hν
    (P.finite_realCoroots_zero_of_mem_interior hA hνint)
  let w : P.weylGroup hA := ⟨v, hv⟩
  let e := MulAction.stabilizerEquivStabilizer (G := P.weylGroup hA)
    (g := w) (a := ν) (b := v ν) rfl
  exact Finite.of_injective e.symm e.symm.injective

/-- For a point of the actual Tits cone, interior membership is equivalent to finite
actual Weyl stabilizer. Kac, third edition, Proposition 3.12(f), reconstructed. -/
theorem mem_interior_titsCone_iff_finite_stabilizer {μ : Dual ℝ H}
    (hμ : μ ∈ P.titsCone hA) :
    μ ∈ interior (P.titsCone hA) ↔ Finite (MulAction.stabilizer (P.weylGroup hA) μ) := by
  constructor
  · exact P.finite_stabilizer_of_mem_interior_titsCone hA
  · intro hf
    let _ := hf
    exact P.mem_interior_titsCone_of_finite_stabilizer hA hμ

end Matrix.Realization
