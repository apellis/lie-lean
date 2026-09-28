/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TensorVermaStability
import LieLean.Algebra.Lie.KacMoody.TensorProduct
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Sort

/-!
# Finite weight-compatible Borel flags and tensor-Verma filtrations

## Main results

A finite-dimensional Cartan-diagonalizable module admits a basis ordered with higher
weights first. Its ordinary basis flag is Borel stable and its tensor-Verma pieces have
actual shifted-Verma factors, with multiplicities given by weight-space dimensions.

## References

The argument is reconstructed from the inspected weight-basis, reverse-root-order,
Mathlib basis-flag and tensor-Verma APIs. No external printed proof was consulted.
-/

open Module LieModule TensorProduct

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H Z : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  [AddCommGroup Z] [Module K Z]
  [LieRingModule P.KacMoodyAlgebra Z] [LieModule K P.KacMoodyAlgebra Z]

/-- A finite-dimensional weight module has a basis ordered by reverse root order.
Reconstructed by extending the strict weight order, breaking ties between basis indices.
No finite-type or algebraic-closure hypothesis is required. -/
theorem exists_weightOrderedBasis [FiniteDimensional K Z] (hZ : IsHDiagonalizable P Z) :
    ∃ (b : Basis (Fin (finrank K Z)) K Z) (wt : Fin (finrank K Z) → Dual K H),
      (∀ j, b j ∈ weightSpace P Z (wt j)) ∧
      ∀ i j, WeightOrd.toWeightOrd P (wt i) < WeightOrd.toWeightOrd P (wt j) → i < j := by
  classical
  let κ := DiagWeightBasisIndex P Z
  let b := diagWeightBasis hZ
  let : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  let w : κ → P.WeightOrd := fun j => WeightOrd.toWeightOrd P j.1
  let o : PartialOrder κ :=
    { le := fun i j => i = j ∨ w i < w j
      le_refl := fun _ => Or.inl rfl
      le_trans := by
        rintro i j k (rfl | hij) (rfl | hjk)
        · exact Or.inl rfl
        · exact Or.inr hjk
        · exact Or.inr hij
        · exact Or.inr (lt_trans hij hjk)
      le_antisymm := by
        rintro i j (hij | hij) (hji | hji)
        · exact hij
        · exact hij
        · exact hji.symm
        · exact (lt_asymm hij hji).elim }
  let : Fintype (LinearExtension κ) := inferInstanceAs (Fintype κ)
  have hc : Fintype.card (LinearExtension κ) = finrank K Z :=
    (Module.finrank_eq_card_basis b).symm
  let e := monoEquivOfFin (LinearExtension κ) hc
  let f : κ ≃ Fin (finrank K Z) :=
    (Equiv.refl κ).trans e.toEquiv.symm
  refine ⟨b.reindex f, fun i => (f.symm i).1, ?_, ?_⟩
  · intro i
    simpa only [Basis.reindex_apply] using diagWeightBasis_mem hZ (f.symm i)
  · intro i j hij
    apply e.lt_iff_lt.mp
    apply lt_of_le_of_ne
    · exact (@toLinearExtension κ o).monotone (Or.inr hij)
    · intro heq
      exact (ne_of_lt hij) (congrArg w heq)

omit [DecidableEq ι] in
/-- Raising by a simple root strictly decreases the reverse root order. -/
theorem toWeightOrd_add_root_lt (μ : Dual K H) (i : ι) :
    WeightOrd.toWeightOrd P (μ + P.root i) < WeightOrd.toWeightOrd P μ := by
  classical
  apply lt_of_le_of_ne
  · refine ⟨Pi.single i 1, Pi.single_nonneg.mpr zero_le_one, ?_⟩
    simp only [WeightOrd.ofWeightOrd_toWeightOrd, add_sub_cancel_left, rootOf_single]
  · intro heq
    have hr : P.root i = 0 := by
      simpa only [WeightOrd.ofWeightOrd_toWeightOrd, add_eq_left] using
        congrArg (WeightOrd.ofWeightOrd P) heq
    have hs : (Pi.single i (1 : ℤ) : ι → ℤ) = 0 :=
      P.rootOf_injective (by rw [rootOf_single, hr, map_zero])
    have := congr_fun hs i
    simp at this

section OrderedBasis

variable {n : ℕ} (b : Basis (Fin n) K Z) (wt : Fin n → Dual K H)
  (hb : ∀ j, b j ∈ weightSpace P Z (wt j))
  (ho : ∀ i j, WeightOrd.toWeightOrd P (wt i) < WeightOrd.toWeightOrd P (wt j) → i < j)

include hb ho in
/-- Every positive-simple derivative of a basis vector is in the preceding basis flag. -/
theorem lie_e_mem_weightBasis_flag (i : ι) (j : Fin n) :
    ⁅e P i, b j⁆ ∈ b.flag j.castSucc := by
  have hv := toEnd_e_mem_weightSpace i (hb j)
  rw [weightSpace_eq_span_of_basis hb] at hv
  apply Submodule.span_mono _ hv
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨k, ?_, rfl⟩
  change k < j
  apply ho
  rw [hk]
  exact toWeightOrd_add_root_lt P (wt j) i

/-- The usual basis flag of a weight-ordered basis is an actual Borel coefficient flag. -/
def weightBorelFlag (k : Fin (n + 1)) : LieSubmodule K (borel P) Z :=
  VermaModule.borelSubmoduleOfGenerators P (b.flag k)
    (by
      intro i z hz
      have hle : b.flag k ≤ (b.flag k).comap (toEnd K P.KacMoodyAlgebra Z (e P i)) := by
        apply b.flag_le_iff.mpr
        intro j hj
        exact b.flag_mono (le_of_lt hj) (lie_e_mem_weightBasis_flag P b wt hb ho i j)
      exact hle hz)
    (by
      intro a z hz
      have hle : b.flag k ≤ (b.flag k).comap (toEnd K P.KacMoodyAlgebra Z (h P a)) := by
        apply b.flag_le_iff.mpr
        intro j hj
        change ⁅h P a, b j⁆ ∈ b.flag k
        rw [hb j a]
        exact (b.flag k).smul_mem _ (b.self_mem_flag hj)
      exact hle hz)

@[simp] theorem weightBorelFlag_toSubmodule (k : Fin (n + 1)) :
    (weightBorelFlag P b wt hb ho k).toSubmodule = b.flag k := rfl

/-- The coefficient flag is strictly increasing, including the zero-dimensional case. -/
theorem weightBorelFlag_strictMono : StrictMono (weightBorelFlag P b wt hb ho) := by
  intro i j hij
  exact b.flag_strictMono hij

@[simp] theorem weightBorelFlag_zero : weightBorelFlag P b wt hb ho 0 = ⊥ := by
  apply LieSubmodule.toSubmodule_injective
  exact b.flag_zero

@[simp] theorem weightBorelFlag_last : weightBorelFlag P b wt hb ho (Fin.last n) = ⊤ := by
  apply LieSubmodule.toSubmodule_injective
  exact b.flag_last

/-- Each coefficient successor is obtained by adjoining the corresponding weight vector. -/
theorem weightBorelFlag_step (j : Fin n) {z : Z}
    (hz : z ∈ weightBorelFlag P b wt hb ho j.succ) :
    ∃ f ∈ weightBorelFlag P b wt hb ho j.castSucc, ∃ c : K, z = f + c • b j := by
  change z ∈ b.flag j.succ at hz
  rw [b.flag_succ] at hz
  obtain ⟨u, hu, f, hf, huf⟩ := Submodule.mem_sup.mp hz
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  exact ⟨f, hf, c, by rw [← huf, add_comm]⟩

/-- The actual canonical tensor-Verma step is the shifted Verma module for this weight. -/
def weightBorelFlag_tensorStepEquiv (Λ : Dual K H) (j : Fin n) :
    VermaModule P (Λ + wt j) ≃ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule.tensorBorelStep P Λ (weightBorelFlag P b wt hb ho j.castSucc)
        (weightBorelFlag P b wt hb ho j.succ) :=
  VermaModule.shiftedVermaEquivTensorBorelStep P Λ _ _ (wt j) (b j)
    (by change b j ∉ b.flag j.castSucc; simp)
    (by change b j ∈ b.flag j.succ; simp)
    (fun _ hz => weightBorelFlag_step P b wt hb ho j hz)
    (lie_e_mem_weightBasis_flag P b wt hb ho · j)
    (by intro a; rw [hb j a, sub_self]; exact LieSubmodule.zero_mem _)

omit [CharZero K] in
include hb in
/-- Counting flag weights gives actual weight-space dimensions, not a formal character count. -/
theorem weightBasis_count (μ : Dual K H) :
    Nat.card {j : Fin n // wt j = μ} = finrank K (weightSpace P Z μ) := by
  classical
  rw [finrank_weightSpace_of_basis hb μ (Set.toFinite _)]
  rw [Nat.card_eq_fintype_card, Set.Finite.card_toFinset]
  exact Fintype.card_congr (Equiv.refl _)

/-- The concrete full-Lie-algebra tensor flag attached to the ordered coefficient basis. -/
def tensorWeightFlag (Λ : Dual K H) (k : Fin (n + 1)) :
    LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ ⊗[K] Z) :=
  VermaModule.tensorBorelSubmodule P Λ (weightBorelFlag P b wt hb ho k)

/-- Concrete tensor pieces form a strict filtration, not only a monotone family. -/
theorem tensorWeightFlag_strictMono (Λ : Dual K H) :
    StrictMono (tensorWeightFlag P b wt hb ho Λ) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  refine lt_iff_le_not_ge.mpr ⟨VermaModule.tensorBorelSubmodule_mono P Λ
    ((weightBorelFlag_strictMono P b wt hb ho).monotone (Fin.castSucc_le_succ j)), ?_⟩
  intro hle
  let F := weightBorelFlag P b wt hb ho j.castSucc
  have he : ∀ i, ⁅e P i, b j⁆ ∈ F := fun i =>
    lie_e_mem_weightBasis_flag P b wt hb ho i j
  have hh : ∀ a, ⁅h P a, b j⁆ - wt j a • b j ∈ F := by
    intro a
    rw [hb j a, sub_self]
    exact F.zero_mem
  let φ := VermaModule.shiftedVermaToTensorQuotient P Λ F (wt j) (b j) he hh
  have hinj : Function.Injective φ :=
    VermaModule.shiftedVermaToTensorQuotient_injective P Λ F (wt j) (b j)
      (by change b j ∉ b.flag j.castSucc; simp) he hh
  have hzero : φ (VermaModule.hwv P (Λ + wt j)) = 0 := by
    rw [VermaModule.shiftedVermaToTensorQuotient_hwv]
    apply (LieSubmodule.Quotient.mk_eq_zero _).mpr
    apply hle
    exact VermaModule.hwv_tmul_mem_tensorSubspace P Λ _
      (show b j ∈ b.flag j.succ by simp)
  exact VermaModule.hwv_ne_zero P (Λ + wt j) (hinj (hzero.trans (map_zero φ).symm))

@[simp] theorem tensorWeightFlag_zero (Λ : Dual K H) :
    tensorWeightFlag P b wt hb ho Λ 0 = ⊥ := by
  simp [tensorWeightFlag]

@[simp] theorem tensorWeightFlag_last (Λ : Dual K H) :
    tensorWeightFlag P b wt hb ho Λ (Fin.last n) = ⊤ := by
  simp [tensorWeightFlag]

end OrderedBasis

/-- Existence of a finite weight-compatible Borel flag from finite-dimensionality and
Cartan diagonalizability alone. The supplied hypotheses do not include a flag or primitive
vectors. The proof sorts an actual weight basis; all coefficient steps have dimension one.
Reconstructed from the inspected weight-decomposition and basis-flag APIs. -/
theorem exists_weightBorelFlag [FiniteDimensional K Z] (hZ : IsHDiagonalizable P Z) :
    ∃ (F : Fin (finrank K Z + 1) → LieSubmodule K (borel P) Z)
      (wt : Fin (finrank K Z) → Dual K H) (z : Fin (finrank K Z) → Z),
      StrictMono F ∧ F 0 = ⊥ ∧ F (Fin.last (finrank K Z)) = ⊤ ∧
      (∀ j, z j ∉ F j.castSucc ∧ z j ∈ F j.succ ∧
        z j ∈ weightSpace P Z (wt j) ∧ (∀ i, ⁅e P i, z j⁆ ∈ F j.castSucc) ∧
        ∀ v ∈ F j.succ, ∃ f ∈ F j.castSucc, ∃ c : K, v = f + c • z j) ∧
      ∀ μ, Nat.card {j // wt j = μ} = finrank K (weightSpace P Z μ) := by
  obtain ⟨b, wt, hb, ho⟩ := exists_weightOrderedBasis P hZ
  refine ⟨weightBorelFlag P b wt hb ho, wt, b,
    weightBorelFlag_strictMono P b wt hb ho, weightBorelFlag_zero P b wt hb ho,
    weightBorelFlag_last P b wt hb ho, ?_, weightBasis_count P b wt hb⟩
  intro j
  refine ⟨?_, ?_, hb j, (fun i => lie_e_mem_weightBasis_flag P b wt hb ho i j),
    fun _ hz => weightBorelFlag_step P b wt hb ho j hz⟩
  · change b j ∉ b.flag j.castSucc
    simp
  · change b j ∈ b.flag j.succ
    simp

/-- A finite-dimensional weight module tensored with any Verma module has an actual finite
standard filtration. The successive factors are canonical images in the ambient quotients,
with full Lie-module equivalences and multiplicities equal to actual weight-space dimensions.
The filtration is constructed, not assumed. Reconstructed from ordered weight bases and the
proved tensor identity; no finite-type, dominance, integrality or algebraic closure is needed. -/
theorem exists_tensorVermaStandardFiltration [FiniteDimensional K Z]
    (hZ : IsHDiagonalizable P Z) (Λ : Dual K H) :
    ∃ (N : Fin (finrank K Z + 1) →
        LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ ⊗[K] Z))
      (wt : Fin (finrank K Z) → Dual K H),
      StrictMono N ∧ N 0 = ⊥ ∧ N (Fin.last (finrank K Z)) = ⊤ ∧
      (∀ j, Nonempty (VermaModule P (Λ + wt j) ≃ₗ⁅K,P.KacMoodyAlgebra⁆
        (N j.succ).map (LieSubmodule.Quotient.mk' (N j.castSucc)))) ∧
      ∀ μ, Nat.card {j // wt j = μ} = finrank K (weightSpace P Z μ) := by
  obtain ⟨b, wt, hb, ho⟩ := exists_weightOrderedBasis P hZ
  exact ⟨tensorWeightFlag P b wt hb ho Λ, wt,
    tensorWeightFlag_strictMono P b wt hb ho Λ, tensorWeightFlag_zero P b wt hb ho Λ,
    tensorWeightFlag_last P b wt hb ho Λ,
    fun j => ⟨weightBorelFlag_tensorStepEquiv P b wt hb ho Λ j⟩, weightBasis_count P b wt hb⟩

end Matrix.Realization.KacMoodyAlgebra
