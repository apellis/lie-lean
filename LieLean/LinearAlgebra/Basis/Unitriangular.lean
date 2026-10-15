/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Unitriangular families

Let `e` be a basis of `M` indexed by `ι` and `f : ι → ℕ`. A family `c : ι → M` such that
`c i - e i` lies in the span of the `e j` with `f j < f i` is again a basis
(`Module.Basis.ofUnitriangular`). No finiteness of the lower sets is needed.

## Main definitions and results

* `Module.Basis.span_eq_top_of_unitriangular`, `Module.Basis.linearIndependent_of_unitriangular`.
* `Module.Basis.ofUnitriangular`: the basis `c`.
-/

namespace Module.Basis

variable {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (e : Module.Basis ι R M) {c : ι → M} {f : ι → ℕ}

include e in
/-- A family unitriangular with respect to a basis spans. -/
theorem span_eq_top_of_unitriangular
    (h : ∀ i, c i - e i ∈ Submodule.span R (e '' {j | f j < f i})) :
    Submodule.span R (Set.range c) = ⊤ := by
  have key : ∀ n i, f i = n → e i ∈ Submodule.span R (Set.range c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hle : Submodule.span R (e '' {j | f j < f i}) ≤ Submodule.span R (Set.range c) :=
        Submodule.span_le.2 fun _ ⟨j, hj, hje⟩ ↦ hje ▸ ih (f j) (hi ▸ hj) j rfl
      rw [← sub_sub_cancel (c i) (e i)]
      exact sub_mem (Submodule.subset_span ⟨i, rfl⟩) (hle (h i))
  rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact key _ i rfl

include e in
lemma repr_apply_of_unitriangular
    (h : ∀ i, c i - e i ∈ Submodule.span R (e '' {j | f j < f i})) {i j : ι} (hij : f j ≤ f i) :
    e.repr (c j) i = Finsupp.single j 1 i := by
  have h1 : e.repr (c j - e j) i = 0 := by
    by_contra hne
    have := (e.mem_span_image.1 (h j)) (Finsupp.mem_support_iff.2 hne)
    exact absurd hij (not_le.2 this)
  rwa [map_sub, Finsupp.sub_apply, sub_eq_zero, e.repr_self] at h1

include e in
/-- A family unitriangular with respect to a basis is linearly independent. -/
theorem linearIndependent_of_unitriangular
    (h : ∀ i, c i - e i ∈ Submodule.span R (e '' {j | f j < f i})) : LinearIndependent R c := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hne
  obtain ⟨m, hm, hmax⟩ := (s.filter fun j ↦ g j ≠ 0).exists_max_image f ⟨i, by simp [hi, hne]⟩
  rw [Finset.mem_filter] at hm
  have h0 := congrArg (fun x ↦ e.repr x m) hg
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_zero, Finsupp.zero_apply] at h0
  rw [Finset.sum_eq_single m (fun j hj hjm ↦ ?_) (fun h ↦ absurd hm.1 h),
    repr_apply_of_unitriangular e h le_rfl, Finsupp.single_eq_same, mul_one] at h0
  · exact hm.2 h0
  · by_cases hj0 : g j = 0
    · rw [hj0, zero_mul]
    · rw [repr_apply_of_unitriangular e h (hmax j (Finset.mem_filter.2 ⟨hj, hj0⟩)),
        Finsupp.single_apply, ite_eq_right hjm, mul_zero]

/-- A family unitriangular with respect to a basis (`c i - e i` in the span of the `e j` with
`f j < f i`) is a basis. -/
noncomputable def ofUnitriangular
    (h : ∀ i, c i - e i ∈ Submodule.span R (e '' {j | f j < f i})) : Module.Basis ι R M :=
  Module.Basis.mk (e.linearIndependent_of_unitriangular h)
    (e.span_eq_top_of_unitriangular h).ge

@[simp] lemma ofUnitriangular_apply
    (h : ∀ i, c i - e i ∈ Submodule.span R (e '' {j | f j < f i})) (i : ι) :
    e.ofUnitriangular h i = c i :=
  Module.Basis.mk_apply _ _ _

end Module.Basis
