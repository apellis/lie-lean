/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Lifting exactness from an exhaustive nonnegative filtration

## Main definitions / results

* `FilteredLinearMap.grade`: the actual quotient `F (p + 1) / F p`.
* `FilteredLinearMap.gradedMap`: the map induced on these quotients.
* `FilteredLinearMap.exists_preimage_mem_of_graded_exact`: lift a boundary in the associated
  graded complex repeatedly, with a primitive in the same filtration bound.
* `FilteredLinearMap.range_eq_ker_of_graded_exact`: exact associated graded implies exactness.

These results use arbitrary modules over a ring, not finite-dimensional vector spaces, complete
filtrations, spectral sequences, or an assumption of exactness of the original complex. Taking
`F p` to mean total CE degree strictly less than `p` makes `F 0 = ⊥` at every chain degree.

## References

Reconstructed finite descending-filtration argument; no external reference consulted.
-/

namespace FilteredLinearMap

variable {R A B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The next filtration stage modulo the previous stage (viewed inside it). -/
def grade (F : ℕ → Submodule R A) (p : ℕ) :=
  F (p + 1) ⧸ (F p).comap (F (p + 1)).subtype

instance (F : ℕ → Submodule R A) (p : ℕ) : AddCommGroup (grade F p) :=
  inferInstanceAs (AddCommGroup (F (p + 1) ⧸ (F p).comap (F (p + 1)).subtype))

instance (F : ℕ → Submodule R A) (p : ℕ) : Module R (grade F p) :=
  inferInstanceAs (Module R (F (p + 1) ⧸ (F p).comap (F (p + 1)).subtype))

/-- Restrict a filtration-preserving map at a fixed filtration bound. -/
def levelMap (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (f : A →ₗ[R] B) (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) :
    F p →ₗ[R] G p := f.restrict (hf p)

/-- The induced map on adjacent filtration quotients. -/
def gradedMap (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (f : A →ₗ[R] B) (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) :
    grade F p →ₗ[R] grade G p :=
  Submodule.mapQ _ _ (levelMap F G f hf (p + 1)) (by
    intro x hx
    exact hf p x hx)

/-- A cycle has a primitive with the same filtration bound if the actual adjacent quotient
complexes are exact. The proof successively removes leading symbols; it does not assume
acyclicity of the original complex. Reconstructed induction on the finite filtration bound. -/
theorem exists_preimage_mem_of_graded_exact
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B) (H : ℕ → Submodule R C)
    (hF : Monotone F) (hG0 : G 0 = ⊥)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : g.comp f = 0)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p)
    (hg : ∀ p, ∀ x ∈ G p, g x ∈ H p)
    (hex : ∀ p, LinearMap.range (gradedMap F G f hf p) =
      LinearMap.ker (gradedMap G H g hg p))
    (p : ℕ) (x : B) (hx : x ∈ G p) (hcycle : g x = 0) :
    ∃ y ∈ F p, f y = x := by
  induction p generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa [hG0] using hx
    exact ⟨0, (F 0).zero_mem, by simp [hx0]⟩
  | succ p ih =>
    let x' : G (p + 1) := ⟨x, hx⟩
    have hsymbol : (Submodule.Quotient.mk x' : grade G p) ∈
        LinearMap.ker (gradedMap G H g hg p) := by
      change Submodule.Quotient.mk (levelMap G H g hg (p + 1) x') = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change g x ∈ H p
      rw [hcycle]
      exact (H p).zero_mem
    rw [← hex p] at hsymbol
    obtain ⟨v, hv⟩ := hsymbol
    obtain ⟨y, hy⟩ :=
      ((F p).comap (F (p + 1)).subtype).mkQ_surjective v
    have hlead : f y - x ∈ G p := by
      rw [← hy] at hv
      change Submodule.Quotient.mk (levelMap F G f hf (p + 1) y) =
        Submodule.Quotient.mk x' at hv
      exact (Submodule.Quotient.eq ((G p).comap (G (p + 1)).subtype)).mp hv
    have hrem : g (x - f y) = 0 := by
      rw [map_sub, hcycle]
      have hz : g (f y) = 0 := LinearMap.congr_fun hgf y
      rw [hz, sub_self]
    obtain ⟨z, hz, hdz⟩ := ih (x - f y)
      (by simpa only [neg_sub] using (G p).neg_mem hlead) hrem
    refine ⟨(y : A) + z, (F (p + 1)).add_mem y.property
      (hF (Nat.le_succ p) hz), ?_⟩
    rw [map_add, hdz, add_sub_cancel]

/-- Exhaustivity turns the bounded primitive theorem into actual range/kernel equality.
No dimensional restriction or completeness assumption is used. Reconstructed from the
finite leading-symbol induction above. -/
theorem range_eq_ker_of_graded_exact
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B) (H : ℕ → Submodule R C)
    (hF : Monotone F) (hG0 : G 0 = ⊥) (hGexhaustive : ∀ x, ∃ p, x ∈ G p)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : g.comp f = 0)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p)
    (hg : ∀ p, ∀ x ∈ G p, g x ∈ H p)
    (hex : ∀ p, LinearMap.range (gradedMap F G f hf p) =
      LinearMap.ker (gradedMap G H g hg p)) :
    LinearMap.range f = LinearMap.ker g := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun hgf x
  · intro x hx
    obtain ⟨p, hp⟩ := hGexhaustive x
    obtain ⟨y, _, hy⟩ :=
      exists_preimage_mem_of_graded_exact F G H hF hG0 f g hgf hf hg hex p x hp hx
    exact ⟨y, hy⟩

end FilteredLinearMap
