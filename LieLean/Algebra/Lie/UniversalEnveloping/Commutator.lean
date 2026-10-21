/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.Filtration
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NoncommRing

/-!
# Commutators in associative algebras and universal enveloping algebras

For an element `a` of an associative `R`-algebra `A`, `LinearMap.commutator R a` is the linear map
`u ↦ a u - u a`. It is a derivation (`LinearMap.commutator_mul`), so if it kills `u` and `v` after
`m` and `n` steps, it kills `u v` after `m + n` steps (`LinearMap.pow_commutator_mul_eq_zero`).
Left multiplication by `a` is the sum of the commuting maps `commutator a` and right
multiplication by `a`, which gives the binomial expansion
`aⁿ u = ∑ⱼ C(n, j) (ad a)ʲ(u) aⁿ⁻ʲ` (`LinearMap.pow_mul_eq_sum_commutator`).

For a Lie algebra `L` and `x ∈ L` with `ad x` locally nilpotent on `L`, the commutator with `ι x`
is locally nilpotent on `U(L)` (`UniversalEnvelopingAlgebra.exists_commutator_pow_eq_zero`).

These are the commutation rules used in the proof of Shapovalov's theorem ([HumO] §4.13).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.13.
-/

open Finset

noncomputable section

namespace LinearMap

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The commutator `u ↦ a u - u a` with a fixed element `a`, as a linear map. -/
def commutator (a : A) : A →ₗ[R] A := mulLeft R a - mulRight R a

variable {R}

lemma commutator_apply (a u : A) : commutator R a u = a * u - u * a := rfl

lemma commutator_mul (a u v : A) :
    commutator R a (u * v) = commutator R a u * v + u * commutator R a v := by
  simp only [commutator_apply]
  noncomm_ring

lemma commutator_pow_eq_zero_of_le {a u : A} {m n : ℕ} (hmn : m ≤ n)
    (hu : (commutator R a ^ m) u = 0) : (commutator R a ^ n) u = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, Module.End.mul_apply, hu, map_zero]

/-- If `ad a` kills `u` after `m` steps and `v` after `n` steps, it kills `u v` after `m + n`
steps. -/
theorem pow_commutator_mul_eq_zero (a : A) :
    ∀ (m n : ℕ) (u v : A), (commutator R a ^ m) u = 0 → (commutator R a ^ n) v = 0 →
      (commutator R a ^ (m + n)) (u * v) = 0 := by
  intro m
  induction m with
  | zero =>
    intro n u v hu _
    rw [pow_zero, Module.End.one_apply] at hu
    rw [hu, zero_mul, map_zero]
  | succ m ihm =>
    intro n
    induction n with
    | zero =>
      intro u v _ hv
      rw [pow_zero, Module.End.one_apply] at hv
      rw [hv, mul_zero, map_zero]
    | succ n ihn =>
      intro u v hu hv
      rw [show m + 1 + (n + 1) = (m + (n + 1)) + 1 by omega, pow_succ, Module.End.mul_apply,
        commutator_mul, map_add]
      have h1 : (commutator R a ^ (m + (n + 1))) (commutator R a u * v) = 0 :=
        ihm (n + 1) _ v (by rwa [← Module.End.mul_apply, ← pow_succ]) hv
      have h2 : (commutator R a ^ (m + 1 + n)) (u * commutator R a v) = 0 :=
        ihn u _ hu (by rwa [← Module.End.mul_apply, ← pow_succ])
      rw [h1, show m + (n + 1) = m + 1 + n by omega, h2, add_zero]

lemma commute_commutator_mulRight (a : A) : Commute (commutator R a) (mulRight R a) :=
  (commute_mulLeft_right a a).sub_left (Commute.refl _)

/-- The binomial expansion `aⁿ u = ∑ⱼ C(n, j) (ad a)ʲ(u) aⁿ⁻ʲ`. -/
theorem pow_mul_eq_sum_commutator (a u : A) (n : ℕ) :
    a ^ n * u =
      ∑ j ∈ Finset.range (n + 1), n.choose j • ((commutator R a ^ j) u * a ^ (n - j)) := by
  have hL : mulLeft R a = commutator R a + mulRight R a := by
    rw [commutator, sub_add_cancel]
  have h := congrArg (fun T : Module.End R A ↦ T u)
    ((commute_commutator_mulRight (R := R) a).add_pow n)
  simp only [← hL, pow_mulLeft, mulLeft_apply] at h
  rw [h, LinearMap.sum_apply]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
    ((commute_commutator_mulRight (R := R) a).pow_pow j (n - j)).eq, Module.End.mul_apply,
    pow_mulRight, mulRight_apply]

/-- If `(ad a)^{J+1}` kills `u` and `J ≤ n`, then `aⁿ u = (∑_{j ≤ J} C(n, j) (ad a)ʲ(u) aᴶ⁻ʲ) aⁿ⁻ᴶ`.
-/
theorem pow_mul_eq_sum_mul_pow {a u : A} {J n : ℕ} (hJ : J ≤ n)
    (hu : (commutator R a ^ (J + 1)) u = 0) :
    a ^ n * u = (∑ j ∈ Finset.range (J + 1), n.choose j • ((commutator R a ^ j) u * a ^ (J - j))) *
      a ^ (n - J) := by
  rw [pow_mul_eq_sum_commutator (R := R), sum_mul]
  symm
  calc ∑ j ∈ Finset.range (J + 1), n.choose j • ((commutator R a ^ j) u * a ^ (J - j)) * a ^ (n - J)
      = ∑ j ∈ Finset.range (J + 1), n.choose j • ((commutator R a ^ j) u * a ^ (n - j)) := by
        refine sum_congr rfl fun j hj ↦ ?_
        rw [Finset.mem_range] at hj
        rw [smul_mul_assoc, mul_assoc, ← pow_add, show J - j + (n - J) = n - j by omega]
    _ = ∑ j ∈ Finset.range (n + 1), n.choose j • ((commutator R a ^ j) u * a ^ (n - j)) := by
        refine sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj ↦ ?_
        rw [Finset.mem_range, not_lt] at hj
        rw [commutator_pow_eq_zero_of_le hj hu, zero_mul, smul_zero]

end LinearMap

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

lemma commutator_ι (x y : L) : LinearMap.commutator R (ι R x) (ι R y) = ι R ⁅x, y⁆ := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, LinearMap.commutator_apply]

lemma commutator_pow_ι (x y : L) (n : ℕ) :
    (LinearMap.commutator R (ι R x) ^ n) (ι R y) = ι R ((LieAlgebra.ad R L x ^ n) y) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, commutator_ι, pow_succ', Module.End.mul_apply,
      LieAlgebra.ad_apply]

/-- If `ad x` is locally nilpotent on `L`, the commutator with `ι x` is locally nilpotent on
`U(L)`. -/
theorem exists_commutator_pow_eq_zero {x : L} (hx : ∀ y : L, ∃ n, (LieAlgebra.ad R L x ^ n) y = 0)
    (u : UniversalEnvelopingAlgebra R L) :
    ∃ n, (LinearMap.commutator R (ι R x) ^ n) u = 0 := by
  obtain ⟨a, rfl⟩ : ∃ a, mkAlgHom R L a = u := by
    induction u using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r =>
    refine ⟨1, ?_⟩
    rw [pow_one, AlgHom.commutes, LinearMap.commutator_apply, Algebra.commutes, sub_self]
  | ι y =>
    obtain ⟨n, hn⟩ := hx y
    refine ⟨n, ?_⟩
    change (LinearMap.commutator R (ι R x) ^ n) (ι R y) = 0
    rw [commutator_pow_ι, hn, map_zero]
  | add a₁ a₂ h₁ h₂ =>
    obtain ⟨m, hm⟩ := h₁
    obtain ⟨n, hn⟩ := h₂
    refine ⟨max m n, ?_⟩
    rw [map_add, map_add, LinearMap.commutator_pow_eq_zero_of_le (le_max_left m n) hm,
      LinearMap.commutator_pow_eq_zero_of_le (le_max_right m n) hn, add_zero]
  | mul a₁ a₂ h₁ h₂ =>
    obtain ⟨m, hm⟩ := h₁
    obtain ⟨n, hn⟩ := h₂
    exact ⟨m + n, by rw [map_mul]; exact LinearMap.pow_commutator_mul_eq_zero _ m n _ _ hm hn⟩

end UniversalEnvelopingAlgebra
