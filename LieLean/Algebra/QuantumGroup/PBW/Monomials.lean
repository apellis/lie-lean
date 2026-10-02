/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RootVectors
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Ordered monomials in the root vectors along a word

Let `Tᵢ` (`i ∈ B`) be algebra automorphisms of a `k`-algebra `A` and `Eᵢ ∈ A`. For a word
`ω = i₁ i₂ ⋯ iₙ` the root vectors are `E_{β_m} = T_{i₁} ⋯ T_{i_{m-1}}(E_{i_m})`
(`CoxeterSystem.rootVector`), and for exponents `c : Fin n → ℕ` the *ordered monomial* is

`E_{β₁}^{c₁} E_{β₂}^{c₂} ⋯ E_{βₙ}^{cₙ}` (`CoxeterSystem.pbwMonomial`).

It is defined by the recursion `M(i ω, c) = Eᵢ^{c₁} Tᵢ(M(ω, c'))`
(`CoxeterSystem.pbwMonomial_eq_prod` is the product formula). This recursion gives a criterion
for linear independence (`CoxeterSystem.linearIndependent_pbwMonomial`): if `S ⊆ A` is a subspace
containing the monomials along all final segments of `ω`, and for every `i` a relation
`∑ₐ Eᵢᵃ Tᵢ(uₐ) = 0` with `uₐ ∈ S` forces all `uₐ = 0`, then the ordered monomials along `ω` are
linearly independent. For `U_v(𝔤)` and `S = U⁺` the hypothesis follows from the triangular
decomposition (`LieLean/Algebra/QuantumGroup/PBW/Independence.lean`); this is the argument of
[Jan] 8.24 (check).

## Main definitions / results

* `CoxeterSystem.pbwMonomial`, `CoxeterSystem.pbwMonomial_eq_prod`.
* `CoxeterSystem.pbwMonomial_mem`: the monomials lie in any subalgebra containing the root
  vectors.
* `CoxeterSystem.linearIndependent_pbwMonomial`: the independence criterion.

Proofs adapted from the ungated `m15-pbw` branch (3473bfd); the arguments are
reconstructed. The printed sources have not been consulted.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 8.21–8.24 (check).
* [Lus] G. Lusztig, *Introduction to quantum groups*, 40.2 (check).
-/

namespace CoxeterSystem

variable {B k A : Type*}

section Semiring

variable [CommSemiring k] [Semiring A] [Algebra k A] (T : B → A ≃ₐ[k] A) (E : B → A)

/-- The ordered monomial `E_{β₁}^{c₁} ⋯ E_{βₙ}^{cₙ}` in the root vectors
`E_{β_m} = T_{i₁} ⋯ T_{i_{m-1}}(E_{i_m})` along the word `ω = i₁ ⋯ iₙ` ([Jan] 8.24 (check),
[Lus] 40.2 (check).1), defined by `M(i ω, c) = Eᵢ^{c₁} Tᵢ(M(ω, c'))`. -/
def pbwMonomial : (ω : List B) → (Fin ω.length → ℕ) → A
  | [], _ => 1
  | i :: ω, c => E i ^ c ⟨0, Nat.succ_pos _⟩ * T i (pbwMonomial ω fun n ↦ c n.succ)

@[simp] lemma pbwMonomial_nil (c : Fin ([] : List B).length → ℕ) :
    pbwMonomial T E [] c = 1 := rfl

lemma pbwMonomial_cons (i : B) (ω : List B) (c : Fin (i :: ω).length → ℕ) :
    pbwMonomial T E (i :: ω) c =
      E i ^ c ⟨0, Nat.succ_pos _⟩ * T i (pbwMonomial T E ω fun n ↦ c n.succ) := rfl

lemma rootVector_cons_zero (i : B) (ω : List B) (h : 0 < (i :: ω).length) :
    rootVector T E (i :: ω) 0 h = E i := by
  simp [rootVector]

lemma rootVector_cons_succ (i : B) (ω : List B) (n : ℕ) (h : n + 1 < (i :: ω).length) :
    rootVector T E (i :: ω) (n + 1) h =
      T i (rootVector T E ω n (Nat.lt_of_succ_lt_succ h)) := by
  simp [rootVector, AlgEquiv.mul_apply]

/-- The ordered monomial is the product of the powers of the root vectors, in the order of the
word. -/
theorem pbwMonomial_eq_prod (ω : List B) (c : Fin ω.length → ℕ) :
    pbwMonomial T E ω c =
      (List.ofFn fun n : Fin ω.length ↦ rootVector T E ω n n.2 ^ c n).prod := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have h := List.ofFn_succ (f := fun n : Fin (ω.length + 1) ↦ rootVector T E (i :: ω) n n.2 ^ c n)
    rw [pbwMonomial_cons, ih]
    change _ = (List.ofFn fun n : Fin (ω.length + 1) ↦ rootVector T E (i :: ω) n n.2 ^ c n).prod
    rw [h, List.prod_cons, map_list_prod, List.map_ofFn]
    congr 1
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext n
    rw [Function.comp_apply, map_pow]
    exact congrArg (· ^ c n.succ) (rootVector_cons_succ T E i ω n _).symm

/-- The ordered monomials lie in every subalgebra containing the root vectors along the word. -/
theorem pbwMonomial_mem {P : Subalgebra k A} {ω : List B}
    (h : ∀ n (hn : n < ω.length), rootVector T E ω n hn ∈ P) (c : Fin ω.length → ℕ) :
    pbwMonomial T E ω c ∈ P := by
  induction ω generalizing P with
  | nil => exact one_mem P
  | cons i ω ih =>
    rw [pbwMonomial_cons]
    refine mul_mem (pow_mem ?_ _) ?_
    · rw [← rootVector_cons_zero T E i ω (Nat.succ_pos _)]
      exact h 0 _
    · have h' : ∀ n (hn : n < ω.length), rootVector T E ω n hn ∈ P.comap (T i).toAlgHom := by
        intro n hn
        rw [Subalgebra.mem_comap]
        change T i (rootVector T E ω n hn) ∈ P
        rw [← rootVector_cons_succ T E i ω n (Nat.succ_lt_succ hn)]
        exact h (n + 1) _
      exact ih h' _

end Semiring

section Field

variable [Field k] [Ring A] [Algebra k A] [Nontrivial A] {T : B → A ≃ₐ[k] A} {E : B → A}

private theorem independent_single_map {k M N J : Type*} [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {m : J → M} (hm : LinearIndependent k m) (f : (ℕ →₀ M) →ₗ[k] N)
    (hf : LinearMap.ker f = ⊥) :
    LinearIndependent k
      (f ∘ fun ix : Σ _ : ℕ, J ↦ Finsupp.single ix.1 (m ix.2)) := by
  exact (Finsupp.linearIndependent_single (fun _ : ℕ ↦ m) (fun _ ↦ hm)).map' f hf

/-- **Independence of ordered monomials** ([Jan] 8.24 (check)): let `S` be a subspace of `A` such
that, for every `i`, a relation `∑ₐ Eᵢᵃ Tᵢ(uₐ) = 0` with all `uₐ ∈ S` forces `uₐ = 0`. If the
ordered monomials along all final segments of `ω` lie in `S`, then the ordered monomials along `ω`
are linearly independent. -/
theorem linearIndependent_pbwMonomial {S : Submodule k A}
    (hS : ∀ (i : B) (f : ℕ →₀ A), (∀ a, f a ∈ S) →
      (f.sum fun a x ↦ E i ^ a * T i x) = 0 → f = 0)
    (ω : List B) (hω : ∀ n c, pbwMonomial T E (ω.drop n) c ∈ S) :
    LinearIndependent k (pbwMonomial T E ω) := by
  induction ω with
  | nil =>
    change LinearIndependent k fun _ : Fin 0 → ℕ ↦ (1 : A)
    exact linearIndependent_unique_iff.2 one_ne_zero
  | cons i ω ih =>
    have ih' : LinearIndependent k (pbwMonomial T E ω) := ih fun n c ↦ hω (n + 1) c
    have hm : ∀ c, pbwMonomial T E ω c ∈ S := hω 1
    set m' : (Fin ω.length → ℕ) → S := fun c ↦ ⟨pbwMonomial T E ω c, hm c⟩ with hm'_def
    have hm' : LinearIndependent k m' := LinearIndependent.of_comp S.subtype ih'
    let Φ : (ℕ →₀ S) →ₗ[k] A :=
      Finsupp.lsum k fun a ↦
        (LinearMap.mulLeft k (E i ^ a)) ∘ₗ (T i).toLinearMap ∘ₗ S.subtype
    have hΦ : LinearMap.ker Φ = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro g hg
      have h0 := hS i (g.mapRange S.subtype (map_zero _)) (fun a ↦ by simp) (by
        rw [Finsupp.sum_mapRange_index fun a ↦ by simp]
        exact hg)
      ext a
      simpa using DFunLike.congr_fun h0 a
    have h1 : LinearIndependent k
        (Φ ∘ fun ix : Σ _ : ℕ, (Fin ω.length → ℕ) ↦ Finsupp.single ix.1 (m' ix.2)) := by
      exact independent_single_map hm' Φ hΦ
    have hinj : Function.Injective fun c : Fin (i :: ω).length → ℕ ↦
        (⟨c ⟨0, Nat.succ_pos _⟩, fun n ↦ c n.succ⟩ : Σ _ : ℕ, (Fin ω.length → ℕ)) := by
      intro c c' h
      simp only [Sigma.mk.injEq, heq_eq_eq] at h
      funext n
      refine Fin.cases ?_ (fun j ↦ ?_) n
      · exact h.1
      · exact congr_fun h.2 j
    convert h1.comp _ hinj using 1
    funext c
    simp [Φ, m', pbwMonomial_cons]

end Field

end CoxeterSystem
