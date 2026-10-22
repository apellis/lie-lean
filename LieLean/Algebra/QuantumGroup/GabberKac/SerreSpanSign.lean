/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.GabberKac.SerreSpan

/-!
# Serre relations at parameters `±1`

Let `(I, ·)` be a Cartan datum and `K` a field. If every parameter `qᵢ` satisfies `qᵢ² = 1`, the
quantum binomials are signed binomial coefficients, `[n j]_{qᵢ} = qᵢ^{j(n-j)} C(n, j)`
(`QuantumGroup.qBinomial_of_sq_eq_one`), so the Serre elements `sᵢⱼ` with parameters `q` differ
from the classical ones (`q = 1`) only by signs. If moreover `qᵢ^{-aᵢⱼ} = qⱼ^{-aⱼᵢ}` for `i ≠ j`,
these signs come from a sign `c(w) = ∏_{a < b} σ(w_a, w_b)` on words, for a function
`σ : I × I → {±1}` with `σ(i, j) σ(j, i) = qᵢ^{-aᵢⱼ}`: the involution `w ↦ c(w) w` of the free
algebra (`LusztigF.signTwist`) maps every Serre product `a sᵢⱼ b` with parameters `q` to a
nonzero multiple of the classical one. Hence the spans of the Serre products of weight `ν` have
the same dimension (`LusztigF.finrank_serreSpan_of_sq_eq_one`).

This is the dimension count behind Lusztig's quasi-classical case ([Lus] 33.2.2 (b), (c)), where
`qᵢ = φ(vᵢ) = ±1`. Lusztig twists by the generators `K_μ` and assumes that `(I, ·)` has no odd
cycles; the sign `c` on words needs no such assumption (our argument).

## Main definitions

* `LusztigF.signWord σ w`: the sign `∏_{a < b} σ(w_a, w_b)` of a word.
* `LusztigF.signTwist σ`: the linear map `w ↦ c(w) w` of the free algebra.

## Main results

* `QuantumGroup.qBinomial_of_sq_eq_one`: quantum binomials at a square root of `1`.
* `LusztigF.finrank_serreSpan_of_sq_eq_one`: `dim Z_ν(q) = dim Z_ν(1)`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 33.2.
-/

open LieLean

noncomputable section

open Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k]

/-- Quantum binomials at a square root `ε` of `1`: `[n j]_ε = ε^{j(n-j)} C(n, j)`. -/
theorem qBinomial_of_sq_eq_one {ε : k} (hε : ε ^ 2 = 1) (n j : ℕ) :
    qBinomial ε n j = ε ^ (j * (n - j)) * n.choose j := by
  have hinv : ε⁻¹ = ε := by
    exact inv_eq_of_mul_eq_one_right (by rw [← sq, hε])
  induction n generalizing j with
  | zero => cases j <;> simp [qBinomial]
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [qBinomial_succ_succ, ih, ih, hinv]
      rcases lt_trichotomy (j + 1) (n + 1) with h | h | h
      · obtain ⟨t, rfl⟩ : ∃ t, n = j + 1 + t := ⟨n - (j + 1), by omega⟩
        rw [show j + 1 + t - (j + 1) = t by omega, show j + 1 + t - j = t + 1 by omega,
          show j + 1 + t + 1 - (j + 1) = t + 1 by omega, Nat.choose_succ_succ, Nat.cast_add,
          ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add,
          show j + 1 + (j + 1) * t = (j + 1) * (t + 1) by ring,
          show t + 1 + j * (t + 1) = (j + 1) * (t + 1) by ring]
        ring
      · obtain rfl : j = n := by omega
        simp
      · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega),
          Nat.choose_eq_zero_of_lt (by omega)]
        simp

end LieLean.QuantumGroup

namespace LusztigF

open FreeAlgebra LieLean.QuantumGroup

variable {K I : Type*} [Field K]

/-! ### The sign of a word -/

section Sign

variable (σ : I → I → K)

/-- The sign `∏_{a < b} σ(w_a, w_b)` of a word `w`. -/
def signWord : List I → K
  | [] => 1
  | i :: w => (w.map (σ i)).prod * signWord w

/-- The cross term `∏_{a ∈ u, b ∈ w} σ(a, b)`. -/
def signCross (u w : List I) : K := (u.map fun a ↦ (w.map (σ a)).prod).prod

@[simp] lemma signWord_nil : signWord σ [] = 1 := rfl

lemma signWord_cons (i : I) (w : List I) :
    signWord σ (i :: w) = (w.map (σ i)).prod * signWord σ w := rfl

lemma signWord_append (u w : List I) :
    signWord σ (u ++ w) = signWord σ u * signWord σ w * signCross σ u w := by
  induction u with
  | nil => simp [signCross]
  | cons i u ih =>
    simp only [List.cons_append, signWord_cons, ih, signCross, List.map_cons, List.prod_cons,
      List.map_append, List.prod_append]
    ring

lemma signCross_perm_right {u w w' : List I} (h : w.Perm w') :
    signCross σ u w = signCross σ u w' := by
  simp only [signCross]
  congr 1
  exact List.map_congr_left fun a _ ↦ (h.map (σ a)).prod_eq

lemma signCross_perm_left {u u' w : List I} (h : u.Perm u') :
    signCross σ u w = signCross σ u' w :=
  (h.map _).prod_eq

variable {σ}

lemma sq_prod_map {l : List I} {f : I → K} (hf : ∀ i, f i ^ 2 = 1) : (l.map f).prod ^ 2 = 1 := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.prod_cons, mul_pow, hf, ih, one_mul]

lemma signWord_sq (hσ : ∀ i j, σ i j ^ 2 = 1) (w : List I) : signWord σ w ^ 2 = 1 := by
  induction w with
  | nil => simp
  | cons i w ih => rw [signWord_cons, mul_pow, sq_prod_map (hσ i), ih, one_mul]

lemma signCross_sq (hσ : ∀ i j, σ i j ^ 2 = 1) (u w : List I) : signCross σ u w ^ 2 = 1 :=
  sq_prod_map fun a ↦ sq_prod_map (hσ a)

lemma signWord_replicate (hσ : ∀ i, σ i i = 1) (i : I) (n : ℕ) :
    signWord σ (List.replicate n i) = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, signWord_cons, ih, hσ]

/-- The sign of the word `i^{m-r} j i^r`. -/
lemma signWord_serre (hσ : ∀ i, σ i i = 1) (i j : I) (m r : ℕ) :
    signWord σ (List.replicate (m - r) i ++ j :: List.replicate r i) =
      σ i j ^ (m - r) * σ j i ^ r := by
  simp [signWord_append, signWord_replicate hσ, signWord_cons, signCross, List.map_replicate,
    List.prod_replicate, hσ]
  ring

end Sign

/-! ### The sign twist of the free algebra -/

section Twist

variable (σ : I → I → K)

/-- The linear map `w ↦ c(w) w` of the free algebra, `c = signWord σ`. -/
def signTwist : LusztigF K I →ₗ[K] LusztigF K I :=
  (wordBasis K I).constr K fun w ↦ signWord σ w • wordBasis K I w

lemma signTwist_wordBasis (w : List I) :
    signTwist σ (wordBasis K I w) = signWord σ w • wordBasis K I w :=
  (wordBasis K I).constr_basis K _ w

variable {σ}

lemma signTwist_signTwist (hσ : ∀ i j, σ i j ^ 2 = 1) (x : LusztigF K I) :
    signTwist σ (signTwist σ x) = x := by
  have : signTwist σ ∘ₗ signTwist σ = LinearMap.id :=
    (wordBasis K I).ext fun w ↦ by
      rw [LinearMap.comp_apply, signTwist_wordBasis, map_smul, signTwist_wordBasis, smul_smul,
        ← sq, signWord_sq hσ, one_smul, LinearMap.id_apply]
  exact LinearMap.congr_fun this x

variable (D : LusztigCartanDatum I)

/-- The word `i^{m-r} j i^r` in the Serre element. -/
lemma pow_mul_mul_pow (i j : I) (m r : ℕ) :
    θ K i ^ (m - r) * θ K j * θ K i ^ r =
      wordBasis K I (List.replicate (m - r) i ++ j :: List.replicate r i) := by
  simp [List.prod_replicate, mul_assoc]

/-- The twist maps a Serre product with parameters `q` to a nonzero multiple of the classical
one. -/
lemma signTwist_serreProduct {q : I → K} (hq : ∀ i, q i ^ 2 = 1) (hσ : ∀ i j, σ i j ^ 2 = 1)
    (hσd : ∀ i, σ i i = 1)
    (hσq : ∀ i j, i ≠ j → σ i j * σ j i = q i ^ (serreExp D i j - 1))
    {g : List I × I × I × List I} (hg : g.2.1 ≠ g.2.2.1) :
    ∃ s : K, s ≠ 0 ∧ signTwist σ (serreProduct D q g) =
      s • serreProduct D (fun _ ↦ (1 : K)) g := by
  obtain ⟨a, i, j, b⟩ := g
  simp only at hg
  set m := serreExp D i j
  set w : ℕ → List I := fun r ↦ List.replicate (m - r) i ++ j :: List.replicate r i
  have key : ∀ r, r ≤ m → (w r).Perm (j :: List.replicate m i) := fun r hr ↦
    List.perm_middle.trans (by rw [← List.replicate_add, Nat.sub_add_cancel hr])
  have hperm : ∀ r, r ≤ m → (w r).Perm (w 0) := fun r hr ↦
    (key r hr).trans (key 0 (Nat.zero_le _)).symm
  set κ := signWord σ a * signWord σ b * signCross σ a (w 0) * signCross σ (a ++ w 0) b
  have hsign : ∀ r, r ≤ m → signWord σ (a ++ w r ++ b) = κ * (σ i j ^ (m - r) * σ j i ^ r) := by
    intro r hr
    rw [signWord_append, signWord_append, signCross_perm_right σ (hperm r hr),
      signCross_perm_left σ ((hperm r hr).append_left a), signWord_serre hσd]
    ring
  have hsq : ∀ x : K, x ^ 2 = 1 → x ≠ 0 := fun x hx h ↦ by simp [h] at hx
  refine ⟨κ * σ i j ^ m, ?_, ?_⟩
  · refine hsq _ ?_
    simp only [κ, mul_pow, signWord_sq hσ, signCross_sq hσ, one_mul]
    rw [← pow_mul, mul_comm, pow_mul, hσ, one_pow]
  have hexp : ∀ r, r ≤ m → q i ^ (r * (m - r)) * (σ i j ^ (m - r) * σ j i ^ r) = σ i j ^ m := by
    intro r hr
    have h1 : σ i j ^ (m - r) * σ j i ^ r = σ i j ^ m * (σ i j * σ j i) ^ r := by
      have : σ i j ^ m = σ i j ^ (m - r) * σ i j ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
      rw [this, mul_pow, show σ i j ^ (m - r) * σ i j ^ r * (σ i j ^ r * σ j i ^ r) =
        σ i j ^ (m - r) * (σ i j ^ 2) ^ r * σ j i ^ r by ring, hσ, one_pow, mul_one]
    have h2 : q i ^ (r * (m - r)) * q i ^ ((m - 1) * r) = 1 := by
      rw [← pow_add]
      suffices h : Even (r * (m - r) + (m - 1) * r) by
        obtain ⟨t, ht⟩ := h
        rw [ht, ← two_mul, pow_mul, hq, one_pow]
      rcases Nat.even_or_odd r with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact ⟨s * (m - r) + (m - 1) * s, by subst hs; ring⟩
      · refine ⟨r * (m - s - 1), ?_⟩
        have : m - r + (m - 1) = 2 * (m - s - 1) := by omega
        rw [mul_comm (m - 1) r, ← mul_add, this]; ring
    rw [h1, hσq i j hg, ← pow_mul]
    linear_combination (σ i j ^ m) * h2
  simp only [serreProduct, serreWord, qSerre, Finset.mul_sum, Finset.sum_mul, map_sum,
    Finset.smul_sum, mul_smul_comm, smul_mul_assoc, map_smul]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  rw [pow_mul_mul_pow, ← wordBasis_append, ← wordBasis_append, signTwist_wordBasis,
    hsign r hr, smul_smul, smul_smul, qBinomial_of_sq_eq_one (hq i), qBinomial_one]
  congr 1
  rw [← hexp r hr]
  ring

/-- **Serre spans at parameters `±1`.** If `qᵢ² = 1` for all `i` and `qᵢ^{-aᵢⱼ} = qⱼ^{-aⱼᵢ}`
for `i ≠ j`, the span of the Serre products of weight `ν` with parameters `q` has the same
dimension as the span of the classical ones (cf. [Lus] 33.2.2 (b)). -/
theorem finrank_serreSpan_of_sq_eq_one {q : I → K} (hq : ∀ i, q i ^ 2 = 1)
    (hsym : ∀ i j, i ≠ j → q i ^ (serreExp D i j - 1) = q j ^ (serreExp D j i - 1))
    (ν : I →₀ ℕ) :
    Module.finrank K (serreSpan D q ν) = Module.finrank K (serreSpan D (fun _ ↦ (1 : K)) ν) := by
  classical
  let _ : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  set σ : I → I → K := fun i j ↦ if i < j then q i ^ (serreExp D i j - 1) else 1
  have hσ : ∀ i j, σ i j ^ 2 = 1 := fun i j ↦ by
    simp only [σ]; split_ifs
    · rw [← pow_mul, mul_comm, pow_mul, hq, one_pow]
    · exact one_pow 2
  have hσd : ∀ i, σ i i = 1 := fun i ↦ by simp [σ]
  have hσq : ∀ i j, i ≠ j → σ i j * σ j i = q i ^ (serreExp D i j - 1) := fun i j hij ↦ by
    rcases lt_or_gt_of_ne hij with h | h
    · simp [σ, h, h.not_gt]
    · simp [σ, h, h.not_gt, hsym i j hij]
  let T : LusztigF K I ≃ₗ[K] LusztigF K I :=
    LinearEquiv.ofInvolutive (signTwist σ) (signTwist_signTwist hσ)
  have hmap : (serreSpan D q ν).map (T : LusztigF K I →ₗ[K] LusztigF K I) =
      serreSpan D (fun _ ↦ (1 : K)) ν := by
    rw [serreSpan, Submodule.map_span]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨s, -, hs⟩ := signTwist_serreProduct D hq hσ hσd hσq hg.1
      change signTwist σ _ ∈ _
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨s, hs0, hs⟩ := signTwist_serreProduct D hq hσ hσd hσq hg.1
      have : serreProduct D (fun _ ↦ (1 : K)) g = s⁻¹ • T (serreProduct D q g) := by
        change _ = s⁻¹ • signTwist σ _
        rw [hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨g, hg, rfl⟩, rfl⟩)
  rw [← hmap, LinearEquiv.finrank_map_eq]

end Twist

end LusztigF
