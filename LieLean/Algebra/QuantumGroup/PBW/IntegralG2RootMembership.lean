/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2AdjointSum

/-!
# Integral membership of the normalized G₂ root divided powers

Every normalized root divided power lies in any subring containing the coefficient ring
and the divided powers of the two simple roots. This is one containment needed for the
integral PBW spanning theorem; it does not prove ordered-span multiplicative closure.
-/

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

open Finset

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {q : k} {e A b C D f : B} {Λ : Subring k} {T : Subring B}
  (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
  (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
  (H : Rel q e A b C D f) (hqΛ : q ∈ Λ) (hqΛ' : q⁻¹ ∈ Λ)
  (hΛT : ∀ c ∈ Λ, algebraMap k B c ∈ T)
  (heT : ∀ a, qDivPow q a e ∈ T) (hfT : ∀ d, qDivPow (q ^ 3) d f ∈ T)

include hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT in
/-- Every divided adjoint sum is integral, by triangular inversion of straightening. -/
lemma adjointSum_mem (n s : ℕ) : adjointSum q A b C D f n s ∈ T := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hFE := T.mul_mem (hfT s) (heT n)
    rw [qDivPow_f_mul_qDivPow_e hq hd hqi hpi H, sum_range_succ] at hFE
    have hrest : ∑ j ∈ range n, B2Integral.sCoef q (3 * s) n j •
        (qDivPow q (n - j) e * adjointSum q A b C D f j s) ∈ T := by
      exact T.sum_mem fun j hj => B2Integral.smul_mem_T hΛT
        (B2Integral.sCoef_mem hqΛ hqΛ' _ _ _) (T.mul_mem (heT _) (ih j (mem_range.mp hj)))
    have hlast := T.sub_mem hFE hrest
    rw [add_sub_cancel_left] at hlast
    simp only [B2Integral.sCoef, Nat.sub_self, mul_zero, zero_mul, pow_zero, mul_one,
      qDivPow_zero', one_mul] at hlast
    have hu : ((-1 : k) ^ n)⁻¹ ∈ Λ := by
      rw [← inv_pow]
      exact Λ.pow_mem (by simp) _
    have hh := B2Integral.smul_mem_T hΛT hu hlast
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : k) ≠ 0)),
      one_smul] at hh

include hq in
lemma adjointCoeff_ne_zero (a b c d l : ℕ) : adjointCoeff q a b c d l ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq)

include hqΛ' in
lemma adjointCoeff_inv_mem (a b c d l : ℕ) : (adjointCoeff q a b c d l)⁻¹ ∈ Λ := by
  rw [adjointCoeff, mul_inv, ← inv_pow, ← inv_pow]
  exact Λ.mul_mem (Λ.pow_mem (by simp) _) (Λ.pow_mem hqΛ' _)

include hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT in
private lemma extract_adjoint_monomial (r s : ℕ) (y : AdjointIndex)
    (hy : y ∈ adjointIndices r s)
    (hrest : ∀ x ∈ adjointIndices r s, x ≠ y →
      M5 q A b C D f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∈ T) :
    M5 q A b C D f y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 ∈ T := by
  have hsum := adjointSum_mem hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT r s
  rw [adjointSum, ← sum_erase_add _ _ hy] at hsum
  have hr : ∑ x ∈ (adjointIndices r s).erase y,
      adjointCoeff q x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 •
        M5 q A b C D f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∈ T := by
    refine T.sum_mem fun x hx => ?_
    rcases mem_erase.mp hx with ⟨hne, hx⟩
    exact B2Integral.smul_mem_T hΛT (adjointCoeff_mem Λ hqΛ _ _ _ _ _) (hrest x hx hne)
  have hh := T.sub_mem hsum hr
  rw [add_sub_cancel_left] at hh
  have hh' := B2Integral.smul_mem_T hΛT
    (adjointCoeff_inv_mem hqΛ' y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2) hh
  rwa [smul_smul, inv_mul_cancel₀ (adjointCoeff_ne_zero hq _ _ _ _ _), one_smul] at hh'

include hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT in
/-- All four nonsimple root divided powers are integral. The simultaneous induction is on
root height, not on the exponent, so all other factors in the extracting sum are smaller. -/
private theorem qDivPow_roots_mem_by_height (N : ℕ) :
    (∀ a, 4 * a = N → qDivPow (q ^ 3) a A ∈ T) ∧
    (∀ b', 3 * b' = N → qDivPow q b' b ∈ T) ∧
    (∀ c, 5 * c = N → qDivPow (q ^ 3) c C ∈ T) ∧
    (∀ d, 2 * d = N → qDivPow q d D ∈ T) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have known (a b' c d l : ℕ) (ha : 4 * a < N) (hb : 3 * b' < N)
        (hc : 5 * c < N) (hd : 2 * d < N) : M5 q A b C D f a b' c d l ∈ T := by
      exact T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem
        ((ih _ ha).1 a rfl) ((ih _ hb).2.1 b' rfl)) ((ih _ hc).2.2.1 c rfl))
        ((ih _ hd).2.2.2 d rfl)) (hfT l)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      have hmem : (t, 0, 0, 0, 0) ∈ adjointIndices (3 * t) t := by simp
      have hh := extract_adjoint_monomial hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT
        (3 * t) t (t, 0, 0, 0, 0) hmem ?_
      · simpa only [M5, P3, qDivPow_zero', mul_one] using hh
      rintro ⟨a, b', c, d, l⟩ hx hne
      have hx' := (mem_adjointIndices _ _ _ _ _ _ _).mp hx
      simp only [ne_eq, Prod.mk.injEq] at hne
      exact known a b' c d l (by omega) (by omega) (by omega) (by omega)
    · intro t ht
      have hmem : (0, t, 0, 0, 0) ∈ adjointIndices (2 * t) t := by simp
      have hh := extract_adjoint_monomial hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT
        (2 * t) t (0, t, 0, 0, 0) hmem ?_
      · simpa only [M5, P3, qDivPow_zero', mul_one, one_mul] using hh
      rintro ⟨a, b', c, d, l⟩ hx hne
      have hx' := (mem_adjointIndices _ _ _ _ _ _ _).mp hx
      simp only [ne_eq, Prod.mk.injEq] at hne
      exact known a b' c d l (by omega) (by omega) (by omega) (by omega)
    · intro t ht
      have hmem : (0, 0, t, 0, 0) ∈ adjointIndices (3 * t) (2 * t) := by simp
      have hh := extract_adjoint_monomial hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT
        (3 * t) (2 * t) (0, 0, t, 0, 0) hmem ?_
      · simpa only [M5, P3, qDivPow_zero', mul_one, one_mul] using hh
      rintro ⟨a, b', c, d, l⟩ hx hne
      have hx' := (mem_adjointIndices _ _ _ _ _ _ _).mp hx
      simp only [ne_eq, Prod.mk.injEq] at hne
      exact known a b' c d l (by omega) (by omega) (by omega) (by omega)
    · intro t ht
      have hmem : (0, 0, 0, t, 0) ∈ adjointIndices t t := by simp
      have hh := extract_adjoint_monomial hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT
        t t (0, 0, 0, t, 0) hmem ?_
      · simpa only [M5, P3, qDivPow_zero', mul_one, one_mul] using hh
      rintro ⟨a, b', c, d, l⟩ hx hne
      have hx' := (mem_adjointIndices _ _ _ _ _ _ _).mp hx
      simp only [ne_eq, Prod.mk.injEq] at hne
      exact known a b' c d l (by omega) (by omega) (by omega) (by omega)

include hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT in
/-- The divided powers of all four nonsimple normalized G₂ roots lie in `T`. -/
theorem qDivPow_roots_mem (n : ℕ) :
    qDivPow (q ^ 3) n A ∈ T ∧ qDivPow q n b ∈ T ∧
      qDivPow (q ^ 3) n C ∈ T ∧ qDivPow q n D ∈ T := by
  have hh := qDivPow_roots_mem_by_height hq hd hqi hpi H hqΛ hqΛ' hΛT heT hfT
  exact ⟨(hh (4 * n)).1 n rfl, (hh (3 * n)).2.1 n rfl,
    (hh (5 * n)).2.2.1 n rfl, (hh (2 * n)).2.2.2 n rfl⟩

/-- A six-root ordered divided-power monomial. -/
def M6 (q : k) (e A b C D f : B) (i a b' c d l : ℕ) : B :=
  qDivPow q i e * M5 q A b C D f a b' c d l

/-- Integral linear combinations of the normalized ordered G₂ divided monomials. -/
def orderedSpan (q : k) (Λ : Subring k) (e A b C D f : B) : AddSubgroup B :=
  AddSubgroup.closure {w | ∃ z ∈ Λ, ∃ i a b' c d l : ℕ,
    w = z • M6 q e A b C D f i a b' c d l}

/-- The subring generated by the coefficient ring and the simple-root divided powers. -/
def genRing (q : k) (Λ : Subring k) (e f : B) : Subring B :=
  Subring.closure (algebraMap k B '' (Λ : Set k) ∪
    Set.range (fun n : ℕ => qDivPow q n e) ∪
    Set.range (fun n : ℕ => qDivPow (q ^ 3) n f))

include hq hd hqi hpi H hqΛ hqΛ' in
/-- The ordered integral span is contained in the generated integral subring.
The reverse containment, requiring multiplicative stability, is not asserted here. -/
theorem orderedSpan_le_genRing :
    orderedSpan q Λ e A b C D f ≤ (genRing q Λ e f).toAddSubgroup := by
  have hΛ : ∀ z ∈ Λ, algebraMap k B z ∈ genRing q Λ e f := fun z hz =>
    Subring.subset_closure (Or.inl (Or.inl ⟨z, hz, rfl⟩))
  have he : ∀ n, qDivPow q n e ∈ genRing q Λ e f := fun n =>
    Subring.subset_closure (Or.inl (Or.inr ⟨n, rfl⟩))
  have hf : ∀ n, qDivPow (q ^ 3) n f ∈ genRing q Λ e f := fun n =>
    Subring.subset_closure (Or.inr ⟨n, rfl⟩)
  have hh := qDivPow_roots_mem hq hd hqi hpi H hqΛ hqΛ' hΛ he hf
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z, hz, i, a, b', c, d, l, rfl⟩ := hx
    exact B2Integral.smul_mem_T hΛ hz (mul_mem (he i)
      (mul_mem (mul_mem (mul_mem (mul_mem (hh a).1 (hh b').2.1) (hh c).2.2.1)
        (hh d).2.2.2) (hf l)))
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

end LieLean.QuantumGroup.G2Integral
