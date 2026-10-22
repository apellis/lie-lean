/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CartanDatum

/-!
# The Cartan datum `(I, ∘)` attached to an integer `l ≥ 1`

Given a Cartan datum `(I, ·)` and an integer `l ≥ 1`, let `lᵢ` be the smallest integer `≥ 1`
with `lᵢ (i · i/2) ∈ lℤ`. Then `i ∘ j = lᵢ lⱼ (i · j)` is again a Cartan datum
([Lus] 2.2.4). It is the Cartan datum of the target of the quantum Frobenius homomorphism
([Lus] Ch. 35).

## Main definitions

* `LusztigCartanDatum.frobOrder`: `lᵢ`, here `l / gcd(l, dᵢ)`.
* `LusztigCartanDatum.frobenius`: the Cartan datum `(I, ∘)`.

## Main results

* `LusztigCartanDatum.frobOrder_dvd_iff`: `lᵢ ∣ n ↔ l ∣ n dᵢ`, so `lᵢ` is Lusztig's integer.
* `LusztigCartanDatum.frobenius_d`: `i ∘ i / 2 = lᵢ² dᵢ`.
* `LusztigCartanDatum.frobOrder_mul_cartanMatrix_frobenius`: `lᵢ a*ᵢⱼ = lⱼ aᵢⱼ`, with
  `a*ᵢⱼ = 2 (i ∘ j)/(i ∘ i)` the Cartan matrix of `(I, ∘)`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 2.2.4.
-/

namespace LusztigCartanDatum

variable {I : Type*} (D : LusztigCartanDatum I) (l : ℕ)

/-- Lusztig's `lᵢ` ([Lus] 2.2.4): the smallest integer `≥ 1` with `l ∣ lᵢ dᵢ`, here
`l / gcd(l, dᵢ)` (`frobOrder_dvd_iff`). -/
def frobOrder (i : I) : ℕ := l / Nat.gcd l (D.d i)

variable {l}

lemma frobOrder_pos (hl : 0 < l) (i : I) : 0 < D.frobOrder l i :=
  Nat.div_pos (Nat.gcd_le_left _ hl) (Nat.gcd_pos_of_pos_left _ hl)

lemma frobOrder_dvd (i : I) : D.frobOrder l i ∣ l :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

/-- `lᵢ ∣ n` if and only if `l ∣ n dᵢ`: `lᵢ` is the least positive integer with
`lᵢ dᵢ ∈ lℤ` ([Lus] 2.2.4). -/
lemma frobOrder_dvd_iff (hl : 0 < l) (i : I) (n : ℤ) :
    (D.frobOrder l i : ℤ) ∣ n ↔ (l : ℤ) ∣ n * D.d i := by
  obtain ⟨g, hgdef⟩ : ∃ g, Nat.gcd l (D.d i) = g := ⟨_, rfl⟩
  have hg : 0 < g := hgdef ▸ Nat.gcd_pos_of_pos_left _ hl
  obtain ⟨l', hl'⟩ := hgdef ▸ Nat.gcd_dvd_left l (D.d i)
  obtain ⟨d', hd'⟩ := hgdef ▸ Nat.gcd_dvd_right l (D.d i)
  have hfo : D.frobOrder l i = l' := by
    rw [frobOrder, hgdef, hl', Nat.mul_div_cancel_left _ hg]
  have hcop : Nat.Coprime l' d' := by
    have := Nat.coprime_div_gcd_div_gcd (m := l) (n := D.d i) (hgdef ▸ hg)
    rw [hgdef] at this
    rwa [hl', hd', Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg] at this
  have hlz : (l : ℤ) = g * l' := by exact_mod_cast hl'
  have hdz : (D.d i : ℤ) = g * d' := by exact_mod_cast hd'
  rw [hfo, hlz, hdz, show n * ((g : ℤ) * d') = g * (n * d') by ring,
    mul_dvd_mul_iff_left (by exact_mod_cast hg.ne')]
  constructor
  · exact fun h ↦ h.mul_right _
  · exact fun h ↦ (Nat.isCoprime_iff_coprime.2 hcop).dvd_of_dvd_mul_right h

lemma dvd_frobOrder_mul_d (hl : 0 < l) (i : I) : l ∣ D.frobOrder l i * D.d i := by
  exact_mod_cast (D.frobOrder_dvd_iff hl i _).1 dvd_rfl

/-- `lᵢ` divides `lⱼ aᵢⱼ` ([Lus] 2.2.4). -/
lemma frobOrder_dvd_mul_cartanMatrix (hl : 0 < l) (i j : I) :
    (D.frobOrder l i : ℤ) ∣ D.frobOrder l j * D.cartanMatrix i j := by
  rw [D.frobOrder_dvd_iff hl, mul_assoc, mul_comm (D.cartanMatrix i j), D.d_mul_cartanMatrix_comm,
    ← mul_assoc]
  exact (Int.natCast_dvd_natCast.2 (D.dvd_frobOrder_mul_d hl j)).mul_right _

/-- The Cartan datum `(I, ∘)`, `i ∘ j = lᵢ lⱼ (i · j)` ([Lus] 2.2.4). -/
def frobenius (hl : 0 < l) : LusztigCartanDatum I where
  dot i j := D.frobOrder l i * D.frobOrder l j * D.dot i j
  dot_comm i j := by rw [D.dot_comm]; ring
  dot_self_pos i := mul_pos (by have := D.frobOrder_pos hl i; positivity) (D.dot_self_pos i)
  even_dot_self i := (D.even_dot_self i).mul_left _
  dot_nonpos i j hij :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (D.dot_nonpos i j hij)
  dot_self_dvd i j := by
    obtain ⟨c, hc⟩ := D.frobOrder_dvd_mul_cartanMatrix hl i j
    refine ⟨c, ?_⟩
    rw [← D.two_mul_d i, ← D.d_mul_cartanMatrix]
    linear_combination (2 * (D.frobOrder l i : ℤ) * D.d i) * hc

lemma frobenius_dot (hl : 0 < l) (i j : I) :
    (D.frobenius hl).dot i j = D.frobOrder l i * D.frobOrder l j * D.dot i j := rfl

/-- `i ∘ i / 2 = lᵢ² dᵢ`. -/
lemma frobenius_d (hl : 0 < l) (i : I) : (D.frobenius hl).d i = D.frobOrder l i ^ 2 * D.d i := by
  have h := (D.frobenius hl).two_mul_d i
  rw [frobenius_dot, ← D.two_mul_d i] at h
  have : ((D.frobenius hl).d i : ℤ) = D.frobOrder l i ^ 2 * D.d i := by linarith
  exact_mod_cast this

/-- The Cartan matrix of `(I, ∘)`: `lᵢ a*ᵢⱼ = lⱼ aᵢⱼ`. -/
lemma frobOrder_mul_cartanMatrix_frobenius (hl : 0 < l) (i j : I) :
    (D.frobOrder l i : ℤ) * (D.frobenius hl).cartanMatrix i j =
      D.frobOrder l j * D.cartanMatrix i j := by
  have h := (D.frobenius hl).d_mul_cartanMatrix i j
  rw [frobenius_d, frobenius_dot, ← D.d_mul_cartanMatrix] at h
  have hi : (0 : ℤ) < D.frobOrder l i * D.d i := by
    have := D.frobOrder_pos hl i; have := D.d_pos i; positivity
  push_cast at h
  have : ((D.frobOrder l i : ℤ) * D.d i) * ((D.frobOrder l i : ℤ) *
      (D.frobenius hl).cartanMatrix i j - D.frobOrder l j * D.cartanMatrix i j) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hi.ne'
  · linarith

end LusztigCartanDatum
