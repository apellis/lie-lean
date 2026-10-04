/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.NeighborSerreShort
import LieLean.Algebra.QuantumGroup.BraidAction.NeighborSerreDegreeOne

/-!
# Neighbor-first transformed Serre relations for every pair of Cartan entries

Let `j ≠ i`, `q = vᵢ`, `r = -aᵢⱼ`, `s = -aⱼᵢ`, `p = vⱼ` (so `pˢ = qʳ`), `Q = qʳ`, and let
`X n = (ad Eᵢ)ⁿ Eⱼ` be the twisted commutators of `BraidAction/Diagonal.lean`, so that
`Tᵢ(Eⱼ) = [r]!⁻¹ X r`. By `twoNode_qSerre_braidEj_braidEi_eq` (`NeighborSerreShort.lean`) the
neighbor-first element `S_{s+1}(Tᵢ Eⱼ, Tᵢ Eᵢ)` is a multiple of the positive-part element
`serreAux p p s (X r) (X (r-1))`. We prove that this element vanishes in `U` for **all** `r, s`,
assuming `[(s+1) r - 2]_q! ≠ 0`, and deduce the neighbor-first relations for `E` and `F`.

## Main results

* `QuantumGroup.TwoNode.dd_mul`: the twisted Leibniz rule for iterated twisted derivations,
  with Gaussian binomial coefficients in `q²`.
* `QuantumGroup.TwoNode.serreAux_top_eq_zero`: in any algebra, if `X (r+1) = 0`,
  `S_{s+1}(x, e) = 0` and `[(s+1) r - 2]_q! ≠ 0`, then `serreAux p p s (X r) (X (r-1)) = 0`.
* `QuantumGroup.twoNode_serreAux_top`: the same in `U`, from its Serre relations.
* `QuantumGroup.twoNode_qSerre_braidEj_braidEi`, `QuantumGroup.twoNode_qSerre_braidFj_braidFi`:
  `S_{1-aⱼᵢ}(Tᵢ Eⱼ, Tᵢ Eᵢ) = 0` and `S_{1-aⱼᵢ}(Tᵢ Fⱼ, Tᵢ Fᵢ) = 0` for every pair of entries
  (including `aᵢⱼ = 0`), in arbitrary ambient rank, assuming `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0` and
  `[(s+1) r - 2]ᵢ! ≠ 0`.

## Method

Write `d` for the twisted derivation `z ↦ Eᵢ z - (twist) z Eᵢ`, so `dⁿ Eⱼ = X n` and
`d (X r) = 0` (`TwoNode.dd`, `TwoNode.X_eq_dd`). Peeling two twisted commutators off the Serre
element (first the one with parameter `p⁻ˢ = Q⁻¹`) gives
`S_{s+1}(Eⱼ, Eᵢ) = -Q serreAux p 1 (s-1) Eⱼ Y` with `Y = Eⱼ X 1 - Q⁻¹ X 1 Eⱼ`
(`TwoNode.qSerre_eq_serreAux_base`). The `s = 1` computation of `NeighborSerreShort.lean` gives
`d^{2r-2} Y = -Q⁻¹ α (X r X (r-1) - Q X (r-1) X r)` and `d^{2r-1} Y = 0` (`TwoNode.dd_base`,
`TwoNode.dd_base_top`). Each further twisted commutator `Z ↦ Eⱼ Z - c Z Eⱼ` is then carried by
`r` more derivations to `X r Z' - c Z' X r`, up to the nonzero factor `G(M + r, r) c₀ᴹ`,
**with the same parameter `c`** (`TwoNode.dd_step`): because `d^{M+1} Z = 0`, the only surviving
terms of the Leibniz expansion are those in which `Eⱼ` becomes `X r` and `Z` becomes `Z'`, and the
twists match since `c_Zʳ = c₀ᴹ`. Iterating (`TwoNode.dd_serreAux`) sends
`serreAux p 1 (s-1) Eⱼ Y` by `(s+1) r - 2` derivations to a nonzero multiple of
`serreAux p 1 (s-1) (X r) (X r X (r-1) - pˢ X (r-1) X r) = serreAux p p s (X r) (X (r-1))`. The
scalar is `-Q⁻¹ α ∏_{l<s-1} G(2r - 2 + (l+1) r, r) c₀^{…}`, nonzero when `[(s+1) r - 2]_q! ≠ 0`;
up to powers of `q` it is `[(s+1) r - 2]! / ([r]!ˢ [r-1]!)` in Gaussian `q²`-integers. For `s = 1`
this is the condition of `NeighborSerreShort.lean`, and for `r = 1` it is `[s-1]ᵢ! ≠ 0`
(`vᵢ² + 1 ≠ 0` for `s = 3`, as in `TripleEdgeOther.lean`).

## References

Reconstructed from the quotient presentation; this computation was not taken from a source
(the statement that `Tᵢ` is an automorphism is [Lus] Prop. 37.1.2, [Jan] Prop. 8.13,
proved there differently).
-/

open LieLean

noncomputable section

open Finset

namespace LieLean.QuantumGroup

namespace TwoNode

open BraidDiagonal ShortNode

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B] {q : k}

/-! ### Iterated twisted derivations -/

variable (q) in
/-- Iterates of the twisted derivations of `e`: the `n`-th step is `z ↦ e z - q^{2n} c z e`, so
that `dd q e c n` raises the weight of an element of twist `c` by `n αᵢ`. -/
def dd (e : B) (c : k) : ℕ → B → B
  | 0, z => z
  | n + 1, z => e * dd e c n z - (q ^ (2 * n) * c) • (dd e c n z * e)

@[simp] lemma dd_zero (e : B) (c : k) (z : B) : dd q e c 0 z = z := rfl

lemma dd_succ (e : B) (c : k) (n : ℕ) (z : B) :
    dd q e c (n + 1) z = e * dd q e c n z - (q ^ (2 * n) * c) • (dd q e c n z * e) := rfl

lemma dd_add (e : B) (c : k) (a b : ℕ) (z : B) :
    dd q e c (a + b) z = dd q e (q ^ (2 * a) * c) b (dd q e c a z) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← add_assoc, dd_succ, ih, dd_succ]
    congr 2
    rw [← mul_assoc, ← pow_add]
    ring_nf

lemma dd_sub_smul (e : B) (c : k) (n : ℕ) (z w : B) (t : k) :
    dd q e c n (z - t • w) = dd q e c n z - t • dd q e c n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dd_succ, ih, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    module

@[simp] lemma dd_zero_right (e : B) (c : k) (n : ℕ) : dd q e c n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dd_succ, ih]

lemma dd_eq_zero_of_lt {e z : B} {c : k} {n : ℕ} (h : dd q e c (n + 1) z = 0) {m : ℕ}
    (hm : n < m) : dd q e c m z = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = n + 1 + t := ⟨m - (n + 1), by omega⟩
  rw [dd_add, h, dd_zero_right]

/-- The twisted commutators of `Diagonal.lean` are iterated twisted derivations. -/
lemma X_eq_dd (e x : B) (Q : k) (n : ℕ) : X q Q e x n = dd q e Q⁻¹ n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [X_succ, ih, dd_succ]; rfl

/-- **The twisted Leibniz rule** for iterated derivations of a product:
`dᴺ (y z) = Σⱼ G(N, j) cᴺ⁻ʲ dʲ y · dᴺ⁻ʲ z`, with Gaussian binomials `G` in `q²`. -/
lemma dd_mul (hq : q ≠ 0) (e : B) (c c' : k) (N : ℕ) (y z : B) :
    dd q e (c * c') N (y * z) = ∑ j ∈ range (N + 1),
      (gauss q N j * c ^ (N - j)) • (dd q e c j y * dd q e c' (N - j) z) := by
  induction N with
  | zero => simp
  | succ N ih =>
    set Y : ℕ → B := fun j ↦ dd q e c j y with hY
    set Z : ℕ → B := fun j ↦ dd q e c' j z with hZ
    set f : ℕ → B := fun j ↦ (gauss q N j * c ^ (N - j)) • (Y (j + 1) * Z (N - j)) with hf
    set g : ℕ → B := fun j ↦ (gauss q N j * c ^ (N - j) * (q ^ (2 * j) * c)) •
      (Y j * Z (N + 1 - j)) with hg
    have key : ∀ j ∈ range (N + 1), e * ((gauss q N j * c ^ (N - j)) • (Y j * Z (N - j))) -
        (q ^ (2 * N) * (c * c')) • ((gauss q N j * c ^ (N - j)) • (Y j * Z (N - j)) * e) =
        f j + g j := by
      intro j hj
      have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
      have hp : q ^ (2 * N) = q ^ (2 * j) * q ^ (2 * (N - j)) := by
        rw [← pow_add]; congr 1; omega
      simp only [hf, hg, hY, hZ]
      rw [show N + 1 - j = N - j + 1 by omega, dd_succ e c j, dd_succ e c' (N - j), hp]
      simp only [mul_sub, sub_mul, smul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, smul_smul]
      module
    rw [dd_succ, ih, mul_sum, sum_mul, smul_sum, ← sum_sub_distrib, sum_congr rfl key,
      sum_add_distrib]
    have hg' : ∑ j ∈ range (N + 1), g j = ∑ j ∈ range N, g (j + 1) + g 0 := sum_range_succ' _ _
    have hR := sum_range_succ' (fun j ↦ (gauss q (N + 1) j * c ^ (N + 1 - j)) •
      (Y j * Z (N + 1 - j))) (N + 1)
    rw [hR, hg']
    have hh : ∑ j ∈ range (N + 1), (gauss q (N + 1) (j + 1) * c ^ (N + 1 - (j + 1))) •
        (Y (j + 1) * Z (N + 1 - (j + 1))) = ∑ j ∈ range (N + 1), f j +
          ∑ j ∈ range N, g (j + 1) := by
      rw [sum_range_succ _ N]
      have hN : (gauss q (N + 1) (N + 1) * c ^ (N + 1 - (N + 1))) •
          (Y (N + 1) * Z (N + 1 - (N + 1))) = f N := by
        simp [hf, gauss]
      rw [hN, sum_range_succ f N, add_right_comm _ (f N), ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun j hj ↦ ?_
      have hj := mem_range.1 hj
      simp only [hf, hg, gauss_succ_succ hq,
        show N + 1 - (j + 1) = N - j by omega]
      rw [show N - j = N - (j + 1) + 1 by omega, pow_succ]
      simp only [add_smul, add_mul]
      module
    have h0 : (gauss q (N + 1) 0 * c ^ (N + 1 - 0)) • (Y 0 * Z (N + 1 - 0)) = g 0 := by
      simp [hg, gauss, pow_succ]
    rw [hh, h0, add_assoc]

lemma gauss_add_symm (a b : ℕ) :
    gauss q (a + b) a = gauss q (a + b) b := by
  have h := qBinomial_symm q (show b ≤ a + b by omega)
  rw [show a + b - b = a by omega] at h
  simp only [gauss, h, show a + b - a = b by omega, show a + b - b = a by omega, mul_comm a b]

/-! ### Propagating a twisted commutator with `x` -/

/-- **One twisted commutator with `x`.** Let `x` be killed by `r + 1` derivations (twist `c₀`)
and `Z` by `M + 1` derivations (twist `c_Z`), with `c_Zʳ = c₀ᴹ`. Then `M + r` derivations send
`x Z - c Z x` to a multiple of `Xᵣ Z' - c Z' Xᵣ` (`Xᵣ = dʳ x`, `Z' = dᴹ Z`), and `M + r + 1`
derivations kill it. -/
lemma dd_step (hq : q ≠ 0) {e x : B} {c0 : k} {r : ℕ} (hX : dd q e c0 (r + 1) x = 0)
    {cZ : k} {M : ℕ} {Z Z' : B} (htw : cZ ^ r = c0 ^ M) (h1 : dd q e cZ (M + 1) Z = 0)
    (h0 : dd q e cZ M Z = Z') (c : k) :
    dd q e (c0 * cZ) (M + r) (x * Z - c • (Z * x)) =
        (gauss q (M + r) r * c0 ^ M) • (dd q e c0 r x * Z' - c • (Z' * dd q e c0 r x)) ∧
      dd q e (c0 * cZ) (M + r + 1) (x * Z - c • (Z * x)) = 0 := by
  have hsw : c0 * cZ = cZ * c0 := mul_comm _ _
  have hXv : ∀ j, r < j → dd q e c0 j x = 0 := fun j hj ↦ dd_eq_zero_of_lt hX hj
  have hZv : ∀ j, M < j → dd q e cZ j Z = 0 := fun j hj ↦ dd_eq_zero_of_lt h1 hj
  have s1 : ∑ j ∈ range (M + r + 1), (gauss q (M + r) j * c0 ^ (M + r - j)) •
      (dd q e c0 j x * dd q e cZ (M + r - j) Z) =
      (gauss q (M + r) r * c0 ^ M) • (dd q e c0 r x * Z') := by
    rw [sum_eq_single r]
    · rw [show M + r - r = M by omega, h0]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hZv (M + r - j) (by omega), mul_zero, smul_zero]
      · rw [hXv j h, zero_mul, smul_zero]
    · intro h
      exact absurd (mem_range.2 (by omega)) h
  have s2 : ∑ j ∈ range (M + r + 1), (gauss q (M + r) j * cZ ^ (M + r - j)) •
      (dd q e cZ j Z * dd q e c0 (M + r - j) x) =
      (gauss q (M + r) r * c0 ^ M) • (Z' * dd q e c0 r x) := by
    rw [sum_eq_single M]
    · rw [show M + r - M = r by omega, h0, gauss_add_symm, htw]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hXv (M + r - j) (by omega), mul_zero, smul_zero]
      · rw [hZv j h, zero_mul, smul_zero]
    · intro h
      exact absurd (mem_range.2 (by omega)) h
  refine ⟨?_, ?_⟩
  · rw [dd_sub_smul, dd_mul hq, hsw, dd_mul hq, s1, s2]
    simp only [smul_sub, smul_smul]
    rw [mul_comm c]
  · rw [dd_sub_smul, dd_mul hq, hsw, dd_mul hq, sum_eq_zero, sum_eq_zero, smul_zero, sub_zero]
    · intro j hj
      have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
      by_cases h : M < j
      · rw [hZv j h, zero_mul, smul_zero]
      · rw [hXv (M + r + 1 - j) (by omega), mul_zero, smul_zero]
    · intro j hj
      have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
      by_cases h : r < j
      · rw [hXv j h, zero_mul, smul_zero]
      · rw [hZv (M + r + 1 - j) (by omega), mul_zero, smul_zero]

/-- **Iterating the step** through a rescaled Serre element `serreAux p c m x Z`: its
`M + m r`-th derivative is a nonzero multiple of `serreAux p c m Xᵣ Z'`, and one more
derivative kills it. -/
lemma dd_serreAux (hq : q ≠ 0) {e x : B} {c0 p : k} (hc0 : c0 ≠ 0) (hp : p ≠ 0) {r : ℕ}
    (hX : dd q e c0 (r + 1) x = 0) (m : ℕ) : ∀ (c cZ : k) (M : ℕ) (Z Z' : B),
    cZ ^ r = c0 ^ M → dd q e cZ (M + 1) Z = 0 → dd q e cZ M Z = Z' →
    (∀ l < m, gauss q (M + (l + 1) * r) r ≠ 0) →
    ∃ K : k, K ≠ 0 ∧
      dd q e (c0 ^ m * cZ) (M + m * r) (serreAux p c m x Z) =
        K • serreAux p c m (dd q e c0 r x) Z' ∧
      dd q e (c0 ^ m * cZ) (M + m * r + 1) (serreAux p c m x Z) = 0 := by
  induction m with
  | zero =>
    intro c cZ M Z Z' _ h1 h0 _
    refine ⟨1, one_ne_zero, ?_, ?_⟩ <;> simp [serreAux, h0, h1]
  | succ m ih =>
    intro c cZ M Z Z' htw h1 h0 hG
    obtain ⟨hs0, hs1⟩ := dd_step hq hX htw h1 h0 (c * p ^ m)
    have htw' : (c0 * cZ) ^ r = c0 ^ (M + r) := by rw [mul_pow, htw, ← pow_add, add_comm]
    have hG' : ∀ l < m, gauss q (M + r + (l + 1) * r) r ≠ 0 := fun l hl ↦ by
      have := hG (l + 1) (by omega)
      rwa [show M + (l + 1 + 1) * r = M + r + (l + 1) * r by ring] at this
    obtain ⟨K, hK, e0, e1⟩ := ih (c * p⁻¹) (c0 * cZ) (M + r) _ _ htw' hs1 hs0 hG'
    have hG0 : gauss q (M + r) r ≠ 0 := by simpa using hG 0 (by omega)
    refine ⟨K * (gauss q (M + r) r * c0 ^ M),
      mul_ne_zero hK (mul_ne_zero hG0 (pow_ne_zero _ hc0)), ?_, ?_⟩
    · rw [serreAux_succ hp, show c0 ^ (m + 1) * cZ = c0 ^ m * (c0 * cZ) by ring,
        show M + (m + 1) * r = M + r + m * r by ring, e0, serreAux_smul_right, smul_smul,
        ← serreAux_succ hp]
    · rw [serreAux_succ hp, show c0 ^ (m + 1) * cZ = c0 ^ m * (c0 * cZ) by ring,
        show M + (m + 1) * r + 1 = M + r + m * r + 1 by ring, e1]

/-! ### The base case: the first twisted commutator `x X₁ - Q⁻¹ X₁ x` -/

/-- `2n + 1` derivations kill `x X₁ - Q⁻¹ X₁ x` (`Q = q^{n+1}`) when `X (n+2) = 0`. -/
lemma dd_base_top (hq : q ≠ 0) {e x : B} {n : ℕ}
    (hX : dd q e (q ^ (n + 1))⁻¹ (n + 2) x = 0) :
    dd q e ((q ^ (n + 1))⁻¹ * (q ^ (2 * 1) * (q ^ (n + 1))⁻¹)) (2 * n + 1)
      (x * dd q e (q ^ (n + 1))⁻¹ 1 x -
        (q ^ (n + 1))⁻¹ • (dd q e (q ^ (n + 1))⁻¹ 1 x * x)) = 0 := by
  set c0 := (q ^ (n + 1))⁻¹ with hc0
  have hX1 (j : ℕ) : dd q e (q ^ (2 * 1) * c0) j (dd q e c0 1 x) = dd q e c0 (1 + j) x :=
    (dd_add e c0 1 j x).symm
  have hXv : ∀ j, n + 1 < j → dd q e c0 j x = 0 := fun j hj ↦ dd_eq_zero_of_lt hX hj
  have hcq : c0 * q ^ (n + 1) = 1 := inv_mul_cancel₀ (pow_ne_zero _ hq)
  have hc : c0 * (q ^ (2 * 1) * c0) ^ (n + 1) = c0 ^ n := by
    linear_combination (c0 ^ n * (c0 * q ^ (n + 1) + 1)) * hcq
  rw [dd_sub_smul, dd_mul hq, show c0 * (q ^ (2 * 1) * c0) = q ^ (2 * 1) * c0 * c0 from
    mul_comm _ _, dd_mul hq, sum_eq_single (n + 1), sum_eq_single n]
  · rw [hX1, hX1, show 1 + (2 * n + 1 - (n + 1)) = n + 1 by omega, show 1 + n = n + 1 by ring,
      show 2 * n + 1 - n = n + 1 by omega, show 2 * n + 1 - (n + 1) = n by omega,
      show 2 * n + 1 = n + (n + 1) by ring, gauss_add_symm, smul_smul, ← sub_smul]
    rw [show gauss q (n + (n + 1)) (n + 1) * c0 ^ n -
        c0 * (gauss q (n + (n + 1)) (n + 1) * (q ^ (2 * 1) * c0) ^ (n + 1)) = 0 by
      linear_combination (-gauss q (n + (n + 1)) (n + 1)) * hc, zero_smul]
  · intro j hj hjn
    have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
    rcases lt_or_gt_of_ne hjn with h | h
    · rw [hXv (2 * n + 1 - j) (by omega), mul_zero, smul_zero]
    · rw [hX1, hXv (1 + j) (by omega), zero_mul, smul_zero]
  · intro h
    exact absurd (mem_range.2 (by omega)) h
  · intro j hj hjn
    have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
    rcases lt_or_gt_of_ne hjn with h | h
    · rw [hX1, hXv (1 + (2 * n + 1 - j)) (by omega), mul_zero, smul_zero]
    · rw [hXv j h, zero_mul, smul_zero]
  · intro h
    exact absurd (mem_range.2 (by omega)) h

/-- `2n` derivations send `x X₁ - Q⁻¹ X₁ x` (`Q = q^{n+1}`) to
`-Q⁻¹ α • (X (n+1) X n - Q X n X (n+1))` when `X (n+2) = 0` (the `s = 1` computation). -/
lemma dd_base (hq : q ≠ 0) {e x : B} {n : ℕ} (hX : dd q e (q ^ (n + 1))⁻¹ (n + 2) x = 0) :
    dd q e ((q ^ (n + 1))⁻¹ * (q ^ (2 * 1) * (q ^ (n + 1))⁻¹)) (2 * n)
      (x * dd q e (q ^ (n + 1))⁻¹ 1 x - (q ^ (n + 1))⁻¹ • (dd q e (q ^ (n + 1))⁻¹ 1 x * x)) =
    (-(q ^ (n + 1))⁻¹ * coeff q n) •
      (dd q e (q ^ (n + 1))⁻¹ (n + 1) x * dd q e (q ^ (n + 1))⁻¹ n x -
        q ^ (n + 1) • (dd q e (q ^ (n + 1))⁻¹ n x * dd q e (q ^ (n + 1))⁻¹ (n + 1) x)) := by
  cases n with
  | zero =>
    simp only [zero_add, pow_one, mul_zero, dd_zero, coeff_zero, mul_one]
    rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hq]
    module
  | succ m =>
    set c0 := (q ^ (m + 1 + 1))⁻¹ with hc0
    have hX1 (j : ℕ) : dd q e (q ^ (2 * 1) * c0) j (dd q e c0 1 x) = dd q e c0 (1 + j) x :=
      (dd_add e c0 1 j x).symm
    have hXv : ∀ j, m + 1 + 1 < j → dd q e c0 j x = 0 := fun j hj ↦ dd_eq_zero_of_lt hX hj
    have hcq : c0 * q ^ (m + 1 + 1) = 1 := inv_mul_cancel₀ (pow_ne_zero _ hq)
    have hA := coef_top hq m
    have hB := coef_next hq m
    simp only [shift, show m + 2 = m + 1 + 1 from rfl] at hA hB
    rw [← hc0] at hA hB
    rw [dd_sub_smul, dd_mul hq, show c0 * (q ^ (2 * 1) * c0) = q ^ (2 * 1) * c0 * c0 from
      mul_comm _ _, dd_mul hq,
      sum_eq_add_of_mem (m + 1) (m + 1 + 1) (mem_range.2 (by omega)) (mem_range.2 (by omega))
        (by omega),
      sum_eq_add_of_mem m (m + 1) (mem_range.2 (by omega)) (mem_range.2 (by omega)) (by omega)]
    · rw [hX1, hX1, hX1, hX1]
      simp only [show 2 * (m + 1) - (m + 1) = m + 1 by omega,
        show 2 * (m + 1) - (m + 1 + 1) = m by omega, show 2 * (m + 1) - m = m + 1 + 1 by omega,
        show 1 + (m + 1) = m + 1 + 1 by omega, show 1 + m = m + 1 by omega] at hA hB ⊢
      set G0 := gauss q (2 * (m + 1)) m
      set G1 := gauss q (2 * (m + 1)) (m + 1)
      set G2 := gauss q (2 * (m + 1)) (m + 1 + 1)
      set c1 := q ^ (2 * 1) * c0
      have eP : G2 * c0 ^ m - c0 * (G1 * c1 ^ (m + 1)) = -c0 * coeff q (m + 1) := by
        linear_combination (-c0) * hA - (G2 * c0 ^ m) * hcq
      have eR : G1 * c0 ^ (m + 1) - c0 * (G0 * c1 ^ (m + 1 + 1)) =
          -(-c0 * coeff q (m + 1) * q ^ (m + 1 + 1)) := by
        linear_combination (-c0) * hB - (G1 * c0 ^ (m + 1)) * hcq
      linear_combination (norm := module)
        eP • (dd q e c0 (m + 1 + 1) x * dd q e c0 (m + 1) x) +
          eR • (dd q e c0 (m + 1) x * dd q e c0 (m + 1 + 1) x)
    · intro j hj hjn
      have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
      rcases lt_or_gt_of_ne hjn.1 with h | h
      · rw [hXv (2 * (m + 1) - j) (by omega), mul_zero, smul_zero]
      · rw [hX1, hXv (1 + j) (by omega), zero_mul, smul_zero]
    · intro j hj hjn
      have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
      rcases lt_or_gt_of_ne hjn.1 with h | h
      · rw [hX1, hXv (1 + (2 * (m + 1) - j)) (by omega), mul_zero, smul_zero]
      · rw [hXv j (by omega), zero_mul, smul_zero]

/-! ### The positive-part identity -/

omit [Ring B] [Algebra k B] in
lemma qFactorial_ne_zero_of_le {a N : ℕ} (h : a ≤ N) (hN : qFactorial q N ≠ 0) :
    qFactorial q a ≠ 0 := by
  induction N with
  | zero => obtain rfl : a = 0 := by omega
            exact hN
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact hN
    · exact ih (by omega) (right_ne_zero_of_mul (by rwa [qFactorial_succ] at hN))

omit [Ring B] [Algebra k B] in
lemma gauss_ne_zero {a b : ℕ} (hq : q ≠ 0) (h : qFactorial q (a + b) ≠ 0) :
    gauss q (a + b) b ≠ 0 := by
  have hb := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show b ≤ a + b by omega)
  refine mul_ne_zero (pow_ne_zero _ hq) fun h0 ↦ h ?_
  rw [← hb, h0, zero_mul, zero_mul]

omit [Ring B] [Algebra k B] in
lemma coeff_ne_zero_of_qFactorial (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) {n : ℕ}
    (h : qFactorial q (2 * n) ≠ 0) : coeff q n ≠ 0 := by
  refine coeff_ne_zero hq hd fun h0 ↦ h ?_
  have hb := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show n ≤ 2 * n by omega)
  rw [← hb, h0, zero_mul, zero_mul]

/-- Peeling two twisted commutators off `S_{s+2}(x, e)`: it is `-Q • serreAux p 1 s x Y` with
`Y = x X₁ - Q⁻¹ X₁ x`, `X₁ = e x - Q⁻¹ x e`, where `p^{s+1} = Q`. -/
lemma qSerre_eq_serreAux_base {p Q : k} (hp : p ≠ 0) {s : ℕ} (hps : p ^ (s + 1) = Q)
    (e x : B) :
    qSerre p (s + 2) x e = (-Q) • serreAux p 1 s x
      (x * dd q e Q⁻¹ 1 x - Q⁻¹ • (dd q e Q⁻¹ 1 x * x)) := by
  have h1 : x * e - Q • (e * x) = (-Q) • dd q e Q⁻¹ 1 x := by
    have hQ : Q ≠ 0 := by rw [← hps]; exact pow_ne_zero _ hp
    rw [dd_succ, dd_zero, pow_zero, one_mul, smul_sub, smul_smul, neg_mul,
      mul_inv_cancel₀ hQ]
    module
  have h2 : p⁻¹ * p⁻¹ ^ s = Q⁻¹ := by rw [← pow_succ', inv_pow, hps]
  rw [← serreAux_one, serreAux_succ hp, one_mul, one_mul, hps, h1, serreAux_smul_right,
    ← serreAux_inv p, serreAux_succ (inv_ne_zero hp), h2, inv_inv, inv_mul_cancel₀ hp,
    serreAux_inv]

/-- **The positive-part identity for every pair of Cartan entries.** Let `Q = q^{n+1}`,
`X m = X q Q e x m` (so `X (n+2) = 0` is the Serre relation `S_{n+2}(e, x) = 0`), and let
`p^{s+1} = Q`. If `S_{s+2}(x, e) = 0` and `[(s+2)(n+1) - 2]_q! ≠ 0`, then
`serreAux p p (s+1) (X (n+1)) (X n) = 0`. -/
theorem serreAux_top_eq_zero (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) {e x : B} {n s : ℕ} {p : k}
    (hp : p ≠ 0) (hps : p ^ (s + 1) = q ^ (n + 1)) (hS : X q (q ^ (n + 1)) e x (n + 2) = 0)
    (hT : qSerre p (s + 2) x e = 0) (hN : qFactorial q ((s + 2) * (n + 1) - 2) ≠ 0) :
    serreAux p p (s + 1) (X q (q ^ (n + 1)) e x (n + 1)) (X q (q ^ (n + 1)) e x n) = 0 := by
  rw [X_eq_dd] at hS
  rw [X_eq_dd, X_eq_dd]
  rw [Nat.sub_eq_of_eq_add (show (s + 2) * (n + 1) = 2 * n + s * (n + 1) + 2 by ring)] at hN
  set Q := q ^ (n + 1) with hQdef
  have hQ : Q ≠ 0 := pow_ne_zero _ hq
  set c0 := Q⁻¹ with hc0
  have hc0' : c0 ≠ 0 := inv_ne_zero hQ
  set Y := x * dd q e c0 1 x - c0 • (dd q e c0 1 x * x) with hY
  have hT' : serreAux p 1 s x Y = 0 := by
    rw [qSerre_eq_serreAux_base (q := q) hp hps] at hT
    exact (smul_eq_zero.1 hT).resolve_left (neg_ne_zero.2 hQ)
  have hX : dd q e c0 (n + 1 + 1) x = 0 := hS
  have htw : (c0 * (q ^ (2 * 1) * c0)) ^ (n + 1) = c0 ^ (2 * n) := by
    have hcq : c0 * Q = 1 := inv_mul_cancel₀ hQ
    linear_combination (c0 ^ (2 * n) * (c0 * Q + 1)) * hcq
  have hG : ∀ l < s, gauss q (2 * n + (l + 1) * (n + 1)) (n + 1) ≠ 0 := by
    intro l hl
    rw [show 2 * n + (l + 1) * (n + 1) = (2 * n + l * (n + 1)) + (n + 1) by ring]
    exact gauss_ne_zero hq (qFactorial_ne_zero_of_le (by nlinarith) hN)
  obtain ⟨K, hK, e0, -⟩ := dd_serreAux hq hc0' hp hX s 1 _ (2 * n) Y _ htw
    (dd_base_top hq hS) (dd_base hq hS) hG
  rw [hT', dd_zero_right, serreAux_smul_right, smul_smul] at e0
  have hα : coeff q n ≠ 0 :=
    coeff_ne_zero_of_qFactorial hq hd (qFactorial_ne_zero_of_le (Nat.le_add_right _ _) hN)
  have hcoef : K * (-c0 * coeff q n) ≠ 0 :=
    mul_ne_zero hK (mul_ne_zero (neg_ne_zero.2 hc0') hα)
  have e1 := (smul_eq_zero.1 e0.symm).resolve_left hcoef
  rw [serreAux_succ hp, mul_inv_cancel₀ hp, ← pow_succ', hps]
  exact e1

end TwoNode

/-! ### The quantum group -/

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

omit [DecidableEq I] in
/-- If `aᵢⱼ ≠ 0` then also `aⱼᵢ ≠ 0`, so both `-aᵢⱼ` and `-aⱼᵢ` are positive. -/
lemma twoNode_negA_pos {i j : I} (hij : i ≠ j) (h : D.cartanMatrix i j ≠ 0) :
    0 < negA D i j ∧ 0 < negA D j i := by
  have h' : D.cartanMatrix j i ≠ 0 := fun h0 ↦
    h ((D.isGeneralizedCartan_cartanMatrix.zero_comm i j).2 h0)
  have e1 := cartanMatrix_eq_neg_negA (D := D) hij
  have e2 := cartanMatrix_eq_neg_negA (D := D) hij.symm
  constructor
  · rcases Nat.eq_zero_or_pos (negA D i j) with h0 | h0
    · exact absurd (by rw [e1, h0]; simp) h
    · exact h0
  · rcases Nat.eq_zero_or_pos (negA D j i) with h0 | h0
    · exact absurd (by rw [e2, h0]; simp) h'
    · exact h0

/-- **The positive-part identity in `U` for every pair of Cartan entries**: for `j ≠ i`,
`r = -aᵢⱼ = n + 1`, `s = -aⱼᵢ`, `serreAux vⱼ vⱼ s (X r) (X (r-1)) = 0`, from the two Serre
relations of `U`, assuming `vᵢ - vᵢ⁻¹ ≠ 0` and `[(s+1) r - 2]ᵢ! ≠ 0`. -/
theorem twoNode_serreAux_top [NeZero v] {i j : I} (hij : i ≠ j)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) {n : ℕ} (hn : negA D i j = n + 1)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    serreAux (v ^ D.d j) (v ^ D.d j) (negA D j i)
      (BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ (n + 1)) (E R v i) (E R v j) (n + 1))
      (BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ (n + 1)) (E R v i) (E R v j) n) = 0 := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hQ : (v ^ D.d i) ^ (n + 1) ≠ 0 := pow_ne_zero _ hq0
  obtain ⟨s, hs⟩ : ∃ s, negA D j i = s + 1 := by
    have := (twoNode_negA_pos (D := D) hij (by rw [cartanMatrix_eq_neg_negA hij, hn]; omega)).2
    exact ⟨negA D j i - 1, by omega⟩
  have hps : (v ^ D.d j) ^ (s + 1) = (v ^ D.d i) ^ (n + 1) := by
    rw [← hs, ← hn]; exact twoNode_param_pow hij
  rw [hs]
  rw [hs, hn] at hN
  refine TwoNode.serreAux_top_eq_zero hq0 hq (pow_ne_zero _ hv) hps ?_ ?_ hN
  · have hc : (v ^ D.d i) ^ (n + 2) * (v ^ D.d i * (v ^ D.d i) ^ (n + 1))⁻¹ = 1 := by
      field_simp
      ring
    rw [BraidDiagonal.X_eq_serreAux hq0 hQ, hc, serreAux_one]
    have h := serre_E R v hij
    rwa [one_sub_cartanMatrix_toNat hij, hn] at h
  · have h := serre_E R v hij.symm
    rwa [one_sub_cartanMatrix_toNat hij.symm, hs] at h

/-- The neighbor-first relation when `aᵢⱼ = aⱼᵢ = 0`: `Tᵢ Eⱼ = Eⱼ` commutes with `Tᵢ Eᵢ`. -/
theorem twoNode_qSerre_braidEj_braidEi_of_zero [NeZero v] {i j : I} (hij : i ≠ j)
    (h0 : negA D i j = 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat (braidEj R v i j) (braidEi R i) = 0 := by
  have ha : D.cartanMatrix i j = 0 := by rw [cartanMatrix_eq_neg_negA hij, h0]; simp
  have ha' : D.cartanMatrix j i = 0 := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).1 ha
  have hE : braidEj R v i j = E R v j := by simp [braidEj, h0, serreAux]
  have hK : Kt R v i * E R v j = E R v j * Kt R v i := by
    rw [Kt, K_mul_E, root_ktilde, ha, mul_zero, zpow_zero, one_smul]
  have key : E R v j * (F R v i * Kt R v i) = F R v i * Kt R v i * E R v j := by
    rw [← mul_assoc, E_mul_F_of_ne hij.symm, mul_assoc, ← hK, mul_assoc]
  have hq1 (a b : QuantumGroup R v) : qSerre (v ^ D.d j) 1 a b = a * b - b * a := by
    simp [qSerre, Finset.sum_range_succ, sub_eq_add_neg]
  rw [ha', show (1 - (0 : ℤ)).toNat = 1 from rfl, hE, hq1, braidEi, mul_neg, neg_mul, key,
    sub_neg_eq_add, neg_add_cancel]

/-- **The neighbor-first transformed Serre relation for every pair of Cartan entries**: for
`j ≠ i`, `S_{1-aⱼᵢ}(Tᵢ Eⱼ, Tᵢ Eᵢ) = 0` in arbitrary ambient rank, assuming `v ≠ 0`,
`vᵢ - vᵢ⁻¹ ≠ 0` and `[(s+1) r - 2]ᵢ! ≠ 0` (`r = -aᵢⱼ`, `s = -aⱼᵢ`). -/
theorem twoNode_qSerre_braidEj_braidEi [NeZero v] {i j : I} (hij : i ≠ j)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat (braidEj R v i j) (braidEi R i) = 0 := by
  rcases Nat.eq_zero_or_pos (negA D i j) with h0 | h0
  · exact twoNode_qSerre_braidEj_braidEi_of_zero hij h0
  · obtain ⟨n, hn⟩ : ∃ n, negA D i j = n + 1 := ⟨negA D i j - 1, by omega⟩
    rw [twoNode_qSerre_braidEj_braidEi_eq hij hq hn, twoNode_serreAux_top hij hq hn hN,
      smul_zero]

/-- The negative neighbor-first transformed Serre relation for every pair of Cartan entries. -/
theorem twoNode_qSerre_braidFj_braidFi [NeZero v] {i j : I} (hij : i ≠ j)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat (braidFj R v i j) (braidFi R i) = 0 :=
  twoNode_qSerre_braidFj_braidFi_of_braidEj (twoNode_qSerre_braidEj_braidEi hij hq hN)

end LieLean.QuantumGroup
