/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction

/-!
# Lusztig's braid group automorphisms `Tᵢ`: the images of `Eⱼ`, `Fⱼ`, `j ≠ i`

Continuing `QuantumGroup/BraidAction.lean`, for `j ≠ i`, `r = -aᵢⱼ` and `q = vᵢ = v^{dᵢ}` we define
([Jan] 8.14, [Lus] 37.1.3, variant `T''_{i,1}`)
* `Tᵢ(Eⱼ) = Σ_{s=0}^{r} (-1)^s q^{-s} Eᵢ^{(r-s)} Eⱼ Eᵢ^{(s)}`,
* `Tᵢ(Fⱼ) = Σ_{s=0}^{r} (-1)^s q^{s} Fᵢ^{(s)} Fⱼ Fᵢ^{(r-s)}`.
For computations it is convenient to write them through the rescaled Serre elements
`serreAux q q⁻¹ r a b = Σ_t (-1)^t [r t]_q q^{-t} a^{r-t} b a^t` of `QuantumGroup/QBinomial.lean`
(this is how we define them, `QuantumGroup.braidEj`, `QuantumGroup.braidFj`; the divided-power
formulas above are `QuantumGroup.braidEj_eq_sum`, `QuantumGroup.braidFj_eq_sum`). The outer
recursion `serreAux_succ'` shows that `serreAux q 1 (r+1) a b = a S - q^r S a` with
`S = serreAux q q⁻¹ r a b`; since `serreAux q 1 (r+1) Fᵢ Fⱼ` is the quantum Serre element, which
vanishes in `U`, we get `Fᵢ Tᵢ(Fⱼ) = q^r Tᵢ(Fⱼ) Fᵢ`, and likewise for `E`. This is the heart of
the relations (d) between `Tᵢ(Eᵢ)` and `Tᵢ(Fⱼ)`, and between `Tᵢ(Eⱼ)` and `Tᵢ(Fᵢ)`
(our own write-up of the standard computation).

## Main definitions

* `QuantumGroup.braidEj`, `QuantumGroup.braidFj`: the images `Tᵢ(Eⱼ)`, `Tᵢ(Fⱼ)` for `j ≠ i`.

## Main results

For `j ≠ i`:
* `QuantumGroup.braidK_mul_braidEj`, `QuantumGroup.braidK_mul_braidFj`: relations (b), (c);
* `QuantumGroup.braidEi_mul_braidFj_sub`, `QuantumGroup.braidEj_mul_braidFi_sub`: relation (d)
  for the pairs `(i, j)` and `(j, i)`.

Together with `QuantumGroup/BraidAction.lean` this verifies all defining relations of `U` for the
proposed images `Tᵢ(Eₗ)`, `Tᵢ(Fₗ)`, `Tᵢ(K_μ)` except: relation (d) for pairs `(j, j')` with
`j, j' ≠ i`, and the quantum Serre relations. These are not proved here.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §37.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 8.
-/

open LieLean

noncomputable section

open Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k]

/-! ### Divided-power sums and rescaled Serre elements -/

section Ring

variable {B : Type*} [Ring B] [Algebra k B]

/-- `Σ_s (-1)^s q^{-s} a^{(r-s)} b a^{(s)} = [r]!⁻¹ Σ_s (-1)^s [r s] q^{-s} a^{r-s} b a^s`. -/
theorem sum_qDivPow_eq_serreAux_left {q : k} {r : ℕ} (hr : qFactorial q r ≠ 0) (a b : B) :
    ∑ s ∈ range (r + 1), ((-1 : k) ^ s * q⁻¹ ^ s) • (qDivPow q (r - s) a * b * qDivPow q s a) =
      (qFactorial q r)⁻¹ • serreAux q q⁻¹ r a b := by
  rw [serreAux, smul_sum]
  refine sum_congr rfl fun s hs ↦ ?_
  have hs : s ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hs)
  have h := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hs
  have h1 : qFactorial q s ≠ 0 := fun h0 ↦ hr (by rw [← h, h0]; ring)
  have h2 : qFactorial q (r - s) ≠ 0 := fun h0 ↦ hr (by rw [← h, h0]; ring)
  have h3 : qBinomial q r s ≠ 0 := fun h0 ↦ hr (by rw [← h, h0]; ring)
  simp only [qDivPow, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← h]
  field_simp

/-- `Σ_s (-1)^s q^{s} a^{(s)} b a^{(r-s)} =
(-1)^r q^r [r]!⁻¹ Σ_t (-1)^t [r t] q^{-t} a^{r-t} b a^t`. -/
theorem sum_qDivPow_eq_serreAux_right {q : k} (hq : q ≠ 0) {r : ℕ} (hr : qFactorial q r ≠ 0)
    (a b : B) :
    ∑ s ∈ range (r + 1), ((-1 : k) ^ s * q ^ s) • (qDivPow q s a * b * qDivPow q (r - s) a) =
      ((qFactorial q r)⁻¹ * (-1) ^ r * q ^ r) • serreAux q q⁻¹ r a b := by
  rw [← sum_range_reflect, serreAux, smul_sum]
  refine sum_congr rfl fun s hs ↦ ?_
  have hs : s ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hs)
  rw [show r + 1 - 1 - s = r - s by omega, show r - (r - s) = s by omega]
  have h := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hs
  have h1 : qFactorial q s ≠ 0 := fun h0 ↦ hr (by rw [← h, h0]; ring)
  have h2 : qFactorial q (r - s) ≠ 0 := fun h0 ↦ hr (by rw [← h, h0]; ring)
  have hsign : (-1 : k) ^ r = (-1) ^ (r - s) * (-1) ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have hpow : q ^ r = q ^ (r - s) * q ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have hqs : q ^ s * q⁻¹ ^ s = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
  have hss : (-1 : k) ^ s * (-1) ^ s = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have h3 : qBinomial q r s ≠ 0 := fun h0 ↦ hr (by rw [← h, h0]; ring)
  simp only [qDivPow, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← h, hsign, hpow]
  field_simp
  rw [sq, hss, one_mul, one_div, hqs]

end Ring

/-! ### The images `Tᵢ(Eⱼ)`, `Tᵢ(Fⱼ)` -/

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

variable (D) in
/-- `r = -aᵢⱼ` as a natural number. -/
abbrev negA (i j : I) : ℕ := (-D.cartanMatrix i j).toNat

omit [DecidableEq I] in
lemma cartanMatrix_eq_neg_negA {i j : I} (hij : i ≠ j) :
    D.cartanMatrix i j = -(negA D i j : ℤ) := by
  have := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos i j hij
  simp only [negA]
  omega

omit [DecidableEq I] in
lemma one_sub_cartanMatrix_toNat {i j : I} (hij : i ≠ j) :
    (1 - D.cartanMatrix i j).toNat = negA D i j + 1 := by
  have := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos i j hij
  simp only [negA]
  omega

variable (R v) in
/-- `Tᵢ(Eⱼ) = [r]ᵢ!⁻¹ Σ_t (-1)^t [r t]ᵢ vᵢ^{-t} Eᵢ^{r-t} Eⱼ Eᵢ^t` (`r = -aᵢⱼ`), which equals
`Σ_s (-1)^s vᵢ^{-s} Eᵢ^{(r-s)} Eⱼ Eᵢ^{(s)}` ([Jan] 8.14) by `braidEj_eq_sum`. -/
def braidEj (i j : I) : QuantumGroup R v :=
  (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
    serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (E R v i) (E R v j)

variable (R v) in
/-- `Tᵢ(Fⱼ) = (-1)^r vᵢ^r [r]ᵢ!⁻¹ Σ_t (-1)^t [r t]ᵢ vᵢ^{-t} Fᵢ^{r-t} Fⱼ Fᵢ^t` (`r = -aᵢⱼ`), which
equals `Σ_s (-1)^s vᵢ^{s} Fᵢ^{(s)} Fⱼ Fᵢ^{(r-s)}` ([Jan] 8.14) by `braidFj_eq_sum`. -/
def braidFj (i j : I) : QuantumGroup R v :=
  ((qFactorial (v ^ D.d i) (negA D i j))⁻¹ * (-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j) •
    serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (F R v i) (F R v j)

/-- The divided-power formula for `Tᵢ(Eⱼ)` ([Jan] 8.14). -/
theorem braidEj_eq_sum {i j : I} (hr : qFactorial (v ^ D.d i) (negA D i j) ≠ 0) :
    braidEj R v i j = ∑ s ∈ range (negA D i j + 1), ((-1 : k) ^ s * (v ^ D.d i)⁻¹ ^ s) •
      (qDivPow (v ^ D.d i) (negA D i j - s) (E R v i) * E R v j *
        qDivPow (v ^ D.d i) s (E R v i)) :=
  (sum_qDivPow_eq_serreAux_left hr _ _).symm

/-- The divided-power formula for `Tᵢ(Fⱼ)` ([Jan] 8.14). -/
theorem braidFj_eq_sum (hv : v ≠ 0) {i j : I} (hr : qFactorial (v ^ D.d i) (negA D i j) ≠ 0) :
    braidFj R v i j = ∑ s ∈ range (negA D i j + 1), ((-1 : k) ^ s * (v ^ D.d i) ^ s) •
      (qDivPow (v ^ D.d i) s (F R v i) * F R v j *
        qDivPow (v ^ D.d i) (negA D i j - s) (F R v i)) :=
  (sum_qDivPow_eq_serreAux_right (pow_ne_zero _ hv) hr _ _).symm

/-- `Eᵢ S = vᵢ^r S Eᵢ` for `S = serreAux vᵢ vᵢ⁻¹ r Eᵢ Eⱼ`, by the quantum Serre relation. -/
lemma E_mul_serreAux (hv : v ≠ 0) {i j : I} (hij : i ≠ j) :
    E R v i * serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (E R v i) (E R v j) =
      (v ^ D.d i) ^ negA D i j •
        (serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (E R v i) (E R v j) * E R v i) := by
  have h := serreAux_succ' (v := v ^ D.d i) (pow_ne_zero _ hv) 1 (negA D i j) (E R v i) (E R v j)
  rw [serreAux_one, ← one_sub_cartanMatrix_toNat hij, serre_E R v hij, one_mul, one_mul,
    eq_comm, sub_eq_zero] at h
  exact h

/-- `Fᵢ S = vᵢ^r S Fᵢ` for `S = serreAux vᵢ vᵢ⁻¹ r Fᵢ Fⱼ`, by the quantum Serre relation. -/
lemma F_mul_serreAux (hv : v ≠ 0) {i j : I} (hij : i ≠ j) :
    F R v i * serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (F R v i) (F R v j) =
      (v ^ D.d i) ^ negA D i j •
        (serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (F R v i) (F R v j) * F R v i) := by
  have h := serreAux_succ' (v := v ^ D.d i) (pow_ne_zero _ hv) 1 (negA D i j) (F R v i) (F R v j)
  rw [serreAux_one, ← one_sub_cartanMatrix_toNat hij, serre_F R v hij, one_mul, one_mul,
    eq_comm, sub_eq_zero] at h
  exact h

/-! ### The relations (b), (c) for `Tᵢ(Eⱼ)`, `Tᵢ(Fⱼ)` -/

lemma zpow_add_mul_zpow_neg (hv : v ≠ 0) (x y : ℤ) (r : ℕ) :
    v ^ (x + y * r) * (v ^ (-y)) ^ r = v ^ x := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hv]
  congr 1
  ring

/-- `Tᵢ(K_μ) Tᵢ(Eⱼ) = v^{⟨μ, j'⟩} Tᵢ(Eⱼ) Tᵢ(K_μ)`. -/
theorem braidK_mul_braidEj (hv : v ≠ 0) {i j : I} (hij : i ≠ j) (μ : Y) :
    braidK R v i (.ofAdd μ) * braidEj R v i j =
      v ^ R.root j μ • (braidEj R v i j * braidK R v i (.ofAdd μ)) := by
  rw [braidK_apply, braidEj, mul_smul_comm, mul_serreAux_of_mul_eq_smul (K_mul_E R v _ i)
    (K_mul_E R v _ j), root_reflY, root_reflY_self, cartanMatrix_eq_neg_negA hij,
    show R.root j μ - R.root i μ * -(negA D i j : ℤ) = R.root j μ + R.root i μ * negA D i j by
      ring, zpow_add_mul_zpow_neg hv, smul_comm, smul_mul_assoc]

/-- `Tᵢ(K_μ) Tᵢ(Fⱼ) = v^{-⟨μ, j'⟩} Tᵢ(Fⱼ) Tᵢ(K_μ)`. -/
theorem braidK_mul_braidFj (hv : v ≠ 0) {i j : I} (hij : i ≠ j) (μ : Y) :
    braidK R v i (.ofAdd μ) * braidFj R v i j =
      v ^ (-R.root j μ) • (braidFj R v i j * braidK R v i (.ofAdd μ)) := by
  have e : v ^ (-R.root j (reflY R i μ)) * (v ^ (-R.root i (reflY R i μ))) ^ negA D i j =
      v ^ (-R.root j μ) := by
    rw [root_reflY, root_reflY_self, cartanMatrix_eq_neg_negA hij, neg_neg, ← zpow_natCast,
      ← zpow_mul, ← zpow_add₀ hv]
    congr 1
    ring
  rw [braidK_apply, braidFj, mul_smul_comm, mul_serreAux_of_mul_eq_smul (K_mul_F R v _ i)
    (K_mul_F R v _ j), e, smul_comm, smul_mul_assoc]

/-! ### The relation (d) for the pairs `(i, j)` and `(j, i)` -/

/-- `[Tᵢ(Eᵢ), Tᵢ(Fⱼ)] = 0` for `j ≠ i`. -/
theorem braidEi_mul_braidFj_sub [NeZero v] {i j : I} (hij : i ≠ j) :
    braidEi R i * braidFj R v i j - braidFj R v i j * braidEi R i = 0 := by
  have hv := NeZero.ne v
  set S := serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (F R v i) (F R v j)
  have hK := mul_serreAux_of_mul_eq_smul (v := v ^ D.d i) (K_mul_F R v (ktilde R i) i)
    (K_mul_F R v (ktilde R i) j) (v ^ D.d i)⁻¹ (negA D i j)
  have hlam : v ^ (-R.root j (ktilde R i)) * (v ^ (-R.root i (ktilde R i))) ^ negA D i j *
      (v ^ D.d i) ^ negA D i j = 1 := by
    rw [root_ktilde, root_ktilde, D.cartanMatrix_self, cartanMatrix_eq_neg_negA hij,
      ← zpow_natCast (v ^ D.d i), ← zpow_natCast v, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_add₀ hv, ← zpow_add₀ hv]
    rw [show -((D.d i : ℤ) * -(negA D i j : ℤ)) + -((D.d i : ℤ) * 2) * (negA D i j : ℤ) +
      (D.d i : ℤ) * (negA D i j : ℤ) = 0 by ring, zpow_zero]
  have key : F R v i * Kt R v i * S = S * (F R v i * Kt R v i) := by
    rw [mul_assoc, hK, mul_smul_comm, ← mul_assoc, F_mul_serreAux hv hij, smul_mul_assoc,
      smul_smul, hlam, one_smul, mul_assoc]
  simp only [braidFj, braidEi, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
  rw [key, sub_neg_eq_add, smul_neg]
  exact neg_add_cancel _

/-- `[Tᵢ(Eⱼ), Tᵢ(Fᵢ)] = 0` for `j ≠ i`. -/
theorem braidEj_mul_braidFi_sub [NeZero v] {i j : I} (hij : i ≠ j) :
    braidEj R v i j * braidFi R i - braidFi R i * braidEj R v i j = 0 := by
  have hv := NeZero.ne v
  set S := serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i j) (E R v i) (E R v j)
  have hK := mul_serreAux_of_mul_eq_smul (v := v ^ D.d i) (K_mul_E R v (-ktilde R i) i)
    (K_mul_E R v (-ktilde R i) j) (v ^ D.d i)⁻¹ (negA D i j)
  have hlam : (v ^ D.d i) ^ negA D i j * (v ^ R.root j (-ktilde R i) *
      (v ^ R.root i (-ktilde R i)) ^ negA D i j) = 1 := by
    rw [map_neg, map_neg, root_ktilde, root_ktilde, D.cartanMatrix_self,
      cartanMatrix_eq_neg_negA hij, ← zpow_natCast (v ^ D.d i), ← zpow_natCast v, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hv, ← zpow_add₀ hv]
    rw [show (D.d i : ℤ) * (negA D i j : ℤ) + (-((D.d i : ℤ) * -(negA D i j : ℤ)) +
      -((D.d i : ℤ) * 2) * (negA D i j : ℤ)) = 0 by ring, zpow_zero]
  have key : K R v (-ktilde R i) * E R v i * S = S * (K R v (-ktilde R i) * E R v i) := by
    rw [mul_assoc, E_mul_serreAux hv hij, mul_smul_comm, ← mul_assoc, hK, smul_mul_assoc,
      smul_smul, hlam, one_smul, mul_assoc]
  simp only [braidEj, braidFi, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
  rw [← key, smul_neg, sub_neg_eq_add]
  exact neg_add_cancel _

end LieLean.QuantumGroup
