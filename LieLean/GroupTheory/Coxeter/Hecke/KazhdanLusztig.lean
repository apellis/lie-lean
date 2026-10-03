/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Triangular
import Mathlib.Algebra.Polynomial.Expand

/-!
# The Kazhdan–Lusztig basis and Kazhdan–Lusztig polynomials

Let `(W, S)` be a Coxeter system and `𝓗 = 𝓗_{v²}(W)` its generic Iwahori–Hecke algebra over
`ℤ[v, v⁻¹]` (`v = LaurentPolynomial.T 1`, `q = v² = LaurentPolynomial.T 2`), with standard basis
`T_w` and quadratic relation `(T_s - q)(T_s + 1) = 0`, and bar involution `h ↦ h̄`
(`IwahoriHeckeAlgebra.barL`: `v̄ = v⁻¹`, `T̄_w = T_{w⁻¹}⁻¹`).

**Normalization.** We use the normalization of Kazhdan and Lusztig [KL]: the Kazhdan–Lusztig
basis element `C'_w` is the unique element of `𝓗` with
```
  C̄'_w = C'_w,     C'_w = q^{-ℓ(w)/2} Σ_{y ≤ w} P_{y,w}(q) T_y,
```
where `P_{w,w} = 1` and, for `y < w`, `P_{y,w} ∈ ℤ[q]` has degree `≤ (ℓ(w) - ℓ(y) - 1)/2`
([KL] Thm. 1.1, (1.1.c)). Here `q^{-ℓ(w)/2} = v^{-ℓ(w)}`. In terms of `H_y = v^{-ℓ(y)} T_y` this
says `C'_w ∈ H_w + Σ_{y < w} v⁻¹ ℤ[v⁻¹] H_y`; up to the substitution `v ↦ v⁻¹` this is Soergel's
normalization `\underline{H}_w ∈ H_w + Σ_y v ℤ[v] H_y` [Soe] (`coeff_toFinsupp_klBasis_eq_zero`).

## Proof

Uniqueness is `IwahoriHeckeAlgebra.eq_zero_of_barL_eq_self` (a bar-invariant element of
`Σ_y v⁻¹ ℤ[v⁻¹] H_y` is zero). Existence is proved by induction on `ℓ(w)` as in [KL] §2: if
`w = s v > v`, then
```
  C'_w = C'_s C'_v - Σ_{z < v, sz < z} μ(z, v) C'_z,
```
where `C'_s = v⁻¹ (T_s + 1)` and `μ(z, v)` is the coefficient of `q^{(ℓ(v) - ℓ(z) - 1)/2}` in
`P_{z,v}`. The corresponding recursion for the polynomials is [KL] (2.2.c):
```
  P_{x,w} = q^{1-c} P_{sx,v} + q^c P_{x,v} - Σ_{z < v, sz < z} μ(z,v) q^{(ℓ(w)-ℓ(z))/2} P_{x,z},
```
with `c = 1` if `sx < x` and `c = 0` otherwise. The verification of the degree bound (the only
delicate point: the `μ`-terms exactly cancel the top coefficients) is written out in the proof of
`IwahoriHeckeAlgebra.isKLElement_klStep`; we reconstructed it from the outline in [KL] §2.

## Main definitions

* `IwahoriHeckeAlgebra.IsKLElement w C P`: `C` is bar invariant and has coefficients
  `v^{-ℓ(w)} P(y)(q)` with the Kazhdan–Lusztig normalization.
* `IwahoriHeckeAlgebra.klBasis w`: the Kazhdan–Lusztig basis element `C'_w`.
* `IwahoriHeckeAlgebra.klPoly y w`: the Kazhdan–Lusztig polynomial `P_{y,w} ∈ ℤ[q]`.
* `IwahoriHeckeAlgebra.klMu y w`: the coefficient `μ(y, w)`.
* `IwahoriHeckeAlgebra.klSimple i`: `C'_s = v⁻¹ (T_s + 1)`.

## Main results

* `IwahoriHeckeAlgebra.existsUnique_klBasis`: **existence and uniqueness of the Kazhdan–Lusztig
  basis** ([KL] Thm. 1.1).
* `IwahoriHeckeAlgebra.barL_klBasis`, `klBasis_eq_sum`, `toFinsupp_klBasis_apply`.
* `IwahoriHeckeAlgebra.klPoly_self`, `klPoly_eq_zero_of_not_bruhatLE`,
  `two_mul_natDegree_klPoly_add_length_lt`: `P_{w,w} = 1`, `P_{y,w} = 0` unless `y ≤ w`, and
  the degree bound.
* `IwahoriHeckeAlgebra.klSimple_mul_klBasis`: `C'_s C'_v = C'_{sv} + Σ_{z<v, sz<z} μ(z,v) C'_z`
  for `sv > v` ([KL] §2.2, (2.3.a); stated there for the basis `C_w`).
* `IwahoriHeckeAlgebra.klPoly_simple_mul`: the recursion [KL] (2.2.c).
* `IwahoriHeckeAlgebra.klBasis_one`, `klBasis_simple`: `C'_1 = 1`, `C'_s = v⁻¹ (T_s + 1)`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184, §1–2.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Ch. 5.
* [Soe] W. Soergel, *Kazhdan–Lusztig-Polynome und eine Kombinatorik für Kipp-Moduln*,
  Represent. Theory **1** (1997), 37–68, §2.
-/

open Finsupp

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

section leftOp

variable {R : Type*} [CommRing R] (q : R)

theorem toFinsupp_T_simple_mul (i : B) (h : IwahoriHeckeAlgebra cs q) :
    toFinsupp cs q (T cs q (s i) * h) = leftOp cs q i (toFinsupp cs q h) := by
  rw [toFinsupp_T_mul, lmul_single_simple]

/-- The coefficients of `T_s h` in terms of those of `h`. -/
theorem leftOp_apply (i : B) (x : W →₀ R) (y : W) :
    leftOp cs q i x y = if ℓ (s i * y) < ℓ y then x (s i * y) + (q - 1) * x y
      else q * x (s i * y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, Finsupp.add_apply, hx, hx']
    split_ifs <;> simp only [Finsupp.add_apply] <;> ring
  | single w a =>
    have hne : ℓ (s i * w) ≠ ℓ w := cs.length_simple_mul_ne w i
    rw [← smul_single_one, map_smul, leftOp_single]
    rcases eq_or_ne y w with rfl | hyw
    · have h1 : s i * y ≠ y := fun h ↦ hne (by rw [h])
      by_cases hy : ℓ y < ℓ (s i * y)
      · simp [hy, h1, not_lt.mpr hy.le]
      · simp [hy, h1, lt_of_le_of_ne (not_lt.mp hy) hne, mul_comm]
    rcases eq_or_ne y (s i * w) with rfl | hyws
    · have h2 : s i * (s i * w) = w := CoxeterSystem.simple_mul_simple_cancel_left cs i
      by_cases hw : ℓ w < ℓ (s i * w)
      · simp [hw, h2, hyw.symm]
      · simp [hw, h2, hyw, mul_comm]
    · have h3 : s i * y ≠ w := fun h ↦
        hyws (by rw [← h, CoxeterSystem.simple_mul_simple_cancel_left])
      split_ifs <;> simp [hyw.symm, hyws.symm, h3.symm]

end leftOp

section Laurent

local notation "𝓗" => IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ)

/-- Evaluation at `q = v²` is `toLaurent ∘ expand 2`. -/
theorem aeval_T_two_eq (P : Polynomial ℤ) :
    Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) P =
      Polynomial.toLaurent (Polynomial.expand ℤ 2 P) := by
  have : Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) =
      Polynomial.toLaurentAlg.comp (Polynomial.expand ℤ 2) := by
    ext
    simp [Polynomial.toLaurent_X_pow]
  rw [this]
  rfl

theorem aeval_T_two_injective :
    Function.Injective
      (Polynomial.aeval (R := ℤ) (LaurentPolynomial.T 2 : LaurentPolynomial ℤ)) := by
  intro P Q h
  rw [aeval_T_two_eq, aeval_T_two_eq] at h
  exact Polynomial.expand_injective two_pos (Polynomial.toLaurent_injective h)

/-- The coefficient of `v^n` in `v^a P(v²)` vanishes unless `n = a + 2k` with `P_k ≠ 0`. -/
theorem coeff_T_mul_aeval_T_two_eq_zero {a n : ℤ} {P : Polynomial ℤ}
    (h : ∀ k : ℕ, n = a + 2 * k → P.coeff k = 0) :
    ((LaurentPolynomial.T a : LaurentPolynomial ℤ) *
      Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) P).coeff n = 0 := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, aeval_T_two_eq,
    LaurentPolynomial.coeff_toLaurent]
  by_cases hm : ∃ j : ℕ, (j : ℤ) = -a + n
  · obtain ⟨j, hj⟩ := hm
    have e : -a + n = Nat.castEmbedding j := by simp [hj]
    rw [e, Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective]
    change (Polynomial.expand ℤ 2 P).coeff j = 0
    rw [Polynomial.coeff_expand two_pos]
    split_ifs with h2
    · obtain ⟨k, rfl⟩ := h2
      rw [Nat.mul_div_cancel_left _ two_pos]
      exact h k (by push_cast at hj; omega)
    · rfl
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨j, hj⟩
    exact hm ⟨j, by simpa using hj⟩

theorem T_mul_aeval_T_two_injective (a : ℤ) : Function.Injective fun P : Polynomial ℤ ↦
    (LaurentPolynomial.T a : LaurentPolynomial ℤ) *
      Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) P :=
  fun _ _ h ↦ aeval_T_two_injective ((LaurentPolynomial.isUnit_T a).mul_left_cancel h)

/-- `μ • v^{-b} P(q) = v^{-a} (μ q^m P)(q)` if `a = b + 2m` (or `μ = 0`). -/
theorem zsmul_T_mul_aeval {a b m : ℕ} {μ : ℤ} (h : μ ≠ 0 → a = b + 2 * m) (P : Polynomial ℤ) :
    μ • (LaurentPolynomial.T (-(b : ℤ)) *
        Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) P) =
      LaurentPolynomial.T (-(a : ℤ)) * Polynomial.aeval (LaurentPolynomial.T 2)
        (Polynomial.C μ * Polynomial.X ^ m * P) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have e : (LaurentPolynomial.T (-(a : ℤ)) : LaurentPolynomial ℤ) *
      LaurentPolynomial.T 2 ^ m = LaurentPolynomial.T (-(b : ℤ)) := by
    rw [LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add, h hμ]
    congr 1
    push_cast
    ring
  rw [map_mul, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ← e, zsmul_eq_mul,
    eq_intCast (algebraMap ℤ (LaurentPolynomial ℤ))]
  ring

/-- `C` is a Kazhdan–Lusztig element for `w` with polynomials `P` (`P y` playing the role of
`P_{y,w}`): `C` is bar invariant, `C = v^{-ℓ(w)} Σ_y P(y)(q) T_y`, `P(w) = 1`, `P(y) = 0` unless
`y ≤ w`, and for `y ≠ w` the coefficient of `q^k` in `P(y)` vanishes if `2k + ℓ(y) ≥ ℓ(w)`
(i.e. `deg P(y) ≤ (ℓ(w) - ℓ(y) - 1)/2`). -/
structure IsKLElement (w : W) (C : 𝓗) (P : W → Polynomial ℤ) : Prop where
  /-- `C` is bar invariant. -/
  barL_eq : barL cs C = C
  /-- The coefficient of `T_y` in `C` is `v^{-ℓ(w)} P(y)(q)`. -/
  toFinsupp_apply (y : W) : toFinsupp cs _ C y =
    LaurentPolynomial.T (-(ℓ w : ℤ)) * Polynomial.aeval (LaurentPolynomial.T 2) (P y)
  /-- `P(w) = 1`. -/
  self : P w = 1
  /-- `P(y) = 0` unless `y ≤ w`. -/
  bruhatLE {y : W} : P y ≠ 0 → cs.BruhatLE y w
  /-- The degree bound: for `y ≠ w`, the coefficient of `q^k` in `P(y)` vanishes if
  `2k + ℓ(y) ≥ ℓ(w)`. -/
  coeff_eq_zero {y : W} (hy : y ≠ w) {k : ℕ} : ℓ w ≤ 2 * k + ℓ y → (P y).coeff k = 0

variable {cs}

theorem IsKLElement.eq_zero_of_not_bruhatLE {w : W} {C : 𝓗} {P : W → Polynomial ℤ}
    (h : IsKLElement cs w C P) {y : W} (hy : ¬cs.BruhatLE y w) : P y = 0 :=
  not_not.mp fun h' ↦ hy (h.bruhatLE h')

theorem IsKLElement.eq_zero_of_length_lt {w : W} {C : 𝓗} {P : W → Polynomial ℤ}
    (h : IsKLElement cs w C P) {y : W} (hy : ℓ w < ℓ y) : P y = 0 :=
  h.eq_zero_of_not_bruhatLE fun h' ↦ by have := h'.length_le; omega

/-- **Uniqueness of Kazhdan–Lusztig elements** ([KL] proof of Thm. 1.1). -/
theorem IsKLElement.unique {w : W} {C C' : 𝓗} {P P' : W → Polynomial ℤ}
    (h : IsKLElement cs w C P) (h' : IsKLElement cs w C' P') : C = C' ∧ P = P' := by
  have hC : C = C' := by
    rw [← sub_eq_zero]
    apply eq_zero_of_barL_eq_self cs (by rw [map_sub, h.barL_eq, h'.barL_eq])
    intro y n hn
    rw [map_sub, Finsupp.sub_apply, h.toFinsupp_apply, h'.toFinsupp_apply, ← mul_sub, ← map_sub]
    apply coeff_T_mul_aeval_T_two_eq_zero
    intro k hk
    rw [Polynomial.coeff_sub]
    rcases eq_or_ne y w with rfl | hyw
    · rw [h.self, h'.self, sub_self]
    · rw [h.coeff_eq_zero hyw (by omega), h'.coeff_eq_zero hyw (by omega), sub_self]
  refine ⟨hC, funext fun y ↦ ?_⟩
  have := h.toFinsupp_apply y
  rw [hC, h'.toFinsupp_apply] at this
  exact (T_mul_aeval_T_two_injective _ this).symm

variable (cs)

theorem isKLElement_one [DecidableEq W] :
    IsKLElement cs 1 (1 : 𝓗) fun y ↦ if y = 1 then 1 else 0 where
  barL_eq := map_one _
  toFinsupp_apply y := by
    rw [toFinsupp_one, cs.length_one]
    rcases eq_or_ne y 1 with rfl | hy
    · simp
    · simp [hy]
  self := by simp
  bruhatLE {y} hy := by
    rcases eq_or_ne y 1 with rfl | h
    · exact cs.bruhatLE_refl 1
    · simp [h] at hy
  coeff_eq_zero {y} hy _ _ := by simp [hy]

/-! ### The inductive step -/

/-- The element `C'_s = v⁻¹ (T_s + 1) = q^{-1/2} (T_s + 1)` ([KL] §1). -/
noncomputable def klSimple (i : B) : 𝓗 :=
  (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) • (T cs _ (s i) + 1)

theorem barL_klSimple (i : B) : barL cs (klSimple cs i) = klSimple cs i :=
  barL_C'_simple cs i

theorem toFinsupp_klSimple_mul_apply (i : B) (h : 𝓗) (y : W) :
    toFinsupp cs _ (klSimple cs i * h) y = LaurentPolynomial.T (-1) *
      ((if ℓ (s i * y) < ℓ y then
          toFinsupp cs _ h (s i * y) + (LaurentPolynomial.T 2 - 1) * toFinsupp cs _ h y
        else LaurentPolynomial.T 2 * toFinsupp cs _ h (s i * y)) + toFinsupp cs _ h y) := by
  rw [klSimple, smul_mul_assoc, add_mul, one_mul, map_smul, map_add, toFinsupp_T_simple_mul,
    Finsupp.smul_apply, Finsupp.add_apply, leftOp_apply, smul_eq_mul]

/-- `μ`-coefficients: for `d` odd, the coefficient of `q^{(d-1)/2}` in `P`; `0` for `d` even.
Applied to `P = P_{z,v}` and `d = ℓ(v) - ℓ(z)` this is `μ(z, v)`. -/
noncomputable def muCoeff (P : Polynomial ℤ) (d : ℕ) : ℤ := if Odd d then P.coeff (d / 2) else 0

theorem muCoeff_ne_zero {P : Polynomial ℤ} {d : ℕ} (h : muCoeff P d ≠ 0) : d % 2 = 1 := by
  rw [muCoeff] at h
  split_ifs at h with hd
  · exact Nat.odd_iff.mp hd
  · exact absurd rfl h

/-- The finite set `{z ≤ v | sᵢ z < z}`. -/
noncomputable def descentsBelow (i : B) (v : W) : Finset W := by
  classical exact (cs.finite_setOf_bruhatLE v).toFinset.filter fun z ↦ ℓ (s i * z) < ℓ z

variable {cs} in
theorem mem_descentsBelow {i : B} {v z : W} :
    z ∈ descentsBelow cs i v ↔ cs.BruhatLE z v ∧ ℓ (s i * z) < ℓ z := by
  simp [descentsBelow]

/-- The candidate `C'_s C'_v - Σ_{z ≤ v, sz < z} μ(z, v) C'_z` for `C'_{sv}`, built from given
elements `Cz z` (playing the role of `C'_z`) and polynomials `P z` (playing the role of
`P_{z,v}`). -/
noncomputable def klStep (Cz : W → 𝓗) (P : W → Polynomial ℤ) (i : B) (v : W) : 𝓗 :=
  klSimple cs i * Cz v - ∑ z ∈ descentsBelow cs i v, muCoeff (P z) (ℓ v - ℓ z) • Cz z

/-- The polynomials of `klStep`, following [KL] (2.2.c): with `Pz z y` playing the role of
`P_{y,z}`, the value at `y` is
`q^{1-c} P_{sy,v} + q^c P_{y,v} - Σ_{z ≤ v, sz < z} μ(z,v) q^{(ℓ(sv)-ℓ(z))/2} P_{y,z}`. -/
noncomputable def klStepPoly (Pz : W → W → Polynomial ℤ) (i : B) (v y : W) : Polynomial ℤ :=
  (if ℓ (s i * y) < ℓ y then Pz v (s i * y) + Polynomial.X * Pz v y
    else Polynomial.X * Pz v (s i * y) + Pz v y) -
  ∑ z ∈ descentsBelow cs i v, Polynomial.C (muCoeff (Pz v z) (ℓ v - ℓ z)) *
    Polynomial.X ^ ((ℓ (s i * v) - ℓ z) / 2) * Pz z y

variable {cs}

/-- **The inductive step in the construction of the Kazhdan–Lusztig basis** ([KL] §2.2;
the verification is reconstructed): if `sv > v` and `Cz z`, `Pz z` are Kazhdan–Lusztig elements
for all `z ≤ v`, then `C'_s C'_v - Σ_{z ≤ v, sz < z} μ(z, v) C'_z` is a Kazhdan–Lusztig element
for `sv`, with the polynomials given by [KL] (2.2.c).

For the degree bound at `y ≠ sv`, `2k + ℓ(y) ≥ ℓ(sv)`: the terms `P_{sy,v}` (`sy < y`),
`q P_{sy,v}` and `P_{y,v}` (`sy > y`) have vanishing `q^k`-coefficient by the bounds for `v`, and
so do the terms `q^{(ℓ(sv)-ℓ(z))/2} P_{y,z}` with `z ≠ y` by the bounds for `z`. What remains, for
`sy < y` and `2k + ℓ(y) = ℓ(sv)`, is the coefficient `μ(y,v)` of `q^{k-1}` in `P_{y,v}`, which is
cancelled by the term `z = y`. -/
theorem isKLElement_klStep {i : B} {v : W} (hv : ℓ v < ℓ (s i * v)) {Cz : W → 𝓗}
    {Pz : W → W → Polynomial ℤ} (hz : ∀ z, cs.BruhatLE z v → IsKLElement cs z (Cz z) (Pz z)) :
    IsKLElement cs (s i * v) (klStep cs Cz (Pz v) i v) (klStepPoly cs Pz i v) := by
  have hvl : ℓ (s i * v) = ℓ v + 1 := by
    rcases cs.length_simple_mul v i with h | h <;> omega
  have hV := hz v (cs.bruhatLE_refl v)
  have hvw : cs.BruhatLE v (s i * v) := cs.bruhatLE_simple_mul (by
    rw [CoxeterSystem.not_isLeftDescent_iff]; omega)
  have hS : ∀ z ∈ descentsBelow cs i v, cs.BruhatLE z v ∧ ℓ (s i * z) < ℓ z := fun z hz' ↦
    mem_descentsBelow.mp hz'
  -- `μ(z, v) ≠ 0` forces `ℓ(z) < ℓ(v)` with odd difference.
  have hμ : ∀ z, muCoeff (Pz v z) (ℓ v - ℓ z) ≠ 0 →
      ℓ (s i * v) = ℓ z + 2 * ((ℓ (s i * v) - ℓ z) / 2) ∧ ℓ z < ℓ v := by
    intro z hz'
    have := muCoeff_ne_zero hz'
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- bar invariance
    rw [klStep, map_sub, map_mul, map_sum, barL_klSimple, hV.barL_eq]
    congr 1
    refine Finset.sum_congr rfl fun z hz' ↦ ?_
    rw [map_zsmul, (hz z (hS z hz').1).barL_eq]
  · -- the coefficients
    intro y
    rw [klStep, map_sub, Finsupp.sub_apply, map_sum, Finsupp.finsetSum_apply,
      toFinsupp_klSimple_mul_apply, klStepPoly, map_sub, map_sum, mul_sub, Finset.mul_sum]
    congr 1
    · rw [hV.toFinsupp_apply, hV.toFinsupp_apply]
      have e : (LaurentPolynomial.T (-(ℓ (s i * v) : ℤ)) : LaurentPolynomial ℤ) =
          LaurentPolynomial.T (-1) * LaurentPolynomial.T (-(ℓ v : ℤ)) := by
        rw [← LaurentPolynomial.T_add, hvl]
        congr 1
        push_cast
        ring
      split_ifs <;> simp only [map_add, map_mul, Polynomial.aeval_X] <;> rw [e] <;> ring
    · refine Finset.sum_congr rfl fun z hz' ↦ ?_
      rw [map_zsmul, Finsupp.smul_apply, (hz z (hS z hz').1).toFinsupp_apply]
      exact zsmul_T_mul_aeval (fun h ↦ (hμ z h).1) _
  · -- `P_{sv, sv} = 1`
    rw [klStepPoly, CoxeterSystem.simple_mul_simple_cancel_left, ite_eq_left (by omega), hV.self,
      hV.eq_zero_of_length_lt (by omega), mul_zero, add_zero]
    rw [Finset.sum_eq_zero, sub_zero]
    intro z hz'
    rw [(hz z (hS z hz').1).eq_zero_of_length_lt (by have := (hS z hz').1.length_le; omega),
      mul_zero]
  · -- support in the Bruhat interval
    intro y hy
    by_contra hyw
    apply hy
    have h1 : ∀ z, cs.BruhatLE z v → Pz z y = 0 := fun z hz' ↦
      (hz z hz').eq_zero_of_not_bruhatLE fun h ↦ hyw ((h.trans hz').trans hvw)
    have h2 : Pz v (s i * y) = 0 := hV.eq_zero_of_not_bruhatLE fun h ↦ by
      rcases h.simple_mul_or i with h' | h' <;>
        rw [CoxeterSystem.simple_mul_simple_cancel_left] at h'
      · exact hyw (h'.trans hvw)
      · exact hyw h'
    rw [klStepPoly, h1 v (cs.bruhatLE_refl v), h2, Finset.sum_eq_zero]
    · simp
    · intro z hz'
      rw [h1 z (hS z hz').1, mul_zero]
  · -- the degree bound
    intro y hy k hk
    -- the coefficient of the `z`-th summand
    have hterm : ∀ z ∈ descentsBelow cs i v, z ≠ y →
        (Polynomial.C (muCoeff (Pz v z) (ℓ v - ℓ z)) *
          Polynomial.X ^ ((ℓ (s i * v) - ℓ z) / 2) * Pz z y).coeff k = 0 := by
      intro z hz' hzy
      rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
      by_cases hμz : muCoeff (Pz v z) (ℓ v - ℓ z) = 0
      · rw [hμz, zero_mul]
      obtain ⟨h1, h2⟩ := hμ z hμz
      split_ifs with hm
      · rw [(hz z (hS z hz').1).coeff_eq_zero (Ne.symm hzy) (by omega), mul_zero]
      · rw [mul_zero]
    rw [klStepPoly, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
    split_ifs with hy'
    · -- `sy < y`
      have hyv : y ≠ v := by rintro rfl; omega
      have hsyv : s i * y ≠ v := by
        rintro rfl
        exact hy (by rw [CoxeterSystem.simple_mul_simple_cancel_left])
      have hsyl : ℓ (s i * y) + 1 = ℓ y := by
        rcases cs.length_simple_mul y i with h | h <;> omega
      rw [Polynomial.coeff_add, hV.coeff_eq_zero hsyv (by omega), zero_add]
      by_cases hyS : y ∈ descentsBelow cs i v
      · rw [Finset.sum_eq_single_of_mem y hyS fun z hz' hzy ↦ hterm z hz' hzy,
          (hz y (hS y hyS).1).self, mul_one, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have hyl := (hS y hyS).1.length_le
        obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Polynomial.coeff_X_mul]
        by_cases hk' : ℓ v ≤ 2 * k + ℓ y
        · rw [hV.coeff_eq_zero hyv hk']
          split_ifs with he
          · by_cases hμy : muCoeff (Pz v y) (ℓ v - ℓ y) = 0
            · rw [hμy, mul_one, sub_zero]
            · have := hμ y hμy
              omega
          · rw [mul_zero, sub_zero]
        · have hodd : Odd (ℓ v - ℓ y) := Nat.odd_iff.mpr (by omega)
          rw [ite_eq_left (by omega), mul_one, muCoeff, ite_eq_left hodd,
            show (ℓ v - ℓ y) / 2 = k by omega, sub_self]
      · rw [Finset.sum_eq_zero fun z hz' ↦ hterm z hz' fun h ↦ hyS (h ▸ hz'), sub_zero]
        have hyv' : ¬cs.BruhatLE y v := fun h ↦ hyS (mem_descentsBelow.mpr ⟨h, hy'⟩)
        rw [hV.eq_zero_of_not_bruhatLE hyv', mul_zero, Polynomial.coeff_zero]
    · -- `sy > y`
      have hyS : y ∉ descentsBelow cs i v := fun h ↦ hy' (hS y h).2
      rw [Finset.sum_eq_zero fun z hz' ↦ hterm z hz' fun h ↦ hyS (h ▸ hz'), sub_zero,
        Polynomial.coeff_add]
      have hsyv : s i * y ≠ v := by
        rintro rfl
        exact hy (by rw [CoxeterSystem.simple_mul_simple_cancel_left])
      have hsyl : ℓ (s i * y) = ℓ y + 1 := by
        rcases cs.length_simple_mul y i with h | h <;> omega
      have e1 : (Pz v y).coeff k = 0 := by
        rcases eq_or_ne y v with rfl | hyv
        · rw [hV.self, Polynomial.coeff_one, ite_eq_right (by omega)]
        · exact hV.coeff_eq_zero hyv (by omega)
      rw [e1, add_zero]
      rcases k with _ | k
      · exact Polynomial.coeff_X_mul_zero _
      · rw [Polynomial.coeff_X_mul, hV.coeff_eq_zero hsyv (by omega)]

variable (cs)

/-- **Existence of Kazhdan–Lusztig elements** ([KL] Thm. 1.1), by induction on `ℓ(w)`
using `isKLElement_klStep`. -/
theorem exists_isKLElement (w : W) : ∃ C P, IsKLElement cs w C P := by
  classical
  induction hn : ℓ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  subst hn
  rcases eq_or_ne w 1 with rfl | hw
  · exact ⟨1, _, isKLElement_one cs⟩
  obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hw
  rw [CoxeterSystem.isLeftDescent_iff] at hi
  have hv : ℓ (s i * w) < ℓ (s i * (s i * w)) := by
    rw [CoxeterSystem.simple_mul_simple_cancel_left]; omega
  have key : ∀ z, ∃ (C : 𝓗) (P : W → Polynomial ℤ),
      cs.BruhatLE z (s i * w) → IsKLElement cs z C P := by
    intro z
    by_cases h : cs.BruhatLE z (s i * w)
    · obtain ⟨C, P, hCP⟩ := ih (ℓ z) (by have := h.length_le; omega) z rfl
      exact ⟨C, P, fun _ ↦ hCP⟩
    · exact ⟨0, 0, fun h' ↦ absurd h' h⟩
  choose Cz Pz hz using key
  have := isKLElement_klStep hv hz
  rw [CoxeterSystem.simple_mul_simple_cancel_left] at this
  exact ⟨_, _, this⟩

/-! ### The Kazhdan–Lusztig basis and polynomials -/

/-- The **Kazhdan–Lusztig basis** element `C'_w` ([KL] Thm. 1.1): the unique bar-invariant element
with `C'_w = q^{-ℓ(w)/2} Σ_{y ≤ w} P_{y,w}(q) T_y`, `P_{w,w} = 1` and
`deg P_{y,w} ≤ (ℓ(w) - ℓ(y) - 1)/2` for `y < w`. -/
noncomputable def klBasis (w : W) : 𝓗 := (exists_isKLElement cs w).choose

/-- The **Kazhdan–Lusztig polynomial** `P_{y,w} ∈ ℤ[q]` ([KL] Thm. 1.1). -/
noncomputable def klPoly (y w : W) : Polynomial ℤ :=
  (exists_isKLElement cs w).choose_spec.choose y

theorem isKLElement_klBasis (w : W) : IsKLElement cs w (klBasis cs w) (klPoly cs · w) :=
  (exists_isKLElement cs w).choose_spec.choose_spec

variable {cs} in
/-- A Kazhdan–Lusztig element is the Kazhdan–Lusztig basis element. -/
theorem IsKLElement.eq_klBasis {w : W} {C : 𝓗} {P : W → Polynomial ℤ}
    (h : IsKLElement cs w C P) : C = klBasis cs w ∧ P = (klPoly cs · w) :=
  h.unique (isKLElement_klBasis cs w)

/-- The Kazhdan–Lusztig basis element `C'_w` is bar invariant ([KL] Thm. 1.1). -/
theorem barL_klBasis (w : W) : barL cs (klBasis cs w) = klBasis cs w :=
  (isKLElement_klBasis cs w).barL_eq

/-- The coefficient of `T_y` in `C'_w` is `v^{-ℓ(w)} P_{y,w}(q)`. -/
theorem toFinsupp_klBasis_apply (y w : W) :
    toFinsupp cs _ (klBasis cs w) y = LaurentPolynomial.T (-(ℓ w : ℤ)) *
      Polynomial.aeval (LaurentPolynomial.T 2) (klPoly cs y w) :=
  (isKLElement_klBasis cs w).toFinsupp_apply y

/-- `P_{w,w} = 1` ([KL] Thm. 1.1). -/
@[simp]
theorem klPoly_self (w : W) : klPoly cs w w = 1 :=
  (isKLElement_klBasis cs w).self

/-- `P_{y,w} = 0` unless `y ≤ w` in the Bruhat order ([KL] Thm. 1.1). -/
theorem klPoly_eq_zero_of_not_bruhatLE {y w : W} (h : ¬cs.BruhatLE y w) : klPoly cs y w = 0 :=
  (isKLElement_klBasis cs w).eq_zero_of_not_bruhatLE h

theorem bruhatLE_of_klPoly_ne_zero {y w : W} (h : klPoly cs y w ≠ 0) : cs.BruhatLE y w :=
  (isKLElement_klBasis cs w).bruhatLE h

/-- For `y ≠ w`, the coefficient of `q^k` in `P_{y,w}` vanishes if `2k + ℓ(y) ≥ ℓ(w)`. -/
theorem coeff_klPoly_eq_zero {y w : W} (h : y ≠ w) {k : ℕ} (hk : ℓ w ≤ 2 * k + ℓ y) :
    (klPoly cs y w).coeff k = 0 :=
  (isKLElement_klBasis cs w).coeff_eq_zero h hk

/-- **The degree bound** ([KL] Thm. 1.1): for `y < w`,
`deg P_{y,w} ≤ (ℓ(w) - ℓ(y) - 1)/2`, i.e. `2 deg P_{y,w} + ℓ(y) < ℓ(w)`. -/
theorem two_mul_natDegree_klPoly_add_length_lt {y w : W} (hyw : cs.BruhatLE y w) (h : y ≠ w) :
    2 * (klPoly cs y w).natDegree + ℓ y < ℓ w := by
  have hl := hyw.eq_or_length_lt.resolve_left h
  have : (klPoly cs y w).natDegree ≤ (ℓ w - ℓ y - 1) / 2 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦
      coeff_klPoly_eq_zero cs h (by omega)
  omega

/-- The coefficient of `H_y = v^{-ℓ(y)} T_y` in `C'_w` lies in `v⁻¹ ℤ[v⁻¹]` for `y ≠ w`: the
coefficient of `v^n` in `[T_y] C'_w` vanishes if `n + ℓ(y) ≥ 0` (Soergel's normalization [Soe]
Thm. 2.1, up to `v ↦ v⁻¹`). -/
theorem coeff_toFinsupp_klBasis_eq_zero {y w : W} (h : y ≠ w) {n : ℤ} (hn : 0 ≤ n + ℓ y) :
    (toFinsupp cs _ (klBasis cs w) y).coeff n = 0 := by
  rw [toFinsupp_klBasis_apply]
  exact coeff_T_mul_aeval_T_two_eq_zero fun k hk ↦ coeff_klPoly_eq_zero cs h (by omega)

/-- The expansion `C'_w = q^{-ℓ(w)/2} Σ_{y ≤ w} P_{y,w}(q) T_y` ([KL] (1.1.c)). -/
theorem klBasis_eq_sum (w : W) :
    klBasis cs w = (LaurentPolynomial.T (-(ℓ w : ℤ)) : LaurentPolynomial ℤ) •
      ∑ y ∈ (cs.finite_setOf_bruhatLE w).toFinset,
        Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) (klPoly cs y w) •
          T cs _ y := by
  classical
  apply (toFinsupp cs _).injective
  ext x
  rw [toFinsupp_klBasis_apply, map_smul, map_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, smul_eq_mul]
  congr 1
  simp_rw [map_smul, toFinsupp_T, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  split_ifs with hx
  · rfl
  · rw [klPoly_eq_zero_of_not_bruhatLE cs hx, map_zero]

/-- **Existence and uniqueness of the Kazhdan–Lusztig basis** ([KL] Thm. 1.1): for every
`w ∈ W` there is a unique `C ∈ 𝓗` with `C̄ = C` and
`C = q^{-ℓ(w)/2} Σ_{y ≤ w} P_y(q) T_y` for polynomials `P_y ∈ ℤ[q]` with `P_w = 1` and
`deg P_y ≤ (ℓ(w) - ℓ(y) - 1)/2` (i.e. `2 deg P_y + ℓ(y) < ℓ(w)`) for `y < w`. It is `C'_w`. -/
theorem existsUnique_klBasis (w : W) : ∃! C : 𝓗, barL cs C = C ∧
    ∃ P : W → Polynomial ℤ,
      C = (LaurentPolynomial.T (-(ℓ w : ℤ)) : LaurentPolynomial ℤ) •
        ∑ y ∈ (cs.finite_setOf_bruhatLE w).toFinset,
          Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) (P y) • T cs _ y ∧
      P w = 1 ∧ ∀ y, cs.BruhatLE y w → y ≠ w → 2 * (P y).natDegree + ℓ y < ℓ w := by
  classical
  refine ⟨klBasis cs w, ⟨barL_klBasis cs w, _, klBasis_eq_sum cs w, klPoly_self cs w,
    fun y hyw h ↦ two_mul_natDegree_klPoly_add_length_lt cs hyw h⟩, ?_⟩
  rintro C ⟨hbar, P, hC, hPw, hdeg⟩
  refine (IsKLElement.eq_klBasis (P := fun y ↦ if cs.BruhatLE y w then P y else 0) ?_).1
  refine ⟨hbar, fun x ↦ ?_, by simp [hPw, cs.bruhatLE_refl w], fun {y} hy ↦ ?_,
    fun {y} hy k hk ↦ ?_⟩
  · rw [hC, map_smul, map_sum, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul]
    congr 1
    simp_rw [map_smul, toFinsupp_T, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    split_ifs <;> simp
  · by_contra h
    simp [h] at hy
  · split_ifs with hyw
    · have := hdeg y hyw hy
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · simp

/-! ### The recursion formulas -/

/-- The coefficient `μ(y, w)` of `q^{(ℓ(w) - ℓ(y) - 1)/2}` in `P_{y,w}` (`0` if `ℓ(w) - ℓ(y)` is
even or `ℓ(y) ≥ ℓ(w)`) ([KL] Def. 1.2, which moreover sets `μ(w, y) = μ(y, w)`; `klMu` is not
symmetrized). -/
noncomputable def klMu (y w : W) : ℤ := muCoeff (klPoly cs y w) (ℓ w - ℓ y)

/-- `C'_1 = 1`. -/
@[simp]
theorem klBasis_one : klBasis cs 1 = 1 := by
  classical
  exact ((isKLElement_one cs).eq_klBasis).1.symm

theorem klPoly_one_right [DecidableEq W] (y : W) :
    klPoly cs y 1 = if y = 1 then 1 else 0 := by
  exact (congrFun ((isKLElement_one cs).eq_klBasis).2 y).symm

/-- **The multiplication formula** ([KL] §2.2, (2.3.a), for `C_w`): if `sv > v`, then
`C'_s C'_v = C'_{sv} + Σ_{z ≤ v, sz < z} μ(z, v) C'_z`. -/
theorem klSimple_mul_klBasis {i : B} {v : W} (hv : ℓ v < ℓ (s i * v)) :
    klSimple cs i * klBasis cs v = klBasis cs (s i * v) +
      ∑ z ∈ descentsBelow cs i v, klMu cs z v • klBasis cs z := by
  have := (isKLElement_klStep hv (Cz := klBasis cs) (Pz := fun z y ↦ klPoly cs y z)
    fun z _ ↦ isKLElement_klBasis cs z).eq_klBasis.1
  rw [← this, klStep]
  simp only [klMu]
  exact (sub_add_cancel _ _).symm

/-- **The recursion for Kazhdan–Lusztig polynomials** ([KL] (2.2.c)): if `w = sv > v`,
then with `c = 1` if `sx < x` and `c = 0` otherwise,
`P_{x,w} = q^{1-c} P_{sx,v} + q^c P_{x,v} - Σ_{z ≤ v, sz < z} μ(z,v) q^{(ℓ(w)-ℓ(z))/2} P_{x,z}`.
-/
theorem klPoly_simple_mul {i : B} {v : W} (hv : ℓ v < ℓ (s i * v)) (x : W) :
    klPoly cs x (s i * v) =
      (if ℓ (s i * x) < ℓ x then klPoly cs (s i * x) v + Polynomial.X * klPoly cs x v
        else Polynomial.X * klPoly cs (s i * x) v + klPoly cs x v) -
      ∑ z ∈ descentsBelow cs i v, Polynomial.C (klMu cs z v) *
        Polynomial.X ^ ((ℓ (s i * v) - ℓ z) / 2) * klPoly cs x z := by
  have := (isKLElement_klStep hv (Cz := klBasis cs) (Pz := fun z y ↦ klPoly cs y z)
    fun z _ ↦ isKLElement_klBasis cs z).eq_klBasis.2
  exact (congrFun this x).symm

/-- `C'_s = v⁻¹ (T_s + 1) = q^{-1/2} (T_s + 1)` ([KL] §1). -/
theorem klBasis_simple (i : B) : klBasis cs (s i) = klSimple cs i := by
  have h := klSimple_mul_klBasis cs (i := i) (v := 1) (by simp)
  rw [klBasis_one, mul_one, mul_one] at h
  rw [h, left_eq_add]
  refine Finset.sum_eq_zero fun z hz ↦ ?_
  have ⟨h1, h2⟩ := mem_descentsBelow.mp hz
  have := h1.length_le
  simp only [cs.length_one, nonpos_iff_eq_zero, cs.length_eq_zero_iff] at this
  subst this
  simp at h2

end Laurent

end IwahoriHeckeAlgebra
