/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.BraidRelationsGeneral

/-!
# Length three at a simple edge with a triangle

Let `i, j` be a mutual simple edge (`aᵢⱼ = aⱼᵢ = -1`) of an arbitrary Cartan datum and `l` a
third node meeting both ends with `aᵢₗ = aⱼₗ = -1` (the entries `aₗᵢ`, `aₗⱼ` are arbitrary), as in
affine type `Ã₂`. We prove `Tᵢ Tⱼ Tᵢ (Eₗ) = Tⱼ Tᵢ Tⱼ (Eₗ)` and its `F` analogue for any algebra
endomorphisms with Lusztig's generator formulas, and hence the length-three relation at a simple
edge whose third nodes meet at most one end or form such triangles.

## Main results

* `QuantumGroup.triangle_core_E`, `QuantumGroup.triangle_core_F`: the rank-three identities.
  With `a = Eᵢ`, `b = Eⱼ`, `z = Eₗ`, both sides of the relation on `Eₗ` are iterated twisted
  commutators of degree `(2, 2, 1)` in `(a, b, z)`, and their difference is an explicit
  combination of `u S₂(a, b) w`, `u S₂(a, z) w`, `u S₂(b, z) w` (ten terms, coefficients in
  `ℤ[q^{±1}, (q + q⁻¹)⁻¹]`); `vᵢ + vᵢ⁻¹ ≠ 0` is assumed.
* `QuantumGroup.HasBraidGeneratorImages.three_E_triangle`, `..._three_F_triangle`.
* `QuantumGroup.HasBraidGeneratorImages.three_braid_triangle`,
  `QuantumGroup.braidEquiv_braid_three_triangle`: the length-three relation when every third node
  `l` has `aᵢₗ = 0`, `aⱼₗ = 0`, or `aᵢₗ = aⱼₗ = -1`.

## Remaining

Triangles in which a third node meets an end of the simple edge with an entry `≤ -2` in the row
of that end (e.g. `aᵢₗ = -2`) are not treated.

## References

Reconstructed: the certificate was found by solving the linear system for the coefficients and
is checked here by normal ordering. G. Lusztig, *Introduction to quantum groups*, 39.4.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

section Core

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B] {q : k}

/-- The quadratic quantum Serre element, expanded. -/
lemma qSerre_two_eq (a b : B) :
    qSerre q 2 a b = a * a * b - (q + q⁻¹) • (a * b * a) + b * a * a := by
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial_one_right,
    qBinomial_self, qBinomial_zero_right]
  simp [qInt, Finset.sum_range_succ, pow_succ, mul_assoc]
  module

/-- **The triangle identity, positive part.** If `a, b, z` satisfy the quadratic Serre relations
`S₂(a, b) = S₂(a, z) = S₂(b, z) = 0` and `q + q⁻¹ ≠ 0`, then with
`c = a b - q⁻¹ b a`, `c' = b a - q⁻¹ a b`, `w = a z - q⁻¹ z a`, `w' = b z - q⁻¹ z b`:
`[b, [c, w]] = [a, [c', w']]` (all brackets twisted by `q⁻¹`). -/
theorem triangle_core_E (hq : q ≠ 0) (hs : q + q⁻¹ ≠ 0) {a b z c c' w w' : B}
    (hab : a * a * b - (q + q⁻¹) • (a * b * a) + b * a * a = 0)
    (haz : a * a * z - (q + q⁻¹) • (a * z * a) + z * a * a = 0)
    (hbz : b * b * z - (q + q⁻¹) • (b * z * b) + z * b * b = 0)
    (hc : c = a * b - q⁻¹ • (b * a)) (hc' : c' = b * a - q⁻¹ • (a * b))
    (hw : w = a * z - q⁻¹ • (z * a)) (hw' : w' = b * z - q⁻¹ • (z * b)) :
    b * (c * w - q⁻¹ • (w * c)) - q⁻¹ • ((c * w - q⁻¹ • (w * c)) * b) =
      a * (c' * w' - q⁻¹ • (w' * c')) - q⁻¹ • ((c' * w' - q⁻¹ • (w' * c')) * a) := by
  subst hc hc' hw hw'
  set Rab := a * a * b - (q + q⁻¹) • (a * b * a) + b * a * a
  set Raz := a * a * z - (q + q⁻¹) • (a * z * a) + z * a * a
  set Rbz := b * b * z - (q + q⁻¹) • (b * z * b) + z * b * b
  have e1 : z * Rab * b = 0 := by rw [hab]; simp
  have e2 : z * b * Rab = 0 := by rw [hab]; simp
  have e3 : Rab * (b * z) = 0 := by rw [hab]; simp
  have e4 : b * Rab * z = 0 := by rw [hab]; simp
  have e5 : Raz * (b * b) = 0 := by rw [haz]; simp
  have e6 : b * Raz * b = 0 := by rw [haz]; simp
  have e7 : b * b * Raz = 0 := by rw [haz]; simp
  have e8 : Rbz * (a * a) = 0 := by rw [hbz]; simp
  have e9 : a * Rbz * a = 0 := by rw [hbz]; simp
  have e10 : a * a * Rbz = 0 := by rw [hbz]; simp
  linear_combination (norm := skip) (-(q⁻¹ ^ 4 * (q + q⁻¹)⁻¹)) • e1 +
    (q⁻¹ ^ 4 * (q + q⁻¹)⁻¹) • e2 + (q + q⁻¹)⁻¹ • e3 + (-(q + q⁻¹)⁻¹) • e4 +
    (-(q⁻¹ ^ 2 * (q + q⁻¹)⁻¹)) • e5 + (q⁻¹ ^ 2) • e6 + (-(q⁻¹ ^ 2 * (q + q⁻¹)⁻¹)) • e7 +
    (q⁻¹ ^ 2 * (q + q⁻¹)⁻¹) • e8 + (-(q⁻¹ ^ 2)) • e9 + (q⁻¹ ^ 2 * (q + q⁻¹)⁻¹) • e10
  simp only [Rab, Raz, Rbz, mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, smul_zero,
    mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
  have h2 : q ^ 2 + 1 ≠ 0 := by
    intro h; apply hs; field_simp; linear_combination h
  match_scalars <;> field_simp <;> ring

/-- **The triangle identity, negative part**: with `c = b a - q a b`, `c' = a b - q b a`,
`w = z a - q a z`, `w' = z b - q b z`, `[[w, c], b] = [[w', c'], a]` (brackets twisted by
`q`). -/
theorem triangle_core_F (hq : q ≠ 0) (hs : q + q⁻¹ ≠ 0) {a b z c c' w w' : B}
    (hab : a * a * b - (q + q⁻¹) • (a * b * a) + b * a * a = 0)
    (haz : a * a * z - (q + q⁻¹) • (a * z * a) + z * a * a = 0)
    (hbz : b * b * z - (q + q⁻¹) • (b * z * b) + z * b * b = 0)
    (hc : c = b * a - q • (a * b)) (hc' : c' = a * b - q • (b * a))
    (hw : w = z * a - q • (a * z)) (hw' : w' = z * b - q • (b * z)) :
    (w * c - q • (c * w)) * b - q • (b * (w * c - q • (c * w))) =
      (w' * c' - q • (c' * w')) * a - q • (a * (w' * c' - q • (c' * w'))) := by
  subst hc hc' hw hw'
  set Rab := a * a * b - (q + q⁻¹) • (a * b * a) + b * a * a
  set Raz := a * a * z - (q + q⁻¹) • (a * z * a) + z * a * a
  set Rbz := b * b * z - (q + q⁻¹) • (b * z * b) + z * b * b
  have e1 : z * Rab * b = 0 := by rw [hab]; simp
  have e2 : z * b * Rab = 0 := by rw [hab]; simp
  have e3 : Rab * (b * z) = 0 := by rw [hab]; simp
  have e4 : b * Rab * z = 0 := by rw [hab]; simp
  have e5 : Raz * (b * b) = 0 := by rw [haz]; simp
  have e6 : b * Raz * b = 0 := by rw [haz]; simp
  have e7 : b * b * Raz = 0 := by rw [haz]; simp
  have e8 : Rbz * (a * a) = 0 := by rw [hbz]; simp
  have e9 : a * Rbz * a = 0 := by rw [hbz]; simp
  have e10 : a * a * Rbz = 0 := by rw [hbz]; simp
  linear_combination (norm := skip) (-(q + q⁻¹)⁻¹) • e1 +
    (q + q⁻¹)⁻¹ • e2 + (q ^ 4 * (q + q⁻¹)⁻¹) • e3 + (-(q ^ 4 * (q + q⁻¹)⁻¹)) • e4 +
    (-(q ^ 2 * (q + q⁻¹)⁻¹)) • e5 + (q ^ 2) • e6 + (-(q ^ 2 * (q + q⁻¹)⁻¹)) • e7 +
    (q ^ 2 * (q + q⁻¹)⁻¹) • e8 + (-(q ^ 2)) • e9 + (q ^ 2 * (q + q⁻¹)⁻¹) • e10
  simp only [Rab, Raz, Rbz, mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, smul_zero,
    mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
  have h2 : q ^ 2 + 1 ≠ 0 := by
    intro h; apply hs; field_simp; linear_combination h
  match_scalars <;> field_simp <;> ring

end Core

section Quantum

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {i j : I} {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
  (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
  (hqi : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (hsi : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

omit [NeZero v] in
lemma serre_E_two {l m : I} (hlm : l ≠ m) (h1 : D.cartanMatrix l m = -1) :
    E R v l * E R v l * E R v m - (v ^ D.d l + (v ^ D.d l)⁻¹) • (E R v l * E R v m * E R v l) +
      E R v m * E R v l * E R v l = 0 := by
  rw [← qSerre_two_eq]
  simpa only [h1, Int.reduceSub, Int.reduceToNat] using serre_E R v hlm

omit [NeZero v] in
lemma serre_F_two {l m : I} (hlm : l ≠ m) (h1 : D.cartanMatrix l m = -1) :
    F R v l * F R v l * F R v m - (v ^ D.d l + (v ^ D.d l)⁻¹) • (F R v l * F R v m * F R v l) +
      F R v m * F R v l * F R v l = 0 := by
  rw [← qSerre_two_eq]
  simpa only [h1, Int.reduceSub, Int.reduceToNat] using serre_F R v hlm

include HS HT hij h h' hqi hsi

/-- **Length three on `Eₗ` at a triangle**: for a third node `l` with `aᵢₗ = aⱼₗ = -1`
(the entries `aₗᵢ`, `aₗⱼ` are arbitrary), `Tᵢ Tⱼ Tᵢ (Eₗ) = Tⱼ Tᵢ Tⱼ (Eₗ)`. -/
theorem HasBraidGeneratorImages.three_E_triangle (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = -1) :
    S (T (S (E R v l))) = T (S (T (E R v l))) := by
  have hv := NeZero.ne v
  have hdj := D.d_eq_of_simply_laced_edge h h'
  have hqj : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by rwa [← hdj]
  have hSl : S (E R v l) = E R v i * E R v l - (v ^ D.d i)⁻¹ • (E R v l * E R v i) := by
    simp [HS.map_E, hli, braidEj_eq_of_cartanMatrix_eq_neg_one hil]
  have hTl : T (E R v l) = E R v j * E R v l - (v ^ D.d i)⁻¹ • (E R v l * E R v j) := by
    simp [HT.map_E, hlj, braidEj_eq_of_cartanMatrix_eq_neg_one hjl, hdj]
  have hSj : S (E R v j) = E R v i * E R v j - (v ^ D.d i)⁻¹ • (E R v j * E R v i) := by
    simp [HS.map_E, hij.symm, braidEj_eq_of_cartanMatrix_eq_neg_one h]
  have hTi : T (E R v i) = E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
    simp [HT.map_E, hij, braidEj_eq_of_cartanMatrix_eq_neg_one h', hdj]
  have hSTi : S (T (E R v i)) = E R v j := HS.three_double_E HT hij h h' hqi
  have hTSj : T (S (E R v j)) = E R v i := HT.three_double_E HS hij.symm h' h hqj
  rw [hSl, hTl]
  simp only [map_sub, map_mul, map_smul]
  rw [hSTi, hTSj]
  simp only [map_sub, map_mul, map_smul, hTl, hSl, hSj, hTi]
  have hab := serre_E_two (R := R) (v := v) hij h
  have haz := serre_E_two (R := R) (v := v) hli.symm hil
  have hbz := serre_E_two (R := R) (v := v) hlj.symm hjl
  rw [← hdj] at hbz
  exact triangle_core_E (pow_ne_zero _ hv) hsi hab haz hbz rfl rfl rfl rfl

/-- **Length three on `Fₗ` at a triangle**, `aᵢₗ = aⱼₗ = -1`. -/
theorem HasBraidGeneratorImages.three_F_triangle (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = -1) :
    S (T (S (F R v l))) = T (S (T (F R v l))) := by
  have hv := NeZero.ne v
  have hdj := D.d_eq_of_simply_laced_edge h h'
  have hqj : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by rwa [← hdj]
  have hSl : S (F R v l) = F R v l * F R v i - (v ^ D.d i) • (F R v i * F R v l) := by
    simp [HS.map_F, hli, braidFj_eq_of_cartanMatrix_eq_neg_one hv hil]
  have hTl : T (F R v l) = F R v l * F R v j - (v ^ D.d i) • (F R v j * F R v l) := by
    simp [HT.map_F, hlj, braidFj_eq_of_cartanMatrix_eq_neg_one hv hjl, hdj]
  have hSj : S (F R v j) = F R v j * F R v i - (v ^ D.d i) • (F R v i * F R v j) := by
    simp [HS.map_F, hij.symm, braidFj_eq_of_cartanMatrix_eq_neg_one hv h]
  have hTi : T (F R v i) = F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
    simp [HT.map_F, hij, braidFj_eq_of_cartanMatrix_eq_neg_one hv h', hdj]
  have hSTi : S (T (F R v i)) = F R v j := HS.three_double_F HT hij h h' hqi
  have hTSj : T (S (F R v j)) = F R v i := HT.three_double_F HS hij.symm h' h hqj
  rw [hSl, hTl]
  simp only [map_sub, map_mul, map_smul]
  rw [hSTi, hTSj]
  simp only [map_sub, map_mul, map_smul, hTl, hSl, hSj, hTi]
  have hab := serre_F_two (R := R) (v := v) hij h
  have haz := serre_F_two (R := R) (v := v) hli.symm hil
  have hbz := serre_F_two (R := R) (v := v) hlj.symm hjl
  rw [← hdj] at hbz
  exact triangle_core_F (pow_ne_zero _ hv) hsi hab haz hbz rfl rfl rfl rfl

omit hsi in
/-- **Length three at a mutual simple edge, with triangles**: if every other node `l` has
`aᵢₗ = 0`, `aⱼₗ = 0`, or `aᵢₗ = aⱼₗ = -1` (other entries arbitrary), then `Tᵢ Tⱼ Tᵢ = Tⱼ Tᵢ Tⱼ`
for algebra endomorphisms with Lusztig's generator formulas. Assumes `vᵢ - vᵢ⁻¹ ≠ 0`, the
q-factorials `[-aᵢₗ]ᵢ!`, `[-aⱼₗ]ⱼ!` nonzero and, when a triangle occurs, `vᵢ + vᵢ⁻¹ ≠ 0`. -/
theorem HasBraidGeneratorImages.three_braid_triangle
    (hfi : ∀ l, l ≠ i → qFactorial (v ^ D.d i) (negA D i l) ≠ 0)
    (hfj : ∀ l, l ≠ j → qFactorial (v ^ D.d j) (negA D j l) ≠ 0)
    (hout : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0 ∨ D.cartanMatrix j l = 0 ∨
      (D.cartanMatrix i l = -1 ∧ D.cartanMatrix j l = -1 ∧
        v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)) :
    S.comp (T.comp S) = T.comp (S.comp T) := by
  have hqj : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by
    simpa only [D.d_eq_of_simply_laced_edge h h'] using hqi
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hli : l = i
    · subst l
      exact HS.three_Ei HT hij h h' hqi
    · by_cases hlj : l = j
      · subst l
        exact (HT.three_Ei HS hij.symm h' h hqj).symm
      · rcases hout l hli hlj with hi0 | hj0 | ⟨hi1, hj1, hs⟩
        · exact (HT.three_E_outer HS hij.symm h' h hqj l hlj hli hi0 (hfj l hlj)).symm
        · exact HS.three_E_outer HT hij h h' hqi l hli hlj hj0 (hfi l hli)
        · exact HS.three_E_triangle HT hij h h' hqi hs l hli hlj hi1 hj1
  · by_cases hli : l = i
    · subst l
      exact HS.three_Fi HT hij h h' hqi
    · by_cases hlj : l = j
      · subst l
        exact (HT.three_Fi HS hij.symm h' h hqj).symm
      · rcases hout l hli hlj with hi0 | hj0 | ⟨hi1, hj1, hs⟩
        · exact (HT.three_F_outer HS hij.symm h' h hqj l hlj hli hi0 (hfj l hlj)).symm
        · exact HS.three_F_outer HT hij h h' hqi l hli hlj hj0 (hfi l hli)
        · exact HS.three_F_triangle HT hij h h' hqi hs l hli hlj hi1 hj1
  · simp only [AlgHom.comp_apply, HS.map_K, HT.map_K,
      reflY_braid_of_simply_laced_edge h h']

omit HS HT hij h h' hqi hsi

/-- The length-three relation for `braidEquiv` at a mutual simple edge of any Cartan datum,
allowing triangles `aᵢₗ = aⱼₗ = -1` (see `HasBraidGeneratorImages.three_braid_triangle`). -/
theorem braidEquiv_braid_three_triangle (hgi : BraidGeneric D v i)
    (hSi : TransformedSerre R v i) (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j)
    (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (hout : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0 ∨ D.cartanMatrix j l = 0 ∨
      (D.cartanMatrix i l = -1 ∧ D.cartanMatrix j l = -1 ∧
        v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)) :
    braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi =
      braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj := by
  have H := (braidHom_hasBraidGeneratorImages hgi hSi).three_braid_triangle
    (braidHom_hasBraidGeneratorImages hgj hSj) hij h h' hgi.sub_ne hgi.qFactorial_ne
    hgj.qFactorial_ne hout
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun H x

end Quantum

end LieLean.QuantumGroup
