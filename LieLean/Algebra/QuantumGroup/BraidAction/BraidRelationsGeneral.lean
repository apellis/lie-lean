/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.GeneralSerre
import LieLean.Algebra.QuantumGroup.BraidAction.GeneralRelations
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeRelation

/-!
# Braid relations of lengths three and six in arbitrary rank

We prove braid relations for Lusztig's automorphisms `Tᵢ` (any algebra endomorphisms with the
generator formulas `HasBraidGeneratorImages`, e.g. `braidEquivOfGeneric`) for pairs of nodes of a
Cartan datum of arbitrary rank, with conditions only on the third nodes:

* length three at a mutual simple edge `aᵢⱼ = aⱼᵢ = -1`, when no third node meets both `i` and
  `j`; the Cartan entries between `i` or `j` and the third nodes are arbitrary (the previous
  `HasBraidGeneratorImages.three_braid` needed them in `{0, -1, -2}`);
* length six at a `(-3, -1)` edge whose third nodes are orthogonal to both ends (the two-node
  part is `BraidAction/TripleEdgeRelation.lean`).

## Main results

* `QuantumGroup.TwoNode.three_outer_core`: for `b z = z b` and `S₂(b, a) = 0`,
  `(ad_b)ʳ (ad_a)ʳ z = [r]! (ad_c)ʳ z` with `c = b a - q⁻¹ a b` (twisted adjoint actions).
* `QuantumGroup.HasBraidGeneratorImages.three_E_outer`, `..._three_F_outer`:
  `Tᵢ Tⱼ Tᵢ (Eₗ) = Tⱼ Tᵢ Tⱼ (Eₗ)` for `aⱼₗ = 0` and arbitrary `aᵢₗ`, `aₗᵢ`.
* `QuantumGroup.HasBraidGeneratorImages.three_braid_outer`,
  `QuantumGroup.braidEquiv_braid_three_outer`.
* `QuantumGroup.HasBraidGeneratorImages.six_braid_of_triple_edge_of_orthogonal`,
  `QuantumGroup.braidEquiv_braid_six_of_orthogonal`.

## Method

With `a = Eᵢ`, `b = Eⱼ`, `z = Eₗ` and `r = -aᵢₗ`, we have `Tⱼ(Eₗ) = Eₗ`,
`Tᵢ(Eₗ) = [r]!⁻¹ (ad_a)ʳ z` and `Tᵢ Tⱼ (Eᵢ) = Eⱼ` (`HasBraidGeneratorImages.three_double_E`), so
both sides of the relation on `Eₗ` are twisted iterated commutators, and the relation is the core
identity above. It follows from the Gaussian Leibniz rule `TwoNode.dd_mul` by the iteration
`TwoNode.dd_serreAux_eq`: `(ad_b)ʳ` kills every term of `(ad_a)ʳ z` except the one where each
factor `a` is hit exactly once, since `(ad_b)² a = 0` and `ad_b z = 0`.

## Remaining cases

A third node meeting both ends of a simple edge (a triangle) needs the rank-three identity of
`(ad_a)^{(t)} (ad_b)^{(r+t)} (ad_a)^{(r)}` type and is not treated. Third nodes meeting a
`(-3, -1)` edge are not treated either.

## References

Reconstructed. G. Lusztig, *Introduction to quantum groups*, 39.4, for the statement.
-/

noncomputable section

open Finset

namespace QuantumGroup

namespace TwoNode

open BraidDiagonal ShortNode

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B] {q : k}

/-- `dd_serreAux` with the explicit scalar. -/
lemma dd_serreAux_eq (hq : q ≠ 0) {e x : B} {c0 p : k} (hp : p ≠ 0) {r : ℕ}
    (hX : dd q e c0 (r + 1) x = 0) (m : ℕ) : ∀ (c cZ : k) (M : ℕ) (Z Z' : B),
    cZ ^ r = c0 ^ M → dd q e cZ (M + 1) Z = 0 → dd q e cZ M Z = Z' →
      dd q e (c0 ^ m * cZ) (M + m * r) (serreAux p c m x Z) =
        (∏ l ∈ range m, (gauss q (M + (l + 1) * r) r * c0 ^ (M + l * r))) •
          serreAux p c m (dd q e c0 r x) Z' ∧
      dd q e (c0 ^ m * cZ) (M + m * r + 1) (serreAux p c m x Z) = 0 := by
  induction m with
  | zero =>
    intro c cZ M Z Z' _ h1 h0
    refine ⟨?_, ?_⟩ <;> simp [serreAux, h0, h1]
  | succ m ih =>
    intro c cZ M Z Z' htw h1 h0
    obtain ⟨hs0, hs1⟩ := dd_step hq hX htw h1 h0 (c * p ^ m)
    have htw' : (c0 * cZ) ^ r = c0 ^ (M + r) := by rw [mul_pow, htw, ← pow_add, add_comm]
    obtain ⟨e0, e1⟩ := ih (c * p⁻¹) (c0 * cZ) (M + r) _ _ htw' hs1 hs0
    refine ⟨?_, ?_⟩
    · rw [serreAux_succ hp, show c0 ^ (m + 1) * cZ = c0 ^ m * (c0 * cZ) by ring,
        show M + (m + 1) * r = M + r + m * r by ring, e0, serreAux_smul_right, smul_smul,
        ← serreAux_succ hp, prod_range_succ']
      congr 2
      · refine prod_congr rfl fun l _ ↦ ?_
        rw [show M + r + (l + 1) * r = M + (l + 1 + 1) * r by ring,
          show M + r + l * r = M + (l + 1) * r by ring]
      · simp
    · rw [serreAux_succ hp, show c0 ^ (m + 1) * cZ = c0 ^ m * (c0 * cZ) by ring,
        show M + (m + 1) * r + 1 = M + r + m * r + 1 by ring, e1]

/-- The twisted commutators are linear in the second argument. -/
lemma X_smul_right (Q s : k) (e x : B) (n : ℕ) : X q Q e (s • x) n = s • X q Q e x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [X_succ, X_succ, ih, mul_smul_comm, smul_mul_assoc, smul_comm (shift q Q n) s, ← smul_sub]

/-- Scaling the acting element scales the `n`-th twisted commutator by `sⁿ`. -/
lemma X_smul_left (Q s : k) (e x : B) (n : ℕ) : X q Q (s • e) x n = s ^ n • X q Q e x n := by
  induction n with
  | zero => simp [X]
  | succ n ih =>
    rw [X_succ, X_succ, ih, pow_succ]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
    congr 2; ring

/-- Algebra homomorphisms commute with twisted commutators. -/
lemma map_X {B' : Type*} [Ring B'] [Algebra k B'] (f : B →ₐ[k] B') (Q : k) (e x : B)
    (n : ℕ) : f (X q Q e x n) = X q Q (f e) (f x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [X_succ, X_succ, map_sub, map_mul, map_smul, map_mul, ih]

/-- **The core identity for length three at an outer node.** If `b z = z b` and
`S₂(b, a) = 0`, then `r` twisted derivations by `b` send `(ad a)ʳ z` to
`[r]! (ad c)ʳ z`, where `c = b a - q⁻¹ a b`. -/
lemma three_outer_core (hq : q ≠ 0) {a b z : B} {r : ℕ} (hab : X q q b a 2 = 0)
    (hbz : b * z = z * b) :
    X q (q ^ r) b (X q (q ^ r) a z r) r =
      qFactorial q r • X q (q ^ r) (b * a - q⁻¹ • (a * b)) z r := by
  have hc (n : ℕ) : q ^ n * (q * q ^ n)⁻¹ = q⁻¹ := by field_simp
  rw [X_eq_dd, X_eq_serreAux hq (pow_ne_zero _ hq), X_eq_serreAux hq (pow_ne_zero _ hq), hc]
  have hX : dd q b q⁻¹ (1 + 1) a = 0 := by
    rw [X_eq_dd] at hab
    exact hab
  have h1 : dd q b 1 (0 + 1) z = 0 := by
    simp [dd_succ, hbz]
  obtain ⟨e0, -⟩ := dd_serreAux_eq hq hq hX r q⁻¹ 1 0 z z (by simp) h1 rfl
  rw [show (q⁻¹ : k) ^ r * 1 = (q ^ r)⁻¹ by rw [mul_one, inv_pow],
    show 0 + r * 1 = r by ring] at e0
  rw [e0]
  congr 1
  · rw [qFactorial_eq_prod]
    refine prod_congr rfl fun l _ ↦ ?_
    simp only [gauss, zero_add, one_mul, mul_one, qBinomial_one_right,
      show l + 1 - 1 = l by omega]
    rw [inv_pow]
    field_simp
  · simp [dd_succ]

end TwoNode

end QuantumGroup

/-! ### Length three at an outer node meeting one endpoint -/

namespace QuantumGroup

open BraidDiagonal

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

variable (R v) in
/-- `Tᵢ(Fₗ) = (-1)ʳ vᵢʳ [r]ᵢ!⁻¹ Y r` (`r = -aᵢₗ`), with `Y` the twisted commutators of `Fₗ`. -/
lemma braidFj_eq_smul_X (hv : v ≠ 0) (i l : I) :
    braidFj R v i l = ((qFactorial (v ^ D.d i) (negA D i l))⁻¹ * (-1) ^ negA D i l *
      (v ^ D.d i) ^ negA D i l) •
      X (v ^ D.d i) ((v ^ D.d i) ^ negA D i l) (F R v i) (F R v l) (negA D i l) := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hc : (v ^ D.d i) ^ negA D i l * (v ^ D.d i * (v ^ D.d i) ^ negA D i l)⁻¹ =
      (v ^ D.d i)⁻¹ := by
    field_simp
  rw [X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc, braidFj]

variable [NeZero v] {i j : I} {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
  (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
  (hqi : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)

include HS HT hij h h' hqi

/-- **Length three on `Eₗ` for an outer node joined only to `i`**, with arbitrary entries
`aᵢₗ`, `aₗᵢ`: `Tᵢ Tⱼ Tᵢ (Eₗ) = Tⱼ Tᵢ Tⱼ (Eₗ)`. -/
theorem HasBraidGeneratorImages.three_E_outer (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hj0 : D.cartanMatrix j l = 0) (hr : qFactorial (v ^ D.d i) (negA D i l) ≠ 0) :
    S (T (S (E R v l))) = T (S (T (E R v l))) := by
  have hv := NeZero.ne v
  have hdj := D.d_eq_of_simply_laced_edge h h'
  set q := v ^ D.d i with hqdef
  have hq : q ≠ 0 := pow_ne_zero _ hv
  set r := negA D i l
  have hTl : T (E R v l) = E R v l := by
    simp [HT.map_E, hlj, braidEj_eq_of_cartanMatrix_eq_zero hj0]
  have hSl : S (E R v l) = (qFactorial q r)⁻¹ • X q (q ^ r) (E R v i) (E R v l) r := by
    simp only [HS.map_E, hli, ↓reduceIte]
    rw [braidEj_eq_smul_X R v hv i l]
  have hTi : T (E R v i) = E R v j * E R v i - q⁻¹ • (E R v i * E R v j) := by
    simp [HT.map_E, hij, braidEj_eq_of_cartanMatrix_eq_neg_one h', hdj, q]
  have hSTi : S (T (E R v i)) = E R v j := HS.three_double_E HT hij h h' hqi
  have hab : X q q (E R v j) (E R v i) 2 = 0 := by
    have hc : q ^ 2 * (q * q)⁻¹ = 1 := by field_simp
    have hs := serre_E R v hij.symm
    rw [one_sub_cartanMatrix_toNat hij.symm, show negA D j i = 1 by simp [negA, h'], ← hdj]
      at hs
    rw [X_eq_serreAux hq hq, hc, serreAux_one]
    exact hs
  have hbz : E R v j * E R v l = E R v l * E R v j :=
    (E_commute_E_of_cartanMatrix_eq_zero hj0).eq
  have hcore := TwoNode.three_outer_core (r := r) hq hab hbz
  have hTSl : T (S (E R v l)) = (qFactorial q r)⁻¹ •
      X q (q ^ r) (E R v j * E R v i - q⁻¹ • (E R v i * E R v j)) (E R v l) r := by
    rw [hSl, map_smul, TwoNode.map_X, hTl, hTi]
  have hSc : S (E R v j * E R v i - q⁻¹ • (E R v i * E R v j)) = E R v j := by
    rw [← hTi]; exact hSTi
  rw [hTSl, hTl, hTSl, map_smul, TwoNode.map_X, hSc, hSl, TwoNode.X_smul_right, hcore,
    smul_smul, smul_smul]
  congr 1
  field_simp

/-- **Length three on `Fₗ` for an outer node joined only to `i`**, arbitrary entries. -/
theorem HasBraidGeneratorImages.three_F_outer (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hj0 : D.cartanMatrix j l = 0) (hr : qFactorial (v ^ D.d i) (negA D i l) ≠ 0) :
    S (T (S (F R v l))) = T (S (T (F R v l))) := by
  have hv := NeZero.ne v
  have hdj := D.d_eq_of_simply_laced_edge h h'
  set q := v ^ D.d i with hqdef
  have hq : q ≠ 0 := pow_ne_zero _ hv
  set r := negA D i l
  set α := (qFactorial q r)⁻¹ * (-1) ^ r * q ^ r
  have hTl : T (F R v l) = F R v l := by
    simp [HT.map_F, hlj, braidFj_eq_of_cartanMatrix_eq_zero hj0]
  have hSl : S (F R v l) = α • X q (q ^ r) (F R v i) (F R v l) r := by
    simp only [HS.map_F, hli, ↓reduceIte]
    rw [braidFj_eq_smul_X R v hv i l]
  have hTi : T (F R v i) = (-q) • (F R v j * F R v i - q⁻¹ • (F R v i * F R v j)) := by
    have e : T (F R v i) = F R v i * F R v j - q • (F R v j * F R v i) := by
      simp [HT.map_F, hij, braidFj_eq_of_cartanMatrix_eq_neg_one hv h', hdj, q]
    rw [e, smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hq]
    module
  have hSTi : S (T (F R v i)) = F R v j := HS.three_double_F HT hij h h' hqi
  have hab : X q q (F R v j) (F R v i) 2 = 0 := by
    have hc : q ^ 2 * (q * q)⁻¹ = 1 := by field_simp
    have hs := serre_F R v hij.symm
    rw [one_sub_cartanMatrix_toNat hij.symm, show negA D j i = 1 by simp [negA, h'], ← hdj]
      at hs
    rw [X_eq_serreAux hq hq, hc, serreAux_one]
    exact hs
  have hbz : F R v j * F R v l = F R v l * F R v j :=
    (F_commute_F_of_cartanMatrix_eq_zero hj0).eq
  have hcore := TwoNode.three_outer_core (r := r) hq hab hbz
  have hTSl : T (S (F R v l)) = α • X q (q ^ r) (T (F R v i)) (F R v l) r := by
    rw [hSl, map_smul, TwoNode.map_X, hTl]
  rw [hTl, hTSl, map_smul, TwoNode.map_X, hSTi, hSl, TwoNode.X_smul_right, hcore, hTi,
    TwoNode.X_smul_left, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [α]
  rw [neg_pow q r, show (-1 : k) ^ r = (-1) ^ r from rfl]
  field_simp

/-- **Length three at a mutual simple edge, in arbitrary rank**: if every other node meets at
most one of `i, j` (with arbitrary Cartan entries), then `Tᵢ Tⱼ Tᵢ = Tⱼ Tᵢ Tⱼ` for any algebra
endomorphisms with Lusztig's generator formulas. The `q`-factorials `[−aᵢₗ]ᵢ!`, `[−aⱼₗ]ⱼ!` are
assumed nonzero (they are, e.g., under `BraidGeneric`). -/
theorem HasBraidGeneratorImages.three_braid_outer
    (hfi : ∀ l, l ≠ i → qFactorial (v ^ D.d i) (negA D i l) ≠ 0)
    (hfj : ∀ l, l ≠ j → qFactorial (v ^ D.d j) (negA D j l) ≠ 0)
    (hout : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0 ∨ D.cartanMatrix j l = 0) :
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
      · rcases hout l hli hlj with hi0 | hj0
        · exact (HT.three_E_outer HS hij.symm h' h hqj l hlj hli hi0 (hfj l hlj)).symm
        · exact HS.three_E_outer HT hij h h' hqi l hli hlj hj0 (hfi l hli)
  · by_cases hli : l = i
    · subst l
      exact HS.three_Fi HT hij h h' hqi
    · by_cases hlj : l = j
      · subst l
        exact (HT.three_Fi HS hij.symm h' h hqj).symm
      · rcases hout l hli hlj with hi0 | hj0
        · exact (HT.three_F_outer HS hij.symm h' h hqj l hlj hli hi0 (hfj l hlj)).symm
        · exact HS.three_F_outer HT hij h h' hqi l hli hlj hj0 (hfi l hli)
  · simp only [AlgHom.comp_apply, HS.map_K, HT.map_K,
      reflY_braid_of_simply_laced_edge h h']

omit HS HT hij h h' hqi

/-- The length-three relation `Tᵢ Tⱼ Tᵢ = Tⱼ Tᵢ Tⱼ` for the general braid automorphisms
`braidEquiv` at a mutual simple edge of any Cartan datum, provided no third node meets both
`i` and `j`; the Cartan entries at the other nodes are arbitrary. -/
theorem braidEquiv_braid_three_outer (hgi : BraidGeneric D v i) (hSi : TransformedSerre R v i)
    (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j) (hij : i ≠ j)
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (hout : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0 ∨ D.cartanMatrix j l = 0) :
    braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi =
      braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj := by
  have H := (braidHom_hasBraidGeneratorImages hgi hSi).three_braid_outer
    (braidHom_hasBraidGeneratorImages hgj hSj) hij h h' hgi.sub_ne hgi.qFactorial_ne
    hgj.qFactorial_ne hout
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun H x

/-! ### Length six at a triple edge in arbitrary rank -/

section Six

variable {i j : I} {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}

/-- **Length six at a `(-3, -1)` edge in arbitrary rank**, when every other node is orthogonal
to both `i` and `j`: `Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ = Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ` for any algebra endomorphisms with
Lusztig's generator formulas, assuming `vᵢ - vᵢ⁻¹ ≠ 0` and `[3]ᵢ! ≠ 0`. The two-node part is
`BraidAction/TripleEdgeRelation.lean`; the other generators are fixed by both maps. -/
theorem HasBraidGeneratorImages.six_braid_of_triple_edge_of_orthogonal
    (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T) (hij : i ≠ j)
    (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (h3 : qFactorial (v ^ D.d i) 3 ≠ 0)
    (hout : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) :
    S.comp (T.comp (S.comp (T.comp (S.comp T)))) =
      T.comp (S.comp (T.comp (S.comp (T.comp S)))) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hli : l = i
    · subst l
      exact tripleSix_six_Ei HS HT hij h h' hq h3
    by_cases hlj : l = j
    · subst l
      exact tripleSix_six_Ej HS HT hij h h' hq h3
    obtain ⟨hi0, hj0⟩ := hout l hli hlj
    simp [HS.map_E, HT.map_E, hli, hlj,
      braidEj_eq_of_cartanMatrix_eq_zero hi0, braidEj_eq_of_cartanMatrix_eq_zero hj0]
  · by_cases hli : l = i
    · subst l
      exact tripleSix_six_Fi HS HT hij h h' hq h3
    by_cases hlj : l = j
    · subst l
      exact tripleSix_six_Fj HS HT hij h h' hq h3
    obtain ⟨hi0, hj0⟩ := hout l hli hlj
    simp [HS.map_F, HT.map_F, hli, hlj,
      braidFj_eq_of_cartanMatrix_eq_zero hi0, braidFj_eq_of_cartanMatrix_eq_zero hj0]
  · simp only [AlgHom.comp_apply, HS.map_K, HT.map_K, reflY_braid_six_of_triple_edge h h']

/-- The length-six relation for the general braid automorphisms `braidEquiv` at a `(-3, -1)`
edge of any Cartan datum whose other nodes are orthogonal to both ends. -/
theorem braidEquiv_braid_six_of_orthogonal (hgi : BraidGeneric D v i)
    (hSi : TransformedSerre R v i) (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j)
    (hij : i ≠ j) (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
    (h3 : qFactorial (v ^ D.d i) 3 ≠ 0)
    (hout : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) :
    braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj *
        braidEquiv hgi hSi * braidEquiv hgj hSj =
      braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi *
        braidEquiv hgj hSj * braidEquiv hgi hSi := by
  have H := (braidHom_hasBraidGeneratorImages hgi hSi).six_braid_of_triple_edge_of_orthogonal
    (braidHom_hasBraidGeneratorImages hgj hSj) hij h h' hgi.sub_ne h3 hout
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun H x

end Six

end QuantumGroup
