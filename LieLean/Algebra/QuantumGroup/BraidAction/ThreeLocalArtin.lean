/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.NextEdge

/-!
# Length three with degree-two external neighbours

## Main results
Constructor-independent simple-edge braid relations and actual local-map consumers.

## References
Reconstructed from the quotient presentation and degree-one recovery proofs. The degree-five
external certificate uses only the original two simple-edge Serre relations and orthogonal
outer-node commutation.
-/
noncomputable section
namespace QuantumGroup
section Polynomial
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Numerator of the outgoing degree-two positive braid image. -/
def threeNextP (q : k) (a c : B) : B :=
  a ^ 2 * c - ((q + q⁻¹) * q⁻¹) • (a * c * a) + q⁻¹ ^ 2 • (c * a ^ 2)

/-- Numerator of the outgoing degree-two negative braid image. -/
def threeNextQ (q : k) (a c : B) : B :=
  q ^ 2 • (a ^ 2 * c) - ((q + q⁻¹) * q) • (a * c * a) + c * a ^ 2

set_option maxHeartbeats 2000000 in
-- The eight contextual Serre multiples expand degree-five noncommutative products.
/-- Degree-five external certificate. Only original simple-edge Serre relations
are used; no relation involving the nonorthogonal external edge is needed. -/
theorem threeNext_polynomial (q : k) (hq : q ≠ 0) (a b c : B)
    (hS : qSerre q 2 a b = 0) (hT : qSerre q 2 b a = 0)
    (hbc : Commute b c) :
    threeNextP q b (threeNextP q a c) =
      (q + q⁻¹) • threeNextP q (b * a - q⁻¹ • (a * b)) c := by
  have h0 := congrArg (fun z : B ↦ z * b * c) hS
  have h1 := congrArg (fun z : B ↦ b * z * c) hS
  have h2 := congrArg (fun z : B ↦ b * c * z) hS
  have h3 := congrArg (fun z : B ↦ c * z * b) hS
  have h4 := congrArg (fun z : B ↦ z * a * c) hT
  have h5 := congrArg (fun z : B ↦ a * c * z) hT
  have h6 := congrArg (fun z : B ↦ z * c * a) hT
  have h7 := congrArg (fun z : B ↦ c * z * a) hT
  have hcb (z : B) : c * (b * z) = b * (c * z) := by
    rw [← mul_assoc, hbc.symm.eq, mul_assoc]
  simp only [threeNextP, qSerre, Finset.sum_range_succ, Finset.sum_range_zero,
    qBinomial, Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero,
    zero_mul, add_zero, zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub,
    sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub,
    smul_smul, mul_assoc, hbc.symm.eq, hcb] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := (match_scalars <;> field_simp [hq] <;> ring))
    q⁻¹ ^ 2 • h0 - q⁻¹ ^ 2 • h1 - q⁻¹ ^ 4 • h2 + q⁻¹ ^ 4 • h3 +
      (q⁻¹ ^ 2 + 1) • h4 - (q⁻¹ ^ 4 + q⁻¹ ^ 2) • h5 -
      (q⁻¹ ^ 2 + 1) • h6 + (q⁻¹ ^ 4 + q⁻¹ ^ 2) • h7

/-- Opposite-algebra transport gives exactly the negative degree-two certificate. -/
theorem threeNext_polynomial_right (q : k) (hq : q ≠ 0) (a b c : B)
    (hS : qSerre q 2 a b = 0) (hT : qSerre q 2 b a = 0)
    (hbc : Commute b c) :
    threeNextQ q b (threeNextQ q a c) =
      (q + q⁻¹) • threeNextQ q (a * b - q • (b * a)) c := by
  have hSop : qSerre q⁻¹ 2 (MulOpposite.op a) (MulOpposite.op b) = 0 := by
    rw [qSerre_inv, qSerre_op, hS, MulOpposite.op_zero, smul_zero]
  have hTop : qSerre q⁻¹ 2 (MulOpposite.op b) (MulOpposite.op a) = 0 := by
    rw [qSerre_inv, qSerre_op, hT, MulOpposite.op_zero, smul_zero]
  have hh := congrArg MulOpposite.unop (threeNext_polynomial q⁻¹ (inv_ne_zero hq)
    (MulOpposite.op a) (MulOpposite.op b) (MulOpposite.op c) hSop hTop hbc.op)
  simp only [threeNextP, inv_inv, MulOpposite.unop_mul, MulOpposite.unop_add,
    MulOpposite.unop_sub, MulOpposite.unop_smul, MulOpposite.unop_pow,
    MulOpposite.unop_op] at hh
  dsimp only [threeNextQ]
  convert hh using 1 <;> noncomm_ring

/-- Algebra homomorphisms preserve the degree-two positive numerator. -/
theorem threeNextP_map (T : B →ₐ[k] B) (q : k) (a c : B) :
    T (threeNextP q a c) = threeNextP q (T a) (T c) := by
  simp only [threeNextP, map_add, map_sub, map_mul, map_pow, map_smul]

/-- The positive numerator is linear in its external entry. -/
theorem threeNextP_smul (q r : k) (a c : B) :
    threeNextP q a (r • c) = r • threeNextP q a c := by
  simp only [threeNextP, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul]
  module

/-- Algebra homomorphisms preserve the degree-two negative numerator. -/
theorem threeNextQ_map (T : B →ₐ[k] B) (q : k) (a c : B) :
    T (threeNextQ q a c) = threeNextQ q (T a) (T c) := by
  simp only [threeNextQ, map_add, map_sub, map_mul, map_pow, map_smul]

/-- The negative numerator is linear in its external entry. -/
theorem threeNextQ_smul (q r : k) (a c : B) :
    threeNextQ q a (r • c) = r • threeNextQ q a c := by
  simp only [threeNextQ, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul]
  module

/-- The positive certificate with the actual divided-power normalization. -/
theorem threeNext_normalized (q : k) (hq : q ≠ 0) (a b c : B)
    (hS : qSerre q 2 a b = 0) (hT : qSerre q 2 b a = 0) (hbc : Commute b c) :
    (q + q⁻¹)⁻¹ • threeNextP q b ((q + q⁻¹)⁻¹ • threeNextP q a c) =
      (q + q⁻¹)⁻¹ • threeNextP q (b * a - q⁻¹ • (a * b)) c := by
  rw [threeNextP_smul, smul_smul, threeNext_polynomial q hq a b c hS hT hbc,
    smul_smul]
  congr 1
  field_simp

/-- The negative certificate with the actual divided-power normalization. -/
theorem threeNext_normalized_right (q : k) (hq : q ≠ 0)
    (a b c : B) (hS : qSerre q 2 a b = 0) (hT : qSerre q 2 b a = 0)
    (hbc : Commute b c) :
    (q + q⁻¹)⁻¹ • threeNextQ q b ((q + q⁻¹)⁻¹ • threeNextQ q a c) =
      (q + q⁻¹)⁻¹ • threeNextQ q (a * b - q • (b * a)) c := by
  rw [threeNextQ_smul, smul_smul, threeNext_polynomial_right q hq a b c hS hT hbc,
    smul_smul]
  congr 1
  field_simp

end Polynomial

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {i j : I} {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
  (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
  (hqi : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)

include HS HT hij h h' hqi

/-- Double transport at an adjacent pair, with arbitrary extra generators present. -/
theorem HasBraidGeneratorImages.three_double_E : S (T (E R v i)) = E R v j := by
  rw [HT.map_E, ite_eq_right hij,
    braidEj_eq_of_cartanMatrix_eq_neg_one h']
  simpa only [map_sub, map_mul, map_smul, HS.map_E, HT.map_E, hij.symm, ↓reduceIte,
    ← D.d_eq_of_simply_laced_edge h h'] using a2Braid_recover_Ej (R := R) i j h hqi

/-- Negative double transport in arbitrary ambient rank. -/
theorem HasBraidGeneratorImages.three_double_F : S (T (F R v i)) = F R v j := by
  rw [HT.map_F, ite_eq_right hij,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h']
  simpa only [map_sub, map_mul, map_smul, HS.map_F, HT.map_F, hij.symm, ↓reduceIte,
    ← D.d_eq_of_simply_laced_edge h h'] using a2Braid_recover_Fj (R := R) i j h hqi

/-- The length-three words agree on the first positive generator. -/
theorem HasBraidGeneratorImages.three_Ei : S (T (S (E R v i))) = T (S (T (E R v i))) := by
  rw [HasBraidGeneratorImages.three_double_E HS HT hij h h' hqi]
  simp only [HS.map_E, HT.map_E, ↓reduceIte, braidEi, map_neg, map_mul, Kt,
    HS.map_K, HT.map_K,
    HasBraidGeneratorImages.three_double_F HS HT hij h h' hqi,
    reflY_reflY_ktilde_of_simply_laced_edge h h']

/-- The length-three words agree on the first negative generator. -/
theorem HasBraidGeneratorImages.three_Fi : S (T (S (F R v i))) = T (S (T (F R v i))) := by
  rw [HasBraidGeneratorImages.three_double_F HS HT hij h h' hqi]
  simp only [HS.map_F, HT.map_F, ↓reduceIte, braidFi, map_neg, map_mul,
    HS.map_K, HT.map_K,
    HasBraidGeneratorImages.three_double_E HS HT hij h h' hqi,
    reflY_reflY_ktilde_of_simply_laced_edge h h']

/-- The new ambient-rank positive case: a third node joined to `i` and orthogonal
to `j`. Reconstructed using double transport and quantum Jacobi. -/
theorem HasBraidGeneratorImages.three_E_one (l : I) (hli' : l ≠ i) (hlj' : l ≠ j)
    (hi1 : D.cartanMatrix i l = -1) (hj0 : D.cartanMatrix j l = 0) :
    S (T (S (E R v l))) = T (S (T (E R v l))) := by
  have hiEl : S (E R v l) =
      E R v i * E R v l - (v ^ D.d i)⁻¹ • (E R v l * E R v i) := by
    simp [HS.map_E, hli', braidEj_eq_of_cartanMatrix_eq_neg_one hi1]
  have hjEl : T (E R v l) = E R v l := by
    simp [HT.map_E, hlj', braidEj_eq_of_cartanMatrix_eq_zero hj0]
  have hjEi : T (E R v i) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
    simp [HT.map_E, hij, braidEj_eq_of_cartanMatrix_eq_neg_one h',
      D.d_eq_of_simply_laced_edge h h']
  calc
    S (T (S (E R v l))) =
        E R v j * S (E R v l) - (v ^ D.d i)⁻¹ • (S (E R v l) * E R v j) := by
      rw [hiEl, map_sub, map_mul, map_smul, map_mul, hjEl,
        map_sub, map_mul, map_smul, map_mul,
        HasBraidGeneratorImages.three_double_E HS HT hij h h' hqi, hiEl]
    _ = T (E R v i) * E R v l - (v ^ D.d i)⁻¹ • (E R v l * T (E R v i)) := by
      rw [hiEl, hjEi]
      exact simplyLaced_qjacobi _ _ (E_commute_E_of_cartanMatrix_eq_zero hj0)
    _ = T (S (T (E R v l))) := by
      rw [hjEl, hiEl, map_sub, map_mul, map_smul, map_mul, hjEl]

/-- The new ambient-rank negative case at the same three-node path. -/
theorem HasBraidGeneratorImages.three_F_one (l : I) (hli' : l ≠ i) (hlj' : l ≠ j)
    (hi1 : D.cartanMatrix i l = -1) (hj0 : D.cartanMatrix j l = 0) :
    S (T (S (F R v l))) = T (S (T (F R v l))) := by
  have hiFl : S (F R v l) =
      F R v l * F R v i - (v ^ D.d i) • (F R v i * F R v l) := by
    simp [HS.map_F, hli', braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hi1]
  have hjFl : T (F R v l) = F R v l := by
    simp [HT.map_F, hlj', braidFj_eq_of_cartanMatrix_eq_zero hj0]
  have hjFi : T (F R v i) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
    simp [HT.map_F, hij, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h',
      D.d_eq_of_simply_laced_edge h h']
  calc
    S (T (S (F R v l))) =
        S (F R v l) * F R v j - (v ^ D.d i) • (F R v j * S (F R v l)) := by
      rw [hiFl, map_sub, map_mul, map_smul, map_mul, hjFl,
        map_sub, map_mul, map_smul, map_mul,
        HasBraidGeneratorImages.three_double_F HS HT hij h h' hqi, hiFl]
    _ = F R v l * T (F R v i) - (v ^ D.d i) • (T (F R v i) * F R v l) := by
      rw [hiFl, hjFi]
      exact simplyLaced_qjacobi_right _ _ (F_commute_F_of_cartanMatrix_eq_zero hj0)
    _ = T (S (T (F R v l))) := by
      rw [hjFl, hiFl, map_sub, map_mul, map_smul, map_mul, hjFl]

/-- Length three on an external positive generator with outgoing Cartan entry -2.
The reverse external entry and its symmetrizer are unrestricted. -/
theorem HasBraidGeneratorImages.three_E_two
    (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hi2 : D.cartanMatrix i l = -2) (hj0 : D.cartanMatrix j l = 0) :
    S (T (S (E R v l))) = T (S (T (E R v l))) := by
  let q := v ^ D.d i
  have hiEl : S (E R v l) = (q + q⁻¹)⁻¹ • threeNextP q (E R v i) (E R v l) := by
    simp [HS.map_E, hli, braidEj_eq_of_cartanMatrix_eq_neg_two hi2, threeNextP, q]
  have hjEl : T (E R v l) = E R v l := by
    simp [HT.map_E, hlj, braidEj_eq_of_cartanMatrix_eq_zero hj0]
  have hjEi : T (E R v i) = E R v j * E R v i - q⁻¹ • (E R v i * E R v j) := by
    simp [HT.map_E, hij, braidEj_eq_of_cartanMatrix_eq_neg_one h',
      q, D.d_eq_of_simply_laced_edge h h']
  have hS : qSerre q 2 (E R v i) (E R v j) = 0 := by
    simpa only [h, Int.reduceSub, Int.reduceToNat] using serre_E R v hij
  have hT : qSerre q 2 (E R v j) (E R v i) = 0 := by
    simpa only [h', Int.reduceSub, Int.reduceToNat, q,
      D.d_eq_of_simply_laced_edge h h'] using serre_E R v hij.symm
  calc
    S (T (S (E R v l))) = (q + q⁻¹)⁻¹ • threeNextP q (E R v j) (S (E R v l)) := by
      rw [hiEl]
      simp only [map_smul, threeNextP_map, hjEl, HS.three_double_E HT hij h h' hqi, hiEl]
    _ = (q + q⁻¹)⁻¹ •
        threeNextP q (E R v j * E R v i - q⁻¹ • (E R v i * E R v j)) (E R v l) := by
      rw [hiEl]
      exact threeNext_normalized q (pow_ne_zero _ (NeZero.ne v)) _ _ _ hS hT
        (E_commute_E_of_cartanMatrix_eq_zero hj0)
    _ = T (S (T (E R v l))) := by
      rw [hjEl, hiEl]
      simp only [map_smul, threeNextP_map, hjEl, hjEi]

/-- Length three on the negative degree-two external generator, with unchanged symmetrizers. -/
theorem HasBraidGeneratorImages.three_F_two
    (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hi2 : D.cartanMatrix i l = -2) (hj0 : D.cartanMatrix j l = 0) :
    S (T (S (F R v l))) = T (S (T (F R v l))) := by
  let q := v ^ D.d i
  have hiFl : S (F R v l) = (q + q⁻¹)⁻¹ • threeNextQ q (F R v i) (F R v l) := by
    simp [HS.map_F, hli, braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) hi2,
      threeNextQ, q]
  have hjFl : T (F R v l) = F R v l := by
    simp [HT.map_F, hlj, braidFj_eq_of_cartanMatrix_eq_zero hj0]
  have hjFi : T (F R v i) = F R v i * F R v j - q • (F R v j * F R v i) := by
    simp [HT.map_F, hij, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h',
      q, D.d_eq_of_simply_laced_edge h h']
  have hS : qSerre q 2 (F R v i) (F R v j) = 0 := by
    simpa only [h, Int.reduceSub, Int.reduceToNat] using serre_F R v hij
  have hT : qSerre q 2 (F R v j) (F R v i) = 0 := by
    simpa only [h', Int.reduceSub, Int.reduceToNat, q,
      D.d_eq_of_simply_laced_edge h h'] using serre_F R v hij.symm
  calc
    S (T (S (F R v l))) = (q + q⁻¹)⁻¹ • threeNextQ q (F R v j) (S (F R v l)) := by
      rw [hiFl]
      simp only [map_smul, threeNextQ_map, hjFl, HS.three_double_F HT hij h h' hqi, hiFl]
    _ = (q + q⁻¹)⁻¹ •
        threeNextQ q (F R v i * F R v j - q • (F R v j * F R v i)) (F R v l) := by
      rw [hiFl]
      exact threeNext_normalized_right q (pow_ne_zero _ (NeZero.ne v)) _ _ _ hS hT
        (F_commute_F_of_cartanMatrix_eq_zero hj0)
    _ = T (S (T (F R v l))) := by
      rw [hjFl, hiFl]
      simp only [map_smul, threeNextQ_map, hjFl, hjFi]


/-- Length three on the entire quotient, allowing degree-two external neighbours.
Every external node meets at most one centre, with outgoing entry zero, -1 or -2.
No map-existence claim is made by this constructor-independent theorem. -/
theorem HasBraidGeneratorImages.three_braid
    (hout : ∀ l, l ≠ i → l ≠ j →
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
      ((D.cartanMatrix i l = -1 ∨ D.cartanMatrix i l = -2) ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = 0 ∧ (D.cartanMatrix j l = -1 ∨ D.cartanMatrix j l = -2))) :
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
      · rcases hout l hli hlj with ⟨hi0, hj0⟩ | ⟨hi1 | hi2, hj0⟩ | ⟨hi0, hj1 | hj2⟩
        · simp [HS.map_E, HT.map_E, hli, hlj,
            braidEj_eq_of_cartanMatrix_eq_zero hi0, braidEj_eq_of_cartanMatrix_eq_zero hj0]
        · exact HS.three_E_one HT hij h h' hqi l hli hlj hi1 hj0
        · exact HS.three_E_two HT hij h h' hqi l hli hlj hi2 hj0
        · exact (HT.three_E_one HS hij.symm h' h hqj l hlj hli hj1 hi0).symm
        · exact (HT.three_E_two HS hij.symm h' h hqj l hlj hli hj2 hi0).symm
  · by_cases hli : l = i
    · subst l
      exact HS.three_Fi HT hij h h' hqi
    · by_cases hlj : l = j
      · subst l
        exact (HT.three_Fi HS hij.symm h' h hqj).symm
      · rcases hout l hli hlj with ⟨hi0, hj0⟩ | ⟨hi1 | hi2, hj0⟩ | ⟨hi0, hj1 | hj2⟩
        · simp [HS.map_F, HT.map_F, hli, hlj,
            braidFj_eq_of_cartanMatrix_eq_zero hi0, braidFj_eq_of_cartanMatrix_eq_zero hj0]
        · exact HS.three_F_one HT hij h h' hqi l hli hlj hi1 hj0
        · exact HS.three_F_two HT hij h h' hqi l hli hlj hi2 hj0
        · exact (HT.three_F_one HS hij.symm h' h hqj l hlj hli hj1 hi0).symm
        · exact (HT.three_F_two HS hij.symm h' h hqj l hlj hli hj2 hi0).symm
  · simp only [AlgHom.comp_apply, HS.map_K, HT.map_K,
      reflY_braid_of_simply_laced_edge h h']

omit HS HT hij h h' hqi in
/-- Automorphism-group version of the constructor-independent length-three theorem. -/
theorem HasBraidGeneratorImages.three_equiv
    {A B : QuantumGroup R v ≃ₐ[k] QuantumGroup R v}
    (HA : HasBraidGeneratorImages i A.toAlgHom) (HB : HasBraidGeneratorImages j B.toAlgHom)
    (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hout : ∀ l, l ≠ i → l ≠ j →
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
      ((D.cartanMatrix i l = -1 ∨ D.cartanMatrix i l = -2) ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = 0 ∧ (D.cartanMatrix j l = -1 ∨ D.cartanMatrix j l = -2))) :
    A * B * A = B * A * B := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (HA.three_braid HB hij h h' hq hout) x

omit HS HT hij h h' hqi

/-- Precisely the graph and scalar contract of the published next-edge constructor. -/
structure ThreeNextData (D : LusztigCartanDatum I) (v : k) (i : I) : Prop where
  edge : ∀ j, j ≠ i → D.cartanMatrix i j = 0 ∨
    (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1)
  leaf : ∀ j l, D.cartanMatrix i j = -1 → D.cartanMatrix i l = -1 →
    j ≠ l → D.cartanMatrix j l = 0
  path : ∀ j l, D.cartanMatrix i j = -1 → D.cartanMatrix i l = 0 →
    D.cartanMatrix j l = 0 ∨ D.cartanMatrix j l = -1 ∨ D.cartanMatrix j l = -2
  diff : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0
  sum : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0
  cube : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0

/-- A node admitting one of the two actual published local constructions.
This is purely graph/scalar data, not assumed transformed relations or map existence. -/
def ThreeLocalData (D : LusztigCartanDatum I) (v : k) (i : I) : Prop :=
  ThreeNextData D v i ∨ HigherDoubleData D v i

/-- Actual automorphism at any node in the union of the two supported local classes. -/
def threeLocalEquiv (i : I) (H : ThreeLocalData D v i) :
    QuantumGroup R v ≃ₐ[k] QuantumGroup R v := by
  classical
  exact if hn : ThreeNextData D v i then
    nextEdgeBraidEquiv i hn.edge hn.leaf hn.path hn.diff hn.sum hn.cube
  else
    let hd := H.resolve_left hn
    nonterminalDoubleBraidEquiv i hd.edge hd.leaf hd.unique hd.path
      hd.diff hd.sum hd.cycl hd.cube

/-- Both branches have the same Lusztig formulas on all generators. -/
theorem threeLocalEquiv_images (i : I) (H : ThreeLocalData D v i) :
    HasBraidGeneratorImages i (threeLocalEquiv (R := R) i H).toAlgHom := by
  classical
  unfold threeLocalEquiv
  split_ifs with hn
  · exact nextEdgeBraid_hasBraidGeneratorImages i hn.edge hn.leaf hn.path
      hn.diff hn.sum hn.cube
  · exact nonterminalDoubleBraid_hasBraidGeneratorImages i (H.resolve_left hn)

omit [DecidableEq I] [NeZero v] in
/-- The local union retains the required centre quantum difference. -/
theorem ThreeLocalData.diff {i : I} (H : ThreeLocalData D v i) :
    v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0 :=
  H.elim ThreeNextData.diff HigherDoubleData.diff

omit [DecidableEq I] [NeZero v] in
/-- The local union bounds each outgoing external degree by two. -/
theorem ThreeLocalData.bound {i : I} (H : ThreeLocalData D v i) (l : I) (hli : l ≠ i) :
    D.cartanMatrix i l = 0 ∨ D.cartanMatrix i l = -1 ∨ D.cartanMatrix i l = -2 := by
  rcases H with H | H
  · rcases H.edge l hli with h0 | ⟨h1, _⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
  · rcases H.edge l hli with h0 | ⟨h1, _⟩ | ⟨h2, _⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)

omit [DecidableEq I] [NeZero v] in
/-- Distinct neighbours in the local union remain orthogonal. -/
theorem ThreeLocalData.leaf {i : I} (H : ThreeLocalData D v i)
    (j l : I) (hji : j ≠ i) (hli : l ≠ i)
    (hj : D.cartanMatrix i j ≠ 0) (hl : D.cartanMatrix i l ≠ 0) (hjl : j ≠ l) :
    D.cartanMatrix j l = 0 := by
  rcases H with H | H
  · rcases H.edge j hji with h0 | ⟨h1, _⟩
    · exact (hj h0).elim
    · rcases H.edge l hli with h0 | ⟨h2, _⟩
      · exact (hl h0).elim
      · exact H.leaf j l h1 h2 hjl
  · exact H.leaf j l hji hli hj hl hjl

omit [DecidableEq I] [NeZero v] in
/-- Complete external-node classification derived from the actual local graph data. -/
theorem ThreeLocalData.outer {i j : I} (Hi : ThreeLocalData D v i)
    (Hj : ThreeLocalData D v j) (hij : i ≠ j) (h : D.cartanMatrix i j = -1)
    (l : I) (hli : l ≠ i) (hlj : l ≠ j) :
    (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
    ((D.cartanMatrix i l = -1 ∨ D.cartanMatrix i l = -2) ∧ D.cartanMatrix j l = 0) ∨
    (D.cartanMatrix i l = 0 ∧ (D.cartanMatrix j l = -1 ∨ D.cartanMatrix j l = -2)) := by
  rcases Hi.bound l hli with hi0 | hi1 | hi2
  · rcases Hj.bound l hlj with hj0 | hj1 | hj2
    · exact Or.inl ⟨hi0, hj0⟩
    · exact Or.inr (Or.inr ⟨hi0, Or.inl hj1⟩)
    · exact Or.inr (Or.inr ⟨hi0, Or.inr hj2⟩)
  · exact Or.inr (Or.inl ⟨Or.inl hi1,
      Hi.leaf j l hij.symm hli (by simp [h]) (by simp [hi1]) hlj.symm⟩)
  · exact Or.inr (Or.inl ⟨Or.inr hi2,
      Hi.leaf j l hij.symm hli (by simp [h]) (by simp [hi2]) hlj.symm⟩)

/-- Genuine length-three relation for the assembled actual local automorphisms,
including NextEdge/NonterminalDouble mixed pairs and degree-two external neighbours. -/
theorem threeLocalEquiv_braid (i j : I) (Hi : ThreeLocalData D v i)
    (Hj : ThreeLocalData D v j) (hij : i ≠ j)
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1) :
    threeLocalEquiv (R := R) i Hi * threeLocalEquiv j Hj * threeLocalEquiv i Hi =
      threeLocalEquiv j Hj * threeLocalEquiv i Hi * threeLocalEquiv j Hj :=
  (threeLocalEquiv_images i Hi).three_equiv (threeLocalEquiv_images j Hj)
    hij h h' Hi.diff (Hi.outer Hj hij h)

/-- Direct mixed-constructor consumer: actual next-edge and nonterminal-double
quotient maps satisfy length three at a mutual simple pair, on the entire algebra. -/
theorem nextEdge_nonterminalDouble_three (i j : I)
    (HN : ThreeNextData D v i) (HD : HigherDoubleData D v j)
    (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1) :
    let A := nextEdgeBraid (R := R) i HN.edge HN.leaf HN.path HN.diff HN.sum HN.cube
    let B := nonterminalDoubleBraid j HD.edge HD.leaf HD.unique HD.path
      HD.diff HD.sum HD.cycl HD.cube
    A.comp (B.comp A) = B.comp (A.comp B) := by
  exact (nextEdgeBraid_hasBraidGeneratorImages i HN.edge HN.leaf HN.path
    HN.diff HN.sum HN.cube).three_braid (nonterminalDoubleBraid_hasBraidGeneratorImages j HD)
      hij h h' HN.diff
      ((show ThreeLocalData D v i from Or.inl HN).outer (Or.inr HD) hij h)

/-- Compatibility with the original next-edge automorphism, on the nose. -/
theorem threeLocalEquiv_eq_nextEdge (i : I) (H : ThreeLocalData D v i)
    (HN : ThreeNextData D v i) :
    threeLocalEquiv (R := R) i H =
      nextEdgeBraidEquiv i HN.edge HN.leaf HN.path HN.diff HN.sum HN.cube := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun ((threeLocalEquiv_images i H).unique
    (nextEdgeBraid_hasBraidGeneratorImages i HN.edge HN.leaf HN.path
      HN.diff HN.sum HN.cube)) x

/-- Compatibility with the original nonterminal-double automorphism, on the nose. -/
theorem threeLocalEquiv_eq_nonterminalDouble (i : I) (H : ThreeLocalData D v i)
    (HD : HigherDoubleData D v i) :
    threeLocalEquiv (R := R) i H =
      nonterminalDoubleBraidEquiv i HD.edge HD.leaf HD.unique HD.path
        HD.diff HD.sum HD.cycl HD.cube := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun ((threeLocalEquiv_images i H).unique
    (nonterminalDoubleBraid_hasBraidGeneratorImages i HD)) x

/-- Length two for the assembled actual maps, including both constructor branches. -/
theorem threeLocalEquiv_comm (i j : I) (Hi : ThreeLocalData D v i)
    (Hj : ThreeLocalData D v j) (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) :
    threeLocalEquiv (R := R) i Hi * threeLocalEquiv j Hj =
      threeLocalEquiv j Hj * threeLocalEquiv i Hi :=
  (threeLocalEquiv_images i Hi).equiv_comm (threeLocalEquiv_images j Hj) hij h0

omit [DecidableEq I] [NeZero v] in
/-- A node incident to a genuine double edge must use the higher-double local class. -/
theorem ThreeLocalData.higher_of_double {i j : I} (H : ThreeLocalData D v i)
    (hij : i ≠ j) (hn : D.cartanMatrix i j ≠ 0)
    (hd : ¬ (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1)) :
    HigherDoubleData D v i := by
  rcases H with H | H
  · rcases H.edge j hij.symm with h0 | h1
    · exact (hn h0).elim
    · exact (hd h1).elim
  · exact H

/-- Length four for the same assembled maps, using the proved higher-rank theorem. -/
theorem threeLocalEquiv_four (i j : I) (Hi : ThreeLocalData D v i)
    (Hj : ThreeLocalData D v j) (hij : i ≠ j)
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1) :
    threeLocalEquiv (R := R) i Hi * threeLocalEquiv j Hj *
        threeLocalEquiv i Hi * threeLocalEquiv j Hj =
      threeLocalEquiv j Hj * threeLocalEquiv i Hi *
        threeLocalEquiv j Hj * threeLocalEquiv i Hi := by
  have HDi := Hi.higher_of_double hij (by simp [h]) (by simp [h])
  have HDj := Hj.higher_of_double hij.symm (by simp [h']) (by simp [h])
  rw [threeLocalEquiv_eq_nonterminalDouble i Hi HDi,
    threeLocalEquiv_eq_nonterminalDouble j Hj HDj]
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (higherDoubleBraid_braid i j HDi HDj hij h h') x

end QuantumGroup

namespace LusztigCartanDatum
variable {I : Type*} (D : LusztigCartanDatum I)

/-- The length-two/three/four Artin relators for simple and double edges.
Length three requires BOTH directed entries to be -1. A directed -1 side of a double
edge does not introduce a spurious length-three relator. No involutions are imposed. -/
def simpleDoubleArtinRelators : Set (FreeGroup I) :=
  {r | ∃ i j, i ≠ j ∧
    ((D.cartanMatrix i j = 0 ∧
      r = (FreeGroup.of i * FreeGroup.of j) * (FreeGroup.of j * FreeGroup.of i)⁻¹) ∨
     ((D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1) ∧
      r = (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i) *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) ∨
     ((D.cartanMatrix i j = -2 ∧ D.cartanMatrix j i = -1) ∧
      r = (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i * FreeGroup.of j) *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j * FreeGroup.of i)⁻¹))}
end LusztigCartanDatum

/-- The simple/double Artin presentation, with no triple-edge or involution relators. -/
abbrev SimpleDoubleArtinGroup {I : Type*} (D : LusztigCartanDatum I) :=
  PresentedGroup D.simpleDoubleArtinRelators

namespace SimpleDoubleArtinGroup
variable {I : Type*} {D : LusztigCartanDatum I}

/-- The Artin generator at a node. -/
def generator (i : I) : SimpleDoubleArtinGroup D := PresentedGroup.of i

/-- The defining orthogonal-node relation. -/
theorem generator_comm {i j : I} (hij : i ≠ j) (h : D.cartanMatrix i j = 0) :
    generator (D := D) i * generator j = generator j * generator i :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨i, j, hij, Or.inl ⟨h, rfl⟩⟩

/-- Only mutual simple edges give a length-three relation. -/
theorem generator_braid {i j : I} (hij : i ≠ j)
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1) :
    generator (D := D) i * generator j * generator i =
      generator j * generator i * generator j :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨i, j, hij, Or.inr (Or.inl ⟨⟨h, h'⟩, rfl⟩)⟩

/-- The defining double-edge relation; swapping the two nodes gives its reverse. -/
theorem generator_four {i j : I} (hij : i ≠ j)
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1) :
    generator (D := D) i * generator j * generator i * generator j =
      generator j * generator i * generator j * generator i :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨i, j, hij, Or.inr (Or.inr ⟨⟨h, h'⟩, rfl⟩)⟩

variable {G : Type*} [Group G] (f : I → G)
  (h2 : ∀ i j, i ≠ j → D.cartanMatrix i j = 0 → f i * f j = f j * f i)
  (h3 : ∀ i j, i ≠ j → D.cartanMatrix i j = -1 → D.cartanMatrix j i = -1 →
    f i * f j * f i = f j * f i * f j)
  (h4 : ∀ i j, i ≠ j → D.cartanMatrix i j = -2 → D.cartanMatrix j i = -1 →
    f i * f j * f i * f j = f j * f i * f j * f i)

/-- Universal lift for the correctly scoped simple/double Artin relations. -/
def lift : SimpleDoubleArtinGroup D →* G :=
  PresentedGroup.toGroup (f := f) (by
    rintro r ⟨i, j, hij, ⟨h0, rfl⟩ | ⟨⟨h1, h1'⟩, rfl⟩ | ⟨⟨h2', h1'⟩, rfl⟩⟩
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [h2 i j hij h0, mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [h3 i j hij h1 h1', mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [h4 i j hij h2' h1', mul_inv_cancel])

@[simp] theorem lift_generator (i : I) : lift f h2 h3 h4 (generator i) = f i :=
  PresentedGroup.toGroup.of _

/-- The lift is determined by its generator images. -/
theorem lift_unique (g : SimpleDoubleArtinGroup D →* G)
    (hg : ∀ i, g (generator i) = f i) : g = lift f h2 h3 h4 := by
  apply PresentedGroup.ext
  intro i
  exact (hg i).trans (lift_generator f h2 h3 h4 i).symm
end SimpleDoubleArtinGroup

namespace QuantumGroup
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  (H : ∀ i, ThreeLocalData D v i)

/-- Genuine all-node Artin representation on the union of the proved local classes.
Every map is constructed from graph/scalar data; every length-two/three/four relation
is proved. This is not a claim for arbitrary symmetrizable Cartan diagrams. -/
def threeLocalArtinHom : SimpleDoubleArtinGroup D →*
    (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  SimpleDoubleArtinGroup.lift (fun i ↦ threeLocalEquiv i (H i))
    (fun i j ↦ threeLocalEquiv_comm i j (H i) (H j))
    (fun i j ↦ threeLocalEquiv_braid i j (H i) (H j))
    (fun i j ↦ threeLocalEquiv_four i j (H i) (H j))

@[simp] theorem threeLocalArtinHom_generator (i : I) :
    threeLocalArtinHom (R := R) H (SimpleDoubleArtinGroup.generator i) =
      threeLocalEquiv i (H i) := SimpleDoubleArtinGroup.lift_generator _ _ _ _ i

/-- All generator formulas, including the arbitrary torus lattice, hold in the action. -/
theorem threeLocalArtinHom_images (i : I) :
    HasBraidGeneratorImages i
      (threeLocalArtinHom (R := R) H (SimpleDoubleArtinGroup.generator i)).toAlgHom := by
  rw [threeLocalArtinHom_generator]
  exact threeLocalEquiv_images i (H i)

/-- Evaluation of the actual automorphism representation defines the Artin action. -/
abbrev threeLocalArtinAction : MulSemiringAction (SimpleDoubleArtinGroup D)
    (QuantumGroup R v) :=
  MulSemiringAction.compHom (QuantumGroup R v) (threeLocalArtinHom (R := R) H)

/-- Every lattice element has the required reflected image under an Artin generator. -/
@[simp] theorem threeLocalArtinHom_K (i : I) (μ : Y) :
    threeLocalArtinHom H (SimpleDoubleArtinGroup.generator i) (K R v μ) =
      K R v (reflY R i μ) := (threeLocalArtinHom_images H i).map_K μ

/-- The positive Chevalley generators have the literal Lusztig images. -/
@[simp] theorem threeLocalArtinHom_E (i l : I) :
    threeLocalArtinHom H (SimpleDoubleArtinGroup.generator i) (E R v l) =
      if l = i then braidEi R i else braidEj R v i l :=
  (threeLocalArtinHom_images H i).map_E l

/-- The negative Chevalley generators have the literal Lusztig images. -/
@[simp] theorem threeLocalArtinHom_F (i l : I) :
    threeLocalArtinHom H (SimpleDoubleArtinGroup.generator i) (F R v l) =
      if l = i then braidFi R i else braidFj R v i l :=
  (threeLocalArtinHom_images H i).map_F l

/-- The constructed representation is uniquely specified by its actual generator maps. -/
theorem threeLocalArtinHom_unique
    (g : SimpleDoubleArtinGroup D →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v))
    (hg : ∀ i, g (SimpleDoubleArtinGroup.generator i) = threeLocalEquiv i (H i)) :
    g = threeLocalArtinHom H := SimpleDoubleArtinGroup.lift_unique _ _ _ _ g hg

end QuantumGroup
