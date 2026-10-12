/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PositiveComul
import LieLean.Algebra.QuantumGroup.TensorModule

/-!
# Finite rank-one intertwining

Exact finite boundaries and eventual intertwining on two Chevalley-twisted Verma factors.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

open LieLean TensorProduct
open scoped TensorProduct
noncomputable section
namespace FiniteIntertwining
open LieLean.QuantumGroup
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- Coefficient of ordinary powers in the positive rank-one factor. -/
def coeff (q : k) : ℕ → k
  | 0 => 1
  | n + 1 => coeff q n * (q - q⁻¹) * q ^ n / qInt q (n + 1)

/-- All string terms up to and including `N`; no boundary is discarded. -/
def partialSum (i : I) (N : ℕ) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  ∑ n ∈ Finset.range (N + 1), coeff (v ^ D.d i) n •
    ((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n))

lemma km_F_pow (i : I) (n : ℕ) :
    K R v (-ktilde R i) * F R v i ^ n =
      (v ^ D.d i) ^ (2 * n) • (F R v i ^ n * K R v (-ktilde R i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc,
      K_neg_ktilde_mul_F, mul_smul_comm, ← mul_assoc, ← pow_succ,
      smul_smul, ← pow_add]
    congr 2

/-- Exact rank-one tensor commutator, before summing coefficients. -/
lemma E_term (hv : v ≠ 0) (i : I) (n : ℕ) :
    (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + K R v (-ktilde R i) ⊗ₜ[k] E R v i) *
        ((F R v i ^ (n + 1)) ⊗ₜ[k] (E R v i ^ (n + 1))) -
      ((F R v i ^ (n + 1)) ⊗ₜ[k] (E R v i ^ (n + 1))) *
        (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i) =
      (qInt (v ^ D.d i) (n + 1) * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹) •
        ((F R v i ^ n * ((v ^ D.d i)⁻¹ ^ n • Kt R v i -
          (v ^ D.d i) ^ n • K R v (-ktilde R i))) ⊗ₜ[k] (E R v i ^ (n + 1))) +
      ((F R v i ^ (n + 1) * ((v ^ D.d i) ^ (2*(n + 1)) • K R v (-ktilde R i) -
          Kt R v i)) ⊗ₜ[k] (E R v i ^ (n + 1+1))) := by
  simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [← pow_succ', ← pow_succ, km_F_pow]
  have h := congrArg (fun z : QuantumGroup R v ↦ z ⊗ₜ[k] (E R v i ^ (n + 1)))
    (E_mul_F_pow_sub (R := R) hv i n)
  simp only [mul_sub, mul_smul_comm, sub_tmul, ← smul_tmul', smul_sub, smul_smul] at h ⊢
  rw [show 2 * (n + 1) = 2 * n+2 by omega, ← h]
  abel

lemma coeff_cancel {q : k} (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
    (n : ℕ) (hn : qInt q (n + 1) ≠ 0) :
    coeff q (n + 1) * (qInt q (n + 1) * (q - q⁻¹)⁻¹) * q⁻¹ ^ n = coeff q n := by
  simp only [coeff, div_eq_mul_inv]
  calc
    _ = coeff q n * ((q - q⁻¹)*(q - q⁻¹)⁻¹) *
        (qInt q (n + 1) * (qInt q (n + 1))⁻¹) * (q^n * q⁻¹^n) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hd, mul_inv_cancel₀ hn, ← mul_pow,
                    mul_inv_cancel₀ hq]; simp

lemma coeff_cancel' {q : k} (hd : q - q⁻¹ ≠ 0)
    (n : ℕ) (hn : qInt q (n + 1) ≠ 0) :
    coeff q (n + 1) * (qInt q (n + 1) * (q - q⁻¹)⁻¹) * q ^ n =
      coeff q n * q ^ (2 * n) := by
  simp only [coeff, div_eq_mul_inv]
  calc
    _ = coeff q n * ((q - q⁻¹)*(q - q⁻¹)⁻¹) *
        (qInt q (n + 1) * (qInt q (n + 1))⁻¹) * q^(2 * n) := by rw [two_mul, pow_add]; ring
    _ = _ := by rw [mul_inv_cancel₀ hd, mul_inv_cancel₀ hn]; simp

def boundaryE (i : I) (n : ℕ) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  (F R v i ^ n * ((v ^ D.d i) ^ (2 * n) • K R v (-ktilde R i) - Kt R v i))
    ⊗ₜ[k] (E R v i ^ (n + 1))

lemma coeff_E_term (hv : v ≠ 0) (i : I)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (n : ℕ) (hn : qInt (v ^ D.d i) (n + 1) ≠ 0) :
    (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + K R v (-ktilde R i) ⊗ₜ[k] E R v i) *
        (coeff (v ^ D.d i) (n + 1) • ((F R v i ^ (n + 1)) ⊗ₜ[k] (E R v i ^ (n + 1)))) -
      (coeff (v ^ D.d i) (n + 1) • ((F R v i ^ (n + 1)) ⊗ₜ[k] (E R v i ^ (n + 1)))) *
        (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i) =
      coeff (v ^ D.d i) (n + 1) • boundaryE R v i (n + 1) -
        coeff (v ^ D.d i) n • boundaryE R v i n := by
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, E_term R v hv]
  simp only [boundaryE, smul_add, mul_sub, mul_smul_comm, sub_tmul, ← smul_tmul',
    smul_sub, smul_smul]
  have h1 := coeff_cancel (pow_ne_zero _ hv) hd n hn
  have h2 := coeff_cancel' hd n hn
  simp only [mul_assoc] at h1 h2 ⊢
  rw [h1, h2]
  abel

/-- The exact boundary of the finite E intertwiner, without discarding the top term. -/
theorem partialSum_E (hv : v ≠ 0) (i : I)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hn : ∀ n, qInt (v ^ D.d i) (n + 1) ≠ 0) (N : ℕ) :
    (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + K R v (-ktilde R i) ⊗ₜ[k] E R v i) *
        partialSum R v i N -
      partialSum R v i N *
        (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i) =
      coeff (v ^ D.d i) N • boundaryE R v i N := by
  induction N with
  | zero =>
    simp [partialSum, coeff, boundaryE, sub_tmul, ← Algebra.TensorProduct.one_def,
      add_sub_add_left_eq_sub]
  | succ N ih =>
    have hs : partialSum R v i (N + 1) = partialSum R v i N +
        coeff (v ^ D.d i) (N + 1) • ((F R v i ^ (N + 1)) ⊗ₜ[k] (E R v i ^ (N + 1))) := by
      exact Finset.sum_range_succ _ _
    rw [hs, mul_add, add_mul (partialSum R v i N)]
    have ht := coeff_E_term R v hv i hd N (hn N)
    rw [sub_eq_iff_eq_add] at ih ht
    rw [ih, ht]
    abel

def flipChevalley : QuantumGroup R v ⊗[k] QuantumGroup R v →ₐ[k]
    QuantumGroup R v ⊗[k] QuantumGroup R v :=
  (Algebra.TensorProduct.comm k (QuantumGroup R v) (QuantumGroup R v)).toAlgHom.comp
    (Algebra.TensorProduct.map (chevalley R v) (chevalley R v))

lemma flipChevalley_tmul (a b : QuantumGroup R v) :
    flipChevalley R v (a ⊗ₜ[k] b) = chevalley R v b ⊗ₜ[k] chevalley R v a := by
  simp [flipChevalley]

lemma flipChevalley_partialSum (i : I) (N : ℕ) :
    flipChevalley R v (partialSum R v i N) = partialSum R v i N := by
  simp [partialSum, flipChevalley_tmul]

/-- Exact F boundary, obtained from E by the actual Chevalley involution and flip. -/
theorem partialSum_F (hv : v ≠ 0) (i : I)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hn : ∀ n, qInt (v ^ D.d i) (n + 1) ≠ 0) (N : ℕ) :
    (F R v i ⊗ₜ[k] Kt R v i + (1 : QuantumGroup R v) ⊗ₜ[k] F R v i) *
        partialSum R v i N -
      partialSum R v i N *
        (F R v i ⊗ₜ[k] K R v (-ktilde R i) + (1 : QuantumGroup R v) ⊗ₜ[k] F R v i) =
      coeff (v ^ D.d i) N • ((F R v i ^ (N + 1)) ⊗ₜ[k]
        (E R v i ^ N * ((v ^ D.d i) ^ (2 * N) • Kt R v i - K R v (-ktilde R i)))) := by
  have h := congrArg (flipChevalley R v) (partialSum_E R v hv i hd hn N)
  simpa [map_sub, map_mul, map_add, flipChevalley_partialSum, flipChevalley_tmul,
    boundaryE, Kt, add_comm] using h

/-- Every toral generator commutes with each finite rank-one partial sum. -/
theorem partialSum_K (hv : v ≠ 0) (i : I) (μ : Y) (N : ℕ) :
    (K R v μ ⊗ₜ[k] K R v μ) * partialSum R v i N =
      partialSum R v i N * (K R v μ ⊗ₜ[k] K R v μ) := by
  have h : Commute (K R v μ ⊗ₜ[k] K R v μ) (F R v i ⊗ₜ[k] E R v i) := by
    change _ * _ = _ * _
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      K_mul_F, K_mul_E, ← smul_tmul', ← tmul_smul, smul_smul,
      ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]
  unfold partialSum
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_smul_comm, smul_mul_assoc]
  exact congrArg (coeff (v ^ D.d i) n • ·)
    (by simpa only [Algebra.TensorProduct.tmul_pow] using (h.pow_right n).eq)

/-- The source's curly factorial, written as a finite product. -/
def curly (q : k) (n : ℕ) : k :=
  ∏ a ∈ Finset.range n, (q ^ (a + 1) - q⁻¹ ^ (a + 1))

lemma curly_eq (q : k) (n : ℕ) : curly q n = qFactorial q n * (q - q⁻¹) ^ n := by
  induction n with
  | zero => simp [curly]
  | succ n ih =>
    rw [curly, Finset.prod_range_succ, ← curly, ih, qFactorial_succ,
      ← qInt_mul_sub, pow_succ]
    ring

lemma coeff_closed (q : k) (n : ℕ) :
    coeff q n = q ^ (∑ a ∈ Finset.range n, a) * (q - q⁻¹) ^ n / qFactorial q n := by
  induction n with
  | zero => simp [coeff]
  | succ n ih =>
    rw [coeff, ih, Finset.sum_range_succ, pow_add, pow_succ, qFactorial_succ]
    simp only [div_eq_mul_inv, mul_inv]
    ring

lemma coeff_curly (q : k) (n : ℕ) (hn : qFactorial q n ≠ 0) :
    coeff q n = q ^ (∑ a ∈ Finset.range n, a) * curly q n * (qFactorial q n)⁻¹ ^ 2 := by
  rw [coeff_closed, curly_eq]
  field_simp

lemma term_divided (i : I) (n : ℕ) (hn : qFactorial (v ^ D.d i) n ≠ 0) :
    coeff (v ^ D.d i) n • ((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n)) =
      ((v ^ D.d i) ^ (∑ a ∈ Finset.range n, a) * curly (v ^ D.d i) n) •
        (qDivPow (v ^ D.d i) n (F R v i) ⊗ₜ[k] qDivPow (v ^ D.d i) n (E R v i)) := by
  rw [coeff_curly _ _ hn]
  simp only [qDivPow, ← smul_tmul', ← tmul_smul, smul_smul, pow_two, mul_assoc]

section Braid
variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- The existing full coproduct conjugated by the existing braid equivalence. -/
def braidDelta (i : I) : QuantumGroup R v →ₐ[k] QuantumGroup R v ⊗[k] QuantumGroup R v :=
  (Algebra.TensorProduct.congr (braidEquivOfNotRoot R hv i)
    (braidEquivOfNotRoot R hv i)).symm.toAlgHom.comp
      ((comul R v).comp (braidEquivOfNotRoot R hv i).toAlgHom)

lemma braidDelta_E (i : I) :
    braidDelta R v hv i (E R v i) =
      E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + K R v (-ktilde R i) ⊗ₜ[k] E R v i := by
  let T := braidEquivOfNotRoot R hv i
  have hT := braidEquivOfNotRoot_hasImages hv R i
  apply (Algebra.TensorProduct.congr T T).injective
  change (Algebra.TensorProduct.congr T T)
    ((Algebra.TensorProduct.congr T T).symm ((comul R v) (T (E R v i)))) = _
  rw [AlgEquiv.apply_symm_apply]
  have hE : T (E R v i) = braidEi R i := by simpa using hT.map_E i
  have hK : ∀ μ, T (K R v μ) = K R v (reflY R i μ) := hT.map_K
  simp [Algebra.TensorProduct.congr_apply, hE, hK, braidEi, Kt,
    add_mul, Algebra.TensorProduct.tmul_mul_tmul, tmul_neg, neg_tmul, K_neg_mul_K, add_comm]

lemma braidDelta_F (i : I) :
    braidDelta R v hv i (F R v i) =
      F R v i ⊗ₜ[k] Kt R v i + (1 : QuantumGroup R v) ⊗ₜ[k] F R v i := by
  let T := braidEquivOfNotRoot R hv i
  have hT := braidEquivOfNotRoot_hasImages hv R i
  apply (Algebra.TensorProduct.congr T T).injective
  change (Algebra.TensorProduct.congr T T)
    ((Algebra.TensorProduct.congr T T).symm ((comul R v) (T (F R v i)))) = _
  rw [AlgEquiv.apply_symm_apply]
  have hF : T (F R v i) = braidFi R i := by simpa using hT.map_F i
  have hK : ∀ μ, T (K R v μ) = K R v (reflY R i μ) := hT.map_K
  simp [Algebra.TensorProduct.congr_apply, hF, hK, braidFi, Kt,
    mul_add, Algebra.TensorProduct.tmul_mul_tmul, tmul_neg, neg_tmul, K_neg_mul_K, add_comm]

lemma braidDelta_K (i : I) (μ : Y) :
    braidDelta R v hv i (K R v μ) = K R v μ ⊗ₜ[k] K R v μ := by
  let T := braidEquivOfNotRoot R hv i
  have hT := braidEquivOfNotRoot_hasImages hv R i
  apply (Algebra.TensorProduct.congr T T).injective
  change (Algebra.TensorProduct.congr T T)
    ((Algebra.TensorProduct.congr T T).symm ((comul R v) (T (K R v μ)))) = _
  rw [AlgEquiv.apply_symm_apply]
  have hK : ∀ μ, T (K R v μ) = K R v (reflY R i μ) := hT.map_K
  simp [Algebra.TensorProduct.congr_apply, hK]
include hv in
/-- Every term agrees with the source's divided-power normalization. -/
theorem partialSum_source (i : I) (N : ℕ) :
    partialSum R v i N = ∑ n ∈ Finset.range (N + 1),
      ((v ^ D.d i) ^ (n * (n - 1) / 2) * curly (v ^ D.d i) n) •
        (qDivPow (v ^ D.d i) n (F R v i) ⊗ₜ[k] qDivPow (v ^ D.d i) n (E R v i)) := by
  apply Finset.sum_congr rfl
  intro n _
  simpa only [Finset.sum_range_id] using
    term_divided R v i n (LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv i n)

/-- Actual E-braid/coproduct identity with its exact finite boundary retained. -/
theorem intertwine_E (i : I) (N : ℕ) :
    braidDelta R v hv i (E R v i) * partialSum R v i N -
      partialSum R v i N * comul R v (E R v i) =
      coeff (v ^ D.d i) N • boundaryE R v i N := by
  rw [braidDelta_E, comul_E]
  exact partialSum_E R v (NeZero.ne v) i
    (shortNode_braidGeneric_of_not_root hv i).sub_ne
    (fun n ↦ qInt_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne v))
      (vd_pow_ne_one hv i) (Nat.succ_pos n)) N

/-- Actual F-braid/coproduct identity with its exact finite boundary retained. -/
theorem intertwine_F (i : I) (N : ℕ) :
    braidDelta R v hv i (F R v i) * partialSum R v i N -
      partialSum R v i N * comul R v (F R v i) =
      coeff (v ^ D.d i) N • ((F R v i ^ (N + 1)) ⊗ₜ[k]
        (E R v i ^ N * ((v ^ D.d i) ^ (2 * N) • Kt R v i - K R v (-ktilde R i)))) := by
  rw [braidDelta_F, comul_F]
  exact partialSum_F R v (NeZero.ne v) i
    (shortNode_braidGeneric_of_not_root hv i).sub_ne
    (fun n ↦ qInt_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne v))
      (vd_pow_ne_one hv i) (Nat.succ_pos n)) N

/-- The toral part of actual braid intertwining holds for every cutoff. -/
theorem intertwine_K (i : I) (μ : Y) (N : ℕ) :
    braidDelta R v hv i (K R v μ) * partialSum R v i N =
      partialSum R v i N * comul R v (K R v μ) := by
  rw [braidDelta_K, comul_K]
  exact partialSum_K R v (NeZero.ne v) i μ N
end Braid

section LowestVerma
variable [NeZero v] (Λ₁ Λ₂ : Y →+ ℤ)

/-- Genuine tensor action on two Chevalley-twisted Verma modules. -/
def lowestPair : QuantumGroup R v ⊗[k] QuantumGroup R v →ₐ[k]
    Module.End k (VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :=
  (TensorModule.actPair R v (VermaModule R v Λ₁) (VermaModule R v Λ₂)).comp
    (Algebra.TensorProduct.map (chevalley R v) (chevalley R v))

omit [NeZero v] in
lemma lowestPair_tmul (a b : QuantumGroup R v)
    (x : VermaModule R v Λ₁) (y : VermaModule R v Λ₂) :
    lowestPair R v Λ₁ Λ₂ (a ⊗ₜ[k] b) (x ⊗ₜ[k] y) =
      (chevalley R v a • x) ⊗ₜ[k] (chevalley R v b • y) := by
  simp [lowestPair, TensorModule.act_tmul]

/-- An explicit first-leg lowering bound kills every later rank-one coefficient. -/
lemma lowestPair_term_zero_of_lowerSpan (i : I) (N n : ℕ)
    {x : VermaModule R v Λ₁} (hx : x ∈ VermaModule.lowerSpan R v Λ₁ i N)
    (y : VermaModule R v Λ₂) (hn : N ≤ n) :
    lowestPair R v Λ₁ Λ₂ ((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n)) (x ⊗ₜ[k] y) = 0 := by
  rw [lowestPair_tmul]
  simp only [map_pow, chevalley_F, chevalley_E]
  have he : E R v i ^ n • x = 0 := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm N r, pow_add, mul_smul,
      VermaModule.E_pow_smul_eq_zero_of_mem_lowerSpan i N hx, smul_zero]
  rw [he, zero_tmul]

/-- Local finiteness is derived from the actual Verma module, not postulated. -/
theorem lowestPair_eventually_zero (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      lowestPair R v Λ₁ Λ₂ ((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n)) z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨N, hN⟩ := VermaModule.exists_E_pow_smul_eq_zero (R := R) (v := v) i x
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [lowestPair_tmul]
    simp only [map_pow, chevalley_F, chevalley_E]
    have he : E R v i ^ n • x = 0 := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [add_comm N r, pow_add, mul_smul, hN, smul_zero]
    rw [he, zero_tmul]
  | add z w hz hw =>
    obtain ⟨N, hN⟩ := hz
    obtain ⟨M, hM⟩ := hw
    exact ⟨max N M, fun n hn ↦ by
      rw [map_add, hN n (le_trans (le_max_left N M) hn),
        hM n (le_trans (le_max_right N M) hn), add_zero]⟩
/-- Every tensor vector has a genuine finite cutoff for the positive rank-one series. -/
theorem lowestPair_stabilizes (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ M, N ≤ M →
      lowestPair R v Λ₁ Λ₂ (partialSum R v i M) z =
        lowestPair R v Λ₁ Λ₂ (partialSum R v i N) z := by
  obtain ⟨N, hN⟩ := lowestPair_eventually_zero R v Λ₁ Λ₂ i z
  refine ⟨N, fun M hM ↦ ?_⟩
  simp only [partialSum, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hM 1))
  intro n _ hn
  simp only [Finset.mem_range] at hn
  rw [hN n (by omega), smul_zero]

omit [NeZero v] in
lemma boundaryE_factor (i : I) (n : ℕ) :
    boundaryE R v i n =
      (v ^ D.d i) ^ (2 * n) •
        (((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n)) * (K R v (-ktilde R i) ⊗ₜ[k] E R v i)) -
        ((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n)) * (Kt R v i ⊗ₜ[k] E R v i) := by
  simp only [boundaryE, Algebra.TensorProduct.tmul_mul_tmul, ← pow_succ,
    mul_sub, mul_smul_comm, sub_tmul, ← smul_tmul']

/-- The E boundary vanishes eventually on the actual lowest Verma tensor. -/
theorem lowestPair_boundaryE_eventually (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ n, N ≤ n → lowestPair R v Λ₁ Λ₂ (boundaryE R v i n) z = 0 := by
  obtain ⟨N, hN⟩ := lowestPair_eventually_zero R v Λ₁ Λ₂ i
    (lowestPair R v Λ₁ Λ₂ (K R v (-ktilde R i) ⊗ₜ[k] E R v i) z)
  obtain ⟨M, hM⟩ := lowestPair_eventually_zero R v Λ₁ Λ₂ i
    (lowestPair R v Λ₁ Λ₂ (Kt R v i ⊗ₜ[k] E R v i) z)
  refine ⟨max N M, fun n hn ↦ ?_⟩
  rw [boundaryE_factor]
  simp only [map_sub, map_smul, map_mul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, hN n (le_trans (le_max_left _ _) hn),
    hM n (le_trans (le_max_right _ _) hn), smul_zero, sub_zero]

/-- The F boundary also has a proved finite cutoff on the actual module. -/
theorem lowestPair_boundaryF_eventually (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ n, N ≤ n → lowestPair R v Λ₁ Λ₂
      ((F R v i ^ (n + 1)) ⊗ₜ[k]
        (E R v i ^ n * ((v ^ D.d i) ^ (2 * n) • Kt R v i - K R v (-ktilde R i)))) z = 0 := by
  obtain ⟨N, hN⟩ := lowestPair_eventually_zero R v Λ₁ Λ₂ i
    (lowestPair R v Λ₁ Λ₂ (F R v i ⊗ₜ[k] Kt R v i) z)
  obtain ⟨M, hM⟩ := lowestPair_eventually_zero R v Λ₁ Λ₂ i
    (lowestPair R v Λ₁ Λ₂ (F R v i ⊗ₜ[k] K R v (-ktilde R i)) z)
  refine ⟨max N M, fun n hn ↦ ?_⟩
  have hf : ((F R v i ^ (n + 1)) ⊗ₜ[k]
        (E R v i ^ n * ((v ^ D.d i) ^ (2 * n) • Kt R v i - K R v (-ktilde R i)))) =
      (v ^ D.d i) ^ (2 * n) •
        (((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n)) * (F R v i ⊗ₜ[k] Kt R v i)) -
        ((F R v i ^ n) ⊗ₜ[k] (E R v i ^ n)) * (F R v i ⊗ₜ[k] K R v (-ktilde R i)) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, ← pow_succ,
      mul_sub, mul_smul_comm, tmul_sub, tmul_smul]
  rw [hf]
  simp only [map_sub, map_smul, map_mul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, hN n (le_trans (le_max_left _ _) hn),
    hM n (le_trans (le_max_right _ _) hn), smul_zero, sub_zero]

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- Rank-one E intertwining on arbitrary vectors, with a derived finite cutoff. -/
theorem lowestPair_intertwine_E (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i (E R v i))
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i n) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i n)
        (lowestPair R v Λ₁ Λ₂ (comul R v (E R v i)) z) := by
  obtain ⟨N, hN⟩ := lowestPair_boundaryE_eventually R v Λ₁ Λ₂ i z
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := congrArg (fun a ↦ lowestPair R v Λ₁ Λ₂ a z) (intertwine_E R v hv i n)
  simpa only [map_sub, map_smul, map_mul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, hN n hn, smul_zero, sub_eq_zero] using h

/-- Rank-one F intertwining on arbitrary vectors, with a derived finite cutoff. -/
theorem lowestPair_intertwine_F (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i (F R v i))
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i n) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i n)
        (lowestPair R v Λ₁ Λ₂ (comul R v (F R v i)) z) := by
  obtain ⟨N, hN⟩ := lowestPair_boundaryF_eventually R v Λ₁ Λ₂ i z
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := congrArg (fun a ↦ lowestPair R v Λ₁ Λ₂ a z) (intertwine_F R v hv i n)
  simpa only [map_sub, map_smul, map_mul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, hN n hn, smul_zero, sub_eq_zero] using h
/-- Arbitrarily long positive rank-one products, not only one generator. -/
theorem lowestPair_intertwine_E_pow (i : I) (m : ℕ)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i (E R v i ^ m))
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i n) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i n)
        (lowestPair R v Λ₁ Λ₂ (comul R v (E R v i ^ m)) z) := by
  induction m generalizing z with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨N, hN⟩ := lowestPair_intertwine_E R v Λ₁ Λ₂ hv i z
    obtain ⟨M, hM⟩ := ih (lowestPair R v Λ₁ Λ₂ (comul R v (E R v i)) z)
    refine ⟨max N M, fun n hn ↦ ?_⟩
    simp only [pow_succ, map_mul, Module.End.mul_apply]
    rw [hN n (le_trans (le_max_left _ _) hn), hM n (le_trans (le_max_right _ _) hn)]
end LowestVerma


end FiniteIntertwining
