/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.SkewKernel
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWPreimage

/-!
# The positive braid intersection and adapted-tail skew kernels

## Main results

* `braid_skewDividedGenerator` and `braid_symm_rev_skewDividedGenerator` prove the actual
  `T''_(i,1)` and inverse `T'_(i,-1)` action on every bounded generator of Lusztig 38.1.1.
  These are the `e = -1` generators: the complementary generator has reversed order.
* `quotientLDeriv_eq_zero_iff_braid_positive` and
  `mem_quotientSkewGenerators_iff_braid_positive` identify the actual left skew kernel,
  bounded-generator algebra and positive braid intersection in the original radical quotient.
* `Modified.quotientLDeriv_integralPBWPreimage_cons_zero` supplies the actual kernel witness
  for every zero-leading adapted tail along an arbitrary reduced word.

The generator computation uses the proved lowering identity and its quantum-factorial
coefficient. The reverse intersection proof is reconstructed from finite skew-string spanning
and triangular directness, not an assumed intersection or form identity. All quotient statements
are over `ℚ(v)` with finite simple-root set, for an arbitrary Cartan datum and root datum.
No finite Weyl group, longest word or ambient-root independence is required. The auxiliary
unnormalized generator computation does not require finite simple-root set.

This does not prove projected coproduct compatibility (38.1.8), restricted braid isometry
(38.2.1), a general PBW product norm, or general PBW crystal-lattice membership.

## References

* G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993,
  37.2.5(b) (`e = -1`), 38.1.1, 38.1.3 and 38.1.6(a).
-/

open LieLean
noncomputable section
namespace LieLean.QuantumGroup
open LusztigF BraidDiagonal
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)

omit [Finite I] [DecidableEq I] in
lemma skew_twist_eq_shift {i j : I} (hij : i ≠ j) (n : ℕ) :
    (𝕧 ^ D.dot i i) ^ n * 𝕧 ^ D.dot i j =
      BraidDiagonal.shift (𝕧 ^ D.d i) ((𝕧 ^ D.d i) ^ negA D i j) n := by
  have hA := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos i j hij
  have hd := LusztigF.zpow_dot_eq (D := D) (v := 𝕧) hij
    (m := negA D i j) (by simp only [negA]; omega)
  rw [LusztigF.zpow_dot_self, hd, BraidDiagonal.shift, pow_mul, inv_pow]

omit [Finite I] in
lemma plus_rev_skewGenerator {i j : I} (hij : i ≠ j) (n : ℕ) :
    plusHom R 𝕧 (rev 𝕂 I (skewGenerator D 𝕧 i j n)) =
      rankTwoXp R 𝕧 i j n := by
  induction n with
  | zero => simp [rankTwoXp_zero]
  | succ n ih =>
    rw [skewGenerator_succ, skewAdjoint_apply, twist_skewGenerator, map_sub,
      rev_mul, rev_mul, rev_θ, map_smul, map_sub, map_mul, map_mul, map_smul,
      plusHom_θ, ih, skew_twist_eq_shift hij, smul_mul_assoc]
    rfl

omit [Finite I] in
/-- Unnormalized lowering identity with its exact factorial coefficient. -/
lemma braid_skewGenerator {i j : I} (hij : i ≠ j) (n : ℕ)
    (hn : n ≤ negA D i j) :
    braidEquivOfNotRoot R ratFunc_X_not_root i
      (plusHom R 𝕧 (skewGenerator D 𝕧 i j n)) =
        (qFactorial (𝕧 ^ D.d i) n / qFactorial (𝕧 ^ D.d i) (negA D i j - n)) •
          rankTwoXp R 𝕧 i j (negA D i j - n) := by
  have hq0 : 𝕧 ^ D.d i ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  have hq : 𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹ ≠ 0 :=
    sub_inv_ne_zero_of_pow_ne_one hq0
      (fun m hm ↦ by rw [← pow_mul]; exact ratFunc_X_not_root _ (Nat.mul_pos (D.d_pos i) hm))
  have hfac (m : ℕ) := qFactorial_ne_zero_of_not_root (D := D)
    RatFunc.X_ne_zero ratFunc_X_not_root i m
  have HT := braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i
  induction n with
  | zero =>
    simpa using map_E_eq_rankTwoXp HT hij
  | succ m ih =>
    have hm : m ≤ negA D i j := by omega
    obtain ⟨r, hr⟩ : ∃ r, negA D i j - m = r + 1 := ⟨negA D i j - m - 1, by omega⟩
    have hr' : negA D i j - (m + 1) = r := by omega
    let s := BraidDiagonal.shift (𝕧 ^ D.d i) ((𝕧 ^ D.d i) ^ negA D i j) m
    let t := BraidDiagonal.shift (𝕧 ^ D.d i) ((𝕧 ^ D.d i) ^ negA D i j) (r + 1)
    have hst : s * t = 1 := by
      have ha : negA D i j = r + 1 + m := by omega
      dsimp [s, t, BraidDiagonal.shift]
      rw [ha]
      field_simp
      ring
    have H := (braidDiagonal_hyp R 𝕧 RatFunc.X_ne_zero hij hq).stepE (K_neg_mul_Kt i) r
    change braidEi R i * rankTwoXp R 𝕧 i j (r + 1) -
      t • (rankTwoXp R 𝕧 i j (r + 1) * braidEi R i) =
      (-(t * cc (𝕧 ^ D.d i) ((𝕧 ^ D.d i) ^ negA D i j) (r + 1))) •
        rankTwoXp R 𝕧 i j r at H
    have H' : rankTwoXp R 𝕧 i j (r + 1) * braidEi R i -
        s • (braidEi R i * rankTwoXp R 𝕧 i j (r + 1)) =
        cc (𝕧 ^ D.d i) ((𝕧 ^ D.d i) ^ negA D i j) (r + 1) •
          rankTwoXp R 𝕧 i j r := by
      have h := congrArg (fun z : QuantumGroup R 𝕧 ↦ (-s) • z) H
      have hneg : (-s) * (-(t * cc (𝕧 ^ D.d i)
          ((𝕧 ^ D.d i) ^ negA D i j) (r + 1))) =
          cc (𝕧 ^ D.d i) ((𝕧 ^ D.d i) ^ negA D i j) (r + 1) := by
        rw [neg_mul_neg, ← mul_assoc, hst, one_mul]
      have hnegst : (-s) * t = -1 := by rw [neg_mul, hst]
      change (-s) • (_ - t • _) = (-s) • ((-(t * _)) • _) at h
      rw [smul_sub, smul_smul, smul_smul, hnegst, hneg] at h
      simpa only [neg_smul, one_smul, neg_neg, sub_eq_add_neg, add_comm] using h
    have hc : qFactorial (𝕧 ^ D.d i) m / qFactorial (𝕧 ^ D.d i) (r + 1) *
        cc (𝕧 ^ D.d i) ((𝕧 ^ D.d i) ^ negA D i j) (r + 1) =
        qFactorial (𝕧 ^ D.d i) (m + 1) / qFactorial (𝕧 ^ D.d i) r := by
      rw [cc_pow hq0 hq (by omega), show negA D i j - r = m + 1 by omega,
        qFactorial_succ, qFactorial_succ]
      have hfr := hfac (r + 1)
      rw [qFactorial_succ] at hfr
      have hqr := (mul_ne_zero_iff.mp hfr).1
      field_simp [hqr, hfac]
    rw [skewGenerator_succ, skewAdjoint_apply, twist_skewGenerator, map_sub,
      map_mul, map_mul, map_smul, plusHom_θ, map_sub, map_mul, map_mul, map_smul,
      ih hm, hr, skew_twist_eq_shift hij]
    have hself := map_E_self HT
    change braidEquivOfNotRoot R ratFunc_X_not_root i (E R 𝕧 i) = _ at hself
    rw [hself, hr']
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [smul_comm s, ← smul_sub, H', smul_smul, hc]

/-- **Lusztig 38.1.3**, the actual `T''_(i,1)` action on every bounded `e = -1`
source generator: the complementary generator has reversed multiplication order. -/
theorem braid_skewDividedGenerator {i j : I} (hij : i ≠ j) (n : ℕ)
    (hn : n ≤ negA D i j) :
    braidEquivOfNotRoot R ratFunc_X_not_root i
      (quotientPlus R (toQuotient D 𝕧 (skewDividedGenerator D 𝕧 i j n))) =
        quotientPlus R (toQuotient D 𝕧
          (rev 𝕂 I (skewDividedGenerator D 𝕧 i j (negA D i j - n)))) := by
  simp only [quotientPlus_toQuotient, skewDividedGenerator, map_smul,
    braid_skewGenerator R hij n hn, plus_rev_skewGenerator R hij, smul_smul]
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀
    (qFactorial_ne_zero_of_not_root (D := D) RatFunc.X_ne_zero ratFunc_X_not_root i n), one_mul]

/-- The inverse `T'_(i,-1)` transports the complementary reversed generator back. -/
theorem braid_symm_rev_skewDividedGenerator {i j : I} (hij : i ≠ j) (n : ℕ)
    (hn : n ≤ negA D i j) :
    (braidEquivOfNotRoot R ratFunc_X_not_root i).symm
      (quotientPlus R (toQuotient D 𝕧
        (rev 𝕂 I (skewDividedGenerator D 𝕧 i j (negA D i j - n))))) =
      quotientPlus R (toQuotient D 𝕧 (skewDividedGenerator D 𝕧 i j n)) := by
  rw [← braid_skewDividedGenerator R hij n hn, AlgEquiv.symm_apply_apply]

/-- The actual bounded-generator algebra is carried into the original positive half. -/
lemma braid_positive_of_mem_skewGenerators (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientSkewGenerators D i) :
    braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) ∈
      (plusHom R 𝕧).range := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hij, n, hn, rfl⟩ := hx
    rw [braid_skewDividedGenerator R hij n hn, quotientPlus_toQuotient]
    exact AlgHom.mem_range_self _ _
  | algebraMap c => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

/-- The positive braid intersection is precisely the original left skew kernel. -/
theorem quotientLDeriv_eq_zero_iff_braid_positive (i : I) (x : Quotient D 𝕧) :
    quotientLDeriv D i x = 0 ↔
      braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) ∈
        (plusHom R 𝕧).range := by
  constructor
  · intro hx
    exact braid_positive_of_mem_skewGenerators R i
      ((mem_quotientSkewGenerators_iff D i x).mpr hx)
  · intro hx
    obtain ⟨N, a, ha, he⟩ := exists_quotientSkewGenerators_decomposition D i x
    cases N with
    | zero => simpa using congrArg (quotientLDeriv D i) he
    | succ N =>
      let T := braidEquivOfNotRoot R ratFunc_X_not_root i
      let b (n : ℕ) := (qFactorial (𝕧 ^ D.d i) n)⁻¹ • T (quotientPlus R (a n))
      let f : ℕ →₀ QuantumGroup R 𝕧 :=
        (∑ n ∈ Finset.range (N + 1), Finsupp.single n (b n)) -
          Finsupp.single 0 (T (quotientPlus R x))
      have hb (n : ℕ) : b n ∈ (plusHom R 𝕧).range :=
        Subalgebra.smul_mem _ (braid_positive_of_mem_skewGenerators R i (ha n)) _
      have hf (n : ℕ) : f n ∈ (plusHom R 𝕧).range := by
        dsimp [f]
        simp only [Finsupp.finsetSum_apply]
        apply sub_mem
        · apply Subalgebra.sum_mem
          intro m hm
          by_cases hmn : m = n
          · subst m; simpa using hb n
          · simp [hmn]
        · by_cases hn : n = 0
          · subst n; simpa using hx
          · simp [Ne.symm hn]
      let L : (ℕ →₀ QuantumGroup R 𝕧) →ₗ[𝕂] QuantumGroup R 𝕧 :=
        Finsupp.lsum 𝕂 (fun n ↦
          (LinearMap.mulLeft 𝕂 (E R 𝕧 i ^ n)).comp T.symm.toLinearMap)
      have hL : L f = 0 := by
        have he' := congrArg (quotientPlus R) he
        simp only [map_sum, map_mul] at he'
        have hgen (n : ℕ) : quotientPlus R (quotientIntegralGenerator D i n) =
            (qFactorial (𝕧 ^ D.d i) n)⁻¹ • E R 𝕧 i ^ n := by
          simp [quotientIntegralGenerator, qDivPow]
        simp only [hgen, smul_mul_assoc] at he'
        dsimp [f]
        rw [map_sub, map_sum]
        simp only [L, Finsupp.lsum_single, LinearMap.comp_apply,
          LinearMap.mulLeft_apply, AlgEquiv.toLinearMap_apply,
          b, map_smul, AlgEquiv.symm_apply_apply, pow_zero, one_mul]
        exact sub_eq_zero.mpr he'.symm
      have hz : f = 0 := eq_zero_of_sum_E_pow_mul_symm ratFunc_X_not_root f hf hL
      have h0 := congrArg (fun g : ℕ →₀ QuantumGroup R 𝕧 ↦ g 0) hz
      have hax : a 0 = x := by
        apply quotientPlus_injective R
        apply T.injective
        simpa [f, b, Finsupp.finsetSum_apply, Finsupp.single_apply, sub_eq_zero] using h0
      rw [← hax]
      exact (mem_quotientSkewGenerators_iff D i (a 0)).mp (ha 0)

/-- The bounded source generators give exactly the positive braid intersection. -/
theorem mem_quotientSkewGenerators_iff_braid_positive (i : I) (x : Quotient D 𝕧) :
    x ∈ quotientSkewGenerators D i ↔
      braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) ∈
        (plusHom R 𝕧).range := by
  rw [mem_quotientSkewGenerators_iff, quotientLDeriv_eq_zero_iff_braid_positive R]

namespace Modified
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU
variable {W : Type*} [Group W]
  {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {i : I} {w : List I}

/-- The zero-leading-exponent preimage is the actual inverse-braid image of the tail. -/
theorem quotientPlus_integralPBWPreimage_cons_zero
    (hw : cs.IsReduced (i :: w)) (c : Fin w.length → ℕ) :
    quotientPlus R (integralPBWPreimage R hw (Fin.cons 0 c)) =
      (Ta R i).symm (quotientPlus R
        (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) c)) := by
  rw [quotientPlus_integralPBWPreimage, quotientPlus_integralPBWPreimage]
  simp [pbwDivSymm, CoxeterSystem.pbwDivMonomial_cons, Ed, qDivPow]

/-- A reduced PBW tail and its inverse-braid image both have actual integral preimages. -/
theorem braid_integralPBWPreimage_cons_zero
    (hw : cs.IsReduced (i :: w)) (c : Fin w.length → ℕ) :
    Ta R i (quotientPlus R (integralPBWPreimage R hw (Fin.cons 0 c))) =
      quotientPlus R (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) c) := by
  rw [quotientPlus_integralPBWPreimage_cons_zero, AlgEquiv.apply_symm_apply]

/-- Factor the original PBW preimage at its first node, with an actual integral tail. -/
theorem integralPBWPreimage_cons
    (hw : cs.IsReduced (i :: w)) (c : Fin (i :: w).length → ℕ) :
    (integralPBWPreimage R hw c : Quotient D 𝕧) =
      quotientIntegralGenerator D i (c 0) *
        (integralPBWPreimage R hw (Fin.cons 0 (fun n ↦ c n.succ)) : Quotient D 𝕧) := by
  apply quotientPlus_injective R
  rw [_root_.map_mul, quotientPlus_integralPBWPreimage,
    quotientPlus_integralPBWPreimage_cons_zero, quotientPlus_integralPBWPreimage]
  have hgen : quotientPlus R (quotientIntegralGenerator D i (c 0)) = Ed R i (c 0) := by
    simpa [quotientIntegralGenerator, qDivPow] using
      quotientPlus_dividedPower R i (c 0)
  rw [hgen]
  rfl


/-- Every zero-leading adapted tail for an arbitrary reduced word lies in the actual left kernel. -/
theorem quotientLDeriv_integralPBWPreimage_cons_zero
    (hw : cs.IsReduced (i :: w)) (c : Fin w.length → ℕ) :
    quotientLDeriv D i (integralPBWPreimage R hw (Fin.cons 0 c)) = 0 := by
  apply (quotientLDeriv_eq_zero_iff_braid_positive R i _).mpr
  change Ta R i (quotientPlus R (integralPBWPreimage R hw (Fin.cons 0 c))) ∈ _
  rw [braid_integralPBWPreimage_cons_zero]
  obtain ⟨x, hx⟩ := toQuotient_surjective D 𝕧
    (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) c)
  exact ⟨x, congrArg (quotientPlus R) hx⟩

end Modified

end LieLean.QuantumGroup
