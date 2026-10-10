/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWB2
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWPrime
import LieLean.Algebra.QuantumGroup.PBW.IntegralB2Opposite

/-!
# Integral B₂ PBW bases for inverse braid operators

Opposite B₂ straightening at the inverse parameter proves integral spanning for both reduced
words with inverse braid operators. The resulting braid invariance gives integral PBW spans
independent of the reduced expression for Cartan data without triple edges.

## Main results

* `Modified.span_pbwDivSymm_b2_braid`: integral invariance under the inverse B₂ braid move.
-/

open LieLean Finset MulOpposite

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

namespace Modified

attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

variable {i j : I} (hij : i ≠ j) (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)

include hij h h' in
/-- **The integral PBW monomials of `i j i j` span the integral form of the rank-two
subalgebra** (type `B₂`). -/
theorem span_pbwDivSymm_b2 :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R [i, j, i, j])) =
      (adjoinPair (R := R) i j).toSubmodule := by
  classical
  set q : 𝕂 := 𝕧 ^ D.d i
  set X := braidEj R 𝕧 i j
  set y := b2RootY R 𝕧 i j
  have hd : 𝕧 ^ D.d j = q ^ 2 := parameter_eq_square_of_double_edge h h'
  have hq0 : q ≠ 0 := pow_ne_zero _ (NeZero.ne 𝕧)
  have hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0 := fun n hn ↦
    qInt_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i) hn
  have hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 2) n ≠ 0 := fun n hn ↦ by
    rw [← hd]
    exact qInt_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne 𝕧))
      (vd_pow_ne_one (D := D) ratFunc_X_not_root j) hn
  have hq : q - q⁻¹ ≠ 0 :=
    sub_inv_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i)
  have h2 : qFactorial q 2 ≠ 0 := qFactorial_vd_ne_zero i 2
  have hF2 : qFactorial q 2 = qInt q 2 := by simp [qFactorial, qInt]
  have H : B2PBW.Rel (q ^ 2) (E R 𝕧 i) (qInt q 2 • X) y (E R 𝕧 j) := by
    have e : qInt q 2 • X = b2RootX R 𝕧 i j := by
      rw [show X = _ from b2_braidEj_eq h, smul_smul, ← hF2, mul_inv_cancel₀ h2, one_smul]
    rw [e]
    exact b2_rel hij h h'
  set Λ : Subring 𝕂 := (LusztigF.integralLaurentEval).range
  have hqΛ : q ∈ Λ := RingHom.mem_range.2 (isLaurent_pow (D.d i))
  have hqΛ' : q⁻¹ ∈ Λ := by
    have := isLaurent_inv_pow (D.d i)
    rw [inv_pow] at this
    exact RingHom.mem_range.2 this
  have hmap : ∀ (f : QuantumGroup R 𝕧 ≃ₐ[𝕂] QuantumGroup R 𝕧) (t : 𝕂) (n : ℕ) (x),
      f (qDivPow t n x) = qDivPow t n (f x) := fun f t n x ↦ map_qDivPow' f.toAlgHom t n x
  set T := braidEquivOfNotRoot R ratFunc_X_not_root
  have Hi := braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i
  have Hj := braidEquivOfNotRoot_hasImages ratFunc_X_not_root R j
  have hT2 : T i (E R 𝕧 j) = X := a2_rootVector_two hij Hi
  have hT3 : T i (T j (E R 𝕧 i)) = y := by
    have e := b2_rootVector_three Hi Hj hij h h' hq
    change T i (T j (E R 𝕧 i)) = _ at e
    rw [e, b2_cc_two hq0 hq, ← b2_qFactorial_two hq0, inv_mul_cancel₀ h2, one_smul,
      BraidDiagonal.X_succ (n := 0), b2_shift_zero]
    rfl
  have hT4 : T i (T j (T i (E R 𝕧 j))) = E R 𝕧 j := b2_rootVector_four Hi Hj hij h h' hq h2
  have hsymm : ∀ k z, (T k).symm z = braidReversal (T k (braidReversal z)) :=
    fun k z ↦ braidEquivOfNotRoot_symm_apply' k z
  have Hs : B2PBW.Rel (q ^ 2) (op (E R 𝕧 i))
      (qInt q 2 • op (braidReversal X)) (op (braidReversal y)) (op (E R 𝕧 j)) := by
    constructor <;> apply unop_injective
    · simpa only [unop_mul, unop_sub, unop_smul, unop_op, map_sub, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal H.fe
    · simpa only [unop_mul, unop_sub, unop_smul, unop_op, map_sub, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal H.ye
    · simpa only [unop_mul, unop_smul, unop_op, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal H.xe
    · simpa only [unop_mul, unop_smul, unop_op, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal H.fy
  have hmono : ∀ c : Fin 4 → ℕ, pbwDivSymm R [i, j, i, j] c =
      B2Integral.M4 q (E R 𝕧 i) (braidReversal X) (braidReversal y) (E R 𝕧 j)
        (c 0) (c 1) (c 2) (c 3) := fun c ↦ by
    simp only [CoxeterSystem.pbwDivMonomial, Ta_symm_apply, _root_.map_mul, _root_.map_one, mul_one]
    change Ed R i _ * ((T i).symm (Ed R j _) * ((T i).symm ((T j).symm (Ed R i _)) *
      (T i).symm ((T j).symm ((T i).symm (Ed R j _))))) = _
    rw [Ed, Ed, Ed, Ed, hmap, hmap, hmap, hmap, hmap, hmap]
    simp only [hsymm, braidReversal_E, braidReversal_involutive _]
    rw [hT4, hT3, hT2, braidReversal_E, hd]
    simp only [B2Integral.M4, B2Integral.M3, mul_assoc]
    rfl
  have hconv : ∀ x, x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R [i, j, i, j])) ↔
      x ∈ B2Integral.orderedSpan q Λ (E R 𝕧 i) (braidReversal X) (braidReversal y)
        (E R 𝕧 j) := fun x ↦ by
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        rw [hmono]; exact B2Integral.M4_mem_orderedSpan _ _ _ _
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul a x _ hx =>
        rw [laurent_smul_U]
        exact B2Integral.smul_mem_orderedSpan (RingHom.mem_range.2 ⟨a, rfl⟩) hx
    · intro hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨c, hc, a, b, c', d, rfl⟩ := hx
        obtain ⟨a', rfl⟩ := RingHom.mem_range.1 hc
        rw [← laurent_smul_U, show B2Integral.M4 q (E R 𝕧 i) (braidReversal X)
          (braidReversal y) (E R 𝕧 j) a b c' d =
          pbwDivSymm R [i, j, i, j] ![a, b, c', d] by rw [hmono]; rfl]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
  have hS := B2Integral.coe_orderedSpan_eq_genRing_of_op hq0 hqi hpi Hs hqΛ hqΛ'
  ext x
  rw [hconv, Subalgebra.mem_toSubmodule, ← SetLike.mem_coe, hS, ← coe_adjoinPair_eq_genRing hd]
  exact Iff.rfl

include hij h h' in
/-- **The integral PBW monomials of `j i j i` span the integral form of the rank-two
subalgebra** (type `B₂`; via the opposite algebra). -/
theorem span_pbwDivSymm_b2_rev :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R [j, i, j, i])) =
      (adjoinPair (R := R) i j).toSubmodule := by
  classical
  set q : 𝕂 := 𝕧 ^ D.d i
  set y' := b2RevRootY R 𝕧 i j
  set X' := (qFactorial q 2)⁻¹ • b2RevRootX R 𝕧 i j
  have hd : 𝕧 ^ D.d j = q ^ 2 := parameter_eq_square_of_double_edge h h'
  have hq0 : q ≠ 0 := pow_ne_zero _ (NeZero.ne 𝕧)
  have hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0 := fun n hn ↦
    qInt_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i) hn
  have hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 2) n ≠ 0 := fun n hn ↦ by
    rw [← hd]
    exact qInt_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne 𝕧))
      (vd_pow_ne_one (D := D) ratFunc_X_not_root j) hn
  have hq : q - q⁻¹ ≠ 0 :=
    sub_inv_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i)
  have h2 : qFactorial q 2 ≠ 0 := qFactorial_vd_ne_zero i 2
  have hF2 : qFactorial q 2 = qInt q 2 := by simp [qFactorial, qInt]
  have hS3 := serre_E R 𝕧 hij
  rw [B2PBW.toNat_one_sub_eq_three h] at hS3
  have hS2 := serre_E R 𝕧 hij.symm
  rw [A2PBW.toNat_one_sub_eq_two h', hd] at hS2
  have H : B2PBW.Rel (q ^ 2) (op (E R 𝕧 i)) (qInt q 2 • op X') (op y') (op (E R 𝕧 j)) := by
    have e : qInt q 2 • op X' = op (b2RevRootX R 𝕧 i j) := by
      rw [← op_smul, smul_smul, ← hF2, mul_inv_cancel₀ h2, one_smul]
    rw [e]
    exact B2PBW.rel_op hq0 hS3 hS2
  set Λ : Subring 𝕂 := (LusztigF.integralLaurentEval).range
  have hqΛ : q ∈ Λ := RingHom.mem_range.2 (isLaurent_pow (D.d i))
  have hqΛ' : q⁻¹ ∈ Λ := by
    have := isLaurent_inv_pow (D.d i)
    rw [inv_pow] at this
    exact RingHom.mem_range.2 this
  have hmap : ∀ (f : QuantumGroup R 𝕧 ≃ₐ[𝕂] QuantumGroup R 𝕧) (t : 𝕂) (n : ℕ) (x),
      f (qDivPow t n x) = qDivPow t n (f x) := fun f t n x ↦ map_qDivPow' f.toAlgHom t n x
  set T := braidEquivOfNotRoot R ratFunc_X_not_root
  have Hi := braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i
  have Hj := braidEquivOfNotRoot_hasImages ratFunc_X_not_root R j
  have hY' : T j (E R 𝕧 i) = y' := by
    have e := a2_rootVector_two hij.symm Hj
    change T j (E R 𝕧 i) = _ at e
    rw [e, braidEj_eq_of_cartanMatrix_eq_neg_one h', parameter_eq_square_of_double_edge h h']
    rfl
  have hY : T j (b2RootY R 𝕧 i j) = E R 𝕧 i := by
    rw [b2RootY_eq_X R 𝕧 (j := j)]
    exact b2_T_X_one Hj hij h h' hq h2
  have hX : T j (T i (E R 𝕧 j)) = X' := by
    have e := a2_rootVector_two hij Hi
    change T i (E R 𝕧 j) = _ at e
    rw [e, b2_braidEj_eq h, _root_.map_smul, b2RootX, _root_.map_sub, _root_.map_mul,
      _root_.map_mul, hY, hY']
    rfl
  have hE : T j (T i (T j (E R 𝕧 i))) = E R 𝕧 i := by
    have e := b2_rootVector_three Hi Hj hij h h' hq
    change T i (T j (E R 𝕧 i)) = _ at e
    rw [e, b2_cc_two hq0 hq, ← b2_qFactorial_two hq0, inv_mul_cancel₀ h2, one_smul,
      ← b2RootY_eq_X, hY]
  have hsymm : ∀ k z, (T k).symm z = braidReversal (T k (braidReversal z)) :=
    fun k z ↦ braidEquivOfNotRoot_symm_apply' k z
  have Hs : B2PBW.Rel (q ^ 2) (op (op (E R 𝕧 i)))
      (qInt q 2 • op (op (braidReversal X'))) (op (op (braidReversal y')))
      (op (op (E R 𝕧 j))) := by
    constructor <;> apply unop_injective <;> apply unop_injective
    · simpa only [unop_mul, unop_sub, unop_smul, unop_op, map_sub, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal (congrArg unop H.fe)
    · simpa only [unop_mul, unop_sub, unop_smul, unop_op, map_sub, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal (congrArg unop H.ye)
    · simpa only [unop_mul, unop_smul, unop_op, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal (congrArg unop H.xe)
    · simpa only [unop_mul, unop_smul, unop_op, map_smul,
        braidReversal_mul, braidReversal_E] using congrArg braidReversal (congrArg unop H.fy)
  have hmono : ∀ c : Fin 4 → ℕ, op (pbwDivSymm R [j, i, j, i] c) =
      B2Integral.M4 q (op (E R 𝕧 i)) (op (braidReversal X')) (op (braidReversal y'))
        (op (E R 𝕧 j)) (c 3) (c 2) (c 1) (c 0) := fun c ↦ by
    simp only [CoxeterSystem.pbwDivMonomial, Ta_symm_apply, _root_.map_mul, _root_.map_one, mul_one]
    change op (Ed R j _ * ((T j).symm (Ed R i _) * ((T j).symm ((T i).symm (Ed R j _)) *
      (T j).symm ((T i).symm ((T j).symm (Ed R i _)))))) = _
    rw [Ed, Ed, Ed, Ed, hmap, hmap, hmap, hmap, hmap, hmap]
    simp only [hsymm, braidReversal_E, braidReversal_involutive _]
    rw [hE, hX, hY', braidReversal_E, hd]
    simp only [B2Integral.M4, B2Integral.M3, qDivPow_op, op_mul, mul_assoc]
    rfl
  have hconv : ∀ x, x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R [j, i, j, i])) ↔
      op x ∈ B2Integral.orderedSpan q Λ (op (E R 𝕧 i)) (op (braidReversal X'))
        (op (braidReversal y')) (op (E R 𝕧 j)) := by
    intro x
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        rw [hmono]; exact B2Integral.M4_mem_orderedSpan _ _ _ _
      | zero => rw [op_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [op_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [laurent_smul_U, op_smul]
        exact B2Integral.smul_mem_orderedSpan (RingHom.mem_range.2 ⟨a, rfl⟩) hx
    · intro hx
      rw [← unop_op x]
      generalize op x = z at hx
      induction hx using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, a, b, c', d, rfl⟩ := hz
        obtain ⟨a', rfl⟩ := RingHom.mem_range.1 hc
        rw [unop_smul, ← laurent_smul_U, show unop (B2Integral.M4 q (op (E R 𝕧 i))
          (op (braidReversal X'))
          (op (braidReversal y')) (op (E R 𝕧 j)) a b c' d) =
          pbwDivSymm R [j, i, j, i] ![d, c', b, a] by
            rw [← unop_op (pbwDivSymm R [j, i, j, i] _), hmono]; rfl]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      | zero => rw [unop_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [unop_add]; exact add_mem hx hy
      | neg x _ hx => rw [unop_neg]; exact neg_mem hx
  have hS := B2Integral.coe_orderedSpan_eq_genRing_of_op hq0 hqi hpi Hs hqΛ hqΛ'
  have hgen : B2Integral.genRing q Λ (op (E R 𝕧 i)) (op (E R 𝕧 j)) =
      (B2Integral.genRing q Λ (E R 𝕧 i) (E R 𝕧 j)).op := by
    rw [B2Integral.genRing, B2Integral.genRing, Subring.op_closure]
    congr 1
    ext z
    constructor
    · rintro ((⟨c, hc, rfl⟩ | ⟨n, rfl⟩) | ⟨n, rfl⟩)
      · exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
      · exact Or.inl (Or.inr ⟨n, by simp [qDivPow_op]⟩)
      · exact Or.inr ⟨n, by simp [qDivPow_op]⟩
    · rintro ((⟨c, hc, hz⟩ | ⟨n, hz⟩) | ⟨n, hz⟩)
      · exact Or.inl (Or.inl ⟨c, hc, unop_injective hz⟩)
      · exact Or.inl (Or.inr ⟨n, unop_injective (by simpa [qDivPow_op] using hz)⟩)
      · exact Or.inr ⟨n, unop_injective (by simpa [qDivPow_op] using hz)⟩
  ext x
  rw [hconv, Subalgebra.mem_toSubmodule, ← SetLike.mem_coe, hS, hgen, SetLike.mem_coe,
    Subring.mem_op, unop_op, ← SetLike.mem_coe, ← coe_adjoinPair_eq_genRing hd]
  exact Iff.rfl

include hij h h' in
/-- **The `B₂` braid move preserves the integral PBW span.** -/
theorem span_pbwDivSymm_b2_braid :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R [i, j, i, j])) =
      Submodule.span 𝒜 (Set.range (pbwDivSymm R [j, i, j, i])) := by
  rw [span_pbwDivSymm_b2 hij h h', span_pbwDivSymm_b2_rev hij h h']

/-- Under the hypothesis that the integral PBW span is invariant under braid moves, the results
below follow as in the simply-laced case. -/
def BraidInvariantSymm (R : D.RootDatum Y) : Prop :=
  ∀ u w : List I, D.cartanMatrix.coxeterMatrix.BraidMove u w →
    Submodule.span 𝒜 (Set.range (pbwDivSymm R u)) = Submodule.span 𝒜 (Set.range (pbwDivSymm R w))

/-- **Braid moves preserve the integral PBW span** for Cartan data without a pair
`aᵢⱼ aⱼᵢ = 3`. -/
theorem braidInvariantSymm_of_mul_ne_three
    (h3 : ∀ i j, D.cartanMatrix i j * D.cartanMatrix j i ≠ 3) : BraidInvariantSymm R := by
  intro u w hm
  obtain ⟨p, s, i, j, hij, hmij, rfl, rfl⟩ := hm
  have hT0 := isBraidLiftable_braidEquivOfNotRoot R ratFunc_X_not_root i j hij hmij
  have key : ∀ u w : List I,
      (u.reverse.map (braidEquivOfNotRoot R ratFunc_X_not_root)).prod =
        (w.reverse.map (braidEquivOfNotRoot R ratFunc_X_not_root)).prod →
      (u.map fun i ↦ (Ta R i).symm).prod = (w.map fun i ↦ (Ta R i).symm).prod := by
    intro u w huw
    ext x
    rw [list_Ta_symm_apply, list_Ta_symm_apply, list_symm_prod_eq_symm, list_symm_prod_eq_symm,
      huw]
  have hw : ∀ (n : ℕ) (a b : ℤ), D.cartanMatrix i j = a → D.cartanMatrix j i = b →
      (a * b).toNat = n → D.cartanMatrix.coxeterMatrix i j = Matrix.coxeterEntry n ∧
        D.cartanMatrix.coxeterMatrix j i = Matrix.coxeterEntry n := by
    intro n a b ha hb hn
    rw [Matrix.coxeterMatrix_apply_of_ne _ hij, Matrix.coxeterMatrix_apply_of_ne _ hij.symm, ha,
      hb, mul_comm b, hn]
    exact ⟨rfl, rfl⟩
  rcases cartanMatrix_cases hij hmij with ⟨h0, h0'⟩ | ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | h3'
  · obtain ⟨hm, hm'⟩ := hw 0 0 0 h0 h0' rfl
    have e : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j] := by
      simp only [CoxeterSystem.braidWord]; rw [hm]; rfl
    have e' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i] := by
      simp only [CoxeterSystem.braidWord]; rw [hm']; rfl
    rw [e, e'] at hT0 ⊢
    exact CoxeterSystem.span_pbwDivMonomial_context (fun i ↦ (Ta R i).symm) (Ed R)
      (span_pbwDivSymm_commuting h0)
      (key [i, j] [j, i] (by simpa using hT0.symm)) p s
  · obtain ⟨hm, hm'⟩ := hw 1 (-1) (-1) h1 h1' rfl
    have e : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [j, i, j] := by
      simp only [CoxeterSystem.braidWord]; rw [hm]; rfl
    have e' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [i, j, i] := by
      simp only [CoxeterSystem.braidWord]; rw [hm']; rfl
    rw [e, e'] at hT0 ⊢
    exact CoxeterSystem.span_pbwDivMonomial_context (fun i ↦ (Ta R i).symm) (Ed R)
      (span_pbwDivSymm_a2_braid hij h1 h1').symm
      (key [j, i, j] [i, j, i] (by simpa using hT0)) p s
  · obtain ⟨hm, hm'⟩ := hw 2 (-2) (-1) h2 h2' rfl
    have e : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j, i, j] := by
      simp only [CoxeterSystem.braidWord]; rw [hm]; rfl
    have e' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i, j, i] := by
      simp only [CoxeterSystem.braidWord]; rw [hm']; rfl
    rw [e, e'] at hT0 ⊢
    exact CoxeterSystem.span_pbwDivMonomial_context (fun i ↦ (Ta R i).symm) (Ed R)
      (span_pbwDivSymm_b2_braid hij h2 h2')
      (key [i, j, i, j] [j, i, j, i] (by simpa using hT0.symm)) p s
  · obtain ⟨hm, hm'⟩ := hw 2 (-1) (-2) h2 h2' rfl
    have e : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j, i, j] := by
      simp only [CoxeterSystem.braidWord]; rw [hm]; rfl
    have e' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i, j, i] := by
      simp only [CoxeterSystem.braidWord]; rw [hm']; rfl
    rw [e, e'] at hT0 ⊢
    exact CoxeterSystem.span_pbwDivMonomial_context (fun i ↦ (Ta R i).symm) (Ed R)
      (span_pbwDivSymm_b2_braid hij.symm h2' h2).symm
      (key [i, j, i, j] [j, i, j, i] (by simpa using hT0.symm)) p s
  · exact absurd h3' (h3 i j)

section BraidInvariantSymm

variable (hB : BraidInvariantSymm R)
include hB

/-- **[Lus] 41.1.4 (a)** (`e = -1`) from braid invariance: reduced expressions of the same element
`w` give the same `𝒜`-span `𝒜U⁺(w, -1)` of the integral PBW monomials. -/
theorem span_pbwDivSymm_of_isReduced_of_braidInvariant {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R u)) = Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) :=
  CoxeterSystem.eq_of_reflTransGen_braidMove (fun _ _ _ hm ↦ hB _ _ hm)
    hu (CoxeterSystem.reflTransGen_braidMove_of_isReduced hu hw huw)

/-- **[Lus] 41.1.4 (c)** (`e = -1`) from braid invariance: if `ℓ(sᵢ w) < ℓ(w)` then
`Eᵢ^{(t)} 𝒜U⁺(w, -1) ⊆ 𝒜U⁺(w, -1)`. -/
theorem qDivPow_E_mul_mem_span_pbwDivSymm_of_braidInvariant {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    {i : I} (hi : cs.IsLeftDescent (cs.wordProd w) i) (t : ℕ) {x : QuantumGroup R 𝕧}
    (hx : x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R w))) :
    qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i) * x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) := by
  obtain ⟨u, hu, hu₀⟩ := exists_reduced_cons_of_isLeftDescent cs hi
  have hs := span_pbwDivSymm_of_isReduced_of_braidInvariant hB cs hu hw hu₀
  rw [← hs] at hx ⊢
  exact CoxeterSystem.mul_mem_pbwDivSpan_cons (fun i ↦ (Ta R i).symm) (Ed R) i u
    (Ed_mul_mem_span i t) hx

/-- **[Lus] 41.1.7** (`e = -1`, finite type) from braid invariance: for a reduced expression of the
longest element `w₀`, `𝒜U⁺(w₀, -1) = 𝒜U⁺`, the `𝒜`-subalgebra generated by the `Eᵢ^{(n)}`. -/
theorem span_pbwDivSymm_longest_eq_of_braidInvariant {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) =
      (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule := by
  let S := Submodule.span 𝒜 (Set.range (pbwDivSymm R w))
  have hplus : ∀ c, pbwDivSymm R w c ∈ Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i)) := fun c ↦ by
    have hc := pbwDivSymm_mem_aPlus (R := R) w [] (by simpa using hw) c
    simp only [List.map_nil, List.prod_nil, AlgEquiv.one_apply] at hc
    generalize pbwDivSymm R w c = y at hc ⊢
    induction hc using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, w', hc, rfl⟩ := hx
      refine smul_mem_of_isLaurent hc ?_
      induction w' with
      | nil => exact one_mem _
      | cons p w' ih =>
        rw [ePow_cons]
        exact mul_mem (Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨p.1, p.2, rfl⟩)) ih
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨c, rfl⟩; exact hplus c
  · intro x hx
    have h1 : (1 : QuantumGroup R 𝕧) ∈ S :=
      CoxeterSystem.one_mem_pbwDivSpan (fun i ↦ (Ta R i).symm) (Ed R) Ed_zero w
    have hmul : ∀ y ∈ S, x * y ∈ S := by
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, n, rfl⟩ := Set.mem_iUnion.1 hx
        exact fun y hy ↦ qDivPow_E_mul_mem_span_pbwDivSymm_of_braidInvariant hB cs hw
          (hw₀ ▸ cs.isLeftDescent_longestElement i) n hy
      | algebraMap a =>
        intro y hy
        rw [← Algebra.smul_def]
        exact S.smul_mem a hy
      | add x z _ _ hx hz =>
        intro y hy; rw [add_mul]; exact add_mem (hx y hy) (hz y hy)
      | mul x z _ _ hx hz =>
        intro y hy; rw [mul_assoc]; exact hx _ (hz y hy)
    simpa using hmul 1 h1

/-- **[Lus] 41.1.7**, second form, from braid invariance: `𝒜U⁺(w₀, -1) = aPlus R`. -/
theorem coe_span_pbwDivSymm_longest_of_braidInvariant {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    (Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) : Set (QuantumGroup R 𝕧)) = aPlus R := by
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      simpa using pbwDivSymm_mem_aPlus (R := R) w [] (by simpa using hw) c
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => rw [laurent_smul_U]; exact smul_mem_aPlus ⟨a, rfl⟩ hx
  · rw [SetLike.mem_coe, span_pbwDivSymm_longest_eq_of_braidInvariant hB cs hw hw₀]
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, w', hc, rfl⟩ := hx
      refine smul_mem_of_isLaurent hc ?_
      induction w' with
      | nil => exact one_mem _
      | cons p w' ih =>
        rw [ePow_cons]
        exact mul_mem (Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨p.1, p.2, rfl⟩)) ih
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx

end BraidInvariantSymm

/-! ### Cartan data without triple edges -/

section NoTripleEdge

variable (h3 : ∀ i j, D.cartanMatrix i j * D.cartanMatrix j i ≠ 3)
include h3

/-- **[Lus] 41.1.4 (a)** (`e = -1`) for Cartan data without a pair `aᵢⱼ aⱼᵢ = 3`. -/
theorem span_pbwDivSymm_of_isReduced_of_mul_ne_three {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R u)) = Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) :=
  span_pbwDivSymm_of_isReduced_of_braidInvariant
    (braidInvariantSymm_of_mul_ne_three h3) cs hu hw huw

/-- **[Lus] 41.1.4 (c)** (`e = -1`) for Cartan data without a pair `aᵢⱼ aⱼᵢ = 3`. -/
theorem qDivPow_E_mul_mem_span_pbwDivSymm_of_mul_ne_three {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    {i : I} (hi : cs.IsLeftDescent (cs.wordProd w) i) (t : ℕ) {x : QuantumGroup R 𝕧}
    (hx : x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R w))) :
    qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i) * x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) :=
  qDivPow_E_mul_mem_span_pbwDivSymm_of_braidInvariant
    (braidInvariantSymm_of_mul_ne_three h3) cs hw hi t hx

/-- **[Lus] 41.1.7** (`e = -1`) in finite type without a pair `aᵢⱼ aⱼᵢ = 3` (types `A`, `B`, `C`,
`D`, `E`, `F`): `𝒜U⁺(w₀, -1) = 𝒜U⁺`. -/
theorem span_pbwDivSymm_longest_eq_of_mul_ne_three {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) =
      (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule :=
  span_pbwDivSymm_longest_eq_of_braidInvariant (braidInvariantSymm_of_mul_ne_three h3) cs hw hw₀

/-- **[Lus] 41.1.7**, second form, without a pair `aᵢⱼ aⱼᵢ = 3`: `𝒜U⁺(w₀, -1) = aPlus R`. -/
theorem coe_span_pbwDivSymm_longest_of_mul_ne_three {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    (Submodule.span 𝒜 (Set.range (pbwDivSymm R w)) : Set (QuantumGroup R 𝕧)) = aPlus R :=
  coe_span_pbwDivSymm_longest_of_braidInvariant (braidInvariantSymm_of_mul_ne_three h3) cs hw hw₀

end NoTripleEdge

variable (h3 : ∀ i j, D.cartanMatrix i j * D.cartanMatrix j i ≠ 3)

include h3 in
/-- **[Lus] 41.1.4 (a)** (`e = 1`, type without triple edges): the `𝒜`-span of the monomials
`E_{i₁}^{(c₁)} T'_{i₁,1}(E_{i₂}^{(c₂)}) ⋯` does not depend on the reduced expression. -/
theorem span_pbwDivPrime_of_isReduced_of_mul_ne_three {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span 𝒜 (Set.range (pbwDivPrime R u)) =
      Submodule.span 𝒜 (Set.range (pbwDivPrime R w)) := by
  rw [span_pbwDivPrime, span_pbwDivPrime, span_pbwDiv_of_isReduced_of_mul_ne_three h3 cs hu hw huw]

include h3 in
/-- **[Lus] 41.1.4 (b)** (`e = -1`, type without triple edges): the `𝒜`-span of the monomials
`E_{i₁}^{(c₁)} T''_{i₁,-1}(E_{i₂}^{(c₂)}) ⋯` does not depend on the reduced expression, and equals
the span `𝒜U⁺(w, -1)` of [Lus] 41.1.4 (a) (`span_pbwDivPrimeSymm`). -/
theorem span_pbwDivPrimeSymm_of_isReduced_of_mul_ne_three {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R u)) =
      Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R w)) := by
  rw [span_pbwDivPrimeSymm, span_pbwDivPrimeSymm, span_pbwDivSymm_of_isReduced_of_mul_ne_three h3
   cs hu hw huw]

include h3 in
/-- **[Lus] 41.1.7** (`e = 1`, via `T'_{i,1}`): `𝒜U⁺(w₀, 1) = 𝒜U⁺` in finite type. -/
theorem coe_span_pbwDivPrime_longest_of_mul_ne_three {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    (Submodule.span 𝒜 (Set.range (pbwDivPrime R w)) : Set (QuantumGroup R 𝕧)) = aPlus R := by
  rw [span_pbwDivPrime, coe_span_pbwDiv_longest_of_mul_ne_three h3 cs hw hw₀]

include h3 in
/-- **[Lus] 41.1.7** (`e = -1`, via `T''_{i,-1}`): `𝒜U⁺(w₀, -1) = 𝒜U⁺` in finite
type. -/
theorem coe_span_pbwDivPrimeSymm_longest_of_mul_ne_three {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    (Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R w)) : Set (QuantumGroup R 𝕧)) = aPlus R := by
  rw [span_pbwDivPrimeSymm, coe_span_pbwDivSymm_longest_of_mul_ne_three h3 cs hw hw₀]

include h3 in
/-- Left-descent stability for the `T'_{i,1}` integral PBW span, without triple edges. -/
theorem qDivPow_E_mul_mem_span_pbwDivPrime_of_mul_ne_three {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    {i : I} (hi : cs.IsLeftDescent (cs.wordProd w) i) (t : ℕ) {x : QuantumGroup R 𝕧}
    (hx : x ∈ Submodule.span 𝒜 (Set.range (pbwDivPrime R w))) :
    qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i) * x ∈
      Submodule.span 𝒜 (Set.range (pbwDivPrime R w)) := by
  rw [span_pbwDivPrime] at hx ⊢
  exact qDivPow_E_mul_mem_span_pbwDiv_of_mul_ne_three h3 cs hw hi t hx

include h3 in
/-- Left-descent stability for the `T''_{i,-1}` integral PBW span, without triple edges. -/
theorem qDivPow_E_mul_mem_span_pbwDivPrimeSymm_of_mul_ne_three {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    {i : I} (hi : cs.IsLeftDescent (cs.wordProd w) i) (t : ℕ) {x : QuantumGroup R 𝕧}
    (hx : x ∈ Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R w))) :
    qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i) * x ∈
      Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R w)) := by
  rw [span_pbwDivPrimeSymm] at hx ⊢
  exact qDivPow_E_mul_mem_span_pbwDivSymm_of_mul_ne_three h3 cs hw hi t hx

end Modified

end LieLean.QuantumGroup
