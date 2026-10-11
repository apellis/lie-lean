/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWG2
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWB2Symm
/-!
# Local integral G₂ spans for inverse braid operators

Both actual `pbwDivSymm` six-letter words span `adjoinPair` over `ℤ[v,v⁻¹]`.
The reconstructed proof conjugates each inverse braid operator by `braidReversal`,
then uses opposite multiplication and Laurent-unit normalization at the inverse parameter.
The four middle root scalars are `-q⁻³`, `q⁻⁴`, `q⁻⁶`, `-q⁻³`.
All fifteen relations come from the existing Serre theorem, not an assumed symmetry.

## Main results

* `Modified.span_pbwDivSymm_g2`, `Modified.span_pbwDivSymm_g2_rev`: both span identities.
* `Modified.span_pbwDivSymm_g2_braid`: the local integral braid-span equality.

## References

Lusztig, *Introduction to quantum groups*. Only the local inverse-convention input
is proved here; global inverse invariance and all-four-convention assembly are separate.
-/

open MulOpposite
noncomputable section
namespace LieLean.QuantumGroup
section
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {q : k} (hq : q ≠ 0) (e f : B)
include hq
private lemma unop_x1_inv : unop (G2PBW.x1 q (op e) (op f)) =
    (-q⁻¹ ^ 3) • G2PBW.x1 q⁻¹ e f := by
  simp only [G2PBW.x1, unop_sub, unop_mul, unop_smul, unop_op, inv_pow, inv_inv,
    smul_sub, smul_smul]
  have hc : -(q ^ 3)⁻¹ * q ^ 3 = (-1 : k) := by field_simp [hq]
  rw [hc]
  module
private lemma unop_x2_inv : unop (G2PBW.x2 q (op e) (op f)) =
    q⁻¹ ^ 4 • G2PBW.x2 q⁻¹ e f := by
  simp only [G2PBW.x2, unop_sub, unop_mul, unop_smul, unop_op, unop_x1_inv hq,
    inv_inv, smul_sub, smul_smul, smul_mul_assoc, mul_smul_comm]
  have hc : q⁻¹ ^ 4 * q = q⁻¹ ^ 3 := by field_simp [hq]
  rw [hc]
  module
private lemma unop_x3_inv : unop (G2PBW.x3 q (op e) (op f)) =
    (-q⁻¹ ^ 3) • G2PBW.x3 q⁻¹ e f := by
  simp only [G2PBW.x3, unop_sub, unop_mul, unop_smul, unop_op, unop_x2_inv hq,
    smul_sub, smul_smul, smul_mul_assoc, mul_smul_comm]
  have hc : q * q⁻¹ ^ 4 = q⁻¹ ^ 3 := by field_simp [hq]
  rw [hc]
  module
private lemma unop_z_inv : unop (G2PBW.z q (op e) (op f)) =
    q⁻¹ ^ 6 • G2PBW.z q⁻¹ e f := by
  simp only [G2PBW.z, unop_sub, unop_mul, unop_smul, unop_x1_inv hq, unop_x2_inv hq,
    smul_sub, smul_smul, smul_mul_assoc, mul_smul_comm]
  have hc : q * (-q⁻¹ ^ 3 * q⁻¹ ^ 4) = -q⁻¹ ^ 6 := by field_simp [hq]
  rw [hc]
  module
omit hq in
private lemma orderedSpan_smul_le {Λ : Subring k} {e A b C D f : B} {u v w t : k}
    (hu : u ∈ Λ) (hv : v ∈ Λ) (hw : w ∈ Λ) (ht : t ∈ Λ) :
    G2Integral.orderedSpan q Λ e (u • A) (v • b) (w • C) (t • D) f ≤
      G2Integral.orderedSpan q Λ e A b C D f := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro z ⟨c, hc, a, b', c', d, l, m, rfl⟩
  simp only [G2Integral.M6, G2Integral.M5, G2Integral.P3, qDivPow_smul_pow,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  exact G2Integral.smul_mem_orderedSpan
    (mul_mem hc (mul_mem (pow_mem ht _) (mul_mem (pow_mem hw _)
      (mul_mem (pow_mem hv _) (pow_mem hu _)))))
    (G2Integral.M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b)
      (C := C) (D := D) (f := f) a b' c' d l m)
omit hq in
private lemma orderedSpan_smul {Λ : Subring k} {e A b C D f : B} {u v w t : k}
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (ht0 : t ≠ 0)
    (hu : u ∈ Λ) (hv : v ∈ Λ) (hw : w ∈ Λ) (ht : t ∈ Λ)
    (hui : u⁻¹ ∈ Λ) (hvi : v⁻¹ ∈ Λ) (hwi : w⁻¹ ∈ Λ) (hti : t⁻¹ ∈ Λ) :
    G2Integral.orderedSpan q Λ e (u • A) (v • b) (w • C) (t • D) f =
      G2Integral.orderedSpan q Λ e A b C D f := by
  refine le_antisymm (orderedSpan_smul_le hu hv hw ht) ?_
  have hh := orderedSpan_smul_le (q := q) (e := e) (A := u • A) (b := v • b)
    (C := w • C) (D := t • D) (f := f) hui hvi hwi hti
  simpa only [smul_smul, inv_mul_cancel₀ hu0, inv_mul_cancel₀ hv0,
    inv_mul_cancel₀ hw0, inv_mul_cancel₀ ht0, one_smul] using hh
private lemma orderedSpan_op_normalized {Λ : Subring k}
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (hS4 : qSerre q 4 e f = 0) (hS2 : qSerre (q ^ 3) 2 f e = 0)
    (hn : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
    (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ) :
    G2Integral.orderedSpan q Λ e
      (unop (G2Integral.X3 q (op e) (op f)))
      (unop (G2Integral.X2 q (op e) (op f)))
      (unop (G2Integral.Z q (op e) (op f)))
      (unop (G2PBW.x1 q (op e) (op f))) f =
      (G2Integral.genRing q Λ e f).toAddSubgroup := by
  have hnorm : ∀ (c d : k) (x : B), c • d • x = d • c • x :=
    fun c d x => smul_comm c d x
  simp only [G2Integral.X3, G2Integral.X2, G2Integral.Z, unop_smul,
    unop_x1_inv hq, unop_x2_inv hq, unop_x3_inv hq, unop_z_inv hq]
  simp only [hnorm (qFactorial q 3)⁻¹, hnorm (qInt q 2)⁻¹]
  rw [← A2Integral.qFactorial_inv' (q := q) 3, ← A2Integral.qInt_inv' (q := q) 2]
  rw [orderedSpan_smul (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hq)))
    (pow_ne_zero _ (inv_ne_zero hq)) (pow_ne_zero _ (inv_ne_zero hq))
    (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hq)))
    (neg_mem (pow_mem hiΛ _)) (pow_mem hiΛ _) (pow_mem hiΛ _)
    (neg_mem (pow_mem hiΛ _))
    (by simpa only [inv_neg, inv_pow, inv_inv] using neg_mem (pow_mem hqΛ 3))
    (by simpa only [inv_pow, inv_inv] using pow_mem hqΛ 4)
    (by simpa only [inv_pow, inv_inv] using pow_mem hqΛ 6)
    (by simpa only [inv_neg, inv_pow, inv_inv] using neg_mem (pow_mem hqΛ 3))]
  have H := G2Integral.rel_of_not_root (inv_ne_zero hq)
    (fun n hn' => by simpa only [inv_pow, inv_ne_one] using hn n hn')
    (by simpa only [qSerre_inv] using hS4)
    (by simpa only [inv_pow, qSerre_inv] using hS2)
  have hh := G2Integral.orderedSpan_eq_genRing (inv_ne_zero hq)
    (by simpa only [A2Integral.qInt_inv'] using hqi)
    (by simpa only [inv_pow, A2Integral.qInt_inv'] using hpi) H hiΛ
    (by simpa only [inv_inv] using hqΛ)
  simpa only [G2Integral.orderedSpan, G2Integral.genRing, G2Integral.M6,
    G2Integral.M5, G2Integral.P3, inv_pow, A2Integral.qDivPow_inv',
    G2Integral.X3, G2Integral.X2, G2Integral.Z] using hh
end
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

namespace Modified

attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

variable {i j : I} (hij : i ≠ j) (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)

include hij h h' in
/-- The integral divided PBW span for `ijijij` is the two-simple-root
integral subalgebra, with the existing inverse braid convention. -/
theorem span_pbwDivSymm_g2 :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R [i, j, i, j, i, j])) =
      (adjoinPair (R := R) i j).toSubmodule := by
  classical
  set q : 𝕂 := 𝕧 ^ D.d i
  have hd : 𝕧 ^ D.d j = q ^ 3 := parameter_eq_cube_of_triple_edge h h'
  have hq0 : q ≠ 0 := pow_ne_zero _ (NeZero.ne 𝕧)
  have hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0 := fun n hn ↦
    qInt_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i) hn
  have hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0 := fun n hn ↦ by
    rw [← hd]
    exact qInt_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne 𝕧))
      (vd_pow_ne_one (D := D) ratFunc_X_not_root j) hn
  have hq : q - q⁻¹ ≠ 0 :=
    sub_inv_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i)
  have hf : qFactorial q 3 ≠ 0 := qFactorial_vd_ne_zero i 3
  have hS4 := serre_E R 𝕧 hij
  rw [h, show (1 - (-3 : ℤ)).toNat = 4 by rfl] at hS4
  have hS2 := serre_E R 𝕧 hij.symm
  rw [h', show (1 - (-1 : ℤ)).toNat = 2 by rfl, hd] at hS2
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
  have hv := altVec_g2_normalized R 𝕧 T Hi Hj hij h h' hq hf
  have ht1 : T i (E R 𝕧 j) = G2Integral.X3 q (E R 𝕧 i) (E R 𝕧 j) := congrFun hv (1 : Fin 6)
  have ht2 : T i (T j (E R 𝕧 i)) = G2Integral.X2 q (E R 𝕧 i) (E R 𝕧 j) := congrFun hv (2 : Fin 6)
  have ht3 : T i (T j (T i (E R 𝕧 j))) = G2Integral.Z q (E R 𝕧 i) (E R 𝕧 j) :=
    congrFun hv (3 : Fin 6)
  have ht4 : T i (T j (T i (T j (E R 𝕧 i)))) = G2PBW.x1 q (E R 𝕧 i) (E R 𝕧 j) :=
    congrFun hv (4 : Fin 6)
  have ht5 : T i (T j (T i (T j (T i (E R 𝕧 j))))) = E R 𝕧 j := congrFun hv (5 : Fin 6)
  let V := ![braidReversal (E R 𝕧 i),
    braidReversal (G2Integral.X3 q (E R 𝕧 i) (E R 𝕧 j)),
    braidReversal (G2Integral.X2 q (E R 𝕧 i) (E R 𝕧 j)),
    braidReversal (G2Integral.Z q (E R 𝕧 i) (E R 𝕧 j)),
    braidReversal (G2PBW.x1 q (E R 𝕧 i) (E R 𝕧 j)),
    braidReversal (E R 𝕧 j)]
  have hV : V = ![E R 𝕧 i,
      unop (G2Integral.X3 q (op (E R 𝕧 i)) (op (E R 𝕧 j))),
      unop (G2Integral.X2 q (op (E R 𝕧 i)) (op (E R 𝕧 j))),
      unop (G2Integral.Z q (op (E R 𝕧 i)) (op (E R 𝕧 j))),
      unop (G2PBW.x1 q (op (E R 𝕧 i)) (op (E R 𝕧 j))), E R 𝕧 j] := by
    simp only [V, G2Integral.X3, G2Integral.X2, G2Integral.Z,
      G2PBW.x3, G2PBW.x2, G2PBW.x1, G2PBW.z, unop_sub, unop_smul,
      unop_mul, unop_op, map_sub, map_smul, braidReversal_mul, braidReversal_E]
  have hsymm : ∀ k z, (T k).symm z = braidReversal (T k (braidReversal z)) :=
    fun k z ↦ braidEquivOfNotRoot_symm_apply' k z
  have hTa : ∀ k z, (Ta R k).symm z = (T k).symm z := fun _ _ => rfl
  have hmono : ∀ c : Fin 6 → ℕ, pbwDivSymm R [i, j, i, j, i, j] c =
      G2Integral.M6 q (V 0) (V 1) (V 2) (V 3) (V 4) (V 5)
        (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) := fun c ↦ by
    simp only [CoxeterSystem.pbwDivMonomial, hTa, _root_.map_mul, _root_.map_one,
      mul_one]
    simp only [Ed, hmap]
    simp only [hsymm, braidReversal_E, braidReversal_involutive _]
    rw [ht5, ht4, ht3, ht2, ht1, braidReversal_E, hd]
    simp only [V, G2Integral.M6, G2Integral.M5, G2Integral.P3,
      mul_assoc, braidReversal_E]
    rfl
  have hconv : ∀ x, x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R [i, j, i, j, i, j])) ↔
      x ∈ G2Integral.orderedSpan q Λ (V 0) (V 1) (V 2) (V 3) (V 4) (V 5) := fun x ↦ by
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        rw [hmono]; exact G2Integral.M6_mem_orderedSpan _ _ _ _ _ _
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul a x _ hx =>
        rw [laurent_smul_U]
        exact G2Integral.smul_mem_orderedSpan (RingHom.mem_range.2 ⟨a, rfl⟩) hx
    · intro hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨c, hc, a, b, c', d, l, m, rfl⟩ := hx
        obtain ⟨a', rfl⟩ := RingHom.mem_range.1 hc
        rw [← laurent_smul_U, show
          G2Integral.M6 q (V 0) (V 1) (V 2) (V 3) (V 4) (V 5) a b c' d l m =
          pbwDivSymm R [i, j, i, j, i, j] ![a, b, c', d, l, m] by rw [hmono]; rfl]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
  have hS : G2Integral.orderedSpan q Λ (V 0) (V 1) (V 2) (V 3) (V 4) (V 5) =
      (G2Integral.genRing q Λ (E R 𝕧 i) (E R 𝕧 j)).toAddSubgroup := by
    rw [hV]
    exact orderedSpan_op_normalized hq0 _ _ hqi hpi hS4 hS2
      (vd_pow_ne_one (D := D) ratFunc_X_not_root i) hqΛ hqΛ'
  ext x
  rw [hconv, hS]
  change x ∈ G2Integral.genRing q Λ (E R 𝕧 i) (E R 𝕧 j) ↔ x ∈ adjoinPair i j
  rw [← SetLike.mem_coe, ← coe_adjoinPair_eq_g2_genRing hd]
  rfl

include hij h h' in
/-- The integral divided PBW span for `jijiji` is the two-simple-root
integral subalgebra, with the existing inverse braid convention. -/
theorem span_pbwDivSymm_g2_rev :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R [j, i, j, i, j, i])) =
      (adjoinPair (R := R) i j).toSubmodule := by
  classical
  set q : 𝕂 := 𝕧 ^ D.d i
  have hd : 𝕧 ^ D.d j = q ^ 3 := parameter_eq_cube_of_triple_edge h h'
  have hq0 : q ≠ 0 := pow_ne_zero _ (NeZero.ne 𝕧)
  have hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0 := fun n hn ↦
    qInt_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i) hn
  have hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0 := fun n hn ↦ by
    rw [← hd]
    exact qInt_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne 𝕧))
      (vd_pow_ne_one (D := D) ratFunc_X_not_root j) hn
  have hq : q - q⁻¹ ≠ 0 :=
    sub_inv_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one (D := D) ratFunc_X_not_root i)
  have hf : qFactorial q 3 ≠ 0 := qFactorial_vd_ne_zero i 3
  have hS4 := serre_E R 𝕧 hij
  rw [h, show (1 - (-3 : ℤ)).toNat = 4 by rfl] at hS4
  have hS2 := serre_E R 𝕧 hij.symm
  rw [h', show (1 - (-1 : ℤ)).toNat = 2 by rfl, hd] at hS2
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
  have hv := altVec_g2_rev R 𝕧 T Hi Hj hij h h' hq hf
  rw [G2Integral.g2c3_eq hq0 hq hf, G2Integral.g2c2_eq hq0 hq hf] at hv
  have h2 : qInt q 2 ≠ 0 := hqi 2 (by decide)
  simp only [mul_assoc, inv_mul_cancel₀ h2, mul_one] at hv
  have ht1 : T j (E R 𝕧 i) = G2PBW.y1 q (E R 𝕧 i) (E R 𝕧 j) := congrFun hv (1 : Fin 6)
  have ht2 : T j (T i (E R 𝕧 j)) = (qFactorial q 3)⁻¹ • G2PBW.y3 q (E R 𝕧 i) (E R 𝕧 j) :=
    congrFun hv (2 : Fin 6)
  have ht3 : T j (T i (T j (E R 𝕧 i))) = (qInt q 2)⁻¹ • G2PBW.y2 q (E R 𝕧 i) (E R 𝕧 j) :=
    congrFun hv (3 : Fin 6)
  have ht4 : T j (T i (T j (T i (E R 𝕧 j)))) = (qFactorial q 3)⁻¹ • G2PBW.w q (E R 𝕧 i) (E R 𝕧 j) :=
    congrFun hv (4 : Fin 6)
  have ht5 : T j (T i (T j (T i (T j (E R 𝕧 i))))) = E R 𝕧 i := congrFun hv (5 : Fin 6)
  let V := ![op (braidReversal (E R 𝕧 i)),
    op (braidReversal ((qFactorial q 3)⁻¹ • G2PBW.w q (E R 𝕧 i) (E R 𝕧 j))),
    op (braidReversal ((qInt q 2)⁻¹ • G2PBW.y2 q (E R 𝕧 i) (E R 𝕧 j))),
    op (braidReversal ((qFactorial q 3)⁻¹ • G2PBW.y3 q (E R 𝕧 i) (E R 𝕧 j))),
    op (braidReversal (G2PBW.y1 q (E R 𝕧 i) (E R 𝕧 j))),
    op (braidReversal (E R 𝕧 j))]
  have hV : V = ![op (E R 𝕧 i),
      unop (G2Integral.X3 q (op (op (E R 𝕧 i))) (op (op (E R 𝕧 j)))),
      unop (G2Integral.X2 q (op (op (E R 𝕧 i))) (op (op (E R 𝕧 j)))),
      unop (G2Integral.Z q (op (op (E R 𝕧 i))) (op (op (E R 𝕧 j)))),
      unop (G2PBW.x1 q (op (op (E R 𝕧 i))) (op (op (E R 𝕧 j)))), op (E R 𝕧 j)] := by
    simp only [V, G2Integral.X3, G2Integral.X2, G2Integral.Z,
      G2PBW.x3, G2PBW.x2, G2PBW.x1, G2PBW.z, G2PBW.w, G2PBW.y3,
      G2PBW.y2, G2PBW.y1, op_sub, op_smul, op_mul, unop_sub, unop_smul,
      unop_mul, unop_op, map_sub, map_smul, braidReversal_mul, braidReversal_E]
  have hsymm : ∀ k z, (T k).symm z = braidReversal (T k (braidReversal z)) :=
    fun k z ↦ braidEquivOfNotRoot_symm_apply' k z
  have hTa : ∀ k z, (Ta R k).symm z = (T k).symm z := fun _ _ => rfl
  have hmono : ∀ c : Fin 6 → ℕ, op (pbwDivSymm R [j, i, j, i, j, i] c) =
      G2Integral.M6 q (V 0) (V 1) (V 2) (V 3) (V 4) (V 5)
        (c 5) (c 4) (c 3) (c 2) (c 1) (c 0) := fun c ↦ by
    simp only [CoxeterSystem.pbwDivMonomial, hTa, _root_.map_mul, _root_.map_one,
      mul_one]
    simp only [Ed, hmap]
    simp only [hsymm, braidReversal_E, braidReversal_involutive _]
    rw [ht5, ht4, ht3, ht2, ht1, braidReversal_E, hd]
    simp only [V, G2Integral.M6, G2Integral.M5, G2Integral.P3,
      op_mul, mul_assoc, braidReversal_E]
    rfl
  have hconv : ∀ x, x ∈ Submodule.span 𝒜 (Set.range (pbwDivSymm R [j, i, j, i, j, i])) ↔
      op x ∈ G2Integral.orderedSpan q Λ (V 0) (V 1) (V 2) (V 3) (V 4) (V 5) := by
    intro x
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        rw [hmono]; exact G2Integral.M6_mem_orderedSpan _ _ _ _ _ _
      | zero => rw [op_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [op_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [laurent_smul_U, op_smul]
        exact G2Integral.smul_mem_orderedSpan (RingHom.mem_range.2 ⟨a, rfl⟩) hx
    · intro hx
      rw [← unop_op x]
      generalize op x = z at hx
      induction hx using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, a, b, c', d, l, m, rfl⟩ := hz
        obtain ⟨a', rfl⟩ := RingHom.mem_range.1 hc
        rw [unop_smul, ← laurent_smul_U, show
          unop (G2Integral.M6 q (V 0) (V 1) (V 2) (V 3) (V 4) (V 5) a b c' d l m) =
          pbwDivSymm R [j, i, j, i, j, i] ![m, l, d, c', b, a] by
            rw [← unop_op (pbwDivSymm R [j, i, j, i, j, i] _), hmono]; rfl]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      | zero => rw [unop_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [unop_add]; exact add_mem hx hy
      | neg x _ hx => rw [unop_neg]; exact neg_mem hx
  have hS : G2Integral.orderedSpan q Λ (V 0) (V 1) (V 2) (V 3) (V 4) (V 5) =
      (G2Integral.genRing q Λ (op (E R 𝕧 i)) (op (E R 𝕧 j))).toAddSubgroup := by
    rw [hV]
    exact orderedSpan_op_normalized hq0 (op (E R 𝕧 i)) (op (E R 𝕧 j)) hqi hpi
      (by rw [qSerre_op, hS4, op_zero, smul_zero])
      (by rw [qSerre_op, hS2, op_zero, smul_zero])
      (vd_pow_ne_one (D := D) ratFunc_X_not_root i) hqΛ hqΛ'
  have hgen : G2Integral.genRing q Λ (op (E R 𝕧 i)) (op (E R 𝕧 j)) =
      (G2Integral.genRing q Λ (E R 𝕧 i) (E R 𝕧 j)).op := by
    rw [G2Integral.genRing, G2Integral.genRing, Subring.op_closure]
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
  rw [hconv, hS, hgen]
  change x ∈ G2Integral.genRing q Λ (E R 𝕧 i) (E R 𝕧 j) ↔ x ∈ adjoinPair i j
  rw [← SetLike.mem_coe, ← coe_adjoinPair_eq_g2_genRing hd]
  rfl

include hij h h' in
/-- The local six-term braid move preserves the inverse integral divided PBW span. -/
theorem span_pbwDivSymm_g2_braid :
    Submodule.span 𝒜 (Set.range (pbwDivSymm R [i, j, i, j, i, j])) =
      Submodule.span 𝒜 (Set.range (pbwDivSymm R [j, i, j, i, j, i])) := by
  rw [span_pbwDivSymm_g2 hij h h', span_pbwDivSymm_g2_rev hij h h']

end Modified
end LieLean.QuantumGroup
