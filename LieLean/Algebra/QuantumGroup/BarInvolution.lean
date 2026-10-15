/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Triangular
import LieLean.Algebra.QuantumGroup.LusztigF.Bar

/-!
# The bar involution of `U`

Over `ℚ(v)` (`v = RatFunc.X`), Lusztig's bar involution of `U` ([Lus] 3.1.12) is the ring
automorphism with `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ`, `K_μ ↦ K_{-μ}`, which is semilinear for the coefficient
involution `v ↦ v⁻¹` of `ℚ(v)`.

We construct it with the universal property of `U`, as an algebra homomorphism from `U` to the
twist `BarTwist R` of `U`, the same ring with `ℚ(v)` acting through `v ↦ v⁻¹`.

## Main definitions and results

* `QuantumGroup.barHom`: the bar involution, as a ring homomorphism `U → U`.
* `QuantumGroup.barHom_E`, `barHom_F`, `barHom_K`, `barHom_smul`: its values on the generators
  and its semilinearity.
* `QuantumGroup.barHom_barHom`: it is an involution.
* `QuantumGroup.barHom_minusHom`, `barHom_plusHom`: it is compatible with the bar involution of
  `'f` along `x ↦ x⁻`, `x ↦ x⁺`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.1.12.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y)

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

/-- `U` with the scalars `ℚ(v)` acting through the bar involution `v ↦ v⁻¹`. -/
def BarTwist : Type _ := QuantumGroup R 𝕧

namespace BarTwist

instance : Ring (BarTwist R) := inferInstanceAs (Ring (QuantumGroup R 𝕧))

instance : Algebra 𝕂 (BarTwist R) :=
  RingHom.toAlgebra' ((algebraMap 𝕂 (QuantumGroup R 𝕧)).comp RatFunc.bar.toRingHom)
    fun c x ↦ Algebra.commutes (RatFunc.bar c) (show QuantumGroup R 𝕧 from x)

/-- The identity map `U → BarTwist R`. -/
def ofU : QuantumGroup R 𝕧 ≃+* BarTwist R := RingEquiv.refl (QuantumGroup R 𝕧)

@[simp] lemma ofU_symm_ofU (x : QuantumGroup R 𝕧) : (ofU R).symm (ofU R x) = x := rfl

lemma smul_ofU (c : 𝕂) (x : QuantumGroup R 𝕧) : c • ofU R x = ofU R (RatFunc.bar c • x) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

lemma qSerre_ofU (d n : ℕ) (a b : QuantumGroup R 𝕧) :
    qSerre (𝕧 ^ d) n (ofU R a) (ofU R b) = ofU R (qSerre (𝕧 ^ d) n a b) := by
  unfold qSerre
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, smul_ofU]
  congr 2
  simp only [map_mul, map_pow, map_neg, map_one, bar_qBinomial]

end BarTwist

open BarTwist

/-- `K_μ ↦ K_{-μ}`, as a monoid homomorphism into `BarTwist R`. -/
def barK : Multiplicative Y →* BarTwist R where
  toFun μ := ofU R (K R 𝕧 (-μ.toAdd))
  map_one' := by simp
  map_mul' μ ν := by rw [← map_mul, K_add]; simp [add_comm]

lemma bar_zpow_X (n : ℤ) : RatFunc.bar (𝕧 ^ n) = 𝕧 ^ (-n) := by
  rw [map_zpow₀, RatFunc.bar_X, inv_zpow']

lemma bar_relations : Relations R 𝕧 (fun i ↦ ofU R (E R 𝕧 i)) (fun i ↦ ofU R (F R 𝕧 i))
    (barK R) where
  K_mul_E μ i := by
    simp only [barK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, smul_ofU, ← map_mul,
      bar_zpow_X]
    rw [K_mul_E, map_neg]
  K_mul_F μ i := by
    simp only [barK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, smul_ofU, ← map_mul,
      bar_zpow_X]
    rw [K_mul_F, map_neg, neg_neg]
  E_mul_F i j := by
    simp only [barK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, ← map_mul, ← map_sub]
    rw [E_mul_F_sub]
    split_ifs
    · rw [smul_ofU]
      congr 1
      rw [map_inv₀, map_sub, map_inv₀, map_pow, RatFunc.bar_X, inv_pow, inv_inv,
        ← neg_sub (𝕧 ^ D.d i), inv_neg, neg_smul, ← smul_neg, neg_sub, Kt, neg_neg]
    · simp
  serre_E i j hij := by
    rw [qSerre_ofU, serre_E R 𝕧 hij, map_zero]
  serre_F i j hij := by
    rw [qSerre_ofU, serre_F R 𝕧 hij, map_zero]

/-- The bar involution of `U` ([Lus] 3.1.12) as an algebra homomorphism into the twist. -/
def barAlgHom : QuantumGroup R 𝕧 →ₐ[𝕂] BarTwist R := lift (bar_relations R)

/-- The bar involution of `U` ([Lus] 3.1.12): the ring endomorphism with `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ`,
`K_μ ↦ K_{-μ}`, semilinear for `v ↦ v⁻¹` (`barHom_smul`). -/
def barHom : QuantumGroup R 𝕧 →+* QuantumGroup R 𝕧 :=
  (ofU R).symm.toRingHom.comp (barAlgHom R).toRingHom

@[simp] theorem barHom_E (i : I) : barHom R (E R 𝕧 i) = E R 𝕧 i := by
  simp [barHom, barAlgHom]

@[simp] theorem barHom_F (i : I) : barHom R (F R 𝕧 i) = F R 𝕧 i := by
  simp [barHom, barAlgHom]

@[simp] theorem barHom_K (μ : Y) : barHom R (K R 𝕧 μ) = K R 𝕧 (-μ) := by
  simp [barHom, barAlgHom, barK]

theorem barHom_smul (c : 𝕂) (x : QuantumGroup R 𝕧) :
    barHom R (c • x) = RatFunc.bar c • barHom R x := by
  change (ofU R).symm (barAlgHom R (c • x)) = _
  rw [map_smul]
  change (ofU R).symm (c • ofU R ((ofU R).symm (barAlgHom R x))) = _
  rw [smul_ofU]
  rfl

theorem barHom_algebraMap (c : 𝕂) :
    barHom R (algebraMap 𝕂 _ c) = algebraMap 𝕂 _ (RatFunc.bar c) := by
  rw [Algebra.algebraMap_eq_smul_one, barHom_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

/-- The square of the bar involution, as an algebra homomorphism. -/
private def barSq : QuantumGroup R 𝕧 →ₐ[𝕂] QuantumGroup R 𝕧 where
  toRingHom := (barHom R).comp (barHom R)
  commutes' c := by simp [barHom_algebraMap]

/-- The bar involution of `U` is an involution. -/
@[simp] theorem barHom_barHom (x : QuantumGroup R 𝕧) : barHom R (barHom R x) = x := by
  have h : barSq R = AlgHom.id 𝕂 _ := by
    ext <;> simp [barSq]
  exact DFunLike.congr_fun h x

theorem barHom_minusHom (x : LusztigF 𝕂 I) :
    barHom R (minusHom R 𝕧 x) = minusHom R 𝕧 (LusztigF.bar x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, barHom_algebraMap, LusztigF.bar_algebraMap, AlgHom.commutes]
  | grade1 i =>
    have := LusztigF.bar_θ (K := ℚ) i
    simp only [LusztigF.θ] at this
    rw [this]
    simp [minusHom]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem barHom_plusHom (x : LusztigF 𝕂 I) :
    barHom R (plusHom R 𝕧 x) = plusHom R 𝕧 (LusztigF.bar x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, barHom_algebraMap, LusztigF.bar_algebraMap, AlgHom.commutes]
  | grade1 i =>
    have := LusztigF.bar_θ (K := ℚ) i
    simp only [LusztigF.θ] at this
    rw [this]
    simp [plusHom]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end LieLean.QuantumGroup
