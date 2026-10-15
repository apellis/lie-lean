/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorLattice
import LieLean.Algebra.QuantumGroup.Modified.IntegralBasisPBW
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWPreimage

/-!
# The triangular basis of `U̇` attached to the canonical basis of `f`

Over `ℚ(v)`, let `B` be the canonical basis of `f` ([Lus] 14.4). The elements `b⁺` (resp. `b⁻`),
`b ∈ B`, form a basis of `U⁺` (resp. `U⁻`) whose `𝒜`-span is `𝒜U⁺` (resp. `𝒜U⁻`). Hence the
elements `b⁻ 1_λ b'⁺` (`b, b' ∈ B`, `λ ∈ X`) form a `ℚ(v)`-basis of `U̇` ([Lus] 23.2.1 (b)) and an
`𝒜`-basis of `𝒜U̇` ([Lus] 23.2.2 (b)).

## Main definitions and results

* `QuantumGroup.canonicalBasisBasis`: `B` as a `ℚ(v)`-basis of `f` (`Um`).
* `QuantumGroup.canonicalPlusBasis`, `QuantumGroup.canonicalMinusBasis`: the bases `b⁺`, `b⁻` of
  `U⁺`, `U⁻`.
* `QuantumGroup.Modified.triangularBasisCanonical`: the `ℚ(v)`-basis `b⁻ 1_λ b'⁺` of `U̇`
  ([Lus] 23.2.1 (b)).
* `QuantumGroup.Modified.aTriangularBasisCanonical`: the same elements as an `𝒜`-basis of `𝒜U̇`
  ([Lus] 23.2.2 (b)).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.4, 23.2.1, 23.2.2.
-/

open TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X
attribute [local instance] Modified.laurentAlgebraK Modified.laurentAlgebraU
  Modified.laurentTowerU

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

variable (D) in
/-- The canonical basis `B` of `f` as a `ℚ(v)`-basis ([Lus] 14.4.3 (d)). -/
def canonicalBasisBasis : Module.Basis (canonicalBasis D) 𝕂 (Um D 𝕧) :=
  Module.Basis.mk (linearIndependent_canonicalBasis D)
    (by rw [Subtype.range_coe, span_canonicalBasis D])

@[simp] lemma canonicalBasisBasis_apply (b : canonicalBasis D) :
    canonicalBasisBasis D b = b :=
  Module.Basis.mk_apply _ _ _

omit [Finite I] in
lemma plusQ_mk (x : LusztigF 𝕂 I) :
    Modified.plusQ R hvn_ratFunc (Submodule.Quotient.mk x) = plusHom R 𝕧 x :=
  rfl

/-- `x ↦ x⁺` agrees with the positive embedding of the radical quotient. -/
lemma plusQ_eq_quotientPlus (x : Um D 𝕧) :
    Modified.plusQ R hvn_ratFunc x = quotientPlus R (negativeQuotientEquiv D x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

omit [Finite I] in
lemma plusQ_mem_adjoin (x : Um D 𝕧) :
    Modified.plusQ R hvn_ratFunc x ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [plusQ_mk, ← range_plusHom R 𝕧]
  exact ⟨x, rfl⟩

omit [Finite I] in
lemma plusQ_injective : Function.Injective (Modified.plusQ R hvn_ratFunc : Um D 𝕧 →ₗ[𝕂] _) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [plusQ_mk, plusHom_eq_zero_iff R 𝕧 hvn_ratFunc] at hx
  exact (Submodule.Quotient.mk_eq_zero _).2 (mem_serreSubmodule.2 hx)

omit [Finite I] in
lemma plusQ_mem_adWeightSpace {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) :
    Modified.plusQ R hvn_ratFunc x ∈ adWeightSpace R 𝕧 (R.rootSum ν) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact plusHom_mem_adWeightSpace hy

/-- `x⁺ ∈ 𝒜U⁺` for `x ∈ 𝒜f`. -/
lemma plusQ_mem_aPlus {x : Um D 𝕧} (hx : x ∈ negIntegral D) :
    Modified.plusQ R hvn_ratFunc x ∈ Modified.aPlus R := by
  have h : quotientPlusIntegral R (negativeQuotientEquiv D x) ∈
      Algebra.adjoin 𝒜 (⋃ i, Set.range (Modified.Ed R i)) := by
    rw [← map_quotientIntegralForm_plus]
    exact ⟨_, hx, rfl⟩
  rw [plusQ_eq_quotientPlus]
  change quotientPlusIntegral R (negativeQuotientEquiv D x) ∈ _
  generalize quotientPlusIntegral R (negativeQuotientEquiv D x) = z at h ⊢
  induction h using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, n, rfl⟩ := Set.mem_iUnion.1 hy
    simpa [Modified.ePow, Modified.Ed] using Modified.ePow_mem_aPlus (R := R) [(i, n)]
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one, Modified.laurent_smul_U]
    simpa using Modified.smul_mem_aPlus (R := R) ⟨a, rfl⟩ (Modified.ePow_mem_aPlus (R := R) [])
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact Modified.mul_mem_aPlus hy hz

/-- The `𝒜`-span of the `x⁺`, `x ∈ 𝒜f`, contains every `E_w`. -/
lemma ePow_mem_span_plusQ (w : List (I × ℕ)) :
    Modified.ePow R w ∈ Submodule.span 𝒜
      (Set.range fun b : canonicalBasis D ↦ Modified.plusQ R hvn_ratFunc (b : Um D 𝕧)) := by
  have hw : Modified.ePow R w ∈ Algebra.adjoin 𝒜 (⋃ i, Set.range (Modified.Ed R i)) := by
    rw [Modified.ePow]
    refine Subalgebra.list_prod_mem _ fun y hy ↦ ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
    exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨p.1, p.2, rfl⟩)
  rw [← map_quotientIntegralForm_plus] at hw
  obtain ⟨y, hy, e⟩ := hw
  have hy' : (negativeQuotientEquiv D).symm y ∈ negIntegral D := by
    change negativeQuotientEquiv D ((negativeQuotientEquiv D).symm y) ∈ quotientIntegralForm D
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  rw [← span_canonicalBasis_laurent] at hy'
  have key : ∀ x ∈ Submodule.span 𝒜 (canonicalBasis D), Modified.plusQ R hvn_ratFunc x ∈
      Submodule.span 𝒜
        (Set.range fun b : canonicalBasis D ↦ Modified.plusQ R hvn_ratFunc (b : Um D 𝕧)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
    | smul a x _ hx =>
      rw [laurent_smul_eq, map_smul, ← Modified.laurent_smul_U]
      exact Submodule.smul_mem _ a hx
  have := key _ hy'
  rw [plusQ_eq_quotientPlus, LinearEquiv.apply_symm_apply] at this
  rw [← e]
  exact this

variable (R) in
/-- `x ↦ x⁺`, `f ≃ U⁺`. -/
def plusQEquiv : Um D 𝕧 ≃ₗ[𝕂] Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).toSubmodule
      (Modified.plusQ R hvn_ratFunc) plusQ_mem_adjoin)
    ⟨fun _ _ h ↦ plusQ_injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      rw [← range_plusHom R 𝕧] at hx
      obtain ⟨y, rfl⟩ := hx
      exact ⟨Submodule.Quotient.mk y, rfl⟩⟩

variable (R) in
/-- The basis `b⁺`, `b ∈ B`, of `U⁺`. -/
def canonicalPlusBasis :
    Module.Basis (canonicalBasis D) 𝕂 (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))) :=
  (canonicalBasisBasis D).map (plusQEquiv R)

lemma canonicalPlusBasis_apply (b : canonicalBasis D) :
    (canonicalPlusBasis R b : QuantumGroup R 𝕧) = Modified.plusQ R hvn_ratFunc (b : Um D 𝕧) := by
  rw [canonicalPlusBasis, Module.Basis.map_apply, canonicalBasisBasis_apply]
  rfl

variable (R) in
/-- The basis `b⁻`, `b ∈ B`, of `U⁻`. -/
def canonicalMinusBasis :
    Module.Basis (canonicalBasis D) 𝕂 (Algebra.adjoin 𝕂 (Set.range (F R 𝕧))) :=
  (canonicalPlusBasis R).map (Modified.chevalleyPlusMinus R)

lemma canonicalMinusBasis_apply (b : canonicalBasis D) :
    (canonicalMinusBasis R b : QuantumGroup R 𝕧) = Modified.minusQ R hvn_ratFunc (b : Um D 𝕧) := by
  rw [canonicalMinusBasis, Module.Basis.map_apply, Modified.chevalleyPlusMinus_apply,
    canonicalPlusBasis_apply]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (b : Um D 𝕧)
  rw [← hx]
  exact chevalley_plusHom x

variable (D) in
/-- The weight `R.rootSum |b|` of `b⁺`. -/
abbrev cbRootWt (R : D.RootDatum Y) (b : canonicalBasis D) : Y →+ ℤ := R.rootSum (cbWt D b)

lemma canonicalPlusBasis_mem (b : canonicalBasis D) :
    (canonicalPlusBasis R b : QuantumGroup R 𝕧) ∈ adWeightSpace R 𝕧 (cbRootWt D R b) := by
  rw [canonicalPlusBasis_apply]
  exact plusQ_mem_adWeightSpace (mem_Uw_cbWt b)

lemma canonicalMinusBasis_mem (b : canonicalBasis D) :
    (canonicalMinusBasis R b : QuantumGroup R 𝕧) ∈ adWeightSpace R 𝕧 (-cbRootWt D R b) := by
  rw [canonicalMinusBasis, Module.Basis.map_apply, Modified.chevalleyPlusMinus_apply,
    ← Modified.wt_omegaAut (R := R)]
  exact Modified.map_mem_adWeightSpace (Modified.omegaAut R) (canonicalPlusBasis_mem b)

lemma canonicalPlusBasis_mem_aPlus (b : canonicalBasis D) :
    (canonicalPlusBasis R b : QuantumGroup R 𝕧) ∈ Modified.aPlus R := by
  rw [canonicalPlusBasis_apply]
  exact plusQ_mem_aPlus (negIntegral_of_mem_canonicalBasis b.2)

lemma ePow_mem_span_canonicalPlusBasis (w : List (I × ℕ)) :
    Modified.ePow R w ∈ Submodule.span 𝒜
      (Set.range fun b ↦ (canonicalPlusBasis R b : QuantumGroup R 𝕧)) := by
  simp_rw [canonicalPlusBasis_apply]
  exact ePow_mem_span_plusQ w

namespace Modified

variable (R) in
/-- **The triangular basis of `U̇` attached to `B`** ([Lus] 23.2.1 (b)): the elements
`b⁻ 1_λ b'⁺`, `b, b' ∈ B`, `λ ∈ X`, form a `ℚ(v)`-basis of `U̇`. -/
def triangularBasisCanonical :
    Module.Basis (canonicalBasis D × (Y →+ ℤ) × canonicalBasis D) 𝕂 (Modified R 𝕧) :=
  triangularBasis ratFunc_X_not_root (canonicalMinusBasis R) (canonicalPlusBasis R)
    (cbRootWt D R) (cbRootWt D R) canonicalMinusBasis_mem canonicalPlusBasis_mem

lemma triangularBasisCanonical_apply (t : canonicalBasis D × (Y →+ ℤ) × canonicalBasis D) :
    triangularBasisCanonical R t = triFun (canonicalMinusBasis R) (canonicalPlusBasis R)
      (cbRootWt D R) (cbRootWt D R) canonicalMinusBasis_mem canonicalPlusBasis_mem t :=
  triangularBasis_apply _ _ _ _ _ _ _ t

variable (R) in
/-- **The triangular `𝒜`-basis of `𝒜U̇` attached to `B`** ([Lus] 23.2.2 (b)): the elements
`b⁻ 1_λ b'⁺`, `b, b' ∈ B`, `λ ∈ X`, form an `𝒜`-basis of `𝒜U̇`. -/
def aTriangularBasisCanonical :
    Module.Basis (canonicalBasis D × (Y →+ ℤ) × canonicalBasis D) 𝒜 (aForm R).toSubmodule :=
  aTriangularBasis (canonicalMinusBasis R) (canonicalPlusBasis R) (cbRootWt D R) (cbRootWt D R)
    canonicalMinusBasis_mem canonicalPlusBasis_mem
    (fun b ↦ by
      rw [canonicalMinusBasis, Module.Basis.map_apply, chevalleyPlusMinus_apply]
      exact chevalley_mem_aMinus (canonicalPlusBasis_mem_aPlus b))
    canonicalPlusBasis_mem_aPlus
    (fun w b ↦ by
      rw [canonicalMinusBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
      have e : (chevalleyPlusMinus R).symm ⟨fPow R w, fPow_mem_minus w⟩ =
          ⟨ePow R w, ePow_mem_plus w⟩ := by
        rw [LinearEquiv.symm_apply_eq]
        apply Subtype.ext
        rw [chevalleyPlusMinus_apply]
        exact (chevalley_ePow w).symm
      rw [e]
      exact isLaurent_repr_of_mem_span _ (ePow_mem_span_canonicalPlusBasis w) b)
    (fun w b ↦ isLaurent_repr_of_mem_span _ (ePow_mem_span_canonicalPlusBasis w) b)

lemma aTriangularBasisCanonical_apply (t : canonicalBasis D × (Y →+ ℤ) × canonicalBasis D) :
    (aTriangularBasisCanonical R t : Modified R 𝕧) = triangularBasisCanonical R t := by
  rw [aTriangularBasisCanonical, aTriangularBasis_apply, triangularBasisCanonical_apply]

end Modified

end LieLean.QuantumGroup
