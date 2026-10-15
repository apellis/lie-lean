/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.CanonicalTriangular
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.ModifiedCanonical
import LieLean.LinearAlgebra.Basis.Unitriangular

/-!
# The canonical basis `Ḃ` of `U̇`

Over `ℚ(v)`, for a root datum with `hY` (dominant `λ` with all `⟨i, λ⟩` arbitrarily large),
[Lus] Thm. 25.2.1 (d): the elements `b ◇_ζ b''` (`ζ ∈ X`, `b, b'' ∈ B`) form a `ℚ(v)`-basis of `U̇`
and an `𝒜`-basis of `𝒜U̇`.

The proof follows Lusztig with the order of the factors exchanged: `b ◇_ζ b''` is
`b''⁻ b⁺ 1_ζ` plus an element of the span of the `b₂⁻ b₁⁺ 1_ζ` with `tr |b₁| < tr |b|` and
`tr |b₂| < tr |b''|` (`exists_modifiedCanonical_eq_triMul`; Lusztig uses `b⁺ b''⁻ 1_ζ`), so the
`b ◇_ζ b''` are unitriangular with respect to the triangular basis `b''⁻ 1_λ b⁺` of
[Lus] 23.2.1 (b) (`Modified.triangularBasisCanonical`). Integrality of the coefficients follows
from `b ◇_ζ b'' ∈ 𝒜U̇` and [Lus] 23.2.2 (b) (`Modified.aTriangularBasisCanonical`).

## Main results

* `exists_triAct_tensorCanonical_lead`: `(b ◇ b'')_{λ,λ''}` is the image of `y⁻x⁺(ξ_{-λ} ⊗ η_{λ''})`
  with `[y] ⊗ [x] = b'' ⊗ b` plus an element of lower degree in both factors.
* `exists_modifiedCanonical_eq_triMul`: the corresponding statement in `U̇` (cf. [Lus] 25.2.1 (e)).
* `modifiedCanonical_sub_mem_span`: unitriangularity with respect to the triangular basis.
* `Modified.modifiedCanonicalBasis`, `Modified.aModifiedCanonicalBasis`: **[Lus] Thm. 25.2.1 (d)**.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.2.1, 23.2.2, 23.3.1,
  24.3.3, 25.2.1.
-/

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF TensorProduct Modified

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### `y⁻x⁺(ξ ⊗ η)` lowers both degrees -/

section StrictDepth

local notation "fQ" => LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧

variable (Λ Λ'' : Y →+ ℤ)

local notation "mkT" =>
  TensorModule.mk (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ'')

local notation "tw" => ChevalleyTwist.toTwist R 𝕧 (VermaModule R 𝕧 Λ)

omit [Finite I] in
/-- `Eᵢ` lowers the degree. -/
lemma E_smul_mem_vermaDegSpan_succ (i : I) {d : ℕ} {p : VermaModule R 𝕧 Λ}
    (hp : p ∈ vermaDegSpan R 𝕧 Λ (d + 1)) : E R 𝕧 i • p ∈ vermaDegSpan R 𝕧 Λ d := by
  obtain ⟨y, hy, rfl⟩ := hp
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have hw' : w.length < d + 1 := hw
    exact vermaDegSpan_mono Λ (by omega) (E_smul_toVerma_monomial_mem_vermaDegSpan Λ i w)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ c hy

omit [Finite I] in
/-- `y⁻ (ʷp ⊗ η) = ʷp ⊗ y⁻η` modulo terms of lower degree in both factors, for `y = θ_w`. -/
lemma minusHom_monomial_smul_sub_mem_tensorDepth_succ (w : List I) {a : ℕ}
    {p : VermaModule R 𝕧 Λ} (hp : p ∈ vermaDegSpan R 𝕧 Λ (a + 1)) :
    minusHom R 𝕧 (monomial 𝕂 w) • mkT (tw p ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'') -
      mkT (tw p ⊗ₜ[𝕂] VermaModule.toVerma R 𝕧 Λ'' (monomial 𝕂 w)) ∈
      tensorDepth R Λ Λ'' a w.length := by
  induction w with
  | nil =>
    rw [monomial_nil, _root_.map_one, one_smul, VermaModule.toVerma_one, sub_self]
    exact zero_mem _
  | cons i w ih =>
    set b := VermaModule.toVerma R 𝕧 Λ'' (monomial 𝕂 w)
    have hb : b ∈ vermaDegSpan R 𝕧 Λ'' (w.length + 1) :=
      ⟨_, monomial_mem_degSpan (Nat.lt_succ_self _), rfl⟩
    have e' : F R 𝕧 i • tw p = tw (E R 𝕧 i • p) := by
      rw [ChevalleyTwist.smul_toTwist, chevalley_F]
    have e : minusHom R 𝕧 (monomial 𝕂 (i :: w)) •
          mkT (tw p ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'') -
        mkT (tw p ⊗ₜ[𝕂] VermaModule.toVerma R 𝕧 Λ'' (monomial 𝕂 (i :: w))) =
        F R 𝕧 i • (minusHom R 𝕧 (monomial 𝕂 w) •
          mkT (tw p ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'') - mkT (tw p ⊗ₜ[𝕂] b)) +
        mkT ((F R 𝕧 i • tw p) ⊗ₜ[𝕂] (K R 𝕧 (-ktilde R i) • b)) := by
      rw [smul_sub, TensorModule.F_smul_tmul, monomial_cons, _root_.map_mul, minusHom_θ,
        mul_smul, F_smul_toVerma, ← monomial_cons, map_add]
      abel
    rw [e, e', List.length_cons]
    exact add_mem (F_smul_mem_tensorDepth i ih)
      (tmul_mem_tensorDepth (E_smul_mem_vermaDegSpan_succ Λ i hp)
        (K_smul_mem_vermaDegSpan Λ'' _ hb))

omit [Finite I] in
/-- `triAct - triEquiv` lowers both degrees ([Lus] 23.3.1 (b)). -/
lemma triAct_sub_triEquiv_mem_tensorDepth_succ {a b : ℕ} {z : fQ ⊗[𝕂] fQ}
    (hz : z ∈ triDepth D (a + 1) (b + 1)) :
    triAct R hvn_ratFunc Λ Λ'' z - triEquiv R hvn_ratFunc Λ Λ'' z ∈ tensorDepth R Λ Λ'' a b := by
  have h : triDepth D (a + 1) (b + 1) ≤ (tensorDepth R Λ Λ'' a b).comap
      (triAct R hvn_ratFunc Λ Λ'' - (triEquiv R hvn_ratFunc Λ Λ'').toLinearMap) := by
    refine Submodule.map₂_le.2 fun p hp q hq ↦ ?_
    obtain ⟨y, hy, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := hq
    simp only [TensorProduct.mk_apply, Submodule.mem_comap, LinearMap.sub_apply,
      LinearEquiv.coe_coe, Submodule.mkQ_apply]
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      have hw' : w.length < b + 1 := hw
      rw [triEquiv_mk_tmul_mk]
      change (minusHom R 𝕧 (monomial 𝕂 w) * plusHom R 𝕧 x) • vermaTensorHwv R 𝕧 Λ Λ'' - _ ∈ _
      rw [mul_smul, plusHom_smul_vermaTensorHwv]
      exact tensorDepth_mono le_rfl (by omega)
        (minusHom_monomial_smul_sub_mem_tensorDepth_succ Λ Λ'' w ⟨x, hx, rfl⟩)
    | zero => simp
    | add y y' _ _ hy hy' =>
      rw [Submodule.Quotient.mk_add, add_tmul, map_add, map_add, add_sub_add_comm]
      exact add_mem hy hy'
    | smul c y _ hy =>
      rw [Submodule.Quotient.mk_smul, ← smul_tmul', map_smul, map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hy
  exact h hz

omit [Finite I] [DecidableEq I] in
lemma mem_degSpan_map_of_mem_Uw {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) :
    x ∈ (degSpan 𝕂 I (ν.degree + 1)).map (serreSubmodule D 𝕧).mkQ := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, weightSpace_le_degSpan (Nat.lt_succ_self _) hy, rfl⟩

end StrictDepth


/-! ### The leading term of `(b ◇ b'')_{λ,λ''}` -/

section Lead

local notation "fQ" => LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧

variable (R) in
/-- `ʷ(x⁻ξ) ⊗ y⁻η` in `ʷM_λ ⊗ M_{λ''}`. -/
def vermaTensorMinus (Λ Λ'' : Y →+ ℤ) (x y : Um D 𝕧) :
    TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ'') :=
  TensorModule.mk _ _ (ChevalleyTwist.toTwist R 𝕧 _ (vermaMinus R Λ x) ⊗ₜ[𝕂] vermaMinus R Λ'' y)

lemma triEquiv_tmul_eq_vermaTensorMinus (Λ Λ'' : Y →+ ℤ) (x y : Um D 𝕧) :
    triEquiv R hvn_ratFunc Λ Λ'' (y ⊗ₜ[𝕂] x) = vermaTensorMinus R Λ Λ'' x y := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [vermaTensorMinus, vermaMinus_mk, vermaMinus_mk]
  exact triEquiv_mk_tmul_mk Λ Λ'' y x

include hR in
/-- `(b ◇ b'')_{λ,λ''}` is the image of `ʷ(b⁻ξ) ⊗ b''⁻η` plus an element of degree `< tr |b|` in
the first factor and `< tr |b''|` in the second (from the triangularity [Lus] 24.3.3 (b)). -/
lemma exists_tensorIrrProj_lead (Λ Λ'' : Dom R) (h₀ : TensorIdx Λ Λ'') :
    ∃ m ∈ tensorDepth R Λ.1 Λ''.1 (hwbWt Λ h₀.1).degree (hwbWt Λ'' h₀.2).degree,
      tensorIrrProj Λ Λ'' (vermaTensorMinus R Λ.1 Λ''.1 h₀.1 h₀.2 + m) =
        tensorCanonical hR Λ Λ'' h₀ := by
  classical
  have hc₀ := repr_tensorCanonical_self hR Λ Λ'' h₀
  have he : ∀ h : TensorIdx Λ Λ'', tensorIrrProj Λ Λ'' (vermaTensorMinus R Λ.1 Λ''.1 h.1 h.2) =
      tensorBasisIdx hR Λ Λ'' h := fun h ↦ by
    rw [tensorBasisIdx_apply, tensorBasis_eq_tensorIrrProj hR Λ Λ'' h]
    rfl
  have hmem : h₀ ∈ ((tensorBasisIdx hR Λ Λ'').repr (tensorCanonical hR Λ Λ'' h₀)).support :=
    Finsupp.mem_support_iff.2 (by rw [hc₀]; exact one_ne_zero)
  refine ⟨∑ h ∈ ((tensorBasisIdx hR Λ Λ'').repr (tensorCanonical hR Λ Λ'' h₀)).support.erase h₀,
    (tensorBasisIdx hR Λ Λ'').repr (tensorCanonical hR Λ Λ'' h₀) h •
      vermaTensorMinus R Λ.1 Λ''.1 h.1 h.2,
    Submodule.sum_mem _ fun h hh ↦ Submodule.smul_mem _ _ ?_, ?_⟩
  · have hl := tensorLt_of_repr_tensorCanonical_ne_zero hR Λ Λ'' (Finset.ne_of_mem_erase hh)
      (Finsupp.mem_support_iff.1 (Finset.mem_of_mem_erase hh))
    exact tmul_mem_tensorDepth (vermaMinus_mem_vermaDegSpan _ hl.2.1 (mem_Uw_cbWt _))
      (vermaMinus_mem_vermaDegSpan _ hl.2.2 (mem_Uw_cbWt _))
  · rw [map_add, map_sum, he]
    simp only [map_smul, he]
    conv_rhs => rw [← (tensorBasisIdx hR Λ Λ'').linearCombination_repr
      (tensorCanonical hR Λ Λ'' h₀), Finsupp.linearCombination_apply, Finsupp.sum,
      ← Finset.add_sum_erase _ _ hmem, hc₀, one_smul]

include hR in
/-- `(b ◇ b'')_{λ,λ''} = y⁻x⁺(ξ_{-λ} ⊗ η_{λ''})` with `[y] ⊗ [x] = b'' ⊗ b + z`, `z` of degree
`< tr |b|` in the second factor and `< tr |b''|` in the first (cf. [Lus] 25.2.1 (e)). -/
lemma exists_triAct_tensorCanonical_lead (Λ Λ'' : Dom R) (h₀ : TensorIdx Λ Λ'') :
    ∃ z ∈ triDepth D (hwbWt Λ h₀.1).degree (hwbWt Λ'' h₀.2).degree,
      tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1
        ((h₀.2 : Um D 𝕧) ⊗ₜ[𝕂] (h₀.1 : Um D 𝕧) + z)) = tensorCanonical hR Λ Λ'' h₀ := by
  obtain ⟨m, hm, e⟩ := exists_tensorIrrProj_lead hR Λ Λ'' h₀
  have ht₀ : (h₀.2 : Um D 𝕧) ⊗ₜ[𝕂] (h₀.1 : Um D 𝕧) ∈
      triDepth D ((hwbWt Λ h₀.1).degree + 1) ((hwbWt Λ'' h₀.2).degree + 1) :=
    Submodule.apply_mem_map₂ _ (mem_degSpan_map_of_mem_Uw (mem_Uw_cbWt _))
      (mem_degSpan_map_of_mem_Uw (mem_Uw_cbWt _))
  obtain ⟨z, hz, ez⟩ := exists_triAct_eq Λ.1 Λ''.1 _ _
    (sub_mem hm (triAct_sub_triEquiv_mem_tensorDepth_succ Λ.1 Λ''.1 ht₀))
  refine ⟨z, hz, ?_⟩
  rw [map_add, ez, triEquiv_tmul_eq_vermaTensorMinus, ← e]
  congr 1
  abel

end Lead

/-! ### Unitriangularity -/

section Unitriangular

local notation "fQ" => LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧

/-- The weight of `b ∈ B` is the `ν` with `b ∈ f_ν`. -/
lemma cbWt_eq_of_mem_Uw (b : canonicalBasis D) {ν : I →₀ ℕ} (hb : (b : Um D 𝕧) ∈ Uw D 𝕧 ν) :
    cbWt D b = ν := by
  have hne : (b : Um D 𝕧) ≠ 0 := (linearIndependent_canonicalBasis D).ne_zero b
  have h1 := proj_of_mem_Uw hb (toZ (cbWt D b))
  rw [proj_of_mem_Uw (mem_Uw_cbWt b), ite_eq_left rfl] at h1
  split_ifs at h1 with h
  · ext i
    have := congrArg (· i) h
    simp only [toZ_apply, Nat.cast_inj] at this
    exact this.symm
  · exact absurd h1 hne

/-- The image in `f` of an element of `'f` of degree `< d` is a combination of the `b ∈ B` with
`tr |b| < d`. -/
lemma map_degSpan_le_span_canonicalBasis (d : ℕ) :
    (degSpan 𝕂 I d).map (serreSubmodule D 𝕧).mkQ ≤
      Submodule.span 𝕂 ((↑) '' {b : canonicalBasis D | (cbWt D b).degree < d}) := by
  rw [degSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hmem : (serreSubmodule D 𝕧).mkQ (monomial 𝕂 w) ∈ Uw D 𝕧 (wordWeight w) :=
    ⟨_, monomial_mem_weightSpace w, rfl⟩
  rw [← span_canonicalBasisAt] at hmem
  refine Submodule.span_mono ?_ hmem
  intro x hx
  have hxB : x ∈ canonicalBasis D := Set.mem_iUnion.2 ⟨_, hx⟩
  refine ⟨⟨x, hxB⟩, ?_, rfl⟩
  have hw' := cbWt_eq_of_mem_Uw ⟨x, hxB⟩
    (by rw [← span_canonicalBasisAt]; exact Submodule.subset_span hx)
  change (cbWt D ⟨x, hxB⟩).degree < d
  rw [hw', degree_wordWeight]
  exact hw

variable (R) in
/-- `(ζ, b, b'') ↦ (b'', ζ + |b|, b)`: the element `b''⁻ 1_{ζ+|b|} b⁺` of the triangular basis is
`b''⁻ b⁺ 1_ζ`. -/
def triangularIdxEquiv : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D ≃
    canonicalBasis D × (Y →+ ℤ) × canonicalBasis D where
  toFun t := (t.2.2, t.1 + cbRootWt D R t.2.1, t.2.1)
  invFun t := (t.2.1 - cbRootWt D R t.2.2, t.2.2, t.1)
  left_inv t := by simp
  right_inv t := by simp

variable (R) in
/-- The triangular basis of [Lus] 23.2.1 (b), indexed so that `(ζ, b, b'')` gives `b''⁻ b⁺ 1_ζ`. -/
def Modified.triangularBasisOne :
    Module.Basis ((Y →+ ℤ) × canonicalBasis D × canonicalBasis D) 𝕂 (Modified R 𝕧) :=
  (triangularBasisCanonical R).reindex (triangularIdxEquiv R).symm

lemma Modified.triangularBasisOne_apply (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    triangularBasisOne R t = triangularBasisCanonical R (t.2.2, t.1 + cbRootWt D R t.2.1, t.2.1) :=
  by rw [triangularBasisOne, Module.Basis.reindex_apply, Equiv.symm_symm]; rfl

/-- `b''⁻ b⁺ 1_ζ` is an element of the triangular basis. -/
lemma leftActOne_triMul_tmul (ζ : Y →+ ℤ) (b b'' : canonicalBasis D) :
    leftActOne R hvn_ratFunc ζ (triMul R hvn_ratFunc ((b'' : Um D 𝕧) ⊗ₜ[𝕂] (b : Um D 𝕧))) =
      triangularBasisOne R (ζ, b, b'') := by
  have e : triMul R hvn_ratFunc ((b'' : Um D 𝕧) ⊗ₜ[𝕂] (b : Um D 𝕧)) =
      (canonicalMinusBasis R b'' : QuantumGroup R 𝕧) * canonicalPlusBasis R b := by
    rw [canonicalMinusBasis_apply, canonicalPlusBasis_apply]
    rfl
  rw [e, leftActOne_eq_elt _
      (mul_mem_adWeightSpace (canonicalMinusBasis_mem b'') (canonicalPlusBasis_mem b)),
    triangularBasisOne_apply, triangularBasisCanonical_apply, triFun]
  dsimp only
  exact elt_index (by abel) (by abel) rfl _ _

/-- `y⁻x⁺1_ζ` with `[y] ⊗ [x] ∈ triDepth a c` is a combination of the `b₂⁻ b₁⁺ 1_ζ` with
`tr |b₁| < a` and `tr |b₂| < c`. -/
lemma leftActOne_triMul_mem_span (ζ : Y →+ ℤ) {a c : ℕ} {z : fQ ⊗[𝕂] fQ}
    (hz : z ∈ triDepth D a c) :
    leftActOne R hvn_ratFunc ζ (triMul R hvn_ratFunc z) ∈ Submodule.span 𝕂
      (triangularBasisOne R '' {t | t.1 = ζ ∧ (cbWt D t.2.1).degree < a ∧
        (cbWt D t.2.2).degree < c}) := by
  have h : triDepth D a c ≤ (Submodule.span 𝕂 (triangularBasisOne R '' {t | t.1 = ζ ∧
      (cbWt D t.2.1).degree < a ∧ (cbWt D t.2.2).degree < c})).comap
        (leftActOne R hvn_ratFunc ζ ∘ₗ triMul R hvn_ratFunc) := by
    refine (Submodule.map₂_le_map₂ (map_degSpan_le_span_canonicalBasis c)
      (map_degSpan_le_span_canonicalBasis a)).trans ?_
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b₂, hb₂, rfl⟩, _, ⟨b₁, hb₁, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨(ζ, b₁, b₂), ⟨rfl, hb₁, hb₂⟩, (leftActOne_triMul_tmul ζ b₁ b₂).symm⟩
  exact h hz

variable (hY : ∀ N : ℕ, ∃ Λ : Dom R, ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i))

include hR hY in
/-- `b ◇_ζ b'' = y⁻x⁺1_ζ` with `[y] ⊗ [x] = b'' ⊗ b + z`, `z` of degree `< tr |b|` in the second
factor and `< tr |b''|` in the first (our form of the triangularity in the proof of
[Lus] 25.2.1 (d)). -/
theorem exists_modifiedCanonical_eq_triMul (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) :
    ∃ z ∈ triDepth D (cbWt D ⟨b, hb⟩).degree (cbWt D ⟨b'', hb''⟩).degree,
      modifiedCanonical hR hY ζ hb hb'' =
        leftActOne R hvn_ratFunc ζ (triMul R hvn_ratFunc (b'' ⊗ₜ[𝕂] b + z)) := by
  obtain ⟨w, hw⟩ := modifiedCanonical_mem_range hR hY ζ hb hb''
  obtain ⟨z₁, hz₁⟩ := exists_leftActOne_eq_triMul hvn_ratFunc ζ w
  obtain ⟨n, hn⟩ := exists_mem_triDepth z₁
  set d₁ := (cbWt D ⟨b, hb⟩).degree
  set d₂ := (cbWt D ⟨b'', hb''⟩).degree
  set N := max n (max d₁ d₂ + 1)
  have hN : n ≤ N ∧ d₁ + 1 ≤ N ∧ d₂ + 1 ≤ N := by omega
  obtain ⟨Λ, Λ'', hζ, hΛ, hΛ''⟩ := exists_dom_pair hY ζ N
  have h₁ : b ∈ canonicalBasisHW D Λ :=
    mem_canonicalBasisHW_of_cbWt Λ hb fun i ↦ by have := hΛ i; omega
  have h₂ : b'' ∈ canonicalBasisHW D Λ'' :=
    mem_canonicalBasisHW_of_cbWt Λ'' hb'' fun i ↦ by have := hΛ'' i; omega
  obtain ⟨z, hz, ez⟩ := exists_triAct_tensorCanonical_lead hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩)
  have ez' : tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 (b'' ⊗ₜ[𝕂] b + z)) =
      tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩) := ez
  have hz' : z ∈ triDepth D d₁ d₂ := hz
  refine ⟨z, hz', ?_⟩
  have ht₀ : b'' ⊗ₜ[𝕂] b ∈ triDepth D (d₁ + 1) (d₂ + 1) :=
    Submodule.apply_mem_map₂ _ (mem_degSpan_map_of_mem_Uw (mem_Uw_cbWt ⟨b'', hb''⟩))
      (mem_degSpan_map_of_mem_Uw (mem_Uw_cbWt ⟨b, hb⟩))
  have hmem : z₁ - (b'' ⊗ₜ[𝕂] b + z) ∈ triDepth D N N :=
    sub_mem (triDepth_mono hN.1 hN.1 hn) (add_mem (triDepth_mono hN.2.1 hN.2.2 ht₀)
      (triDepth_mono (by omega) (by omega) hz'))
  have h0 := leftActOne_triMul_eq_zero hR Λ Λ'' hΛ hΛ'' hmem (by
    rw [map_sub, map_sub, ez', ← modTensorAct_leftActOne_triMul Λ Λ'' hζ, ← hz₁, hw,
      modTensorAct_modifiedCanonical hR hY ζ hb hb'' Λ Λ'' hζ h₁ h₂, sub_self])
  rw [hζ, map_sub, map_sub, sub_eq_zero, ← hz₁, hw] at h0
  exact h0

include hR hY in
/-- `b ◇_ζ b'' - b''⁻ b⁺ 1_ζ` is a combination of the `b₂⁻ b₁⁺ 1_ζ` with `tr |b₁| < tr |b|` and
`tr |b₂| < tr |b''|`. -/
theorem modifiedCanonical_sub_mem_span (ζ : Y →+ ℤ) (b b'' : canonicalBasis D) :
    modifiedCanonical hR hY ζ b.2 b''.2 - triangularBasisOne R (ζ, b, b'') ∈
      Submodule.span 𝕂 (triangularBasisOne R '' {t | t.1 = ζ ∧
        (cbWt D t.2.1).degree < (cbWt D b).degree ∧
          (cbWt D t.2.2).degree < (cbWt D b'').degree}) := by
  obtain ⟨z, hz, e⟩ := exists_modifiedCanonical_eq_triMul hR hY ζ b.2 b''.2
  rw [e, map_add, map_add, leftActOne_triMul_tmul, add_sub_cancel_left]
  exact leftActOne_triMul_mem_span ζ hz

end Unitriangular

/-! ### The canonical basis `Ḃ` of `U̇` -/

section Basis

variable (D) in
/-- `tr |b| + tr |b''|` for the index `(ζ, b, b'')`. -/
def Modified.canonicalPairDegree (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) : ℕ :=
  (cbWt D t.2.1).degree + (cbWt D t.2.2).degree

variable (hY : ∀ N : ℕ, ∃ Λ : Dom R, ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i))

include hR hY in
lemma modifiedCanonical_sub_mem_span_lt (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    modifiedCanonical hR hY t.1 t.2.1.2 t.2.2.2 - triangularBasisOne R t ∈
      Submodule.span 𝕂 (triangularBasisOne R ''
        {s | canonicalPairDegree D s < canonicalPairDegree D t}) := by
  refine Submodule.span_mono (Set.image_mono fun s hs ↦ ?_)
    (modifiedCanonical_sub_mem_span hR hY t.1 t.2.1 t.2.2)
  simp only [Set.mem_ofPred_eq, canonicalPairDegree] at hs ⊢
  omega

/-- **[Lus] Thm. 25.2.1 (d)**, over `ℚ(v)`: the elements `b ◇_ζ b''` (`ζ ∈ X`, `b, b'' ∈ B`) form a
`ℚ(v)`-basis of `U̇`. Lusztig assumes the root datum `Y`-regular; here `R.IsXRegular` and `hY` (see
`existsUnique_modifiedCanonical`). -/
def Modified.modifiedCanonicalBasis :
    Module.Basis ((Y →+ ℤ) × canonicalBasis D × canonicalBasis D) 𝕂 (Modified R 𝕧) :=
  (triangularBasisOne R).ofUnitriangular (modifiedCanonical_sub_mem_span_lt hR hY)

theorem Modified.modifiedCanonicalBasis_apply (ζ : Y →+ ℤ) (b b'' : canonicalBasis D) :
    modifiedCanonicalBasis hR hY (ζ, b, b'') = modifiedCanonical hR hY ζ b.2 b''.2 :=
  Module.Basis.ofUnitriangular_apply _ _ _

variable (R) in
/-- The triangular `𝒜`-basis of [Lus] 23.2.2 (b), indexed so that `(ζ, b, b'')` gives
`b''⁻ b⁺ 1_ζ`. -/
def Modified.aTriangularBasisOne :
    Module.Basis ((Y →+ ℤ) × canonicalBasis D × canonicalBasis D) 𝒜 (aForm R).toSubmodule :=
  (aTriangularBasisCanonical R).reindex (triangularIdxEquiv R).symm

lemma Modified.aTriangularBasisOne_apply (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    (aTriangularBasisOne R t : Modified R 𝕧) = triangularBasisOne R t := by
  rw [aTriangularBasisOne, Module.Basis.reindex_apply, aTriangularBasisCanonical_apply,
    triangularBasisOne, Module.Basis.reindex_apply]

/-- The `ℚ(v)`-coordinates of an element of `𝒜U̇` in the triangular basis are its
`𝒜`-coordinates. -/
lemma Modified.repr_triangularBasisOne_coe (x : (aForm R).toSubmodule)
    (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    (triangularBasisOne R).repr x t =
      LusztigF.integralLaurentEval ((aTriangularBasisOne R).repr x t) := by
  have hx : (x : Modified R 𝕧) = Finsupp.linearCombination 𝕂 (triangularBasisOne R)
      (((aTriangularBasisOne R).repr x).mapRange LusztigF.integralLaurentEval (map_zero _)) := by
    conv_lhs => rw [← (aTriangularBasisOne R).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Submodule.coe_smul, aTriangularBasisOne_apply, Modified.laurent_smul]
  rw [hx, Module.Basis.repr_linearCombination, Finsupp.mapRange_apply]

include hR hY in
lemma modifiedCanonical_sub_mem_aSpan_lt (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    (⟨modifiedCanonical hR hY t.1 t.2.1.2 t.2.2.2,
        modifiedCanonical_mem_aForm hR hY t.1 t.2.1.2 t.2.2.2⟩ : (aForm R).toSubmodule) -
      aTriangularBasisOne R t ∈ Submodule.span 𝒜 (aTriangularBasisOne R ''
        {s | canonicalPairDegree D s < canonicalPairDegree D t}) := by
  have h𝕂 := (triangularBasisOne R).mem_span_image.1 (modifiedCanonical_sub_mem_span_lt hR hY t)
  rw [Module.Basis.mem_span_image]
  intro s hs
  by_contra hst
  apply Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hs)
  apply LusztigF.integralLaurentEval_injective
  rw [map_zero, ← repr_triangularBasisOne_coe, Submodule.coe_sub, aTriangularBasisOne_apply]
  by_contra hne
  exact hst (h𝕂 (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne)))

/-- **[Lus] Thm. 25.2.1 (d)**, over `𝒜`: the elements `b ◇_ζ b''` (`ζ ∈ X`, `b, b'' ∈ B`) form an
`𝒜`-basis of `𝒜U̇`. -/
def Modified.aModifiedCanonicalBasis :
    Module.Basis ((Y →+ ℤ) × canonicalBasis D × canonicalBasis D) 𝒜 (aForm R).toSubmodule :=
  (aTriangularBasisOne R).ofUnitriangular (modifiedCanonical_sub_mem_aSpan_lt hR hY)

theorem Modified.aModifiedCanonicalBasis_apply (ζ : Y →+ ℤ) (b b'' : canonicalBasis D) :
    (aModifiedCanonicalBasis hR hY (ζ, b, b'') : Modified R 𝕧) =
      modifiedCanonical hR hY ζ b.2 b''.2 := by
  rw [aModifiedCanonicalBasis, Module.Basis.ofUnitriangular_apply]

end Basis

end LieLean.QuantumGroup
