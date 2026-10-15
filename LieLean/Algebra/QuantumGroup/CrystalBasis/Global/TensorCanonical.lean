/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorLattice
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.CanonicalFamily

/-!
# The canonical basis of `ʷL_q(λ) ⊗ L_q(λ')`

For dominant `λ, λ'`, Lusztig orders `B(λ) × B(λ')` by `(b₂, b₂') < (b₁, b₁')` iff
`tr |b₂| - tr |b₂'| = tr |b₁| - tr |b₁'|`, `tr |b₂| < tr |b₁|` and `tr |b₂'| < tr |b₁'|`
([Lus] 24.3.1), and applies Lemma 24.2.1 to the matrix `ρ` of `Ψ = Θ ∘ (¯ ⊗ ¯)` in the basis
`b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}` (24.3.2). The resulting family `π` gives elements
`(b₁ ◇ b₁')_{λ,λ'} = Σ π_{b₁,b₁';b₂,b₂'} b₂⁺ξ_{-λ} ⊗ b₂'⁻η_{λ'}` which are `Ψ`-invariant and
congruent to `b₁⁺ξ_{-λ} ⊗ b₁'⁻η_{λ'}` modulo `v⁻¹ℒ` ([Lus] Thm. 24.3.3 (a), (b)).

## Main definitions

* `TensorLt`: Lusztig's strict order on `B(λ) × B(λ')`.
* `TensorIdx`: `B(λ) × B(λ')` with the opposite of Lusztig's order, the poset `H` to which
  Lemma 24.2.1 is applied.
* `tensorRho`: the coefficients `ρ` as Laurent polynomials; `tensorPi`: the family `π`.
* `tensorLat`: Lusztig's `ℒ`, the `ℤ[v⁻¹]`-span of the basis, described by coordinates.
* `tensorCanonical`: the element `(b₁ ◇ b₁')_{λ,λ'}`.

## Main results

* `isLusztigMatrix_tensorRho`: `ρ` satisfies the hypotheses of Lemma 24.2.1 (24.3.2).
* `existsUnique_tensorCanonical`: [Lus] Thm. 24.3.3 (a).
* `repr_tensorCanonical_self`, `tensorLt_of_repr_tensorCanonical_ne_zero`,
  `isNegLaurent_repr_tensorCanonical`: [Lus] Thm. 24.3.3 (b).

## Implementation notes

Lusztig assumes the root datum `Y`-regular; as for `B(λ)` (`canonicalBasisHWBasis`), we work with
`X`-regular root data. Lusztig deduces uniqueness in (a) from (d); we prove it directly by the
same maximal-coefficient argument, which only uses the triangularity of `Ψ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 24.2.1, 24.3.1–24.3.3.
-/

open scoped RatFunc
open TensorProduct LaurentPolynomial

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-! ### `v⁻¹ℤ[v⁻¹]` inside `ℚ(v)` -/

/-- `c ∈ v⁻¹ℤ[v⁻¹]`. -/
def IsNegLaurent (c : 𝕂) : Prop := ∃ a : LaurentPolynomial ℤ, a.IsNeg ∧ integralLaurentEval a = c

lemma isNegLaurent_zero : IsNegLaurent 0 := ⟨0, isNeg_zero, map_zero _⟩

lemma IsNegLaurent.add {c d : 𝕂} (hc : IsNegLaurent c) (hd : IsNegLaurent d) :
    IsNegLaurent (c + d) := by
  obtain ⟨a, ha, rfl⟩ := hc
  obtain ⟨b, hb, rfl⟩ := hd
  exact ⟨a + b, ha.add hb, map_add _ _ _⟩

lemma IsNegLaurent.sub {c d : 𝕂} (hc : IsNegLaurent c) (hd : IsNegLaurent d) :
    IsNegLaurent (c - d) := by
  obtain ⟨a, ha, rfl⟩ := hc
  obtain ⟨b, hb, rfl⟩ := hd
  exact ⟨a - b, ha.sub hb, map_sub _ _ _⟩

lemma IsNegLaurent.neg {c : 𝕂} (hc : IsNegLaurent c) : IsNegLaurent (-c) := by
  simpa using isNegLaurent_zero.sub hc

/-- An element of `v⁻¹ℤ[v⁻¹]` fixed by the bar involution is zero. -/
lemma IsNegLaurent.eq_zero_of_bar_eq {c : 𝕂} (hc : IsNegLaurent c) (h : RatFunc.bar c = c) :
    c = 0 := by
  obtain ⟨a, ha, rfl⟩ := hc
  rw [bar_integralLaurentEval] at h
  rw [ha.eq_zero_of_invert_eq (integralLaurentEval_injective h), map_zero]

lemma isNegLaurent_inv_X_mul {a : LaurentPolynomial ℤ} (ha : a.IsNeg) :
    IsNegLaurent (𝕧⁻¹ * integralLaurentEval a) := by
  refine ⟨T (-1) * a, fun n hn ↦ ?_, ?_⟩
  · rw [coeff_T_mul]
    exact ha _ (by omega)
  · rw [map_mul, integralLaurentEval_T, zpow_neg_one]

lemma isNegLaurent_inv_X : IsNegLaurent 𝕧⁻¹ := by
  refine ⟨T (-1), fun n hn ↦ ?_, by rw [integralLaurentEval_T, zpow_neg_one]⟩
  rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne (by omega)]

variable {I : Type u} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### Lusztig's order on `B(λ) × B(λ')` -/

section Order

lemma exists_negGlobal_eq_word (ν : I →₀ ℕ) (β : negCrystal D ν) :
    ∃ w : List I, w.length = ν.degree ∧
      negGlobal D ν β = negGlobal D (wordWeight w) ⟦⟨w, rfl⟩⟧ := by
  obtain ⟨⟨w, hw⟩, rfl⟩ := Quotient.exists_rep β
  subst hw
  exact ⟨w, (GrandLoop.degree_wordWeight w).symm, rfl⟩

variable (D) in
/-- There are finitely many `b ∈ B` with `tr |b| ≤ N`. -/
lemma finite_setOf_degree_cbWt_le (N : ℕ) :
    {b : canonicalBasis D | (cbWt D b).degree ≤ N}.Finite := by
  have hfin : {w : List I | w.length ≤ N}.Finite := List.finite_length_le I N
  refine ((hfin.image fun w ↦ negGlobal D (wordWeight w) ⟦⟨w, rfl⟩⟧).preimage
    Subtype.val_injective.injOn).subset fun b hb ↦ ?_
  obtain ⟨β, hβ⟩ := ((mem_canonicalBasis_iff D).1 b.2).choose_spec
  obtain ⟨w, hw, he⟩ := exists_negGlobal_eq_word (cbWt D b) β
  exact ⟨w, hw.le.trans hb, he.symm.trans hβ.symm⟩

variable (Λ Λ' : Dom R)

/-- There are finitely many `b ∈ B(λ)` with `tr |b| ≤ N`. -/
lemma finite_setOf_degree_hwbWt_le (N : ℕ) :
    {b : canonicalBasisHW D Λ | (hwbWt Λ b).degree ≤ N}.Finite :=
  (finite_setOf_degree_cbWt_le D N).preimage
    (f := fun b : canonicalBasisHW D Λ ↦ (⟨b, canonicalBasisHW_subset D Λ b.2⟩ : canonicalBasis D))
    (by intro x _ y _ h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)

/-- **[Lus] 24.3.1**: Lusztig's strict order, `(b₂, b₂') < (b₁, b₁')` iff
`tr |b₂| - tr |b₂'| = tr |b₁| - tr |b₁'|`, `tr |b₂| < tr |b₁|` and `tr |b₂'| < tr |b₁'|`. -/
def TensorLt (h₂ h₁ : canonicalBasisHW D Λ × canonicalBasisHW D Λ') : Prop :=
  ((hwbWt Λ h₂.1).degree : ℤ) - (hwbWt Λ' h₂.2).degree =
      ((hwbWt Λ h₁.1).degree : ℤ) - (hwbWt Λ' h₁.2).degree ∧
    (hwbWt Λ h₂.1).degree < (hwbWt Λ h₁.1).degree ∧
    (hwbWt Λ' h₂.2).degree < (hwbWt Λ' h₁.2).degree

variable {Λ Λ'}

lemma TensorLt.ne {h₂ h₁ : canonicalBasisHW D Λ × canonicalBasisHW D Λ'}
    (h : TensorLt Λ Λ' h₂ h₁) : h₂ ≠ h₁ := by
  rintro rfl
  exact lt_irrefl _ h.2.1

lemma TensorLt.trans {h₃ h₂ h₁ : canonicalBasisHW D Λ × canonicalBasisHW D Λ'}
    (h : TensorLt Λ Λ' h₃ h₂) (h' : TensorLt Λ Λ' h₂ h₁) : TensorLt Λ Λ' h₃ h₁ :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

lemma TensorLt.asymm {h₂ h₁ : canonicalBasisHW D Λ × canonicalBasisHW D Λ'}
    (h : TensorLt Λ Λ' h₂ h₁) : ¬ TensorLt Λ Λ' h₁ h₂ :=
  fun h' ↦ lt_asymm h.2.1 h'.2.1

/-- The relation `≺` of `TensorLower` refines Lusztig's order. -/
lemma TensorLower.tensorLt {h₂ h₁ : canonicalBasisHW D Λ × canonicalBasisHW D Λ'}
    (h : TensorLower Λ Λ' h₂ h₁) : TensorLt Λ Λ' h₂ h₁ := by
  obtain ⟨ν, hν, e₁, e₂⟩ := h
  have hpos : 0 < ν.degree := by
    rw [Nat.pos_iff_ne_zero, Ne, Finsupp.degree_eq_zero_iff]
    exact hν
  unfold TensorLt
  rw [e₁, e₂, map_add, map_add]
  refine ⟨by push_cast; ring, by omega, by omega⟩

variable (Λ Λ')

/-- `B(λ) × B(λ')` with the opposite of Lusztig's order of [Lus] 24.3.1: `h ≤ h'` iff
`h' ≤ h` for Lusztig. This is the poset `H` of [Lus] 24.3.2, so that `π_{h,h'}` is defined for
`h ≤ h'`. -/
def TensorIdx : Type _ := canonicalBasisHW D Λ × canonicalBasisHW D Λ'

instance : PartialOrder (TensorIdx Λ Λ') where
  le h h' := h = h' ∨ TensorLt Λ Λ' h' h
  le_refl _ := Or.inl rfl
  le_trans := by
    rintro a b c (rfl | hab) (rfl | hbc)
    · exact Or.inl rfl
    · exact Or.inr hbc
    · exact Or.inr hab
    · exact Or.inr (hbc.trans hab)
  le_antisymm := by
    rintro a b (rfl | hab) (h | hba)
    · rfl
    · rfl
    · exact h.symm
    · exact absurd hba hab.asymm

lemma tensorIdx_le_iff {h h' : TensorIdx Λ Λ'} : h ≤ h' ↔ h = h' ∨ TensorLt Λ Λ' h' h := Iff.rfl

lemma finite_setOf_le (h : TensorIdx Λ Λ') : {h' : TensorIdx Λ Λ' | h ≤ h'}.Finite := by
  refine ((finite_setOf_degree_hwbWt_le Λ (hwbWt Λ h.1).degree).prod
    (finite_setOf_degree_hwbWt_le Λ' (hwbWt Λ' h.2).degree)).subset ?_
  rintro h' (rfl | hh)
  · exact ⟨show (hwbWt Λ h.1).degree ≤ _ from le_rfl, show (hwbWt Λ' h.2).degree ≤ _ from le_rfl⟩
  · exact Set.mem_prod.2 ⟨hh.2.1.le, hh.2.2.le⟩

instance : LocallyFiniteOrder (TensorIdx Λ Λ') :=
  LocallyFiniteOrder.ofFiniteIcc fun a _ ↦ (finite_setOf_le Λ Λ' a).subset fun _ hx ↦ hx.1

instance : DecidableRel (α := TensorIdx Λ Λ') (· ≤ ·) := Classical.decRel _

end Order

/-! ### The matrix `ρ` and the family `π` -/

section Family

variable (Λ Λ' : Dom R)

/-- The basis `tensorBasis`, indexed by `TensorIdx`. -/
def tensorBasisIdx : Module.Basis (TensorIdx Λ Λ') 𝕂 (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :=
  tensorBasis hR Λ Λ'

lemma tensorBasisIdx_apply (h : TensorIdx Λ Λ') :
    tensorBasisIdx hR Λ Λ' h = tensorBasis hR Λ Λ' h :=
  rfl

lemma repr_tensorPsi_tensorBasisIdx_self (h : TensorIdx Λ Λ') :
    (tensorBasisIdx hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasisIdx hR Λ Λ' h)) h = 1 :=
  repr_tensorPsi_self hR Λ Λ' h

/-- The coefficient `ρ_{h;h'}` of `b'⁺ξ_{-λ} ⊗ b''⁻η_{λ'}` (`h' = (b', b'')`) in `Ψ(e_h)`, as a
Laurent polynomial ([Lus] 24.3.2). -/
def tensorRho (h h' : TensorIdx Λ Λ') : LaurentPolynomial ℤ :=
  (isLaurent_repr_tensorPsi hR Λ Λ' h h').choose

lemma integralLaurentEval_tensorRho (h h' : TensorIdx Λ Λ') :
    integralLaurentEval (tensorRho hR Λ Λ' h h') =
      (tensorBasisIdx hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasisIdx hR Λ Λ' h)) h' :=
  (isLaurent_repr_tensorPsi hR Λ Λ' h h').choose_spec

/-- The coefficients of `Ψ(z)`: `[e_j] Ψ(z) = Σ_k \bar{z_k} ρ_{k;j}`. -/
lemma repr_tensorPsi (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1)
    (j : TensorIdx Λ Λ') :
    (tensorBasisIdx hR Λ Λ').repr (tensorPsi hR Λ Λ' z) j =
      ∑ k ∈ ((tensorBasisIdx hR Λ Λ').repr z).support,
        RatFunc.bar ((tensorBasisIdx hR Λ Λ').repr z k) *
          (tensorBasisIdx hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasisIdx hR Λ Λ' k)) j := by
  conv_lhs => rw [← (tensorBasisIdx hR Λ Λ').linearCombination_repr z]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [tensorPsi_smul, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]

lemma repr_tensorPsi_eq_zero_of_not_le {h h' : TensorIdx Λ Λ'} (hh : ¬ h ≤ h') :
    (tensorBasisIdx hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasisIdx hR Λ Λ' h)) h' = 0 := by
  rw [tensorIdx_le_iff, not_or] at hh
  exact repr_tensorPsi_eq_zero hR Λ Λ' (Ne.symm hh.1) fun hl ↦ hh.2 hl.tensorLt

lemma tensorRho_eq_zero_of_not_le {h h' : TensorIdx Λ Λ'} (hh : ¬ h ≤ h') :
    tensorRho hR Λ Λ' h h' = 0 := by
  apply integralLaurentEval_injective
  rw [integralLaurentEval_tensorRho, map_zero, repr_tensorPsi_eq_zero_of_not_le hR Λ Λ' hh]

/-- Two finite sums agree if the summand vanishes outside their common part. -/
private lemma sum_eq_sum_of_vanish {α M : Type*} [AddCommMonoid M]
    {S T : Finset α} (f : α → M) (hS : ∀ x ∈ S, x ∉ T → f x = 0)
    (hT : ∀ x ∈ T, x ∉ S → f x = 0) : ∑ x ∈ S, f x = ∑ x ∈ T, f x := by
  classical
  calc ∑ x ∈ S, f x = ∑ x ∈ S ∪ T, f x := Finset.sum_subset Finset.subset_union_left
        fun x hx hxS ↦ hT x ((Finset.mem_union.1 hx).resolve_left hxS) hxS
    _ = ∑ x ∈ T, f x := (Finset.sum_subset Finset.subset_union_right
        fun x hx hxT ↦ hS x ((Finset.mem_union.1 hx).resolve_right hxT) hxT).symm

/-- **[Lus] 24.3.2**: `ρ` satisfies the hypotheses of Lemma 24.2.1: `ρ_{h;h} = 1` and
`Σ_{h''} \bar ρ_{h;h''} ρ_{h'';h'} = δ_{h,h'}` (from `Ψ² = 1`). -/
theorem isLusztigMatrix_tensorRho : IsLusztigMatrix (tensorRho hR Λ Λ') where
  self h := integralLaurentEval_injective (by
    rw [integralLaurentEval_tensorRho, map_one]; exact repr_tensorPsi_self hR Λ Λ' h)
  inv h h' hh := by
    classical
    apply integralLaurentEval_injective
    have hΨ : (tensorBasisIdx hR Λ Λ').repr (tensorPsi hR Λ Λ'
        (tensorPsi hR Λ Λ' (tensorBasisIdx hR Λ Λ' h))) h' =
        (tensorBasisIdx hR Λ Λ').repr (tensorBasisIdx hR Λ Λ' h) h' := by rw [tensorPsi_tensorPsi]
    rw [repr_tensorPsi, Module.Basis.repr_self] at hΨ
    rw [map_sum, apply_ite integralLaurentEval, map_one, map_zero]
    simp only [map_mul, ← bar_integralLaurentEval, integralLaurentEval_tensorRho]
    rw [← sum_eq_sum_of_vanish (S := ((tensorBasisIdx hR Λ Λ').repr
      (tensorPsi hR Λ Λ' (tensorBasisIdx hR Λ Λ' h))).support), hΨ, Finsupp.single_apply]
    · intro x _ hx
      rw [Finset.mem_Icc, not_and_or] at hx
      rcases hx with hx | hx
      · rw [repr_tensorPsi_eq_zero_of_not_le hR Λ Λ' hx, map_zero, zero_mul]
      · rw [repr_tensorPsi_eq_zero_of_not_le hR Λ Λ' hx, mul_zero]
    · intro x _ hx
      rw [Finsupp.notMem_support_iff.1 hx, map_zero, zero_mul]

/-- The family `π` of [Lus] 24.3.2, given by Lemma 24.2.1. -/
def tensorPi (h h' : TensorIdx Λ Λ') : LaurentPolynomial ℤ := lusztigFamily (tensorRho hR Λ Λ') h h'

lemma isLusztigFamily_tensorPi : IsLusztigFamily (tensorRho hR Λ Λ') (tensorPi hR Λ Λ') :=
  isLusztigFamily_lusztigFamily (isLusztigMatrix_tensorRho hR Λ Λ')

end Family

/-! ### The canonical basis -/

section Canonical

variable (Λ Λ' : Dom R)

/-- Lusztig's `ℒ`, the `ℤ[v⁻¹]`-span of the basis `b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}` ([Lus] 24.3.1): the
vectors whose coordinates lie in `ℤ[v⁻¹]`, i.e. `v⁻¹ z_h ∈ v⁻¹ℤ[v⁻¹]`. -/
def tensorLat : AddSubgroup (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) where
  carrier := {z | ∀ h, IsNegLaurent (𝕧⁻¹ * (tensorBasisIdx hR Λ Λ').repr z h)}
  add_mem' hz hz' h := by rw [map_add, Finsupp.add_apply, mul_add]; exact (hz h).add (hz' h)
  zero_mem' h := by rw [map_zero, Finsupp.zero_apply, mul_zero]; exact isNegLaurent_zero
  neg_mem' hz h := by rw [map_neg, Finsupp.neg_apply, mul_neg]; exact (hz h).neg

lemma mem_tensorLat_iff {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} :
    z ∈ tensorLat hR Λ Λ' ↔ ∀ h, IsNegLaurent (𝕧⁻¹ * (tensorBasisIdx hR Λ Λ').repr z h) := Iff.rfl

/-- `z ∈ v⁻¹ℒ` iff all coordinates of `z` lie in `v⁻¹ℤ[v⁻¹]`. -/
lemma smul_mem_tensorLat_iff {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} :
    𝕧 • z ∈ tensorLat hR Λ Λ' ↔ ∀ h, IsNegLaurent ((tensorBasisIdx hR Λ Λ').repr z h) := by
  simp only [mem_tensorLat_iff, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (NeZero.ne 𝕧), one_mul]

/-- The coordinates of `(b₁ ◇ b₁')_{λ,λ'}`: `π_{h;h'}` for `h' ≤ h` in Lusztig's order. -/
def tensorCanonicalRepr (h : TensorIdx Λ Λ') :
    TensorIdx Λ Λ' →₀ 𝕂 :=
  Finsupp.ofSupportFinite
    (fun h' : TensorIdx Λ Λ' ↦
      if h ≤ h' then integralLaurentEval (tensorPi hR Λ Λ' h h') else 0)
    ((finite_setOf_le Λ Λ' h).subset fun _ hh' ↦ by_contra fun hn ↦ hh' (ite_eq_right hn))

/-- **[Lus] 24.3.3**: the element `(b₁ ◇ b₁')_{λ,λ'} = Σ π_{b₁,b₁';b₂,b₂'} b₂⁺ξ_{-λ} ⊗ b₂'⁻η_{λ'}`
for `h = (b₁, b₁')`. -/
def tensorCanonical (h : TensorIdx Λ Λ') : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1 :=
  (tensorBasisIdx hR Λ Λ').repr.symm (tensorCanonicalRepr hR Λ Λ' h)

lemma repr_tensorCanonical (h h' : TensorIdx Λ Λ') :
    (tensorBasisIdx hR Λ Λ').repr (tensorCanonical hR Λ Λ' h) h' =
      if h ≤ h' then integralLaurentEval (tensorPi hR Λ Λ' h h') else 0 := by
  rw [tensorCanonical, LinearEquiv.apply_symm_apply, tensorCanonicalRepr,
    Finsupp.ofSupportFinite_coe]

/-- **[Lus] 24.3.3 (b)**: the coefficient of `b₁⁺ξ_{-λ} ⊗ b₁'⁻η_{λ'}` is `1`. -/
theorem repr_tensorCanonical_self (h : TensorIdx Λ Λ') :
    (tensorBasisIdx hR Λ Λ').repr (tensorCanonical hR Λ Λ' h) h = 1 := by
  classical
  rw [repr_tensorCanonical, ite_eq_left le_rfl, (isLusztigFamily_tensorPi hR Λ Λ').self, map_one]

/-- **[Lus] 24.3.3 (b)**: the other coefficients vanish unless `(b₂, b₂') < (b₁, b₁')`. -/
theorem tensorLt_of_repr_tensorCanonical_ne_zero {h h' : TensorIdx Λ Λ'} (hne : h' ≠ h)
    (h0 : (tensorBasisIdx hR Λ Λ').repr (tensorCanonical hR Λ Λ' h) h' ≠ 0) :
    TensorLt Λ Λ' h' h := by
  classical
  rw [repr_tensorCanonical] at h0
  by_cases hh : h ≤ h'
  · exact (hh.resolve_left hne.symm)
  · exact absurd (ite_eq_right hh) h0

/-- **[Lus] 24.3.3 (b)**: the other coefficients lie in `v⁻¹ℤ[v⁻¹]`. -/
theorem isNegLaurent_repr_tensorCanonical {h h' : TensorIdx Λ Λ'} (hne : h' ≠ h) :
    IsNegLaurent ((tensorBasisIdx hR Λ Λ').repr (tensorCanonical hR Λ Λ' h) h') := by
  classical
  rw [repr_tensorCanonical]
  split_ifs with hh
  · exact ⟨_, (isLusztigFamily_tensorPi hR Λ Λ').isNeg h h' (lt_of_le_of_ne hh hne.symm), rfl⟩
  · exact isNegLaurent_zero

/-- **[Lus] 24.3.3 (a)**: `Ψ((b₁ ◇ b₁')_{λ,λ'}) = (b₁ ◇ b₁')_{λ,λ'}`. -/
theorem tensorPsi_tensorCanonical (h : TensorIdx Λ Λ') :
    tensorPsi hR Λ Λ' (tensorCanonical hR Λ Λ' h) = tensorCanonical hR Λ Λ' h := by
  classical
  refine (tensorBasisIdx hR Λ Λ').ext_elem fun j ↦ ?_
  rw [repr_tensorPsi]
  set c := (tensorBasisIdx hR Λ Λ').repr (tensorCanonical hR Λ Λ' h)
  by_cases hj : h ≤ (j : TensorIdx Λ Λ')
  · rw [repr_tensorCanonical, ite_eq_left hj,
      (isLusztigFamily_tensorPi hR Λ Λ').eq_sum h j hj, map_sum]
    refine sum_eq_sum_of_vanish _ (fun x hx hxI ↦ ?_) (fun x hx hxS ↦ ?_) |>.trans
      (Finset.sum_congr rfl fun x hx ↦ ?_)
    · have hhx : h ≤ (x : TensorIdx Λ Λ') := by
        by_contra hn
        exact Finsupp.mem_support_iff.1 hx (by rw [repr_tensorCanonical, ite_eq_right hn])
      rw [Finset.mem_Icc, not_and] at hxI
      rw [repr_tensorPsi_eq_zero_of_not_le hR Λ Λ' (hxI hhx), mul_zero]
    · rw [Finsupp.notMem_support_iff.1 hxS, map_zero, zero_mul]
    · rw [map_mul, integralLaurentEval_tensorRho, ← bar_integralLaurentEval,
        repr_tensorCanonical, ite_eq_left (Finset.mem_Icc.1 hx).1]
  · rw [repr_tensorCanonical, ite_eq_right hj]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hhx : h ≤ (x : TensorIdx Λ Λ') := by
      by_contra hn
      exact Finsupp.mem_support_iff.1 hx (by rw [repr_tensorCanonical, ite_eq_right hn])
    rw [repr_tensorPsi_eq_zero_of_not_le hR Λ Λ' fun hxj ↦ hj (hhx.trans hxj), mul_zero]

/-- Uniqueness in [Lus] 24.3.3 (a): a `Ψ`-invariant element of `v⁻¹ℒ` is zero. -/
theorem eq_zero_of_tensorPsi_eq {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1}
    (hz : tensorPsi hR Λ Λ' z = z) (hneg : 𝕧 • z ∈ tensorLat hR Λ Λ') : z = 0 := by
  classical
  rw [smul_mem_tensorLat_iff] at hneg
  by_contra hne
  set s := ((tensorBasisIdx hR Λ Λ').repr z).support
  have hs : s.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun e ↦ hne ((tensorBasisIdx hR Λ Λ').repr.map_eq_zero_iff.1 e)
  obtain ⟨j, hj⟩ := s.exists_minimal hs
  have key : (tensorBasisIdx hR Λ Λ').repr (tensorPsi hR Λ Λ' z) j =
      (tensorBasisIdx hR Λ Λ').repr z j := by rw [hz]
  rw [repr_tensorPsi, Finset.sum_eq_single_of_mem j hj.1,
    repr_tensorPsi_tensorBasisIdx_self, mul_one] at key
  · exact Finsupp.mem_support_iff.1 hj.1 ((hneg j).eq_zero_of_bar_eq key)
  · intro k hk hkj
    by_cases hkj' : k ≤ (j : TensorIdx Λ Λ')
    · exact absurd (le_antisymm (hj.2 hk hkj') hkj').symm hkj
    · rw [repr_tensorPsi_eq_zero_of_not_le hR Λ Λ' hkj', mul_zero]

/-- **[Lus] Thm. 24.3.3 (a)**: for `h = (b₁, b₁') ∈ B(λ) × B(λ')` there is a unique `x ∈ ℒ` with
`Ψ(x) = x` and `x - b₁⁺ξ_{-λ} ⊗ b₁'⁻η_{λ'} ∈ v⁻¹ℒ`, namely `(b₁ ◇ b₁')_{λ,λ'}`. -/
theorem existsUnique_tensorCanonical (h : TensorIdx Λ Λ') :
    ∃! x, x ∈ tensorLat hR Λ Λ' ∧ tensorPsi hR Λ Λ' x = x ∧
      𝕧 • (x - tensorBasisIdx hR Λ Λ' h) ∈ tensorLat hR Λ Λ' := by
  classical
  have hneg : 𝕧 • (tensorCanonical hR Λ Λ' h - tensorBasisIdx hR Λ Λ' h) ∈ tensorLat hR Λ Λ' := by
    rw [smul_mem_tensorLat_iff]
    intro h'
    rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hh : h = h'
    · subst hh
      rw [ite_eq_left rfl, repr_tensorCanonical_self, sub_self]
      exact isNegLaurent_zero
    · rw [ite_eq_right hh, sub_zero]
      exact isNegLaurent_repr_tensorCanonical hR Λ Λ' (Ne.symm hh)
  refine ⟨tensorCanonical hR Λ Λ' h, ⟨?_, tensorPsi_tensorCanonical hR Λ Λ' h, hneg⟩, ?_⟩
  · intro h'
    by_cases hh : h' = h
    · subst hh
      rw [repr_tensorCanonical_self, mul_one]
      exact isNegLaurent_inv_X
    · obtain ⟨a, ha, he⟩ := isNegLaurent_repr_tensorCanonical hR Λ Λ' hh
      rw [← he]
      exact isNegLaurent_inv_X_mul ha
  · rintro x ⟨-, hx, hx'⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_tensorPsi_eq hR Λ Λ' ?_ ?_
    · rw [map_sub, hx, tensorPsi_tensorCanonical]
    · have := sub_mem hx' hneg
      rwa [← smul_sub, sub_sub_sub_cancel_right] at this

end Canonical

end LieLean.QuantumGroup
