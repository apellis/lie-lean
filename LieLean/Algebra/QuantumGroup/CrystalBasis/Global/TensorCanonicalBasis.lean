/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorCanonical

/-!
# The canonical basis of `ʷL_q(λ) ⊗ L_q(λ')`: parts (c), (d) of [Lus] Thm. 24.3.3

The elements `(b₁ ◇ b₁')_{λ,λ'}` (`tensorCanonical`) form a `ℚ(v)`-basis of `ʷL_q(λ) ⊗ L_q(λ')`,
an `𝒜`-basis of `𝒜ℒ` and a `ℤ[v⁻¹]`-basis of `ℒ` ([Lus] 24.3.3 (c)), and the natural map
`ℒ ∩ Ψ(ℒ) → ℒ/v⁻¹ℒ` is an isomorphism ([Lus] 24.3.3 (d)). This is the canonical basis of
`ʷL_q(λ) ⊗ L_q(λ')` ([Lus] 24.3.4).

## Main definitions

* `IsIntInv c`: `c ∈ ℤ[v⁻¹]`.
* `tensorLatA`: Lusztig's `𝒜ℒ`, the `𝒜`-span of the basis `b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}`.
* `tensorLatNeg`: `v⁻¹ℒ`.
* `tensorCanonicalBasis`: the canonical basis, as a `ℚ(v)`-basis.
* `tensorLatResidue`: the natural map `ℒ ∩ Ψ(ℒ) → ℒ/v⁻¹ℒ`.

## Main results

* `tensorCanonicalBasis_apply`, `mem_tensorLatA_iff`, `mem_tensorLat_iff_canonical`:
  [Lus] Thm. 24.3.3 (c). Since the `(b₁ ◇ b₁')` form a `ℚ(v)`-basis, being an `𝒜`-basis of `𝒜ℒ`
  (resp. a `ℤ[v⁻¹]`-basis of `ℒ`) says exactly that `𝒜ℒ` (resp. `ℒ`) consists of the vectors
  whose coordinates in this basis lie in `𝒜` (resp. `ℤ[v⁻¹]`).
* `bijective_tensorLatResidue`: [Lus] Thm. 24.3.3 (d).

## Proof

As Lusztig says, (c) and (d) are clear from the triangularity (b). We write it out: an element of
`ℒ` (resp. `𝒜ℒ`, resp. the whole space) is reduced to zero by subtracting multiples of the
`(b ◇ b')` at a maximal coordinate, with an induction on the size of the set of pairs below its
support. For (d), an element of `ℒ ∩ Ψ(ℒ)` has coordinates in `ℤ[v⁻¹] ∩ ℤ[v] = ℤ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 24.3.1–24.3.4.
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

/-! ### `ℤ[v⁻¹]` inside `ℚ(v)` -/

section Scalars

lemma isNeg_T_one_mul_mul {f g : LaurentPolynomial ℤ} (hf : f.IsNeg) (hg : g.IsNeg) :
    (T 1 * (f * g)).IsNeg := by
  classical
  intro n hn
  rw [coeff_T_mul, AddMonoidAlgebra.coeff_mul, Finsupp.sum]
  refine Finset.sum_eq_zero fun a ha ↦ ?_
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun b hb ↦ ite_eq_right fun hab ↦ ?_
  have ha' : a < 0 := lt_of_not_ge fun h ↦ (Finsupp.mem_support_iff.1 ha) (hf a h)
  have hb' : b < 0 := lt_of_not_ge fun h ↦ (Finsupp.mem_support_iff.1 hb) (hg b h)
  omega

private lemma coeff_intCast (k n : ℤ) :
    (k : LaurentPolynomial ℤ).coeff n = if n = 0 then k else 0 := by
  rw [AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp_all [eq_comm]

/-- `c ∈ ℤ[v⁻¹]`, i.e. `v⁻¹ c ∈ v⁻¹ℤ[v⁻¹]`. -/
def IsIntInv (c : 𝕂) : Prop := IsNegLaurent (𝕧⁻¹ * c)

lemma isIntInv_zero : IsIntInv 0 := by
  rw [IsIntInv, mul_zero]; exact isNegLaurent_zero

lemma isIntInv_one : IsIntInv 1 := by
  rw [IsIntInv, mul_one]; exact isNegLaurent_inv_X

lemma IsIntInv.add {c d : 𝕂} (hc : IsIntInv c) (hd : IsIntInv d) : IsIntInv (c + d) := by
  rw [IsIntInv, mul_add]; exact IsNegLaurent.add hc hd

lemma IsIntInv.neg {c : 𝕂} (hc : IsIntInv c) : IsIntInv (-c) := by
  rw [IsIntInv, mul_neg]; exact IsNegLaurent.neg hc

lemma IsIntInv.sub {c d : 𝕂} (hc : IsIntInv c) (hd : IsIntInv d) : IsIntInv (c - d) := by
  rw [sub_eq_add_neg]; exact hc.add hd.neg

lemma IsNegLaurent.isIntInv {c : 𝕂} (hc : IsNegLaurent c) : IsIntInv c := by
  obtain ⟨a, ha, rfl⟩ := hc
  exact isNegLaurent_inv_X_mul ha

/-- `v⁻¹ℤ[v⁻¹] · ℤ[v⁻¹] ⊆ v⁻¹ℤ[v⁻¹]`. -/
lemma IsNegLaurent.mul_isIntInv {c d : 𝕂} (hc : IsNegLaurent c) (hd : IsIntInv d) :
    IsNegLaurent (c * d) := by
  obtain ⟨a, ha, rfl⟩ := hc
  obtain ⟨b, hb, hb'⟩ := hd
  refine ⟨T 1 * (a * b), isNeg_T_one_mul_mul ha hb, ?_⟩
  rw [map_mul, map_mul, hb', integralLaurentEval_T, zpow_one, mul_left_comm (integralLaurentEval a),
    ← mul_assoc, mul_inv_cancel₀ (NeZero.ne 𝕧), one_mul]

lemma IsIntInv.mul {c d : 𝕂} (hc : IsIntInv c) (hd : IsIntInv d) : IsIntInv (c * d) := by
  rw [IsIntInv, ← mul_assoc]; exact IsNegLaurent.mul_isIntInv hc hd

lemma isIntInv_intCast (n : ℤ) : IsIntInv n := by
  refine ⟨T (-1) * (n : LaurentPolynomial ℤ), fun m hm ↦ ?_, ?_⟩
  · rw [coeff_T_mul, coeff_intCast, ite_eq_right (by omega)]
  · rw [map_mul, map_intCast, integralLaurentEval_T, zpow_neg_one]

/-- `v⁻¹ c ∈ v⁻¹ℤ[v⁻¹]` iff `c ∈ ℤ[v⁻¹]`; `c ∈ v⁻¹ℤ[v⁻¹]` iff `v c ∈ ℤ[v⁻¹]`. -/
lemma isIntInv_X_mul_iff {c : 𝕂} : IsIntInv (𝕧 * c) ↔ IsNegLaurent c := by
  rw [IsIntInv, ← mul_assoc, inv_mul_cancel₀ (NeZero.ne 𝕧), one_mul]

private lemma exists_of_isIntInv {c : 𝕂} (hc : IsIntInv c) :
    ∃ p : LaurentPolynomial ℤ, (T (-1) * p).IsNeg ∧ integralLaurentEval p = c := by
  obtain ⟨a, ha, he⟩ := hc
  refine ⟨T 1 * a, by rwa [← mul_assoc, ← T_add, neg_add_cancel, T_zero, one_mul], ?_⟩
  rw [map_mul, he, integralLaurentEval_T, zpow_one, ← mul_assoc, mul_inv_cancel₀ (NeZero.ne 𝕧),
    one_mul]

/-- An element of `ℤ[v⁻¹]` is an integer modulo `v⁻¹ℤ[v⁻¹]`. -/
lemma IsIntInv.exists_int_sub {c : 𝕂} (hc : IsIntInv c) : ∃ n : ℤ, IsNegLaurent (c - n) := by
  obtain ⟨p, hp, rfl⟩ := exists_of_isIntInv hc
  refine ⟨p.coeff 0, p - (p.coeff 0 : LaurentPolynomial ℤ), fun n hn ↦ ?_, by
    rw [map_sub, map_intCast]⟩
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_intCast]
  rcases hn.eq_or_lt with rfl | hn
  · simp
  · have := hp (n - 1) (by omega)
    rw [coeff_T_mul, sub_neg_eq_add, sub_add_cancel] at this
    rw [this, ite_eq_right (by omega), sub_zero]

/-- `ℤ[v⁻¹] ∩ ℤ[v] = ℤ`. -/
lemma IsIntInv.exists_int_of_bar {c : 𝕂} (hc : IsIntInv c) (hc' : IsIntInv (RatFunc.bar c)) :
    ∃ n : ℤ, c = n := by
  obtain ⟨p, hp, rfl⟩ := exists_of_isIntInv hc
  obtain ⟨p', hp', he⟩ := exists_of_isIntInv hc'
  rw [bar_integralLaurentEval] at he
  obtain rfl := integralLaurentEval_injective he
  refine ⟨p.coeff 0, ?_⟩
  rw [← map_intCast integralLaurentEval]
  congr 1
  ext n
  rw [coeff_intCast]
  split_ifs with h
  · rw [h]
  · rcases lt_or_gt_of_ne h with h | h
    · have := hp' (-n - 1) (by omega)
      rwa [coeff_T_mul, invert_apply, show -(-n - 1 - -1) = n by ring] at this
    · have := hp (n - 1) (by omega)
      rwa [coeff_T_mul, sub_neg_eq_add, sub_add_cancel] at this

/-- An integer in `v⁻¹ℤ[v⁻¹]` is zero. -/
lemma IsNegLaurent.eq_zero_of_intCast {n : ℤ} (hn : IsNegLaurent n) : n = 0 := by
  have := hn.eq_zero_of_bar_eq (by rw [map_intCast])
  exact_mod_cast this

end Scalars

variable {I : Type u} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### Triangularity -/

section Triangular

variable (Λ Λ' : Dom R)

local notation "e" => tensorBasisIdx hR Λ Λ'
local notation "c" => tensorCanonical hR Λ Λ'

lemma le_of_repr_tensorCanonical_ne_zero {h h' : TensorIdx Λ Λ'}
    (h0 : (e).repr (c h) h' ≠ 0) : h ≤ h' := by
  by_contra hn
  exact h0 (by rw [repr_tensorCanonical, ite_eq_right hn])

open Classical in
/-- The pairs below the support of `z` in Lusztig's order (i.e. above it in `TensorIdx`). -/
def suppClosure (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) : Finset (TensorIdx Λ Λ') :=
  ((e).repr z).support.biUnion fun h ↦ (finite_setOf_le Λ Λ' h).toFinset

lemma mem_suppClosure {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} {h : TensorIdx Λ Λ'} :
    h ∈ suppClosure hR Λ Λ' z ↔ ∃ k ∈ ((e).repr z).support, k ≤ h := by
  simp [suppClosure]

/-- The reduction step: subtracting `z_i (b ◇ b')_i` at a coordinate `i` which is maximal for
Lusztig's order shrinks `suppClosure`. -/
lemma suppClosure_ssubset {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} {i : TensorIdx Λ Λ'}
    (hi : Minimal (· ∈ ((e).repr z).support) i) :
    suppClosure hR Λ Λ' (z - (e).repr z i • c i) ⊂ suppClosure hR Λ Λ' z := by
  have hsupp : ∀ k, k ∈ ((e).repr (z - (e).repr z i • c i)).support →
      (k ∈ ((e).repr z).support ∨ i ≤ k) ∧ k ≠ i := by
    intro k hk
    rw [Finsupp.mem_support_iff, map_sub, LinearEquiv.map_smul, Finsupp.sub_apply,
      Finsupp.smul_apply, smul_eq_mul] at hk
    refine ⟨?_, ?_⟩
    · by_contra hn
      rw [not_or, Finsupp.mem_support_iff, not_not] at hn
      exact hk (by rw [hn.1, repr_tensorCanonical, ite_eq_right hn.2, mul_zero, sub_zero])
    · rintro rfl
      exact hk (by rw [repr_tensorCanonical_self, mul_one, sub_self])
  refine Finset.ssubset_iff_of_subset (fun h hh ↦ ?_) |>.2 ⟨i, ?_, ?_⟩
  · obtain ⟨k, hk, hkh⟩ := (mem_suppClosure hR Λ Λ').1 hh
    rcases (hsupp k hk).1 with hk' | hk'
    · exact (mem_suppClosure hR Λ Λ').2 ⟨k, hk', hkh⟩
    · exact (mem_suppClosure hR Λ Λ').2 ⟨i, hi.1, hk'.trans hkh⟩
  · exact (mem_suppClosure hR Λ Λ').2 ⟨i, hi.1, le_rfl⟩
  · rw [mem_suppClosure]
    rintro ⟨k, hk, hki⟩
    obtain ⟨hk', hne⟩ := hsupp k hk
    rcases hk' with hk' | hk'
    · exact hne (le_antisymm hki (hi.2 hk' hki))
    · exact hne (le_antisymm hki hk')

/-- The induction principle behind [Lus] 24.3.3 (c): if `L` is an additive subgroup whose
coordinates satisfy `Q`, and which contains `a (b ◇ b')` for every `a` satisfying `Q`, then every
element of `L` is reached from `0` by adding such multiples. -/
lemma induction_tensorCanonical (L : AddSubgroup (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1))
    (Q : 𝕂 → Prop)
    (hQ : ∀ z ∈ L, ∀ h, Q ((e).repr z h)) (hL : ∀ a h, Q a → a • c h ∈ L)
    (P : (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) → Prop) (hP0 : P 0)
    (hPadd : ∀ z a h, P z → Q a → P (z + a • c h)) :
    ∀ z ∈ L, P z := by
  suffices ∀ n, ∀ z ∈ L, (suppClosure hR Λ Λ' z).card = n → P z from
    fun z hz ↦ this _ z hz rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro z hz rfl
    by_cases h0 : z = 0
    · rw [h0]; exact hP0
    have hs : ((e).repr z).support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      exact fun h ↦ h0 ((e).repr.map_eq_zero_iff.1 h)
    obtain ⟨i, hi⟩ := ((e).repr z).support.exists_minimal hs
    have hz' : z - (e).repr z i • c i ∈ L := sub_mem hz (hL _ i (hQ z hz i))
    have := ih _ (Finset.card_lt_card (suppClosure_ssubset hR Λ Λ' hi)) _ hz' rfl
    simpa using hPadd _ _ i this (hQ z hz i)

/-- **[Lus] 24.3.3 (c)**: the `(b ◇ b')_{λ,λ'}` span `ʷL_q(λ) ⊗ L_q(λ')` over `ℚ(v)`. -/
lemma span_tensorCanonical : ⊤ ≤ Submodule.span 𝕂 (Set.range c) := by
  intro z _
  refine induction_tensorCanonical hR Λ Λ' ⊤ (fun _ ↦ True) (fun _ _ _ ↦ trivial)
    (fun _ _ _ ↦ AddSubgroup.mem_top _) (· ∈ Submodule.span 𝕂 (Set.range c))
    (zero_mem _) (fun z a h hz _ ↦ add_mem hz (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨h, rfl⟩))) z (AddSubgroup.mem_top z)

/-- **[Lus] 24.3.3 (c)**: the `(b ◇ b')_{λ,λ'}` are linearly independent over `ℚ(v)`. -/
lemma linearIndependent_tensorCanonical : LinearIndependent 𝕂 c := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hgi
  set s' := s.filter fun k ↦ g k ≠ 0
  obtain ⟨j, hj⟩ := s'.exists_minimal ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  have hj' := Finset.mem_filter.1 hj.1
  have key := congrArg (fun z ↦ (e).repr z j) hg
  simp only [map_sum, LinearEquiv.map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at key
  rw [Finset.sum_eq_single_of_mem j hj'.1, repr_tensorCanonical_self, mul_one] at key
  · exact hj'.2 key
  · intro k hk hkj
    by_cases hgk : g k = 0
    · rw [hgk, zero_mul]
    by_cases hr : (e).repr (c k) j = 0
    · rw [hr, mul_zero]
    exact absurd (le_antisymm (hj.2 (Finset.mem_filter.2 ⟨hk, hgk⟩)
      (le_of_repr_tensorCanonical_ne_zero hR Λ Λ' hr))
      (le_of_repr_tensorCanonical_ne_zero hR Λ Λ' hr)).symm hkj

/-- **[Lus] 24.3.3 (c)**, **24.3.4**: the canonical basis `(b₁ ◇ b₁')_{λ,λ'}` of
`ʷL_q(λ) ⊗ L_q(λ')` over `ℚ(v)`. -/
def tensorCanonicalBasis :
    Module.Basis (TensorIdx Λ Λ') 𝕂 (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :=
  .mk (linearIndependent_tensorCanonical hR Λ Λ') (span_tensorCanonical hR Λ Λ')

@[simp] lemma tensorCanonicalBasis_apply (h : TensorIdx Λ Λ') :
    tensorCanonicalBasis hR Λ Λ' h = c h :=
  Module.Basis.mk_apply _ _ _

local notation "cb" => tensorCanonicalBasis hR Λ Λ'

lemma repr_tensorCanonicalBasis_add_smul (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) (a : 𝕂)
    (h : TensorIdx Λ Λ') :
    (cb).repr (z + a • c h) = (cb).repr z + Finsupp.single h a := by
  rw [map_add, LinearEquiv.map_smul, ← tensorCanonicalBasis_apply, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `Ψ(Σ a_h (b ◇ b')_h) = Σ \bar a_h (b ◇ b')_h`. -/
lemma repr_tensorPsi_tensorCanonicalBasis (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1)
    (h : TensorIdx Λ Λ') :
    (cb).repr (tensorPsi hR Λ Λ' z) h = RatFunc.bar ((cb).repr z h) := by
  classical
  have hk : ∀ k, tensorPsi hR Λ Λ' ((cb).repr z k • cb k) = RatFunc.bar ((cb).repr z k) • cb k := by
    intro k
    rw [tensorPsi_smul, tensorCanonicalBasis_apply, tensorPsi_tensorCanonical,
      ← tensorCanonicalBasis_apply hR Λ Λ']
  conv_lhs => rw [← (cb).linearCombination_repr z]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp_rw [hk]
  rw [map_sum, Finsupp.finsetSum_apply]
  simp_rw [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hh
  · rfl
  · rw [Finsupp.notMem_support_iff.1 hh, map_zero]

end Triangular

/-! ### Lattices -/

section Lattices

variable (Λ Λ' : Dom R)

local notation "e" => tensorBasisIdx hR Λ Λ'
local notation "c" => tensorCanonical hR Λ Λ'
local notation "cb" => tensorCanonicalBasis hR Λ Λ'

/-- Lusztig's `𝒜ℒ`, the `𝒜`-span of the basis `b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}` ([Lus] 24.3.1): the vectors
whose coordinates lie in `𝒜`. -/
def tensorLatA : AddSubgroup (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) where
  carrier := {z | ∀ h, Modified.IsLaurent ((e).repr z h)}
  add_mem' hz hz' h := by rw [map_add, Finsupp.add_apply]; exact (hz h).add (hz' h)
  zero_mem' h := by rw [map_zero, Finsupp.zero_apply]; exact Modified.isLaurent_zero
  neg_mem' hz h := by rw [map_neg, Finsupp.neg_apply]; exact (hz h).neg

/-- `v⁻¹ℒ`: the vectors whose coordinates lie in `v⁻¹ℤ[v⁻¹]`. -/
def tensorLatNeg : AddSubgroup (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) where
  carrier := {z | ∀ h, IsNegLaurent ((e).repr z h)}
  add_mem' hz hz' h := by rw [map_add, Finsupp.add_apply]; exact (hz h).add (hz' h)
  zero_mem' h := by rw [map_zero, Finsupp.zero_apply]; exact isNegLaurent_zero
  neg_mem' hz h := by rw [map_neg, Finsupp.neg_apply]; exact (hz h).neg

lemma mem_tensorLatNeg_iff {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} :
    z ∈ tensorLatNeg hR Λ Λ' ↔ 𝕧 • z ∈ tensorLat hR Λ Λ' :=
  (smul_mem_tensorLat_iff hR Λ Λ').symm

lemma tensorLatNeg_le : tensorLatNeg hR Λ Λ' ≤ tensorLat hR Λ Λ' :=
  fun _ hz h ↦ (hz h).isIntInv

lemma isIntInv_repr_tensorCanonical (h h' : TensorIdx Λ Λ') : IsIntInv ((e).repr (c h) h') := by
  rcases eq_or_ne h' h with rfl | hne
  · rw [repr_tensorCanonical_self]; exact isIntInv_one
  · exact (isNegLaurent_repr_tensorCanonical hR Λ Λ' hne).isIntInv

lemma isLaurent_repr_tensorCanonical (h h' : TensorIdx Λ Λ') :
    Modified.IsLaurent ((e).repr (c h) h') := by
  rw [repr_tensorCanonical]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact Modified.isLaurent_zero

lemma smul_tensorCanonical_mem_tensorLat {a : 𝕂} (ha : IsIntInv a) (h : TensorIdx Λ Λ') :
    a • c h ∈ tensorLat hR Λ Λ' := fun h' ↦ by
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact ha.mul (isIntInv_repr_tensorCanonical hR Λ Λ' h h')

lemma smul_tensorCanonical_mem_tensorLatA {a : 𝕂} (ha : Modified.IsLaurent a)
    (h : TensorIdx Λ Λ') : a • c h ∈ tensorLatA hR Λ Λ' := fun h' ↦ by
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact ha.mul (isLaurent_repr_tensorCanonical hR Λ Λ' h h')

/-- **[Lus] 24.3.3 (c)**: the `(b ◇ b')_{λ,λ'}` form a `ℤ[v⁻¹]`-basis of `ℒ`: an element lies in
`ℒ` iff its coordinates in the canonical basis lie in `ℤ[v⁻¹]`. -/
theorem mem_tensorLat_iff_canonical {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} :
    z ∈ tensorLat hR Λ Λ' ↔ ∀ h, IsIntInv ((cb).repr z h) := by
  classical
  constructor
  · refine induction_tensorCanonical hR Λ Λ' (tensorLat hR Λ Λ') IsIntInv (fun z hz h ↦ hz h)
      (fun _ h ha ↦ smul_tensorCanonical_mem_tensorLat hR Λ Λ' ha h)
      (fun z ↦ ∀ h, IsIntInv ((cb).repr z h)) (fun h ↦ by simpa using isIntInv_zero) ?_ z
    intro z a i hz ha h
    rw [repr_tensorCanonicalBasis_add_smul, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs
    · exact (hz h).add ha
    · simpa using hz h
  · intro hz
    rw [← (cb).linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum]
    refine AddSubgroup.sum_mem _ fun h _ ↦ ?_
    rw [tensorCanonicalBasis_apply]
    exact smul_tensorCanonical_mem_tensorLat hR Λ Λ' (hz h) h

/-- **[Lus] 24.3.3 (c)**: the `(b ◇ b')_{λ,λ'}` form an `𝒜`-basis of `𝒜ℒ`: an element lies in
`𝒜ℒ` iff its coordinates in the canonical basis lie in `𝒜`. -/
theorem mem_tensorLatA_iff {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} :
    z ∈ tensorLatA hR Λ Λ' ↔ ∀ h, Modified.IsLaurent ((cb).repr z h) := by
  classical
  constructor
  · refine induction_tensorCanonical hR Λ Λ' (tensorLatA hR Λ Λ') Modified.IsLaurent
      (fun z hz h ↦ hz h)
      (fun _ h ha ↦ smul_tensorCanonical_mem_tensorLatA hR Λ Λ' ha h)
      (fun z ↦ ∀ h, Modified.IsLaurent ((cb).repr z h))
      (fun h ↦ by simpa using Modified.isLaurent_zero) ?_ z
    intro z a i hz ha h
    rw [repr_tensorCanonicalBasis_add_smul, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs
    · exact (hz h).add ha
    · simpa using hz h
  · intro hz
    rw [← (cb).linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum]
    refine AddSubgroup.sum_mem _ fun h _ ↦ ?_
    rw [tensorCanonicalBasis_apply]
    exact smul_tensorCanonical_mem_tensorLatA hR Λ Λ' (hz h) h

/-- The elements of `ℒ ∩ Ψ(ℒ)` are the `ℤ`-linear combinations of the `(b ◇ b')_{λ,λ'}`. -/
lemma exists_int_repr_of_mem {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1}
    (hz : z ∈ tensorLat hR Λ Λ')
    (hz' : tensorPsi hR Λ Λ' z ∈ tensorLat hR Λ Λ') (h : TensorIdx Λ Λ') :
    ∃ n : ℤ, (cb).repr z h = n := by
  rw [mem_tensorLat_iff_canonical] at hz hz'
  refine (hz h).exists_int_of_bar ?_
  rw [← repr_tensorPsi_tensorCanonicalBasis]
  exact hz' h

/-- `ℒ ∩ Ψ(ℒ)`. -/
def tensorLatBar : AddSubgroup (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :=
  tensorLat hR Λ Λ' ⊓ (tensorLat hR Λ Λ').map (tensorPsi hR Λ Λ')

lemma mem_tensorLatBar_iff {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} :
    z ∈ tensorLatBar hR Λ Λ' ↔ z ∈ tensorLat hR Λ Λ' ∧ tensorPsi hR Λ Λ' z ∈ tensorLat hR Λ Λ' := by
  rw [tensorLatBar, AddSubgroup.mem_inf, AddSubgroup.mem_map]
  refine and_congr_right fun _ ↦ ⟨?_, fun h ↦ ⟨_, h, tensorPsi_tensorPsi hR Λ Λ' z⟩⟩
  rintro ⟨y, hy, rfl⟩
  rwa [tensorPsi_tensorPsi]

/-- The natural map `ℒ ∩ Ψ(ℒ) → ℒ/v⁻¹ℒ`. -/
def tensorLatResidue :
    tensorLatBar hR Λ Λ' →+ tensorLat hR Λ Λ' ⧸ (tensorLatNeg hR Λ Λ').addSubgroupOf
      (tensorLat hR Λ Λ') :=
  (QuotientAddGroup.mk' _).comp (AddSubgroup.inclusion inf_le_left)

lemma tensorLatResidue_apply (x : tensorLatBar hR Λ Λ') :
    tensorLatResidue hR Λ Λ' x =
      QuotientAddGroup.mk (⟨x, (AddSubgroup.mem_inf.1 x.2).1⟩ : tensorLat hR Λ Λ') :=
  rfl

lemma tensorLatResidue_eq_mk {x : tensorLatBar hR Λ Λ'} {w : tensorLat hR Λ Λ'}
    (h : (w : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) - x ∈ tensorLatNeg hR Λ Λ') :
    tensorLatResidue hR Λ Λ' x = QuotientAddGroup.mk' _ w := by
  rw [tensorLatResidue_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
    AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]
  exact h

lemma tensorCanonical_mem_tensorLatBar (h : TensorIdx Λ Λ') : c h ∈ tensorLatBar hR Λ Λ' := by
  rw [mem_tensorLatBar_iff, tensorPsi_tensorCanonical]
  have := smul_tensorCanonical_mem_tensorLat hR Λ Λ' isIntInv_one h
  rw [one_smul] at this
  exact ⟨this, this⟩

/-- Every element of `ℒ` is congruent modulo `v⁻¹ℒ` to a `ℤ`-combination of the
`(b ◇ b')_{λ,λ'}`. -/
lemma exists_sub_sum_mem_tensorLatNeg {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1}
    (hz : z ∈ tensorLat hR Λ Λ') :
    ∃ (s : Finset (TensorIdx Λ Λ')) (n : TensorIdx Λ Λ' → ℤ),
      z - ∑ h ∈ s, (n h : 𝕂) • c h ∈ tensorLatNeg hR Λ Λ' := by
  classical
  have hn : ∀ h, ∃ n : ℤ, IsNegLaurent ((e).repr z h - n) :=
    fun h ↦ IsIntInv.exists_int_sub (hz h)
  choose n hn using hn
  refine ⟨((e).repr z).support, n, ?_⟩
  have hz' : z = ∑ h ∈ ((e).repr z).support, (e).repr z h • e h := by
    conv_lhs => rw [← (e).linearCombination_repr z]
    rfl
  nth_rw 1 [hz']
  rw [← Finset.sum_sub_distrib]
  refine AddSubgroup.sum_mem _ fun h _ ↦ ?_
  have : (e).repr z h • e h - (n h : 𝕂) • c h =
      ((e).repr z h - n h) • e h - (n h : 𝕂) • (c h - e h) := by
    rw [sub_smul, smul_sub]; abel
  rw [this]
  refine sub_mem (fun h' ↦ ?_) (fun h' ↦ ?_)
  · rw [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply]
    split_ifs
    · rw [mul_one]; exact hn h
    · rw [mul_zero]; exact isNegLaurent_zero
  · rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    refine IsNegLaurent.mul_isIntInv ?_ (isIntInv_intCast _)
    rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs with hh
    · subst hh
      rw [repr_tensorCanonical_self, sub_self]
      exact isNegLaurent_zero
    · rw [sub_zero]
      exact isNegLaurent_repr_tensorCanonical hR Λ Λ' (Ne.symm hh)

/-- **[Lus] 24.3.3 (d)**: the natural map `ℒ ∩ Ψ(ℒ) → ℒ/v⁻¹ℒ` is an isomorphism. -/
theorem bijective_tensorLatResidue : Function.Bijective (tensorLatResidue hR Λ Λ') := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun ⟨z, hz⟩ hz0 ↦ ?_, fun y ↦ ?_⟩
  · rw [mem_tensorLatBar_iff] at hz
    rw [tensorLatResidue, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hz0
    change z ∈ tensorLatNeg hR Λ Λ' at hz0
    rw [mem_tensorLatNeg_iff, mem_tensorLat_iff_canonical] at hz0
    refine Subtype.ext ((cb).repr.map_eq_zero_iff.1 (Finsupp.ext fun h ↦ ?_))
    obtain ⟨n, hn⟩ := exists_int_repr_of_mem hR Λ Λ' hz.1 hz.2 h
    have h1 := hz0 h
    rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, isIntInv_X_mul_iff, hn] at h1
    rw [hn, h1.eq_zero_of_intCast, Int.cast_zero, Finsupp.zero_apply]
  · obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
    have hw : (w : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) ∈ tensorLat hR Λ Λ' := w.2
    have hex := exists_sub_sum_mem_tensorLatNeg hR Λ Λ' hw
    obtain ⟨s, n, hsn⟩ := hex
    have hmem : ∑ h ∈ s, (n h : 𝕂) • c h ∈ tensorLatBar hR Λ Λ' :=
      AddSubgroup.sum_mem _ fun h _ ↦ by
        rw [Int.cast_smul_eq_zsmul 𝕂]
        exact AddSubgroup.zsmul_mem _ (tensorCanonical_mem_tensorLatBar hR Λ Λ' h) _
    exact ⟨⟨_, hmem⟩, tensorLatResidue_eq_mk hR Λ Λ' hsn⟩

end Lattices

end LieLean.QuantumGroup
