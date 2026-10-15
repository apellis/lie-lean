/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightInnerProduct
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.ModifiedCanonicalBasis
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorCanonicalBasis
import LieLean.Algebra.QuantumGroup.Modified.BaseChange
import LieLean.Algebra.QuantumGroup.Modified.FormLimit

/-!
# Almost orthonormality of the canonical basis of `U̇`

Over `ℚ(v)`, let `A = ℚ[[v⁻¹]] ∩ ℚ(v)` be the local ring at `v = ∞` (`InfinityLocalRing`). For
`ζ, ζ₁ ∈ X` and `b, b'', b₁, b₁'' ∈ B`, [Lus] Thm. 26.3.1 (a) states
`(b ◇_ζ b'', b₁ ◇_{ζ₁} b₁'') ≡ δ_{b,b₁} δ_{b'',b₁''} δ_{ζ,ζ₁} mod v⁻¹A`: the canonical basis of `U̇`
is almost orthonormal for Lusztig's form. Consequently the form is nondegenerate.

## Main results

* `isNegLaurent_tensorIrrForm_tensorCanonical_sub`: the elements `(b ◇ b'')_{λ,λ''}` of
  `ʷΛ_λ ⊗ Λ_{λ''}` are almost orthonormal for the form of [Lus] 26.2.1, modulo `v⁻¹ℤ[v⁻¹]`
  (the statement (c) in the proof of [Lus] 26.3.1).
* `Modified.form_modifiedCanonical_sub_mem`: **[Lus] Thm. 26.3.1 (a)**;
  `Modified.form_modifiedCanonicalBasis_sub_mem` is the same statement for the basis
  `Modified.modifiedCanonicalBasis` of [Lus] 25.2.1 (d).
* `Modified.eq_zero_of_forall_form_eq_zero`: Lusztig's form on `U̇` over `ℚ(v)` is
  nondegenerate, a consequence of 26.3.1 (a) (our own short deduction: the reduction of an
  almost orthonormal basis modulo `v⁻¹` is orthonormal for a form with values in the formally
  real field `ℚ`); `Modified.eq_zero_of_forall_form_eq_zero_of_transcendental` transfers this to
  any parameter transcendental over `ℚ` in a field of characteristic zero.

## Hypotheses

Lusztig states 26.3.1 for every root datum, reducing to the simply connected case by 25.2.2. Here
the root datum is `X`-regular and satisfies `hY` (dominant `λ` with all `⟨i, λ⟩` arbitrarily
large), as in [Lus] 25.2.1 (`existsUnique_modifiedCanonical`); removing `hY` via [Lus] 25.2.2 is
tracked in the roadmap.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.3.3, 24.3.3, 25.2.1,
  26.1.2, 26.2.1–26.2.3, 26.3.1.
-/

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF TensorProduct Modified

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-! ### `ℤ[v⁻¹] ⊆ A` -/

section Scalars

/-- `v⁻¹ℤ[v⁻¹] ⊆ v⁻¹A`. -/
lemma IsNegLaurent.exists_eq_uniformizer_mul {c : 𝕂} (hc : IsNegLaurent c) :
    ∃ a : A, c = algebraMap A 𝕂 (ϖ * a) := by
  obtain ⟨f, hf, rfl⟩ := hc
  have hterm : ∀ n ∈ f.coeff.support,
      integralLaurentEval (AddMonoidAlgebra.single n (f.coeff n)) =
        algebraMap A 𝕂 (ϖ * ((f.coeff n : A) * ϖ ^ (-n - 1).toNat)) := by
    intro n hn
    have hn' : n < 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.1 hn (hf n (by omega))
    have hC : integralLaurentEval (LaurentPolynomial.C (f.coeff n)) = (f.coeff n : 𝕂) := by
      simp [integralLaurentEval]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (-n - 1).toNat = k := ⟨_, rfl⟩
    have hn2 : n = -((k : ℤ) + 1) := by omega
    rw [LaurentPolynomial.single_eq_C_mul_T, _root_.map_mul, hC, integralLaurentEval_T,
      _root_.map_mul, _root_.map_mul, map_pow, InfinityLocalRing.algebraMap_uniformizer,
      map_intCast, hk, hn2, zpow_neg,
      zpow_add_one₀ RatFunc.X_ne_zero, zpow_natCast, mul_inv, inv_pow]
    ring
  refine ⟨∑ n ∈ f.coeff.support, (f.coeff n : A) * ϖ ^ (-n - 1).toNat, ?_⟩
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, map_sum, Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl hterm

/-- `ℤ[v⁻¹] ⊆ A`. -/
lemma IsIntInv.exists_eq_algebraMap {c : 𝕂} (hc : IsIntInv c) : ∃ a : A, c = algebraMap A 𝕂 a := by
  obtain ⟨n, hn⟩ := hc.exists_int_sub
  obtain ⟨a, ha⟩ := hn.exists_eq_uniformizer_mul
  exact ⟨n + ϖ * a, by rw [map_add, ← ha, map_intCast, add_sub_cancel]⟩

lemma isIntInv_ite (p : Prop) [Decidable p] : IsIntInv (if p then 1 else 0) := by
  split_ifs
  · exact isIntInv_one
  · exact isIntInv_zero

/-- `x y z ∈ v⁻¹ℤ[v⁻¹]` if one of `x, y` lies in `v⁻¹ℤ[v⁻¹]` and the other factors in `ℤ[v⁻¹]`. -/
lemma isNegLaurent_mul_mul {x y z : 𝕂}
    (h : IsNegLaurent x ∧ IsIntInv y ∨ IsIntInv x ∧ IsNegLaurent y) (hz : IsIntInv z) :
    IsNegLaurent (x * y * z) := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact (hx.mul_isIntInv hy).mul_isIntInv hz
  · rw [mul_comm x]
    exact (hy.mul_isIntInv hx).mul_isIntInv hz

lemma isNegLaurent_finset_sum {ι : Type*} (s : Finset ι) {f : ι → 𝕂}
    (h : ∀ i ∈ s, IsNegLaurent (f i)) : IsNegLaurent (∑ i ∈ s, f i) :=
  Finset.sum_induction _ IsNegLaurent (fun _ _ ↦ IsNegLaurent.add) isNegLaurent_zero h

/-- If all `x_g y_{g'} B(e_g, e_{g'})` lie in `v⁻¹ℤ[v⁻¹]`, so does `B(x, y)`. -/
lemma isNegLaurent_bilinForm {M ι : Type*} [AddCommGroup M] [Module 𝕂 M]
    (B : LinearMap.BilinForm 𝕂 M) (e : Module.Basis ι 𝕂 M) (x y : M)
    (h : ∀ g g', IsNegLaurent (e.repr x g * e.repr y g' * B (e g) (e g'))) :
    IsNegLaurent (B x y) := by
  rw [← LinearMap.BilinForm.sum_repr_mul_repr_mul e x y, Finsupp.sum]
  refine isNegLaurent_finset_sum _ fun g _ ↦ ?_
  rw [Finsupp.sum]
  refine isNegLaurent_finset_sum _ fun g' _ ↦ ?_
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc]
  exact h g g'

end Scalars

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### The form on `ʷΛ_λ ⊗ Λ_{λ''}` -/

section Tensor

variable (Λ Λ'' : Dom R)

/-- The form `(x ⊗ x', y ⊗ y') = (x, y)_λ (x', y')_{λ''}` on `ʷΛ_λ ⊗ Λ_{λ''}` ([Lus] 26.2.1). -/
def tensorIrrForm : LinearMap.BilinForm 𝕂 (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ''.1) :=
  (IrreducibleModule.tensorForm hR hvn_ratFunc Λ.1 Λ''.1).compl₁₂
    (TensorModule.mk _ _).toLinearMap (TensorModule.mk _ _).toLinearMap

lemma tensorIrrForm_tensorBasisIdx (h h' : TensorIdx Λ Λ'') :
    tensorIrrForm hR Λ Λ'' (tensorBasisIdx hR Λ Λ'' h) (tensorBasisIdx hR Λ Λ'' h') =
      formL hvt hR Λ (evq hvt Λ h.1) (evq hvt Λ h'.1) *
        formL hvt hR Λ'' (evq hvt Λ'' h.2) (evq hvt Λ'' h'.2) := by
  rw [tensorBasisIdx_apply, tensorBasisIdx_apply]
  erw [tensorBasis_apply, tensorBasis_apply]
  exact TensorModule.form_tmul _ _ _ _ _ _

open Classical in
/-- The basis `b⁺ξ_{-λ} ⊗ b''⁻η_{λ''}` is almost orthonormal ([Lus] 19.3.3). -/
lemma isNegLaurent_tensorIrrForm_tensorBasisIdx_sub (h h' : TensorIdx Λ Λ'') :
    IsNegLaurent (tensorIrrForm hR Λ Λ'' (tensorBasisIdx hR Λ Λ'' h) (tensorBasisIdx hR Λ Λ'' h') -
      if h = h' then 1 else 0) := by
  have h₁ := isNegLaurent_formL_evq_sub hR Λ h.1 h'.1
  have h₂ := isNegLaurent_formL_evq_sub hR Λ'' h.2 h'.2
  have e : tensorIrrForm hR Λ Λ'' (tensorBasisIdx hR Λ Λ'' h) (tensorBasisIdx hR Λ Λ'' h') -
      (if h = h' then 1 else 0) =
      (formL hvt hR Λ (evq hvt Λ h.1) (evq hvt Λ h'.1) - if h.1 = h'.1 then 1 else 0) *
        formL hvt hR Λ'' (evq hvt Λ'' h.2) (evq hvt Λ'' h'.2) +
      (formL hvt hR Λ'' (evq hvt Λ'' h.2) (evq hvt Λ'' h'.2) - if h.2 = h'.2 then 1 else 0) *
        (if h.1 = h'.1 then 1 else 0) := by
    rw [tensorIrrForm_tensorBasisIdx]
    have : (if h = h' then (1 : 𝕂) else 0) =
        (if h.1 = h'.1 then 1 else 0) * (if h.2 = h'.2 then 1 else 0) := by
      rw [ite_zero_mul_ite_zero, one_mul]
      exact if_congr Prod.ext_iff rfl rfl
    rw [this]
    ring
  rw [e]
  have hq : IsIntInv (formL hvt hR Λ'' (evq hvt Λ'' h.2) (evq hvt Λ'' h'.2)) := by
    have := h₂.isIntInv.add (isIntInv_ite (h.2 = h'.2))
    rwa [sub_add_cancel] at this
  exact (h₁.mul_isIntInv hq).add (h₂.mul_isIntInv (isIntInv_ite _))

lemma isIntInv_tensorIrrForm_tensorBasisIdx (h h' : TensorIdx Λ Λ'') :
    IsIntInv (tensorIrrForm hR Λ Λ'' (tensorBasisIdx hR Λ Λ'' h) (tensorBasisIdx hR Λ Λ'' h')) := by
  classical
  have := (isNegLaurent_tensorIrrForm_tensorBasisIdx_sub hR Λ Λ'' h h').isIntInv.add
    (isIntInv_ite (h = h'))
  rwa [sub_add_cancel] at this

lemma isNegLaurent_repr_tensorCanonical_sub (h g : TensorIdx Λ Λ'') :
    IsNegLaurent ((tensorBasisIdx hR Λ Λ'').repr
      (tensorCanonical hR Λ Λ'' h - tensorBasisIdx hR Λ Λ'' h) g) := by
  classical
  rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rcases eq_or_ne g h with rfl | hne
  · rw [repr_tensorCanonical_self, ite_eq_left rfl, sub_self]
    exact isNegLaurent_zero
  · rw [ite_eq_right hne.symm, sub_zero]
    exact isNegLaurent_repr_tensorCanonical hR Λ Λ'' hne

open Classical in
/-- **The statement (c) in the proof of [Lus] Thm. 26.3.1**: the elements `(b ◇ b'')_{λ,λ''}`
are almost orthonormal, `((b ◇ b'')_{λ,λ''}, (b₁ ◇ b₁'')_{λ,λ''}) ≡ δ mod v⁻¹ℤ[v⁻¹]`
(from [Lus] 24.3.3 (b) and 19.3.3). -/
theorem isNegLaurent_tensorIrrForm_tensorCanonical_sub (h h' : TensorIdx Λ Λ'') :
    IsNegLaurent (tensorIrrForm hR Λ Λ'' (tensorCanonical hR Λ Λ'' h)
      (tensorCanonical hR Λ Λ'' h') - if h = h' then 1 else 0) := by
  set B := tensorIrrForm hR Λ Λ''
  set e := tensorBasisIdx hR Λ Λ''
  have hsplit : B (tensorCanonical hR Λ Λ'' h) (tensorCanonical hR Λ Λ'' h') -
      (if h = h' then 1 else 0) = (B (e h) (e h') - if h = h' then 1 else 0) +
        B (e h) (tensorCanonical hR Λ Λ'' h' - e h') +
        B (tensorCanonical hR Λ Λ'' h - e h) (tensorCanonical hR Λ Λ'' h') := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hsplit]
  refine ((isNegLaurent_tensorIrrForm_tensorBasisIdx_sub hR Λ Λ'' h h').add ?_).add ?_
  · refine isNegLaurent_bilinForm B e _ _ fun g g' ↦ isNegLaurent_mul_mul (Or.inr ⟨?_, ?_⟩)
      (isIntInv_tensorIrrForm_tensorBasisIdx hR Λ Λ'' g g')
    · rw [Module.Basis.repr_self, Finsupp.single_apply]
      exact isIntInv_ite _
    · exact isNegLaurent_repr_tensorCanonical_sub hR Λ Λ'' h' g'
  · exact isNegLaurent_bilinForm B e _ _ fun g g' ↦ isNegLaurent_mul_mul
      (Or.inl ⟨isNegLaurent_repr_tensorCanonical_sub hR Λ Λ'' h g,
        isIntInv_repr_tensorCanonical hR Λ Λ'' h' g'⟩)
      (isIntInv_tensorIrrForm_tensorBasisIdx hR Λ Λ'' g g')

end Tensor

/-! ### [Lus] 26.3.1 (a) -/

section Orthonormal

variable (hY : ∀ N : ℕ, ∃ Λ : Dom R, ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i))

omit [Finite I] in
/-- `(u 1_ζ, u' 1_{ζ'}) = 0` for `ζ ≠ ζ'` ([Lus] 26.1.2 (a)). -/
theorem Modified.form_leftActOne_leftActOne_of_ne {ζ ζ' : Y →+ ℤ} (hζ : ζ ≠ ζ')
    (u u' : QuantumGroup R 𝕧) :
    Modified.form R 𝕧 hvn_ratFunc (leftActOne R hvn_ratFunc ζ u)
      (leftActOne R hvn_ratFunc ζ' u') = 0 := by
  have h1 : Modified.form R 𝕧 hvn_ratFunc (leftActOne R hvn_ratFunc ζ u)
      (leftActOne R hvn_ratFunc ζ' u') = Modified.form R 𝕧 hvn_ratFunc (one ζ)
        (leftActOne R hvn_ratFunc ζ' (rho R 𝕧 u * u')) := by
    rw [leftActOne_apply, form_leftAct_left, leftActOne_apply _ ζ' u', ← leftAct_mul]
    rfl
  have hz : one ζ * leftActOne R hvn_ratFunc ζ' (rho R 𝕧 u * u') * one ζ' =
      one ζ * leftActOne R hvn_ratFunc ζ' (rho R 𝕧 u * u') := by
    rw [mul_assoc, leftActOne_mul, one_mul_one_self, ← leftActOne_apply]
  have h2 := form_one_mul_mul_one_eq_zero (R := R) hvn_ratFunc (l₁ := ζ) (l₂ := ζ) (m₁ := ζ)
    (m₂ := ζ') (fun h ↦ hζ (Prod.mk.inj h).2) (one ζ)
    (leftActOne R hvn_ratFunc ζ' (rho R 𝕧 u * u'))
  rw [one_mul_one_self, one_mul_one_self, hz, ← form_one_mul, one_mul_one_self] at h2
  rw [h1, h2]

include hR hY in
/-- `(b ◇_ζ b'', b₁ ◇_{ζ₁} b₁'') = 0` for `ζ ≠ ζ₁` ([Lus] 26.1.2 (a)). -/
theorem Modified.form_modifiedCanonical_of_ne {ζ ζ₁ : Y →+ ℤ} (hζ : ζ ≠ ζ₁)
    {b b'' b₁ b₁'' : Um D 𝕧} (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D)
    (hb₁ : b₁ ∈ canonicalBasis D) (hb₁'' : b₁'' ∈ canonicalBasis D) :
    Modified.form R 𝕧 hvn_ratFunc (modifiedCanonical hR hY ζ hb hb'')
      (modifiedCanonical hR hY ζ₁ hb₁ hb₁'') = 0 := by
  obtain ⟨u, hu⟩ := modifiedCanonical_mem_range hR hY ζ hb hb''
  obtain ⟨u₁, hu₁⟩ := modifiedCanonical_mem_range hR hY ζ₁ hb₁ hb₁''
  rw [← hu, ← hu₁]
  exact form_leftActOne_leftActOne_of_ne hζ u u₁

open Classical in
include hR hY in
/-- [Lus] Thm. 26.3.1 (a) for `ζ₁ = ζ`: `(b ◇_ζ b'', b₁ ◇_ζ b₁'') ≡ δ_{b,b₁} δ_{b'',b₁''}`
modulo `v⁻¹A`. As in the source, both sides are compared with the form of
`(b ◇ b'')_{λ,λ''}` and `(b₁ ◇ b₁'')_{λ,λ''}` for large `λ` (statement (c) and [Lus] 26.2.3). -/
theorem Modified.form_modifiedCanonical_sub_mem_of_eq (ζ : Y →+ ℤ) {b b'' b₁ b₁'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D)
    (hb₁ : b₁ ∈ canonicalBasis D) (hb₁'' : b₁'' ∈ canonicalBasis D) :
    ∃ a : A, Modified.form R 𝕧 hvn_ratFunc (modifiedCanonical hR hY ζ hb hb'')
        (modifiedCanonical hR hY ζ hb₁ hb₁'') - (if b = b₁ ∧ b'' = b₁'' then 1 else 0) =
      algebraMap A 𝕂 (ϖ * a) := by
  obtain ⟨u, hu⟩ := modifiedCanonical_mem_range hR hY ζ hb hb''
  obtain ⟨u₁, hu₁⟩ := modifiedCanonical_mem_range hR hY ζ hb₁ hb₁''
  obtain ⟨M, hM⟩ := IrreducibleModule.tendstoAtInfinity_tensorForm hR hvn_ratFunc
    InfinityLocalRing.exists_pow_mul InfinityLocalRing.algebraMap_uniformizer ζ u u₁ 1
  set N := max M.toNat (max (max (cbWt D ⟨b, hb⟩).degree (cbWt D ⟨b'', hb''⟩).degree)
    (max (cbWt D ⟨b₁, hb₁⟩).degree (cbWt D ⟨b₁'', hb₁''⟩).degree))
  obtain ⟨Λ, Λ'', hζ, hΛ, hΛ''⟩ := exists_dom_pair hY ζ N
  have hΛ₂ : ζ + Λ.1 = Λ''.1 := by rw [← hζ, sub_add_cancel]
  let Λ₂ : Dom R := ⟨ζ + Λ.1, hΛ₂ ▸ Λ''.2⟩
  have hN₂ : ∀ i, (N : ℤ) ≤ Λ₂.1 (R.coroot i) := fun i ↦ by
    change (N : ℤ) ≤ (ζ + Λ.1) (R.coroot i)
    rw [hΛ₂]
    exact hΛ'' i
  have hmem : ∀ {x : Um D 𝕧} (hx : x ∈ canonicalBasis D) (Λ' : Dom R),
      (cbWt D ⟨x, hx⟩).degree ≤ N → (∀ i, (N : ℤ) ≤ Λ'.1 (R.coroot i)) →
        x ∈ canonicalBasisHW D Λ' := fun hx Λ' hxN hΛ' ↦
    mem_canonicalBasisHW_of_cbWt Λ' hx fun i ↦ (Int.ofNat_le.2 hxN).trans (hΛ' i)
  have h₁ := hmem hb Λ (by simp [N]) hΛ
  have h₂ := hmem hb'' Λ₂ (by simp [N]) hN₂
  have h₃ := hmem hb₁ Λ (by simp [N]) hΛ
  have h₄ := hmem hb₁'' Λ₂ (by simp [N]) hN₂
  have hζ₂ : Λ₂.1 - Λ.1 = ζ := add_sub_cancel_right _ _
  have key : tensorIrrForm hR Λ Λ₂ (tensorCanonical hR Λ Λ₂ (⟨b, h₁⟩, ⟨b'', h₂⟩))
      (tensorCanonical hR Λ Λ₂ (⟨b₁, h₃⟩, ⟨b₁'', h₄⟩)) =
      IrreducibleModule.tensorForm hR hvn_ratFunc Λ.1 (ζ + Λ.1)
        (u • IrreducibleModule.tensorHwv Λ.1 (ζ + Λ.1))
        (u₁ • IrreducibleModule.tensorHwv Λ.1 (ζ + Λ.1)) := by
    rw [← modTensorAct_modifiedCanonical hR hY ζ hb hb'' Λ Λ₂ hζ₂ h₁ h₂,
      ← modTensorAct_modifiedCanonical hR hY ζ hb₁ hb₁'' Λ Λ₂ hζ₂ h₃ h₄, ← hu, ← hu₁,
      modTensorAct_leftActOne Λ Λ₂ hζ₂, modTensorAct_leftActOne Λ Λ₂ hζ₂]
    rfl
  obtain ⟨a, ha⟩ := hM Λ.1 fun i ↦ (Int.self_le_toNat M).trans
    ((Int.ofNat_le.2 (le_max_left _ _)).trans (hΛ i))
  obtain ⟨c, hc⟩ := (isNegLaurent_tensorIrrForm_tensorCanonical_sub hR Λ Λ₂
    (⟨b, h₁⟩, ⟨b'', h₂⟩) (⟨b₁, h₃⟩, ⟨b₁'', h₄⟩)).exists_eq_uniformizer_mul
  have hiff : ((⟨b, h₁⟩, ⟨b'', h₂⟩) : TensorIdx Λ Λ₂) = (⟨b₁, h₃⟩, ⟨b₁'', h₄⟩) ↔
      b = b₁ ∧ b'' = b₁'' := by
    simp
  rw [pow_one] at ha
  beta_reduce at ha
  refine ⟨c - a, ?_⟩
  rw [← hu, ← hu₁, leftActOne_apply, leftActOne_apply, ← if_congr hiff rfl rfl, mul_sub,
    _root_.map_sub, ← hc, ← ha, ← key, sub_sub_sub_cancel_left]
  split_ifs <;> first | rfl | contradiction

open Classical in
include hR hY in
/-- **[Lus] Thm. 26.3.1 (a)**: `(b ◇_ζ b'', b₁ ◇_{ζ₁} b₁'') ≡ δ_{ζ,ζ₁} δ_{b,b₁} δ_{b'',b₁''}`
modulo `v⁻¹A`, `A = ℚ[[v⁻¹]] ∩ ℚ(v)` the local ring of `ℚ(v)` at `v = ∞`. Extra hypotheses
`R.IsXRegular` and `hY` (route-only, from 25.2.1; Lusztig has no assumption on the root datum). -/
theorem Modified.form_modifiedCanonical_sub_mem (ζ ζ₁ : Y →+ ℤ) {b b'' b₁ b₁'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D)
    (hb₁ : b₁ ∈ canonicalBasis D) (hb₁'' : b₁'' ∈ canonicalBasis D) :
    ∃ a : A, Modified.form R 𝕧 hvn_ratFunc (modifiedCanonical hR hY ζ hb hb'')
        (modifiedCanonical hR hY ζ₁ hb₁ hb₁'') -
          (if ζ = ζ₁ ∧ b = b₁ ∧ b'' = b₁'' then 1 else 0) = algebraMap A 𝕂 (ϖ * a) := by
  classical
  by_cases hζ : ζ = ζ₁
  · subst hζ
    obtain ⟨a, ha⟩ := form_modifiedCanonical_sub_mem_of_eq hR hY ζ hb hb'' hb₁ hb₁''
    exact ⟨a, by simpa only [true_and] using ha⟩
  · exact ⟨0, by simp [hζ, form_modifiedCanonical_of_ne hR hY hζ]⟩

open Classical in
include hR hY in
/-- [Lus] 26.3.1 (a) in terms of the basis `modifiedCanonicalBasis` of [Lus] 25.2.1 (d). -/
theorem Modified.form_modifiedCanonicalBasis_sub_mem
    (t t' : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    ∃ a : A, Modified.form R 𝕧 hvn_ratFunc (modifiedCanonicalBasis hR hY t)
        (modifiedCanonicalBasis hR hY t') - (if t = t' then 1 else 0) =
      algebraMap A 𝕂 (ϖ * a) := by
  classical
  obtain ⟨ζ, b, b''⟩ := t
  obtain ⟨ζ₁, b₁, b₁''⟩ := t'
  obtain ⟨a, ha⟩ := form_modifiedCanonical_sub_mem hR hY ζ ζ₁ b.2 b''.2 b₁.2 b₁''.2
  refine ⟨a, ?_⟩
  rw [modifiedCanonicalBasis_apply, modifiedCanonicalBasis_apply, ← ha]
  congr 1
  exact if_congr (by simp [Prod.ext_iff, Subtype.ext_iff]) rfl rfl

include hR hY in
/-- Lusztig's form on `U̇` over `ℚ(v)` is nondegenerate: a consequence of the almost
orthonormality [Lus] 26.3.1 (a) (our own deduction; Lusztig does not state it separately).

After scaling, the coordinates of `x` in the canonical basis lie in `A` and are not all in
`v⁻¹A`; by 26.3.1 (a), `(x, x)` is then congruent to a nonzero sum of squares modulo `v⁻¹A`, which
cannot vanish since `A/v⁻¹A = ℚ` is formally real. Extra hypotheses `R.IsXRegular` and `hY`
(route-only, from 25.2.1). -/
theorem Modified.eq_zero_of_forall_form_eq_zero (x : Modified R 𝕧)
    (hx : ∀ y, Modified.form R 𝕧 hvn_ratFunc x y = 0) : x = 0 := by
  classical
  set e := modifiedCanonicalBasis hR hY
  set c := e.repr x
  set S := c.support
  set F := Modified.form R 𝕧 hvn_ratFunc
  have hirr : Irreducible (ϖ : A) := irreducible_localX
  have hϖ0 : algebraMap A 𝕂 ϖ ≠ 0 := by
    rw [InfinityLocalRing.algebraMap_uniformizer]
    exact inv_ne_zero RatFunc.X_ne_zero
  by_contra hne
  have hS : S.Nonempty :=
    Finsupp.support_nonempty_iff.2 fun h ↦ hne (e.repr.map_eq_zero_iff.1 h)
  -- clear denominators
  choose m d hd using fun t ↦ InfinityLocalRing.exists_pow_mul (c t)
  set M := S.sup m
  have hd' : ∀ t ∈ S, algebraMap A 𝕂 (ϖ ^ M) * c t =
      algebraMap A 𝕂 (ϖ ^ (M - m t) * d t) := by
    intro t ht
    rw [_root_.map_mul, ← hd, ← mul_assoc, ← _root_.map_mul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup ht)]
  have hd0 : ∀ t ∈ S, ϖ ^ (M - m t) * d t ≠ 0 := by
    intro t ht h
    have := hd' t ht
    rw [h, map_zero, mul_eq_zero, map_pow] at this
    rcases this with h1 | h1
    · exact pow_ne_zero _ hϖ0 h1
    · exact Finsupp.mem_support_iff.1 ht h1
  choose! n u hu using fun t (ht : t ∈ S) ↦
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hd0 t ht) hirr
  -- divide by the smallest power of `ϖ`
  obtain ⟨t₀, ht₀, hmin⟩ := S.exists_min_image n hS
  set f : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D → A :=
    fun t ↦ (u t : A) * ϖ ^ (n t - n t₀)
  have hc : ∀ t ∈ S, algebraMap A 𝕂 (ϖ ^ M) * c t =
      algebraMap A 𝕂 (ϖ ^ n t₀) * algebraMap A 𝕂 (f t) := by
    intro t ht
    rw [hd' t ht, hu t ht, ← _root_.map_mul]
    congr 1
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (hmin t ht)]
  set y := ∑ t ∈ S, algebraMap A 𝕂 (f t) • e t
  have hy : algebraMap A 𝕂 (ϖ ^ n t₀) • y = algebraMap A 𝕂 (ϖ ^ M) • x := by
    conv_rhs => rw [← e.linearCombination_repr x, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [smul_smul, smul_smul, hc t ht]
  have hyy : F y y = 0 := by
    have h := congrArg (fun z ↦ F z z) hy
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx, mul_zero] at h
    have h0 : algebraMap A 𝕂 (ϖ ^ n t₀) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ hϖ0
    simpa [h0, hϖ0] using h
  -- `(y, y) ≡ Σ_t f_t²`
  choose a ha using form_modifiedCanonicalBasis_sub_mem hR hY
  have hF : ∀ t t', F (e t) (e t') =
      (if t = t' then 1 else 0) + algebraMap A 𝕂 (ϖ * a t t') := fun t t' ↦ by
    rw [← ha t t']
    ring
  have hexp : F y y = ∑ t ∈ S, ∑ t' ∈ S,
      algebraMap A 𝕂 (f t) * (algebraMap A 𝕂 (f t') * F (e t') (e t)) := by
    simp only [y, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
  have hsum : F y y = algebraMap A 𝕂 (∑ t ∈ S, f t ^ 2 +
      ϖ * ∑ t ∈ S, ∑ t' ∈ S, f t * f t' * a t' t) := by
    rw [hexp, _root_.map_add, map_sum, _root_.map_mul, map_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    simp only [hF, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', ht, ↓reduceIte, map_sum, Finset.mul_sum, _root_.map_mul, map_pow]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun t' _ ↦ by ring
  -- the residue of `Σ_t f_t²` vanishes, so `ϖ ∣ f_{t₀} = u_{t₀}`, a unit
  rw [hyy, eq_comm, ← map_zero (algebraMap A 𝕂)] at hsum
  have hsum' := congrArg (Ideal.Quotient.mk (Ideal.span {(ϖ : A)}))
    (InfinityLocalRing.injective_algebraMap hsum)
  rw [_root_.map_add, _root_.map_mul, Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_span_singleton_self _), zero_mul, add_zero, map_zero, map_sum] at hsum'
  simp only [map_pow] at hsum'
  have h₀ := eq_zero_of_sum_sq_eq_zero S _ hsum' t₀ ht₀
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h₀
  simp only [f, Nat.sub_self, pow_zero, mul_one] at h₀
  exact hirr.not_isUnit (isUnit_of_dvd_unit h₀ (u t₀).isUnit)


include hR hY in
/-- Lusztig's form on `U̇` is nondegenerate over any field of characteristic zero, at any
parameter transcendental over `ℚ` (from the case `ℚ(v)`, `Modified.eq_zero_of_forall_form_eq_zero`,
by `Modified.form_nondegenerate_of_transcendental`). -/
theorem Modified.eq_zero_of_forall_form_eq_zero_of_transcendental {L : Type*} [Field L]
    [CharZero L] {w : L} (hw : Transcendental ℚ w) [NeZero w] (x : Modified R w)
    (hx : ∀ y, Modified.form R w (fun _ hn ↦ LusztigF.pow_ne_one_of_transcendental hw hn) x y = 0) :
    x = 0 :=
  form_nondegenerate_of_transcendental (eq_zero_of_forall_form_eq_zero hR hY) hw x hx

end Orthonormal

end LieLean.QuantumGroup
