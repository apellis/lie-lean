/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Blocks
import LieLean.Algebra.Lie.KacMoody.WeightBasis
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products in the category `𝒪`

Let `V, W` be modules over the Kac–Moody algebra `𝔤(A)`, and let `V ⊗ W` be their tensor product
with the Lie module structure `x (v ⊗ w) = x v ⊗ w + v ⊗ x w` (Mathlib's
`TensorProduct.LieModule`). We show:

* if `V, W` are `𝔥`-diagonalizable, so is `V ⊗ W`, with
  `(V ⊗ W)_ξ = ∑_μ V_μ ⊗ W_{ξ - μ}`;
* if `V, W` lie in `𝒪`, so does `V ⊗ W`, and `ch (V ⊗ W) = ch V · ch W` in `ℰ`;
* if moreover `V, W` are integrable, so is `V ⊗ W`; hence, for `A` a symmetrizable generalized
  Cartan matrix, `V ⊗ W` is a direct sum of modules `L(Λ'')`, `Λ''` dominant integral
  ([Kac] §10.7), with multiplicities determined by `ch V · ch W`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.diagWeightBasis`: a basis of weight vectors of an
  `𝔥`-diagonalizable module.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.weightSpace_tensorProduct`:
  `(V ⊗ W)_ξ = ⨆_μ V_μ ⊗ W_{ξ - μ}`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.tensorProduct`: `𝒪` is closed under tensor
  products ([Kac] §9.1).
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.character_tensorProduct`:
  `ch (V ⊗ W) = ch V · ch W` ([Kum] Def. 2.1.1 (d)).
* `Matrix.Realization.KacMoodyAlgebra.IsIntegrable.tensorProduct`: tensor products of integrable
  modules are integrable (integrability as in [Kac] §3.6).
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.exists_isInternal_tensorProduct`:
  `L(Λ) ⊗ L(Λ')` is a direct sum of modules `L(Λ'')`, `Λ''` dominant integral, for `Λ, Λ'`
  dominant integral ([Kac] §10.7).

## Proof

We reconstructed the (standard) arguments. An `𝔥`-diagonalizable module has a basis of weight
vectors (collect bases of the weight spaces), and the tensor product `bᵢ ⊗ cⱼ` of two such bases
is a basis of weight vectors of `V ⊗ W`, of weights `wt i + wt j`. For a module with a basis of
weight vectors, `M_ξ` is spanned by the basis vectors of weight `ξ`, so `dim M_ξ` is their number
and `ch M = ∑ₖ e^{wt k}` (a summable family in `ℰ`). For `M = V ⊗ W` this family is the product of
the families for `V` and `W`, and Mathlib's `HahnSeries.SummableFamily.hsum_mul` gives
`ch (V ⊗ W) = ch V · ch W`. Local nilpotence of `eᵢ` on `V ⊗ W` follows from the binomial formula
for the commuting operators `eᵢ ⊗ 1` and `1 ⊗ eᵢ`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.6, §9.1, §9.7,
  §10.7.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §2.1.
-/

open Module LieModule TensorProduct

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  {M V W : Type*} [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M] [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W]
  [Module K W] [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

/-! ### Modules with a basis of weight vectors -/

section WeightBasis

variable {κ : Type*} {b : Basis κ K M} {wt : κ → Dual K H}
  (hb : ∀ k, b k ∈ weightSpace P M (wt k))
include hb

omit hb in
lemma top_le_iSup_span_of_basis :
    ⊤ ≤ ⨆ η, Submodule.span K (b '' {k | wt k = η}) := by
  rw [← b.span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact Submodule.mem_iSup_of_mem (wt k) (Submodule.subset_span ⟨k, rfl, rfl⟩)

/-- If `M` has a basis `b` of weight vectors, then `M_ξ` is spanned by the `b k` of weight `ξ`. -/
theorem weightSpace_eq_span_of_basis (ξ : Dual K H) :
    weightSpace P M ξ = Submodule.span K (b '' {k | wt k = ξ}) := by
  have hle (η : Dual K H) : Submodule.span K (b '' {k | wt k = η}) ≤ weightSpace P M η := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl, rfl⟩
    exact hb k
  refine le_antisymm (fun x hx ↦ ?_) (hle ξ)
  exact mem_of_mem_iSup_of_le (h P) _ hle hx (top_le_iSup_span_of_basis (b := b) (wt := wt) trivial)

/-- A module with a basis of weight vectors is `𝔥`-diagonalizable. -/
theorem isHDiagonalizable_of_basis : IsHDiagonalizable P M := by
  refine eq_top_iff.mpr ((top_le_iSup_span_of_basis (b := b) (wt := wt)).trans
    (iSup_mono fun η ↦ ?_))
  rw [weightSpace_eq_span_of_basis hb]

/-- If `M` has a basis of weight vectors, and only finitely many of them have weight `ξ`, then
`dim M_ξ` is their number. -/
theorem finrank_weightSpace_of_basis (ξ : Dual K H) (hfin : {k | wt k = ξ}.Finite) :
    finrank K (weightSpace P M ξ) = hfin.toFinset.card := by
  have hrange : b '' {k | wt k = ξ} =
      Set.range (b ∘ (Subtype.val : ↥(hfin.toFinset : Set κ) → κ)) := by
    rw [Set.Finite.coe_toFinset, Set.image_eq_range]
    rfl
  rw [weightSpace_eq_span_of_basis hb, hrange,
    finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)]
  simp

end WeightBasis

section Diagonalizable

/-- `V_μ ⊗ W_ν ⊆ (V ⊗ W)_{μ + ν}`. -/
lemma tmul_mem_weightSpace {μ ν : Dual K H} {v : V} {w : W} (hv : v ∈ weightSpace P V μ)
    (hw : w ∈ weightSpace P W ν) : v ⊗ₜ[K] w ∈ weightSpace P (V ⊗[K] W) (μ + ν) := fun a ↦ by
  rw [LieModule.lie_tmul_right, hv a, hw a, LinearMap.add_apply, add_smul, smul_tmul',
    tmul_smul]

variable (hV : IsHDiagonalizable P V) (hW : IsHDiagonalizable P W)

/-- The basis of weight vectors `bᵢ ⊗ cⱼ` of `V ⊗ W`. -/
abbrev tensorWeightBasis :
    Basis (DiagWeightBasisIndex P V × DiagWeightBasisIndex P W) K (V ⊗[K] W) :=
  (diagWeightBasis hV).tensorProduct (diagWeightBasis hW)

lemma tensorWeightBasis_mem (p : DiagWeightBasisIndex P V × DiagWeightBasisIndex P W) :
    tensorWeightBasis hV hW p ∈ weightSpace P (V ⊗[K] W) (p.1.1 + p.2.1) := by
  rw [Basis.tensorProduct_apply']
  exact tmul_mem_weightSpace (diagWeightBasis_mem hV p.1) (diagWeightBasis_mem hW p.2)

include hV hW in
/-- The tensor product of `𝔥`-diagonalizable modules is `𝔥`-diagonalizable. -/
theorem IsHDiagonalizable.tensorProduct : IsHDiagonalizable P (V ⊗[K] W) :=
  isHDiagonalizable_of_basis (tensorWeightBasis_mem hV hW)

include hV hW in
/-- **Weight spaces of a tensor product**: `(V ⊗ W)_ξ = ⨆_μ V_μ ⊗ W_{ξ - μ}` for
`𝔥`-diagonalizable `V, W`. -/
theorem weightSpace_tensorProduct (ξ : Dual K H) :
    weightSpace P (V ⊗[K] W) ξ = ⨆ μ, LinearMap.range
      (TensorProduct.map (weightSpace P V μ).subtype (weightSpace P W (ξ - μ)).subtype) := by
  refine le_antisymm ?_ (iSup_le fun μ ↦ ?_)
  · rw [weightSpace_eq_span_of_basis (tensorWeightBasis_mem hV hW), Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    refine Submodule.mem_iSup_of_mem p.1.1 ⟨⟨diagWeightBasis hV p.1, diagWeightBasis_mem hV p.1⟩ ⊗ₜ
      ⟨diagWeightBasis hW p.2, ?_⟩, ?_⟩
    · have := diagWeightBasis_mem hW p.2
      rwa [show p.2.1 = ξ - p.1.1 by rw [← hp]; abel] at this
    · rw [map_tmul, Basis.tensorProduct_apply']
      rfl
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul v w =>
      have := tmul_mem_weightSpace v.2 w.2
      rwa [add_sub_cancel] at this
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

end Diagonalizable

/-! ### Characters of modules with a basis of weight vectors -/

variable [CharZero K]

/-- If a module `M` in `𝒪` has a basis `b` of weight vectors `b k ∈ M_{wt k}`, then
`ch M = ∑ₖ e^{wt k}`, for any summable family with these terms. -/
theorem IsCategoryO.character_eq_hsum (hM : IsCategoryO P M) {κ : Type*} {b : Basis κ K M}
    {wt : κ → Dual K H} (hb : ∀ k, b k ∈ weightSpace P M (wt k))
    (s : HahnSeries.SummableFamily P.WeightOrd ℤ κ)
    (hs : ∀ k, s k = CharacterRing.exp P ℤ (wt k)) :
    hM.character = s.hsum := by
  ext ξ
  have hset (k : κ) : CharacterRing.coeffAt (s k : P.CharacterRing ℤ) ξ ≠ 0 ↔ wt k = ξ := by
    classical
    rw [hs, CharacterRing.coeff_exp]
    split_ifs with h <;> simp [h, eq_comm]
  have hfin : {k | wt k = ξ}.Finite :=
    (s.finite_co_support (WeightOrd.toWeightOrd P ξ)).subset fun k hk ↦ (hset k).mpr hk
  have hsum := HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset (s := s)
    (g := WeightOrd.toWeightOrd P ξ) (t := hfin.toFinset)
    (fun k hk ↦ by simpa using (hset k).mp hk)
  rw [IsCategoryO.coeffAt_character, finrank_weightSpace_of_basis hb ξ hfin]
  change _ = HahnSeries.coeff s.hsum (WeightOrd.toWeightOrd P ξ)
  rw [hsum, Finset.sum_congr rfl fun k hk ↦
    (?_ : CharacterRing.coeffAt (s k : P.CharacterRing ℤ) ξ = 1)]
  · simp
  · classical
    rw [hs, CharacterRing.coeff_exp]
    simp [((Set.Finite.mem_toFinset hfin).mp hk).symm]

/-! ### Tensor products in `𝒪` -/

omit [CharZero K] in
lemma weightSpace_weightBasisIndex_ne_bot (hV : IsHDiagonalizable P V)
    (k : DiagWeightBasisIndex P V) :
    weightSpace P V k.1 ≠ ⊥ := fun h0 ↦ (diagWeightBasis hV).ne_zero k (by
  have := diagWeightBasis_mem hV k
  rwa [h0, Submodule.mem_bot] at this)

namespace IsCategoryO

/-- The summable family `k ↦ e^{wt k}` in `ℰ` attached to the basis `diagWeightBasis` of weight
vectors of a module in `𝒪`; its sum is the character
(`IsCategoryO.character_eq_hsum_weightFamily`). -/
def weightFamily (hV : IsCategoryO P V) :
    HahnSeries.SummableFamily P.WeightOrd ℤ (DiagWeightBasisIndex P V) where
  toFun k := CharacterRing.exp P ℤ k.1
  isPWO_iUnion_support' := by
    obtain ⟨s, hs⟩ := hV.exists_finset
    refine (WeightOrd.isPWO_iff P).mpr ⟨s, fun μ hμ ↦ ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hμ
    have hμk : μ = WeightOrd.toWeightOrd P k.1 := HahnSeries.support_single_subset hk
    obtain ⟨Λ, hΛ, c, hc, hkc⟩ :=
      hs k.1 (weightSpace_weightBasisIndex_ne_bot hV.iSup_weightSpaceOfMap_eq_top k)
    exact ⟨Λ, hΛ, c, hc, by rw [hμk, WeightOrd.ofWeightOrd_toWeightOrd, hkc]⟩
  finite_co_support' g := by
    have := hV.finiteDimensional_weightSpaceOfMap (WeightOrd.ofWeightOrd P g)
    have : Finite (Basis.ofVectorSpaceIndex K (weightSpace P V (WeightOrd.ofWeightOrd P g))) :=
      Module.Finite.finite_basis (Basis.ofVectorSpace K _)
    refine (Set.finite_univ.image (Sigma.mk (WeightOrd.ofWeightOrd P g))).subset ?_
    rintro ⟨μ, i⟩ hk
    have hμ : μ = WeightOrd.ofWeightOrd P g := by
      by_contra hne
      apply hk
      have hg : g ≠ WeightOrd.toWeightOrd P μ := fun h ↦
        hne (by rw [h, WeightOrd.ofWeightOrd_toWeightOrd])
      simp [CharacterRing.exp, hg]
    subst hμ
    exact ⟨i, trivial, rfl⟩

lemma weightFamily_apply (hV : IsCategoryO P V) (k : DiagWeightBasisIndex P V) :
    hV.weightFamily k = CharacterRing.exp P ℤ k.1 :=
  rfl

/-- The character of a module in `𝒪` is the sum `∑ₖ e^{wt k}` over a basis of weight vectors. -/
theorem character_eq_hsum_weightFamily (hV : IsCategoryO P V) :
    hV.character = hV.weightFamily.hsum :=
  hV.character_eq_hsum (diagWeightBasis_mem hV.iSup_weightSpaceOfMap_eq_top) _
    hV.weightFamily_apply

variable (hV : IsCategoryO P V) (hW : IsCategoryO P W)

include hV hW in
/-- **`𝒪` is closed under tensor products** ([Kac] §9.1): if `V` and `W` lie in `𝒪`, so
does `V ⊗ W`. -/
theorem tensorProduct : IsCategoryO P (V ⊗[K] W) := by
  have hb := tensorWeightBasis_mem hV.iSup_weightSpaceOfMap_eq_top hW.iSup_weightSpaceOfMap_eq_top
  have hfin (ξ : Dual K H) : {p : DiagWeightBasisIndex P V × DiagWeightBasisIndex P W |
      p.1.1 + p.2.1 = ξ}.Finite := by
    refine ((hV.weightFamily.mul hW.weightFamily).finite_co_support
      (WeightOrd.toWeightOrd P ξ)).subset fun p hp ↦ ?_
    simp only [Set.mem_ofPred_eq, HahnSeries.SummableFamily.mul_toFun, weightFamily_apply,
      ← CharacterRing.exp_add] at hp ⊢
    change CharacterRing.coeffAt (CharacterRing.exp P ℤ (p.1.1 + p.2.1)) ξ ≠ 0
    rw [hp, CharacterRing.coeff_exp_self]
    exact one_ne_zero
  refine ⟨IsHDiagonalizable.tensorProduct hV.iSup_weightSpaceOfMap_eq_top
    hW.iSup_weightSpaceOfMap_eq_top, fun ξ ↦ ?_, ?_⟩
  · change FiniteDimensional K (weightSpace P _ ξ)
    rw [weightSpace_eq_span_of_basis hb]
    exact FiniteDimensional.span_of_finite K ((hfin ξ).image _)
  · classical
    obtain ⟨s, hs⟩ := hV.exists_finset
    obtain ⟨t, ht⟩ := hW.exists_finset
    refine ⟨(s ×ˢ t).image fun x ↦ x.1 + x.2, fun ξ hξ ↦ ?_⟩
    change weightSpace P _ ξ ≠ ⊥ at hξ
    rw [weightSpace_eq_span_of_basis hb] at hξ
    obtain ⟨p, hp⟩ : ∃ p : DiagWeightBasisIndex P V × DiagWeightBasisIndex P W,
        p.1.1 + p.2.1 = ξ := by
      by_contra! h
      apply hξ
      rw [Submodule.span_eq_bot]
      rintro _ ⟨q, hq, rfl⟩
      exact absurd hq (h q)
    obtain ⟨Λ, hΛ, c, hc, hμ⟩ :=
      hs p.1.1 (weightSpace_weightBasisIndex_ne_bot hV.iSup_weightSpaceOfMap_eq_top p.1)
    obtain ⟨Λ', hΛ', c', hc', hν⟩ :=
      ht p.2.1 (weightSpace_weightBasisIndex_ne_bot hW.iSup_weightSpaceOfMap_eq_top p.2)
    refine ⟨Λ + Λ', Finset.mem_image.mpr ⟨(Λ, Λ'), Finset.mem_product.mpr ⟨hΛ, hΛ'⟩, rfl⟩,
      c + c', add_nonneg hc hc', ?_⟩
    rw [← hp, hμ, hν, map_add]
    abel

/-- **Characters are multiplicative** ([Kum] Def. 2.1.1 (d)): `ch (V ⊗ W) = ch V · ch W` for `V, W`
in `𝒪`. -/
theorem character_tensorProduct :
    (hV.tensorProduct hW).character = hV.character * hW.character := by
  rw [(hV.tensorProduct hW).character_eq_hsum
      (tensorWeightBasis_mem hV.iSup_weightSpaceOfMap_eq_top hW.iSup_weightSpaceOfMap_eq_top)
      (hV.weightFamily.mul hW.weightFamily) fun p ↦ by
        rw [HahnSeries.SummableFamily.mul_toFun, weightFamily_apply, weightFamily_apply,
          CharacterRing.exp_add],
    HahnSeries.SummableFamily.hsum_mul, ← character_eq_hsum_weightFamily,
    ← character_eq_hsum_weightFamily]

/-- The multiplicities `[V ⊗ W : L(μ)]` are determined by `ch V · ch W`: they are the coefficients
of the unique `c ∈ ℰ` with `∑_μ c_μ ch L(μ) = ch V · ch W` (`sumIrreducibleCharacter_injective`). -/
theorem sumIrreducibleCharacter_multiplicities_tensorProduct :
    sumIrreducibleCharacter P (hV.tensorProduct hW).multiplicities =
      hV.character * hW.character := by
  rw [← character_eq_sumIrreducibleCharacter, character_tensorProduct]

end IsCategoryO

/-! ### Integrable modules -/

omit [CharZero K] in
/-- If `x` acts locally nilpotently on `V` and on `W`, it acts locally nilpotently on `V ⊗ W`. -/
theorem exists_pow_toEnd_tensorProduct_eq_zero (x : P.KacMoodyAlgebra)
    (hV : ∀ v : V, ∃ n : ℕ, (toEnd K P.KacMoodyAlgebra V x ^ n) v = 0)
    (hW : ∀ w : W, ∃ n : ℕ, (toEnd K P.KacMoodyAlgebra W x ^ n) w = 0) (t : V ⊗[K] W) :
    ∃ n : ℕ, (toEnd K P.KacMoodyAlgebra (V ⊗[K] W) x ^ n) t = 0 := by
  set X := toEnd K P.KacMoodyAlgebra V x
  set Y := toEnd K P.KacMoodyAlgebra W x
  set T := toEnd K P.KacMoodyAlgebra (V ⊗[K] W) x
  have hT : T = X.rTensor W + Y.lTensor V := LinearMap.ext fun _ ↦ rfl
  have hcomm : Commute (X.rTensor W) (Y.lTensor V) := by
    change _ * _ = _ * _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  have hpow {Z : Module.End K V} {v : V} {a n : ℕ} (ha : (Z ^ a) v = 0) (h : a ≤ n) :
      (Z ^ n) v = 0 := by
    rw [← Nat.sub_add_cancel h, pow_add, Module.End.mul_apply, ha, map_zero]
  have hpow' {Z : Module.End K W} {w : W} {a n : ℕ} (ha : (Z ^ a) w = 0) (h : a ≤ n) :
      (Z ^ n) w = 0 := by
    rw [← Nat.sub_add_cancel h, pow_add, Module.End.mul_apply, ha, map_zero]
  suffices t ∈ T.maxGenEigenspace 0 by
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp this
    exact ⟨k, by simpa using hk⟩
  induction t with
  | tmul v w =>
    obtain ⟨a, ha⟩ := hV v
    obtain ⟨b, hb⟩ := hW w
    refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨a + b, ?_⟩
    rw [zero_smul, sub_zero, hT, hcomm.add_pow', LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hm
    rw [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.rTensor_pow, LinearMap.lTensor_pow,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
    rcases le_or_gt a m.1 with h | h
    · rw [hpow ha h, zero_tmul, smul_zero]
    · rw [hpow' hb (by omega), tmul_zero, smul_zero]
  | add x y hx hy => exact add_mem hx hy

omit [CharZero K] in
/-- **Tensor products of integrable modules are integrable** (integrability as in [Kac] §3.6). -/
theorem IsIntegrable.tensorProduct (hV : IsIntegrable P V) (hW : IsIntegrable P W) :
    IsIntegrable P (V ⊗[K] W) where
  isHDiagonalizable := hV.isHDiagonalizable.tensorProduct hW.isHDiagonalizable
  exists_pow_e_eq_zero i :=
    exists_pow_toEnd_tensorProduct_eq_zero _ (hV.exists_pow_e_eq_zero i) (hW.exists_pow_e_eq_zero i)
  exists_pow_f_eq_zero i :=
    exists_pow_toEnd_tensorProduct_eq_zero _ (hV.exists_pow_f_eq_zero i) (hW.exists_pow_f_eq_zero i)

open scoped Classical in
/-- **Tensor products of integrable highest-weight modules** ([Kac] §10.7): for `A` a
symmetrizable generalized Cartan matrix, `K` of characteristic zero and `Λ, Λ'` dominant integral,
`L(Λ) ⊗ L(Λ')` is the internal direct sum of a family of submodules, each isomorphic to some
`L(Λ'')` with `Λ''` dominant integral. The multiplicities are determined by
`ch L(Λ) · ch L(Λ')` (`IsCategoryO.sumIrreducibleCharacter_multiplicities_tensorProduct`). -/
theorem IrreducibleModule.exists_isInternal_tensorProduct [FiniteDimensional K H]
    (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable) {Λ Λ' : Dual K H}
    (hΛ : P.IsDominantIntegral Λ) (hΛ' : P.IsDominantIntegral Λ') :
    ∃ s : Set (LieSubmodule K P.KacMoodyAlgebra
        (IrreducibleModule P Λ ⊗[K] IrreducibleModule P Λ')),
      DirectSum.IsInternal (fun N : s ↦
        (N : Submodule K (IrreducibleModule P Λ ⊗[K] IrreducibleModule P Λ'))) ∧
      ∀ N ∈ s, ∃ Λ'', P.IsDominantIntegral Λ'' ∧
        Nonempty (N ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ'') :=
  IsCategoryO.exists_isInternal_irreducibleModule hA hS
    ((isCategoryO P Λ).tensorProduct (isCategoryO P Λ'))
    (((isIntegrable_iff P hA).mpr hΛ).tensorProduct ((isIntegrable_iff P hA).mpr hΛ'))

end Matrix.Realization.KacMoodyAlgebra

end
