/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.RelativeKoszul
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Relative Koszul data for adjoint actions and tensor products

This file supplies the hypotheses of
`LieModule.ChevalleyEilenberg.RelativeKoszul.relExact` in the situation used for relative Lie
algebra cohomology: `H` acts through a linear map `η : H → L` by `ad` on `L` and by the module
action on `X` (`LieModule.ChevalleyEilenberg.DerivAction.ofMap`), and `X = X₁ ⊗ X₂` is a tensor
product of two modules with polynomial coordinates, with coordinates on `X` in the disjoint union
of the variables (`LieModule.ChevalleyEilenberg.RelativeKoszul.tensorCoord`).

## Main results

* `LieModule.ChevalleyEilenberg.RelativeKoszul.iSup_weightSpaceOf_D`,
  `iSup_weightSpaceOf_φ`: `L` and `X` are sums of weight spaces.
* `LieModule.ChevalleyEilenberg.RelativeKoszul.isLeading_tensorCoord`: leading terms on a tensor
  product.
* `LieModule.ChevalleyEilenberg.RelativeKoszul.isWeightCoord_tensorCoord`: weight coordinates on
  a tensor product.

## References

Input to Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
Thm. 6.15 (a); the arguments are our own.
-/

open Module TensorProduct MvPolynomial

noncomputable section

namespace LieModule.ChevalleyEilenberg

variable {K H L : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]

variable (M : Type*) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The action of `H` on `L` and on an `L`-module through `η : H → L`. -/
def DerivAction.ofMap (η : H →ₗ[K] L) : DerivAction K H L M where
  D := (LieAlgebra.ad K L : L →ₗ[K] Module.End K L) ∘ₗ η
  φ := (toEnd K L M : L →ₗ[K] Module.End K M) ∘ₗ η
  D_lie a x y := leibniz_lie (η a) x y
  φ_lie a x m := leibniz_lie (η a) x m

variable {M}

@[simp] lemma DerivAction.ofMap_D (η : H →ₗ[K] L) (a : H) (x : L) :
    (DerivAction.ofMap M η).D a x = ⁅η a, x⁆ := rfl

@[simp] lemma DerivAction.ofMap_φ (η : H →ₗ[K] L) (a : H) (m : M) :
    (DerivAction.ofMap M η).φ a m = ⁅η a, m⁆ := rfl

namespace RelativeKoszul

/-! ### Sums of weight spaces -/

section Weights

variable {X J : Type*} [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X]
  {V : Submodule K L} {p : L →ₗ[K] V} {Ψ : X ≃ₗ[K] MvPolynomial J K} {b : Basis J K V}
  {wt : J → Dual K H} {c : Dual K H} {η : H →ₗ[K] L} {ρ : DerivAction K H L X}

omit [LieModule K L X] in
/-- `L = V ⊕ η(H)` is a sum of weight spaces. -/
theorem iSup_weightSpaceOf_D (hr : IsRelData η ρ p) (hw : IsWeightCoord b wt ρ Ψ c) :
    ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤ := by
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨a, ha⟩ := hr.sub_mem y
  rw [← sub_add_cancel y (p y : L), ha]
  refine add_mem (Submodule.mem_iSup_of_mem 0 fun a' ↦ ?_) ?_
  · rw [hr.D_eq, LieAlgebra.ad_apply, hr.lie_eta, LinearMap.zero_apply, zero_smul]
  · have hy : (p y : L) ∈ (Submodule.span K (Set.range b)).map V.subtype := by
      rw [b.span_eq]
      exact ⟨p y, Submodule.mem_top, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at hy
    refine Submodule.span_le.mpr ?_ hy
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (wt j) fun a ↦ hw.basis a j

omit [LieModule K L X] in
/-- `X` is a sum of weight spaces. -/
theorem iSup_weightSpaceOf_φ (hw : IsWeightCoord b wt ρ Ψ c) :
    ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  rw [← Ψ.symm_apply_apply x, (Ψ x).as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ ↦ ?_
  rw [← mul_one (Ψ x |>.coeff m), ← smul_eq_mul, ← smul_monomial, map_smul]
  exact Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem (c + monoWt wt m) fun a ↦ hw.monomial a m)

end Weights

/-! ### Coordinates on a tensor product -/

section Tensor

variable {X₁ X₂ J₁ J₂ : Type*} [AddCommGroup X₁] [Module K X₁] [AddCommGroup X₂] [Module K X₂]
  (Ψ₁ : X₁ ≃ₗ[K] MvPolynomial J₁ K) (Ψ₂ : X₂ ≃ₗ[K] MvPolynomial J₂ K)

lemma tensorEquivSum_tmul (q₁ : MvPolynomial J₁ K) (q₂ : MvPolynomial J₂ K) :
    tensorEquivSum K J₁ J₂ K (q₁ ⊗ₜ q₂) = rename Sum.inl q₁ * rename Sum.inr q₂ := by
  have h1 : ((tensorEquivSum K J₁ J₂ K).toAlgHom.comp Algebra.TensorProduct.includeLeft :
      MvPolynomial J₁ K →ₐ[K] _) = rename Sum.inl :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  have h2 : ((tensorEquivSum K J₁ J₂ K).toAlgHom.comp Algebra.TensorProduct.includeRight :
      MvPolynomial J₂ K →ₐ[K] _) = rename Sum.inr :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  have e : q₁ ⊗ₜ[K] q₂ = (q₁ ⊗ₜ[K] (1 : MvPolynomial J₂ K)) * ((1 : MvPolynomial J₁ K) ⊗ₜ q₂) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e, map_mul, ← AlgHom.congr_fun h1 q₁, ← AlgHom.congr_fun h2 q₂]
  rfl

lemma tensorEquivSum_monomial (m₁ : J₁ →₀ ℕ) (m₂ : J₂ →₀ ℕ) :
    tensorEquivSum K J₁ J₂ K (monomial m₁ 1 ⊗ₜ monomial m₂ 1) = monomial (m₁.sumElim m₂) 1 := by
  rw [tensorEquivSum_tmul, rename_monomial, rename_monomial, monomial_mul_monomial, mul_one,
    Finsupp.sumElim_eq_add]

lemma tensorEquivSum_mem {a₁ a₂ : ℕ} {q₁ : MvPolynomial J₁ K} {q₂ : MvPolynomial J₂ K}
    (h₁ : q₁ ∈ restrictTotalDegree J₁ K a₁) (h₂ : q₂ ∈ restrictTotalDegree J₂ K a₂) :
    tensorEquivSum K J₁ J₂ K (q₁ ⊗ₜ q₂) ∈ restrictTotalDegree (J₁ ⊕ J₂) K (a₁ + a₂) := by
  rw [mem_restrictTotalDegree] at *
  rw [tensorEquivSum_tmul]
  exact (totalDegree_mul _ _).trans (add_le_add ((totalDegree_rename_le _ _).trans h₁)
    ((totalDegree_rename_le _ _).trans h₂))

/-- The coordinates `X₁ ⊗ X₂ ≃ K[x_j]_{j ∈ J₁} ⊗ K[x_j]_{j ∈ J₂} ≃ K[x_j]_{j ∈ J₁ ⊕ J₂}`. -/
def tensorCoord : X₁ ⊗[K] X₂ ≃ₗ[K] MvPolynomial (J₁ ⊕ J₂) K :=
  TensorProduct.congr Ψ₁ Ψ₂ ≪≫ₗ (tensorEquivSum K J₁ J₂ K).toLinearEquiv

@[simp] lemma tensorCoord_tmul (x₁ : X₁) (x₂ : X₂) :
    tensorCoord Ψ₁ Ψ₂ (x₁ ⊗ₜ x₂) = tensorEquivSum K J₁ J₂ K (Ψ₁ x₁ ⊗ₜ Ψ₂ x₂) := rfl

lemma tensorCoord_symm_tensorEquivSum (q₁ : MvPolynomial J₁ K) (q₂ : MvPolynomial J₂ K) :
    (tensorCoord Ψ₁ Ψ₂).symm (tensorEquivSum K J₁ J₂ K (q₁ ⊗ₜ q₂)) =
      Ψ₁.symm q₁ ⊗ₜ Ψ₂.symm q₂ := by
  rw [LinearEquiv.symm_apply_eq, tensorCoord_tmul, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

lemma tensorCoord_symm_monomial (m : J₁ ⊕ J₂ →₀ ℕ) :
    (tensorCoord Ψ₁ Ψ₂).symm (monomial m 1) =
      Ψ₁.symm (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) 1) ⊗ₜ
        Ψ₂.symm (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1) := by
  rw [← tensorCoord_symm_tensorEquivSum, tensorEquivSum_monomial,
    Finsupp.comapDomain_sumElim_comapDomain]

/-- The polynomials of degree `≤ n` in `J₁ ⊕ J₂` are spanned by the products of polynomials of
degrees `≤ a₁`, `≤ a₂` with `a₁ + a₂ ≤ n`. -/
lemma restrictTotalDegree_induction {n : ℕ} (Q : MvPolynomial (J₁ ⊕ J₂) K → Prop)
    (h0 : Q 0) (hadd : ∀ q q', Q q → Q q' → Q (q + q')) (hsmul : ∀ (r : K) q, Q q → Q (r • q))
    (hQ : ∀ a₁ a₂ (q₁ : MvPolynomial J₁ K) (q₂ : MvPolynomial J₂ K), a₁ + a₂ ≤ n →
      q₁ ∈ restrictTotalDegree J₁ K a₁ → q₂ ∈ restrictTotalDegree J₂ K a₂ →
        Q (tensorEquivSum K J₁ J₂ K (q₁ ⊗ₜ q₂)))
    {q : MvPolynomial (J₁ ⊕ J₂) K} (hq : q ∈ restrictTotalDegree (J₁ ⊕ J₂) K n) : Q q := by
  rw [mem_restrictTotalDegree] at hq
  rw [q.as_sum]
  refine Finset.sum_induction _ Q hadd h0 fun m hm ↦ ?_
  rw [← mul_one (q.coeff m), ← smul_eq_mul, ← smul_monomial]
  refine hsmul _ _ ?_
  rw [← Finsupp.comapDomain_sumElim_comapDomain m, ← tensorEquivSum_monomial]
  have hdeg : m.degree ≤ n := (le_totalDegree hm).trans hq
  rw [← Finsupp.comapDomain_sumElim_comapDomain m, Finsupp.sumElim_eq_add, map_add,
    Finsupp.degree_mapDomain, Finsupp.degree_mapDomain] at hdeg
  exact hQ _ _ _ _ hdeg ((mem_restrictTotalDegree _ _ _).mpr (totalDegree_monomial_le _ _))
    ((mem_restrictTotalDegree _ _ _).mpr (totalDegree_monomial_le _ _))

lemma monoWt_sumElim (wt : J₁ ⊕ J₂ → Dual K H) (m₁ : J₁ →₀ ℕ) (m₂ : J₂ →₀ ℕ) :
    monoWt wt (m₁.sumElim m₂) = monoWt (wt ∘ Sum.inl) m₁ + monoWt (wt ∘ Sum.inr) m₂ := by
  rw [Finsupp.sumElim_eq_add, monoWt,
    Finsupp.sum_add_index' (h := fun j (k : ℕ) ↦ k • wt j) (fun _ ↦ zero_smul ℕ _)
      (fun _ _ _ ↦ add_smul _ _ _),
    Finsupp.sum_mapDomain_index (h := fun j (k : ℕ) ↦ k • wt j) (fun _ ↦ zero_smul ℕ _)
      (fun _ _ _ ↦ add_smul _ _ _),
    Finsupp.sum_mapDomain_index (h := fun j (k : ℕ) ↦ k • wt j) (fun _ ↦ zero_smul ℕ _)
      (fun _ _ _ ↦ add_smul _ _ _)]
  rfl

lemma X_inl_mul_tensorEquivSum (j : J₁) (q₁ : MvPolynomial J₁ K) (q₂ : MvPolynomial J₂ K) :
    X (Sum.inl j) * tensorEquivSum K J₁ J₂ K (q₁ ⊗ₜ q₂) =
      tensorEquivSum K J₁ J₂ K ((X j * q₁) ⊗ₜ q₂) := by
  rw [tensorEquivSum_tmul, tensorEquivSum_tmul, map_mul, rename_X, mul_assoc]

lemma X_inr_mul_tensorEquivSum (j : J₂) (q₁ : MvPolynomial J₁ K) (q₂ : MvPolynomial J₂ K) :
    X (Sum.inr j) * tensorEquivSum K J₁ J₂ K (q₁ ⊗ₜ q₂) =
      tensorEquivSum K J₁ J₂ K (q₁ ⊗ₜ (X j * q₂)) := by
  rw [tensorEquivSum_tmul, tensorEquivSum_tmul, map_mul, rename_X, mul_left_comm]

variable [LieRingModule L X₁] [LieModule K L X₁] [LieRingModule L X₂] [LieModule K L X₂]
  {V : Submodule K L}

/-- **Leading terms on a tensor product**: if the basis vectors indexed by `J₁` act on `X₁` with
leading term `x_j` and do not raise the degree on `X₂`, and symmetrically for `J₂`, then the basis
acts on `X₁ ⊗ X₂` with leading terms `x_j` in the coordinates `tensorCoord`. -/
theorem isLeading_tensorCoord (b : Basis (J₁ ⊕ J₂) K V)
    (h₁ : ∀ j n (q : MvPolynomial J₁ K), q ∈ restrictTotalDegree J₁ K n →
      Ψ₁ ⁅(b (Sum.inl j) : L), Ψ₁.symm q⁆ - X j * q ∈ restrictTotalDegree J₁ K n)
    (h₁' : ∀ j n (q : MvPolynomial J₂ K), q ∈ restrictTotalDegree J₂ K n →
      Ψ₂ ⁅(b (Sum.inl j) : L), Ψ₂.symm q⁆ ∈ restrictTotalDegree J₂ K n)
    (h₂ : ∀ j n (q : MvPolynomial J₁ K), q ∈ restrictTotalDegree J₁ K n →
      Ψ₁ ⁅(b (Sum.inr j) : L), Ψ₁.symm q⁆ ∈ restrictTotalDegree J₁ K n)
    (h₂' : ∀ j n (q : MvPolynomial J₂ K), q ∈ restrictTotalDegree J₂ K n →
      Ψ₂ ⁅(b (Sum.inr j) : L), Ψ₂.symm q⁆ - X j * q ∈ restrictTotalDegree J₂ K n) :
    IsLeading (tensorCoord Ψ₁ Ψ₂) b := by
  intro j n q hq
  refine restrictTotalDegree_induction
    (fun q ↦ tensorCoord Ψ₁ Ψ₂ ⁅(b j : L), (tensorCoord Ψ₁ Ψ₂).symm q⁆ - X j * q ∈
      restrictTotalDegree (J₁ ⊕ J₂) K n) (by simp) (fun q q' h h' ↦ ?_) (fun r q h ↦ ?_)
    (fun a₁ a₂ q₁ q₂ ha hq₁ hq₂ ↦ ?_) hq
  · simpa only [map_add, lie_add, mul_add, add_sub_add_comm] using add_mem h h'
  · simpa only [map_smul, lie_smul, mul_smul_comm, ← smul_sub] using Submodule.smul_mem _ r h
  · have hmono : restrictTotalDegree (J₁ ⊕ J₂) K (a₁ + a₂) ≤ restrictTotalDegree (J₁ ⊕ J₂) K n :=
      fun q hq ↦ (mem_restrictTotalDegree _ _ _).mpr
        (((mem_restrictTotalDegree _ _ _).mp hq).trans ha)
    refine hmono ?_
    rw [tensorCoord_symm_tensorEquivSum, TensorProduct.LieModule.lie_tmul_right, map_add,
      tensorCoord_tmul, tensorCoord_tmul, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    rcases j with j | j
    · rw [X_inl_mul_tensorEquivSum, add_sub_right_comm, ← map_sub, ← TensorProduct.sub_tmul]
      exact add_mem (tensorEquivSum_mem (h₁ j a₁ q₁ hq₁) hq₂)
        (tensorEquivSum_mem hq₁ (h₁' j a₂ q₂ hq₂))
    · rw [X_inr_mul_tensorEquivSum, add_sub_assoc, ← map_sub, ← TensorProduct.tmul_sub]
      exact add_mem (tensorEquivSum_mem (h₂ j a₁ q₁ hq₁) hq₂)
        (tensorEquivSum_mem hq₁ (h₂' j a₂ q₂ hq₂))

/-- **Weight coordinates on a tensor product**: monomials in `tensorCoord` are tensors of weight
vectors, of weight `c₁ + c₂ + Σ mⱼ wt j`. -/
theorem isWeightCoord_tensorCoord {η : H →ₗ[K] L} (b : Basis (J₁ ⊕ J₂) K V)
    {wt : J₁ ⊕ J₂ → Dual K H} {c₁ c₂ : Dual K H}
    (hb : ∀ a j, ⁅η a, (b j : L)⁆ = wt j a • (b j : L))
    (hm₁ : ∀ a m, ⁅η a, Ψ₁.symm (monomial m 1)⁆ =
      (c₁ + monoWt (wt ∘ Sum.inl) m) a • Ψ₁.symm (monomial m 1))
    (hm₂ : ∀ a m, ⁅η a, Ψ₂.symm (monomial m 1)⁆ =
      (c₂ + monoWt (wt ∘ Sum.inr) m) a • Ψ₂.symm (monomial m 1)) :
    IsWeightCoord b wt (DerivAction.ofMap (X₁ ⊗[K] X₂) η) (tensorCoord Ψ₁ Ψ₂) (c₁ + c₂) where
  basis a j := hb a j
  monomial a m := by
    rw [DerivAction.ofMap_φ, tensorCoord_symm_monomial, TensorProduct.LieModule.lie_tmul_right,
      hm₁, hm₂, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul]
    conv_rhs => rw [← Finsupp.comapDomain_sumElim_comapDomain m, monoWt_sumElim,
      Finsupp.comapDomain_sumElim_comapDomain m]
    congr 1
    simp only [LinearMap.add_apply]
    ring

end Tensor

end RelativeKoszul

end LieModule.ChevalleyEilenberg
