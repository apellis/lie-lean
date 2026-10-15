/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CategoryOIntTensor
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.CrystalDecomposition
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorProductRuleIntegrable
import LieLean.RepresentationTheory.Crystal.TensorHighestWeight

/-!
# Decomposition of `L_q(μ) ⊗ L_q(ν)` by crystal bases

**[Kas] Prop. 4.2.** For dominant weights `λ`, `μ`, Kashiwara decomposes `V(λ) ⊗ V(μ)` as the
direct sum of the `V(λ + wt b)` over the elements `b ∈ B(μ)` with `εᵢ(b) ≤ ⟨hᵢ, λ⟩` for all `i`.
The proof combines three results:

* the tensor product of the crystal bases `(L(μ), B(μ))`, `(L(ν), B(ν))` is a crystal base of
  `L_q(μ) ⊗ L_q(ν)` whose crystal is `B(ν) ⊗ B(μ)` (`TensorModule.isCrystalBase_tensor_integrable`,
  `TensorModule.nonempty_crystalEquiv_integrable`; [HK] Thm. 4.4.1, [Kas] Thm. 4.1);
* in `𝒪_int` the irreducible summands of a module correspond to the highest weight elements of
  its crystal base, with the same weights (`GrandLoop.exists_crystalEquiv_sigma_of_isCategoryOInt`;
  [Kas] Thm. 4.3, (4.6));
* `b₂ ⊗ b₁` is a highest weight element iff `b₂` is highest and `εᵢ(b₁) ≤ ⟨hᵢ, wt b₂⟩`
  (`Crystal.IsSeminormal.isHighestWeight_tensor_iff`; [Kas] Lemma 4.1), and `u_ν` is the only
  highest weight element of `B(ν)`.

The tensor product is in `𝒪_int` by `TensorModule.isCategoryOInt`.

## Main result

* `GrandLoop.nonempty_tensor_equiv_dfinsupp`: `L_q(μ) ⊗ L_q(ν) ≅ ⊕_b L_q(ν + wt b)`, the sum over
  the `b ∈ B(μ)` with `εᵢ(b) ≤ ⟨i, ν⟩` for all `i`.

With the library's (Lusztig's) coproduct the two tensor factors are exchanged compared with
Kashiwara's: his `V(λ) ⊗ V(μ)` corresponds to `L_q(μ) ⊗ L_q(ν)` with `ν = λ`.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §4.4–4.5.
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
-/

noncomputable section

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B₁ B₂ : Type*}
  {C₁ : Crystal D B₁} {C₂ : Crystal D B₂} {J : Type*} {B : J → Type*} {C : ∀ j, Crystal D (B j)}

/-- **Highest weight elements of a tensor product** ([Kas] §4.5, the argument for Prop. 4.2). Let
`C₂ ⊗ C₁` be isomorphic to a disjoint union of crystals `C j`, each with exactly one highest weight
element `t j`, and let `t₂` be the only highest weight element of `C₂`, of weight `x`, with
`nᵢ = ⟨hᵢ, x⟩`. Then the summands are indexed by the `b ∈ C₁` with `εᵢ(b) ≤ nᵢ` for all `i` (the
highest weight elements of `C₂ ⊗ C₁` are the `t₂ ⊗ b`, [Kas] Lemma 4.1), and
`wt (t j) = x + wt b`. -/
theorem exists_equiv_isHighestWeight_tensor (t : ∀ j, B j) (t₂ : B₂) {x : X} {n : ι → ℤ}
    (hx : C₂.wt t₂ = x) (hn : ∀ i, D.coroot i x = n i) (h₁ : C₁.IsSeminormal)
    (h₂ : C₂.IsSeminormal) (ht : ∀ j b, (C j).IsHighestWeight b ↔ b = t j)
    (ht₂ : ∀ b, C₂.IsHighestWeight b ↔ b = t₂) (Ξ : Equiv (Crystal.sigma C) (C₂.tensor C₁)) :
    ∃ e : J ≃ {b // ∀ i, C₁.ε i b ≤ (n i : WithBot ℤ)},
      ∀ j, (C j).wt (t j) = x + C₁.wt (e j) := by
  have hhw : ∀ b : B₂ × B₁, (C₂.tensor C₁).IsHighestWeight b ↔
      b.1 = t₂ ∧ ∀ i, C₁.ε i b.2 ≤ (n i : WithBot ℤ) := by
    rintro ⟨b₂, b₁⟩
    rw [IsSeminormal.isHighestWeight_tensor_iff h₂ h₁, ht₂]
    exact and_congr_right fun h ↦ by rw [h, hx]; simp only [hn]
  have htop : ∀ j, (C₂.tensor C₁).IsHighestWeight (Ξ ⟨j, t j⟩) := fun j ↦ by
    rw [← Equiv.coe_toStrictHom, StrictHom.isHighestWeight_apply_iff, isHighestWeight_sigma_iff,
      ht]
  let f : J → {b // ∀ i, C₁.ε i b ≤ (n i : WithBot ℤ)} :=
    fun j ↦ ⟨(Ξ ⟨j, t j⟩).2, ((hhw _).1 (htop j)).2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun j j' h ↦ ?_, fun b ↦ ?_⟩
    · have h2 : (Ξ ⟨j, t j⟩).2 = (Ξ ⟨j', t j'⟩).2 := congrArg Subtype.val h
      have h1 : (Ξ ⟨j, t j⟩).1 = (Ξ ⟨j', t j'⟩).1 :=
        ((hhw _).1 (htop j)).1.trans ((hhw _).1 (htop j')).1.symm
      exact (Sigma.mk.inj_iff.1 (Ξ.toEquiv.injective (Prod.ext h1 h2))).1
    · obtain ⟨⟨j, x⟩, hx⟩ := Ξ.toEquiv.surjective (t₂, b.1)
      rw [Equiv.coe_toEquiv] at hx
      have hh : (C₂.tensor C₁).IsHighestWeight (Ξ ⟨j, x⟩) := by
        rw [hx, hhw]
        exact ⟨rfl, b.2⟩
      rw [← Equiv.coe_toStrictHom, StrictHom.isHighestWeight_apply_iff,
        isHighestWeight_sigma_iff, ht] at hh
      subst hh
      exact ⟨j, Subtype.ext (congrArg Prod.snd hx)⟩
  refine ⟨_root_.Equiv.ofBijective f hf, fun j ↦ ?_⟩
  have h := Ξ.wt_apply ⟨j, t j⟩
  change C₂.wt (Ξ _).1 + C₁.wt (Ξ _).2 = _ at h
  rw [((hhw _).1 (htop j)).1, hx] at h
  exact h.symm

end Crystal

namespace LieLean.QuantumGroup
namespace IrreducibleModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-- The identification `L_q(Λ) ≃ L_q(Λ')` for equal weights `Λ = Λ'`. -/
def equivOfEq {Λ Λ' : Y →+ ℤ} (h : Λ = Λ') :
    IrreducibleModule R v Λ ≃ₗ[QuantumGroup R v] IrreducibleModule R v Λ' := by
  subst h
  exact LinearEquiv.refl _ _

end IrreducibleModule

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k] {hvt : Transcendental ℚ v}
  {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] [IsDomain A]
  [IsDiscreteValuationRing A] [Finite I] {ϖ : A}
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

include hinj hϖ hϖv hk hfund

/-- The crystal of the crystal base `(L(μ) ⊗ L(ν), B(μ) ⊗ B(ν))` of `L_q(μ) ⊗ L_q(ν)`, which is
`B(ν) ⊗ B(μ)` ([HK] Thm. 4.4.1), is a disjoint union `⊔ⱼ B(λⱼ)` with
`L_q(μ) ⊗ L_q(ν) ≅ ⊕ⱼ L_q(λⱼ)` ([Kas] Thm. 4.3, (4.6)). -/
theorem exists_crystalEquiv_sigma_tensor (μ ν : Dom R) :
    ∃ (s : Set (Submodule (QuantumGroup R v)
        (TensorModule k (IrreducibleModule R v μ.1) (IrreducibleModule R v ν.1))))
      (Λ : s → Dom R)
      (_ : Crystal.Equiv (Crystal.sigma fun j ↦ crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ j))
        ((crystalHW hvt hR hinj hϖ hϖv hk hfund ν).tensor
          (crystalHW hvt hR hinj hϖ hϖv hk hfund μ))),
      Nonempty ((Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v]
        TensorModule k (IrreducibleModule R v μ.1) (IrreducibleModule R v ν.1)) := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hB₁ := isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund μ
  have hB₂ := isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund ν
  have hO : IsCategoryOInt R v
      (TensorModule k (IrreducibleModule R v μ.1) (IrreducibleModule R v ν.1)) :=
    TensorModule.isCategoryOInt hR hv' (IrreducibleModule.isCategoryOInt hR hv' μ.2)
      (IrreducibleModule.isCategoryOInt hR hv' ν.2)
  obtain ⟨Θ⟩ := TensorModule.nonempty_crystalEquiv_integrable hϖ hϖv hB₁ hB₂ hk hinj
  obtain ⟨s, Λ, Φ, -, -, hΨ⟩ :=
    exists_crystalEquiv_sigma_of_isCategoryOInt (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hO
      (TensorModule.isCrystalBase_tensor_integrable hϖ hϖv hB₁ hB₂ hk hinj)
  exact ⟨s, Λ, Φ.trans Θ.symm, hΨ⟩

/-- **[Kas] Prop. 4.2 (decomposition of a tensor product).** For dominant `μ`, `ν`,
`L_q(μ) ⊗ L_q(ν) ≅ ⊕_b L_q(ν + wt b)` as `U`-modules, the sum running over the elements `b` of
the crystal `B(μ)` of `L_q(μ)` with `εᵢ(b) ≤ ⟨i, ν⟩` for every `i`. Kashiwara writes
`V(λ) ⊗ V(μ) ≅ ⊕ V(λ + wt b)` over `b ∈ B(μ)` with `εᵢ(b) ≤ ⟨hᵢ, λ⟩`; the tensor factors are
exchanged here because the library's coproduct is Lusztig's. Kashiwara works over `ℚ(q)`; here `v`
is transcendental over `ℚ` and the crystal bases are taken over a discrete valuation ring `A`
with `k = A[ϖ⁻¹]` and `ϖ ↦ v⁻¹` (the hypotheses of the grand loop). -/
theorem nonempty_tensor_equiv_dfinsupp (μ ν : Dom R) :
    Nonempty ((Π₀ b : {b // ∀ i, (crystalHW hvt hR hinj hϖ hϖv hk hfund μ).ε i b ≤
          ((ν.1 (R.coroot i) : ℤ) : WithBot ℤ)},
        IrreducibleModule R v (ν.1 + (crystalHW hvt hR hinj hϖ hϖv hk hfund μ).wt b)) ≃ₗ[QuantumGroup R v]
      TensorModule k (IrreducibleModule R v μ.1) (IrreducibleModule R v ν.1)) := by
  obtain ⟨s, Λ, Ξ, ⟨Ψ⟩⟩ := exists_crystalEquiv_sigma_tensor hinj hϖ hϖv hk hfund μ ν
  obtain ⟨e, he⟩ := Crystal.exists_equiv_isHighestWeight_tensor
    (fun j ↦ topHW hvt hR hinj hϖ (Λ j)) (topHW hvt hR hinj hϖ ν)
    (wt_topHW hinj hϖ hϖv hk hfund ν) (fun i ↦ rfl)
    (isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund μ)
    (isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund ν)
    (fun j ↦ isHighestWeight_crystalHW_iff hinj hϖ hϖv hk hfund (Λ j))
    (isHighestWeight_crystalHW_iff hinj hϖ hϖv hk hfund ν) Ξ
  have hwt : ∀ b, ν.1 + (crystalHW hvt hR hinj hϖ hϖv hk hfund μ).wt b.1 = (Λ (e.symm b)).1 :=
    fun b ↦ by
      refine Eq.symm ((wt_topHW hinj hϖ hϖv hk hfund (Λ (e.symm b))).symm.trans
        ((he (e.symm b)).trans ?_))
      exact congrArg (fun x ↦ ν.1 + (crystalHW hvt hR hinj hϖ hϖv hk hfund μ).wt x.1)
        (e.apply_symm_apply b)
  exact ⟨(DFinsupp.mapRange.linearEquiv fun b ↦ IrreducibleModule.equivOfEq (hwt b)).trans
    ((DFinsupp.domLCongr e).symm.trans Ψ)⟩

end GrandLoop

end LieLean.QuantumGroup
