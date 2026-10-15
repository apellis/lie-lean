/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CategoryOInt

/-!
# `L_q(Λ)` and tensor products in `𝒪_int`

* `QuantumGroup.IrreducibleModule.isCategoryOInt`: for dominant `Λ`, `L_q(Λ)` lies in `𝒪_int`.
* `QuantumGroup.TensorModule.weightSpace_le_iSup_weightPiece`: the weight space `(M₁ ⊗ M₂)^Λ` of a
  tensor product of weight modules is spanned by the `M₁^{Λ₁} ⊗ M₂^{Λ₂}` with `Λ₁ + Λ₂ = Λ`.
* `QuantumGroup.TensorModule.isCategoryOInt`: `𝒪_int` is closed under tensor products (for an
  `X`-regular root datum).

These are the facts used implicitly in [HK] §3.2 and [Kas] §4.5 when the tensor product of two
modules `V(λ) ⊗ V(μ)` is decomposed in `𝒪_int`; the proofs are our own.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §3.2.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §4.5.
-/

open TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

/-- For dominant `Λ`, the simple module `L_q(Λ)` lies in `𝒪_int`: it is integrable, its weight
spaces are images of those of `M_q(Λ)`, which are finite-dimensional, and its weights lie in
`Λ - Q₊`. -/
theorem IrreducibleModule.isCategoryOInt (hR : R.IsXRegular)
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ : Y →+ ℤ} (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    IsCategoryOInt R v (IrreducibleModule R v Λ) := by
  have hle := weightSpace_quotient_le_map hv' (VermaModule.iSup_weightSpace_eq_top (Λ := Λ))
    (VermaModule.maxSubmodule R v Λ)
  have hbot : ∀ Λ', (∀ ν, Λ' ≠ Λ - R.rootSum ν) →
      weightSpace R v (IrreducibleModule R v Λ) Λ' = ⊥ := fun Λ' h ↦ by
    have := hle Λ'
    rwa [VermaModule.weightSpace_eq_bot hv' h, Submodule.map_bot, le_bot_iff] at this
  refine ⟨IrreducibleModule.isIntegrable hR hv' hΛ, fun Λ' ↦ ?_, ⟨{Λ}, fun Λ' h ↦ ?_⟩⟩
  · by_cases hν : ∃ ν, Λ' = Λ - R.rootSum ν
    · obtain ⟨ν, rfl⟩ := hν
      have := VermaModule.finiteDimensional_weightSpace (Λ := Λ) hv' hR ν
      exact Submodule.finiteDimensional_of_le (hle _)
    · rw [hbot Λ' fun ν h ↦ hν ⟨ν, h⟩]
      infer_instance
  · by_contra! hν
    exact h (hbot Λ' fun ν ↦ hν Λ (Finset.mem_singleton_self Λ) ν)

namespace TensorModule

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]

variable (R v M₁ M₂) in
/-- The image `M₁^{Λ₁} ⊗ M₂^{Λ₂}` of the tensor product of two weight spaces in `M₁ ⊗ M₂`. -/
def weightPiece (Λ₁ Λ₂ : Y →+ ℤ) : Submodule k (TensorModule k M₁ M₂) :=
  LinearMap.range ((mk M₁ M₂).toLinearMap ∘ₗ
    TensorProduct.map (weightSpace R v M₁ Λ₁).subtype (weightSpace R v M₂ Λ₂).subtype)

omit [NeZero v] in
lemma tmul_mem_weightPiece {Λ₁ Λ₂ : Y →+ ℤ} {x : M₁} {y : M₂}
    (hx : x ∈ weightSpace R v M₁ Λ₁) (hy : y ∈ weightSpace R v M₂ Λ₂) :
    mk M₁ M₂ (x ⊗ₜ[k] y) ∈ weightPiece R v M₁ M₂ Λ₁ Λ₂ :=
  ⟨⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩, rfl⟩

lemma weightPiece_le (Λ₁ Λ₂ : Y →+ ℤ) :
    weightPiece R v M₁ M₂ Λ₁ Λ₂ ≤ weightSpace R v (TensorModule k M₁ M₂) (Λ₁ + Λ₂) := by
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact tmul_mem_weightSpace x.2 y.2
  | add t t' h h' => rw [map_add]; exact Submodule.add_mem _ h h'

omit [NeZero v] in
lemma weightPiece_eq_bot_of_left {Λ₁ Λ₂ : Y →+ ℤ} (h : weightSpace R v M₁ Λ₁ = ⊥) :
    weightPiece R v M₁ M₂ Λ₁ Λ₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have hx : (x : M₁) = 0 := (Submodule.mem_bot k).1 (h ▸ x.2)
    simp [hx]
  | add t t' h h' => rw [map_add]; exact Submodule.add_mem _ h h'

omit [NeZero v] in
lemma weightPiece_eq_bot_of_right {Λ₁ Λ₂ : Y →+ ℤ} (h : weightSpace R v M₂ Λ₂ = ⊥) :
    weightPiece R v M₁ M₂ Λ₁ Λ₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have hy : (y : M₂) = 0 := (Submodule.mem_bot k).1 (h ▸ y.2)
    simp [hy]
  | add t t' h h' => rw [map_add]; exact Submodule.add_mem _ h h'

/-- The weight space `(M₁ ⊗ M₂)^Λ` of a tensor product of weight modules is the sum of the
`M₁^{Λ₁} ⊗ M₂^{Λ₂}` with `Λ₁ + Λ₂ = Λ` (`v` not a root of unity). -/
theorem weightSpace_le_iSup_weightPiece (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (h₁ : ⨆ Λ, weightSpace R v M₁ Λ = ⊤) (h₂ : ⨆ Λ, weightSpace R v M₂ Λ = ⊤) (Λ : Y →+ ℤ) :
    weightSpace R v (TensorModule k M₁ M₂) Λ ≤
      ⨆ (p : (Y →+ ℤ) × (Y →+ ℤ)) (_ : p.1 + p.2 = Λ), weightPiece R v M₁ M₂ p.1 p.2 := by
  set P := ⨆ (p : (Y →+ ℤ) × (Y →+ ℤ)) (_ : p.1 + p.2 = Λ), weightPiece R v M₁ M₂ p.1 p.2
  set Q := ⨆ (μ : Y →+ ℤ) (_ : μ ≠ Λ), weightSpace R v (TensorModule k M₁ M₂) μ
  have hP : P ≤ weightSpace R v (TensorModule k M₁ M₂) Λ :=
    iSup₂_le fun p hp ↦ by rw [← hp]; exact weightPiece_le p.1 p.2
  intro z hz
  have htop : ⊤ ≤ P ⊔ Q := by
    rw [← span_tmul_weight h₁ h₂, Submodule.span_le]
    rintro _ ⟨Λ₁, Λ₂, x, y, hx, hy, rfl⟩
    by_cases h : Λ₁ + Λ₂ = Λ
    · exact Submodule.mem_sup_left
        (Submodule.mem_iSup_of_mem (Λ₁, Λ₂) (Submodule.mem_iSup_of_mem h
          (tmul_mem_weightPiece hx hy)))
    · exact Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem (Λ₁ + Λ₂) (Submodule.mem_iSup_of_mem h
          (tmul_mem_weightSpace hx hy)))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := z)))
  have hb' : b ∈ weightSpace R v (TensorModule k M₁ M₂) Λ := by
    have := Submodule.sub_mem _ hz (hP ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := (Submodule.disjoint_def.1 (iSupIndep_weightSpace hv' Λ)) b hb' hb
  rw [hb0, add_zero]
  exact ha

/-- **`𝒪_int` is closed under tensor products** (for an `X`-regular root datum and `v` not a root
of unity): `M₁ ⊗ M₂` is integrable ([Lus] 3.5.2 (a)), its weight space of weight `Λ` is the sum
of the finitely many nonzero `M₁^{Λ₁} ⊗ M₂^{Λ₂}`, `Λ₁ + Λ₂ = Λ`, and its weights lie in the cones
below the sums of the given maximal weights. -/
theorem isCategoryOInt (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (h₁ : IsCategoryOInt R v M₁) (h₂ : IsCategoryOInt R v M₂) :
    IsCategoryOInt R v (TensorModule k M₁ M₂) := by
  classical
  have hinj : Function.Injective R.rootSum := fun ν ν' h ↦ by
    by_contra hne
    obtain ⟨μ, hμ⟩ := R.exists_rootSum_ne hR hne
    exact hμ (by rw [h])
  obtain ⟨s₁, hs₁⟩ := h₁.exists_finset
  obtain ⟨s₂, hs₂⟩ := h₂.exists_finset
  have hle := weightSpace_le_iSup_weightPiece (M₁ := M₁) (M₂ := M₂) hv'
    h₁.isIntegrable.iSup_weightSpace_eq_top h₂.isIntegrable.iSup_weightSpace_eq_top
  -- the pairs of weights contributing to a given weight
  let S : (Y →+ ℤ) → Set ((Y →+ ℤ) × (Y →+ ℤ)) := fun Λ ↦
    {p | p.1 + p.2 = Λ ∧ weightSpace R v M₁ p.1 ≠ ⊥ ∧ weightSpace R v M₂ p.2 ≠ ⊥}
  have hle' : ∀ Λ, weightSpace R v (TensorModule k M₁ M₂) Λ ≤
      ⨆ p ∈ S Λ, weightPiece R v M₁ M₂ p.1 p.2 := fun Λ ↦ (hle Λ).trans <|
    iSup₂_le fun p hp ↦ by
      by_cases h1 : weightSpace R v M₁ p.1 = ⊥
      · rw [weightPiece_eq_bot_of_left h1]; exact bot_le
      by_cases h2 : weightSpace R v M₂ p.2 = ⊥
      · rw [weightPiece_eq_bot_of_right h2]; exact bot_le
      exact le_iSup₂_of_le p ⟨hp, h1, h2⟩ le_rfl
  have hfin : ∀ Λ, (S Λ).Finite := fun Λ ↦ by
    let T : Set ((Y →+ ℤ) × (Y →+ ℤ)) :=
      ⋃ μ ∈ ((s₁ ×ˢ s₂ : Finset ((Y →+ ℤ) × (Y →+ ℤ))) : Set ((Y →+ ℤ) × (Y →+ ℤ))),
        ⋃ ν ∈ {ν : I →₀ ℕ | R.rootSum ν = μ.1 + μ.2 - Λ},
          (fun q : (I →₀ ℕ) × (I →₀ ℕ) ↦ (μ.1 - R.rootSum q.1, μ.2 - R.rootSum q.2)) ''
            (Finset.HasAntidiagonal.antidiagonal ν : Set ((I →₀ ℕ) × (I →₀ ℕ)))
    refine Set.Finite.subset ?_ (show S Λ ⊆ T from ?_)
    · refine Set.Finite.biUnion (Finset.finite_toSet _) fun μ _ ↦
        Set.Finite.biUnion ?_ fun ν _ ↦ (Finset.finite_toSet _).image _
      exact Set.Subsingleton.finite fun ν hν ν' hν' ↦ hinj (hν.trans hν'.symm)
    rintro ⟨Λ₁, Λ₂⟩ ⟨hΛ, hn₁, hn₂⟩
    obtain ⟨μ₁, hμ₁, ν₁, rfl⟩ := hs₁ _ hn₁
    obtain ⟨μ₂, hμ₂, ν₂, rfl⟩ := hs₂ _ hn₂
    refine Set.mem_biUnion (x := (μ₁, μ₂)) (Finset.mem_coe.2 (Finset.mem_product.2 ⟨hμ₁, hμ₂⟩)) ?_
    refine Set.mem_biUnion (x := ν₁ + ν₂) ?_
      ⟨(ν₁, ν₂), Finset.mem_coe.2 (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl), rfl⟩
    change R.rootSum (ν₁ + ν₂) = μ₁ + μ₂ - Λ
    rw [R.rootSum_add, ← hΛ]
    ext y
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
    ring
  refine ⟨isIntegrable h₁.isIntegrable h₂.isIntegrable, fun Λ ↦ ?_, ?_⟩
  · have := (hfin Λ).to_subtype
    have : ∀ p : S Λ, FiniteDimensional k (weightPiece R v M₁ M₂ p.1.1 p.1.2) := fun p ↦ by
      have := h₁.finiteDimensional_weightSpace p.1.1
      have := h₂.finiteDimensional_weightSpace p.1.2
      exact LinearMap.finiteDimensional_range _
    have hsup : weightSpace R v (TensorModule k M₁ M₂) Λ ≤
        ⨆ p : S Λ, weightPiece R v M₁ M₂ p.1.1 p.1.2 :=
      (hle' Λ).trans (iSup₂_le fun p hp ↦ le_iSup_of_le (⟨p, hp⟩ : S Λ) le_rfl)
    exact Submodule.finiteDimensional_of_le hsup
  · refine ⟨Finset.image₂ (· + ·) s₁ s₂, fun Λ hΛ ↦ ?_⟩
    obtain ⟨⟨Λ₁, Λ₂⟩, ⟨rfl, hn₁, hn₂⟩⟩ : (S Λ).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      refine hΛ (le_bot_iff.1 ((hle' Λ).trans ?_))
      simp [h]
    obtain ⟨μ₁, hμ₁, ν₁, rfl⟩ := hs₁ _ hn₁
    obtain ⟨μ₂, hμ₂, ν₂, rfl⟩ := hs₂ _ hn₂
    refine ⟨μ₁ + μ₂, Finset.mem_image₂_of_mem hμ₁ hμ₂, ν₁ + ν₂, ?_⟩
    rw [R.rootSum_add]
    ext y
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
    ring

end TensorModule

end LieLean.QuantumGroup
