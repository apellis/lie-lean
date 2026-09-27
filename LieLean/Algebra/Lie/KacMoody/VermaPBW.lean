/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaWeights
import LieLean.Algebra.Lie.UniversalEnveloping.TensorDecomposition

/-!
# Verma modules are free of rank one over `U(𝔫₋)`

Let `M(Λ)` be the Verma module over the Kac–Moody algebra `𝔤 = 𝔤(A)`. As a consequence of the
Poincaré–Birkhoff–Witt theorem, the map `U(𝔫₋) → M(Λ)`, `u ↦ u • v_Λ`, is a linear isomorphism
([Kac] §9.2 (check)). In particular `v_Λ ≠ 0` and `dim M(Λ)_Λ = 1`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.borelChar`: the character `𝔟 → K`, `h + n ↦ Λ(h)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.equivEnvNNeg`: the linear isomorphism
  `U(𝔫₋) ≃ M(Λ)`, `u ↦ u • v_Λ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.equivEnvNNeg_mul`: the isomorphism
  `U(𝔫₋) ≃ M(Λ)` is `U(𝔫₋)`-linear; thus `M(Λ)` is a free `U(𝔫₋)`-module of rank one, with basis
  `v_Λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.hwv_ne_zero`: `v_Λ ≠ 0`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_weightSpace_self`: `dim M(Λ)_Λ = 1`.

## Proof

By PBW (`UniversalEnvelopingAlgebra.tensorEquivOfIsCompl`), multiplication
`U(𝔫₋) ⊗ U(𝔟) → U(𝔤)` is a linear isomorphism, since `𝔤 = 𝔫₋ ⊕ 𝔟`. Let
`χ : U(𝔟) → K` be the algebra morphism extending the character `borelChar Λ` of `𝔟`. For
`b ∈ U(𝔟)` we have `b - χ(b) ∈ J(Λ)`, which gives surjectivity. The map
`ψ = (id ⊗ χ) ∘ (mult)⁻¹ : U(𝔤) → U(𝔫₋)` vanishes on `J(Λ)` and is a left inverse of
`U(𝔫₋) → U(𝔤)`, which gives injectivity. The argument is the standard one ([Kac] §9.2 (check)),
written out here in detail.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.2.
-/

open Module LieModule TensorProduct

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (Λ : Dual K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))
local notation "mapB" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (borel P))

/-- The character `𝔟 → K`, `h + n ↦ Λ(h)` (`h ∈ 𝔥`, `n ∈ 𝔫₊`), of the Borel subalgebra. -/
def borelChar : borel P →ₗ⁅K⁆ K where
  toLinearMap := Λ ∘ₗ cartanProj P ∘ₗ (borel P).incl.toLinearMap
  map_lie' {x y} := by
    change Λ (cartanProj P ((⁅x, y⁆ : borel P) : P.KacMoodyAlgebra)) = _
    rw [LieSubalgebra.coe_bracket,
      cartanProj_of_mem_nPos P (lie_mem_nPos_of_mem_borel P x.2 y.2), map_zero,
      LieRing.of_associative_ring_bracket, mul_comm, sub_self]

lemma borelChar_apply (x : borel P) : borelChar P Λ x = Λ (cartanProj P x) := rfl

namespace VermaModule

open UniversalEnvelopingAlgebra hiding ι

/-- The algebra morphism `χ : U(𝔟) → K` extending `borelChar Λ`. -/
abbrev envBorelChar : UniversalEnvelopingAlgebra K (borel P) →ₐ[K] K :=
  UniversalEnvelopingAlgebra.lift K (borelChar P Λ)

/-- `x - Λ(h) ∈ J(Λ)` for `x = h + n ∈ 𝔟`. -/
lemma ι_sub_mem_vermaIdeal {x : P.KacMoodyAlgebra} (hx : x ∈ borel P) :
    ιᵤ x - algebraMap K 𝓤 (Λ (cartanProj P x)) ∈ vermaIdeal P Λ := by
  obtain ⟨a, n, hn, rfl⟩ := (mem_borel P).mp hx
  rw [(cartanProj P).map_add, cartanProj_h, cartanProj_of_mem_nPos P hn, add_zero, map_add,
    add_sub_right_comm]
  exact add_mem (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
    (Submodule.subset_span (Or.inl ⟨n, hn, rfl⟩))

/-- `b - χ(b) ∈ J(Λ)` for `b ∈ U(𝔟)`. -/
lemma map_sub_mem_vermaIdeal (b : UniversalEnvelopingAlgebra K (borel P)) :
    mapB b - algebraMap K 𝓤 (envBorelChar P Λ b) ∈ vermaIdeal P Λ := by
  induction b using UniversalEnvelopingAlgebra.induction with
  | algebraMap r => simp
  | ι x =>
    rw [map_ι, lift_ι_apply]
    exact ι_sub_mem_vermaIdeal P Λ x.2
  | mul a b ha hb =>
    have : mapB (a * b) - algebraMap K 𝓤 (envBorelChar P Λ (a * b)) =
        mapB a • (mapB b - algebraMap K 𝓤 (envBorelChar P Λ b)) +
          envBorelChar P Λ b • (mapB a - algebraMap K 𝓤 (envBorelChar P Λ a)) := by
      simp only [map_mul]
      rw [smul_eq_mul, Algebra.smul_def, mul_sub, mul_sub,
        Algebra.commutes (envBorelChar P Λ b) (mapB a),
        Algebra.commutes (envBorelChar P Λ b) (algebraMap K 𝓤 (envBorelChar P Λ a))]
      abel
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_of_tower_mem _ _ ha)
  | add a b ha hb =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact add_mem ha hb

lemma mk_map_borel (b : UniversalEnvelopingAlgebra K (borel P)) :
    mk P Λ (mapB b) = envBorelChar P Λ b • hwv P Λ := by
  rw [← sub_eq_zero, ← algebraMap_smul 𝓤, ← mk_eq_smul, ← map_sub, mk_eq_zero_iff]
  exact map_sub_mem_vermaIdeal P Λ b

/-- The multiplication isomorphism `U(𝔫₋) ⊗ U(𝔟) ≃ U(𝔤)` (PBW). -/
abbrev mulEquiv :
    UniversalEnvelopingAlgebra K (nNeg P) ⊗[K] UniversalEnvelopingAlgebra K (borel P) ≃ₗ[K] 𝓤 :=
  tensorEquivOfIsCompl (isCompl_nNeg_borel P)

/-- The map `ψ = (id ⊗ χ) ∘ (mult)⁻¹ : U(𝔤) → U(𝔫₋)`. -/
def proj : 𝓤 →ₗ[K] UniversalEnvelopingAlgebra K (nNeg P) :=
  (TensorProduct.rid K _).toLinearMap ∘ₗ
    (LinearMap.lTensor _ (envBorelChar P Λ).toLinearMap) ∘ₗ (mulEquiv P).symm.toLinearMap

lemma proj_mul (n : UniversalEnvelopingAlgebra K (nNeg P))
    (b : UniversalEnvelopingAlgebra K (borel P)) :
    proj P Λ (mapN n * mapB b) = envBorelChar P Λ b • n := by
  have : (mulEquiv P).symm (mapN n * mapB b) = n ⊗ₜ b := by
    rw [LinearEquiv.symm_apply_eq, tensorEquivOfIsCompl_apply_tmul]
  simp only [proj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, this,
    LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.rid_tmul]

lemma proj_map (n : UniversalEnvelopingAlgebra K (nNeg P)) : proj P Λ (mapN n) = n := by
  have := proj_mul P Λ n 1
  rwa [map_one, mul_one, map_one, one_smul] at this

lemma proj_mul_map_eq_zero {b : UniversalEnvelopingAlgebra K (borel P)}
    (hb : envBorelChar P Λ b = 0) (u : 𝓤) : proj P Λ (u * mapB b) = 0 := by
  obtain ⟨t, rfl⟩ := (mulEquiv P).surjective u
  induction t using TensorProduct.inductionOn with
  | tmul n b' =>
    rw [tensorEquivOfIsCompl_apply_tmul, mul_assoc, ← map_mul, proj_mul, map_mul, hb, mul_zero,
      zero_smul]
  | add t t' ht ht' => rw [map_add, add_mul, map_add, ht, ht', add_zero]

/-- The left ideal `{x | ∀ u, ψ(u x) = 0}`. -/
def projKer : Submodule 𝓤 𝓤 where
  carrier := {x | ∀ u, proj P Λ (u * x) = 0}
  add_mem' hx hy u := by rw [mul_add, map_add, hx, hy, add_zero]
  zero_mem' u := by rw [mul_zero, map_zero]
  smul_mem' c x hx u := by rw [smul_eq_mul, ← mul_assoc]; exact hx _

lemma vermaIdeal_le_projKer : vermaIdeal P Λ ≤ projKer P Λ := by
  rw [vermaIdeal, Submodule.span_le]
  rintro _ (⟨x, hx, rfl⟩ | ⟨a, rfl⟩)
  · intro u
    have := proj_mul_map_eq_zero P Λ (b := ιᵤ ⟨x, nPos_le_borel P hx⟩) (by
      rw [lift_ι_apply, borelChar_apply]
      simp [cartanProj_of_mem_nPos P hx]) u
    rwa [map_ι] at this
  · intro u
    have := proj_mul_map_eq_zero P Λ
      (b := ιᵤ ⟨h P a, h_mem_borel P a⟩ - algebraMap K _ (Λ a)) (by
        rw [map_sub, lift_ι_apply, borelChar_apply, AlgHom.commutes]
        simp) u
    rwa [map_sub, map_ι, AlgHom.commutes] at this

lemma proj_eq_zero_of_mem {x : 𝓤} (hx : x ∈ vermaIdeal P Λ) : proj P Λ x = 0 := by
  simpa using vermaIdeal_le_projKer P Λ hx 1

/-- The linear map `U(𝔫₋) → M(Λ)`, `u ↦ u • v_Λ`. -/
def envNNegToVerma : UniversalEnvelopingAlgebra K (nNeg P) →ₗ[K] VermaModule P Λ :=
  (mk P Λ).restrictScalars K ∘ₗ (mapN).toLinearMap

omit [CharZero K] in
lemma envNNegToVerma_apply (u : UniversalEnvelopingAlgebra K (nNeg P)) :
    envNNegToVerma P Λ u = mapN u • hwv P Λ :=
  mk_eq_smul P Λ _

lemma envNNegToVerma_injective : Function.Injective (envNNegToVerma P Λ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  rw [envNNegToVerma_apply, ← mk_eq_smul] at hu
  have := proj_eq_zero_of_mem P Λ ((mk_eq_zero_iff P Λ).mp hu)
  rwa [proj_map] at this

lemma envNNegToVerma_surjective : Function.Surjective (envNNegToVerma P Λ) := by
  intro m
  obtain ⟨x, rfl⟩ := mk_surjective P Λ m
  obtain ⟨t, rfl⟩ := (mulEquiv P).surjective x
  induction t using TensorProduct.inductionOn with
  | tmul n b =>
    refine ⟨envBorelChar P Λ b • n, ?_⟩
    rw [LinearMap.map_smul, envNNegToVerma_apply, tensorEquivOfIsCompl_apply_tmul, mk_eq_smul,
      mul_smul, ← mk_eq_smul P Λ (mapB b), mk_map_borel, smul_comm]
  | add t t' ht ht' =>
    obtain ⟨u, hu⟩ := ht
    obtain ⟨u', hu'⟩ := ht'
    exact ⟨u + u', by rw [map_add, hu, hu', map_add, map_add]⟩

/-- **PBW for Verma modules** ([Kac] §9.2 (check)): the map `U(𝔫₋) → M(Λ)`, `u ↦ u • v_Λ`, is
a linear isomorphism. -/
def equivEnvNNeg : UniversalEnvelopingAlgebra K (nNeg P) ≃ₗ[K] VermaModule P Λ :=
  LinearEquiv.ofBijective (envNNegToVerma P Λ)
    ⟨envNNegToVerma_injective P Λ, envNNegToVerma_surjective P Λ⟩

@[simp] lemma equivEnvNNeg_apply (u : UniversalEnvelopingAlgebra K (nNeg P)) :
    equivEnvNNeg P Λ u = mapN u • hwv P Λ :=
  envNNegToVerma_apply P Λ u

/-- The isomorphism `U(𝔫₋) ≃ M(Λ)` is `U(𝔫₋)`-linear, so `M(Λ)` is a free `U(𝔫₋)`-module of
rank one with basis `v_Λ` ([Kac] §9.2 (check)). -/
theorem equivEnvNNeg_mul (u u' : UniversalEnvelopingAlgebra K (nNeg P)) :
    equivEnvNNeg P Λ (u * u') = mapN u • equivEnvNNeg P Λ u' := by
  simp [mul_smul]

instance : Nontrivial (UniversalEnvelopingAlgebra K (nNeg P)) :=
  (UniversalEnvelopingAlgebra.lift K (0 : nNeg P →ₗ⁅K⁆ K)).toRingHom.domain_nontrivial

/-- The highest-weight vector of `M(Λ)` is nonzero ([Kac] §9.2 (check)). -/
theorem hwv_ne_zero : hwv P Λ ≠ 0 := by
  have : equivEnvNNeg P Λ 1 = hwv P Λ := by simp
  rw [← this, ne_eq, LinearEquiv.map_eq_zero_iff]
  exact one_ne_zero

instance : Nontrivial (VermaModule P Λ) := ⟨⟨_, _, hwv_ne_zero P Λ⟩⟩

/-- `dim M(Λ)_Λ = 1` ([Kac] §9.2 (check)). -/
theorem finrank_weightSpace_self : finrank K (weightSpace P Λ Λ) = 1 := by
  rw [weightSpace_self, finrank_span_singleton (hwv_ne_zero P Λ)]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra

end
