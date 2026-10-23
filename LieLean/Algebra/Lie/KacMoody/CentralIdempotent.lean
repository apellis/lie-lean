/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CentralDecomposition

/-!
# Central elements acting as block projections

On a finitely generated module whose centre acts locally finitely (e.g. a finitely generated
module in category `𝒪`), the projection onto a generalized central character block is the
action of a single element of the centre `Z(U(𝔤))` (`exists_rep_eq_centralBlockProjection`).
The generators have components in finitely many blocks, and on each of these blocks every
central element has a uniform nilpotence exponent, so a polynomial in finitely many central
elements separates the blocks.

This is the form of the block projections used in Humphreys' §10.8: translation functors
restricted to a finitely generated module are then cut out of `M ↦ M ⊗ L` by the action of a
central element on `M ⊗ L`, which is natural in `M`.

## Main results

* `AlgHom.exists_rep_eq_id_and_eq_zero`: separation of finitely many generalized characters
  of a commutative algebra acting with uniform nilpotence exponents.
* `Matrix.Realization.KacMoodyAlgebra.exists_rep_eq_centralBlockProjection`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §1.12, §10.8 (the central idempotents are implicit there; the argument
  is reconstructed).
-/

open Module LieModule
noncomputable section

namespace AlgHom

variable {K R V : Type*} [Field K] [CommRing R] [Algebra K R] [AddCommGroup V] [Module K V]

/-- **Separating generalized characters.** Let a commutative algebra `R` act on `V` by `ρ`, and
let `B ψ` be subspaces on which every `ρ a - ψ a` is nilpotent with a uniform exponent. For a
finite set `T` of characters and a character `χ`, some `c ∈ R` acts as the identity on `B χ`
and as zero on every `B ψ`, `ψ ∈ T`, `ψ ≠ χ`. -/
theorem exists_rep_eq_id_and_eq_zero (ρ : R →ₐ[K] Module.End K V)
    (B : (R →ₐ[K] K) → Submodule K V)
    (hB : ∀ ψ a, ∃ n : ℕ, ∀ v ∈ B ψ, ((ρ a - ψ a • 1) ^ n) v = 0)
    (T : Finset (R →ₐ[K] K)) (χ : R →ₐ[K] K) :
    ∃ c : R, (∀ v ∈ B χ, ρ c v = v) ∧ ∀ ψ ∈ T, ψ ≠ χ → ∀ v ∈ B ψ, ρ c v = 0 := by
  classical
  have hρ : ∀ (a : R) (x : K), ρ (a - algebraMap K R x) = ρ a - x • 1 := by
    intro a x
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  -- An element with nonzero `χ`-value killing the other blocks.
  have step : ∃ b : R, χ b ≠ 0 ∧ ∀ ψ ∈ T, ψ ≠ χ → ∀ v ∈ B ψ, ρ b v = 0 := by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp⟩
    | insert ψ T _ ih =>
      obtain ⟨b, hb, hbT⟩ := ih
      by_cases hψ : ψ = χ
      · refine ⟨b, hb, fun ψ' hψ' hne v hv ↦ ?_⟩
        rcases Finset.mem_insert.mp hψ' with rfl | hψ'
        · exact absurd hψ hne
        · exact hbT ψ' hψ' hne v hv
      obtain ⟨a, ha⟩ : ∃ a, χ a ≠ ψ a := by
        by_contra! h
        exact hψ (AlgHom.ext h).symm
      obtain ⟨n, hn⟩ := hB ψ a
      refine ⟨b * (a - algebraMap K R (ψ a)) ^ n, ?_, fun ψ' hψ' hne v hv ↦ ?_⟩
      · rw [map_mul, map_pow, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply]
        exact mul_ne_zero hb (pow_ne_zero _ (sub_ne_zero.mpr ha))
      rcases Finset.mem_insert.mp hψ' with rfl | hψ'
      · rw [map_mul, map_pow, hρ, Module.End.mul_apply, hn v hv, map_zero]
      · rw [mul_comm, map_mul, Module.End.mul_apply, hbT ψ' hψ' hne v hv, map_zero]
  obtain ⟨b, hb, hbT⟩ := step
  set y : R := (χ b)⁻¹ • b with hy
  have hχy : χ y = 1 := by rw [hy, map_smul, smul_eq_mul, inv_mul_cancel₀ hb]
  obtain ⟨m, hm⟩ := hB χ y
  refine ⟨1 - (1 - y) ^ m, fun v hv ↦ ?_, fun ψ hψ hne v hv ↦ ?_⟩
  · have h1 : ρ (1 - y) = -(ρ y - χ y • 1) := by
      rw [hχy, one_smul, map_sub, map_one, neg_sub]
    rw [map_sub, map_one, map_pow, h1, neg_pow, LinearMap.sub_apply, Module.End.one_apply,
      Module.End.mul_apply, hm v hv, map_zero, sub_zero]
  · have hyv : ρ y v = 0 := by rw [hy, map_smul, LinearMap.smul_apply, hbT ψ hψ hne v hv,
      smul_zero]
    have hk : ∀ k : ℕ, ((1 - ρ y) ^ k) v = v := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hyv,
          sub_zero, ih]
    rw [map_sub, map_one, map_pow, map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply,
      hk, sub_self]

end AlgHom

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- The action of a central element, shifted by a scalar and raised to a power, as a morphism
of `𝔤`-modules. -/
def centralShiftPow (z : 𝓩) (c : K) (n : ℕ) : V →ₗ⁅K,P.KacMoodyAlgebra⁆ V where
  toLinearMap := (rep P V (z : 𝓤) - c • 1) ^ n
  map_lie' {x v} := by
    have hc : Commute (rep P V (z : 𝓤) - c • 1) (rep P V (UniversalEnvelopingAlgebra.ι K x)) :=
      (rep_center_commute P z _).sub_left (Commute.smul_left (Commute.one_left _) c)
    have := congrArg (· v) (hc.pow_left n).eq
    simp only [Module.End.mul_apply, rep_ι] at this
    exact this

@[simp] theorem centralShiftPow_apply (z : 𝓩) (c : K) (n : ℕ) (v : V) :
    centralShiftPow P z c n v = ((rep P V (z : 𝓤) - c • 1) ^ n) v := rfl

variable [IsAlgClosed K]

/-- On a finitely generated module with locally finite central action, every block is killed
by a fixed power of `z - χ(z)`, for each central `z`. -/
theorem exists_pow_eq_zero_of_mem_centralBlock (hV : IsCentralLocallyFinite P V) {s : Finset V}
    (hs : LieSubmodule.lieSpan K P.KacMoodyAlgebra (s : Set V) = ⊤) (χ : 𝓩 →ₐ[K] K) (z : 𝓩) :
    ∃ n : ℕ, ∀ v ∈ centralBlock P V χ, ((rep P V (z : 𝓤) - χ z • 1) ^ n) v = 0 := by
  classical
  have ht : ∀ t ∈ s, ∃ n : ℕ,
      ((rep P V (z : 𝓤) - χ z • 1) ^ n) (centralBlockProjection P hV χ t) = 0 := fun t _ ↦
    (mem_centralBlock P χ _).mp (centralBlockProjection_mem P hV χ t) z
  choose! n hn using ht
  refine ⟨s.sup n, fun v hv ↦ ?_⟩
  have hker : LieSubmodule.lieSpan K P.KacMoodyAlgebra (s : Set V) ≤
      ((centralShiftPow P z (χ z) (s.sup n)).comp (centralBlockProjection P hV χ)).ker := by
    rw [LieSubmodule.lieSpan_le]
    intro t ht
    rw [SetLike.mem_coe, LieModuleHom.mem_ker, LieModuleHom.comp_apply, centralShiftPow_apply,
      ← Nat.sub_add_cancel (Finset.le_sup ht), pow_add, Module.End.mul_apply, hn t ht,
      map_zero]
  rw [hs] at hker
  have := hker (LieSubmodule.mem_top v)
  rwa [LieModuleHom.mem_ker, LieModuleHom.comp_apply, centralBlockProjection_self P hV χ hv,
    centralShiftPow_apply] at this

/-- **Block projections are central.** On a finitely generated module with locally finite
central action (e.g. a finitely generated module in `𝒪`), the projection onto the block of a
central character `χ` is the action of an element of `Z(U(𝔤))`. -/
theorem exists_rep_eq_centralBlockProjection (hV : IsCentralLocallyFinite P V) {s : Finset V}
    (hs : LieSubmodule.lieSpan K P.KacMoodyAlgebra (s : Set V) = ⊤) (χ : 𝓩 →ₐ[K] K) :
    ∃ z : 𝓩, ∀ v, rep P V (z : 𝓤) v = centralBlockProjection P hV χ v := by
  classical
  choose T hT₀ _ using fun t : V ↦ exists_finset_sum_centralBlockProjection P hV t
  let T' := s.biUnion T
  -- Outside `T'`, the projections vanish.
  have hzero : ∀ ψ ∉ T', ∀ v, centralBlockProjection P hV ψ v = 0 := by
    intro ψ hψ v
    have hker : LieSubmodule.lieSpan K P.KacMoodyAlgebra (s : Set V) ≤
        (centralBlockProjection P hV ψ).ker := by
      rw [LieSubmodule.lieSpan_le]
      intro t ht
      exact hT₀ t ψ fun h ↦ hψ (Finset.mem_biUnion.mpr ⟨t, ht, h⟩)
    rw [hs] at hker
    exact hker (LieSubmodule.mem_top v)
  obtain ⟨c, hcχ, hcT⟩ := AlgHom.exists_rep_eq_id_and_eq_zero
    ((rep P V).comp (Subalgebra.center K 𝓤).val)
    (fun ψ ↦ (centralBlock P V ψ).toSubmodule)
    (fun ψ a ↦ exists_pow_eq_zero_of_mem_centralBlock P hV hs ψ a) T' χ
  refine ⟨c, fun v ↦ ?_⟩
  obtain ⟨S, hS₀, hS⟩ := exists_finset_sum_centralBlockProjection P hV v
  conv_lhs => rw [← hS]
  rw [map_sum]
  have hc : ∀ ψ, rep P V (c : 𝓤) (centralBlockProjection P hV ψ v) =
      if ψ = χ then centralBlockProjection P hV χ v else 0 := by
    intro ψ
    split_ifs with h
    · subst h
      exact hcχ _ (centralBlockProjection_mem P hV ψ v)
    · by_cases hψ : ψ ∈ T'
      · exact hcT ψ hψ h _ (centralBlockProjection_mem P hV ψ v)
      · rw [hzero ψ hψ v, map_zero]
  simp only [hc, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (hS₀ χ h).symm

end Matrix.Realization.KacMoodyAlgebra
