/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaUniformity

/-!
# Verma modules are torsion-free

In finite type, `M(λ)` is a free module of rank one over the domain `U(𝔫⁻)`, and `U(𝔫⁻)` satisfies
the left Ore condition. Hence morphisms into Verma modules cannot have "torsion" kernels: a
morphism from a submodule of a Verma module to a Verma module is zero or injective. This is the
argument behind Humphreys, GSM 94, Theorem 4.2 (a) and §4.2; it is used for Theorem 7.16 (b)
(`[M(ξ) : L(λ)] ≤ 1` for antidominant `λ`).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.map_rep`: morphisms of `𝔤`-modules commute
  with the action of `U(𝔤)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.eq_zero_or_ker_le`: if `f : X → M(ξ)`,
  `g : X → M(λ)` and `ker f ≤ ker g`, then `g = 0` or `ker g ≤ ker f`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.eq_zero_or_injective`: a morphism from a
  submodule of a Verma module to a Verma module is zero or injective.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §4.1–§4.2.
-/

open Module

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))

section rep

variable {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

omit [CharZero K] [FiniteDimensional K H] in
/-- A morphism of `𝔤`-modules commutes with the action of `U(𝔤)`. -/
lemma VermaModule.map_rep (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (u : UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) (v : V) :
    f (VermaModule.rep P V u v) = VermaModule.rep P W u (f v) := by
  induction u using UniversalEnvelopingAlgebra.induction generalizing v with
  | algebraMap r => simp
  | ι x => rw [VermaModule.rep_ι, VermaModule.rep_ι, LieModuleHom.map_lie]
  | mul a b ha hb => rw [map_mul, Module.End.mul_apply, ha, hb, map_mul, Module.End.mul_apply]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, map_add, ha, hb, map_add,
      LinearMap.add_apply]

end rep

omit [CharZero K] [FiniteDimensional K H] in
/-- On a Verma module, the action of `U(𝔤)` through `rep` is the module action. -/
lemma VermaModule.rep_eq_smul (Λ : Dual K H) (u : UniversalEnvelopingAlgebra K 𝔤)
    (m : VermaModule P Λ) : VermaModule.rep P (VermaModule P Λ) u m = u • m :=
  (VermaModule.map_smul_eq_rep P Λ LieModuleHom.id u m).symm

variable (hA : A.IsFiniteCartan)
include hA

/-- **Verma modules are torsion-free** (finite type). Let `f : X → M(ξ)` and `g : X → M(λ)` be
morphisms with `ker f ≤ ker g`. Then `g = 0` or `ker g ≤ ker f`. Proof: if `g q ≠ 0` and
`g p = 0 ≠ f p`, the Ore condition for `U(𝔫⁻)` gives `u (f q) = v (f p) ≠ 0`; then
`u q - v p ∈ ker f ≤ ker g`, so `u (g q) = v (g p) = 0`, although `M(λ)` is a free
`U(𝔫⁻)`-module and `U(𝔫⁻)` is a domain. -/
theorem VermaModule.eq_zero_or_ker_le {X : Type*} [AddCommGroup X] [Module K X]
    [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X] {ξ lam : Dual K H}
    (f : X →ₗ⁅K,𝔤⁆ VermaModule P ξ) (g : X →ₗ⁅K,𝔤⁆ VermaModule P lam) (hfg : f.ker ≤ g.ker) :
    g = 0 ∨ g.ker ≤ f.ker := by
  have := finiteDimensional P hA
  by_contra! h
  obtain ⟨h0, hle⟩ := h
  obtain ⟨q, hq⟩ : ∃ q, g q ≠ 0 := by
    by_contra! hq
    exact h0 (LieModuleHom.ext hq)
  obtain ⟨p, hp, hfp⟩ : ∃ p, g p = 0 ∧ f p ≠ 0 := by
    rw [SetLike.not_le_iff_exists] at hle
    obtain ⟨p, hpg, hpf⟩ := hle
    exact ⟨p, hpg, hpf⟩
  have hfq : f q ≠ 0 := fun h ↦ hq (hfg h)
  obtain ⟨a, ha⟩ := (equivEnvNNeg P ξ).surjective (f q)
  obtain ⟨b, hb⟩ := (equivEnvNNeg P ξ).surjective (f p)
  obtain ⟨c, hc⟩ := (equivEnvNNeg P lam).surjective (g q)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hfq (by rw [← ha, map_zero])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hfp (by rw [← hb, map_zero])
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hq (by rw [← hc, map_zero])
  obtain ⟨u, v, huv, hu⟩ := UniversalEnvelopingAlgebra.exists_common_left_multiple a b ha0 hb0
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (zero_mul a)
  have hmem : VermaModule.rep P X (mapN u) q - VermaModule.rep P X (mapN v) p ∈ f.ker := by
    rw [LieModuleHom.mem_ker, map_sub, VermaModule.map_rep, VermaModule.map_rep,
      VermaModule.rep_eq_smul, VermaModule.rep_eq_smul, ← ha, ← hb, ← equivEnvNNeg_mul,
      ← equivEnvNNeg_mul, huv, sub_self]
  have key := hfg hmem
  rw [LieModuleHom.mem_ker, map_sub, VermaModule.map_rep, VermaModule.map_rep, hp, map_zero,
    sub_zero, ← hc, VermaModule.rep_eq_smul, ← equivEnvNNeg_mul] at key
  exact mul_ne_zero hu0 hc0 ((LinearEquiv.map_eq_zero_iff _).mp key)

/-- A morphism from a submodule of a Verma module to a Verma module is zero or injective. -/
theorem VermaModule.eq_zero_or_injective {ξ lam : Dual K H}
    (N : LieSubmodule K 𝔤 (VermaModule P ξ)) (φ : N →ₗ⁅K,𝔤⁆ VermaModule P lam) :
    φ = 0 ∨ Function.Injective φ := by
  have hker : N.incl.ker ≤ φ.ker := by
    rw [LieSubmodule.ker_incl]
    exact bot_le
  refine (VermaModule.eq_zero_or_ker_le P hA N.incl φ hker).imp_right fun h ↦ ?_
  rw [← LieModuleHom.ker_eq_bot, eq_bot_iff, ← LieSubmodule.ker_incl]
  exact h

end Matrix.Realization.KacMoodyAlgebra
