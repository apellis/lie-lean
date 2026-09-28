/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.FiniteType
import LieLean.Algebra.Lie.KacMoody.VermaHom
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Ore argument for enveloping algebras of finite-dimensional Lie algebras

## Main results

* `UniversalEnvelopingAlgebra.finrank_filtration_le`: a polynomial PBW growth bound.
* `UniversalEnvelopingAlgebra.exists_common_left_multiple`: nonzero principal left
  ideals in the enveloping algebra of a finite-dimensional Lie algebra intersect.
* `UniversalEnvelopingAlgebra.nonempty_oreSet`: the actual Mathlib left Ore condition.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_oreSet_envNNeg`: the finite-type instance.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.inf_ne_bot_of_finite_type`:
  every two nonzero submodules of an arbitrary-weight finite-type Verma module intersect.

These supply the Ore-domain and uniformity steps for classical Verma Hom uniqueness,
not yet the full dimension bound. No integrality or regularity hypothesis is used.
The proofs below are reconstructed, not transcribed from a consulted source; see
Humphreys, *Representations of semisimple Lie algebras in the BGG category O*, §4.2
for the classical application identified in `BGG/Uniqueness.lean`.
-/

open Module
noncomputable section

namespace UniversalEnvelopingAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

private theorem finite_degree_indices {σ : Type*} [Finite σ] (n : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree ≤ n} := by
  let f : {s : σ →₀ ℕ // s.degree ≤ n} → (σ → Fin (n + 1)) :=
    fun s i ↦ ⟨s.1 i, Nat.lt_succ_of_le ((Finsupp.le_degree i s.1).trans s.2)⟩
  exact Finite.of_injective f fun s t h ↦ Subtype.ext
    (Finsupp.ext fun i ↦ congrArg Fin.val (congrFun h i))

/-- Each PBW filtration piece of a finite-dimensional Lie algebra is finite-dimensional. -/
theorem finiteDimensional_filtration [FiniteDimensional K L] (n : ℕ) :
    FiniteDimensional K (filtration K L n) := by
  have := finite_degree_indices (σ := Fin (finrank K L)) n
  exact Module.Finite.of_basis (filtrationBasis (Module.finBasis K L) n)

/-- An elementary polynomial growth bound for the PBW filtration. -/
theorem finrank_filtration_le [FiniteDimensional K L] (n : ℕ) :
    finrank K (filtration K L n) ≤ (n + 1) ^ finrank K L := by
  classical
  have := finite_degree_indices (σ := Fin (finrank K L)) n
  let := Fintype.ofFinite {s : Fin (finrank K L) →₀ ℕ // s.degree ≤ n}
  rw [finrank_eq_card_basis (filtrationBasis (Module.finBasis K L) n)]
  let f : {s : Fin (finrank K L) →₀ ℕ // s.degree ≤ n} →
      (Fin (finrank K L) → Fin (n + 1)) :=
    fun s i ↦ ⟨s.1 i, Nat.lt_succ_of_le ((Finsupp.le_degree i s.1).trans s.2)⟩
  have hf : Function.Injective f := fun s t h ↦ Subtype.ext
    (Finsupp.ext fun i ↦ congrArg Fin.val (congrFun h i))
  simpa using Fintype.card_le_of_injective f hf

private theorem exists_polynomial_lt_two_pow (c r : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ c * n ^ r < 2 ^ n := by
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt r (by norm_num : (1 : ℝ) < 2)).const_mul
    (c : ℝ)
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, (c : ℝ) * (n ^ r / 2 ^ n) < 1 :=
    hlim.eventually_lt_const (by simp)
  obtain ⟨n, hn, h⟩ := (Filter.eventually_ge_atTop 1 |>.and hsmall).exists
  refine ⟨n, hn, ?_⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h' : (c : ℝ) * (n : ℝ) ^ r < (2 : ℝ) ^ n := by
    apply (div_lt_one hp).mp
    simpa [mul_div_assoc] using h
  exact_mod_cast h'

private theorem not_doubling_of_polynomial_bound (f : ℕ → ℕ) (d r : ℕ)
    (hzero : 0 < f 0) (hbound : ∀ n, f n ≤ (n + 1) ^ r) :
    ¬ ∀ n, 2 * f n ≤ f (n + d) := by
  intro hdouble
  have hgrowth : ∀ n, 2 ^ n ≤ f (n * d) := by
    intro n
    induction n with
    | zero => simpa using Nat.succ_le_iff.mpr hzero
    | succ n ih =>
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := pow_succ' _ _
        _ ≤ 2 * f (n * d) := Nat.mul_le_mul_left 2 ih
        _ ≤ f ((n + 1) * d) := by simpa [Nat.add_mul] using hdouble (n * d)
  obtain ⟨n, hn, hlt⟩ := exists_polynomial_lt_two_pow ((d + 1) ^ r) r
  have hle : 2 ^ n ≤ (d + 1) ^ r * n ^ r := calc
    2 ^ n ≤ f (n * d) := hgrowth n
    _ ≤ (n * d + 1) ^ r := hbound _
    _ ≤ ((d + 1) * n) ^ r := Nat.pow_le_pow_left (by nlinarith) r
    _ = (d + 1) ^ r * n ^ r := mul_pow _ _ _
  omega

/-- The enveloping algebra of a finite-dimensional Lie algebra has common nonzero left multiples.
This is the essential Ore condition, proved for the actual enveloping algebra by PBW
polynomial growth, rather than assumed as a typeclass. -/
theorem exists_common_left_multiple [FiniteDimensional K L]
    (a b : UniversalEnvelopingAlgebra K L) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ u v : UniversalEnvelopingAlgebra K L, u * a = v * b ∧ u * a ≠ 0 := by
  by_contra! hdisjoint
  obtain ⟨da, hda⟩ := exists_mem_filtration a
  obtain ⟨db, hdb⟩ := exists_mem_filtration b
  let d := max da db
  have hda' : a ∈ filtration K L d := filtration_mono (le_max_left _ _) hda
  have hdb' : b ∈ filtration K L d := filtration_mono (le_max_right _ _) hdb
  have hfinite : ∀ n, FiniteDimensional K (filtration K L n) :=
    finiteDimensional_filtration
  have hdouble : ∀ n, 2 * finrank K (filtration K L n) ≤
      finrank K (filtration K L (n + d)) := by
    intro n
    let T : (filtration K L n × filtration K L n) →ₗ[K] filtration K L (n + d) :=
      { toFun := fun x ↦ ⟨x.1.1 * a + x.2.1 * b,
          add_mem (mul_mem_filtration x.1.2 hda') (mul_mem_filtration x.2.2 hdb')⟩
        map_add' := fun x y ↦ Subtype.ext (by dsimp; noncomm_ring)
        map_smul' := fun c x ↦ Subtype.ext (by dsimp; simp [smul_add]) }
    have hT : Function.Injective T := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      rintro ⟨u, v⟩ h
      have heq : u.1 * a = (-v.1) * b := by
        have h' := congrArg Subtype.val h
        change u.1 * a + v.1 * b = 0 at h'
        simpa using (eq_neg_of_add_eq_zero_left h')
      have hu : u.1 = 0 := (mul_eq_zero.mp (hdisjoint u.1 (-v.1) heq)).resolve_right ha
      have hv : v.1 = 0 := by
        rw [hu, zero_mul, neg_mul, eq_comm, neg_eq_zero] at heq
        exact (mul_eq_zero.mp heq).resolve_right hb
      exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
    have := LinearMap.finrank_le_finrank_of_injective hT
    simpa [Module.finrank_prod, two_mul] using this
  have hzero : 0 < finrank K (filtration K L 0) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨1, one_mem_filtration 0⟩, fun h ↦ one_ne_zero (congrArg Subtype.val h)⟩
  exact not_doubling_of_polynomial_bound (fun n ↦ finrank K (filtration K L n)) d
    (finrank K L) hzero finrank_filtration_le hdouble

/-- The nonzero elements of the enveloping algebra of a finite-dimensional Lie algebra
form a left Ore set.
No Ore hypothesis is imposed: the witnesses come from `exists_common_left_multiple`. -/
theorem nonempty_oreSet [FiniteDimensional K L] :
    Nonempty (OreLocalization.OreSet
      (nonZeroDivisors (UniversalEnvelopingAlgebra K L))) := by
  apply OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors.mpr
  intro r s
  by_cases hr : r = 0
  · exact ⟨0, 1, by simp [hr]⟩
  obtain ⟨u, v, huv, hu⟩ := exists_common_left_multiple r s.1 hr
    (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
  refine ⟨v, ⟨u, mem_nonZeroDivisors_iff_ne_zero.mpr ?_⟩, huv⟩
  intro h
  exact hu (by rw [h, zero_mul])

end UniversalEnvelopingAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

include hA

/-- The actual negative-nilradical enveloping algebra in finite type is a left Ore domain. -/
theorem nonempty_oreSet_envNNeg :
    Nonempty (OreLocalization.OreSet (nonZeroDivisors
      (UniversalEnvelopingAlgebra K (nNeg P)))) := by
  have := finiteDimensional P hA
  exact UniversalEnvelopingAlgebra.nonempty_oreSet

namespace VermaModule

/-- Every two nonzero Lie submodules of an arbitrary-weight finite-type Verma module
intersect nontrivially. This is the uniformity step of the standard Ore-domain proof of
classical Hom uniqueness. No integrality, regularity, or algebraic closure is required. -/
theorem inf_ne_bot_of_finite_type (Λ : Dual K H)
    (N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ))
    (h₁ : N₁ ≠ ⊥) (h₂ : N₂ ≠ ⊥) : N₁ ⊓ N₂ ≠ ⊥ := by
  have := finiteDimensional P hA
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ N₁, x ≠ 0 := by
    simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, exists_prop] using h₁
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ N₂, y ≠ 0 := by
    simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, exists_prop] using h₂
  obtain ⟨a, rfl⟩ := (equivEnvNNeg P Λ).surjective x
  obtain ⟨b, rfl⟩ := (equivEnvNNeg P Λ).surjective y
  have ha : a ≠ 0 := fun h ↦ hx0 (by rw [h, map_zero])
  have hb : b ≠ 0 := fun h ↦ hy0 (by rw [h, map_zero])
  obtain ⟨u, v, huv, hu⟩ := UniversalEnvelopingAlgebra.exists_common_left_multiple a b ha hb
  rw [ne_eq, LieSubmodule.eq_bot_iff]
  push Not
  refine ⟨equivEnvNNeg P Λ (u * a), ⟨?_, ?_⟩, ?_⟩
  · rw [equivEnvNNeg_mul]
    exact smul_mem P Λ N₁ _ hx
  · rw [huv, equivEnvNNeg_mul]
    exact smul_mem P Λ N₂ _ hy
  · exact (LinearEquiv.map_ne_zero_iff _).mpr hu

end VermaModule
end Matrix.Realization.KacMoodyAlgebra
