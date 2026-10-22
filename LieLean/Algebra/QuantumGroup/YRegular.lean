/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Weight
import Mathlib.RingTheory.Localization.Module

/-!
# `Y`-regular root data

A root datum `(Y, …)` is `Y`-regular if the simple coroots `i ∈ Y` are linearly independent
([Lus] 2.2.2). For `Y` free of finite rank over `ℤ`, `Y`-regularity gives weights
`Λ ∈ Hom(Y, ℤ)` with all `⟨i, Λ⟩` arbitrarily large. This is the hypothesis `hY` of the
dominant-tensor characterization of the canonical basis of `U̇` ([Lus] Thm. 25.2.1,
`LieLean.QuantumGroup.existsUnique_modifiedCanonical`).

## Main definitions

* `LusztigCartanDatum.RootDatum.IsYRegular`: the simple coroots `i ∈ Y` are linearly independent.

## Main results

* `LusztigCartanDatum.RootDatum.exists_le_coroot_of_isYRegular`: for `Y` free of finite rank,
  `I` finite and `R` `Y`-regular, for every `N` there is `Λ : Y →+ ℤ` with `N ≤ ⟨i, Λ⟩` for all
  `i`.

## Proof

Write `Y ⊆ ℚ ⊗ Y`. The coroots stay linearly independent over `ℚ`, so some `ℚ`-linear form
takes the value `1` on all of them; a common denominator `d` of its values on a `ℤ`-basis of
`Y` makes `d` times it integral, with value `d ≥ 1` on every coroot. Multiply by `N`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §2.2.
-/

noncomputable section

namespace LusztigCartanDatum.RootDatum

variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} (R : D.RootDatum Y)

/-- A root datum is `Y`-regular if the simple coroots `i ∈ Y` are linearly independent
([Lus] 2.2.2). -/
def IsYRegular : Prop := LinearIndependent ℤ R.coroot

variable {R}

/-- For `Y` free of finite rank over `ℤ` and `I` finite, a `Y`-regular root datum has a weight
`Λ : Y →+ ℤ` with `⟨i, Λ⟩ = d` for all `i`, for some `d ≥ 1`. -/
theorem exists_coroot_eq_of_isYRegular [Finite I] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (hR : R.IsYRegular) : ∃ d : ℤ, 1 ≤ d ∧ ∃ Λ : Y →+ ℤ, ∀ i, Λ (R.coroot i) = d := by
  classical
  let κ := Module.Free.ChooseBasisIndex ℤ Y
  let b := Module.Free.chooseBasis ℤ Y
  -- the embedding `Y → (κ → ℚ)`
  let e : Y →ₗ[ℤ] (κ → ℚ) :=
    (LinearMap.funLeft ℤ ℚ id ∘ₗ (Finsupp.lcoeFun ∘ₗ
      Finsupp.mapRange.linearMap (Int.castAddHom ℚ).toIntLinearMap)) ∘ₗ b.repr.toLinearMap
  have he : ∀ y j, e y j = (b.repr y j : ℚ) := fun y j ↦ rfl
  have he_inj : Function.Injective e := by
    intro y y' h
    apply b.repr.injective
    ext j
    have := congr_fun h j
    rw [he, he] at this
    exact_mod_cast this
  have hZ : LinearIndependent ℤ (e ∘ R.coroot) := hR.map' e (LinearMap.ker_eq_bot.2 he_inj)
  have hQ : LinearIndependent ℚ (e ∘ R.coroot) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hZ
  -- a `ℚ`-linear form with value `1` on the coroots
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Module.Basis.span hQ).constr ℚ fun _ ↦ (1 : ℚ) : _ →ₗ[ℚ] ℚ)
  have hg1 : ∀ i, g (e (R.coroot i)) = 1 := fun i ↦ by
    have := LinearMap.congr_fun hg (Module.Basis.span hQ i)
    rw [Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply,
      Module.Basis.span_apply] at this
    exact this
  -- clearing denominators
  let c : κ → ℚ := fun j ↦ g (Pi.single j 1)
  let d : ℕ := ∏ j, (c j).den
  have hd : (d : ℤ) ≥ 1 := by
    have : 0 < d := Finset.prod_pos fun j _ ↦ (c j).den_pos
    omega
  have hint : ∀ j, ∃ a : ℤ, (a : ℚ) = d * c j := fun j ↦ by
    obtain ⟨m, hm⟩ : (c j).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    refine ⟨(c j).num * m, ?_⟩
    rw [hm, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, mul_comm ((c j).den : ℚ),
      mul_assoc, Rat.den_mul_eq_num, mul_comm]
  choose a ha using hint
  let Λ : Y →+ ℤ :=
    (∑ j, a j • (b.coord j : Y →ₗ[ℤ] ℤ)).toAddMonoidHom
  have hΛ : ∀ y, (Λ y : ℚ) = d * g (e y) := fun y ↦ by
    have hy : e y = ∑ j, (b.repr y j : ℚ) • Pi.single j 1 := by
      ext j'; simp [he, Finset.sum_apply, Pi.single_apply]
    rw [hy, map_sum, Finset.mul_sum]
    simp only [Λ, LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply,
      LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, map_smul]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ha]
    simp only [c]
    ring
  refine ⟨d, hd, Λ, fun i ↦ ?_⟩
  have := hΛ (R.coroot i)
  rw [hg1, mul_one] at this
  exact_mod_cast this

/-- For `Y` free of finite rank over `ℤ` and `I` finite, a `Y`-regular root datum has, for every
`N`, a weight `Λ : Y →+ ℤ` with `N ≤ ⟨i, Λ⟩` for all `i` (the hypothesis `hY` of [Lus]
Thm. 25.2.1). -/
theorem exists_le_coroot_of_isYRegular [Finite I] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (hR : R.IsYRegular) (N : ℕ) : ∃ Λ : Y →+ ℤ, ∀ i, (N : ℤ) ≤ Λ (R.coroot i) := by
  obtain ⟨d, hd, Λ, hΛ⟩ := exists_coroot_eq_of_isYRegular hR
  refine ⟨(N : ℤ) • Λ, fun i ↦ ?_⟩
  rw [AddMonoidHom.smul_apply, hΛ, smul_eq_mul]
  nlinarith

end LusztigCartanDatum.RootDatum
