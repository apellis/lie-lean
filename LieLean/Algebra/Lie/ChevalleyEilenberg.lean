/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The Chevalley–Eilenberg complex in low degrees

For a Lie algebra `L` over a commutative ring `R`, the Chevalley–Eilenberg complex computing the
Lie algebra homology `H_•(L)` with trivial coefficients is `⋯ → ⋀³L → ⋀²L → L → R`, with
differential
`∂(x₁ ∧ ⋯ ∧ xₙ) = ∑_{i < j} (-1)^{i+j} [xᵢ, xⱼ] ∧ x₁ ∧ ⋯ x̂ᵢ ⋯ x̂ⱼ ⋯ ∧ xₙ`.
We only need the degrees two and three:
`∂₂ (a ∧ b) = -[a, b]` and `∂₃ (a ∧ b ∧ c) = -[a, b] ∧ c + [a, c] ∧ b - [b, c] ∧ a`.

We prove `∂₂ ∘ ∂₃ = 0` (this is the Jacobi identity) and naturality, and the part of the five-term
exact sequence of a surjection `φ : L → L'` of Lie algebras (with kernel `𝔯`) which we need:
`H₂(L') → 𝔯 / [L, 𝔯] → H₁(L)` is exact at `𝔯 / [L, 𝔯]`. Concretely: if `t ∈ ⋀²L` and the
two-cycle `(⋀²φ) t` of `L'` is a boundary, then `∂₂ t ∈ [L, 𝔯]`
(`LieAlgebra.ChevalleyEilenberg.d₂_mem_lie_ker_of_map_mem_range_d₃`).

## Main definitions

* `LieAlgebra.ChevalleyEilenberg.wedge₂`: the bilinear map `(a, b) ↦ a ∧ b` into `⋀²L`.
* `LieAlgebra.ChevalleyEilenberg.d₂`: the differential `∂₂ : ⋀²L → L`.
* `LieAlgebra.ChevalleyEilenberg.d₃`: the differential `∂₃ : ⋀³L → ⋀²L`.

## Main results

* `LieAlgebra.ChevalleyEilenberg.d₂_comp_d₃`: `∂₂ ∘ ∂₃ = 0`.
* `LieAlgebra.ChevalleyEilenberg.d₂_map`, `d₃_map`: naturality.
* `LieAlgebra.ChevalleyEilenberg.d₂_mem_lie_ker_of_map_mem_range_d₃`: exactness of
  `H₂(L') → 𝔯 / [L, 𝔯] → H₁(L)` in the middle, for a surjection `L → L'` with kernel `𝔯` onto a
  projective module `L'`.
* `LieAlgebra.ChevalleyEilenberg.ker_inf_le_of_range_d₃_eq_ker_d₂`: if `H₂(L') = 0` then
  `𝔯 ∩ [L, L] ⊆ [L, 𝔯]`.

## References

* C. A. Weibel, *An introduction to homological algebra*, CUP 1994, §7.7 (check) (the
  Chevalley–Eilenberg complex) and §7.5 (check) (the Hochschild–Serre spectral sequence and its
  five-term exact sequence; we prove only the part used here, by a direct argument which we
  reconstructed).
-/

open exteriorPower

namespace LieAlgebra

namespace ChevalleyEilenberg

section Wedge

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

lemma ιMulti_two_update_zero (a b c : M) :
    ιMulti R 2 ![c, b] = ιMulti R 2 (Function.update ![a, b] 0 c) := by
  congr 1; ext i; fin_cases i <;> rfl

lemma ιMulti_two_update_one (a b c : M) :
    ιMulti R 2 ![a, c] = ιMulti R 2 (Function.update ![a, b] 1 c) := by
  congr 1; ext i; fin_cases i <;> rfl

/-- The bilinear map `(a, b) ↦ a ∧ b ∈ ⋀²M`. -/
noncomputable def wedge₂ : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      rw [ιMulti_two_update_zero R M a b, ιMulti_two_update_zero R M a b,
        ιMulti_two_update_zero R M a b, AlternatingMap.map_update_add])
    (fun c a b ↦ by
      rw [ιMulti_two_update_zero R M a b, ιMulti_two_update_zero R M a b,
        AlternatingMap.map_update_smul])
    (fun a b b' ↦ by
      rw [ιMulti_two_update_one R M a b, ιMulti_two_update_one R M a b,
        ιMulti_two_update_one R M a b, AlternatingMap.map_update_add])
    (fun c a b ↦ by
      rw [ιMulti_two_update_one R M a b, ιMulti_two_update_one R M a b,
        AlternatingMap.map_update_smul])

variable {R M}

lemma wedge₂_apply (a b : M) : wedge₂ R M a b = ιMulti R 2 ![a, b] := rfl

lemma ιMulti_two (v : Fin 2 → M) : ιMulti R 2 v = wedge₂ R M (v 0) (v 1) := by
  rw [wedge₂_apply]; congr 1; ext i; fin_cases i <;> rfl

@[simp] lemma wedge₂_self (a : M) : wedge₂ R M a a = 0 :=
  (ιMulti R 2).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)

lemma wedge₂_swap (a b : M) : wedge₂ R M b a = -wedge₂ R M a b := by
  have h := wedge₂_self (R := R) (a + b)
  simp only [map_add, LinearMap.add_apply, wedge₂_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

lemma span_wedge₂ : Submodule.span R (Set.range fun p : M × M ↦ wedge₂ R M p.1 p.2) = ⊤ := by
  rw [eq_top_iff, ← ιMulti_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨v, rfl⟩
  exact ⟨(v 0, v 1), (ιMulti_two v).symm⟩

@[simp] lemma map_wedge₂ {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (a b : M) :
    map 2 f (wedge₂ R M a b) = wedge₂ R N (f a) (f b) := by
  rw [wedge₂_apply, map_apply_ιMulti, wedge₂_apply]
  congr 1; ext i; fin_cases i <;> rfl

/-- The wedge `a ∧ b ∧ c ∈ ⋀³M`. -/
noncomputable abbrev wedge₃ (a b c : M) : ⋀[R]^3 M := ιMulti R 3 ![a, b, c]

lemma ιMulti_three (v : Fin 3 → M) : ιMulti R 3 v = wedge₃ (v 0) (v 1) (v 2) := by
  congr 1; ext i; fin_cases i <;> rfl

end Wedge

section CommRing

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The alternating map `(a, b) ↦ -[a, b]`. -/
noncomputable def d₂Alt : L [⋀^Fin 2]→ₗ[R] L where
  toFun v := -⁅v 0, v 1⁆
  map_update_add' v i x y := by
    obtain rfl : ‹DecidableEq (Fin 2)› = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [add_lie, lie_add, -lie_skew] <;> abel
  map_update_smul' v i c x := by
    obtain rfl : ‹DecidableEq (Fin 2)› = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [-lie_skew]
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all

/-- The Chevalley–Eilenberg differential `∂₂ : ⋀²L → L`, `a ∧ b ↦ -[a, b]`. -/
noncomputable def d₂ : ⋀[R]^2 L →ₗ[R] L := alternatingMapLinearEquiv (d₂Alt R L)

/-- The alternating map `(a, b, c) ↦ -[a, b] ∧ c + [a, c] ∧ b - [b, c] ∧ a`. -/
noncomputable def d₃Alt : L [⋀^Fin 3]→ₗ[R] ⋀[R]^2 L where
  toFun v := -wedge₂ R L ⁅v 0, v 1⁆ (v 2) + wedge₂ R L ⁅v 0, v 2⁆ (v 1) -
    wedge₂ R L ⁅v 1, v 2⁆ (v 0)
  map_update_add' v i x y := by
    obtain rfl : ‹DecidableEq (Fin 3)› = instDecidableEqFin 3 := Subsingleton.elim _ _
    fin_cases i <;> simp [add_lie, lie_add, -lie_skew] <;> abel
  map_update_smul' v i c x := by
    obtain rfl : ‹DecidableEq (Fin 3)› = instDecidableEqFin 3 := Subsingleton.elim _ _
    fin_cases i <;> simp [smul_sub, smul_add, -lie_skew]
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hv hij
    all_goals first
      | exact absurd rfl hij
      | rw [hv]; simp [← lie_skew (v 2) (v 1), ← lie_skew (v 1) (v 0), -lie_skew]

/-- The Chevalley–Eilenberg differential `∂₃ : ⋀³L → ⋀²L`,
`a ∧ b ∧ c ↦ -[a, b] ∧ c + [a, c] ∧ b - [b, c] ∧ a`. -/
noncomputable def d₃ : ⋀[R]^3 L →ₗ[R] ⋀[R]^2 L := alternatingMapLinearEquiv (d₃Alt R L)

variable {R L}

@[simp] lemma d₂_wedge₂ (a b : L) : d₂ R L (wedge₂ R L a b) = -⁅a, b⁆ := by
  rw [wedge₂_apply, d₂, alternatingMapLinearEquiv_apply_ιMulti]; rfl

lemma d₂_ιMulti (v : Fin 2 → L) : d₂ R L (ιMulti R 2 v) = -⁅v 0, v 1⁆ := by
  rw [ιMulti_two, d₂_wedge₂]

@[simp] lemma d₃_wedge₃ (a b c : L) : d₃ R L (wedge₃ a b c) =
    -wedge₂ R L ⁅a, b⁆ c + wedge₂ R L ⁅a, c⁆ b - wedge₂ R L ⁅b, c⁆ a := by
  rw [d₃, alternatingMapLinearEquiv_apply_ιMulti]; rfl

lemma d₃_ιMulti (v : Fin 3 → L) : d₃ R L (ιMulti R 3 v) =
    -wedge₂ R L ⁅v 0, v 1⁆ (v 2) + wedge₂ R L ⁅v 0, v 2⁆ (v 1) - wedge₂ R L ⁅v 1, v 2⁆ (v 0) := by
  rw [ιMulti_three, d₃_wedge₃]

/-- `∂₂ ∘ ∂₃ = 0`: this is the Jacobi identity. -/
theorem d₂_comp_d₃ : d₂ R L ∘ₗ d₃ R L = 0 := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    d₃_ιMulti, map_sub, map_add, map_neg, d₂_wedge₂, LinearMap.zero_apply]
  have := lie_jacobi (v 0) (v 1) (v 2)
  rw [← lie_skew (v 0) ⁅v 1, v 2⁆, ← lie_skew (v 1) ⁅v 2, v 0⁆, ← lie_skew (v 2) ⁅v 0, v 1⁆,
    ← lie_skew (v 2) (v 0)] at this
  simp only [neg_lie, neg_neg] at this
  rw [← neg_eq_zero, ← this]
  abel

@[simp] lemma d₂_d₃ (w : ⋀[R]^3 L) : d₂ R L (d₃ R L w) = 0 :=
  LinearMap.congr_fun d₂_comp_d₃ w

lemma range_d₃_le_ker_d₂ : LinearMap.range (d₃ R L) ≤ LinearMap.ker (d₂ R L) := by
  rintro _ ⟨w, rfl⟩; exact d₂_d₃ w

section naturality

variable {L' : Type*} [LieRing L'] [LieAlgebra R L'] (φ : L →ₗ⁅R⁆ L')

/-- Naturality of `∂₂`. -/
theorem d₂_map (t : ⋀[R]^2 L) : d₂ R L' (map 2 (φ : L →ₗ[R] L') t) = φ (d₂ R L t) := by
  have : d₂ R L' ∘ₗ map 2 (φ : L →ₗ[R] L') = (φ : L →ₗ[R] L') ∘ₗ d₂ R L := by
    refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      map_apply_ιMulti, d₂_ιMulti, map_neg, LieHom.coe_toLinearMap, LieHom.map_lie]
  exact LinearMap.congr_fun this t

/-- Naturality of `∂₃`. -/
theorem d₃_map (w : ⋀[R]^3 L) :
    d₃ R L' (map 3 (φ : L →ₗ[R] L') w) = map 2 (φ : L →ₗ[R] L') (d₃ R L w) := by
  have : d₃ R L' ∘ₗ map 3 (φ : L →ₗ[R] L') = map 2 (φ : L →ₗ[R] L') ∘ₗ d₃ R L := by
    refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      map_apply_ιMulti, d₃_ιMulti, map_sub, map_add, map_neg, map_wedge₂,
      LieHom.coe_toLinearMap, LieHom.map_lie]
  exact LinearMap.congr_fun this w

end naturality

variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/-- The image under `∂₂` of the span of some wedges `a ∧ b` is the span of the corresponding
brackets. -/
lemma map_d₂_span_wedge₂ (p : L → L → Prop) :
    (Submodule.span R {t | ∃ a b, p a b ∧ t = wedge₂ R L a b}).map (d₂ R L) =
      Submodule.span R {x | ∃ a b, p a b ∧ x = ⁅a, b⁆} := by
  rw [Submodule.map_span]
  have : d₂ R L '' {t | ∃ a b, p a b ∧ t = wedge₂ R L a b} =
      -{x | ∃ a b, p a b ∧ x = ⁅a, b⁆} := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_neg]
    constructor
    · rintro ⟨_, ⟨a, b, hab, rfl⟩, rfl⟩; exact ⟨a, b, hab, by simp⟩
    · rintro ⟨a, b, hab, hx⟩
      exact ⟨_, ⟨a, b, hab, rfl⟩, by rw [d₂_wedge₂, ← hx, neg_neg]⟩
  rw [this, Submodule.span_neg]

/-- The five-term exact sequence of a surjection `φ : L → L'` with kernel `𝔯`, at `𝔯 / [L, 𝔯]`:
if `t ∈ ⋀²L` and `(⋀²φ) t` is a boundary, then `∂₂ t ∈ [L, 𝔯]`. (If moreover `∂₂ t ∈ 𝔯`, then
`(⋀²φ) t` is a cycle by naturality; this is the map `H₂(L') → 𝔯 / [L, 𝔯]`.) We assume that `L'` is
a projective `R`-module, e.g. that `R` is a field. -/
theorem d₂_mem_lie_ker_of_map_mem_range_d₃ [Module.Projective R L'] {φ : L →ₗ⁅R⁆ L'}
    (hφ : Function.Surjective φ) {t : ⋀[R]^2 L}
    (ht : map 2 (φ : L →ₗ[R] L') t ∈ LinearMap.range (d₃ R L')) :
    d₂ R L t ∈ ⁅(⊤ : LieIdeal R L), φ.ker⁆ := by
  set I : LieIdeal R L := ⁅(⊤ : LieIdeal R L), φ.ker⁆
  set q : L →ₗ[R] L ⧸ I.toSubmodule := I.toSubmodule.mkQ
  obtain ⟨s, hs⟩ := (φ : L →ₗ[R] L').exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hφ)
  have hs' : ∀ a : L', φ (s a) = a := fun a ↦ LinearMap.congr_fun hs a
  have hker : ∀ a : L, s (φ a) - a ∈ φ.ker := fun a ↦ by
    rw [LieHom.mem_ker, map_sub, hs', sub_self]
  -- the map `D : ⋀²L' → L / [L, 𝔯]` with `D ∘ ⋀²φ = q ∘ ∂₂`
  set D : ⋀[R]^2 L' →ₗ[R] L ⧸ I.toSubmodule := q ∘ₗ d₂ R L ∘ₗ map 2 s
  have hD : D ∘ₗ map 2 (φ : L →ₗ[R] L') = q ∘ₗ d₂ R L := by
    refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
    simp only [D, q, LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      map_apply_ιMulti, d₂_ιMulti, map_neg, Submodule.mkQ_apply, LieHom.coe_toLinearMap]
    rw [neg_inj, Submodule.Quotient.eq]
    have h1 := hker (v 0)
    have h2 := hker (v 1)
    have : ⁅s (φ (v 0)), s (φ (v 1))⁆ - ⁅v 0, v 1⁆ =
        ⁅s (φ (v 0)) - v 0, s (φ (v 1)) - v 1⁆ + ⁅v 0, s (φ (v 1)) - v 1⁆ -
          ⁅v 1, s (φ (v 0)) - v 0⁆ := by
      simp only [lie_sub, sub_lie, ← lie_skew (v 1) (v 0), ← lie_skew (v 1) (s (φ (v 0)))]
      abel
    rw [this]
    refine I.toSubmodule.sub_mem (I.toSubmodule.add_mem ?_ ?_) ?_ <;>
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) ‹_›
  obtain ⟨w, hw⟩ := ht
  obtain ⟨w', rfl⟩ := map_surjective (R := R) (n := 3) (f := (φ : L →ₗ[R] L')) hφ w
  rw [d₃_map] at hw
  have h1 := LinearMap.congr_fun hD (d₃ R L w')
  have h2 := LinearMap.congr_fun hD t
  simp only [LinearMap.coe_comp, Function.comp_apply] at h1 h2
  rw [hw, h2, d₂_d₃, map_zero] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

/-- If `H₂(L') = 0` and `φ : L → L'` is surjective with kernel `𝔯`, then `𝔯 ∩ [L, L] ⊆ [L, 𝔯]`
(part of the five-term exact sequence). -/
theorem ker_inf_le_of_range_d₃_eq_ker_d₂ [Module.Projective R L'] {φ : L →ₗ⁅R⁆ L'}
    (hφ : Function.Surjective φ) (h : LinearMap.range (d₃ R L') = LinearMap.ker (d₂ R L')) :
    φ.ker ⊓ ⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆ ≤ ⁅(⊤ : LieIdeal R L), φ.ker⁆ := by
  rintro x ⟨hx, hx'⟩
  have hx'' : x ∈ LinearMap.range (d₂ R L) := by
    have : (⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆ : LieIdeal R L).toSubmodule ≤
        LinearMap.range (d₂ R L) := by
      rw [LieSubmodule.lieIdeal_oper_eq_linear_span, Submodule.span_le]
      rintro _ ⟨a, b, rfl⟩
      exact ⟨-wedge₂ R L a b, by simp⟩
    exact this hx'
  obtain ⟨t, rfl⟩ := hx''
  refine d₂_mem_lie_ker_of_map_mem_range_d₃ hφ ?_
  rw [h, LinearMap.mem_ker, d₂_map]
  exact hx

end CommRing

end ChevalleyEilenberg

end LieAlgebra
