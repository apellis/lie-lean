/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import LieLean.LinearAlgebra.Matrix.Cartan.Generalized

/-!
# The standard bilinear form on a realization of a symmetrizable matrix

Let `A` be a symmetrizable square integer matrix, written as `A = diag(ε) B` with `εᵢ` positive
rationals and `B` symmetric, and let `(𝔥, Π, Π^∨)` be a realization of `A` over a field `K` of
characteristic zero. Following [Kac] §2.1, fix a complement `𝔥''` of the span of the simple
coroots in `𝔥` and define a bilinear form on `𝔥` by (2.1.2)–(2.1.3):
`(αᵢ^∨ | h) = ⟨αᵢ, h⟩ εᵢ` for `h ∈ 𝔥` and `(h' | h'') = 0` for `h', h'' ∈ 𝔥''`.
The complement `𝔥''` is chosen once and for all (`Matrix.Realization.corootCompl`).

## Main definitions

* `Matrix.Symmetrization`: a symmetrization `A = diag(ε) B` of `A` ([Kac] (2.1.1), (2.3.1)).
* `Matrix.Realization.corootCoord`: coordinates with respect to the simple coroots; its kernel
  `Matrix.Realization.corootCompl` is the chosen complement `𝔥''` of the span of the coroots.
* `Matrix.Realization.bilinForm`: the symmetric bilinear form on `𝔥` of [Kac] (2.1.2)–(2.1.3).
* `Matrix.Realization.toDual`: the isomorphism `ν : 𝔥 ≃ 𝔥*` induced by the form ([Kac] §2.1).
* `Matrix.Realization.dualBilinForm`: the induced form on `𝔥*`.
* `Matrix.Realization.rho`, `Matrix.Realization.rhoCheck`: elements `ρ ∈ 𝔥*`, `ρ^∨ ∈ 𝔥` with
  `⟨ρ, αᵢ^∨⟩ = 1` and `⟨αᵢ, ρ^∨⟩ = 1` for all `i` ([Kac] §2.5, §10.8; `ρ^∨` defines the
  principal gradation, [Kac] §1.5).

## Main results

* `Matrix.isSymmetrizable_iff_nonempty_symmetrization`.
* `Matrix.Realization.isSymm_bilinForm`, `Matrix.Realization.nondegenerate_bilinForm`: the form
  on `𝔥` is symmetric and nondegenerate ([Kac] Lemma 2.1 b)).
* `Matrix.Realization.bilinForm_coroot_left`, `Matrix.Realization.bilinForm_corootCompl`: the
  defining properties (2.1.2), (2.1.3).
* `Matrix.Realization.toDual_coroot`: `ν(αᵢ^∨) = εᵢ αᵢ` ([Kac] (2.1.5)).
* `Matrix.Realization.dualBilinForm_root_root`: `(αᵢ | αⱼ) = aᵢⱼ / εᵢ = bᵢⱼ`
  ([Kac] (2.1.6)).
* `Matrix.Realization.dualBilinForm_root_self`: `(αᵢ | αᵢ) = 2 / εᵢ`, a positive rational.
* `Matrix.Realization.apply_coroot_eq`: `⟨λ, αᵢ^∨⟩ = 2 (λ | αᵢ) / (αᵢ | αᵢ)`
  ([Kac] (2.3.5)).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.1, §2.3
  (stated over `ℂ`).
-/

open Module

noncomputable section

namespace Matrix

variable {ι : Type*}

/-- A symmetrization of a square integer matrix `A` ([Kac] (2.3.1)): positive rationals `εᵢ` such
that `A = diag(ε) B` with `B` symmetric, i.e. `εⱼ aᵢⱼ = εᵢ aⱼᵢ` for all `i, j`. The symmetric
matrix `B` is `Matrix.Symmetrization.matrix`. -/
structure Symmetrization (A : Matrix ι ι ℤ) where
  /-- The positive rationals `εᵢ`. -/
  ε : ι → ℚ
  ε_pos : ∀ i, 0 < ε i
  ε_mul_comm : ∀ i j, ε j * A i j = ε i * A j i

namespace Symmetrization

variable {A : Matrix ι ι ℤ} (S : A.Symmetrization)

lemma ε_ne_zero (i : ι) : S.ε i ≠ 0 := (S.ε_pos i).ne'

/-- The symmetric matrix `B = diag(ε)⁻¹ A`, with entries `bᵢⱼ = aᵢⱼ / εᵢ`. -/
def matrix : Matrix ι ι ℚ := of fun i j ↦ A i j / S.ε i

lemma matrix_apply (i j : ι) : S.matrix i j = A i j / S.ε i := rfl

lemma isSymm_matrix : S.matrix.IsSymm := by
  ext i j
  simp only [transpose_apply, matrix_apply]
  rw [div_eq_div_iff (S.ε_ne_zero j) (S.ε_ne_zero i), mul_comm (A j i : ℚ), S.ε_mul_comm,
    mul_comm]

lemma map_eq_diagonal_mul [Fintype ι] [DecidableEq ι] :
    A.map (Int.cast : ℤ → ℚ) = diagonal S.ε * S.matrix := by
  ext i j
  simp [diagonal_mul, matrix_apply, mul_div_cancel₀ _ (S.ε_ne_zero i)]

end Symmetrization

theorem isSymmetrizable_iff_nonempty_symmetrization [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℤ} : A.IsSymmetrizable ↔ Nonempty A.Symmetrization := by
  rw [isSymmetrizable_iff_mul_eq_mul]
  constructor
  · rintro ⟨d, hd, hdA⟩
    refine ⟨⟨fun i ↦ (d i : ℚ)⁻¹, fun i ↦ by simpa using hd i, fun i j ↦ ?_⟩⟩
    have hi : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    have hj : (d j : ℚ) ≠ 0 := by exact_mod_cast (hd j).ne'
    have : (d i : ℚ) * A i j = d j * A j i := by exact_mod_cast hdA i j
    field_simp
    linear_combination this
  · rintro ⟨S⟩
    exact isSymmetrizable_iff_mul_eq_mul.mp (isSymmetrizable_iff_exists_eq_diagonal_mul.mpr
      ⟨S.ε, S.matrix, S.ε_pos, S.isSymm_matrix, S.map_eq_diagonal_mul⟩)

namespace Realization

variable [Fintype ι] {A : Matrix ι ι ℤ} {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  (P : Realization A K H)

/-! ### Coordinates with respect to the simple coroots -/

/-- Coordinates with respect to the simple coroots: a chosen left inverse of
`c ↦ ∑ cᵢ αᵢ^∨`. Its kernel `P.corootCompl` is a complement of the span of the coroots. -/
def corootCoord : H →ₗ[K] ι → K := P.corootMap.leftInverse

@[simp] lemma corootCoord_corootMap (c : ι → K) : P.corootCoord (P.corootMap c) = c :=
  LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr P.corootMap_injective) c

lemma coroot_eq_corootMap [DecidableEq ι] (i : ι) : P.coroot i = P.corootMap (Pi.single i 1) := by
  simp [corootMap, Fintype.linearCombination_apply, Pi.single_apply]

@[simp] lemma corootCoord_coroot [DecidableEq ι] (i : ι) :
    P.corootCoord (P.coroot i) = Pi.single i 1 := by
  rw [coroot_eq_corootMap, corootCoord_corootMap]

/-- The chosen complement `𝔥''` of the span of the simple coroots ([Kac] §2.1). -/
def corootCompl : Submodule K H := LinearMap.ker P.corootCoord

theorem isCompl_corootCompl : IsCompl (LinearMap.range P.corootMap) P.corootCompl := by
  have h := LinearMap.isCompl_of_proj (p := LinearMap.range P.corootMap)
    (f := P.corootMap.rangeRestrict ∘ₗ P.corootCoord) (by
      rintro ⟨_, c, rfl⟩
      ext
      simp)
  have hker : LinearMap.ker (P.corootMap.rangeRestrict ∘ₗ P.corootCoord) = P.corootCompl := by
    rw [LinearMap.ker_comp, LinearMap.ker_rangeRestrict,
      LinearMap.ker_eq_bot.mpr P.corootMap_injective, Submodule.comap_bot]
    rfl
  rwa [hker] at h

/-! ### The elements `ρ` and `ρ^∨` -/

/-- An element `ρ ∈ 𝔥*` with `⟨ρ, αᵢ^∨⟩ = 1` for all `i` ([Kac] §10.8; [Kac] §2.5 has
`⟨ρ, αᵢ^∨⟩ = aᵢᵢ/2`, which is `1` when `aᵢᵢ = 2`). It exists since the simple coroots are linearly
independent; it is unique only up to the annihilator of the coroots, and this is a chosen one. -/
def rho : Dual K H := ∑ i, LinearMap.proj i ∘ₗ P.corootCoord

@[simp] theorem rho_coroot (i : ι) : P.rho (P.coroot i) = 1 := by
  classical
  simp [rho, LinearMap.sum_apply]

/-- An element `ρ^∨ ∈ 𝔥` with `⟨αᵢ, ρ^∨⟩ = 1` for all `i`; it exists since the simple roots are
linearly independent. It defines the principal gradation ([Kac] §1.5). -/
def rhoCheck [FiniteDimensional K H] : H :=
  (P.rootMap_surjective (fun _ ↦ 1)).choose

@[simp] theorem root_rhoCheck [FiniteDimensional K H] (i : ι) : P.root i P.rhoCheck = 1 :=
  congr_fun (P.rootMap_surjective (fun _ ↦ 1)).choose_spec i

/-- `⟨α, ρ^∨⟩` is the height of `α` for `α` in the root lattice. -/
theorem rootOf_rhoCheck [FiniteDimensional K H] (k : ι → ℤ) :
    P.rootOf k P.rhoCheck = ((height k : ℤ) : K) := by
  simp [rootOf_apply, height]

/-! ### The bilinear form on `𝔥` -/

variable {P} in
lemma sum_smul_coroot {c : ι → K} : ∑ i, c i • P.coroot i = P.corootMap c := by
  simp [corootMap, Fintype.linearCombination_apply]

variable (S : A.Symmetrization)

/-- The symmetric bilinear form on `𝔥` of [Kac] (2.1.2)–(2.1.3). In terms of the coordinates
`p(h)` of `corootCoord`, it is
`(x | y) = ∑ᵢ εᵢ (p(x)ᵢ ⟨αᵢ, y⟩ + p(y)ᵢ ⟨αᵢ, x⟩) - ∑ᵢⱼ εⱼ aᵢⱼ p(x)ᵢ p(y)ⱼ`,
see `Matrix.Realization.bilinForm_apply`. -/
def bilinForm : LinearMap.BilinForm K H :=
  ∑ i, (S.ε i : K) • (LinearMap.BilinForm.linMulLin (LinearMap.proj i ∘ₗ P.corootCoord)
      (P.root i) + LinearMap.BilinForm.linMulLin (P.root i)
        (LinearMap.proj i ∘ₗ P.corootCoord)) -
    ∑ i, ∑ j, ((S.ε j : K) * A i j) • LinearMap.BilinForm.linMulLin
      (LinearMap.proj i ∘ₗ P.corootCoord) (LinearMap.proj j ∘ₗ P.corootCoord)

lemma bilinForm_apply (x y : H) :
    P.bilinForm S x y = ∑ i, (S.ε i : K) * (P.corootCoord x i * P.root i y +
      P.corootCoord y i * P.root i x) -
      ∑ i, ∑ j, (S.ε j : K) * A i j * P.corootCoord x i * P.corootCoord y j := by
  simp only [bilinForm, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.BilinForm.linMulLin_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, smul_eq_mul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ by ring
  · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

variable [CharZero K]

theorem isSymm_bilinForm : (P.bilinForm S).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
  rw [bilinForm_apply, bilinForm_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  · conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have := congrArg (fun q : ℚ ↦ (q : K)) (S.ε_mul_comm j i)
    rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_intCast, Rat.cast_intCast] at this
    linear_combination -(P.corootCoord x i * P.corootCoord y j) * this

omit [CharZero K] in
/-- [Kac] (2.1.2): `(αᵢ^∨ | h) = ⟨αᵢ, h⟩ εᵢ`. -/
@[simp] theorem bilinForm_coroot_left (i : ι) (x : H) :
    P.bilinForm S (P.coroot i) x = S.ε i * P.root i x := by
  classical
  rw [bilinForm_apply]
  simp only [corootCoord_coroot, Pi.single_apply, P.root_coroot]
  have h2 : ∑ k, ∑ j, ((S.ε j : K) * A k j * if k = i then 1 else 0) * P.corootCoord x j =
      ∑ j, (S.ε j : K) * A i j * P.corootCoord x j := by
    rw [Fintype.sum_eq_single i (fun k hk ↦ by simp [hk])]
    simp
  rw [h2]
  simp only [mul_add, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [add_sub_assoc, sub_eq_zero.mpr (Finset.sum_congr rfl fun _ _ ↦ by ring), add_zero]

@[simp] theorem bilinForm_coroot_right (i : ι) (x : H) :
    P.bilinForm S x (P.coroot i) = S.ε i * P.root i x := by
  rw [(P.isSymm_bilinForm S).eq, bilinForm_coroot_left]

omit [CharZero K] in
lemma bilinForm_corootMap_left (c : ι → K) (x : H) :
    P.bilinForm S (P.corootMap c) x = ∑ i, c i * S.ε i * P.root i x := by
  rw [← sum_smul_coroot, map_sum, LinearMap.sum_apply]
  simp [mul_assoc]

omit [CharZero K] in
/-- [Kac] (2.1.3): `(h' | h'') = 0` for `h', h'' ∈ 𝔥''`. -/
theorem bilinForm_corootCompl {x y : H} (hx : x ∈ P.corootCompl) (hy : y ∈ P.corootCompl) :
    P.bilinForm S x y = 0 := by
  rw [corootCompl, LinearMap.mem_ker] at hx hy
  simp [bilinForm_apply, hx, hy]

/-- The form on `𝔥` is nondegenerate ([Kac] Lemma 2.1 b)). -/
theorem nondegenerate_bilinForm [FiniteDimensional K H] : (P.bilinForm S).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (P.isSymm_bilinForm S).isRefl).mpr fun x hx ↦ ?_
  -- `x` is killed by all simple roots, hence lies in the span of the coroots
  have hker : x ∈ LinearMap.ker P.rootMap := by
    rw [LinearMap.mem_ker]
    ext i
    have := hx (P.coroot i)
    rw [bilinForm_coroot_right] at this
    simpa [(S.ε_ne_zero i)] using this
  obtain ⟨c, rfl⟩ := P.ker_rootMap_le hker
  -- then `∑ cᵢ εᵢ αᵢ = 0`
  have hc : ∑ i, (c i * S.ε i) • P.root i = 0 := by
    ext y
    have := hx y
    rw [bilinForm_corootMap_left] at this
    simpa using this
  have := Fintype.linearIndependent_iff.mp P.linearIndependent_root _ hc
  have hc0 : c = 0 := by
    ext i
    simpa [S.ε_ne_zero i] using this i
  simp [hc0]

variable [FiniteDimensional K H]

/-- The isomorphism `ν : 𝔥 ≃ 𝔥*`, `ν(h) = (h | ·)`, induced by the form ([Kac] §2.1). -/
def toDual : H ≃ₗ[K] Dual K H :=
  (P.bilinForm S).toDual (P.nondegenerate_bilinForm S)

@[simp] lemma toDual_apply (x y : H) : P.toDual S x y = P.bilinForm S x y := rfl

@[simp] lemma bilinForm_toDual_symm_left (μ : Dual K H) (x : H) :
    P.bilinForm S ((P.toDual S).symm μ) x = μ x :=
  LinearMap.BilinForm.apply_toDual_symm_apply μ x

@[simp] lemma bilinForm_toDual_symm_right (μ : Dual K H) (x : H) :
    P.bilinForm S x ((P.toDual S).symm μ) = μ x := by
  rw [(P.isSymm_bilinForm S).eq, bilinForm_toDual_symm_left]

/-- [Kac] (2.1.5): `ν(αᵢ^∨) = εᵢ αᵢ`. -/
theorem toDual_coroot (i : ι) : P.toDual S (P.coroot i) = (S.ε i : K) • P.root i := by
  ext x
  simp

theorem toDual_symm_root (i : ι) :
    (P.toDual S).symm (P.root i) = (S.ε i : K)⁻¹ • P.coroot i := by
  rw [LinearEquiv.symm_apply_eq, map_smul, toDual_coroot, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast S.ε_ne_zero i), one_smul]

/-- The symmetric bilinear form on `𝔥*` induced by the form on `𝔥` via `ν` ([Kac] §2.1). -/
def dualBilinForm : LinearMap.BilinForm K (Dual K H) :=
  LinearMap.BilinForm.congr (P.toDual S) (P.bilinForm S)

lemma dualBilinForm_apply (μ μ' : Dual K H) :
    P.dualBilinForm S μ μ' = P.bilinForm S ((P.toDual S).symm μ) ((P.toDual S).symm μ') := rfl

/-- `(λ | μ) = ⟨λ, ν⁻¹(μ)⟩`. -/
lemma dualBilinForm_apply_eq (μ μ' : Dual K H) :
    P.dualBilinForm S μ μ' = μ ((P.toDual S).symm μ') := by
  rw [dualBilinForm_apply, bilinForm_toDual_symm_left]

theorem isSymm_dualBilinForm : (P.dualBilinForm S).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun μ μ' ↦ by
    rw [dualBilinForm_apply, dualBilinForm_apply, (P.isSymm_bilinForm S).eq]

/-- `(λ | αᵢ) = ⟨λ, αᵢ^∨⟩ / εᵢ`. -/
lemma dualBilinForm_root_right (μ : Dual K H) (i : ι) :
    P.dualBilinForm S μ (P.root i) = μ (P.coroot i) / S.ε i := by
  rw [dualBilinForm_apply_eq, toDual_symm_root, map_smul, smul_eq_mul, inv_mul_eq_div]

/-- [Kac] (2.1.6): `(αᵢ | αⱼ) = aᵢⱼ / εᵢ`, the entry `bᵢⱼ` of the symmetric matrix
`B`. -/
theorem dualBilinForm_root_root (i j : ι) :
    P.dualBilinForm S (P.root i) (P.root j) = (S.matrix i j : K) := by
  rw [dualBilinForm_root_right, P.root_coroot, S.matrix_apply]
  have hi : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  have hj : (S.ε j : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero j
  have : (S.ε j : K) * A i j = S.ε i * A j i := by exact_mod_cast S.ε_mul_comm i j
  push_cast
  field_simp
  linear_combination -this

variable {P} in
/-- `(αᵢ | αᵢ) = 2 / εᵢ` is a positive rational number ([Kac] (2.1.6), (2.3.3)). -/
theorem dualBilinForm_root_self (hA : A.IsGeneralizedCartan) (i : ι) :
    P.dualBilinForm S (P.root i) (P.root i) = ((2 / S.ε i : ℚ) : K) := by
  rw [dualBilinForm_root_right, P.root_coroot, hA.diag]
  push_cast
  rfl

omit [Fintype ι] in
lemma two_div_ε_pos (i : ι) : 0 < 2 / S.ε i := div_pos two_pos (S.ε_pos i)

variable {P} in
/-- [Kac] (2.3.5): `⟨λ, αᵢ^∨⟩ = 2 (λ | αᵢ) / (αᵢ | αᵢ)`. -/
theorem apply_coroot_eq (hA : A.IsGeneralizedCartan) (μ : Dual K H) (i : ι) :
    μ (P.coroot i) =
      2 * P.dualBilinForm S μ (P.root i) / P.dualBilinForm S (P.root i) (P.root i) := by
  rw [dualBilinForm_root_self S hA, dualBilinForm_root_right]
  have hi : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  push_cast
  field_simp

/-- `(ρ | αᵢ) = εᵢ⁻¹`. -/
theorem dualBilinForm_rho_root (i : ι) : P.dualBilinForm S P.rho (P.root i) = (S.ε i : K)⁻¹ := by
  rw [dualBilinForm_root_right, rho_coroot, one_div]

variable {P} in
/-- `2 (ρ | αᵢ) = (αᵢ | αᵢ)` ([Kac] §2.5). -/
theorem two_mul_dualBilinForm_rho_root (hA : A.IsGeneralizedCartan) (i : ι) :
    2 * P.dualBilinForm S P.rho (P.root i) = P.dualBilinForm S (P.root i) (P.root i) := by
  rw [dualBilinForm_rho_root, dualBilinForm_root_self S hA]
  push_cast
  ring

end Realization

end Matrix

end
