/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generalized Cartan matrices and their realizations

## Main definitions

* `Matrix.IsGeneralizedCartan`: a generalized Cartan matrix (GCM), [Kac] §1.1.
* `Matrix.IsSymmetrizable`: a matrix `A` is symmetrizable if `D A` is symmetric for some diagonal
  matrix `D` with positive entries.
* `Matrix.Realization`: a realization `(𝔥, Π, Π^∨)` of a square integer matrix `A` over a field,
  [Kac] §1.1.
* `Matrix.Realization.std`: the standard realization.
* `Matrix.Realization.rootOf`: the embedding of the root lattice `Q = ℤ^ι` in `𝔥*`.

## Main results

* `Matrix.IsFiniteCartan.isGeneralizedCartan`: a finite-type Cartan matrix is a GCM.
* `Matrix.isSymmetrizable_iff_exists_eq_diagonal_mul`: symmetrizability in Kac's form `A = D B`
  with `D` diagonal positive rational and `B` symmetric.
* `Matrix.Realization.exists_linearEquiv`: realizations are unique up to isomorphism ([Kac]
  Prop. 1.1).

## Conventions

We follow [Kac]: a realization of `A = (aᵢⱼ)` consists of a vector space `𝔥`, linearly independent
`αᵢ^∨ ∈ 𝔥` (the simple coroots) and `αᵢ ∈ 𝔥*` (the simple roots) with `⟨αⱼ, αᵢ^∨⟩ = aᵢⱼ` and
`dim 𝔥 = 2n - rank A`. Note that Mathlib's `CartanMatrix.Realisation` (for finite-type Cartan
matrices and perfect pairings) uses the transposed convention `⟨αᵢ, αⱼ^∨⟩ = Aᵢⱼ`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.1, §2.1,
  §2.3 (stated over `ℂ`).
-/

open Module

namespace Matrix

variable {ι : Type*}

/-- A generalized Cartan matrix ([Kac] §1.1): an integer matrix with `aᵢᵢ = 2`, `aᵢⱼ ≤ 0` for
`i ≠ j`, and `aᵢⱼ = 0 ↔ aⱼᵢ = 0`. -/
structure IsGeneralizedCartan (A : Matrix ι ι ℤ) : Prop where
  diag : ∀ i, A i i = 2
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  zero_comm : ∀ i j, A i j = 0 ↔ A j i = 0

namespace IsGeneralizedCartan

variable {A : Matrix ι ι ℤ}

lemma transpose (hA : A.IsGeneralizedCartan) : Aᵀ.IsGeneralizedCartan where
  diag i := by simpa using hA.diag i
  offDiag_nonpos i j hij := by simpa using hA.offDiag_nonpos j i hij.symm
  zero_comm i j := by simpa using hA.zero_comm j i

lemma toNat_neg_eq (hA : A.IsGeneralizedCartan) {i j : ι} (hij : i ≠ j) :
    ((-A i j).toNat : ℤ) = -A i j := by
  have := hA.offDiag_nonpos i j hij
  omega

end IsGeneralizedCartan

lemma IsFiniteCartan.isGeneralizedCartan [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}
    (hA : A.IsFiniteCartan) : A.IsGeneralizedCartan where
  diag := hA.diag
  offDiag_nonpos := hA.offDiag_nonpos
  zero_comm := hA.zero_comm

variable [Fintype ι] [DecidableEq ι]

/-- A square integer matrix `A` is symmetrizable if there are positive integers `dᵢ` such that
`diagonal d * A` is symmetric. See `Matrix.isSymmetrizable_iff_exists_eq_diagonal_mul` for the
equivalent form `A = D B` of [Kac] (2.3.1). [Kac] §2.1 allows any invertible complex diagonal
`D`; for generalized Cartan matrices the two notions agree ([Kac] §2.3). -/
def IsSymmetrizable (A : Matrix ι ι ℤ) : Prop :=
  ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ (diagonal d * A).IsSymm

lemma IsFiniteCartan.isSymmetrizable {A : Matrix ι ι ℤ} (hA : A.IsFiniteCartan) :
    A.IsSymmetrizable := by
  obtain ⟨d, hd, hdA⟩ := hA.exists_posDef
  exact ⟨d, hd, hdA.isHermitian⟩

lemma IsSymmetrizable.of_isSymm {A : Matrix ι ι ℤ} (hA : A.IsSymm) : A.IsSymmetrizable :=
  ⟨1, fun _ ↦ one_pos, by simpa [← Pi.one_def] using hA⟩

lemma isSymmetrizable_iff_mul_eq_mul {A : Matrix ι ι ℤ} :
    A.IsSymmetrizable ↔ ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ ∀ i j, d i * A i j = d j * A j i := by
  refine exists_congr fun d ↦ and_congr_right fun _ ↦ ?_
  rw [IsSymm, ← Matrix.ext_iff]
  simp only [transpose_apply, diagonal_mul]
  exact ⟨fun h i j ↦ (h j i), fun h i j ↦ h j i⟩

/-- Symmetrizability in the form of [Kac] (2.3.1): `A = D B` with `D` a diagonal matrix with
positive (rational) entries and `B` a symmetric rational matrix. -/
theorem isSymmetrizable_iff_exists_eq_diagonal_mul {A : Matrix ι ι ℤ} :
    A.IsSymmetrizable ↔ ∃ (ε : ι → ℚ) (B : Matrix ι ι ℚ), (∀ i, 0 < ε i) ∧ B.IsSymm ∧
      A.map (Int.cast : ℤ → ℚ) = diagonal ε * B := by
  rw [isSymmetrizable_iff_mul_eq_mul]
  constructor
  · rintro ⟨d, hd, hdA⟩
    refine ⟨fun i ↦ (d i : ℚ)⁻¹, of fun i j ↦ d i * A i j, fun i ↦ by simpa using hd i, ?_, ?_⟩
    · ext i j; simp only [transpose_apply, of_apply]; exact_mod_cast hdA j i
    · ext i j
      have : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
      simp [diagonal_mul, this]
  · rintro ⟨ε, B, hε, hB, hAB⟩
    -- clear denominators of `ε⁻¹`
    let N : ℕ := ∏ i, (ε i)⁻¹.den
    have hN : ∀ i, ∃ m : ℤ, (N : ℚ) * (ε i)⁻¹ = m := by
      intro i
      refine ⟨((N / (ε i)⁻¹.den : ℕ) : ℤ) * (ε i)⁻¹.num, ?_⟩
      have hdvd : (ε i)⁻¹.den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have h1 : ((N / (ε i)⁻¹.den : ℕ) : ℚ) * (ε i)⁻¹.den = N := by
        exact_mod_cast Nat.div_mul_cancel hdvd
      rw [Int.cast_mul, Int.cast_natCast, ← Rat.mul_den_eq_num, ← h1]
      ring
    choose d hd using hN
    have hNpos : (0 : ℚ) < N := by
      have : 0 < N := Finset.prod_pos fun i _ ↦ Rat.den_pos _
      exact_mod_cast this
    refine ⟨d, fun i ↦ ?_, fun i j ↦ ?_⟩
    · have : (0 : ℚ) < d i := by rw [← hd]; exact mul_pos hNpos (inv_pos.mpr (hε i))
      exact_mod_cast this
    · have hA : ∀ i j, (A i j : ℚ) = ε i * B i j := fun i j ↦ by
        simpa [diagonal_mul] using congr_fun₂ hAB i j
      have : (d i : ℚ) * A i j = d j * A j i := by
        rw [← hd, ← hd, hA, hA, hB.apply j i]
        field_simp [(hε i).ne', (hε j).ne']
      exact_mod_cast this

/-! ### Realizations -/

end Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- A realization of a square integer matrix `A` over a field `K` ([Kac] §1.1): a `K`-vector space
`H` (Kac's `𝔥`) with linearly independent simple coroots `αᵢ^∨ ∈ H` and simple roots `αᵢ ∈ H*`
such that `⟨αⱼ, αᵢ^∨⟩ = aᵢⱼ` and `dim H = 2 |ι| - rank A`. The dimension condition is only
meaningful for finite-dimensional `H`, which is assumed in the results below. -/
structure Realization (A : Matrix ι ι ℤ) (K H : Type*) [Field K] [AddCommGroup H]
    [Module K H] where
  /-- The simple coroots `αᵢ^∨`. -/
  coroot : ι → H
  /-- The simple roots `αᵢ`. -/
  root : ι → Dual K H
  linearIndependent_coroot : LinearIndependent K coroot
  linearIndependent_root : LinearIndependent K root
  root_coroot : ∀ i j, root j (coroot i) = A i j
  finrank_add_rank : finrank K H + (A.map (Int.cast : ℤ → K)).rank = 2 * Fintype.card ι

namespace Realization

variable {A : Matrix ι ι ℤ} {K H H' : Type*} [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup H'] [Module K H']

/-- The linear map `c ↦ ∑ cᵢ αᵢ^∨`. -/
def corootMap (P : Realization A K H) : (ι → K) →ₗ[K] H :=
  Fintype.linearCombination K P.coroot

/-- The linear map `h ↦ (⟨αⱼ, h⟩)ⱼ`. -/
def rootMap (P : Realization A K H) : H →ₗ[K] ι → K :=
  LinearMap.pi P.root

@[simp] lemma rootMap_apply (P : Realization A K H) (h : H) (j : ι) :
    P.rootMap h j = P.root j h := rfl

lemma rootMap_corootMap (P : Realization A K H) (c : ι → K) :
    P.rootMap (P.corootMap c) = c ᵥ* A.map (Int.cast : ℤ → K) := by
  ext j
  simp [corootMap, Fintype.linearCombination_apply, vecMul, dotProduct, root_coroot]

lemma corootMap_injective (P : Realization A K H) : Function.Injective P.corootMap :=
  P.linearIndependent_coroot.fintypeLinearCombination_injective

lemma rootMap_surjective [FiniteDimensional K H] (P : Realization A K H) :
    Function.Surjective P.rootMap := by
  classical
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  let c : ι → K := fun i ↦ φ fun j ↦ if i = j then 1 else 0
  have h : ∑ j, c j • P.root j = 0 := by
    ext h
    have := LinearMap.congr_fun hφ h
    simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
    rw [LinearMap.zero_apply, ← this, LinearMap.pi_apply_eq_sum_univ φ (P.rootMap h)]
    simp [c, LinearMap.sum_apply, mul_comm]
  have h' := Fintype.linearIndependent_iff.mp P.linearIndependent_root c h
  refine LinearMap.ext fun v ↦ ?_
  rw [LinearMap.pi_apply_eq_sum_univ φ v]
  simp [show ∀ i, (φ fun j ↦ if i = j then 1 else 0) = 0 from h']

lemma finrank_ker_rootMap [FiniteDimensional K H] (P : Realization A K H) :
    finrank K (LinearMap.ker P.rootMap) + Fintype.card ι = finrank K H := by
  have := LinearMap.finrank_range_add_finrank_ker P.rootMap
  rw [LinearMap.range_eq_top.mpr P.rootMap_surjective, finrank_top, finrank_fintype_fun_eq_card]
    at this
  omega

/-- The common kernel of the simple roots is contained in the span of the simple coroots. -/
lemma ker_rootMap_le [FiniteDimensional K H] (P : Realization A K H) :
    LinearMap.ker P.rootMap ≤ LinearMap.range P.corootMap := by
  set AK := A.map (Int.cast : ℤ → K)
  set N := LinearMap.ker (P.rootMap ∘ₗ P.corootMap)
  have hN : N = LinearMap.ker AKᵀ.mulVecLin := by
    ext c
    simp only [N, LinearMap.mem_ker, LinearMap.comp_apply, rootMap_corootMap, mulVecLin_apply,
      mulVec_transpose, AK]
  have hfinN : finrank K N + AK.rank = Fintype.card ι := by
    have := LinearMap.finrank_range_add_finrank_ker AKᵀ.mulVecLin
    rw [finrank_fintype_fun_eq_card, ← hN] at this
    rw [← rank_transpose AK, rank]
    omega
  have hle : N.map P.corootMap ≤ LinearMap.ker P.rootMap := by
    rintro _ ⟨c, hc, rfl⟩
    simpa [N] using hc
  have heq : N.map P.corootMap = LinearMap.ker P.rootMap := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [← (Submodule.equivMapOfInjective _ P.corootMap_injective N).finrank_eq]
    have := P.finrank_ker_rootMap
    have : finrank K H + AK.rank = 2 * Fintype.card ι := P.finrank_add_rank
    omega
  rw [← heq]
  exact LinearMap.map_le_range

/-- Uniqueness of realizations ([Kac] Prop. 1.1): any two realizations of `A` are isomorphic. -/
theorem exists_linearEquiv [FiniteDimensional K H] [FiniteDimensional K H']
    (P : Realization A K H) (Q : Realization A K H') :
    ∃ e : H ≃ₗ[K] H', (∀ i, e (P.coroot i) = Q.coroot i) ∧ ∀ i h, Q.root i (e h) = P.root i h := by
  classical
  obtain ⟨π, hπ⟩ := P.corootMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr P.corootMap_injective)
  obtain ⟨σ, hσ⟩ := Q.rootMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr Q.rootMap_surjective)
  let φ : H →ₗ[K] H' :=
    Q.corootMap ∘ₗ π + σ ∘ₗ P.rootMap ∘ₗ (LinearMap.id - P.corootMap ∘ₗ π)
  have hQP : ∀ c, Q.rootMap (Q.corootMap c) = P.rootMap (P.corootMap c) := by
    intro c; rw [rootMap_corootMap, rootMap_corootMap]
  have hσ' : ∀ v, Q.rootMap (σ v) = v := fun v ↦ LinearMap.congr_fun hσ v
  have hφroot : ∀ h, Q.rootMap (φ h) = P.rootMap h := by
    intro h
    simp only [φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_add, hσ', hQP, map_sub]
    abel
  have hπc : ∀ c, π (P.corootMap c) = c := fun c ↦ LinearMap.congr_fun hπ c
  have hφcoroot : ∀ c, φ (P.corootMap c) = Q.corootMap c := by
    intro c
    simp [φ, hπc]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    have hker : h ∈ LinearMap.ker P.rootMap := by
      rw [LinearMap.mem_ker, ← hφroot, hh, map_zero]
    obtain ⟨c, rfl⟩ := P.ker_rootMap_le hker
    rw [hφcoroot] at hh
    rw [Q.corootMap_injective (hh.trans (map_zero _).symm), map_zero]
  have hdim : finrank K H = finrank K H' := by
    have := P.finrank_add_rank; have := Q.finrank_add_rank; omega
  refine ⟨LinearMap.linearEquivOfInjective φ hinj hdim, fun i ↦ ?_, fun i h ↦ ?_⟩
  · have := hφcoroot (Pi.single i 1)
    simpa [corootMap, Fintype.linearCombination_apply, Pi.single_apply] using this
  · exact congr_fun (hφroot h) i

/-! ### The root lattice -/

/-- The element `∑ kᵢ αᵢ ∈ 𝔥*` of the root lattice `Q = ⊕ ℤ αᵢ` attached to `k : ι → ℤ`. We
identify `Q` with `ι → ℤ`; the positive cone `Q₊` is `{k | 0 ≤ k}` and the height of `k` is
`∑ kᵢ`. -/
def rootOf (P : Realization A K H) : (ι → ℤ) →+ Dual K H where
  toFun k := ∑ i, (k i : K) • P.root i
  map_zero' := by simp
  map_add' k l := by simp [add_smul, Finset.sum_add_distrib]

lemma rootOf_apply (P : Realization A K H) (k : ι → ℤ) :
    P.rootOf k = ∑ i, (k i : K) • P.root i := rfl

@[simp] lemma rootOf_single [DecidableEq ι] (P : Realization A K H) (i : ι) :
    P.rootOf (Pi.single i 1) = P.root i := by
  simp [rootOf_apply, Pi.single_apply]

/-- `⟨∑ kₗ αₗ, αⱼ^∨⟩ = ∑ₗ aⱼₗ kₗ`. -/
lemma rootOf_apply_coroot (P : Realization A K H) (k : ι → ℤ) (j : ι) :
    P.rootOf k (P.coroot j) = ((A *ᵥ k) j : ℤ) := by
  simp [rootOf_apply, P.root_coroot, mulVec, dotProduct, mul_comm]

/-- In characteristic zero, the root lattice embeds in `𝔥*`. -/
lemma rootOf_injective [CharZero K] (P : Realization A K H) : Function.Injective P.rootOf := by
  rw [injective_iff_map_eq_zero]
  intro k hk
  have := Fintype.linearIndependent_iff.mp P.linearIndependent_root (fun i ↦ (k i : K)) hk
  ext i
  exact_mod_cast this i

lemma rootOf_ne_zero [CharZero K] (P : Realization A K H) {k : ι → ℤ} (hk : k ≠ 0) :
    P.rootOf k ≠ 0 := by
  rwa [Ne, ← map_zero P.rootOf, P.rootOf_injective.eq_iff]

/-- The height `∑ kᵢ` of an element `k` of the root lattice. -/
def height (k : ι → ℤ) : ℤ := ∑ i, k i

/-! ### The standard realization -/

variable (A K)

/-- The kernel of `A`, acting on column vectors. -/
abbrev stdKer : Submodule K (ι → K) := LinearMap.ker (A.map (Int.cast : ℤ → K)).mulVecLin

/-- The underlying space `Kⁿ × (ker A)*` of the standard realization. -/
abbrev StdSpace : Type _ := (ι → K) × Dual K (stdKer A K)

/-- A projection of `Kⁿ` onto `ker A`, used to define the standard realization. -/
noncomputable def stdProj : (ι → K) →ₗ[K] stdKer A K :=
  ((stdKer A K).subtype.exists_leftInverse_of_injective (stdKer A K).ker_subtype).choose

lemma stdProj_subtype (c : stdKer A K) : stdProj A K c = c :=
  LinearMap.congr_fun
    ((stdKer A K).subtype.exists_leftInverse_of_injective (stdKer A K).ker_subtype).choose_spec c

/-- The simple roots of the standard realization: `αⱼ (v, f) = (v A)ⱼ + f (p eⱼ)`. -/
noncomputable def stdRoot [DecidableEq ι] (j : ι) : Dual K (StdSpace A K) :=
  (LinearMap.proj j ∘ₗ (A.map (Int.cast : ℤ → K)).vecMulLinear) ∘ₗ LinearMap.fst K _ _ +
    Dual.eval K _ (stdProj A K (Pi.single j 1)) ∘ₗ LinearMap.snd K _ _

lemma stdRoot_apply [DecidableEq ι] (j : ι) (v : ι → K) (f : Dual K (stdKer A K)) :
    stdRoot A K j (v, f) = (v ᵥ* A.map (Int.cast : ℤ → K)) j + f (stdProj A K (Pi.single j 1)) :=
  rfl

lemma linearIndependent_stdRoot [DecidableEq ι] : LinearIndependent K (stdRoot A K) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- evaluating on `(v, 0)` shows `c ∈ ker A`
  have h1 : A.map (Int.cast : ℤ → K) *ᵥ c = 0 := by
    ext i
    have := LinearMap.congr_fun hc (Pi.single i 1, 0)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, stdRoot_apply, LinearMap.zero_apply,
      add_zero, smul_eq_mul, single_vecMul, one_smul] at this
    simpa [mulVec, dotProduct, mul_comm] using this
  -- evaluating on `(0, f)` shows `c = 0`
  have h2 : ∀ f : Dual K (stdKer A K), f ⟨c, h1⟩ = 0 := by
    intro f
    have := LinearMap.congr_fun hc (0, f)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, stdRoot_apply, LinearMap.zero_apply,
      zero_vecMul, Pi.zero_apply, zero_add, smul_eq_mul] at this
    have hc' : c = ∑ j, c j • Pi.single j 1 := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    calc f ⟨c, h1⟩ = f (stdProj A K c) := by rw [← stdProj_subtype A K ⟨c, h1⟩]
      _ = ∑ j, c j * f (stdProj A K (Pi.single j 1)) := by
        conv_lhs => rw [hc']
        simp [map_sum]
      _ = 0 := this
  have := (forall_dual_apply_eq_zero_iff K (⟨c, h1⟩ : stdKer A K)).mp h2
  intro i
  exact congr_fun (congr_arg Subtype.val this) i

/-- The standard realization of `A` on `Kⁿ × (ker A)*` (cf. [Kac] proof of Prop. 1.1, in
coordinate-free form, with roots and coroots exchanged):
`αᵢ^∨ = (eᵢ, 0)` and `αⱼ (v, f) = (v A)ⱼ + f (p eⱼ)`, where `p` is a
projection of `Kⁿ` onto `ker A`. -/
noncomputable def std [DecidableEq ι] : Realization A K (StdSpace A K) where
  coroot i := (Pi.single i 1, 0)
  root := stdRoot A K
  linearIndependent_coroot := by
    have := (Pi.linearIndependent_single_one ι K).map'
      (LinearMap.inl K (ι → K) (Dual K (stdKer A K)))
      (LinearMap.ker_eq_bot.mpr (LinearMap.inl_injective))
    convert this using 1
    funext i
    simp
  linearIndependent_root := linearIndependent_stdRoot A K
  root_coroot i j := by simp [stdRoot_apply]
  finrank_add_rank := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A.map (Int.cast : ℤ → K)).mulVecLin
    rw [finrank_fintype_fun_eq_card] at h1
    have h2 : finrank K (StdSpace A K) = Fintype.card ι +
        finrank K (LinearMap.ker (A.map (Int.cast : ℤ → K)).mulVecLin) := by
      rw [Module.finrank_prod, Subspace.dual_finrank_eq, finrank_fintype_fun_eq_card]
    have h3 : (A.map (Int.cast : ℤ → K)).rank =
      finrank K (LinearMap.range (A.map (Int.cast : ℤ → K)).mulVecLin) := rfl
    omega

/-- Existence of realizations ([Kac] Prop. 1.1). -/
theorem nonempty_realization : Nonempty (Realization A K (StdSpace A K)) := by
  classical exact ⟨std A K⟩

end Realization

end Matrix
