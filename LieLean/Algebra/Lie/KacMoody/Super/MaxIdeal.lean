/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.Auxiliary

/-!
# The maximal ideal of `G̃(A, τ)` meeting `𝔥` trivially

Inside `U = U(G̃(A, τ))`, an ideal of `G̃(A, τ)` is a subspace `I ⊆ G̃` with `[G̃, I] ⊆ I` for the
super commutator (`SuperEnveloping.IsIdeal`). Such an ideal is graded by the weights of `𝔥`
(`le_iSup_inf_weightSpace`), so if it meets `𝔥` trivially it lies in the sum of the nonzero weight
spaces. Hence the sum of all ideals meeting `𝔥` trivially still meets `𝔥` trivially: this is the
unique maximal such ideal `R` ([Kac78] §1.2, cf. [Kac] Thm. 1.2 (e)), and
`G(A, τ) = G̃(A, τ) / R`. It is stable under the parity involution (`parity_mem_maxIdeal`), so it is
a graded ideal.

## Main definitions

* `Matrix.Realization.SuperEnveloping.IsIdeal`: ideals of `G̃(A, τ)`.
* `Matrix.Realization.SuperEnveloping.maxIdeal`: the maximal ideal `R` meeting `𝔥` trivially.

## Main results

* `Matrix.Realization.SuperEnveloping.le_iSup_inf_weightSpace`: `ad 𝔥`-stable subspaces are
  sums of their weight components.
* `Matrix.Realization.SuperEnveloping.isIdeal_maxIdeal`,
  `Matrix.Realization.SuperEnveloping.maxIdeal_inf_range_h`,
  `Matrix.Realization.SuperEnveloping.le_maxIdeal`: `R` is the largest ideal meeting `𝔥`
  trivially.
* `Matrix.Realization.SuperEnveloping.parity_mem_maxIdeal`: `σ(R) ⊆ R`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Thm. 1.2 (e).
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

namespace SuperEnveloping

/-! ### Weight decomposition of `ad 𝔥`-stable subspaces -/

/-- The adjoint action `a ↦ ad (h a)` of `𝔥` on `U`, as a linear map. -/
def adHLin : H →ₗ[K] Module.End K (P.SuperEnveloping p) where
  toFun := adH P p
  map_add' a b := by
    ext u; simp only [adH, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, add_mul, mul_add]; abel
  map_smul' c a := by
    ext u; simp only [adH, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, smul_mul_assoc, mul_smul_comm,
      smul_sub, RingHom.id_apply]

lemma weightSpace_eq_weightSpaceOf (μ : Dual K H) :
    weightSpace P p μ = Module.End.weightSpaceOf (adHLin P p) μ := by
  ext u
  simp only [mem_weightSpace, Module.End.mem_weightSpaceOf, adHLin, adH, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    sub_eq_iff_eq_add']

variable [CharZero K]

/-- A subspace stable under `ad 𝔥` is the sum of its intersections with the weight spaces. -/
lemma le_iSup_inf_weightSpace (N : Submodule K (P.SuperEnveloping p))
    (hN : ∀ a, ∀ x ∈ N, superBracket P p (h P p a) x ∈ N) :
    N ≤ ⨆ μ, N ⊓ weightSpace P p μ := by
  have := Module.End.inf_iSup_weightSpaceOf_le (adHLin P p) N fun a x hx ↦ by
    have := hN a x hx
    rwa [superBracket_of_even_left P p (isEven_h P p a)] at this
  simp only [← weightSpace_eq_weightSpaceOf, iSup_weightSpace, inf_top_eq] at this
  exact this

/-! ### Ideals -/

/-- An ideal of `G̃(A, τ)`: a subspace `I ⊆ G̃` with `[G̃, I] ⊆ I`. -/
structure IsIdeal (I : Submodule K (P.SuperEnveloping p)) : Prop where
  le_gTilde : I ≤ gTilde P p
  superBracket_mem : ∀ x ∈ gTilde P p, ∀ y ∈ I, superBracket P p x y ∈ I

/-- An ideal meeting `𝔥` trivially lies in the sum of the nonzero weight spaces. -/
lemma IsIdeal.le_iSup_ne_zero {I : Submodule K (P.SuperEnveloping p)} (hI : IsIdeal P p I)
    (hI0 : I ⊓ LinearMap.range (h P p) = ⊥) :
    I ≤ ⨆ μ ∈ {μ : Dual K H | μ ≠ 0}, weightSpace P p μ := by
  refine (le_iSup_inf_weightSpace P p I fun a x hx ↦
    hI.superBracket_mem _ (h_mem_gTilde P p a) x hx).trans (iSup_le fun μ ↦ ?_)
  by_cases hμ : μ = 0
  · subst hμ
    have : I ⊓ weightSpace P p 0 ≤ I ⊓ LinearMap.range (h P p) := by
      rw [← gTilde_inf_weightSpace_zero P p]
      exact le_inf inf_le_left (le_inf (inf_le_left.trans hI.le_gTilde) inf_le_right)
    rw [hI0] at this
    exact this.trans bot_le
  · exact inf_le_right.trans (le_biSup (fun μ ↦ weightSpace P p μ) hμ)

/-- The maximal ideal `R` of `G̃(A, τ)` meeting `𝔥` trivially ([Kac78] §1.2). -/
def maxIdeal : Submodule K (P.SuperEnveloping p) :=
  sSup {I | IsIdeal P p I ∧ I ⊓ LinearMap.range (h P p) = ⊥}

omit [CharZero K] in
theorem isIdeal_maxIdeal : IsIdeal P p (maxIdeal P p) where
  le_gTilde := sSup_le fun _ hI ↦ hI.1.le_gTilde
  superBracket_mem x hx := by
    have : maxIdeal P p ≤ (maxIdeal P p).comap (superBracketRight P p x) :=
      sSup_le fun I hI y hy ↦ le_sSup hI (hI.1.superBracket_mem x hx y hy)
    exact fun y hy ↦ this hy

lemma maxIdeal_le_iSup_ne_zero :
    maxIdeal P p ≤ ⨆ μ ∈ {μ : Dual K H | μ ≠ 0}, weightSpace P p μ :=
  sSup_le fun _ hI ↦ hI.1.le_iSup_ne_zero P p hI.2

/-- `R ∩ 𝔥 = 0`. -/
theorem maxIdeal_inf_range_h : maxIdeal P p ⊓ LinearMap.range (h P p) = ⊥ := by
  refine eq_bot_iff.2 fun x ⟨hx, hx0⟩ ↦ ?_
  obtain ⟨a, rfl⟩ := hx0
  exact Submodule.disjoint_def.1 ((iSupIndep_weightSpace P p).disjoint_biSup
    (y := {μ : Dual K H | μ ≠ 0}) (x := 0) (by simp)) _ (h_mem_weightSpace P p a)
    (maxIdeal_le_iSup_ne_zero P p hx)

omit [CharZero K] in
/-- `R` is the largest ideal meeting `𝔥` trivially ([Kac78] §1.2, cf. [Kac] Thm. 1.2 (e)). -/
theorem le_maxIdeal {I : Submodule K (P.SuperEnveloping p)} (hI : IsIdeal P p I)
    (hI0 : I ⊓ LinearMap.range (h P p) = ⊥) : I ≤ maxIdeal P p :=
  le_sSup ⟨hI, hI0⟩

/-! ### Stability under the parity involution -/

omit [CharZero K] in
lemma parity_superBracket (x y : P.SuperEnveloping p) :
    parity P p (superBracket P p x y) = superBracket P p (parity P p x) (parity P p y) := by
  simp only [superBracket, map_sub, map_mul, map_smul, map_add, parity_parity]

omit [CharZero K] in
lemma IsHomog.parity_eq {c : ZMod 2} {x : P.SuperEnveloping p} (hx : IsHomog P p c x) :
    parity P p x = zSign K c • x := hx

lemma parity_mem_gTilde {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) :
    parity P p x ∈ gTilde P p := by
  have h1 : nPlus P p ≤ (gTilde P p).comap (parity P p).toLinearMap :=
    (nPlus_le_iff P p).2 fun i w ↦ by
      simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, (isHomog_eLie P p i w).parity_eq]
      exact Submodule.smul_mem _ _ (nPlus_le_gTilde P p (eLie_mem_nPlus P p i w))
  have h2 : nMinus P p ≤ (gTilde P p).comap (parity P p).toLinearMap :=
    Submodule.map_le_iff_le_comap.2 ((nPlus_le_iff P p).2 fun i w ↦ by
      simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply,
        (isHomog_eLie P p i w).omega.parity_eq]
      exact Submodule.smul_mem _ _
        (nMinus_le_gTilde P p (omega_mem_nMinus P p (eLie_mem_nPlus P p i w))))
  have h3 : LinearMap.range (h P p) ≤ (gTilde P p).comap (parity P p).toLinearMap := by
    rintro _ ⟨a, rfl⟩
    simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, (isHomog_h P p a).parity_eq,
      zSign_zero, one_smul]
    exact h_mem_gTilde P p a
  exact (sup_le (sup_le h2 h3) h1 : gTilde P p ≤ _) hx

/-- `σ(R) ⊆ R`: the maximal ideal is graded. -/
theorem parity_mem_maxIdeal {x : P.SuperEnveloping p} (hx : x ∈ maxIdeal P p) :
    parity P p x ∈ maxIdeal P p := by
  let I := (maxIdeal P p).map (parity P p).toLinearMap
  have hI : IsIdeal P p I := by
    refine ⟨Submodule.map_le_iff_le_comap.2 fun y hy ↦
      parity_mem_gTilde P p ((isIdeal_maxIdeal P p).le_gTilde hy), ?_⟩
    rintro y hy _ ⟨z, hz, rfl⟩
    refine ⟨superBracket P p (parity P p y) z,
      (isIdeal_maxIdeal P p).superBracket_mem _ (parity_mem_gTilde P p hy) z hz, ?_⟩
    simp only [AlgHom.toLinearMap_apply, parity_superBracket, parity_parity]
  have hI0 : I ⊓ LinearMap.range (h P p) = ⊥ := by
    refine eq_bot_iff.2 fun y ⟨⟨z, hz, hzy⟩, a, ha⟩ ↦ ?_
    have hz' : z = h P p a := by
      have := congrArg (parity P p) hzy
      simp only [AlgHom.toLinearMap_apply, parity_parity] at this
      rw [this, ← ha, (isHomog_h P p a).parity_eq, zSign_zero, one_smul]
    have : z ∈ maxIdeal P p ⊓ LinearMap.range (h P p) := ⟨hz, a, hz'.symm⟩
    rw [maxIdeal_inf_range_h] at this
    rw [Submodule.mem_bot] at this ⊢
    rw [← hzy, this, map_zero]
  exact le_maxIdeal P p hI hI0 ⟨x, hx, rfl⟩

end SuperEnveloping

end Matrix.Realization
