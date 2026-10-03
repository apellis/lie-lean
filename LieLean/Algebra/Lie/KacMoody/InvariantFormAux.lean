/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.InvariantForm
import LieLean.Algebra.Lie.KacMoody.RootSpaceDim
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# The invariant bilinear form on the auxiliary Lie algebra `𝔤̃(A)`

Let `A` be a symmetrizable matrix with symmetrization `A = diag(ε) B`, `(𝔥, Π, Π^∨)` a
realization of `A` over a field `K` of characteristic zero, and `(·|·)` the bilinear form on `𝔥`
of [Kac] §2.1 (`Matrix.Realization.bilinForm`), with the induced isomorphism `ν : 𝔥 ≃ 𝔥*`.
We construct a symmetric invariant bilinear form on the auxiliary Lie algebra `𝔤̃(A)` extending
the form on `𝔥` and show that its radical is the maximal ideal `𝔯`, so that it descends to a
nondegenerate form on `𝔤(A) = 𝔤̃(A)/𝔯` ([Kac] Thm. 2.2); see
`LieLean/Algebra/Lie/KacMoody/InvariantForm.lean` for the latter.

## The construction

Kac constructs the form on `𝔤(A)` degree by degree for the principal gradation, defining
`(x | Σ [uᵢ, vᵢ]) = Σ ([x, uᵢ] | vᵢ)` and proving that this is well defined. We reorganise this
argument so that no well-definedness needs to be checked: the form is written down directly and
the content of the proof becomes the identity ([Kac] Thm. 2.2 e))
`(C_μ)`: `[x, y] = (x | y) ν⁻¹(μ)` for `x ∈ 𝔤̃_μ`, `y ∈ 𝔤̃_{-μ}`,
which is proved by induction on the height, the inductive step being Kac's well-definedness
computation. This reorganisation was reconstructed by us, not taken from the book.

Fix `ρ^∨ ∈ 𝔥` with `⟨αᵢ, ρ^∨⟩ = 1` for all `i` (`Matrix.Realization.rhoCheck`), so that
`⟨μ, ρ^∨⟩ = ± ht μ ≠ 0` for every nonzero weight `μ` of `𝔤̃(A)`. Let `π₀ : 𝔤̃ → 𝔥` be the
projection of the triangular decomposition `𝔤̃ = 𝔫̃₋ ⊕ 𝔥 ⊕ 𝔫̃₊` and `D : 𝔤̃ → 𝔤̃` the operator
which is multiplication by `⟨μ, ρ^∨⟩⁻¹` on `𝔤̃_μ` for `μ ≠ 0` and zero on `𝔥`. Put
`(x | y) = (π₀ x | π₀ y) + (π₀ [D x, y] | ρ^∨)`.
Then `(𝔤̃_μ | 𝔤̃_ν) = 0` unless `μ + ν = 0`, the form restricts to the given form on `𝔥`, and
`(x | y) = ⟨μ, ρ^∨⟩⁻¹ (π₀ [x, y] | ρ^∨)` for `x ∈ 𝔤̃_μ`, `μ ≠ 0`; hence the form is symmetric.
If `[x, y] = c ν⁻¹(μ)` for some scalar `c` then `c = (x | y)`, by pairing with `ρ^∨`.

*Lemma 1.* Let `x ∈ 𝔤̃_α`, `y ∈ 𝔤̃_β`, `z ∈ 𝔤̃_γ` with `α + β + γ = 0` and assume `C_α, C_β, C_γ`.
If one of `α, β, γ` is zero, or `α` and `β` are linearly independent, then
`(x | [y, z]) = (y | [z, x]) = (z | [x, y])`. Indeed, in the independent case the Jacobi
identity and `C` give `(x|[y,z]) ν⁻¹α + (y|[z,x]) ν⁻¹β + (z|[x,y]) ν⁻¹γ = 0` with
`γ = -α - β`; if `α = 0` then `x ∈ 𝔥` and all three terms equal `⟨β, x⟩ (y | z)`.

*Lemma 2.* If moreover `β = ±αₖ` and `x, z ≠ 0`, the hypothesis of Lemma 1 holds: otherwise
`α` and `γ` would be nonzero multiples of `αₖ`, which is impossible as `𝔤̃_{mαₖ} = 0` for
`|m| ≥ 2`.

*Proof of `C_μ`.* `C_0` is trivial and `C_{-μ}` follows from `C_μ` by symmetry. For `μ = αᵢ`,
`[eᵢ, fᵢ] = αᵢ^∨ = εᵢ ν⁻¹(αᵢ)`. Let `μ > 0` have height `≥ 2` and assume `C` for all weights of
smaller absolute height. Then `𝔤̃_μ` is spanned by elements `[eⱼ, x']`, `x' ∈ 𝔤̃_λ`,
`λ = μ - αⱼ`, and `𝔤̃_{-μ}` by elements `w = [fᵢ, y']`, `y' ∈ 𝔤̃_{-κ}`, `κ = μ - αᵢ`. By `C_{αⱼ}`
and `C_λ`, `[[eⱼ, x'], w] = [eⱼ, [x', w]] - [x', [eⱼ, w]] = (eⱼ|[x',w]) ν⁻¹αⱼ -
(x'|[eⱼ,w]) ν⁻¹λ`, so it suffices to show `(eⱼ | [x', w]) = -(x' | [eⱼ, w])`. Using the Jacobi
identity and Lemmas 1, 2 (at heights `< ht μ`):
`(x' | [eⱼ, w]) = δᵢⱼ (x' | [αᵢ^∨, y']) + (x' | [fᵢ, [eⱼ, y']])
  = -δᵢⱼ ⟨λ, αᵢ^∨⟩ (x' | y') + ([x', fᵢ] | [eⱼ, y'])` and
`(eⱼ | [x', w]) = (eⱼ | [[x', fᵢ], y']) + (eⱼ | [fᵢ, [x', y']])
  = -([x', fᵢ] | [eⱼ, y']) + δᵢⱼ ⟨λ, αᵢ^∨⟩ (x' | y')`,
where for `i ≠ j` we used `[x', y'] ∈ 𝔤̃_{αᵢ - αⱼ} = 0`, and for `i = j` we used
`[x', y'] = (x'|y') ν⁻¹λ` (by `C_λ`), `(eᵢ | fᵢ) = εᵢ` and `εᵢ ⟨αᵢ, ν⁻¹λ⟩ = ⟨λ, αᵢ^∨⟩`.

*Invariance.* The set of `y` with `([x, y] | z) = (x | [y, z])` for all `x, z` is a Lie
subalgebra; by Lemmas 1 and 2 (and `C_μ` for all `μ`) it contains the generators `eᵢ, fᵢ, 𝔥`.

*Radical.* The radical of an invariant form is an ideal; it meets `𝔥` trivially since the form
is nondegenerate on `𝔥`, so it lies in `𝔯`. Conversely if `r ∈ 𝔯 ∩ 𝔤̃_μ` and `y ∈ 𝔤̃_{-μ}` then
`(r | y) ν⁻¹(μ) = [r, y] ∈ 𝔯 ∩ 𝔥 = 0`, so `(r | y) = 0`.

## Main definitions

* `Matrix.Realization.AuxLieAlgebra.hComp`: the projection `π₀ : 𝔤̃(A) → 𝔥`.
* `Matrix.Realization.AuxLieAlgebra.degInv`: the operator `D`.
* `Matrix.Realization.AuxLieAlgebra.invFormAux`: the invariant form on `𝔤̃(A)`.

## Main results

* `Matrix.Realization.AuxLieAlgebra.isSymm_invFormAux`: the form is symmetric.
* `Matrix.Realization.AuxLieAlgebra.invFormAux_h_h`: it restricts to the form on `𝔥`.
* `Matrix.Realization.AuxLieAlgebra.invFormAux_eq_zero`: `(𝔤̃_μ | 𝔤̃_ν) = 0` unless `μ + ν = 0`.
* `Matrix.Realization.AuxLieAlgebra.lie_eq_invFormAux_smul`: `[x, y] = (x | y) ν⁻¹(μ)` for
  `x ∈ 𝔤̃_μ`, `y ∈ 𝔤̃_{-μ}` ([Kac] Thm. 2.2 e), for `𝔤̃(A)`).
* `Matrix.Realization.AuxLieAlgebra.lieInvariant_invFormAux`: the form is invariant.
* `Matrix.Realization.AuxLieAlgebra.invFormAux_eq_zero_iff_mem_maxIdeal`: its radical is the
  maximal ideal `𝔯`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.2.
-/

open Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

namespace AuxLieAlgebra

/-! ### Complements on the root space decomposition -/

omit [CharZero K] in
lemma mem_iSup_rootSpace (x : P.AuxLieAlgebra) : x ∈ ⨆ μ, rootSpace P μ := by
  have hx : x ∈ ⨆ μ ∈ allWeights P, rootSpace P μ := by
    rw [iSup_rootSpace_eq_top]; trivial
  exact (iSup₂_le fun μ _ ↦ le_iSup (fun μ ↦ rootSpace P μ) μ) hx

omit [CharZero K] in
/-- Induction principle along the root space decomposition of `𝔤̃(A)`. -/
@[elab_as_elim]
lemma induction_on_rootSpace {p : P.AuxLieAlgebra → Prop} (x : P.AuxLieAlgebra)
    (mem : ∀ μ, ∀ x ∈ rootSpace P μ, p x) (add : ∀ x y, p x → p y → p (x + y)) : p x :=
  Submodule.iSup_induction (fun μ ↦ rootSpace P μ) (motive := p) (mem_iSup_rootSpace P x) mem
    (mem 0 0 (Submodule.zero_mem _)) add

omit [CharZero K] in
/-- `𝔤̃_μ = 0` unless `μ ∈ -(Q₊ \ 0) ∪ {0} ∪ (Q₊ \ 0)`. -/
lemma rootSpace_eq_bot {μ : Dual K H} (hμ : μ ∉ allWeights P) : rootSpace P μ = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  have hx' : x ∈ ⨆ ν, ⨆ (_ : ν ∈ allWeights P), rootSpace P ν := by
    have : x ∈ ⨆ ν ∈ allWeights P, rootSpace P ν := by rw [iSup_rootSpace_eq_top]; trivial
    exact this
  have := mem_of_mem_iSup_of_le (h P) (fun ν ↦ ⨆ (_ : ν ∈ allWeights P), rootSpace P ν)
    (fun ν ↦ iSup_le fun _ ↦ le_rfl) hx hx'
  simpa [hμ] using this

omit [DecidableEq ι] [CharZero K] in
lemma mem_negWeights_iff {μ : Dual K H} : μ ∈ P.negWeights ↔ -μ ∈ P.posWeights := by
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, by simp⟩
  · rintro ⟨k, hk, hμ⟩
    exact ⟨k, hk, show -P.rootOf k = μ by rw [hμ, neg_neg]⟩

section FiniteDimensional

variable [FiniteDimensional K H]

omit [DecidableEq ι] [CharZero K] in
/-- A weight `μ ∈ Q₊ \ {0}` has positive height `⟨μ, ρ^∨⟩`. -/
lemma exists_nat_of_mem_posWeights {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    ∃ n : ℕ, 0 < n ∧ μ P.rhoCheck = n := by
  obtain ⟨k, ⟨hk0, hk⟩, rfl⟩ := hμ
  have hpos : 0 < height k := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    exact Finset.sum_pos' (fun j _ ↦ hk0 j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hk0 i)
      (Ne.symm hi)⟩
  refine ⟨(height k).toNat, by omega, ?_⟩
  rw [rootOf_rhoCheck, ← Int.cast_natCast, Int.toNat_of_nonneg hpos.le]

omit [DecidableEq ι] in
lemma apply_rhoCheck_ne_zero {μ : Dual K H} (hμ : μ ∈ allWeights P) (hμ0 : μ ≠ 0) :
    μ P.rhoCheck ≠ 0 := by
  rcases hμ with (hμ | hμ) | hμ
  · obtain ⟨n, hn, hμn⟩ := exists_nat_of_mem_posWeights P ((mem_negWeights_iff P).mp hμ)
    rw [LinearMap.neg_apply, neg_eq_iff_eq_neg] at hμn
    rw [hμn, neg_ne_zero]
    exact_mod_cast hn.ne'
  · exact absurd hμ hμ0
  · obtain ⟨n, hn, hμn⟩ := exists_nat_of_mem_posWeights P hμ
    rw [hμn]
    exact_mod_cast hn.ne'

lemma apply_rhoCheck_ne_zero_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.AuxLieAlgebra}
    (hx : x ∈ rootSpace P μ) (hx0 : x ≠ 0) : μ P.rhoCheck ≠ 0 := by
  by_cases hμw : μ ∈ allWeights P
  · exact apply_rhoCheck_ne_zero P hμw hμ
  · rw [rootSpace_eq_bot P hμw] at hx
    exact absurd ((Submodule.mem_bot K).mp hx) hx0

end FiniteDimensional

/-! ### The projection onto `𝔥` -/

/-- The `𝔥`-component `π₀ x` of `x ∈ 𝔤̃(A)` in the triangular decomposition
`𝔤̃(A) = 𝔫̃₋ ⊕ 𝔥 ⊕ 𝔫̃₊`. -/
def hComp : P.AuxLieAlgebra →ₗ[K] H :=
  LinearMap.fst K H (FreeLieAlgebra K ι) ∘ₗ
    LinearMap.snd K (FreeLieAlgebra K ι) (H × FreeLieAlgebra K ι) ∘ₗ
      (triangularEquiv P).symm.toLinearMap

omit [CharZero K] in
lemma hComp_triangular (y : FreeLieAlgebra K ι) (a : H) (z : FreeLieAlgebra K ι) :
    hComp P (fHom P y + h P a + eHom P z) = a := by
  rw [← triangularEquiv_apply]
  simp only [hComp, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.snd_apply, LinearMap.fst_apply]

omit [CharZero K] in
@[simp] lemma hComp_h (a : H) : hComp P (h P a) = a := by
  simpa using hComp_triangular P 0 a 0

omit [CharZero K] in
lemma hComp_eHom (z : FreeLieAlgebra K ι) : hComp P (eHom P z) = 0 := by
  simpa using hComp_triangular P 0 0 z

omit [CharZero K] in
lemma hComp_fHom (y : FreeLieAlgebra K ι) : hComp P (fHom P y) = 0 := by
  simpa using hComp_triangular P y 0 0

lemma hComp_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.AuxLieAlgebra} (hx : x ∈ rootSpace P μ) :
    hComp P x = 0 := by
  by_cases hμw : μ ∈ allWeights P
  · rcases hμw with (hμ' | hμ') | hμ'
    · obtain ⟨y, rfl⟩ := rootSpace_neg_le P hμ' hx
      exact hComp_fHom P y
    · exact absurd hμ' hμ
    · obtain ⟨z, rfl⟩ := rootSpace_pos_le P hμ' hx
      exact hComp_eHom P z
  · rw [rootSpace_eq_bot P hμw] at hx
    simp [(Submodule.mem_bot K).mp hx]

lemma mem_range_h_of_mem {x : P.AuxLieAlgebra} (hx : x ∈ rootSpace P 0) :
    x ∈ LinearMap.range (h P) := by
  rwa [← rootSpace_zero]

lemma h_hComp_of_mem {x : P.AuxLieAlgebra} (hx : x ∈ rootSpace P 0) : h P (hComp P x) = x := by
  obtain ⟨a, rfl⟩ := mem_range_h_of_mem P hx
  simp

lemma hComp_lie_h (a : H) (x : P.AuxLieAlgebra) : hComp P ⁅h P a, x⁆ = 0 := by
  induction x using induction_on_rootSpace P with
  | mem μ x hx =>
    rw [hx a, map_smul]
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hComp_of_mem P hμ hx]
  | add x y hx hy => rw [lie_add, map_add, hx, hy, add_zero]

/-! ### The operator `D` -/

variable [FiniteDimensional K H]

/-- The operator acting by `⟨μ, ρ^∨⟩` on `𝔤̃_μ` for `μ ≠ 0` and by the identity on `𝔥`. -/
def degOp : Module.End K P.AuxLieAlgebra :=
  ad K _ (h P P.rhoCheck) + h P ∘ₗ hComp P

lemma degOp_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.AuxLieAlgebra} (hx : x ∈ rootSpace P μ) :
    degOp P x = μ P.rhoCheck • x := by
  simp [degOp, hComp_of_mem P hμ hx, hx P.rhoCheck]

omit [CharZero K] in
lemma degOp_h (a : H) : degOp P (h P a) = h P a := by
  simp [degOp, lie_h_h]

lemma lie_h_degOp (a : H) (x : P.AuxLieAlgebra) : ⁅h P a, degOp P x⁆ = degOp P ⁅h P a, x⁆ := by
  simp only [degOp, LinearMap.add_apply, ad_apply, LinearMap.comp_apply, lie_add, lie_h_h,
    hComp_lie_h, map_zero, add_zero]
  rw [leibniz_lie, lie_h_h, zero_lie, zero_add]

lemma degOp_surjective : Function.Surjective (degOp P) := by
  intro y
  induction y using induction_on_rootSpace P with
  | mem μ y hy =>
    by_cases hμ : μ = 0
    · subst hμ
      obtain ⟨a, rfl⟩ := mem_range_h_of_mem P hy
      exact ⟨h P a, degOp_h P a⟩
    · by_cases hy0 : y = 0
      · exact ⟨0, by simp [hy0]⟩
      · refine ⟨(μ P.rhoCheck)⁻¹ • y, ?_⟩
        rw [map_smul, degOp_of_mem P hμ hy, smul_smul,
          inv_mul_cancel₀ (apply_rhoCheck_ne_zero_of_mem P hμ hy hy0), one_smul]
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, map_add _ _ _⟩

lemma degOp_injective : Function.Injective (degOp P) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hle := inf_iSup_weightSpaceOfMap_le (h P) (LinearMap.ker (degOp P)) (fun a m hm ↦ by
    rw [LinearMap.mem_ker] at hm ⊢
    rw [← lie_h_degOp, hm, lie_zero]) (allWeights P)
  rw [iSup_rootSpace_eq_top, inf_top_eq] at hle
  refine (iSup₂_le fun μ _ ↦ ?_ : _ ≤ (⊥ : Submodule K P.AuxLieAlgebra)) (hle hx)
  intro y hy'
  obtain ⟨hy, hyμ⟩ := Submodule.mem_inf.mp hy'
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot]
  by_cases hμ : μ = 0
  · subst hμ
    obtain ⟨a, rfl⟩ := mem_range_h_of_mem P hyμ
    rwa [degOp_h] at hy
  · rw [degOp_of_mem P hμ hyμ] at hy
    by_contra hy0
    exact apply_rhoCheck_ne_zero_of_mem P hμ hyμ hy0 ((smul_eq_zero.mp hy).resolve_right hy0)

/-- `degOp` as a linear automorphism of `𝔤̃(A)`. -/
def degOpEquiv : P.AuxLieAlgebra ≃ₗ[K] P.AuxLieAlgebra :=
  LinearEquiv.ofBijective (degOp P) ⟨degOp_injective P, degOp_surjective P⟩

/-- The operator `D` acting by `⟨μ, ρ^∨⟩⁻¹` on `𝔤̃_μ` for `μ ≠ 0` and by zero on `𝔥`. -/
def degInv : Module.End K P.AuxLieAlgebra :=
  (degOpEquiv P).symm.toLinearMap - h P ∘ₗ hComp P

lemma degInv_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.AuxLieAlgebra} (hx : x ∈ rootSpace P μ) :
    degInv P x = (μ P.rhoCheck)⁻¹ • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hne := apply_rhoCheck_ne_zero_of_mem P hμ hx hx0
  have : (degOpEquiv P).symm x = (μ P.rhoCheck)⁻¹ • x := by
    rw [LinearEquiv.symm_apply_eq]
    change x = degOp P _
    rw [map_smul, degOp_of_mem P hμ hx, smul_smul, inv_mul_cancel₀ hne, one_smul]
  simp [degInv, this, hComp_of_mem P hμ hx]

lemma degInv_h (a : H) : degInv P (h P a) = 0 := by
  have : (degOpEquiv P).symm (h P a) = h P a := by
    rw [LinearEquiv.symm_apply_eq]
    exact (degOp_h P a).symm
  simp [degInv, this]

/-! ### The form -/

variable (S : A.Symmetrization)

/-- The invariant form on `𝔤̃(A)`: `(x | y) = (π₀ x | π₀ y) + (π₀ [D x, y] | ρ^∨)`, where
`π₀ = hComp` and `D = degInv`. -/
def invFormAux : LinearMap.BilinForm K P.AuxLieAlgebra :=
  LinearMap.mk₂ K (fun x y ↦ P.bilinForm S (hComp P x) (hComp P y) +
      P.bilinForm S (hComp P ⁅degInv P x, y⁆) P.rhoCheck)
    (fun x₁ x₂ y ↦ by simp only [map_add, LinearMap.add_apply, add_lie]; ring)
    (fun c x y ↦ by simp only [map_smul, LinearMap.smul_apply, smul_lie, smul_eq_mul]; ring)
    (fun x y₁ y₂ ↦ by simp only [map_add, lie_add, LinearMap.add_apply]; ring)
    (fun c x y ↦ by simp only [map_smul, lie_smul, LinearMap.smul_apply, smul_eq_mul]; ring)

lemma invFormAux_apply (x y : P.AuxLieAlgebra) :
    invFormAux P S x y = P.bilinForm S (hComp P x) (hComp P y) +
      P.bilinForm S (hComp P ⁅degInv P x, y⁆) P.rhoCheck := rfl

lemma invFormAux_h_left (a : H) (y : P.AuxLieAlgebra) :
    invFormAux P S (h P a) y = P.bilinForm S a (hComp P y) := by
  simp [invFormAux_apply, degInv_h]

/-- The form restricts to the form `Matrix.Realization.bilinForm` on `𝔥`. -/
@[simp] theorem invFormAux_h_h (a b : H) :
    invFormAux P S (h P a) (h P b) = P.bilinForm S a b := by
  simp [invFormAux_h_left]

lemma invFormAux_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.AuxLieAlgebra}
    (hx : x ∈ rootSpace P μ) (y : P.AuxLieAlgebra) :
    invFormAux P S x y = (μ P.rhoCheck)⁻¹ * P.bilinForm S (hComp P ⁅x, y⁆) P.rhoCheck := by
  simp [invFormAux_apply, hComp_of_mem P hμ hx, degInv_of_mem P hμ hx]

/-- `(𝔤̃_μ | 𝔤̃_ν) = 0` unless `μ + ν = 0`. -/
theorem invFormAux_eq_zero {μ ν : Dual K H} {x y : P.AuxLieAlgebra} (hx : x ∈ rootSpace P μ)
    (hy : y ∈ rootSpace P ν) (hμν : μ + ν ≠ 0) : invFormAux P S x y = 0 := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [zero_add] at hμν
    obtain ⟨a, rfl⟩ := mem_range_h_of_mem P hx
    simp [invFormAux_h_left, hComp_of_mem P hμν hy]
  · rw [invFormAux_of_mem P S hμ hx, hComp_of_mem P hμν (lie_mem_rootSpace P hx hy)]
    simp

lemma invFormAux_comm_of_mem {μ ν : Dual K H} {x y : P.AuxLieAlgebra} (hx : x ∈ rootSpace P μ)
    (hy : y ∈ rootSpace P ν) : invFormAux P S x y = invFormAux P S y x := by
  by_cases hμν : μ + ν = 0
  · obtain rfl : ν = -μ := eq_neg_of_add_eq_zero_right hμν
    by_cases hμ : μ = 0
    · subst hμ
      obtain ⟨a, rfl⟩ := mem_range_h_of_mem P hx
      obtain ⟨b, rfl⟩ := mem_range_h_of_mem P (by simpa using hy)
      simp [(P.isSymm_bilinForm S).eq a b]
    · rw [invFormAux_of_mem P S hμ hx, invFormAux_of_mem P S (neg_ne_zero.mpr hμ) hy, ← lie_skew]
      simp only [map_neg, LinearMap.neg_apply, inv_neg, neg_mul, mul_neg]
  · rw [invFormAux_eq_zero P S hx hy hμν, invFormAux_eq_zero P S hy hx (by rwa [add_comm])]

/-- The form on `𝔤̃(A)` is symmetric. -/
theorem isSymm_invFormAux : (invFormAux P S).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
  induction x using induction_on_rootSpace P with
  | mem μ x hx =>
    induction y using induction_on_rootSpace P with
    | mem ν y hy => exact invFormAux_comm_of_mem P S hx hy
    | add y₁ y₂ h₁ h₂ => simp [h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp [h₁, h₂]

/-- `(eᵢ | fⱼ) = δᵢⱼ εᵢ` ([Kac] §2.2). -/
theorem invFormAux_e_f (i j : ι) :
    invFormAux P S (e P i) (f P j) = if i = j then (S.ε i : K) else 0 := by
  split_ifs with hij
  · subst hij
    rw [invFormAux_of_mem P S (P.linearIndependent_root.ne_zero i) (e_mem_rootSpace P i),
      lie_e_f_self, hComp_h, bilinForm_coroot_left, root_rhoCheck]
    simp
  · refine invFormAux_eq_zero P S (e_mem_rootSpace P i) (f_mem_rootSpace P j) fun h0 ↦ hij ?_
    by_contra hne
    have := Fintype.linearIndependent_iff.mp P.linearIndependent_root
      (fun k ↦ (if k = i then 1 else 0) - if k = j then 1 else 0)
      (by
        rw [← sub_eq_add_neg] at h0
        simpa [sub_smul, Finset.sum_sub_distrib, ite_smul] using h0) i
    simp [hne] at this

/-! ### The identity `[x, y] = (x | y) ν⁻¹(μ)` -/

/-- The statement `C_μ`: `[x, y] = (x | y) ν⁻¹(μ)` for all `x ∈ 𝔤̃_μ` and `y ∈ 𝔤̃_{-μ}`. It holds
for all `μ` by `Matrix.Realization.AuxLieAlgebra.lie_eq_invFormAux_smul`. -/
def LieEqForm (μ : Dual K H) : Prop :=
  ∀ x ∈ rootSpace P μ, ∀ y ∈ rootSpace P (-μ),
    ⁅x, y⁆ = invFormAux P S x y • h P ((P.toDual S).symm μ)

variable {P S}

lemma lieEqForm_of_exists {μ : Dual K H} (hμ : μ ≠ 0)
    (hex : ∀ x ∈ rootSpace P μ, ∀ y ∈ rootSpace P (-μ),
      ∃ c : K, ⁅x, y⁆ = c • h P ((P.toDual S).symm μ)) : LieEqForm P S μ := by
  intro x hx y hy
  obtain ⟨c, hc⟩ := hex x hx y hy
  by_cases hx0 : x = 0
  · simp [hx0]
  have hne := apply_rhoCheck_ne_zero_of_mem P hμ hx hx0
  rw [hc, invFormAux_of_mem P S hμ hx, hc]
  congr 1
  simp only [map_smul, hComp_h, LinearMap.smul_apply, bilinForm_toDual_symm_left, smul_eq_mul]
  field_simp

variable (P S) in
lemma lieEqForm_zero : LieEqForm P S 0 := by
  intro x hx y hy
  rw [neg_zero] at hy
  obtain ⟨a, rfl⟩ := mem_range_h_of_mem P hx
  obtain ⟨b, rfl⟩ := mem_range_h_of_mem P hy
  simp [lie_h_h]

variable (S) in
lemma lieEqForm_of_notMem {μ : Dual K H} (hμ : μ ∉ allWeights P) : LieEqForm P S μ := by
  intro x hx y _
  rw [rootSpace_eq_bot P hμ, Submodule.mem_bot] at hx
  simp [hx]

lemma LieEqForm.neg {μ : Dual K H} (hμ : LieEqForm P S μ) : LieEqForm P S (-μ) := by
  intro x hx y hy
  rw [neg_neg] at hy
  rw [← lie_skew, hμ y hy x hx, (isSymm_invFormAux P S).eq y x]
  simp only [map_neg, smul_neg]

variable (P S) in
lemma lieEqForm_root (i : ι) : LieEqForm P S (P.root i) := by
  refine lieEqForm_of_exists (P.linearIndependent_root.ne_zero i) fun x hx y hy ↦ ?_
  rw [rootSpace_root, Submodule.mem_span_singleton] at hx
  rw [rootSpace_neg_root, Submodule.mem_span_singleton] at hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hε : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  refine ⟨a * b * S.ε i, ?_⟩
  rw [smul_lie, lie_smul, lie_e_f_self, toDual_symm_root, map_smul, smul_smul, smul_smul,
    mul_assoc, mul_inv_cancel₀ hε, mul_one]

/-! ### Invariance for triples -/

variable (P S) in
/-- The cyclic invariance `(x | [y, z]) = (y | [z, x]) = (z | [x, y])` for a triple. -/
def InvTriple (x y z : P.AuxLieAlgebra) : Prop :=
  invFormAux P S x ⁅y, z⁆ = invFormAux P S z ⁅x, y⁆ ∧
    invFormAux P S y ⁅z, x⁆ = invFormAux P S z ⁅x, y⁆

lemma InvTriple.rotate {x y z : P.AuxLieAlgebra} (hxyz : InvTriple P S x y z) :
    InvTriple P S y z x :=
  ⟨hxyz.2.trans hxyz.1.symm, hxyz.1.symm⟩

/-- Lemma 1 of the module docstring, independent case. -/
lemma invTriple_of_linearIndependent {α β γ : Dual K H} (hsum : α + β + γ = 0)
    (hα : LieEqForm P S α) (hβ : LieEqForm P S β) (hγ : LieEqForm P S γ)
    {x y z : P.AuxLieAlgebra} (hx : x ∈ rootSpace P α) (hy : y ∈ rootSpace P β)
    (hz : z ∈ rootSpace P γ) (hind : ∀ s t : K, s • α + t • β = 0 → s = 0 ∧ t = 0) :
    InvTriple P S x y z := by
  have e1 : β + γ = -α := by rw [eq_neg_iff_add_eq_zero, ← hsum]; abel
  have e2 : γ + α = -β := by rw [eq_neg_iff_add_eq_zero, ← hsum]; abel
  have e3 : α + β = -γ := by rw [eq_neg_iff_add_eq_zero, ← hsum]
  have h1 := hα x hx _ (e1 ▸ lie_mem_rootSpace P hy hz)
  have h2 := hβ y hy _ (e2 ▸ lie_mem_rootSpace P hz hx)
  have h3 := hγ z hz _ (e3 ▸ lie_mem_rootSpace P hx hy)
  have hj : h P (invFormAux P S x ⁅y, z⁆ • (P.toDual S).symm α +
      invFormAux P S y ⁅z, x⁆ • (P.toDual S).symm β +
      invFormAux P S z ⁅x, y⁆ • (P.toDual S).symm γ) = h P 0 := by
    rw [map_add, map_add, map_smul, map_smul, map_smul, ← h1, ← h2, ← h3, lie_jacobi, map_zero]
  have hj' := congrArg (P.toDual S) (h_injective P hj)
  simp only [map_add, map_smul, LinearEquiv.apply_symm_apply, map_zero] at hj'
  have hγ' : γ = -α - β := by rw [sub_eq_add_neg, ← neg_add, e3, neg_neg]
  rw [hγ'] at hj'
  obtain ⟨hs, ht⟩ := hind (invFormAux P S x ⁅y, z⁆ - invFormAux P S z ⁅x, y⁆)
    (invFormAux P S y ⁅z, x⁆ - invFormAux P S z ⁅x, y⁆) (by rw [← hj']; module)
  exact ⟨sub_eq_zero.mp hs, sub_eq_zero.mp ht⟩

/-- Lemma 1 of the module docstring, case of a zero weight. -/
lemma invTriple_of_zero {β γ : Dual K H} (hsum : β + γ = 0) (hβ : LieEqForm P S β)
    {x y z : P.AuxLieAlgebra} (hx : x ∈ rootSpace P 0) (hy : y ∈ rootSpace P β)
    (hz : z ∈ rootSpace P γ) : InvTriple P S x y z := by
  obtain rfl : γ = -β := eq_neg_of_add_eq_zero_right hsum
  obtain ⟨a, rfl⟩ := mem_range_h_of_mem P hx
  have e1 : invFormAux P S (h P a) ⁅y, z⁆ = β a * invFormAux P S y z := by
    rw [hβ y hy z hz, map_smul, invFormAux_h_h, bilinForm_toDual_symm_right, smul_eq_mul,
      mul_comm]
  have e2 : invFormAux P S z ⁅h P a, y⁆ = β a * invFormAux P S y z := by
    rw [hy a, map_smul, smul_eq_mul, (isSymm_invFormAux P S).eq z y]
  have e3 : invFormAux P S y ⁅z, h P a⁆ = β a * invFormAux P S y z := by
    rw [← lie_skew, hz a]
    simp
  exact ⟨e1.trans e2.symm, e3.trans e2.symm⟩

lemma invTriple_of_zero_left {x y z : P.AuxLieAlgebra} (hx : x = 0) : InvTriple P S x y z := by
  subst hx; simp [InvTriple]

lemma invTriple_of_zero_right {x y z : P.AuxLieAlgebra} (hz : z = 0) : InvTriple P S x y z := by
  subst hz; simp [InvTriple]

omit [FiniteDimensional K H] in
/-- A positive weight `μ` of `𝔤̃(A)` which is a multiple of a simple root `αₖ` is `αₖ`. -/
lemma eq_root_of_mem_posWeights {μ : Dual K H} (hμ : μ ∈ P.posWeights) {x : P.AuxLieAlgebra}
    (hx : x ∈ rootSpace P μ) (hx0 : x ≠ 0) {k : ι} {c : K} (hc : μ = c • P.root k) :
    μ = P.root k := by
  obtain ⟨a, ⟨ha0, ha⟩, rfl⟩ := hμ
  have hsum' : ∑ l, (a l : K) • P.root l - ∑ l, (if l = k then c else 0) • P.root l = 0 := by
    rw [← rootOf_apply, hc]
    simp [ite_smul]
  have hsum : ∑ l, ((a l : K) - if l = k then c else 0) • P.root l = 0 := by
    rw [← hsum', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ ↦ by module
  have hal : ∀ l, l ≠ k → a l = 0 := fun l hl ↦ by
    have := Fintype.linearIndependent_iff.mp P.linearIndependent_root _ hsum l
    simpa [hl] using this
  set n := (a k).toNat with hn
  have hak : a = n • Pi.single k 1 := by
    ext l
    by_cases hl : l = k
    · subst hl; simp [hn, Int.toNat_of_nonneg (ha0 l)]
    · simp [hl, hal l hl]
  have hμn : P.rootOf a = n • P.root k := by rw [hak, map_nsmul, rootOf_single]
  have hn0 : n ≠ 0 := by
    rintro h0
    exact ha (by rw [hak, h0, zero_smul])
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    rw [hμn, hn1, one_smul]
  · rw [hμn, rootSpace_nsmul_root_eq_bot P k hn2, Submodule.mem_bot] at hx
    exact absurd hx hx0

omit [FiniteDimensional K H] in
/-- A nonzero weight `μ` of `𝔤̃(A)` which is a multiple of a simple root `αₖ` is `±αₖ`. -/
lemma eq_root_or_eq_neg_root {μ : Dual K H} {x : P.AuxLieAlgebra} (hx : x ∈ rootSpace P μ)
    (hx0 : x ≠ 0) (hμ0 : μ ≠ 0) {k : ι} {c : K} (hc : μ = c • P.root k) :
    μ = P.root k ∨ μ = -P.root k := by
  have hμw : μ ∈ allWeights P := by
    by_contra hμw
    rw [rootSpace_eq_bot P hμw, Submodule.mem_bot] at hx
    exact hx0 hx
  rcases hμw with (hμ | hμ) | hμ
  · right
    have hωx := chevalleyInvolution_mem_rootSpace P hx
    have hωx0 : chevalleyInvolution P x ≠ 0 := fun h0 ↦ hx0 (by
      simpa using congrArg (chevalleyInvolution P) h0)
    have := eq_root_of_mem_posWeights ((mem_negWeights_iff P).mp hμ) hωx hωx0 (k := k) (c := -c)
      (by rw [hc]; module)
    rw [← this, neg_neg]
  · exact absurd hμ hμ0
  · exact Or.inl (eq_root_of_mem_posWeights hμ hx hx0 hc)

/-- Lemmas 1 and 2 of the module docstring: invariance for a triple whose middle element has
weight `±αₖ`. -/
lemma invTriple_of_root {α β γ : Dual K H} (hsum : α + β + γ = 0)
    (hα : LieEqForm P S α) (hβ : LieEqForm P S β) (hγ : LieEqForm P S γ)
    {x y z : P.AuxLieAlgebra} (hx : x ∈ rootSpace P α) (hy : y ∈ rootSpace P β)
    (hz : z ∈ rootSpace P γ) {k : ι} (hβk : β = P.root k ∨ β = -P.root k) :
    InvTriple P S x y z := by
  by_cases hx0 : x = 0
  · exact invTriple_of_zero_left hx0
  by_cases hz0 : z = 0
  · exact invTriple_of_zero_right hz0
  by_cases hα0 : α = 0
  · subst hα0
    exact invTriple_of_zero (by simpa using hsum) hβ hx hy hz
  by_cases hγ0 : γ = 0
  · subst hγ0
    exact (invTriple_of_zero (by simpa using hsum) hα hz hx hy).rotate
  have hβ0 : β ≠ 0 := by
    rcases hβk with rfl | rfl <;> simp [P.linearIndependent_root.ne_zero k]
  refine invTriple_of_linearIndependent hsum hα hβ hγ hx hy hz fun s t hst ↦ ?_
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right hβ0⟩
  exfalso
  have hαβ : α = (-(s⁻¹ * t)) • β := by
    have h1 : s • α = -(t • β) := eq_neg_of_add_eq_zero_left hst
    calc α = s⁻¹ • (s • α) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      _ = _ := by rw [h1]; module
  have hαc : ∃ c : K, α = c • P.root k := by
    rcases hβk with rfl | rfl
    · exact ⟨_, hαβ⟩
    · exact ⟨s⁻¹ * t, by rw [hαβ, smul_neg, neg_smul, neg_neg]⟩
  obtain ⟨c, hc⟩ := hαc
  have hγαβ : γ = -α - β := by rw [← sub_eq_zero, ← hsum]; abel
  have h2 : rootSpace P (2 • P.root k) = ⊥ := rootSpace_nsmul_root_eq_bot P k le_rfl
  have h2' : rootSpace P (-(2 • P.root k)) = ⊥ := rootSpace_neg_nsmul_root_eq_bot P k le_rfl
  rcases eq_root_or_eq_neg_root hx hx0 hα0 hc with rfl | rfl <;>
    rcases hβk with rfl | rfl
  · rw [hγαβ, show -P.root k - P.root k = -(2 • P.root k) by rw [two_smul]; abel, h2',
      Submodule.mem_bot] at hz
    exact hz0 hz
  · exact hγ0 (by rw [hγαβ]; abel)
  · exact hγ0 (by rw [hγαβ]; abel)
  · rw [hγαβ, show - -P.root k - -P.root k = 2 • P.root k by rw [two_smul]; abel, h2,
      Submodule.mem_bot] at hz
    exact hz0 hz

/-! ### Proof of `C_μ` by induction on the height -/

omit [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
variable (P) in
lemma wordWt_cons_mem_posWeights (j : ι) (l : List ι) : wordWt P (j :: l) ∈ P.posWeights := by
  classical
  rw [wordWt_eq_rootOf]
  refine ⟨counts (j :: l), ⟨fun i ↦ ?_, fun h0 ↦ ?_⟩, rfl⟩
  · simp [counts]
  · have := congr_fun h0 j
    simp [counts] at this
    omega

omit [FiniteDimensional K H] in
variable (P) in
/-- For `μ > 0` not a simple root, `𝔤̃_μ` is spanned by the `[eⱼ, x]`, `x ∈ 𝔤̃_{μ - αⱼ}`. -/
lemma rootSpace_induction_e {μ : Dual K H} {p : P.AuxLieAlgebra → Prop} (hμ : μ ∈ P.posWeights)
    (hμ1 : ∀ j, μ ≠ P.root j) (zero : p 0) (add : ∀ x y, p x → p y → p (x + y))
    (smul : ∀ (c : K) x, p x → p (c • x))
    (gen : ∀ j ν, ν ∈ P.posWeights → μ = P.root j + ν → ∀ x ∈ rootSpace P ν, p ⁅e P j, x⁆) :
    ∀ x ∈ rootSpace P μ, p x := by
  intro x hx
  have hx' : x ∈ posSpan P μ := rootSpace_le_posSpan P hμ hx
  rw [posSpan] at hx'
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, l, hjl, rfl⟩ := hx
    cases l with
    | nil => exact absurd (by simpa using hjl.symm) (hμ1 j)
    | cons i l =>
      rw [List.map_cons, adProd_cons]
      refine gen i (wordWt P (j :: l)) (wordWt_cons_mem_posWeights P j l) ?_ _
        (adProd_mem_rootSpace P j l)
      rw [← hjl]
      simp only [wordWt_cons]
      abel
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul c x _ hx => exact smul c x hx

omit [FiniteDimensional K H] in
variable (P) in
/-- For `μ > 0` not a simple root, `𝔤̃_{-μ}` is spanned by the `[fⱼ, y]`,
`y ∈ 𝔤̃_{-(μ - αⱼ)}`. -/
lemma rootSpace_induction_f {μ : Dual K H} {p : P.AuxLieAlgebra → Prop} (hμ : μ ∈ P.posWeights)
    (hμ1 : ∀ j, μ ≠ P.root j) (zero : p 0) (add : ∀ x y, p x → p y → p (x + y))
    (smul : ∀ (c : K) x, p x → p (c • x))
    (gen : ∀ j ν, ν ∈ P.posWeights → μ = P.root j + ν → ∀ y ∈ rootSpace P (-ν), p ⁅f P j, y⁆) :
    ∀ y ∈ rootSpace P (-μ), p y := by
  intro y hy
  have hωy : chevalleyInvolution P y ∈ rootSpace P μ := by
    simpa using chevalleyInvolution_mem_rootSpace P hy
  have hgen : ∀ j ν, ν ∈ P.posWeights → μ = P.root j + ν → ∀ x ∈ rootSpace P ν,
      p (chevalleyInvolution P ⁅e P j, x⁆) := by
    intro j ν hν hμν x hx
    have := smul (-1) _ (gen j ν hν hμν _ (chevalleyInvolution_mem_rootSpace P hx))
    simpa using this
  have := rootSpace_induction_e P (p := fun x ↦ p (chevalleyInvolution P x)) hμ hμ1
    (by simpa using zero) (fun x y hx hy ↦ by simpa using add _ _ hx hy)
    (fun c x hx ↦ by simpa using smul c _ hx) hgen _ hωy
  simpa using this

omit [DecidableEq ι] [FiniteDimensional K H] in
variable (P) in
lemma root_sub_root_notMem {i j : ι} (hij : i ≠ j) : P.root i - P.root j ∉ allWeights P := by
  classical
  have hr : P.root i - P.root j = P.rootOf (Pi.single i 1 - Pi.single j 1) := by
    simp [map_sub]
  rintro ((⟨k, ⟨hk0, -⟩, hk⟩ | h0) | ⟨k, ⟨hk0, -⟩, hk⟩)
  · change -P.rootOf k = _ at hk
    rw [hr, ← map_neg, P.rootOf_injective.eq_iff] at hk
    have h1 := congr_fun hk i
    have h2 := hk0 i
    simp [hij] at h1 h2
    omega
  · rw [Set.mem_singleton_iff, hr, ← map_zero P.rootOf, P.rootOf_injective.eq_iff] at h0
    have := congr_fun h0 i
    simp [hij] at this
  · rw [hr, P.rootOf_injective.eq_iff] at hk
    have h1 := congr_fun hk j
    have h2 := hk0 j
    simp [hij.symm] at h1 h2
    omega

/-- The inductive step of the proof of `C_μ` (see the module docstring). -/
lemma lie_lie_e_lie_f {μ ν κ : Dual K H} {i j : ι} (hν : μ = P.root j + ν)
    (hκ : μ = P.root i + κ) (hCi : LieEqForm P S (P.root i)) (hCj : LieEqForm P S (P.root j))
    (hCν : LieEqForm P S ν) (hCκ : LieEqForm P S κ) (hCνi : LieEqForm P S (ν - P.root i))
    {x y : P.AuxLieAlgebra} (hx : x ∈ rootSpace P ν) (hy : y ∈ rootSpace P (-κ)) :
    ⁅⁅e P j, x⁆, ⁅f P i, y⁆⁆ =
      invFormAux P S (e P j) ⁅x, ⁅f P i, y⁆⁆ • h P ((P.toDual S).symm μ) := by
  set w := ⁅f P i, y⁆ with hw
  set u := ⁅x, f P i⁆ with hu
  set z := ⁅e P j, y⁆ with hz
  have hwμ : w ∈ rootSpace P (-μ) := by
    have := lie_mem_rootSpace P (f_mem_rootSpace P i) hy
    rwa [show -P.root i + -κ = -μ by rw [hκ]; abel] at this
  have hxw : ⁅x, w⁆ ∈ rootSpace P (-P.root j) := by
    have := lie_mem_rootSpace P hx hwμ
    rwa [show ν + -μ = -P.root j by rw [hν]; abel] at this
  have hew : ⁅e P j, w⁆ ∈ rootSpace P (-ν) := by
    have := lie_mem_rootSpace P (e_mem_rootSpace P j) hwμ
    rwa [show P.root j + -μ = -ν by rw [hν]; abel] at this
  have huν : u ∈ rootSpace P (ν - P.root i) := by
    have := lie_mem_rootSpace P hx (f_mem_rootSpace P i)
    rwa [← sub_eq_add_neg] at this
  have hzν : z ∈ rootSpace P (-(ν - P.root i)) := by
    have := lie_mem_rootSpace P (e_mem_rootSpace P j) hy
    rwa [show P.root j + -κ = -(ν - P.root i) by
      have : P.root j + ν = P.root i + κ := hν.symm.trans hκ
      rw [← sub_eq_zero, ← sub_eq_zero.mpr this]; abel] at this
  -- the key identity `(eⱼ | [x, w]) = -(x | [eⱼ, w])`
  have key : invFormAux P S x ⁅e P j, w⁆ = -invFormAux P S (e P j) ⁅x, w⁆ := by
    -- `(x | [fᵢ, z]) = ([x, fᵢ] | z)`
    have h1 : invFormAux P S x ⁅f P i, z⁆ = invFormAux P S u z := by
      have := (invTriple_of_root (α := ν) (β := -P.root i) (γ := -(ν - P.root i))
        (by abel) hCν hCi.neg hCνi.neg hx (f_mem_rootSpace P i) hzν (k := i) (Or.inr rfl)).1
      rw [this, (isSymm_invFormAux P S).eq]
    -- `(eⱼ | [u, y]) = -(u | z)`
    have h2 : invFormAux P S (e P j) ⁅u, y⁆ = -invFormAux P S u z := by
      have ht := (invTriple_of_root (α := -κ) (β := P.root j) (γ := ν - P.root i)
        (by rw [hκ] at hν; rw [← sub_eq_zero.mpr hν.symm]; abel) hCκ.neg hCj hCνi hy
        (e_mem_rootSpace P j) huν (k := j) (Or.inl rfl)).rotate
      rw [ht.1, ← ht.2, ← lie_skew, map_neg]
    by_cases hij : i = j
    · subst hij
      have hνκ : ν = κ := add_left_cancel (hν.symm.trans hκ)
      subst hνκ
      have hxy := hCν x hx y hy
      have e1 : invFormAux P S x ⁅⁅e P i, f P i⁆, y⁆ =
          -(ν (P.coroot i) * invFormAux P S x y) := by
        rw [lie_e_f_self, hy (P.coroot i)]
        simp
      have e2 : invFormAux P S (e P i) ⁅f P i, ⁅x, y⁆⁆ =
          ν (P.coroot i) * invFormAux P S x y := by
        have hei : invFormAux P S (e P i) (f P i) = S.ε i := by simp [invFormAux_e_f]
        rw [hxy, lie_smul, ← lie_skew, lie_h_f, neg_neg, smul_smul, map_smul, hei, smul_eq_mul]
        have hε : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
        have : P.root i ((P.toDual S).symm ν) = ν (P.coroot i) / S.ε i := by
          rw [← dualBilinForm_apply_eq, (P.isSymm_dualBilinForm S).eq, dualBilinForm_root_right]
        rw [this]
        field_simp
      rw [hw, leibniz_lie, map_add, e1, h1, leibniz_lie, map_add, e2, ← hu, h2]
      ring
    · have e1 : ⁅e P j, f P i⁆ = 0 := lie_e_f_of_ne P (Ne.symm hij)
      have e2 : ⁅x, y⁆ = 0 := by
        have := lie_mem_rootSpace P hx hy
        rw [show ν + -κ = P.root i - P.root j by
          have : P.root j + ν = P.root i + κ := hν.symm.trans hκ
          rw [← sub_eq_zero, ← sub_eq_zero.mpr this]; abel,
          rootSpace_eq_bot P (root_sub_root_notMem P hij), Submodule.mem_bot] at this
        exact this
      rw [hw, leibniz_lie, e1, zero_lie, zero_add, h1, leibniz_lie, e2, lie_zero, add_zero,
        ← hu, h2, neg_neg]
  rw [lie_lie, hCj _ (e_mem_rootSpace P j) _ hxw, hCν _ hx _ hew, key, neg_smul, sub_neg_eq_add,
    ← smul_add, ← map_add, ← map_add, ← hν]

omit [DecidableEq ι] [CharZero K] in
variable (P) in
lemma exists_nat_eq_of_mem_negWeights {μ : Dual K H} (hμ : μ ∈ P.negWeights) :
    ∃ n : ℕ, 0 < n ∧ μ P.rhoCheck = -(n : K) := by
  obtain ⟨n, hn, hμn⟩ := exists_nat_of_mem_posWeights P ((mem_negWeights_iff P).mp hμ)
  exact ⟨n, hn, by rw [← hμn, LinearMap.neg_apply, neg_neg]⟩

variable (P S) in
/-- `C_μ` for all `μ`: `[x, y] = (x | y) ν⁻¹(μ)` for `x ∈ 𝔤̃_μ` and `y ∈ 𝔤̃_{-μ}`
([Kac] Thm. 2.2 e), for `𝔤̃(A)`). -/
theorem lie_eq_invFormAux_smul (μ : Dual K H) : LieEqForm P S μ := by
  have hpos : ∀ n : ℕ, ∀ μ ∈ P.posWeights, μ P.rhoCheck = n → LieEqForm P S μ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
    intro μ hμ hμn
    -- `C` at weights of smaller absolute height
    have low : ∀ ν : Dual K H, ∀ m : ℤ, ν P.rhoCheck = m → |m| < n → LieEqForm P S ν := by
      intro ν m hν hm
      by_cases hνw : ν ∈ allWeights P
      · rcases hνw with (hν' | hν') | hν'
        · obtain ⟨m', -, hνm'⟩ := exists_nat_eq_of_mem_negWeights P hν'
          have hmm : (m' : ℤ) = -m := by
            have : ((m' : ℤ) : K) = ((-m : ℤ) : K) := by
              push_cast; rw [← hν, hνm', neg_neg]
            exact_mod_cast this
          have := (IH m' (by rw [abs_lt] at hm; omega) _ ((mem_negWeights_iff P).mp hν')
            (by rw [LinearMap.neg_apply, hνm', neg_neg])).neg
          rwa [neg_neg] at this
        · rw [Set.mem_singleton_iff.mp hν']
          exact lieEqForm_zero P S
        · obtain ⟨m', -, hνm'⟩ := exists_nat_of_mem_posWeights P hν'
          have hmm : (m' : ℤ) = m := by
            have : ((m' : ℤ) : K) = ((m : ℤ) : K) := by push_cast; rw [← hν, hνm']
            exact_mod_cast this
          exact IH m' (by rw [abs_lt] at hm; omega) _ hν' hνm'
      · exact lieEqForm_of_notMem S hνw
    by_cases hμ1 : ∃ j, μ = P.root j
    · obtain ⟨j, rfl⟩ := hμ1
      exact lieEqForm_root P S j
    simp only [not_exists] at hμ1
    refine lieEqForm_of_exists (fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ hμ)) ?_
    refine rootSpace_induction_e P (p := fun x ↦ ∀ y ∈ rootSpace P (-μ),
      ∃ c : K, ⁅x, y⁆ = c • h P ((P.toDual S).symm μ)) hμ hμ1 ?_ ?_ ?_ ?_
    · exact fun y _ ↦ ⟨0, by simp⟩
    · intro x₁ x₂ h₁ h₂ y hy
      obtain ⟨c₁, hc₁⟩ := h₁ y hy
      obtain ⟨c₂, hc₂⟩ := h₂ y hy
      exact ⟨c₁ + c₂, by rw [add_lie, hc₁, hc₂, add_smul]⟩
    · intro c x hx y hy
      obtain ⟨c', hc'⟩ := hx y hy
      exact ⟨c * c', by rw [smul_lie, hc', smul_smul]⟩
    intro j ν hν hμν x hx
    refine rootSpace_induction_f P (p := fun y ↦
      ∃ c : K, ⁅⁅e P j, x⁆, y⁆ = c • h P ((P.toDual S).symm μ)) hμ hμ1 ?_ ?_ ?_ ?_
    · exact ⟨0, by simp⟩
    · rintro y₁ y₂ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
      exact ⟨c₁ + c₂, by rw [lie_add, hc₁, hc₂, add_smul]⟩
    · rintro c y ⟨c', hc'⟩
      exact ⟨c * c', by rw [lie_smul, hc', smul_smul]⟩
    intro i κ hκ hμκ y hy
    -- heights
    obtain ⟨mν, hmν, hνm⟩ := exists_nat_of_mem_posWeights P hν
    have hνρ : ν P.rhoCheck = ((n : ℤ) - 1 : ℤ) := by
      rw [show ν = μ - P.root j by rw [hμν]; abel, LinearMap.sub_apply, hμn, root_rhoCheck]
      push_cast; ring
    have hn2 : 2 ≤ n := by
      have : ((mν : ℤ) : K) = ((n : ℤ) - 1 : ℤ) := by rw [← hνρ, hνm, Int.cast_natCast]
      have := (Int.cast_injective (α := K)) this
      omega
    have hκρ : κ P.rhoCheck = ((n : ℤ) - 1 : ℤ) := by
      rw [show κ = μ - P.root i by rw [hμκ]; abel, LinearMap.sub_apply, hμn, root_rhoCheck]
      push_cast; ring
    have hνiρ : (ν - P.root i) P.rhoCheck = ((n : ℤ) - 2 : ℤ) := by
      rw [LinearMap.sub_apply, hνρ, root_rhoCheck]
      push_cast; ring
    have hrρ : ∀ k, P.root k P.rhoCheck = ((1 : ℤ) : K) := fun k ↦ by simp
    have hlt : ∀ m : ℤ, (m = 1 ∨ m = n - 1 ∨ m = n - 2) → |m| < n := by
      intro m hm
      rw [abs_lt]
      omega
    exact ⟨_, lie_lie_e_lie_f hμν hμκ (low _ _ (hrρ i) (hlt _ (Or.inl rfl)))
      (low _ _ (hrρ j) (hlt _ (Or.inl rfl))) (low _ _ hνρ (hlt _ (Or.inr (Or.inl rfl))))
      (low _ _ hκρ (hlt _ (Or.inr (Or.inl rfl))))
      (low _ _ hνiρ (hlt _ (Or.inr (Or.inr rfl)))) hx hy⟩
  by_cases hμw : μ ∈ allWeights P
  · rcases hμw with (hμ | hμ) | hμ
    · obtain ⟨n, -, hμn⟩ := exists_nat_of_mem_posWeights P ((mem_negWeights_iff P).mp hμ)
      simpa using (hpos n _ ((mem_negWeights_iff P).mp hμ) hμn).neg
    · rw [Set.mem_singleton_iff.mp hμ]
      exact lieEqForm_zero P S
    · obtain ⟨n, -, hμn⟩ := exists_nat_of_mem_posWeights P hμ
      exact hpos n μ hμ hμn
  · exact lieEqForm_of_notMem S hμw

/-! ### Invariance -/

lemma lie_left_eq_of_invTriple {β : Dual K H} {y : P.AuxLieAlgebra} (hy : y ∈ rootSpace P β)
    (hinv : ∀ α γ, α + β + γ = 0 → ∀ x ∈ rootSpace P α, ∀ z ∈ rootSpace P γ,
      InvTriple P S x y z) (x z : P.AuxLieAlgebra) :
    invFormAux P S ⁅x, y⁆ z = invFormAux P S x ⁅y, z⁆ := by
  induction x using induction_on_rootSpace P with
  | mem α x hx =>
    induction z using induction_on_rootSpace P with
    | mem γ z hz =>
      by_cases hs : α + β + γ = 0
      · rw [(hinv α γ hs x hx z hz).1, (isSymm_invFormAux P S).eq]
      · rw [invFormAux_eq_zero P S (lie_mem_rootSpace P hx hy) hz hs,
          invFormAux_eq_zero P S hx (lie_mem_rootSpace P hy hz) (by rwa [← add_assoc])]
    | add z₁ z₂ h₁ h₂ => simp [lie_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp [add_lie, h₁, h₂]

variable (P S) in
/-- The form on `𝔤̃(A)` is invariant: `([x, y] | z) = (x | [y, z])`. -/
theorem invFormAux_lie (x y z : P.AuxLieAlgebra) :
    invFormAux P S ⁅x, y⁆ z = invFormAux P S x ⁅y, z⁆ := by
  have C := lie_eq_invFormAux_smul P S
  suffices ∀ y x z : P.AuxLieAlgebra, invFormAux P S ⁅x, y⁆ z = invFormAux P S x ⁅y, z⁆ from
    this y x z
  intro y
  induction y using induction_on with
  | he k =>
    exact lie_left_eq_of_invTriple (e_mem_rootSpace P k) fun α γ hs x hx z hz ↦
      invTriple_of_root hs (C α) (C _) (C γ) hx (e_mem_rootSpace P k) hz (Or.inl rfl)
  | hf k =>
    exact lie_left_eq_of_invTriple (f_mem_rootSpace P k) fun α γ hs x hx z hz ↦
      invTriple_of_root hs (C α) (C _) (C γ) hx (f_mem_rootSpace P k) hz (Or.inr rfl)
  | hh a =>
    exact lie_left_eq_of_invTriple (h_mem_rootSpace P a) fun α γ hs x hx z hz ↦
      (invTriple_of_zero (by rw [← hs]; abel) (C γ) (h_mem_rootSpace P a) hz hx).rotate.rotate
  | zero => simp
  | add y₁ y₂ h₁ h₂ => intro x z; simp [lie_add, add_lie, h₁ x z, h₂ x z]
  | smul c y hy => intro x z; simp [lie_smul, smul_lie, hy x z]
  | lie y₁ y₂ h₁ h₂ =>
    intro x z
    rw [leibniz_lie, ← lie_skew y₁, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
    simp only [h₁, h₂]
    rw [lie_lie, map_sub]
    abel

variable (P S) in
/-- The form on `𝔤̃(A)` is invariant, in the sense of `LinearMap.BilinForm.lieInvariant`. -/
theorem lieInvariant_invFormAux : (invFormAux P S).lieInvariant P.AuxLieAlgebra := by
  intro x y z
  rw [← lie_skew, map_neg, LinearMap.neg_apply, invFormAux_lie]

/-! ### The radical is `𝔯` -/

variable (P S) in
/-- The maximal ideal `𝔯` lies in the radical of the form. -/
theorem invFormAux_eq_zero_of_mem_maxIdeal {r : P.AuxLieAlgebra} (hr : r ∈ maxIdeal P)
    (y : P.AuxLieAlgebra) : invFormAux P S r y = 0 := by
  have hle := inf_iSup_weightSpaceOfMap_le (h P) (maxIdeal P).toSubmodule
    (lie_h_mem P _) (allWeights P)
  rw [iSup_rootSpace_eq_top, inf_top_eq] at hle
  have hr' : r ∈ ⨆ μ, (maxIdeal P).toSubmodule ⊓ rootSpace P μ :=
    (iSup₂_le fun μ _ ↦ le_iSup (fun μ ↦ (maxIdeal P).toSubmodule ⊓ rootSpace P μ) μ) (hle hr)
  refine Submodule.iSup_induction _ (motive := fun r ↦ invFormAux P S r y = 0) hr' ?_ (by simp)
    fun r₁ r₂ h₁ h₂ ↦ by rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
  intro μ r hr
  obtain ⟨hr𝔯, hrμ⟩ := Submodule.mem_inf.mp hr
  by_cases hμ : μ = 0
  · subst hμ
    have : r ∈ (maxIdeal P).toSubmodule ⊓ LinearMap.range (h P) :=
      ⟨hr𝔯, mem_range_h_of_mem P hrμ⟩
    rw [maxIdeal_inf_range_h, Submodule.mem_bot] at this
    simp [this]
  induction y using induction_on_rootSpace P with
  | mem ν y hy =>
    by_cases hμν : μ + ν = 0
    · obtain rfl : ν = -μ := eq_neg_of_add_eq_zero_right hμν
      have hmem : ⁅r, y⁆ ∈ (maxIdeal P).toSubmodule ⊓ LinearMap.range (h P) :=
        ⟨lie_mem_left K P.AuxLieAlgebra (maxIdeal P) _ _ hr𝔯, by
          rw [lie_eq_invFormAux_smul P S μ r hrμ y hy]
          exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)⟩
      rw [maxIdeal_inf_range_h, Submodule.mem_bot, lie_eq_invFormAux_smul P S μ r hrμ y hy,
        smul_eq_zero] at hmem
      refine hmem.resolve_right fun h0 ↦ hμ ?_
      rw [← map_zero (h P)] at h0
      simpa using h_injective P h0
    · exact invFormAux_eq_zero P S hrμ hy hμν
  | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]

variable (P S) in
/-- The radical of the form on `𝔤̃(A)` is the maximal ideal `𝔯`. -/
theorem invFormAux_eq_zero_iff_mem_maxIdeal {r : P.AuxLieAlgebra} :
    (∀ y, invFormAux P S r y = 0) ↔ r ∈ maxIdeal P := by
  refine ⟨fun hr ↦ ?_, fun hr y ↦ invFormAux_eq_zero_of_mem_maxIdeal P S hr y⟩
  let I := LieAlgebra.InvariantForm.orthogonal (invFormAux P S) (lieInvariant_invFormAux P S) ⊤
  have hI : I ≤ maxIdeal P := by
    rw [le_maxIdeal_iff, eq_bot_iff]
    rintro _ ⟨hx, ⟨a, rfl⟩⟩
    rw [Submodule.mem_bot, ← map_zero (h P)]
    congr 1
    refine (P.nondegenerate_bilinForm S).2 a fun b ↦ ?_
    have := hx (h P b) (LieSubmodule.mem_top _)
    rwa [invFormAux_h_h] at this
  refine hI fun n _ ↦ ?_
  rw [(isSymm_invFormAux P S).eq]
  exact hr n

end AuxLieAlgebra

end Matrix.Realization

end
