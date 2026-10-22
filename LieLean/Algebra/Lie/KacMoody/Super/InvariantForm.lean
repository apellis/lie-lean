/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.InvariantFormAux
import LieLean.Algebra.Lie.KacMoody.Super.MaxIdeal

/-!
# The supersymmetric form on `G̃(A, τ)`: definition

Let `A = diag(ε) B` be a symmetrizable matrix, `(𝔥, Π, Π^∨)` a realization of `A` over a field
`K` of characteristic zero, `τ` a parity and `(·|·)` the form on `𝔥` of [Kac] §2.1
(`Matrix.Realization.bilinForm`), with `ν : 𝔥 ≃ 𝔥*`. Following the even case
(`LieLean/Algebra/Lie/KacMoody/InvariantFormAux.lean`) we write down a bilinear form on the
auxiliary Lie superalgebra `G̃ = G̃(A, τ) ⊆ U(G̃(A, τ))`:
`(x | y) = (π₀ x | π₀ y) + (π₀ [D x, y] | ρ^∨)`,
where `π₀ : U → 𝔥` is the `𝔥`-component of the weight-zero part, `D` acts on `U_μ` by
`⟨μ, ρ^∨⟩⁻¹` (and by `0` on `U_0`), and `[·,·]` is the super commutator. It is the form of
[Kac78] Prop. 1.4; the remaining properties (`[x, y] = (x | y) ν⁻¹(μ)`, invariance, radical `R`)
are proved in `Super/InvariantFormLie.lean`.

In this file: the weight projections of `U` (`wScale`), the operators `π₀`, `D`, the form
`invForm`, its vanishing on `U_μ × U_ν` for `μ + ν ≠ 0`, its restriction to `𝔥`, its
supersymmetry `(y | x) = (-1)^{|x||y|} (x | y)` on homogeneous elements of `G̃` of opposite
weights, and its values `(eᵢ | fⱼ) = δᵢⱼ εᵢ`.

## Main definitions

* `Matrix.Realization.SuperEnveloping.wScale`: the operator acting on `U_μ` by a scalar `c μ`.
* `Matrix.Realization.SuperEnveloping.hComp`: the projection `π₀ : U → 𝔥`.
* `Matrix.Realization.SuperEnveloping.invForm`: the form on `G̃(A, τ)`.

## Main results

* `Matrix.Realization.SuperEnveloping.invForm_h_h`: the form restricts to the form on `𝔥`.
* `Matrix.Realization.SuperEnveloping.invForm_eq_zero`: `(U_μ | U_ν) = 0` unless `μ + ν = 0`.
* `Matrix.Realization.SuperEnveloping.invForm_swap`: supersymmetry on `G̃`.
* `Matrix.Realization.SuperEnveloping.invForm_e_f`: `(eᵢ | fⱼ) = δᵢⱼ εᵢ`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.4.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.2.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

namespace SuperEnveloping

/-! ### Linearity and antisymmetry of the super commutator -/

lemma superBracket_add_right (x y z : P.SuperEnveloping p) :
    superBracket P p x (y + z) = superBracket P p x y + superBracket P p x z :=
  (superBracketRight P p x).map_add y z

lemma superBracket_smul_right (c : K) (x y : P.SuperEnveloping p) :
    superBracket P p x (c • y) = c • superBracket P p x y :=
  (superBracketRight P p x).map_smul c y

variable {P p} in
/-- Super antisymmetry: `[y, x] = -(-1)^{|x||y|} [x, y]` for homogeneous `x, y`. -/
lemma superBracket_swap [CharZero K] {a b : ZMod 2} {x y : P.SuperEnveloping p}
    (hx : IsHomog P p a x) (hy : IsHomog P p b y) :
    superBracket P p y x = -(zSign K (a * b) • superBracket P p x y) := by
  rw [superBracket_of_isHomog hy hx, superBracket_of_isHomog hx hy, mul_comm b a, smul_sub,
    smul_smul, zSign_mul_self, one_smul, neg_sub]

/-! ### Weight projections -/

open Classical in
theorem isInternal_weightSpace : DirectSum.IsInternal (weightSpace P p) := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_weightSpace P p)
    (iSup_weightSpace P p)

open Classical in
/-- The operator acting on each weight space `U_μ` by the scalar `c μ`. -/
def wScale (c : Dual K H → K) : Module.End K (P.SuperEnveloping p) :=
  DirectSum.toModule K (Dual K H) _ (fun μ ↦ c μ • (weightSpace P p μ).subtype) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace P p))
      (isInternal_weightSpace P p)).symm.toLinearMap

open Classical in
lemma wScale_of_mem (c : Dual K H → K) {μ : Dual K H} {x : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) : wScale P p c x = c μ • x := by
  have : (LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace P p))
      (isInternal_weightSpace P p)).symm x =
        DirectSum.lof K _ (fun μ ↦ weightSpace P p μ) μ ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of (weightSpace P p) μ ⟨x, hx⟩).symm
  simp only [wScale, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    DirectSum.toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply]

/-- Induction along the weight decomposition of `U`. -/
@[elab_as_elim]
lemma induction_on_weightSpace {q : P.SuperEnveloping p → Prop} (x : P.SuperEnveloping p)
    (mem : ∀ μ, ∀ x ∈ weightSpace P p μ, q x) (add : ∀ x y, q x → q y → q (x + y)) : q x :=
  Submodule.iSup_induction (weightSpace P p) (motive := q)
    (by rw [iSup_weightSpace]; trivial) mem (mem 0 0 (Submodule.zero_mem _)) add

lemma wScale_mem_weightSpace {c : Dual K H → K} {μ : Dual K H} (hc : ∀ ν, ν ≠ μ → c ν = 0)
    (x : P.SuperEnveloping p) : wScale P p c x ∈ weightSpace P p μ := by
  induction x using induction_on_weightSpace P p with
  | mem ν x hx =>
    rw [wScale_of_mem P p c hx]
    by_cases hν : ν = μ
    · subst hν; exact Submodule.smul_mem _ _ hx
    · rw [hc ν hν, zero_smul]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

section GTilde

variable [CharZero K]

/-- `G̃` is the sum of its weight spaces. -/
lemma gTilde_le_iSup : gTilde P p ≤ ⨆ μ, gTilde P p ⊓ weightSpace P p μ :=
  le_iSup_inf_weightSpace P p _ fun a _ hy ↦ superBracket_mem_gTilde P p (h_mem_gTilde P p a) hy

/-- Induction along the weight decomposition of `G̃`. -/
@[elab_as_elim]
lemma induction_on_gTilde {q : P.SuperEnveloping p → Prop} {x : P.SuperEnveloping p}
    (hx : x ∈ gTilde P p) (mem : ∀ μ, ∀ x ∈ gTilde P p, x ∈ weightSpace P p μ → q x)
    (add : ∀ x y, q x → q y → q (x + y)) : q x :=
  Submodule.iSup_induction (fun μ ↦ gTilde P p ⊓ weightSpace P p μ) (motive := q)
    (gTilde_le_iSup P p hx) (fun μ x hx ↦ mem μ x hx.1 hx.2)
    (mem 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)) add

lemma wScale_mem_gTilde (c : Dual K H → K) {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) :
    wScale P p c x ∈ gTilde P p := by
  refine induction_on_gTilde P p hx (fun μ x hx hxμ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [wScale_of_mem P p c hxμ]; exact Submodule.smul_mem _ _ hx
  · rw [map_add]; exact add_mem hx hy

end GTilde

/-! ### The projection `π₀ : U → 𝔥` -/

open Classical in
/-- The projection of `U` onto its weight-zero part `U_0`. -/
def proj0 : Module.End K (P.SuperEnveloping p) := wScale P p fun μ ↦ if μ = 0 then 1 else 0

lemma proj0_of_mem_zero {x : P.SuperEnveloping p} (hx : x ∈ weightSpace P p 0) :
    proj0 P p x = x := by
  simp [proj0, wScale_of_mem P p _ hx]

lemma proj0_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) : proj0 P p x = 0 := by
  simp [proj0, wScale_of_mem P p _ hx, hμ]

lemma proj0_mem (x : P.SuperEnveloping p) : proj0 P p x ∈ weightSpace P p 0 :=
  wScale_mem_weightSpace P p (fun ν hν ↦ by simp [hν]) x

/-- A left inverse of the injective map `h : 𝔥 → U`. -/
def hInv : P.SuperEnveloping p →ₗ[K] H :=
  (LinearMap.exists_leftInverse_of_injective (h P p)
    (LinearMap.ker_eq_bot.2 (h_injective P p))).choose

@[simp] lemma hInv_h (a : H) : hInv P p (h P p a) = a :=
  LinearMap.congr_fun (LinearMap.exists_leftInverse_of_injective (h P p)
    (LinearMap.ker_eq_bot.2 (h_injective P p))).choose_spec a

/-- The `𝔥`-component `π₀ x` of the weight-zero part of `x ∈ U`. On `G̃ = ñ₋ ⊕ 𝔥 ⊕ ñ₊` it is the
projection onto `𝔥`. -/
def hComp : P.SuperEnveloping p →ₗ[K] H := hInv P p ∘ₗ proj0 P p

@[simp] lemma hComp_h (a : H) : hComp P p (h P p a) = a := by
  simp [hComp, proj0_of_mem_zero P p (h_mem_weightSpace P p a)]

lemma hComp_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) : hComp P p x = 0 := by
  simp [hComp, proj0_of_mem P p hμ hx]

lemma h_hComp_of_mem_zero [CharZero K] {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hx0 : x ∈ weightSpace P p 0) : h P p (hComp P p x) = x := by
  obtain ⟨a, rfl⟩ : x ∈ LinearMap.range (h P p) := by
    rw [← gTilde_inf_weightSpace_zero P p]; exact ⟨hx, hx0⟩
  rw [hComp_h]

lemma h_hComp [CharZero K] {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) :
    h P p (hComp P p x) = proj0 P p x := by
  have : hComp P p x = hComp P p (proj0 P p x) := by
    simp [hComp, proj0_of_mem_zero P p (proj0_mem P p x)]
  rw [this]
  exact h_hComp_of_mem_zero P p (wScale_mem_gTilde P p _ hx) (proj0_mem P p x)

/-! ### The operator `D` -/

variable [FiniteDimensional K H]

/-- The operator `D` acting on `U_μ` by `⟨μ, ρ^∨⟩⁻¹` (in particular by `0` on `U_0`). -/
def degInv : Module.End K (P.SuperEnveloping p) := wScale P p fun μ ↦ (μ P.rhoCheck)⁻¹

lemma degInv_of_mem {μ : Dual K H} {x : P.SuperEnveloping p} (hx : x ∈ weightSpace P p μ) :
    degInv P p x = (μ P.rhoCheck)⁻¹ • x :=
  wScale_of_mem P p _ hx

lemma degInv_of_mem_zero {x : P.SuperEnveloping p} (hx : x ∈ weightSpace P p 0) :
    degInv P p x = 0 := by
  simp [degInv_of_mem P p hx]

/-! ### The form -/

variable (S : A.Symmetrization)

/-- The form on `G̃(A, τ)`: `(x | y) = (π₀ x | π₀ y) + (π₀ [D x, y] | ρ^∨)`, where `π₀ = hComp`,
`D = degInv` and `[·,·]` is the super commutator. -/
def invForm : LinearMap.BilinForm K (P.SuperEnveloping p) :=
  LinearMap.mk₂ K (fun x y ↦ P.bilinForm S (hComp P p x) (hComp P p y) +
      P.bilinForm S (hComp P p (superBracket P p (degInv P p x) y)) P.rhoCheck)
    (fun x₁ x₂ y ↦ by
      simp only [map_add, LinearMap.add_apply, superBracket_add_left]; ring)
    (fun c x y ↦ by
      simp only [map_smul, LinearMap.smul_apply, superBracket_smul_left, smul_eq_mul]; ring)
    (fun x y₁ y₂ ↦ by
      simp only [map_add, superBracket_add_right, LinearMap.add_apply]; ring)
    (fun c x y ↦ by
      simp only [map_smul, superBracket_smul_right, LinearMap.smul_apply, smul_eq_mul]; ring)

lemma invForm_apply (x y : P.SuperEnveloping p) :
    invForm P p S x y = P.bilinForm S (hComp P p x) (hComp P p y) +
      P.bilinForm S (hComp P p (superBracket P p (degInv P p x) y)) P.rhoCheck := rfl

lemma invForm_of_mem_zero {x : P.SuperEnveloping p} (hx : x ∈ weightSpace P p 0)
    (y : P.SuperEnveloping p) :
    invForm P p S x y = P.bilinForm S (hComp P p x) (hComp P p y) := by
  simp [invForm_apply, degInv_of_mem_zero P p hx, superBracket_zero_left]

lemma invForm_h_left (a : H) (y : P.SuperEnveloping p) :
    invForm P p S (h P p a) y = P.bilinForm S a (hComp P p y) := by
  rw [invForm_of_mem_zero P p S (h_mem_weightSpace P p a), hComp_h]

/-- The form restricts to the form `Matrix.Realization.bilinForm` on `𝔥`. -/
@[simp] theorem invForm_h_h (a b : H) :
    invForm P p S (h P p a) (h P p b) = P.bilinForm S a b := by
  rw [invForm_h_left, hComp_h]

lemma invForm_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) (y : P.SuperEnveloping p) :
    invForm P p S x y =
      (μ P.rhoCheck)⁻¹ * P.bilinForm S (hComp P p (superBracket P p x y)) P.rhoCheck := by
  simp [invForm_apply, hComp_of_mem P p hμ hx, degInv_of_mem P p hx, superBracket_smul_left]

/-- `(U_μ | U_ν) = 0` unless `μ + ν = 0`. -/
theorem invForm_eq_zero {μ ν : Dual K H} {x y : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) (hy : y ∈ weightSpace P p ν) (hμν : μ + ν ≠ 0) :
    invForm P p S x y = 0 := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [zero_add] at hμν
    rw [invForm_of_mem_zero P p S hx, hComp_of_mem P p hμν hy, map_zero]
  · rw [invForm_of_mem P p S hμ hx,
      hComp_of_mem P p hμν (superBracket_mem_weightSpace hx hy)]
    simp

/-! ### Weights and parities of `G̃` -/

section Weights

omit [FiniteDimensional K H]
variable [CharZero K]

/-- `[eᵢ, fⱼ] = δᵢⱼ αᵢ^∨`. -/
lemma superBracket_e_f (i j : ι) :
    superBracket P p (e P p i) (f P p j) = if i = j then h P p (P.coroot i) else 0 := by
  rw [superBracket_of_isHomog (isHomog_e P p i) (isHomog_f P p j), ← superSign_eq_zSign,
    e_mul_f_sub]

omit [CharZero K] in
/-- A nonzero element of `G̃` of weight `μ` has `μ ∈ -(Q₊ \ 0) ∪ {0} ∪ (Q₊ \ 0)`. -/
lemma mem_allWeights {μ : Dual K H} {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxμ : x ∈ weightSpace P p μ) (hx0 : x ≠ 0) : μ ∈ AuxLieAlgebra.allWeights P := by
  by_contra hμ
  have hle : gTilde P p ≤ ⨆ ν ∈ AuxLieAlgebra.allWeights P, weightSpace P p ν := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (nMinus_le_iSup_weightSpace P p).trans (iSup₂_le fun k hk ↦
        le_biSup (fun ν ↦ weightSpace P p ν) (Or.inl (Or.inl ⟨k, hk, rfl⟩)))
    · rintro _ ⟨a, rfl⟩
      exact le_biSup (fun ν ↦ weightSpace P p ν) (Or.inl (Or.inr rfl))
        (h_mem_weightSpace P p a)
    · exact (nPlus_le_iSup_weightSpace P p).trans (iSup₂_le fun k hk ↦
        le_biSup (fun ν ↦ weightSpace P p ν) (Or.inr ⟨k, hk, rfl⟩))
  exact hx0 (Submodule.disjoint_def.1 ((iSupIndep_weightSpace P p).disjoint_biSup hμ) _ hxμ
    (hle hx))

/-- Odd elements of `G̃_0 = 𝔥` vanish. -/
lemma eq_zero_of_isHomog_one {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hx0 : x ∈ weightSpace P p 0) (hxa : IsHomog P p 1 x) : x = 0 := by
  obtain ⟨a, rfl⟩ : x ∈ LinearMap.range (h P p) := by
    rw [← gTilde_inf_weightSpace_zero P p]; exact ⟨hx, hx0⟩
  have h2 : (2 : K) • h P p a = 0 := by
    have := hxa
    rw [IsHomog, parity_h, zSign_one, neg_one_smul] at this
    rw [two_smul]; nth_rw 1 [this]; exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- Induction over the homogeneous elements of `G̃_μ`. -/
lemma induction_homog {μ : Dual K H} {q : P.SuperEnveloping p → Prop} {x : P.SuperEnveloping p}
    (hx : x ∈ gTilde P p) (hxμ : x ∈ weightSpace P p μ)
    (hom : ∀ a, ∀ x ∈ gTilde P p, x ∈ weightSpace P p μ → IsHomog P p a x → q x)
    (add : ∀ x y, q x → q y → q (x + y)) : q x := by
  have hdec : x = (2 : K)⁻¹ • (x + parity P p x) + (2 : K)⁻¹ • (x - parity P p x) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul K x, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]
  rw [hdec]
  have hσ := parity_mem_gTilde P p hx
  have hσμ := parity_mem_weightSpace P p hxμ
  refine add _ _ (hom 0 _ ?_ ?_ ?_) (hom 1 _ ?_ ?_ ?_)
  · exact Submodule.smul_mem _ _ (add_mem hx hσ)
  · exact Submodule.smul_mem _ _ (add_mem hxμ hσμ)
  · rw [IsHomog, map_smul, map_add, parity_parity, zSign_zero, one_smul, add_comm]
  · exact Submodule.smul_mem _ _ (sub_mem hx hσ)
  · exact Submodule.smul_mem _ _ (sub_mem hxμ hσμ)
  · rw [IsHomog, map_smul, map_sub, parity_parity, zSign_one, neg_one_smul, ← smul_neg, neg_sub]

end Weights

section Form

variable [CharZero K]

lemma apply_rhoCheck_ne_zero_of_mem {μ : Dual K H} (hμ : μ ≠ 0) {x : P.SuperEnveloping p}
    (hx : x ∈ gTilde P p) (hxμ : x ∈ weightSpace P p μ) (hx0 : x ≠ 0) : μ P.rhoCheck ≠ 0 :=
  AuxLieAlgebra.apply_rhoCheck_ne_zero P (mem_allWeights P p hx hxμ hx0) hμ

/-- Supersymmetry: `(y | x) = (-1)^{|x||y|} (x | y)` for homogeneous `x, y ∈ G̃` lying in weight
spaces. -/
theorem invForm_swap {μ ν : Dual K H} {a b : ZMod 2} {x y : P.SuperEnveloping p}
    (hx : x ∈ gTilde P p) (hxμ : x ∈ weightSpace P p μ) (hxa : IsHomog P p a x)
    (_hy : y ∈ gTilde P p) (hyν : y ∈ weightSpace P p ν) (hyb : IsHomog P p b y) :
    invForm P p S y x = zSign K (a * b) * invForm P p S x y := by
  by_cases hμν : μ + ν = 0
  · obtain rfl : ν = -μ := eq_neg_of_add_eq_zero_right hμν
    by_cases hμ : μ = 0
    · subst hμ
      rw [neg_zero] at hyν
      rw [invForm_of_mem_zero P p S hyν, invForm_of_mem_zero P p S hxμ,
        (P.isSymm_bilinForm S).eq (hComp P p y)]
      rcases zmod_two_cases a with rfl | rfl
      · rw [zero_mul, zSign_zero, one_mul]
      · rcases zmod_two_cases b with rfl | rfl
        · rw [mul_zero, zSign_zero, one_mul]
        · rw [eq_zero_of_isHomog_one P p hx hxμ hxa]; simp
    · rw [invForm_of_mem P p S (neg_ne_zero.2 hμ) hyν, invForm_of_mem P p S hμ hxμ,
        superBracket_swap hxa hyb]
      simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.neg_apply, inv_neg]
      ring
  · rw [invForm_eq_zero P p S hyν hxμ (by rwa [add_comm]), invForm_eq_zero P p S hxμ hyν hμν,
      mul_zero]

/-- `(eᵢ | fⱼ) = δᵢⱼ εᵢ`. -/
theorem invForm_e_f (i j : ι) :
    invForm P p S (e P p i) (f P p j) = if i = j then (S.ε i : K) else 0 := by
  split_ifs with hij
  · subst hij
    rw [invForm_of_mem P p S (P.linearIndependent_root.ne_zero i) (e_mem_weightSpace P p i),
      superBracket_e_f]
    simp
  · refine invForm_eq_zero P p S (e_mem_weightSpace P p i) (f_mem_weightSpace P p j) fun h0 ↦
      hij (P.linearIndependent_root.injective ?_)
    rwa [← sub_eq_add_neg, sub_eq_zero] at h0

/-! ### The identity `[x, y] = (x | y) ν⁻¹(μ)` -/

/-- The statement `C_μ`: `[x, y] = (x | y) ν⁻¹(μ)` for all `x ∈ G̃_μ` and `y ∈ G̃_{-μ}`. -/
def LieEqForm (μ : Dual K H) : Prop :=
  ∀ x ∈ gTilde P p, x ∈ weightSpace P p μ → ∀ y ∈ gTilde P p, y ∈ weightSpace P p (-μ) →
    superBracket P p x y = invForm P p S x y • h P p ((P.toDual S).symm μ)

variable {P p S}

lemma lieEqForm_of_exists {μ : Dual K H} (hμ : μ ≠ 0)
    (hex : ∀ x ∈ gTilde P p, x ∈ weightSpace P p μ → ∀ y ∈ gTilde P p,
      y ∈ weightSpace P p (-μ) → ∃ c : K, superBracket P p x y = c • h P p ((P.toDual S).symm μ)) :
    LieEqForm P p S μ := by
  intro x hx hxμ y hy hyμ
  obtain ⟨c, hc⟩ := hex x hx hxμ y hy hyμ
  by_cases hx0 : x = 0
  · simp [hx0, superBracket_zero_left]
  have hne := apply_rhoCheck_ne_zero_of_mem P p hμ hx hxμ hx0
  rw [hc, invForm_of_mem P p S hμ hxμ, hc, map_smul, hComp_h, map_smul, LinearMap.smul_apply,
    bilinForm_toDual_symm_left, smul_eq_mul]
  congr 1
  field_simp

variable (P p S) in
lemma lieEqForm_zero : LieEqForm P p S 0 := by
  intro x hx hx0 y _ hy0
  obtain ⟨a, rfl⟩ : x ∈ LinearMap.range (h P p) := by
    rw [← gTilde_inf_weightSpace_zero P p]; exact ⟨hx, hx0⟩
  rw [neg_zero] at hy0
  rw [superBracket_h_of_mem_weightSpace P p a hy0, map_zero, map_zero, smul_zero,
    LinearMap.zero_apply, zero_smul]

variable (S) in
lemma lieEqForm_of_notMem {μ : Dual K H} (hμ : μ ∉ AuxLieAlgebra.allWeights P) :
    LieEqForm P p S μ := by
  intro x hx hxμ y _ _
  obtain rfl : x = 0 := by
    by_contra hx0; exact hμ (mem_allWeights P p hx hxμ hx0)
  simp [superBracket_zero_left]

lemma LieEqForm.neg {μ : Dual K H} (hμ : LieEqForm P p S μ) : LieEqForm P p S (-μ) := by
  intro x hx hxμ y hy hyμ
  rw [neg_neg] at hyμ
  refine induction_homog (q := fun x ↦ superBracket P p x y =
      invForm P p S x y • h P p ((P.toDual S).symm (-μ))) P p hx hxμ
    (fun a x hx hxμ hxa ↦ ?_) (fun x₁ x₂ h₁ h₂ ↦ ?_)
  · refine induction_homog (q := fun y ↦ superBracket P p x y =
        invForm P p S x y • h P p ((P.toDual S).symm (-μ))) P p hy hyμ
      (fun b y hy hyμ hyb ↦ ?_) (fun y₁ y₂ h₁ h₂ ↦ ?_)
    · have := hμ y hy hyμ x hx hxμ
      rw [superBracket_swap hyb hxa, this, invForm_swap P p S hy hyμ hyb hx hxμ hxa, map_neg,
        map_neg, mul_comm b a, mul_smul, smul_neg, smul_neg]
    · rw [superBracket_add_right, h₁, h₂, map_add, add_smul]
  · rw [superBracket_add_left, h₁, h₂, map_add, LinearMap.add_apply, add_smul]

end Form

end SuperEnveloping

end Matrix.Realization
