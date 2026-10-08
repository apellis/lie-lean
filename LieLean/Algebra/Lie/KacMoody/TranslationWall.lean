/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationFacetClosureNonintegral

/-!
# Translation from a wall: the short exact sequence

Let `A` be of finite type, `λ`, `μ` antidominant with `ν = z (λ - μ)` (`z ∈ W`) dominant integral,
and let `α = v αᵢ > 0` be a positive root with `⟨μ + ρ, α^∨⟩ = 0`, `⟨λ + ρ, α^∨⟩ ≠ 0`, such that
`±α` are the only roots orthogonal to `μ + ρ` (`μ♮` lies on the single wall `H_α`); then the
stabilizer of `μ` for the dot action is `{1, s}`, `s = s_α`. For `w ∈ W` with `w α > 0` there is
a short exact sequence

`0 → M(ws·λ) → T_μ^λ M(w·μ) → M(w·λ) → 0`

(Humphreys, GSM 94, Theorem 7.14 (a)).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.exists_verma_lieSubmodule_of_extension`: a module with a
  two-step standard filtration `N ⊆ T`, `N ≅ M(a)`, `T/N ≅ M(b)` with `b ≰ a`, also has a
  submodule `S ≅ M(b)` with `T/S ≅ M(a)` (the step of Humphreys, GSM 94, Prop. 3.7 (a) used for
  Theorem 7.14 (a)).
* `Matrix.Realization.KacMoodyAlgebra.translation_verma_shortExact_of_isAntidominant`:
  Humphreys, GSM 94, Theorem 7.14 (a), for arbitrary (not necessarily integral) weights.

## Proof

The filtration of `T_μ^λ M(w·μ)` from Theorem 7.12
(`exists_translation_verma_filtration_of_isAntidominant`) has exactly two Verma steps,
`M(w·λ)` and `M(ws·λ)`, and `ws·λ - w·λ = -⟨λ + ρ, α^∨⟩ wα ∈ Q₊ \ 0`. If `M(w·λ)` is the bottom
step, the vector of weight `ws·λ` lifting the generator of the top step is primitive (no weight
above it occurs), and the morphism `M(ws·λ) → T_μ^λ M(w·μ)` it defines splits the projection to
the top step. In either case `M(ws·λ)` is a submodule with quotient `M(w·λ)`. Humphreys deduces
this from Prop. 3.7 (a); the argument here is our own.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.7, §7.14.
-/

noncomputable section

open Module LieModule TensorProduct

namespace LieSubmodule

variable {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup V] [Module K V]
  [LieRingModule L V] [LieModule K L V]

/-- A monotone family of submodules is constant across an interval of zero steps. -/
theorem eq_of_forall_step_eq_bot {n : ℕ} (F : Fin (n + 1) → LieSubmodule K L V)
    (hF : Monotone F) {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ n)
    (hstep : ∀ j : Fin n, p ≤ j.val → j.val < q →
      (F j.succ).map (Quotient.mk' (F j.castSucc)) = ⊥) :
    F ⟨p, by omega⟩ = F ⟨q, by omega⟩ := by
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    rw [ih (by omega) fun j hj hjq ↦ hstep j hj (by omega)]
    have h := hstep ⟨q, by omega⟩ hpq (by simp)
    exact (le_antisymm ((map_mk'_eq_bot_iff _ _).mp h)
      (hF (Fin.castSucc_le_succ _))).symm

end LieSubmodule

namespace Matrix.Realization.KacMoodyAlgebra

section Extension

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

local notation "𝔤" => KacMoodyAlgebra P

/-- **Reordering a two-step standard filtration** (cf. Humphreys, GSM 94, Prop. 3.7 (a)). Let
`X` be the sum of its weight spaces and `N ≤ T` submodules with `N ≅ M(a)` and `T/N ≅ M(b)`
(the image of `T` in `X/N`), where `b ∉ a - Q₊`. Then `T` has a submodule `S ≅ M(b)` with
`T/S ≅ M(a)`. -/
theorem exists_verma_lieSubmodule_of_extension
    (hX : ⨆ μ, weightSpaceOfMap X (h P) μ = ⊤) {N T : LieSubmodule K 𝔤 X} (hNT : N ≤ T)
    {a b : Dual K H} (eN : VermaModule P a ≃ₗ⁅K,𝔤⁆ N)
    (eQ : VermaModule P b ≃ₗ⁅K,𝔤⁆ T.map (LieSubmodule.Quotient.mk' N)) (hab : b ∉ cone P a) :
    ∃ S : LieSubmodule K 𝔤 X, S ≤ T ∧ Nonempty (VermaModule P b ≃ₗ⁅K,𝔤⁆ S) ∧
      Nonempty (VermaModule P a ≃ₗ⁅K,𝔤⁆ T.map (LieSubmodule.Quotient.mk' S)) := by
  classical
  -- the generator of the top step and a lift `x ∈ T` of weight `b`
  set y : X ⧸ N := (eQ (VermaModule.hwv P b) : X ⧸ N) with hy
  have hyw : y ∈ weightSpaceOfMap (X ⧸ N) (h P) b :=
    mem_weightSpaceOfMap_lieSubmodule_iff.mp (map_mem_weightSpaceOfMap P
      eQ.toLieModuleHom (VermaModule.hwv_mem_weightSpace P b))
  obtain ⟨x, hxw, hxy⟩ := (map_weightSpaceOfMap_quotient P N hX b).ge hyw
  change LieSubmodule.Quotient.mk' N x = y at hxy
  have hxT : x ∈ T := by
    obtain ⟨t, htT, ht⟩ := (LieSubmodule.mem_map _).mp (eQ (VermaModule.hwv P b)).2
    have hxt : x - t ∈ N := by
      rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub, hxy, ht, sub_self]
    have := T.add_mem (hNT hxt) htT
    rwa [sub_add_cancel] at this
  -- `x` is primitive: no weight `b + αᵢ` occurs in `N ≅ M(a)` or in `T/N ≅ M(b)`
  have hprim : ∀ i, ⁅e P i, x⁆ = 0 := by
    intro i
    have hey : ⁅e P i, eQ (VermaModule.hwv P b)⁆ = 0 := by
      have := eQ.toLieModuleHom.map_lie (e P i) (VermaModule.hwv P b)
      rw [VermaModule.lie_e_hwv, map_zero] at this
      exact this.symm
    have hmem : ⁅e P i, x⁆ ∈ N := by
      rw [← LieSubmodule.Quotient.mk_eq_zero, LieModuleHom.map_lie, hxy, hy,
        ← LieSubmodule.coe_bracket, hey, LieSubmodule.coe_zero]
    have hw : ⁅e P i, x⁆ ∈ weightSpaceOfMap X (h P) (b + P.root i) := by
      simpa using toEnd_e_mem_weightSpace (P := P) (V := X) i hxw
    set n : N := ⟨_, hmem⟩
    have hn : n ∈ weightSpaceOfMap N (h P) (b + P.root i) :=
      mem_weightSpaceOfMap_lieSubmodule_iff.mpr hw
    have hn' := map_mem_weightSpaceOfMap P eN.symm.toLieModuleHom hn
    rw [show weightSpaceOfMap (VermaModule P a) (h P) (b + P.root i) = ⊥ from
      VermaModule.weightSpace_eq_bot P a fun k hk hbk ↦ hab ⟨k + Pi.single i 1,
        add_nonneg hk (Pi.single_nonneg.mpr zero_le_one), by
          rw [map_add, rootOf_single, ← sub_sub, ← hbk, add_sub_cancel_right]⟩] at hn'
    have h0 : n = 0 := by
      have := (Submodule.mem_bot K).mp hn'
      simpa using this
    exact congrArg Subtype.val h0
  -- the morphism `φ : M(b) → T`, `v_b ↦ x`
  let xT : T := ⟨x, hxT⟩
  have hxTw : xT ∈ weightSpaceOfMap T (h P) b := mem_weightSpaceOfMap_lieSubmodule_iff.mpr hxw
  have hxTe : ∀ i, ⁅e P i, xT⁆ = 0 := fun i ↦ Subtype.ext (by
    rw [LieSubmodule.coe_bracket]; exact hprim i)
  let φ : VermaModule P b →ₗ⁅K,𝔤⁆ T := (VermaModule.homEquiv P T b).symm
    ⟨xT, mem_primitiveVectors.mpr ⟨hxTw, hxTe⟩⟩
  have hφ : φ (VermaModule.hwv P b) = xT :=
    congrArg Subtype.val ((VermaModule.homEquiv P T b).apply_symm_apply
      ⟨xT, mem_primitiveVectors.mpr ⟨hxTw, hxTe⟩⟩)
  -- the projection `π : T → T/N` and `π ∘ φ = eQ`
  let π : T →ₗ⁅K,𝔤⁆ T.map (LieSubmodule.Quotient.mk' N) :=
    LieModuleHom.codRestrict _ ((LieSubmodule.Quotient.mk' N).comp T.incl)
      (fun t ↦ (LieSubmodule.mem_map _).mpr ⟨t, t.2, rfl⟩)
  have hπ : ∀ t : T, (π t : X ⧸ N) = LieSubmodule.Quotient.mk' N (t : X) := fun _ ↦ rfl
  have hπφ : π.comp φ = (eQ : VermaModule P b →ₗ⁅K,𝔤⁆ _) := by
    refine VermaModule.hom_ext P b (Subtype.ext ?_)
    rw [LieModuleHom.comp_apply, hπ, hφ]
    exact hxy
  have hπφ' : ∀ z, π (φ z) = eQ z := fun z ↦ by
    rw [← LieModuleHom.comp_apply, hπφ]; rfl
  have hφinj : Function.Injective φ := fun z z' hzz' ↦ eQ.injective (by
    rw [← hπφ', ← hπφ', hzz'])
  -- `S` is the image of `φ`
  let φX : VermaModule P b →ₗ⁅K,𝔤⁆ X := T.incl.comp φ
  have hφXinj : Function.Injective φX := fun z z' h ↦ hφinj (Subtype.ext h)
  refine ⟨φX.range, ?_, ⟨LieModuleEquiv.ofBijective
    (LieModuleHom.codRestrict φX.range φX fun z ↦ (LieModuleHom.mem_range _ _).mpr ⟨z, rfl⟩)
    ⟨fun z z' h ↦ hφXinj (congrArg (fun q : φX.range ↦ (q : X)) h), ?_⟩⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact (φ z).2
  · rintro ⟨_, z, rfl⟩
    exact ⟨z, rfl⟩
  -- `T/S ≅ M(a)` via `M(a) ≅ N → T/S`
  let θ : VermaModule P a →ₗ⁅K,𝔤⁆ T.map (LieSubmodule.Quotient.mk' φX.range) :=
    LieModuleHom.codRestrict _ ((LieSubmodule.Quotient.mk' φX.range).comp
      (N.incl.comp (eN : VermaModule P a →ₗ⁅K,𝔤⁆ N)))
      (fun m ↦ (LieSubmodule.mem_map _).mpr ⟨(eN m : X), hNT (eN m).2, rfl⟩)
  have hθ : ∀ m, (θ m : X ⧸ φX.range) = LieSubmodule.Quotient.mk' φX.range (eN m : X) :=
    fun _ ↦ rfl
  refine ⟨LieModuleEquiv.ofBijective θ ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : ((θ m : X ⧸ φX.range)) = 0 := by rw [hm]; rfl
    rw [hθ, LieSubmodule.Quotient.mk_eq_zero] at h1
    obtain ⟨z, hz⟩ := (LieModuleHom.mem_range _ _).mp h1
    have hz0 : eQ z = 0 := by
      rw [← hπφ']
      refine Subtype.ext ?_
      rw [hπ]
      change LieSubmodule.Quotient.mk' N (φX z) = 0
      rw [hz, LieSubmodule.Quotient.mk_eq_zero]
      exact (eN m).2
    have hz' : z = 0 := by simpa using hz0
    have : (eN m : X) = 0 := by rw [← hz, hz', map_zero]
    have : eN m = 0 := Subtype.ext this
    simpa using this
  · rintro ⟨q, hq⟩
    obtain ⟨t, htT, rfl⟩ := (LieSubmodule.mem_map _).mp hq
    set z := eQ.symm (π ⟨t, htT⟩)
    have hmem : t - φX z ∈ N := by
      rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub]
      have h1 : LieSubmodule.Quotient.mk' N (φX z) = (eQ z : X ⧸ N) := by
        rw [← hπφ' z]; rfl
      rw [h1, show z = eQ.symm (π ⟨t, htT⟩) from rfl, LieModuleEquiv.apply_symm_apply, hπ,
        sub_self]
    refine ⟨eN.symm ⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [hθ, LieModuleEquiv.apply_symm_apply]
    change LieSubmodule.Quotient.mk' φX.range (t - φX z) = _
    rw [map_sub, (LieSubmodule.Quotient.mk_eq_zero _).mpr ((LieModuleHom.mem_range _ _).mpr
      ⟨z, rfl⟩), sub_zero]

end Extension

/-! ### Two-step filtrations -/

section TwoStep

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

local notation "𝔤" => KacMoodyAlgebra P

/-- A filtration `0 = F₀ ≤ ⋯ ≤ Fₙ` whose only nonzero steps are `j₁ < j₂`, with steps
`≅ M(a)` and `≅ M(b)`, has `N = F_{j₁+1} ≅ M(a)` and `Fₙ/N ≅ M(b)`. -/
theorem exists_of_two_steps {n : ℕ} (F : Fin (n + 1) → LieSubmodule K 𝔤 X) (hF : Monotone F)
    (hF0 : F 0 = ⊥) {j₁ j₂ : Fin n} (h12 : j₁ < j₂)
    (hzero : ∀ j, j ≠ j₁ → j ≠ j₂ →
      (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) = ⊥) {a b : Dual K H}
    (e₁ : Nonempty (VermaModule P a ≃ₗ⁅K,𝔤⁆
      (F j₁.succ).map (LieSubmodule.Quotient.mk' (F j₁.castSucc))))
    (e₂ : Nonempty (VermaModule P b ≃ₗ⁅K,𝔤⁆
      (F j₂.succ).map (LieSubmodule.Quotient.mk' (F j₂.castSucc)))) :
    F j₁.succ ≤ F (Fin.last n) ∧ Nonempty (VermaModule P a ≃ₗ⁅K,𝔤⁆ F j₁.succ) ∧
      Nonempty (VermaModule P b ≃ₗ⁅K,𝔤⁆
        (F (Fin.last n)).map (LieSubmodule.Quotient.mk' (F j₁.succ))) := by
  have h12' : j₁.val < j₂.val := h12
  have hc1 : F j₁.castSucc = ⊥ := by
    rw [← hF0]
    exact (LieSubmodule.eq_of_forall_step_eq_bot F hF (Nat.zero_le j₁.val) (by omega)
      fun j _ hj ↦ hzero j (fun h ↦ by rw [h] at hj; omega)
        (fun h ↦ by rw [h] at hj; omega)).symm
  have hc2 : F j₂.castSucc = F j₁.succ := by
    exact (LieSubmodule.eq_of_forall_step_eq_bot F hF (p := j₁.val + 1) (q := j₂.val)
      (by omega) (by omega)
      fun j hj hj' ↦ hzero j (fun h ↦ by rw [h] at hj; omega)
        (fun h ↦ by rw [h] at hj'; omega)).symm
  have hc3 : F j₂.succ = F (Fin.last n) :=
    LieSubmodule.eq_of_forall_step_eq_bot F hF (p := j₂.val + 1) (q := n) (by omega) le_rfl
      fun j hj _ ↦ hzero j (fun h ↦ by rw [h] at hj; omega) (fun h ↦ by rw [h] at hj; omega)
  refine ⟨hc3 ▸ hc2 ▸ hF (Fin.castSucc_le_succ j₂), ?_, ?_⟩
  · rw [hc1] at e₁
    obtain ⟨e₁⟩ := e₁
    exact ⟨e₁.trans (LieSubmodule.mapMkBotEquiv _).symm⟩
  · rwa [hc2, hc3] at e₂

end TwoStep

section RootLemmas

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsFiniteCartan)

include hA in
/-- In finite type the coroot of a real root is determined by the root: if `v' αᵢ' = v αᵢ`, then
`⟨x, (v' αᵢ')^∨⟩ = ⟨x, (v αᵢ)^∨⟩` (both equal `2 (x | β) / (β | β)` for a `W`-invariant form). -/
lemma _root_.Matrix.Realization.corootPairing_eq_of_apply_root_eq
    {v v' : P.weylGroup hA.isGeneralizedCartan} {i i' : ι}
    (h : (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (x : Dual K H) :
    P.corootPairing hA.isGeneralizedCartan x v' i' =
      P.corootPairing hA.isGeneralizedCartan x v i := by
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (Matrix.diagonal d * A).IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  have hform : ∀ (u : P.weylGroup hA.isGeneralizedCartan) (j : ι) (y : Dual K H),
      P.dualBilinForm S y ((u : Dual K H ≃ₗ[K] Dual K H) (P.root j)) =
        P.corootPairing hA.isGeneralizedCartan y u j / S.ε j := by
    intro u j y
    rw [← P.dualBilinForm_weylGroup hA.isGeneralizedCartan S (u⁻¹).2, inv_apply_apply,
      dualBilinForm_root_right]
    rfl
  have hself : ∀ (u : P.weylGroup hA.isGeneralizedCartan) (j : ι),
      P.corootPairing hA.isGeneralizedCartan ((u : Dual K H ≃ₗ[K] Dual K H) (P.root j)) u j =
        2 := by
    intro u j
    rw [corootPairing, inv_apply_apply, P.root_coroot_self hA.isGeneralizedCartan]
  have hne : ∀ j, (S.ε j : K) ≠ 0 := fun j ↦ by exact_mod_cast S.ε_ne_zero j
  have hε : (S.ε i' : K) = S.ε i := by
    have h1 := hform v i ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    have h2 := hform v' i' ((v' : Dual K H ≃ₗ[K] Dual K H) (P.root i'))
    rw [hself] at h1 h2
    rw [h] at h2
    have e : (2 : K) / S.ε i' = 2 / S.ε i := h2.symm.trans h1
    field_simp [hne i, hne i'] at e
    exact e.symm
  have h1 := hform v i x
  have h2 := hform v' i' x
  rw [h] at h2
  rw [hε] at h2
  exact (div_left_inj' (hne i)).mp (h2.symm.trans h1)

include hA in
/-- The reflection in a real root only depends on the root up to sign. -/
lemma _root_.Matrix.Realization.reflectionOf_eq_of_apply_root_eq
    {v v' : P.weylGroup hA.isGeneralizedCartan} {i i' : ι}
    (h : (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) :
    P.reflectionOf hA.isGeneralizedCartan v' i' = P.reflectionOf hA.isGeneralizedCartan v i := by
  rcases h with h | h
  · refine Subtype.ext (LinearEquiv.ext fun x ↦ ?_)
    rw [reflectionOf_apply', reflectionOf_apply', corootPairing_eq_of_apply_root_eq hA h, h]
  · have h' : ((v' * (P.coxeterSystem hA.isGeneralizedCartan).simple i' :
        P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) (P.root i') =
        (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) := by
      rw [mul_simple_apply_root, h, neg_neg]
    refine Subtype.ext (LinearEquiv.ext fun x ↦ ?_)
    rw [reflectionOf_apply', reflectionOf_apply', ← corootPairing_eq_of_apply_root_eq hA h',
      corootPairing_mul_simple, h]
    module

end RootLemmas

/-! ### Translation from a wall -/

section Wall

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

open VermaModule

omit [CharZero K] [FiniteDimensional K H] in
include hA in
/-- If `ν = z (λ - μ)` is integral (`z ∈ W`), then so is `λ - μ`. -/
lemma integral_sub_of_apply_eq {lam μ ν : Dual K H} (hν : P.IsDominantIntegral ν)
    {z : Dual K H ≃ₗ[K] Dual K H} (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (lam - μ) = ν) :
    ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n := by
  have hνint : ∀ i, ∃ n : ℤ, ν (P.coroot i) = n := fun i ↦ by
    obtain ⟨n, hn⟩ := hν i; exact ⟨n, by rw [hn, Int.cast_natCast]⟩
  intro j
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA.isGeneralizedCartan (inv_mem hz) hνint
  obtain ⟨n, hn⟩ := hνint j
  have e : (lam + P.rho) - (μ + P.rho) = z⁻¹ ν := by
    rw [add_sub_add_right_eq_sub, ← hzν]
    exact (z.symm_apply_apply _).symm
  refine ⟨n + (A *ᵥ k) j, ?_⟩
  rw [e, hk, LinearMap.add_apply, hn, rootOf_apply_coroot]
  push_cast
  ring

omit [FiniteDimensional K H] in
include hA in
/-- If every reflection fixing `μ + ρ` is `s = s_α`, the stabilizer of `μ` for the dot action
is `{1, s}`. -/
lemma eq_one_or_eq_of_weylDot_eq {μ : Dual K H} {v : P.weylGroup hA.isGeneralizedCartan} {i : ι}
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      P.reflectionOf hA.isGeneralizedCartan v' i' = P.reflectionOf hA.isGeneralizedCartan v i)
    {w' : P.weylGroup hA.isGeneralizedCartan}
    (hw' : P.weylDot hA.isGeneralizedCartan w' μ = μ) :
    w' = 1 ∨ w' = P.reflectionOf hA.isGeneralizedCartan v i := by
  have hfix : (w' : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) = μ + P.rho := by
    have := congrArg (· + P.rho) hw'
    simpa [weylDot] using this
  have hmem := (apply_eq_self_iff_mem_closure_reflectionOf hA (μ + P.rho) w').mp hfix
  have hle : Subgroup.closure {s | ∃ v' i', P.corootPairing hA.isGeneralizedCartan
      (μ + P.rho) v' i' = 0 ∧ P.reflectionOf hA.isGeneralizedCartan v' i' = s} ≤
      Subgroup.closure {P.reflectionOf hA.isGeneralizedCartan v i} := by
    refine Subgroup.closure_mono ?_
    rintro _ ⟨v', i', h0, rfl⟩
    exact hwall v' i' h0
  set s := P.reflectionOf hA.isGeneralizedCartan v i
  have hss : s * s = 1 := reflectionOf_mul_self v i
  have key : ∀ y ∈ Subgroup.closure {s}, y = 1 ∨ y = s := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact Or.inr hx
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Or.inl (one_mul 1)
      · exact Or.inr (one_mul _)
      · exact Or.inr (mul_one _)
      · exact Or.inl hss
    | inv x _ hx =>
      rcases hx with rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (inv_eq_of_mul_eq_one_left hss)
  exact key _ (hle hmem)

omit [FiniteDimensional K H] in
include hA in
/-- With `α = v αᵢ > 0`, `⟨λ + ρ, α^∨⟩ ∈ ℤ_{<0}` and `w α > 0`: `ws·λ - w·λ ∈ Q₊ \ 0`, so
`ws·λ ∉ w·λ - Q₊`. -/
lemma weylDot_mul_reflectionOf_notMem_cone {lam : Dual K H}
    {v w : P.weylGroup hA.isGeneralizedCartan} {i : ι} {n : ℤ} (hn : n < 0)
    (hpair : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n)
    (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i) :
    P.weylDot hA.isGeneralizedCartan (w * P.reflectionOf hA.isGeneralizedCartan v i) lam ∉
      cone P (P.weylDot hA.isGeneralizedCartan w lam) := by
  obtain ⟨l, hl, hwl⟩ := hw
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearEquiv.map_eq_zero_iff] at hwl
    exact P.linearIndependent_root.ne_zero i hwl
  have he : P.weylDot hA.isGeneralizedCartan (w * P.reflectionOf hA.isGeneralizedCartan v i)
      lam = P.weylDot hA.isGeneralizedCartan w lam - P.rootOf (n • l) := by
    simp only [weylDot]
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, reflectionOf_apply', hpair, map_sub, map_smul,
      ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hwl, map_zsmul, ← Int.cast_smul_eq_zsmul K]
    abel
  rintro ⟨k, hk, hke⟩
  rw [he, sub_right_inj] at hke
  have hkl := P.rootOf_injective hke
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hl0
  have h1 : 0 ≤ k j := hk j
  have h2 : (n • l) j = k j := congrFun hkl j
  have h3 : 0 < l j := lt_of_le_of_ne (hl j) (Ne.symm hj)
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  have := mul_neg_of_neg_of_pos hn h3
  linarith

variable [IsAlgClosed K]

include hA in
/-- **Translation from a wall: the short exact sequence** (Humphreys, GSM 94, Theorem 7.14 (a),
for arbitrary weights). Let `λ`, `μ` be antidominant, `ν = z (λ - μ)` (`z ∈ W`) dominant integral,
`α = v αᵢ` a positive root with `⟨μ + ρ, α^∨⟩ = 0` and `⟨λ + ρ, α^∨⟩ ≠ 0`, and suppose `±α` are
the only roots orthogonal to `μ + ρ` (`μ♮` lies on the single wall `H_α`; Humphreys assumes
moreover that `λ` is regular, which is not needed here). Let `s = s_α`. For `w ∈ W` with
`w α > 0`, the `χ_λ`-block `T_μ^λ M(w·μ)` of
`M(w·μ) ⊗ L(ν)` has a submodule `S ≅ M(ws·λ)` with quotient `≅ M(w·λ)`:
`0 → M(ws·λ) → T_μ^λ M(w·μ) → M(w·λ) → 0`. Humphreys states this for `w ∈ W_[λ]`. -/
theorem translation_verma_shortExact_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i) :
    ∃ S : LieSubmodule K 𝔤
        (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ⊗[K] IrreducibleModule P ν),
      S ≤ centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ⊗[K]
        IrreducibleModule P ν) (centralCharacter P lam) ∧
      Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan
        (w * P.reflectionOf hA.isGeneralizedCartan v i) lam) ≃ₗ⁅K,𝔤⁆ S) ∧
      Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) ≃ₗ⁅K,𝔤⁆
        (centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ⊗[K]
          IrreducibleModule P ν) (centralCharacter P lam)).map
            (LieSubmodule.Quotient.mk' S)) := by
  classical
  set s := P.reflectionOf hA.isGeneralizedCartan v i with hs
  set a := P.weylDot hA.isGeneralizedCartan w lam with ha
  set b := P.weylDot hA.isGeneralizedCartan (w * s) lam with hb
  -- `⟨λ + ρ, α^∨⟩ ∈ ℤ_{<0}` and `b ∉ a - Q₊`
  have hint := integral_sub_of_apply_eq hA hν hz hzν
  obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hint v i).mpr ⟨0, by rw [Int.cast_zero]; exact hμα⟩
  change P.corootPairing _ (lam + P.rho) v i = n at hn
  have hn0 : n < 0 := lt_of_le_of_ne (hlam v i hv n hn) (by rintro rfl; exact hlamα (by simp [hn]))
  have hab : b ∉ cone P a := weylDot_mul_reflectionOf_notMem_cone hA hn0 hn hw
  have hne : a ≠ b := fun h ↦ hab (h ▸ mem_cone_self a)
  -- the filtration of Theorem 7.12 and its two Verma steps
  obtain ⟨N, F, x, S, hmono, hF0, hFlast, hiso, hzero, hbij⟩ :=
    exists_translation_verma_filtration_of_isAntidominant hA hlam hμ hν hz hzν w
  have hsμ : P.weylDot hA.isGeneralizedCartan s μ = μ := by
    simp only [weylDot, hs, reflectionOf_apply', hμα, zero_smul, sub_zero, add_sub_cancel_right]
  obtain ⟨j₁, hj₁, hxa⟩ := hbij.surjOn ⟨1, by simp [weylDot], by rw [mul_one]⟩
  obtain ⟨j₂, hj₂, hxb⟩ := hbij.surjOn ⟨s, hsμ, rfl⟩
  have hS : ∀ j ∈ S, j = j₁ ∨ j = j₂ := by
    intro j hj
    obtain ⟨w', hw', hxj⟩ := hbij.mapsTo hj
    rcases eq_one_or_eq_of_weylDot_eq hA
      (fun v' i' h0 ↦ reflectionOf_eq_of_apply_root_eq hA (hwall v' i' h0)) hw' with rfl | rfl
    · left
      exact hbij.injOn hj hj₁ (by rw [hxj, mul_one, hxa])
    · right
      exact hbij.injOn hj hj₂ (by rw [hxj, hxb])
  have h12 : j₁ ≠ j₂ := by
    rintro rfl
    exact hne (hxa.symm.trans hxb)
  have hzero' : ∀ j, j ≠ j₁ → j ≠ j₂ →
      (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) = ⊥ := fun j h1 h2 ↦
    hzero j fun hj ↦ (hS j hj).elim h1 h2
  have hX : ⨆ μ', weightSpaceOfMap
      (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ⊗[K] IrreducibleModule P ν) (h P)
        μ' = ⊤ :=
    ((VermaModule.isCategoryO P _).tensorProduct
      (IrreducibleModule.isCategoryO P ν)).iSup_weightSpaceOfMap_eq_top
  rcases lt_or_gt_of_ne h12 with hlt | hlt
  · -- `M(w·λ)` at the bottom: reorder
    have e₁ := hiso j₁ hj₁
    have e₂ := hiso j₂ hj₂
    rw [hxa] at e₁
    rw [hxb] at e₂
    obtain ⟨hle, ⟨eN⟩, ⟨eQ⟩⟩ := exists_of_two_steps F hmono hF0 hlt hzero' e₁ e₂
    rw [hFlast] at hle eQ
    exact exists_verma_lieSubmodule_of_extension hX hle eN eQ hab
  · -- `M(ws·λ)` at the bottom
    have e₁ := hiso j₂ hj₂
    have e₂ := hiso j₁ hj₁
    rw [hxb] at e₁
    rw [hxa] at e₂
    obtain ⟨hle, eN, eQ⟩ := exists_of_two_steps F hmono hF0 hlt
      (fun j h1 h2 ↦ hzero' j h2 h1) e₁ e₂
    rw [hFlast] at hle eQ
    exact ⟨_, hle, eN, eQ⟩

end Wall

end Matrix.Realization.KacMoodyAlgebra
