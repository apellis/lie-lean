/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Stability
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Towards Littelmann's isomorphism theorem

Littelmann's isomorphism theorem ([Lit95] §7 (check)) states that for two paths `π, π'` with
image in the dominant chamber and `π(1) = π'(1)`, the crystals `B(π)` and `B(π')` are isomorphic,
by the unique isomorphism sending `π` to `π'`. This file sets up the statement
(`LittelmannPath.ComponentIso`) and the abstract tools used to prove instances of it, and proves
it in the cases available so far.

## Main definitions

* `Crystal.IsHighestWeight C b`: all `ẽᵢ b = 0`.
* `Crystal.fWord C l b`: `f̃_{i₁} ⋯ f̃_{iₖ} b` for a word `l = [i₁, …, iₖ]`.
* `Crystal.Equiv.ofInjective`: an injective strict morphism is an isomorphism onto its image.
* `Crystal.Equiv.restrictCongr`, `Crystal.Equiv.restrictClosure`: restrictions of isomorphisms
  to stable subsets and to connected components.
* `LittelmannPath.ComponentIso π π'`: the conclusion of Littelmann's isomorphism theorem: an
  isomorphism of crystals `B(π) ≅ B(π')` sending `π` to `π'`.
* `LittelmannPath.reparam π τ`: the reparametrization `π ∘ τ` of a path by an order automorphism
  `τ` of the line fixing `0` and `1`.

## Main results

* `Crystal.exists_isHighestWeight_fWord`: in a crystal with a height function which decreases
  under the `ẽᵢ`, every element is `f̃_{i₁} ⋯ f̃_{iₖ} b` for a highest weight element `b`.
* `Crystal.StrictHom.injective`: a strict morphism out of such a crystal with a unique highest
  weight element is injective.
* `Crystal.StrictHom.range_eq_closure`: its image is the connected component of the image of the
  highest weight element.
* `Matrix.Realization.componentIso_straightLine_iff`: for a dominant integral weight `λ` and any
  path `π`, `B(π_λ) ≅ B(π)` (with `π_λ ↦ π`) if and only if there is a strict morphism
  `B(π_λ) → {paths}` sending `π_λ` to `π`. So to prove Littelmann's isomorphism theorem for `π`
  it suffices to construct such a morphism; injectivity is automatic.
* `LittelmannPath.reparamEquiv`: reparametrization is an automorphism of the crystal of all
  paths; hence `LittelmannPath.componentIso_reparam`: `B(π) ≅ B(π ∘ τ)`. This is the case of the
  isomorphism theorem which Littelmann's convention of paths modulo reparametrization makes
  tautological; for our parametrized paths it is a theorem.

## What is not proved

The general isomorphism theorem, even for the dominant concatenations `π_λ * η` needed for the
crystal-level Littlewood–Richardson decomposition (see
`LieLean.RepresentationTheory.Crystal.Path.Decomposition`), is not proved. Its content is that the
connected component of a dominant path contains no other dominant path (equivalently, that the
set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ`), together with the independence of the
resulting crystal structure from `π`. For straight lines this is
`Matrix.Realization.component_straightLine_eq_fOrbit` (via Lakshmibai–Seshadri paths), whose
proof uses that all paths of `B(π_λ)` have their directions in the single orbit `Wλ`; this fails
for general dominant paths. A characters-only argument cannot work: the character of any
connected component of `B(λ) ⊗ B(μ)` is `∑ ch L(ν)` over the highest weight elements it contains
(`Matrix.Realization.setCharacter_component_concat_eq_hsum`), whatever their number, so the
characters do not see whether two highest weight elements lie in the same component. A natural
route (which we believe to be close to Littelmann's, [Lit95] §4–7 (check); we could not consult
the source) is a theory of Lakshmibai–Seshadri type paths "of shape `π`" for an arbitrary
dominant path `π` (pieces of `π` twisted by Weyl group elements, with chain conditions),
generalizing `LittelmannPath.LSData`; in finite type an alternative is the Pitman transform
`P_{w₀}` of [BBO], which requires the braid relations for Pitman transforms.

## References

* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
* [BBO] P. Biane, P. Bougerol, N. O'Connell, *Littelmann paths and Brownian paths*, Duke Math. J.
  **130** (2005), 127–167.
-/

open Set Module

/-! ### Highest weight elements and strict morphisms -/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B₁ B₂ : Type*}
  (C : Crystal D B) {C₁ : Crystal D B₁} {C₂ : Crystal D B₂}

/-- A highest weight element of a crystal: all `ẽᵢ b = 0`. -/
def IsHighestWeight (b : B) : Prop := ∀ i, C.e i b = none

/-- `fWord [i₁, …, iₖ] b = f̃_{i₁} ⋯ f̃_{iₖ} b` (`none` if some step gives `0`). -/
def fWord : List ι → B → Option B
  | [], b => some b
  | i :: l, b => (fWord l b).bind (C.f i)

@[simp] lemma fWord_nil (b : B) : C.fWord [] b = some b := rfl

lemma fWord_cons (i : ι) (l : List ι) (b : B) :
    C.fWord (i :: l) b = (C.fWord l b).bind (C.f i) := rfl

variable {C}

lemma mem_closure_of_fWord_eq_some {l : List ι} {b b' : B} (h : C.fWord l b = some b') :
    b' ∈ C.closure {b} := by
  induction l generalizing b' with
  | nil =>
    cases h
    exact subset_closure {b} rfl
  | cons i l ih =>
    obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp h
    exact (isStable_closure {b}).f_mem i c b' (ih hc) hf

variable (C) in
/-- In a crystal with a height function `ht : B → ℕ` which decreases under all `ẽᵢ`, every
element is `f̃_{i₁} ⋯ f̃_{iₖ} b` for some highest weight element `b` (apply raising operators as
long as possible). -/
theorem exists_isHighestWeight_fWord (ht : B → ℕ)
    (hht : ∀ i b b', C.e i b = some b' → ht b' < ht b) (b : B) :
    ∃ h, C.IsHighestWeight h ∧ ∃ l, C.fWord l h = some b := by
  induction hn : ht b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    by_cases hb : C.IsHighestWeight b
    · exact ⟨b, hb, [], rfl⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hb
      obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hi
      obtain ⟨h, hh, l, hl⟩ := ih (ht b') (hn ▸ hht i b b' hb') b' rfl
      exact ⟨h, hh, i :: l, by
        rw [fWord_cons, hl, Option.bind_some]; exact (C.f_eq_some_iff i b' b).mpr hb'⟩

lemma isHighestWeight_of_fWord {l : List ι} {b b' : B} (h : C.fWord l b = some b')
    (hb' : C.IsHighestWeight b') : l = [] := by
  cases l with
  | nil => rfl
  | cons i l =>
    obtain ⟨c, -, hf⟩ := Option.bind_eq_some_iff.mp h
    have := hb' i
    rw [(C.f_eq_some_iff i c b').mp hf] at this
    exact absurd this (Option.some_ne_none c)

/-- If every element of a crystal is `f̃_{i₁} ⋯ f̃_{iₖ} b₀`, then `b₀` is its only possible
highest weight element. -/
lemma eq_of_isHighestWeight {b₀ b : B} (hgen : ∃ l, C.fWord l b₀ = some b)
    (hb : C.IsHighestWeight b) : b = b₀ := by
  obtain ⟨l, hl⟩ := hgen
  obtain rfl := isHighestWeight_of_fWord hl hb
  exact (Option.some_injective _ hl).symm

namespace StrictHom

variable (ψ : StrictHom C₁ C₂)

lemma fWord_apply (l : List ι) (b : B₁) : C₂.fWord l (ψ b) = (C₁.fWord l b).map ψ := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [fWord_cons, fWord_cons, ih]
    cases C₁.fWord l b <;> simp [ψ.f_apply]

lemma isHighestWeight_apply_iff {b : B₁} : C₂.IsHighestWeight (ψ b) ↔ C₁.IsHighestWeight b := by
  simp only [IsHighestWeight, ψ.e_apply, Option.map_eq_none_iff]

/-- The image of a strict morphism is stable under all `ẽᵢ` and `f̃ᵢ`. -/
lemma isStable_range : C₂.IsStable (Set.range ψ) where
  e_mem i _ c hb h := by
    obtain ⟨b, rfl⟩ := hb
    rw [ψ.e_apply] at h
    obtain ⟨b', -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨b', rfl⟩
  f_mem i _ c hb h := by
    obtain ⟨b, rfl⟩ := hb
    rw [ψ.f_apply] at h
    obtain ⟨b', -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨b', rfl⟩

/-- A strict morphism out of a crystal with a height function decreasing under the `ẽᵢ` and a
unique highest weight element is injective: two elements with the same image are either both of
highest weight, or are obtained by `f̃ᵢ` from elements of smaller height with the same image. -/
theorem injective (ht : B₁ → ℕ) (hht : ∀ i b b', C₁.e i b = some b' → ht b' < ht b)
    (huniq : ∀ h h', C₁.IsHighestWeight h → C₁.IsHighestWeight h' → h = h') :
    Function.Injective ψ := by
  intro a a' haa
  induction hn : ht a using Nat.strong_induction_on generalizing a a' with
  | _ n ih =>
    by_cases ha : C₁.IsHighestWeight a
    · refine huniq a a' ha (ψ.isHighestWeight_apply_iff.mp ?_)
      rw [← haa]
      exact ψ.isHighestWeight_apply_iff.mpr ha
    · obtain ⟨i, hi⟩ := not_forall.mp ha
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hi
      have h1 : C₂.e i (ψ a') = some (ψ c) := by rw [← haa, ψ.e_apply, hc, Option.map_some]
      rw [ψ.e_apply] at h1
      obtain ⟨c', hc', hcc⟩ := Option.map_eq_some_iff.mp h1
      obtain rfl := ih (ht c) (hn ▸ hht i a c hc) hcc.symm rfl
      exact C₁.e_injective hc hc'

/-- If every element of `B₁` is `f̃_{i₁} ⋯ f̃_{iₖ} b₀`, the image of a strict morphism is the
connected component of the image of `b₀`. -/
theorem range_eq_closure {b₀ : B₁} (hgen : ∀ b, ∃ l, C₁.fWord l b₀ = some b) :
    Set.range ψ = C₂.closure {ψ b₀} := by
  refine subset_antisymm ?_ (closure_subset ψ.isStable_range (singleton_subset_iff.mpr ⟨b₀, rfl⟩))
  rintro _ ⟨b, rfl⟩
  obtain ⟨l, hl⟩ := hgen b
  exact mem_closure_of_fWord_eq_some (by rw [ψ.fWord_apply, hl, Option.map_some])

end StrictHom

/-! ### Isomorphisms onto images and restrictions -/

namespace Equiv

/-- An injective strict morphism is an isomorphism onto its image. -/
noncomputable def ofInjective (ψ : StrictHom C₁ C₂) (h : Function.Injective ψ) :
    Equiv C₁ (Crystal.restrict ψ.isStable_range) where
  toEquiv := _root_.Equiv.ofInjective ψ h
  wt_map b := ψ.wt_apply b
  ε_map i b := ψ.ε_apply i b
  e_map i b := Option.map_injective Subtype.val_injective <| by
    rw [restrict_e, Option.map_map]
    exact ψ.e_apply i b
  f_map i b := Option.map_injective Subtype.val_injective <| by
    rw [restrict_f, Option.map_map]
    exact ψ.f_apply i b

@[simp] lemma coe_ofInjective_apply (ψ : StrictHom C₁ C₂) (h : Function.Injective ψ) (b : B₁) :
    (ofInjective ψ h b : B₂) = ψ b := rfl

/-- The restriction of an isomorphism of crystals to stable subsets corresponding to each other. -/
def restrictCongr (Φ : Equiv C₁ C₂) {S₁ : Set B₁} {S₂ : Set B₂} (h₁ : C₁.IsStable S₁)
    (h₂ : C₂.IsStable S₂) (h : ∀ b, b ∈ S₁ ↔ Φ b ∈ S₂) :
    Equiv (Crystal.restrict h₁) (Crystal.restrict h₂) where
  toEquiv := Φ.toEquiv.subtypeEquiv h
  wt_map b := Φ.wt_apply b.1
  ε_map i b := Φ.ε_apply i b.1
  e_map i b := Option.map_injective Subtype.val_injective <| by
    rw [restrict_e, Option.map_map]
    change _ = Option.map (Φ ∘ Subtype.val) _
    rw [← Option.map_map, restrict_e]
    exact Φ.e_apply i b.1
  f_map i b := Option.map_injective Subtype.val_injective <| by
    rw [restrict_f, Option.map_map]
    change _ = Option.map (Φ ∘ Subtype.val) _
    rw [← Option.map_map, restrict_f]
    exact Φ.f_apply i b.1

@[simp] lemma coe_restrictCongr_apply (Φ : Equiv C₁ C₂) {S₁ : Set B₁} {S₂ : Set B₂}
    (h₁ : C₁.IsStable S₁) (h₂ : C₂.IsStable S₂) (h : ∀ b, b ∈ S₁ ↔ Φ b ∈ S₂) (b : S₁) :
    (restrictCongr Φ h₁ h₂ h b : B₂) = Φ b := rfl

/-- An isomorphism of crystals maps connected components onto connected components. -/
theorem image_closure (Φ : Equiv C₁ C₂) (b : B₁) :
    Φ '' C₁.closure {b} = C₂.closure {Φ b} := by
  apply subset_antisymm
  · have hT : C₁.IsStable {x | Φ x ∈ C₂.closure {Φ b}} :=
      ⟨fun i x x' hx h ↦ (isStable_closure _).e_mem i _ _ hx (by rw [Φ.e_apply, h]; rfl),
        fun i x x' hx h ↦ (isStable_closure _).f_mem i _ _ hx (by rw [Φ.f_apply, h]; rfl)⟩
    rintro _ ⟨x, hx, rfl⟩
    exact closure_subset hT (singleton_subset_iff.mpr (subset_closure {Φ b} rfl)) hx
  · refine closure_subset ⟨fun i y y' hy h ↦ ?_, fun i y y' hy h ↦ ?_⟩
      (singleton_subset_iff.mpr ⟨b, subset_closure {b} rfl, rfl⟩)
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [Φ.e_apply] at h
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨x', (isStable_closure _).e_mem i x x' hx hx', rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [Φ.f_apply] at h
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨x', (isStable_closure _).f_mem i x x' hx hx', rfl⟩

/-- An isomorphism of crystals restricts to an isomorphism between the connected component of
`b` and that of its image. -/
def restrictClosure (Φ : Equiv C₁ C₂) (b : B₁) :
    Equiv (Crystal.restrict (C₁.isStable_closure {b}))
      (Crystal.restrict (C₂.isStable_closure {Φ b})) :=
  restrictCongr Φ _ _ fun x ↦ by
    rw [← image_closure Φ b]
    exact (EquivLike.injective Φ).mem_set_image.symm

@[simp] lemma coe_restrictClosure_apply (Φ : Equiv C₁ C₂) (b : B₁) (x : C₁.closure {b}) :
    (restrictClosure Φ b x : B₂) = Φ x := rfl

end Equiv

/-- Restrictions to equal stable subsets are isomorphic. -/
def restrictEquivOfEq {S S' : Set B} (hS : C.IsStable S) (hS' : C.IsStable S') (h : S = S') :
    Equiv (restrict hS) (restrict hS') := by
  subst h
  exact Equiv.refl _

@[simp] lemma coe_restrictEquivOfEq_apply {S S' : Set B} (hS : C.IsStable S) (hS' : C.IsStable S')
    (h : S = S') (b : S) : (C.restrictEquivOfEq hS hS' h b : B) = b := by
  subst h
  rfl

end Crystal

/-! ### The isomorphism property for paths -/

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

section Reparam

variable (π : LittelmannPath S) (τ : 𝕜 ≃o 𝕜) (h0 : τ 0 = 0) (h1 : τ 1 = 1)

/-- The reparametrization `π ∘ τ` of a path by an order automorphism `τ` of the line with
`τ(0) = 0` and `τ(1) = 1`. -/
def reparam : LittelmannPath S where
  toFun t := π (τ t)
  wt := π.wt
  toFun_of_nonpos' t ht := π.apply_of_nonpos (by rw [← h0]; exact τ.monotone ht)
  toFun_of_one_le' t ht := π.apply_of_one_le (by rw [← h1]; exact τ.monotone ht)
  continuous_coroot' i := (π.continuous_pairing i).comp τ.continuous

omit [IsStrictOrderedRing 𝕜] in
@[simp] lemma reparam_apply (t : 𝕜) : π.reparam τ h0 h1 t = π (τ t) := rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] lemma wt_reparam : (π.reparam τ h0 h1).wt = π.wt := rfl

omit [IsStrictOrderedRing 𝕜] in
lemma pairing_reparam (i : ι) : (π.reparam τ h0 h1).pairing i = π.pairing i ∘ τ := rfl

omit [IsStrictOrderedRing 𝕜] in
lemma runningMin_reparam (i : ι) (t : 𝕜) :
    (π.reparam τ h0 h1).runningMin i t = π.runningMin i (τ t) := by
  rw [runningMin, runningMin, pairing_reparam, Set.image_comp, τ.image_Icc, h0,
    τ.monotone.map_max, h0]

omit [IsStrictOrderedRing 𝕜] in
lemma minPairing_reparam (i : ι) : (π.reparam τ h0 h1).minPairing i = π.minPairing i := by
  rw [minPairing, minPairing, runningMin_reparam, h1]

omit [IsStrictOrderedRing 𝕜] in
lemma eCoeff_reparam (i : ι) (t : 𝕜) : (π.reparam τ h0 h1).eCoeff i t = π.eCoeff i (τ t) := by
  rw [eCoeff, eCoeff, runningMin_reparam, minPairing_reparam]

/-- Reparametrization commutes with the root operators `eᵢ`. -/
theorem e_reparam (i : ι) :
    e i (π.reparam τ h0 h1) = (e i π).map (reparam · τ h0 h1) := by
  by_cases hQ : π.minPairing i ≤ -1
  · rw [e_of_le hQ, e_of_le (by rwa [minPairing_reparam]), Option.map_some]
    congr 1
    ext t
    simp only [eRaw_apply, reparam_apply, eCoeff_reparam]
  · rw [(e_eq_none_iff).mpr (not_le.mp hQ),
      (e_eq_none_iff).mpr (by rw [minPairing_reparam]; exact not_le.mp hQ), Option.map_none]

/-- The order automorphism `t ↦ 1 - τ(1 - t)` (conjugate of `τ` by `t ↦ 1 - t`). -/
noncomputable def revIso : 𝕜 ≃o 𝕜 :=
  StrictMono.orderIsoOfSurjective (fun t ↦ 1 - τ (1 - t))
    (fun s t hst ↦ by simp only [sub_lt_sub_iff_left]; exact τ.strictMono (by linarith))
    fun u ↦ ⟨1 - τ.symm (1 - u), by simp⟩

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
@[simp] lemma revIso_apply (t : 𝕜) : revIso τ t = 1 - τ (1 - t) := rfl

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
lemma revIso_zero (h1 : τ 1 = 1) : revIso τ 0 = 0 := by simp [h1]

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
lemma revIso_one (h0 : τ 0 = 0) : revIso τ 1 = 1 := by simp [h0]

lemma rev_reparam :
    (π.reparam τ h0 h1).rev = π.rev.reparam (revIso τ) (revIso_zero τ h1)
      (revIso_one τ h0) := by
  ext t
  simp [rev_apply, h1]

lemma reparam_rev_reparam :
    (π.rev.reparam (revIso τ) (revIso_zero τ h1) (revIso_one τ h0)).rev =
      π.reparam τ h0 h1 := by
  rw [← rev_reparam, rev_rev]

/-- Reparametrization commutes with the root operators `fᵢ`. -/
theorem f_reparam (i : ι) :
    f i (π.reparam τ h0 h1) = (f i π).map (reparam · τ h0 h1) := by
  rw [f, rev_reparam, e_reparam, f, Option.map_map, Option.map_map]
  congr 1
  funext ρ
  simp only [Function.comp_apply]
  rw [← rev_rev (ρ.rev.reparam τ h0 h1), rev_reparam, rev_rev]
  ext t
  simp

end Reparam

variable [FloorRing 𝕜]

/-- Reparametrization by an order automorphism `τ` of the line fixing `0` and `1` is an
automorphism of the crystal of all paths. -/
noncomputable def reparamEquiv (τ : 𝕜 ≃o 𝕜) (h0 : τ 0 = 0) (h1 : τ 1 = 1) :
    Crystal.Equiv (crystal S) (crystal S) where
  toFun π := π.reparam τ h0 h1
  invFun π := π.reparam τ.symm (by rw [τ.symm_apply_eq, h0]) (by rw [τ.symm_apply_eq, h1])
  left_inv π := by ext t; simp
  right_inv π := by ext t; simp
  wt_map π := rfl
  ε_map i π := by simp [ε, minPairing_reparam]
  e_map i π := e_reparam π τ h0 h1 i
  f_map i π := f_reparam π τ h0 h1 i

/-- **Littelmann's isomorphism property** for two paths `π, π'` ([Lit95] Thm. 7.1 (check)): there
is an isomorphism of crystals `B(π) ≅ B(π')` sending `π` to `π'`. Littelmann's isomorphism theorem
states this for all paths `π, π'` with image in the dominant chamber and `π(1) = π'(1)`. -/
def ComponentIso (π π' : LittelmannPath S) : Prop :=
  ∃ ψ : Crystal.Equiv π.componentCrystal π'.componentCrystal,
    (ψ ⟨π, π.mem_component_self⟩ : LittelmannPath S) = π'

lemma ComponentIso.refl (π : LittelmannPath S) : ComponentIso π π :=
  ⟨Crystal.Equiv.refl _, rfl⟩

lemma ComponentIso.symm {π π' : LittelmannPath S} (h : ComponentIso π π') : ComponentIso π' π := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨ψ.symm, ?_⟩
  have : (⟨π', π'.mem_component_self⟩ : π'.component) = ψ ⟨π, π.mem_component_self⟩ :=
    Subtype.ext hψ.symm
  rw [this]
  exact congrArg Subtype.val (ψ.toEquiv.symm_apply_apply _)

lemma ComponentIso.trans {π π' π'' : LittelmannPath S} (h : ComponentIso π π')
    (h' : ComponentIso π' π'') : ComponentIso π π'' := by
  obtain ⟨ψ, hψ⟩ := h
  obtain ⟨ψ', hψ'⟩ := h'
  refine ⟨ψ.trans ψ', ?_⟩
  have : ψ ⟨π, π.mem_component_self⟩ = ⟨π', π'.mem_component_self⟩ := Subtype.ext hψ
  change (ψ' (ψ ⟨π, π.mem_component_self⟩) : LittelmannPath S) = π''
  rw [this, hψ']

/-- An automorphism of the crystal of all paths identifies `B(π)` with `B(Φ π)`. -/
theorem componentIso_of_equiv (Φ : Crystal.Equiv (crystal S) (crystal S))
    (π : LittelmannPath S) : ComponentIso π (Φ π) :=
  ⟨Crystal.Equiv.restrictClosure Φ π, rfl⟩

/-- **The isomorphism theorem for reparametrizations**: `B(π) ≅ B(π ∘ τ)`, with `π ↦ π ∘ τ`, for
every order automorphism `τ` of the line fixing `0` and `1`. -/
theorem componentIso_reparam (π : LittelmannPath S) (τ : 𝕜 ≃o 𝕜) (h0 : τ 0 = 0)
    (h1 : τ 1 = 1) : ComponentIso π (π.reparam τ h0 h1) :=
  componentIso_of_equiv (reparamEquiv τ h0 h1) π

end LittelmannPath

/-! ### The crystal `B(λ)` and the isomorphism property -/

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

lemma crystal_fWord (l : List ι) (π : LittelmannPath S) :
    (crystal S).fWord l π = fWord l π := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [Crystal.fWord_cons, ih]; rfl

/-- If `B(π) = {f_{i₁} ⋯ f_{iₖ} π}`, every element of the crystal `B(π)` is obtained from `π` by
lowering operators. -/
lemma exists_fWord_componentCrystal {π : LittelmannPath S} (h : π.component = π.fOrbit)
    (b : π.component) : ∃ l, π.componentCrystal.fWord l ⟨π, π.mem_component_self⟩ = some b := by
  obtain ⟨l, hl⟩ : b.1 ∈ π.fOrbit := h ▸ b.2
  refine ⟨l, ?_⟩
  have := (Crystal.restrictHom π.isStable_component).fWord_apply l ⟨π, π.mem_component_self⟩
  rw [Crystal.restrictHom_apply, crystal_fWord, hl] at this
  obtain ⟨b', hb', hbb⟩ := Option.map_eq_some_iff.mp this.symm
  rw [show b = b' from Subtype.ext hbb.symm]
  exact hb'

/-- If `B(π) = {f_{i₁} ⋯ f_{iₖ} π}`, then `π` is the only highest weight element of `B(π)`
(provided `π` itself is of highest weight). -/
lemma isHighestWeight_componentCrystal_iff {π : LittelmannPath S} (h : π.component = π.fOrbit)
    (hπ : ∀ i, e i π = none) (b : π.component) :
    π.componentCrystal.IsHighestWeight b ↔ b = ⟨π, π.mem_component_self⟩ := by
  refine ⟨Crystal.eq_of_isHighestWeight (exists_fWord_componentCrystal h b), ?_⟩
  rintro rfl i
  have := Crystal.restrict_e π.isStable_component i ⟨π, π.mem_component_self⟩
  rw [crystal_e, hπ i, Option.map_eq_none_iff] at this
  exact this

end LittelmannPath

namespace Matrix.Realization

open LittelmannPath

variable {ι K H : Type*} [Fintype ι] [Field K] [ConditionallyCompleteLinearOrder K]
  [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [FloorRing K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsGeneralizedCartan)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

/-- The highest weight element `π_λ` of `B(λ)`. -/
noncomputable abbrev pathCrystalTop :
    (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component :=
  ⟨_, mem_component_self _⟩

/-- Every element of `B(λ)` is `f_{i₁} ⋯ f_{iₖ} π_λ`. -/
lemma exists_fWord_pathCrystal
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ∃ l, (P.pathCrystal hA hΛ).fWord l (pathCrystalTop hA hΛ) = some b := by
  classical
  exact exists_fWord_componentCrystal (component_straightLine_eq_fOrbit (hA := hA) hΛ).1 b

/-- `π_λ` is the only highest weight element of `B(λ)` ([Lit95] (check)). -/
theorem isHighestWeight_pathCrystal_iff
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    (P.pathCrystal hA hΛ).IsHighestWeight b ↔ b = pathCrystalTop hA hΛ := by
  classical
  exact isHighestWeight_componentCrystal_iff (component_straightLine_eq_fOrbit (hA := hA) hΛ).1
    (e_straightLine hA hΛ) b

/-- The depth `∑ᵢ kᵢ` of an element of `B(λ)` of weight `λ - ∑ᵢ kᵢ αᵢ`. -/
noncomputable def pathDepth
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) : ℕ :=
  (∑ j, (exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ b).choose j).toNat

/-- The raising operators decrease the depth by one. -/
theorem pathDepth_of_e_eq_some {i : ι}
    {b b' : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component}
    (h : (P.pathCrystal hA hΛ).e i b = some b') :
    pathDepth hA hΛ b' + 1 = pathDepth hA hΛ b := by
  classical
  obtain ⟨hk, hwk⟩ := (exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ b).choose_spec
  obtain ⟨hk', hwk'⟩ := (exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ b').choose_spec
  set k := (exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ b).choose
  set k' := (exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ b').choose
  have hw := (P.pathCrystal hA hΛ).wt_e i b b' h
  have hw' : ((P.pathCrystal hA hΛ).wt b' : Dual K H) =
      ((P.pathCrystal hA hΛ).wt b : Dual K H) + P.root i := by
    rw [hw, AddSubgroup.coe_add, coe_root_cartanDatum]
  rw [hwk, hwk', ← rootOf_single P i] at hw'
  have hkk : k = k' + Pi.single i 1 := by
    refine P.rootOf_injective ?_
    rw [← sub_eq_zero] at hw' ⊢
    rw [← hw', map_add]
    abel
  have hsum : ∑ j, k j = ∑ j, k' j + 1 := by
    rw [hkk]
    simp [Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ j, k' j := Finset.sum_nonneg fun j _ ↦ hk' j
  change (∑ j, k' j).toNat + 1 = (∑ j, k j).toNat
  omega

/-- **Criterion for Littelmann's isomorphism property** with `B(λ)`: for a dominant integral
weight `λ` and any path `π`, `B(π_λ) ≅ B(π)` with `π_λ ↦ π` if and only if there is a strict
morphism of crystals from `B(π_λ)` to the crystal of all paths sending `π_λ` to `π`. Such a
morphism is automatically injective (`Crystal.StrictHom.injective`), because `π_λ` is the only
highest weight element of `B(π_λ)` and every element is obtained from it by lowering operators
(Littelmann's stability theorem, `Matrix.Realization.component_straightLine_eq_fOrbit`), and its
image is the connected component of `π`. -/
theorem componentIso_straightLine_iff (π : LittelmannPath (P.pathSpace hA)) :
    ComponentIso (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩) π ↔
      ∃ ψ : Crystal.StrictHom (P.pathCrystal hA hΛ) (crystal (P.pathSpace hA)),
        ψ (pathCrystalTop hA hΛ) = π := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    exact ⟨(Crystal.restrictHom π.isStable_component).comp Φ.toStrictHom, hΦ⟩
  · rintro ⟨ψ, hψ⟩
    have hinj := ψ.injective (pathDepth hA hΛ)
      (fun i b b' h ↦ by have := pathDepth_of_e_eq_some hA hΛ h; omega)
      (fun h h' hh hh' ↦ by
        rw [(isHighestWeight_pathCrystal_iff hA hΛ h).mp hh,
          (isHighestWeight_pathCrystal_iff hA hΛ h').mp hh'])
    have hrange : Set.range ψ = π.component := by
      rw [ψ.range_eq_closure (exists_fWord_pathCrystal hA hΛ), hψ]
      rfl
    refine ⟨(Crystal.Equiv.ofInjective ψ hinj).trans
      ((crystal (P.pathSpace hA)).restrictEquivOfEq ψ.isStable_range π.isStable_component
        hrange), ?_⟩
    change ((crystal (P.pathSpace hA)).restrictEquivOfEq ψ.isStable_range π.isStable_component
      hrange (Crystal.Equiv.ofInjective ψ hinj (pathCrystalTop hA hΛ)) : _) = π
    rw [Crystal.coe_restrictEquivOfEq_apply, Crystal.Equiv.coe_ofInjective_apply, hψ]

end Matrix.Realization
