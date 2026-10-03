/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Folding

/-!
# Morphisms from crystals of a Levi datum

Let `D` be a Cartan datum indexed by `ι`, `D'` one indexed by `κ`, and `e : κ → ι` a map of
colours (typically the inclusion of a subset `J ⊆ ι`, `D'` a Cartan datum of the principal
submatrix `A_J`). A map `Φ : B' → B` from a `D'`-crystal to a `D`-crystal is a *Levi morphism*
(`Crystal.IsLeviHom`) if it sends `ẽₖ, f̃ₖ` to `ẽ_{e k}, f̃_{e k}` and
`⟨wt Φ b, α_{e k}^∨⟩ = ⟨wt b, αₖ^∨⟩`. Thus `Φ` is a strict morphism from `B'` to the restriction
of `B` to the colours `e(κ)`, where weights are compared only through the coroots of those
colours. These maps are used to define normal crystals relative to the path model
(`Crystal.IsNormal`).

## Main results

* `Crystal.IsLeviHom.ε_apply`, `Crystal.IsLeviHom.φ_apply`: between seminormal crystals a Levi
  morphism preserves `εₖ` and `φₖ`.
* `Crystal.IsLeviHom.map_reflection`: it intertwines Kashiwara's reflections,
  `Φ ∘ Sₖ = S_{e k} ∘ Φ`.
* `Crystal.IsLeviHom.tensor`: the tensor product of Levi morphisms between seminormal crystals is
  a Levi morphism.
* `Crystal.IsLeviHom.comp_strictHom`, `Crystal.IsLeviHom.strictHom_comp`, `Crystal.IsLeviHom.inl`,
  `Crystal.IsLeviHom.inr`: compatibility with strict morphisms and disjoint unions.
-/

namespace Crystal

variable {ι κ X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {D : CartanDatum ι X}
  {D' : CartanDatum κ Y} {B B' B'' B₁ B₂ B₁' B₂' : Type*}

/-- A *Levi morphism* along a map of colours `e : κ → ι`: a map `Φ : B' → B` from a crystal over
`D'` to a crystal over `D` such that `Φ (ẽₖ b) = ẽ_{e k} Φ(b)`, `Φ (f̃ₖ b) = f̃_{e k} Φ(b)` (both
sides possibly `0`) and `⟨wt Φ(b), α_{e k}^∨⟩ = ⟨wt b, αₖ^∨⟩`. -/
structure IsLeviHom (C' : Crystal D' B') (C : Crystal D B) (e : κ → ι) (Φ : B' → B) : Prop where
  map_e : ∀ k b, (C'.e k b).map Φ = C.e (e k) (Φ b)
  map_f : ∀ k b, (C'.f k b).map Φ = C.f (e k) (Φ b)
  coroot_wt : ∀ k b, D.coroot (e k) (C.wt (Φ b)) = D'.coroot k (C'.wt b)

namespace IsLeviHom

variable {C' : Crystal D' B'} {C : Crystal D B} {e : κ → ι} {Φ : B' → B}

lemma map_eIter (h : IsLeviHom C' C e Φ) (k : κ) (n : ℕ) (b : B') :
    (C'.eIter k n b).map Φ = C.eIter (e k) n (Φ b) := by
  rw [eIter_eq_iterOpt, eIter_eq_iterOpt]
  exact iterOpt_map (h.map_e k) n b

lemma map_fIter (h : IsLeviHom C' C e Φ) (k : κ) (n : ℕ) (b : B') :
    (C'.fIter k n b).map Φ = C.fIter (e k) n (Φ b) := by
  rw [fIter_eq_iterOpt, fIter_eq_iterOpt]
  exact iterOpt_map (h.map_f k) n b

/-- Between seminormal crystals a Levi morphism preserves `εₖ`. -/
theorem ε_apply (h : IsLeviHom C' C e Φ) (hC' : C'.IsSeminormal) (hC : C.IsSeminormal) (k : κ)
    (b : B') : C.ε (e k) (Φ b) = C'.ε k b := by
  obtain ⟨m, hm⟩ := hC.exists_ε_eq (e k) (Φ b)
  obtain ⟨m', hm'⟩ := hC'.exists_ε_eq k b
  have key : ∀ n : ℕ, (n : WithBot ℤ) ≤ C.ε (e k) (Φ b) ↔ (n : WithBot ℤ) ≤ C'.ε k b := fun n => by
    rw [← (hC (e k) (Φ b) n).1, ← (hC' k b n).1, ← h.map_eIter, Option.isSome_map]
  have h1 := (key m).mp (le_of_eq hm.symm)
  have h2 := (key m').mpr (le_of_eq hm'.symm)
  rw [hm'] at h1
  rw [hm] at h2
  rw [hm, hm']
  have h1' : m ≤ m' := by exact_mod_cast h1
  have h2' : m' ≤ m := by exact_mod_cast h2
  rw [le_antisymm h1' h2']

/-- Between seminormal crystals a Levi morphism preserves `φₖ`. -/
theorem φ_apply (h : IsLeviHom C' C e Φ) (hC' : C'.IsSeminormal) (hC : C.IsSeminormal) (k : κ)
    (b : B') : C.φ (e k) (Φ b) = C'.φ k b := by
  rw [C.φ_eq, C'.φ_eq, h.ε_apply hC' hC, h.coroot_wt]

/-- A Levi morphism between seminormal crystals intertwines Kashiwara's reflections:
`Φ (Sₖ b) = S_{e k} Φ(b)`. -/
theorem map_reflection (h : IsLeviHom C' C e Φ) (hC' : C'.IsSeminormal) (hC : C.IsSeminormal)
    (k : κ) (b : B') : Φ (C'.reflection k b) = C.reflection (e k) (Φ b) :=
  hC'.map_reflection_of_eq hC (h.map_e k) (h.map_f k) (h.coroot_wt k) b

/-- Precomposition with a strict morphism. -/
theorem comp_strictHom (h : IsLeviHom C' C e Φ) {C'' : Crystal D' B''} (ψ : StrictHom C'' C') :
    IsLeviHom C'' C e (Φ ∘ ψ) where
  map_e k b := by rw [Function.comp_apply, ← h.map_e, ψ.e_apply, Option.map_map]
  map_f k b := by rw [Function.comp_apply, ← h.map_f, ψ.f_apply, Option.map_map]
  coroot_wt k b := by rw [Function.comp_apply, h.coroot_wt, ψ.wt_apply]

/-- Postcomposition with a strict morphism. -/
theorem strictHom_comp (h : IsLeviHom C' C e Φ) {C₂ : Crystal D B₂} (ψ : StrictHom C C₂) :
    IsLeviHom C' C₂ e (ψ ∘ Φ) where
  map_e k b := by rw [Function.comp_apply, ψ.e_apply, ← h.map_e, Option.map_map]
  map_f k b := by rw [Function.comp_apply, ψ.f_apply, ← h.map_f, Option.map_map]
  coroot_wt k b := by rw [Function.comp_apply, ψ.wt_apply, h.coroot_wt]

/-- Composition with the first inclusion into a disjoint union. -/
theorem inl (h : IsLeviHom C' C e Φ) (C₂ : Crystal D B₂) :
    IsLeviHom C' (C.sum C₂) e (Sum.inl ∘ Φ) where
  map_e k b := by
    change _ = (C.e (e k) (Φ b)).map Sum.inl
    rw [← h.map_e, Option.map_map]
  map_f k b := by
    change _ = (C.f (e k) (Φ b)).map Sum.inl
    rw [← h.map_f, Option.map_map]
  coroot_wt k b := h.coroot_wt k b

/-- Composition with the second inclusion into a disjoint union. -/
theorem inr (h : IsLeviHom C' C e Φ) (C₁ : Crystal D B₁) :
    IsLeviHom C' (C₁.sum C) e (Sum.inr ∘ Φ) where
  map_e k b := by
    change _ = (C.e (e k) (Φ b)).map Sum.inr
    rw [← h.map_e, Option.map_map]
  map_f k b := by
    change _ = (C.f (e k) (Φ b)).map Sum.inr
    rw [← h.map_f, Option.map_map]
  coroot_wt k b := h.coroot_wt k b

/-- **Tensor products**: if `Φ₁, Φ₂` are Levi morphisms between seminormal crystals, then so is
`Φ₁ ⊗ Φ₂ : B₁' ⊗ B₂' → B₁ ⊗ B₂`. -/
theorem tensor {C₁' : Crystal D' B₁'} {C₂' : Crystal D' B₂'} {C₁ : Crystal D B₁}
    {C₂ : Crystal D B₂} {Φ₁ : B₁' → B₁} {Φ₂ : B₂' → B₂} (h₁ : IsLeviHom C₁' C₁ e Φ₁)
    (h₂ : IsLeviHom C₂' C₂ e Φ₂) (hC₁' : C₁'.IsSeminormal) (hC₁ : C₁.IsSeminormal)
    (hC₂' : C₂'.IsSeminormal) (hC₂ : C₂.IsSeminormal) :
    IsLeviHom (C₁'.tensor C₂') (C₁.tensor C₂) e (Prod.map Φ₁ Φ₂) where
  map_e k b := by
    obtain ⟨b₁, b₂⟩ := b
    rw [tensor_e, tensor_e]
    simp only [Prod.map_apply]
    rw [h₂.ε_apply hC₂' hC₂, h₁.φ_apply hC₁' hC₁]
    split_ifs
    · rw [← h₁.map_e, Option.map_map, Option.map_map]
      rfl
    · rw [← h₂.map_e, Option.map_map, Option.map_map]
      rfl
  map_f k b := by
    obtain ⟨b₁, b₂⟩ := b
    rw [tensor_f, tensor_f]
    simp only [Prod.map_apply]
    rw [h₂.ε_apply hC₂' hC₂, h₁.φ_apply hC₁' hC₁]
    split_ifs
    · rw [← h₁.map_f, Option.map_map, Option.map_map]
      rfl
    · rw [← h₂.map_f, Option.map_map, Option.map_map]
      rfl
  coroot_wt k b := by
    simp only [tensor_wt, map_add, Prod.map_fst, Prod.map_snd, h₁.coroot_wt, h₂.coroot_wt]

end IsLeviHom

end Crystal
