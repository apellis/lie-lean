/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.TensorPower

/-!
# Changing the weight lattice of a crystal

A morphism of Cartan data `ψ : D → D'` on the same index set (`CartanDatum.Hom`) is an additive
map of weight lattices sending simple roots to simple roots and compatible with the simple
coroots. A crystal for `D` becomes a crystal for `D'` with weights `ψ ∘ wt` and the same
`εᵢ`, `φᵢ`, `ẽᵢ`, `f̃ᵢ` (`Crystal.mapDatum`). This is compatible with strict morphisms,
similarities, tensor products and tensor powers.

## Main definitions

* `CartanDatum.Hom`: morphisms of Cartan data.
* `Crystal.mapDatum`: the crystal with weights pushed forward along a morphism of Cartan data.
* `Crystal.tensorPowMapDatum`: the identity `(ψ_* C)^{⊗n} → ψ_* (C^{⊗n})` as a strict morphism.
-/

variable {ι X X' : Type*} [AddCommGroup X] [AddCommGroup X']

namespace CartanDatum

/-- A morphism of Cartan data `D → D'` on the same index set: an additive map of weight lattices
with `ψ(αᵢ) = αᵢ'` and `⟨ψ μ, αᵢ'^∨⟩ = ⟨μ, αᵢ^∨⟩`. -/
structure Hom (D : CartanDatum ι X) (D' : CartanDatum ι X') where
  /-- The map of weight lattices. -/
  toFun : X →+ X'
  map_root : ∀ i, toFun (D.root i) = D'.root i
  coroot_map : ∀ i μ, D'.coroot i (toFun μ) = D.coroot i μ

end CartanDatum

namespace Crystal

variable {D : CartanDatum ι X} {D' : CartanDatum ι X'} (ψ : D.Hom D') {B B₁ B₂ : Type*}

/-- The crystal `ψ_* C` for `D'`: weights `ψ ∘ wt`, the same `εᵢ`, `φᵢ`, `ẽᵢ`, `f̃ᵢ`. -/
def mapDatum (C : Crystal D B) : Crystal D' B where
  wt b := ψ.toFun (C.wt b)
  ε := C.ε
  φ := C.φ
  e := C.e
  f := C.f
  φ_eq i b := by rw [C.φ_eq, ψ.coroot_map]
  f_eq_some_iff := C.f_eq_some_iff
  wt_e i b b' h := by rw [C.wt_e i b b' h, map_add, ψ.map_root]
  ε_e := C.ε_e
  e_eq_none_of_φ_eq_bot := C.e_eq_none_of_φ_eq_bot

variable (C : Crystal D B)

@[simp] lemma mapDatum_wt (b : B) : (C.mapDatum ψ).wt b = ψ.toFun (C.wt b) := rfl

@[simp] lemma mapDatum_ε : (C.mapDatum ψ).ε = C.ε := rfl

@[simp] lemma mapDatum_φ : (C.mapDatum ψ).φ = C.φ := rfl

@[simp] lemma mapDatum_e : (C.mapDatum ψ).e = C.e := rfl

@[simp] lemma mapDatum_f : (C.mapDatum ψ).f = C.f := rfl

@[simp] lemma mapDatum_eIter (i : ι) : ∀ (n : ℕ) (b : B),
    (C.mapDatum ψ).eIter i n b = C.eIter i n b
  | 0, _ => rfl
  | n + 1, b => by
    rw [eIter_succ, eIter_succ, mapDatum_e]
    cases C.e i b with
    | none => rfl
    | some c => exact mapDatum_eIter i n c

@[simp] lemma mapDatum_fIter (i : ι) : ∀ (n : ℕ) (b : B),
    (C.mapDatum ψ).fIter i n b = C.fIter i n b
  | 0, _ => rfl
  | n + 1, b => by
    rw [fIter_succ, fIter_succ, mapDatum_f]
    cases C.f i b with
    | none => rfl
    | some c => exact mapDatum_fIter i n c

@[simp] lemma mapDatum_fWord : ∀ (w : List ι) (b : B), (C.mapDatum ψ).fWord w b = C.fWord w b
  | [], _ => rfl
  | j :: w, b => by rw [fWord_cons, fWord_cons, mapDatum_fWord w b, mapDatum_f]

variable {C} in
lemma IsSeminormal.mapDatum (hC : C.IsSeminormal) : (C.mapDatum ψ).IsSeminormal := fun i b n ↦ by
  rw [mapDatum_eIter, mapDatum_fIter]
  exact hC i b n

variable {C₁ : Crystal D B₁} {C₂ : Crystal D B₂} {m : ℕ}

/-- A similarity `C₁ → C₂` is a similarity `ψ_* C₁ → ψ_* C₂`. -/
def Similarity.mapDatum (σ : Similarity C₁ C₂ m) :
    Similarity (C₁.mapDatum ψ) (C₂.mapDatum ψ) m where
  toFun := σ
  wt_map b := by rw [mapDatum_wt, mapDatum_wt, σ.wt_apply, map_nsmul]
  ε_map := σ.ε_map
  e_map i b := by rw [mapDatum_eIter]; exact σ.e_map i b
  f_map i b := by rw [mapDatum_fIter]; exact σ.f_map i b

@[simp] lemma Similarity.mapDatum_apply (σ : Similarity C₁ C₂ m) (b : B₁) :
    σ.mapDatum ψ b = σ b := rfl

/-- `ψ_* C₁ ⊗ ψ_* C₂ ≅ ψ_* (C₁ ⊗ C₂)`, the identity. -/
def tensorMapDatum (C₁ : Crystal D B₁) (C₂ : Crystal D B₂) :
    Equiv ((C₁.mapDatum ψ).tensor (C₂.mapDatum ψ)) ((C₁.tensor C₂).mapDatum ψ) where
  toEquiv := _root_.Equiv.refl _
  wt_map b := by simp
  ε_map i b := by simp [tensor_ε, ψ.coroot_map]
  e_map _ _ := Option.map_id'.symm
  f_map _ _ := Option.map_id'.symm

/-- `(ψ_* C)^{⊗n} ≅ ψ_* (C^{⊗n})`, the identity. -/
def tensorPowMapDatum (C : Crystal D B) : (n : ℕ) →
    Equiv ((C.mapDatum ψ).tensorPow n) ((C.tensorPow n).mapDatum ψ)
  | 0 =>
    { toEquiv := _root_.Equiv.refl _
      wt_map := fun _ ↦ map_zero ψ.toFun
      ε_map := fun _ _ ↦ rfl
      e_map := fun _ _ ↦ rfl
      f_map := fun _ _ ↦ rfl }
  | n + 1 => ((Equiv.refl _).tensorCongr (tensorPowMapDatum C n)).trans
      (tensorMapDatum ψ C (C.tensorPow n))

@[simp] lemma tensorPowMapDatum_apply (C : Crystal D B) : ∀ (n : ℕ) (x : TPow B n),
    tensorPowMapDatum ψ C n x = x
  | 0, _ => rfl
  | n + 1, x => by
    change (x.1, tensorPowMapDatum ψ C n x.2) = x
    rw [tensorPowMapDatum_apply C n x.2]
    rfl

@[simp] lemma tensorPowMapDatum_symm_apply (C : Crystal D B) (n : ℕ) (x : TPow B n) :
    (tensorPowMapDatum ψ C n).symm x = x := by
  calc (tensorPowMapDatum ψ C n).symm x
      = (tensorPowMapDatum ψ C n).symm (tensorPowMapDatum ψ C n x) := by
        rw [tensorPowMapDatum_apply]
    _ = x := (tensorPowMapDatum ψ C n).toEquiv.symm_apply_apply x

end Crystal
