/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.WeylGroupAction

/-!
# Kashiwara's reflections under folding maps

Let `C` be a crystal for a Cartan datum `D` and `C'` one for a Cartan datum `D'`, both seminormal,
and `Φ : B → B'` a map sending the operators `ẽₖ, f̃ₖ` of one colour `k` of `D` to products of
the operators of pairwise orthogonal, commuting colours `a, c, …` of `D'`:
`Φ(ẽₖ b) = ẽₐ ẽ_c ⋯ Φ(b)` and `Φ(f̃ₖ b) = f̃ₐ f̃_c ⋯ Φ(b)`, with
`⟨wt Φ(b), α_a^∨⟩ = ⟨wt Φ(b), α_c^∨⟩ = ⋯ = ⟨wt b, αₖ^∨⟩`. Then `Φ` sends Kashiwara's reflection
`Sₖ` to the product `Sₐ S_c ⋯` (`Crystal.IsSeminormal.map_reflection_of_bind₂`,
`Crystal.IsSeminormal.map_reflection_of_bind₃`, and `Crystal.IsSeminormal.map_reflection_of_eq`
for a single colour). This is the crystal-theoretic content of *folding* a Dynkin diagram along
an automorphism (e.g. `A₃ → B₂`, `D₄ → G₂`), used in
`LieLean.RepresentationTheory.Crystal.Path.BraidFolding` to deduce the braid relations of types
`B₂` and `G₂` from those of types `A₃` and `D₄`.

## Main definitions

* `Crystal.iterOpt`: the iterates of a partial map `B → Option B`.

## Main results

* `Crystal.iterOpt_bind_of_comm`: the iterates of the product of two commuting partial maps are
  the products of their iterates.
* `Crystal.IsSeminormal.map_reflection_of_bind₂`, `Crystal.IsSeminormal.map_reflection_of_bind₃`:
  `Φ(Sₖ b) = Sₐ S_c Φ(b)`, resp. `Φ(Sₖ b) = Sₐ S_c S_d Φ(b)`.
-/

namespace Crystal

variable {ι ι' X X' : Type*} [AddCommGroup X] [AddCommGroup X'] {D : CartanDatum ι X}
  {D' : CartanDatum ι' X'} {B B' : Type*}

/-! ### Iterates of partial maps -/

/-- The `n`-th iterate of a partial map. -/
def iterOpt (F : B → Option B) : ℕ → B → Option B
  | 0, b => some b
  | n + 1, b => (F b).bind (iterOpt F n)

@[simp] lemma iterOpt_zero (F : B → Option B) (b : B) : iterOpt F 0 b = some b := rfl

lemma iterOpt_succ (F : B → Option B) (n : ℕ) (b : B) :
    iterOpt F (n + 1) b = (F b).bind (iterOpt F n) := rfl

lemma eIter_eq_iterOpt (C : Crystal D B) (i : ι) (n : ℕ) : C.eIter i n = iterOpt (C.e i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext b
    rw [eIter_succ, iterOpt_succ, ih]

lemma fIter_eq_iterOpt (C : Crystal D B) (i : ι) (n : ℕ) : C.fIter i n = iterOpt (C.f i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext b
    rw [fIter_succ, iterOpt_succ, ih]

/-- A map intertwining two partial maps intertwines their iterates. -/
lemma iterOpt_map {F : B → Option B} {G : B' → Option B'} {Φ : B → B'}
    (h : ∀ b, (F b).map Φ = G (Φ b)) (n : ℕ) (b : B) :
    (iterOpt F n b).map Φ = iterOpt G n (Φ b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [iterOpt_succ, iterOpt_succ, ← h]
    cases F b with
    | none => rfl
    | some c => exact ih c

/-- The iterates of the product `G ∘ F` of two commuting partial maps are the products of their
iterates. -/
lemma iterOpt_bind_of_comm {F G : B → Option B} (hFG : ∀ b, (F b).bind G = (G b).bind F)
    (n : ℕ) (b : B) :
    iterOpt (fun x => (F x).bind G) n b = (iterOpt F n b).bind (iterOpt G n) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    have hc : ∀ y, (iterOpt F n y).bind G = (G y).bind (iterOpt F n) := fun y =>
      bind_comm_of_iter F G hFG (iterOpt F) (fun _ => rfl) (fun _ _ => rfl) n y
    rw [iterOpt_succ, iterOpt_succ, Option.bind_assoc, Option.bind_assoc]
    congr 1
    funext x
    simp only [ih]
    rw [show (iterOpt F n x).bind (iterOpt G (n + 1)) =
        ((iterOpt F n x).bind G).bind (iterOpt G n) by rw [Option.bind_assoc]; rfl,
      hc, Option.bind_assoc]

/-! ### Transport of string maps and reflections -/

variable {C : Crystal D B} {C' : Crystal D' B'} {Φ : B → B'} {k : ι}

/-- A map sending `ẽₖ, f̃ₖ` to `E, F` sends the string maps of colour `k` to the iterates of
`E, F`. -/
lemma map_stringMap {E F : B' → Option B'} (he : ∀ b, (C.e k b).map Φ = E (Φ b))
    (hf : ∀ b, (C.f k b).map Φ = F (Φ b)) (n : ℤ) (b : B) :
    (C.stringMap k n b).map Φ =
      (if 0 ≤ n then iterOpt F n.toNat else iterOpt E (-n).toNat) (Φ b) := by
  unfold stringMap
  split_ifs
  · rw [fIter_eq_iterOpt, iterOpt_map hf]
  · rw [eIter_eq_iterOpt, iterOpt_map he]

/-- A map sending `ẽₖ, f̃ₖ` to `ẽₐ, f̃ₐ` sends the string maps of colour `k` to those of
colour `a`. -/
lemma map_stringMap_of_eq {a : ι'} (he : ∀ b, (C.e k b).map Φ = C'.e a (Φ b))
    (hf : ∀ b, (C.f k b).map Φ = C'.f a (Φ b)) (n : ℤ) (b : B) :
    (C.stringMap k n b).map Φ = C'.stringMap a n (Φ b) := by
  rw [map_stringMap he hf]
  unfold stringMap
  split_ifs
  · rw [fIter_eq_iterOpt]
  · rw [eIter_eq_iterOpt]

/-- A map sending `ẽₖ, f̃ₖ` to the products `ẽₐ ẽ_c, f̃ₐ f̃_c` of two commuting colours sends
the string map of length `n` of colour `k` to the product of those of colours `a, c`. -/
lemma map_stringMap_of_bind₂ {a c : ι'}
    (he : ∀ b, (C.e k b).map Φ = (C'.e c (Φ b)).bind (C'.e a))
    (hf : ∀ b, (C.f k b).map Φ = (C'.f c (Φ b)).bind (C'.f a))
    (hee : ∀ x, (C'.e c x).bind (C'.e a) = (C'.e a x).bind (C'.e c))
    (hff : ∀ x, (C'.f c x).bind (C'.f a) = (C'.f a x).bind (C'.f c)) (n : ℤ) (b : B) :
    (C.stringMap k n b).map Φ = (C'.stringMap c n (Φ b)).bind (C'.stringMap a n) := by
  rw [map_stringMap (E := fun x => (C'.e c x).bind (C'.e a))
    (F := fun x => (C'.f c x).bind (C'.f a)) he hf]
  unfold stringMap
  split_ifs
  · rw [iterOpt_bind_of_comm hff, fIter_eq_iterOpt, fIter_eq_iterOpt]
  · rw [iterOpt_bind_of_comm hee, eIter_eq_iterOpt, eIter_eq_iterOpt]

/-- Three pairwise commuting partial maps: the product of the first two commutes with the
third. -/
lemma bind_bind_comm {F G K : B' → Option B'} (hFK : ∀ x, (F x).bind K = (K x).bind F)
    (hGK : ∀ x, (G x).bind K = (K x).bind G) (x : B') :
    ((F x).bind G).bind K = (K x).bind fun y => (F y).bind G := by
  rw [Option.bind_assoc]
  simp only [hGK]
  rw [← Option.bind_assoc, hFK, Option.bind_assoc]

/-- A map sending `ẽₖ, f̃ₖ` to the products `ẽₐ ẽ_c ẽ_d, f̃ₐ f̃_c f̃_d` of three pairwise
commuting colours sends the string map of length `n` of colour `k` to the product of those of
colours `a, c, d`. -/
lemma map_stringMap_of_bind₃ {a c d : ι'}
    (he : ∀ b, (C.e k b).map Φ = ((C'.e d (Φ b)).bind (C'.e c)).bind (C'.e a))
    (hf : ∀ b, (C.f k b).map Φ = ((C'.f d (Φ b)).bind (C'.f c)).bind (C'.f a))
    (hee : ∀ x, (C'.e d x).bind (C'.e c) = (C'.e c x).bind (C'.e d))
    (hff : ∀ x, (C'.f d x).bind (C'.f c) = (C'.f c x).bind (C'.f d))
    (hee' : ∀ x, (C'.e d x).bind (C'.e a) = (C'.e a x).bind (C'.e d))
    (hff' : ∀ x, (C'.f d x).bind (C'.f a) = (C'.f a x).bind (C'.f d))
    (hee'' : ∀ x, (C'.e c x).bind (C'.e a) = (C'.e a x).bind (C'.e c))
    (hff'' : ∀ x, (C'.f c x).bind (C'.f a) = (C'.f a x).bind (C'.f c)) (n : ℤ) (b : B) :
    (C.stringMap k n b).map Φ =
      ((C'.stringMap d n (Φ b)).bind (C'.stringMap c n)).bind (C'.stringMap a n) := by
  rw [map_stringMap (E := fun x => ((C'.e d x).bind (C'.e c)).bind (C'.e a))
    (F := fun x => ((C'.f d x).bind (C'.f c)).bind (C'.f a)) he hf]
  unfold stringMap
  split_ifs
  · rw [iterOpt_bind_of_comm (F := fun x => (C'.f d x).bind (C'.f c)) (bind_bind_comm hff' hff''),
      iterOpt_bind_of_comm hff, fIter_eq_iterOpt, fIter_eq_iterOpt, fIter_eq_iterOpt]
  · rw [iterOpt_bind_of_comm (F := fun x => (C'.e d x).bind (C'.e c)) (bind_bind_comm hee' hee''),
      iterOpt_bind_of_comm hee, eIter_eq_iterOpt, eIter_eq_iterOpt, eIter_eq_iterOpt]

namespace IsSeminormal

variable (hC : C.IsSeminormal) (hC' : C'.IsSeminormal)
include hC hC'

/-- A map sending `ẽₖ, f̃ₖ` to `ẽₐ, f̃ₐ`, compatibly with `⟨wt, α^∨⟩`, sends `Sₖ` to `Sₐ`. -/
theorem map_reflection_of_eq {a : ι'} (he : ∀ b, (C.e k b).map Φ = C'.e a (Φ b))
    (hf : ∀ b, (C.f k b).map Φ = C'.f a (Φ b))
    (hw : ∀ b, D'.coroot a (C'.wt (Φ b)) = D.coroot k (C.wt b)) (b : B) :
    Φ (C.reflection k b) = C'.reflection a (Φ b) := by
  have key := map_stringMap_of_eq he hf (D.coroot k (C.wt b)) b
  rw [hC.stringMap_reflection, Option.map_some, ← hw b, hC'.stringMap_reflection] at key
  exact Option.some_injective _ key

/-- **Folding two colours**: a map sending `ẽₖ, f̃ₖ` to `ẽₐ ẽ_c, f̃ₐ f̃_c` for two orthogonal
commuting colours `a, c`, compatibly with `⟨wt, α^∨⟩`, sends `Sₖ` to `Sₐ S_c`. -/
theorem map_reflection_of_bind₂ {a c : ι'}
    (he : ∀ b, (C.e k b).map Φ = (C'.e c (Φ b)).bind (C'.e a))
    (hf : ∀ b, (C.f k b).map Φ = (C'.f c (Φ b)).bind (C'.f a))
    (hcomm : C'.OperatorsCommute c a) (hac : D'.coroot a (D'.root c) = 0)
    (hwa : ∀ b, D'.coroot a (C'.wt (Φ b)) = D.coroot k (C.wt b))
    (hwc : ∀ b, D'.coroot c (C'.wt (Φ b)) = D.coroot k (C.wt b)) (b : B) :
    Φ (C.reflection k b) = C'.reflection a (C'.reflection c (Φ b)) := by
  have key := map_stringMap_of_bind₂ he hf hcomm.e_e hcomm.f_f (D.coroot k (C.wt b)) b
  have hw : D'.coroot a (C'.wt (C'.reflection c (Φ b))) = D.coroot k (C.wt b) := by
    rw [hC'.wt_reflection, D'.reflection_apply, map_sub, map_zsmul, hac, smul_zero, sub_zero,
      hwa]
  rw [hC.stringMap_reflection, Option.map_some, ← hwc b, hC'.stringMap_reflection,
    Option.bind_some, hwc b, ← hw, hC'.stringMap_reflection] at key
  exact Option.some_injective _ key

/-- **Folding three colours**: a map sending `ẽₖ, f̃ₖ` to `ẽₐ ẽ_c ẽ_d, f̃ₐ f̃_c f̃_d` for three
pairwise orthogonal commuting colours, compatibly with `⟨wt, α^∨⟩`, sends `Sₖ` to
`Sₐ S_c S_d`. -/
theorem map_reflection_of_bind₃ {a c d : ι'}
    (he : ∀ b, (C.e k b).map Φ = ((C'.e d (Φ b)).bind (C'.e c)).bind (C'.e a))
    (hf : ∀ b, (C.f k b).map Φ = ((C'.f d (Φ b)).bind (C'.f c)).bind (C'.f a))
    (hdc : C'.OperatorsCommute d c) (hda : C'.OperatorsCommute d a)
    (hca : C'.OperatorsCommute c a) (hcd : D'.coroot c (D'.root d) = 0)
    (had : D'.coroot a (D'.root d) = 0) (hac : D'.coroot a (D'.root c) = 0)
    (hwa : ∀ b, D'.coroot a (C'.wt (Φ b)) = D.coroot k (C.wt b))
    (hwc : ∀ b, D'.coroot c (C'.wt (Φ b)) = D.coroot k (C.wt b))
    (hwd : ∀ b, D'.coroot d (C'.wt (Φ b)) = D.coroot k (C.wt b)) (b : B) :
    Φ (C.reflection k b) = C'.reflection a (C'.reflection c (C'.reflection d (Φ b))) := by
  have key := map_stringMap_of_bind₃ he hf hdc.e_e hdc.f_f hda.e_e hda.f_f hca.e_e hca.f_f
    (D.coroot k (C.wt b)) b
  have hw₁ : D'.coroot c (C'.wt (C'.reflection d (Φ b))) = D.coroot k (C.wt b) := by
    rw [hC'.wt_reflection, D'.reflection_apply, map_sub, map_zsmul, hcd, smul_zero, sub_zero,
      hwc]
  have hw₂ : D'.coroot a (C'.wt (C'.reflection c (C'.reflection d (Φ b)))) =
      D.coroot k (C.wt b) := by
    rw [hC'.wt_reflection, D'.reflection_apply, map_sub, map_zsmul, hac, smul_zero, sub_zero,
      hC'.wt_reflection, D'.reflection_apply, map_sub, map_zsmul, had, smul_zero, sub_zero, hwa]
  rw [hC.stringMap_reflection, Option.map_some, ← hwd b, hC'.stringMap_reflection,
    Option.bind_some, hwd b, ← hw₁, hC'.stringMap_reflection, Option.bind_some, hw₁, ← hw₂,
    hC'.stringMap_reflection] at key
  exact Option.some_injective _ key

end IsSeminormal

end Crystal
