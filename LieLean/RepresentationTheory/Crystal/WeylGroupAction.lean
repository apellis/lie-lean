/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.WeylAction
import LieLean.RepresentationTheory.Crystal.Subcrystal
import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Kashiwara's reflections: morphisms, commuting colours and Weyl group actions

This file supplies the formal part of the construction of a Weyl group action on a seminormal
crystal from Kashiwara's reflections `Sᵢ` (`Crystal.reflection`).

* Strict morphisms of crystals commute with the `Sᵢ` (`Crystal.StrictHom.map_reflection`); in
  particular so does the inclusion of a stable subset (`Crystal.coe_reflection_restrict`).
* If the operators of two colours `i ≠ j` commute (`Crystal.OperatorsCommute`) and
  `⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = 0`, then `Sᵢ Sⱼ = Sⱼ Sᵢ` (`Crystal.IsSeminormal.reflection_comm`):
  the braid relation of length `mᵢⱼ = 2`.
* Given a Coxeter system `(W, s)` with Coxeter matrix `M` and the braid relations
  `(Sᵢ Sⱼ)^{mᵢⱼ} = 1`, the `Sᵢ` extend to a homomorphism `W →* Perm B`
  (`Crystal.IsSeminormal.weylAction`); the relations with `mᵢᵢ = 1` and `mᵢⱼ = ∞` hold
  automatically (`Crystal.IsSeminormal.isLiftable_iff`).

## References

* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413, §7.
-/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B₁ B₂ : Type*}

/-! ### Strict morphisms commute with the reflections -/

namespace StrictHom

variable {C₁ : Crystal D B₁} {C₂ : Crystal D B₂} (ψ : StrictHom C₁ C₂)

lemma eIter_apply (i : ι) (n : ℕ) (b : B₁) :
    C₂.eIter i n (ψ b) = (C₁.eIter i n b).map ψ := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [eIter_succ, eIter_succ, ψ.e_apply]
    cases C₁.e i b with
    | none => rfl
    | some c => exact ih c

lemma fIter_apply (i : ι) (n : ℕ) (b : B₁) :
    C₂.fIter i n (ψ b) = (C₁.fIter i n b).map ψ := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [fIter_succ, fIter_succ, ψ.f_apply]
    cases C₁.f i b with
    | none => rfl
    | some c => exact ih c

private lemma getD_map (x : Option B₁) (b : B₁) : (x.map ψ).getD (ψ b) = ψ (x.getD b) := by
  cases x <;> rfl

/-- Strict morphisms commute with Kashiwara's reflections. -/
theorem map_reflection (i : ι) (b : B₁) : ψ (C₁.reflection i b) = C₂.reflection i (ψ b) := by
  simp only [reflection, ψ.wt_apply]
  split_ifs
  · rw [ψ.fIter_apply, getD_map]
  · rw [ψ.eIter_apply, getD_map]

end StrictHom

/-- The reflections of a stable subset are the restrictions of the ambient reflections. -/
lemma coe_reflection_restrict (C : Crystal D B) {S : Set B} (hS : C.IsStable S) (i : ι)
    (b : S) : ((restrict hS).reflection i b : B) = C.reflection i b :=
  (restrictHom hS).map_reflection i b

/-! ### Commuting colours -/

/-- The crystal operators of colours `i` and `j` commute (as partial maps). -/
structure OperatorsCommute (C : Crystal D B) (i j : ι) : Prop where
  e_e : ∀ b, (C.e i b).bind (C.e j) = (C.e j b).bind (C.e i)
  e_f : ∀ b, (C.e i b).bind (C.f j) = (C.f j b).bind (C.e i)
  f_e : ∀ b, (C.f i b).bind (C.e j) = (C.e j b).bind (C.f i)
  f_f : ∀ b, (C.f i b).bind (C.f j) = (C.f j b).bind (C.f i)

/-- If two partial maps commute, an iterate of the first commutes with the second. -/
lemma bind_comm_of_iter (F G : B → Option B) (hFG : ∀ b, (F b).bind G = (G b).bind F)
    (T : ℕ → B → Option B) (h0 : ∀ b, T 0 b = some b)
    (hs : ∀ n b, T (n + 1) b = (F b).bind (T n)) (n : ℕ) (b : B) :
    (T n b).bind G = (G b).bind (T n) := by
  induction n generalizing b with
  | zero =>
    rw [h0, Option.bind_some]
    cases G b with
    | none => rfl
    | some c => exact (h0 c).symm
  | succ n ih =>
    have hT : T (n + 1) = fun c => (F c).bind (T n) := funext (hs n)
    rw [hT, Option.bind_assoc]
    simp only [ih]
    rw [← Option.bind_assoc, hFG, Option.bind_assoc]

namespace OperatorsCommute

variable {C : Crystal D B} {i j : ι}

lemma symm (h : C.OperatorsCommute i j) : C.OperatorsCommute j i where
  e_e b := (h.e_e b).symm
  e_f b := (h.f_e b).symm
  f_e b := (h.e_f b).symm
  f_f b := (h.f_f b).symm

/-- Kashiwara's string map of colour `i` and length `n`: `f̃ᵢⁿ` for `n ≥ 0`, `ẽᵢ⁻ⁿ` for
`n < 0`. -/
def _root_.Crystal.stringMap (C : Crystal D B) (i : ι) (n : ℤ) : B → Option B :=
  if 0 ≤ n then C.fIter i n.toNat else C.eIter i (-n).toNat

lemma _root_.Crystal.reflection_eq_getD_stringMap (C : Crystal D B) (i : ι) (b : B) :
    C.reflection i b = (C.stringMap i (D.coroot i (C.wt b)) b).getD b := by
  unfold reflection stringMap
  split_ifs <;> rfl

private lemma iter_left (G : B → Option B)
    (hG : ∀ b, (C.e i b).bind G = (G b).bind (C.e i))
    (hG' : ∀ b, (C.f i b).bind G = (G b).bind (C.f i)) (n : ℤ) (b : B) :
    (C.stringMap i n b).bind G = (G b).bind (C.stringMap i n) := by
  unfold stringMap
  split_ifs
  · exact bind_comm_of_iter _ G hG' _ (fun _ => rfl) (fun _ _ => rfl) _ b
  · exact bind_comm_of_iter _ G hG _ (fun _ => rfl) (fun _ _ => rfl) _ b

/-- String maps of commuting colours commute. -/
theorem stringMap_comm (h : C.OperatorsCommute i j) (m n : ℤ) (b : B) :
    (C.stringMap i m b).bind (C.stringMap j n) =
      (C.stringMap j n b).bind (C.stringMap i m) := by
  refine iter_left _ (fun b => ?_) (fun b => ?_) m b
  · exact (iter_left _ (fun c => (h.e_e c).symm) (fun c => (h.e_f c).symm) n b).symm
  · exact (iter_left _ (fun c => (h.f_e c).symm) (fun c => (h.f_f c).symm) n b).symm

end OperatorsCommute

namespace IsSeminormal

variable {C : Crystal D B} {i j : ι}

lemma stringMap_reflection (hC : C.IsSeminormal) (i : ι) (b : B) :
    C.stringMap i (D.coroot i (C.wt b)) b = some (C.reflection i b) := by
  unfold stringMap
  split_ifs with h
  · exact hC.fIter_reflection h
  · exact hC.eIter_reflection (not_le.mp h)

/-- **The braid relation of length two** ([Kas94] §7): if the operators of colours
`i, j` commute and `⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = 0`, then `Sᵢ Sⱼ = Sⱼ Sᵢ`. -/
theorem reflection_comm (hC : C.IsSeminormal) (h : C.OperatorsCommute i j)
    (hij : D.coroot i (D.root j) = 0) (hji : D.coroot j (D.root i) = 0) (b : B) :
    C.reflection i (C.reflection j b) = C.reflection j (C.reflection i b) := by
  have hi : D.coroot i (C.wt (C.reflection j b)) = D.coroot i (C.wt b) := by
    rw [hC.wt_reflection, D.reflection_apply, map_sub, map_zsmul, hij, smul_zero, sub_zero]
  have hj : D.coroot j (C.wt (C.reflection i b)) = D.coroot j (C.wt b) := by
    rw [hC.wt_reflection, D.reflection_apply, map_sub, map_zsmul, hji, smul_zero, sub_zero]
  have key := h.stringMap_comm (D.coroot i (C.wt b)) (D.coroot j (C.wt b)) b
  rw [hC.stringMap_reflection i b, hC.stringMap_reflection j b, Option.bind_some,
    Option.bind_some, ← hi, ← hj, hC.stringMap_reflection, hC.stringMap_reflection] at key
  exact (Option.some_injective _ key).symm

/-! ### Weyl group actions -/

variable {M : CoxeterMatrix ι} {W : Type*} [Group W]

/-- The Coxeter relations for the `Sᵢ` reduce to the pairs with `2 ≤ mᵢⱼ < ∞`. -/
theorem isLiftable_iff (hC : C.IsSeminormal) :
    M.IsLiftable hC.reflectionPerm ↔ ∀ i j, i ≠ j → M i j ≠ 0 →
      (hC.reflectionPerm i * hC.reflectionPerm j) ^ M i j = 1 := by
  refine ⟨fun h i j _ _ => h i j, fun h i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal, pow_one]
    ext b
    exact hC.reflection_reflection i b
  · by_cases hM : M i j = 0
    · rw [hM, pow_zero]
    · exact h i j hij hM

/-- Commuting reflections satisfy the Coxeter relation of order two. -/
lemma reflectionPerm_mul_pow_two (hC : C.IsSeminormal)
    (hcomm : ∀ b, C.reflection i (C.reflection j b) = C.reflection j (C.reflection i b)) :
    (hC.reflectionPerm i * hC.reflectionPerm j) ^ 2 = 1 := by
  ext b
  simp only [pow_two, Equiv.Perm.mul_apply, reflectionPerm_apply, Equiv.Perm.one_apply]
  rw [hcomm (C.reflection i (C.reflection j b)), hC.reflection_reflection,
    hC.reflection_reflection]

/-- **Kashiwara's Weyl group action**: if the `Sᵢ` satisfy the Coxeter relations of a Coxeter
system `(W, s)`, they extend to an action `W →* Perm B` with `sᵢ ↦ Sᵢ`. -/
noncomputable def weylAction (hC : C.IsSeminormal) (cs : CoxeterSystem M W)
    (h : M.IsLiftable hC.reflectionPerm) : W →* Equiv.Perm B :=
  cs.lift ⟨hC.reflectionPerm, h⟩

@[simp] lemma weylAction_simple (hC : C.IsSeminormal) (cs : CoxeterSystem M W)
    (h : M.IsLiftable hC.reflectionPerm) (i : ι) :
    hC.weylAction cs h (cs.simple i) = hC.reflectionPerm i :=
  cs.lift_apply_simple h i

end IsSeminormal

end Crystal
