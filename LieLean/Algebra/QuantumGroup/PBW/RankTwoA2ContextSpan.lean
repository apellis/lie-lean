/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RankTwoA2BraidSpan
import LieLean.Algebra.QuantumGroup.BraidAction.GeneralArtin
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Braid
import Mathlib.Algebra.Algebra.Operations

/-!
# Actual ordered PBW spans in word context

## Main results

* `CoxeterSystem.span_pbwMonomial_append` factors the span of the actual recursive
  PBW monomials into a prefix span and the transported suffix span.
* `CoxeterSystem.span_pbwMonomial_context` transports a local span equality through
  arbitrary context, provided the two local words have equal composite automorphisms.
* `QuantumGroup.span_pbwMonomial_a2_context` applies this to the actual A₂ words.

These are ordered-span statements, not global spanning or basis statements. In particular,
local generator images alone are not substituted for the full braid relation on the suffix.

## References

Reconstructed from the recursive PBW definition and the repository's actual A₂ span theorem.
-/

open LieLean

noncomputable section

namespace CoxeterSystem

variable {B k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  (T : B → A ≃ₐ[k] A) (E : B → A)

/-- The recursion for actual PBW monomials induces a product formula for their spans. -/
theorem span_pbwMonomial_cons (i : B) (w : List B) :
    Submodule.span k (Set.range (pbwMonomial T E (i :: w))) =
      Submodule.span k (Set.range fun n : ℕ ↦ E i ^ n) *
        (Submodule.span k (Set.range (pbwMonomial T E w))).map (T i).toLinearMap := by
  rw [Submodule.map_span, Submodule.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c 0, rfl⟩, _, ⟨_, ⟨(fun n ↦ c n.succ), rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, _, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    exact ⟨Fin.cons n c, rfl⟩

/-- Append factorization for the spans of actual recursive PBW monomials. The suffix
is acted on by the full composite automorphism of the prefix, in the root-vector order. -/
theorem span_pbwMonomial_append (p s : List B) :
    Submodule.span k (Set.range (pbwMonomial T E (p ++ s))) =
      Submodule.span k (Set.range (pbwMonomial T E p)) *
        (Submodule.span k (Set.range (pbwMonomial T E s))).map
          ((p.map T).prod).toLinearMap := by
  induction p with
  | nil =>
    have hnil : Set.range (pbwMonomial T E []) = {1} := by
      ext x
      simp [pbwMonomial]
    simp [hnil, ← Submodule.one_eq_span, show (1 : A →ₗ[k] A) = LinearMap.id by rfl]
  | cons i p ih =>
    rw [List.cons_append, span_pbwMonomial_cons, ih, span_pbwMonomial_cons]
    have hmap (P Q : Submodule k A) :
        (P * Q).map (T i).toLinearMap = P.map (T i).toLinearMap *
          Q.map (T i).toLinearMap := Submodule.map_mul P Q (T i).toAlgHom
    rw [hmap, mul_assoc, ← Submodule.map_comp]
    rfl

/-- Equal actual ordered spans remain equal after adding any common prefix. -/
theorem span_pbwMonomial_prefix {u w : List B}
    (hspan : Submodule.span k (Set.range (pbwMonomial T E u)) =
      Submodule.span k (Set.range (pbwMonomial T E w))) (p : List B) :
    Submodule.span k (Set.range (pbwMonomial T E (p ++ u))) =
      Submodule.span k (Set.range (pbwMonomial T E (p ++ w))) := by
  rw [span_pbwMonomial_append, span_pbwMonomial_append, hspan]

/-- Equal actual ordered spans transport through arbitrary word context when the
local words also have equal composite braid automorphisms. -/
theorem span_pbwMonomial_context {u w : List B}
    (hspan : Submodule.span k (Set.range (pbwMonomial T E u)) =
      Submodule.span k (Set.range (pbwMonomial T E w)))
    (hT : (u.map T).prod = (w.map T).prod) (p s : List B) :
    Submodule.span k (Set.range (pbwMonomial T E (p ++ u ++ s))) =
      Submodule.span k (Set.range (pbwMonomial T E (p ++ w ++ s))) := by
  have hs : Submodule.span k (Set.range (pbwMonomial T E (u ++ s))) =
      Submodule.span k (Set.range (pbwMonomial T E (w ++ s))) := by
    rw [span_pbwMonomial_append, span_pbwMonomial_append, hspan, hT]
  let S (w : List B) := Submodule.span k (Set.range (pbwMonomial T E w))
  exact (congrArg S (List.append_assoc p u s)).trans
    ((span_pbwMonomial_prefix T E hs p).trans
      (congrArg S (List.append_assoc p w s)).symm)

end CoxeterSystem

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (T : I → QuantumGroup R v ≃ₐ[k] QuantumGroup R v)
  {i j : I} (Hi : HasBraidGeneratorImages i (T i).toAlgHom)
  (Hj : HasBraidGeneratorImages j (T j).toAlgHom)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)

include Hi Hj hij h h' hq

/-- An actual A₂ braid move preserves the ordered PBW span in arbitrary word context.
The full three-factor braid relation is explicit; no reducedness of the context is needed. -/
theorem span_pbwMonomial_a2_context
    (hT : T i * T j * T i = T j * T i * T j) (p s : List I) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v)
      (p ++ [i, j, i] ++ s))) =
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v)
      (p ++ [j, i, j] ++ s))) := by
  apply CoxeterSystem.span_pbwMonomial_context
    T (E R v) (span_pbwMonomial_a2_braid R v T Hi Hj hij h h' hq)
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, ← mul_assoc] using hT

omit Hi Hj hq in
/-- At a non-root-of-unity parameter, the existing braid action supplies the full
operator relation (`isBraidLiftable_braidEquivOfNotRoot`, every Cartan datum) and hence
contextual A₂ ordered-span equality; no global spanning assertion is made. -/
theorem span_pbwMonomial_a2_context_of_not_root
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (p s : List I) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv') (E R v) (p ++ [i, j, i] ++ s))) =
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv') (E R v) (p ++ [j, i, j] ++ s))) := by
  have H (l : I) : HasBraidGeneratorImages l
      (braidEquivOfNotRoot R hv' l).toAlgHom :=
    braidHom_hasBraidGeneratorImages
      (braidGeneric_of_braidSerreGeneric (shortNode_braidGeneric_of_not_root hv' l).sub_ne
        (braidSerreGeneric_of_not_root hv' l))
      (transformedSerre_of_braidSerreGeneric
        (shortNode_braidGeneric_of_not_root hv' l).sub_ne (braidSerreGeneric_of_not_root hv' l))
  apply span_pbwMonomial_a2_context R v (braidEquivOfNotRoot R hv')
    (H i) (H j) hij h h' (shortNode_braidGeneric_of_not_root hv' i).sub_ne
  have hLift : D.cartanMatrix.coxeterMatrix.IsBraidLiftable (braidEquivOfNotRoot R hv') :=
    isBraidLiftable_braidEquivOfNotRoot R hv'
  have hm : D.cartanMatrix.coxeterMatrix i j = 3 := by
    rw [Matrix.coxeterMatrix_apply_of_ne _ hij, h, h']
    rfl
  have hm' : D.cartanMatrix.coxeterMatrix j i = 3 := by
    rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, h, h']
    rfl
  have e := hLift i j hij (by omega)
  simpa [CoxeterSystem.braidWord, hm, hm', CoxeterSystem.alternatingWord,
    ← mul_assoc] using e.symm

end LieLean.QuantumGroup
