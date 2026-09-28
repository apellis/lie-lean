/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Stability
import Mathlib.Topology.UniformSpace.Real

/-!
# A two-piece rational LS-path characterization

This file treats normalized representatives with one rational breakpoint,
not arbitrary continuous paths modulo an unconstructed reparametrization quotient.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
499–525, Section 4, definitions preceding and following Lemma 4.3 (consulted at
https://www.mi.uni-koeln.de/~littelma/papers/RootOperator.pdf).
The source orders directions decreasingly toward the dominant weight and requires
`a * <preceding direction, coroot> ∈ ℤ` at each saturated reflection step.
The proofs below are reconstructed; no general crystal isomorphism is assumed.
-/

open Set

namespace LittelmannPath

variable {ι X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
  {D : CartanDatum ι X} {S : D.PathSpace ℝ V} {L : LSData S}

/-- At a simple descending cover, the position-chain condition at the normalized
breakpoint is precisely the source's time-times-coroot integrality condition.
This is the simple-cover case of the a-chain definition in [Lit95, Section 4]. -/
theorem chain_simple_break_iff {x : X} {i : ι} (hx : x ∈ L.O)
    (hi : 0 < D.coroot i x) (a : ℝ) :
    L.Chain (a • S.embed (D.reflection i x)) (D.reflection i x) x ↔
      ∃ n : ℤ, a * (D.coroot i x : ℝ) = n := by
  have heq : S.coroot i (a • S.embed (D.reflection i x)) =
      -(a * (D.coroot i x : ℝ)) := by
    simp [S.coroot_embed]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_int (i := i)
      (Or.inl ⟨by simp only [D.coroot_reflection]; omega, hi⟩)
    exact ⟨-n, by rw [heq] at hn; push_cast; linarith⟩
  · rintro ⟨n, hn⟩
    exact Relation.ReflTransGen.single ⟨S.coroot i, L.step_simple i x hx hi,
      -n, by rw [heq, hn, Int.cast_neg]⟩

variable {π : LittelmannPath S}

/-- An explicit affine formula on a nontrivial closed interval supplies its right direction. -/
lemma hasRightDir_of_affine {u v t : ℝ} {x : X} {p : V}
    (hut : u ≤ t) (htv : t < v)
    (h : ∀ s ∈ Icc u v, π s = p + s • S.embed x) : π.HasRightDir t x := by
  refine ⟨v - t, sub_pos.mpr htv, fun s hs ↦ ?_⟩
  rw [h s ⟨hut.trans hs.1, by linarith [hs.2]⟩, h t ⟨hut, htv.le⟩,
    sub_smul]
  abel

/-- An explicit affine formula on a nontrivial closed interval supplies its left direction. -/
lemma hasLeftDir_of_affine {u v t : ℝ} {x : X} {p : V}
    (hut : u < t) (htv : t ≤ v)
    (h : ∀ s ∈ Icc u v, π s = p + s • S.embed x) : π.HasLeftDir t x := by
  refine ⟨t - u, sub_pos.mpr hut, fun s hs ↦ ?_⟩
  rw [h s ⟨by linarith [hs.1], hs.2.trans htv⟩, h t ⟨hut.le, htv⟩,
    sub_smul]
  abel

/-- For an actual two-piece affine path, all local LS conditions reduce to the
single breakpoint chain. This is a direct local-to-finite bridge, not an LS hypothesis. -/
theorem isLS_twoPiece_iff {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {x y : X} (hx : x ∈ L.O) (hy : y ∈ L.O)
    (hleft : ∀ t ∈ Icc (0 : ℝ) a, π t = t • S.embed x)
    (hright : ∀ t ∈ Icc a 1, π t = a • S.embed x + (t - a) • S.embed y) :
    IsLS L π ↔ L.Chain (a • S.embed x) x y := by
  have hl : ∀ t ∈ Icc (0 : ℝ) a, π t = (0 : V) + t • S.embed x := by
    simpa using hleft
  have hr : ∀ t ∈ Icc a 1,
      π t = (a • S.embed x - a • S.embed y) + t • S.embed y := by
    intro t ht
    rw [hright t ht, sub_smul]
    abel
  have hpa := hleft a ⟨ha.1.le, le_rfl⟩
  constructor
  · intro h
    rw [← hpa]
    exact h.chain a ha x y (hasLeftDir_of_affine ha.1 le_rfl hl)
      (hasRightDir_of_affine le_rfl ha.2 hr)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      by_cases hta : t < a
      · exact ⟨x, hx, hasRightDir_of_affine ht.1 hta hl⟩
      · exact ⟨y, hy, hasRightDir_of_affine (le_of_not_gt hta) ht.2 hr⟩
    · intro t ht
      by_cases hta : t ≤ a
      · exact ⟨x, hx, hasLeftDir_of_affine ht.1 hta hl⟩
      · exact ⟨y, hy, hasLeftDir_of_affine (lt_of_not_ge hta) ht.2 hr⟩
    · intro t ht u v hu hv
      rcases lt_trichotomy t a with hta | rfl | hta
      · have hu' := hu.unique (hasLeftDir_of_affine ht.1 hta.le hl)
        have hv' := hv.unique (hasRightDir_of_affine ht.1.le hta hl)
        subst u
        subst v
        exact .refl
      · have hu' := hu.unique (hasLeftDir_of_affine ha.1 le_rfl hl)
        have hv' := hv.unique (hasRightDir_of_affine le_rfl ha.2 hr)
        subst u
        subst v
        rwa [hpa]
      · have hu' := hu.unique (hasLeftDir_of_affine hta ht.2.le hr)
        have hv' := hv.unique (hasRightDir_of_affine hta.le ht.2 hr)
        subst u
        subst v
        exact .refl

/-- Concrete rational two-direction characterization, with a simple descending cover.
For the normalized representative with slopes `s_i x, x` and rational breakpoint `a`,
the repository's `IsLS` is equivalent to the numerical a-chain condition.
For `L = P.lsData hA hΛ`, these directions lie in the actual Weyl orbit. The source
uses `a * <s_i x, α_i∨>`, whose sign is immaterial for integrality.
Source: [Lit95, Section 4, a-chain and LS-path definitions]; reconstructed proof. -/
theorem isLS_simple_twoPiece_iff {a : ℚ} (ha : a ∈ Ioo (0 : ℚ) 1)
    {x : X} {i : ι} (hx : x ∈ L.O) (hi : 0 < D.coroot i x)
    (hleft : ∀ t ∈ Icc (0 : ℝ) (a : ℝ), π t = t • S.embed (D.reflection i x))
    (hright : ∀ t ∈ Icc (a : ℝ) 1,
      π t = (a : ℝ) • S.embed (D.reflection i x) + (t - a) • S.embed x) :
    IsLS L π ↔ ∃ n : ℤ, a * (D.coroot i x : ℚ) = n := by
  have ha' : (a : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  rw [isLS_twoPiece_iff ha' (L.reflection_mem i x hx) hx hleft hright,
    chain_simple_break_iff hx hi]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by exact_mod_cast hn⟩

end LittelmannPath
