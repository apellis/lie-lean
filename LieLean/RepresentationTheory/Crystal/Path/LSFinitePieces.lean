/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.LSTwoPiece
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite piecewise-affine position-chain criteria

## Main definitions

* `LittelmannPath.finitePiecePosition`: the cumulative displacement at a rational breakpoint.

## Main results

* `LittelmannPath.isLS_finitePieces_iff`: for a supplied finite piecewise-affine path,
  the global LS condition is equivalent to position chains at the internal breakpoints.
* `LittelmannPath.isLS_rationalPieces_iff`: the cumulative affine formula with rational
  breakpoints, as in Littelmann's normalization.

The directions may be arbitrary members of the supplied `LSData` orbit. Equal consecutive
slopes are allowed: a redundant subdivision needs only a reflexive chain. Neither
endpoint contributes a chain. These are criteria for supplied path objects, not constructors.
The path type already requires an integral endpoint and continuous simple-coroot pairings.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
499–525, Section 4, printed pp. 509–510, definitions around Lemma 4.3. The finite affine
formula follows the source. The proofs of the local-to-finite bridge are reconstructed.
Here chains are the repository's position chains, not a newly established comparison with
all source time-times-coroot a-chains. No reparametrization quotient or crystal isomorphism
is asserted. In the actual realization `P.lsData hA hΛ`, steps are saturated descending
Bruhat covers in the dominant integral Weyl orbit.
-/

open Set

namespace LittelmannPath

private lemma exists_fin_Ico {n : ℕ} (a : Fin (n + 1) → ℝ) {t : ℝ}
    (ht : t ∈ Ico (a 0) (a (Fin.last n))) :
    ∃ i : Fin n, t ∈ Ico (a i.castSucc) (a i.succ) := by
  classical
  have hex : ∃ j, t < a j := ⟨Fin.last n, ht.2⟩
  let j := Fin.find (fun j ↦ t < a j) hex
  have hj : j ≠ 0 := by
    intro h
    have hs := Fin.find_spec hex
    change t < a j at hs
    rw [h] at hs
    exact (not_lt_of_ge ht.1) hs
  refine ⟨j.pred hj, ?_, ?_⟩
  · exact le_of_not_gt (Fin.find_min hex (Fin.castSucc_pred_lt hj))
  · simpa [Fin.succ_pred] using Fin.find_spec hex

private lemma exists_fin_Ioc {n : ℕ} (a : Fin (n + 1) → ℝ) {t : ℝ}
    (ht : t ∈ Ioc (a 0) (a (Fin.last n))) :
    ∃ i : Fin n, t ∈ Ioc (a i.castSucc) (a i.succ) := by
  classical
  have hex : ∃ j, t ≤ a j := ⟨Fin.last n, ht.2⟩
  let j := Fin.find (fun j ↦ t ≤ a j) hex
  have hj : j ≠ 0 := by
    intro h
    have hs := Fin.find_spec hex
    change t ≤ a j at hs
    rw [h] at hs
    exact (not_le_of_gt ht.1) hs
  refine ⟨j.pred hj, ?_, ?_⟩
  · exact lt_of_not_ge (Fin.find_min hex (Fin.castSucc_pred_lt hj))
  · simpa [Fin.succ_pred] using Fin.find_spec hex

variable {ι X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
  {D : CartanDatum ι X} {S : D.PathSpace ℝ V} {L : LSData S}
  {π : LittelmannPath S}

/-- For finitely many affine pieces, the only possibly nonreflexive local position chains
are at internal breakpoints. There are `n + 1` pieces, so `n = 0` includes a single segment.
The endpoint conditions concern only the inward directions. Reconstructed from the local
LS definition; compare [Lit95, Section 4, p. 510] for the finite-breakpoint formulation. -/
theorem isLS_finitePieces_iff {n : ℕ} {a : Fin (n + 2) → ℝ}
    (ha : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last (n + 1)) = 1)
    {x : Fin (n + 1) → X} (hx : ∀ i, x i ∈ L.O) {p : Fin (n + 1) → V}
    (hpiece : ∀ i t, t ∈ Icc (a i.castSucc) (a i.succ) →
      π t = p i + t • S.embed (x i)) :
    IsLS L π ↔ ∀ i : Fin n,
      L.Chain (π (a i.succ.castSucc)) (x i.castSucc) (x i.succ) := by
  have hr (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Ico (a i.castSucc) (a i.succ)) :
      π.HasRightDir t (x i) := hasRightDir_of_affine ht.1 ht.2 (hpiece i)
  have hl (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Ioc (a i.castSucc) (a i.succ)) :
      π.HasLeftDir t (x i) := hasLeftDir_of_affine ht.1 ht.2 (hpiece i)
  have hbreak (i : Fin n) : a i.succ.castSucc ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · rw [← ha0]
      exact ha (by simp)
    · rw [← ha1]
      exact ha (Fin.castSucc_lt_last _)
  constructor
  · intro h i
    exact h.chain _ (hbreak i) _ _
      (hl i.castSucc ⟨ha (by simp), by simp [Fin.castSucc_succ]⟩)
      (hr i.succ ⟨le_rfl, ha Fin.castSucc_lt_succ⟩)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨i, hi⟩ := exists_fin_Ico a (by simpa [ha0, ha1] using ht)
      exact ⟨x i, hx i, hr i hi⟩
    · intro t ht
      obtain ⟨i, hi⟩ := exists_fin_Ioc a (by simpa [ha0, ha1] using ht)
      exact ⟨x i, hx i, hl i hi⟩
    · intro t ht u v hu hv
      obtain ⟨i, hi⟩ := exists_fin_Ico a
        (by simpa [ha0, ha1] using (⟨ht.1.le, ht.2⟩ : t ∈ Ico (0 : ℝ) 1))
      have hv' := hv.unique (hr i hi)
      subst v
      rcases lt_or_eq_of_le hi.1 with hlt | heq
      · have hu' := hu.unique (hl i ⟨hlt, hi.2.le⟩)
        subst u
        exact .refl
      · have hi0 : i ≠ 0 := by
          intro hi0
          subst i
          simp [ha0] at heq
          exact ht.1.ne' heq.symm
        obtain ⟨j, rfl⟩ : ∃ j : Fin n, j.succ = i :=
          ⟨i.pred hi0, Fin.succ_pred _ _⟩
        have hu' := hu.unique (hl j.castSucc ⟨by
          rw [← heq]
          exact ha (by simp), by simpa [Fin.castSucc_succ] using heq.symm.le⟩)
        subst u
        rw [← heq]
        exact h j

variable (S) in
/-- Cumulative displacement before a breakpoint of a finite rational subdivision.
This is the partial sum in [Lit95, Section 4, p. 510], without a direction-order assumption.
The sum uses only pieces strictly before `i`; in particular the value at `0` is zero. -/
noncomputable def finitePiecePosition {n : ℕ} (a : Fin (n + 1) → ℚ)
    (x : Fin n → X) (i : Fin (n + 1)) : V :=
  ∑ j : Fin n with j.castSucc < i,
    ((a j.succ : ℝ) - (a j.castSucc : ℝ)) • S.embed (x j)

/-- The initial cumulative displacement is zero. -/
@[simp] theorem finitePiecePosition_zero {n : ℕ} (a : Fin (n + 1) → ℚ)
    (x : Fin n → X) : finitePiecePosition S a x 0 = 0 := by
  simp [finitePiecePosition]

/-- Finite rational piecewise-linear characterization for an already supplied path.
There are `n + 1` orbit directions and strictly increasing rational breakpoints from `0` to `1`.
The literal cumulative affine formula is a hypothesis, not an LS or integrality assumption.
The conclusion is the actual position-chain condition at every internal breakpoint.

This follows the affine normalization in [Lit95, Section 4, p. 510]. Unlike the source's
strictly decreasing direction presentation, redundant equal-direction subdivisions are
permitted. Identifying these position chains with all source a-chains requires a separate
root-lattice congruence argument, which is not claimed here. -/
theorem isLS_rationalPieces_iff {n : ℕ} {a : Fin (n + 2) → ℚ}
    (ha : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last (n + 1)) = 1)
    {x : Fin (n + 1) → X} (hx : ∀ i, x i ∈ L.O)
    (hpiece : ∀ i t, t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ) →
      π t = finitePiecePosition S a x i.castSucc +
        (t - (a i.castSucc : ℝ)) • S.embed (x i)) :
    IsLS L π ↔ ∀ i : Fin n,
      L.Chain (finitePiecePosition S a x i.succ.castSucc) (x i.castSucc) (x i.succ) := by
  have ha' : StrictMono (fun i ↦ (a i : ℝ)) := by
    intro i j hij
    change (a i : ℝ) < (a j : ℝ)
    exact_mod_cast ha hij
  have hshape (i : Fin (n + 1)) (t : ℝ)
      (ht : t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ)) :
      π t = (finitePiecePosition S a x i.castSucc -
        (a i.castSucc : ℝ) • S.embed (x i)) + t • S.embed (x i) := by
    rw [hpiece i t ht, sub_smul]
    abel
  rw [isLS_finitePieces_iff ha' (by simp [ha0]) (by simp [ha1]) hx hshape]
  have hpos (i : Fin n) : π (a i.succ.castSucc : ℝ) =
      finitePiecePosition S a x i.succ.castSucc := by
    rw [hpiece i.succ _ ⟨le_rfl, (ha' Fin.castSucc_lt_succ).le⟩]
    simp
  simp only [hpos]

end LittelmannPath
