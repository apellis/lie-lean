/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.ParabolicRecursion.SignProjection

/-!
# Parabolic Kazhdan–Lusztig multiplication: the sign module

## Conventions

We use `q = v²`, `(T_s-q)(T_s+1)=0`, and `C'_s=v⁻¹(T_s+1)`.
The representatives `W^J` index cosets `d W_J` and have no right `J`-descents.
For both inducing characters `u=q` (`ind`) and `u=-1` (`sgn`),
`m_d=[T_d]`, `m̃_d=v^{-ℓ(d)}m_d`, and
`C^{J,u}_w=v^{-ℓ(w)} Σ_x P^{J,u}_{x,w}(v²)m_x`.
The imported `parabolicKLMu` is `[v⁻¹][m̃_x]C^{J,u}_w` for either character.

This file proves the multiplication recursion for `u=-1`, with no finiteness hypotheses.
The `u=q` multiplication recursion is not asserted here. Its correction set must also
include the boundary indices `x` for which `sx` is not minimal, unlike the sign case.

## Main results

* `klSimple_smul_parabolicKLBasis_sgn_of_lt`: the sign ascent formula.
* `klSimple_smul_parabolicKLBasis_sgn_of_not_mem`: the sign boundary formula.
* `klSimple_smul_parabolicKLBasis_sgn_of_gt`: the descent eigenvalue formula.

## References

V. Deodhar, *On some geometric aspects of Bruhat orderings II. The parabolic analogue of
Kazhdan–Lusztig polynomials*, J. Algebra **111** (1987), 483–506.
The proofs are our own, by projecting the ordinary multiplication theorem. Nonminimal
ordinary canonical elements vanish in the sign quotient,
while sign parabolic μ-coefficients on minimal representatives equal the ordinary ones.
-/

open LaurentPolynomial CoxeterSystem

namespace IwahoriHeckeAlgebra

attribute [local instance] Classical.propDecidable

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {J : Set B}

local prefix:100 "ℓ " => cs.length
local notation "χ₋" => sgn (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])
local notation "h₋" => isBarCompatible_sgn (cs.parabolicCoxeterSystem J)

/-- Extend the sign canonical family by zero away from minimal representatives. -/
noncomputable def parabolicSignKLBasis (w : W) : InducedModule χ₋ :=
  if hw : w ∈ cs.minCosetReps J then parabolicKLBasis h₋ ⟨w, hw⟩ else 0

/-- Projection of any ordinary canonical element, including nonminimal indices.
Reconstructed from the sign projection and right-descent vanishing. -/
theorem mk_klBasis_eq_parabolicSignKLBasis (w : W) :
    (Submodule.Quotient.mk (klBasis cs w) : InducedModule χ₋) =
      parabolicSignKLBasis cs w := by
  classical
  rw [parabolicSignKLBasis]
  split_ifs with hw
  · exact mk_klBasis_eq_parabolicKLBasis_sgn J ⟨w, hw⟩
  · exact mk_klBasis_eq_zero_sgn_of_not_mem_minCosetReps cs hw

/-- The finite μ-correction in the sign multiplication formula. The sum is over `z ≤ w`
with `sz < z`; nonminimal indices contribute zero. -/
noncomputable def parabolicSignCorrection (i : B) (w : cs.minCosetReps J) :
    InducedModule χ₋ :=
  ∑ z ∈ descentsBelow cs i w,
    if hz : z ∈ cs.minCosetReps J then
      parabolicKLMu h₋ ⟨z, hz⟩ w • parabolicKLBasis h₋ ⟨z, hz⟩ else 0

/-- The projected ordinary ascent recursion, valid also when `sw` is nonminimal.
Reconstructed from the ordinary multiplication theorem and sign projection. -/
theorem klSimple_smul_parabolicKLBasis_sgn (i : B) (w : cs.minCosetReps J)
    (hw : ℓ w < ℓ (cs.simple i * w)) :
    klSimple cs i • parabolicKLBasis h₋ w =
      parabolicSignKLBasis cs (cs.simple i * w) + parabolicSignCorrection cs i w := by
  classical
  have h := congrArg
    (fun a => (Submodule.Quotient.mk a : InducedModule χ₋))
    (klSimple_mul_klBasis cs hw)
  rw [show (Submodule.Quotient.mk (klSimple cs i * klBasis cs w) :
      InducedModule χ₋) = klSimple cs i • Submodule.Quotient.mk (klBasis cs w) from rfl,
    mk_klBasis_eq_parabolicKLBasis_sgn J w, Submodule.Quotient.mk_add,
    mk_klBasis_eq_parabolicSignKLBasis] at h
  rw [h]
  congr 1
  rw [parabolicSignCorrection]
  change (inducedIdeal χ₋).mkQ (∑ z ∈ descentsBelow cs i w,
    klMu cs z w • klBasis cs z) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul]
  change klMu cs z w • (Submodule.Quotient.mk (klBasis cs z) : InducedModule χ₋) = _
  rw [mk_klBasis_eq_parabolicSignKLBasis, parabolicSignKLBasis]
  split_ifs with hz
  · rw [parabolicKLMu_sgn]
  · exact smul_zero _

/-- Deodhar's sign-module ascent multiplication recursion, for arbitrary `J`.
Reconstructed by projecting the ordinary multiplication theorem. -/
theorem klSimple_smul_parabolicKLBasis_sgn_of_lt (i : B) (w : cs.minCosetReps J)
    (hw : ℓ w < ℓ (cs.simple i * w))
    (hsw : cs.simple i * (w : W) ∈ cs.minCosetReps J) :
    klSimple cs i • parabolicKLBasis h₋ w =
      parabolicKLBasis h₋ ⟨cs.simple i * w, hsw⟩ + parabolicSignCorrection cs i w := by
  rw [klSimple_smul_parabolicKLBasis_sgn cs i w hw, parabolicSignKLBasis, dite_eq_left hsw]

/-- In the sign boundary case the leading term vanishes, but the lower μ-sum remains.
Reconstructed by projecting the ordinary multiplication theorem. -/
theorem klSimple_smul_parabolicKLBasis_sgn_of_not_mem (i : B) (w : cs.minCosetReps J)
    (hw : ℓ w < ℓ (cs.simple i * w))
    (hsw : cs.simple i * (w : W) ∉ cs.minCosetReps J) :
    klSimple cs i • parabolicKLBasis h₋ w = parabolicSignCorrection cs i w := by
  rw [klSimple_smul_parabolicKLBasis_sgn cs i w hw, parabolicSignKLBasis, dite_eq_right hsw,
    zero_add]

/-- A left descent acts by `v+v⁻¹` on the sign canonical element.
Reconstructed from the ordinary descent eigenvalue relation by projection. -/
theorem klSimple_smul_parabolicKLBasis_sgn_of_gt (i : B) (w : cs.minCosetReps J)
    (hw : ℓ (cs.simple i * w) < ℓ w) :
    klSimple cs i • parabolicKLBasis h₋ w =
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) •
        parabolicKLBasis h₋ w := by
  have h := congrArg
    (fun a => (Submodule.Quotient.mk a : InducedModule χ₋))
    (T_simple_mul_klBasis cs hw)
  change T cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) (cs.simple i) •
      (Submodule.Quotient.mk (klBasis cs w) : InducedModule χ₋) =
      Submodule.Quotient.mk ((LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) • klBasis cs w) at h
  rw [Submodule.Quotient.mk_smul, mk_klBasis_eq_parabolicKLBasis_sgn J w] at h
  rw [klSimple, smul_assoc, add_smul, one_smul, h, smul_add, smul_smul, ← T_add]
  norm_num [add_smul]

/-- The complete sign-module `C'_s` multiplication formula, for arbitrary Coxeter systems
and arbitrary parabolic subgroups. In the ascent branch the extended leading term is zero
exactly when `sw` is not minimal. Reconstructed from the ordinary recursion by projection. -/
theorem klBasis_simple_smul_parabolicKLBasis_sgn (i : B) (w : cs.minCosetReps J) :
    klBasis cs (cs.simple i) • parabolicKLBasis h₋ w =
      if ℓ w < ℓ (cs.simple i * w) then
        parabolicSignKLBasis cs (cs.simple i * w) + parabolicSignCorrection cs i w
      else
        (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) •
          parabolicKLBasis h₋ w := by
  rw [klBasis_simple]
  split_ifs with hw
  · exact klSimple_smul_parabolicKLBasis_sgn cs i w hw
  · apply klSimple_smul_parabolicKLBasis_sgn_of_gt cs i w
    rcases cs.length_simple_mul (w : W) i with h | h <;> omega

end IwahoriHeckeAlgebra
