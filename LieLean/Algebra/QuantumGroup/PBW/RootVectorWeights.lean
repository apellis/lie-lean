/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RootVectorsQuantum

/-!
# Conjugation weights of quantum root vectors

The root vector `T_{i₁} ⋯ T_{iₙ}(E_{i_{n+1}})` has character
`s_{i₁} ⋯ s_{iₙ}(α_{i_{n+1}})` for conjugation by `K_μ`. We encode this character directly in
`Hom(Y, ℤ)`, using the existing coweight reflections `reflY`. This works for every word;
reducedness is needed only for the accompanying membership in `U⁺` in finite type.

## Main definitions

* `QuantumGroup.adWeightSpace`: the conjugation weight space in `U`.
* `QuantumGroup.wordWeightAction`: successive simple reflections on characters.
* `QuantumGroup.rootVectorWeight`: the prefix-reflected simple-root character.

## Main results

* `QuantumGroup.rootVector_mem_adWeightSpace`: weights for any family with braid generator images.
* `QuantumGroup.rootVector_conj_of_not_root`: the formula for the actual braid automorphisms.
* `QuantumGroup.rootVector_mem_adjoin_and_adWeightSpace_of_isFiniteCartan`: the reduced-word
  root vector belongs to `U⁺` and has the specified conjugation character.

This does not assert independence, spanning, a PBW basis, or identification with a nonnegative
root-lattice graded piece of `U⁺`. No finite-rank or characteristic-zero assumption is needed
for the conjugation formula; the actual automorphisms require a nonzero parameter not a root
of unity.

## References

* J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §§4.7, 8.18, 8.21.
* G. Lusztig, *Introduction to quantum groups*, §§37.1.2–37.1.3.

The proofs here are reconstructed from the generator relations.
-/

noncomputable section

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- The character-`χ` weight space for conjugation by the torus; equivalently,
`K_μ x = v^{χ(μ)} x K_μ`. See Jantzen §4.7; reconstructed from the relations. -/
def adWeightSpace (χ : Y →+ ℤ) : Submodule k (QuantumGroup R v) where
  carrier := {x | ∀ μ, K R v μ * x = v ^ χ μ • (x * K R v μ)}
  add_mem' {a b} ha hb μ := by rw [mul_add, add_mul, ha μ, hb μ, smul_add]
  zero_mem' μ := by simp
  smul_mem' c x hx μ := by rw [mul_smul_comm, hx μ, smul_mul_assoc, smul_comm]

variable {R v}

/-- Simple root vectors have their simple-root characters. -/
lemma E_mem_adWeightSpace (i : I) : E R v i ∈ adWeightSpace R v (R.root i) :=
  fun μ ↦ K_mul_E R v μ i

/-- The commutation definition gives the conjugation eigenvalue equation. -/
lemma conj_eq_of_mem_adWeightSpace {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) (μ : Y) :
    K R v μ * x * K R v (-μ) = v ^ χ μ • x := by
  rw [hx μ, smul_mul_assoc, mul_assoc, K_mul_K_neg, mul_one]

/-- A braid generator sends weight `χ` to `sᵢχ = χ ∘ sᵢ`.
See Jantzen §8.18; reconstructed using only the torus generator formula. -/
theorem HasBraidGeneratorImages.map_mem_adWeightSpace {i : I}
    {T : QuantumGroup R v →ₐ[k] QuantumGroup R v} (HT : HasBraidGeneratorImages i T)
    {χ : Y →+ ℤ} {x : QuantumGroup R v} (hx : x ∈ adWeightSpace R v χ) :
    T x ∈ adWeightSpace R v (χ.comp (reflY R i)) := fun μ ↦ by
  have h := congrArg T (hx (reflY R i μ))
  simpa only [map_mul, map_smul, HT.map_K, reflY_reflY, AddMonoidHom.comp_apply] using h

variable (R)

omit [DecidableEq I] in
/-- Apply the simple reflections of a word to a character, with the leftmost reflection
acting last: `s_{i₁} ⋯ s_{iₙ} χ`. -/
def wordWeightAction : List I → (Y →+ ℤ) → (Y →+ ℤ)
  | [], χ => χ
  | i :: ω, χ => (wordWeightAction ω χ).comp (reflY R i)

omit [DecidableEq I] in
/-- The character of the `n`-th root vector: the first `n` simple reflections applied to
the simple root at position `n`. Positions are zero-based. -/
def rootVectorWeight (ω : List I) (n : ℕ) (hn : n < ω.length) : Y →+ ℤ :=
  wordWeightAction R (ω.take n) (R.root ω[n])

omit [DecidableEq I] in
/-- The character reflection is the usual `sᵢχ = χ - χ(αᵢ∨) αᵢ`.
This identifies the action used in `rootVectorWeight` with simple-root reflection. -/
lemma comp_reflY_eq (χ : Y →+ ℤ) (i : I) :
    χ.comp (reflY R i) = χ - χ (R.coroot i) • R.root i := by
  ext μ
  simp only [AddMonoidHom.comp_apply, reflY_apply, map_sub, map_zsmul,
    AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, smul_eq_mul]
  rw [mul_comm]

variable {R}
variable {T : I → QuantumGroup R v ≃ₐ[k] QuantumGroup R v}

/-- A word of braid automorphisms transforms conjugation characters by the same word
of simple reflections. -/
theorem word_braid_mem_adWeightSpace
    (hT : ∀ i, HasBraidGeneratorImages i (T i).toAlgHom)
    (ω : List I) {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) :
    (ω.map T).prod x ∈ adWeightSpace R v (wordWeightAction R ω χ) := by
  induction ω with
  | nil => simpa [wordWeightAction] using hx
  | cons i ω ih =>
    simpa only [List.map_cons, List.prod_cons, AlgEquiv.mul_apply, wordWeightAction,
      AlgEquiv.coe_toAlgHom] using
      (hT i).map_mem_adWeightSpace ih

/-- The weight of a root vector along any word is its prefix-reflected simple root.
See Jantzen §§8.18, 8.21; proof reconstructed by iteration. -/
theorem rootVector_mem_adWeightSpace
    (hT : ∀ i, HasBraidGeneratorImages i (T i).toAlgHom)
    (ω : List I) (n : ℕ) (hn : n < ω.length) :
    CoxeterSystem.rootVector T (E R v) ω n hn ∈
      adWeightSpace R v (rootVectorWeight R ω n hn) :=
  word_braid_mem_adWeightSpace hT (ω.take n) (E_mem_adWeightSpace ω[n])

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- The actual Lusztig braid automorphisms have the predicted root-vector characters,
over any field, for a nonzero parameter not a root of unity. -/
theorem rootVector_mem_adWeightSpace_of_not_root (ω : List I) (n : ℕ)
    (hn : n < ω.length) :
    CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn ∈
      adWeightSpace R v (rootVectorWeight R ω n hn) :=
  rootVector_mem_adWeightSpace
    (braidEquivOfGeneric_images
      (fun i ↦ (shortNode_braidGeneric_of_not_root hv i).sub_ne)
      (braidSerreGeneric_of_not_root hv)) ω n hn

/-- **Root-vector conjugation formula** for the actual braid automorphisms:
`K_μ E_β K_{-μ} = v^{β(μ)} E_β`, where `β = s_{i₁} ⋯ s_{iₙ}(α_{i_{n+1}})`.
See Jantzen §§8.18, 8.21; reconstructed from the generator relations. -/
theorem rootVector_conj_of_not_root (ω : List I) (n : ℕ) (hn : n < ω.length) (μ : Y) :
    K R v μ * CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn *
        K R v (-μ) =
      v ^ rootVectorWeight R ω n hn μ •
        CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn :=
  conj_eq_of_mem_adWeightSpace (rootVector_mem_adWeightSpace_of_not_root hv ω n hn) μ

/-- **Finite-type reduced-word root vectors** lie in `U⁺` and have the prefix-reflected
simple-root character. This combines the existing positivity theorem with the conjugation
weight formula, not with an identification of root-lattice graded pieces.
See Jantzen §§8.18, 8.21; reconstructed from the two component results. -/
theorem rootVector_mem_adjoin_and_adWeightSpace_of_isFiniteCartan [Fintype I]
    {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
    (hA : D.cartanMatrix.IsFiniteCartan) {ω : List I} (hω : cs.IsReduced ω)
    (n : ℕ) (hn : n < ω.length) :
    CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn ∈
        Algebra.adjoin k (Set.range (E R v)) ∧
      CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn ∈
        adWeightSpace R v (rootVectorWeight R ω n hn) := by
  exact ⟨rootVector_mem_adjoin_of_not_root
    (LusztigCartanDatum.braidOuterCondition_of_isFiniteCartan hA)
    (fun _ _ hij ↦ hA.mul_le_three hij) hv hω n hn,
    rootVector_mem_adWeightSpace_of_not_root hv ω n hn⟩

end QuantumGroup
