/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import LieLean.Algebra.QuantumGroup.RestrictedBraidIsometry.ClosedNorm

/-!
# Generator and word pairings

Multidegrees and complementary norms identify pairings of generators with words.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF
namespace RestrictedBraidIsometry
variable {I : Type*} [DecidableEq I] (D : LusztigCartanDatum I) (i : I)
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

/-- Bounded adjoint generators at the fixed node. -/
def Gen := {p : I × ℕ // i ≠ p.1 ∧ p.2 ≤ negA D i p.1}

def complement (g : Gen D i) : Gen D i :=
  ⟨(g.val.1, negA D i g.val.1 - g.val.2), g.property.1, Nat.sub_le _ _⟩

omit [DecidableEq I] in
lemma complement_complement (g : Gen D i) : complement D i (complement D i g) = g := by
  apply Subtype.ext
  simp [complement, Nat.sub_sub_self g.property.2]

omit [DecidableEq I] in
lemma complement_injective : Function.Injective (complement D i) := by
  intro a b h
  have := congrArg (complement D i) h
  simpa only [complement_complement] using this

def generatorDegree (g : Gen D i) : I →₀ ℕ :=
  Finsupp.single g.val.1 1 + Finsupp.single i g.val.2

def awayDegree (ν : I →₀ ℕ) : ℕ := ν.sum (fun j n ↦ if j = i then 0 else n)

lemma awayDegree_add (ν μ : I →₀ ℕ) :
    awayDegree i (ν + μ) = awayDegree i ν + awayDegree i μ := by
  apply Finsupp.sum_add_index
  · intros; simp
  · intro j _ a b; split_ifs <;> simp

@[simp] lemma awayDegree_zero : awayDegree i (0 : I →₀ ℕ) = 0 := by
  simp [awayDegree]

@[simp] lemma awayDegree_generator (g : Gen D i) :
    awayDegree i (generatorDegree D i g) = 1 := by
  rw [generatorDegree, awayDegree_add]
  simp [awayDegree, Finsupp.sum_single_index, Ne.symm g.property.1]

omit [DecidableEq I] in
lemma generatorDegree_injective : Function.Injective (generatorDegree D i) := by
  classical
  intro a b h
  have hj : a.val.1 = b.val.1 := by
    by_contra hne
    have hh := congrArg (fun ν : I →₀ ℕ ↦ ν a.val.1) h
    simp [generatorDegree, a.property.1, hne] at hh
  have hn := congrArg (fun ν : I →₀ ℕ ↦ ν i) h
  simp only [generatorDegree, Finsupp.add_apply, Finsupp.single_eq_same] at hn
  apply Subtype.ext
  apply Prod.ext hj
  simpa [Ne.symm a.property.1, Ne.symm b.property.1] using hn

def sourceGen (g : Gen D i) : Quotient D 𝕧 :=
  toQuotient D 𝕧 (skewDividedGenerator D 𝕧 i g.val.1 g.val.2)

variable [Finite I]

def targetGen (g : Gen D i) : Quotient D 𝕧 :=
  quotientRev D (sourceGen D i (complement D i g))

/-- Products preserve list order; reversal acts on each generator only. -/
def generatorWord (f : Gen D i → Quotient D 𝕧) : List (Gen D i) → Quotient D 𝕧
  | [] => 1
  | g :: l => f g * generatorWord f l

abbrev sourceWord := generatorWord D i (sourceGen D i)
abbrev targetWord := generatorWord D i (targetGen D i)

def wordDegree (f : Gen D i → Gen D i) : List (Gen D i) → I →₀ ℕ
  | [] => 0
  | g :: l => generatorDegree D i (f g) + wordDegree f l

omit [Finite I] in
lemma awayDegree_word (f : Gen D i → Gen D i) (l : List (Gen D i)) :
    awayDegree i (wordDegree D i f l) = l.length := by
  induction l with
  | nil => simp [wordDegree]
  | cons g l ih => simp [wordDegree, awayDegree_add, ih, Nat.add_comm]

omit [Finite I] in
lemma sourceGen_degree (g : Gen D i) :
    sourceGen D i g ∈ RightStringComparison.degreeSpace (D := D) (generatorDegree D i g) := by
  refine ⟨skewDividedGenerator D 𝕧 i g.val.1 g.val.2, ?_, rfl⟩
  apply Submodule.smul_mem
  simpa [generatorDegree, Finsupp.smul_single] using
    (RightStringComparison.skewGenerator_degree (D := D) i g.val.1 g.val.2)

lemma targetGen_degree (g : Gen D i) :
    targetGen D i g ∈ RightStringComparison.degreeSpace (D := D)
      (generatorDegree D i (complement D i g)) :=
  RightStringComparison.degree_rev (sourceGen_degree D i (complement D i g))

omit [Finite I] in
lemma generatorWord_degree (f : Gen D i → Quotient D 𝕧) (σ : Gen D i → Gen D i)
    (hf : ∀ g, f g ∈ RightStringComparison.degreeSpace (D := D) (generatorDegree D i (σ g)))
    (l : List (Gen D i)) :
    generatorWord D i f l ∈ RightStringComparison.degreeSpace (D := D) (wordDegree D i σ l) := by
  induction l with
  | nil => exact ⟨1, one_mem_weightSpace, (toQuotient D 𝕧).map_one⟩
  | cons g l ih => exact RightStringComparison.degree_mul (hf g) ih

lemma quotientForm_degree_ne {ν μ : I →₀ ℕ} (hne : ν ≠ μ)
    {x y : Quotient D 𝕧} (hx : x ∈ RightStringComparison.degreeSpace (D := D) ν)
    (hy : y ∈ RightStringComparison.degreeSpace (D := D) μ) : quotientForm D x y = 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  change quotientForm D (toQuotient D 𝕧 a) (toQuotient D 𝕧 b) = 0
  rw [quotientForm_toQuotient]
  exact form_eq_zero_of_ne D 𝕧 hne ha hb

lemma generatorWord_pairing_zero (f : Gen D i → Quotient D 𝕧) (σ : Gen D i → Gen D i)
    (hf : ∀ g, f g ∈ RightStringComparison.degreeSpace (D := D) (generatorDegree D i (σ g)))
    (g : Gen D i) (l : List (Gen D i)) (hl : l.length ≠ 1) :
    quotientForm D (f g) (generatorWord D i f l) = 0 := by
  apply quotientForm_degree_ne D
    (ν := generatorDegree D i (σ g)) (μ := wordDegree D i σ l) _ (hf g)
    (generatorWord_degree D i f σ hf l)
  intro h
  have hh := congrArg (awayDegree i) h
  rw [awayDegree_generator, awayDegree_word] at hh
  exact hl hh.symm

lemma one_word_pairing_zero (f : Gen D i → Quotient D 𝕧) (σ : Gen D i → Gen D i)
    (hf : ∀ g, f g ∈ RightStringComparison.degreeSpace (D := D) (generatorDegree D i (σ g)))
    (l : List (Gen D i)) (hl : l.length ≠ 0) :
    quotientForm D 1 (generatorWord D i f l) = 0 := by
  apply quotientForm_degree_ne D (ν := 0) (μ := wordDegree D i σ l) _
    ⟨1, one_mem_weightSpace, (toQuotient D 𝕧).map_one⟩ (generatorWord_degree D i f σ hf l)
  intro h
  have hh := congrArg (awayDegree i) h
  rw [awayDegree_zero, awayDegree_word] at hh
  exact hl hh.symm

lemma generator_pairing (g h : Gen D i) :
    quotientForm D (targetGen D i g) (targetGen D i h) =
      quotientForm D (sourceGen D i g) (sourceGen D i h) := by
  by_cases he : g = h
  · subst h
    rw [targetGen, quotientForm_rev]
    exact (quotientForm_skewDividedGenerator_complement D g.property.1
      g.val.2 g.property.2).symm
  · have hs : generatorDegree D i g ≠ generatorDegree D i h :=
      fun hh ↦ he (generatorDegree_injective D i hh)
    have ht : generatorDegree D i (complement D i g) ≠
        generatorDegree D i (complement D i h) :=
      fun hh ↦ he (complement_injective D i (generatorDegree_injective D i hh))
    rw [quotientForm_degree_ne D ht (targetGen_degree D i g) (targetGen_degree D i h),
      quotientForm_degree_ne D hs (sourceGen_degree D i g) (sourceGen_degree D i h)]

/-- Original quotient generator pairing against every forward transformed word. -/
theorem generator_word_pairing (g : Gen D i) (l : List (Gen D i)) :
    quotientForm D (targetGen D i g) (targetWord D i l) =
      quotientForm D (sourceGen D i g) (sourceWord D i l) := by
  by_cases hl : l.length = 1
  · cases l with
    | nil => simp at hl
    | cons h t =>
      cases t with
      | nil => simpa [sourceWord, targetWord, generatorWord] using generator_pairing D i g h
      | cons h' t => simp at hl
  · rw [generatorWord_pairing_zero D i (targetGen D i) (complement D i)
        (targetGen_degree D i) g l hl,
      generatorWord_pairing_zero D i (sourceGen D i) id (sourceGen_degree D i) g l hl]

/-- Scalar base pairing in the original form, for forward transformed words. -/
theorem one_word_pairing (l : List (Gen D i)) :
    quotientForm D 1 (targetWord D i l) = quotientForm D 1 (sourceWord D i l) := by
  cases l with
  | nil => rfl
  | cons g l =>
    rw [one_word_pairing_zero D i (targetGen D i) (complement D i)
        (targetGen_degree D i) (g :: l) (by simp),
      one_word_pairing_zero D i (sourceGen D i) id (sourceGen_degree D i)
        (g :: l) (by simp)]

end RestrictedBraidIsometry
