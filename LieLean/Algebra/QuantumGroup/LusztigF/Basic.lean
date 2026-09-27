/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import LieLean.Algebra.QuantumGroup.CartanDatum

/-!
# Lusztig's algebra `'f`: grading, twists and skew derivations

Let `(I, ·)` be a Cartan datum, `k` a field and `v ∈ k` (Lusztig takes `k = ℚ(v)`; the
downstream specialization is `k = RatFunc ℚ`, `v = RatFunc.X`). Lusztig's algebra `'f`
([Lus] 1.2.1 (check)) is the free associative `k`-algebra on generators `θᵢ`, `i ∈ I`; we take
it to be `FreeAlgebra k I` (`LusztigF k I` is an abbreviation). It is graded by `ℕ[I]`, modelled
as `I →₀ ℕ`: `'f_ν` is spanned by the monomials `θ_{i₁} ⋯ θ_{iₙ}` with `i₁ + ⋯ + iₙ = ν`.

For `i ∈ I` we define
* the twist `σᵢ = twist D v i`, the algebra automorphism `θⱼ ↦ v^{i·j} θⱼ`, so that
  `σᵢ(x) = v^{i·|x|} x` for homogeneous `x`;
* the skew derivations `rᵢ` and `ᵢr` of [Lus] 1.2.13 (check), characterized by `rᵢ(θⱼ) = δᵢⱼ`,
  `ᵢr(θⱼ) = δᵢⱼ` and
  `rᵢ(xy) = x rᵢ(y) + v^{|y|·i} rᵢ(x) y = x rᵢ(y) + rᵢ(x) σᵢ(y)`,
  `ᵢr(xy) = ᵢr(x) y + v^{|x|·i} x ᵢr(y) = ᵢr(x) y + σᵢ(x) ᵢr(y)`.
  They are constructed as the off-diagonal entries of algebra homomorphisms from `'f` to
  `2 × 2` upper triangular matrices over `'f`.

## Main definitions

* `LusztigF k I`: the free algebra `'f`; `LusztigF.θ k i`: its generators.
* `LusztigF.counit`: the augmentation `'f → k` (the constant term).
* `LusztigF.monomial`, `LusztigF.wordWeight`, `LusztigF.weightSpace ν` (= `'f_ν`).
* `LusztigF.gradingHom`: the algebra map `'f → 'f[ℕ[I]]`, `θᵢ ↦ θᵢ e^{i}`, encoding the grading.
* `LusztigF.twist D v i` (`σᵢ`), `LusztigF.rDeriv D v i` (`rᵢ`), `LusztigF.lDeriv D v i` (`ᵢr`).

## Main results

* `LusztigF.induction_left`, `LusztigF.induction_right`: induction on `'f` by left or right
  multiplication by generators.
* `LusztigF.mul_mem_weightSpace`, `LusztigF.iSup_weightSpace`, `LusztigF.iSupIndep_weightSpace`:
  `'f = ⊕_ν 'f_ν` is a grading; `LusztigF.finiteDimensional_weightSpace`.
* `LusztigF.rDeriv_mul`, `LusztigF.lDeriv_mul`, `LusztigF.rDeriv_θ`, `LusztigF.lDeriv_θ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.2.
-/

noncomputable section

open Finset

variable {k I : Type*} [Field k]

/-- Lusztig's algebra `'f` ([Lus] 1.2.1 (check)): the free associative `k`-algebra with `1` on
generators `θᵢ`, `i ∈ I`. -/
abbrev LusztigF (k I : Type*) [Field k] := FreeAlgebra k I

namespace LusztigF

variable (k) in
/-- The generator `θᵢ` of `'f`. -/
abbrev θ (i : I) : LusztigF k I := FreeAlgebra.ι k i

/-- The augmentation `'f → k` (the constant term), the counit of `'f`. -/
abbrev counit : LusztigF k I →ₐ[k] k := FreeAlgebra.algebraMapInv

@[simp] lemma counit_θ (i : I) : counit (θ k i) = 0 := by
  simp [counit, FreeAlgebra.algebraMapInv]

@[simp] lemma counit_algebraMap (c : k) : counit (algebraMap k (LusztigF k I) c) = c :=
  FreeAlgebra.algebraMap_leftInverse c

/-! ### Induction principles -/

/-- Induction on `'f` by left multiplication with generators. -/
theorem induction_left {P : LusztigF k I → Prop} (algebraMap : ∀ c, P (algebraMap k _ c))
    (smul : ∀ (c : k) x, P x → P (c • x)) (add : ∀ x y, P x → P y → P (x + y))
    (θ_mul : ∀ i x, P x → P (θ k i * x)) (x : LusztigF k I) : P x := by
  have key : ∀ a : LusztigF k I, ∀ y, P y → P (a * y) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c => intro y hy; rw [← Algebra.smul_def]; exact smul c y hy
    | grade1 i => exact θ_mul i
    | mul a b ha hb => intro y hy; rw [mul_assoc]; exact ha _ (hb _ hy)
    | add a b ha hb => intro y hy; rw [add_mul]; exact add _ _ (ha _ hy) (hb _ hy)
  simpa using key x 1 (by simpa using algebraMap 1)

/-- Induction on `'f` by right multiplication with generators. -/
theorem induction_right {P : LusztigF k I → Prop} (algebraMap : ∀ c, P (algebraMap k _ c))
    (smul : ∀ (c : k) x, P x → P (c • x)) (add : ∀ x y, P x → P y → P (x + y))
    (mul_θ : ∀ x i, P x → P (x * θ k i)) (x : LusztigF k I) : P x := by
  have key : ∀ a : LusztigF k I, ∀ y, P y → P (y * a) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c => intro y hy; rw [← Algebra.commutes, ← Algebra.smul_def]; exact smul c y hy
    | grade1 i => exact fun y hy ↦ mul_θ y i hy
    | mul a b ha hb => intro y hy; rw [← mul_assoc]; exact hb _ (ha _ hy)
    | add a b ha hb => intro y hy; rw [mul_add]; exact add _ _ (ha _ hy) (hb _ hy)
  simpa using key x 1 (by simpa using algebraMap 1)

/-! ### Monomials and the grading -/

variable (k) in
/-- The monomial `θ_{i₁} ⋯ θ_{iₙ}` of a word `[i₁, …, iₙ]`. -/
def monomial (w : List I) : LusztigF k I := (w.map (θ k)).prod

/-- The weight `i₁ + ⋯ + iₙ ∈ ℕ[I]` of a word `[i₁, …, iₙ]`. -/
def wordWeight (w : List I) : I →₀ ℕ := (w.map fun i ↦ Finsupp.single i 1).sum

@[simp] lemma monomial_nil : monomial k ([] : List I) = 1 := rfl

@[simp] lemma monomial_cons (i : I) (w : List I) :
    monomial k (i :: w) = θ k i * monomial k w := by simp [monomial]

lemma monomial_append (w w' : List I) :
    monomial k (w ++ w') = monomial k w * monomial k w' := by simp [monomial]

@[simp] lemma wordWeight_nil : wordWeight ([] : List I) = 0 := rfl

@[simp] lemma wordWeight_cons (i : I) (w : List I) :
    wordWeight (i :: w) = Finsupp.single i 1 + wordWeight w := by simp [wordWeight]

lemma wordWeight_append (w w' : List I) :
    wordWeight (w ++ w') = wordWeight w + wordWeight w' := by simp [wordWeight]

lemma wordWeight_apply (w : List I) (i : I) [DecidableEq I] :
    wordWeight w i = w.count i := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [wordWeight_cons, Finsupp.add_apply, ih, List.count_cons, Finsupp.single_apply,
      beq_iff_eq]
    split_ifs <;> omega

lemma length_eq_sum_wordWeight (w : List I) : w.length = (wordWeight w).sum fun _ n ↦ n := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordWeight_cons, Finsupp.sum_add_index' (by simp) (by simp), ← ih]
    simp [add_comm]

variable (k) in
/-- The weight space `'f_ν`, spanned by the monomials of weight `ν` ([Lus] 1.2.1 (check)). -/
def weightSpace (ν : I →₀ ℕ) : Submodule k (LusztigF k I) :=
  Submodule.span k (monomial k '' {w | wordWeight w = ν})

lemma monomial_mem_weightSpace (w : List I) : monomial k w ∈ weightSpace k (wordWeight w) :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

lemma one_mem_weightSpace : (1 : LusztigF k I) ∈ weightSpace k 0 :=
  monomial_mem_weightSpace (k := k) ([] : List I)

lemma algebraMap_mem_weightSpace (c : k) : algebraMap k (LusztigF k I) c ∈ weightSpace k 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ one_mem_weightSpace

lemma θ_mem_weightSpace (i : I) : θ k i ∈ weightSpace k (Finsupp.single i 1) := by
  simpa [monomial] using monomial_mem_weightSpace (k := k) [i]

lemma mul_mem_weightSpace {ν μ : I →₀ ℕ} {x y : LusztigF k I} (hx : x ∈ weightSpace k ν)
    (hy : y ∈ weightSpace k μ) : x * y ∈ weightSpace k (ν + μ) := by
  have : weightSpace k ν * weightSpace k μ ≤ weightSpace k (ν + μ) := by
    rw [weightSpace, weightSpace, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, _, ⟨w', hw', rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq] at hw hw'
    dsimp only
    rw [← monomial_append, ← hw, ← hw', ← wordWeight_append]
    exact monomial_mem_weightSpace _
  exact this (Submodule.mul_mem_mul hx hy)

lemma span_monomial : Submodule.span k (Set.range (monomial k (I := I))) = ⊤ := by
  suffices h : ∀ x, x ∈ Submodule.span k (Set.range (monomial k (I := I))) from
    eq_top_iff.2 fun x _ ↦ h x
  intro x
  induction x using induction_left with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | smul c x hx => exact Submodule.smul_mem _ _ hx
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | θ_mul i x hx =>
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact Submodule.subset_span ⟨i :: w, monomial_cons i w⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

theorem iSup_weightSpace : ⨆ ν, weightSpace k (I := I) ν = ⊤ := by
  rw [eq_top_iff, ← span_monomial, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace w)

variable (k I) in
/-- The algebra homomorphism `'f → 'f[ℕ[I]]`, `θᵢ ↦ θᵢ e^{i}`, which encodes the grading:
`gradingHom x = x e^ν` for `x ∈ 'f_ν` (`gradingHom_of_mem`). -/
def gradingHom : LusztigF k I →ₐ[k] AddMonoidAlgebra (LusztigF k I) (I →₀ ℕ) :=
  FreeAlgebra.lift k fun i ↦ AddMonoidAlgebra.single (Finsupp.single i 1) (θ k i)

lemma gradingHom_monomial (w : List I) :
    gradingHom k I (monomial k w) = AddMonoidAlgebra.single (wordWeight w) (monomial k w) := by
  induction w with
  | nil => simp [AddMonoidAlgebra.one_def]
  | cons i w ih =>
    rw [monomial_cons, map_mul, ih]
    simp [gradingHom, AddMonoidAlgebra.single_mul_single]

lemma gradingHom_of_mem {ν : I →₀ ℕ} {x : LusztigF k I} (hx : x ∈ weightSpace k ν) :
    gradingHom k I x = AddMonoidAlgebra.single ν x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [gradingHom_monomial, hw]
  | zero => simp [AddMonoidAlgebra.single_zero]
  | add y z _ _ hy hz => rw [map_add, hy, hz, AddMonoidAlgebra.single_add]
  | smul c y _ hy =>
    rw [map_smul, hy, AddMonoidAlgebra.smul_single]

theorem iSupIndep_weightSpace : iSupIndep (weightSpace k (I := I)) := by
  classical
  intro ν
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 : (gradingHom k I x).coeff ν = x := by
    rw [gradingHom_of_mem hx]; simp [AddMonoidAlgebra.coeff_single]
  have h2 : ∀ y ∈ ⨆ μ, ⨆ (_ : μ ≠ ν), weightSpace k μ, (gradingHom k I y).coeff ν = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem μ y hy =>
      induction hy using Submodule.iSup_induction' with
      | mem hμ y hy =>
        rw [gradingHom_of_mem hy]
        simp [AddMonoidAlgebra.coeff_single, hμ]
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
  rw [← h1, h2 x hx']

/-- The words of a given weight form a finite set. -/
lemma finite_setOf_wordWeight_eq (ν : I →₀ ℕ) : {w : List I | wordWeight w = ν}.Finite := by
  classical
  have key : ∀ n, {w : List I | w.length = n ∧ ∀ i ∈ w, i ∈ ν.support}.Finite := by
    intro n
    induction n with
    | zero => exact (Set.finite_singleton []).subset fun w hw ↦ List.eq_nil_of_length_eq_zero hw.1
    | succ n ih =>
      refine ((ν.support.finite_toSet.image2 (· :: ·) ih)).subset ?_
      rintro (_ | ⟨i, w⟩) ⟨hl, hw⟩
      · simp at hl
      · exact ⟨i, hw i (by simp), w, ⟨by simpa using hl, fun j hj ↦ hw j (by simp [hj])⟩, rfl⟩
  refine (key (ν.sum fun _ n ↦ n)).subset ?_
  rintro w rfl
  refine ⟨length_eq_sum_wordWeight w, fun i hi ↦ ?_⟩
  · rw [Finsupp.mem_support_iff, wordWeight_apply]
    exact (List.count_pos_iff.2 hi).ne'

instance finiteDimensional_weightSpace (ν : I →₀ ℕ) : FiniteDimensional k (weightSpace k ν) :=
  have := (finite_setOf_wordWeight_eq (I := I) ν).image (monomial k)
  have : Finite (monomial k '' {w | wordWeight w = ν}) := this.to_subtype
  FiniteDimensional.span_of_finite k (Set.toFinite _)

/-! ### Twists and skew derivations -/

variable (D : CartanDatum I) (v : k)

/-- The twist `σᵢ : 'f → 'f`, `θⱼ ↦ v^{i·j} θⱼ`; on `'f_ν` it is multiplication by
`v^{i·ν}`. -/
def twist (i : I) : LusztigF k I →ₐ[k] LusztigF k I :=
  FreeAlgebra.lift k fun j ↦ (v ^ D.dot i j) • θ k j

@[simp] lemma twist_θ (i j : I) : twist D v i (θ k j) = v ^ D.dot i j • θ k j := by
  simp [twist]

lemma twist_comm (i j : I) (x : LusztigF k I) :
    twist D v i (twist D v j x) = twist D v j (twist D v i x) := by
  have : (twist D v i).comp (twist D v j) = (twist D v j).comp (twist D v i) := by
    ext l
    simp [smul_smul, mul_comm]
  exact congr($this x)

@[simp] lemma counit_twist (i : I) (x : LusztigF k I) : counit (twist D v i x) = counit x := by
  have : counit.comp (twist D v i) = counit := by ext l; simp
  exact congr($this x)

variable {D v} in
/-- On `'f_ν` the twist `σᵢ` is multiplication by `v^{i·ν}`. -/
theorem twist_of_mem (hv : v ≠ 0) (i : I) {ν : I →₀ ℕ} {x : LusztigF k I}
    (hx : x ∈ weightSpace k ν) :
    twist D v i x = v ^ D.weightDot (Finsupp.single i 1) ν • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w with
    | nil => simp
    | cons l w ih =>
      rw [monomial_cons, map_mul, ih, twist_θ, smul_mul_smul_comm, wordWeight_cons,
        D.weightDot_add_right, D.weightDot_single_single, zpow_add₀ hv]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul c y _ hy => rw [map_smul, hy, smul_comm]

variable [DecidableEq I]

/-- The algebra homomorphism `'f → M₂('f)`, `x ↦ [[x, rᵢ(x)], [0, σᵢ(x)]]`, used to construct the
skew derivation `rᵢ`. -/
def rMat (i : I) : LusztigF k I →ₐ[k] Matrix (Fin 2) (Fin 2) (LusztigF k I) :=
  FreeAlgebra.lift k fun j ↦ !![θ k j, if i = j then 1 else 0; 0, v ^ D.dot i j • θ k j]

/-- The algebra homomorphism `'f → M₂('f)`, `x ↦ [[σᵢ(x), ᵢr(x)], [0, x]]`, used to construct the
skew derivation `ᵢr`. -/
def lMat (i : I) : LusztigF k I →ₐ[k] Matrix (Fin 2) (Fin 2) (LusztigF k I) :=
  FreeAlgebra.lift k fun j ↦ !![v ^ D.dot i j • θ k j, if i = j then 1 else 0; 0, θ k j]

/-- The linear map extracting the `(0, 1)` entry of a `2 × 2` matrix. -/
def entry01 : Matrix (Fin 2) (Fin 2) (LusztigF k I) →ₗ[k] LusztigF k I where
  toFun M := M 0 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Lusztig's skew derivation `rᵢ : 'f → 'f` ([Lus] 1.2.13 (check)): `rᵢ(θⱼ) = δᵢⱼ` and
`rᵢ(xy) = x rᵢ(y) + v^{|y|·i} rᵢ(x) y` (`rDeriv_mul`). -/
def rDeriv (i : I) : LusztigF k I →ₗ[k] LusztigF k I :=
  entry01 ∘ₗ (rMat D v i).toLinearMap

/-- Lusztig's skew derivation `ᵢr : 'f → 'f` ([Lus] 1.2.13 (check)): `ᵢr(θⱼ) = δᵢⱼ` and
`ᵢr(xy) = ᵢr(x) y + v^{|x|·i} x ᵢr(y)` (`lDeriv_mul`). -/
def lDeriv (i : I) : LusztigF k I →ₗ[k] LusztigF k I :=
  entry01 ∘ₗ (lMat D v i).toLinearMap

lemma rMat_entries (i : I) (x : LusztigF k I) :
    rMat D v i x 0 0 = x ∧ rMat D v i x 1 0 = 0 ∧ rMat D v i x 1 1 = twist D v i x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Matrix.algebraMap_matrix_apply]
  | grade1 j => simp [rMat]
  | mul a b ha hb =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1,
      hb.2.2]
    simp
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

lemma lMat_entries (i : I) (x : LusztigF k I) :
    lMat D v i x 0 0 = twist D v i x ∧ lMat D v i x 1 0 = 0 ∧ lMat D v i x 1 1 = x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Matrix.algebraMap_matrix_apply]
  | grade1 j => simp [lMat]
  | mul a b ha hb =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1,
      hb.2.2]
    simp
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

lemma rDeriv_apply (i : I) (x : LusztigF k I) : rDeriv D v i x = rMat D v i x 0 1 := rfl

lemma lDeriv_apply (i : I) (x : LusztigF k I) : lDeriv D v i x = lMat D v i x 0 1 := rfl

/-- `rᵢ(xy) = x rᵢ(y) + rᵢ(x) σᵢ(y)`. -/
theorem rDeriv_mul (i : I) (x y : LusztigF k I) :
    rDeriv D v i (x * y) = x * rDeriv D v i y + rDeriv D v i x * twist D v i y := by
  simp only [rDeriv_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (rMat_entries D v i x).1,
    (rMat_entries D v i y).2.2]

/-- `ᵢr(xy) = ᵢr(x) y + σᵢ(x) ᵢr(y)`. -/
theorem lDeriv_mul (i : I) (x y : LusztigF k I) :
    lDeriv D v i (x * y) = lDeriv D v i x * y + twist D v i x * lDeriv D v i y := by
  simp only [lDeriv_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (lMat_entries D v i x).1,
    (lMat_entries D v i y).2.2]
  rw [add_comm]

@[simp] lemma rDeriv_θ (i j : I) : rDeriv D v i (θ k j) = if i = j then 1 else 0 := by
  simp [rDeriv_apply, rMat]

@[simp] lemma lDeriv_θ (i j : I) : lDeriv D v i (θ k j) = if i = j then 1 else 0 := by
  simp [lDeriv_apply, lMat]

@[simp] lemma rDeriv_algebraMap (i : I) (c : k) : rDeriv D v i (algebraMap k _ c) = 0 := by
  simp [rDeriv_apply, Matrix.algebraMap_matrix_apply]

@[simp] lemma lDeriv_algebraMap (i : I) (c : k) : lDeriv D v i (algebraMap k _ c) = 0 := by
  simp [lDeriv_apply, Matrix.algebraMap_matrix_apply]

@[simp] lemma rDeriv_one (i : I) : rDeriv D v i 1 = 0 := by
  simpa using rDeriv_algebraMap D v i (1 : k)

@[simp] lemma lDeriv_one (i : I) : lDeriv D v i 1 = 0 := by
  simpa using lDeriv_algebraMap D v i (1 : k)

lemma rDeriv_θ_mul (i j : I) (x : LusztigF k I) :
    rDeriv D v i (θ k j * x) = θ k j * rDeriv D v i x + if i = j then twist D v i x else 0 := by
  rw [rDeriv_mul, rDeriv_θ]; split_ifs <;> simp

lemma rDeriv_mul_θ (i j : I) (x : LusztigF k I) :
    rDeriv D v i (x * θ k j) =
      (if i = j then x else 0) + v ^ D.dot i j • (rDeriv D v i x * θ k j) := by
  rw [rDeriv_mul, rDeriv_θ, twist_θ, mul_smul_comm]; split_ifs <;> simp

lemma lDeriv_θ_mul (i j : I) (x : LusztigF k I) :
    lDeriv D v i (θ k j * x) =
      (if i = j then x else 0) + v ^ D.dot i j • (θ k j * lDeriv D v i x) := by
  rw [lDeriv_mul, lDeriv_θ, twist_θ, smul_mul_assoc]; split_ifs <;> simp

/-- `rᵢ ∘ σⱼ = v^{i·j} σⱼ ∘ rᵢ`. -/
lemma rDeriv_twist (i j : I) (x : LusztigF k I) :
    rDeriv D v i (twist D v j x) = v ^ D.dot i j • twist D v j (rDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    simp only [twist_θ, map_smul, rDeriv_θ]
    split_ifs with h <;> simp [h, D.dot_comm]
  | mul a b ha hb =>
    rw [map_mul, rDeriv_mul, rDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist_comm D v i j]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

/-- `ᵢr ∘ σⱼ = v^{i·j} σⱼ ∘ ᵢr`. -/
lemma lDeriv_twist (i j : I) (x : LusztigF k I) :
    lDeriv D v i (twist D v j x) = v ^ D.dot i j • twist D v j (lDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    simp only [twist_θ, map_smul, lDeriv_θ]
    split_ifs with h <;> simp [h, D.dot_comm]
  | mul a b ha hb =>
    rw [map_mul, lDeriv_mul, lDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist_comm D v i j]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

lemma counit_rDeriv_θ_mul (i j : I) (x : LusztigF k I) :
    counit (rDeriv D v i (θ k j * x)) = if i = j then counit x else 0 := by
  rw [rDeriv_θ_mul]; split_ifs <;> simp

end LusztigF
