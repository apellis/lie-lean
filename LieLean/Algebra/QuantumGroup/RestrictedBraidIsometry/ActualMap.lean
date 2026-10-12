/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import LieLean.Algebra.QuantumGroup.RestrictedBraidIsometry.GeneratorPairing

/-!
# Actual restricted braid map

The positive braid restriction on the original left kernel and its projected extension.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF TensorProduct
namespace RestrictedBraidIsometry
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (i : I)

lemma exists_forward (x : quotientSkewGenerators D i) :
    ∃ y : Quotient D 𝕧,
      quotientPlus R y = braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) := by
  obtain ⟨a, ha⟩ := braid_positive_of_mem_skewGenerators R i x.property
  exact ⟨toQuotient D 𝕧 a, ha⟩

/-- The actual restricted positive braid map, characterized in the original quantum group. -/
def braidRestriction : quotientSkewGenerators D i →ₐ[𝕂] Quotient D 𝕧 where
  toFun x := (exists_forward R i x).choose
  map_zero' := by
    apply quotientPlus_injective R
    rw [(exists_forward R i 0).choose_spec]
    simp only [ZeroMemClass.coe_zero, map_zero]
  map_one' := by
    apply quotientPlus_injective R
    rw [(exists_forward R i 1).choose_spec]
    simp only [OneMemClass.coe_one, map_one]
  map_add' a b := by
    apply quotientPlus_injective R
    rw [(exists_forward R i (a+b)).choose_spec]
    simp only [(exists_forward R i a).choose_spec,
      (exists_forward R i b).choose_spec, AddMemClass.coe_add, map_add]
  map_mul' a b := by
    apply quotientPlus_injective R
    rw [(exists_forward R i (a*b)).choose_spec]
    simp only [(exists_forward R i a).choose_spec,
      (exists_forward R i b).choose_spec, MulMemClass.coe_mul, map_mul]
  commutes' c := by
    apply quotientPlus_injective R
    rw [(exists_forward R i (algebraMap 𝕂 _ c)).choose_spec]
    simp only [Subalgebra.coe_algebraMap, AlgHom.commutes, AlgEquiv.commutes]

lemma braidRestriction_spec (x : quotientSkewGenerators D i) :
    quotientPlus R (braidRestriction R i x) =
      braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) :=
  (exists_forward R i x).choose_spec

/-- The original left projector, with codomain restricted to the proved kernel algebra. -/
def kernelProjection : Quotient D 𝕧 →ₗ[𝕂] quotientSkewGenerators D i :=
  (quotientSkewProjection D i).codRestrict (quotientSkewGenerators D i).toSubmodule fun x ↦ by
    rw [quotientSkewGenerators_eq]
    exact quotientSkewProjection_mem D i x

/-- Linear extension of the actual restricted braid by the original zero-string projector. -/
def projectedBraid : Module.End 𝕂 (Quotient D 𝕧) :=
  (braidRestriction R i).toLinearMap ∘ₗ kernelProjection (D := D) i

lemma projectedBraid_of_mem (x : quotientSkewGenerators D i) :
    projectedBraid R i x = braidRestriction R i x := by
  change braidRestriction R i (kernelProjection (D := D) i x) = braidRestriction R i x
  congr 1
  apply Subtype.ext
  exact quotientSkewProjection_of_ker D i ((mem_quotientSkewGenerators_iff D i x).mp x.property)

lemma projectedBraid_spec (x : Quotient D 𝕧) :
    quotientPlus R (projectedBraid R i x) =
      braidEquivOfNotRoot R ratFunc_X_not_root i
        (quotientPlus R (quotientSkewProjection D i x)) :=
  braidRestriction_spec R i (kernelProjection (D := D) i x)

omit [Finite I] in
lemma sourceGen_mem (g : Gen D i) : sourceGen D i g ∈ quotientSkewGenerators D i :=
  Algebra.subset_adjoin ⟨g.val.1, g.property.1, g.val.2, g.property.2, rfl⟩

omit [Finite I] in
lemma sourceWord_mem (l : List (Gen D i)) : sourceWord D i l ∈ quotientSkewGenerators D i := by
  induction l with
  | nil => exact one_mem _
  | cons g l ih => exact mul_mem (sourceGen_mem i g) ih

lemma projectedBraid_generator (g : Gen D i) :
    projectedBraid R i (sourceGen D i g) = targetGen D i g := by
  apply quotientPlus_injective R
  rw [projectedBraid_spec, quotientSkewProjection_of_ker D i
    ((mem_quotientSkewGenerators_iff D i _).mp (sourceGen_mem i g))]
  simpa only [targetGen, sourceGen, complement, quotientRev_toQuotient] using
    braid_skewDividedGenerator R g.property.1 g.val.2 g.property.2

lemma projectedBraid_word (l : List (Gen D i)) :
    projectedBraid R i (sourceWord D i l) = targetWord D i l := by
  have h (l : List (Gen D i)) :
      braidRestriction R i ⟨sourceWord D i l, sourceWord_mem i l⟩ = targetWord D i l := by
    induction l with
    | nil => exact (braidRestriction R i).map_one
    | cons g l ih =>
      change braidRestriction R i
        (⟨sourceGen D i g, sourceGen_mem i g⟩ * ⟨sourceWord D i l, sourceWord_mem i l⟩) = _
      rw [map_mul, ih]
      rw [← projectedBraid_of_mem]
      exact congrArg (fun z ↦ z * targetWord D i l) (projectedBraid_generator R i g)
  rw [projectedBraid_of_mem R i ⟨_, sourceWord_mem i l⟩]
  exact h l

omit [Finite I] in
/-- Original bounded-generator words span the actual kernel algebra. -/
theorem mem_sourceWord_span {x : Quotient D 𝕧} (hx : x ∈ quotientSkewGenerators D i) :
    x ∈ Submodule.span 𝕂 (Set.range (sourceWord D i)) := by
  have hmul : ∀ a ∈ Submodule.span 𝕂 (Set.range (sourceWord D i)),
      ∀ b ∈ Submodule.span 𝕂 (Set.range (sourceWord D i)),
      a * b ∈ Submodule.span 𝕂 (Set.range (sourceWord D i)) := by
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨m, rfl⟩ := hb
        have he : sourceWord D i (l ++ m) = sourceWord D i l * sourceWord D i m := by
          induction l with
          | nil => simp [sourceWord, generatorWord]
          | cons g l ih =>
            simpa [sourceWord, generatorWord, mul_assoc] using
              congrArg (fun z ↦ sourceGen D i g * z) ih
        rw [← he]
        exact Submodule.subset_span ⟨l ++ m, rfl⟩
      | zero => simp
      | add b c _ _ hb hc => simpa only [mul_add] using add_mem hb hc
      | smul c b _ hb => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hb
    | zero => simp
    | add a c _ _ ha hc => simpa only [add_mul] using add_mem ha hc
    | smul c a _ ha => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ha
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hij, n, hn, rfl⟩ := hx
    let g : Gen D i := ⟨(j,n), hij, hn⟩
    have he : sourceWord D i [g] = toQuotient D 𝕧 (skewDividedGenerator D 𝕧 i j n) :=
      mul_one _
    rw [← he]
    exact Submodule.subset_span ⟨[g], rfl⟩
  | algebraMap c =>
    have h := Submodule.subset_span (R := 𝕂) (s := Set.range (sourceWord D i)) ⟨[], rfl⟩
    simpa only [sourceWord, generatorWord, Algebra.smul_def, mul_one] using
      Submodule.smul_mem _ c h
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact hmul a ha b hb

lemma generator_kernel_pairing (g : Gen D i) {x : Quotient D 𝕧}
    (hx : x ∈ quotientSkewGenerators D i) :
    quotientForm D (targetGen D i g) (projectedBraid R i x) =
      quotientForm D (sourceGen D i g) x := by
  have hs := mem_sourceWord_span i hx
  clear hx
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [projectedBraid_word]
    exact generator_word_pairing D i g l
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul c a _ ha => simp only [map_smul, ha]

lemma one_kernel_pairing {x : Quotient D 𝕧} (hx : x ∈ quotientSkewGenerators D i) :
    quotientForm D 1 (projectedBraid R i x) = quotientForm D 1 x := by
  have hs := mem_sourceWord_span i hx
  clear hx
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [projectedBraid_word]
    exact one_word_pairing D i l
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul c a _ ha => simp only [map_smul, ha]

end RestrictedBraidIsometry
