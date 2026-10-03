/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterRing
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroup
import LieLean.RepresentationTheory.Crystal.Character

/-!
# Crystals over the integral weights of a realization

Let `(𝔥, Π, Π^∨)` be a realization of a generalized Cartan matrix `A` over a field `K` of
characteristic zero. The integral weights `{λ ∈ 𝔥* | ⟨λ, αᵢ^∨⟩ ∈ ℤ for all i}` form a weight
lattice with simple roots `αᵢ` and coroots `λ ↦ ⟨λ, αᵢ^∨⟩`; this is the Cartan datum over which
the crystals of integrable `𝔤(A)`-modules live. For finite crystals over it, we define the
character in the algebra `ℰ` of formal characters (`Matrix.Realization.CharacterRing`).

## Main definitions

* `Matrix.Realization.integralWeights`: the lattice of integral weights, as a subgroup of `𝔥*`.
* `Matrix.Realization.cartanDatum`: the corresponding Cartan datum.
* `Crystal.formalCharacter`: the character `∑_b e^{wt b} ∈ ℰ` of a finite crystal.
* `Crystal.formalCharacterOfCones`: the character `∑_μ #{b | wt b = μ} e^μ ∈ ℰ` of a crystal whose
  weights lie in a finite union of cones `Λ - Q₊`.

## Main results

* `Matrix.Realization.cartanMatrix_cartanDatum`: the Cartan matrix of the datum is `A`.
* `Matrix.Realization.coe_reflection_cartanDatum`: the simple reflections of the datum are the
  fundamental reflections of `𝔥*`.
* `Crystal.formalCharacter_tensor`: `ch (B₁ ⊗ B₂) = ch B₁ · ch B₂` in `ℰ`.
* `Crystal.coeffAt_formalCharacter`: the coefficient of `e^μ` is the number of elements of
  weight `μ`.
* `Crystal.IsSeminormal.coeffAt_formalCharacterOfCones_reflection`: the character of a
  seminormal crystal is invariant under the fundamental reflections.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §10.1.
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §2.1,
  Ch. 4.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
-/

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The lattice of integral weights `{λ ∈ 𝔥* | ⟨λ, αᵢ^∨⟩ ∈ ℤ for all i}`
([Kac] §10.1). -/
def integralWeights : AddSubgroup (Dual K H) where
  carrier := {μ | ∀ i, ∃ n : ℤ, μ (P.coroot i) = n}
  add_mem' {μ ν} hμ hν i := by
    obtain ⟨m, hm⟩ := hμ i
    obtain ⟨n, hn⟩ := hν i
    exact ⟨m + n, by simp [hm, hn]⟩
  zero_mem' _ := ⟨0, by simp⟩
  neg_mem' {μ} hμ i := by
    obtain ⟨m, hm⟩ := hμ i
    exact ⟨-m, by simp [hm]⟩

lemma mem_integralWeights {μ : Dual K H} :
    μ ∈ P.integralWeights ↔ ∀ i, ∃ n : ℤ, μ (P.coroot i) = n := Iff.rfl

lemma root_mem_integralWeights (j : ι) : P.root j ∈ P.integralWeights :=
  fun i ↦ ⟨A i j, P.root_coroot i j⟩

variable [CharZero K]

/-- The pairing `λ ↦ ⟨λ, αᵢ^∨⟩ ∈ ℤ` on integral weights. -/
noncomputable def corootInt (i : ι) : Dual ℤ P.integralWeights where
  toFun μ := Classical.choose (μ.2 i)
  map_add' μ ν := by
    apply Int.cast_injective (α := K)
    rw [Int.cast_add, ← Classical.choose_spec (μ.2 i), ← Classical.choose_spec (ν.2 i),
      ← Classical.choose_spec ((μ + ν).2 i)]
    simp
  map_smul' m μ := by
    apply Int.cast_injective (α := K)
    rw [RingHom.id_apply, smul_eq_mul, Int.cast_mul, ← Classical.choose_spec (μ.2 i),
      ← Classical.choose_spec ((m • μ).2 i)]
    simp

@[simp] lemma corootInt_spec (i : ι) (μ : P.integralWeights) :
    ((P.corootInt i μ : ℤ) : K) = (μ : Dual K H) (P.coroot i) :=
  (Classical.choose_spec (μ.2 i)).symm

/-- The Cartan datum of a realization of a generalized Cartan matrix: the weight lattice is the
lattice of integral weights, with simple roots `αᵢ` and coroots `λ ↦ ⟨λ, αᵢ^∨⟩`. -/
noncomputable def cartanDatum (hA : A.IsGeneralizedCartan) :
    CartanDatum ι P.integralWeights where
  root j := ⟨P.root j, P.root_mem_integralWeights j⟩
  coroot := P.corootInt
  coroot_root_self i := Int.cast_injective (α := K) <| by
    rw [corootInt_spec, P.root_coroot, hA.diag]

variable (hA : A.IsGeneralizedCartan)

@[simp] lemma coe_root_cartanDatum (j : ι) :
    ((P.cartanDatum hA).root j : Dual K H) = P.root j := rfl

@[simp] lemma coroot_cartanDatum_cast (i : ι) (μ : P.integralWeights) :
    (((P.cartanDatum hA).coroot i μ : ℤ) : K) = (μ : Dual K H) (P.coroot i) :=
  P.corootInt_spec i μ

/-- The Cartan matrix of the Cartan datum of a realization of `A` is `A`. -/
theorem cartanMatrix_cartanDatum : (P.cartanDatum hA).cartanMatrix = A := by
  ext i j
  apply Int.cast_injective (α := K)
  rw [CartanDatum.cartanMatrix_apply, coroot_cartanDatum_cast, coe_root_cartanDatum,
    P.root_coroot]

/-- The simple reflections of the Cartan datum are the fundamental reflections `rᵢ` of `𝔥*`. -/
theorem coe_reflection_cartanDatum (i : ι) (μ : P.integralWeights) :
    ((P.cartanDatum hA).reflection i μ : Dual K H) = P.reflection hA i μ := by
  rw [CartanDatum.reflection_apply, P.reflection_apply, AddSubgroup.coe_sub,
    AddSubgroup.coe_zsmul, coe_root_cartanDatum, ← Int.cast_smul_eq_zsmul K,
    coroot_cartanDatum_cast]

end Matrix.Realization

namespace Crystal

open Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Matrix.Realization A K H} {hA : A.IsGeneralizedCartan}
  {B B₁ B₂ : Type*}

/-- The character `ch B = ∑_{b ∈ B} e^{wt b}` of a finite crystal over the integral weights of a
realization, as an element of the algebra `ℰ` of formal characters. -/
noncomputable def formalCharacter [Fintype B] (C : Crystal (P.cartanDatum hA) B) :
    P.CharacterRing ℤ :=
  ∑ b, CharacterRing.exp P ℤ (C.wt b : Dual K H)

/-- The coefficient of `e^μ` in `ch B` is the number of elements of weight `μ`. -/
theorem coeffAt_formalCharacter [Fintype B] (C : Crystal (P.cartanDatum hA) B) (μ : Dual K H) :
    (formalCharacter C).coeffAt μ = Nat.card {b // (C.wt b : Dual K H) = μ} := by
  classical
  have h : ∀ b, (CharacterRing.exp P ℤ (C.wt b : Dual K H)).coeffAt μ =
      if (C.wt b : Dual K H) = μ then 1 else 0 := fun b ↦ by
    rw [CharacterRing.coeff_exp]; simp only [eq_comm]
  rw [formalCharacter, CharacterRing.coeffAt, HahnSeries.coeff_sum]
  refine (Finset.sum_congr rfl fun b _ ↦ h b).trans ?_
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The character in `ℰ` of a tensor product of finite crystals is the product of the
characters. -/
theorem formalCharacter_tensor [Fintype B₁] [Fintype B₂] (C₁ : Crystal (P.cartanDatum hA) B₁)
    (C₂ : Crystal (P.cartanDatum hA) B₂) :
    formalCharacter (C₁.tensor C₂) = formalCharacter C₁ * formalCharacter C₂ := by
  simp only [formalCharacter, Finset.sum_mul_sum, ← CharacterRing.exp_add, tensor_wt,
    AddSubgroup.coe_add]
  exact Fintype.sum_prod_type _

/-- The character `ch B = ∑_μ #{b | wt b = μ} e^μ ∈ ℰ` of a crystal (possibly infinite) whose
weights lie in a finite union of cones `Λ - Q₊`. The multiplicity of `μ` is
`Nat.card {b | wt b = μ}`, which is only meaningful when this set is finite (`Nat.card` is `0` on
infinite types). For finite crystals it agrees with `Crystal.formalCharacter`
(`Crystal.formalCharacterOfCones_eq`). -/
noncomputable def formalCharacterOfCones (C : Crystal (P.cartanDatum hA) B)
    (hC : ∃ t : Finset (Dual K H), ∀ b, ∃ Λ ∈ t, ∃ k : ι → ℤ, 0 ≤ k ∧
      (C.wt b : Dual K H) = Λ - P.rootOf k) : P.CharacterRing ℤ :=
  CharacterRing.ofFun P (fun μ ↦ Nat.card {b // (C.wt b : Dual K H) = μ}) <| by
    obtain ⟨t, ht⟩ := hC
    refine ⟨t, fun μ hμ ↦ ?_⟩
    obtain ⟨⟨b, rfl⟩⟩ : Nonempty {b // (C.wt b : Dual K H) = μ} := by
      by_contra h
      have := not_nonempty_iff.mp h
      exact hμ (by simp [Nat.card_of_isEmpty])
    exact ht b

@[simp] lemma coeffAt_formalCharacterOfCones (C : Crystal (P.cartanDatum hA) B) (hC)
    (μ : Dual K H) :
    (formalCharacterOfCones C hC).coeffAt μ = Nat.card {b // (C.wt b : Dual K H) = μ} := rfl

lemma formalCharacterOfCones_eq [Fintype B] (C : Crystal (P.cartanDatum hA) B) (hC) :
    formalCharacterOfCones C hC = formalCharacter C :=
  CharacterRing.ext fun μ ↦ by rw [coeffAt_formalCharacterOfCones, coeffAt_formalCharacter]

private def fiberEquiv (C : Crystal (P.cartanDatum hA) B) (ν : P.integralWeights) :
    {b // (C.wt b : Dual K H) = ν} ≃ {b // C.wt b = ν} :=
  _root_.Equiv.subtypeEquivRight fun _ ↦ Subtype.coe_inj

/-- The character in `ℰ` of a seminormal crystal is invariant under the fundamental reflections:
the coefficients of `e^{rᵢ μ}` and `e^μ` agree ([Kas] §11, via `Sᵢ`). -/
theorem IsSeminormal.coeffAt_formalCharacterOfCones_reflection {C : Crystal (P.cartanDatum hA) B}
    (hs : C.IsSeminormal) (hC) (i : ι) (μ : Dual K H) :
    (formalCharacterOfCones C hC).coeffAt (P.reflection hA i μ) =
      (formalCharacterOfCones C hC).coeffAt μ := by
  simp only [coeffAt_formalCharacterOfCones]
  by_cases hμ : μ ∈ P.integralWeights
  · lift μ to P.integralWeights using hμ
    rw [← coe_reflection_cartanDatum, Nat.card_congr (fiberEquiv C _),
      Nat.card_congr (fiberEquiv C _), hs.card_wt_reflection]
  · have h₁ : IsEmpty {b // (C.wt b : Dual K H) = μ} :=
      ⟨fun ⟨b, hb⟩ ↦ hμ (hb ▸ (C.wt b).2)⟩
    have h₂ : IsEmpty {b // (C.wt b : Dual K H) = P.reflection hA i μ} := by
      refine ⟨fun ⟨b, hb⟩ ↦ hμ ?_⟩
      rw [← P.reflection_reflection hA i μ, ← hb, ← coe_reflection_cartanDatum]
      exact ((P.cartanDatum hA).reflection i (C.wt b)).2
    simp [Nat.card_of_isEmpty]

end Crystal
