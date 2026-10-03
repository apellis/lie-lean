/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.Generalized
import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# The algebra `ℰ` of formal characters

Let `P` be a realization of a matrix `A` over a field `K` of characteristic zero, with Cartan
space `𝔥 = H`, and let `Q₊ = {∑ kᵢ αᵢ | kᵢ ∈ ℤ≥0} ⊂ 𝔥*`. Kac ([Kac] §9.7) defines the
algebra `ℰ` of formal series `∑_{λ ∈ 𝔥*} c_λ e^λ` whose support lies in a finite union of cones
`D(Λ) = Λ - Q₊`, with the product `e^λ e^μ = e^{λ + μ}`, i.e. the convolution product
`(c d)_μ = ∑_ν c_ν d_{μ - ν}`.

## Design

We realize `ℰ` (with coefficients in any commutative ring `R`) as the ring of Hahn series
`HahnSeries P.WeightOrd R`, where `P.WeightOrd` is `𝔥*` with the partial order
`μ ≤ ν ↔ μ - ν ∈ Q₊`, the *reverse* of the usual dominance order (the reversal is needed since
Hahn series have well-founded support, whereas the cones `Λ - Q₊` are bounded *above* for the
dominance order). This order makes `P.WeightOrd` an ordered abelian group (antisymmetry uses
`CharZero K`: the root lattice embeds in `𝔥*`). The main point is
`Matrix.Realization.WeightOrd.isPWO_iff`: a subset of `𝔥*` is partially well-ordered for this
order if and only if it lies in a finite union of cones `Λ - Q₊`. Hence the Hahn series are
exactly Kac's formal series, the Hahn series product is the convolution product (the finiteness
of the sums is part of Mathlib's construction), and we get the commutative ring structure of `ℰ`
for free.

## Main definitions

* `Matrix.Realization.WeightOrd`: the type `𝔥*` with the order `μ ≤ ν ↔ μ - ν ∈ Q₊`.
* `Matrix.Realization.CharacterRing`: the algebra `ℰ`, as a ring of Hahn series.
* `Matrix.Realization.CharacterRing.exp`: the element `e^λ` of `ℰ`.
* `Matrix.Realization.CharacterRing.ofFun`: the element of `ℰ` defined by a function
  `𝔥* → R` supported in a finite union of cones.

## Main results

* `Matrix.Realization.WeightOrd.isPWO_iff`: the partially well-ordered subsets of
  `P.WeightOrd` are exactly the subsets of finite unions of cones `Λ - Q₊`.
* `Matrix.Realization.CharacterRing.exp_add`: `e^{λ + μ} = e^λ e^μ`.
* `Matrix.Realization.CharacterRing.coeff_exp_mul`: `(e^λ c)_μ = c_{μ - λ}`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.7.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The dual `𝔥*` of the Cartan space of a realization, with the partial order
`μ ≤ ν ↔ μ - ν ∈ Q₊` (the reverse of the dominance order). The cone `D(Λ) = Λ - Q₊` of [Kac]
§9.1 is the set of elements `≥ Λ` for this order. -/
def WeightOrd (_ : Realization A K H) : Type _ := Dual K H

namespace WeightOrd

instance : AddCommGroup P.WeightOrd := inferInstanceAs (AddCommGroup (Dual K H))

/-- The identity map `𝔥* → P.WeightOrd`. -/
def toWeightOrd : Dual K H ≃+ P.WeightOrd := AddEquiv.refl _

/-- The identity map `P.WeightOrd → 𝔥*`. -/
def ofWeightOrd : P.WeightOrd ≃+ Dual K H := AddEquiv.refl _

@[simp] lemma ofWeightOrd_toWeightOrd (μ : Dual K H) :
    ofWeightOrd P (toWeightOrd P μ) = μ := rfl

@[simp] lemma toWeightOrd_ofWeightOrd (μ : P.WeightOrd) :
    toWeightOrd P (ofWeightOrd P μ) = μ := rfl

@[simp] lemma toWeightOrd_symm : (toWeightOrd P).symm = ofWeightOrd P := rfl

@[simp] lemma ofWeightOrd_symm : (ofWeightOrd P).symm = toWeightOrd P := rfl

variable [CharZero K]

instance : PartialOrder P.WeightOrd where
  le μ ν := ∃ k : ι → ℤ, 0 ≤ k ∧ ofWeightOrd P μ - ofWeightOrd P ν = P.rootOf k
  le_refl μ := ⟨0, le_rfl, by simp⟩
  le_trans μ ν ρ := by
    rintro ⟨k, hk, hμν⟩ ⟨l, hl, hνρ⟩
    refine ⟨k + l, add_nonneg hk hl, ?_⟩
    rw [map_add, ← hμν, ← hνρ]
    abel
  le_antisymm μ ν := by
    rintro ⟨k, hk, hμν⟩ ⟨l, hl, hνμ⟩
    have h0 : P.rootOf (k + l) = P.rootOf 0 := by
      rw [map_add, ← hμν, ← hνμ, map_zero]
      abel
    have hkl := P.rootOf_injective h0
    have hk0 : k = 0 := le_antisymm (fun i ↦ by
      have := congr_fun hkl i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      have := hl i
      simp only [Pi.zero_apply] at this ⊢
      omega) hk
    rw [hk0, map_zero, sub_eq_zero] at hμν
    exact hμν

lemma le_iff {μ ν : P.WeightOrd} :
    μ ≤ ν ↔ ∃ k : ι → ℤ, 0 ≤ k ∧ ofWeightOrd P μ - ofWeightOrd P ν = P.rootOf k := Iff.rfl

lemma toWeightOrd_le_iff {μ ν : Dual K H} :
    toWeightOrd P μ ≤ toWeightOrd P ν ↔ ∃ k : ι → ℤ, 0 ≤ k ∧ μ - ν = P.rootOf k := Iff.rfl

instance : IsOrderedAddMonoid P.WeightOrd where
  add_le_add_left μ ν := by
    rintro ⟨k, hk, h⟩ ρ
    refine ⟨k, hk, ?_⟩
    rw [map_add, map_add, ← h]
    abel

/-- `μ ≥ Λ` in `P.WeightOrd` iff `μ` lies in the cone `D(Λ) = Λ - Q₊`. -/
lemma toWeightOrd_le_toWeightOrd_iff_exists_eq_sub {Λ μ : Dual K H} :
    toWeightOrd P Λ ≤ toWeightOrd P μ ↔ ∃ k : ι → ℤ, 0 ≤ k ∧ μ = Λ - P.rootOf k := by
  rw [toWeightOrd_le_iff]
  refine exists_congr fun k ↦ and_congr_right fun _ ↦ ?_
  constructor <;> intro h
  · rw [← h]; abel
  · rw [h]; abel

/-- The cone `D(Λ) = Λ - Q₊`, as a subset of `P.WeightOrd`, is partially well-ordered (Dickson's
lemma). -/
theorem isPWO_Ici (Λ : P.WeightOrd) : (Set.Ici Λ).IsPWO := by
  let g : (ι → ℕ) → P.WeightOrd := fun k ↦ Λ - toWeightOrd P (P.rootOf fun i ↦ (k i : ℤ))
  have hg : Monotone g := by
    intro k l hkl
    refine ⟨fun i ↦ (l i : ℤ) - k i, fun i ↦ ?_, ?_⟩
    · have := hkl i
      simp only [Pi.zero_apply, sub_nonneg]
      exact_mod_cast this
    · simp only [g, ofWeightOrd_toWeightOrd, sub_sub_sub_cancel_left, ← map_sub]
      congr 1
  have hpwo : (Set.univ : Set (ι → ℕ)).IsPWO := by
    rw [← Set.pi_univ]
    exact Set.IsPWO.pi fun _ ↦ Set.isPWO_of_wellQuasiOrderedLE _
  refine (hpwo.image_of_monotone hg).mono ?_
  rintro μ ⟨k, hk, hΛμ⟩
  refine ⟨fun i ↦ (k i).toNat, Set.mem_univ _, ?_⟩
  have hk' : (fun i ↦ ((k i).toNat : ℤ)) = k := funext fun i ↦ Int.toNat_of_nonneg (hk i)
  simp only [g, hk']
  apply (ofWeightOrd P).injective
  rw [map_sub, ofWeightOrd_toWeightOrd, ← hΛμ, sub_sub_cancel]

/-- **Characterization of the supports of elements of `ℰ`**: a subset of `P.WeightOrd` is
partially well-ordered if and only if it lies in a finite union of cones `D(Λ) = Λ - Q₊`.
(The argument is standard: a partially well-ordered set has finitely many minimal elements, and
conversely the cones are partially well-ordered by Dickson's lemma.) -/
theorem isPWO_iff {s : Set P.WeightOrd} :
    s.IsPWO ↔ ∃ t : Finset (Dual K H), ∀ μ ∈ s, ∃ Λ ∈ t,
      ∃ k : ι → ℤ, 0 ≤ k ∧ ofWeightOrd P μ = Λ - P.rootOf k := by
  classical
  constructor
  · intro hs
    have hfin : {b | Minimal (· ∈ s) b}.Finite :=
      (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
        (hs.mono fun _ hb ↦ hb.1)
    refine ⟨hfin.toFinset.image (ofWeightOrd P), fun μ hμ ↦ ?_⟩
    obtain ⟨b, hbμ, hb⟩ := hs.exists_le_minimal hμ
    refine ⟨ofWeightOrd P b, Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hb), ?_⟩
    rw [← toWeightOrd_le_toWeightOrd_iff_exists_eq_sub]
    exact hbμ
  · rintro ⟨t, ht⟩
    refine ((Finset.isPWO_bUnion t (f := fun Λ ↦ Set.Ici (toWeightOrd P Λ))).mpr
      fun Λ _ ↦ isPWO_Ici P _).mono fun μ hμ ↦ ?_
    obtain ⟨Λ, hΛ, hμΛ⟩ := ht μ hμ
    exact Set.mem_biUnion hΛ ((toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr hμΛ)

end WeightOrd

open WeightOrd

variable [CharZero K]

/-- The algebra `ℰ` of formal characters ([Kac] §9.7) with coefficients in `R`: formal
series `∑_{λ ∈ 𝔥*} c_λ e^λ` whose support lies in a finite union of cones `Λ - Q₊`, with the
convolution product. It is realized as the ring of Hahn series on `P.WeightOrd`; see
`Matrix.Realization.WeightOrd.isPWO_iff`. -/
abbrev CharacterRing (R : Type*) [Zero R] : Type _ := HahnSeries P.WeightOrd R

namespace CharacterRing

variable {P} {R : Type*}

/-- The coefficient `c_μ` of `c ∈ ℰ`. -/
abbrev coeffAt [Zero R] (c : P.CharacterRing R) (μ : Dual K H) : R :=
  HahnSeries.coeff c (toWeightOrd P μ)

lemma exists_finset [Zero R] (c : P.CharacterRing R) : ∃ t : Finset (Dual K H), ∀ μ,
    c.coeffAt μ ≠ 0 → ∃ Λ ∈ t, ∃ k : ι → ℤ, 0 ≤ k ∧ μ = Λ - P.rootOf k := by
  obtain ⟨t, ht⟩ := (isPWO_iff P).mp c.isPWO_support
  exact ⟨t, fun μ hμ ↦ ht (toWeightOrd P μ) hμ⟩

@[ext] lemma ext [Zero R] {c d : P.CharacterRing R} (h : ∀ μ, c.coeffAt μ = d.coeffAt μ) : c = d :=
  HahnSeries.ext (funext fun μ ↦ h (ofWeightOrd P μ))

variable (P) in
/-- The element of `ℰ` with coefficients `c : 𝔥* → R`, whose support lies in a finite union of
cones `Λ - Q₊`. -/
def ofFun [Zero R] (c : Dual K H → R) (hc : ∃ t : Finset (Dual K H), ∀ μ, c μ ≠ 0 →
    ∃ Λ ∈ t, ∃ k : ι → ℤ, 0 ≤ k ∧ μ = Λ - P.rootOf k) : P.CharacterRing R where
  coeff μ := c (ofWeightOrd P μ)
  isPWO_support' := by
    obtain ⟨t, ht⟩ := hc
    exact (isPWO_iff P).mpr ⟨t, fun μ hμ ↦ ht _ hμ⟩

@[simp] lemma coeff_ofFun [Zero R] (c : Dual K H → R) (hc) (μ : Dual K H) :
    (ofFun P c hc).coeffAt μ = c μ := rfl

variable (P R) in
/-- The element `e^λ` of `ℰ`. -/
def exp [Zero R] [One R] (μ : Dual K H) : P.CharacterRing R := HahnSeries.single (toWeightOrd P μ) 1

open Classical in
lemma coeff_exp [Zero R] [One R] (μ ν : Dual K H) :
    (exp P R μ).coeffAt ν = if ν = μ then 1 else 0 := by
  simp only [coeffAt, exp, HahnSeries.coeff_single]
  rfl

@[simp] lemma coeff_exp_self [Zero R] [One R] (μ : Dual K H) : (exp P R μ).coeffAt μ = 1 := by
  simp [coeffAt, exp]

variable [CommRing R]

@[simp] lemma exp_zero : exp P R 0 = 1 := by
  simp [exp]

/-- `e^{λ + μ} = e^λ e^μ`. -/
lemma exp_add (μ ν : Dual K H) : exp P R (μ + ν) = exp P R μ * exp P R ν := by
  simp [exp, HahnSeries.single_mul_single]

/-- `(e^λ c)_μ = c_{μ - λ}`. -/
lemma coeff_exp_mul (Λ : Dual K H) (c : P.CharacterRing R) (μ : Dual K H) :
    (exp P R Λ * c).coeffAt μ = c.coeffAt (μ - Λ) := by
  simp only [coeffAt, exp]
  rw [HahnSeries.coeff_single_mul, one_mul, map_sub]

/-- The convolution formula for the product of `ℰ`: `(c d)_μ = ∑_ν c_ν d_{μ - ν}`, the sum
having only finitely many nonzero terms. -/
lemma coeff_mul (c d : P.CharacterRing R) (μ : Dual K H) :
    (c * d).coeffAt μ = ∑ᶠ ν, c.coeffAt ν * d.coeffAt (μ - ν) := by
  classical
  set s := Finset.antidiagonal c.isPWO_support d.isPWO_support (toWeightOrd P μ)
  rw [finsum_eq_sum_of_support_subset _ (s := s.image fun x ↦ ofWeightOrd P x.1), coeffAt,
    HahnSeries.coeff_mul, Finset.sum_image]
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    obtain ⟨-, -, hx⟩ := Finset.mem_antidiagonal.mp hx
    have : μ - ofWeightOrd P x.1 = ofWeightOrd P x.2 := by
      rw [← ofWeightOrd_toWeightOrd P μ, ← hx, map_add, add_sub_cancel_left]
    simp only [coeffAt, this, toWeightOrd_ofWeightOrd]
  · intro x hx y hy hxy
    obtain ⟨-, -, hx⟩ := Finset.mem_antidiagonal.mp hx
    obtain ⟨-, -, hy⟩ := Finset.mem_antidiagonal.mp hy
    have h1 : x.1 = y.1 := hxy
    refine Prod.ext h1 ?_
    rw [← hy, h1] at hx
    exact add_left_cancel hx
  · intro ν hν
    rw [Function.mem_support] at hν
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(toWeightOrd P ν, toWeightOrd P (μ - ν)),
      Finset.mem_antidiagonal.mpr ⟨left_ne_zero_of_mul hν, right_ne_zero_of_mul hν, ?_⟩, rfl⟩)
    rw [← map_add, add_sub_cancel]

end CharacterRing

end Matrix.Realization
