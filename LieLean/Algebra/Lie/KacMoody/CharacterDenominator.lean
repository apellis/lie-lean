/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterVerma
import LieLean.Combinatorics.Enumerative.SignReversingInvolution
import Mathlib.Data.Finsupp.Interval
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# The Kac–Moody denominator and the character of a Verma module

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a realization `P` over a field `K` of characteristic
zero. The *denominator* ([Kac] §10.2 (check)) is the element
`R = ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α}` of the algebra `ℰ` of formal characters. Choosing a basis
of `𝔫₋` consisting of root vectors (`Matrix.Realization.KacMoodyAlgebra.nNegBasis`, indexed by
`NegRootIndex`: the index `(α, j)` contributes the factor `1 - e^{-α}`), the product expands as
`R = ∑_S (-1)^{|S|} e^{-wt S}`, the sum running over the finite sets `S` of indices, with
`wt S = ∑_{(α, j) ∈ S} α`. This is how we define `R`, as a summable family of Hahn series.

We prove `R · ch M(Λ) = e^Λ`, i.e. `ch M(Λ) = e^Λ ∏_{α ∈ Δ₊} (1 - e^{-α})^{-mult α}`
([Kac] (9.7.2) (check)). The proof combines the computation `dim M(Λ)_{Λ - β} = K(β)`
(`Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_weightSpace_sub`) with the sign-reversing
involution of `Finsupp.PairInvolution.sum_neg_one_pow_card_eq_ite`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.denominator`: the denominator `R ∈ ℰ`.
* `Matrix.Realization.KacMoodyAlgebra.kostantSeries`: `∑_s e^{-wt s} = ∑_β K(β) e^{-β} ∈ ℰ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.denominator_mul_kostantSeries`:
  `∏ (1 - e^{-α}) · ∏ (1 - e^{-α})⁻¹ = 1`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.character_eq_exp_mul_kostantSeries`:
  `ch M(Λ) = e^Λ ∑_β K(β) e^{-β}`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.denominator_mul_character`:
  `R · ch M(Λ) = e^Λ` ([Kac] (9.7.2) (check)).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.7, §10.2.
-/

open Module LieModule HahnSeries

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Weights of multisets and sets of indices -/

lemma negRootWt_add (s t : NegRootIndex P →₀ ℕ) :
    negRootWt P (s + t) = negRootWt P s + negRootWt P t :=
  Finsupp.sum_add_index' (h := fun (x : NegRootIndex P) (n : ℕ) ↦ n • x.root)
    (fun _ ↦ zero_nsmul _)
    (fun _ _ _ ↦ add_nsmul _ _ _)

@[simp] lemma negRootWt_zero : negRootWt P 0 = 0 := Finsupp.sum_zero_index

lemma negRootWt_single (x : NegRootIndex P) (n : ℕ) :
    negRootWt P (Finsupp.single x n) = n • x.root :=
  Finsupp.sum_single_index (h := fun (x : NegRootIndex P) (n : ℕ) ↦ n • x.root) (zero_nsmul _)

/-- The weight `negRootWt` lies in `Q₊`. -/
lemma exists_negRootWt_eq_rootOf (s : NegRootIndex P →₀ ℕ) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ negRootWt P s = P.rootOf k := by
  induction s using Finsupp.induction_linear with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | add s t hs ht =>
    obtain ⟨k, hk, hks⟩ := hs
    obtain ⟨l, hl, hlt⟩ := ht
    exact ⟨k + l, add_nonneg hk hl, by rw [negRootWt_add, hks, hlt, map_add]⟩
  | single x n =>
    obtain ⟨k, hk, hkx⟩ := x.1.2
    refine ⟨n • k, nsmul_nonneg hk.1 n, ?_⟩
    rw [negRootWt_single, map_nsmul, hkx]
    rfl

/-- The weight `∑_{x ∈ S} x.root` of a finite set of indices. -/
def finsetWt (S : Finset (NegRootIndex P)) : Dual K H := ∑ x ∈ S, x.root

/-- The multiset of indices underlying a finite set. -/
def finsetToFinsupp (S : Finset (NegRootIndex P)) : NegRootIndex P →₀ ℕ :=
  ∑ x ∈ S, Finsupp.single x 1

lemma negRootWt_finsetToFinsupp (S : Finset (NegRootIndex P)) :
    negRootWt P (finsetToFinsupp P S) = finsetWt P S :=
  map_sum (AddMonoidHom.mk' (negRootWt P) (negRootWt_add P)) _ S |>.trans
    (Finset.sum_congr rfl fun x _ ↦ by simp [negRootWt_single])

lemma finsetToFinsupp_apply (S : Finset (NegRootIndex P)) (x : NegRootIndex P) :
    finsetToFinsupp P S x = if x ∈ S then 1 else 0 := by
  classical
  simp [finsetToFinsupp, Finsupp.finsetSum_apply, Finsupp.single_apply]

lemma finsetToFinsupp_injective : Function.Injective (finsetToFinsupp P) := by
  intro S T h
  ext x
  have := DFunLike.congr_fun h x
  rw [finsetToFinsupp_apply, finsetToFinsupp_apply] at this
  split_ifs at this with h1 h2 h2 <;> simp_all

lemma exists_finsetWt_eq_rootOf (S : Finset (NegRootIndex P)) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ finsetWt P S = P.rootOf k := by
  rw [← negRootWt_finsetToFinsupp]
  exact exists_negRootWt_eq_rootOf P _

variable [CharZero K]

/-- There are finitely many multisets of indices of a given weight. -/
theorem finite_setOf_negRootWt_eq (β : Dual K H) :
    {s : NegRootIndex P →₀ ℕ | negRootWt P s = β}.Finite := by
  set S := {s : NegRootIndex P →₀ ℕ | negRootWt P s = β}
  set B := VermaModule.pbwBasisVerma P 0
  let W := VermaModule.weightSpace P 0 (0 - β)
  have hmem : ∀ s : S, B s ∈ W := fun s ↦ by
    have := VermaModule.pbwBasisVerma_mem_weightSpace P 0 s
    rwa [s.2] at this
  let f : S → W := fun s ↦ ⟨B s, hmem s⟩
  have hf : LinearIndependent K f := by
    refine LinearIndependent.of_comp W.subtype ?_
    exact B.linearIndependent.comp _ Subtype.val_injective
  have := VermaModule.finiteDimensional_weightSpace P 0 (0 - β)
  exact Set.finite_coe_iff.mp hf.finite

lemma finite_setOf_finsetWt_eq (β : Dual K H) :
    {S : Finset (NegRootIndex P) | finsetWt P S = β}.Finite := by
  refine ((finite_setOf_negRootWt_eq P β).preimage
    (finsetToFinsupp_injective P).injOn).subset fun S hS ↦ ?_
  simpa [negRootWt_finsetToFinsupp] using hS

/-- There are finitely many pairs `(S, s)` of a set and a multiset of indices of a given total
weight. -/
lemma finite_setOf_pairWeight_eq (β : Dual K H) :
    {p : Finset (NegRootIndex P) × (NegRootIndex P →₀ ℕ) |
      Finsupp.PairInvolution.pairWeight NegRootIndex.root p = β}.Finite := by
  classical
  let T := finite_setOf_negRootWt_eq P β
  refine (T.biUnion fun t _ ↦ ((t.support.powerset : Set (Finset (NegRootIndex P))).toFinite.prod
    (Set.finite_Icc 0 t))).subset fun p hp ↦ ?_
  refine Set.mem_biUnion (x := finsetToFinsupp P p.1 + p.2) ?_ ⟨?_, ?_⟩
  · change negRootWt P _ = β
    rw [negRootWt_add, negRootWt_finsetToFinsupp]
    exact hp
  · refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun x hx ↦ ?_)
    simp [finsetToFinsupp_apply, hx]
  · exact ⟨zero_le, le_add_self⟩

/-! ### The denominator and the Kostant series -/

omit [DecidableEq ι] in
lemma isPWO_iUnion_support_single {α : Type*} (f : α → Dual K H) (c : α → ℤ)
    (hf : ∀ a, ∃ k : ι → ℤ, 0 ≤ k ∧ f a = P.rootOf k) :
    (⋃ a, (HahnSeries.single (toWeightOrd P (-f a)) (c a) : P.CharacterRing ℤ).support).IsPWO := by
  refine (isPWO_Ici P (toWeightOrd P 0)).mono (Set.iUnion_subset fun a μ hμ ↦ ?_)
  obtain rfl := support_single_subset hμ
  obtain ⟨k, hk, hfk⟩ := hf a
  exact ⟨k, hk, by simp [hfk]⟩

/-- The family `(-1)^{|S|} e^{-wt S}` indexed by the finite sets `S` of indices. -/
def denominatorFamily : SummableFamily P.WeightOrd ℤ (Finset (NegRootIndex P)) where
  toFun S := HahnSeries.single (toWeightOrd P (-finsetWt P S)) ((-1) ^ S.card)
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_single P _ _ (exists_finsetWt_eq_rootOf P)
  finite_co_support' g := by
    refine (finite_setOf_finsetWt_eq P (-ofWeightOrd P g)).subset fun S hS ↦ ?_
    by_contra h
    refine hS (coeff_single_of_ne fun hg ↦ h ?_)
    simp [hg]

/-- The **denominator** `R = ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α} = ∑_S (-1)^{|S|} e^{-wt S} ∈ ℰ`
([Kac] §10.2 (check)). -/
def denominator : P.CharacterRing ℤ := (denominatorFamily P).hsum

/-- The family `e^{-wt s}` indexed by the multisets `s` of indices. -/
def kostantFamily : SummableFamily P.WeightOrd ℤ (NegRootIndex P →₀ ℕ) where
  toFun s := HahnSeries.single (toWeightOrd P (-negRootWt P s)) 1
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_single P _ _ (exists_negRootWt_eq_rootOf P)
  finite_co_support' g := by
    refine (finite_setOf_negRootWt_eq P (-ofWeightOrd P g)).subset fun s hs ↦ ?_
    by_contra h
    refine hs (coeff_single_of_ne fun hg ↦ h ?_)
    simp [hg]

/-- The **Kostant series** `∏_{α ∈ Δ₊} (1 - e^{-α})^{-mult α} = ∑_s e^{-wt s} ∈ ℰ`. -/
def kostantSeries : P.CharacterRing ℤ := (kostantFamily P).hsum

/-- The coefficient of `e^{-β}` in the Kostant series is Kostant's partition function `K(β)`. -/
theorem coeffAt_kostantSeries (β : Dual K H) :
    (kostantSeries P).coeffAt (-β) = kostantPartition P β := by
  classical
  have hfin := finite_setOf_negRootWt_eq P β
  rw [coeffAt, kostantSeries, SummableFamily.coeff_hsum, finsum_eq_sum_of_support_subset _
    (s := hfin.toFinset), kostantPartition,
    show Nat.card {s // negRootWt P s = β} = Nat.card {s | negRootWt P s = β} from rfl,
    Nat.card_eq_card_finite_toFinset hfin]
  · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Set.Finite.mem_toFinset] at hs
    simp [kostantFamily, (show negRootWt P s = β from hs).symm]
  · intro s hs
    rw [Function.mem_support] at hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra h
    refine hs (coeff_single_of_ne fun hg ↦ h ?_)
    simpa using hg.symm

/-- `∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α} · ∏_{α ∈ Δ₊} (1 - e^{-α})^{-mult α} = 1`. -/
theorem denominator_mul_kostantSeries : denominator P * kostantSeries P = 1 := by
  classical
  rw [denominator, kostantSeries, ← SummableFamily.hsum_mul]
  refine HahnSeries.ext (funext fun g ↦ ?_)
  have hfin := finite_setOf_pairWeight_eq P (-ofWeightOrd P g)
  have hmul : ∀ p : Finset (NegRootIndex P) × (NegRootIndex P →₀ ℕ),
      ((denominatorFamily P).mul (kostantFamily P) p).coeff g =
        if Finsupp.PairInvolution.pairWeight NegRootIndex.root p = -ofWeightOrd P g then
          (-1) ^ p.1.card else 0 := by
    intro p
    simp only [SummableFamily.mul_toFun, denominatorFamily, kostantFamily,
      SummableFamily.coe_mk, single_mul_single, mul_one, coeff_single]
    refine if_congr ?_ rfl rfl
    rw [← map_add, ← neg_add]
    change _ ↔ finsetWt P p.1 + negRootWt P p.2 = _
    constructor
    · rintro rfl
      simp
    · intro h
      rw [h, neg_neg, toWeightOrd_ofWeightOrd]
  rw [SummableFamily.coeff_hsum, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset)]
  · rw [Finset.sum_congr rfl fun p hp ↦
      (hmul p).trans (ite_eq_left ((Set.Finite.mem_toFinset _).mp hp))]
    rw [Finsupp.PairInvolution.sum_neg_one_pow_card_eq_ite _ _ fun p ↦ Set.Finite.mem_toFinset _,
      coeff_one, neg_eq_zero]
    exact if_congr ⟨fun h ↦ by rw [← toWeightOrd_ofWeightOrd P g, h]; rfl,
      fun h ↦ by rw [h]; rfl⟩ rfl rfl
  · intro p hp
    rw [Function.mem_support, hmul] at hp
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra h
    exact hp (ite_eq_right h)

namespace VermaModule

/-- `ch M(Λ) = e^Λ ∑_β K(β) e^{-β}` ([Kac] (9.7.2) (check)). -/
theorem character_eq_exp_mul_kostantSeries (Λ : Dual K H) :
    (isCategoryO P Λ).character = exp P ℤ Λ * kostantSeries P := by
  rw [character_eq]
  congr 1
  ext μ
  rw [IsCategoryO.coeffAt_character, ← neg_neg μ, coeffAt_kostantSeries,
    ← finrank_weightSpace_sub P 0 (-μ), zero_sub]

/-- **The character of a Verma module** ([Kac] (9.7.2) (check)):
`ch M(Λ) = e^Λ ∏_{α ∈ Δ₊} (1 - e^{-α})^{-mult α}`, in the form `R · ch M(Λ) = e^Λ`, where `R` is
the denominator. -/
theorem denominator_mul_character (Λ : Dual K H) :
    denominator P * (isCategoryO P Λ).character = exp P ℤ Λ := by
  rw [character_eq_exp_mul_kostantSeries, mul_left_comm, denominator_mul_kostantSeries, mul_one]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
