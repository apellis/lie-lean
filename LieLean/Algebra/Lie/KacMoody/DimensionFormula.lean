/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterFormula
import LieLean.Algebra.Lie.KacMoody.FiniteDimensional
import LieLean.Algebra.Lie.KacMoody.WeightBasis
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupForm
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Weyl's dimension formula

For a Cartan matrix `A` of finite type and a dominant integral weight `Λ`, the dimension of the
irreducible module `L(Λ)` is
`dim L(Λ) = ∏_{α ∈ Δ₊} (Λ + ρ | α) / ∏_{α ∈ Δ₊} (ρ | α)` (Humphreys, GSM 94, Thm. 2.5).

## Proof (Humphreys, GSM 94, §2.5)

For additive maps `φ_a : 𝔥* → K`, the operators `∂_a e^μ = φ_a(μ) e^μ` on the group ring `ℤ[𝔥*]`
are commuting derivations. Let `E_S` be `∏_{a ∈ S} ∂_a` followed by the augmentation `e^μ ↦ 1`
(`AddMonoidAlgebra.augDeriv`). By the Leibniz rule, `E_S((∏_{j ∈ J} f_j) g) = E_S(∏ f_j) E_∅(g)`
when `|S| = |J|` and every `f_j` has augmentation zero (`AddMonoidAlgebra.augDeriv_prod_mul`).
Apply `E_{Δ₊}`, with `φ_α = (· | α)`, to the Weyl character formula
`∏_{α ∈ Δ₊} (1 - e^{-α}) · e^ρ ch L(Λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`, read in `ℤ[𝔥*]`
(`IrreducibleModule.denominatorAlg_mul_eq_sum`). The left side gives
`E_{Δ₊}(∏ (1 - e^{-α})) dim L(Λ)`. Since `∏_{α ∈ Δ₊} (w μ | α) = (-1)^{ℓ(w)} ∏_{α ∈ Δ₊} (μ | α)`
(`prod_posRootFinset_weylGroup`), the right side gives `|W| ∏_{α ∈ Δ₊} (Λ + ρ | α)`. The case
`Λ = 0` determines the constant `E_{Δ₊}(∏ (1 - e^{-α})) = |W| ∏_{α ∈ Δ₊} (ρ | α)`.

Humphreys works with the coroot pairings `⟨μ, α^∨⟩ = 2 (μ | α) / (α | α)`; the quotient is the
same for the form `(· | ·)` of any symmetrization of `A`.

## Main definitions

* `AddMonoidAlgebra.augDeriv`: the map `E_S : ℤ[G] → K`, `e^μ ↦ ∏_{a ∈ S} φ_a(μ)`.
* `Matrix.Realization.KacMoodyAlgebra.toCharacterRing`: the ring homomorphism `ℤ[𝔥*] → ℰ`.
* `Matrix.Realization.KacMoodyAlgebra.posRootFinset`: the finite set `Δ₊` in finite type.

## Main results

* `AddMonoidAlgebra.augDeriv_prod_mul`: the vanishing behind the proof.
* `Matrix.Realization.KacMoodyAlgebra.toCharacterRing_denominatorAlg`: in finite type, the
  denominator `R` is `∏_{α ∈ Δ₊} (1 - e^{-α})`.
* `Matrix.Realization.KacMoodyAlgebra.prod_posRootFinset_weylGroup`:
  `∏_{α ∈ Δ₊} (w μ | α) = (-1)^{ℓ(w)} ∏_{α ∈ Δ₊} (μ | α)`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_eq_prod_div`: **Weyl's
  dimension formula**.

The source works with a semisimple Lie algebra over `ℂ`; here `A` is a Cartan matrix of finite
type over a field `K` of characteristic zero, with a finite-dimensional realization.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  §2.5.
-/

open Finset

noncomputable section

namespace AddMonoidAlgebra

variable {G κ K : Type*} [AddCommMonoid G] [CommRing K]

/-- For a family `φ` of additive maps `G → K` and a finite set `S` of indices, the additive map
`ℤ[G] → K`, `∑ n_μ e^μ ↦ ∑ n_μ ∏_{a ∈ S} φ_a(μ)`. It is the augmentation `e^μ ↦ 1` composed with
the product `∏_{a ∈ S} ∂_a` of the commuting derivations `∂_a e^μ = φ_a(μ) e^μ`
(Humphreys, GSM 94, §2.5). -/
def augDeriv (φ : κ → G →+ K) (S : Finset κ) : AddMonoidAlgebra ℤ G →+ K :=
  (Finsupp.liftAddHom fun μ ↦ (AddMonoidHom.mulRight (∏ a ∈ S, φ a μ)).comp
    (Int.castAddHom K)).comp (coeffAddEquiv : AddMonoidAlgebra ℤ G ≃+ (G →₀ ℤ)).toAddMonoidHom

variable (φ : κ → G →+ K)

@[simp]
lemma augDeriv_single (S : Finset κ) (μ : G) (n : ℤ) :
    augDeriv φ S (single μ n) = n * ∏ a ∈ S, φ a μ := by
  simp [augDeriv]

lemma augDeriv_mul [DecidableEq κ] (S : Finset κ) (f g : AddMonoidAlgebra ℤ G) :
    augDeriv φ S (f * g) =
      ∑ T ∈ S.powerset, augDeriv φ T f * augDeriv φ (S \ T) g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, sum_add_distrib]
  | single μ m =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, sum_add_distrib]
    | single ν n =>
      simp only [single_mul_single, augDeriv_single, map_add, prod_add, mul_sum]
      refine sum_congr rfl fun T _ ↦ ?_
      push_cast
      ring

lemma augDeriv_empty_mul (f g : AddMonoidAlgebra ℤ G) :
    augDeriv φ ∅ (f * g) = augDeriv φ ∅ f * augDeriv φ ∅ g := by
  classical
  simp [augDeriv_mul]

@[simp]
lemma augDeriv_empty_one : augDeriv φ (∅ : Finset κ) 1 = 1 := by
  simp [one_def]

/-- The vanishing behind Weyl's dimension formula (Humphreys, GSM 94, proof of Thm. 2.5): let
`f_j`, `j ∈ J`, have augmentation zero. If `|S| < |J|`, the augmented derivative `∂_S` of
`(∏_J f_j) g` vanishes; if `|S| = |J|`, it is `∂_S(∏_J f_j)` times the augmentation of `g`. -/
theorem augDeriv_prod_mul {ι : Type*} (f : ι → AddMonoidAlgebra ℤ G)
    (J : Finset ι) (hf : ∀ j ∈ J, augDeriv φ ∅ (f j) = 0) :
    ∀ (S : Finset κ) (g : AddMonoidAlgebra ℤ G),
      (#S < #J → augDeriv φ S ((∏ j ∈ J, f j) * g) = 0) ∧
      (#S = #J → augDeriv φ S ((∏ j ∈ J, f j) * g) =
        augDeriv φ S (∏ j ∈ J, f j) * augDeriv φ ∅ g) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro S g
    refine ⟨fun h ↦ absurd h (by simp), fun h ↦ ?_⟩
    obtain rfl : S = ∅ := card_eq_zero.mp (by simpa using h)
    simp
  | @insert a J ha ih =>
    intro S g
    have hf' : ∀ j ∈ J, augDeriv φ ∅ (f j) = 0 := fun j hj ↦ hf j (mem_insert_of_mem hj)
    have hfa : augDeriv φ ∅ (f a) = 0 := hf a (mem_insert_self a J)
    -- expand `∂_S (f a · X)` by the Leibniz rule
    have hexp : ∀ X, augDeriv φ S ((∏ j ∈ insert a J, f j) * X) =
        ∑ T ∈ S.powerset, augDeriv φ T (f a) * augDeriv φ (S \ T) ((∏ j ∈ J, f j) * X) := by
      intro X
      rw [prod_insert ha, mul_assoc, augDeriv_mul]
    have hcardT : ∀ T ∈ S.powerset, T ≠ ∅ → #(S \ T) < #S := fun T hT hT0 ↦ by
      rw [card_sdiff_of_subset (mem_powerset.mp hT)]
      have := card_pos.mpr (nonempty_iff_ne_empty.mpr hT0)
      have := card_le_card (mem_powerset.mp hT)
      omega
    rw [card_insert_of_notMem ha]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [hexp]
      refine sum_eq_zero fun T hT ↦ ?_
      by_cases hT0 : T = ∅
      · rw [hT0, hfa, zero_mul]
      · rw [(ih hf' (S \ T) g).1 (by have := hcardT T hT hT0; omega), mul_zero]
    · have key : ∀ X, augDeriv φ S ((∏ j ∈ insert a J, f j) * X) =
          (∑ T ∈ S.powerset, augDeriv φ T (f a) * augDeriv φ (S \ T) (∏ j ∈ J, f j)) *
            augDeriv φ ∅ X := by
        intro X
        rw [hexp, sum_mul]
        refine sum_congr rfl fun T hT ↦ ?_
        by_cases hT0 : T = ∅
        · rw [hT0, hfa, zero_mul, zero_mul, zero_mul]
        by_cases h1 : #(S \ T) = #J
        · rw [(ih hf' (S \ T) X).2 h1, mul_assoc]
        · have hlt : #(S \ T) < #J := by have := hcardT T hT hT0; omega
          have h1' := (ih hf' (S \ T) 1).1 hlt
          rw [mul_one] at h1'
          rw [(ih hf' (S \ T) X).1 hlt, h1']; simp
      rw [key g, ← mul_one (∏ j ∈ insert a J, f j), key 1, augDeriv_empty_one, mul_one]

end AddMonoidAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

open AddMonoidAlgebra CharacterRing WeightOrd Module

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Finite formal characters -/

/-- The ring homomorphism `ℤ[𝔥*] → ℰ`, `e^μ ↦ e^μ`, from the group ring of `𝔥*` (finite formal
characters) to the algebra of formal characters. -/
noncomputable def toCharacterRing : AddMonoidAlgebra ℤ (Dual K H) →+* P.CharacterRing ℤ :=
  (AddMonoidAlgebra.lift ℤ (P.CharacterRing ℤ) (Dual K H)
    { toFun := fun μ ↦ exp P ℤ μ.toAdd
      map_one' := exp_zero
      map_mul' := fun μ ν ↦ exp_add μ.toAdd ν.toAdd }).toRingHom

omit [DecidableEq ι] in
lemma toCharacterRing_single (μ : Dual K H) (n : ℤ) :
    toCharacterRing P (AddMonoidAlgebra.single μ n) = n • exp P ℤ μ := by
  simp [toCharacterRing]

omit [DecidableEq ι] in
lemma coeffAt_toCharacterRing (f : AddMonoidAlgebra ℤ (Dual K H)) (μ : Dual K H) :
    (toCharacterRing P f).coeffAt μ = f.coeff μ := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, HahnSeries.coeff_add, coeff_add, Finsupp.add_apply, hf, hg]
  | single ν n =>
    rw [toCharacterRing_single, coeffAt, HahnSeries.coeff_smul, ← coeffAt, coeff_exp,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : μ = ν
    · simp [h]
    · simp [h, Ne.symm h]

omit [DecidableEq ι] in
lemma toCharacterRing_injective : Function.Injective (toCharacterRing P) := fun f g h ↦ by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext (f := f.coeff) (g := g.coeff) fun μ ↦ ?_)
  rw [← coeffAt_toCharacterRing P f μ, ← coeffAt_toCharacterRing P g μ, h]

/-! ### Finite type -/

section FiniteType

variable (hA : A.IsFiniteCartan)
include hA

/-- The finite set `Δ₊` of positive roots of `𝔤(A)`, for `A` of finite type. -/
noncomputable def posRootFinset : Finset (Dual K H) :=
  (Set.Finite.subset (finite_roots P hA) (t := {α | α ∈ roots P ∧ α ∈ P.posWeights})
    fun _ h ↦ h.1).toFinset

lemma mem_posRootFinset {α : Dual K H} :
    α ∈ posRootFinset P hA ↔ α ∈ roots P ∧ α ∈ P.posWeights := by
  simp [posRootFinset]

lemma NegRootIndex.root_mem_posRootFinset (x : NegRootIndex P) :
    x.root ∈ posRootFinset P hA := by
  obtain ⟨⟨α, hα⟩, j⟩ := x
  refine (mem_posRootFinset P hA).mpr ⟨?_, hα⟩
  have hne : rootSpace P (-α) ≠ ⊥ := fun h ↦ by
    have : 0 < finrank K (rootSpace P (-α)) := Fin.pos j
    rw [h, finrank_bot] at this
    exact lt_irrefl 0 this
  have hroot : -α ∈ roots P :=
    ⟨neg_ne_zero.mpr fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ hα), hne⟩
  simpa [NegRootIndex.root] using neg_mem_roots P hroot

/-- In finite type, the index set of a root-vector basis of `𝔫₋` is the set of positive roots. -/
noncomputable def negRootIndexEquiv : NegRootIndex P ≃ posRootFinset P hA where
  toFun x := ⟨x.root, NegRootIndex.root_mem_posRootFinset P hA x⟩
  invFun α := ⟨⟨α.1, ((mem_posRootFinset P hA).mp α.2).2⟩, ⟨0, by
    rw [finrank_rootSpace_of_mem_roots P hA (neg_mem_roots P ((mem_posRootFinset P hA).mp α.2).1)]
    exact one_pos⟩⟩
  left_inv x := by
    obtain ⟨⟨α, hα⟩, j⟩ := x
    have hmem := (mem_posRootFinset P hA).mp (NegRootIndex.root_mem_posRootFinset P hA ⟨⟨α, hα⟩, j⟩)
    have h1 : finrank K (rootSpace P (-α)) = 1 :=
      finrank_rootSpace_of_mem_roots P hA (neg_mem_roots P hmem.1)
    have hj := j.2
    refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
    simp only at hj ⊢
    omega
  right_inv _ := rfl

@[simp] lemma coe_negRootIndexEquiv_apply (x : NegRootIndex P) :
    (negRootIndexEquiv P hA x : Dual K H) = x.root := rfl

/-- The Weyl denominator `∏_{α ∈ Δ₊} (1 - e^{-α})` as a finite formal character. -/
noncomputable def denominatorAlg : AddMonoidAlgebra ℤ (Dual K H) :=
  ∏ α ∈ posRootFinset P hA, (1 - AddMonoidAlgebra.single (-α) 1)

omit [CharZero K] hA in
lemma prod_neg_single_neg_root (T : Finset (NegRootIndex P)) :
    ∏ x ∈ T, (-AddMonoidAlgebra.single (-x.root) 1 : AddMonoidAlgebra ℤ (Dual K H)) =
      AddMonoidAlgebra.single (-finsetWt P T) ((-1) ^ T.card) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [finsetWt, AddMonoidAlgebra.one_def]
  | @insert a T ha ih =>
    rw [Finset.prod_insert ha, ih, neg_mul, AddMonoidAlgebra.single_mul_single,
      Finset.card_insert_of_notMem ha,
      show finsetWt P (insert a T) = a.root + finsetWt P T from Finset.sum_insert ha,
      ← AddMonoidAlgebra.single_neg, pow_succ]
    congr 1 <;> first | ring | abel

/-- In finite type, the denominator `R ∈ ℰ` is the image of `∏_{α ∈ Δ₊} (1 - e^{-α})`. -/
theorem toCharacterRing_denominatorAlg :
    toCharacterRing P (denominatorAlg P hA) = denominator P := by
  classical
  let : Fintype (NegRootIndex P) := Fintype.ofEquiv _ (negRootIndexEquiv P hA).symm
  have h1 : denominatorAlg P hA =
      ∑ T : Finset (NegRootIndex P), AddMonoidAlgebra.single (-finsetWt P T) ((-1) ^ T.card) := by
    rw [denominatorAlg, ← Finset.prod_coe_sort,
      ← (negRootIndexEquiv P hA).prod_comp
        (fun α ↦ (1 - AddMonoidAlgebra.single (-(α : Dual K H)) 1))]
    simp only [coe_negRootIndexEquiv_apply, sub_eq_neg_add]
    rw [Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun T _ ↦ ?_
    rw [Finset.prod_const_one, mul_one]
    exact prod_neg_single_neg_root P T
  ext μ
  rw [coeffAt_toCharacterRing, h1, coeff_sum, Finsupp.finsetSum_apply, denominator, coeffAt,
    HahnSeries.SummableFamily.coeff_hsum, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  simp only [denominatorFamily, HahnSeries.SummableFamily.coe_mk, HahnSeries.coeff_single,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : μ = -finsetWt P T
  · simp [h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right fun hμ ↦ h ((toWeightOrd P).injective hμ)]

/-! ### The dimension formula -/

variable [FiniteDimensional K H] (S : A.Symmetrization)

/-- `∏_{α ∈ Δ₊} (rᵢ μ | α) = -∏_{α ∈ Δ₊} (μ | α)`: `rᵢ` permutes `Δ₊ \ {αᵢ}` and sends `αᵢ` to
`-αᵢ`. -/
lemma prod_posRootFinset_reflection (i : ι) (μ : Dual K H) :
    ∏ α ∈ posRootFinset P hA,
        P.dualBilinForm S (P.reflection hA.isGeneralizedCartan i μ) α =
      -∏ α ∈ posRootFinset P hA, P.dualBilinForm S μ α := by
  classical
  set hGC := hA.isGeneralizedCartan
  set r := P.reflection hGC i
  have hr : ∀ α, P.dualBilinForm S (r μ) α = P.dualBilinForm S μ (r α) := fun α ↦ by
    have := P.dualBilinForm_reflection hGC S i (r μ) α
    simp only [r, reflection_reflection] at this
    exact this.symm
  simp_rw [hr]
  have hi : P.root i ∈ posRootFinset P hA :=
    (mem_posRootFinset P hA).mpr ⟨root_mem_roots P i, P.root_mem_posWeights i⟩
  rw [← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ _ hi]
  simp only [r, reflection_root_self, map_neg, neg_mul]
  congr 2
  have hmem : ∀ α ∈ (posRootFinset P hA).erase (P.root i),
      r α ∈ (posRootFinset P hA).erase (P.root i) := by
    intro α hα
    obtain ⟨hne, hα⟩ := Finset.mem_erase.mp hα
    obtain ⟨hroot, hpos⟩ := (mem_posRootFinset P hA).mp hα
    refine Finset.mem_erase.mpr ⟨fun h ↦ ?_, (mem_posRootFinset P hA).mpr
      ⟨apply_mem_roots P hGC (P.reflection_mem_weylGroup hGC i) hroot,
        reflection_mem_posWeights P hGC hroot hpos hne⟩⟩
    have : α = -P.root i := by
      rw [← reflection_reflection P hGC i α]
      simp only [r] at h
      rw [h, reflection_root_self]
    exact Set.disjoint_left.mp P.disjoint_posWeights_negWeights hpos
      (this ▸ P.neg_root_mem_negWeights i)
  exact Finset.prod_nbij' r r hmem hmem (fun α _ ↦ reflection_reflection P hGC i α)
    (fun α _ ↦ reflection_reflection P hGC i α) fun _ _ ↦ rfl

/-- `∏_{α ∈ Δ₊} (w μ | α) = (-1)^{ℓ(w)} ∏_{α ∈ Δ₊} (μ | α)` for `w ∈ W`. -/
theorem prod_posRootFinset_weylGroup (w : P.weylGroup hA.isGeneralizedCartan) (μ : Dual K H) :
    ∏ α ∈ posRootFinset P hA, P.dualBilinForm S ((w : Dual K H ≃ₗ[K] Dual K H) μ) α =
      (-1) ^ (P.coxeterSystem hA.isGeneralizedCartan).length w *
        ∏ α ∈ posRootFinset P hA, P.dualBilinForm S μ α := by
  set cs := P.coxeterSystem hA.isGeneralizedCartan
  induction w using cs.simple_induction_left generalizing μ with
  | one => simp
  | mul_simple_left w i ih =>
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple,
      prod_posRootFinset_reflection, ih]
    rcases cs.length_simple_mul w i with h | h
    · rw [h, pow_succ]; ring
    · rw [← h, pow_succ]; ring

omit [DecidableEq ι] hA in
/-- `(ρ | α) ≠ 0` for `α ∈ Q₊ \ {0}`. -/
lemma dualBilinForm_rho_ne_zero {α : Dual K H} (hα : α ∈ P.posWeights) :
    P.dualBilinForm S P.rho α ≠ 0 := by
  obtain ⟨k, ⟨hk0, hkne⟩, rfl⟩ := hα
  have h : P.dualBilinForm S P.rho (P.rootOf k) = ((∑ i, (k i : ℚ) * (S.ε i)⁻¹ : ℚ) : K) := by
    rw [rootOf_apply, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, dualBilinForm_rho_root, smul_eq_mul]
  rw [h, Rat.cast_ne_zero]
  refine (Finset.sum_pos' (fun i _ ↦ mul_nonneg (by exact_mod_cast hk0 i)
    (inv_nonneg.mpr (S.ε_pos i).le)) ?_).ne'
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra! h0
    exact hkne (funext h0)
  exact ⟨i, Finset.mem_univ _, mul_pos (by exact_mod_cast lt_of_le_of_ne (hk0 i) (Ne.symm hi))
    (inv_pos.mpr (S.ε_pos i))⟩

/-- For `Λ` dominant integral, `ch L(Λ)` is the image of a finite formal character whose
augmentation is `dim L(Λ)`. -/
theorem IrreducibleModule.exists_toCharacterRing_eq_character {Λ : Dual K H}
    (hΛ : P.IsDominantIntegral Λ) {κ : Type*} (φ : κ → Dual K H →+ K) :
    ∃ χ : AddMonoidAlgebra ℤ (Dual K H),
      toCharacterRing P χ = (isCategoryO P Λ).character ∧
        augDeriv φ ∅ χ = finrank K (IrreducibleModule P Λ) := by
  classical
  have := IrreducibleModule.finiteDimensional hA hΛ
  let b := (isCategoryO P Λ).weightBasis
  have : Finite (WeightBasisIndex P (IrreducibleModule P Λ)) := Module.Finite.finite_basis b
  set d : Dual K H → ℕ := fun μ ↦ finrank K (weightSpace P (IrreducibleModule P Λ) μ)
  have hfin : {μ | d μ ≠ 0}.Finite :=
    (Set.finite_range (Sigma.fst : WeightBasisIndex P (IrreducibleModule P Λ) → Dual K H)).subset
      fun μ hμ ↦ ⟨⟨μ, ⟨0, Nat.pos_of_ne_zero hμ⟩⟩, rfl⟩
  set s := hfin.toFinset
  refine ⟨∑ μ ∈ s, AddMonoidAlgebra.single μ (d μ : ℤ), ?_, ?_⟩
  · ext μ
    rw [coeffAt_toCharacterRing, IsCategoryO.coeffAt_character, coeff_sum,
      Finsupp.finsetSum_apply]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs with hμ
    · rfl
    · simp only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hμ
      exact_mod_cast hμ.symm
  · simp only [map_sum, augDeriv_single, Finset.prod_empty, mul_one, Int.cast_natCast]
    let e : WeightBasisIndex P (IrreducibleModule P Λ) ≃ Σ μ : s, Fin (d μ) :=
      { toFun := fun x ↦ ⟨⟨x.1, (Set.Finite.mem_toFinset hfin).mpr (Fin.pos x.2).ne'⟩, x.2⟩
        invFun := fun y ↦ ⟨y.1.1, y.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Module.finrank_eq_nat_card_basis b, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_sigma]
    simp only [Fintype.card_fin, Nat.cast_sum]
    exact (Finset.sum_coe_sort s fun μ ↦ (d μ : K)).symm

/-- The Weyl character formula as an identity of finite formal characters:
`∏_{α ∈ Δ₊} (1 - e^{-α}) · e^ρ · χ = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}` if `χ ↦ ch L(Λ)`. -/
theorem IrreducibleModule.denominatorAlg_mul_eq_sum [Fintype (P.weylGroup hA.isGeneralizedCartan)]
    {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) {χ : AddMonoidAlgebra ℤ (Dual K H)}
    (hχ : toCharacterRing P χ = (isCategoryO P Λ).character) :
    denominatorAlg P hA * (AddMonoidAlgebra.single P.rho 1 * χ) =
      ∑ w : P.weylGroup hA.isGeneralizedCartan, AddMonoidAlgebra.single
        ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho))
        ((-1) ^ (P.coxeterSystem hA.isGeneralizedCartan).length w) := by
  classical
  apply toCharacterRing_injective P
  rw [map_mul, map_mul, hχ, toCharacterRing_denominatorAlg, toCharacterRing_single, one_smul,
    ← mul_assoc, mul_comm (denominator P),
    IrreducibleModule.exp_rho_mul_denominator_mul_character hA.isGeneralizedCartan
      hA.isSymmetrizable hΛ]
  ext μ
  rw [coeffAt_weylAltSum, coeffAt_toCharacterRing, finsum_eq_sum_of_fintype, coeff_sum,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- **Weyl's dimension formula** in product form: for `A` of finite type and `Λ` dominant
integral, `dim L(Λ) · ∏_{α ∈ Δ₊} (ρ | α) = ∏_{α ∈ Δ₊} (Λ + ρ | α)`. -/
theorem IrreducibleModule.finrank_mul_prod_eq_prod {Λ : Dual K H}
    (hΛ : P.IsDominantIntegral Λ) :
    (finrank K (IrreducibleModule P Λ) : K) * ∏ α ∈ posRootFinset P hA, P.dualBilinForm S P.rho α =
      ∏ α ∈ posRootFinset P hA, P.dualBilinForm S (Λ + P.rho) α := by
  classical
  set hGC := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  let _ : Fintype (P.weylGroup hGC) := Fintype.ofFinite _
  let φ : Dual K H → Dual K H →+ K := fun α ↦ ((P.dualBilinForm S).flip α).toAddMonoidHom
  have hφ (α μ : Dual K H) : φ α μ = P.dualBilinForm S μ α := rfl
  set E := augDeriv φ (posRootFinset P hA)
  -- `E` applied to both sides of the character formula.
  have key : ∀ Λ : Dual K H, P.IsDominantIntegral Λ → ∀ χ : AddMonoidAlgebra ℤ (Dual K H),
      toCharacterRing P χ = (isCategoryO P Λ).character →
      E (denominatorAlg P hA) * augDeriv φ ∅ χ =
        Fintype.card (P.weylGroup hGC) *
          ∏ α ∈ posRootFinset P hA, P.dualBilinForm S (Λ + P.rho) α := by
    intro Λ hΛ χ hχ
    have hf : ∀ α ∈ posRootFinset P hA,
        augDeriv φ ∅ (1 - AddMonoidAlgebra.single (-α) 1 : AddMonoidAlgebra ℤ (Dual K H)) = 0 :=
      fun α _ ↦ by simp
    have hL : E (denominatorAlg P hA * (AddMonoidAlgebra.single P.rho 1 * χ)) =
        E (denominatorAlg P hA) * augDeriv φ ∅ χ := by
      rw [denominatorAlg, ((augDeriv_prod_mul φ (fun α ↦ 1 - AddMonoidAlgebra.single (-α) 1)
        (posRootFinset P hA) hf) (posRootFinset P hA) _).2 rfl, augDeriv_empty_mul,
        augDeriv_single, Finset.prod_empty, mul_one, Int.cast_one, one_mul]
    rw [← hL, IrreducibleModule.denominatorAlg_mul_eq_sum P hA hΛ hχ, map_sum]
    simp only [E, augDeriv_single, hφ, prod_posRootFinset_weylGroup P hA S, Int.cast_pow,
      Int.cast_neg, Int.cast_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h0 := key 0 (isDominantIntegral_zero (P := P)) 1
    (by rw [map_one, IrreducibleModule.character_zero hGC])
  obtain ⟨χ, hχ, hdim⟩ := IrreducibleModule.exists_toCharacterRing_eq_character P hA hΛ φ
  have h1 := key Λ hΛ χ hχ
  rw [augDeriv_empty_one, mul_one, zero_add] at h0
  rw [hdim] at h1
  have hW : (Fintype.card (P.weylGroup hGC) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_left_cancel₀ hW
  rw [← h1, h0]
  ring

/-- **Weyl's dimension formula** (Humphreys, GSM 94, Thm. 2.5): for `A` of finite type and `Λ`
dominant integral, `dim L(Λ) = ∏_{α ∈ Δ₊} (Λ + ρ | α) / (ρ | α)`, for the form `(· | ·)` of any
symmetrization of `A`. Humphreys states it for a semisimple Lie algebra over `ℂ`, with the coroot
pairings `⟨μ, α^∨⟩ = 2 (μ | α) / (α | α)` in place of `(μ | α)`, which gives the same quotient. -/
theorem IrreducibleModule.finrank_eq_prod_div {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) :
    (finrank K (IrreducibleModule P Λ) : K) =
      ∏ α ∈ posRootFinset P hA, P.dualBilinForm S (Λ + P.rho) α / P.dualBilinForm S P.rho α := by
  have hne : ∏ α ∈ posRootFinset P hA, P.dualBilinForm S P.rho α ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun α hα ↦
      dualBilinForm_rho_ne_zero P S ((mem_posRootFinset P hA).mp hα).2
  rw [Finset.prod_div_distrib, eq_div_iff hne]
  exact IrreducibleModule.finrank_mul_prod_eq_prod P hA S hΛ

end FiniteType

end Matrix.Realization.KacMoodyAlgebra
