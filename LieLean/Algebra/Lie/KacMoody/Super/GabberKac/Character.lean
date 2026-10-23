/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterAntiInvariant
import LieLean.Algebra.Lie.KacMoody.CharacterFormula
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.Character
import LieLean.Algebra.Lie.KacMoody.GabberKac
import LieLean.Algebra.Lie.KacMoody.Kostant.Degree0
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.Cancellation
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.CasimirExpansion
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.IntegrableAt
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupForm

/-!
# The character of the Verma module of `G(A, τ)`

Let `G(A, τ)` be the contragredient Lie superalgebra of a symmetrizable generalized Cartan matrix
`A` with an admissible parity `τ`, and `M̄(Λ)` its Verma module. Write `D = ch M̄(0) = ∑_β
dim M̄(0)_{-β} e^{-β}` and `R = ∏_{α > 0} (1 - e^{-α})^{mult α}` for the denominator of the
Kac–Moody algebra `𝔤(A)` with the same Cartan matrix. We prove `D R = 1`: the Verma modules of
`G(A, τ)` and of `𝔤(A)` have the same character. Equivalently, `dim M̄(Λ)_{Λ - β} = K(β)`, Kostant's
partition function of `𝔤(A)`.

This is the step of [Kac78] §2 which, combined with the Casimir operator, gives the analogue of the
Gabber–Kac theorem for `G(A, τ)`. In the even case it is the PBW theorem for `U(𝔫₋)` together with
Gabber–Kac; here it is proved directly, without any PBW basis of `U(𝔫̄₋)`.

The proof follows the argument of [Kac] §10.4 for the denominator identity. Let `Y = D R - 1`,
supported in `-Q₊ \ 0`, and suppose `Y ≠ 0`; let `-β` be a maximal weight of `Y`.

* Since `M̄(0) / U fᵢ v̄₀` is integrable at `i` (`GVerma.isIntegrableAt_quotient`), its character
  `(1 - e^{-αᵢ}) D` is `rᵢ`-invariant, and `e^ρ R` is `rᵢ`-anti-invariant, so `(1 - e^{-αᵢ}) e^ρ Y`
  is `rᵢ`-anti-invariant. Comparing coefficients at `ρ - β` and `rᵢ(ρ - β)` gives
  `⟨-β, αᵢ^∨⟩ ≥ 0` for all `i`.
* The quotient `T = M̄(0) / Σᵢ U fᵢ v̄₀` is one-dimensional, of weight `0`. Expanding `ch T` above
  `-β` in Verma characters `ch M̄(κ)` with `(κ + 2ρ | κ) = 0` (`IsCasimirModule.exists_expansion`)
  and multiplying by `R` shows that `-β` is either such a `κ` or a weight of `R`; in both cases
  `(-β + 2ρ | -β) = 0`, by the denominator identity of `𝔤(A)` in the second case.
* This contradicts `⟨-β, αᵢ^∨⟩ ≥ 0` (`dualBilinForm_neg_rootOf_add_two_rho_ne_zero`).

## Main definitions

* `Matrix.Realization.SuperEnveloping.vermaChar`: `D = ch M̄(0)`.

## Main results

* `Matrix.Realization.SuperEnveloping.vermaChar_mul_denominator`: `D R = 1`.
* `Matrix.Realization.SuperEnveloping.vermaChar_eq_kostantSeries`: `D = ∑_β K(β) e^{-β}`.
* `Matrix.Realization.SuperEnveloping.GVerma.finrank_modWeightSpace_sub_eq_kostantPartition`:
  `dim M̄(Λ)_{Λ - β} = K(β)`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.7, §10.4.
-/

universe u v w

open Module HahnSeries Matrix.Realization.CharacterRing Matrix.Realization.WeightOrd

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι : Type u} {K : Type v} {H : Type w} [Fintype ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} {p : ι → ZMod 2}
  [CharZero K]

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

/-! ### Elements of `ℰ` supported in `-Q₊` -/

variable (P) in
/-- `c ∈ ℰ` is supported in `-Q₊`. -/
def IsNegSupported (c : P.CharacterRing ℤ) : Prop :=
  ∀ μ, c.coeffAt μ ≠ 0 → ∃ k : ι → ℤ, 0 ≤ k ∧ μ = -P.rootOf k

/-- `ν` lies above `μ` in the order of `ℰ` when `ν - μ ∈ Q₊`. -/
lemma toWeightOrd_le_of_eq_add {μ ν : Dual K H} {k : ι → ℤ} (hk : 0 ≤ k)
    (h : ν = μ + P.rootOf k) : toWeightOrd P ν ≤ toWeightOrd P μ :=
  ⟨k, hk, by simp only [ofWeightOrd_toWeightOrd]; rw [h, add_sub_cancel_left]⟩

lemma toWeightOrd_lt_of_eq_add {μ ν : Dual K H} {k : ι → ℤ} (hk : k ∈ posCone ι)
    (h : ν = μ + P.rootOf k) : toWeightOrd P ν < toWeightOrd P μ := by
  refine lt_of_le_of_ne (toWeightOrd_le_of_eq_add hk.1 h) fun he ↦ hk.2 ?_
  have : ν = μ := (toWeightOrd P).injective he
  rw [this, left_eq_add, ← map_zero P.rootOf] at h
  exact P.rootOf_injective h

/-- If `d` is supported in `-Q₊`, the coefficient `(c d)_μ` only depends on the coefficients of
`c` at weights above `μ`. -/
lemma coeffAt_mul_congr {c c' d : P.CharacterRing ℤ} (hd : IsNegSupported P d) {μ : Dual K H}
    (h : ∀ ν, toWeightOrd P ν ≤ toWeightOrd P μ → c.coeffAt ν = c'.coeffAt ν) :
    (c * d).coeffAt μ = (c' * d).coeffAt μ := by
  rw [CharacterRing.coeff_mul, CharacterRing.coeff_mul]
  refine finsum_congr fun ν ↦ ?_
  by_cases h0 : d.coeffAt (μ - ν) = 0
  · rw [h0, mul_zero, mul_zero]
  obtain ⟨k, hk, hμν⟩ := hd _ h0
  have hν : ν = μ + P.rootOf k := by rw [← neg_neg (P.rootOf k), ← hμν]; abel
  rw [h ν (toWeightOrd_le_of_eq_add hk hν)]

lemma IsNegSupported.mul {c d : P.CharacterRing ℤ} (hc : IsNegSupported P c)
    (hd : IsNegSupported P d) : IsNegSupported P (c * d) := by
  intro μ hμ
  rw [CharacterRing.coeff_mul] at hμ
  obtain ⟨ν, hν⟩ : ∃ ν, c.coeffAt ν * d.coeffAt (μ - ν) ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (finsum_eq_zero_of_forall_eq_zero h)
  obtain ⟨a, ha, h1⟩ := hc ν (left_ne_zero_of_mul hν)
  obtain ⟨b, hb, h2⟩ := hd _ (right_ne_zero_of_mul hν)
  refine ⟨a + b, add_nonneg ha hb, ?_⟩
  rw [map_add, neg_add, ← h1, ← h2, add_sub_cancel]

lemma IsNegSupported.coeffAt_mul_zero {c d : P.CharacterRing ℤ} (hc : IsNegSupported P c)
    (hd : IsNegSupported P d) : (c * d).coeffAt 0 = c.coeffAt 0 * d.coeffAt 0 := by
  rw [CharacterRing.coeff_mul, finsum_eq_single _ 0 fun ν hν ↦ ?_, zero_sub, neg_zero]
  by_contra h
  obtain ⟨a, ha, h1⟩ := hc ν (left_ne_zero_of_mul h)
  obtain ⟨b, hb, h2⟩ := hd _ (right_ne_zero_of_mul h)
  rw [h1, zero_sub, neg_neg] at h2
  have hab : a + b = 0 := P.rootOf_injective (by rw [map_add, h2, neg_add_cancel, map_zero])
  have : a = 0 := le_antisymm (hab ▸ le_add_of_nonneg_right hb) ha
  rw [this, map_zero, neg_zero] at h1
  exact hν h1

variable [DecidableEq ι]

lemma isNegSupported_denominator : IsNegSupported P (KacMoodyAlgebra.denominator P) :=
  fun _ h ↦ KacMoodyAlgebra.exists_eq_neg_rootOf_of_coeffAt_denominator_ne_zero P h

lemma coeffAt_denominator_zero : (KacMoodyAlgebra.denominator P).coeffAt 0 = 1 := by
  classical
  rw [KacMoodyAlgebra.coeffAt_denominator, finsum_eq_single _ ∅ fun S hS ↦ ?_]
  · simp [KacMoodyAlgebra.finsetWt]
  · rw [ite_eq_right_iff]
    intro h
    exact absurd (neg_eq_zero.1 h)
      (KacMoodyAlgebra.finsetWt_ne_zero P (Finset.nonempty_iff_ne_empty.2 hS))

/-! ### The character of `M̄(0)` -/

variable (P p) in
/-- The character `D = ch M̄(0) = ∑_β dim M̄(0)_{-β} e^{-β}`. -/
def vermaChar : P.CharacterRing ℤ :=
  ofFun P (fun μ ↦ (GVerma.vermaDim P p (-μ) : ℤ)) ⟨{0}, fun μ hμ ↦ by
    obtain ⟨d, hd, h⟩ := GVerma.exists_eq_rootOf_of_vermaDim_ne_zero (by exact_mod_cast hμ)
    exact ⟨0, Finset.mem_singleton_self _, d, hd, by rw [← h, zero_sub, neg_neg]⟩⟩

lemma coeffAt_vermaChar (μ : Dual K H) :
    (vermaChar P p).coeffAt μ = GVerma.vermaDim P p (-μ) := rfl

lemma isNegSupported_vermaChar : IsNegSupported P (vermaChar P p) := fun μ hμ ↦ by
  obtain ⟨d, hd, h⟩ := GVerma.exists_eq_rootOf_of_vermaDim_ne_zero (P := P) (p := p)
    (β := -μ) fun h ↦ hμ (by rw [coeffAt_vermaChar, h, Nat.cast_zero])
  exact ⟨d, hd, by rw [← h, neg_neg]⟩

lemma coeffAt_vermaChar_zero : (vermaChar P p).coeffAt 0 = 1 := by
  rw [coeffAt_vermaChar, neg_zero, GVerma.vermaDim_zero, Nat.cast_one]

/-! ### The quotients `M̄(0) / U fᵢ v̄₀` and `M̄(0) / Σᵢ U fᵢ v̄₀` -/

omit [Fintype ι] [CharZero K] [DecidableEq ι] in
lemma _root_.FreeAlgebra.word_append_singleton (w : List ι) (i : ι) :
    FreeAlgebra.word (R := K) (w ++ [i]) = FreeAlgebra.word w * FreeAlgebra.ι K i := by
  induction w with
  | nil => simp [FreeAlgebra.word_nil, FreeAlgebra.word_cons]
  | cons j w ih =>
    rw [List.cons_append, FreeAlgebra.word_cons, FreeAlgebra.word_cons, ih, mul_assoc]

lemma wordVector_append (w : List ι) (i : ι) :
    GVerma.wordVector P p 0 (w ++ [i]) =
      syzComponent P p i (GVerma.wordVector P p (-P.root i) w) := by
  rw [GVerma.wordVector, GVerma.wordVector, syzComponent_fAlg_smul_hwv,
    FreeAlgebra.word_append_singleton, map_mul, mul_smul, fAlg_ι]

lemma syzComponent_mem_range (i : ι) (v : GVerma P p (-P.root i)) :
    syzComponent P p i v ∈ LinearMap.range (syzMap P p) := by
  refine ⟨Pi.single i v, ?_⟩
  rw [syzMap_apply, Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero])
    (by simp), Pi.single_eq_same]

/-- The image of `fᵢ`: it lies in the sum of the nonzero weight spaces of `M̄(0)`. -/
lemma syzComponent_mem_iSup (i : ι) (v : GVerma P p (-P.root i)) :
    syzComponent P p i v ∈ ⨆ μ, ⨆ (_ : μ ≠ 0), modWeightSpace P p (GVerma P p 0) μ := by
  have hv : v ∈ Submodule.span K (Set.range (GVerma.wordVector P p (-P.root i))) := by
    rw [GVerma.span_wordVector]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← wordVector_append]
    refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem ?_ (GVerma.wordVector_mem _))
    rw [zero_sub, neg_ne_zero, ← map_zero P.rootOf]
    intro h
    exact (by simp : w ++ [i] ≠ []) (wordVec_eq_zero_iff.1 (P.rootOf_injective h))
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [(syzComponent P p i).map_smul_of_tower]; exact Submodule.smul_mem _ a hx

lemma hwv_notMem_range_syzMap : GVerma.hwv P p 0 ∉ LinearMap.range (syzMap P p) := by
  rintro ⟨v, hv⟩
  have h1 : GVerma.hwv P p 0 ∈ ⨆ μ, ⨆ (_ : μ ≠ 0), modWeightSpace P p (GVerma P p 0) μ := by
    rw [← hv, syzMap_apply]
    exact Submodule.sum_mem _ fun i _ ↦ syzComponent_mem_iSup i (v i)
  have h0 : GVerma.hwv P p 0 ∈ modWeightSpace P p (GVerma P p 0) 0 := by
    rw [GVerma.modWeightSpace_self]; exact Submodule.mem_span_singleton_self _
  exact GVerma.hwv_ne_zero P p 0
    (Submodule.disjoint_def.1 (iSupIndep_modWeightSpace (GVerma P p 0) 0) _ h0 h1)

open Classical in
/-- `M̄(0) / Σᵢ U fᵢ v̄₀` is one-dimensional, of weight `0`. -/
lemma finrank_modWeightSpace_quotient_range_syzMap (μ : Dual K H) :
    finrank K (modWeightSpace P p (GVerma P p 0 ⧸ LinearMap.range (syzMap P p)) μ) =
      if μ = 0 then 1 else 0 := by
  have hV := (GVerma.isBounded (P := P) (p := p) (Λ := 0)).iSup_modWeightSpace_eq_top
  rw [modWeightSpace_quotient _ hV]
  split_ifs with hμ
  · subst hμ
    rw [GVerma.modWeightSpace_self, Submodule.map_span, Set.image_singleton,
      finrank_span_singleton]
    intro h
    exact hwv_notMem_range_syzMap ((Submodule.Quotient.mk_eq_zero _).1 h)
  · have h := GVerma.modWeightSpace_sub_eq P p 0 (-μ)
    rw [sub_neg_eq_add, zero_add] at h
    rw [h, Submodule.map_span]
    rw [Submodule.span_eq_bot.2 ?_, finrank_bot]
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rcases List.eq_nil_or_concat w with rfl | ⟨w', i, rfl⟩
    · refine absurd ?_ hμ
      rw [Set.mem_ofPred_eq] at hw
      simpa [wordVec_eq_zero_iff.2 rfl] using hw.symm
    · rw [List.concat_eq_append] at *
      simp only [LinearMap.coe_restrictScalars, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rw [wordVector_append]
      exact syzComponent_mem_range i _

/-! ### `rᵢ`-invariance of `(1 - e^{-αᵢ}) D` -/

lemma range_syzComponent_eq (i : ι) :
    LinearMap.range (syzComponent P p i) = Submodule.span 𝒰 {f P p i ^ 1 • GVerma.hwv P p 0} := by
  rw [LinearMap.range_eq_map, ← GVerma.span_hwv, Submodule.map_span, Set.image_singleton, pow_one]
  congr 2
  have := syzComponent_fAlg_smul_hwv (P := P) (p := p) i 1
  rwa [map_one, one_smul, one_smul] at this

lemma finrank_modWeightSpace_range_syzComponent (hA : A.IsGeneralizedCartan) (i : ι)
    (μ : Dual K H) :
    finrank K (modWeightSpace P p (LinearMap.range (syzComponent P p i)) μ) =
      GVerma.vermaDim P p (-P.root i - μ) := by
  rw [← finrank_modWeightSpace_equiv (LinearEquiv.ofInjective _ (syzComponent_injective hA i)),
    GVerma.finrank_modWeightSpace]

/-- The character of `M̄(0) / U fᵢ v̄₀` is `(1 - e^{-αᵢ}) D`. -/
lemma finrank_modWeightSpace_quotient_range_syzComponent (hA : A.IsGeneralizedCartan) (i : ι)
    (μ : Dual K H) :
    (finrank K (modWeightSpace P p (GVerma P p 0 ⧸ LinearMap.range (syzComponent P p i)) μ) :
      ℤ) = (vermaChar P p).coeffAt μ - (vermaChar P p).coeffAt (μ + P.root i) := by
  have hV := (GVerma.isBounded (P := P) (p := p) (Λ := 0)).iSup_modWeightSpace_eq_top
  have h := finrank_modWeightSpace_eq_add (LinearMap.range (syzComponent P p i)) hV μ
  rw [finrank_modWeightSpace_range_syzComponent hA, GVerma.finrank_modWeightSpace, zero_sub] at h
  have h' : -P.root i - μ = -(μ + P.root i) := by abel
  rw [coeffAt_vermaChar, coeffAt_vermaChar, h, h']
  push_cast
  ring

omit [DecidableEq ι] in
/-- The coefficient of `e^{-αᵢ}`-twisted products. -/
lemma coeffAt_one_sub_exp_mul (i : ι) (c : P.CharacterRing ℤ) (μ : Dual K H) :
    ((1 - exp P ℤ (-P.root i)) * c).coeffAt μ = c.coeffAt μ - c.coeffAt (μ + P.root i) := by
  rw [sub_mul, one_mul]
  simp only [coeffAt, HahnSeries.coeff_sub]
  rw [← coeffAt, ← coeffAt, ← coeffAt, coeff_exp_mul, sub_neg_eq_add]

omit [DecidableEq ι] in
lemma coeffAt_mul_reflection_of_anti {r : Dual K H ≃ₗ[K] Dual K H} {c d : P.CharacterRing ℤ}
    (hc : ∀ μ, c.coeffAt (r μ) = -c.coeffAt μ) (hd : ∀ μ, d.coeffAt (r μ) = d.coeffAt μ)
    (μ : Dual K H) : (c * d).coeffAt (r μ) = -(c * d).coeffAt μ := by
  rw [CharacterRing.coeff_mul, CharacterRing.coeff_mul, ← finsum_comp_equiv r.toEquiv,
    ← finsum_neg_distrib]
  refine finsum_congr fun ν ↦ ?_
  rw [LinearEquiv.coe_toEquiv, hc, ← map_sub, hd, neg_mul]

omit [DecidableEq ι] in
open Classical in
lemma coeffAt_one (μ : Dual K H) :
    (1 : P.CharacterRing ℤ).coeffAt μ = if μ = 0 then 1 else 0 := by
  rw [← exp_zero (P := P) (R := ℤ), coeff_exp]

omit [DecidableEq ι] in
lemma coeffAt_add (c d : P.CharacterRing ℤ) (μ : Dual K H) :
    (c + d).coeffAt μ = c.coeffAt μ + d.coeffAt μ := by
  simp only [coeffAt, HahnSeries.coeff_add]

omit [DecidableEq ι] in
lemma coeffAt_sub (c d : P.CharacterRing ℤ) (μ : Dual K H) :
    (c - d).coeffAt μ = c.coeffAt μ - d.coeffAt μ := by
  simp only [coeffAt, HahnSeries.coeff_sub]

variable [FiniteDimensional K H] (S : A.Symmetrization) (hA : A.IsGeneralizedCartan)
  (hp : A.IsSuperAdmissible p)

include S hA hp in
/-- `(1 - e^{-αᵢ}) D` is `rᵢ`-invariant: it is the character of `M̄(0) / U fᵢ v̄₀`, which is
integrable at `i` ([Kac78] §2). -/
lemma coeffAt_vermaChar_reflection (i : ι) (μ : Dual K H) :
    (vermaChar P p).coeffAt (P.reflection hA i μ) -
        (vermaChar P p).coeffAt (P.reflection hA i μ + P.root i) =
      (vermaChar P p).coeffAt μ - (vermaChar P p).coeffAt (μ + P.root i) := by
  rw [← finrank_modWeightSpace_quotient_range_syzComponent hA,
    ← finrank_modWeightSpace_quotient_range_syzComponent hA]
  have hint := GVerma.isIntegrableAt_quotient (P := P) (p := p) S hA hp 0 i 1
  rw [← range_syzComponent_eq] at hint
  have h : finrank K (modWeightSpace P p (GVerma P p 0 ⧸ LinearMap.range (syzComponent P p i))
      (P.reflection hA i μ)) =
      finrank K (modWeightSpace P p (GVerma P p 0 ⧸ LinearMap.range (syzComponent P p i)) μ) :=
    congrArg Cardinal.toNat
      (rank_modWeightSpace_reflection_of_isIntegrableAt (V := GVerma P p 0 ⧸
        LinearMap.range (syzComponent P p i)) hA hint μ)
  rw [h]

/-! ### The character identity -/

omit [FiniteDimensional K H] in
/-- The difference `Y = D R - 1` is supported in `-Q₊ \ 0`. -/
lemma exists_posCone_of_coeffAt_vermaChar_mul_denominator_sub_one_ne_zero {μ : Dual K H}
    (h : (vermaChar P p * KacMoodyAlgebra.denominator P - 1).coeffAt μ ≠ 0) :
    ∃ k ∈ posCone ι, μ = -P.rootOf k := by
  classical
  rw [coeffAt_sub, coeffAt_one] at h
  by_cases hμ : μ = 0
  · subst hμ
    rw [isNegSupported_vermaChar.coeffAt_mul_zero isNegSupported_denominator,
      coeffAt_vermaChar_zero, coeffAt_denominator_zero] at h
    simp at h
  · simp only [hμ, ite_false, sub_zero] at h
    obtain ⟨k, hk, rfl⟩ := (isNegSupported_vermaChar.mul isNegSupported_denominator) μ h
    refine ⟨k, ⟨hk, ?_⟩, rfl⟩
    rintro rfl
    simp at hμ

include S hA hp in
/-- Step one: a maximal weight `-β` of `D R - 1` satisfies `⟨-β, αᵢ^∨⟩ ≥ 0` for all `i`. -/
theorem sum_mul_le_zero_of_maximal {β : Dual K H} {k : ι → ℤ} (hβ : β = -P.rootOf k)
    (hne : (vermaChar P p * KacMoodyAlgebra.denominator P - 1).coeffAt β ≠ 0)
    (hmax : ∀ μ, toWeightOrd P μ < toWeightOrd P β →
      (vermaChar P p * KacMoodyAlgebra.denominator P - 1).coeffAt μ = 0)
    (i : ι) : ∑ j, A i j * k j ≤ 0 := by
  classical
  set D := vermaChar P p
  set R := KacMoodyAlgebra.denominator P
  set Y := D * R - 1 with hYdef
  set r := P.reflection hA i
  set E : P.CharacterRing ℤ := 1 - exp P ℤ (-P.root i)
  set W := E * (exp P ℤ P.rho * Y)
  have hrρ : r P.rho = P.rho - P.root i := by
    rw [reflection_apply, rho_coroot, one_smul]
  have hEρ : ∀ μ, (E * exp P ℤ P.rho).coeffAt (r μ) = -(E * exp P ℤ P.rho).coeffAt μ := by
    intro μ
    rw [coeffAt_one_sub_exp_mul, coeffAt_one_sub_exp_mul, coeff_exp, coeff_exp, coeff_exp,
      coeff_exp]
    have h1 : r μ = P.rho ↔ μ + P.root i = P.rho := by
      rw [← eq_sub_iff_add_eq, ← hrρ]
      constructor
      · intro h; rw [← h, reflection_reflection]
      · intro h; rw [h, reflection_reflection]
    have h2 : r μ + P.root i = P.rho ↔ μ = P.rho := by
      rw [← eq_sub_iff_add_eq, ← hrρ]
      exact r.injective.eq_iff
    simp only [h1, h2]
    split_ifs <;> norm_num
  have hED : ∀ μ, (E * D).coeffAt (r μ) = (E * D).coeffAt μ := by
    intro μ
    rw [coeffAt_one_sub_exp_mul, coeffAt_one_sub_exp_mul]
    exact coeffAt_vermaChar_reflection S hA hp i μ
  have hWeq : W = exp P ℤ P.rho * R * (E * D) - E * exp P ℤ P.rho := by
    simp only [W, hYdef]; ring
  have hW : ∀ μ, W.coeffAt (r μ) = -W.coeffAt μ := by
    intro μ
    rw [hWeq, coeffAt_sub, coeffAt_sub, coeffAt_mul_reflection_of_anti
      (KacMoodyAlgebra.coeffAt_exp_rho_mul_denominator_reflection hA i) hED, hEρ]
    ring
  have hWY : ∀ μ, W.coeffAt μ = Y.coeffAt (μ - P.rho) - Y.coeffAt (μ + P.root i - P.rho) := by
    intro μ
    rw [coeffAt_one_sub_exp_mul, coeff_exp_mul, coeff_exp_mul]
  have hsingle : ∀ n : ℤ, 0 < n → Pi.single i n ∈ posCone ι := fun n hn ↦
    ⟨Pi.single_nonneg.2 hn.le, fun h ↦ hn.ne' (by simpa using congrFun h i)⟩
  have hroot : ∀ n : ℤ, P.rootOf (Pi.single i n) = (n : K) • P.root i := by
    intro n
    simp [rootOf_apply, Pi.single_apply]
  set s := ∑ j, A i j * k j
  have hβα : β (P.coroot i) = -(s : K) := by
    rw [hβ, LinearMap.neg_apply, rootOf_apply_coroot]
    simp [s, Matrix.mulVec, dotProduct]
  -- the coefficient of `W` at `β + ρ` is `Y_β`
  have hWmm : W.coeffAt (β + P.rho) = Y.coeffAt β := by
    have e : β + P.rho + P.root i - P.rho = β + P.rootOf (Pi.single i 1) := by
      rw [hroot, Int.cast_one, one_smul]; abel
    have h0 := hmax _ (toWeightOrd_lt_of_eq_add (hsingle 1 one_pos) rfl)
    rw [hWY, e, h0, add_sub_cancel_right, sub_zero]
  by_contra hs
  push Not at hs
  set n := s - 1
  have hrmm : r (β + P.rho) = β + P.rootOf (Pi.single i n) + P.rho := by
    rw [reflection_apply, hroot]
    simp only [LinearMap.add_apply, hβα, rho_coroot, n]
    push_cast
    module
  have h1 : W.coeffAt (r (β + P.rho)) = Y.coeffAt (β + P.rootOf (Pi.single i n)) := by
    have e : β + P.rootOf (Pi.single i n) + P.rho + P.root i - P.rho =
        β + P.rootOf (Pi.single i n) + P.rootOf (Pi.single i 1) := by
      rw [hroot 1, Int.cast_one, one_smul]; abel
    have e' : β + P.rootOf (Pi.single i (n + 1)) =
        β + P.rootOf (Pi.single i n) + P.rootOf (Pi.single i 1) := by
      rw [hroot, hroot, hroot]; push_cast; module
    have h0 := hmax _ (toWeightOrd_lt_of_eq_add (hsingle (n + 1) (by omega)) rfl)
    rw [e'] at h0
    rw [hWY, hrmm, e, h0, add_sub_cancel_right, sub_zero]
  rw [hW, hWmm] at h1
  rcases eq_or_lt_of_le (show 0 ≤ n by omega) with hn | hn
  · rw [← hn, Pi.single_zero, map_zero, add_zero] at h1
    exact hne (by omega)
  · rw [hmax _ (toWeightOrd_lt_of_eq_add (hsingle n hn) rfl)] at h1
    exact hne (by omega)

include S hA in
/-- Step two: a maximal weight `β` of `D R - 1` satisfies `(β + 2ρ | β) = 0`. Expand the character
of the one-dimensional module `M̄(0) / Σᵢ U fᵢ v̄₀` above `β` in characters of Verma modules
`M̄(κ)` with `(κ + 2ρ | κ) = 0`; multiplying by `R` shows that `β` is such a `κ` or a weight of
`R`, and in the second case `β + ρ ∈ W ρ` by the denominator identity of `𝔤(A)`. -/
theorem dualBilinForm_eq_zero_of_maximal {β : Dual K H} {k : ι → ℤ} (hk : 0 ≤ k)
    (hβ : β = -P.rootOf k)
    (hne : (vermaChar P p * KacMoodyAlgebra.denominator P - 1).coeffAt β ≠ 0)
    (hmax : ∀ μ, toWeightOrd P μ < toWeightOrd P β →
      (vermaChar P p * KacMoodyAlgebra.denominator P - 1).coeffAt μ = 0) :
    P.dualBilinForm S (β + 2 • P.rho) β = 0 := by
  classical
  set D := vermaChar P p
  set R := KacMoodyAlgebra.denominator P
  set Y := D * R - 1 with hYdef
  set N := LinearMap.range (syzMap P p)
  have hT : IsCasimirModule P p S (GVerma P p 0 ⧸ N) {0} 0 := by
    have h := (IsCasimirModule.gVerma (S := S) (Λs := {0}) (μ₀ := 0) hA
      ⟨0, Finset.mem_singleton_self _, le_rfl⟩).quotient N
    rwa [map_zero] at h
  obtain ⟨a, ha, hexp⟩ := hT.exists_expansion hA β
  have haneg : ∀ κ, a κ ≠ 0 → ∃ k : ι → ℤ, 0 ≤ k ∧ κ = 0 - P.rootOf k := fun κ hκ ↦ by
    obtain ⟨Λ, hΛ, hle⟩ := (ha κ (Finsupp.mem_support_iff.2 hκ)).2
    rw [Finset.mem_singleton] at hΛ
    subst hΛ
    exact (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).1 hle
  set A' : P.CharacterRing ℤ := ofFun P (fun κ ↦ a κ) ⟨{0}, fun κ hκ ↦
    ⟨0, Finset.mem_singleton_self _, haneg κ hκ⟩⟩
  have hA'neg : IsNegSupported P A' := fun κ hκ ↦ by
    obtain ⟨k, hk, h⟩ := haneg κ hκ
    exact ⟨k, hk, by rw [h, zero_sub]⟩
  set F := A' * D
  have hF : ∀ μ, toWeightOrd P μ ≤ toWeightOrd P β →
      F.coeffAt μ = (1 : P.CharacterRing ℤ).coeffAt μ := by
    intro μ hμ
    have h := hexp μ hμ
    rw [finrank_modWeightSpace_quotient_range_syzMap] at h
    have hsum : F.coeffAt μ = a.sum fun κ m ↦ m * (GVerma.vermaDim P p (κ - μ) : ℤ) := by
      rw [CharacterRing.coeff_mul, finsum_eq_sum_of_support_subset (s := a.support)]
      · refine Finset.sum_congr rfl fun κ _ ↦ ?_
        rw [coeffAt_vermaChar, neg_sub]
        rfl
      · intro κ hκ
        rw [Function.mem_support] at hκ
        exact Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hκ)
    rw [coeffAt_one, hsum, ← h]
    split_ifs <;> simp
  have ha0 : a 0 = 1 := by
    have h := hF 0 (toWeightOrd_le_of_eq_add hk (by rw [hβ, neg_add_cancel]))
    rw [hA'neg.coeffAt_mul_zero isNegSupported_vermaChar, coeffAt_vermaChar_zero, mul_one,
      coeffAt_one] at h
    simp only [↓reduceIte] at h
    exact h
  have hR : R.coeffAt β = a β + Y.coeffAt β := by
    have h1 : R.coeffAt β = (F * R).coeffAt β := by
      rw [coeffAt_mul_congr isNegSupported_denominator hF, one_mul]
    have h2 : F * R = A' + Y * A' := by simp only [F, Y]; ring
    have h3 : (Y * A').coeffAt β = Y.coeffAt β := by
      rw [CharacterRing.coeff_mul, finsum_eq_single _ β fun ν hν ↦ ?_, sub_self]
      · change Y.coeffAt β * a 0 = _
        rw [ha0, mul_one]
      by_contra h
      obtain ⟨k', hk', hk'eq⟩ := hA'neg _ (right_ne_zero_of_mul h)
      have hν' : ν = β + P.rootOf k' := by rw [← neg_neg (P.rootOf k'), ← hk'eq]; abel
      have hk'0 : k' ≠ 0 := by rintro rfl; rw [map_zero, add_zero] at hν'; exact hν hν'
      exact left_ne_zero_of_mul h (hmax ν (toWeightOrd_lt_of_eq_add ⟨hk', hk'0⟩ hν'))
    rw [h1, h2, coeffAt_add, h3]
    rfl
  by_cases haβ : a β = 0
  · rw [haβ, zero_add] at hR
    have hS := Matrix.isSymmetrizable_iff_nonempty_symmetrization.mpr ⟨S⟩
    have hR' : (exp P ℤ P.rho * R).coeffAt (β + P.rho) ≠ 0 := by
      rw [coeff_exp_mul, add_sub_cancel_right, hR]; exact hne
    rw [KacMoodyAlgebra.IrreducibleModule.exp_rho_mul_denominator hA hS] at hR'
    change (∑ᶠ w : P.weylGroup hA, if (w : Dual K H ≃ₗ[K] Dual K H) P.rho = β + P.rho then
      ((-1) ^ (P.coxeterSystem hA).length w : ℤ) else 0) ≠ 0 at hR'
    obtain ⟨w, hw⟩ : ∃ w : P.weylGroup hA,
        (w : Dual K H ≃ₗ[K] Dual K H) P.rho = β + P.rho := by
      by_contra h
      push Not at h
      exact hR' (finsum_eq_zero_of_forall_eq_zero fun w ↦ by simp [h w])
    have hγ : P.dualBilinForm S (β + P.rho) (β + P.rho) = P.dualBilinForm S P.rho P.rho := by
      rw [← hw, P.dualBilinForm_weylGroup hA S w.2]
    have hs : P.dualBilinForm S β P.rho = P.dualBilinForm S P.rho β :=
      (P.isSymm_dualBilinForm S).eq β P.rho
    simp only [two_smul, map_add, LinearMap.add_apply] at hγ ⊢
    linear_combination hγ - hs
  · have h := (ha β (Finsupp.mem_support_iff.2 haβ)).1
    exact h

include S hA hp in
/-- **The character of the Verma module of `G(A, τ)`** ([Kac78] §2): `ch M̄(0) · R = 1`, where
`R` is the denominator of the Kac–Moody algebra `𝔤(A)`. -/
theorem vermaChar_mul_denominator :
    vermaChar P p * KacMoodyAlgebra.denominator P = 1 := by
  rw [← sub_eq_zero]
  set Y := vermaChar P p * KacMoodyAlgebra.denominator P - 1 with hY
  by_contra hY0
  obtain ⟨m, hm⟩ := Y.isPWO_support.exists_minimal (HahnSeries.support_nonempty_iff.2 hY0)
  set β := ofWeightOrd P m
  have hmβ : toWeightOrd P β = m := toWeightOrd_ofWeightOrd P m
  have hne : Y.coeffAt β ≠ 0 := by
    change Y.coeff (toWeightOrd P β) ≠ 0
    rw [hmβ]; exact hm.prop
  have hmax : ∀ μ, toWeightOrd P μ < toWeightOrd P β → Y.coeffAt μ = 0 := by
    intro μ hμ
    by_contra h
    exact hm.not_lt (show Y.coeff (toWeightOrd P μ) ≠ 0 from h) (hmβ ▸ hμ)
  obtain ⟨k, hk, hβk⟩ := exists_posCone_of_coeffAt_vermaChar_mul_denominator_sub_one_ne_zero hne
  have h0 := dualBilinForm_eq_zero_of_maximal S hA hk.1 hβk hne hmax
  rw [hβk] at h0
  exact P.dualBilinForm_neg_rootOf_add_two_rho_ne_zero S hk
    (sum_mul_le_zero_of_maximal S hA hp hβk hne hmax) h0

include S hA hp in
/-- `ch M̄(0) = ∑_β K(β) e^{-β}`, the character of the Verma module of `𝔤(A)`. -/
theorem vermaChar_eq_kostantSeries : vermaChar P p = KacMoodyAlgebra.kostantSeries P := by
  rw [← mul_one (vermaChar P p), ← KacMoodyAlgebra.denominator_mul_kostantSeries, ← mul_assoc,
    vermaChar_mul_denominator S hA hp, one_mul]

include S hA hp in
/-- **Weight multiplicities of Verma modules of `G(A, τ)`** ([Kac78] §2):
`dim M̄(Λ)_{Λ - β} = K(β)`, Kostant's partition function of the Kac–Moody algebra `𝔤(A)` with the
same Cartan matrix. -/
theorem GVerma.finrank_modWeightSpace_sub_eq_kostantPartition (Λ β : Dual K H) :
    finrank K (modWeightSpace P p (GVerma P p Λ) (Λ - β)) =
      KacMoodyAlgebra.kostantPartition P β := by
  have h := congrArg (fun c : P.CharacterRing ℤ ↦ c.coeffAt (-β))
    (vermaChar_eq_kostantSeries S hA hp)
  simp only [coeffAt_vermaChar, neg_neg, KacMoodyAlgebra.coeffAt_kostantSeries] at h
  rw [GVerma.finrank_modWeightSpace, sub_sub_cancel]
  exact_mod_cast h

end Matrix.Realization.SuperEnveloping
