/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.GlobalInduction
import LieLean.Algebra.QuantumGroup.LusztigF.IntegralPairing
import LieLean.Algebra.QuantumGroup.PBW.Crystal.Signed

/-!
# The signed global basis of `f`

Let `G(b)`, `b ∈ B(∞)_ν`, be Kashiwara's global basis of `U⁻_ν ≅ f_ν` (`negGlobal`, from
`(G.1)`, [Kas91] (7.5.4)). We prove that `±G(B(∞)_ν)` is the set of the `x ∈ U⁻_ν` with

* `x ∈ 𝒜f` (here `U⁻_ℤ`, `negIntegral`),
* `x̄ = x`,
* `(x, x) ∈ 1 + v⁻¹ℤ[[v⁻¹]]`, in the sense of the expansion at `v = ∞` (`intSeriesInf`).

This is `mem_signedGlobal_iff`. In [Lus] 14.2.3 Lusztig defines his signed basis `𝐁` of `f` as
the set of the `x ∈ 𝒜f` with `x̄ = x` and `(x, x) ∈ 1 + v⁻¹ℤ[[v⁻¹]]`. So the homogeneous elements
of `𝐁` of weight `ν` are exactly the `±G(b)`, `b ∈ B(∞)_ν`. `mem_signedGlobal_iff` is the one
place where Kashiwara's `G(b)` and Lusztig's `𝐁` are identified; later results that only use the
properties of `G(b)` do not depend on how that identification is proved.

## Main results

* `mem_localRing_iff`, `exists_algebraMap_eq_iff`: an element of `ℚ(v)` lies in the local ring
  `A` at `v = ∞` iff its expansion at `v = ∞` is a power series in `v⁻¹`.
* `mem_intSeriesInf_of_mem_intLaurentInf`: `A ∩ ℤ((v⁻¹)) ⊆ ℤ[[v⁻¹]]`.
* `negGlobal`: Kashiwara's `G(b)`, `b ∈ B(∞)_ν`.
* `formU_negGlobal_self`: `(G(b), G(b)) ∈ 1 + v⁻¹ℤ[[v⁻¹]]`.
* `mem_signedGlobal_iff`: the characterization of `±G(b)` above.

## Proof

The proof is our own and differs from Lusztig's, which uses the geometric construction of `𝐁`.
* For `x = ±G(b)`: `G(b) ≡ b̃ mod v⁻¹L(∞)`, so `(G(b), G(b)) ∈ 1 + v⁻¹A` by Kashiwara's
  polarization ([Kas91] Prop. 5.1.2). Also `(G(b), G(b)) ∈ ℤ((v⁻¹))` by the integrality
  [Lus] 14.2.6 (b) (`quotientForm_mem_intLaurentInf`). Together these give `1 + v⁻¹ℤ[[v⁻¹]]`.
* Conversely, `(x, x) ∈ A` gives `x ∈ L(∞)` ([Kas91] Prop. 5.1.3).
  - Since `x̄ = x`, also `x ∈ L(∞)⁻`, so `x` lies in the balanced set
    `E(ν) = U⁻_ℤ ∩ L(∞) ∩ L(∞)⁻`.
  - The norm condition makes the residue of `x` a signed crystal element `±b̃`
    (`PBWSignedCrystal.exists_signed_crystal_residue`).
  - Then `x = ±G(b)`, because `E(ν) → L(∞)/v⁻¹L(∞)` is injective (`(G.1)`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.2.3, 14.2.6.
* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, Prop. 5.1.2, 5.1.3, §7.
-/

open scoped RatFunc Pointwise

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X
local notation "hv'" => pow_ne_one_of_transcendental' transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-! ### The local ring at `v = ∞` and expansions -/

/-- `ℚ[v]_(v)` is the set of rational functions whose Laurent expansion at `v = 0` is a power
series. -/
lemma mem_localRing_iff (g : 𝕂) : g ∈ Sl2.RankOne.LocalRing ↔
    ∃ F : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ F = algebraMap 𝕂 (LaurentSeries ℚ) g := by
  change g ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime 𝕂
    (Polynomial.idealX ℚ) ↔ _
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff, RatFunc.valuation_eq_LaurentSeries_valuation,
    ← LaurentSeries.valuation_def, LaurentSeries.val_le_one_iff_eq_coe]

/-- The local ring `A` at `v = ∞` is the set of rational functions whose expansion at `v = ∞` is a
power series in `v⁻¹`. -/
lemma exists_algebraMap_eq_iff (f : 𝕂) : (∃ a : A, algebraMap A 𝕂 a = f) ↔
    ∃ F : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ F = expandInf f := by
  rw [expandInf_apply, ← mem_localRing_iff]
  constructor
  · rintro ⟨a, rfl⟩
    change RatFunc.bar (RatFunc.bar (algebraMap Sl2.RankOne.LocalRing 𝕂 a)) ∈ _
    rw [RatFunc.bar_bar]
    exact a.2
  · intro h
    refine ⟨(⟨RatFunc.bar f, h⟩ : Sl2.RankOne.LocalRing), ?_⟩
    change RatFunc.bar (RatFunc.bar f) = f
    exact RatFunc.bar_bar f

/-- `ℤ[[v⁻¹]] ∩ ℚ(v) ⊆ A`. -/
lemma exists_algebraMap_eq_of_mem_intSeriesInf {f : 𝕂} (hf : f ∈ intSeriesInf) :
    ∃ a : A, algebraMap A 𝕂 a = f := by
  obtain ⟨G, hG⟩ := mem_intSeriesInf.1 hf
  exact (exists_algebraMap_eq_iff f).2 ⟨_, hG⟩

/-- `A ∩ ℤ((v⁻¹)) ⊆ ℤ[[v⁻¹]]`: an integer Laurent series in `v⁻¹` which is a power series has
integer coefficients. -/
lemma mem_intSeriesInf_of_mem_intLaurentInf {f : 𝕂} (hA : ∃ a : A, algebraMap A 𝕂 a = f)
    (hf : f ∈ intLaurentInf) : f ∈ intSeriesInf := by
  obtain ⟨F, hF⟩ := (exists_algebraMap_eq_iff f).1 hA
  obtain ⟨n, hn⟩ := hf
  obtain ⟨G, hG⟩ := mem_intSeriesInf.1 hn
  have hX : expandInf 𝕧⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X := by
    rw [expandInf_inv_X]; simp [intSeriesHom]
  have hmap : PowerSeries.map (Int.castRingHom ℚ) G = PowerSeries.X ^ n * F := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_mul, map_pow, ← hX, hF, ← map_pow, ← map_mul, ← hG]
    rfl
  refine mem_intSeriesInf.2 ⟨PowerSeries.mk fun k ↦ PowerSeries.coeff (k + n) G, ?_⟩
  rw [← hF]
  change HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) _) = _
  congr 1
  ext k
  have := congrArg (PowerSeries.coeff (k + n)) hmap
  rw [PowerSeries.coeff_map, PowerSeries.coeff_X_pow_mul'] at this
  simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, Nat.add_sub_cancel] at this
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, ← this]

/-- If `f ∈ ℤ((v⁻¹)) ∩ ℚ(v)` and `f ∈ 1 + v⁻¹A`, then `f ∈ 1 + v⁻¹ℤ[[v⁻¹]]`. -/
lemma exists_eq_one_add_of_mem_intLaurentInf {f : 𝕂} (a : A)
    (hfa : f = 1 + algebraMap A 𝕂 (ϖ * a)) (hf : f ∈ intLaurentInf) :
    ∃ g ∈ intSeriesInf, f = 1 + 𝕧⁻¹ * g := by
  have hfa' : f = 1 + 𝕧⁻¹ * algebraMap A 𝕂 a := by
    rw [hfa, map_mul, InfinityLocalRing.algebraMap_uniformizer]
  refine ⟨algebraMap A 𝕂 a, mem_intSeriesInf_of_mem_intLaurentInf ⟨a, rfl⟩ ?_, hfa'⟩
  have he : algebraMap A 𝕂 a = 𝕧 ^ (1 : ℤ) * (f - 1) := by
    rw [hfa', zpow_one, add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ RatFunc.X_ne_zero,
      one_mul]
  rw [he]
  exact mul_mem (zpow_X_mem_intLaurentInf 1) (sub_mem hf (one_mem _))

/-! ### Kashiwara's global basis `G(b)` -/

variable {I : Type u} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- Kashiwara's global basis element `G(b)` of `U⁻_ν`, `b ∈ B(∞)_ν` ([Kas91] (7.5.4)): the unique
element of `E(ν) = U⁻_ℤ ∩ U⁻_ν ∩ L(∞) ∩ L(∞)⁻` congruent to `b` modulo `v⁻¹L(∞)`. -/
def negGlobal (ν : I →₀ ℕ) (b : negCrystal D ν) : Um D 𝕧 :=
  letI := Fintype.ofFinite I
  negGlobalLift D.isXRegular_extendedRootDatum D.exists_fundamental_extendedRootDatum
    (globalBelow D.isXRegular_extendedRootDatum D.exists_fundamental_extendedRootDatum ν) b

lemma negGlobal_mem (ν : I →₀ ℕ) (b : negCrystal D ν) :
    negGlobal D ν b ∈ negBalanced D ν := by
  let := Fintype.ofFinite I
  exact (negGlobalLift_spec _ _ _ b).1

lemma negGlobal_sub_mem (ν : I →₀ ℕ) (b : negCrystal D ν) :
    negGlobal D ν b - fWi (D := D) hvt (Quotient.out b).1 ∈ ϖ • latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  exact (negGlobalLift_spec _ _ _ b).2.1

lemma negBar_negGlobal (ν : I →₀ ℕ) (b : negCrystal D ν) :
    negBar D (negGlobal D ν b) = negGlobal D ν b := by
  let := Fintype.ofFinite I
  exact (negGlobalLift_spec _ _ _ b).2.2.1

/-- The form on `U⁻` is the form on `f` transported along `U⁻ ≅ f`. -/
lemma formU_eq_quotientForm (x y : Um D 𝕧) :
    formU hv' x y = quotientForm D (negativeQuotientEquiv D x) (negativeQuotientEquiv D y) := by
  simp [quotientForm]

/-- `(G(b), G(b)) ∈ 1 + v⁻¹A`, from `G(b) ≡ b̃ mod v⁻¹L(∞)` ([Kas91] Prop. 5.1.2). -/
lemma exists_formU_negGlobal_self (ν : I →₀ ℕ) (b : negCrystal D ν) :
    ∃ a : A, formU hv' (negGlobal D ν b) (negGlobal D ν b) = 1 + algebraMap A 𝕂 (ϖ * a) := by
  classical
  set w := (Quotient.out b).1
  set d := negGlobal D ν b - fWi (D := D) hvt w with hd
  have hdP : d ∈ ϖ • latInf (D := D) hvt A := negGlobal_sub_mem D ν b
  have hdL : d ∈ latInf (D := D) hvt A := Submodule.smul_le_self_of_tower ϖ _ hdP
  have hwL : fWi (D := D) hvt w ∈ latInf (D := D) hvt A :=
    NegativePart.fWord_mem_latticeInf _ _ w
  obtain ⟨a₀, ha₀⟩ := PBWSignedCrystal.word_pairing (D := D) w w
  obtain ⟨a₁, ha₁⟩ := PBWSignedCrystal.form_mem_uniformizer (D := D) hwL hdP
  obtain ⟨a₂, ha₂⟩ := PBWSignedCrystal.form_mem_uniformizer (D := D) hdL hdP
  have hG : negGlobal D ν b = fWi (D := D) hvt w + d := by rw [hd, add_sub_cancel]
  refine ⟨a₀ + a₁ + a₁ + a₂, ?_⟩
  rw [hG, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha₀,
    formU_comm _ d (fWi hvt w), ha₁, ha₂]
  simp only [sub_self, zero_mem, ↓reduceIte, mul_add, map_add]
  ring

/-- `(G(b), G(b)) ∈ 1 + v⁻¹ℤ[[v⁻¹]]`: our own proof, from [Kas91] Prop. 5.1.2 and the integrality
[Lus] 14.2.6 (b). -/
theorem formU_negGlobal_self (ν : I →₀ ℕ) (b : negCrystal D ν) :
    ∃ g ∈ intSeriesInf, formU hv' (negGlobal D ν b) (negGlobal D ν b) = 1 + 𝕧⁻¹ * g := by
  obtain ⟨a, ha⟩ := exists_formU_negGlobal_self D ν b
  have hZ := (negGlobal_mem D ν b).1
  refine exists_eq_one_add_of_mem_intLaurentInf a ha ?_
  rw [formU_eq_quotientForm]
  exact quotientForm_mem_intLaurentInf D hZ hZ

/-- **The signed global basis** ([Lus] 14.2.3 for Kashiwara's `G(b)`): an element `x ∈ U⁻_ν`
is `±G(b)` for some `b ∈ B(∞)_ν` if and only if `x ∈ U⁻_ℤ`, `x̄ = x` and
`(x, x) ∈ 1 + v⁻¹ℤ[[v⁻¹]]`.

Lusztig defines his signed basis `𝐁` of `f` by these three conditions ([Lus] 14.2.3), so this
identifies the elements of `𝐁` of weight `ν` with the `±G(b)`. Our proof is our own (see the
module docstring); Lusztig's uses the geometric construction. -/
theorem mem_signedGlobal_iff {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) :
    (x ∈ negIntegral D ∧ negBar D x = x ∧
        ∃ g ∈ intSeriesInf, formU hv' x x = 1 + 𝕧⁻¹ * g) ↔
      ∃ b : negCrystal D ν, x = negGlobal D ν b ∨ x = -negGlobal D ν b := by
  classical
  let := Fintype.ofFinite I
  constructor
  · rintro ⟨hxZ, hbar, g, hg, hxx⟩
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_mem_intSeriesInf hg
    have hxx' : formU hv' x x = algebraMap A 𝕂 (1 + ϖ * a) := by
      rw [hxx, map_add, map_one, map_mul, InfinityLocalRing.algebraMap_uniformizer]
    have hxL : x ∈ latInf (D := D) hvt A :=
      (mem_latInf_iff_formU_mem (hR := D.isXRegular_extendedRootDatum)
        InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
        InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
        D.exists_fundamental_extendedRootDatum hx).2 ⟨_, hxx'⟩
    obtain ⟨w, e, he, hxw⟩ :=
      PBWSignedCrystal.exists_signed_crystal_residue D hxZ hxL ⟨a, hxx'⟩
    have hee : (e : 𝕂) * e = 1 := by rcases he with rfl | rfl <;> norm_num
    -- the word `w` has weight `ν`
    have hwν : wordWeight w = ν := by
      by_contra hne
      have hne' : LusztigF.toZ ν ≠ LusztigF.toZ (wordWeight w) :=
        fun h ↦ hne (LusztigF.toZ_injective h).symm
      have hp := proj_mem_smul_latInf (D := D) (LusztigF.toZ (wordWeight w)) hxw
      rw [map_sub, map_smul, proj_of_mem_Uw hx, proj_of_mem_Uw (fWi_mem_Uw w)] at hp
      simp only [hne', ↓reduceIte, zero_sub] at hp
      have hp' := zsmul_mem (neg_mem hp) e
      rw [neg_neg, ← Int.cast_smul_eq_zsmul 𝕂, smul_smul, hee, one_smul] at hp'
      exact PBWSignedCrystal.word_not_mem_uniformizer (D := D) w hp'
    set b : negCrystal D ν := Quotient.mk _ ⟨w, hwν⟩
    have hout : fWi (D := D) hvt (Quotient.out b).1 - fWi hvt w ∈ ϖ • latInf (D := D) hvt A :=
      Quotient.exact (Quotient.out_eq b)
    have hsub : x - (e : 𝕂) • negGlobal D ν b ∈ ϖ • latInf (D := D) hvt A := by
      have e1 : x - (e : 𝕂) • negGlobal D ν b = (x - (e : 𝕂) • fWi (D := D) hvt w) -
          (e : 𝕂) • ((negGlobal D ν b - fWi hvt (Quotient.out b).1) +
            (fWi hvt (Quotient.out b).1 - fWi hvt w)) := by
        rw [sub_add_sub_cancel, smul_sub]; abel
      rw [e1]
      refine sub_mem hxw ?_
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (add_mem (negGlobal_sub_mem D ν b) hout) e
    have hxE : x ∈ negBalanced D ν :=
      ⟨hxZ, hx, hxL, (mem_latInfBar_iff D x).2 (by rw [hbar]; exact hxL)⟩
    have hGE : (e : 𝕂) • negGlobal D ν b ∈ negBalanced D ν := by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := negGlobal_mem D ν b
      have hs : (e : 𝕂) • negGlobal D ν b = e • negGlobal D ν b := Int.cast_smul_eq_zsmul 𝕂 _ _
      rw [hs]
      exact ⟨zsmul_mem h₁ e, zsmul_mem h₂ e, zsmul_mem h₃ e, zsmul_mem h₄ e⟩
    have hxe := eq_of_mem_negBalanced (negGlobalAt D ν) hxE hGE hsub
    refine ⟨b, ?_⟩
    rcases he with rfl | rfl
    · left; simpa using hxe
    · right; simpa using hxe
  · rintro ⟨b, hb⟩
    obtain ⟨g, hg, hgg⟩ := formU_negGlobal_self D ν b
    have hZ := (negGlobal_mem D ν b).1
    rcases hb with rfl | rfl
    · exact ⟨hZ, negBar_negGlobal D ν b, g, hg, hgg⟩
    · refine ⟨neg_mem hZ, by rw [map_neg, negBar_negGlobal], g, hg, ?_⟩
      simp only [map_neg, LinearMap.neg_apply, neg_neg, hgg]

end LieLean.QuantumGroup
