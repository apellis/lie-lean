/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.NegativeFiltrationGlobal

/-!
# Independence of the global lifts of the choice of string: [Kas91] Lemma 7.5.1

By Cor. 7.4.2 (`negFiltGlobalAt`), for every `i ∈ I` each `b ∈ f̃ᵢB(∞)_ν` has a unique lift
`Gᵢ(b) ∈ (fᵢU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻` with residue `b` (unique by `negFilt_eq_zero_of_mem`).
[Kas91] Lemma 7.5.1 states that `Gᵢ(b) = Gⱼ(b)` for `b ∈ f̃ᵢB(∞) ∩ f̃ⱼB(∞)`. We prove it in the
form `eq_of_mem_negFilt`: two elements of `(fᵢU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻` and
`(fⱼU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻` that are both congruent to `f̃_w 1` modulo `v⁻¹L(∞)`, for a nonempty
word `w`, are equal. The hypothesis is the induction hypothesis `GlobalBelow` of
Prop. 7.4.1 at the weights below `ν`.

The proof is Kashiwara's. Write `f̃_w 1 = f̃_{w'} f̃_k 1` and choose a dominant `λ` with
`⟨hₖ, λ⟩ = 0` and `⟨hⱼ, λ⟩ ≥ |ν|` for `j ≠ k`. Then `f̃ₖu_λ = 0`
(`fW_append_singleton_eq_zero`), so `Gᵢ(b)u_λ ∈ (fᵢV(λ))^ℤ ∩ v⁻¹L(λ) ∩ L(λ)⁻`, which vanishes by
Prop. 7.4.1. By (7.5.3) (`exists_starU_eq_f_of_evq_eq_zero`: the kernel of `u ↦ u u_λ` on `U⁻_ν`
is `U⁻ fₖ`), `Gᵢ(b) ∈ U⁻fₖ`, and likewise `Gⱼ(b)`. Applying `*` ([Kas91] Prop. 5.2.4,
`starU_mem_latInf`), `(Gᵢ(b) - Gⱼ(b))*` lies in `fₖU⁻ ∩ U⁻_ℤ ∩ v⁻¹L(∞) ∩ L(∞)⁻`. That
intersection lies in `(fₖU⁻)^ℤ_ν ∩ v⁻¹L(∞) ∩ L(∞)⁻` (`mem_negFilt_of_eq_f`, from (6.1.2)), which
is zero by Cor. 7.4.2.

Kashiwara uses (7.5.3) without proof. Here it follows from the description of the kernel of
`y ↦ y⁻v_λ` (`ker_ev_eq`) by taking weight components. The step `U⁻_ℤ ∩ fₖU⁻ ⊆ (fₖU⁻)^ℤ` is also
implicit in the source; we deduce it from (6.1.2) (`df_sub_df_comp_mem_negFilt`) and the vanishing
of the `0`-th string component on `fₖU⁻` (`comp_zero_f`).

## Main results

* `exists_starU_eq_f_of_evq_eq_zero`: [Kas91] (7.5.3).
* `eq_of_mem_negFilt`: **[Kas91] Lemma 7.5.1**.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.5.
-/

open Pointwise

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} {Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I}

/-! ### The anti-automorphism `*` on `U⁻_ℤ` and `L(∞)⁻` -/

section Star

omit [Finite I] [DecidableEq I] in
/-- Bar commutes with word reversal on `'f`. -/
lemma bar_rev (x : LusztigF 𝕂 I) : LusztigF.bar (rev 𝕂 I x) = rev 𝕂 I (LusztigF.bar x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [rev_algebraMap, LusztigF.bar_algebraMap, rev_algebraMap]
  | grade1 i =>
    change LusztigF.bar (rev 𝕂 I (θ 𝕂 i)) = rev 𝕂 I (LusztigF.bar (θ 𝕂 i))
    rw [rev_θ, LusztigF.bar_θ, rev_θ]
  | mul a b ha hb => rw [rev_mul, map_mul, map_mul, ha, hb, rev_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

omit [Finite I] [DecidableEq I] in
/-- `*` commutes with bar on `U⁻`. -/
lemma negBar_starU (x : Um D 𝕧) : negBar D (starU D 𝕧 x) = starU D 𝕧 (negBar D x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [starU_mk, negBar_mk, negBar_mk, starU_mk, bar_rev]

omit [Finite I] [DecidableEq I] in
lemma rev_θ_pow (i : I) (n : ℕ) : rev 𝕂 I (θ 𝕂 i ^ n) = θ 𝕂 i ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, rev_mul, ih, rev_θ, ← pow_succ', pow_succ]

variable (D) in
/-- `*` transported to the radical quotient. -/
def quotientStar (q : Quotient D 𝕧) : Quotient D 𝕧 :=
  negativeQuotientEquiv D (starU D 𝕧 ((negativeQuotientEquiv D).symm q))

lemma quotientStar_toQuotient (a : LusztigF 𝕂 I) :
    quotientStar D (toQuotient D 𝕧 a) = toQuotient D 𝕧 (rev 𝕂 I a) := by
  rw [quotientStar, negativeQuotientEquiv_symm_toQuotient, starU_mk]
  rfl

lemma quotientStar_mul (q q' : Quotient D 𝕧) :
    quotientStar D (q * q') = quotientStar D q' * quotientStar D q := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 q
  obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 q'
  rw [← map_mul, quotientStar_toQuotient, quotientStar_toQuotient, quotientStar_toQuotient,
    rev_mul, map_mul]

lemma quotientStar_mem {q : Quotient D 𝕧} (hq : q ∈ quotientIntegralForm D) :
    quotientStar D q ∈ quotientIntegralForm D := by
  induction hq using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    have e : quotientIntegralGenerator D i n =
        toQuotient D 𝕧 (QuantumGroup.qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i)) := by
      rw [quotientIntegralGenerator, QuantumGroup.qDivPow, QuantumGroup.qDivPow, map_smul,
        map_pow]
    have hr : rev 𝕂 I (QuantumGroup.qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i)) =
        QuantumGroup.qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i) := by
      rw [QuantumGroup.qDivPow, map_smul, rev_θ_pow]
    rw [e, quotientStar_toQuotient, hr, ← e]
    exact quotientIntegralGenerator_mem D i n
  | algebraMap c =>
    have e : (algebraMap (LaurentPolynomial ℤ) (Quotient D 𝕧) c) =
        toQuotient D 𝕧 (algebraMap 𝕂 (LusztigF 𝕂 I) (integralLaurentEval c)) := by
      rw [AlgHom.commutes]; rfl
    rw [e, quotientStar_toQuotient, rev_algebraMap, ← e]
    exact Subalgebra.algebraMap_mem _ c
  | add x y _ _ hx hy =>
    rw [quotientStar, map_add, map_add, map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy => rw [quotientStar_mul]; exact mul_mem hy hx

/-- `U⁻_ℤ* = U⁻_ℤ`. -/
lemma starU_mem_negIntegral {x : Um D 𝕧} (hx : x ∈ negIntegral D) :
    starU D 𝕧 x ∈ negIntegral D := by
  have := quotientStar_mem (D := D) hx
  rwa [quotientStar, LinearEquiv.symm_apply_apply] at this

/-- `(L(∞)⁻)* = L(∞)⁻`. -/
lemma starU_mem_latInfBar {x : Um D 𝕧} (hx : x ∈ latInfBar D) : starU D 𝕧 x ∈ latInfBar D := by
  let := Fintype.ofFinite I
  rw [mem_latInfBar_iff, negBar_starU]
  exact starU_mem_latInf (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hx

/-- `(v⁻¹L(∞))* = v⁻¹L(∞)`. -/
lemma starU_mem_smul_latInf' {x : Um D 𝕧} (hx : x ∈ ϖ • latInf (D := D) hvt A) :
    starU D 𝕧 x ∈ ϖ • latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  exact starU_mem_smul_latInf (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hx

end Star

/-! ### `U⁻_ℤ ∩ fₖU⁻ ⊆ (fₖU⁻)^ℤ` -/

section Filtration

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

omit [Finite I] in
/-- The `0`-th `i`-string component vanishes on `fᵢU⁻`. -/
lemma comp_zero_f (i : I) (z : Um D 𝕧) : comp hvt i 0 (NegativePart.f D 𝕧 i z) = 0 := by
  have hq0 := NegativePart.pow_d_ne_zero (D := D) (NeZero.ne 𝕧) i
  have hq := NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i
  have key : comp (D := D) hvt i 0 ∘ₗ NegativePart.f D 𝕧 i = 0 :=
    BosonModule.ext_df (V := bosv i) hq0 hq fun n x hx ↦ by
      have hne := BosonModule.qInt_ne_zero' hq0 hq (Nat.succ_pos n)
      have e : NegativePart.f D 𝕧 i ((bosv i).df n x) =
          QuantumGroup.qInt (𝕧 ^ D.d i)⁻¹ (n + 1) • (bosv i).df (n + 1) x := by
        rw [df_succ, smul_smul, mul_inv_cancel₀ hne, one_smul]
      rw [LinearMap.comp_apply, LinearMap.zero_apply, e, map_smul,
        BosonModule.component_df hq0 hq hx]
      simp
  exact LinearMap.congr_fun key z

/-- `U⁻_{ℤ,ν} ∩ fᵢU⁻ ⊆ (fᵢU⁻)^ℤ_ν`. -/
lemma mem_negFilt_of_eq_f {i : I} {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ negIntegral D)
    (hxw : x ∈ Uw D 𝕧 ν) {z : Um D 𝕧} (hz : x = NegativePart.f D 𝕧 i z) :
    x ∈ negFilt D i 1 ν := by
  have h := df_sub_df_comp_mem_negFilt D i (n := 0) (Nat.zero_le _) hx
    (by rwa [Finsupp.single_zero, tsub_zero])
  rwa [BosonModule.df_zero, BosonModule.df_zero, hz, comp_zero_f, sub_zero, ← hz] at h

end Filtration

/-! ### [Kas91] (7.5.3) -/

section Wall

variable {R : D.RootDatum Y} (hR : R.IsXRegular)

include hR in
/-- **[Kas91] (7.5.3)**: if `⟨hₖ, λ⟩ = 0` and `⟨hⱼ, λ⟩ ≥ νⱼ` for `j ≠ k`, then every `x ∈ U⁻_ν`
with `x u_λ = 0` lies in `U⁻fₖ`; equivalently, `x* ∈ fₖU⁻`. -/
theorem exists_starU_eq_f_of_evq_eq_zero {Λ : Dom R} {k : I} {ν : I →₀ ℕ}
    (hk : Λ.1 (R.coroot k) = 0) (hΛ : ∀ j, j ≠ k → (ν j : ℤ) ≤ Λ.1 (R.coroot j)) {x : Um D 𝕧}
    (hx : x ∈ Uw D 𝕧 ν) (h0 : evq hvt Λ x = 0) :
    ∃ z, starU D 𝕧 x = NegativePart.f D 𝕧 k z := by
  classical
  obtain ⟨Y, hY, rfl⟩ := hx
  set n : I → ℕ := fun i ↦ (Λ.1 (R.coroot i)).toNat
  have hker : Y ∈ evKernel D n := by
    rw [← ker_ev_eq hR Λ, LinearMap.mem_ker]; exact h0
  set P : Submodule 𝕂 (LusztigF 𝕂 I) :=
    serreSubmodule D 𝕧 ⊔ LinearMap.range (LinearMap.mulRight 𝕂 (θ 𝕂 k))
  have hle : evKernel D n ≤ P.comap (LusztigF.weightProj ν) := by
    refine sup_le (fun s hs ↦ ?_) ?_
    · rw [Submodule.mem_comap]
      refine Submodule.mem_sup_left (mem_serreSubmodule.2 ?_)
      exact weightProj_mem_serreIdeal (mem_serreSubmodule.1 hs) ν
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap,
      weightProj_of_mem (wordBasis_mem_weightSpace (rfl : wordWeight (powWord n g) = _))]
    split_ifs with hg
    · have hgi : n g.2 + 1 ≤ ν g.2 := by
        have := congrArg (fun μ : I →₀ ℕ ↦ μ g.2) hg
        simp only [powWord, wordWeight_append, GrandLoop.wordWeight_replicate,
          Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
          smul_eq_mul, mul_one] at this
        omega
      have hg2 : g.2 = k := by
        by_contra hne
        have := hΛ g.2 hne
        simp only [n] at hgi
        omega
      have hnk : n g.2 = 0 := by simp [n, hg2, hk]
      refine Submodule.mem_sup_right ⟨FreeAlgebra.wordBasis 𝕂 I g.1, ?_⟩
      rw [LinearMap.mulRight_apply, powWord, hnk, hg2, ← monomial_eq_wordBasis,
        ← monomial_eq_wordBasis]
      simp [monomial]
    · exact zero_mem _
  have hYP : Y ∈ P := by
    have := hle hker
    simpa only [Submodule.mem_comap, weightProj_of_mem hY, ↓reduceIte] using this
  obtain ⟨s, hs, t, ⟨Z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hYP
  refine ⟨Submodule.Quotient.mk (rev 𝕂 I Z), ?_⟩
  have e : (Submodule.Quotient.mk (s + Z * θ 𝕂 k) : Um D 𝕧) =
      Submodule.Quotient.mk (Z * θ 𝕂 k) := by
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hs, zero_add]
  change starU D 𝕧 (Submodule.Quotient.mk (s + LinearMap.mulRight 𝕂 (θ 𝕂 k) Z)) = _
  rw [LinearMap.mulRight_apply, e, starU_mk, rev_mul, rev_θ, NegativePart.f_mk]

omit [Finite I] in
/-- `f̃ᵢ u_λ = 0` if `⟨hᵢ, λ⟩ = 0`. -/
lemma fK_hwv_eq_zero {Λ : Dom R} {k : I} (hk : Λ.1 (R.coroot k) = 0) :
    fK hvt hR Λ k (IrreducibleModule.hwv R 𝕧 Λ.1) = 0 := by
  have hv' := pow_ne_one_of_transcendental' hvt
  set V := nodeSl2 R 𝕧 (IrreducibleModule R 𝕧 Λ.1) hv' (isInt hvt hR Λ) k
  have hE : V.E (IrreducibleModule.hwv R 𝕧 Λ.1) = 0 := IrreducibleModule.E_smul_hwv k
  have hp : IrreducibleModule.hwv R 𝕧 Λ.1 ∈ V.wt (Λ.1 (R.coroot k)) :=
    mem_nodeWt_of_mem IrreducibleModule.hwv_mem_weightSpace
  have h := IntegrableSl2.fTilde_dF (V := V) (pow_d_ne_zero k) (pow_d_ne_one hv' k) hE hp 0
  rw [IntegrableSl2.dF_zero] at h
  change V.fTilde _ _ _ = 0
  rw [h, IntegrableSl2.dF_apply, pow_one]
  change _ • (F R 𝕧 k • IrreducibleModule.hwv R 𝕧 Λ.1) = 0
  rw [F_smul_hwv_eq_zero hR hv' hk, smul_zero]

omit [Finite I] in
/-- `f̃_{w'} f̃ₖ u_λ = 0` if `⟨hₖ, λ⟩ = 0`. -/
lemma fW_append_singleton_eq_zero {Λ : Dom R} {k : I} (hk : Λ.1 (R.coroot k) = 0)
    (w : List I) : fW hvt hR Λ (w ++ [k]) = 0 := by
  induction w with
  | nil => exact fK_hwv_eq_zero hR hk
  | cons i w ih => rw [List.cons_append, fW_cons, ih, map_zero]

end Wall

/-! ### [Kas91] Lemma 7.5.1 -/

section Lemma

variable {R : D.RootDatum Y} (hR : R.IsXRegular)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

include hfund in
/-- The first half of the proof of [Kas91] Lemma 7.5.1: if `x ∈ (fᵢU⁻)^ℤ_ν ∩ L(∞)⁻` is
congruent to `f̃_{w'} f̃ₖ 1` modulo `v⁻¹L(∞)`, then `x* ∈ fₖU⁻`. -/
lemma exists_starU_eq_f_of_mem_negFilt {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) {i k : I}
    {w : List I} {x : Um D 𝕧} (hx : x ∈ negFilt D i 1 ν) (hx₁ : x ∈ latInfBar D)
    (hxw : x - fWi (D := D) hvt (w ++ [k]) ∈ ϖ • latInf (D := D) hvt A) :
    ∃ z, starU D 𝕧 x = NegativePart.f D 𝕧 k z := by
  obtain ⟨Λ, hk, hΛ⟩ := GrandLoop.exists_dom_wall hfund k ν.degree
  have hdeg : ∀ j, j ≠ k → (ν j : ℤ) ≤ Λ.1 (R.coroot j) := fun j hj ↦
    le_trans (by exact_mod_cast Finsupp.le_degree j ν) (hΛ j hj)
  refine exists_starU_eq_f_of_evq_eq_zero hR hk hdeg (mem_negFilt_le D hx).2 ?_
  refine hwFilt_eq_zero_of_mem hR hfund hIH Λ i le_rfl (evq_mem_hwFilt Λ hx) ?_ ?_
  · have e : evq hvt Λ x = evq hvt Λ (x - fWi hvt (w ++ [k])) +
        (evq hvt Λ (fWi hvt (w ++ [k])) - fW hvt hR Λ (w ++ [k])) := by
      rw [fW_append_singleton_eq_zero hR hk, map_sub, sub_zero, sub_add_cancel]
    rw [e]
    exact add_mem (evq_mem_smul_lat' (hR := hR) hfund hxw Λ)
      (evq_fWord_sub_fW_mem InfinityLocalRing.injective_algebraMap
        InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
        InfinityLocalRing.exists_pow_mul hfund (w ++ [k]) Λ)
  · rw [mem_latBar_iff, hwBar_evq]
    exact evq_mem_lat' (hR := hR) hfund hx₁ Λ

include hfund in
/-- **[Kas91] Lemma 7.5.1.** Under the induction hypothesis of [Kas91] §7 at the weights below
`ν`, let `x ∈ (fᵢU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻` and `y ∈ (fⱼU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻` be congruent
modulo `v⁻¹L(∞)` to the same element `f̃_w 1` of `B(∞)`, with `w` nonempty. Then `x = y`; that is,
`Gᵢ(b) = Gⱼ(b)` for `b ∈ f̃ᵢB(∞) ∩ f̃ⱼB(∞) ∩ B(∞)_ν`. Kashiwara's proof. -/
theorem eq_of_mem_negFilt {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) {i j : I} {w : List I}
    (hw : w ≠ []) {x y : Um D 𝕧} (hx : x ∈ negFilt D i 1 ν) (hx₁ : x ∈ latInfBar D)
    (hxw : x - fWi (D := D) hvt w ∈ ϖ • latInf (D := D) hvt A) (hy : y ∈ negFilt D j 1 ν)
    (hy₁ : y ∈ latInfBar D) (hyw : y - fWi (D := D) hvt w ∈ ϖ • latInf (D := D) hvt A) :
    x = y := by
  set k := w.getLast hw
  have ew : w = w.dropLast ++ [k] := (List.dropLast_append_getLast hw).symm
  rw [ew] at hxw hyw
  obtain ⟨zx, hzx⟩ := exists_starU_eq_f_of_mem_negFilt hR hfund hIH hx hx₁ hxw
  obtain ⟨zy, hzy⟩ := exists_starU_eq_f_of_mem_negFilt hR hfund hIH hy hy₁ hyw
  set Q := x - y
  have hQs : starU D 𝕧 Q = NegativePart.f D 𝕧 k (zx - zy) := by
    rw [map_sub, map_sub, hzx, hzy]
  have hQZ : Q ∈ negIntegral D := sub_mem (mem_negFilt_le D hx).1 (mem_negFilt_le D hy).1
  have hQw : Q ∈ Uw D 𝕧 ν := sub_mem (mem_negFilt_le D hx).2 (mem_negFilt_le D hy).2
  have hQϖ : Q ∈ ϖ • latInf (D := D) hvt A := by
    have e : Q = (x - fWi hvt (w.dropLast ++ [k])) - (y - fWi hvt (w.dropLast ++ [k])) := by
      simp only [Q]; abel
    rw [e]; exact sub_mem hxw hyw
  have hQ₁ : Q ∈ latInfBar D := sub_mem hx₁ hy₁
  have hF : starU D 𝕧 Q ∈ negFilt D k 1 ν :=
    mem_negFilt_of_eq_f (starU_mem_negIntegral hQZ) (starU_mem_Uw hQw) hQs
  have h0 := negFilt_eq_zero_of_mem hR hfund hIH k le_rfl hF (starU_mem_smul_latInf' hQϖ)
    (starU_mem_latInfBar hQ₁)
  have : Q = 0 := by rw [← starU_starU (D := D) (v := 𝕧) Q, h0, map_zero]
  exact sub_eq_zero.1 this

end Lemma

end LieLean.QuantumGroup
