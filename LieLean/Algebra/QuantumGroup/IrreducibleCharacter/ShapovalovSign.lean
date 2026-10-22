/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Rank
import LieLean.Algebra.QuantumGroup.GabberKac.SerreSpanSign

/-!
# Shapovalov pairings under a sign twist

Let `σ : I → I → K` and let `T = LusztigF.signTwist σ` be the linear map of `'f = K⟨θᵢ⟩` scaling
each word `w` by `∏_{a < b} σ(w_a, w_b)`. This file compares the Shapovalov-type pairings
`S_c(w, y) = ε(E_w y)` of `LusztigF.vermaForm` for two coefficient families `c`, `c'` related by

`c i μ · ∏ₖ σ(i, k)^{μₖ} = sᵢ · ∏ₖ σ(k, i)^{μₖ} · c' i μ`.

Under this relation `E_i^{c}(T y) = sᵢ ∏ₖ σ(k, i)^{μₖ} · T(E_i^{c'} y)` for `y` of weight `μ`
(`LusztigF.vermaOp_signTwist`), hence `S_c(w, T y) = κ S_{c'}(w, y)` with `κ ≠ 0`
(`LusztigF.vermaForm_signTwist`), and the kernels of the Shapovalov maps on `'f_ν` correspond under
`T` (`LusztigF.shapovalovMap_signTwist_eq_zero_iff`); for `σ` with values `±1` the ranks agree
(`LusztigF.shapovalovRank_eq_of_signTwist`).

Consequently, at parameters `qᵢ = ±1` with `qᵢ^{-aᵢⱼ} = qⱼ^{-aⱼᵢ}`, an element of `'f_ν`
(`νᵢ ≤ nᵢ`) in the kernel of a pairing whose coefficients are the classical ones `nᵢ - ⟨μ, αᵢ^∨⟩`
twisted by the sign character `μ ↦ ∏ₖ qᵢ^{-aᵢₖ μₖ}` lies in the span of the Serre products with
parameters `q` (`LusztigF.mem_serreSpan_of_shapovalovMap_eq_zero_of_sq_eq_one`), by the classical
kernel (`LusztigF.mem_serreSpan_of_shapovalovMap_eq_zero`, from the Gabber–Kac theorem).

This is used for the pairing of [Lus] 35.4.2 at a quasi-classical parameter (`q_i = ±1`): its
coefficients differ from the classical ones `⟨Λ - μ, αᵢ^∨⟩` by such a sign character, which
`LusztigF.signTwist_serreProduct` matches with the Serre relations at the parameters `qᵢ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 33.2, 35.4.
-/

noncomputable section

open FreeAlgebra

namespace LusztigF

variable {K I : Type*} [Field K]

/-! ### Sign characters of weights -/

/-- The character `μ ↦ ∏ₖ f(k)^{μₖ}` of `ℕ[I]`. -/
def weightSign (f : I → K) (μ : I →₀ ℕ) : K := μ.prod fun k m ↦ f k ^ m

@[simp] lemma weightSign_zero (f : I → K) : weightSign f 0 = 1 := by simp [weightSign]

lemma weightSign_add (f : I → K) (μ μ' : I →₀ ℕ) :
    weightSign f (μ + μ') = weightSign f μ * weightSign f μ' := by
  classical exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _

@[simp] lemma weightSign_single (f : I → K) (i : I) (m : ℕ) :
    weightSign f (Finsupp.single i m) = f i ^ m :=
  Finsupp.prod_single_index (pow_zero _)

lemma weightSign_ne_zero {f : I → K} (hf : ∀ k, f k ≠ 0) (μ : I →₀ ℕ) : weightSign f μ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (hf k)

lemma weightSign_mul (f g : I → K) (μ : I →₀ ℕ) :
    weightSign (fun k ↦ f k * g k) μ = weightSign f μ * weightSign g μ := by
  simp only [weightSign, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]

lemma prod_map_eq_weightSign (f : I → K) (w : List I) :
    (w.map f).prod = weightSign f (wordWeight w) := by
  classical
  induction w with
  | nil => simp
  | cons i w ih => rw [List.map_cons, List.prod_cons, ih, wordWeight_cons, weightSign_add,
      weightSign_single, pow_one]

/-- Removing one letter `i` from a weight with `μᵢ ≠ 0`. -/
lemma weightSign_tsub_single (f : I → K) {μ : I →₀ ℕ} {i : I} (h : μ i ≠ 0) :
    weightSign f μ = f i * weightSign f (μ - Finsupp.single i 1) := by
  classical
  conv_lhs => rw [← single_add_tsub_single h, add_comm]
  rw [weightSign_add, weightSign_single, pow_one, mul_comm]

/-! ### The twist and the Verma-type operators -/

section Twist

variable [DecidableEq I] (σ : I → I → K)

omit [DecidableEq I] in
lemma signTwist_mem {μ : I →₀ ℕ} {y : LusztigF K I} (hy : y ∈ wordSpan K μ) :
    signTwist σ y ∈ wordSpan K μ := by
  induction hy using wordSpan_induction with
  | word w hw =>
    rw [signTwist_wordBasis]; exact Submodule.smul_mem _ _ (wordBasis_mem_wordSpan_of_eq hw)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

omit [DecidableEq I] in
/-- `T(θⱼ y) = ∏ₖ σ(j, k)^{μₖ} θⱼ T(y)` for `y` of weight `μ`. -/
lemma signTwist_ι_mul (j : I) {μ : I →₀ ℕ} {y : LusztigF K I} (hy : y ∈ wordSpan K μ) :
    signTwist σ (ι K j * y) = weightSign (σ j) μ • (ι K j * signTwist σ y) := by
  induction hy using wordSpan_induction with
  | word w hw =>
    rw [ι_mul_wordBasis, signTwist_wordBasis, signTwist_wordBasis, signWord_cons,
      prod_map_eq_weightSign, hw, mul_smul_comm, ι_mul_wordBasis, smul_smul]
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add, smul_add]
  | smul a y _ hy => rw [mul_smul_comm, map_smul, hy, map_smul, mul_smul_comm, smul_comm]

variable {σ}

/-- **The Verma-type operators under the twist.** If
`c μ · ∏ₖ σ(i, k)^{μₖ} = s · ∏ₖ σ(k, i)^{μₖ} · c' μ` for all `μ` and `σ(i, i) = 1`, then
`E_i^{c}(T y) = s ∏ₖ σ(k, i)^{μₖ} · T(E_i^{c'} y)` for `y` of weight `μ`. -/
theorem vermaOp_signTwist {i : I} {c c' : (I →₀ ℕ) → K} {s : K} (hσi : σ i i = 1)
    (hc : ∀ μ, c μ * weightSign (σ i) μ = s * weightSign (fun k ↦ σ k i) μ * c' μ)
    {μ : I →₀ ℕ} {y : LusztigF K I} (hy : y ∈ wordSpan K μ) :
    vermaOp i c (signTwist σ y) =
      (s * weightSign (fun k ↦ σ k i) μ) • signTwist σ (vermaOp i c' y) := by
  suffices h : ∀ w : List I, vermaOp i c (signTwist σ (wordBasis K I w)) =
      (s * weightSign (fun k ↦ σ k i) (wordWeight w)) •
        signTwist σ (vermaOp i c' (wordBasis K I w)) by
    induction hy using wordSpan_induction with
    | word w hw => rw [h, hw]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add, map_add, smul_add]
    | smul a y _ hy => rw [map_smul, map_smul, hy, map_smul, map_smul, smul_comm]
  intro w
  induction w with
  | nil => rw [signTwist_wordBasis]; simp
  | cons j w ih =>
    have hw : wordBasis K I w ∈ wordSpan K (wordWeight w) := wordBasis_mem_wordSpan w
    have hTw : signTwist σ (wordBasis K I w) ∈ wordSpan K (wordWeight w) := signTwist_mem σ hw
    rw [← ι_mul_wordBasis, signTwist_ι_mul σ j hw, map_smul, vermaOp_ι_mul, vermaOp_ι_mul, ih,
      wordWeight_cons, weightSign_add, map_add, smul_add, smul_add]
    rw [weightSign_single, pow_one]
    congr 1
    · -- the terms `θⱼ E(y)`
      by_cases hμi : wordWeight w i = 0
      · rw [vermaOp_eq_zero_of_mem i c' hμi hw]
        simp
      · have hE : vermaOp i c' (wordBasis K I w) ∈
            wordSpan K (wordWeight w - Finsupp.single i 1) :=
          vermaOp_mem_wordSpan i c' hw
        rw [signTwist_ι_mul σ j hE, mul_smul_comm, smul_smul, smul_smul,
          weightSign_tsub_single (σ j) hμi]
        congr 1
        ring
    · split_ifs with hij
      · subst hij
        rw [weightScale_of_mem c hTw, weightScale_of_mem c' hw, map_smul, smul_smul, smul_smul,
          hσi]
        congr 1
        rw [mul_comm, hc]
        ring
      · simp

/-- **The Verma-type word operators under the twist.** Under the hypotheses of
`LusztigF.vermaOp_signTwist` at every `i`, with `sᵢ ≠ 0` and `σ` nowhere zero, for each word
`u` and weight `μ` there is `κ ≠ 0` with `E_u^{c}(T y) = κ · T(E_u^{c'} y)` for all `y` of
weight `μ`. -/
theorem vermaWordOp_signTwist {c c' : I → (I →₀ ℕ) → K} {s : I → K} (hs : ∀ i, s i ≠ 0)
    (hσ0 : ∀ i j, σ i j ≠ 0) (hσd : ∀ i, σ i i = 1)
    (hc : ∀ i μ, c i μ * weightSign (σ i) μ = s i * weightSign (fun k ↦ σ k i) μ * c' i μ)
    (u : List I) (μ : I →₀ ℕ) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ y ∈ wordSpan K μ,
      vermaWordOp c u (signTwist σ y) = κ • signTwist σ (vermaWordOp c' u y) := by
  induction u generalizing μ with
  | nil => exact ⟨1, one_ne_zero, fun y _ ↦ by simp⟩
  | cons i u ih =>
    obtain ⟨κ, hκ, h⟩ := ih (μ - Finsupp.single i 1)
    refine ⟨s i * weightSign (fun k ↦ σ k i) μ * κ,
      mul_ne_zero (mul_ne_zero (hs i) (weightSign_ne_zero (fun k ↦ hσ0 k i) μ)) hκ,
      fun y hy ↦ ?_⟩
    rw [vermaWordOp_cons, vermaOp_signTwist (hσd i) (hc i) hy, map_smul,
      h _ (vermaOp_mem_wordSpan i (c' i) hy), smul_smul, vermaWordOp_cons]

omit [DecidableEq I] in
variable (σ) in
/-- The augmentation is unchanged by the twist. -/
lemma algebraMapInv_signTwist (y : LusztigF K I) :
    algebraMapInv (signTwist σ y) = algebraMapInv y := by
  have : (algebraMapInv : LusztigF K I →ₐ[K] K).toLinearMap ∘ₗ signTwist σ =
      (algebraMapInv : LusztigF K I →ₐ[K] K).toLinearMap :=
    (wordBasis K I).ext fun w ↦ by
      rw [LinearMap.comp_apply, signTwist_wordBasis, map_smul]
      cases w with
      | nil => simp
      | cons a w => simp [algebraMapInv]
  exact LinearMap.congr_fun this y

/-- **The Shapovalov pairings under the twist.** For each word `u` and weight `μ` there is
`κ ≠ 0` with `S_c(u, T y) = κ · S_{c'}(u, y)` for all `y` of weight `μ`. -/
theorem vermaForm_signTwist {c c' : I → (I →₀ ℕ) → K} {s : I → K} (hs : ∀ i, s i ≠ 0)
    (hσ0 : ∀ i j, σ i j ≠ 0) (hσd : ∀ i, σ i i = 1)
    (hc : ∀ i μ, c i μ * weightSign (σ i) μ = s i * weightSign (fun k ↦ σ k i) μ * c' i μ)
    (u : List I) (μ : I →₀ ℕ) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ y ∈ wordSpan K μ, vermaForm c u (signTwist σ y) = κ * vermaForm c' u y := by
  obtain ⟨κ, hκ, h⟩ := vermaWordOp_signTwist hs hσ0 hσd hc u μ
  exact ⟨κ, hκ, fun y hy ↦ by
    rw [vermaForm_apply, h y hy, map_smul, algebraMapInv_signTwist, smul_eq_mul, vermaForm_apply]⟩

/-- **Kernels of the Shapovalov maps under the twist.** For `y ∈ 'f_ν`, `S_c(·, T y) = 0` iff
`S_{c'}(·, y) = 0`. -/
theorem shapovalovMap_signTwist_eq_zero_iff {c c' : I → (I →₀ ℕ) → K} {s : I → K}
    (hs : ∀ i, s i ≠ 0) (hσ0 : ∀ i j, σ i j ≠ 0) (hσd : ∀ i, σ i i = 1)
    (hc : ∀ i μ, c i μ * weightSign (σ i) μ = s i * weightSign (fun k ↦ σ k i) μ * c' i μ)
    {ν : I →₀ ℕ} {y : LusztigF K I} (hy : y ∈ weightSpace K ν) :
    shapovalovMap c ν (signTwist σ y) = 0 ↔ shapovalovMap c' ν y = 0 := by
  have hy' : y ∈ wordSpan K ν := hy
  rw [shapovalovMap_eq_zero_iff c (signTwist_mem σ hy'), shapovalovMap_eq_zero_iff c' hy]
  refine forall_congr' fun u ↦ ?_
  obtain ⟨κ, hκ, h⟩ := vermaForm_signTwist hs hσ0 hσd hc u ν
  rw [h y hy', mul_eq_zero, or_iff_right hκ]

/-- **Ranks of the Shapovalov maps under the twist.** If moreover `σ(i, j)² = 1`, the Shapovalov
maps for `c` and `c'` have ranks of the same dimension on `'f_ν`. -/
theorem shapovalovRank_eq_of_signTwist {c c' : I → (I →₀ ℕ) → K} {s : I → K}
    (hs : ∀ i, s i ≠ 0) (hσ : ∀ i j, σ i j ^ 2 = 1) (hσd : ∀ i, σ i i = 1)
    (hc : ∀ i μ, c i μ * weightSign (σ i) μ = s i * weightSign (fun k ↦ σ k i) μ * c' i μ)
    (ν : I →₀ ℕ) : shapovalovRank c ν = shapovalovRank c' ν := by
  have hσ0 : ∀ i j, σ i j ≠ 0 := fun i j h ↦ by simpa [h] using hσ i j
  have : FiniteDimensional K (weightSpace K ν) := by
    rw [weightSpace_eq_span]
    exact FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hW : (weightSpace K ν).map (signTwist σ) = weightSpace K ν := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun y hy ↦ signTwist_mem σ hy)
      fun y hy ↦ ⟨signTwist σ y, signTwist_mem σ hy, signTwist_signTwist hσ y⟩
  have hrange : LinearMap.range ((shapovalovMap c ν).domRestrict (weightSpace K ν)) =
      LinearMap.range ((shapovalovMap c ν ∘ₗ signTwist σ).domRestrict (weightSpace K ν)) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_domRestrict, Submodule.map_comp, hW]
  rw [shapovalovRank, shapovalovRank, hrange]
  refine LinearMap.finrank_range_eq_of_ker_eq _ _ ?_
  ext y
  simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.comp_apply]
  exact shapovalovMap_signTwist_eq_zero_iff hs hσ0 hσd hc y.2

end Twist

/-! ### The classical and quasi-classical kernels -/

section Kernel

variable [Fintype I] [DecidableEq I] [CharZero K] (D : LusztigCartanDatum I)

/-- A weight of the standard realization over `K` with `⟨Λ, αᵢ^∨⟩ = nᵢ`. -/
def stdWeightOver (n : I → ℕ) : Module.Dual K (Matrix.Realization.StdSpace D.cartanMatrix K) :=
  (∑ i, (n i : K) • LinearMap.proj i) ∘ₗ LinearMap.fst K (I → K) _

omit [CharZero K] in
lemma stdWeightOver_coroot (n : I → ℕ) (i : I) :
    stdWeightOver D n ((Matrix.Realization.std D.cartanMatrix K).coroot i) = n i := by
  simp [stdWeightOver, Matrix.Realization.std, Pi.single_apply]

omit [Fintype I] in
/-- **The classical kernel.** If `y ∈ 'f_ν` with `νᵢ ≤ nᵢ` for all `i` pairs to zero with all
words for the classical Shapovalov pairing of highest weight `n`, then `y` lies in the span of
the classical Serre products of weight `ν`. -/
theorem mem_serreSpan_of_shapovalovMap_eq_zero [Finite I] (n : I → ℕ) {ν : I →₀ ℕ}
    (hν : ∀ i, ν i ≤ n i)
    {y : LusztigF K I} (hy : y ∈ weightSpace K ν)
    (h0 : shapovalovMap (classicalCoeff K D n) ν y = 0) :
    y ∈ serreSpan D (fun _ ↦ (1 : K)) ν := by
  have := Fintype.ofFinite I
  exact mem_serreSpan_of_vermaForm_eq_zero D (Matrix.Realization.std D.cartanMatrix K)
      (stdWeightOver_coroot D n) hν hy fun w hw ↦ congr_fun h0 ⟨w, hw⟩

omit [Fintype I] in
/-- **The quasi-classical kernel.** Let `qᵢ² = 1` with `qᵢ^{-aᵢⱼ} = qⱼ^{-aⱼᵢ}` for `i ≠ j`, and
let the coefficients `c` differ from the classical ones of highest weight `n` by the sign character
`μ ↦ ∏ₖ qᵢ^{-aᵢₖ μₖ}` and nonzero scalars `sᵢ`. If `y ∈ 'f_ν` with `νᵢ ≤ nᵢ` pairs to zero with all
words for the pairing `S_c`, then `y` lies in the span of the Serre products of weight `ν` with
parameters `q`. -/
theorem mem_serreSpan_of_shapovalovMap_eq_zero_of_sq_eq_one [Finite I] {q : I → K}
    (hq : ∀ i, q i ^ 2 = 1)
    (hsym : ∀ i j, i ≠ j → q i ^ (serreExp D i j - 1) = q j ^ (serreExp D j i - 1))
    (n : I → ℕ) {c : I → (I →₀ ℕ) → K} {s : I → K} (hs : ∀ i, s i ≠ 0)
    (hc : ∀ i μ, c i μ =
      s i * weightSign (fun k ↦ q i ^ (serreExp D i k - 1)) μ * classicalCoeff K D n i μ)
    {ν : I →₀ ℕ} (hν : ∀ i, ν i ≤ n i) {y : LusztigF K I} (hy : y ∈ weightSpace K ν)
    (h0 : shapovalovMap c ν y = 0) :
    y ∈ serreSpan D q ν := by
  have := Fintype.ofFinite I
  let _ : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  set σ : I → I → K := fun i j ↦ if i < j then q i ^ (serreExp D i j - 1) else 1
  have hσ : ∀ i j, σ i j ^ 2 = 1 := fun i j ↦ by
    simp only [σ]; split_ifs
    · rw [← pow_mul, mul_comm, pow_mul, hq, one_pow]
    · exact one_pow 2
  have hσ0 : ∀ i j, σ i j ≠ 0 := fun i j h ↦ by simpa [h] using hσ i j
  have hσd : ∀ i, σ i i = 1 := fun i ↦ by simp [σ]
  have hσq : ∀ i j, i ≠ j → σ i j * σ j i = q i ^ (serreExp D i j - 1) := fun i j hij ↦ by
    rcases lt_or_gt_of_ne hij with h | h
    · simp [σ, h, h.not_gt]
    · simp [σ, h, h.not_gt, hsym i j hij]
  have hτ : ∀ i k, q i ^ (serreExp D i k - 1) = σ k i * σ i k := fun i k ↦ by
    by_cases hik : i = k
    · subst hik; simp [hσd, serreExp, D.cartanMatrix_self]
    · rw [mul_comm, hσq i k hik]
  -- the twist relates `c` to the classical coefficients
  have hc' : ∀ i μ, c i μ * weightSign (σ i) μ =
      s i * weightSign (fun k ↦ σ k i) μ * classicalCoeff K D n i μ := fun i μ ↦ by
    have hB : weightSign (σ i) μ * weightSign (σ i) μ = 1 := by
      rw [← weightSign_mul]
      simp only [← sq, hσ]
      simp [weightSign]
    rw [hc, show (fun k ↦ q i ^ (serreExp D i k - 1)) = fun k ↦ σ k i * σ i k from
      funext (hτ i), weightSign_mul]
    linear_combination (s i * weightSign (fun k ↦ σ k i) μ * classicalCoeff K D n i μ) * hB
  have hTy : signTwist σ y ∈ weightSpace K ν := signTwist_mem σ hy
  have h2 := mem_serreSpan_of_shapovalovMap_eq_zero D n hν hTy
    ((shapovalovMap_signTwist_eq_zero_iff hs hσ0 hσd hc' hTy).1 (by
      rwa [signTwist_signTwist hσ]))
  -- the twist maps the classical Serre span into the one with parameters `q`
  have hmap : ∀ z ∈ serreSpan D (fun _ ↦ (1 : K)) ν, signTwist σ z ∈ serreSpan D q ν := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, rfl⟩ := hz
      obtain ⟨t, ht0, ht⟩ := signTwist_serreProduct D hq hσ hσd hσq hg.1
      have : signTwist σ (serreProduct D (fun _ ↦ (1 : K)) g) = t⁻¹ • serreProduct D q g := by
        rw [← signTwist_signTwist hσ (serreProduct D q g), ht, map_smul, smul_smul,
          inv_mul_cancel₀ ht0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a b _ hb => rw [map_smul]; exact Submodule.smul_mem _ _ hb
  have := hmap _ h2
  rwa [signTwist_signTwist hσ] at this

end Kernel

end LusztigF
