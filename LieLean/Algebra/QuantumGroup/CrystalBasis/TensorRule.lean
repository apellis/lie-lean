/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorStrings
import LieLean.Algebra.QuantumGroup.CrystalBasis.Sl2
import Mathlib.RingTheory.Flat.Domain

/-!
# The strings of a tensor product of two strings

We continue `QuantumGroup/CrystalBasis/TensorStrings.lean`. For primitive vectors `η ∈ M₁ᵃ`,
`ζ ∈ M₂ᵇ`, `uᵢ = F^{(i)} η`, `vⱼ = F^{(j)} ζ`, `s ≤ min(a, b)` and `ℓ = a + b - 2s`, the lowest
vector `F^{(ℓ)} w_s` of the string of `w_s` is `e z_s` with `e ∈ 1 + ϖ A`
(`QuantumGroup.IntegrableSl2.tensor_dF_tensorHigh_top`), so that modulo `ϖ`
`F^{(r)} w_s ≡ u_r ⊗ v_s` for `r ≤ a - s` and `F^{(r)} w_s ≡ u_{a-s} ⊗ v_{s + r - (a - s)}` for
`a - s ≤ r ≤ ℓ` (`QuantumGroup.IntegrableSl2.tensor_dF_tensorHigh_sub_tensorIndex`): the string of
`w_s` reduces to the string of `u₀ ⊗ v_s` in the crystal `B(a) ⊗ B(b)` ([HK] (4.12)).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
-/

open TensorProduct Finset

namespace LieLean.QuantumGroup

/-- Coordinate functionals of a linearly independent family. -/
lemma exists_coord {k ι M : Type*} [Field k] [AddCommGroup M] [Module k M] [DecidableEq ι]
    {f : ι → M}
    (hf : LinearIndependent k f) :
    ∃ ξ : ι → Module.Dual k M, ∀ i j, ξ i (f j) = if j = i then 1 else 0 := by
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination k f).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hf)
  refine ⟨fun i ↦ Finsupp.lapply i ∘ₗ g, fun i j ↦ ?_⟩
  have := LinearMap.congr_fun hg (Finsupp.single j 1)
  simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
    LinearMap.id_apply] at this
  simp [this, Finsupp.single_apply]

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] (V₁ : IntegrableSl2 q M₁) (V₂ : IntegrableSl2 q M₂)
  (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {a b : ℕ} {η : M₁} {ζ : M₂}

include hq0 hq

/-- The vectors `F^{(i)} η`, `i ≤ p`, of a string are linearly independent. -/
lemma linearIndependent_dF_single {p : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
    {V : IntegrableSl2 q M} {x : M} (hx : x ∈ V.prim p) (hx0 : x ≠ 0) :
    LinearIndependent k (fun i : Fin (p + 1) ↦ V.dF i x) := by
  have h := linearIndependent_dF (ι := Unit) (p := fun _ ↦ p) (η := fun _ ↦ x) hq0 hq
    (fun _ ↦ hx) (fun p₀ ↦ by
      rw [linearIndependent_subsingleton_index_iff]
      intro _; exact hx0)
  exact h.comp (fun i ↦ ⟨(), i⟩) (fun i j hij ↦ by simpa using hij)

variable {V₁ V₂} in
/-- The vectors `uᵢ ⊗ vⱼ`, `i ≤ a`, `j ≤ b`, are linearly independent. -/
lemma linearIndependent_tmul_dF (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (hη0 : η ≠ 0)
    (hζ0 : ζ ≠ 0) :
    LinearIndependent k (fun x : Fin (a + 1) × Fin (b + 1) ↦ V₁.dF x.1 η ⊗ₜ[k] V₂.dF x.2 ζ) := by
  have h1 := linearIndependent_dF_single hq0 hq hη hη0
  have h2 := linearIndependent_dF_single hq0 hq hζ hζ0
  have h := LinearIndependent.tmul_of_isDomain h1 h2
  exact h

/-! ### `F` on the lowest line -/

/-- `F (Σ_{i ≤ s} eᵢ u_{a-s+i} ⊗ v_{b-i})`, for any coefficients `eᵢ`. -/
theorem tensorF_lowLine (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) {s : ℕ} (hsa : s ≤ a)
    (hsb : s ≤ b) (e : ℕ → k) :
    tensorF V₁ V₂ (∑ i ∈ range (s + 1), e i • (V₁.dF (a - s + i) η ⊗ₜ[k] V₂.dF (b - i) ζ)) =
      ∑ i ∈ range s, (e i * qIntZ q ((a : ℤ) - s + i + 1) +
        e (i + 1) * q ^ ((a : ℤ) - 2 * (a - s + i + 1 : ℕ)) * qIntZ q ((b : ℤ) - i)) •
        (V₁.dF (a - s + i + 1) η ⊗ₜ[k] V₂.dF (b - i) ζ) := by
  rw [map_sum]
  have hterm : ∀ i ∈ range (s + 1), tensorF V₁ V₂ (e i •
      (V₁.dF (a - s + i) η ⊗ₜ[k] V₂.dF (b - i) ζ)) =
      (e i * qIntZ q (((a - s + i : ℕ) : ℤ) + 1)) •
        (V₁.dF (a - s + i + 1) η ⊗ₜ[k] V₂.dF (b - i) ζ) +
      (e i * q ^ ((a : ℤ) - 2 * (a - s + i : ℕ)) * qIntZ q (((b - i : ℕ) : ℤ) + 1)) •
        (V₁.dF (a - s + i) η ⊗ₜ[k] V₂.dF (b - i + 1) ζ) := by
    intro i _
    have hmem : V₁.dF (a - s + i) η ∈ V₁.wt ((a : ℤ) - 2 * (a - s + i : ℕ)) := dF_mem hη.1 _
    rw [map_smul, tensorF_tmul hmem, F_dF_eq hq0 hq, F_dF_eq hq0 hq, smul_add]
    simp only [← smul_tmul' (R' := k), tmul_smul (R' := k), smul_smul, mul_assoc]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_range_succ _ s, sum_range_succ' _ s]
  have h1 : V₁.dF (a - s + s + 1) η = 0 :=
    dF_eq_zero_of_primitive hq0 hq hη.1 hη.2 (by push_cast; omega)
  have h2 : V₂.dF (b - 0 + 1) ζ = 0 :=
    dF_eq_zero_of_primitive hq0 hq hζ.1 hζ.2 (by push_cast; omega)
  rw [h1, h2]
  simp only [zero_tmul, tmul_zero, smul_zero, add_zero]
  rw [add_comm, ← sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi := mem_range.1 hi
  rw [show a - s + (i + 1) = a - s + i + 1 by omega, show b - (i + 1) + 1 = b - i by omega,
    ← add_smul]
  congr 1
  have e2 : (((b - (i + 1) : ℕ) : ℤ) + 1) = b - i := by
    push_cast [show i + 1 ≤ b by omega]; ring
  have e3 : (((a - s + i : ℕ) : ℤ) + 1) = a - s + i + 1 := by push_cast [hsa]; ring
  rw [e2, e3]
  ring

/-- An `F`-killed combination of the lowest line is a multiple of `z_s`. -/
theorem eq_lowCoeff_of_tensorF_eq_zero (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b)
    (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0) {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) (e : ℕ → k)
    (h : tensorF V₁ V₂ (∑ i ∈ range (s + 1),
      e i • (V₁.dF (a - s + i) η ⊗ₜ[k] V₂.dF (b - i) ζ)) = 0) :
    ∀ i ≤ s, e i = e 0 * lowCoeff q a b s i := by
  rw [tensorF_lowLine V₁ V₂ hq0 hq hη hζ hsa hsb, ← Fin.sum_univ_eq_sum_range] at h
  -- independence of the vectors `u_{a-s+i+1} ⊗ v_{b-i}`, `i < s`
  have hli := (linearIndependent_tmul_dF hq0 hq hη hζ hη0 hζ0).comp
    (fun i : Fin s ↦ ((⟨a - s + i + 1, by omega⟩ : Fin (a + 1)), (⟨b - i, by omega⟩ : Fin (b + 1))))
    (fun i j hij ↦ by
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hij
      exact Fin.ext (by omega))
  have hc := Fintype.linearIndependent_iff.1 hli _ h
  intro i
  induction i with
  | zero => intro _; simp [lowCoeff]
  | succ i ih =>
    intro hi
    have h0 := hc ⟨i, by omega⟩
    simp only at h0
    rw [lowCoeff]
    rw [show e 0 * (-lowCoeff q a b s i * qIntZ q ((a : ℤ) - s + i + 1) *
        q ^ ((a : ℤ) - 2 * s + 2 * i + 2) / qIntZ q ((b : ℤ) - i)) =
        -(e 0 * lowCoeff q a b s i) * qIntZ q ((a : ℤ) - s + i + 1) *
        q ^ ((a : ℤ) - 2 * s + 2 * i + 2) / qIntZ q ((b : ℤ) - i) by ring, ← ih (by omega)]
    have hb : qIntZ q ((b : ℤ) - i) ≠ 0 := qIntZ_ne_zero hq0 hq (by omega)
    have hz : q ^ ((a : ℤ) - 2 * (a - s + i + 1 : ℕ)) * q ^ ((a : ℤ) - 2 * s + 2 * i + 2) = 1 := by
      rw [← zpow_add₀ hq0, show (a : ℤ) - 2 * (a - s + i + 1 : ℕ) + ((a : ℤ) - 2 * s + 2 * i + 2)
        = 0 by push_cast [hsa]; ring, zpow_zero]
    field_simp
    linear_combination (q ^ ((a : ℤ) - 2 * s + 2 * i + 2)) * h0 -
      e (i + 1) * qIntZ q ((b : ℤ) - i) * hz

/-! ### The lowest vector of the string of `w_s` -/

/-- `w_s` has weight `a + b - 2s`. -/
lemma tensorHigh_mem_wt (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (s : ℕ) :
    tensorHigh V₁ V₂ a b η ζ s ∈ (tensor V₁ V₂ hq0 hq).wt ((a : ℤ) + b - 2 * s) := by
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ ?_
  have hi := mem_range.1 hi
  have h := tmul_mem_tensor_wt hq0 hq (dF_mem hη.1 i) (dF_mem hζ.1 (s - i))
  convert h using 2
  push_cast [show i ≤ s by omega]
  ring

/-- The lowest vector `F^{(ℓ)} w_s` (`ℓ = a + b - 2s`) of the string of `w_s` is a multiple of
`z_s`. -/
theorem exists_tensor_dF_tensorHigh_top (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b)
    (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0) {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) :
    ∃ e : k, (tensor V₁ V₂ hq0 hq).dF (a + b - 2 * s) (tensorHigh V₁ V₂ a b η ζ s) =
      e • tensorLow V₁ V₂ a b η ζ s := by
  classical
  set T := tensor V₁ V₂ hq0 hq
  set ℓ := a + b - 2 * s
  have hw : tensorHigh V₁ V₂ a b η ζ s ∈ T.wt (ℓ : ℤ) := by
    convert tensorHigh_mem_wt V₁ V₂ hq0 hq hη hζ s using 2
    simp only [ℓ]
    push_cast [show 2 * s ≤ a + b by omega]
    ring
  have hwE : T.E (tensorHigh V₁ V₂ a b η ζ s) = 0 :=
    tensor_E_tensorHigh V₁ V₂ hq0 hq hη hζ hsa
  -- `F^{(ℓ)} w_s` lies in the span of the lowest line
  have hspan : T.dF ℓ (tensorHigh V₁ V₂ a b η ζ s) ∈ Submodule.span k
      (Set.range fun t : Fin (s + 1) ↦ V₁.dF (a - s + t) η ⊗ₜ[k] V₂.dF (b - t) ζ) := by
    rw [tensor_dF_tensorHigh V₁ V₂ hq0 hq hη]
    refine Submodule.sum_mem _ fun i hi ↦ Submodule.sum_mem _ fun p hp ↦ ?_
    have hi := mem_range.1 hi
    have hp := mem_antidiagonal.1 hp
    refine Submodule.smul_mem _ _ ?_
    by_cases h1 : p.1 + i ≤ a
    · by_cases h2 : p.2 + (s - i) ≤ b
      · refine Submodule.subset_span ⟨⟨p.1 + i - (a - s), by omega⟩, ?_⟩
        simp only
        congr 3 <;> omega
      · rw [dF_eq_zero_of_primitive hq0 hq hζ.1 hζ.2 (by push_cast; omega), tmul_zero]
        exact zero_mem _
    · rw [dF_eq_zero_of_primitive hq0 hq hη.1 hη.2 (by push_cast; omega), zero_tmul]
      exact zero_mem _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hspan
  set e : ℕ → k := fun i ↦ if h : i < s + 1 then c ⟨i, h⟩ else 0
  have hx : T.dF ℓ (tensorHigh V₁ V₂ a b η ζ s) =
      ∑ i ∈ range (s + 1), e i • (V₁.dF (a - s + i) η ⊗ₜ[k] V₂.dF (b - i) ζ) := by
    rw [← hc, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [e, i.2, ↓reduceDIte]
  -- it is killed by `F`
  have hF : tensorF V₁ V₂ (∑ i ∈ range (s + 1),
      e i • (V₁.dF (a - s + i) η ⊗ₜ[k] V₂.dF (b - i) ζ)) = 0 := by
    rw [← hx]
    change T.F (T.dF ℓ _) = 0
    rw [F_dF hq0 hq, dF_eq_zero_of_primitive hq0 hq hw hwE (by push_cast; omega), smul_zero]
  have he := eq_lowCoeff_of_tensorF_eq_zero V₁ V₂ hq0 hq hη hζ hη0 hζ0 hsa hsb e hF
  refine ⟨e 0, ?_⟩
  rw [hx, tensorLow, smul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [he i (by have := mem_range.1 hi; omega), smul_smul]

/-- The position of `F^{(r)} w_s` in `B(a) ⊗ B(b)`: `(r, s)` for `r ≤ a - s` and
`(a - s, s + r - (a - s))` otherwise ([HK] (4.12)). -/
def tensorIndex (a s r : ℕ) : ℕ × ℕ := if r ≤ a - s then (r, s) else (a - s, s + (r - (a - s)))

/-! ### Congruences modulo `ϖ` -/

section Congruences

variable {A : Type*} [CommRing A] [Algebra A k] [IsLocalRing A] {ϖ : A}
  (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖq : algebraMap A k ϖ = q)

omit hq0 hq [IsLocalRing A] in
lemma smul_mem_smallSpan_of_inPow {M : Type*} [AddCommGroup M] [Module k M] {g : ℕ × ℕ → M}
    (hq0' : algebraMap A k ϖ ≠ 0) {c : k} (hc : InPow ϖ 0 c) {y : M}
    (hy : y ∈ smallSpan k ϖ g) : c • y ∈ smallSpan k ϖ g := by
  induction hy using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨κ, p, hκ, rfl⟩ := hy
    rw [smul_smul]
    exact smul_mem_smallSpan g (by simpa using hc.mul hq0' hκ) p
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz

omit hq0 hq [IsLocalRing A] in
lemma inPow_coord_of_mem_smallSpan (ξ : Module.Dual k (M₁ ⊗[k] M₂))
    (hξ : ∀ p : ℕ × ℕ, ξ (V₁.dF p.1 η ⊗ₜ[k] V₂.dF p.2 ζ) = 0 ∨
      ξ (V₁.dF p.1 η ⊗ₜ[k] V₂.dF p.2 ζ) = 1) {y : M₁ ⊗[k] M₂}
    (hy : y ∈ smallSpan k ϖ (fun p ↦ V₁.dF p.1 η ⊗ₜ[k] V₂.dF p.2 ζ)) :
    InPow ϖ 1 (ξ y) := by
  induction hy using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨κ, p, hκ, rfl⟩ := hy
    rw [map_smul, smul_eq_mul]
    rcases hξ p with h | h <;> rw [h]
    · simpa using inPow_zero (ϖ := ϖ) (k := k) 1
    · simpa using hκ
  | zero => simpa using inPow_zero (ϖ := ϖ) (k := k) 1
  | add y z _ _ hy hz => rw [map_add]; exact hy.add hz

include hϖ hϖq in
/-- The coefficient `e` with `F^{(ℓ)} w_s = e z_s` lies in `1 + ϖ A`. -/
theorem isOnePow_of_tensor_dF_tensorHigh_top (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b)
    (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0) {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) {e : k}
    (he : (tensor V₁ V₂ hq0 hq).dF (a + b - 2 * s) (tensorHigh V₁ V₂ a b η ζ s) =
      e • tensorLow V₁ V₂ a b η ζ s) : IsOnePow ϖ 0 e := by
  classical
  set T := tensor V₁ V₂ hq0 hq
  -- `F^{(a-s)} w_s = e E^{(b-s)} z_s`
  have hw : tensorHigh V₁ V₂ a b η ζ s ∈ T.wt ((a + b - 2 * s : ℕ) : ℤ) := by
    convert tensorHigh_mem_wt V₁ V₂ hq0 hq hη hζ s using 2
    push_cast [show 2 * s ≤ a + b by omega]
    ring
  have hwE : T.E (tensorHigh V₁ V₂ a b η ζ s) = 0 :=
    tensor_E_tensorHigh V₁ V₂ hq0 hq hη hζ hsa
  have hrel : T.dF (a - s) (tensorHigh V₁ V₂ a b η ζ s) =
      e • T.dE (b - s) (tensorLow V₁ V₂ a b η ζ s) := by
    rw [← map_smul, ← he, dE_dF_of_primitive hq0 hq hw hwE (show b - s ≤ a + b - 2 * s by omega)
      le_rfl, show a + b - 2 * s - (a + b - 2 * s) + (b - s) = b - s by omega, qBinomial_self,
      one_smul, show a + b - 2 * s - (b - s) = a - s by omega]
  have hA := tensor_dF_tensorHigh_sub V₁ V₂ hq0 hq hϖ hϖq hη (ζ := ζ) hsa hsb (r := a - s) le_rfl
  have hB := tensor_dE_tensorLow_sub V₁ V₂ hq0 hq hϖ hϖq hη hζ hsa hsb (t := b - s) le_rfl
  rw [show b - (b - s) = s by omega] at hB
  -- the coordinate at `u_{a-s} ⊗ v_s`
  obtain ⟨ξ, hξ⟩ := exists_coord (linearIndependent_tmul_dF hq0 hq hη hζ hη0 hζ0)
  set i₀ : Fin (a + 1) × Fin (b + 1) := (⟨a - s, by omega⟩, ⟨s, by omega⟩)
  have hξp : ∀ p : ℕ × ℕ, ξ i₀ (V₁.dF p.1 η ⊗ₜ[k] V₂.dF p.2 ζ) = 0 ∨
      ξ i₀ (V₁.dF p.1 η ⊗ₜ[k] V₂.dF p.2 ζ) = 1 := by
    rintro ⟨i, j⟩
    by_cases hi : i ≤ a
    · by_cases hj : j ≤ b
      · have := hξ i₀ (⟨i, by omega⟩, ⟨j, by omega⟩)
        simp only at this
        rw [this]
        split_ifs <;> simp
      · left
        rw [dF_eq_zero_of_primitive hq0 hq hζ.1 hζ.2 (by push_cast; omega), tmul_zero, map_zero]
    · left
      rw [dF_eq_zero_of_primitive hq0 hq hη.1 hη.2 (by push_cast; omega), zero_tmul, map_zero]
  have h0 : ξ i₀ (V₁.dF (a - s) η ⊗ₜ[k] V₂.dF s ζ) = 1 := by
    have := hξ i₀ i₀
    simpa [i₀] using this
  have h1 := inPow_coord_of_mem_smallSpan V₁ V₂ (ξ i₀) hξp hA
  have h2 := inPow_coord_of_mem_smallSpan V₁ V₂ (ξ i₀) hξp hB
  rw [map_sub, h0] at h1 h2
  rw [hrel, map_smul, smul_eq_mul] at h1
  subst hϖq
  obtain ⟨α₁, hα₁⟩ := h1
  obtain ⟨α₂, hα₂⟩ := h2
  -- `e (1 + σ₂) = 1 + σ₁`
  have hd : ξ i₀ (T.dE (b - s) (tensorLow V₁ V₂ a b η ζ s)) =
      algebraMap A k (1 + ϖ * α₂) := by
    rw [zpow_one] at hα₂
    rw [map_add, map_one, map_mul]
    linear_combination hα₂
  have hn : e * ξ i₀ (T.dE (b - s) (tensorLow V₁ V₂ a b η ζ s)) =
      algebraMap A k (1 + ϖ * α₁) := by
    rw [zpow_one] at hα₁
    rw [map_add, map_one, map_mul]
    linear_combination hα₁
  have hne : algebraMap A k (1 + ϖ * α₂) ≠ 0 := by
    obtain ⟨u, hu⟩ := isUnit_one_add_mul hϖ α₂
    rw [← hu]
    intro h0
    have := congrArg (algebraMap A k) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have he' : e = algebraMap A k (1 + ϖ * α₁) / algebraMap A k (1 + ϖ * α₂) := by
    rw [eq_div_iff hne, ← hd, hn]
  rw [he']
  simpa using (show IsOnePow ϖ 0 (algebraMap A k (1 + ϖ * α₁)) from ⟨α₁, by simp⟩).div hϖ
    hq0 (show IsOnePow ϖ 0 (algebraMap A k (1 + ϖ * α₂)) from ⟨α₂, by simp⟩)

include hϖ hϖq in
/-- Modulo `ϖ`, the string `F^{(r)} w_s` (`r ≤ a + b - 2s`) reduces to `u_r ⊗ v_s` for
`r ≤ a - s` and to `u_{a-s} ⊗ v_{s + r - (a - s)}` for `r ≥ a - s` ([HK] (4.12)). -/
theorem tensor_dF_tensorHigh_sub_tensorIndex (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b)
    (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0) {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) {r : ℕ}
    (hr : r ≤ a + b - 2 * s) :
    (tensor V₁ V₂ hq0 hq).dF r (tensorHigh V₁ V₂ a b η ζ s) -
      V₁.dF (tensorIndex a s r).1 η ⊗ₜ[k] V₂.dF (tensorIndex a s r).2 ζ ∈
      smallSpan k ϖ (fun p ↦ V₁.dF p.1 η ⊗ₜ[k] V₂.dF p.2 ζ) := by
  by_cases h : r ≤ a - s
  · simp only [tensorIndex, h, ↓reduceIte]
    exact tensor_dF_tensorHigh_sub V₁ V₂ hq0 hq hϖ hϖq hη hsa hsb h
  simp only [tensorIndex, h, ↓reduceIte]
  set T := tensor V₁ V₂ hq0 hq
  obtain ⟨e, he⟩ := exists_tensor_dF_tensorHigh_top V₁ V₂ hq0 hq hη hζ hη0 hζ0 hsa hsb
  have he1 := isOnePow_of_tensor_dF_tensorHigh_top V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 hsa hsb he
  have hw : tensorHigh V₁ V₂ a b η ζ s ∈ T.wt ((a + b - 2 * s : ℕ) : ℤ) := by
    convert tensorHigh_mem_wt V₁ V₂ hq0 hq hη hζ s using 2
    push_cast [show 2 * s ≤ a + b by omega]
    ring
  have hwE : T.E (tensorHigh V₁ V₂ a b η ζ s) = 0 :=
    tensor_E_tensorHigh V₁ V₂ hq0 hq hη hζ hsa
  set t := a + b - 2 * s - r
  have hrel : T.dF r (tensorHigh V₁ V₂ a b η ζ s) =
      e • T.dE t (tensorLow V₁ V₂ a b η ζ s) := by
    rw [← map_smul, ← he, dE_dF_of_primitive hq0 hq hw hwE (show t ≤ a + b - 2 * s by omega)
      le_rfl, show a + b - 2 * s - (a + b - 2 * s) + t = t by omega, qBinomial_self,
      one_smul, show a + b - 2 * s - t = r by omega]
  have hB := tensor_dE_tensorLow_sub V₁ V₂ hq0 hq hϖ hϖq hη hζ hsa hsb (t := t) (by omega)
  rw [show b - t = s + (r - (a - s)) by omega] at hB
  rw [hrel, show e • T.dE t (tensorLow V₁ V₂ a b η ζ s) -
      V₁.dF (a - s) η ⊗ₜ[k] V₂.dF (s + (r - (a - s))) ζ =
      e • (T.dE t (tensorLow V₁ V₂ a b η ζ s) -
        V₁.dF (a - s) η ⊗ₜ[k] V₂.dF (s + (r - (a - s))) ζ) +
      (e - 1) • (V₁.dF (a - s) η ⊗ₜ[k] V₂.dF (s + (r - (a - s))) ζ) by
    rw [smul_sub, sub_smul, one_smul]; abel]
  subst hϖq
  exact add_mem (smul_mem_smallSpan_of_inPow hq0 he1.inPow hB)
    (smul_mem_smallSpan _ he1.sub_one ((a - s, s + (r - (a - s))) : ℕ × ℕ))

end Congruences

end IntegrableSl2

end LieLean.QuantumGroup
