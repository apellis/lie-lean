/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityProj
import LieLean.Algebra.QuantumGroup.LusztigF.Reverse

/-!
# Polarization of `(L(∞), B(∞))`

Lusztig's form `( , )` on `'f` vanishes on the Serre ideal `J`, so it descends to a symmetric
bilinear form on `U⁻ = 'f/J` (`GrandLoop.formU`). With `e'ᵢ = ᵢr` it satisfies
`(fᵢ u, w) = (θᵢ, θᵢ) (u, e'ᵢ w)` (`GrandLoop.formU_f`, [Lus] 1.2.13), and on string vectors
`(fᵢ^{(r)} x, fᵢ^{(s)} y) = δᵣₛ cᵣ (x, y)` for `x, y ∈ ker e'ᵢ` with `cᵣ ∈ 1 + ϖ A`
(`GrandLoop.formU_df_df`). Hence ([Kas91] Prop. 5.1.2, [Jan] 10.19–10.20):

* `(L(∞), L(∞)) ⊆ A` (`GrandLoop.formU_mem`) and `(f̃ᵢ u, w) ≡ (u, ẽᵢ w)` modulo `ϖ A` for
  `u, w ∈ L(∞)` (`GrandLoop.formU_kF_sub_kE_mem`);
* `B(∞)` is orthonormal modulo `ϖ` (`GrandLoop.formU_fWi_fWi`).

The string components of elements of `L(∞)` lie in `L(∞)` (`GrandLoop.comp_mem_latInf`,
[Jan] 10.10 (3)).

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), §5.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.16–10.20 (finite type).
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.13.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### The form on `U⁻` -/

section Form

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

omit [CharZero k] in
lemma form_eq_zero_of_mem_left {x : LusztigF k I} (hx : x ∈ serreSubmodule D v)
    (y : LusztigF k I) : form D v x y = 0 :=
  (mem_radical_iff D v).1 (serreIdeal_le_radical (NeZero.ne v) hv' (mem_serreSubmodule.1 hx)) y

omit [CharZero k] in
lemma form_eq_zero_of_mem_right (x : LusztigF k I) {y : LusztigF k I}
    (hy : y ∈ serreSubmodule D v) : form D v x y = 0 := by
  rw [form_comm]; exact form_eq_zero_of_mem_left hv' hy x

omit [CharZero k] in
/-- `y ↦ (x, y)` on `U⁻`. -/
def formAux : LusztigF k I →ₗ[k] (Um D v →ₗ[k] k) where
  toFun x := (serreSubmodule D v).liftQ (form D v x) fun y hy ↦
    form_eq_zero_of_mem_right hv' x hy
  map_add' x x' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.add_apply,
      Submodule.liftQ_apply, map_add]
    rfl
  map_smul' c x := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply,
      Submodule.liftQ_apply, map_smul, RingHom.id_apply]
    rfl

omit [CharZero k] in
/-- Lusztig's form on `U⁻ = 'f/J`. -/
def formU : LinearMap.BilinForm k (Um D v) :=
  (serreSubmodule D v).liftQ (formAux hv') fun x hx ↦ by
    rw [LinearMap.mem_ker]
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y ↦ ?_)
    exact form_eq_zero_of_mem_left hv' hx y

omit [CharZero k] in
lemma formU_mk (x y : LusztigF k I) :
    formU (D := D) hv' (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = form D v x y := rfl

omit [CharZero k] in
lemma formU_comm (u w : Um D v) : formU hv' u w = formU hv' w u := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact form_comm D v x y

omit [CharZero k] in
/-- `(fᵢ u, w) = (θᵢ, θᵢ) (u, e'ᵢ w)`. -/
lemma formU_f (i : I) (u w : Um D v) :
    formU hv' (NegativePart.f D v i u) w = thetaNorm D v i *
      formU hv' u (NegativePart.e D v (NeZero.ne v) hv' i w) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact form_θ_mul D v i x y

end Form

/-! ### Strings -/

section Strings

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- The boson structure of `U⁻` at `i` (`q = vᵢ⁻¹`). -/
abbrev bos (i : I) : BosonModule (v ^ D.d i)⁻¹ (Um D v) :=
  NegativePart.boson D v (NeZero.ne v) hv' i

omit [CharZero k] in
lemma df_succ (i : I) (n : ℕ) (m : Um D v) :
    (bos (D := D) hv' i).df (n + 1) m =
      (qInt (v ^ D.d i)⁻¹ (n + 1))⁻¹ • NegativePart.f D v i ((bos (D := D) hv' i).df n m) := by
  rw [BosonModule.df_apply, BosonModule.df_apply, map_smul, smul_smul, qFactorial_succ, mul_inv,
    pow_succ', Module.End.mul_apply]
  rfl

variable (D v) in
/-- `cᵣ = ∏_{m < r} [m+1]⁻¹ (θᵢ, θᵢ) vᵢ^m`. -/
def coefU (i : I) : ℕ → k
  | 0 => 1
  | r + 1 => coefU i r * ((qInt (v ^ D.d i)⁻¹ (r + 1))⁻¹ * thetaNorm D v i * ((v ^ D.d i) ^ r))

omit [CharZero k] in
/-- **`(fᵢ^{(r)} x, fᵢ^{(s)} y) = δᵣₛ cᵣ (x, y)`** for `x, y ∈ ker e'ᵢ`. -/
theorem formU_df_df (i : I) {x y : Um D v} (hx : (bos (D := D) hv' i).e x = 0)
    (hy : (bos (D := D) hv' i).e y = 0) :
    ∀ r s, formU hv' ((bos hv' i).df r x) ((bos hv' i).df s y) =
      if r = s then coefU D v i r * formU hv' x y else 0 := by
  have hq0 : (v ^ D.d i)⁻¹ ≠ 0 := NegativePart.pow_d_ne_zero (NeZero.ne v) i
  have hq := NegativePart.pow_d_ne_one (D := D) hv' i
  -- `(f^{(r+1)} a, w) = [r+1]⁻¹ (θᵢ,θᵢ) (f^{(r)} a, e w)`
  have step : ∀ r (a w : Um D v), formU hv' ((bos hv' i).df (r + 1) a) w =
      (qInt (v ^ D.d i)⁻¹ (r + 1))⁻¹ * thetaNorm D v i *
        formU hv' ((bos hv' i).df r a) ((bos hv' i).e w) := by
    intro r a w
    rw [df_succ, map_smul, LinearMap.smul_apply, formU_f, smul_eq_mul, mul_assoc]
    rfl
  intro r
  induction r with
  | zero =>
    intro s
    rcases s with _ | s
    · simp [coefU]
    · rw [formU_comm, step, BosonModule.df_zero, hx, map_zero, mul_zero]; simp
  | succ r ih =>
    intro s
    rcases s with _ | s
    · rw [step, BosonModule.df_zero, hy, map_zero, mul_zero]; simp
    · rw [step, BosonModule.e_df_succ hq0 hq hy, map_smul, smul_eq_mul, ih s, inv_inv]
      by_cases h : r = s
      · subst h; simp [coefU]; ring
      · simp [h]

end Strings

/-! ### Components -/

section Components

variable (hvt) in
/-- The `n`-th `i`-string component of `u ∈ U⁻`. -/
abbrev comp (i : I) (n : ℕ) : Module.End k (Um D v) :=
  (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).component
    (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) n

lemma e_comp (i : I) (n : ℕ) (u : Um D v) :
    (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (comp hvt i n u) = 0 :=
  BosonModule.e_component _ _ n u

lemma exists_sum_comp (i : I) (u : Um D v) :
    ∃ N, (∀ n, N ≤ n → comp (D := D) hvt i n u = 0) ∧
      u = ∑ n ∈ range N, (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df n
        (comp hvt i n u) :=
  BosonModule.exists_sum_component _ _ u

/-- `(ẽᵢ u)ₙ = uₙ₊₁`. -/
lemma comp_kE (i : I) (n : ℕ) (u : Um D v) :
    comp (D := D) hvt i n (kE hvt i u) = comp hvt i (n + 1) u := by
  have hq0 := NegativePart.pow_d_ne_zero (D := D) (NeZero.ne v) i
  have hq := NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i
  have key : comp (D := D) hvt i n ∘ₗ kE hvt i = comp hvt i (n + 1) :=
    BosonModule.ext_df (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) i) hq0 hq
      fun j x hx ↦ by
        rcases j with _ | j
        · simp only [LinearMap.comp_apply, BosonModule.df_zero]
          rw [show kE hvt i x = 0 from BosonModule.eTilde_of_ker hq0 hq hx, map_zero]
          have := BosonModule.component_df hq0 hq hx 0 (n + 1)
          simpa using this.symm
        · simp only [LinearMap.comp_apply]
          rw [show kE hvt i ((bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df (j + 1) x) =
            (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df j x from
              BosonModule.eTilde_df_succ hq0 hq hx j,
            BosonModule.component_df hq0 hq hx, BosonModule.component_df hq0 hq hx]
          simp
  exact LinearMap.congr_fun key u

/-- `(f̃ᵢ u)ₙ₊₁ = uₙ`. -/
lemma comp_succ_kF (i : I) (n : ℕ) (u : Um D v) :
    comp (D := D) hvt i (n + 1) (kF hvt i u) = comp hvt i n u := by
  have hq0 := NegativePart.pow_d_ne_zero (D := D) (NeZero.ne v) i
  have hq := NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i
  have key : comp (D := D) hvt i (n + 1) ∘ₗ kF hvt i = comp hvt i n :=
    BosonModule.ext_df (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) i) hq0 hq
      fun j x hx ↦ by
        simp only [LinearMap.comp_apply]
        rw [show kF hvt i ((bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df j x) =
          (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df (j + 1) x from
            BosonModule.fTilde_df hq0 hq hx j,
          BosonModule.component_df hq0 hq hx, BosonModule.component_df hq0 hq hx]
        simp
  exact LinearMap.congr_fun key u

/-- `(f̃ᵢ u)₀ = 0`. -/
lemma comp_zero_kF (i : I) (u : Um D v) : comp (D := D) hvt i 0 (kF hvt i u) = 0 := by
  have hq0 := NegativePart.pow_d_ne_zero (D := D) (NeZero.ne v) i
  have hq := NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i
  have key : comp (D := D) hvt i 0 ∘ₗ kF hvt i = 0 :=
    BosonModule.ext_df (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) i) hq0 hq
      fun j x hx ↦ by
        simp only [LinearMap.comp_apply, LinearMap.zero_apply]
        rw [show kF hvt i ((bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df j x) =
          (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df (j + 1) x from
            BosonModule.fTilde_df hq0 hq hx j,
          BosonModule.component_df hq0 hq hx]
        simp
  exact LinearMap.congr_fun key u

/-- `u = Σ_{n < N} fᵢ^{(n)} uₙ` for any `N` beyond the last nonzero component. -/
lemma eq_sum_comp (i : I) (u : Um D v) {N : ℕ} (hN : ∀ n, N ≤ n → comp (D := D) hvt i n u = 0) :
    u = ∑ n ∈ range N, (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df n
      (comp hvt i n u) := by
  obtain ⟨N₀, hN₀, hu⟩ := exists_sum_comp (hvt := hvt) i u
  conv_lhs => rw [hu]
  rcases le_total N₀ N with h | h
  · refine sum_subset (range_subset_range.2 h) fun n _ hn ↦ ?_
    rw [hN₀ n (by simpa using hn), map_zero]
  · refine (sum_subset (range_subset_range.2 h) fun n _ hn ↦ ?_).symm
    rw [hN n (by simpa using hn), map_zero]

/-- `(u, w) = Σₙ cₙ (uₙ, wₙ)`. -/
lemma formU_eq_sum (i : I) (u w : Um D v) {N : ℕ}
    (hu : ∀ n, N ≤ n → comp (D := D) hvt i n u = 0)
    (hw : ∀ n, N ≤ n → comp (D := D) hvt i n w = 0) :
    formU (pow_ne_one_of_transcendental' hvt) u w =
      ∑ r ∈ range N, coefU D v i r *
        formU (pow_ne_one_of_transcendental' hvt) (comp hvt i r u) (comp hvt i r w) := by
  conv_lhs => rw [eq_sum_comp i u hu, eq_sum_comp i w hw]
  simp only [map_sum, LinearMap.sum_apply]
  simp_rw [formU_df_df (pow_ne_one_of_transcendental' hvt) i (e_comp i _ u) (e_comp i _ w)]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  refine sum_congr rfl fun r hr ↦ ?_
  simp [Finset.mem_range.1 hr]

/-- `(f̃ᵢ u, w) = Σₙ cₙ₊₁ (uₙ, wₙ₊₁)`. -/
lemma formU_kF_eq_sum (i : I) (u w : Um D v) {N : ℕ}
    (hu : ∀ n, N ≤ n → comp (D := D) hvt i n u = 0)
    (hw : ∀ n, N ≤ n → comp (D := D) hvt i n w = 0) :
    formU (pow_ne_one_of_transcendental' hvt) (kF hvt i u) w =
      ∑ r ∈ range N, coefU D v i (r + 1) *
        formU (pow_ne_one_of_transcendental' hvt) (comp hvt i r u) (comp hvt i (r + 1) w) := by
  have hFu : ∀ n, N + 1 ≤ n → comp (D := D) hvt i n (kF hvt i u) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [comp_succ_kF]; exact hu m (by omega)
  rw [formU_eq_sum i _ w hFu (fun n hn ↦ hw n (by omega)), sum_range_succ', comp_zero_kF,
    map_zero, LinearMap.zero_apply, mul_zero, add_zero]
  simp_rw [comp_succ_kF]

/-- `(u, ẽᵢ w) = Σₙ cₙ (uₙ, wₙ₊₁)`. -/
lemma formU_kE_eq_sum (i : I) (u w : Um D v) {N : ℕ}
    (hu : ∀ n, N ≤ n → comp (D := D) hvt i n u = 0)
    (hw : ∀ n, N ≤ n → comp (D := D) hvt i n w = 0) :
    formU (pow_ne_one_of_transcendental' hvt) u (kE hvt i w) =
      ∑ r ∈ range N, coefU D v i r *
        formU (pow_ne_one_of_transcendental' hvt) (comp hvt i r u) (comp hvt i (r + 1) w) := by
  rw [formU_eq_sum i u _ hu (fun n hn ↦ by rw [comp_kE]; exact hw _ (by omega))]
  simp_rw [comp_kE]

end Components

section Pol

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
/-- The string components of an element of `L(∞)` lie in `L(∞)` ([Jan] 10.10 (3)). -/
lemma comp_mem_latInf (i : I) (n : ℕ) {u : Um D v} (hu : u ∈ latInf hvt A) :
    comp hvt i n u ∈ latInf hvt A := by
  induction n generalizing u with
  | zero =>
    have := BosonModule.fTilde_eTilde_add_component
      (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) i)
      (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
      (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) u
    have h0 : comp hvt i 0 u = u - kF hvt i (kE hvt i u) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact this
    rw [h0]
    exact sub_mem hu (kashiwaraF_mem_latInf' i _
      (kashiwaraE_mem_latInf' (hR := hR) hinj hϖ hϖv hk hfund i _ hu))
  | succ n ih =>
    rw [← comp_kE]
    exact ih (kashiwaraE_mem_latInf' (hR := hR) hinj hϖ hϖv hk hfund i _ hu)

omit hinj hk hfund [Finite I] [DecidableEq I] in
/-- `cᵣ ∈ 1 + ϖ A`. -/
lemma exists_coefU (i : I) : ∀ r, ∃ a : A, coefU D v i r = algebraMap A k (1 + ϖ * a) := by
  have hd := D.d_pos i
  set w := ϖ ^ D.d i with hw_def
  have hw : w ∈ IsLocalRing.maximalIdeal A := Ideal.pow_mem_of_mem _ hϖ _ hd
  have hwv : algebraMap A k w = (v ^ D.d i)⁻¹ := by rw [map_pow, hϖv, inv_pow]
  have hw0 : algebraMap A k w ≠ 0 := by rw [hwv]; exact inv_ne_zero (pow_ne_zero _ (NeZero.ne v))
  have hconv : ∀ κ : k, IsOnePow w 0 κ → ∃ a : A, κ = algebraMap A k (1 + ϖ * a) := by
    rintro κ ⟨a, rfl⟩
    obtain ⟨d', hd'⟩ : ∃ d', D.d i = d' + 1 := ⟨D.d i - 1, by omega⟩
    refine ⟨ϖ ^ d' * a, ?_⟩
    rw [zpow_zero, one_mul, hw_def, hd', pow_succ]
    ring_nf
  intro r
  induction r with
  | zero => exact ⟨0, by simp [coefU]⟩
  | succ r ih =>
    obtain ⟨a, ha⟩ := ih
    have h1 : IsOnePow w r (qInt (v ^ D.d i)⁻¹ (r + 1))⁻¹ := by
      rw [← hwv]
      have := (isOnePow_qInt hw0 (Nat.succ_pos r)).inv hw
      convert this using 1; push_cast; ring
    have h2 : IsOnePow w 0 (thetaNorm D v i) := by
      have : IsOnePow w 0 (1 - (v ^ D.d i)⁻¹ ^ 2) := ⟨-w, by
        rw [zpow_zero, one_mul, map_add, map_one, map_mul, map_neg, hwv]; ring⟩
      simpa [thetaNorm] using this.inv hw
    have h3 : IsOnePow w (-(r : ℤ)) ((v ^ D.d i) ^ r) := by
      convert isOnePow_zpow (ϖ := w) (-(r : ℤ)) using 1
      rw [hwv, inv_zpow', neg_neg, zpow_natCast]
    obtain ⟨b, hb⟩ := hconv _ (by simpa using (h1.mul hw0 h2).mul hw0 h3)
    refine ⟨a + b + ϖ * a * b, ?_⟩
    rw [coefU, ha, hb, ← map_mul]
    congr 1; ring

include hR in
/-- **[Kas91] Prop. 5.1.2 (i)**: `(u, w) ∈ A` for `u, w ∈ L(∞)` of one weight. -/
theorem formU_mem_of_mem_Uw : ∀ n (ν : I →₀ ℕ), ν.degree = n → ∀ u w : Um D v,
    u ∈ latInf hvt A → u ∈ Uw D v ν → w ∈ latInf hvt A → w ∈ Uw D v ν →
    ∃ a : A, formU (pow_ne_one_of_transcendental' hvt) u w = algebraMap A k a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hν u w hu huw hw hww
  have hspan := mem_span_fWi_of_mem hu huw
  clear hu huw
  induction hspan using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by rw [map_add, LinearMap.add_apply, hx, hy, map_add]⟩
  | smul c a _ ha =>
    obtain ⟨x, hx⟩ := ha
    refine ⟨c * x, ?_⟩
    rw [← algebraMap_smul k c a, map_smul, LinearMap.smul_apply, hx, smul_eq_mul, map_mul]
  | mem u hu' =>
    obtain ⟨w₀, hw₀, rfl⟩ := hu'
    rcases w₀ with _ | ⟨i, w₁⟩
    · -- weight `0`
      have hν0 : ν = 0 := by simpa using hw₀.symm
      subst hν0
      have hwspan := mem_span_fWi_of_mem hw hww
      clear hw hww
      induction hwspan using Submodule.span_induction with
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hb
        exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
      | smul c a _ ha =>
        obtain ⟨x, hx⟩ := ha
        refine ⟨c * x, ?_⟩
        rw [← algebraMap_smul k c a, map_smul, hx, smul_eq_mul, map_mul]
      | mem w hw' =>
        obtain ⟨w₂, hw₂, rfl⟩ := hw'
        have : w₂ = [] := by
          refine List.eq_nil_of_length_eq_zero ?_
          rw [← degree_wordWeight, hw₂, map_zero]
        subst this
        exact ⟨1, by simp [fWi, formU_mk, map_one]⟩
    · -- `u = f̃ᵢ u'`
      set u' := fWi (D := D) hvt w₁
      have hu'L : u' ∈ latInf hvt A := NegativePart.fWord_mem_latticeInf _ _ w₁
      have hνi : 1 ≤ ν i := by
        rw [← hw₀, wordWeight_cons]; simp
      obtain ⟨N₁, hN₁, -⟩ := exists_sum_comp (hvt := hvt) i u'
      obtain ⟨N₂, hN₂, -⟩ := exists_sum_comp (hvt := hvt) i w
      have hf := formU_kF_eq_sum (hvt := hvt) i u' w (N := max N₁ N₂)
        (fun m hm ↦ hN₁ m (le_of_max_le_left hm)) (fun m hm ↦ hN₂ m (le_of_max_le_right hm))
      change ∃ a : A, formU (pow_ne_one_of_transcendental' hvt) (kF hvt i u') w = _
      rw [hf]
      have hterm : ∀ r, ∃ a : A, coefU D v i (r + 1) *
          formU (pow_ne_one_of_transcendental' hvt) (comp hvt i r u') (comp hvt i (r + 1) w) =
            algebraMap A k a := by
        intro r
        obtain ⟨c, hc⟩ := exists_coefU hϖ hϖv (D := D) i (r + 1)
        have hu'w : u' ∈ Uw D v (ν - Finsupp.single i 1) := by
          have := fWi_mem_Uw (D := D) (hvt := hvt) w₁
          convert this using 2
          rw [← hw₀, wordWeight_cons]; simp
        have h1 := component_mem_Uw (hvt := hvt) i hu'w r
        have h2 := component_mem_Uw (hvt := hvt) i hww (r + 1)
        have e : ν - Finsupp.single i 1 - Finsupp.single i r = ν - Finsupp.single i (r + 1) := by
          rw [tsub_tsub, ← Finsupp.single_add, add_comm]
        rw [e] at h1
        have hdeg : (ν - Finsupp.single i (r + 1)).degree < n := by
          have hle : Finsupp.single i (min (ν i) (r + 1)) ≤ ν := by
            intro l
            by_cases hl : l = i
            · subst hl; simp
            · simp [Ne.symm hl]
          have e2 : ν - Finsupp.single i (r + 1) = ν - Finsupp.single i (min (ν i) (r + 1)) := by
            ext l
            by_cases hl : l = i
            · subst hl; simp; omega
            · simp [Ne.symm hl]
          rw [e2, ← hν]
          have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
          rw [map_add, Finsupp.degree_single] at this
          omega
        obtain ⟨a, ha⟩ := ih _ hdeg _ rfl _ _ (comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i r
          hu'L) h1 (comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i (r + 1) hw) h2
        exact ⟨(1 + ϖ * c) * a, by rw [hc, ha, map_mul]⟩
      choose a ha using hterm
      exact ⟨∑ r ∈ range (max N₁ N₂), a r, by rw [map_sum]; exact sum_congr rfl fun r _ ↦ ha r⟩

include hR in
/-- **[Kas91] Prop. 5.1.2 (i)**: `(L(∞), L(∞)) ⊆ A`. -/
theorem formU_mem {u w : Um D v} (hu : u ∈ latInf hvt A) (hw : w ∈ latInf hvt A) :
    ∃ a : A, formU (pow_ne_one_of_transcendental' hvt) u w = algebraMap A k a := by
  induction hu using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by rw [map_add, LinearMap.add_apply, hx, hy, map_add]⟩
  | smul c a _ ha =>
    obtain ⟨x, hx⟩ := ha
    refine ⟨c * x, ?_⟩
    rw [← algebraMap_smul k c a, map_smul, LinearMap.smul_apply, hx, smul_eq_mul, map_mul]
  | mem u hu =>
    obtain ⟨w₁, rfl⟩ := hu
    induction hw using Submodule.span_induction with
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
    | smul c a _ ha =>
      obtain ⟨x, hx⟩ := ha
      refine ⟨c * x, ?_⟩
      rw [← algebraMap_smul k c a, map_smul, hx, smul_eq_mul, map_mul]
    | mem w hw =>
      obtain ⟨w₂, rfl⟩ := hw
      by_cases h : wordWeight w₁ = wordWeight w₂
      · exact formU_mem_of_mem_Uw (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund _ _ rfl _ _
          (NegativePart.fWord_mem_latticeInf _ _ w₁) (fWi_mem_Uw (hvt := hvt) w₁)
          (NegativePart.fWord_mem_latticeInf _ _ w₂) (h ▸ fWi_mem_Uw (hvt := hvt) w₂)
      · refine ⟨0, ?_⟩
        obtain ⟨y₁, hy₁, e₁⟩ := fWi_mem_Uw (D := D) (hvt := hvt) w₁
        obtain ⟨y₂, hy₂, e₂⟩ := fWi_mem_Uw (D := D) (hvt := hvt) w₂
        change formU _ (fWi hvt w₁) (fWi hvt w₂) = _
        rw [← e₁, ← e₂, Submodule.mkQ_apply, Submodule.mkQ_apply, formU_mk,
          form_eq_zero_of_ne D v h hy₁ hy₂, map_zero]

include hR in
/-- **[Kas91] Prop. 5.1.2 (ii)**: `(f̃ᵢ u, w) ≡ (u, ẽᵢ w)` modulo `ϖ A` for `u, w ∈ L(∞)`. -/
theorem formU_kF_sub_kE_mem (i : I) {u w : Um D v} (hu : u ∈ latInf hvt A)
    (hw : w ∈ latInf hvt A) :
    ∃ a : A, formU (pow_ne_one_of_transcendental' hvt) (kF hvt i u) w -
      formU (pow_ne_one_of_transcendental' hvt) u (kE hvt i w) = algebraMap A k (ϖ * a) := by
  obtain ⟨N₁, hN₁, -⟩ := exists_sum_comp (hvt := hvt) i u
  obtain ⟨N₂, hN₂, -⟩ := exists_sum_comp (hvt := hvt) i w
  rw [formU_kF_eq_sum (hvt := hvt) i u w (N := max N₁ N₂)
      (fun m hm ↦ hN₁ m (le_of_max_le_left hm)) (fun m hm ↦ hN₂ m (le_of_max_le_right hm)),
    formU_kE_eq_sum (hvt := hvt) i u w (N := max N₁ N₂)
      (fun m hm ↦ hN₁ m (le_of_max_le_left hm)) (fun m hm ↦ hN₂ m (le_of_max_le_right hm)),
    ← sum_sub_distrib]
  have hterm : ∀ r, ∃ a : A, coefU D v i (r + 1) *
      formU (pow_ne_one_of_transcendental' hvt) (comp hvt i r u) (comp hvt i (r + 1) w) -
      coefU D v i r *
      formU (pow_ne_one_of_transcendental' hvt) (comp hvt i r u) (comp hvt i (r + 1) w) =
        algebraMap A k (ϖ * a) := by
    intro r
    obtain ⟨c₁, hc₁⟩ := exists_coefU hϖ hϖv (D := D) i (r + 1)
    obtain ⟨c₀, hc₀⟩ := exists_coefU hϖ hϖv (D := D) i r
    obtain ⟨b, hb⟩ := formU_mem (hR := hR) hinj hϖ hϖv hk hfund
      (comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i r hu)
      (comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i (r + 1) hw)
    exact ⟨(c₁ - c₀) * b, by rw [hc₁, hc₀, hb, ← map_mul, ← map_mul, ← map_sub]; ring_nf⟩
  choose a ha using hterm
  exact ⟨∑ r ∈ range (max N₁ N₂), a r, by
    rw [mul_sum, map_sum]; exact sum_congr rfl fun r _ ↦ ha r⟩

include hR in
lemma formU_mem_smul {u w : Um D v} (hu : u ∈ latInf hvt A) (hw : w ∈ ϖ • latInf hvt A) :
    ∃ a : A, formU (pow_ne_one_of_transcendental' hvt) u w = algebraMap A k (ϖ * a) := by
  obtain ⟨w₀, hw₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
  obtain ⟨a, ha⟩ := formU_mem (hR := hR) hinj hϖ hϖv hk hfund hu hw₀
  refine ⟨a, ?_⟩
  rw [← algebraMap_smul k ϖ w₀, map_smul, ha, smul_eq_mul, map_mul]

include hR in
open scoped Classical in
/-- **[Kas91] Prop. 5.1.2 (iii)**: `B(∞)` is orthonormal modulo `ϖ`:
`(f̃_w 1, f̃_{w'} 1) ≡ 1` if the two classes agree and `≡ 0` otherwise. -/
theorem formU_fWi_fWi (w w' : List I) :
    ∃ a : A, formU (pow_ne_one_of_transcendental' hvt) (fWi (D := D) hvt w) (fWi hvt w') =
      (if fWi (D := D) hvt w - fWi hvt w' ∈ ϖ • latInf hvt A then 1 else 0) +
        algebraMap A k (ϖ * a) := by
  classical
  induction w generalizing w' with
  | nil =>
    by_cases hw' : w' = []
    · subst hw'
      refine ⟨0, ?_⟩
      simp [fWi, formU_mk]
    · have hne : wordWeight ([] : List I) ≠ wordWeight w' := by
        intro h
        refine hw' (List.eq_nil_of_length_eq_zero ?_)
        rw [← degree_wordWeight, ← h]; simp
      have hnot : fWi (D := D) hvt [] - fWi hvt w' ∉ ϖ • latInf hvt A := fun h ↦
        hne (wordWeight_eq_of_sub_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund h)
      refine ⟨0, ?_⟩
      obtain ⟨y₂, hy₂, e₂⟩ := fWi_mem_Uw (D := D) (hvt := hvt) w'
      rw [ite_eq_right hnot, ← e₂, map_mul, map_zero, mul_zero, add_zero]
      change form D v 1 y₂ = 0
      exact form_eq_zero_of_ne D v hne (by simpa using one_mem_weightSpace) hy₂
  | cons i w₀ ih =>
    obtain ⟨a₁, ha₁⟩ := formU_kF_sub_kE_mem (hR := hR) hinj hϖ hϖv hk hfund i
      (NegativePart.fWord_mem_latticeInf _ _ w₀) (NegativePart.fWord_mem_latticeInf _ _ w')
    change ∃ a : A, formU _ (kF hvt i (fWi hvt w₀)) (fWi hvt w') = _
    rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i w' with h | ⟨w₁, hw₁⟩
    · -- `ẽᵢ b' = 0`
      obtain ⟨a₂, ha₂⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund
        (NegativePart.fWord_mem_latticeInf _ _ w₀) h
      have hnot : fWi (D := D) hvt (i :: w₀) - fWi hvt w' ∉ ϖ • latInf hvt A := by
        intro h'
        have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i h'
        rw [map_sub, fWi, NegativePart.fWord_cons, NegativePart.kashiwaraE_kashiwaraF] at this
        exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀ (by simpa using add_mem this h)
      refine ⟨a₁ + a₂, ?_⟩
      rw [ite_eq_right hnot, zero_add, mul_add, map_add, ← ha₁, ← ha₂]
      ring
    · have h0 : kE (D := D) hvt i (fWi hvt w') ∉ ϖ • latInf hvt A := fun h' ↦
        fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₁ (by simpa using sub_mem h' hw₁)
      obtain ⟨a₂, ha₂⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund
        (NegativePart.fWord_mem_latticeInf _ _ w₀) hw₁
      obtain ⟨a₃, ha₃⟩ := ih w₁
      have hiff : fWi (D := D) hvt w₀ - fWi hvt w₁ ∈ ϖ • latInf hvt A ↔
          fWi (D := D) hvt (i :: w₀) - fWi hvt w' ∈ ϖ • latInf hvt A := by
        have hc := fWi_sub_mem_of_kE (hR := hR) hinj hϖ hϖv hk hfund i h0 hw₁
        constructor
        · intro h'
          have := LinearMap.map_mem_smul_of_mem ϖ
            (fun m hm ↦ kashiwaraF_mem_latInf' (hvt := hvt) (A := A) i m hm) h'
          rw [map_sub] at this
          have := sub_mem this hc
          convert this using 1
          simp only [fWi, NegativePart.fWord_cons]; abel
        · intro h'
          have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i h'
          rw [map_sub, fWi, NegativePart.fWord_cons, NegativePart.kashiwaraE_kashiwaraF] at this
          have := add_mem this hw₁
          convert this using 1; abel
      refine ⟨a₁ + a₂ + a₃, ?_⟩
      rw [← hiff]
      have e : formU (pow_ne_one_of_transcendental' hvt) (fWi hvt w₀)
          (kE (D := D) hvt i (fWi hvt w')) =
          formU (pow_ne_one_of_transcendental' hvt) (fWi hvt w₀)
            (kE (D := D) hvt i (fWi hvt w') - fWi hvt w₁) +
          formU (pow_ne_one_of_transcendental' hvt) (fWi (D := D) hvt w₀) (fWi hvt w₁) := by
        rw [map_sub]; ring
      rw [eq_add_of_sub_eq ha₁, e, ha₂, ha₃]
      simp only [map_add, map_mul]
      ring

end Pol

end GrandLoop

end LieLean.QuantumGroup
