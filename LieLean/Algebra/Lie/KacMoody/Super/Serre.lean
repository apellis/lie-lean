/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.InvariantFormLie

/-!
# The Serre relations hold in `G(A, τ)`

Let `A` be a symmetrizable generalized Cartan matrix and `p` a parity with `aᵢⱼ` even whenever
`eᵢ` is odd. The Serre elements `(ad eᵢ)^{1 - aᵢⱼ} eⱼ` and `(ad fᵢ)^{1 - aᵢⱼ} fⱼ` (`i ≠ j`) of
`G̃(A, τ)` lie in the maximal ideal `R`; equivalently the Serre relations hold in
`G(A, τ) = G̃(A, τ) / R` ([Kac78] §1.2, cf. [Kac] §3.3).

The proof follows the even case (`LieLean/Algebra/Lie/KacMoody/Serre.lean`), with two changes.

* An element `x ∈ G̃_β`, `β > 0`, with `[fₖ, x] = 0` for all `k` lies in `R`: here we use that `R`
  is the radical of the invariant form (`mem_maxIdeal_iff`). For `β` not simple, `G̃_{-β}` is
  spanned by the `[fₖ, y]`, and `([fₖ, y] | x) = ±(y | [fₖ, x]) = 0`; for `β = αₖ` we have
  `x ∈ K eₖ` and `[fₖ, eₖ] ≠ 0`.
* For odd `i` the `𝔰𝔩₂` identity is replaced by its super analogue: for `v` with `[fᵢ, v] = 0` and
  `[h, v] = λ(h) v`, `[fᵢ, (ad eᵢ)^{m+1} v] = c_m (ad eᵢ)^m v` with `c_m = λ(αᵢ^∨) + m` for `m`
  even and `c_m = m + 1` for `m` odd, since `[fᵢ, eᵢ] = αᵢ^∨` and `[fᵢ, [eᵢ, w]] = [αᵢ^∨, w] -
  [eᵢ, [fᵢ, w]]`. For `v = eⱼ` and `m = -aᵢⱼ` (even) the coefficient vanishes. This is where the
  parity condition on `A` enters.

For `k = j ≠ i` the bracket `[fⱼ, (ad eᵢ)^{1 - aᵢⱼ} eⱼ]` has weight `(1 - aᵢⱼ) αᵢ`; it vanishes
since `G̃_{nαᵢ} = 0` for `n ≥ 3` and for `n = 2`, `i` even, and directly for `aᵢⱼ = 0 = aⱼᵢ`.

## Main definitions

* `Matrix.Realization.SuperEnveloping.adE`, `adF`: the iterated super commutators
  `(ad eᵢ)ⁿ v`, `(ad fᵢ)ⁿ v`.
* `Matrix.Realization.SuperEnveloping.serreE`, `serreF`: the Serre elements.

## Main results

* `Matrix.Realization.SuperEnveloping.omega_mem_maxIdeal`: the Chevalley involution preserves `R`.
* `Matrix.Realization.SuperEnveloping.mem_maxIdeal_of_superBracket_f_eq_zero`: [Kac] Lemma 1.5 for
  `G̃(A, τ)`.
* `Matrix.Realization.SuperEnveloping.superBracket_f_serreE`: `[fₖ, (ad eᵢ)^{1 - aᵢⱼ} eⱼ] = 0`.
* `Matrix.Realization.SuperEnveloping.serreE_mem_maxIdeal`,
  `Matrix.Realization.SuperEnveloping.serreF_mem_maxIdeal`: the Serre relations hold in `G(A, τ)`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Lemma 1.5, §3.3.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2) [CharZero K]

namespace SuperEnveloping

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

/-! ### The Chevalley involution preserves `R` -/

/-- `ω(R) ⊆ R`. -/
theorem omega_mem_maxIdeal {r : 𝒰} (hr : r ∈ maxIdeal P p) : omega P p r ∈ maxIdeal P p := by
  have hR := isIdeal_maxIdeal P p
  have hωω' : ∀ x : 𝒰, omega P p (omega P p x) = parity P p x := fun x ↦
    DFunLike.congr_fun (omega_comp_omega P p) x
  have hωω : ∀ x : 𝒰, omega P p (omega P p (parity P p x)) = x := fun x ↦ by
    rw [hωω', parity_parity]
  let I : Submodule K 𝒰 := (maxIdeal P p).map (omega P p).toLinearMap
  have hI : IsIdeal P p I := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      exact omega_mem_gTilde P p (hR.le_gTilde hr)
    · rintro x hx _ ⟨r, hr, rfl⟩
      refine ⟨superBracket P p (omega P p (parity P p x)) r,
        hR.superBracket_mem _ (omega_mem_gTilde P p (parity_mem_gTilde P p hx)) r hr, ?_⟩
      simp only [AlgHom.toLinearMap_apply]
      rw [omega_superBracket, hωω]
  have hI0 : I ⊓ LinearMap.range (h P p) = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨⟨r, hr, rfl⟩, ⟨a, ha⟩⟩
    simp only [AlgHom.toLinearMap_apply] at ha ⊢
    have hr' : parity P p r ∈ maxIdeal P p ⊓ LinearMap.range (h P p) := by
      refine ⟨parity_mem_maxIdeal P p hr, -a, ?_⟩
      rw [map_neg, ← omega_h, ha, hωω']
    rw [maxIdeal_inf_range_h, Submodule.mem_bot] at hr'
    rw [Submodule.mem_bot, ← hωω r, hr']
    simp
  exact le_maxIdeal P p hI hI0 ⟨r, hr, rfl⟩

/-! ### Iterated super commutators -/

/-- The iterated super commutator `(ad eᵢ)ⁿ v`. -/
def adE (i : ι) (n : ℕ) (v : 𝒰) : 𝒰 := (superBracketRight P p (e P p i) ^ n) v

/-- The iterated super commutator `(ad fᵢ)ⁿ v`. -/
def adF (i : ι) (n : ℕ) (v : 𝒰) : 𝒰 := (superBracketRight P p (f P p i) ^ n) v

omit [CharZero K] in
@[simp] lemma adE_zero (i : ι) (v : 𝒰) : adE P p i 0 v = v := rfl

omit [CharZero K] in
lemma adE_succ (i : ι) (n : ℕ) (v : 𝒰) :
    adE P p i (n + 1) v = superBracket P p (e P p i) (adE P p i n v) := by
  rw [adE, pow_succ', Module.End.mul_apply]; rfl

omit [CharZero K] in
@[simp] lemma adF_zero (i : ι) (v : 𝒰) : adF P p i 0 v = v := rfl

omit [CharZero K] in
lemma adF_succ (i : ι) (n : ℕ) (v : 𝒰) :
    adF P p i (n + 1) v = superBracket P p (f P p i) (adF P p i n v) := by
  rw [adF, pow_succ', Module.End.mul_apply]; rfl

omit [CharZero K] in
lemma omega_adE (i : ι) (n : ℕ) (v : 𝒰) :
    omega P p (adE P p i n v) = adF P p i n (omega P p v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [adE_succ, adF_succ, omega_superBracket, omega_e, ih]

variable {P p}

lemma isHomog_adE (i : ι) (n : ℕ) {b : ZMod 2} {v : 𝒰} (hv : IsHomog P p b v) :
    IsHomog P p (n * p i + b) (adE P p i n v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [adE_succ, show ((n + 1 : ℕ) : ZMod 2) * p i + b = p i + (n * p i + b) by push_cast; ring]
    exact (isHomog_e P p i).superBracket ih

omit [CharZero K] in
lemma adE_mem_weightSpace (i : ι) (n : ℕ) {μ : Dual K H} {v : 𝒰} (hv : v ∈ weightSpace P p μ) :
    adE P p i n v ∈ weightSpace P p (μ + n • P.root i) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [adE_succ, succ_nsmul, ← add_assoc, add_comm _ (P.root i)]
    exact superBracket_mem_weightSpace (e_mem_weightSpace P p i) ih

lemma adE_mem_gTilde (i : ι) (n : ℕ) {v : 𝒰} (hv : v ∈ gTilde P p) :
    adE P p i n v ∈ gTilde P p := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [adE_succ]; exact superBracket_e_mem_gTilde P p i ih

/-! ### Brackets with `fₖ` -/

omit [CharZero K] in
lemma zSign_mul_self' (q : ZMod 2) : zSign K (q * q) = zSign K q := by
  rcases zmod_two_cases q with rfl | rfl <;> rfl

/-- `[fᵢ, [eᵢ, w]] = -(-1)^{p i} ν(αᵢ^∨) w + (-1)^{p i} [eᵢ, [fᵢ, w]]` for `w` of weight `ν`. -/
lemma superBracket_f_superBracket_e (i : ι) {c : ZMod 2} {ν : Dual K H} {w : 𝒰}
    (hw : IsHomog P p c w) (hwν : w ∈ weightSpace P p ν) :
    superBracket P p (f P p i) (superBracket P p (e P p i) w) =
      -((zSign K (p i) * ν (P.coroot i)) • w) +
        zSign K (p i) • superBracket P p (e P p i) (superBracket P p (f P p i) w) := by
  rw [superBracket_jacobi (isHomog_f P p i) (isHomog_e P p i) hw, superBracket_f_e,
    ite_eq_left rfl, superBracket_neg_left, superBracket_smul_left,
    superBracket_h_of_mem_weightSpace P p _ hwν, superSign_eq_zSign, zSign_mul_self',
    smul_smul]

/-- For `k ≠ i`, `fₖ` super-commutes with `eᵢ`, so `[fₖ, v] = 0` implies
`[fₖ, (ad eᵢ)ⁿ v] = 0`. -/
lemma superBracket_f_adE_of_ne {k i : ι} (hki : k ≠ i) (n : ℕ) {b : ZMod 2} {v : 𝒰}
    (hv : IsHomog P p b v) (hfv : superBracket P p (f P p k) v = 0) :
    superBracket P p (f P p k) (adE P p i n v) = 0 := by
  induction n with
  | zero => exact hfv
  | succ n ih =>
    rw [adE_succ, superBracket_jacobi (isHomog_f P p k) (isHomog_e P p i) (isHomog_adE i n hv),
      superBracket_f_e, ite_eq_right hki, smul_zero, neg_zero, superBracket_zero_left, ih,
      superBracket_zero_right, smul_zero, add_zero]

/-- The coefficient `c_m` of `[fᵢ, (ad eᵢ)^{m+1} v] = c_m (ad eᵢ)^m v`, for `λ = ⟨wt v, αᵢ^∨⟩`:
`-(m + 1)(λ + m)` for `eᵢ` even, and `λ + m` (`m` even), `m + 1` (`m` odd) for `eᵢ` odd. -/
def serreCoeff (q : ZMod 2) (c : K) (m : ℕ) : K :=
  if q = 1 then (if Even m then c + m else m + 1) else -((m + 1) * (c + m))

omit [CharZero K] in
lemma serreCoeff_zero (q : ZMod 2) (c : K) : serreCoeff q c 0 = -(zSign K q * c) := by
  rcases zmod_two_cases q with rfl | rfl <;> simp [serreCoeff, zSign]

omit [CharZero K] in
lemma serreCoeff_succ (q : ZMod 2) (c : K) (m : ℕ) :
    serreCoeff q c (m + 1) =
      -(zSign K q * (c + 2 * (m + 1 : ℕ))) + zSign K q * serreCoeff q c m := by
  rcases zmod_two_cases q with rfl | rfl
  · simp only [serreCoeff, zSign, zero_ne_one, ite_false, one_mul]
    push_cast; ring
  · rcases Nat.even_or_odd m with hm | hm
    · have hm' : ¬ Even (m + 1) := Nat.not_even_iff_odd.2 hm.add_one
      simp only [serreCoeff, zSign, ite_true, hm, hm', ite_false]
      push_cast; ring
    · have hm' : Even (m + 1) := hm.add_one
      have hm'' : ¬ Even m := Nat.not_even_iff_odd.2 hm
      simp only [serreCoeff, zSign, ite_true, hm', hm'', ite_false]
      push_cast; ring

/-- The super `𝔰𝔩₂` identity: for `v` of weight `μ` with `[fᵢ, v] = 0`,
`[fᵢ, (ad eᵢ)^{m+1} v] = c_m (ad eᵢ)^m v`. -/
lemma superBracket_f_adE_succ (hA : A.IsGeneralizedCartan) (i : ι) {b : ZMod 2} {μ : Dual K H}
    {v : 𝒰} (hv : IsHomog P p b v) (hvμ : v ∈ weightSpace P p μ)
    (hfv : superBracket P p (f P p i) v = 0) (m : ℕ) :
    superBracket P p (f P p i) (adE P p i (m + 1) v) =
      serreCoeff (p i) (μ (P.coroot i)) m • adE P p i m v := by
  induction m with
  | zero =>
    rw [adE_succ, adE_zero, superBracket_f_superBracket_e i hv hvμ, hfv, superBracket_zero_right,
      smul_zero, add_zero, serreCoeff_zero, neg_smul]
  | succ m ih =>
    rw [adE_succ, superBracket_f_superBracket_e i (isHomog_adE i (m + 1) hv)
      (adE_mem_weightSpace i (m + 1) hvμ), ih, superBracket_smul_right, ← adE_succ, smul_smul,
      ← neg_smul, ← add_smul, serreCoeff_succ]
    congr 1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, P.root_coroot, hA.diag, nsmul_eq_mul]
    push_cast; ring

/-! ### The Serre elements -/

variable (P p) in
/-- The positive Serre element `(ad eᵢ)^{1 - aᵢⱼ} eⱼ`. -/
def serreE (i j : ι) : 𝒰 := adE P p i ((-A i j).toNat + 1) (e P p j)

variable (P p) in
/-- The negative Serre element `(ad fᵢ)^{1 - aᵢⱼ} fⱼ`. -/
def serreF (i j : ι) : 𝒰 := adF P p i ((-A i j).toNat + 1) (f P p j)

omit [CharZero K] in
lemma omega_serreE (i j : ι) : omega P p (serreE P p i j) = serreF P p i j := by
  rw [serreE, omega_adE, omega_e, serreF]

lemma serreE_mem_gTilde (i j : ι) : serreE P p i j ∈ gTilde P p :=
  adE_mem_gTilde i _ (nPlus_le_gTilde P p (e_mem_nPlus P p j))

omit [CharZero K] in
lemma serreE_mem_weightSpace (i j : ι) :
    serreE P p i j ∈ weightSpace P p (P.root j + ((-A i j).toNat + 1) • P.root i) :=
  adE_mem_weightSpace i _ (e_mem_weightSpace P p j)

omit [CharZero K] [DecidableEq ι] in
lemma serreE_weight_mem_posWeights {i j : ι} (hij : i ≠ j) (n : ℕ) :
    P.root j + n • P.root i ∈ P.posWeights := by
  classical
  refine ⟨Pi.single j 1 + n • Pi.single i 1, ⟨?_, fun h0 ↦ ?_⟩, by
    rw [map_add, map_nsmul, P.rootOf_single, P.rootOf_single]⟩
  · exact add_nonneg (Pi.single_nonneg.2 zero_le_one)
      (nsmul_nonneg (Pi.single_nonneg.2 zero_le_one) n)
  · have := congr_fun h0 j
    simp [hij.symm] at this

/-- `[fₖ, (ad eᵢ)^{1 - aᵢⱼ} eⱼ] = 0` for all `k` ([Kac78] §1.2, cf. [Kac] §3.3). -/
theorem superBracket_f_serreE (hA : A.IsGeneralizedCartan) (hp : A.IsSuperAdmissible p)
    {i j : ι} (hij : i ≠ j) (k : ι) : superBracket P p (f P p k) (serreE P p i j) = 0 := by
  have hn : ((-A i j).toNat : ℤ) = -A i j := Int.toNat_of_nonneg (by
    linarith [hA.offDiag_nonpos i j hij])
  by_cases hki : k = i
  · subst hki
    rw [serreE, superBracket_f_adE_succ hA k (isHomog_e P p j) (e_mem_weightSpace P p j)
      (by rw [superBracket_f_e, ite_eq_right hij, smul_zero, neg_zero]), P.root_coroot]
    have hc : serreCoeff (p k) (A k j : K) (-A k j).toNat = 0 := by
      have hn' : (((-A k j).toNat : ℕ) : K) = -(A k j : K) := by exact_mod_cast hn
      unfold serreCoeff
      split_ifs with hk he
      · rw [hn']; ring
      · exact absurd (by
          obtain ⟨r, hr⟩ := hp k j hk
          exact ⟨(-r).toNat, by omega⟩) he
      · rw [hn']; ring
    rw [hc, zero_smul]
  by_cases hkj : k = j
  · subst hkj
    set n := (-A i k).toNat with hn_def
    have hw : superBracket P p (f P p k) (serreE P p i k) ∈
        weightSpace P p ((n + 1) • P.root i) := by
      have := superBracket_mem_weightSpace (f_mem_weightSpace P p k) (serreE_mem_weightSpace i k)
      rwa [neg_add_cancel_left] at this
    have hG : superBracket P p (f P p k) (serreE P p i k) ∈ gTilde P p :=
      superBracket_f_mem_gTilde P p k (serreE_mem_gTilde i k)
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases Nat.lt_or_ge n 1 with h1 | h1
      · -- `aᵢⱼ = 0`, so `aⱼᵢ = 0` and `[fⱼ, [eᵢ, eⱼ]] = ±[eᵢ, hⱼ] = 0`
        have hA0 : A i k = 0 := by omega
        have hA0' : A k i = 0 := (hA.zero_comm i k).1 hA0
        rw [serreE, ← hn_def, show n = 0 by omega, adE_succ, adE_zero,
          superBracket_jacobi (isHomog_f P p k) (isHomog_e P p i) (isHomog_e P p k),
          superBracket_f_e, ite_eq_right hki, superBracket_f_e, ite_eq_left rfl, smul_zero,
          neg_zero, superBracket_zero_left, zero_add,
          show ∀ y, superBracket P p (e P p i) (-y) = -superBracket P p (e P p i) y from
            fun y ↦ (superBracketRight P p (e P p i)).map_neg y,
          superBracket_smul_right, superBracket_e_h, P.root_coroot, hA0']
        simp
      · -- `n = 1`, so `aᵢⱼ = -1` is odd and `eᵢ` is even: `G̃_{2αᵢ} = 0`
        have hA1 : A i k = -1 := by omega
        have hi : p i = 0 := by
          rcases zmod_two_cases (p i) with hi | hi
          · exact hi
          · obtain ⟨r, hr⟩ := hp i k hi; omega
        refine eq_zero_of_mem_two_root_of_even P p hi hG (Or.inl ?_)
        rwa [show n + 1 = 2 by omega] at hw
    · exact eq_zero_of_mem_weightSpace_nsmul_root P p (by omega) hG hw
  · rw [serreE]
    exact superBracket_f_adE_of_ne hki _ (isHomog_e P p j)
      (by rw [superBracket_f_e, ite_eq_right hkj, smul_zero, neg_zero])

/-! ### The Serre elements lie in `R` -/

variable [FiniteDimensional K H] (S : A.Symmetrization)

variable (P p) in
include S in
/-- An element `x ∈ G̃_β`, `β > 0`, with `[fₖ, x] = 0` for all `k` lies in `R`
(cf. [Kac] Lemma 1.5). -/
theorem mem_maxIdeal_of_superBracket_f_eq_zero {β : Dual K H} (hβ : β ∈ P.posWeights)
    {x : 𝒰} (hx : x ∈ gTilde P p) (hxβ : x ∈ weightSpace P p β)
    (hfx : ∀ k, superBracket P p (f P p k) x = 0) : x ∈ maxIdeal P p := by
  by_cases hβ1 : ∃ k, β = P.root k
  · obtain ⟨k, rfl⟩ := hβ1
    obtain ⟨c, rfl⟩ := mem_weightSpace_root P p hx hxβ
    have h0 := hfx k
    rw [superBracket_smul_right, superBracket_f_e, ite_eq_left rfl, smul_neg, neg_eq_zero,
      smul_smul] at h0
    have hh : h P p (P.coroot k) ≠ 0 := fun h0 ↦ P.linearIndependent_coroot.ne_zero k
      ((injective_iff_map_eq_zero _).1 (h_injective P p) _ h0)
    have hs : superSign K p k k ≠ 0 := by unfold superSign; split_ifs <;> norm_num
    obtain rfl : c = 0 := by
      rcases smul_eq_zero.1 h0 with h0 | h0
      · exact (mul_eq_zero.1 h0).resolve_right hs
      · exact absurd h0 hh
    rw [zero_smul]
    exact zero_mem _
  push Not at hβ1
  refine (mem_maxIdeal_iff P p S hx).2 fun y hy ↦ ?_
  refine induction_on_gTilde P p (q := fun y ↦ invForm P p S y x = 0) hy
    (fun ν y hy hyν ↦ ?_) (fun y₁ y₂ h₁ h₂ ↦ by rw [map_add, LinearMap.add_apply, h₁, h₂,
      add_zero])
  by_cases hνβ : ν + β = 0
  · obtain rfl : ν = -β := eq_neg_of_add_eq_zero_left hνβ
    refine gTilde_induction_f P p (q := fun y ↦ invForm P p S y x = 0) hβ (fun j ↦ hβ1 j)
      (by simp) (fun y₁ y₂ h₁ h₂ ↦ by rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero])
      (fun c y h ↦ by rw [map_smul, LinearMap.smul_apply, h, smul_zero])
      (fun j ν' a _ _ y' hy' _ hya ↦ ?_) y hy hyν
    rw [superBracket_swap hya (isHomog_f P p j), map_neg, map_smul, LinearMap.neg_apply,
      LinearMap.smul_apply, invForm_superBracket P p S hy'
        (nMinus_le_gTilde P p (f_mem_nMinus P p j)) hx, hfx, map_zero, smul_zero, neg_zero]
  · exact invForm_eq_zero P p S hyν hxβ hνβ

variable (P p) in
include S in
/-- The positive Serre elements lie in `R` ([Kac78] §1.2). -/
theorem serreE_mem_maxIdeal (hA : A.IsGeneralizedCartan) (hp : A.IsSuperAdmissible p)
    {i j : ι} (hij : i ≠ j) : serreE P p i j ∈ maxIdeal P p :=
  mem_maxIdeal_of_superBracket_f_eq_zero P p S (serreE_weight_mem_posWeights hij _)
    (serreE_mem_gTilde i j) (serreE_mem_weightSpace i j) (superBracket_f_serreE hA hp hij)

variable (P p) in
include S in
/-- The negative Serre elements lie in `R` ([Kac78] §1.2). -/
theorem serreF_mem_maxIdeal (hA : A.IsGeneralizedCartan) (hp : A.IsSuperAdmissible p)
    {i j : ι} (hij : i ≠ j) : serreF P p i j ∈ maxIdeal P p := by
  rw [← omega_serreE]
  exact omega_mem_maxIdeal P p (serreE_mem_maxIdeal P p S hA hp hij)

end SuperEnveloping

end Matrix.Realization
