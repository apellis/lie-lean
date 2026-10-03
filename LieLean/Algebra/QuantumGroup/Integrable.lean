/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Verma

/-!
# Integrable `U_q(𝔤)`-modules

A `U`-module `M` is *integrable* ([Lus] 3.5.1, cf. [Jan] 5.7) if it is the sum of its
weight spaces `M^Λ`, `Λ ∈ X`, and all `Eᵢ`, `Fᵢ` act locally nilpotently.

We show:
* the elements on which a fixed `Fᵢ` acts nilpotently form a `U`-submodule
  (`QuantumGroup.fLocNilSubmodule`); the key input is that the quantum Serre relation lets one
  move powers of `Fᵢ` past `Fⱼ`: `Fᵢ^N Fⱼ ∈ span {Fᵢ^p Fⱼ Fᵢ^{N-p} | p < 1 - aᵢⱼ}`
  (`QuantumGroup.pow_mul_mem_span_of_qSerre`), together with the commutation formula for
  `[Eᵢ, Fᵢ^{N}]`;
* every `Eᵢ` acts locally nilpotently on the Verma module `M_q(Λ)`
  (`QuantumGroup.VermaModule.exists_E_pow_smul_eq_zero`);
* for dominant `Λ` (`⟨i, Λ⟩ ≥ 0` for all `i`) the quotient
  `L̃_q(Λ) = M_q(Λ) ⧸ Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ` (`QuantumGroup.FPowQuotient`, the quantum analogue of
  `Matrix.Realization.FPowQuotient`) is integrable, and so is its quotient `L_q(Λ)`
  (`QuantumGroup.IrreducibleModule.isIntegrable`), since `Fᵢ^{⟨i,Λ⟩+1} v_Λ` lies in the maximal
  submodule of `M_q(Λ)` (`QuantumGroup.VermaModule.fPowSubmodule_le_maxSubmodule`).

The arguments are the standard ones ([Jan] 5.6–5.10, [Lus] 3.5.3, 3.5.6), written out
by us.

## Main definitions

* `QuantumGroup.IsIntegrable`: integrable `U`-modules.
* `QuantumGroup.fLocNilSubmodule`: the `U`-submodule on which `Fᵢ` acts locally nilpotently.
* `QuantumGroup.VermaModule.fPowSubmodule`, `QuantumGroup.FPowQuotient`: `L̃_q(Λ)`.

## Main results

* `QuantumGroup.pow_mul_mem_span_of_qSerre`.
* `QuantumGroup.IsIntegrable.quotient`: quotients of integrable modules are integrable.
* `QuantumGroup.FPowQuotient.isIntegrable`, `QuantumGroup.IrreducibleModule.isIntegrable`.
* `QuantumGroup.FPowQuotient.toIrreducibleModule`: the surjection `L̃_q(Λ) → L_q(Λ)`.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 5.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.5.
-/

noncomputable section

open LusztigF

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-! ### Moving powers past a Serre-related element -/

section Ring

variable {B : Type*} [Ring B] [Algebra k B]

/-- If the quantum Serre element `Σ_{r ≤ m} (-1)^r [m r]_q a^{m-r} b a^r` vanishes, then
`a^N b ∈ span {a^p b a^{N-p} | p < m, p ≤ N}` for every `N`. -/
theorem pow_mul_mem_span_of_qSerre {q : k} {m : ℕ} {a b : B} (h : qSerre q m a b = 0) (N : ℕ) :
    a ^ N * b ∈ Submodule.span k {x | ∃ p < m, p ≤ N ∧ x = a ^ p * b * a ^ (N - p)} := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  by_cases hN : N < m
  · exact Submodule.subset_span ⟨N, hN, le_rfl, by simp⟩
  push Not at hN
  -- `a^m b = -Σ_{r < m} c_{r+1} a^{m-r-1} b a^{r+1}`
  have hs := h
  rw [qSerre, Finset.sum_range_succ'] at hs
  simp only [pow_zero, qBinomial_zero_right, mul_one, one_smul, Nat.sub_zero] at hs
  have hab : a ^ m * b = -∑ r ∈ Finset.range m, ((-1) ^ (r + 1) * qBinomial q m (r + 1)) •
      (a ^ (m - (r + 1)) * b * a ^ (r + 1)) := eq_neg_of_add_eq_zero_right hs
  have e : a ^ N * b = a ^ (N - m) * (a ^ m * b) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]
  rw [e, hab, mul_neg, Finset.mul_sum]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun r hr ↦ ?_)
  have hr := Finset.mem_range.1 hr
  rw [mul_smul_comm]
  refine Submodule.smul_mem _ _ ?_
  have e' : a ^ (N - m) * (a ^ (m - (r + 1)) * b * a ^ (r + 1)) =
      a ^ (N - (r + 1)) * b * a ^ (r + 1) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, show N - m + (m - (r + 1)) = N - (r + 1) by omega]
  rw [e']
  have ih' := ih (N - (r + 1)) (by omega)
  have hle : Submodule.span k {x | ∃ p < m, p ≤ N - (r + 1) ∧ x = a ^ p * b * a ^ (N - (r + 1) - p)}
      ≤ (Submodule.span k {x | ∃ p < m, p ≤ N ∧ x = a ^ p * b * a ^ (N - p)}).comap
        (LinearMap.mulRight k (a ^ (r + 1))) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, hp, hpN, rfl⟩
    refine Submodule.subset_span ⟨p, hp, by omega, ?_⟩
    simp only [LinearMap.mulRight_apply, mul_assoc, ← pow_add]
    congr 3
    omega
  exact hle ih'

end Ring

/-! ### Integrable modules -/

section Module

variable (R v) (M : Type*) [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-- A `U`-module is integrable ([Lus] 3.5.1, cf. [Jan] 5.7) if it is the sum of its
weight spaces `M^Λ` (`Λ ∈ X`) and all `Eᵢ`, `Fᵢ` act locally nilpotently. -/
structure IsIntegrable : Prop where
  iSup_weightSpace_eq_top : ⨆ Λ, weightSpace R v M Λ = ⊤
  exists_E_pow_smul_eq_zero : ∀ i (m : M), ∃ n : ℕ, E R v i ^ n • m = 0
  exists_F_pow_smul_eq_zero : ∀ i (m : M), ∃ n : ℕ, F R v i ^ n • m = 0

variable {R v M}

/-- A family of elements of `U` which, applied to `m`, all give `0`, spans a subspace of `U`
killing `m`. -/
lemma smul_eq_zero_of_mem_span {S : Set (QuantumGroup R v)} {m : M}
    (hS : ∀ s ∈ S, s • m = 0) {x : QuantumGroup R v} (hx : x ∈ Submodule.span k S) :
    x • m = 0 := by
  induction hx using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => simp
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_assoc, hx, smul_zero]

lemma F_pow_smul_F_smul_eq_zero {i j : I} (hij : i ≠ j) {m : M} {n : ℕ}
    (hm : ∀ n' ≥ n, F R v i ^ n' • m = 0) :
    F R v i ^ (n + (1 - D.cartanMatrix i j).toNat) • (F R v j • m) = 0 := by
  rw [← mul_smul]
  refine smul_eq_zero_of_mem_span ?_ (pow_mul_mem_span_of_qSerre (serre_F R v hij) _)
  rintro _ ⟨p, hp, -, rfl⟩
  rw [mul_smul, hm _ (by omega), smul_zero]

variable (R v M) in
/-- The `U`-submodule of elements on which `Fᵢ` acts nilpotently (cf. proof of [Jan] Lemma 5.7). -/
def fLocNilSubmodule [NeZero v] (i : I) : Submodule (QuantumGroup R v) M where
  carrier := {m | ∃ n : ℕ, F R v i ^ n • m = 0}
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨n', hn'⟩
    have ha : F R v i ^ (n + n') • a = 0 := by rw [add_comm, pow_add, mul_smul, hn, smul_zero]
    have hb : F R v i ^ (n + n') • b = 0 := by rw [pow_add, mul_smul, hn', smul_zero]
    exact ⟨n + n', by rw [smul_add, ha, hb, add_zero]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' u m hm := by
    -- `m` with `Fᵢ^n m = 0` for all large `n`
    let P : M → Prop := fun m ↦ ∃ n : ℕ, ∀ n' ≥ n, F R v i ^ n' • m = 0
    have hP : ∀ m, (∃ n : ℕ, F R v i ^ n • m = 0) → P m := fun m ⟨n, hn⟩ ↦
      ⟨n, fun n' hn' ↦ by rw [← Nat.sub_add_cancel hn', pow_add, mul_smul, hn, smul_zero]⟩
    have hP' : ∀ m, P m → ∃ n : ℕ, F R v i ^ n • m = 0 := fun m ⟨n, hn⟩ ↦ ⟨n, hn n le_rfl⟩
    have hFK : ∀ (μ : Y) (n : ℕ),
        F R v i ^ n * K R v μ = (v ^ R.root i μ) ^ n • (K R v μ * F R v i ^ n) := fun μ n ↦ by
      simpa using pow_mul_pow_of_mul_eq_smul (F_mul_K (NeZero.ne v) μ i) n 1
    have hK : ∀ (μ : Y) (m : M) (n : ℕ), F R v i ^ n • m = 0 → F R v i ^ n • K R v μ • m = 0 :=
      fun μ m n hn ↦ by rw [← mul_smul, hFK, smul_assoc, mul_smul, hn, smul_zero, smul_zero]
    suffices ∀ u : QuantumGroup R v, ∀ m, P m → P (u • m) from hP' _ (this u m (hP m hm))
    intro u
    induction u using QuantumGroup.induction_on with
    | algebraMap c =>
      rintro m ⟨n, hn⟩
      exact ⟨n, fun n' hn' ↦ by rw [algebraMap_smul, smul_comm, hn n' hn', smul_zero]⟩
    | E j =>
      rintro m ⟨n, hn⟩
      by_cases hij : i = j
      · subst hij
        refine ⟨n + 1, fun n' hn' ↦ ?_⟩
        obtain ⟨n', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
        have h := E_mul_F_pow_sub (R := R) (NeZero.ne v) i n'
        have h' := (sub_sub_cancel (E R v i * F R v i ^ (n' + 1))
          (F R v i ^ (n' + 1) * E R v i)).symm
        rw [h] at h'
        have hn'' : F R v i ^ n' • m = 0 := hn n' (by omega)
        have hX : (F R v i ^ n' * ((v ^ D.d i)⁻¹ ^ n' • Kt R v i -
            (v ^ D.d i) ^ n' • K R v (-ktilde R i))) • m = 0 := by
          rw [mul_smul, sub_smul, smul_assoc, smul_assoc, smul_sub,
            smul_comm (F R v i ^ n') ((v ^ D.d i)⁻¹ ^ n'),
            smul_comm (F R v i ^ n') ((v ^ D.d i) ^ n'), hK _ _ _ hn'', hK _ _ _ hn'',
            smul_zero, smul_zero, sub_zero]
        rw [← mul_smul, h', sub_smul, mul_smul, hn _ (by omega), smul_zero, zero_sub,
          neg_eq_zero, smul_assoc, hX, smul_zero]
      · refine ⟨n, fun n' hn' ↦ ?_⟩
        rw [← mul_smul, ← ((Commute.pow_right (E_mul_F_of_ne (Ne.symm hij)) n')).eq, mul_smul,
          hn n' hn', smul_zero]
    | F j =>
      rintro m ⟨n, hn⟩
      by_cases hij : i = j
      · subst hij
        exact ⟨n, fun n' hn' ↦ by rw [← mul_smul, ← pow_succ, hn _ (by omega)]⟩
      · exact ⟨n + (1 - D.cartanMatrix i j).toNat, fun n' hn' ↦ by
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn'
          rw [add_right_comm, F_pow_smul_F_smul_eq_zero hij (n := n + d) fun n'' hn'' ↦ hn _
            (by omega)]⟩
    | K μ =>
      rintro m ⟨n, hn⟩
      exact ⟨n, fun n' hn' ↦ hK μ m n' (hn n' hn')⟩
    | add x y hx hy =>
      intro m hm
      obtain ⟨n, hn⟩ := hx m hm
      obtain ⟨n', hn'⟩ := hy m hm
      exact ⟨max n n', fun n'' h ↦ by
        rw [add_smul, smul_add, hn n'' (le_of_max_le_left h), hn' n'' (le_of_max_le_right h),
          add_zero]⟩
    | mul x y hx hy => exact fun m hm ↦ by rw [mul_smul]; exact hx _ (hy m hm)

lemma iSup_weightSpace_quotient (h : ⨆ Λ, weightSpace R v M Λ = ⊤)
    (N : Submodule (QuantumGroup R v) M) : ⨆ Λ, weightSpace R v (M ⧸ N) Λ = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hm : m ∈ ⨆ Λ, weightSpace R v M Λ := by rw [h]; trivial
  induction hm using Submodule.iSup_induction' with
  | mem Λ m hm =>
    refine Submodule.mem_iSup_of_mem Λ fun μ ↦ ?_
    rw [← Submodule.Quotient.mk_smul, hm μ, Submodule.Quotient.mk_smul]
  | zero => exact Submodule.zero_mem _
  | add m m' _ _ hm hm' => rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hm hm'

omit [Module k M] [IsScalarTower k (QuantumGroup R v) M] in
lemma exists_pow_smul_mk_eq_zero {N : Submodule (QuantumGroup R v) M} {u : QuantumGroup R v}
    {m : M} (h : ∃ n : ℕ, u ^ n • m = 0) :
    ∃ n : ℕ, u ^ n • (Submodule.Quotient.mk m : M ⧸ N) = 0 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← Submodule.Quotient.mk_smul, hn, Submodule.Quotient.mk_zero]⟩

/-- `x⁺ m = ε(x) m` if all `Eⱼ` annihilate `m`. -/
lemma plusHom_smul_of_E_smul_eq_zero {m : M} (hm : ∀ j, E R v j • m = 0)
    (x : LusztigF k I) : plusHom R v x • m = LusztigF.counit x • m := by
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, algebraMap_smul, LusztigF.counit_algebraMap]
  | grade1 i => rw [plusHom_θ, hm, LusztigF.counit_θ, zero_smul]
  | mul a b ha hb => rw [map_mul, mul_smul, hb, smul_comm, ha, smul_smul, map_mul, mul_comm]
  | add a b ha hb => rw [map_add, add_smul, ha, hb, map_add, add_smul]

/-- Quotients of integrable modules are integrable. -/
theorem IsIntegrable.quotient (hM : IsIntegrable R v M) (N : Submodule (QuantumGroup R v) M) :
    IsIntegrable R v (M ⧸ N) where
  iSup_weightSpace_eq_top := iSup_weightSpace_quotient hM.iSup_weightSpace_eq_top N
  exists_E_pow_smul_eq_zero i x := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact exists_pow_smul_mk_eq_zero (hM.exists_E_pow_smul_eq_zero i m)
  exists_F_pow_smul_eq_zero i x := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact exists_pow_smul_mk_eq_zero (hM.exists_F_pow_smul_eq_zero i m)

end Module

/-! ### Local nilpotence of `Eᵢ` on Verma modules -/

namespace VermaModule

variable {Λ : Y →+ ℤ}

variable (R v Λ) in
/-- The span of the `y⁻ v_Λ`, `y` a monomial containing fewer than `n` factors `θᵢ`. -/
def lowerSpan (i : I) (n : ℕ) : Submodule k (VermaModule R v Λ) :=
  Submodule.span k {m | ∃ w : List I, wordWeight w i < n ∧ m = toVerma R v Λ (monomial k w)}

lemma lowerSpan_mono (i : I) {n n' : ℕ} (h : n ≤ n') :
    lowerSpan R v Λ i n ≤ lowerSpan R v Λ i n' :=
  Submodule.span_mono fun _ ⟨w, hw, e⟩ ↦ ⟨w, by omega, e⟩

lemma toVerma_monomial_mem_lowerSpan (i : I) (w : List I) :
    toVerma R v Λ (monomial k w) ∈ lowerSpan R v Λ i (wordWeight w i + 1) :=
  Submodule.subset_span ⟨w, by omega, rfl⟩

lemma F_smul_mem_lowerSpan (i j : I) {n : ℕ} {m : VermaModule R v Λ}
    (hm : m ∈ lowerSpan R v Λ i n) :
    F R v j • m ∈ lowerSpan R v Λ i (n + if i = j then 1 else 0) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨w, hw, rfl⟩ := hm
    refine Submodule.subset_span ⟨j :: w, ?_, ?_⟩
    · by_cases hij : i = j
      · subst hij; simp only [wordWeight_cons, Finsupp.add_apply, Finsupp.single_eq_same]
        simp; omega
      · simp only [wordWeight_cons, Finsupp.add_apply]
        simp [hij]; omega
    · rw [monomial_cons, toVerma_apply, toVerma_apply, map_mul, mul_smul, minusHom_θ]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

variable [NeZero v]

lemma E_smul_toVerma_monomial_mem (i : I) (w : List I) :
    E R v i • toVerma R v Λ (monomial k w) ∈ lowerSpan R v Λ i (wordWeight w i) := by
  induction w with
  | nil => simp [monomial, toVerma_one]
  | cons j w ih =>
    have ht : toVerma R v Λ (monomial k (j :: w)) = F R v j • toVerma R v Λ (monomial k w) := by
      rw [monomial_cons, toVerma_apply, toVerma_apply, map_mul, mul_smul, minusHom_θ]
    set t := toVerma R v Λ (monomial k w)
    have h := E_mul_F_sub R v i j
    rw [sub_eq_iff_eq_add] at h
    have hcount : wordWeight (j :: w) i = wordWeight w i + if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst hij; simp [wordWeight_cons]; omega
      · simp [wordWeight_cons, hij]
    rw [ht, ← mul_smul, h, add_smul, mul_smul, hcount]
    refine Submodule.add_mem _ ?_ (F_smul_mem_lowerSpan i j ih)
    split_ifs with hij
    · subst hij
      have hw := toVerma_mem_weightSpace (Λ := Λ) (R := R) (v := v)
        (monomial_mem_weightSpace (k := k) w)
      rw [smul_assoc, sub_smul, Kt_smul_of_mem_weightSpace hw,
        K_neg_ktilde_smul_of_mem_weightSpace hw, ← sub_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (toVerma_monomial_mem_lowerSpan i w))
    · rw [zero_smul]; exact Submodule.zero_mem _

lemma E_pow_smul_eq_zero_of_mem_lowerSpan (i : I) (n : ℕ) {m : VermaModule R v Λ}
    (hm : m ∈ lowerSpan R v Λ i n) : E R v i ^ n • m = 0 := by
  induction n generalizing m with
  | zero =>
    induction hm using Submodule.span_induction with
    | mem m hm => obtain ⟨w, hw, -⟩ := hm; omega
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_comm, hx, smul_zero]
  | succ n ih =>
    rw [pow_succ, mul_smul]
    refine ih ?_
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨w, hw, rfl⟩ := hm
      exact lowerSpan_mono i (by omega) (E_smul_toVerma_monomial_mem i w)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

/-- Every `Eᵢ` acts locally nilpotently on `M_q(Λ)`. -/
theorem exists_E_pow_smul_eq_zero (i : I) (m : VermaModule R v Λ) :
    ∃ n : ℕ, E R v i ^ n • m = 0 := by
  obtain ⟨y, rfl⟩ : m ∈ LinearMap.range (toVerma R v Λ) := by rw [range_toVerma]; trivial
  have hy : y ∈ Submodule.span k (Set.range (monomial k (I := I))) := by
    rw [span_monomial]; trivial
  suffices ∃ n, toVerma R v Λ y ∈ lowerSpan R v Λ i n from
    this.imp fun n hn ↦ E_pow_smul_eq_zero_of_mem_lowerSpan i n hn
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact ⟨_, toVerma_monomial_mem_lowerSpan i w⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨n', hn'⟩ := hy
    exact ⟨max n n', by
      rw [map_add]
      exact Submodule.add_mem _ (lowerSpan_mono i (le_max_left _ _) hn)
        (lowerSpan_mono i (le_max_right _ _) hn')⟩
  | smul c x _ hx => exact hx.imp fun n hn ↦ by rw [map_smul]; exact Submodule.smul_mem _ _ hn

/-! ### `L̃_q(Λ)` and the integrability of `L_q(Λ)` -/

variable (R v Λ) in
/-- The submodule `Σᵢ U Fᵢ^{⟨i,Λ⟩⁺+1} v_Λ` of `M_q(Λ)` (for dominant `Λ`, `⟨i,Λ⟩⁺ = ⟨i,Λ⟩`). -/
def fPowSubmodule : Submodule (QuantumGroup R v) (VermaModule R v Λ) :=
  Submodule.span _ (Set.range fun i ↦ F R v i ^ ((Λ (R.coroot i)).toNat + 1) • hwv R v Λ)

/-- A quotient of `M_q(Λ)` by a submodule containing all `Fᵢ^{⟨i,Λ⟩⁺+1} v_Λ` is integrable
([Jan] 5.7, 5.9). -/
theorem isIntegrable_quotient {N : Submodule (QuantumGroup R v) (VermaModule R v Λ)}
    (hN : fPowSubmodule R v Λ ≤ N) : IsIntegrable R v (VermaModule R v Λ ⧸ N) where
  iSup_weightSpace_eq_top := iSup_weightSpace_quotient iSup_weightSpace_eq_top N
  exists_E_pow_smul_eq_zero i x := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact exists_pow_smul_mk_eq_zero (exists_E_pow_smul_eq_zero i m)
  exists_F_pow_smul_eq_zero i x := by
    have h1 : (Submodule.Quotient.mk (hwv R v Λ) : VermaModule R v Λ ⧸ N) ∈
        fLocNilSubmodule R v (VermaModule R v Λ ⧸ N) i := by
      refine ⟨(Λ (R.coroot i)).toNat + 1, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hN (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have := Submodule.smul_mem _ u h1
    rwa [← Submodule.Quotient.mk_smul, ← mk_eq_smul_hwv] at this

lemma F_pow_smul_mem_weightSpace {Λ' : Y →+ ℤ} {m : VermaModule R v Λ}
    (hm : m ∈ weightSpace R v (VermaModule R v Λ) Λ') (i : I) (n : ℕ) :
    F R v i ^ n • m ∈ weightSpace R v (VermaModule R v Λ) (Λ' - n • R.root i) := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ', mul_smul, succ_nsmul, ← sub_sub]
    exact F_smul_mem_weightSpace ih i

/-- If `y ∈ 'f` has no constant term and `y⁻ v_Λ` is a weight vector annihilated by all `Eⱼ`,
then `y⁻ v_Λ` lies in the maximal submodule `M'_q(Λ)`. -/
theorem toVerma_mem_maxSubmodule (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {y : LusztigF k I} (hy : LusztigF.counit y = 0) {Λ' : Y →+ ℤ}
    (hw : toVerma R v Λ y ∈ weightSpace R v (VermaModule R v Λ) Λ')
    (hE : ∀ j, E R v j • toVerma R v Λ y = 0) : toVerma R v Λ y ∈ maxSubmodule R v Λ := by
  rw [mem_maxSubmodule_iff hR hv']
  intro u
  have e : ∀ x, minusHom R v x • toVerma R v Λ y = toVerma R v Λ (x * y) := fun x ↦ by
    rw [toVerma_apply, toVerma_apply, map_mul, mul_smul]
  induction mem_triangularSpan_of u (NeZero.ne v) using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, μ, w', rfl⟩ := hu
    rw [mul_smul, mul_smul, plusHom_smul_of_E_smul_eq_zero hE, smul_comm (K R v μ), hw μ,
      smul_comm (minusHom R v _), smul_comm (minusHom R v _), e, map_smul, map_smul,
      hwCoord_toVerma, map_mul, hy, mul_zero, smul_zero, smul_zero]
  | zero => rw [zero_smul, map_zero]
  | add x x' _ _ hx hx' => rw [add_smul, map_add, hx, hx', add_zero]
  | smul c x _ hx => rw [smul_assoc, map_smul, hx, smul_zero]

/-- For dominant `Λ`, the vectors `Fᵢ^{⟨i,Λ⟩+1} v_Λ` lie in the maximal submodule of `M_q(Λ)`
([Jan] 5.6); hence `L_q(Λ)` is a quotient of `L̃_q(Λ)`. -/
theorem fPowSubmodule_le_maxSubmodule (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) : fPowSubmodule R v Λ ≤ maxSubmodule R v Λ := by
  rw [fPowSubmodule, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have e : F R v i ^ ((Λ (R.coroot i)).toNat + 1) • hwv R v Λ =
      toVerma R v Λ (θ k i ^ ((Λ (R.coroot i)).toNat + 1)) := by
    rw [toVerma_apply, map_pow, minusHom_θ]
  have hw := F_pow_smul_mem_weightSpace (hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ)) i
    ((Λ (R.coroot i)).toNat + 1)
  change F R v i ^ ((Λ (R.coroot i)).toNat + 1) • hwv R v Λ ∈ maxSubmodule R v Λ
  rw [e] at hw ⊢
  refine toVerma_mem_maxSubmodule hR hv' (by simp) hw fun j ↦ ?_
  rw [← e]
  exact E_smul_F_pow_smul_eq_zero (NeZero.ne v) hwv_mem_weightSpace (fun j ↦ E_smul_hwv j)
    (Int.toNat_of_nonneg (hΛ i)).symm j

end VermaModule

/-- For dominant `Λ`, the simple module `L_q(Λ)` is integrable ([Jan] 5.10,
[Lus] 3.5.6). Requires an `X`-regular root datum and `v` not a root of unity. -/
theorem IrreducibleModule.isIntegrable [NeZero v] (hR : R.IsXRegular)
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ : Y →+ ℤ} (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    IsIntegrable R v (IrreducibleModule R v Λ) :=
  VermaModule.isIntegrable_quotient (VermaModule.fPowSubmodule_le_maxSubmodule hR hv' hΛ)

variable (R v) in
/-- The module `L̃_q(Λ) = M_q(Λ) ⧸ Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ` for dominant `Λ` ([Jan] 5.9,
[Lus] 3.5.6); the quantum analogue of `Matrix.Realization.FPowQuotient`. -/
abbrev FPowQuotient (Λ : Y →+ ℤ) : Type _ :=
  VermaModule R v Λ ⧸ VermaModule.fPowSubmodule R v Λ

/-- `L̃_q(Λ)` is integrable ([Jan] 5.9). -/
theorem FPowQuotient.isIntegrable [NeZero v] (Λ : Y →+ ℤ) :
    IsIntegrable R v (FPowQuotient R v Λ) :=
  VermaModule.isIntegrable_quotient le_rfl

/-- For dominant `Λ`, `L_q(Λ)` is a quotient of `L̃_q(Λ)` ([Jan] 5.10, proof). -/
def FPowQuotient.toIrreducibleModule [NeZero v] (hR : R.IsXRegular)
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ : Y →+ ℤ} (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    FPowQuotient R v Λ →ₗ[QuantumGroup R v] IrreducibleModule R v Λ :=
  Submodule.factor (VermaModule.fPowSubmodule_le_maxSubmodule hR hv' hΛ)

theorem FPowQuotient.toIrreducibleModule_surjective [NeZero v] (hR : R.IsXRegular)
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ : Y →+ ℤ} (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    Function.Surjective (FPowQuotient.toIrreducibleModule hR hv' hΛ) :=
  Submodule.factor_surjective (VermaModule.fPowSubmodule_le_maxSubmodule hR hv' hΛ)

end QuantumGroup
