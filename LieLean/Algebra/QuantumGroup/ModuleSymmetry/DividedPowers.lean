/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Braid

/-!
# Lusztig's `Tᵢ` on divided powers

Let `v` be nonzero and not a root of unity and let `Tᵢ = T''_{i,1}` be Lusztig's automorphism
`braidEquivOfNotRoot` of `U`. We prove the divided-power formulas of [Lus] 37.1.3 (the
"more generally" list, with `e = -1`): for `n ≥ 0`, `a = -⟨i, j'⟩`, `vᵢ = v^{dᵢ}`,

* `Tᵢ(Eⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{-r} Eᵢ^{(s)} Eⱼ^{(n)} Eᵢ^{(r)}` for `j ≠ i`
  (`braidEquivOfNotRoot_qDivPow_E_ne`);
* `Tᵢ(Fⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{r} Fᵢ^{(r)} Fⱼ^{(n)} Fᵢ^{(s)}` for `j ≠ i`
  (`braidEquivOfNotRoot_qDivPow_F_ne`);
* `Tᵢ(Eᵢ^{(n)}) = (-1)^n vᵢ^{-n(n-1)} Fᵢ^{(n)} K̃_{ni}` and
  `Tᵢ(Fᵢ^{(n)}) = (-1)^n vᵢ^{n(n-1)} K̃_{-ni} Eᵢ^{(n)}`;

and the corresponding formulas for the inverse `Tᵢ⁻¹ = T'_{i,-1}`
(`braidEquivOfNotRoot_symm_qDivPow_E_ne`, `_F_ne`, `_E_self`, `_F_self`).

## Main results

* `QuantumGroup.braidEquivOfNotRoot_qDivPow_E_ne`, `braidEquivOfNotRoot_qDivPow_F_ne`,
  `braidEquivOfNotRoot_qDivPow_E_self`, `braidEquivOfNotRoot_qDivPow_F_self`.
* `QuantumGroup.T_qDivPow_E_smul_of_lowest`: on `i`-lowest vectors of integrable modules,
  `Tᵢ(Eⱼ^{(n)})` acts as `braidEjDiv`.
* `QuantumGroup.plusHom_eq_zero_of_smul_lowest`: lowest weight vectors of the `ʷL̃_q(Λ)` detect
  `U⁺`.

The formula for `Eⱼ^{(n)}` is proved on integrable modules (our argument, in the spirit of
[Lus] 37.2.2): on a vector `T(η)`, `η` primitive for the `𝔰𝔩₂` at `i`, both `Tᵢ(Eⱼ^{(n)})` and the
right hand side act as `κ Ψ_{p,an}(Eⱼ^{(n)} η)` (`QuantumGroup/ModuleSymmetry/Rank1Formula.lean`),
the higher-order Serre vanishing `Eᵢ^{an+1} Eⱼ^n η = 0` coming from the ordinary quantum Serre
relation. Every `i`-lowest vector is such a `T(η)`, and the lowest weight vectors of the modules
`ʷL̃_q(Λ)` detect elements of `U⁺` (via `mem_serreIdeal_of_toVerma_mem_fPowSubmodule`), first for
the root datum `freeCoroot R` and then for `R` by `mapHom`. The formula for `Fⱼ^{(n)}` follows by
`ω Tᵢ ω D_ζ = D_ζ Tᵢ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 37.1.3, 37.2.2.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

/-! ### Higher-order annihilation from a quantum Serre relation -/

section Serre

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

variable {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]

/-- If `S_q(a, b) = 0` with `m + 1` factors `a` and `aᴺ x = 0` for `N ≥ N₀`, then
`aᴺ bⁿ x = 0` for `N ≥ N₀ + m n` (higher-order quantum Serre vanishing). -/
lemma pow_smul_pow_smul_eq_zero_of_qSerre {q : k} {m : ℕ} {a b : B}
    (h : qSerre q (m + 1) a b = 0) {N₀ : ℕ} {x : M} (hx : ∀ N, N₀ ≤ N → a ^ N • x = 0) (n : ℕ) :
    ∀ N, N₀ + m * n ≤ N → a ^ N • (b ^ n • x) = 0 := by
  induction n with
  | zero => intro N hN; simpa using hx N (by simpa using hN)
  | succ n ih =>
    intro N hN
    have hN' : N₀ + m * n + m ≤ N := by rw [Nat.mul_succ] at hN; omega
    rw [pow_succ', mul_smul, ← mul_smul]
    have hmem := pow_mul_mem_span_of_qSerre h N
    refine Submodule.span_induction (p := fun y _ ↦ y • (b ^ n • x) = 0) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨r, hr, -, rfl⟩
      rw [mul_smul, mul_smul, ih (N - r) (by omega), smul_zero, smul_zero]
    · simp
    · intro y z _ _ hy hz; rw [add_smul, hy, hz, add_zero]
    · intro c y _ hy; rw [smul_assoc, hy, smul_zero]

end Serre

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-! ### The right hand sides -/

variable (R v) in
/-- `Σ_{r+s=an} (-1)^r vᵢ^{-r} Eᵢ^{(s)} Eⱼ^{(n)} Eᵢ^{(r)}`, the value of `Tᵢ = T''_{i,1}` on
`Eⱼ^{(n)}` ([Lus] 37.1.3), `a = -⟨i, j'⟩`. -/
def braidEjDiv (i j : I) (n : ℕ) : QuantumGroup R v :=
  ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i)⁻¹ ^ r) •
    (qDivPow (v ^ D.d i) (negA D i j * n - r) (E R v i) * qDivPow (v ^ D.d j) n (E R v j) *
      qDivPow (v ^ D.d i) r (E R v i))

variable (R v) in
/-- `Σ_{r+s=an} (-1)^r vᵢ^{r} Fᵢ^{(r)} Fⱼ^{(n)} Fᵢ^{(s)}`, the value of `Tᵢ = T''_{i,1}` on
`Fⱼ^{(n)}` ([Lus] 37.1.3), `a = -⟨i, j'⟩`. -/
def braidFjDiv (i j : I) (n : ℕ) : QuantumGroup R v :=
  ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i) ^ r) •
    (qDivPow (v ^ D.d i) r (F R v i) * qDivPow (v ^ D.d j) n (F R v j) *
      qDivPow (v ^ D.d i) (negA D i j * n - r) (F R v i))

lemma braidEjDiv_mem_adjoin (i j : I) (n : ℕ) :
    braidEjDiv R v i j n ∈ Algebra.adjoin k (Set.range (E R v)) := by
  have hE : ∀ l, E R v l ∈ Algebra.adjoin k (Set.range (E R v)) :=
    fun l ↦ Algebra.subset_adjoin ⟨l, rfl⟩
  have hD : ∀ q l c, qDivPow q c (E R v l) ∈ Algebra.adjoin k (Set.range (E R v)) :=
    fun q l c ↦ Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (hE l) c) _
  exact Subalgebra.sum_mem _ fun r _ ↦ Subalgebra.smul_mem _
    (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hD _ _ _) (hD _ _ _)) (hD _ _ _)) _

/-! ### The formula on integrable modules -/

section Module

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]
  [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M) {i j : I}

include hv in
/-- On a vector `T(η)`, `η` primitive of weight `p` at `i`, the element `braidEjDiv` acts as
`(-1)^p vᵢ^p Ψ_{p,an}(Eⱼ^{(n)} η)`. -/
lemma braidEjDiv_smul_T_of_primitive (hji : j ≠ i) (n p : ℕ) {η : M}
    (hη : η ∈ (nodeSl2 R v M hv hM i).wt p) (hE : (nodeSl2 R v M hv hM i).E η = 0) :
    braidEjDiv R v i j n • (nodeSl2 R v M hv hM i).T (v ^ D.d i) η =
      ((-1) ^ p * (v ^ D.d i) ^ p) • (nodeSl2 R v M hv hM i).psi p (negA D i j * n)
        (qDivPow (v ^ D.d j) n (E R v j) • η) := by
  set V := nodeSl2 R v M hv hM i
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hqr := pow_d_ne_one (D := D) hv i
  have hEF : qDivPow (v ^ D.d j) n (E R v j) * F R v i =
      F R v i * qDivPow (v ^ D.d j) n (E R v j) := by
    have h1 : E R v j * F R v i = F R v i * E R v j := by
      have := E_mul_F_sub (R := R) (v := v) j i
      simp only [hji, ↓reduceIte] at this
      exact sub_eq_zero.1 this
    simp only [qDivPow, smul_mul_assoc, mul_smul_comm]
    rw [((show Commute (E R v j) (F R v i) from h1).pow_left n).eq]
  have hZF : ∀ x, act R v M (qDivPow (v ^ D.d j) n (E R v j)) (V.F x) =
      V.F (act R v M (qDivPow (v ^ D.d j) n (E R v j)) x) := fun x ↦ by
    change qDivPow (v ^ D.d j) n (E R v j) • F R v i • x =
      F R v i • qDivPow (v ^ D.d j) n (E R v j) • x
    rw [← mul_smul, hEF, mul_smul]
  have hT0 : V.T (v ^ D.d i) η = ((-1) ^ p * (v ^ D.d i) ^ p) • V.dF p η := by
    have := IntegrableSl2.T_dF_of_primitive hq0 hqr hq0 (fun _ _ ↦ rfl) hη hE (Nat.zero_le p)
    simpa using this
  rw [hT0, smul_comm, IntegrableSl2.psi_apply]
  congr 1
  rw [braidEjDiv, sum_smul]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [smul_assoc]
  change ((-1) ^ s * (v ^ D.d i)⁻¹ ^ s) • act R v M (qDivPow (v ^ D.d i) (negA D i j * n - s)
    (E R v i) * qDivPow (v ^ D.d j) n (E R v j) * qDivPow (v ^ D.d i) s (E R v i)) (V.dF p η) = _
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    act_qDivPow (v ^ D.d i) (negA D i j * n - s) (E R v i), act_qDivPow (v ^ D.d i) s (E R v i)]
  change ((-1) ^ s * (v ^ D.d i)⁻¹ ^ s) • V.dE (negA D i j * n - s)
    (act R v M (qDivPow (v ^ D.d j) n (E R v j)) (V.dE s (V.dF p η))) = _
  split_ifs with hsp
  · rw [IntegrableSl2.dE_dF_of_primitive hq0 hqr hη hE hsp le_rfl, Nat.sub_self, zero_add,
      qBinomial_self, one_smul, IntegrableSl2.comm_dF (V := V) _ hZF]
    rfl
  · rw [IntegrableSl2.dE_dF_eq_zero_of_lt hq0 hqr hη hE le_rfl (by omega), map_zero,
      map_zero, smul_zero, zero_smul]

include hv in
/-- `T(Eⱼ^{(n)} η) = braidEjDiv · T(η)` for `η` primitive at `i` (the rank-one input). -/
lemma T_qDivPow_E_smul_of_primitive (hji : j ≠ i) (n p : ℕ) {η : M}
    (hη : η ∈ (nodeSl2 R v M hv hM i).wt p) (hE : (nodeSl2 R v M hv hM i).E η = 0) :
    (nodeSl2 R v M hv hM i).T (v ^ D.d i) (qDivPow (v ^ D.d j) n (E R v j) • η) =
      braidEjDiv R v i j n • (nodeSl2 R v M hv hM i).T (v ^ D.d i) η := by
  set V := nodeSl2 R v M hv hM i
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hqr := pow_d_ne_one (D := D) hv i
  have hij : i ≠ j := Ne.symm hji
  set r := negA D i j * n with hr
  rw [braidEjDiv_smul_T_of_primitive hv hM hji n p hη hE]
  apply IntegrableSl2.T_eq_psi_of_mem hq0 hqr
  set Z := qDivPow (v ^ D.d j) n (E R v j)
  -- weight of `Z η`
  have hZη : Z • η ∈ V.wt ((p : ℤ) - r) := by
    have hpow : ∀ (c : ℕ) (x : M) (m : ℤ), x ∈ V.wt m →
        E R v j ^ c • x ∈ V.wt (m - negA D i j * c) := by
      intro c
      induction c with
      | zero => intro x m hx; simpa using hx
      | succ c ih =>
        intro x m hx
        rw [pow_succ', mul_smul]
        have := E_smul_mem_nodeWt (ih x m hx) j
        rw [cartanMatrix_eq_neg_negA hij] at this
        change _ ∈ nodeWt R v M i _
        convert this using 2
        push_cast; ring
    have := hpow n η p hη
    rw [show (p : ℤ) - (negA D i j * n : ℕ) = p - negA D i j * n by push_cast; ring]
    simp only [Z, qDivPow, smul_assoc]
    exact Submodule.smul_mem _ _ this
  -- higher-order Serre vanishing
  have hZE : (V.E ^ (r + 1)) (Z • η) = 0 := by
    have hs := serre_E (R := R) (v := v) hij
    rw [one_sub_cartanMatrix_toNat hij] at hs
    have hx : ∀ N, 1 ≤ N → E R v i ^ N • η = 0 := by
      intro N hN
      obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le' hN
      rw [pow_succ, mul_smul]
      change E R v i ^ N • V.E η = 0
      rw [hE, smul_zero]
    have := pow_smul_pow_smul_eq_zero_of_qSerre hs hx n (r + 1) (by rw [hr]; omega)
    change (act R v M (E R v i) ^ (r + 1)) (Z • η) = 0
    rw [← map_pow]
    change E R v i ^ (r + 1) • (Z • η) = 0
    simp only [Z, qDivPow, smul_assoc, smul_comm _ ((qFactorial (v ^ D.d j) n)⁻¹)]
    rw [this, smul_zero]
  rcases le_or_gt (r : ℤ) p with hrp | hrp
  · exact IntegrableSl2.mem_stringsLT_of_nonneg hq0 hqr (by omega) hZη hZE
  · have hEF : Z * F R v i = F R v i * Z := by
      have h1 : E R v j * F R v i = F R v i * E R v j := by
        have := E_mul_F_sub (R := R) (v := v) j i
        simp only [hji, ↓reduceIte] at this
        exact sub_eq_zero.1 this
      simp only [Z, qDivPow, smul_mul_assoc, mul_smul_comm]
      rw [((show Commute (E R v j) (F R v i) from h1).pow_left n).eq]
    have hF : (V.F ^ (p + 1)) (Z • η) = 0 := by
      have hc : ∀ (N : ℕ) (x : M), (V.F ^ N) (Z • x) = Z • (V.F ^ N) x := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          intro x
          rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
          change F R v i • (Z • (V.F ^ N) x) = Z • (F R v i • (V.F ^ N) x)
          rw [← mul_smul, ← mul_smul, hEF]
      have h0 := IntegrableSl2.dF_eq_zero_of_primitive hq0 hqr hη hE
        (show (p : ℤ) < (p + 1 : ℕ) by push_cast; omega)
      rw [IntegrableSl2.dF_apply] at h0
      rw [hc, (smul_eq_zero.1 h0).resolve_left
        (inv_ne_zero (qFactorial_ne_zero_of_pow_ne_one hq0 hqr _)), smul_zero]
    have := IntegrableSl2.mem_stringsLT_of_nonpos hq0 hqr (by omega) hZη hF
    rwa [show p + 1 + (-((p : ℤ) - r)).toNat = r + 1 by omega] at this

variable {Ti : QuantumGroup R v →ₐ[k] QuantumGroup R v} (H : HasBraidGeneratorImages i Ti)
include H

include hv in
/-- On every `i`-lowest vector `m` of an integrable module, `Tᵢ(Eⱼ^{(n)})` acts as
`braidEjDiv`. -/
theorem T_qDivPow_E_smul_of_lowest (hji : j ≠ i) (n p : ℕ) {m : M}
    (hm : m ∈ (nodeSl2 R v M hv hM i).wt (-(p : ℤ))) (hF : (nodeSl2 R v M hv hM i).F m = 0) :
    Ti (qDivPow (v ^ D.d j) n (E R v j)) • m = braidEjDiv R v i j n • m := by
  set V := nodeSl2 R v M hv hM i
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hqr := pow_d_ne_one (D := D) hv i
  set η := V.dE p m with hηdef
  -- `m` is primitive for the flipped structure
  have hm' : m ∈ V.flip.wt p := by simpa using hm
  have hη : η ∈ V.wt p := by
    have := V.dE_mem hm p
    rwa [show -(p : ℤ) + 2 * p = p by ring] at this
  have hηE : V.E η = 0 := by
    rw [hηdef, IntegrableSl2.E_dE hq0 hqr]
    have := IntegrableSl2.dF_eq_zero_of_primitive (V := V.flip) hq0 hqr hm' hF
      (show (p : ℤ) < (p + 1 : ℕ) by push_cast; omega)
    rw [IntegrableSl2.flip_dF] at this
    rw [this, smul_zero]
  have hdF : V.dF p η = m := by
    have := IntegrableSl2.dE_dF_of_primitive (V := V.flip) hq0 hqr hm' hF (le_refl p) le_rfl
    simpa using this
  have hT : V.T (v ^ D.d i) η = ((-1) ^ p * (v ^ D.d i) ^ p) • m := by
    have := IntegrableSl2.T_dF_of_primitive hq0 hqr hq0 (fun _ _ ↦ rfl) hη hηE (Nat.zero_le p)
    simpa [hdF] using this
  have hc : ((-1 : k) ^ p * (v ^ D.d i) ^ p) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq0)
  have key := nodeSl2_T_smul hv hM H (qDivPow (v ^ D.d j) n (E R v j)) η
  rw [T_qDivPow_E_smul_of_primitive hv hM hji n p hη hηE, hT] at key
  have key2 : ((-1 : k) ^ p * (v ^ D.d i) ^ p) • (Ti (qDivPow (v ^ D.d j) n (E R v j)) • m) =
      ((-1 : k) ^ p * (v ^ D.d i) ^ p) • (braidEjDiv R v i j n • m) := by
    rw [smul_comm _ (Ti _) m, smul_comm _ (braidEjDiv R v i j n) m]
    exact key.symm
  exact smul_right_injective M hc key2

end Module

/-! ### Lowest weight vectors detect `U⁺` -/

section Detect

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

open VermaModule in
include hv in
/-- If `x⁺` kills the lowest weight vector `ʷv_Λ` of `ʷL̃_q(Λ)` for every dominant `Λ`, and the
simple coroots can be paired with arbitrarily large integers, then `x⁺ = 0`. -/
theorem plusHom_eq_zero_of_smul_lowest
    (hcor : ∀ N : ℕ, ∃ Λ : Y →+ ℤ, ∀ i, (N : ℤ) ≤ Λ (R.coroot i)) (x : LusztigF k I)
    (h : ∀ Λ : Y →+ ℤ, (∀ i, 0 ≤ Λ (R.coroot i)) → plusHom R v x •
      ChevalleyTwist.toTwist R v (FPowQuotient R v Λ)
        (Submodule.Quotient.mk (hwv R v Λ)) = 0) :
    plusHom R v x = 0 := by
  classical
  have hx : minusHom R v x = 0 := by
    set N := ∑ ν ∈ (LusztigF.gradingHom k I x).coeff.support, ∑ i ∈ ν.support, ν i
    obtain ⟨Λ, hΛ⟩ := hcor N
    have hΛ0 : ∀ i, 0 ≤ Λ (R.coroot i) := fun i ↦ (hΛ i).trans' (by positivity)
    rw [minusHom_eq_zero_iff R v hv]
    refine mem_serreIdeal_of_toVerma_mem_fPowSubmodule hv (Λ := Λ) hΛ0 (fun ν hν i ↦ ?_) ?_
    · have hνs : ν ∈ (LusztigF.gradingHom k I x).coeff.support := Finsupp.mem_support_iff.2 hν
      have h1 : ν i ≤ ∑ i ∈ ν.support, ν i := by
        by_cases hi : i ∈ ν.support
        · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi
        · rw [Finsupp.notMem_support_iff.1 hi]; exact Nat.zero_le _
      have h2 : ∑ i ∈ ν.support, ν i ≤ N :=
        Finset.single_le_sum (f := fun ν : I →₀ ℕ ↦ ∑ i ∈ ν.support, ν i)
          (fun _ _ ↦ Nat.zero_le _) hνs
      have := hΛ i
      omega
    · have := h Λ hΛ0
      rw [ChevalleyTwist.smul_toTwist, ← AlgHom.comp_apply, chevalley_comp_plusHom,
        LinearEquiv.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
  rwa [plusHom_eq_zero_iff R v hv, ← minusHom_eq_zero_iff R v hv]

end Detect

/-! ### The formulas in `U` -/

section Formulas

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

omit [NeZero v] in
lemma qDivPow_E_mem_adjoin (q : k) (j : I) (n : ℕ) :
    qDivPow q n (E R v j) ∈ Algebra.adjoin k (Set.range (E R v)) :=
  Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) n) _

include hv in
/-- The formula on a root datum whose simple coroots pair with arbitrarily large integers. -/
lemma braidEquivOfNotRoot_qDivPow_E_ne_aux
    (hcor : ∀ N : ℕ, ∃ Λ : Y →+ ℤ, ∀ i, (N : ℤ) ≤ Λ (R.coroot i)) {i j : I} (hji : j ≠ i)
    (n : ℕ) : braidEquivOfNotRoot R hv i (qDivPow (v ^ D.d j) n (E R v j)) =
      braidEjDiv R v i j n := by
  have H := braidEquivOfNotRoot_hasImages hv R i
  have hmem : braidEquivOfNotRoot R hv i (qDivPow (v ^ D.d j) n (E R v j)) -
      braidEjDiv R v i j n ∈ Algebra.adjoin k (Set.range (E R v)) := by
    refine sub_mem ?_ (braidEjDiv_mem_adjoin i j n)
    simp only [qDivPow, map_smul, map_pow]
    refine Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ?_ n) _
    have := H.map_E j
    simp only [hji, ↓reduceIte] at this
    change (braidEquivOfNotRoot R hv i).toAlgHom (E R v j) ∈ _
    rw [this]
    exact braidEj_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (Algebra.subset_adjoin ⟨j, rfl⟩)
  obtain ⟨x, hx⟩ := exists_plusHom_eq hmem
  have h0 : plusHom R v x = 0 := by
    refine plusHom_eq_zero_of_smul_lowest hv hcor x fun Λ hΛ ↦ ?_
    set M := ChevalleyTwist R v (FPowQuotient R v Λ)
    have hM : IsIntegrable R v M := ChevalleyTwist.isIntegrable (FPowQuotient.isIntegrable Λ)
    set g := ChevalleyTwist.toTwist R v (FPowQuotient R v Λ)
      (Submodule.Quotient.mk (VermaModule.hwv R v Λ))
    have hg : g ∈ weightSpace R v M (-Λ) := by
      intro μ
      rw [ChevalleyTwist.smul_toTwist, chevalley_K, ← Submodule.Quotient.mk_smul,
        VermaModule.K_smul_hwv, Submodule.Quotient.mk_smul, map_smul, map_neg,
        AddMonoidHom.neg_apply]
    have hgw : g ∈ (nodeSl2 R v M hv hM i).wt (-((Λ (R.coroot i)).toNat : ℤ)) := by
      have := mem_nodeWt_of_mem (i := i) hg
      rwa [AddMonoidHom.neg_apply, ← Int.toNat_of_nonneg (hΛ i)] at this
    have hgF : (nodeSl2 R v M hv hM i).F g = 0 := by
      change F R v i • g = 0
      rw [ChevalleyTwist.smul_toTwist, chevalley_F, ← Submodule.Quotient.mk_smul,
        VermaModule.E_smul_hwv, Submodule.Quotient.mk_zero, map_zero]
    have := T_qDivPow_E_smul_of_lowest hv hM H hji n _ hgw hgF
    rw [hx, sub_smul, sub_eq_zero]
    exact this
  rw [h0, eq_comm, sub_eq_zero] at hx
  exact hx

include hv in
/-- **Lusztig's `Tᵢ` on `Eⱼ^{(n)}`** ([Lus] 37.1.3, `T''_{i,1}`): for `j ≠ i` and `n ≥ 0`,
`Tᵢ(Eⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{-r} Eᵢ^{(s)} Eⱼ^{(n)} Eᵢ^{(r)}`, `a = -⟨i, j'⟩`, for every
root datum, any field and `v ≠ 0` not a root of unity (Lusztig: over `ℚ(v)`). -/
theorem braidEquivOfNotRoot_qDivPow_E_ne (R : D.RootDatum Y) {i j : I} (hji : j ≠ i) (n : ℕ) :
    braidEquivOfNotRoot R hv i (qDivPow (v ^ D.d j) n (E R v j)) = braidEjDiv R v i j n := by
  have key := braidEquivOfNotRoot_qDivPow_E_ne_aux hv (R := R.freeCoroot)
    R.exists_le_freeCoroot hji n
  have e := mapHom_wordProd R.freeCorootHom (braidEquivOfNotRoot R.freeCoroot hv)
    (braidEquivOfNotRoot R hv) (braidEquivOfNotRoot_hasImages hv R.freeCoroot)
    (braidEquivOfNotRoot_hasImages hv R) [i] (qDivPow (v ^ D.d j) n (E R.freeCoroot v j))
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at e
  rw [key] at e
  have h1 : mapHom v R.freeCorootHom (qDivPow (v ^ D.d j) n (E R.freeCoroot v j)) =
      qDivPow (v ^ D.d j) n (E R v j) := by
    simp [qDivPow, map_smul, map_pow]
  have h2 : mapHom v R.freeCorootHom (braidEjDiv R.freeCoroot v i j n) = braidEjDiv R v i j n := by
    simp [braidEjDiv, map_sum, map_smul, map_mul, qDivPow, map_pow]
  rw [h1, h2] at e
  exact e.symm

end Formulas

/-! ### `Fⱼ^{(n)}` via the Chevalley involution -/

section Chevalley

omit [DecidableEq I] in
lemma qDivPow_smul_pow {B : Type*} [Ring B] [Algebra k B] (q c : k) (n : ℕ) (a : B) :
    qDivPow q n (c • a) = c ^ n • qDivPow q n a := by
  simp only [qDivPow, smul_pow, smul_comm (c ^ n)]

lemma diagHom_qDivPow_E (c : I → kˣ) (q : k) (n : ℕ) (l : I) :
    diagHom R v c (qDivPow q n (E R v l)) = ((c l : k) ^ n) • qDivPow q n (E R v l) := by
  simp only [qDivPow, map_smul, map_pow, diagHom_E, smul_pow]
  exact smul_comm _ _ _

lemma chevalley_qDivPow_E (q : k) (n : ℕ) (l : I) :
    chevalley R v (qDivPow q n (E R v l)) = qDivPow q n (F R v l) := by
  simp [qDivPow, map_smul, map_pow]

lemma chevalley_qDivPow_F (q : k) (n : ℕ) (l : I) :
    chevalley R v (qDivPow q n (F R v l)) = qDivPow q n (E R v l) := by
  simp [qDivPow, map_smul, map_pow]

lemma chevalley_chevalley (x : QuantumGroup R v) : chevalley R v (chevalley R v x) = x :=
  DFunLike.congr_fun (chevalley_comp_chevalley R v) x

variable [NeZero v]

lemma chevalley_diagHom_braidEjDiv (i j : I) (n : ℕ) :
    chevalley R v (diagHom R v (chevalleyScalar D v) (braidEjDiv R v i j n)) =
      ((chevalleyScalar D v j : k) ^ n) • braidFjDiv R v i j n := by
  have hq : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  rw [braidEjDiv, braidFjDiv, map_sum, map_sum, smul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [mem_range] at hr
  obtain ⟨t, ht⟩ : ∃ t, negA D i j * n = r + t := ⟨negA D i j * n - r, by omega⟩
  simp only [map_smul, map_mul, diagHom_qDivPow_E, chevalley_qDivPow_E, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [show negA D i j * n + 1 - 1 - r = t by omega, show negA D i j * n - r = t by omega,
    show negA D i j * n - t = r by omega]
  congr 1
  simp only [chevalleyScalar, Units.val_mk0]
  rw [neg_pow (v ^ D.d i), neg_pow (v ^ D.d i), neg_pow (v ^ D.d j)]
  field_simp
  have h1 : v ^ (t * D.d i) * v⁻¹ ^ (t * D.d i) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (NeZero.ne v), one_pow]
  have h2 : (-1 : k) ^ (t * 2) = 1 := Even.neg_one_pow ⟨t, by ring⟩
  ring_nf
  linear_combination (v ^ (D.d j * n) * (-1 : k) ^ (t * 2)) * h1 + v ^ (D.d j * n) * h2

end Chevalley

/-! ### The remaining formulas -/

omit [DecidableEq I] in
/-- `(ab)ⁿ = c^{n(n-1)/2} aⁿ bⁿ` when `ba = c ab`. -/
lemma mul_pow_eq_choose_smul {B : Type*} [Ring B] [Algebra k B] {a b : B} {c : k}
    (h : b * a = c • (a * b)) (n : ℕ) : (a * b) ^ n = c ^ n.choose 2 • (a ^ n * b ^ n) := by
  have hb : ∀ m : ℕ, b ^ m * a = c ^ m • (a * b ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc b ^ (m + 1) * a = b ^ m * (b * a) := by rw [pow_succ, mul_assoc]
        _ = c • ((b ^ m * a) * b) := by rw [h, mul_smul_comm, mul_assoc]
        _ = c ^ (m + 1) • (a * b ^ (m + 1)) := by
          rw [ih, smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ, ← pow_succ']
  induction n with
  | zero => simp
  | succ n ih =>
    calc (a * b) ^ (n + 1) = c ^ n.choose 2 • (a ^ n * (b ^ n * a) * b) := by
          rw [pow_succ, ih, smul_mul_assoc]; congr 1; noncomm_ring
      _ = c ^ (n + 1).choose 2 • (a ^ (n + 1) * b ^ (n + 1)) := by
          rw [hb, mul_smul_comm, smul_mul_assoc, smul_smul, ← pow_add, Nat.choose_succ_succ,
            Nat.choose_one_right, add_comm n]
          congr 1
          rw [pow_succ, pow_succ]; noncomm_ring

omit [DecidableEq I] in
lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

section Self

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

omit [NeZero v] in
lemma Kt_mul_F_self (i : I) :
    Kt R v i * F R v i = (v ^ D.d i)⁻¹ ^ 2 • (F R v i * Kt R v i) := by
  rw [Kt, K_mul_F, root_ktilde, D.cartanMatrix_self, inv_pow, ← pow_mul, ← zpow_natCast,
    ← zpow_neg]
  push_cast; ring_nf

lemma E_mul_K_neg_self (i : I) :
    E R v i * K R v (-ktilde R i) = (v ^ D.d i) ^ 2 • (K R v (-ktilde R i) * E R v i) := by
  have h := K_mul_E R v (-ktilde R i) i
  rw [map_neg, root_ktilde, D.cartanMatrix_self] at h
  rw [h, smul_smul, ← pow_mul, ← zpow_natCast, ← zpow_add₀ (NeZero.ne v)]
  push_cast; ring_nf; simp

include hv in
/-- **Lusztig's `Tᵢ` on `Eᵢ^{(n)}`** ([Lus] 37.1.3, `T''_{i,1}`):
`Tᵢ(Eᵢ^{(n)}) = (-1)^n vᵢ^{-n(n-1)} Fᵢ^{(n)} K̃_{ni}`. -/
theorem braidEquivOfNotRoot_qDivPow_E_self (R : D.RootDatum Y) (i : I) (n : ℕ) :
    braidEquivOfNotRoot R hv i (qDivPow (v ^ D.d i) n (E R v i)) =
      ((-1) ^ n * (v ^ D.d i)⁻¹ ^ (n * (n - 1))) •
        (qDivPow (v ^ D.d i) n (F R v i) * K R v (n • ktilde R i)) := by
  have H := braidEquivOfNotRoot_hasImages hv R i
  have hE : braidEquivOfNotRoot R hv i (E R v i) = -(F R v i * Kt R v i) := by
    have := H.map_E i
    simpa using this
  rw [qDivPow, map_smul, map_pow, hE, neg_pow,
    show ((-1 : QuantumGroup R v) ^ n) = algebraMap k _ ((-1) ^ n) by simp, ← Algebra.smul_def,
    mul_pow_eq_choose_smul (Kt_mul_F_self i), Kt, K_pow, ← pow_mul, two_mul_choose_two,
    qDivPow, smul_mul_assoc, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

include hv in
/-- **Lusztig's `Tᵢ` on `Fᵢ^{(n)}`** ([Lus] 37.1.3, `T''_{i,1}`):
`Tᵢ(Fᵢ^{(n)}) = (-1)^n vᵢ^{n(n-1)} K̃_{-ni} Eᵢ^{(n)}`. -/
theorem braidEquivOfNotRoot_qDivPow_F_self (R : D.RootDatum Y) (i : I) (n : ℕ) :
    braidEquivOfNotRoot R hv i (qDivPow (v ^ D.d i) n (F R v i)) =
      ((-1) ^ n * (v ^ D.d i) ^ (n * (n - 1))) •
        (K R v (n • -ktilde R i) * qDivPow (v ^ D.d i) n (E R v i)) := by
  have H := braidEquivOfNotRoot_hasImages hv R i
  have hF : braidEquivOfNotRoot R hv i (F R v i) = -(K R v (-ktilde R i) * E R v i) := by
    have := H.map_F i
    simpa using this
  rw [qDivPow, map_smul, map_pow, hF, neg_pow,
    show ((-1 : QuantumGroup R v) ^ n) = algebraMap k _ ((-1) ^ n) by simp, ← Algebra.smul_def,
    mul_pow_eq_choose_smul (E_mul_K_neg_self i), K_pow, ← pow_mul, two_mul_choose_two,
    qDivPow, mul_smul_comm, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

include hv in
/-- **Lusztig's `Tᵢ` on `Fⱼ^{(n)}`** ([Lus] 37.1.3, `T''_{i,1}`): for `j ≠ i`,
`Tᵢ(Fⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{r} Fᵢ^{(r)} Fⱼ^{(n)} Fᵢ^{(s)}`, `a = -⟨i, j'⟩`. -/
theorem braidEquivOfNotRoot_qDivPow_F_ne (R : D.RootDatum Y) {i j : I} (hji : j ≠ i) (n : ℕ) :
    braidEquivOfNotRoot R hv i (qDivPow (v ^ D.d j) n (F R v j)) = braidFjDiv R v i j n := by
  have H := braidEquivOfNotRoot_hasImages hv R i
  have h := DFunLike.congr_fun (chevalley_comp_comp_diagHom H) (qDivPow (v ^ D.d j) n (E R v j))
  simp only [AlgHom.comp_apply, diagHom_qDivPow_E, map_smul, chevalley_qDivPow_E] at h
  have hE' : (braidEquivOfNotRoot R hv i).toAlgHom (qDivPow (v ^ D.d j) n (E R v j)) =
      braidEjDiv R v i j n := braidEquivOfNotRoot_qDivPow_E_ne hv R hji n
  rw [hE'] at h
  have h' := congrArg (chevalley R v) h
  rw [map_smul, chevalley_chevalley, chevalley_diagHom_braidEjDiv] at h'
  exact smul_right_injective _ (pow_ne_zero _ (Units.ne_zero _)) h'

end Self

/-! ### The inverse `Tᵢ⁻¹ = T'_{i,-1}` -/

section Inverse

variable [NeZero v]

lemma braidReversal_qDivPow (q : k) (n : ℕ) (x : QuantumGroup R v) :
    braidReversal (qDivPow q n x) = qDivPow q n (braidReversal x) := by
  rw [qDivPow, map_smul, braidReversal_pow, qDivPow]

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

lemma braidEquivOfNotRoot_symm_apply (R : D.RootDatum Y) (i : I) (x : QuantumGroup R v) :
    (braidEquivOfNotRoot R hv i).symm x =
      braidReversal (braidEquivOfNotRoot R hv i (braidReversal x)) :=
  rfl

/-- **Lusztig's `Tᵢ⁻¹ = T'_{i,-1}` on `Eⱼ^{(n)}`** ([Lus] 37.1.3): for `j ≠ i`,
`Tᵢ⁻¹(Eⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{-r} Eᵢ^{(r)} Eⱼ^{(n)} Eᵢ^{(s)}`. -/
theorem braidEquivOfNotRoot_symm_qDivPow_E_ne (R : D.RootDatum Y) {i j : I} (hji : j ≠ i)
    (n : ℕ) : (braidEquivOfNotRoot R hv i).symm (qDivPow (v ^ D.d j) n (E R v j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i)⁻¹ ^ r) •
        (qDivPow (v ^ D.d i) r (E R v i) * qDivPow (v ^ D.d j) n (E R v j) *
          qDivPow (v ^ D.d i) (negA D i j * n - r) (E R v i)) := by
  rw [braidEquivOfNotRoot_symm_apply, braidReversal_qDivPow, braidReversal_E,
    braidEquivOfNotRoot_qDivPow_E_ne hv R hji, braidEjDiv, map_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  simp only [map_smul, braidReversal_mul, braidReversal_qDivPow, braidReversal_E, mul_assoc]

/-- **Lusztig's `Tᵢ⁻¹ = T'_{i,-1}` on `Fⱼ^{(n)}`** ([Lus] 37.1.3): for `j ≠ i`,
`Tᵢ⁻¹(Fⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{r} Fᵢ^{(s)} Fⱼ^{(n)} Fᵢ^{(r)}`. -/
theorem braidEquivOfNotRoot_symm_qDivPow_F_ne (R : D.RootDatum Y) {i j : I} (hji : j ≠ i)
    (n : ℕ) : (braidEquivOfNotRoot R hv i).symm (qDivPow (v ^ D.d j) n (F R v j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i) ^ r) •
        (qDivPow (v ^ D.d i) (negA D i j * n - r) (F R v i) * qDivPow (v ^ D.d j) n (F R v j) *
          qDivPow (v ^ D.d i) r (F R v i)) := by
  rw [braidEquivOfNotRoot_symm_apply, braidReversal_qDivPow, braidReversal_F,
    braidEquivOfNotRoot_qDivPow_F_ne hv R hji, braidFjDiv, map_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  simp only [map_smul, braidReversal_mul, braidReversal_qDivPow, braidReversal_F, mul_assoc]

/-- **Lusztig's `Tᵢ⁻¹ = T'_{i,-1}` on `Eᵢ^{(n)}`** ([Lus] 37.1.3):
`Tᵢ⁻¹(Eᵢ^{(n)}) = (-1)^n vᵢ^{-n(n-1)} K̃_{-ni} Fᵢ^{(n)}`. -/
theorem braidEquivOfNotRoot_symm_qDivPow_E_self (R : D.RootDatum Y) (i : I) (n : ℕ) :
    (braidEquivOfNotRoot R hv i).symm (qDivPow (v ^ D.d i) n (E R v i)) =
      ((-1) ^ n * (v ^ D.d i)⁻¹ ^ (n * (n - 1))) •
        (K R v (-(n • ktilde R i)) * qDivPow (v ^ D.d i) n (F R v i)) := by
  rw [braidEquivOfNotRoot_symm_apply, braidReversal_qDivPow, braidReversal_E,
    braidEquivOfNotRoot_qDivPow_E_self hv R, map_smul, braidReversal_mul, braidReversal_K,
    braidReversal_qDivPow, braidReversal_F]

/-- **Lusztig's `Tᵢ⁻¹ = T'_{i,-1}` on `Fᵢ^{(n)}`** ([Lus] 37.1.3):
`Tᵢ⁻¹(Fᵢ^{(n)}) = (-1)^n vᵢ^{n(n-1)} Eᵢ^{(n)} K̃_{ni}`. -/
theorem braidEquivOfNotRoot_symm_qDivPow_F_self (R : D.RootDatum Y) (i : I) (n : ℕ) :
    (braidEquivOfNotRoot R hv i).symm (qDivPow (v ^ D.d i) n (F R v i)) =
      ((-1) ^ n * (v ^ D.d i) ^ (n * (n - 1))) •
        (qDivPow (v ^ D.d i) n (E R v i) * K R v (n • ktilde R i)) := by
  rw [braidEquivOfNotRoot_symm_apply, braidReversal_qDivPow, braidReversal_F,
    braidEquivOfNotRoot_qDivPow_F_self hv R, map_smul, braidReversal_mul, braidReversal_K,
    braidReversal_qDivPow, braidReversal_E, smul_neg, neg_neg]

end Inverse

end LieLean.QuantumGroup
