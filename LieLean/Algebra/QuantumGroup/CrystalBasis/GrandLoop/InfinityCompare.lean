/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityString
import LieLean.Algebra.QuantumGroup.CrystalBasis.NegativePart

/-!
# `π_λ : U⁻ → V(λ)` and Kashiwara's operators

For dominant `λ` let `π_λ : U⁻ → V(λ)`, `u ↦ u v_λ` (`GrandLoop.evq`). We compare Kashiwara's
operators `ẽᵢ`, `f̃ᵢ` on `U⁻` (`QuantumGroup.NegativePart.kashiwaraE`, `kashiwaraF`, built from
`e'ᵢ = ᵢr`) with those on `V(λ)`:

* for homogeneous `u ∈ U⁻` there is `r` such that `π_λ(f̃ᵢ u) ≡ f̃ᵢ π_λ(u)` and
  `π_λ(ẽᵢ u) ≡ ẽᵢ π_λ(u)` modulo `ϖ L(λ)` whenever `⟨i, λ⟩ ≥ r`
  (`GrandLoop.exists_evq_kashiwara_sub_mem`; [Jan] 10.6 (b));
* `π_λ(L(∞)) ⊆ L(λ)` and `π_λ(f̃ᵢ b) ≡ f̃ᵢ π_λ(b)` modulo `ϖ L(λ)` for the generators
  `b = f̃_{i₁} ⋯ f̃_{iᵣ} 1` of `L(∞)` and all dominant `λ`
  (`GrandLoop.evq_mem_lat_of_mem_latticeInf`, `GrandLoop.evq_fWord_mem_and_sub_mem`,
  `GrandLoop.evq_kashiwaraF_sub_mem_of_forall`; [Jan] Prop. 10.9), by passing from `λ` to
  `μ + λ` with `μ` large through `S ∘ Φ_{μ,λ} : V(μ + λ) → V(λ)`.

The setting is that of the grand loop (`GrandLoop.allProp`): `v` transcendental, `A ⊆ k` a
discrete valuation ring with `k = A[ϖ⁻¹]` and `ϖ ↦ v⁻¹`, and fundamental weights.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.6–10.9 (finite type, lattices at
  `q = 0`).
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### Weights of iterated derivations -/

omit [NeZero v] [CharZero k] in
lemma rDeriv_pow_eq_zero_of_mem (i : I) {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ LusztigF.weightSpace k ν) : (rDeriv D v i ^ (ν i + 1)) y = 0 := by
  induction h : ν i generalizing ν y with
  | zero => rw [zero_add, pow_one]; exact rDeriv_eq_zero_of_mem D v i h hy
  | succ n ih =>
    obtain ⟨μ', rfl⟩ : ∃ μ', ν = μ' + Finsupp.single i 1 := by
      refine ⟨ν - Finsupp.single i 1, ?_⟩
      ext l
      by_cases hl : l = i
      · subst hl; simp [h]
      · simp [Ne.symm hl]
    have hμ' : μ' i = n := by simpa using h
    rw [pow_succ, Module.End.mul_apply]
    exact ih (rDeriv_mem_weightSpace D v i hy) hμ'

lemma pow_smul_mem_of_le {M : Type*} [AddCommGroup M] [Module A M] {L : Submodule A M} {x : M}
    {s s' : ℕ} (hss' : s ≤ s') (h : ϖ ^ s • x ∈ L) : ϖ ^ s' • x ∈ L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hss'
  rw [pow_add, mul_comm, mul_smul]
  exact L.smul_mem _ h

/-! ### Bounded denominators -/

section Large

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- `L(λ)` is a crystal lattice. -/
lemma isCrystalLattice_lat (Λ : Dom R) :
    IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) (lat hvt hR A Λ) :=
  (isCrystalBase (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ).choose

/-- For `y ∈ 'f` there is `s` with `ϖ^s y⁻ v_λ ∈ L(λ)` for all dominant `λ` ([Jan] 10.6 (a)). -/
theorem exists_pow_smul_ev_mem (y : LusztigF k I) :
    ∃ s : ℕ, ∀ Λ : Dom R, ϖ ^ s • ev R v Λ.1 y ∈ lat hvt hR A Λ := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  induction y using FreeAlgebra.induction_wordBasis with
  | zero => exact ⟨0, fun Λ ↦ by simp⟩
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨s', hs'⟩ := hb
    refine ⟨s + s', fun Λ ↦ ?_⟩
    rw [map_add, smul_add]
    exact add_mem (pow_smul_mem_of_le (by omega) (hs Λ)) (pow_smul_mem_of_le (by omega) (hs' Λ))
  | smul c a ha =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨m, b, hb⟩ := hk c
    refine ⟨m + s, fun Λ ↦ ?_⟩
    rw [map_smul, pow_add, mul_smul, smul_comm, ← algebraMap_smul k (ϖ ^ m), smul_smul, hb,
      algebraMap_smul, smul_comm]
    exact Submodule.smul_mem _ b (hs Λ)
  | word w =>
    exact ⟨expo (D := D) w, fun Λ ↦ pow_expo_smul_ev_mem (n := w.length + 1)
      (fun s _ ↦ (hall s).1) hϖv Λ w (by omega)⟩

/-- A uniform `s` for all `rᵢ^m y` ([Jan] 10.6 (a)). -/
theorem exists_pow_smul_ev_rDeriv_mem (i : I) {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ LusztigF.weightSpace k ν) :
    ∃ s : ℕ, ∀ m, ∀ Λ : Dom R, ϖ ^ s • ev R v Λ.1 ((rDeriv D v i ^ m) y) ∈ lat hvt hR A Λ := by
  choose S hS using fun m ↦
    exists_pow_smul_ev_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund ((rDeriv D v i ^ m) y)
  refine ⟨∑ m ∈ range (ν i + 1), S m, fun m Λ ↦ ?_⟩
  by_cases hm : m < ν i + 1
  · exact pow_smul_mem_of_le (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_range.2 hm)) (hS m Λ)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hm)
    rw [show ν i + 1 + d = d + (ν i + 1) by ring, pow_add, Module.End.mul_apply,
      rDeriv_pow_eq_zero_of_mem i hy, map_zero,
      map_zero, smul_zero]
    exact zero_mem _

/-- **[Jan] 10.6 (b), one string**: for `y ∈ 'f_ν` with `ᵢr(y) ∈ J` and `n ∈ ℕ`, if `⟨i, λ⟩` is
large then `f̃ᵢ Fᵢ^{(n)} (y v_λ) ≡ Fᵢ^{(n+1)} (y v_λ)`,
`ẽᵢ Fᵢ^{(n+1)} (y v_λ) ≡ Fᵢ^{(n)} (y v_λ)` and `ẽᵢ (y v_λ) ≡ 0` modulo `ϖ L(λ)`. -/
theorem exists_string_sub_mem (i : I) {ν : I →₀ ℕ} {y : LusztigF k I}
    (hyw : y ∈ LusztigF.weightSpace k ν) (hy : lDeriv D v i y ∈ serreIdeal D v) (n : ℕ) :
    ∃ r : ℤ, ∀ Λ : Dom R, r ≤ Λ.1 (R.coroot i) → ∀ m ≤ n,
      fK hvt hR Λ i ((nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF m
          (ev R v Λ.1 y)) -
        (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF (m + 1)
          (ev R v Λ.1 y) ∈ ϖ • lat hvt hR A Λ ∧
      eK hvt hR Λ i ((nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF
          (m + 1) (ev R v Λ.1 y)) -
        (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF m
          (ev R v Λ.1 y) ∈ ϖ • lat hvt hR A Λ ∧
      eK hvt hR Λ i (ev R v Λ.1 y) ∈ ϖ • lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨s, hs⟩ := exists_pow_smul_ev_rDeriv_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i
    hyw
  refine ⟨s + n + 2 + |R.rootSum ν (R.coroot i)|, fun Λ hΛ m hmn ↦ ?_⟩
  set V := nodeSl2 R v _ hv' (isInt hvt hR Λ) i
  have hq0 : v ^ D.d i ≠ 0 := pow_d_ne_zero i
  have hq := pow_d_ne_one (D := D) hv' i
  have hL := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ
  have hKS := hL.isKashiwaraStable i
  have hxw : ev R v Λ.1 y ∈ V.wt (Λ.1 (R.coroot i) - R.rootSum ν (R.coroot i)) := by
    have := mem_nodeWt_of_mem (i := i) (ev_mem_weightSpace hv' hR Λ.1 hyw)
    change _ ∈ nodeWt R v _ i _
    simpa using this
  obtain ⟨N, η, h1, h2, h3, hx⟩ := V.exists_sum_dF hq0 hq hxw
  have hab := abs_nonneg (R.rootSum ν (R.coroot i))
  have hle := le_abs_self (R.rootSum ν (R.coroot i))
  have hle' := neg_abs_le (R.rootSum ν (R.coroot i))
  have hcomp := component_mem_of_large hϖ hϖv Λ hL i hy s (fun m ↦ hs m Λ) m
    (by omega) h1 h2 h3 hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]
    exact hKS.fTilde_dF_sub_mem ϖ h1 N m fun j hj b hb ↦ hcomp j hj b (by omega)
  · rw [hx]
    exact hKS.eTilde_dF_sub_mem ϖ h1 N m (by omega) fun j hj b hb ↦ hcomp j hj b (by omega)
  · rw [hx]
    rcases N with _ | N
    · simp
    · have hsum := V.eTilde_sum hq0 hq h1 h2 N
      change V.eTilde hq0 hq _ ∈ _
      rw [hsum]
      refine sum_mem fun j _ ↦ (hKS.smul ϖ).dF_mem (h1 (j + 1)) ?_ j
      simpa using hcomp (j + 1) (by omega) 0 (by omega)

end Large

/-! ### `π_λ` and the operators on `U⁻` -/

section Evq

lemma evq_f (Λ : Dom R) (i : I) (u : Um D v) :
    evq hvt Λ (NegativePart.f D v i u) = F R v i • evq hvt Λ u := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact ev_ι_mul Λ.1 i y

lemma evq_df (Λ : Dom R) (i : I) (n : ℕ) (u : Um D v) :
    evq hvt Λ ((NegativePart.boson D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i).df n u)
      = (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF n
        (evq hvt Λ u) := by
  have hpow : ∀ n : ℕ, evq hvt Λ ((NegativePart.f D v i ^ n) u) =
      ((nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).F ^ n)
        (evq hvt Λ u) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, evq_f, ih, pow_succ', Module.End.mul_apply]
      rfl
  rw [BosonModule.df_apply, map_smul, IntegrableSl2.dF_apply, NegativePart.boson_f, hpow,
    IntegrableSl2.qFactorial_inv]

/-- A class in `U⁻_{-ν}` killed by `e'ᵢ` has a representative in `'f_ν` killed by `ᵢr` modulo
`J`. -/
lemma exists_rep_of_e_eq_zero (i : I) {ν : I →₀ ℕ} {c : Um D v} (hc : c ∈ Uw D v ν)
    (he : NegativePart.e D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i c = 0) :
    ∃ y : LusztigF k I, y ∈ LusztigF.weightSpace k ν ∧ lDeriv D v i y ∈ serreIdeal D v ∧
      Submodule.Quotient.mk y = c := by
  obtain ⟨y, hy, rfl⟩ := hc
  refine ⟨y, hy, ?_, rfl⟩
  rw [Submodule.mkQ_apply, NegativePart.e_mk, Submodule.Quotient.mk_eq_zero] at he
  exact mem_serreSubmodule.1 he

/-- The string components of a homogeneous element of `U⁻` are homogeneous. -/
lemma component_mem_Uw (i : I) {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν) (n : ℕ) :
    (NegativePart.boson D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i).component
      (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
      (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) n u ∈
      Uw D v (ν - Finsupp.single i n) := by
  set B := NegativePart.boson D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i
  have hv0 := NeZero.ne v
  have hv' := pow_ne_one_of_transcendental' hvt
  have hsh := B.map_component_shift (NegativePart.pow_d_ne_zero hv0 i)
    (NegativePart.pow_d_ne_one hv' i) B (NegativePart.proj D v) (Finsupp.single i 1)
    (NegativePart.proj_e hv0 hv' i) (NegativePart.proj_f i) n (LusztigF.toZ ν) u
  have hu' : NegativePart.proj D v (LusztigF.toZ ν) u = u :=
    (NegativePart.mem_weightSpace_iff ν u).1 hu
  rw [hu'] at hsh
  change _ ∈ NegativePart.weightSpace D v _
  rw [NegativePart.mem_weightSpace_iff]
  by_cases hn : n ≤ ν i
  · have e : LusztigF.toZ ν - n • Finsupp.single i (1 : ℤ) =
        LusztigF.toZ (ν - Finsupp.single i n) := by
      ext l
      simp only [Finsupp.coe_sub, Pi.sub_apply, LusztigF.toZ_apply, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.coe_tsub]
      split_ifs with h
      · subst h; push_cast [hn]; ring
      · simp
    rw [e] at hsh
    exact hsh.symm
  · have hneg : ¬ 0 ≤ LusztigF.toZ ν - n • Finsupp.single i (1 : ℤ) := fun h ↦ by
      have := h i
      simp at this
      omega
    have h0 : ∀ x : Um D v, NegativePart.proj D v
        (LusztigF.toZ ν - n • Finsupp.single i (1 : ℤ)) x = 0 := fun x ↦ by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [NegativePart.proj_mk, LusztigF.zWeightProj, ite_eq_right hneg]
      rfl
    rw [h0] at hsh
    rw [hsh, map_zero]

end Evq

section LargeU

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- **[Jan] 10.6 (b)**: for homogeneous `u ∈ U⁻` there is `r` such that
`π_λ(f̃ᵢ u) ≡ f̃ᵢ π_λ(u)` and `π_λ(ẽᵢ u) ≡ ẽᵢ π_λ(u)` modulo `ϖ L(λ)` for all dominant `λ` with
`⟨i, λ⟩ ≥ r`. -/
theorem exists_evq_kashiwara_sub_mem (i : I) {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν) :
    ∃ r : ℤ, ∀ Λ : Dom R, r ≤ Λ.1 (R.coroot i) →
      evq hvt Λ (NegativePart.kashiwaraF D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i u)
          - fK hvt hR Λ i (evq hvt Λ u) ∈ ϖ • lat hvt hR A Λ ∧
      evq hvt Λ (NegativePart.kashiwaraE D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i u)
          - eK hvt hR Λ i (evq hvt Λ u) ∈ ϖ • lat hvt hR A Λ := by
  have hv0 := NeZero.ne v
  have hv' := pow_ne_one_of_transcendental' hvt
  set B := NegativePart.boson D v hv0 hv' i
  have hq0 := NegativePart.pow_d_ne_zero hv0 (D := D) i
  have hq := NegativePart.pow_d_ne_one (D := D) hv' i
  obtain ⟨N, -, hm⟩ := B.exists_sum_component hq0 hq u
  set c := fun n ↦ B.component hq0 hq n u
  have hrep : ∀ n, ∃ y : LusztigF k I, y ∈ LusztigF.weightSpace k (ν - Finsupp.single i n) ∧
      lDeriv D v i y ∈ serreIdeal D v ∧ Submodule.Quotient.mk y = c n := fun n ↦
    exists_rep_of_e_eq_zero (hvt := hvt) i (component_mem_Uw (hvt := hvt) i hu n)
      (B.e_component hq0 hq n u)
  choose y hyw hyl hyc using hrep
  choose r hr using fun n ↦ exists_string_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i
    (hyw n) (hyl n) n
  refine ⟨∑ n ∈ range N, |r n|, fun Λ hΛ ↦ ?_⟩
  have hrn : ∀ n ∈ range N, r n ≤ Λ.1 (R.coroot i) := fun n hn ↦
    (le_abs_self _).trans ((single_le_sum (fun j _ ↦ abs_nonneg (r j)) hn).trans hΛ)
  have hev : ∀ n, evq hvt Λ (c n) = ev R v Λ.1 (y n) := fun n ↦ by rw [← hyc n]; rfl
  have hker : ∀ n, B.e (c n) = 0 := fun n ↦ B.e_component hq0 hq n u
  constructor
  · rw [hm]
    rw [map_sum, map_sum, map_sum, map_sum, ← sum_sub_distrib]
    refine sum_mem fun n hn ↦ ?_
    change evq hvt Λ (B.fTilde hq0 hq (B.df n (c n))) - _ ∈ _
    rw [BosonModule.fTilde_df hq0 hq (hker n), evq_df (hR := hR), evq_df (hR := hR), hev]
    have := (hr n Λ (hrn n hn) n le_rfl).1
    rw [← neg_mem_iff, neg_sub]
    exact this
  · rw [hm]
    rw [map_sum, map_sum, map_sum, map_sum, ← sum_sub_distrib]
    refine sum_mem fun n hn ↦ ?_
    change evq hvt Λ (B.eTilde hq0 hq (B.df n (c n))) - _ ∈ _
    rcases n with _ | n
    · rw [BosonModule.df_zero, BosonModule.eTilde_of_ker hq0 hq (hker 0), map_zero, zero_sub,
        neg_mem_iff, hev]
      exact (hr 0 Λ (hrn 0 hn) 0 le_rfl).2.2
    · rw [BosonModule.eTilde_df_succ hq0 hq (hker _), evq_df (hR := hR), evq_df (hR := hR), hev]
      have := (hr (n + 1) Λ (hrn _ hn) n (by omega)).2.1
      rw [← neg_mem_iff, neg_sub]
      exact this

end LargeU

/-! ### All dominant weights: [Jan] Prop. 10.9 -/

/-- `Φ_{λ₁,λ₂}(L(λ₁ + λ₂)) ⊆ L(λ₁) ⊗ L(λ₂)`. -/
lemma tensorEmb_mem_LL [Finite I] [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) {Λ₁ Λ₂ : Dom R} (hA : ∀ s, PropA hvt hR A s)
    {x : IrreducibleModule R v (Λ₁ + Λ₂).1}
    (hx : x ∈ lat hvt hR A (Λ₁ + Λ₂)) : tensorEmb hvt hR Λ₁.2 Λ₂.2 x ∈ LL hvt hR A Λ₁ Λ₂ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    change tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) ∈ _
    rw [tensorEmb_fW]
    have hz := fW_tmul_mem_LL (hvt := hvt) (hR := hR) (A := A) Λ₁ Λ₂ [] []
    have hzw := fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [] []
    simp only [fW_nil, LusztigF.wordWeight_nil, add_zero] at hz hzw
    exact fTw_mem_LL hϖ hϖv w (ν := 0) (fun s _ ↦ hA s) hz hzw
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_tensorEmb]; exact Submodule.smul_mem _ c ha

lemma evq_add [Finite I] (Λ₁ Λ₂ : Dom R) (u : Um D v) :
    Sh hvt hR Λ₁ Λ₂ (tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) u)) = evq hvt Λ₂ u := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact Sh_tensorEmb_ev Λ₁ Λ₂ y

section All

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- **[Jan] Prop. 10.9, inductive step**: if `u ∈ U⁻_{-ν}` and `π_λ(u) ∈ L(λ)` for all dominant
`λ`, then `π_λ(f̃ᵢ u) ≡ f̃ᵢ π_λ(u)` modulo `ϖ L(λ)` for all dominant `λ`. -/
theorem evq_kashiwaraF_sub_mem_of_forall {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν)
    (hL : ∀ Λ : Dom R, evq hvt Λ u ∈ lat hvt hR A Λ) (i : I) (Λ : Dom R) :
    evq hvt Λ (NegativePart.kashiwaraF D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i u)
      - fK hvt hR Λ i (evq hvt Λ u) ∈ ϖ • lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨r, hr⟩ := exists_evq_kashiwara_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i hu
  obtain ⟨Λi, hΛi⟩ := hfund i
  let μ : Dom R := ⟨(r.toNat : ℤ) • Λi.1, fun j ↦ by
    rw [AddMonoidHom.smul_apply]; exact smul_nonneg (by positivity) (Λi.2 j)⟩
  have hμ : r ≤ (μ + Λ).1 (R.coroot i) := by
    change r ≤ (r.toNat : ℤ) • Λi.1 (R.coroot i) + Λ.1 (R.coroot i)
    simp only [hΛi i, ↓reduceIte, smul_eq_mul, mul_one]
    have := Λ.2 i
    omega
  have h1 := (hr (μ + Λ) hμ).1
  set X := evq hvt (μ + Λ) u
  have hX : X ∈ lat hvt hR A (μ + Λ) := hL (μ + Λ)
  obtain ⟨y, hy, rfl⟩ := hu
  have hXw : X ∈ wsp (μ + Λ) ν := ev_mem_weightSpace hv' hR _ hy
  -- `T = S ∘ Φ`
  have key : evq hvt Λ (NegativePart.kashiwaraF D v (NeZero.ne v) hv' i
        (Submodule.mkQ _ y)) - fK hvt hR Λ i (evq hvt Λ (Submodule.mkQ _ y)) =
      Sh hvt hR μ Λ (tensorEmb hvt hR μ.2 Λ.2 (evq hvt (μ + Λ)
        (NegativePart.kashiwaraF D v (NeZero.ne v) hv' i (Submodule.mkQ _ y)) -
          fK hvt hR (μ + Λ) i X))
        + (Sh hvt hR μ Λ (fT hvt hR μ Λ i (tensorEmb hvt hR μ.2 Λ.2 X)) -
          fK hvt hR Λ i (Sh hvt hR μ Λ (tensorEmb hvt hR μ.2 Λ.2 X))) := by
    rw [map_sub, map_sub, evq_add, ← map_kashiwaraF hv' (isInt hvt hR (μ + Λ)) i
      (isIntT hvt hR μ Λ), evq_add]
    abel
  rw [key]
  refine add_mem ?_ ?_
  · -- `T (ϖ L(μ+λ)) ⊆ ϖ L(λ)`
    obtain ⟨z₀, hz₀, -, hz⟩ := TensorModule.exists_smul_weight (S := ⊤)
      (by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)) h1 Submodule.mem_top
    rw [hz]
    refine Sh_mem_smul ?_
    rw [smul_tensorEmb]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (tensorEmb_mem_LL hϖ hϖv (fun s ↦ (hall s).1) hz₀)
  · exact Sh_fT_sub_mem hϖ hϖv (d := ν.degree) (fun s _ ↦ (hall s).1) (fun s _ ↦ (hall s).2.1)
      (fun s _ ↦ (hall s).2.2.1) i rfl (tensorEmb_mem_LL hϖ hϖv (fun s ↦ (hall s).1) hX)
      (map_mem_weightSpace _ hXw)

/-- **[Jan] Prop. 10.9**: `π_λ(f̃_{i₁} ⋯ f̃_{iᵣ} 1) ∈ L(λ)` and
`π_λ(f̃ᵢ f̃_w 1) ≡ f̃ᵢ π_λ(f̃_w 1)` modulo `ϖ L(λ)`, for all dominant `λ`. -/
theorem evq_fWord_mem_and_sub_mem (w : List I) :
    (∀ Λ : Dom R, evq hvt Λ (NegativePart.fWord D v (NeZero.ne v)
      (pow_ne_one_of_transcendental' hvt) w) ∈ lat hvt hR A Λ) ∧
    ∀ (i : I) (Λ : Dom R), evq hvt Λ (NegativePart.kashiwaraF D v (NeZero.ne v)
      (pow_ne_one_of_transcendental' hvt) i (NegativePart.fWord D v (NeZero.ne v)
        (pow_ne_one_of_transcendental' hvt) w)) - fK hvt hR Λ i (evq hvt Λ
          (NegativePart.fWord D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) w)) ∈
        ϖ • lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hmem : ∀ w, (∀ Λ : Dom R, evq hvt Λ (NegativePart.fWord D v (NeZero.ne v) hv' w) ∈
      lat hvt hR A Λ) := by
    intro w
    induction w with
    | nil =>
      intro Λ
      change ev R v Λ.1 1 ∈ _
      rw [ev_one]
      exact IrreducibleModule.hwv_mem_lattice hR hv' Λ.2 A
    | cons i w ih =>
      intro Λ
      have h := evq_kashiwaraF_sub_mem_of_forall (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
        (NegativePart.fWord_mem_weightSpace (NeZero.ne v) hv' w) ih i Λ
      rw [NegativePart.fWord_cons]
      have h2 := add_mem (IntegrableSl2.smul_le ϖ h)
        (kashiwaraF_mem_lat Λ i (ih Λ))
      simpa using h2
  exact ⟨hmem w, fun i Λ ↦ evq_kashiwaraF_sub_mem_of_forall (hvt := hvt) (hR := hR) hinj hϖ hϖv
    hk hfund (NegativePart.fWord_mem_weightSpace (NeZero.ne v) hv' w) (hmem w) i Λ⟩

/-- **[Jan] Prop. 10.9**: `π_λ(L(∞)) ⊆ L(λ)` for every dominant `λ`. -/
theorem evq_mem_lat_of_mem_latticeInf {u : Um D v}
    (hu : u ∈ NegativePart.latticeInf D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) A)
    (Λ : Dom R) : evq hvt Λ u ∈ lat hvt hR A Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    exact (evq_fWord_mem_and_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w).1 Λ
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul k c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ c ha

end All

end GrandLoop

end LieLean.QuantumGroup
