/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityLattice
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase

/-!
# The crystal base `(L(∞), B(∞))` of `U⁻`

In the setting of the grand loop, `B(∞)` (the nonzero classes of the `f̃_{i₁} ⋯ f̃_{iᵣ} 1` in
`L(∞)/ϖ L(∞)`, `NegativePart.baseInf`) has the properties of a crystal base of `U⁻`
([KS97] Def. 2.3.2, [Jan] 10.11–10.12):

* the classes of distinct elements of `B(∞)` of one weight are linearly independent over `A/ϖA`
  (`GrandLoop.coeff_mem_of_sum_fWi_mem`), and `B(∞)` spans `L(∞)/ϖ L(∞)` (`GrandLoop.span_BInf`);
* `ẽᵢ B(∞) ⊆ B(∞) ∪ {0}`, `f̃ᵢ B(∞) ⊆ B(∞)`, and `f̃ᵢ b = b' ↔ ẽᵢ b' = b`
  (`GrandLoop.eQinf_mem_baseInf`, `GrandLoop.fQinf_eq_iff`).

We obtain the crystal of `B(∞)` (`GrandLoop.crystalInf`, [KS97] Example 3.1.3):
`wt(f̃_w 1) = -wt w`, `εᵢ(b) = max {n | ẽᵢⁿ b ≠ 0}` and `φᵢ = εᵢ + ⟨i, wt⟩`.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.11, 10.12 (finite type).
* [KS97] M. Kashiwara, Y. Saito, *Geometric construction of crystal bases*, Duke Math. J. 89
  (1997), arXiv:q-alg/9606009, §2.3, §3.1.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### The operators on `L(∞)/ϖ L(∞)` -/

variable (hvt A ϖ) in
/-- `L(∞)/ϖ L(∞)`. -/
abbrev QInf : Type _ := latInf hvt A ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A (latInf (D := D) hvt A))

variable (hvt A) in
/-- `f̃_w 1` as an element of `L(∞)`. -/
abbrev fwInf (w : List I) : latInf (D := D) hvt A :=
  ⟨fWi hvt w, NegativePart.fWord_mem_latticeInf _ _ w⟩

lemma quotQ_map {f : Module.End k (Um D v)} (hf : ∀ m ∈ latInf (D := D) hvt A, f m ∈ latInf hvt A) :
    (Ideal.span {ϖ} • ⊤ : Submodule A (latInf (D := D) hvt A)) ≤
      (Ideal.span {ϖ} • ⊤ : Submodule A (latInf (D := D) hvt A)).comap
        ((f.restrictScalars A).restrict hf) := fun x hx ↦ by
  rw [Submodule.ideal_span_singleton_smul] at hx ⊢
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- An endomorphism of `U⁻` preserving `L(∞)`, on `L(∞)/ϖ L(∞)`. -/
abbrev endQ {f : Module.End k (Um D v)} (hf : ∀ m ∈ latInf (D := D) hvt A, f m ∈ latInf hvt A) :
    QInf (D := D) hvt A ϖ →ₗ[A] QInf (D := D) hvt A ϖ :=
  Submodule.mapQ _ _ ((f.restrictScalars A).restrict hf) (quotQ_map hf)

lemma endQ_mk {f : Module.End k (Um D v)} (hf : ∀ m ∈ latInf (D := D) hvt A, f m ∈ latInf hvt A)
    (x : latInf (D := D) hvt A) :
    endQ (ϖ := ϖ) hf (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨f x, hf x x.2⟩ := rfl

lemma kashiwaraF_mem_latInf' (i : I) :
    ∀ m ∈ latInf (D := D) hvt A,
      NegativePart.kashiwaraF D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i m ∈
        latInf hvt A :=
  fun _ hm ↦ NegativePart.kashiwaraF_mem_latticeInf _ _ i hm

variable (hvt) in
/-- Kashiwara's `ẽᵢ` on `U⁻`. -/
abbrev kE (i : I) : Module.End k (Um D v) :=
  NegativePart.kashiwaraE D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i

variable (hvt) in
/-- Kashiwara's `f̃ᵢ` on `U⁻`. -/
abbrev kF (i : I) : Module.End k (Um D v) :=
  NegativePart.kashiwaraF D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i

lemma kE_kF (i : I) (u : Um D v) : kE (D := D) hvt i (kF hvt i u) = u :=
  NegativePart.kashiwaraE_kashiwaraF _ _ i u

/-- `ẽᵢ f̃_w 1 = 0` if `wt w` has no `i`-component. -/
lemma kE_fWi_eq_zero (i : I) {w : List I} (h : wordWeight w i = 0) :
    kE (D := D) hvt i (fWi hvt w) = 0 := by
  have he : NegativePart.e D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i
      (fWi hvt w) = 0 := by
    obtain ⟨y, hy, hyw⟩ := fWi_mem_Uw (D := D) (v := v) (hvt := hvt) w
    rw [← hyw, Submodule.mkQ_apply, NegativePart.e_mk, bosonE_eq_zero_of_mem i h hy]
    rfl
  exact (NegativePart.boson D v _ _ i).eTilde_eq_zero_iff _ _ _ |>.2 he

lemma proj_mem_latInf (γ : I →₀ ℤ) {u : Um D v} (hu : u ∈ latInf (D := D) hvt A) :
    NegativePart.proj D v γ u ∈ latInf (D := D) hvt A := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    rw [proj_of_mem_Uw (NegativePart.fWord_mem_weightSpace _ _ w)]
    split_ifs
    · exact NegativePart.fWord_mem_latticeInf _ _ w
    · exact zero_mem _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul k c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ c ha

lemma proj_mem_smul_latInf (γ : I →₀ ℤ) {u : Um D v} (hu : u ∈ ϖ • latInf (D := D) hvt A) :
    NegativePart.proj D v γ u ∈ ϖ • latInf (D := D) hvt A :=
  LinearMap.map_mem_smul_of_mem ϖ (fun _ hm ↦ proj_mem_latInf γ hm) hu


/-- `ẽᵢ` kills `U⁻_{-μ}` if `μᵢ = 0`. -/
lemma kE_eq_zero_of_mem (i : I) {μ : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v μ) (h : μ i = 0) :
    kE (D := D) hvt i u = 0 := by
  have he : NegativePart.e D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i u = 0 := by
    obtain ⟨y, hy, rfl⟩ := hu
    rw [Submodule.mkQ_apply, NegativePart.e_mk, bosonE_eq_zero_of_mem i h hy]
    rfl
  exact (NegativePart.boson D v _ _ i).eTilde_eq_zero_iff _ _ _ |>.2 he

/-- `ẽᵢⁿ U⁻_{-ν} ⊆ U⁻_{-(ν - n i)}` for `n ≤ νᵢ`, and `ẽᵢ^{νᵢ+1}` kills `U⁻_{-ν}`. -/
lemma kE_pow_mem (i : I) {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν) :
    ∀ n ≤ ν i, (kE (D := D) hvt i ^ n) u ∈ Uw D v (ν - Finsupp.single i n) := by
  intro n
  induction n with
  | zero => intro _; simpa using hu
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have e : ν - Finsupp.single i n = (ν - Finsupp.single i (n + 1)) + Finsupp.single i 1 := by
      ext l
      by_cases hl : l = i
      · subst hl; simp; omega
      · simp [Ne.symm hl]
    rw [e] at h1
    rw [pow_succ', Module.End.mul_apply]
    exact NegativePart.kashiwaraE_mem_weightSpace _ _ i h1

lemma kE_pow_eq_zero (i : I) {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν) :
    (kE (D := D) hvt i ^ (ν i + 1)) u = 0 := by
  rw [pow_succ', Module.End.mul_apply]
  exact kE_eq_zero_of_mem i (kE_pow_mem i hu (ν i) le_rfl) (by simp)

/-- The weight of an element of `L(∞)` congruent to `f̃_{w'} 1` modulo `ϖ L(∞)`. -/
lemma wordWeight_eq_of_mem_Uw {μ : I →₀ ℕ} {u : Um D v} (huw : u ∈ Uw D v μ)
    (h0 : u ∉ ϖ • latInf hvt A) {w' : List I} (h : u - fWi hvt w' ∈ ϖ • latInf hvt A) :
    wordWeight w' = μ := by
  by_contra hne
  have := proj_mem_smul_latInf (toZ μ) h
  rw [map_sub, proj_of_mem_Uw huw, proj_of_mem_Uw (fWi_mem_Uw w'), ite_eq_left rfl,
    ite_eq_right (fun h' ↦ hne (toZ_injective h')), sub_zero] at this
  exact h0 this


section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
lemma kashiwaraE_mem_latInf' (i : I) :
    ∀ m ∈ latInf (D := D) hvt A,
      NegativePart.kashiwaraE D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i m ∈
        latInf hvt A :=
  fun _ hm ↦ kashiwaraE_mem_latticeInf (hR := hR) hinj hϖ hϖv hk hfund i hm

include hR in
/-- Congruent elements of `B(∞)` have the same weight. -/
lemma wordWeight_eq_of_sub_mem_latInf {w w' : List I}
    (h : fWi (D := D) hvt w - fWi hvt w' ∈ ϖ • latInf hvt A) : wordWeight w = wordWeight w' := by
  by_contra hne
  have := proj_mem_smul_latInf (toZ (wordWeight w)) h
  rw [map_sub, proj_of_mem_Uw (fWi_mem_Uw w), proj_of_mem_Uw (fWi_mem_Uw w'), ite_eq_left rfl,
    ite_eq_right (fun h' ↦ hne (toZ_injective h').symm), sub_zero] at this
  exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w this

/-- A dominant weight that is large for `ν` and for the bound of
`GrandLoop.exists_evq_kashiwara_sub_mem` for `f̃_w 1`. -/
lemma exists_large (i : I) (w : List I) :
    ∃ Λ : Dom R, (∀ j, ((wordWeight w).degree : ℤ) ≤ Λ.1 (R.coroot j)) ∧
      evq hvt Λ (kF hvt i (fWi hvt w)) - fK hvt hR Λ i (evq hvt Λ (fWi hvt w)) ∈
        ϖ • lat hvt hR A Λ ∧
      evq hvt Λ (kE hvt i (fWi hvt w)) - eK hvt hR Λ i (evq hvt Λ (fWi hvt w)) ∈
        ϖ • lat hvt hR A Λ := by
  obtain ⟨r, hr⟩ := exists_evq_kashiwara_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i
    (fWi_mem_Uw w)
  obtain ⟨Λ, hΛ⟩ := exists_dom_ge hfund (max (wordWeight w).degree r.toNat)
  refine ⟨Λ, fun j ↦ le_trans (by exact_mod_cast le_max_left _ _) (hΛ j), hr Λ ?_⟩
  have := hΛ i
  have := le_max_right (wordWeight w).degree r.toNat
  omega

/-- `ẽᵢ (f̃_w v_λ)` modulo `ϖ L(λ)` from the comparison. -/
lemma evq_kE_sub_eK_fW_mem (i : I) (w : List I) {Λ : Dom R}
    (h : evq hvt Λ (kE hvt i (fWi hvt w)) - eK hvt hR Λ i (evq hvt Λ (fWi hvt w)) ∈
      ϖ • lat hvt hR A Λ) :
    evq hvt Λ (kE hvt i (fWi hvt w)) - eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ := by
  have h2 := LinearMap.map_mem_smul_of_mem ϖ
    (fun m hm ↦ (isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ).kashiwaraE_mem
      i m hm) (evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w Λ)
  rw [map_sub] at h2
  simpa using add_mem h h2

include hR in
/-- **[Jan] Prop. 10.12**: `ẽᵢ B(∞) ⊆ B(∞) ∪ {0}`, on representatives. -/
theorem kE_fWi_cases (i : I) (w : List I) :
    kE (D := D) hvt i (fWi hvt w) ∈ ϖ • latInf hvt A ∨
      ∃ w', kE (D := D) hvt i (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf hvt A := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  by_cases hνi : wordWeight w i = 0
  · left; rw [kE_fWi_eq_zero i hνi]; exact zero_mem _
  obtain ⟨μ, hμ⟩ : ∃ μ, wordWeight w = μ + Finsupp.single i 1 := by
    refine ⟨wordWeight w - Finsupp.single i 1, ?_⟩
    ext l
    by_cases hl : l = i
    · subst hl; simp; omega
    · simp [Ne.symm hl]
  have hew : kE (D := D) hvt i (fWi hvt w) ∈ Uw D v μ :=
    NegativePart.kashiwaraE_mem_weightSpace _ _ i (hμ ▸ fWi_mem_Uw w)
  have heL : kE (D := D) hvt i (fWi hvt w) ∈ latInf hvt A :=
    kashiwaraE_mem_latticeInf (hR := hR) hinj hϖ hϖv hk hfund i
      (NegativePart.fWord_mem_latticeInf _ _ w)
  obtain ⟨Λ, hΛ, -, hE⟩ := exists_large (hR := hR) hinj hϖ hϖv hk hfund i w
  have hΛμ : ∀ j, (μ.degree : ℤ) ≤ Λ.1 (R.coroot j) := fun j ↦ by
    have := hΛ j; rw [hμ, map_add] at this; push_cast at this; omega
  have h1 := evq_kE_sub_eK_fW_mem hinj hϖ hϖv hk hfund i w hE
  have hiff := mem_smul_latInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛμ heL hew
  by_cases h0 : evq hvt Λ (kE (D := D) hvt i (fWi hvt w)) ∈ ϖ • lat hvt hR A Λ
  · exact Or.inl (hiff.2 h0)
  rcases (hall w.length).2.1 Λ w rfl i with hB | ⟨w', hB⟩
  · exact absurd (by simpa using add_mem h1 hB) h0
  have h2 : evq hvt Λ (kE (D := D) hvt i (fWi hvt w)) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ := by
    simpa using add_mem h1 hB
  have hw' : wordWeight w' = μ :=
    wordWeight_eq_of_sub_mem hvt hR A ϖ Λ (evq_mem_wsp hR hew Λ) h0 h2
  refine Or.inr ⟨w', ?_⟩
  have hdw : kE (D := D) hvt i (fWi hvt w) - fWi hvt w' ∈ Uw D v μ :=
    sub_mem hew (hw' ▸ fWi_mem_Uw w')
  rw [mem_smul_latInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛμ
    (sub_mem heL (NegativePart.fWord_mem_latticeInf _ _ w')) hdw, map_sub]
  have h3 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w' Λ
  simpa using sub_mem h2 h3

include hR in
/-- **[Jan] Prop. 10.12**: `f̃ᵢ ẽᵢ b = b` for `b ∈ B(∞)` with `ẽᵢ b ≠ 0`, on representatives. -/
theorem fWi_sub_mem_of_kE (i : I) {w w' : List I}
    (h0 : kE (D := D) hvt i (fWi hvt w) ∉ ϖ • latInf hvt A)
    (h : kE (D := D) hvt i (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf hvt A) :
    fWi (D := D) hvt w - fWi hvt (i :: w') ∈ ϖ • latInf hvt A := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  by_cases hνi : wordWeight w i = 0
  · exact absurd (by rw [kE_fWi_eq_zero i hνi]; exact zero_mem _) h0
  obtain ⟨μ, hμ⟩ : ∃ μ, wordWeight w = μ + Finsupp.single i 1 := by
    refine ⟨wordWeight w - Finsupp.single i 1, ?_⟩
    ext l
    by_cases hl : l = i
    · subst hl; simp; omega
    · simp [Ne.symm hl]
  have hew : kE (D := D) hvt i (fWi hvt w) ∈ Uw D v μ :=
    NegativePart.kashiwaraE_mem_weightSpace _ _ i (hμ ▸ fWi_mem_Uw w)
  have heL : kE (D := D) hvt i (fWi hvt w) ∈ latInf hvt A :=
    kashiwaraE_mem_latticeInf (hR := hR) hinj hϖ hϖv hk hfund i
      (NegativePart.fWord_mem_latticeInf _ _ w)
  obtain ⟨Λ, hΛ, -, hE⟩ := exists_large (hR := hR) hinj hϖ hϖv hk hfund i w
  have hΛμ : ∀ j, (μ.degree : ℤ) ≤ Λ.1 (R.coroot j) := fun j ↦ by
    have := hΛ j; rw [hμ, map_add] at this; push_cast at this; omega
  have h1 := evq_kE_sub_eK_fW_mem hinj hϖ hϖv hk hfund i w hE
  have hev0 : evq hvt Λ (kE (D := D) hvt i (fWi hvt w)) ∉ ϖ • lat hvt hR A Λ := fun h' ↦
    h0 ((mem_smul_latInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛμ heL hew).2 h')
  -- `π_λ(ẽᵢ f̃_w 1) ≡ f̃_{w'} v_λ`
  have hdL : kE (D := D) hvt i (fWi hvt w) - fWi hvt w' ∈ latInf hvt A :=
    sub_mem heL (NegativePart.fWord_mem_latticeInf _ _ w')
  have h2 : evq hvt Λ (kE (D := D) hvt i (fWi hvt w)) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ := by
    have hs : evq hvt Λ (kE (D := D) hvt i (fWi hvt w) - fWi hvt w') ∈ ϖ • lat hvt hR A Λ := by
      obtain ⟨u₀, hu₀, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      rw [← he, ← algebraMap_smul k ϖ u₀, map_smul, algebraMap_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _
        (evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund hu₀ Λ)
    rw [map_sub] at hs
    have h3 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w' Λ
    simpa using add_mem hs h3
  have hw' : wordWeight w' = μ :=
    wordWeight_eq_of_sub_mem hvt hR A ϖ Λ (evq_mem_wsp hR hew Λ) hev0 h2
  have hΛw' : ∀ j, ((wordWeight w').degree : ℤ) ≤ Λ.1 (R.coroot j) := hw' ▸ hΛμ
  have hw0 := fW_notMem_of_large (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (A := A) w hΛ
  have hw'0 := fW_notMem_of_large (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (A := A) w' hΛw'
  have hEw : eK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ := by
    have := sub_mem h2 h1
    rw [show evq hvt Λ (kE (D := D) hvt i (fWi hvt w)) - fW hvt hR Λ w' -
      (evq hvt Λ (kE (D := D) hvt i (fWi hvt w)) - eK hvt hR Λ i (fW hvt hR Λ w)) =
      eK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ w' by abel] at this
    exact this
  have hF := (fK_sub_mem_iff (fun r ↦ (hall r).2.2.1) Λ i hw'0 hw0).2 hEw
  -- pull back to `L(∞)`
  have hww : wordWeight (i :: w') = wordWeight w := by
    rw [wordWeight_cons, hw', hμ, add_comm]
  have hdw : fWi (D := D) hvt w - fWi hvt (i :: w') ∈ Uw D v (wordWeight w) :=
    sub_mem (fWi_mem_Uw w) (hww ▸ fWi_mem_Uw (i :: w'))
  rw [mem_smul_latInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛ
    (sub_mem (NegativePart.fWord_mem_latticeInf _ _ w) (NegativePart.fWord_mem_latticeInf _ _ _))
    hdw, map_sub]
  have h4 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w Λ
  have h5 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (i :: w') Λ
  have hF' : fW hvt hR Λ (i :: w') - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ := by
    rw [fW_cons]; exact hF
  have := sub_mem (sub_mem h4 h5) hF'
  convert this using 1
  abel

include hR in
/-- **[Jan] Prop. 10.11 (b)**: distinct elements of `B(∞)` of one weight are linearly
independent over `A/ϖA`, on representatives. -/
theorem coeff_mem_of_sum_fWi_mem {ν : I →₀ ℕ} (S : Finset (List I))
    (hS : ∀ w ∈ S, wordWeight w = ν)
    (hd : ∀ w₁ ∈ S, ∀ w₂ ∈ S, w₁ ≠ w₂ → fWi (D := D) hvt w₁ - fWi hvt w₂ ∉ ϖ • latInf hvt A)
    (a : List I → A) (h : ∑ w ∈ S, a w • fWi (D := D) hvt w ∈ ϖ • latInf hvt A) :
    ∀ w ∈ S, a w ∈ Ideal.span {ϖ} := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨Λ, hΛ⟩ := exists_dom_ge hfund ν.degree
  have hcong : ∀ w, evq hvt Λ (fWi hvt w) - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ := fun w ↦
    evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w Λ
  have hevS : ∀ x ∈ ϖ • latInf (D := D) hvt A, evq hvt Λ x ∈ ϖ • lat hvt hR A Λ := by
    intro x hx
    obtain ⟨u₀, hu₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [← algebraMap_smul k ϖ u₀, map_smul, algebraMap_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund hu₀ Λ)
  refine (hall ν.degree).2.2.2.1 Λ ν rfl S hS (fun w hw ↦ ?_) (fun w₁ hw₁ w₂ hw₂ hne h' ↦ ?_) a ?_
  · exact fW_notMem_of_large (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (A := A) w
      ((hS w hw).symm ▸ hΛ)
  · refine hd w₁ hw₁ w₂ hw₂ hne ?_
    have hdw : fWi (D := D) hvt w₁ - fWi hvt w₂ ∈ Uw D v ν :=
      sub_mem (hS w₁ hw₁ ▸ fWi_mem_Uw w₁) (hS w₂ hw₂ ▸ fWi_mem_Uw w₂)
    rw [mem_smul_latInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛ
      (sub_mem (NegativePart.fWord_mem_latticeInf _ _ _)
        (NegativePart.fWord_mem_latticeInf _ _ _)) hdw, map_sub]
    have := add_mem (sub_mem (hcong w₁) (hcong w₂)) h'
    convert this using 1; abel
  · have h1 := hevS _ h
    rw [map_sum] at h1
    have h2 : ∑ w ∈ S, a w • (evq hvt Λ (fWi hvt w) - fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ :=
      sum_mem fun w _ ↦ Submodule.smul_mem _ _ (hcong w)
    have := sub_mem h1 h2
    convert this using 1
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun w _ ↦ ?_
    have e : evq hvt Λ (a w • fWi hvt w) = a w • evq hvt Λ (fWi hvt w) := by
      rw [← algebraMap_smul k (a w) (fWi hvt w), map_smul, algebraMap_smul]
    rw [e, smul_sub]
    abel

/-! ### The crystal `B(∞)` -/

variable (hvt A ϖ) in
/-- `B(∞) ⊆ L(∞)/ϖ L(∞)`. -/
abbrev BInf : Set (QInf (D := D) hvt A ϖ) :=
  NegativePart.baseInf D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) A ϖ

include hR in
lemma mk_fwInf_mem_BInf (w : List I) :
    (Submodule.Quotient.mk (fwInf hvt A w) : QInf (D := D) hvt A ϖ) ∈ BInf hvt A ϖ :=
  ⟨⟨w, rfl⟩, fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w
    ((IntegrableSl2.mk_eq_zero_iff ϖ _).1 h)⟩

omit [Finite I] [IsDomain A] [IsDiscreteValuationRing A] hinj hϖ hϖv hk hfund in
lemma exists_eq_mk_of_mem_BInf {b : QInf (D := D) hvt A ϖ} (hb : b ∈ BInf hvt A ϖ) :
    ∃ w, b = Submodule.Quotient.mk (fwInf hvt A w) := by
  obtain ⟨⟨w, rfl⟩, -⟩ := hb
  exact ⟨w, rfl⟩

variable (hR) in
/-- `ẽᵢ` on `L(∞)/ϖ L(∞)`. -/
def eQInf (i : I) : QInf (D := D) hvt A ϖ →ₗ[A] QInf (D := D) hvt A ϖ :=
  endQ (kashiwaraE_mem_latInf' (hR := hR) hinj hϖ hϖv hk hfund i)

lemma eQInf_mk (i : I) (x : latInf (D := D) hvt A) :
    eQInf hR hinj hϖ hϖv hk hfund i (Submodule.Quotient.mk x : QInf (D := D) hvt A ϖ) =
      Submodule.Quotient.mk ⟨kE hvt i x,
        kashiwaraE_mem_latInf' (hR := hR) hinj hϖ hϖv hk hfund i x x.2⟩ := rfl

omit hinj hϖ hϖv hk hfund in
variable (hvt A ϖ) in
/-- `f̃ᵢ` on `L(∞)/ϖ L(∞)`. -/
def fQInf (i : I) : QInf (D := D) hvt A ϖ →ₗ[A] QInf (D := D) hvt A ϖ :=
  endQ (kashiwaraF_mem_latInf' (hvt := hvt) (A := A) i)

omit [Finite I] [IsDomain A] [IsDiscreteValuationRing A] hinj hϖ hϖv hk hfund in
lemma fQInf_mk (i : I) (x : latInf (D := D) hvt A) :
    fQInf hvt A ϖ i (Submodule.Quotient.mk x) = Submodule.Quotient.mk
      ⟨kF hvt i x, NegativePart.kashiwaraF_mem_latticeInf _ _ i x.2⟩ := rfl

lemma eQInf_fQInf (i : I) (b : QInf (D := D) hvt A ϖ) :
    eQInf hR hinj hϖ hϖv hk hfund i (fQInf hvt A ϖ i b) = b := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [fQInf_mk, eQInf_mk]
  congr 1
  exact Subtype.ext (kE_kF i x.1)

include hR in
lemma fQInf_mem_BInf (i : I) {b : QInf (D := D) hvt A ϖ} (hb : b ∈ BInf hvt A ϖ) :
    fQInf hvt A ϖ i b ∈ BInf hvt A ϖ := by
  obtain ⟨w, rfl⟩ := exists_eq_mk_of_mem_BInf hb
  exact mk_fwInf_mem_BInf (hR := hR) hinj hϖ hϖv hk hfund (i :: w)

/-- `ẽᵢ B(∞) ⊆ B(∞) ∪ {0}` ([Jan] Prop. 10.12). -/
theorem eQInf_mem_BInf (i : I) {b : QInf (D := D) hvt A ϖ} (hb : b ∈ BInf hvt A ϖ) :
    eQInf hR hinj hϖ hϖv hk hfund i b ∈ BInf hvt A ϖ ∨ eQInf hR hinj hϖ hϖv hk hfund i b = 0 := by
  obtain ⟨w, rfl⟩ := exists_eq_mk_of_mem_BInf hb
  rw [eQInf_mk]
  rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i w with h | ⟨w', h⟩
  · exact Or.inr ((IntegrableSl2.mk_eq_zero_iff ϖ _).2 h)
  · left
    rw [(IntegrableSl2.mk_eq_mk_iff ϖ _ (fwInf hvt A w')).2 h]
    exact mk_fwInf_mem_BInf (hR := hR) hinj hϖ hϖv hk hfund w'

/-- `f̃ᵢ b = b' ↔ ẽᵢ b' = b` on `B(∞)` ([Jan] Prop. 10.12). -/
theorem fQInf_eq_iff (i : I) {b b' : QInf (D := D) hvt A ϖ} (hb : b ∈ BInf hvt A ϖ)
    (hb' : b' ∈ BInf hvt A ϖ) :
    fQInf hvt A ϖ i b = b' ↔ eQInf hR hinj hϖ hϖv hk hfund i b' = b := by
  constructor
  · rintro rfl; exact eQInf_fQInf hinj hϖ hϖv hk hfund i b
  · intro h
    obtain ⟨w, rfl⟩ := exists_eq_mk_of_mem_BInf hb
    obtain ⟨w', rfl⟩ := exists_eq_mk_of_mem_BInf hb'
    rw [eQInf_mk, IntegrableSl2.mk_eq_mk_iff] at h
    have h0 : kE (D := D) hvt i (fWi hvt w') ∉ ϖ • latInf hvt A := fun h' ↦
      fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund (A := A) w (by simpa using sub_mem h' h)
    have := fWi_sub_mem_of_kE (hR := hR) hinj hϖ hϖv hk hfund i h0 h
    rw [fQInf_mk]
    exact ((IntegrableSl2.mk_eq_mk_iff ϖ (fwInf hvt A w') ⟨_, _⟩).2 this).symm

/-- The weight of `b ∈ B(∞)`. -/
noncomputable def wtInf (b : BInf (D := D) hvt A ϖ) : Y →+ ℤ :=
  -R.rootSum (wordWeight (exists_eq_mk_of_mem_BInf b.2).choose)

include hR in
lemma wtInf_eq (b : BInf (D := D) hvt A ϖ) {w : List I}
    (hw : b.1 = Submodule.Quotient.mk (fwInf hvt A w)) :
    wtInf (R := R) b = -R.rootSum (wordWeight w) := by
  have h := (exists_eq_mk_of_mem_BInf b.2).choose_spec
  rw [h, IntegrableSl2.mk_eq_mk_iff] at hw
  rw [wtInf, wordWeight_eq_of_sub_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund hw]

lemma eQInf_pow_mk (i : I) (n : ℕ) (x : latInf (D := D) hvt A) :
    ∃ h, (eQInf hR hinj hϖ hϖv hk hfund i ^ n) (Submodule.Quotient.mk x : QInf (D := D) hvt A ϖ) =
      Submodule.Quotient.mk ⟨(kE (D := D) hvt i ^ n) x, h⟩ := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ n ih =>
    obtain ⟨h, he⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [pow_succ', Module.End.mul_apply]
      exact kashiwaraE_mem_latInf' (hR := hR) hinj hϖ hϖv hk hfund i _ h
    · rw [pow_succ', Module.End.mul_apply, he, eQInf_mk]
      congr 1
      apply Subtype.ext
      change kE (D := D) hvt i ((kE (D := D) hvt i ^ n) (x : Um D v)) =
        (kE (D := D) hvt i ^ (n + 1)) (x : Um D v)
      rw [pow_succ', Module.End.mul_apply]

lemma exists_eQInf_pow_eq_zero (i : I) (b : BInf (D := D) hvt A ϖ) :
    ∃ n, (eQInf hR hinj hϖ hϖv hk hfund i ^ n) b.1 = 0 := by
  obtain ⟨w, hw⟩ := exists_eq_mk_of_mem_BInf b.2
  obtain ⟨h, he⟩ := eQInf_pow_mk hinj hϖ hϖv hk hfund i (wordWeight w i + 1) (fwInf hvt A w)
  refine ⟨wordWeight w i + 1, ?_⟩
  rw [hw, he]
  have : (kE (D := D) hvt i ^ (wordWeight w i + 1)) (fWi hvt w) = 0 :=
    kE_pow_eq_zero i (fWi_mem_Uw w)
  simp only [this]
  rfl

variable (hR) in
/-- `εᵢ(b) = max {n | ẽᵢⁿ b ≠ 0}` on `B(∞)`. -/
noncomputable def epsInf (i : I) (b : BInf (D := D) hvt A ϖ) : ℕ :=
  open scoped Classical in
  Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i b) - 1

omit [Finite I] [IsDomain A] [IsDiscreteValuationRing A] hinj hϖ hϖv hk hfund in
lemma zero_notMem_BInf : (0 : QInf (D := D) hvt A ϖ) ∉ BInf hvt A ϖ := fun h ↦ h.2 rfl

include hR in
lemma eQInf_mem_of_ne (i : I) (b : BInf (D := D) hvt A ϖ)
    (h : eQInf hR hinj hϖ hϖv hk hfund i b.1 ≠ 0) :
    eQInf hR hinj hϖ hϖv hk hfund i b.1 ∈ BInf hvt A ϖ :=
  (eQInf_mem_BInf hinj hϖ hϖv hk hfund i b.2).resolve_right h

variable (hR) in
open scoped Classical in
/-- `ẽᵢ` on `B(∞) ∪ {0}`, with `0` modelled by `none`. -/
noncomputable def eInf (i : I) (b : BInf (D := D) hvt A ϖ) : Option (BInf (D := D) hvt A ϖ) :=
  if h : eQInf hR hinj hϖ hϖv hk hfund i b.1 = 0 then none
  else some ⟨_, eQInf_mem_of_ne hinj hϖ hϖv hk hfund i b h⟩

variable (hR) in
/-- `f̃ᵢ` on `B(∞)`. -/
noncomputable def fInf (i : I) (b : BInf (D := D) hvt A ϖ) : Option (BInf (D := D) hvt A ϖ) :=
  some ⟨_, fQInf_mem_BInf (hR := hR) hinj hϖ hϖv hk hfund i b.2⟩

lemma eInf_eq_some_iff (i : I) (b b' : BInf (D := D) hvt A ϖ) :
    eInf hR hinj hϖ hϖv hk hfund i b = some b' ↔ eQInf hR hinj hϖ hϖv hk hfund i b.1 = b'.1 := by
  unfold eInf
  split_ifs with h
  · simp only [false_iff]
    intro h'
    exact zero_notMem_BInf (h ▸ h' ▸ b'.2)
  · simp [Subtype.ext_iff]

lemma fInf_eq_some_iff (i : I) (b b' : BInf (D := D) hvt A ϖ) :
    fInf hR hinj hϖ hϖv hk hfund i b = some b' ↔ fQInf hvt A ϖ i b.1 = b'.1 := by
  simp [fInf, Subtype.ext_iff]

lemma wtInf_eInf (i : I) (b b' : BInf (D := D) hvt A ϖ)
    (h : eQInf hR hinj hϖ hϖv hk hfund i b.1 = b'.1) :
    wtInf (R := R) b' = wtInf (R := R) b + R.root i := by
  obtain ⟨w, hw⟩ := exists_eq_mk_of_mem_BInf b.2
  obtain ⟨w', hw'⟩ := exists_eq_mk_of_mem_BInf b'.2
  rw [hw, eQInf_mk, hw', IntegrableSl2.mk_eq_mk_iff] at h
  have h0 : kE (D := D) hvt i (fWi hvt w) ∉ ϖ • latInf hvt A := fun h' ↦
    fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund (A := A) w' (by simpa using sub_mem h' h)
  have hνi : wordWeight w i ≠ 0 := fun h' ↦ h0 (by rw [kE_fWi_eq_zero i h']; exact zero_mem _)
  obtain ⟨μ, hμ⟩ : ∃ μ, wordWeight w = μ + Finsupp.single i 1 := by
    refine ⟨wordWeight w - Finsupp.single i 1, ?_⟩
    ext l
    by_cases hl : l = i
    · subst hl; simp; omega
    · simp [Ne.symm hl]
  have hew : kE (D := D) hvt i (fWi hvt w) ∈ Uw D v μ :=
    NegativePart.kashiwaraE_mem_weightSpace _ _ i (hμ ▸ fWi_mem_Uw w)
  have hw'μ := wordWeight_eq_of_mem_Uw hew h0 h
  rw [wtInf_eq (hR := hR) hinj hϖ hϖv hk hfund b hw,
    wtInf_eq (hR := hR) hinj hϖ hϖv hk hfund b' hw',
    hw'μ, hμ,
    R.rootSum_add, R.rootSum_single, one_smul]
  abel

lemma epsInf_eq (i : I) (b b' : BInf (D := D) hvt A ϖ)
    (h : eQInf hR hinj hϖ hϖv hk hfund i b.1 = b'.1) :
    epsInf hR hinj hϖ hϖv hk hfund i b = epsInf hR hinj hϖ hϖv hk hfund i b' + 1 := by
  classical
  have hb0 : ¬ (eQInf hR hinj hϖ hϖv hk hfund i ^ 0) b.1 = 0 := by
    simpa using fun h' ↦ zero_notMem_BInf (h' ▸ b.2)
  have hb'0 : ¬ (eQInf hR hinj hϖ hϖv hk hfund i ^ 0) b'.1 = 0 := by
    simpa using fun h' ↦ zero_notMem_BInf (h' ▸ b'.2)
  have hsucc : ∀ n, (eQInf hR hinj hϖ hϖv hk hfund i ^ (n + 1)) b.1 =
      (eQInf hR hinj hϖ hϖv hk hfund i ^ n) b'.1 := fun n ↦ by
    rw [pow_succ, Module.End.mul_apply, h]
  have e1 := Nat.find_comp_succ (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i b)
    (by simpa only [hsucc] using exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i b') hb0
  have e2 : Nat.find (p := fun n ↦ (eQInf hR hinj hϖ hϖv hk hfund i ^ (n + 1)) b.1 = 0)
      (by simpa only [hsucc] using exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i b') =
      Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i b') := by
    simp only [hsucc]
  have hpos : 0 < Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i b') :=
    Nat.pos_of_ne_zero fun h0 ↦ hb'0 (h0 ▸ Nat.find_spec
      (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i b'))
  unfold epsInf
  omega

variable (hR) in
/-- **The crystal `B(∞)`** ([KS97] Example 3.1.3): `B(∞)` with `wt`, `εᵢ(b) = max {n | ẽᵢⁿ b ≠ 0}`,
`φᵢ = εᵢ + ⟨i, wt⟩` and Kashiwara's operators. -/
noncomputable def crystalInf : Crystal R.crystalDatum (BInf (D := D) hvt A ϖ) where
  wt := wtInf
  ε i b := ((epsInf hR hinj hϖ hϖv hk hfund i b : ℤ) : WithBot ℤ)
  φ i b := (((epsInf hR hinj hϖ hϖv hk hfund i b : ℤ) + wtInf (R := R) b (R.coroot i) : ℤ) :
    WithBot ℤ)
  e := eInf hR hinj hϖ hϖv hk hfund
  f := fInf hR hinj hϖ hϖv hk hfund
  φ_eq i b := by simp
  f_eq_some_iff i b b' := by
    rw [fInf_eq_some_iff, eInf_eq_some_iff]
    exact fQInf_eq_iff hinj hϖ hϖv hk hfund i b.2 b'.2
  wt_e i b b' h := wtInf_eInf hinj hϖ hϖv hk hfund i b b'
    ((eInf_eq_some_iff (hR := hR) hinj hϖ hϖv hk hfund i b b').1 h)
  ε_e i b b' h := by
    rw [epsInf_eq hinj hϖ hϖv hk hfund i b b'
      ((eInf_eq_some_iff (hR := hR) hinj hϖ hϖv hk hfund i b b').1 h)]
    push_cast
    rfl
  e_eq_none_of_φ_eq_bot i b h := absurd h WithBot.coe_ne_bot

include hR in
/-- `B(∞)` spans `L(∞)/ϖ L(∞)` over `A/ϖA`. -/
lemma span_BInf : Submodule.span (A ⧸ Ideal.span {ϖ}) (BInf (D := D) hvt A ϖ) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span (mk_fwInf_mem_BInf (hR := hR) hinj hϖ hϖv hk hfund w)
  | zero => exact zero_mem _
  | add a b ha hb iha ihb => exact add_mem iha ihb
  | smul c a ha iha =>
    rw [show (⟨c • a, Submodule.smul_mem _ c ha⟩ : latInf (D := D) hvt A) = c • ⟨a, ha⟩ from rfl,
      ← Module.Quotient.mk_smul_mk]
    exact Submodule.smul_mem _ _ iha

end Base

end GrandLoop

end LieLean.QuantumGroup
