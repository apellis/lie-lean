/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityCompare

/-!
# The lattice `L(∞)`

Let `L(∞) ⊆ U⁻` be the `A`-span of the `f̃_{i₁} ⋯ f̃_{iᵣ} 1` (`NegativePart.latticeInf`). In the
setting of the grand loop we show:

* `π_λ(f̃_w 1) ≡ f̃_w v_λ` modulo `ϖ L(λ)` (`GrandLoop.evq_fWord_sub_fW_mem`);
* for `⟨j, λ⟩ ≥ |ν|` for all `j`, `π_λ` maps `L(∞)_{-ν}` onto `L(λ)_{λ-ν}`
  (`GrandLoop.exists_evq_eq`, by Nakayama's lemma), hence `u ∈ U⁻_{-ν}` lies in `L(∞)` iff
  `π_λ(u) ∈ L(λ)` (`GrandLoop.mem_latticeInf_iff`; [Jan] Thm. 10.10 (a));
* `ẽᵢ L(∞) ⊆ L(∞)` (`GrandLoop.kashiwaraE_mem_latticeInf`; [Jan] Thm. 10.10 (b)).

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.10 (finite type, lattices at
  `q = 0`).
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

variable (hvt A) in
/-- `L(∞)`. -/
abbrev latInf : Submodule A (Um D v) :=
  NegativePart.latticeInf D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) A

variable (hvt) in
/-- `f̃_w 1 ∈ U⁻`. -/
abbrev fWi (w : List I) : Um D v :=
  NegativePart.fWord D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) w

lemma fWi_mem_Uw (w : List I) : fWi (D := D) hvt w ∈ Uw D v (wordWeight w) :=
  NegativePart.fWord_mem_weightSpace _ _ w

omit [NeZero v] [CharZero k] in
lemma proj_of_mem_Uw {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν) (γ : I →₀ ℤ) :
    NegativePart.proj D v γ u = if toZ ν = γ then u else 0 := by
  obtain ⟨y, hy, rfl⟩ := hu
  rw [Submodule.mkQ_apply, NegativePart.proj_mk, zWeightProj_of_mem hy]
  split_ifs <;> simp

/-- `L(∞) ∩ U⁻_{-ν}` is spanned by the `f̃_w 1` of weight `-ν`. -/
lemma mem_span_fWi_of_mem {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ latInf hvt A)
    (huw : u ∈ Uw D v ν) :
    u ∈ Submodule.span A (fWi (D := D) hvt '' {w | wordWeight w = ν}) := by
  have hproj : NegativePart.proj D v (toZ ν) u = u := by
    rw [proj_of_mem_Uw huw]; simp
  rw [← hproj]
  clear hproj huw
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    rw [proj_of_mem_Uw (fWi_mem_Uw (hvt := hvt) w)]
    split_ifs with h
    · exact Submodule.subset_span ⟨w, toZ_injective h, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul k c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ c ha

lemma evq_mem_wsp (hR : R.IsXRegular) {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν)
    (Λ : Dom R) :
    evq hvt Λ u ∈ wsp Λ ν := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact ev_mem_weightSpace (pow_ne_one_of_transcendental' hvt) hR Λ.1 hy

omit [NeZero v] [CharZero k] in
/-- Dominant weights with `⟨j, λ⟩ ≥ N` for all `j`. -/
lemma exists_dom_ge [Finite I]
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0) (N : ℕ) :
    ∃ Λ : Dom R, ∀ j, (N : ℤ) ≤ Λ.1 (R.coroot j) := by
  obtain ⟨ρ, hρ⟩ := exists_rho hfund
  refine ⟨⟨(N : ℤ) • ρ.1, fun j ↦ by
    rw [AddMonoidHom.smul_apply]; exact smul_nonneg (by positivity) (ρ.2 j)⟩, fun j ↦ ?_⟩
  change (N : ℤ) ≤ (N : ℤ) • ρ.1 (R.coroot j)
  rw [smul_eq_mul]
  have := hρ j
  nlinarith

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- `π_λ(f̃_w 1) ≡ f̃_w v_λ` modulo `ϖ L(λ)`. -/
theorem evq_fWord_sub_fW_mem (w : List I) (Λ : Dom R) :
    evq hvt Λ (fWi hvt w) - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ := by
  induction w with
  | nil =>
    change ev R v Λ.1 1 - IrreducibleModule.hwv R v Λ.1 ∈ _
    rw [ev_one, sub_self]; exact zero_mem _
  | cons i w ih =>
    have h1 := (evq_fWord_mem_and_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w).2 i Λ
    have h2 := kashiwaraF_mem_smul_lat Λ i ih
    rw [map_sub] at h2
    change evq hvt Λ (NegativePart.kashiwaraF D v _ _ i (fWi hvt w)) - fK hvt hR Λ i
      (fW hvt hR Λ w) ∈ _
    simpa using add_mem h1 h2

/-- **[Jan] Thm. 10.10 (a)**: if `⟨j, λ⟩ ≥ |ν|` for all `j`, every `x ∈ L(λ)_{λ-ν}` is
`π_λ(u)` for some `u ∈ L(∞) ∩ U⁻_{-ν}` (Nakayama's lemma). -/
theorem exists_evq_eq {Λ : Dom R} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1}
    (hx : x ∈ lat hvt hR A Λ) (hxw : x ∈ wsp Λ ν) :
    ∃ u ∈ latInf hvt A, u ∈ Uw D v ν ∧ evq hvt Λ u = x := by
  have hv' := pow_ne_one_of_transcendental' hvt
  set S := Submodule.span A (fWi (D := D) hvt '' {w | wordWeight w = ν})
  set M : Submodule A (IrreducibleModule R v Λ.1) :=
    lat hvt hR A Λ ⊓ (wsp Λ ν).restrictScalars A
  set N : Submodule A (IrreducibleModule R v Λ.1) := S.map ((evq hvt Λ).restrictScalars A)
  have hSL : S ≤ latInf hvt A ⊓ (Uw D v ν).restrictScalars A := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨NegativePart.fWord_mem_latticeInf _ _ w, hw ▸ fWi_mem_Uw (hvt := hvt) w⟩
  have hMfg : M.FG := by
    have := (wtN_fg (hvt := hvt) (hR := hR) (A := A) Λ (Λ.1 - R.rootSum ν)).map
      (lat hvt hR A Λ).subtype
    convert this using 1
    ext y
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
      Submodule.subtype_apply, M]
    constructor
    · rintro ⟨hy, hyw⟩; exact ⟨⟨y, hy⟩, (mem_wtN).2 hyw, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, (mem_wtN).1 hy⟩
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hle : M ≤ N ⊔ Ideal.span {ϖ} • M := by
    intro y ⟨hy, hyw⟩
    -- `y` is an `A`-combination of the `f̃_w v_λ` of weight `λ - ν`
    have key : ∀ z ∈ lat hvt hR A Λ, weightSetProj hv' (isInt hvt hR Λ) {Λ.1 - R.rootSum ν} z ∈
        Submodule.span A (fW hvt hR Λ '' {w | wordWeight w = ν}) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨w, rfl⟩ := hz
        rw [weightSetProj_fW (hvt := hvt)]
        split_ifs with h
        · exact Submodule.subset_span ⟨w, h, rfl⟩
        · exact zero_mem _
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [← algebraMap_smul k c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ c ha
    have hP : weightSetProj hv' (isInt hvt hR Λ) {Λ.1 - R.rootSum ν} y = y := by
      rw [weightSetProj_of_mem _ _ _ hyw]; simp
    have hy' := key y hy
    rw [hP] at hy'
    refine (Submodule.span_le.2 ?_) hy'
    rintro _ ⟨w, hw, rfl⟩
    have hd := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w Λ
    have hdw : evq hvt Λ (fWi hvt w) - fW hvt hR Λ w ∈ wsp Λ ν :=
      sub_mem (evq_mem_wsp hR (hw ▸ fWi_mem_Uw (hvt := hvt) w) Λ) (hw ▸ fW_mem_wsp hvt hR Λ w)
    obtain ⟨z₀, hz₀, hz₀w, hz⟩ := TensorModule.exists_smul_weight hϖ0 hd hdw
    have e : fW hvt hR Λ w = evq hvt Λ (fWi hvt w) - ϖ • z₀ := by rw [← hz]; abel
    rw [e]
    refine sub_mem (Submodule.mem_sup_left ⟨fWi hvt w, Submodule.subset_span ⟨w, hw, rfl⟩, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ)
        ⟨hz₀, hz₀w⟩))
  have hjac : Ideal.span {ϖ} ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hϖ
  have hMN := Submodule.le_of_le_smul_of_le_jacobson_bot hMfg hjac hle
  obtain ⟨u, hu, rfl⟩ := hMN ⟨hx, hxw⟩
  exact ⟨u, (hSL hu).1, (hSL hu).2, rfl⟩

/-- **[Jan] Thm. 10.10 (a)**: for `⟨j, λ⟩ ≥ |ν|` and `u ∈ U⁻_{-ν}`, `u ∈ L(∞) ↔ π_λ(u) ∈ L(λ)`. -/
theorem mem_latticeInf_iff {Λ : Dom R} {ν : I →₀ ℕ}
    (hΛ : ∀ i, (ν.degree : ℤ) ≤ Λ.1 (R.coroot i)) {u : Um D v} (hu : u ∈ Uw D v ν) :
    u ∈ latInf hvt A ↔ evq hvt Λ u ∈ lat hvt hR A Λ := by
  refine ⟨fun h ↦ evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund h Λ, fun h ↦ ?_⟩
  obtain ⟨u', hu', hu'w, he⟩ := exists_evq_eq (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund h
    (evq_mem_wsp hR hu Λ)
  have := evq_injective (hvt := hvt) (hR := hR) hΛ (a₁ := ⟨u', hu'w⟩) (a₂ := ⟨u, hu⟩) he
  rw [← show u' = u from congrArg Subtype.val this]
  exact hu'

include hR in
/-- **[Jan] Thm. 10.10 (b)**: `ẽᵢ L(∞) ⊆ L(∞)`. -/
theorem kashiwaraE_mem_latticeInf (i : I) {u : Um D v} (hu : u ∈ latInf hvt A) :
    NegativePart.kashiwaraE D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i u ∈
      latInf hvt A := by
  have hv' := pow_ne_one_of_transcendental' hvt
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    set ν := wordWeight w
    by_cases hνi : ν i = 0
    · -- `e'ᵢ` kills `f̃_w 1`
      have he : NegativePart.e D v (NeZero.ne v) hv' i (fWi hvt w) = 0 := by
        obtain ⟨y, hy, hyw⟩ := fWi_mem_Uw (D := D) (v := v) (hvt := hvt) w
        rw [← hyw, Submodule.mkQ_apply, NegativePart.e_mk, bosonE_eq_zero_of_mem i hνi hy]
        rfl
      rw [NegativePart.kashiwaraE, (NegativePart.boson D v _ hv' i).eTilde_eq_zero_iff _ _ _
        |>.2 he]
      exact zero_mem _
    obtain ⟨μ, hμ⟩ : ∃ μ, ν = μ + Finsupp.single i 1 := by
      refine ⟨ν - Finsupp.single i 1, ?_⟩
      ext l
      by_cases hl : l = i
      · subst hl; simp; omega
      · simp [Ne.symm hl]
    have hew : NegativePart.kashiwaraE D v (NeZero.ne v) hv' i (fWi hvt w) ∈ Uw D v μ :=
      NegativePart.kashiwaraE_mem_weightSpace _ _ i (hμ ▸ fWi_mem_Uw w)
    obtain ⟨r, hr⟩ := exists_evq_kashiwara_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i
      (fWi_mem_Uw w)
    obtain ⟨ρ, hρ⟩ := exists_rho hfund
    set n : ℕ := max μ.degree r.toNat
    let Λ : Dom R := ⟨(n : ℤ) • ρ.1, fun j ↦ by
      rw [AddMonoidHom.smul_apply]; exact smul_nonneg (by positivity) (ρ.2 j)⟩
    have hΛj : ∀ j, (n : ℤ) ≤ Λ.1 (R.coroot j) := fun j ↦ by
      change (n : ℤ) ≤ (n : ℤ) • ρ.1 (R.coroot j)
      rw [smul_eq_mul]
      have := hρ j
      nlinarith
    have hΛ : ∀ j, (μ.degree : ℤ) ≤ Λ.1 (R.coroot j) := fun j ↦
      le_trans (by exact_mod_cast le_max_left _ _) (hΛj j)
    have hrΛ : r ≤ Λ.1 (R.coroot i) := by
      refine le_trans ?_ (hΛj i)
      have := le_max_right μ.degree r.toNat
      omega
    rw [mem_latticeInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛ hew]
    have h1 := (hr Λ hrΛ).2
    have h2 := (isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ).kashiwaraE_mem
      i _ (evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund
        (NegativePart.fWord_mem_latticeInf _ _ w) Λ)
    simpa using add_mem (IntegrableSl2.smul_le ϖ h1) h2
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul k c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ c ha

/-- For `⟨j, λ⟩ ≥ |ν|` and `u ∈ L(∞) ∩ U⁻_{-ν}`: `u ∈ ϖ L(∞) ↔ π_λ(u) ∈ ϖ L(λ)`. -/
theorem mem_smul_latInf_iff {Λ : Dom R} {ν : I →₀ ℕ}
    (hΛ : ∀ i, (ν.degree : ℤ) ≤ Λ.1 (R.coroot i)) {u : Um D v} (hu : u ∈ latInf hvt A)
    (huw : u ∈ Uw D v ν) : u ∈ ϖ • latInf hvt A ↔ evq hvt Λ u ∈ ϖ • lat hvt hR A Λ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  constructor
  · intro h
    obtain ⟨u₀, hu₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    rw [← algebraMap_smul k ϖ u₀, map_smul, algebraMap_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund hu₀ Λ)
  · intro h
    obtain ⟨x, hx, hxw, hxe⟩ := TensorModule.exists_smul_weight hϖ0 h (evq_mem_wsp hR huw Λ)
    obtain ⟨u', hu', hu'w, he⟩ := exists_evq_eq (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hx
      hxw
    have hsw : ϖ • u' ∈ Uw D v ν := by
      rw [← algebraMap_smul k ϖ u']; exact Submodule.smul_mem _ _ hu'w
    have heq : evq hvt Λ (ϖ • u') = evq hvt Λ u := by
      rw [← algebraMap_smul k ϖ u', map_smul, algebraMap_smul, he, hxe]
    have := evq_injective (hvt := hvt) (hR := hR) hΛ (a₁ := ⟨ϖ • u', hsw⟩) (a₂ := ⟨u, huw⟩) heq
    rw [← show ϖ • u' = u from congrArg Subtype.val this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hu'

include hR in
/-- `ẽᵢ (ϖ L(∞)) ⊆ ϖ L(∞)`. -/
lemma kashiwaraE_mem_smul_latInf (i : I) {u : Um D v} (hu : u ∈ ϖ • latInf hvt A) :
    NegativePart.kashiwaraE D v (NeZero.ne v) (pow_ne_one_of_transcendental' hvt) i u ∈
      ϖ • latInf hvt A :=
  LinearMap.map_mem_smul_of_mem ϖ
    (fun _ hm ↦ kashiwaraE_mem_latticeInf (hR := hR) hinj hϖ hϖv hk hfund i hm) hu

include hR in
/-- **[Jan] Prop. 10.11 (a)**: `f̃_w 1 ∉ ϖ L(∞)`, so `0 ∉ B(∞)`. -/
theorem fWi_notMem (w : List I) : fWi (D := D) hvt w ∉ ϖ • latInf hvt A := by
  have hϖu : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  induction w with
  | nil =>
    intro h
    obtain ⟨Λ, -⟩ := exists_dom_ge (R := R) hfund 0
    obtain ⟨u₀, hu₀, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    refine hwv_notMem (hvt := hvt) (hR := hR) hinj hϖu Λ ?_
    have : evq hvt Λ (fWi hvt []) = IrreducibleModule.hwv R v Λ.1 := ev_one Λ.1
    rw [← this, ← he, ← algebraMap_smul k ϖ u₀, map_smul, algebraMap_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund hu₀ Λ)
  | cons i w ih =>
    intro h
    refine ih ?_
    have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i h
    rwa [fWi, NegativePart.fWord_cons, NegativePart.kashiwaraE_kashiwaraF] at this

/-- For `⟨j, λ⟩ ≥ |wt w|`, `f̃_w v_λ ∉ ϖ L(λ)`. -/
theorem fW_notMem_of_large {Λ : Dom R} (w : List I)
    (hΛ : ∀ i, ((wordWeight w).degree : ℤ) ≤ Λ.1 (R.coroot i)) :
    fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ := by
  intro h
  refine fWi_notMem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (A := A) w ?_
  rw [mem_smul_latInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛ
    (NegativePart.fWord_mem_latticeInf _ _ w) (fWi_mem_Uw (hvt := hvt) w)]
  simpa using add_mem (evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w Λ) h

end Base

end GrandLoop

end LieLean.QuantumGroup
