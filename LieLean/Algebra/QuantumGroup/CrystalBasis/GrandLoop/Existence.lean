/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Main
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase

/-!
# Existence of crystal bases of `V(λ)`

From the grand loop (`GrandLoop.allProp`) we obtain Kashiwara's existence theorem
([HK] Thm. 5.1.1): `(L(λ), B(λ))` is a crystal base of `V(λ) = L_q(λ)` for every dominant `λ`
(`GrandLoop.isCrystalBase`). Here `L(λ) = Σ A f̃_{i₁} ⋯ f̃_{iᵣ} v_λ`
(`IrreducibleModule.lattice`), `B(λ)` is the set of nonzero classes of the
`f̃_{i₁} ⋯ f̃_{iᵣ} v_λ` in `L(λ)/ϖ L(λ)` (`IrreducibleModule.base`), `A ⊆ k` is a discrete
valuation ring with `k = A[ϖ⁻¹]` and `ϖ ↦ v⁻¹`, and `v` is transcendental over `ℚ`. Freeness of
`L(λ)` comes from its weight decomposition (`GrandLoop.free_lat`).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.1,
  §5.3.
-/

open Finset Pointwise LusztigF TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### The lattice -/

section Lattice

/-- `ẽᵢ L(λ) ⊆ L(λ)`, given `A(r)` for all `r`. -/
lemma kashiwaraE_mem_lat (hA : ∀ r, PropA hvt hR A r) (Λ : Dom R) (i : I)
    {m : IrreducibleModule R v Λ.1} (hm : m ∈ lat hvt hR A Λ) :
    eK hvt hR Λ i m ∈ lat hvt hR A Λ := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨w, rfl⟩ := hm
    exact hA w.length Λ (wordWeight w) (degree_wordWeight w) i _
      (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w) (fW_mem_wsp hvt hR Λ w)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c ha

variable (hvt hR A) in
/-- The weight components of `L(λ)`. -/
def wtN (Λ : Dom R) (μ : Y →+ ℤ) : Submodule A (lat hvt hR A Λ) :=
  ((weightSpace R v (IrreducibleModule R v Λ.1) μ).restrictScalars A).comap
    (lat hvt hR A Λ).subtype

lemma mem_wtN {Λ : Dom R} {μ : Y →+ ℤ} {x : lat hvt hR A Λ} :
    x ∈ wtN hvt hR A Λ μ ↔ (x : IrreducibleModule R v Λ.1) ∈ weightSpace R v _ μ := Iff.rfl

open scoped Classical in
/-- `L(λ) = ⨁_μ L(λ)_μ`. -/
theorem isInternal_wtN [Finite I] (Λ : Dom R) : DirectSum.IsInternal (wtN hvt hR A Λ) := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro μ
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hind := iSupIndep_weightSpace (R := R) (M := IrreducibleModule R v Λ.1) hv'
    have h1 : (x : IrreducibleModule R v Λ.1) ∈
        ⨆ (ν) (_ : ν ≠ μ), weightSpace R v (IrreducibleModule R v Λ.1) ν := by
      have : (⨆ (ν) (_ : ν ≠ μ), wtN hvt hR A Λ ν).map (lat hvt hR A Λ).subtype ≤
          (⨆ (ν) (_ : ν ≠ μ), weightSpace R v (IrreducibleModule R v Λ.1) ν).restrictScalars A := by
        rw [Submodule.map_iSup]
        refine iSup_le fun ν ↦ ?_
        rw [Submodule.map_iSup]
        refine iSup_le fun hν ↦ ?_
        rintro _ ⟨y, hy, rfl⟩
        change (y : IrreducibleModule R v Λ.1) ∈
          ⨆ (ν) (_ : ν ≠ μ), weightSpace R v (IrreducibleModule R v Λ.1) ν
        exact Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hν hy)
      exact this ⟨x, hx', rfl⟩
    exact Subtype.ext (Submodule.disjoint_def.1 (iSupIndep_def.1 hind μ) _ hx h1)
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.mem_iSup_of_mem (Λ.1 - R.rootSum (wordWeight w))
        (show _ ∈ wtN hvt hR A Λ _ from fW_mem_wsp hvt hR Λ w)
    | zero => exact zero_mem _
    | add a b ha hb iha ihb => exact add_mem iha ihb
    | smul c a ha iha => exact Submodule.smul_mem _ c iha

/-- The weight components of `L(λ)` are finitely generated. -/
theorem wtN_fg [Finite I] [IsNoetherianRing A] (Λ : Dom R) (μ : Y →+ ℤ) :
    (wtN hvt hR A Λ μ).FG := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  set W := {w : List I | Λ.1 - R.rootSum (wordWeight w) = μ}
  have hW : W.Finite := by
    by_cases h : ∃ w₀, w₀ ∈ W
    · obtain ⟨w₀, hw₀⟩ := h
      refine (finite_words (wordWeight w₀)).subset fun w (hw : _ = μ) ↦ ?_
      change wordWeight w = wordWeight w₀
      refine LusztigCartanDatum.RootDatum.rootSum_injective hR ?_
      have h1 : Λ.1 - R.rootSum (wordWeight w) = Λ.1 - R.rootSum (wordWeight w₀) :=
        hw.trans hw₀.symm
      exact sub_right_injective h1
    · push Not at h
      rw [Set.eq_empty_of_forall_notMem h]
      exact Set.finite_empty
  let fw : List I → lat hvt hR A Λ := fun w ↦
    ⟨fW hvt hR Λ w, IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w⟩
  let P : lat hvt hR A Λ →ₗ[A] lat hvt hR A Λ :=
    ((weightSetProj hv' (isInt hvt hR Λ) {μ}).restrictScalars A).restrict
      fun m hm ↦ weightSetProj_mem_lat hvt hR A Λ {μ} hm
  have key : ∀ y (hy : y ∈ lat hvt hR A Λ), P ⟨y, hy⟩ ∈ Submodule.span A (fw '' W) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      have hP : P (fw w) = if Λ.1 - R.rootSum (wordWeight w) ∈ ({μ} : Set (Y →+ ℤ)) then fw w
          else 0 := by
        apply Subtype.ext
        change weightSetProj hv' (isInt hvt hR Λ) {μ} (fW hvt hR Λ w) = _
        rw [weightSetProj_of_mem hv' _ _ (fW_mem_wsp hvt hR Λ w)]
        split_ifs <;> rfl
      change P (fw w) ∈ _
      rw [hP]
      split_ifs with h
      · exact Submodule.subset_span ⟨w, h, rfl⟩
      · exact zero_mem _
    | zero => exact (map_zero P).symm ▸ zero_mem _
    | add a b ha hb iha ihb =>
      have : P ⟨a + b, add_mem ha hb⟩ = P ⟨a, ha⟩ + P ⟨b, hb⟩ := by
        rw [← map_add]; rfl
      rw [this]; exact add_mem iha ihb
    | smul c a ha iha =>
      have : P ⟨c • a, Submodule.smul_mem _ c ha⟩ = c • P ⟨a, ha⟩ := by
        rw [← map_smul]; rfl
      rw [this]; exact Submodule.smul_mem _ c iha
  refine (Submodule.fg_span (hW.image fw)).of_le fun x hx ↦ ?_
  have hPx : P x = x := by
    apply Subtype.ext
    change weightSetProj hv' (isInt hvt hR Λ) {μ} (x : IrreducibleModule R v Λ.1) = x
    have hx' : (x : IrreducibleModule R v Λ.1) ∈ weightSpace R v _ μ := hx
    rw [weightSetProj_of_mem hv' _ _ hx']
    simp
  rw [← hPx]
  exact key x x.2

/-- `L(λ)` is a free `A`-module. -/
theorem free_lat [Finite I] [IsDomain A] [IsPrincipalIdealRing A]
    (hinj : Function.Injective (algebraMap A k)) (Λ : Dom R) :
    Module.Free A (lat hvt hR A Λ) := by
  classical
  have : ∀ μ, Module.Free A (wtN hvt hR A Λ μ) := fun μ ↦ by
    have : Module.Finite A (wtN hvt hR A Λ μ) := Module.Finite.iff_fg.2 (wtN_fg Λ μ)
    have : Module.IsTorsionFree A (wtN hvt hR A Λ μ) := ⟨fun r hr m₁ m₂ h ↦ by
      have hr0 : algebraMap A k r ≠ 0 := fun h0 ↦ hr.ne_zero (hinj (by rw [h0, map_zero]))
      have h' := congrArg (fun z : wtN hvt hR A Λ μ ↦ ((z : lat hvt hR A Λ) :
        IrreducibleModule R v Λ.1)) h
      simp only [Submodule.coe_smul_of_tower] at h'
      rw [← algebraMap_smul k r (m₁ : IrreducibleModule R v Λ.1),
        ← algebraMap_smul k r (m₂ : IrreducibleModule R v Λ.1)] at h'
      exact Subtype.ext (Subtype.ext (smul_right_injective _ hr0 h'))⟩
    exact Module.free_of_finite_type_torsion_free' (R := A) (M := wtN hvt hR A Λ μ)
  exact Module.Free.of_basis ((isInternal_wtN Λ).collectedBasis
    fun μ ↦ Module.Free.chooseBasis A (wtN hvt hR A Λ μ))

end Lattice

/-! ### The crystal base -/

section Base

variable [Finite I]

omit [Finite I] in
/-- The projection of `f̃_w v_λ` to the weight `λ - ν`. -/
lemma weightSetProj_fW (Λ : Dom R) (ν : I →₀ ℕ) (w : List I) :
    weightSetProj (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) {Λ.1 - R.rootSum ν}
      (fW hvt hR Λ w) = if wordWeight w = ν then fW hvt hR Λ w else 0 := by
  classical
  rw [weightSetProj_of_mem _ _ _ (fW_mem_wsp hvt hR Λ w)]
  have hiff : (Λ.1 - R.rootSum (wordWeight w) ∈ ({Λ.1 - R.rootSum ν} : Set _)) ↔
      wordWeight w = ν := by
    rw [Set.mem_singleton_iff]
    exact ⟨fun h ↦ LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h),
      fun h ↦ by rw [h]⟩
  simp only [hiff]

omit [Finite I] in
/-- `D(r)` for all `r` gives the linear independence of a finite family of distinct nonzero
classes of `f̃`-words over `A/ϖA` (any weights). -/
lemma coeff_mem_of_sum_mem (hD : ∀ r, PropD hvt hR A ϖ r) (Λ : Dom R) {ι : Type*}
    (s : Finset ι) (wd : ι → List I) (hinjwd : Set.InjOn wd (s : Set ι))
    (hwd0 : ∀ b ∈ s, fW hvt hR Λ (wd b) ∉ ϖ • lat hvt hR A Λ)
    (hdist : ∀ b₁ ∈ s, ∀ b₂ ∈ s, b₁ ≠ b₂ →
      fW hvt hR Λ (wd b₁) - fW hvt hR Λ (wd b₂) ∉ ϖ • lat hvt hR A Λ)
    (a : ι → A) (hsum : ∑ b ∈ s, a b • fW hvt hR Λ (wd b) ∈ ϖ • lat hvt hR A Λ)
    (b₀ : ι) (hb₀ : b₀ ∈ s) : a b₀ ∈ Ideal.span {ϖ} := by
  classical
  have : Nonempty ι := ⟨b₀⟩
  obtain ⟨ν₀, hν₀⟩ : ∃ ν₀, wordWeight (wd b₀) = ν₀ := ⟨_, rfl⟩
  have hP : ∑ b ∈ s.filter (fun b ↦ wordWeight (wd b) = ν₀), a b • fW hvt hR Λ (wd b) ∈
      ϖ • lat hvt hR A Λ := by
    have h1 := weightSetProj_mem_smul_lat hvt hR A ϖ Λ {Λ.1 - R.rootSum ν₀} hsum
    rw [map_sum] at h1
    simp only [LinearMap.map_smul_of_tower, weightSetProj_fW, smul_ite, smul_zero] at h1
    rwa [← Finset.sum_filter] at h1
  have hinj' : Set.InjOn wd ((s.filter fun b ↦ wordWeight (wd b) = ν₀) : Set ι) :=
    hinjwd.mono (by intro b hb; exact (Finset.mem_filter.1 hb).1)
  let a' : List I → A := fun w ↦
    a (Function.invFunOn wd ((s.filter fun b ↦ wordWeight (wd b) = ν₀) : Set ι) w)
  have ha' : ∀ b ∈ s.filter (fun b ↦ wordWeight (wd b) = ν₀), a' (wd b) = a b :=
    fun b hb ↦ by simp only [a']; rw [hinj'.leftInvOn_invFunOn hb]
  have hb₀' : b₀ ∈ s.filter (fun b ↦ wordWeight (wd b) = ν₀) := Finset.mem_filter.2 ⟨hb₀, hν₀⟩
  have hD' := hD ν₀.degree Λ ν₀ rfl ((s.filter fun b ↦ wordWeight (wd b) = ν₀).image wd)
    (fun w hw ↦ by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hw
      exact (Finset.mem_filter.1 hb).2)
    (fun w hw ↦ by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hw
      exact hwd0 b (Finset.mem_filter.1 hb).1)
    (fun w₁ hw₁ w₂ hw₂ hne ↦ by
      obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.1 hw₁
      obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.1 hw₂
      exact hdist b₁ (Finset.mem_filter.1 hb₁).1 b₂ (Finset.mem_filter.1 hb₂).1
        fun h ↦ hne (h ▸ rfl))
    a' (by
      rw [Finset.sum_image hinj']
      convert hP using 1
      exact Finset.sum_congr rfl fun b hb ↦ by rw [ha' b hb])
    (wd b₀) (Finset.mem_image_of_mem wd hb₀')
  rwa [ha' b₀ hb₀'] at hD'

omit [Finite I] in
/-- `B(λ)` is linearly independent over `A/ϖA`, from `D(r)` for all `r`. -/
theorem linearIndependent_base (hD : ∀ r, PropD hvt hR A ϖ r) (Λ : Dom R) :
    LinearIndependent (A ⧸ Ideal.span {ϖ})
      (Subtype.val : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ → _)
      := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  let fw : List I → lat hvt hR A Λ := fun w ↦
    ⟨fW hvt hR Λ w, IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w⟩
  have hbase : ∀ b ∈ IrreducibleModule.base hR hv' Λ.2 A ϖ, ∃ w, b =
      Submodule.Quotient.mk (fw w) ∧ fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ := by
    rintro _ ⟨⟨w, rfl⟩, hb0⟩
    exact ⟨w, rfl, fun h ↦ hb0 ((IntegrableSl2.mk_eq_zero_iff ϖ (fw w)).2 h)⟩
  rw [linearIndependent_iff']
  intro s g hg b₀ hb₀
  choose wd hwd hwd0 using fun b : IrreducibleModule.base hR hv' Λ.2 A ϖ ↦ hbase b.1 b.2
  choose a ha using fun b ↦ Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}) (g b)
  have hsum : ∑ b ∈ s, a b • fW hvt hR Λ (wd b) ∈ ϖ • lat hvt hR A Λ := by
    have e := map_sum (Submodule.mkQ (Ideal.span {ϖ} • ⊤ : Submodule A (lat hvt hR A Λ)))
      (fun b ↦ a b • fw (wd b)) s
    rw [Submodule.mkQ_apply] at e
    have h1 : ∑ b ∈ s, g b • (b : lat hvt hR A Λ ⧸
        (Ideal.span {ϖ} • ⊤ : Submodule A (lat hvt hR A Λ))) =
        Submodule.Quotient.mk (∑ b ∈ s, a b • fw (wd b)) := by
      rw [e]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [← ha b, hwd b, Module.Quotient.mk_smul_mk]
      rfl
    rw [h1] at hg
    have := (IntegrableSl2.mk_eq_zero_iff ϖ _).1 hg
    have e2 : ((∑ b ∈ s, a b • fw (wd b) : lat hvt hR A Λ) : IrreducibleModule R v Λ.1) =
        ∑ b ∈ s, a b • fW hvt hR Λ (wd b) := by
      rw [Submodule.coe_sum]; rfl
    rwa [e2] at this
  rw [← ha b₀, Ideal.Quotient.eq_zero_iff_mem]
  refine coeff_mem_of_sum_mem hD Λ s wd (fun b₁ _ b₂ _ he ↦ Subtype.ext (by
    rw [hwd b₁, hwd b₂, he])) (fun b _ ↦ hwd0 b) (fun b₁ _ b₂ _ hne h ↦ hne (Subtype.ext ?_))
    a hsum b₀ hb₀
  rw [hwd b₁, hwd b₂]
  exact (IntegrableSl2.mk_eq_mk_iff ϖ _ _).2 h

variable (hvt hR A) in
/-- `f̃_w v_λ` as an element of `L(λ)`. -/
abbrev fwL (Λ : Dom R) (w : List I) : lat hvt hR A Λ :=
  ⟨fW hvt hR Λ w, IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w⟩

/-- The quotient `L(λ)/ϖ L(λ)`. -/
abbrev QL (Λ : Dom R) : Type _ :=
  lat hvt hR A Λ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A (lat hvt hR A Λ))

omit [Finite I] in
lemma mem_base_iff (Λ : Dom R) (b : QL (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) Λ) :
    b ∈ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ ↔
      ∃ w, b = Submodule.Quotient.mk (fwL hvt hR A Λ w) ∧
        fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ := by
  constructor
  · rintro ⟨⟨w, rfl⟩, hb0⟩
    exact ⟨w, rfl, fun h ↦ hb0 ((IntegrableSl2.mk_eq_zero_iff ϖ _).2 h)⟩
  · rintro ⟨w, rfl, hw⟩
    exact ⟨⟨w, rfl⟩, fun h ↦ hw ((IntegrableSl2.mk_eq_zero_iff ϖ _).1 h)⟩

omit [Finite I] in
lemma mk_fwL_mem_or (Λ : Dom R) (w : List I) :
    (Submodule.Quotient.mk (fwL hvt hR A Λ w) : QL (ϖ := ϖ) Λ) ∈
      IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ ∨
    (Submodule.Quotient.mk (fwL hvt hR A Λ w) : QL (ϖ := ϖ) Λ) = 0 := by
  by_cases h : fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ
  · exact Or.inr ((IntegrableSl2.mk_eq_zero_iff ϖ _).2 h)
  · exact Or.inl ((mem_base_iff Λ _).2 ⟨w, rfl, h⟩)

omit [Finite I] in
/-- `B(λ)` spans `L(λ)/ϖ L(λ)`. -/
lemma span_base (Λ : Dom R) :
    Submodule.span (A ⧸ Ideal.span {ϖ})
      (IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rcases mk_fwL_mem_or (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) Λ w with h | h
    · exact Submodule.subset_span h
    · exact h ▸ zero_mem _
  | zero => exact zero_mem _
  | add a b ha hb iha ihb => exact add_mem iha ihb
  | smul c a ha iha =>
    rw [show (⟨c • a, Submodule.smul_mem _ c ha⟩ : lat hvt hR A Λ) = c • ⟨a, ha⟩ from rfl,
      ← Module.Quotient.mk_smul_mk]
    exact Submodule.smul_mem _ _ iha

omit [Finite I] in
/-- `f̃ᵢ b ≡ b' ↔ ẽᵢ b' ≡ b` for nonzero classes of `f̃`-words, from `C(r)` for all `r`. -/
lemma fK_sub_mem_iff (hC : ∀ r, PropC hvt hR A ϖ r) (Λ : Dom R) (i : I) {w w' : List I}
    (hw0 : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) (hw'0 : fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ) :
    fK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ ↔
      eK hvt hR Λ i (fW hvt hR Λ w') - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hlen : ∀ w : List I, (wordWeight w).degree = w.length := degree_wordWeight
  constructor
  · intro h
    have hf0 : fK hvt hR Λ i (fW hvt hR Λ w) ∉ ϖ • lat hvt hR A Λ := fun hm ↦
      hw'0 (by have := sub_mem hm h; rwa [sub_sub_cancel] at this)
    have hwt : wordWeight w' = wordWeight w + Finsupp.single i 1 :=
      wordWeight_eq_of_sub_mem hvt hR A ϖ Λ (by
        have := kashiwaraF_mem_weightSpace hv' (isInt hvt hR Λ) i (fW_mem_wsp hvt hR Λ w)
        convert this using 2
        rw [R.rootSum_add, R.rootSum_single, one_nsmul]; abel) hf0 h
    have hl : w.length + 1 = w'.length := by
      rw [← hlen, ← hlen, hwt, map_add, Finsupp.degree_single]
    have := ((hC w'.length) Λ i w w' hl rfl hw0 hw'0).1 h
    have := neg_mem this
    rwa [neg_sub] at this
  · intro h
    have he0 : eK hvt hR Λ i (fW hvt hR Λ w') ∉ ϖ • lat hvt hR A Λ := fun hm ↦
      hw0 (by have := sub_mem hm h; rwa [sub_sub_cancel] at this)
    have hew := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i (fW_mem_wsp hvt hR Λ w')
    obtain ⟨ν₀, hν₀⟩ := exists_eq_add_single hR hv' Λ (i := i) (j := 1)
      (ν := wordWeight w') (by rw [one_smul]; exact hew)
      (fun h0 ↦ he0 (by rw [h0]; exact zero_mem _))
    have hwt : wordWeight w = ν₀ := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ
      (by convert hew using 2; rw [hν₀, R.rootSum_add, R.rootSum_single, one_nsmul]; abel)
      he0 h
    have hl : w.length + 1 = w'.length := by
      rw [← hlen, ← hlen, hν₀, hwt, map_add, Finsupp.degree_single]
    exact ((hC w'.length) Λ i w w' hl rfl hw0 hw'0).2
      (by have := neg_mem h; rwa [neg_sub] at this)

omit [Finite I] in
lemma eQ_mem_base (hB : ∀ r, PropB hvt hR A ϖ r) (Λ : Dom R)
    (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
      (lat hvt hR A Λ)) (i : I) (b : QL (ϖ := ϖ) Λ)
    (hb : b ∈ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    hL.eQ ϖ i b ∈ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ ∨
      hL.eQ ϖ i b = 0 := by
  obtain ⟨w, rfl, hw0⟩ := (mem_base_iff Λ b).1 hb
  rcases hB w.length Λ w rfl i with h | ⟨w', h⟩
  · exact Or.inr ((IntegrableSl2.mk_eq_zero_iff ϖ _).2 h)
  · have he : hL.eQ ϖ i (Submodule.Quotient.mk (fwL hvt hR A Λ w)) =
        Submodule.Quotient.mk (fwL hvt hR A Λ w') := (IntegrableSl2.mk_eq_mk_iff ϖ _ _).2 h
    rw [he]
    exact mk_fwL_mem_or Λ w'

omit [Finite I] in
lemma fQ_mem_base (Λ : Dom R)
    (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
      (lat hvt hR A Λ)) (i : I) (b : QL (ϖ := ϖ) Λ)
    (hb : b ∈ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    hL.fQ ϖ i b ∈ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ ∨
      hL.fQ ϖ i b = 0 := by
  obtain ⟨w, rfl, hw0⟩ := (mem_base_iff Λ b).1 hb
  exact mk_fwL_mem_or Λ (i :: w)

omit [Finite I] in
lemma fQ_eq_iff_base (hC : ∀ r, PropC hvt hR A ϖ r) (Λ : Dom R)
    (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
      (lat hvt hR A Λ)) (i : I) (b : QL (ϖ := ϖ) Λ)
    (hb : b ∈ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ)
    (b' : QL (ϖ := ϖ) Λ)
    (hb' : b' ∈ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    hL.fQ ϖ i b = b' ↔ hL.eQ ϖ i b' = b := by
  obtain ⟨w, rfl, hw0⟩ := (mem_base_iff Λ b).1 hb
  obtain ⟨w', rfl, hw'0⟩ := (mem_base_iff Λ b').1 hb'
  change (Submodule.Quotient.mk (fwL hvt hR A Λ (i :: w)) : QL (ϖ := ϖ) Λ) = _ ↔
    (Submodule.Quotient.mk ⟨eK hvt hR Λ i (fW hvt hR Λ w'),
      hL.kashiwaraE_mem i _ (fwL hvt hR A Λ w').2⟩ : QL (ϖ := ϖ) Λ) = _
  rw [IntegrableSl2.mk_eq_mk_iff, IntegrableSl2.mk_eq_mk_iff]
  exact fK_sub_mem_iff hC Λ i hw0 hw'0

omit [Finite I] in
/-- The crystal-base properties of `B(λ)` with respect to a crystal lattice structure on
`L(λ)`. -/
lemma isCrystalBase_of (hB : ∀ r, PropB hvt hR A ϖ r) (hC : ∀ r, PropC hvt hR A ϖ r)
    (hD : ∀ r, PropD hvt hR A ϖ r) (Λ : Dom R)
    (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
      (lat hvt hR A Λ)) :
    IsCrystalBase hL ϖ (IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ)
    where
  linearIndependent := linearIndependent_base hD Λ
  span_eq_top := span_base (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) Λ
  exists_weight b hb := by
    obtain ⟨w, rfl, -⟩ := (mem_base_iff Λ b).1 hb
    exact ⟨_, fwL hvt hR A Λ w, fW_mem_wsp hvt hR Λ w, rfl⟩
  eQ_mem := eQ_mem_base hB Λ hL
  fQ_mem := fQ_mem_base Λ hL
  fQ_eq_iff := fQ_eq_iff_base hC Λ hL

variable [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- **Existence of crystal bases** (Kashiwara; [HK] Thm. 5.1.1): `(L(λ), B(λ))` is a crystal base
of `V(λ)` at `ϖ`. -/
theorem isCrystalBase (Λ : Dom R) :
    ∃ hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
      (lat hvt hR A Λ),
      IsCrystalBase hL ϖ (IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ)
      := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  exact ⟨{ span_eq_top := IrreducibleModule.span_lattice hR _ Λ.2 A
           free := free_lat hinj Λ
           weightSetProj_mem := fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ S hm
           kashiwaraE_mem := fun i _ hm ↦ kashiwaraE_mem_lat (fun r ↦ (hall r).1) Λ i hm
           kashiwaraF_mem := fun i _ hm ↦ kashiwaraF_mem_lat Λ i hm },
    isCrystalBase_of (fun r ↦ (hall r).2.1) (fun r ↦ (hall r).2.2.1)
      (fun r ↦ (hall r).2.2.2.1) Λ _⟩

end Base

end GrandLoop

end LieLean.QuantumGroup
