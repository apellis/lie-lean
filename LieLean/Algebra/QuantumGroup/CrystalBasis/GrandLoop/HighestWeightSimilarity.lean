/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityProj
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinitySimilarity
import LieLean.RepresentationTheory.Crystal.SimilarityEmbedding

/-!
# Similarity of the crystals `B(λ)`

For dominant `λ` and `m > 0` there is an `m`-similarity `S_λ : B(λ) → B(mλ)` of the crystals of
the crystal bases `(L(λ), B(λ))` of `L_q(λ)`, with `S_λ(u_λ) = u_{mλ}` ([Kas96] Thm. 3.1):
`S_λ(f̃_{i₁} ⋯ f̃_{iₗ} u_λ) = f̃_{i₁}ᵐ ⋯ f̃_{iₗ}ᵐ u_{mλ}`.

## Main definitions

* `GrandLoop.crystalHW`: the crystal of `(L(λ), B(λ))` (`GrandLoop.isCrystalBase`), with the
  highest weight element `GrandLoop.topHW`.
* `GrandLoop.jHW`: the weak embedding `B(λ) → B(∞)`, `f̃_w u_λ ↦ f̃_w u_∞`
  (`GrandLoop.isWeakEmbedding_jHW`).

## Main results

* `GrandLoop.fWord_crystalHW`: `f̃_w u_λ` is the class of `f̃_w v_λ` (or `0`).
* `GrandLoop.exists_similarityHW`: [Kas96] Thm. 3.1.

## Proof

As in [Kas96], from the similarity of `B(∞)` (`GrandLoop.similarityInf`, [Kas96] Thm. 3.2) through
the embeddings `B(λ) → B(∞) ⊗ T_λ`: we use `π̄_λ` (`GrandLoop.fWi_sub_mem_of_fW_sub_mem`,
[Jan] Prop. 10.14, and `GrandLoop.evq_fWord_sub_fW_mem`) and the abstract statement
`Crystal.Similarity.exists_of_isWeakEmbedding`.

## References

* [Kas96] M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194 (1996), 177–186, §3.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Prop. 10.14.
-/

open LusztigF Pointwise

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

variable (R) in
/-- `m λ` for a dominant weight `λ`. -/
def nsmulDom (m : ℕ) (Λ : Dom R) : Dom R :=
  ⟨m • Λ.1, fun i ↦ by rw [AddMonoidHom.smul_apply]; exact nsmul_nonneg (Λ.2 i) m⟩

omit [DecidableEq I] in
@[simp] lemma nsmulDom_val (m : ℕ) (Λ : Dom R) : (nsmulDom R m Λ).1 = m • Λ.1 := rfl

omit [DecidableEq I] [NeZero v] [CharZero k] in
lemma not_isUnit_ϖ [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) : ¬IsUnit ϖ :=
  (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ

variable (hvt hR) in
/-- The element `f̃_w u_λ = [f̃_w v_λ]` of `B(λ)`, for `f̃_w v_λ ∉ ϖ L(λ)`. -/
def mkHW (Λ : Dom R) (w : List I) (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) :
    IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ :=
  ⟨Submodule.Quotient.mk (fwL hvt hR A Λ w), (mem_base_iff Λ _).2 ⟨w, rfl, hw⟩⟩

lemma mkHW_eq_mkHW_iff (Λ : Dom R) {w w' : List I} (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (hw' : fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ) :
    mkHW hvt hR Λ w hw = mkHW hvt hR Λ w' hw' ↔
      fW hvt hR Λ w - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ := by
  rw [mkHW, mkHW, Subtype.mk.injEq, IntegrableSl2.mk_eq_mk_iff]

lemma exists_mkHW (Λ : Dom R)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    ∃ (w : List I) (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ), b = mkHW hvt hR Λ w hw := by
  obtain ⟨w, hb, hw⟩ := (mem_base_iff Λ b.1).1 b.2
  exact ⟨w, hw, Subtype.ext hb⟩

lemma fW_nil_notMem (hinj : Function.Injective (algebraMap A k)) [IsLocalRing A]
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (Λ : Dom R) : fW hvt hR Λ [] ∉ ϖ • lat hvt hR A Λ :=
  hwv_notMem hinj (not_isUnit_ϖ hϖ) Λ

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

variable (hvt hR) in
/-- `(L(λ), B(λ))` is a crystal base of `L_q(λ)` ([HK] Thm. 5.1.1). -/
lemma isCrystalBaseHW (Λ : Dom R) :
    IsCrystalBase (isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ) ϖ
      (IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :=
  (isCrystalBase (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ).choose_spec

variable (hvt hR) in
/-- The crystal `B(λ)` of the crystal base `(L(λ), B(λ))` of `L_q(λ)`. -/
def crystalHW (Λ : Dom R) : Crystal R.crystalDatum
    (IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :=
  (isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ).crystal (not_isUnit_ϖ hϖ)

variable (hvt hR) in
/-- The highest weight element `u_λ = [v_λ]` of `B(λ)`. -/
def topHW (Λ : Dom R) : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ :=
  mkHW hvt hR Λ [] (fW_nil_notMem hinj hϖ Λ)

lemma f_crystalHW_mkHW (Λ : Dom R) (i : I) {w : List I}
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) (hiw : fW hvt hR Λ (i :: w) ∉ ϖ • lat hvt hR A Λ) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).f i (mkHW hvt hR Λ w hw) =
      some (mkHW hvt hR Λ (i :: w) hiw) :=
  ((isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ).f_eq_some_iff (not_isUnit_ϖ hϖ) i _ _).2 rfl

lemma f_crystalHW_mkHW_eq_none (Λ : Dom R) (i : I) {w : List I}
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) (hiw : fW hvt hR Λ (i :: w) ∈ ϖ • lat hvt hR A Λ) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).f i (mkHW hvt hR Λ w hw) = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  intro b hb
  have h := ((isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ).f_eq_some_iff (not_isUnit_ϖ hϖ) i
    _ _).1 hb
  have h0 : (Submodule.Quotient.mk (fwL hvt hR A Λ (i :: w)) : QL (ϖ := ϖ) Λ) = 0 :=
    (IntegrableSl2.mk_eq_zero_iff ϖ _).2 hiw
  have hb0 : b.1 = 0 := h.symm.trans h0
  exact (isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ).zero_notMem (not_isUnit_ϖ hϖ)
    (hb0 ▸ b.2)

/-- `f̃_w u_λ` is the class of `f̃_w v_λ`, or `0` if `f̃_w v_λ ∈ ϖ L(λ)`. -/
theorem fWord_crystalHW (Λ : Dom R) (w : List I) :
    (∀ hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ,
      (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).fWord w (topHW hvt hR hinj hϖ Λ) =
        some (mkHW hvt hR Λ w hw)) ∧
    (fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ →
      (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).fWord w
        (topHW hvt hR hinj hϖ Λ) = none) := by
  induction w with
  | nil => exact ⟨fun _ ↦ rfl, fun h ↦ absurd h (fW_nil_notMem hinj hϖ Λ)⟩
  | cons i w ih =>
    by_cases hw : fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ
    · have hiw : fW hvt hR Λ (i :: w) ∈ ϖ • lat hvt hR A Λ := kashiwaraF_mem_smul_lat Λ i hw
      refine ⟨fun h ↦ absurd hiw h, fun _ ↦ ?_⟩
      rw [Crystal.fWord_cons, ih.2 hw]
      rfl
    · rw [Crystal.fWord_cons, ih.1 hw, Option.bind_some]
      refine ⟨fun hiw ↦ f_crystalHW_mkHW hinj hϖ hϖv hk hfund Λ i hw hiw,
        fun hiw ↦ f_crystalHW_mkHW_eq_none hinj hϖ hϖv hk hfund Λ i hw hiw⟩

variable (hvt hR) in
/-- `B(λ)` is generated by `u_λ`. -/
theorem exists_fWord_crystalHW (Λ : Dom R)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    ∃ w, (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).fWord w
      (topHW hvt hR hinj hϖ Λ) = some b := by
  obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) Λ b
  exact ⟨w, (fWord_crystalHW hinj hϖ hϖv hk hfund Λ w).1 hw⟩

variable (hvt hR) in
lemma isSeminormal_crystalHW (Λ : Dom R) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).IsSeminormal :=
  (isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ).isSeminormal_crystal _

lemma wt_mkHW (Λ : Dom R) (w : List I) (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).wt (mkHW hvt hR Λ w hw) =
      Λ.1 - R.rootSum (wordWeight w) :=
  (isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ).wt_eq (not_isUnit_ϖ hϖ) (mkHW hvt hR Λ w hw)
    (fwL hvt hR A Λ w) (fW_mem_wsp hvt hR Λ w) rfl

/-! ### The weak embedding `B(λ) → B(∞)` -/

lemma fW_sub_mem_of_mkB_eq (Λ : Dom R) {w w' : List I}
    (h : mkB hvt hR hinj hϖ hϖv hk hfund w = mkB hvt hR hinj hϖ hϖv hk hfund w') :
    fW hvt hR Λ w - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ := by
  rw [mkB_eq_mkB_iff] at h
  have h1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund h Λ
  have h2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) hinj hϖ hϖv hk
    hfund w Λ
  have h3 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) hinj hϖ hϖv hk
    hfund w' Λ
  rw [map_sub] at h1
  have := sub_mem (sub_mem h1 h2) (neg_mem h3)
  convert this using 1
  abel

lemma mkB_eq_of_fW_sub_mem (Λ : Dom R) {w w' : List I} (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (h : fW hvt hR Λ w - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ) :
    mkB hvt hR hinj hϖ hϖv hk hfund w = mkB hvt hR hinj hϖ hϖv hk hfund w' := by
  rw [mkB_eq_mkB_iff]
  exact fWi_sub_mem_of_fW_sub_mem hinj hϖ hϖv hk hfund _ w w' rfl hw h

variable (hvt hR) in
/-- The map `B(λ) → B(∞)`, `f̃_w u_λ ↦ f̃_w u_∞`. -/
def jHW (Λ : Dom R) (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    BInf (D := D) hvt A ϖ :=
  mkB hvt hR hinj hϖ hϖv hk hfund (exists_mkHW (hvt := hvt) Λ b).choose

lemma jHW_mkHW (Λ : Dom R) (w : List I) (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) :
    jHW hvt hR hinj hϖ hϖv hk hfund Λ (mkHW hvt hR Λ w hw) =
      mkB hvt hR hinj hϖ hϖv hk hfund w := by
  obtain ⟨hw', h⟩ := (exists_mkHW (hvt := hvt) Λ (mkHW hvt hR Λ w hw)).choose_spec
  rw [jHW]
  refine mkB_eq_of_fW_sub_mem hinj hϖ hϖv hk hfund Λ hw' ?_
  exact (mkHW_eq_mkHW_iff Λ hw' hw).1 h.symm

lemma fInf_mkB (i : I) (w : List I) :
    (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).f i (mkB hvt hR hinj hϖ hϖv hk hfund w) =
      some (mkB hvt hR hinj hϖ hϖv hk hfund (i :: w)) := rfl

lemma f_mkHW (Λ : Dom R) (i : I) {w : List I} (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    {b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ}
    (h : (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).f i (mkHW hvt hR Λ w hw) = some b) :
    ∃ hiw, b = mkHW hvt hR Λ (i :: w) hiw := by
  by_cases hiw : fW hvt hR Λ (i :: w) ∈ ϖ • lat hvt hR A Λ
  · rw [f_crystalHW_mkHW_eq_none hinj hϖ hϖv hk hfund Λ i hw hiw] at h
    cases h
  · rw [f_crystalHW_mkHW hinj hϖ hϖv hk hfund Λ i hw hiw] at h
    exact ⟨hiw, (Option.some_injective _ h).symm⟩

lemma e_jHW (Λ : Dom R) (i : I)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).e i (jHW hvt hR hinj hϖ hϖv hk hfund Λ b) =
      ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).e i b).map
        (jHW hvt hR hinj hϖ hϖv hk hfund Λ) := by
  obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) Λ b
  cases he : (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).e i (mkHW hvt hR Λ w hw) with
  | some b₂ =>
    obtain ⟨u, hu, rfl⟩ := exists_mkHW (hvt := hvt) Λ b₂
    have hf := ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).f_eq_some_iff i _ _).2 he
    obtain ⟨hiu, hb⟩ := f_mkHW hinj hϖ hϖv hk hfund Λ i hu hf
    rw [Option.map_some, Crystal.e_eq_some_iff, jHW_mkHW, jHW_mkHW, fInf_mkB]
    congr 1
    exact mkB_eq_of_fW_sub_mem hinj hϖ hϖv hk hfund Λ hiu
      ((mkHW_eq_mkHW_iff Λ hiu hw).1 hb.symm)
  | none =>
    rw [Option.map_none, Option.eq_none_iff_forall_ne_some]
    intro x hx
    obtain ⟨u, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund x
    rw [Crystal.e_eq_some_iff, fInf_mkB, jHW_mkHW, Option.some_inj] at hx
    have h1 := fW_sub_mem_of_mkB_eq hinj hϖ hϖv hk hfund Λ hx
    have hu : fW hvt hR Λ u ∉ ϖ • lat hvt hR A Λ := fun hm ↦ by
      have hm' : fW hvt hR Λ (i :: u) ∈ ϖ • lat hvt hR A Λ := kashiwaraF_mem_smul_lat Λ i hm
      exact hw (by have := sub_mem hm' h1; rwa [sub_sub_cancel] at this)
    have hiu : fW hvt hR Λ (i :: u) ∉ ϖ • lat hvt hR A Λ := fun hm ↦
      hw (by have := sub_mem hm h1; rwa [sub_sub_cancel] at this)
    have hf : (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).f i (mkHW hvt hR Λ u hu) =
        some (mkHW hvt hR Λ w hw) := by
      rw [f_crystalHW_mkHW hinj hϖ hϖv hk hfund Λ i hu hiu, (mkHW_eq_mkHW_iff Λ hiu hw).2 h1]
    rw [((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).f_eq_some_iff i _ _).1 hf] at he
    cases he

lemma isSome_eIter_crystalInf (i : I) (n : ℕ) (x : BInf (D := D) hvt A ϖ) :
    ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).eIter i n x).isSome ↔
      (n : WithBot ℤ) ≤ (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).ε i x := by
  classical
  have key : ∀ (n : ℕ) (x : BInf (D := D) hvt A ϖ),
      ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).eIter i n x).isSome ↔
        (eQInf hR hinj hϖ hϖv hk hfund i ^ n) x.1 ≠ 0 := by
    intro n
    induction n with
    | zero => intro x; simpa using fun h ↦ zero_notMem_BInf (h ▸ x.2)
    | succ n ih =>
      intro x
      rw [Crystal.eIter_succ, pow_succ, Module.End.mul_apply]
      change ((eInf hR hinj hϖ hϖv hk hfund i x).bind _).isSome ↔ _
      unfold eInf
      split_ifs with h
      · simp [h]
      · rw [Option.bind_some, ih]
  rw [key]
  change _ ↔ (n : WithBot ℤ) ≤ ((epsInf hR hinj hϖ hϖv hk hfund i x : ℤ) : WithBot ℤ)
  rw [← WithBot.coe_natCast, WithBot.coe_le_coe, Nat.cast_le, epsInf]
  have h0 : (eQInf hR hinj hϖ hϖv hk hfund i ^ 0) x.1 ≠ 0 := by
    simpa using fun h ↦ zero_notMem_BInf (h ▸ x.2)
  have hpos : 0 < Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i x) :=
    Nat.pos_of_ne_zero fun h ↦ h0 (h ▸ Nat.find_spec
      (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i x))
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hle : Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i x) ≤ n := by
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    apply h
    rw [hd, add_comm, pow_add, Module.End.mul_apply, Nat.find_spec
      (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i x), map_zero]
  · intro h hn
    exact Nat.find_min (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund i x)
      (show n < _ by omega) hn

variable (hvt hR) in
/-- `B(λ) → B(∞)` is a weak embedding (cf. [Kas96] §2, `B(λ) ↪ B(∞) ⊗ T_λ`). -/
theorem isWeakEmbedding_jHW (Λ : Dom R) :
    Crystal.IsWeakEmbedding (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
      (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund) (topHW hvt hR hinj hϖ Λ)
      (jHW hvt hR hinj hϖ hϖv hk hfund Λ) where
  injective b b' h := by
    obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) Λ b
    obtain ⟨w', hw', rfl⟩ := exists_mkHW (hvt := hvt) Λ b'
    rw [jHW_mkHW, jHW_mkHW] at h
    exact (mkHW_eq_mkHW_iff Λ hw hw').2
      (fW_sub_mem_of_mkB_eq hinj hϖ hϖv hk hfund Λ h)
  ε_map i b := by
    have hC := isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ
    have heIter : ∀ n (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ),
        (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).eIter i n
          (jHW hvt hR hinj hϖ hϖv hk hfund Λ b) =
        ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).eIter i n b).map
          (jHW hvt hR hinj hϖ hϖv hk hfund Λ) := by
      intro n
      induction n with
      | zero => intro b; rfl
      | succ n ih =>
        intro b
        rw [Crystal.eIter_succ, Crystal.eIter_succ, e_jHW]
        cases (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).e i b with
        | none => rfl
        | some c => exact ih c
    obtain ⟨n, hn⟩ := hC.exists_ε_eq i b
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).ε i
        (jHW hvt hR hinj hϖ hϖv hk hfund Λ b) = n' :=
      ⟨epsInf hR hinj hϖ hϖv hk hfund i _, by
        change ((epsInf hR hinj hϖ hϖv hk hfund i _ : ℤ) : WithBot ℤ) = _; rfl⟩
    have h1 : ∀ c : ℕ, ((c : WithBot ℤ) ≤ n' ↔ (c : WithBot ℤ) ≤ n) := fun c ↦ by
      rw [← hn, ← hn', ← isSome_eIter_crystalInf hinj hϖ hϖv hk hfund, heIter,
        Option.isSome_map, hC.isSome_eIter_iff]
    rw [hn, hn']
    have a1 := (h1 n).2 le_rfl
    have a2 := (h1 n').1 le_rfl
    exact_mod_cast le_antisymm (by exact_mod_cast a2) (by exact_mod_cast a1)
  wt_map b := by
    obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) Λ b
    rw [jHW_mkHW, wt_mkHW, topHW, wt_mkHW]
    change wtInf (R := R) _ = _
    rw [wtInf_mkB, wordWeight_nil, R.rootSum_zero, sub_zero]
    abel
  f_map i b b₁ h := by
    obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) Λ b
    obtain ⟨hiw, rfl⟩ := f_mkHW hinj hϖ hϖv hk hfund Λ i hw h
    rw [jHW_mkHW, jHW_mkHW, fInf_mkB]

variable (hvt hR) in
lemma jHW_topHW (Λ : Dom R) :
    jHW hvt hR hinj hϖ hϖv hk hfund Λ (topHW hvt hR hinj hϖ Λ) =
      mkB hvt hR hinj hϖ hϖv hk hfund [] :=
  jHW_mkHW hinj hϖ hϖv hk hfund Λ [] _

/-- **Similarity of `B(λ)`** ([Kas96] Thm. 3.1): for `m > 0` there is an `m`-similarity
`S_λ : B(λ) → B(mλ)` with `S_λ(u_λ) = u_{mλ}`. -/
theorem exists_similarityHW [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {m : ℕ} (hm : 0 < m)
    (Λ : Dom R) :
    ∃ S : Crystal.Similarity (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
      (crystalHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom R m Λ)) m,
      S (topHW hvt hR hinj hϖ Λ) = topHW hvt hR hinj hϖ (nsmulDom R m Λ) := by
  obtain ⟨S, hS, -⟩ := Crystal.Similarity.exists_of_isWeakEmbedding hm
    (isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
    (isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom R m Λ))
    (exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
    (by rw [topHW, topHW, wt_mkHW, wt_mkHW]; simp)
    (isWeakEmbedding_jHW hvt hR hinj hϖ hϖv hk hfund Λ)
    (isWeakEmbedding_jHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom R m Λ))
    (by rw [jHW_topHW, jHW_topHW])
    (similarityInf hvt hR hinj hϖ hϖv hk hfund hm)
    (by rw [jHW_topHW, similarityInf_one])
  exact ⟨S, hS⟩

end GrandLoop

end LieLean.QuantumGroup
