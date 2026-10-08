/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Rank1

/-!
# Kashiwara operators on integrable `U_q(𝔰𝔩₂)`-modules

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module (`QuantumGroup.IntegrableSl2`) over a field `k`, with
`q` nonzero and not a root of unity. Every vector `m ∈ Mⁿ` can be written uniquely as
`m = Σⱼ F^{(j)} ηⱼ` with `ηⱼ ∈ M^{n+2j}` primitive (`E ηⱼ = 0`) and `F^{(j)} ηⱼ ≠ 0` only if
`n + j ≥ 0` ([HK] Lemma 4.1.1). The Kashiwara operators are
`ẽ m = Σⱼ F^{(j-1)} ηⱼ` and `f̃ m = Σⱼ F^{(j+1)} ηⱼ` ([HK] Def. 4.1.2).

We encode the decomposition as a linear equivalence (`IntegrableSl2.stringEquiv`) between `M`
and the direct sum, over pairs `(n, j)` with `n + j ≥ 0`, of the spaces of primitive vectors of
weight `n + 2j` (`IntegrableSl2.stringSummand`); `ẽ` and `f̃` are the composites of its inverse
with the maps `η ↦ F^{(j-1)} η` and `η ↦ F^{(j+1)} η` on the summands.

## Main definitions

* `IntegrableSl2.prim p`: the primitive vectors of weight `p`.
* `IntegrableSl2.stringEquiv`: the string decomposition `⨁_{(n, j)} prim (n + 2j) ≃ M`.
* `IntegrableSl2.eTilde`, `IntegrableSl2.fTilde`: the Kashiwara operators `ẽ`, `f̃`.

## Main results

* `IntegrableSl2.dF_eq_zero_of_sum_eq_zero`: uniqueness of the string decomposition
  ([HK] Lemma 4.1.1).
* `IntegrableSl2.eTilde_dF_succ`, `IntegrableSl2.eTilde_of_primitive`,
  `IntegrableSl2.fTilde_dF`: `ẽ F^{(j+1)} η = F^{(j)} η` for `j < p`, `ẽ η = 0` and
  `f̃ F^{(j)} η = F^{(j+1)} η` for `η ∈ Mᵖ` primitive.
* `IntegrableSl2.eTilde_mem`, `IntegrableSl2.fTilde_mem`: `ẽ Mⁿ ⊆ M^{n+2}`, `f̃ Mⁿ ⊆ M^{n-2}`.
* `IntegrableSl2.map_eTilde`, `IntegrableSl2.map_fTilde`: the Kashiwara operators commute with
  linear maps commuting with `E`, `F` and preserving the gradings ([HK] Prop. 4.1.3 (2)).
* `IntegrableSl2.flip_eTilde`: `ẽ` of the module with `E` and `F` interchanged is `f̃`.
* `IntegrableSl2.eTilde_eq_zero_iff`: `ẽ m = 0 ↔ E m = 0`.
* `IntegrableSl2.exists_sum_dF`: every `m ∈ Mⁿ` is a finite sum `Σ F^{(j)} ηⱼ` as above.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.1.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §3.
-/

open Finset DirectSum

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M)

/-! ### Primitive vectors and string summands -/

/-- The primitive vectors of weight `p`: `Mᵖ ∩ ker E`. -/
def prim (p : ℤ) : Submodule k M := V.wt p ⊓ LinearMap.ker V.E

/-- The summand `(n, j)` of the string decomposition: the primitive vectors of weight `n + 2j`
if `n + j ≥ 0` (so that `F^{(j)}` is injective on them), and `0` otherwise. -/
def stringSummand (i : ℤ × ℕ) : Submodule k M :=
  if 0 ≤ i.1 + i.2 then V.prim (i.1 + 2 * i.2) else ⊥

variable {V}

lemma mem_prim {p : ℤ} {η : M} : η ∈ V.prim p ↔ η ∈ V.wt p ∧ V.E η = 0 := Iff.rfl

lemma stringSummand_le (i : ℤ × ℕ) : V.stringSummand i ≤ V.prim (i.1 + 2 * i.2) := by
  unfold stringSummand
  split_ifs
  · exact le_rfl
  · exact bot_le

lemma mem_stringSummand {n : ℤ} {j : ℕ} (h : 0 ≤ n + j) {η : M} :
    η ∈ V.stringSummand (n, j) ↔ η ∈ V.prim (n + 2 * j) := by
  simp [stringSummand, h]

/-- The projection of `M` onto `Mⁿ`, as an endomorphism of `M`. -/
noncomputable def wtProj (n : ℤ) : Module.End k M :=
  (V.wt n).subtype ∘ₗ DirectSum.component k ℤ (fun n ↦ V.wt n) n ∘ₗ V.decompose.toLinearMap

lemma wtProj_of_mem {n n' : ℤ} {m : M} (hm : m ∈ V.wt n') :
    V.wtProj n m = if n' = n then m else 0 := by
  simp only [wtProj, LinearMap.comp_apply, LinearEquiv.coe_coe, decompose_of_mem V hm,
    ← DirectSum.lof_eq_of k]
  split_ifs with h
  · subst h
    rw [DirectSum.component.lof_self]
    rfl
  · rw [DirectSum.component.of]
    simp [h]

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-! ### Uniqueness of the string decomposition -/

/-- `E F^{(j)} η = [p - j + 1] F^{(j-1)} η`, in the form used below. -/
lemma E_dF_of_prim {p : ℤ} {η : M} (hη : η ∈ V.prim p) (j : ℕ) :
    V.E (V.dF (j + 1) η) = qIntZ q (p - j) • V.dF j η :=
  E_dF_succ_of_primitive hq0 hq hη.1 hη.2 j

/-- If `F^{(j)} η = 0` would follow from `c • F^{(j-1)} η = 0` for the coefficient
`c = [p - j + 1]`. -/
lemma dF_succ_eq_zero_of_smul {p : ℤ} {η : M} (hη : η ∈ V.prim p) {j : ℕ}
    (h : qIntZ q (p - j) • V.dF j η = 0) : V.dF (j + 1) η = 0 := by
  by_cases hc : p - j = 0
  · exact dF_eq_zero_of_primitive hq0 hq hη.1 hη.2 (by push_cast; omega)
  · have h' := (smul_eq_zero.1 h).resolve_left (qIntZ_ne_zero hq0 hq hc)
    have e := F_dF hq0 hq (V := V) j η
    rw [h', map_zero] at e
    exact (smul_eq_zero.1 e.symm).resolve_left
      (qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos j))

/-- Uniqueness of the string decomposition ([HK] Lemma 4.1.1): if `Σ_{j<N} F^{(j)} ηⱼ = 0` with
`ηⱼ ∈ M^{n+2j}` primitive, then every `F^{(j)} ηⱼ` vanishes. (We apply `E` and induct on `N`.) -/
theorem dF_eq_zero_of_sum_range_eq_zero (N : ℕ) :
    ∀ (n : ℤ) (η : ℕ → M), (∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) →
      ∑ j ∈ range N, V.dF j (η j) = 0 → ∀ j < N, V.dF j (η j) = 0 := by
  induction N with
  | zero => intro _ _ _ _ j hj; omega
  | succ N ih =>
    intro n η hη hsum
    rw [sum_range_succ'] at hsum
    -- apply `E`
    have hE : ∑ j ∈ range N, V.dF j (qIntZ q (n + j + 2) • η (j + 1)) = 0 := by
      have := congrArg V.E hsum
      rw [map_add, map_sum, map_zero, dF_zero, (hη 0).2, add_zero] at this
      rw [← this]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [E_dF_of_prim hq0 hq (hη (j + 1)) j, map_smul]
      congr 2
      push_cast
      ring
    have hη' : ∀ j : ℕ, qIntZ q (n + j + 2) • η (j + 1) ∈ V.prim (n + 2 + 2 * j) := by
      intro j
      have h := Submodule.smul_mem _ (qIntZ q (n + j + 2)) (hη (j + 1))
      convert h using 2
      push_cast
      ring
    have h1 := ih (n + 2) _ hη' hE
    have hsucc : ∀ j < N, V.dF (j + 1) (η (j + 1)) = 0 := by
      intro j hj
      refine dF_succ_eq_zero_of_smul hq0 hq (hη (j + 1)) ?_
      rw [← map_smul]
      convert h1 j hj using 3
      push_cast
      ring_nf
    intro j hj
    rcases j with _ | j
    · rw [sum_eq_zero fun j hj ↦ hsucc j (mem_range.1 hj), zero_add] at hsum
      exact hsum
    · exact hsucc j (by omega)

/-- Uniqueness of the string decomposition, for a finite set of indices. -/
theorem dF_eq_zero_of_sum_eq_zero {n : ℤ} {t : Finset ℕ} {η : ℕ → M}
    (hη : ∀ j ∈ t, η j ∈ V.prim (n + 2 * (j : ℕ))) (hsum : ∑ j ∈ t, V.dF j (η j) = 0) :
    ∀ j ∈ t, V.dF j (η j) = 0 := by
  classical
  set η' : ℕ → M := fun j ↦ if j ∈ t then η j else 0
  have hη' : ∀ j : ℕ, η' j ∈ V.prim (n + 2 * j) := fun j ↦ by
    by_cases hj : j ∈ t
    · simpa [η', hj] using hη j hj
    · simp [η', hj]
  set N := t.sup id + 1
  have ht : t ⊆ range N := fun j hj ↦ mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hj))
  have hsum' : ∑ j ∈ range N, V.dF j (η' j) = 0 := by
    rw [← sum_subset ht fun j _ hj ↦ by simp [η', hj]]
    rw [← hsum]
    exact sum_congr rfl fun j hj ↦ by simp [η', hj]
  intro j hj
  have := dF_eq_zero_of_sum_range_eq_zero hq0 hq N n η' hη' hsum' j (mem_range.1 (ht hj))
  simpa [η', hj] using this

/-- `F^{(j)}` is injective on primitive vectors of weight `p ≥ j`. -/
lemma eq_zero_of_dF_eq_zero {p : ℕ} {η : M} (hη : η ∈ V.prim p) {j : ℕ} (hj : j ≤ p)
    (h : V.dF j η = 0) : η = 0 := by
  have e := dE_dF_of_primitive hq0 hq hη.1 hη.2 (le_refl j) hj
  rw [h, map_zero, Nat.sub_self, dF_zero, Nat.sub_add_cancel hj] at e
  exact (smul_eq_zero.1 e.symm).resolve_left (qBinomial_ne_zero_of_pow_ne_one hq0 hq hj)

lemma eq_zero_of_dF_eq_zero_of_mem_stringSummand {n : ℤ} {j : ℕ} {η : M}
    (hη : η ∈ V.stringSummand (n, j)) (h : V.dF j η = 0) : η = 0 := by
  by_cases hnj : 0 ≤ n + j
  · rw [mem_stringSummand hnj] at hη
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * j := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    rw [← hp] at hη
    exact eq_zero_of_dF_eq_zero hq0 hq hη (by omega) h
  · simpa [stringSummand, hnj] using hη

omit hq0 hq in
lemma dF_mem_wt_of_mem_stringSummand {n : ℤ} {j : ℕ} {η : M}
    (hη : η ∈ V.stringSummand (n, j)) : V.dF j η ∈ V.wt n := by
  have h := dF_mem (stringSummand_le (n, j) hη).1 j
  rwa [show n + 2 * (j : ℤ) - 2 * j = n by ring] at h

/-! ### The string decomposition -/

variable (V) in
/-- The map `⨁_{(n, j)} prim (n + 2j) → M`, `(ηₙⱼ) ↦ Σ F^{(j)} ηₙⱼ`. -/
noncomputable def stringMap : (⨁ i : ℤ × ℕ, V.stringSummand i) →ₗ[k] M :=
  DirectSum.toModule k (ℤ × ℕ) M fun i ↦ V.dF i.2 ∘ₗ (V.stringSummand i).subtype

omit hq0 hq in
lemma stringMap_lof (i : ℤ × ℕ) (η : V.stringSummand i) :
    V.stringMap (DirectSum.lof k (ℤ × ℕ) (fun i ↦ V.stringSummand i) i η) = V.dF i.2 η := by
  simp [stringMap, DirectSum.toModule_lof]

theorem stringMap_injective : Function.Injective V.stringMap := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  -- `stringMap x = Σ_{i ∈ supp x} F^{(i.2)} xᵢ`
  have hx' : ∑ i ∈ x.support, V.dF i.2 (x i : M) = 0 := by
    rw [← hx, stringMap, DirectSum.toModule, DFinsupp.lsum_apply_apply,
      DFinsupp.sumAddHom_apply]
    rfl
  -- each term vanishes
  have key : ∀ i ∈ x.support, V.dF i.2 (x i : M) = 0 := by
    intro i0 hi0
    obtain ⟨n, j0⟩ := i0
    -- project to `Mⁿ`
    have hproj := congrArg (V.wtProj n) hx'
    rw [map_sum, map_zero] at hproj
    have hterm : ∀ i ∈ x.support, V.wtProj n (V.dF i.2 (x i : M)) =
        if i.1 = n then V.dF i.2 (x i : M) else 0 := fun i _ ↦
      wtProj_of_mem (dF_mem_wt_of_mem_stringSummand (x i).2)
    rw [sum_congr rfl hterm, ← sum_filter] at hproj
    -- reindex the terms of weight `n` by `j`
    set s := x.support.filter fun i ↦ i.1 = n
    have hs : s = (s.image Prod.snd).image fun j ↦ (n, j) := by
      ext ⟨n', j⟩
      simp only [mem_image, Prod.exists, s, mem_filter, DFinsupp.mem_support_toFun]
      constructor
      · rintro ⟨h1, rfl⟩; exact ⟨j, ⟨n', j, ⟨h1, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨j', ⟨a, b, ⟨h1, rfl⟩, rfl⟩, h2⟩
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨h1, rfl⟩
    rw [hs, sum_image fun _ _ _ _ h ↦ by simpa using h] at hproj
    have := dF_eq_zero_of_sum_eq_zero hq0 hq (n := n) (η := fun j ↦ (x (n, j) : M))
      (fun j _ ↦ stringSummand_le (n, j) (x (n, j)).2) hproj j0
    exact this (mem_image.2 ⟨(n, j0), mem_filter.2 ⟨hi0, rfl⟩, rfl⟩)
  ext i
  by_cases hi : i ∈ x.support
  · exact eq_zero_of_dF_eq_zero_of_mem_stringSummand hq0 hq (x i).2 (key i hi)
  · simpa using hi

theorem stringMap_surjective : Function.Surjective V.stringMap := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← V.iSup_wt, iSup_le_iff]
  intro n m hm
  refine wt_induction (V := V) hq0 hq (P := fun m ↦ m ∈ LinearMap.range V.stringMap)
    (zero_mem _) (fun _ _ ↦ add_mem) (fun c _ ↦ Submodule.smul_mem _ c) ?_ hm
  intro p j η hjp hn hη hE
  have hmem : η ∈ V.stringSummand (n, j) := by
    rw [mem_stringSummand (by omega), show n + 2 * (j : ℤ) = p by omega]
    exact ⟨hη, hE⟩
  exact ⟨_, stringMap_lof (n, j) ⟨η, hmem⟩⟩

/-- The string decomposition `⨁_{(n, j)} prim (n + 2j) ≃ M`, `(ηₙⱼ) ↦ Σ F^{(j)} ηₙⱼ`
([HK] Lemma 4.1.1). -/
noncomputable def stringEquiv : (⨁ i : ℤ × ℕ, V.stringSummand i) ≃ₗ[k] M :=
  LinearEquiv.ofBijective V.stringMap ⟨stringMap_injective hq0 hq, stringMap_surjective hq0 hq⟩

lemma stringEquiv_symm_dF {n : ℤ} {j : ℕ} {η : M} (hη : η ∈ V.stringSummand (n, j)) :
    (stringEquiv hq0 hq).symm (V.dF j η) =
      DirectSum.lof k (ℤ × ℕ) (fun i ↦ V.stringSummand i) (n, j) ⟨η, hη⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  exact (stringMap_lof (n, j) ⟨η, hη⟩).symm

/-! ### The Kashiwara operators -/

variable (V) in
/-- The Kashiwara operator `ẽ` ([HK] Def. 4.1.2): `ẽ (Σⱼ F^{(j)} ηⱼ) = Σⱼ F^{(j-1)} ηⱼ`
(the term `j = 0` is dropped). -/
noncomputable def eTilde : Module.End k M :=
  DirectSum.toModule k (ℤ × ℕ) M
      (fun i ↦ (if i.2 = 0 then 0 else V.dF (i.2 - 1)) ∘ₗ (V.stringSummand i).subtype) ∘ₗ
    (stringEquiv hq0 hq).symm.toLinearMap

variable (V) in
/-- The Kashiwara operator `f̃` ([HK] Def. 4.1.2): `f̃ (Σⱼ F^{(j)} ηⱼ) = Σⱼ F^{(j+1)} ηⱼ`. -/
noncomputable def fTilde : Module.End k M :=
  DirectSum.toModule k (ℤ × ℕ) M
      (fun i ↦ V.dF (i.2 + 1) ∘ₗ (V.stringSummand i).subtype) ∘ₗ
    (stringEquiv hq0 hq).symm.toLinearMap

/-- `f̃ F^{(j)} η = F^{(j+1)} η` for every primitive `η`. -/
theorem fTilde_dF {p : ℤ} {η : M} (hη : V.E η = 0) (hp : η ∈ V.wt p) (j : ℕ) :
    V.fTilde hq0 hq (V.dF j η) = V.dF (j + 1) η := by
  by_cases hjp : (j : ℤ) ≤ p
  · have hmem : η ∈ V.stringSummand (p - 2 * j, j) := by
      rw [mem_stringSummand (by omega), show p - 2 * (j : ℤ) + 2 * j = p by ring]
      exact ⟨hp, hη⟩
    rw [fTilde, LinearMap.comp_apply, LinearEquiv.coe_coe, stringEquiv_symm_dF hq0 hq hmem,
      DirectSum.toModule_lof]
    rfl
  · rw [dF_eq_zero_of_primitive hq0 hq hp hη (by omega),
      dF_eq_zero_of_primitive hq0 hq hp hη (by push_cast; omega), map_zero]

/-- `ẽ F^{(j+1)} η = F^{(j)} η` for `η ∈ Mᵖ` primitive and `j < p`. -/
theorem eTilde_dF_succ {p : ℤ} {η : M} (hη : V.E η = 0) (hp : η ∈ V.wt p) {j : ℕ}
    (hj : (j : ℤ) < p) : V.eTilde hq0 hq (V.dF (j + 1) η) = V.dF j η := by
  have hmem : η ∈ V.stringSummand (p - 2 * (j + 1 : ℕ), j + 1) := by
    rw [mem_stringSummand (by push_cast; omega)]
    rw [show p - 2 * ((j + 1 : ℕ) : ℤ) + 2 * ((j + 1 : ℕ) : ℤ) = p by ring]
    exact ⟨hp, hη⟩
  rw [eTilde, LinearMap.comp_apply, LinearEquiv.coe_coe, stringEquiv_symm_dF hq0 hq hmem,
    DirectSum.toModule_lof]
  simp

/-- `ẽ η = 0` for `η` primitive. -/
theorem eTilde_of_primitive {p : ℤ} {η : M} (hη : V.E η = 0) (hp : η ∈ V.wt p) :
    V.eTilde hq0 hq η = 0 := by
  by_cases hp0 : 0 ≤ p
  · have hmem : η ∈ V.stringSummand (p, 0) := by
      rw [mem_stringSummand (by simpa using hp0)]
      simpa using (show η ∈ V.prim p from ⟨hp, hη⟩)
    have := stringEquiv_symm_dF hq0 hq hmem
    rw [dF_zero] at this
    rw [eTilde, LinearMap.comp_apply, LinearEquiv.coe_coe, this, DirectSum.toModule_lof]
    simp
  · rw [eq_zero_of_primitive_of_neg hq0 hq hp hη (by omega), map_zero]

/-- `ẽ F^{(p)} η`-free form: `ẽ F^{(j+1)} η = F^{(j)} η` whenever `F^{(j+1)} η ≠ 0`. -/
theorem eTilde_dF_succ' {p : ℤ} {η : M} (hη : V.E η = 0) (hp : η ∈ V.wt p) {j : ℕ}
    (h : V.dF (j + 1) η ≠ 0) : V.eTilde hq0 hq (V.dF (j + 1) η) = V.dF j η := by
  refine eTilde_dF_succ hq0 hq hη hp ?_
  by_contra hj
  exact h (dF_eq_zero_of_primitive hq0 hq hp hη (by push_cast; omega))

/-- `ẽ` maps `Mⁿ` to `M^{n+2}`. -/
theorem eTilde_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) : V.eTilde hq0 hq m ∈ V.wt (n + 2) := by
  refine wt_induction (V := V) hq0 hq (P := fun m ↦ V.eTilde hq0 hq m ∈ V.wt (n + 2))
    (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun c x hx ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_ hm
  intro p j η hjp hn hη hE
  rcases j with _ | j
  · rw [dF_zero, eTilde_of_primitive hq0 hq hE hη]
    exact zero_mem _
  · rw [eTilde_dF_succ hq0 hq hE hη (by omega)]
    have := dF_mem hη j
    convert this using 2
    push_cast at hn ⊢
    omega

/-- `f̃` maps `Mⁿ` to `M^{n-2}`. -/
theorem fTilde_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) : V.fTilde hq0 hq m ∈ V.wt (n - 2) := by
  refine wt_induction (V := V) hq0 hq (P := fun m ↦ V.fTilde hq0 hq m ∈ V.wt (n - 2))
    (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun c x hx ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_ hm
  intro p j η hjp hn hη hE
  rw [fTilde_dF hq0 hq hE hη]
  have := dF_mem hη (j + 1)
  convert this using 2
  push_cast
  omega

/-- `ẽ f̃ F^{(j)} η = F^{(j)} η` for `η ∈ Mᵖ` primitive and `j < p`. -/
theorem eTilde_fTilde_dF {p : ℤ} {η : M} (hη : V.E η = 0) (hp : η ∈ V.wt p) {j : ℕ}
    (hj : (j : ℤ) < p) : V.eTilde hq0 hq (V.fTilde hq0 hq (V.dF j η)) = V.dF j η := by
  rw [fTilde_dF hq0 hq hη hp, eTilde_dF_succ hq0 hq hη hp hj]

/-- `f̃ ẽ F^{(j+1)} η = F^{(j+1)} η` for every primitive `η`. -/
theorem fTilde_eTilde_dF_succ {p : ℤ} {η : M} (hη : V.E η = 0) (hp : η ∈ V.wt p) (j : ℕ) :
    V.fTilde hq0 hq (V.eTilde hq0 hq (V.dF (j + 1) η)) = V.dF (j + 1) η := by
  by_cases hj : (j : ℤ) < p
  · rw [eTilde_dF_succ hq0 hq hη hp hj, fTilde_dF hq0 hq hη hp]
  · rw [dF_eq_zero_of_primitive hq0 hq hp hη (by push_cast; omega), map_zero, map_zero]

/-! ### Naturality -/

omit hq0 hq in
lemma map_dF {M' : Type*} [AddCommGroup M'] [Module k M'] {V' : IntegrableSl2 q M'}
    {f : M →ₗ[k] M'} (hF : ∀ m, f (V.F m) = V'.F (f m)) (a : ℕ) (m : M) :
    f (V.dF a m) = V'.dF a (f m) := by
  have hpow : ∀ (a : ℕ) m, f ((V.F ^ a) m) = (V'.F ^ a) (f m) := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => intro m; rw [pow_succ', pow_succ', Module.End.mul_apply,
        Module.End.mul_apply, hF, ih]
  rw [dF_apply, dF_apply, map_smul, hpow]

/-- The Kashiwara operator `ẽ` commutes with linear maps commuting with `E`, `F` and preserving
the gradings ([HK] Prop. 4.1.3 (2)). -/
theorem map_eTilde {M' : Type*} [AddCommGroup M'] [Module k M'] (V' : IntegrableSl2 q M')
    (f : M →ₗ[k] M') (hE : ∀ m, f (V.E m) = V'.E (f m)) (hF : ∀ m, f (V.F m) = V'.F (f m))
    (hwt : ∀ n, ∀ m ∈ V.wt n, f m ∈ V'.wt n) (m : M) :
    f (V.eTilde hq0 hq m) = V'.eTilde hq0 hq (f m) := by
  have key : ∀ n, ∀ m ∈ V.wt n, f (V.eTilde hq0 hq m) = V'.eTilde hq0 hq (f m) := by
    intro n m hm
    refine eq_on_wt (V := V) hq0 hq (f ∘ₗ V.eTilde hq0 hq) (V'.eTilde hq0 hq ∘ₗ f) ?_ hm
    intro p j η hjp _ hη hEη
    have hη' : f η ∈ V'.wt p := hwt p η hη
    have hEη' : V'.E (f η) = 0 := by rw [← hE, hEη, map_zero]
    simp only [LinearMap.comp_apply]
    rw [map_dF hF]
    rcases j with _ | j
    · rw [dF_zero, dF_zero, eTilde_of_primitive hq0 hq hEη hη,
        eTilde_of_primitive hq0 hq hEη' hη', map_zero]
    · rw [eTilde_dF_succ hq0 hq hEη hη (by omega), eTilde_dF_succ hq0 hq hEη' hη' (by omega),
        map_dF hF]
  exact LinearMap.congr_fun
    (V.ext_wt (f := f ∘ₗ V.eTilde hq0 hq) (g := V'.eTilde hq0 hq ∘ₗ f) key) m

/-- The Kashiwara operator `f̃` commutes with linear maps commuting with `E`, `F` and preserving
the gradings ([HK] Prop. 4.1.3 (2)). -/
theorem map_fTilde {M' : Type*} [AddCommGroup M'] [Module k M'] (V' : IntegrableSl2 q M')
    (f : M →ₗ[k] M') (hE : ∀ m, f (V.E m) = V'.E (f m)) (hF : ∀ m, f (V.F m) = V'.F (f m))
    (hwt : ∀ n, ∀ m ∈ V.wt n, f m ∈ V'.wt n) (m : M) :
    f (V.fTilde hq0 hq m) = V'.fTilde hq0 hq (f m) := by
  have key : ∀ n, ∀ m ∈ V.wt n, f (V.fTilde hq0 hq m) = V'.fTilde hq0 hq (f m) := by
    intro n m hm
    refine eq_on_wt (V := V) hq0 hq (f ∘ₗ V.fTilde hq0 hq) (V'.fTilde hq0 hq ∘ₗ f) ?_ hm
    intro p j η hjp _ hη hEη
    have hη' : f η ∈ V'.wt p := hwt p η hη
    have hEη' : V'.E (f η) = 0 := by rw [← hE, hEη, map_zero]
    simp only [LinearMap.comp_apply]
    rw [map_dF hF, fTilde_dF hq0 hq hEη hη, fTilde_dF hq0 hq hEη' hη', map_dF hF]
  exact LinearMap.congr_fun
    (V.ext_wt (f := f ∘ₗ V.fTilde hq0 hq) (g := V'.fTilde hq0 hq ∘ₗ f) key) m

/-! ### Interchanging `E` and `F` -/

/-- For the module with `E` and `F` interchanged, `ẽ` is `f̃`: the `j`-th vector of a string of
length `p + 1` counted from the top is the `(p - j)`-th counted from the bottom. -/
theorem flip_eTilde : V.flip.eTilde hq0 hq = V.fTilde hq0 hq := by
  refine V.ext_wt fun n m hm ↦ eq_on_wt (V := V) hq0 hq _ _ ?_ hm
  intro p j η hjp _ hη hEη
  obtain ⟨hξ, hEξ⟩ := flip_primitive hq0 hq hη hEη
  rw [fTilde_dF hq0 hq hEη hη, dF_eq_flip_dF hq0 hq hη hEη hjp]
  rcases Nat.lt_or_ge j p with hjp' | hjp'
  · rw [show p - j = (p - (j + 1)) + 1 by omega, eTilde_dF_succ hq0 hq hEξ hξ (by omega),
      dF_eq_flip_dF hq0 hq hη hEη (show j + 1 ≤ p by omega)]
  · obtain rfl : j = p := le_antisymm hjp hjp'
    rw [Nat.sub_self, dF_zero, eTilde_of_primitive hq0 hq hEξ hξ,
      dF_eq_zero_of_primitive hq0 hq hη hEη (by push_cast; omega)]

/-- For the module with `E` and `F` interchanged, `f̃` is `ẽ`. -/
theorem flip_fTilde : V.flip.fTilde hq0 hq = V.eTilde hq0 hq := by
  have := flip_eTilde hq0 hq (V := V.flip)
  rw [flip_flip] at this
  exact this.symm

/-! ### Comparison with `E` and `F` -/

/-- Every `m ∈ Mⁿ` is a finite sum `Σ_{j<N} F^{(j)} ηⱼ` with `ηⱼ ∈ M^{n+2j}` primitive and
`ηⱼ = 0` unless `n + j ≥ 0` ([HK] Lemma 4.1.1, existence). -/
theorem exists_sum_dF {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    ∃ (N : ℕ) (η : ℕ → M), (∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) ∧ (∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) ∧
      (∀ j, N ≤ j → η j = 0) ∧ m = ∑ j ∈ range N, V.dF j (η j) := by
  classical
  refine wt_induction (V := V) hq0 hq (P := fun m ↦ ∃ (N : ℕ) (η : ℕ → M),
      (∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) ∧ (∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) ∧
      (∀ j, N ≤ j → η j = 0) ∧ m = ∑ j ∈ range N, V.dF j (η j)) ?_ ?_ ?_ ?_ hm
  · exact ⟨0, 0, fun _ ↦ zero_mem _, fun _ h ↦ absurd rfl h, fun _ _ ↦ rfl, by simp⟩
  · rintro x y ⟨N₁, η₁, h₁, h₁', h₁'', rfl⟩ ⟨N₂, η₂, h₂, h₂', h₂'', rfl⟩
    refine ⟨max N₁ N₂, η₁ + η₂, fun j ↦ add_mem (h₁ j) (h₂ j), fun j hj ↦ ?_,
      fun j hj ↦ by simp [h₁'' j (le_of_max_le_left hj), h₂'' j (le_of_max_le_right hj)], ?_⟩
    · by_cases h : η₁ j = 0
      · exact h₂' j (by simpa [h] using hj)
      · exact h₁' j h
    · have e : ∀ (η : ℕ → M) (N : ℕ), (∀ j, N ≤ j → η j = 0) → ∀ N', N ≤ N' →
          ∑ j ∈ range N, V.dF j (η j) = ∑ j ∈ range N', V.dF j (η j) := by
        intro η N hη N' hN
        refine sum_subset (range_subset_range.2 hN) fun j _ hj ↦ ?_
        rw [hη j (by simpa using hj), map_zero]
      rw [e η₁ N₁ h₁'' _ (le_max_left _ _), e η₂ N₂ h₂'' _ (le_max_right _ _), ← sum_add_distrib]
      simp [map_add]
  · rintro c x ⟨N, η, h, h', h'', rfl⟩
    refine ⟨N, c • η, fun j ↦ Submodule.smul_mem _ c (h j), fun j hj ↦ h' j fun h0 ↦ ?_,
      fun j hj ↦ by simp [h'' j hj], ?_⟩
    · exact hj (by simp [h0])
    · rw [smul_sum]
      simp [map_smul]
  · intro p j η hjp hn hη hE
    refine ⟨j + 1, Pi.single j η, fun i ↦ ?_, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | hij
      · rw [Pi.single_eq_same, show n + 2 * (i : ℤ) = p by omega]
        exact ⟨hη, hE⟩
      · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
    · rcases eq_or_ne i j with rfl | hij
      · omega
      · simp [Pi.single_eq_of_ne hij] at hi
    · rw [Pi.single_eq_of_ne (by omega)]
    · rw [sum_eq_single_of_mem j (mem_range.2 (Nat.lt_succ_self j)) fun i _ hij ↦ by
        rw [Pi.single_eq_of_ne hij, map_zero], Pi.single_eq_same]

/-- `ẽ m = 0` if and only if `E m = 0`, for `m ∈ Mⁿ`. -/
theorem eTilde_eq_zero_iff {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    V.eTilde hq0 hq m = 0 ↔ V.E m = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ eTilde_of_primitive hq0 hq h hm⟩
  obtain ⟨N, η, h1, h2, -, rfl⟩ := exists_sum_dF hq0 hq hm
  rcases N with _ | N
  · simp
  rw [map_sum, sum_range_succ', dF_zero, eTilde_of_primitive hq0 hq (h1 0).2 (h1 0).1,
    add_zero] at h
  have he : ∀ j, V.eTilde hq0 hq (V.dF (j + 1) (η (j + 1))) = V.dF j (η (j + 1)) := by
    intro j
    by_cases h0 : η (j + 1) = 0
    · simp [h0]
    · have := h2 _ h0
      exact eTilde_dF_succ hq0 hq (h1 (j + 1)).2 (h1 (j + 1)).1 (by push_cast at this ⊢; omega)
  simp only [he] at h
  have hη : ∀ j : ℕ, η (j + 1) ∈ V.prim (n + 2 + 2 * j) := fun j ↦ by
    convert h1 (j + 1) using 2; push_cast; ring
  have hz := dF_eq_zero_of_sum_range_eq_zero hq0 hq N (n + 2) (fun j ↦ η (j + 1)) hη h
  rw [map_sum, sum_range_succ', dF_zero, (h1 0).2, add_zero]
  refine sum_eq_zero fun j hj ↦ ?_
  rw [E_dF_of_prim hq0 hq (h1 (j + 1)) j, hz j (mem_range.1 hj), smul_zero]

end IntegrableSl2

end LieLean.QuantumGroup
