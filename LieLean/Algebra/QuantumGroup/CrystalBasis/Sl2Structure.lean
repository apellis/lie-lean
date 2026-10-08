/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Sl2
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The structure of crystal bases of integrable `U_q(𝔰𝔩₂)`-modules

Let `(L, B)` be a crystal base of an integrable `U_q(𝔰𝔩₂)`-module `M`
(`QuantumGroup.IntegrableSl2.IsCrystalBase`). Every `b ∈ B` with `ẽ b = 0` is the class of a
primitive vector `η_b ∈ L` (`QuantumGroup.IntegrableSl2.IsCrystalBase.exists_highest_lift`), and
every element of `B` is `f̃ʲ b` for a unique such `b` and `j ≤ ⟨wt b⟩`
(`QuantumGroup.IntegrableSl2.IsCrystalBase.exists_strCls_eq`).

If `A` is a local ring with fraction field `k`, `c` is a non-unit and `M` is finite-dimensional,
then `L` is the `A`-span of the strings `F^{(j)} η_b` and the `η_b` form a string basis of `M`
(`QuantumGroup.IntegrableSl2.IsCrystalBase.eq_stringLattice`): every crystal base is of the form
`QuantumGroup.IntegrableSl2.isCrystalBase_stringLattice` ([HK] Thm. 4.3.2, uniqueness of crystal
bases of finite-dimensional `U_q(𝔰𝔩₂)`-modules; our proof via Nakayama's lemma).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.3.
-/

open Finset Pointwise

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M} {c : A} {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}

namespace IsCrystalBase

variable (hB : V.IsCrystalBase hq0 hq L c B) (hc : ¬IsUnit c)
include hB

lemma zero_notMem (hc : ¬IsUnit c) : (0 : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) ∉ B := by
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  intro h0
  exact hB.linearIndependent.ne_zero ⟨0, h0⟩ rfl

/-- The vectors `F^{(j)} η`, `j ≤ p`, of a primitive `η ∈ L` with nonzero class are nonzero
modulo `c L`. -/
lemma dF_notMem_smul {p : ℕ} {η : M} (hη : η ∈ V.prim p) (hηc : η ∉ c • L) {j : ℕ}
    (hj : j ≤ p) : V.dF j η ∉ c • L := by
  intro h
  have := LinearMap.map_mem_smul_of_mem (f := V.eTilde hq0 hq ^ j) c
    (pow_apply_mem hB.isKashiwaraStable.eTilde_mem j) h
  rw [eTilde_pow_dF hq0 hq hη le_rfl (by exact_mod_cast hj), Nat.sub_self, dF_zero] at this
  exact hηc this

include hc in
/-- Every element of `B` is the class of `F^{(k)} η` for a primitive `η ∈ L` with `[η] ∈ B`
(from [HK] Prop. 4.2.11 (3)). -/
lemma exists_string_lift (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) (hb : b ∈ B) :
    ∃ (p k : ℕ) (η : M) (hηL : η ∈ L), η ∈ V.prim p ∧ k ≤ p ∧
      Submodule.Quotient.mk ⟨η, hηL⟩ ∈ B ∧
      ∃ hx : V.dF k η ∈ L, b = Submodule.Quotient.mk ⟨V.dF k η, hx⟩ := by
  obtain ⟨n, x, hx, rfl⟩ := hB.exists_wt b hb
  obtain ⟨N, η, h1, h2, -, hxη⟩ := exists_sum_dF hq0 hq hx
  have hu : ∑ j ∈ range N, V.dF j (η j) ∈ L := hxη ▸ x.2
  have hxB : Submodule.Quotient.mk ⟨_, hu⟩ ∈ B := by
    convert hb using 2; exact Subtype.ext hxη.symm
  obtain ⟨k, -, hkL, hkB, -, hmod⟩ := hB.isKashiwaraStable.exists_of_mk_mem c B
    (hB.zero_notMem hc) hB.eQ_mem hB.fQ_eq_iff N n η h1 h2 hu hxB
  have hη0 : η k ≠ 0 := by
    rintro h
    apply hB.zero_notMem hc
    have : (⟨η k, hkL⟩ : L) = 0 := Subtype.ext h
    rw [this, Submodule.Quotient.mk_zero] at hkB
    exact hkB
  have hnk := h2 k hη0
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * k := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  have hηp : η k ∈ V.prim p := hp ▸ h1 k
  refine ⟨p, k, η k, hkL, hηp, by omega, hkB,
    hB.isKashiwaraStable.dF_mem hηp hkL k, ?_⟩
  rw [mk_eq_mk_iff]
  rw [← hxη] at hmod
  exact hmod

include hc in
/-- An element `b ∈ B` with `ẽ b = 0` is the class of a primitive vector of `L`. -/
lemma exists_highest_lift (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) (hb : b ∈ B)
    (he : V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c b = 0) :
    ∃ (p : ℕ) (η : M) (hηL : η ∈ L), η ∈ V.prim p ∧ b = Submodule.Quotient.mk ⟨η, hηL⟩ := by
  obtain ⟨p, k, η, hηL, hηp, hkp, hηB, hx, rfl⟩ := hB.exists_string_lift hc b hb
  have hηc : η ∉ c • L := fun h ↦ hB.zero_notMem hc (by
    rwa [(mk_eq_zero_iff c ⟨η, hηL⟩).2 h] at hηB)
  rcases k with _ | k
  · exact ⟨p, η, hηL, hηp, by simp⟩
  · exfalso
    rw [eTildeQ_mk, mk_eq_zero_iff] at he
    have e := eTilde_dF_succ (j := k) (p := (p : ℤ)) hq0 hq hηp.2 hηp.1 (by omega)
    change V.eTilde hq0 hq (V.dF (k + 1) η) ∈ c • L at he
    rw [e] at he
    exact hB.dF_notMem_smul hηp hηc (by omega) he

/-! ### Strings of `B` -/

/-- `ẽ f̃ b = b` if `f̃ b ≠ 0`. -/
lemma eQ_fQ (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) (hb : b ∈ B)
    (hf : V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c b ≠ 0) :
    V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c
      (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c b) = b :=
  (hB.fQ_eq_iff b hb _ ((hB.fQ_mem b hb).resolve_right hf)).1 rfl

/-- `f̃ʲ b ∈ B` if it is nonzero. -/
lemma fQ_pow_mem (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) (hb : b ∈ B) (j : ℕ)
    (hj : (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j) b ≠ 0) :
    (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j) b ∈ B := by
  induction j with
  | zero => simpa using hb
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply] at hj ⊢
    have h0 : (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j) b ≠ 0 := by
      intro h; rw [h, map_zero] at hj; exact hj rfl
    exact (hB.fQ_mem _ (ih h0)).resolve_right hj

/-- `ẽᵃ f̃^{a+r} b = f̃ʳ b` if `f̃^{a+r} b ≠ 0`. -/
lemma eQ_pow_fQ_pow (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) (hb : b ∈ B) (a r : ℕ)
    (h : (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ (a + r)) b ≠ 0) :
    (V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c ^ a)
      ((V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ (a + r)) b) =
      (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ r) b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + r = (a + r) + 1 by omega] at h ⊢
    rw [pow_succ' (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c), Module.End.mul_apply]
      at h ⊢
    have h0 : (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ (a + r)) b ≠ 0 := by
      intro h'; rw [h', map_zero] at h; exact h rfl
    rw [pow_succ, Module.End.mul_apply, hB.eQ_fQ _ (hB.fQ_pow_mem b hb _ h0) h, ih h0]

/-- Two nonzero classes of weight vectors which are equal have equal weights. -/
lemma wt_eq_of_mk_eq (hc : ¬IsUnit c) {x y : M} (hx : x ∈ L) (hy : y ∈ L) {n n' : ℤ}
    (hxn : x ∈ V.wt n) (hyn : y ∈ V.wt n') (hxB : Submodule.Quotient.mk ⟨x, hx⟩ ∈ B)
    (hxy : (Submodule.Quotient.mk ⟨x, hx⟩ : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
      Submodule.Quotient.mk ⟨y, hy⟩) : n = n' := by
  by_contra hne
  have h := (mk_eq_mk_iff c _ _).1 hxy
  have h' := LinearMap.map_mem_smul_of_mem (f := V.wtProj n) c
    (fun m hm ↦ hB.isKashiwaraStable.wtProj_mem m hm n) h
  simp only at h'
  simp only [map_sub, wtProj_of_mem hxn, wtProj_of_mem hyn, ↓reduceIte, Ne.symm hne,
    sub_zero] at h'
  exact hB.zero_notMem hc (by rwa [(mk_eq_zero_iff c ⟨x, hx⟩).2 h'] at hxB)

/-- The elements of `B` killed by `ẽ`. -/
def highest : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :=
  {b | b ∈ B ∧ V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c b = 0}

/-- The weight of a highest element. -/
noncomputable def hwt (h : hB.highest) : ℕ :=
  Classical.choose (hB.exists_highest_lift hc h.1 h.2.1 h.2.2)

/-- A primitive lift of a highest element. -/
noncomputable def hvec (h : hB.highest) : M :=
  Classical.choose (Classical.choose_spec (hB.exists_highest_lift hc h.1 h.2.1 h.2.2))

lemma hvec_spec (h : hB.highest) : ∃ hηL : hB.hvec hc h ∈ L,
    hB.hvec hc h ∈ V.prim (hB.hwt hc h) ∧ h.1 = Submodule.Quotient.mk ⟨_, hηL⟩ := by
  obtain ⟨hηL, hp, he⟩ :=
    Classical.choose_spec (Classical.choose_spec (hB.exists_highest_lift hc h.1 h.2.1 h.2.2))
  exact ⟨hηL, hp, he⟩

lemma hvec_mem (h : hB.highest) : hB.hvec hc h ∈ L := (hB.hvec_spec hc h).1

lemma hvec_prim (h : hB.highest) : hB.hvec hc h ∈ V.prim (hB.hwt hc h) :=
  (hB.hvec_spec hc h).2.1

lemma mk_hvec (h : hB.highest) :
    (Submodule.Quotient.mk ⟨_, hB.hvec_mem hc h⟩ : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
      h.1 :=
  (hB.hvec_spec hc h).2.2.symm

lemma hvec_notMem (h : hB.highest) : hB.hvec hc h ∉ c • L := fun h' ↦ by
  have := hB.mk_hvec hc h
  rw [(mk_eq_zero_iff c _).2 h'] at this
  exact hB.zero_notMem hc (this ▸ h.2.1)

lemma fQ_pow_highest (h : hB.highest) (j : ℕ) :
    (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j) h.1 =
      Submodule.Quotient.mk ⟨V.dF j (hB.hvec hc h),
        hB.isKashiwaraStable.dF_mem (hB.hvec_prim hc h) (hB.hvec_mem hc h) j⟩ := by
  rw [← hB.mk_hvec hc h, fTildeQ_pow_mk]
  congr 2
  exact fTilde_pow_apply hq0 hq (hB.hvec_prim hc h) j

/-- The class `f̃ʲ h` of `F^{(j)} η_h`. -/
noncomputable def strCls (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) :
    L ⧸ (Ideal.span {c} • ⊤ : Submodule A L) :=
  (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ (x.2 : ℕ)) x.1.1

lemma strCls_ne_zero (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) : hB.strCls hc x ≠ 0 := by
  rw [strCls, fQ_pow_highest, Ne, mk_eq_zero_iff]
  exact hB.dF_notMem_smul (hB.hvec_prim hc x.1) (hB.hvec_notMem hc x.1)
    (Nat.lt_succ_iff.1 x.2.2)

lemma strCls_mem (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) : hB.strCls hc x ∈ B :=
  hB.fQ_pow_mem _ x.1.2.1 _ (hB.strCls_ne_zero hc x)

lemma strCls_injective : Function.Injective (hB.strCls hc) := by
  rintro ⟨h, j, hj⟩ ⟨h', j', hj'⟩ he
  simp only [strCls] at he
  have key : ∀ (h h' : hB.highest) (j r : ℕ),
      (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j) h.1 ≠ 0 →
      (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j) h.1 =
        (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ (j + r)) h'.1 → h = h' ∧ r = 0 := by
    intro h h' j r hne he
    have e1 := hB.eQ_pow_fQ_pow h.1 h.2.1 j 0 (by simpa using hne)
    have e2 := hB.eQ_pow_fQ_pow h'.1 h'.2.1 j r (he ▸ hne)
    simp only [add_zero, pow_zero, Module.End.one_apply] at e1
    rw [he, e2] at e1
    -- `h = f̃ʳ h'`
    rcases r with _ | r
    · simp only [pow_zero, Module.End.one_apply] at e1
      exact ⟨Subtype.ext e1.symm, rfl⟩
    · exfalso
      have hne' : (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ (1 + r)) h'.1 ≠ 0 := by
        rw [add_comm, e1]; intro h0; rw [← h0] at hne; exact hne (by simp [h0] at *)
      have e3 := hB.eQ_pow_fQ_pow h'.1 h'.2.1 1 r hne'
      rw [pow_one, show 1 + r = r + 1 by omega, e1] at e3
      have := h.2.2
      rw [e3] at this
      have hr : (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ r) h'.1 ≠ 0 := by
        intro h0
        rw [show 1 + r = r + 1 by omega, pow_succ', Module.End.mul_apply, h0, map_zero] at hne'
        exact hne' rfl
      exact hr this
  rcases le_total j j' with hjj | hjj
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hjj
    obtain ⟨rfl, rfl⟩ := key h h' j r (by
      have := hB.strCls_ne_zero hc ⟨h, j, hj⟩; simpa [strCls] using this) he
    rfl
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hjj
    obtain ⟨rfl, rfl⟩ := key h' h j' r (by
      have := hB.strCls_ne_zero hc ⟨h', j', hj'⟩; simpa [strCls] using this) he.symm
    rfl

/-- Every element of `B` is `f̃ʲ h` for a highest `h` and `j ≤ ⟨wt h⟩`. -/
lemma exists_strCls_eq (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) (hb : b ∈ B) :
    ∃ x, hB.strCls hc x = b := by
  obtain ⟨p, k, η, hηL, hηp, hkp, hηB, hx, rfl⟩ := hB.exists_string_lift hc b hb
  have hhigh : Submodule.Quotient.mk ⟨η, hηL⟩ ∈ hB.highest := by
    refine ⟨hηB, ?_⟩
    rw [eTildeQ_mk, mk_eq_zero_iff]
    simp only [eTilde_of_primitive hq0 hq hηp.2 hηp.1]
    exact zero_mem _
  set h : hB.highest := ⟨_, hhigh⟩
  have hwt : hB.hwt hc h = p := by
    have := hB.wt_eq_of_mk_eq hc (hB.hvec_mem hc h) hηL (hB.hvec_prim hc h).1 hηp.1
      ((hB.mk_hvec hc h) ▸ hηB) (hB.mk_hvec hc h)
    exact_mod_cast this
  refine ⟨⟨h, ⟨k, by omega⟩⟩, ?_⟩
  simp only [strCls, h, fTildeQ_pow_mk]
  congr 2
  exact fTilde_pow_apply hq0 hq hηp k

lemma strCls_eq (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) :
    hB.strCls hc x = Submodule.Quotient.mk ⟨V.dF x.2 (hB.hvec hc x.1),
      hB.isKashiwaraStable.dF_mem (hB.hvec_prim hc x.1) (hB.hvec_mem hc x.1) _⟩ :=
  hB.fQ_pow_highest hc x.1 x.2

lemma range_strCls : Set.range (hB.strCls hc) = B := by
  ext b
  exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ hB.strCls_mem hc x, fun hb ↦ hB.exists_strCls_eq hc b hb⟩

/-! ### Finite-dimensional modules -/

/-- `ẽᵃ (f̃ʲ h) = 0` iff `a > j`: the element `f̃ʲ h` has `ε = j`. -/
lemma eQ_pow_strCls_eq_zero_iff (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) (a : ℕ) :
    (V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c ^ a) (hB.strCls hc x) = 0 ↔
      (x.2 : ℕ) < a := by
  obtain ⟨h, j, hj⟩ := x
  have hne : ∀ j' (hj' : j' < hB.hwt hc h + 1),
      (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j') h.1 ≠ 0 :=
    fun j' hj' ↦ hB.strCls_ne_zero hc ⟨h, j', hj'⟩
  simp only [strCls]
  constructor
  · intro h0
    by_contra hlt
    push Not at hlt
    have e := hB.eQ_pow_fQ_pow h.1 h.2.1 a (j - a) (by rw [Nat.add_sub_cancel' hlt]; exact hne j hj)
    rw [Nat.add_sub_cancel' hlt] at e
    rw [e] at h0
    exact hne (j - a) (by omega) h0
  · intro hlt
    have e1 : (V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c ^ j)
        ((V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ j) h.1) = h.1 := by
      simpa using hB.eQ_pow_fQ_pow h.1 h.2.1 j 0 (by simpa using hne j hj)
    rw [show a = (a - j - 1) + 1 + j by omega, pow_add, Module.End.mul_apply, e1, pow_succ,
      Module.End.mul_apply, h.2.2, map_zero]

/-- `f̃ᵃ (f̃ʲ h) = 0` iff `j + a > ⟨wt h⟩`: the element `f̃ʲ h` has `φ = ⟨wt h⟩ - j`. -/
lemma fQ_pow_strCls_eq_zero_iff (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) (a : ℕ) :
    (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ a) (hB.strCls hc x) = 0 ↔
      hB.hwt hc x.1 < x.2 + a := by
  obtain ⟨h, j, hj⟩ := x
  simp only [strCls]
  rw [← Module.End.mul_apply, ← pow_add, hB.fQ_pow_highest hc h, mk_eq_zero_iff]
  constructor
  · intro h0
    by_contra hlt
    push Not at hlt
    exact hB.dF_notMem_smul (hB.hvec_prim hc h) (hB.hvec_notMem hc h) (by omega) h0
  · intro hlt
    change V.dF (a + j) (hB.hvec hc h) ∈ c • L
    rw [dF_eq_zero_of_primitive hq0 hq (hB.hvec_prim hc h).1 (hB.hvec_prim hc h).2
      (by push_cast; omega)]
    exact zero_mem _

/-- The string vectors `F^{(j)} η_h` of a crystal base. -/
noncomputable def strVec (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) : M :=
  V.dF x.2 (hB.hvec hc x.1)

lemma strVec_mem (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) : hB.strVec hc x ∈ L :=
  hB.isKashiwaraStable.dF_mem (hB.hvec_prim hc x.1) (hB.hvec_mem hc x.1) _

section FiniteDimensional

variable [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M]

omit [IsLocalRing A] in
lemma moduleFinite : Module.Finite A L := by
  have : Module.Free A L := hB.free
  let bL := Module.Free.chooseBasis A L
  have hli : LinearIndependent k (fun i ↦ (bL i : M)) :=
    (LinearIndependent.iff_fractionRing A k).1 (bL.linearIndependent.map' L.subtype L.ker_subtype)
  have : Finite (Module.Free.ChooseBasisIndex A L) := hli.finite
  exact Module.Finite.of_basis bL

omit [IsLocalRing A] in
lemma finite_index : Finite (Σ h : hB.highest, Fin (hB.hwt hc h + 1)) := by
  have : Module.Finite A L := hB.moduleFinite
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hBfin : Finite B := hB.linearIndependent.finite
  exact Finite.of_injective (fun x ↦ (⟨hB.strCls hc x, hB.strCls_mem hc x⟩ : B))
    (fun x y h ↦ hB.strCls_injective hc (congrArg Subtype.val h))

/-- `L` is spanned by the string vectors (Nakayama's lemma). -/
lemma le_span_strVec : L ≤ Submodule.span A (Set.range (hB.strVec hc)) := by
  classical
  have : Module.Finite A L := hB.moduleFinite
  have := hB.finite_index hc
  have : Fintype (Σ h : hB.highest, Fin (hB.hwt hc h + 1)) := Fintype.ofFinite _
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {c})
    (Module.Finite.iff_fg.1 inferInstance)
    ((Ideal.span_le.2 (by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hc)).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)) ?_
  intro x hx
  -- the class of `x` is a combination of the classes of the string vectors
  have hmk : Submodule.Quotient.mk (⟨x, hx⟩ : L) ∈ Submodule.span (A ⧸ Ideal.span {c})
      (Set.range (hB.strCls hc)) := by
    rw [hB.range_strCls hc, hB.span_quot_eq_top]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmk
  choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := Ideal.span {c}) (g i)
  have hsum : ∑ i, a i • hB.strVec hc i ∈ Submodule.span A (Set.range (hB.strVec hc)) :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdiff : x - ∑ i, a i • hB.strVec hc i ∈ Ideal.span {c} • L := by
    rw [Submodule.ideal_span_singleton_smul]
    have hmem : ∑ i, a i • hB.strVec hc i ∈ L :=
      Submodule.sum_mem _ fun i _ ↦ L.smul_mem _ (hB.strVec_mem hc i)
    refine (mk_eq_mk_iff c ⟨x, hx⟩ ⟨_, hmem⟩).1 ?_
    rw [← hg]
    simp only [← ha, strCls_eq, Module.Quotient.mk_smul_mk]
    have := map_sum (Submodule.mkQ (Ideal.span {c} • (⊤ : Submodule A L)))
      (fun i ↦ a i • (⟨hB.strVec hc i, hB.strVec_mem hc i⟩ : L)) Finset.univ
    simp only [Submodule.mkQ_apply, strVec] at this
    rw [← this]
    congr 1
    exact Subtype.ext (by simp [strVec])
  have := Submodule.add_mem_sup hsum hdiff
  simpa using this

lemma span_strVec : Submodule.span A (Set.range (hB.strVec hc)) = L :=
  le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hB.strVec_mem hc i))
    (hB.le_span_strVec hc)

lemma card_index_le_finrank [Fintype (Σ h : hB.highest, Fin (hB.hwt hc h + 1))] :
    Fintype.card (Σ h : hB.highest, Fin (hB.hwt hc h + 1)) ≤ Module.finrank A L := by
  classical
  have : Module.Finite A L := hB.moduleFinite
  have : Module.Free A L := hB.free
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  let b := Module.Free.chooseBasis A L
  let w : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :=
    Submodule.mkQ _ '' Set.range b
  have hA : Submodule.span A w = ⊤ := by
    rw [Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
  have hw : Submodule.span (A ⧸ Ideal.span {c}) w = ⊤ :=
    eq_top_iff.2 fun y _ ↦ Submodule.span_le_restrictScalars A (A ⧸ Ideal.span {c}) w
      (hA ▸ Submodule.mem_top)
  have h1 := linearIndependent_le_span _ hB.linearIndependent w hw
  have h2 : Fintype.card w ≤ Fintype.card (Module.Free.ChooseBasisIndex A L) :=
    Fintype.card_le_of_surjective (fun i ↦ ⟨Submodule.mkQ _ (b i), b i, ⟨i, rfl⟩, rfl⟩)
      (by rintro ⟨_, _, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩)
  have h3 : Cardinal.mk (Σ h : hB.highest, Fin (hB.hwt hc h + 1)) ≤ Cardinal.mk B :=
    Cardinal.mk_le_of_injective (f := fun x ↦ (⟨hB.strCls hc x, hB.strCls_mem hc x⟩ : B))
      (fun x y h ↦ hB.strCls_injective hc (congrArg Subtype.val h))
  rw [Module.finrank_eq_card_chooseBasisIndex]
  have := h3.trans h1
  rw [Cardinal.mk_fintype, Nat.cast_le] at this
  omega

/-- The string vectors of a crystal base are linearly independent over `k`. -/
theorem linearIndependent_strVec : LinearIndependent k (hB.strVec hc) := by
  classical
  have := hB.finite_index hc
  have : Fintype (Σ h : hB.highest, Fin (hB.hwt hc h + 1)) := Fintype.ofFinite _
  let v : (Σ h : hB.highest, Fin (hB.hwt hc h + 1)) → L := fun i ↦ ⟨_, hB.strVec_mem hc i⟩
  have hv : LinearIndependent A v := by
    refine linearIndependent_of_top_le_span_of_card_le_finrank (fun x _ ↦ ?_)
      (hB.card_index_le_finrank hc)
    have hx : (x : M) ∈ Submodule.map L.subtype (Submodule.span A (Set.range v)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact hB.le_span_strVec hc x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy
  exact (LinearIndependent.iff_fractionRing A k).1 (hv.map' L.subtype L.ker_subtype)

lemma span_k_strVec : Submodule.span k (Set.range (hB.strVec hc)) = ⊤ := by
  rw [eq_top_iff, ← hB.span_eq_top, Submodule.span_le]
  intro x hx
  exact Submodule.span_le_restrictScalars A k _ (hB.le_span_strVec hc hx)

/-- The highest vectors of a given weight span the primitive vectors of that weight. -/
theorem prim_le_span (p₀ : ℕ) : V.prim p₀ ≤
    Submodule.span k (Set.range fun t : {t // hB.hwt hc t = p₀} ↦ hB.hvec hc t) := by
  let Φ : Module.End k M := V.wtProj p₀ - V.fTilde hq0 hq ∘ₗ V.eTilde hq0 hq ∘ₗ V.wtProj p₀
  have hmap : Submodule.map Φ (Submodule.span k (Set.range (hB.strVec hc))) ≤
      Submodule.span k (Set.range fun t : {t // hB.hwt hc t = p₀} ↦ hB.hvec hc t) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨⟨h, j⟩, rfl⟩
    have hp := hB.hvec_prim hc h
    have hw : hB.strVec hc ⟨h, j⟩ ∈ V.wt ((hB.hwt hc h : ℤ) - 2 * (j : ℕ)) := by
      simpa [strVec] using V.dF_mem hp.1 (j : ℕ)
    simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, V.wtProj_of_mem hw]
    split_ifs with he
    · obtain ⟨j, hj⟩ := j
      cases j with
      | zero =>
        have he' : hB.hwt hc h = p₀ := by simpa using he
        simp only [strVec, dF_zero, eTilde_of_primitive hq0 hq hp.2 hp.1, map_zero, sub_zero]
        exact Submodule.subset_span ⟨⟨h, he'⟩, rfl⟩
      | succ j =>
        simp only [strVec, fTilde_eTilde_dF_succ hq0 hq hp.2 hp.1, sub_self]
        exact zero_mem _
    · simp
  intro x hx
  have hΦ : Φ x = x := by
    have h1 : V.wtProj p₀ x = x := by simpa using V.wtProj_of_mem (n := p₀) hx.1
    simp [Φ, h1, eTilde_of_primitive hq0 hq hx.2 hx.1]
  rw [← hΦ]
  exact hmap ⟨x, by rw [hB.span_k_strVec hc]; trivial, rfl⟩

/-- **Structure of crystal bases at one colour** (cf. [HK] Thm. 4.3.2): a crystal base
`(L, B)` of a finite-dimensional integrable `U_q(𝔰𝔩₂)`-module over a local domain `A` with
fraction field `k` is the string lattice of the highest vectors `η_h` (lifts of the highest
elements `h` of `B`): the `η_h` of each weight form a basis of the primitive vectors of that
weight and `L` is spanned over `A` by the `F^{(j)} η_h`, whose classes form `B`. -/
theorem eq_stringLattice :
    (∀ h, hB.hvec hc h ∈ V.prim (hB.hwt hc h)) ∧
    (∀ p₀ : ℕ, LinearIndependent k (fun t : {t // hB.hwt hc t = p₀} ↦ hB.hvec hc t)) ∧
    (∀ p₀ : ℕ, V.prim p₀ ≤
      Submodule.span k (Set.range fun t : {t // hB.hwt hc t = p₀} ↦ hB.hvec hc t)) ∧
    L = V.stringLattice A (hB.hvec hc) (hB.hwt hc) := by
  refine ⟨hB.hvec_prim hc, fun p₀ ↦ ?_, hB.prim_le_span hc, (hB.span_strVec hc).symm⟩
  have := (hB.linearIndependent_strVec hc).comp
    (fun t : {t // hB.hwt hc t = p₀} ↦ (⟨t.1, 0⟩ : Σ h : hB.highest, Fin (hB.hwt hc h + 1)))
    (fun s t hst ↦ Subtype.ext (congrArg Sigma.fst hst))
  simpa [Function.comp_def, strVec] using this

end FiniteDimensional

end IsCrystalBase

end IntegrableSl2

end LieLean.QuantumGroup
