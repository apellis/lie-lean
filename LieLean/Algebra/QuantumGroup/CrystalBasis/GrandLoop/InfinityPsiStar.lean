/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityPsiEmb

/-!
# `Ψᵢ` and the `*`-crystal structure of `B(∞)`

Assume `A/ϖA` is formally real, so that `*` induces an involution of `B(∞)` (`GrandLoop.starInf`,
from `B(∞)* = B(∞)`). Put `f̃ᵢ* = * f̃ᵢ *` on `B(∞)` (`GrandLoop.fsInf`). Then
([Kas93a] Thm. 2.2.1 (ii), (iii); [KS97] Thm. 3.2.2 (2), (3)):

* if `Ψᵢ(b) = b' ⊗ f̃ᵢⁿ bᵢ`, then `εᵢ(b*) = n`, `εᵢ(b'*) = 0` and `b = f̃ᵢ*ⁿ b'`
  (`GrandLoop.psiInf_star`), and `Ψᵢ(f̃ᵢ* b) = b' ⊗ f̃ᵢⁿ⁺¹ bᵢ` (`GrandLoop.psiInf_fsInf`);
* the image of `Ψᵢ` is `{b ⊗ f̃ᵢⁿ bᵢ | εᵢ(b*) = 0, n ≥ 0}` (`GrandLoop.exists_psiInf_eq_iff`);
* `Ψᵢ` is the unique strict morphism `B(∞) → B(∞) ⊗ Bᵢ` sending `u_∞` to `u_∞ ⊗ bᵢ`
  (`GrandLoop.eq_psiInfHom`).

## References

* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858, §2.2.
* [KS97] M. Kashiwara, Y. Saito, *Geometric construction of crystal bases*, Duke Math. J. 89
  (1997); arXiv:q-alg/9606009v1, §3.2.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

lemma kE_pow_kF_pow (i : I) {j m : ℕ} (hjm : j ≤ m) (y : Um D v) :
    (kE hvt i ^ j) ((kF hvt i ^ m) y) = (kF hvt i ^ (m - j)) y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih (by omega)]
    obtain ⟨r, hr⟩ : ∃ r, m - j = r + 1 := ⟨m - j - 1, by omega⟩
    rw [hr, pow_succ', Module.End.mul_apply, kE_kF, show m - (j + 1) = r by omega]

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
lemma kE_pow_mem_smul_latInf (i : I) (j : ℕ) {x : Um D v} (hx : x ∈ ϖ • latInf hvt A) :
    (kE hvt i ^ j) x ∈ ϖ • latInf hvt A := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i ih

/-! ### `*` on `B(∞)` -/

variable (hvt hR) in
/-- `b ↦ b*` on `B(∞)` ([Kas93a] Thm. 2.1.1). -/
def starInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (b : BInf (D := D) hvt A ϖ) :
    BInf (D := D) hvt A ϖ :=
  mkB hvt hR hinj hϖ hϖv hk hfund (starU_fWi_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
    (D := D)
    (A := A) (exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b).choose).choose

theorem starInf_mkB [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {w w' : List I}
    (h : starU D v (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf hvt A) :
    starInf hvt hR hinj hϖ hϖv hk hfund (mkB hvt hR hinj hϖ hϖv hk hfund w) =
      mkB hvt hR hinj hϖ hϖv hk hfund w' := by
  set b := mkB hvt hR hinj hϖ hϖv hk hfund w
  have hb := (exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b).choose_spec
  set w₁ := (exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b).choose
  have h₁ := (starU_fWi_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
    (D := D) (A := A) w₁).choose_spec
  change mkB hvt hR hinj hϖ hϖv hk hfund
    (starU_fWi_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
    (D := D) (A := A) w₁).choose = _
  rw [mkB_eq_mkB_iff]
  have hww : fWi (D := D) hvt w - fWi hvt w₁ ∈ ϖ • latInf hvt A :=
    (mkB_eq_mkB_iff (hR := hR) hinj hϖ hϖv hk hfund w w₁).1 hb
  have h2 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hww
  rw [map_sub] at h2
  have := sub_mem (add_mem h2 h₁) h
  convert neg_mem this using 1; abel

theorem starInf_starInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (b : BInf (D := D) hvt A ϖ) :
    starInf hvt hR hinj hϖ hϖv hk hfund (starInf hvt hR hinj hϖ hϖv hk hfund b) = b := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨w', hw'⟩ := starU_fWi_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
    (D := D) (A := A) w
  rw [starInf_mkB hinj hϖ hϖv hk hfund hw', starInf_mkB hinj hϖ hϖv hk hfund (w' := w)]
  have := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hw'
  rw [map_sub, starU_starU] at this
  simpa using neg_mem this

/-! ### `f̃ᵢ*` on `B(∞)` -/

variable (hvt hR) in
/-- `f̃ᵢ` on `B(∞)`, as a map `B(∞) → B(∞)`. -/
def fB (i : I) (b : BInf (D := D) hvt A ϖ) : BInf (D := D) hvt A ϖ :=
  ⟨_, fQInf_mem_BInf (hR := hR) hinj hϖ hϖv hk hfund i b.2⟩

lemma fB_mkB (i : I) (w : List I) :
    fB hvt hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund w) =
      mkB hvt hR hinj hϖ hϖv hk hfund (i :: w) := rfl

variable (hvt hR) in
/-- `f̃ᵢ* = * f̃ᵢ *` on `B(∞)`. -/
def fsInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (b : BInf (D := D) hvt A ϖ) :
    BInf (D := D) hvt A ϖ :=
  starInf hvt hR hinj hϖ hϖv hk hfund
    (fB hvt hR hinj hϖ hϖv hk hfund i (starInf hvt hR hinj hϖ hϖv hk hfund b))

theorem fsInf_mkB [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {u u' : List I}
    (h : kFs hvt i (fWi (D := D) hvt u) - fWi hvt u' ∈ ϖ • latInf hvt A) :
    fsInf hvt hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund u) =
      mkB hvt hR hinj hϖ hϖv hk hfund u' := by
  obtain ⟨us, hus⟩ := starU_fWi_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
    (D := D) (A := A) u
  rw [fsInf, starInf_mkB hinj hϖ hϖv hk hfund hus, fB_mkB, starInf_mkB hinj hϖ hϖv hk hfund]
  have hc : fWi (D := D) hvt (i :: us) = kF hvt i (fWi hvt us) := rfl
  have h1 : kF hvt i (fWi (D := D) hvt us) - kF hvt i (starU D v (fWi hvt u)) ∈
      ϖ • latInf hvt A := by
    have := kF_mem_smul_latInf (hvt := hvt) (A := A) (ϖ := ϖ) i (neg_mem hus)
    rwa [map_neg, map_sub, neg_sub] at this
  have h2 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h1
  rw [map_sub] at h2
  rw [hc]
  have := add_mem h2 h
  convert this using 1
  rw [kFs_apply]; abel

/-! ### `Ψᵢ` and `*` -/

include hR in
/-- `εᵢ` of the class of `x ≡ f̃ᵢᵐ y` with `ẽᵢ y = 0`, `y ∉ ϖ L(∞)`. -/
lemma epsInf_mkB_of_kF_pow (i : I) (m : ℕ) {y : Um D v} (hy : y ∉ ϖ • latInf hvt A)
    (hey : kE hvt i y = 0) {w : List I}
    (hw : fWi hvt w - (kF hvt i ^ m) y ∈ ϖ • latInf hvt A) :
    epsInf hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund w) = m := by
  have e0 : (kE hvt i ^ m) ((kF hvt i ^ m) y) = y := by
    rw [kE_pow_kF_pow i le_rfl, Nat.sub_self, pow_zero, Module.End.one_apply]
  have e1 : (kE hvt i ^ (m + 1)) ((kF hvt i ^ m) y) = 0 := by
    rw [pow_succ', Module.End.mul_apply, e0, hey]
  refine epsInf_mkB (hR := hR) hinj hϖ hϖv hk hfund i w (n := m) ?_ ?_
  · intro h
    have h1 := kE_pow_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i m hw
    rw [map_sub, e0] at h1
    exact hy (by simpa using sub_mem h h1)
  · have h1 := kE_pow_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i (m + 1) hw
    rwa [map_sub, e1, sub_zero] at h1

/-- **[Kas93a] Thm. 2.2.1 (ii), [KS97] Thm. 3.2.2 (2)**: if `Ψᵢ(b) = b' ⊗ f̃ᵢⁿ bᵢ`, then
`εᵢ(b*) = n`, `εᵢ(b'*) = 0` and `b = f̃ᵢ*ⁿ b'`. -/
theorem psiInf_star [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {b b' : BInf (D := D) hvt A ϖ}
    {n : ℕ} (h : psiInf hvt hR hinj hϖ hϖv hk hfund i b = (b', -(n : ℤ))) :
    epsInf hR hinj hϖ hϖv hk hfund i (starInf hvt hR hinj hϖ hϖv hk hfund b) = n ∧
      epsInf hR hinj hϖ hϖv hk hfund i (starInf hvt hR hinj hϖ hϖv hk hfund b') = 0 ∧
      (fsInf hvt hR hinj hϖ hϖv hk hfund i)^[n] b' = b := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨m, P, w₀, hP, hPw, he, hw₀, hw, -, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w
  rw [hpsi, Prod.mk.injEq, neg_inj, Nat.cast_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  have hP0 : P ∉ ϖ • latInf hvt A := fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀
    (by simpa using sub_mem h hw₀)
  set y := starU D v P
  have hy : y ∉ ϖ • latInf hvt A := fun h ↦ hP0 (by
    simpa [y, starU_starU] using starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h)
  have hey : kE hvt i y = 0 :=
    BosonModule.eTilde_of_ker (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) i)
      (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
      (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) he
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ws, hws⟩ := starU_fWi_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
      (D := D) (A := A) w
    rw [starInf_mkB hinj hϖ hϖv hk hfund hws]
    refine epsInf_mkB_of_kF_pow (hR := hR) hinj hϖ hϖv hk hfund i m hy hey ?_
    have h1 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hw
    rw [map_sub, rmulF_apply, starU_starU, ← kF_pow_eq_df (hvt := hvt) i he] at h1
    have := sub_mem h1 hws
    convert this using 1; abel
  · obtain ⟨ws, hws⟩ := starU_fWi_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
      (D := D) (A := A) w₀
    rw [starInf_mkB hinj hϖ hϖv hk hfund hws]
    refine epsInf_mkB_of_kF_pow (hR := hR) hinj hϖ hϖv hk hfund i 0 hy hey ?_
    have h1 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hw₀
    rw [map_sub] at h1
    have := add_mem h1 hws
    rw [pow_zero, Module.End.one_apply]
    convert neg_mem this using 1; abel
  · -- `f̃ᵢ*ʲ b' ≡ P fᵢ^{(j)}`
    have key : ∀ j : ℕ, ∃ u : List I,
        (fsInf hvt hR hinj hϖ hϖv hk hfund i)^[j] (mkB hvt hR hinj hϖ hϖv hk hfund w₀) =
          mkB hvt hR hinj hϖ hϖv hk hfund u ∧
        rmulF hvt i j P - fWi hvt u ∈ ϖ • latInf hvt A := by
      intro j
      induction j with
      | zero => exact ⟨w₀, rfl, by simpa using hw₀⟩
      | succ j ih =>
        obtain ⟨u, hu, hPu⟩ := ih
        obtain ⟨u', hu'⟩ := rmulF_sub_mem_of_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i (j + 1)
          hP hPw he hw₀
        refine ⟨u', ?_, hu'⟩
        rw [Function.iterate_succ_apply', hu]
        apply fsInf_mkB hinj hϖ hϖv hk hfund i
        have e1 : rmulF hvt i j P = (kFs hvt i ^ j) P := rmulF_eq_kFs_pow i j he
        have e2 : rmulF hvt i (j + 1) P = kFs hvt i ((kFs hvt i ^ j) P) := by
          rw [rmulF_eq_kFs_pow i _ he, pow_succ', Module.End.mul_apply]
        have h1 := kFs_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i hPu
        rw [map_sub, e1] at h1
        rw [e2] at hu'
        have := add_mem (neg_mem h1) hu'
        convert this using 1; abel
    obtain ⟨u, hu, hPu⟩ := key m
    rw [hu, mkB_eq_mkB_iff]
    have := add_mem hPu hw
    convert neg_mem this using 1; abel

/-- **[Kas93a] Thm. 2.2.1 (ii)**: `Ψᵢ(f̃ᵢ* b) = b' ⊗ f̃ᵢⁿ⁺¹ bᵢ` if `Ψᵢ(b) = b' ⊗ f̃ᵢⁿ bᵢ`. -/
theorem psiInf_fsInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I)
    (b : BInf (D := D) hvt A ϖ) :
    psiInf hvt hR hinj hϖ hϖv hk hfund i (fsInf hvt hR hinj hϖ hϖv hk hfund i b) =
      ((psiInf hvt hR hinj hϖ hϖv hk hfund i b).1,
        (psiInf hvt hR hinj hϖ hϖv hk hfund i b).2 - 1) := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨m, P, w₀, hP, hPw, he, hw₀, hw, -, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w
  obtain ⟨u', hu'⟩ := rmulF_sub_mem_of_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i (m + 1)
    hP hPw he hw₀
  have e : rmulF hvt i (m + 1) P = kFs hvt i (rmulF hvt i m P) := by
    rw [rmulF_eq_kFs_pow i _ he, rmulF_eq_kFs_pow i _ he, pow_succ', Module.End.mul_apply]
  have h1 : kFs hvt i (fWi (D := D) hvt w) - fWi hvt u' ∈ ϖ • latInf hvt A := by
    have h2 := kFs_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i hw
    rw [map_sub, ← e] at h2
    have := add_mem h2 hu'
    convert this using 1; abel
  have hu'' : fWi hvt u' - rmulF hvt i (m + 1) P ∈ ϖ • latInf hvt A := by
    have := neg_mem hu'
    rwa [neg_sub] at this
  rw [fsInf_mkB hinj hϖ hϖv hk hfund i h1, hpsi,
    psiInf_eq hinj hϖ hϖv hk hfund i he hw₀ hu'']
  simp only [Nat.cast_add, Nat.cast_one, Prod.mk.injEq, true_and]
  ring

/-- **[Kas93a] Thm. 2.2.1 (iii), [KS97] Thm. 3.2.2 (3)**: the image of `Ψᵢ` is
`{b ⊗ f̃ᵢⁿ bᵢ | εᵢ(b*) = 0, n ≥ 0}`. -/
theorem exists_psiInf_eq_iff [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I)
    (b' : BInf (D := D) hvt A ϖ) (n : ℕ) :
    (∃ b, psiInf hvt hR hinj hϖ hϖv hk hfund i b = (b', -(n : ℤ))) ↔
      epsInf hR hinj hϖ hϖv hk hfund i (starInf hvt hR hinj hϖ hϖv hk hfund b') = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    exact (psiInf_star hinj hϖ hϖv hk hfund i hb).2.1
  · intro h0
    obtain ⟨u, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b'
    obtain ⟨m, P, u₀, hP, hPw, he, hu₀, hu, -, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i u
    have hm : m = 0 := by
      have := (psiInf_star hinj hϖ hϖv hk hfund i hpsi).1
      rw [h0] at this
      omega
    subst hm
    obtain ⟨w', hw'⟩ := rmulF_sub_mem_of_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i n hP hPw he hu₀
    refine ⟨mkB hvt hR hinj hϖ hϖv hk hfund w', ?_⟩
    rw [psiInf_eq hinj hϖ hϖv hk hfund i he hu₀ (m := n) (by simpa using neg_mem hw'),
      Prod.mk.injEq, mkB_eq_mkB_iff]
    refine ⟨?_, rfl⟩
    rw [rmulF_zero] at hu
    have := add_mem hu₀ hu
    convert neg_mem this using 1; abel

/-- **Uniqueness of `Ψᵢ`** ([Kas93a] Thm. 2.2.1 (i)): a strict morphism `B(∞) → B(∞) ⊗ Bᵢ` sending
`u_∞` to `u_∞ ⊗ bᵢ` is `Ψᵢ`. -/
theorem eq_psiInfHom [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I)
    (Ψ : Crystal.StrictHom (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund)
      ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
        (Crystal.elementary R.crystalDatum i)))
    (h : Ψ (mkB hvt hR hinj hϖ hϖv hk hfund []) = (mkB hvt hR hinj hϖ hϖv hk hfund [], 0)) :
    Ψ = psiInfHom hvt hR hinj hϖ hϖv hk hfund i := by
  apply Crystal.StrictHom.ext
  intro b
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  induction w with
  | nil => rw [h]; exact (psiInf_one hinj hϖ hϖv hk hfund i).symm
  | cons j w ih =>
    have h1 := Ψ.f_apply j (mkB hvt hR hinj hϖ hϖv hk hfund w)
    have h2 := (psiInfHom hvt hR hinj hϖ hϖv hk hfund i).f_apply j
      (mkB hvt hR hinj hϖ hϖv hk hfund w)
    have hf : (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).f j
        (mkB hvt hR hinj hϖ hϖv hk hfund w) = some (mkB hvt hR hinj hϖ hϖv hk hfund (j :: w)) :=
      rfl
    rw [hf, Option.map_some, ih] at h1
    rw [hf, Option.map_some] at h2
    exact Option.some_injective _ (h1.symm.trans h2)

end Base

end GrandLoop

end LieLean.QuantumGroup
