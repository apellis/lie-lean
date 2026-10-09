/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityPsi

/-!
# The embeddings `Ψᵢ : B(∞) → B(∞) ⊗ Bᵢ`

Assume `A/ϖA` is formally real. Writing `b = f̃ᵢ*ᵐ b₀` with `ẽᵢ* b₀ = 0`
(`GrandLoop.exists_starStr`, `GrandLoop.psiInf_spec`), the map `Ψᵢ(b) = b₀ ⊗ f̃ᵢᵐ bᵢ`
(`GrandLoop.psiInf`) is an injective strict morphism of crystals `B(∞) → B(∞) ⊗ Bᵢ` sending `u_∞`
to `u_∞ ⊗ bᵢ` (`GrandLoop.psiInfHom`, `GrandLoop.psiInf_injective`, `GrandLoop.psiInf_one`;
[Kas93a] Thm. 2.2.1 (i), [KS97] Thm. 3.2.2 (1)). Here `Bᵢ` is `Crystal.elementary i`, with
`f̃ᵢᵐ bᵢ = bᵢ(-m)`, and `⊗` is Kashiwara's tensor product `Crystal.tensor`.

As in [Kas93a], `ẽᵢ Ψᵢ = Ψᵢ ẽᵢ` comes from `T = Φ ∘ π_{μ+λ}` and the tensor product rule
(`GrandLoop.kE_rmulF`). For `j ≠ i` we use instead that `ẽⱼ` commutes exactly with `f̃ᵢ*` on `U⁻`
and preserves `ker e''ᵢ` (`GrandLoop.kE_kFs`, `GrandLoop.e_starU_kE_eq_zero`). The equality
`εⱼ Ψᵢ = εⱼ` is deduced from `ẽⱼ Ψᵢ = Ψᵢ ẽⱼ` by induction on `εⱼ`, using that `ẽⱼ` vanishes on
`Ψᵢ(b)` only when `εⱼ` does; [Kas93a] computes it through `T` instead.

The image lies in `B(∞) × {f̃ᵢⁿ bᵢ | n ≥ 0}`, and for `b ≠ u_∞` some `Ψᵢ(b)` has `n > 0`
(`GrandLoop.psiInf_snd_nonpos`, `GrandLoop.exists_psiInf_snd_neg`): these are the hypotheses
(5)–(7) of [KS97] Prop. 3.2.3.

## References

* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858, §2.2.
* [KS97] M. Kashiwara, Y. Saito, *Geometric construction of crystal bases*, Duke Math. J. 89
  (1997); arXiv:q-alg/9606009v1, §3.2.
-/

open Finset Pointwise TensorProduct LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

open VermaModule TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### `f̃ᵢ*ᵐ` and `rmulF` -/

lemma kEs_kFs (i : I) (u : Um D v) : kEs hvt i (kFs (D := D) hvt i u) = u := by
  rw [kEs_apply, kFs_apply, starU_starU, kE_kF, starU_starU]

/-- `P fᵢ^{(m)} = f̃ᵢ*ᵐ P` for `e''ᵢ P = 0`. -/
lemma rmulF_eq_kFs_pow (i : I) (m : ℕ) {P : Um D v}
    (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0) :
    rmulF hvt i m P = (kFs hvt i ^ m) P := by
  rw [rmulF_apply, ← kF_pow_eq_df (hvt := hvt) i he]
  clear he
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih, kFs_apply,
      starU_starU]

/-- For `j ≠ i`, `ẽⱼ` commutes with `f̃ᵢ*ᵐ`. -/
lemma kE_kFs_pow {i j : I} (hij : i ≠ j) (m : ℕ) (u : Um D v) :
    kE hvt j ((kFs hvt i ^ m) u) = (kFs hvt i ^ m) (kE hvt j u) := by
  induction m generalizing u with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [kE_kFs hij, ih]

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
lemma kFs_mem_smul_latInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {u : Um D v}
    (hu : u ∈ ϖ • latInf hvt A) : kFs hvt i u ∈ ϖ • latInf hvt A :=
  starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund
    (kF_mem_smul_latInf i (starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hu))

include hR in
lemma kEs_mem_smul_latInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {u : Um D v}
    (hu : u ∈ ϖ • latInf hvt A) : kEs hvt i u ∈ ϖ • latInf hvt A :=
  starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund
    (kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i
      (starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hu))

include hR in
/-- `f̃ᵢ*ᵐ u ∈ ϖ L(∞)` iff `u ∈ ϖ L(∞)`. -/
lemma kFs_pow_mem_smul_iff [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (m : ℕ) (u : Um D v) :
    (kFs hvt i ^ m) u ∈ ϖ • latInf hvt A ↔ u ∈ ϖ • latInf hvt A := by
  induction m generalizing u with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    constructor
    · intro h
      have := kEs_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i h
      rw [kEs_kFs] at this
      exact (ih u).1 this
    · intro h
      exact kFs_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i ((ih u).2 h)

/-! ### `B(∞)` through words -/

variable (hvt hR) in
/-- The class of `f̃_w 1` in `B(∞)`. -/
def mkB (w : List I) : BInf (D := D) hvt A ϖ :=
  ⟨_, mk_fwInf_mem_BInf (hR := hR) hinj hϖ hϖv hk hfund w⟩

lemma mkB_eq_mkB_iff (w w' : List I) :
    mkB hvt hR hinj hϖ hϖv hk hfund w = mkB hvt hR hinj hϖ hϖv hk hfund w' ↔
      fWi (D := D) hvt w - fWi hvt w' ∈ ϖ • latInf hvt A := by
  rw [mkB, mkB, Subtype.mk.injEq, IntegrableSl2.mk_eq_mk_iff]

lemma exists_eq_mkB (b : BInf (D := D) hvt A ϖ) : ∃ w, b = mkB hvt hR hinj hϖ hϖv hk hfund w := by
  obtain ⟨w, hw⟩ := exists_eq_mk_of_mem_BInf b.2
  exact ⟨w, Subtype.ext hw⟩

lemma wtInf_mkB (w : List I) :
    wtInf (R := R) (mkB hvt hR hinj hϖ hϖv hk hfund w) = -R.rootSum (wordWeight w) :=
  wtInf_eq (hR := hR) hinj hϖ hϖv hk hfund _ rfl

/-- `εⱼ(f̃_w 1) = n` if `ẽⱼⁿ f̃_w 1 ∉ ϖ L(∞)` and `ẽⱼⁿ⁺¹ f̃_w 1 ∈ ϖ L(∞)`. -/
lemma epsInf_mkB (j : I) (w : List I) {n : ℕ}
    (h1 : (kE hvt j ^ n) (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A)
    (h2 : (kE hvt j ^ (n + 1)) (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A) :
    epsInf hR hinj hϖ hϖv hk hfund j (mkB hvt hR hinj hϖ hϖv hk hfund w) = n := by
  classical
  have hzero : ∀ c, (eQInf hR hinj hϖ hϖv hk hfund j ^ c)
      (mkB hvt hR hinj hϖ hϖv hk hfund w).1 = 0 ↔
      (kE hvt j ^ c) (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A := by
    intro c
    obtain ⟨h, he⟩ := eQInf_pow_mk hinj hϖ hϖv hk hfund j c (fwInf hvt A w)
    rw [mkB, he, IntegrableSl2.mk_eq_zero_iff]
  have hfind : Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund j
      (mkB hvt hR hinj hϖ hϖv hk hfund w)) = n + 1 := by
    rw [Nat.find_eq_iff]
    refine ⟨(hzero _).2 h2, fun c hc h ↦ h1 ?_⟩
    rw [hzero] at h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show c ≤ n by omega)
    rw [hd, add_comm, pow_add, Module.End.mul_apply]
    clear hd hc
    induction d with
    | zero => simpa using h
    | succ d ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund j ih
  rw [epsInf, hfind, Nat.add_sub_cancel]

lemma eInf_mkB_eq_none (j : I) (w : List I)
    (h : kE hvt j (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A) :
    eInf hR hinj hϖ hϖv hk hfund j (mkB hvt hR hinj hϖ hϖv hk hfund w) = none := by
  have hz : eQInf hR hinj hϖ hϖv hk hfund j (mkB hvt hR hinj hϖ hϖv hk hfund w).1 = 0 := by
    rw [mkB, eQInf_mk, IntegrableSl2.mk_eq_zero_iff]
    exact h
  simp [eInf, hz]

lemma eInf_mkB_eq_some (j : I) (w w' : List I)
    (h : kE hvt j (fWi (D := D) hvt w) - fWi hvt w' ∈ ϖ • latInf hvt A) :
    eInf hR hinj hϖ hϖv hk hfund j (mkB hvt hR hinj hϖ hϖv hk hfund w) =
      some (mkB hvt hR hinj hϖ hϖv hk hfund w') := by
  rw [eInf_eq_some_iff, mkB, mkB, eQInf_mk]
  exact (IntegrableSl2.mk_eq_mk_iff ϖ _ _).2 h

include hR in
lemma exists_eps (j : I) (w : List I) : ∃ n : ℕ,
    (kE hvt j ^ n) (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A ∧
      (kE hvt j ^ (n + 1)) (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A := by
  classical
  have hex : ∃ n, (kE hvt j ^ (n + 1)) (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A :=
    ⟨wordWeight w j, by rw [kE_pow_eq_zero j (fWi_mem_Uw (hvt := hvt) w)]; exact zero_mem _⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | n
  · simpa using fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w
  · exact Nat.find_min hex (show n < Nat.find hex by omega)

/-! ### `Ψᵢ` -/

variable (hvt hR) in
/-- **`Ψᵢ(b) = b₀ ⊗ f̃ᵢᵐ bᵢ`** for `b = f̃ᵢ*ᵐ b₀`, `ẽᵢ* b₀ = 0` ([Kas93a] Thm. 2.2.1), with
`f̃ᵢᵐ bᵢ = bᵢ(-m)`. -/
def psiInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (b : BInf (D := D) hvt A ϖ) :
    BInf (D := D) hvt A ϖ × ℤ :=
  (mkB hvt hR hinj hϖ hϖv hk hfund (exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
      i (exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b).choose).choose_spec.choose_spec.choose,
    -((exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i
      (exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b).choose).choose : ℤ))

/-- `Ψᵢ` from any `*`-string data. -/
theorem psiInf_eq [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {w : List I} {m : ℕ}
    {P : Um D v} {w₀ : List I}
    (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0)
    (hw₀ : P - fWi hvt w₀ ∈ ϖ • latInf hvt A)
    (hw : fWi hvt w - rmulF hvt i m P ∈ ϖ • latInf hvt A) :
    psiInf hvt hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund w) =
      (mkB hvt hR hinj hϖ hϖv hk hfund w₀, -(m : ℤ)) := by
  set b := mkB hvt hR hinj hϖ hϖv hk hfund w
  have hb := (exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b).choose_spec
  set w' := (exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b).choose
  obtain ⟨-, -, he', hP'₀, hw'r, -⟩ := (exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv
    hk hfund i w').choose_spec.choose_spec.choose_spec
  set m' := (exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i w').choose
  set P' := (exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i w').choose_spec.choose
  set w₀' := (exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i
    w').choose_spec.choose_spec.choose
  have hww' : fWi (D := D) hvt w - fWi hvt w' ∈ ϖ • latInf hvt A :=
    (mkB_eq_mkB_iff (hR := hR) hinj hϖ hϖv hk hfund w w').1 hb
  have hP0 : P ∉ ϖ • latInf hvt A := fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀
    (by simpa using sub_mem h hw₀)
  have h1 : rmulF hvt i m P - rmulF hvt i m' P' ∈ ϖ • latInf hvt A := by
    have := add_mem (sub_mem hww' hw) hw'r
    convert this using 1; abel
  have hpsi : psiInf hvt hR hinj hϖ hϖv hk hfund i b =
      (mkB hvt hR hinj hϖ hϖv hk hfund w₀', -(m' : ℤ)) := rfl
  obtain ⟨hmm, hPP'⟩ := eq_of_rmulF_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i he he' hP0 h1
  rw [hpsi, ← hmm]
  congr 1
  rw [mkB_eq_mkB_iff]
  have := add_mem (sub_mem (neg_mem hP'₀) hPP') hw₀
  convert this using 1; abel

/-- The defining data of `Ψᵢ(f̃_w 1)`. -/
theorem psiInf_spec [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (w : List I) :
    ∃ (m : ℕ) (P : Um D v) (w₀ : List I), P ∈ latInf hvt A ∧ P ∈ Uw D v (wordWeight w₀) ∧
      (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0 ∧
      P - fWi hvt w₀ ∈ ϖ • latInf hvt A ∧ fWi hvt w - rmulF hvt i m P ∈ ϖ • latInf hvt A ∧
      wordWeight w₀ + Finsupp.single i m = wordWeight w ∧
      psiInf hvt hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund w) =
        (mkB hvt hR hinj hϖ hϖv hk hfund w₀, -(m : ℤ)) := by
  obtain ⟨m, P, w₀, hP, hPw, he, hw₀, hw, hwt⟩ :=
    exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i w
  exact ⟨m, P, w₀, hP, hPw, he, hw₀, hw, hwt, psiInf_eq hinj hϖ hϖv hk hfund i he hw₀ hw⟩

/-- `Ψᵢ` preserves weights: `wt b = wt b₀ - m αᵢ`. -/
theorem wtInf_psiInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (b : BInf (D := D) hvt A ϖ) :
    wtInf (R := R) (psiInf hvt hR hinj hϖ hϖv hk hfund i b).1 +
      (psiInf hvt hR hinj hϖ hϖv hk hfund i b).2 • R.root i = wtInf (R := R) b := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨m, P, w₀, -, -, -, -, -, hwt, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w
  rw [hpsi, wtInf_mkB, wtInf_mkB, ← hwt, R.rootSum_add, R.rootSum_single, neg_smul,
    natCast_zsmul]
  abel

/-- `εᵢ(b) = 0` iff `ẽᵢ b = 0` on `B(∞)`. -/
lemma epsInf_eq_zero_iff (j : I) (b : BInf (D := D) hvt A ϖ) :
    epsInf hR hinj hϖ hϖv hk hfund j b = 0 ↔ eInf hR hinj hϖ hϖv hk hfund j b = none := by
  classical
  have hb0 : ¬ (eQInf hR hinj hϖ hϖv hk hfund j ^ 0) b.1 = 0 := by
    simpa using fun h' ↦ zero_notMem_BInf (h' ▸ b.2)
  have hpos : 0 < Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund j b) :=
    Nat.pos_of_ne_zero fun h0 ↦ hb0 (h0 ▸ Nat.find_spec
      (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund j b))
  have hnone : eInf hR hinj hϖ hϖv hk hfund j b = none ↔
      eQInf hR hinj hϖ hϖv hk hfund j b.1 = 0 := by
    unfold eInf; split_ifs with h <;> simp [h]
  rw [hnone, epsInf]
  constructor
  · intro h
    have h1 : Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund j b) = 1 := by
      omega
    have := Nat.find_spec (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund j b)
    rwa [h1, pow_one] at this
  · intro h
    have : Nat.find (exists_eQInf_pow_eq_zero (hR := hR) hinj hϖ hϖv hk hfund j b) ≤ 1 :=
      Nat.find_min' _ (by rw [pow_one]; exact h)
    omega

/-- `ẽⱼ Ψᵢ = Ψᵢ ẽⱼ` for `j ≠ i`. -/
theorem e_psiInf_of_ne [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {i j : I} (hij : i ≠ j)
    (b : BInf (D := D) hvt A ϖ) :
    ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
        (Crystal.elementary (D := R.crystalDatum) i)).e j
        (psiInf hvt hR hinj hϖ hϖv hk hfund i b) =
      (eInf hR hinj hϖ hϖv hk hfund j b).map (psiInf hvt hR hinj hϖ hϖv hk hfund i) := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨m, P, w₀, -, -, he, hw₀, hw, -, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w
  rw [hpsi]
  have hte : ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
      (Crystal.elementary (D := R.crystalDatum) i)).e j
        (mkB hvt hR hinj hϖ hϖv hk hfund w₀, -(m : ℤ)) =
      (eInf hR hinj hϖ hϖv hk hfund j (mkB hvt hR hinj hϖ hϖv hk hfund w₀)).map
        (·, -(m : ℤ)) := by
    simp [Crystal.tensor, Crystal.elementary, Ne.symm hij, crystalInf]
  rw [hte]
  have hcomm : kE hvt j (fWi (D := D) hvt w) - (kFs hvt i ^ m) (kE hvt j P) ∈
      ϖ • latInf hvt A := by
    have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund j hw
    rwa [map_sub, rmulF_eq_kFs_pow i m he, kE_kFs_pow hij] at this
  have hP0 : kE hvt j P - kE hvt j (fWi (D := D) hvt w₀) ∈ ϖ • latInf hvt A := by
    have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund j hw₀
    rwa [map_sub] at this
  rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund j w₀ with h0 | ⟨w₀', h0⟩
  · have hP : kE hvt j P ∈ ϖ • latInf hvt A := by
      have := add_mem hP0 h0; simpa using this
    have h1 : kE hvt j (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A := by
      have := add_mem hcomm
        ((kFs_pow_mem_smul_iff (hR := hR) hinj hϖ hϖv hk hfund i m _).2 hP)
      simpa using this
    rw [eInf_mkB_eq_none hinj hϖ hϖv hk hfund j w₀ h0,
      eInf_mkB_eq_none hinj hϖ hϖv hk hfund j w h1]
    rfl
  · have hP' : kE hvt j P - fWi hvt w₀' ∈ ϖ • latInf hvt A := by
      have := add_mem hP0 h0
      convert this using 1; abel
    have hne : kE hvt j (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A := by
      intro h
      have h2 : (kFs hvt i ^ m) (kE hvt j P) ∈ ϖ • latInf hvt A := by
        have := sub_mem h hcomm; simpa using this
      rw [kFs_pow_mem_smul_iff (hR := hR) hinj hϖ hϖv hk hfund] at h2
      exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀' (by simpa using sub_mem h2 hP')
    rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund j w with h1 | ⟨w', h1⟩
    · exact absurd h1 hne
    have he' := e_starU_kE_eq_zero (hvt := hvt) hij he
    rw [eInf_mkB_eq_some hinj hϖ hϖv hk hfund j w₀ w₀' h0,
      eInf_mkB_eq_some hinj hϖ hϖv hk hfund j w w' h1, Option.map_some, Option.map_some,
      psiInf_eq hinj hϖ hϖv hk hfund i he' hP' (m := m)]
    rw [rmulF_eq_kFs_pow i m he']
    have := sub_mem hcomm h1
    convert this using 1; abel

/-- `ẽᵢ Ψᵢ = Ψᵢ ẽᵢ` ([Kas93a] Thm. 2.2.1, the case `j = i`). -/
theorem e_psiInf_self [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I)
    (b : BInf (D := D) hvt A ϖ) :
    ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
        (Crystal.elementary (D := R.crystalDatum) i)).e i
        (psiInf hvt hR hinj hϖ hϖv hk hfund i b) =
      (eInf hR hinj hϖ hϖv hk hfund i b).map (psiInf hvt hR hinj hϖ hϖv hk hfund i) := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨m, P, w₀, hPL, hPw, he, hw₀, hw, -, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w
  obtain ⟨kk, hkk1, hkk2⟩ := exists_eps (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i w₀
  have heps := epsInf_mkB (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i w₀ hkk1 hkk2
  have hmain := kE_rmulF (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i hPL hPw he hw₀ hkk1 hkk2 hw
  have hP0 : P ∉ ϖ • latInf hvt A := fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀
    (by simpa using sub_mem h hw₀)
  have hkP : kE hvt i P - kE hvt i (fWi (D := D) hvt w₀) ∈ ϖ • latInf hvt A := by
    have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i hw₀
    rwa [map_sub] at this
  rw [hpsi]
  have hte : ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
      (Crystal.elementary (D := R.crystalDatum) i)).e i
        (mkB hvt hR hinj hϖ hϖv hk hfund w₀, -(m : ℤ)) =
      if (m : ℤ) ≤ kk - R.rootSum (wordWeight w₀) (R.coroot i) then
        (eInf hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund w₀)).map
          (·, -(m : ℤ))
      else some (mkB hvt hR hinj hϖ hϖv hk hfund w₀, -(m : ℤ) + 1) := by
    simp only [Crystal.tensor, Crystal.elementary, crystalInf, ite_true, neg_neg, heps,
      wtInf_mkB]
    simp only [AddMonoidHom.neg_apply, WithBot.coe_le_coe, ← sub_eq_add_neg]
    rfl
  rw [hte]
  split_ifs with hm
  · obtain ⟨hA, hB⟩ := hmain.1 hm
    by_cases hEP : kE hvt i P ∈ ϖ • latInf hvt A
    · have h0 : kE hvt i (fWi (D := D) hvt w₀) ∈ ϖ • latInf hvt A := by
        simpa using sub_mem hEP hkP
      rw [eInf_mkB_eq_none hinj hϖ hϖv hk hfund i w₀ h0,
        eInf_mkB_eq_none hinj hϖ hϖv hk hfund i w (hA hEP)]
      rfl
    · obtain ⟨P', hP'L, he', hP'E, hwP'⟩ := hB hEP
      have h0 : kE hvt i (fWi (D := D) hvt w₀) ∉ ϖ • latInf hvt A := fun h ↦
        hEP (by simpa using add_mem hkP h)
      rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i w₀ with h0' | ⟨w₀', h0'⟩
      · exact absurd h0' h0
      have hne : kE hvt i (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A := by
        intro h
        have h2 : (kFs hvt i ^ m) P' ∈ ϖ • latInf hvt A := by
          rw [← rmulF_eq_kFs_pow i m he']; simpa using sub_mem h hwP'
        rw [kFs_pow_mem_smul_iff (hR := hR) hinj hϖ hϖv hk hfund] at h2
        exact hEP (by simpa using sub_mem h2 hP'E)
      rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i w with h1 | ⟨w', h1⟩
      · exact absurd h1 hne
      have hP'0 : P' - fWi hvt w₀' ∈ ϖ • latInf hvt A := by
        have := add_mem (add_mem hP'E hkP) h0'
        convert this using 1; abel
      rw [eInf_mkB_eq_some hinj hϖ hϖv hk hfund i w₀ w₀' h0',
        eInf_mkB_eq_some hinj hϖ hϖv hk hfund i w w' h1, Option.map_some, Option.map_some,
        psiInf_eq hinj hϖ hϖv hk hfund i he' hP'0 (m := m)]
      have := sub_mem hwP' h1
      convert this using 1; abel
  · have hB := hmain.2 (lt_of_not_ge hm)
    have hne : kE hvt i (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A := by
      intro h
      have h2 : (kFs hvt i ^ (m - 1)) P ∈ ϖ • latInf hvt A := by
        rw [← rmulF_eq_kFs_pow i (m - 1) he]; simpa using sub_mem h hB
      rw [kFs_pow_mem_smul_iff (hR := hR) hinj hϖ hϖv hk hfund] at h2
      exact hP0 h2
    rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i w with h1 | ⟨w', h1⟩
    · exact absurd h1 hne
    have hb' : psiInf hvt hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund w') =
        (mkB hvt hR hinj hϖ hϖv hk hfund w₀, -((m - 1 : ℕ) : ℤ)) := by
      refine psiInf_eq hinj hϖ hϖv hk hfund i he hw₀ ?_
      have := sub_mem hB h1
      convert this using 1; abel
    have hsome := eInf_mkB_eq_some (hR := hR) hinj hϖ hϖv hk hfund i w w' h1
    rw [hsome, Option.map_some, hb']
    -- `m ≥ 1` by weights
    have hm1 : 1 ≤ m := by
      by_contra hm0
      obtain rfl : m = 0 := by omega
      have hwt1 := wtInf_psiInf (hR := hR) hinj hϖ hϖv hk hfund i
        (mkB hvt hR hinj hϖ hϖv hk hfund w')
      have hwt2 := wtInf_psiInf (hR := hR) hinj hϖ hϖv hk hfund i
        (mkB hvt hR hinj hϖ hϖv hk hfund w)
      rw [hb'] at hwt1
      rw [hpsi] at hwt2
      have hwe := wtInf_eInf (hR := hR) hinj hϖ hϖv hk hfund i _ _
        ((eInf_eq_some_iff (hR := hR) hinj hϖ hϖv hk hfund i _ _).1 hsome)
      have hroot : R.root i = 0 := by
        have : wtInf (R := R) (mkB hvt hR hinj hϖ hϖv hk hfund w') =
            wtInf (R := R) (mkB hvt hR hinj hϖ hϖv hk hfund w) := by
          rw [← hwt1, ← hwt2]
        rw [this] at hwe
        simpa using hwe
      have h2 := R.crystalDatum.coroot_root_self i
      simp [hroot] at h2
    congr 2
    push_cast [Nat.cast_sub hm1]
    ring

/-- `ẽⱼ Ψᵢ = Ψᵢ ẽⱼ` for all `j`. -/
theorem e_psiInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i j : I) (b : BInf (D := D) hvt A ϖ) :
    ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
        (Crystal.elementary (D := R.crystalDatum) i)).e j
        (psiInf hvt hR hinj hϖ hϖv hk hfund i b) =
      (eInf hR hinj hϖ hϖv hk hfund j b).map (psiInf hvt hR hinj hϖ hϖv hk hfund i) := by
  by_cases hij : i = j
  · subst hij; exact e_psiInf_self (hR := hR) hinj hϖ hϖv hk hfund i b
  · exact e_psiInf_of_ne (hR := hR) hinj hϖ hϖv hk hfund hij b

/-- `εⱼ Ψᵢ = εⱼ`. -/
theorem eps_psiInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i j : I) (b : BInf (D := D) hvt A ϖ) :
    ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
        (Crystal.elementary (D := R.crystalDatum) i)).ε j
        (psiInf hvt hR hinj hϖ hϖv hk hfund i b) =
      ((epsInf hR hinj hϖ hϖv hk hfund j b : ℤ) : WithBot ℤ) := by
  set C := (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
    (Crystal.elementary (D := R.crystalDatum) i)
  induction hn : epsInf hR hinj hϖ hϖv hk hfund j b generalizing b with
  | zero =>
    have hb := (epsInf_eq_zero_iff hinj hϖ hϖv hk hfund j b).1 hn
    have hC := e_psiInf (hR := hR) hinj hϖ hϖv hk hfund i j b
    rw [hb, Option.map_none] at hC
    set b₀ := (psiInf hvt hR hinj hϖ hϖv hk hfund i b).1
    set n := (psiInf hvt hR hinj hϖ hϖv hk hfund i b).2
    have hpair : psiInf hvt hR hinj hϖ hϖv hk hfund i b = (b₀, n) := rfl
    rw [hpair] at hC ⊢
    by_cases hij : j = i
    · subst hij
      simp only [C, Crystal.tensor, Crystal.elementary, crystalInf, ite_true] at hC ⊢
      split_ifs at hC with hle
      · rw [Option.map_eq_none_iff, ← epsInf_eq_zero_iff] at hC
        rw [hC] at hle ⊢
        refine max_eq_left ?_
        norm_cast at hle ⊢
        simp only [LusztigCartanDatum.RootDatum.crystalDatum_coroot] at hle ⊢
        omega
      · simp at hC
    · simp only [C, Crystal.tensor, Crystal.elementary, crystalInf, hij, ite_false, bot_le,
        ite_true, Option.map_eq_none_iff] at hC ⊢
      rw [← epsInf_eq_zero_iff] at hC
      rw [hC]
      simp
  | succ n ih =>
    have hne : eInf hR hinj hϖ hϖv hk hfund j b ≠ none := by
      rw [Ne, ← epsInf_eq_zero_iff]; omega
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 hne
    have hε := (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).ε_e j b b' hb'
    have hC := e_psiInf (hR := hR) hinj hϖ hϖv hk hfund i j b
    rw [hb', Option.map_some] at hC
    have hεC := C.ε_e j _ _ hC
    have hn' : epsInf hR hinj hϖ hϖv hk hfund j b' = n := by
      simp only [crystalInf, hn] at hε
      norm_cast at hε
      omega
    rw [hεC, ih b' hn']
    norm_cast

variable (hvt hR) in
/-- **[Kas93a] Thm. 2.2.1 (i)**: `Ψᵢ : B(∞) → B(∞) ⊗ Bᵢ`, `f̃ᵢ*ᵐ b₀ ↦ b₀ ⊗ f̃ᵢᵐ bᵢ`
(`ẽᵢ* b₀ = 0`), is a strict morphism of crystals. -/
def psiInfHom [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) :
    Crystal.StrictHom (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund)
      ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).tensor
        (Crystal.elementary (D := R.crystalDatum) i)) where
  toFun := psiInf hvt hR hinj hϖ hϖv hk hfund i
  wt_map b := wtInf_psiInf (hR := hR) hinj hϖ hϖv hk hfund i b
  ε_map j b := eps_psiInf hinj hϖ hϖv hk hfund i j b
  e_map j b := e_psiInf (hR := hR) hinj hϖ hϖv hk hfund i j b
  f_map j b := by
    obtain ⟨b', hb'⟩ : ∃ b', fInf hR hinj hϖ hϖv hk hfund j b = some b' := ⟨_, rfl⟩
    change _ = (fInf hR hinj hϖ hϖv hk hfund j b).map _
    rw [hb', Option.map_some]
    rw [Crystal.f_eq_some_iff]
    have he : eInf hR hinj hϖ hϖv hk hfund j b' = some b :=
      ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).f_eq_some_iff j b b').1 hb'
    rw [e_psiInf (hR := hR) hinj hϖ hϖv hk hfund i j b', he, Option.map_some]

/-- `Ψᵢ` is injective. -/
theorem psiInf_injective [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) :
    Function.Injective (psiInf hvt hR hinj hϖ hϖv hk hfund i) := by
  intro b b' h
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨w', rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b'
  obtain ⟨m, P, w₀, -, -, he, hw₀, hw, -, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w
  obtain ⟨m', P', w₀', -, -, he', hw₀', hw', -, hpsi'⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w'
  rw [hpsi, hpsi', Prod.mk.injEq, neg_inj, Nat.cast_inj] at h
  obtain ⟨h0, rfl⟩ := h
  rw [mkB_eq_mkB_iff] at h0 ⊢
  have hPP : P - P' ∈ ϖ • latInf hvt A := by
    have := add_mem (sub_mem hw₀ hw₀') h0
    convert this using 1; abel
  have heP : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v (P - P')) = 0 := by
    rw [map_sub, map_sub, he, he', sub_zero]
  have hr := (kFs_pow_mem_smul_iff (hR := hR) hinj hϖ hϖv hk hfund i m _).2 hPP
  rw [← rmulF_eq_kFs_pow i m heP, map_sub] at hr
  have := add_mem (sub_mem hw hw') hr
  convert this using 1; abel

/-- `Ψᵢ(u_∞) = u_∞ ⊗ bᵢ`. -/
theorem psiInf_one [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) :
    psiInf hvt hR hinj hϖ hϖv hk hfund i (mkB hvt hR hinj hϖ hϖv hk hfund []) =
      (mkB hvt hR hinj hϖ hϖv hk hfund [], 0) := by
  obtain ⟨m, P, w₀, -, -, -, hw₀, hw, hwt, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i []
  have hm : m = 0 := by
    have := congrArg (· i) hwt
    simp [wordWeight] at this
    omega
  subst hm
  rw [hpsi, Nat.cast_zero, neg_zero, Prod.mk.injEq, mkB_eq_mkB_iff]
  refine ⟨?_, rfl⟩
  have := add_mem hw₀ (by simpa using hw)
  convert neg_mem this using 1; abel

/-- `Ψᵢ(B(∞)) ⊆ B(∞) × {f̃ᵢⁿ bᵢ | n ≥ 0}`. -/
theorem psiInf_snd_nonpos [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I)
    (b : BInf (D := D) hvt A ϖ) : (psiInf hvt hR hinj hϖ hϖv hk hfund i b).2 ≤ 0 := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨m, P, w₀, hP, hPw, he, hw₀, hw, hwt, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund i w
  rw [hpsi]
  simp

omit [Finite I] [IsDomain A] [IsDiscreteValuationRing A] hinj hϖ hϖv hk hfund in
/-- `ẽᵢ* P = 0` if `e''ᵢ P = 0`. -/
lemma kEs_eq_zero (i : I) {P : Um D v}
    (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0) :
    kEs hvt i P = 0 := by
  rw [kEs_apply]
  have : kE hvt i (starU D v P) = 0 :=
    BosonModule.eTilde_of_ker (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) i)
      (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
      (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) he
  rw [this, map_zero]

/-- For `b ≠ u_∞` there is `i` with `Ψᵢ(b) = b₀ ⊗ f̃ᵢⁿ bᵢ`, `n > 0`: take the first letter `i` of
a word for `b*`, so that `ẽᵢ* b ≠ 0`. -/
theorem exists_psiInf_snd_neg [IsFormallyReal (A ⧸ Ideal.span {ϖ})]
    (b : BInf (D := D) hvt A ϖ) (hb : b ≠ mkB hvt hR hinj hϖ hϖv hk hfund []) :
    ∃ i, (psiInf hvt hR hinj hϖ hϖv hk hfund i b).2 < 0 := by
  obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
  obtain ⟨w', hw'⟩ := exists_fWi_sub_starU_mem (hR := hR) hinj hϖ hϖv hk hfund (D := D) (A := A) w
  cases w' with
  | nil =>
    exfalso
    apply hb
    rw [mkB_eq_mkB_iff]
    have h1 : starU D v (fWi (D := D) hvt []) = fWi hvt [] := by
      change starU D v (Submodule.Quotient.mk 1) = Submodule.Quotient.mk 1
      rw [starU_mk, rev_one]
    rwa [h1] at hw'
  | cons j w'' =>
    refine ⟨j, ?_⟩
    obtain ⟨m, P, w₀, -, -, he, -, hw, -, hpsi⟩ := psiInf_spec hinj hϖ hϖv hk hfund j w
    rw [hpsi]
    suffices hm : m ≠ 0 by simp only [Left.neg_neg_iff, Nat.cast_pos]; omega
    rintro rfl
    have hc : fWi (D := D) hvt (j :: w'') = kF hvt j (fWi hvt w'') := rfl
    have h1 := kEs_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund j hw'
    rw [map_sub, kEs_apply (u := starU D v _), starU_starU, hc, kE_kF] at h1
    have h2 := kEs_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund j hw
    rw [map_sub, rmulF_zero, kEs_eq_zero j he, sub_zero] at h2
    have h3 : starU D v (fWi (D := D) hvt w'') ∈ ϖ • latInf hvt A := by
      simpa using sub_mem h2 h1
    have h4 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h3
    rw [starU_starU] at h4
    exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w'' h4

end Base

end GrandLoop

end LieLean.QuantumGroup
