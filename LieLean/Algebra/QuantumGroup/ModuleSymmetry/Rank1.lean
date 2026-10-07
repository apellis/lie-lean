/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Strings
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.DirectSum.Module

/-!
# The symmetries of an integrable `U_q(𝔰𝔩₂)`-module

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module (`QuantumGroup.IntegrableSl2`, [Lus] 5.1.1) over a field
`k`, with `q` nonzero and not a root of unity, and let `t ∈ k` be nonzero with
`[n, j]_t = [n, j]_q` for all `n, j` (e.g. `t = q` or `t = q⁻¹`). Following [Lus] 5.2.1 we define
the symmetry `T = T''_t : M → M` by
`T(m) = Σ_{-a+b-c=n} (-1)^b t^{b-ac} E^{(a)} F^{(b)} E^{(c)} m` for `m ∈ Mⁿ`
(`QuantumGroup.IntegrableSl2.T`); for `t = v^e` this is Lusztig's `T''_{i,e}`, and the same
construction applied to the module with `E` and `F` interchanged (`IntegrableSl2.flip`) is
Lusztig's `T'_{i,e}`.

## Main results

* `IntegrableSl2.T_dF_of_primitive`: for `η ∈ Mᵖ` with `E η = 0` and `j + h = p`,
  `T(F^{(j)} η) = (-1)^h t^{h(j+1)} F^{(h)} η` (the analogue of [Lus] 5.2.2 for `T''` on
  `F`-strings, by the `q`-binomial identities of `QuantumGroup.QBinomialSeries`);
* `IntegrableSl2.flip_T_inv_T`, `IntegrableSl2.T_flip_T_inv`, `IntegrableSl2.symmEquiv`:
  `T''_{t}` and `T'_{t⁻¹}` are mutually inverse ([Lus] 5.2.3(a));
* `IntegrableSl2.T_eq_zpow_smul_flip_T`: `T''_t = (-t)ⁿ T'_t` on `Mⁿ` ([Lus] 5.2.3(b));
* `IntegrableSl2.T_E`, `IntegrableSl2.T_F`: `T(E m) = -t^{-n} F T(m)` and
  `T(F m) = -t^{n-2} E T(m)` for `m ∈ Mⁿ` (cf. [Lus] 5.2.4);
* `IntegrableSl2.T_mem`: `T` maps `Mⁿ` to `M⁻ⁿ`;
* `IntegrableSl2.map_T`: `T` is natural for linear maps commuting with `E`, `F` and the gradings.

The string formula is proved directly from the definition; the other statements follow because
every weight vector is a sum of vectors `F^{(j)} η` (`IntegrableSl2.mem_strings`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §5.2.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §8.2–8.3.
-/

open Finset

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M)

/-! ### Definition -/

/-- The term `(-1)^b t^{b-ac} E^{(a)} F^{(b)} E^{(c)}` of `T` on `Mⁿ`, where `b = n + a + c`
(and the term is zero if `n + a + c < 0`). -/
noncomputable def symmTerm (t : k) (n : ℤ) (a c : ℕ) : Module.End k M :=
  if 0 ≤ n + a + c then
    ((-1) ^ (n + a + c).toNat * t ^ (n + a + c).toNat * t⁻¹ ^ (a * c)) •
      (V.dE a * V.dF (n + a + c).toNat * V.dE c)
  else 0

lemma symmTerm_apply (t : k) (n : ℤ) (a c : ℕ) (m : M) :
    V.symmTerm t n a c m = if 0 ≤ n + a + c then
      ((-1) ^ (n + a + c).toNat * t ^ (n + a + c).toNat * t⁻¹ ^ (a * c)) •
        V.dE a (V.dF (n + a + c).toNat (V.dE c m)) else 0 := by
  unfold symmTerm
  split_ifs <;> rfl

lemma pow_apply_eq_zero_of_le {f : Module.End k M} {x : M} {N b : ℕ} (h : (f ^ N) x = 0)
    (hb : N ≤ b) : (f ^ b) x = 0 := by
  rw [← Nat.sub_add_cancel hb, pow_add, Module.End.mul_apply, h, map_zero]

variable {V}

lemma dE_eq_zero_of_le {x : M} {N b : ℕ} (h : (V.E ^ N) x = 0) (hb : N ≤ b) : V.dE b x = 0 := by
  rw [dE_apply, pow_apply_eq_zero_of_le h hb, smul_zero]

lemma dF_eq_zero_of_le {x : M} {N b : ℕ} (h : (V.F ^ N) x = 0) (hb : N ≤ b) : V.dF b x = 0 := by
  rw [dF_apply, pow_apply_eq_zero_of_le h hb, smul_zero]

variable (V)

lemma hasFiniteSupport_symmTerm (t : k) (n : ℤ) (m : M) :
    (Function.support fun ac : ℕ × ℕ ↦ V.symmTerm t n ac.1 ac.2 m).Finite := by
  obtain ⟨N, hN⟩ := V.exists_E_pow_eq_zero m
  choose B hB using fun c : ℕ ↦ V.exists_F_pow_eq_zero ((V.E ^ c) m)
  set A := (∑ c ∈ range N, B c) + n.natAbs
  refine (Set.Finite.subset (range A ×ˢ range N).finite_toSet) ?_
  intro ⟨a, c⟩ hac
  by_contra hnot
  apply hac
  simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, not_and_or, not_lt] at hnot
  simp only [symmTerm_apply]
  split_ifs with h
  swap
  · rfl
  rcases hnot with ha | hc
  · rcases le_or_gt N c with hc | hc
    · rw [dE_eq_zero_of_le hN hc, map_zero, map_zero, smul_zero]
    have hBc : B c ≤ ∑ c ∈ range N, B c := single_le_sum (by simp) (mem_range.2 hc)
    have hb : B c ≤ (n + a + c).toNat := by omega
    rw [dE_apply c m, map_smul, dF_eq_zero_of_le (hB c) hb, smul_zero, map_zero, smul_zero]
  · rw [dE_eq_zero_of_le hN hc, map_zero, map_zero, smul_zero]

/-- `T` on `Mⁿ`, as a linear map on `M` (it is only meaningful on `Mⁿ`). -/
noncomputable def symmWt (t : k) (n : ℤ) : M →ₗ[k] M where
  toFun m := ∑ᶠ ac : ℕ × ℕ, V.symmTerm t n ac.1 ac.2 m
  map_add' x y := by
    simp only [map_add]
    exact finsum_add_distrib (V.hasFiniteSupport_symmTerm t n x)
      (V.hasFiniteSupport_symmTerm t n y)
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (V.hasFiniteSupport_symmTerm t n x)).symm

lemma isInternal : DirectSum.IsInternal V.wt :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top V.iSupIndep_wt V.iSup_wt

/-- The decomposition `M ≅ ⊕ₙ Mⁿ`. -/
noncomputable def decompose :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap V.wt) V.isInternal).symm

lemma decompose_of_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    V.decompose m = DirectSum.of (fun n ↦ V.wt n) n ⟨m, hm⟩ := by
  rw [decompose, LinearEquiv.symm_apply_eq]
  exact (DirectSum.coeLinearMap_of (A := V.wt) n ⟨m, hm⟩).symm

/-- The symmetry `T''_t` of [Lus] 5.2.1: on `Mⁿ` it is
`Σ_{-a+b-c=n} (-1)^b t^{b-ac} E^{(a)} F^{(b)} E^{(c)}`. -/
noncomputable def T (t : k) : Module.End k M :=
  DirectSum.toModule k ℤ M (fun n ↦ V.symmWt t n ∘ₗ (V.wt n).subtype) ∘ₗ
    V.decompose.toLinearMap

lemma T_of_mem (t : k) {n : ℤ} {m : M} (hm : m ∈ V.wt n) : V.T t m = V.symmWt t n m := by
  rw [T, LinearMap.comp_apply, LinearEquiv.coe_coe, decompose_of_mem V hm,
    ← DirectSum.lof_eq_of k, DirectSum.toModule_lof]
  rfl

lemma T_of_mem' (t : k) {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    V.T t m = ∑ᶠ ac : ℕ × ℕ, V.symmTerm t n ac.1 ac.2 m :=
  V.T_of_mem t hm

/-- Linear maps agreeing on all weight vectors are equal. -/
lemma ext_wt {N : Type*} [AddCommGroup N] [Module k N] {f g : M →ₗ[k] N}
    (h : ∀ n, ∀ m ∈ V.wt n, f m = g m) : f = g := by
  have : ⊤ ≤ LinearMap.eqLocus f g := V.iSup_wt ▸ iSup_le fun n m hm ↦ h n m hm
  ext m
  exact this Submodule.mem_top

/-- `T` maps `Mⁿ` to `M⁻ⁿ`. -/
theorem T_mem (t : k) {n : ℤ} {m : M} (hm : m ∈ V.wt n) : V.T t m ∈ V.wt (-n) := by
  rw [T_of_mem' V t hm, finsum_eq_sum _ (V.hasFiniteSupport_symmTerm t n m)]
  refine Submodule.sum_mem _ fun ⟨a, c⟩ _ ↦ ?_
  simp only [symmTerm_apply]
  split_ifs with h
  · refine Submodule.smul_mem _ _ ?_
    have hb : (((n + a + c).toNat : ℕ) : ℤ) = n + a + c := Int.toNat_of_nonneg h
    have := dE_mem (dF_mem (dE_mem hm c) (n + a + c).toNat) a
    rwa [hb, show n + 2 * (c : ℤ) - 2 * (n + a + c) + 2 * a = -n by ring] at this
  · exact zero_mem _

/-- Naturality of `T`: a linear map commuting with `E`, `F` and preserving the gradings
commutes with `T`. -/
theorem map_T {M' : Type*} [AddCommGroup M'] [Module k M'] (V' : IntegrableSl2 q M')
    (f : M →ₗ[k] M') (hE : ∀ m, f (V.E m) = V'.E (f m)) (hF : ∀ m, f (V.F m) = V'.F (f m))
    (hwt : ∀ n, ∀ m ∈ V.wt n, f m ∈ V'.wt n) (t : k) (m : M) :
    f (V.T t m) = V'.T t (f m) := by
  have hpow : ∀ (g : Module.End k M) (g' : Module.End k M'), (∀ m, f (g m) = g' (f m)) →
      ∀ (a : ℕ) m, f ((g ^ a) m) = (g' ^ a) (f m) := by
    intro g g' hg a
    induction a with
    | zero => simp
    | succ a ih => intro m; rw [pow_succ', pow_succ', Module.End.mul_apply,
        Module.End.mul_apply, hg, ih]
  have hdE : ∀ a m, f (V.dE a m) = V'.dE a (f m) := fun a m ↦ by
    rw [dE_apply, dE_apply, map_smul, hpow _ _ hE]
  have hdF : ∀ a m, f (V.dF a m) = V'.dF a (f m) := fun a m ↦ by
    rw [dF_apply, dF_apply, map_smul, hpow _ _ hF]
  have key : ∀ n, ∀ m ∈ V.wt n, f (V.T t m) = V'.T t (f m) := by
    intro n m hm
    rw [T_of_mem' V t hm, T_of_mem' V' t (hwt n m hm),
      map_finsum f (V.hasFiniteSupport_symmTerm t n m)]
    congr 1
    ext ⟨a, c⟩
    simp only [symmTerm_apply]
    split_ifs
    · rw [map_smul, hdE, hdF, hdE]
    · exact map_zero f
  exact LinearMap.congr_fun (V.ext_wt (f := f ∘ₗ V.T t) (g := V'.T t ∘ₗ f) key) m

lemma flip_flip : V.flip.flip = V := by
  cases V
  simp only [flip, neg_neg]

/-! ### Strings -/

variable {V}

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- `F^{(a)} F^{(b)} = [a+b, a] F^{(a+b)}`. -/
lemma dF_dF (a b : ℕ) (m : M) : V.dF a (V.dF b m) = qBinomial q (a + b) a • V.dF (a + b) m := by
  have h := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show a ≤ a + b by omega)
  rw [Nat.add_sub_cancel_left] at h
  have ha := qFactorial_ne_zero_of_pow_ne_one hq0 hq a
  have hb := qFactorial_ne_zero_of_pow_ne_one hq0 hq b
  have hab := qBinomial_ne_zero_of_pow_ne_one hq0 hq (show a ≤ a + b by omega)
  rw [dF_apply, dF_apply, dF_apply, map_smul, ← Module.End.mul_apply, ← pow_add, smul_smul,
    smul_smul, ← h]
  congr 1
  field_simp

/-- Induction over strings: a property of vectors of `Mⁿ` closed under linear combinations holds
as soon as it holds for the vectors `F^{(j)} η` with `η ∈ Mᵖ` primitive, `j ≤ p`, `n = p - 2j`. -/
lemma wt_induction {n : ℤ} {P : M → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : k) x, P x → P (c • x))
    (hgen : ∀ (p j : ℕ) (η : M), j ≤ p → n = p - 2 * j → η ∈ V.wt p → V.E η = 0 →
      P (V.dF j η)) {m : M} (hm : m ∈ V.wt n) : P m := by
  have h := mem_strings (V := V) hq0 hq hm
  rw [strings] at h
  clear hm
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, η, hη, hE, rfl⟩ := hx
    rcases lt_or_ge (n + 2 * j) 0 with hneg | hnn
    · rw [eq_zero_of_primitive_of_neg hq0 hq hη hE hneg, map_zero]
      exact h0
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * j := ⟨_, Int.toNat_of_nonneg hnn⟩
    rw [← hp] at hη
    by_cases hjp : j ≤ p
    · exact hgen p j η hjp (by omega) hη hE
    · rw [dF_eq_zero_of_primitive hq0 hq hη hE (by omega)]
      exact h0
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

/-- Two linear maps agreeing on the vectors `F^{(j)} η` (`η ∈ Mᵖ` primitive, `j ≤ p`,
`n = p - 2j`) agree on `Mⁿ`. -/
lemma eq_on_wt {N : Type*} [AddCommGroup N] [Module k N] (f g : M →ₗ[k] N) {n : ℤ}
    (hgen : ∀ (p j : ℕ) (η : M), j ≤ p → n = p - 2 * j → η ∈ V.wt p → V.E η = 0 →
      f (V.dF j η) = g (V.dF j η)) {m : M} (hm : m ∈ V.wt n) : f m = g m :=
  wt_induction (P := fun m ↦ f m = g m) hq0 hq (by simp)
    (fun x y hx hy ↦ by simp [hx, hy]) (fun c x hx ↦ by simp [hx]) hgen hm

/-- `E^{(c)} F^{(j)} η = 0` for `η ∈ Mᵖ` primitive and `j < c`, `j ≤ p`. -/
lemma dE_dF_eq_zero_of_lt {p : ℕ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0) {j c : ℕ}
    (hjp : j ≤ p) (hjc : j < c) : V.dE c (V.dF j η) = 0 := by
  refine dE_eq_zero_of_le (N := j + 1) ?_ hjc
  have h := dE_dF_of_primitive hq0 hq hη hE (le_refl j) hjp
  rw [Nat.sub_self, dF_zero, dE_apply] at h
  have hf := qFactorial_ne_zero_of_pow_ne_one hq0 hq j
  have h' : (V.E ^ j) (V.dF j η) = (qFactorial q j * qBinomial q (p - j + j) j) • η := by
    rw [mul_smul, ← h, smul_smul, mul_inv_cancel₀ hf, one_smul]
  rw [pow_succ', Module.End.mul_apply, h', map_smul, hE, smul_zero]

/-- `F^{(i)} η = E^{(p-i)} F^{(p)} η` for `η ∈ Mᵖ` primitive and `i ≤ p`: lowest-weight
strings of the flipped module. -/
lemma dF_eq_flip_dF {p : ℕ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0) {i : ℕ} (hi : i ≤ p) :
    V.dF i η = V.flip.dF (p - i) (V.dF p η) := by
  rw [flip_dF, dE_dF_of_primitive hq0 hq hη hE (Nat.sub_le p i) le_rfl,
    show p - p + (p - i) = p - i by omega, qBinomial_self, one_smul, Nat.sub_sub_self hi]

/-- `F^{(p)} η` is primitive in the flipped module, of weight `p`. -/
lemma flip_primitive {p : ℕ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0) :
    V.dF p η ∈ V.flip.wt p ∧ V.flip.E (V.dF p η) = 0 := by
  refine ⟨?_, ?_⟩
  · have := dF_mem hη p
    rw [flip_wt, show -(p : ℤ) = p - 2 * p by ring]
    exact this
  · rw [flip_E, F_dF hq0 hq, dF_eq_zero_of_primitive hq0 hq hη hE (by push_cast; omega),
      smul_zero]

omit hq0 hq in
/-- The `q`-binomial sum giving the coefficient of `T` on strings. -/
lemma sum_symm_coeff {t : k} (ht0 : t ≠ 0) (ht : ∀ n j, qBinomial t n j = qBinomial q n j)
    (h j : ℕ) :
    ∑ a ∈ range (j + 1), ∑ c ∈ range (j + 1), (-t) ^ (h + a + c) * t⁻¹ ^ (a * c) *
      (qBinomial q (h + c) c * qBinomial q (h + a) (j - c) * qBinomial q j a) =
      (-t) ^ h * (-t ^ (h + 1)) ^ j := by
  have inner : ∀ a ∈ range (j + 1), ∑ c ∈ range (j + 1), (-t) ^ (h + a + c) * t⁻¹ ^ (a * c) *
      (qBinomial q (h + c) c * qBinomial q (h + a) (j - c) * qBinomial q j a) =
      qBinomial q j a * (-t) ^ (h + a) * ∑ c ∈ range (j + 1),
        (-1) ^ c * (t * t⁻¹ ^ a) ^ c * qBinomial t (h + c) c * qBinomial t (h + a) (j - c) := by
    intro a _
    rw [mul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [ht, ht, mul_pow, ← pow_mul, pow_add, neg_pow t c]
    ring
  rw [sum_congr rfl inner, sum_eq_single 0]
  · rw [qBinomial_zero_right, pow_zero, mul_one, add_zero, one_mul]
    rw [sum_qBinomial_mul_qBinomial_zero ht0 h j]
  · intro a ha ha0
    rw [sum_qBinomial_mul_qBinomial_eq_zero ht0 h (by omega)
      (by simp only [mem_range] at ha; omega), mul_zero]
  · intro h0
    simp at h0

/-- The string formula: for `η ∈ Mᵖ` with `E η = 0` and `j ≤ p`,
`T(F^{(j)} η) = (-1)^{p-j} t^{(p-j)(j+1)} F^{(p-j)} η` (cf. [Lus] 5.2.2). -/
theorem T_dF_of_primitive {t : k} (ht0 : t ≠ 0) (ht : ∀ n j, qBinomial t n j = qBinomial q n j)
    {p : ℕ} {η : M} (hη : η ∈ V.wt p) (hE : V.E η = 0) {j : ℕ} (hj : j ≤ p) :
    V.T t (V.dF j η) = ((-1) ^ (p - j) * t ^ ((p - j) * (j + 1))) • V.dF (p - j) η := by
  obtain ⟨h, rfl⟩ : ∃ h, p = h + j := ⟨p - j, by omega⟩
  rw [show h + j - j = h by omega]
  set n : ℤ := h - j with hn
  have hm : V.dF j η ∈ V.wt n := by
    have := dF_mem hη j
    rwa [show ((h + j : ℕ) : ℤ) - 2 * j = n by push_cast; ring] at this
  -- each term is a multiple of `F^{(h)} η`
  have hterm : ∀ a ∈ range (j + 1), ∀ c ∈ range (j + 1),
      (-t) ^ j • V.symmTerm t n a c (V.dF j η) = ((-t) ^ (h + a + c) * t⁻¹ ^ (a * c) *
        (qBinomial q (h + c) c * qBinomial q (h + a) (j - c) * qBinomial q j a)) •
          V.dF h η := by
    intro a ha c hc
    simp only [mem_range] at ha hc
    rw [symmTerm_apply]
    split_ifs with hb
    · obtain ⟨b, hb'⟩ : ∃ b : ℕ, (b : ℤ) = n + a + c := ⟨_, Int.toNat_of_nonneg hb⟩
      rw [← hb', Int.toNat_natCast]
      rw [dE_dF_of_primitive hq0 hq hη hE (show c ≤ j by omega) (by omega), map_smul,
        dF_dF hq0 hq, map_smul, map_smul, show b + (j - c) = h + a by omega,
        dE_dF_of_primitive hq0 hq hη hE (show a ≤ h + a by omega) (by omega),
        show h + j - (h + a) + a = j by omega, show h + a - a = h by omega,
        show h + j - j + c = h + c by omega]
      simp only [smul_smul]
      congr 1
      have hbsymm : qBinomial q (h + a) b = qBinomial q (h + a) (j - c) := by
        rw [show b = h + a - (j - c) by omega, qBinomial_symm q (by omega)]
      rw [hbsymm, show h + a + c = b + j by omega, pow_add, neg_pow t b]
      ring
    · rw [smul_zero, qBinomial_eq_zero_of_lt q (show h + a < j - c by omega), mul_zero,
        zero_mul, mul_zero, zero_smul]
  -- the support of the sum
  have hsupp : (Function.support fun ac : ℕ × ℕ ↦ V.symmTerm t n ac.1 ac.2 (V.dF j η)) ⊆
      ↑(range (j + 1) ×ˢ range (j + 1)) := by
    intro ⟨a, c⟩ hac
    by_contra hnot
    apply hac
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, not_and_or, not_lt] at hnot
    simp only [symmTerm_apply]
    split_ifs with hb
    swap
    · rfl
    rcases le_or_gt (j + 1) c with hc | hc
    · rw [dE_dF_eq_zero_of_lt hq0 hq hη hE (by omega) (by omega), map_zero, map_zero, smul_zero]
    have ha : j + 1 ≤ a := by omega
    rw [dE_dF_of_primitive hq0 hq hη hE (show c ≤ j by omega) (by omega), map_smul, dF_dF hq0 hq,
      dF_eq_zero_of_primitive hq0 hq hη hE (by push_cast; omega), smul_zero, smul_zero,
      map_zero, smul_zero]
  have hsum : (-t) ^ j • V.T t (V.dF j η) = ((-t) ^ h * (-t ^ (h + 1)) ^ j) • V.dF h η := by
    rw [T_of_mem' V t hm, finsum_eq_sum_of_support_subset _ hsupp, smul_sum, sum_product,
      ← sum_symm_coeff ht0 ht h j, sum_smul]
    refine sum_congr rfl fun a ha ↦ ?_
    rw [sum_smul]
    exact sum_congr rfl fun c hc ↦ hterm a ha c hc
  have hne : (-t) ^ j ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 ht0)
  apply smul_right_injective M hne
  simp only
  rw [hsum, smul_smul]
  congr 1
  rw [neg_pow t h, neg_pow t j, neg_pow (t ^ (h + 1)) j]
  ring

/-! ### Consequences -/

section Consequences

variable {t : k} (ht0 : t ≠ 0) (ht : ∀ n j, qBinomial t n j = qBinomial q n j)
include ht0 ht

omit hq0 hq ht0 in
lemma qBinomial_inv_eq (n j : ℕ) : qBinomial t⁻¹ n j = qBinomial q n j := by
  rw [qBinomial_inv, ht]

/-- `T'_{t⁻¹} T''_t = 1` ([Lus] 5.2.3(a)). -/
theorem flip_T_inv_T (m : M) : V.flip.T t⁻¹ (V.T t m) = m := by
  have ht' := qBinomial_inv_eq ht
  have key := V.ext_wt (f := V.flip.T t⁻¹ ∘ₗ V.T t) (g := LinearMap.id) fun n m hm ↦
    eq_on_wt hq0 hq (V.flip.T t⁻¹ ∘ₗ V.T t) LinearMap.id (fun p j η hj _ hη hE ↦ by
      obtain ⟨hη', hE'⟩ := flip_primitive hq0 hq hη hE
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [T_dF_of_primitive hq0 hq ht0 ht hη hE hj, map_smul,
        dF_eq_flip_dF hq0 hq hη hE (Nat.sub_le p j), Nat.sub_sub_self hj,
        T_dF_of_primitive (V := V.flip) hq0 hq (inv_ne_zero ht0) ht' hη' hE' hj,
        ← dF_eq_flip_dF hq0 hq hη hE hj, smul_smul]
      conv_rhs => rw [← one_smul k (V.dF j η)]
      congr 1
      rw [inv_pow, ← mul_assoc, mul_right_comm _ _ ((-1) ^ (p - j)), ← pow_add,
        ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, mul_inv_cancel₀ (pow_ne_zero _ ht0)])
      hm
  exact LinearMap.congr_fun key m

/-- `T''_t T'_{t⁻¹} = 1` ([Lus] 5.2.3(a)). -/
theorem T_flip_T_inv (m : M) : V.T t (V.flip.T t⁻¹ m) = m := by
  have := flip_T_inv_T (V := V.flip) hq0 hq (inv_ne_zero ht0) (qBinomial_inv_eq ht) m
  rwa [flip_flip, inv_inv] at this

variable (V) in
/-- `T''_t` as a linear automorphism of `M`, with inverse `T'_{t⁻¹}`. -/
noncomputable def symmEquiv : M ≃ₗ[k] M where
  toFun := V.T t
  invFun := V.flip.T t⁻¹
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv := flip_T_inv_T hq0 hq ht0 ht
  right_inv := T_flip_T_inv hq0 hq ht0 ht

@[simp] lemma symmEquiv_apply (m : M) : V.symmEquiv hq0 hq ht0 ht m = V.T t m := rfl

@[simp] lemma symmEquiv_symm_apply (m : M) :
    (V.symmEquiv hq0 hq ht0 ht).symm m = V.flip.T t⁻¹ m := rfl

/-- `T''_t = (-t)ⁿ T'_t` on `Mⁿ` ([Lus] 5.2.3(b)). -/
theorem T_eq_zpow_smul_flip_T {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    V.T t m = (-t) ^ n • V.flip.T t m :=
  eq_on_wt hq0 hq (V.T t) ((-t) ^ n • V.flip.T t) (fun p j η hj hn hη hE ↦ by
    obtain ⟨hη', hE'⟩ := flip_primitive hq0 hq hη hE
    rw [LinearMap.smul_apply, T_dF_of_primitive hq0 hq ht0 ht hη hE hj,
      dF_eq_flip_dF hq0 hq hη hE hj,
      T_dF_of_primitive (V := V.flip) hq0 hq ht0 ht hη' hE' (Nat.sub_le p j),
      Nat.sub_sub_self hj, smul_smul]
    have e : V.flip.dF j (V.dF p η) = V.dF (p - j) η := by
      rw [dF_eq_flip_dF hq0 hq hη hE (Nat.sub_le p j), Nat.sub_sub_self hj]
    rw [e]
    congr 1
    obtain ⟨h, rfl⟩ : ∃ h, p = h + j := ⟨p - j, by omega⟩
    rw [show h + j - j = h by omega, hn, show ((h + j : ℕ) : ℤ) - 2 * j = (h : ℤ) - (j : ℤ) by
      push_cast; ring, zpow_sub₀ (neg_ne_zero.2 ht0), zpow_natCast, zpow_natCast]
    have hne : (-t) ^ j ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 ht0)
    field_simp
    rw [neg_pow t, neg_pow t]
    ring) hm

/-- `T(E m) = -t^{-n} F T(m)` for `m ∈ Mⁿ`. -/
theorem T_E {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    V.T t (V.E m) = -(t ^ (-n)) • V.F (V.T t m) :=
  eq_on_wt hq0 hq (V.T t ∘ₗ V.E) (-(t ^ (-n)) • (V.F ∘ₗ V.T t)) (fun p j η hj hn hη hE ↦ by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rcases j with _ | j
    · rw [T_dF_of_primitive hq0 hq ht0 ht hη hE hj, Nat.sub_zero, dF_zero, hE, map_zero,
        map_smul, F_dF hq0 hq, dF_eq_zero_of_primitive hq0 hq hη hE (by push_cast; omega),
        smul_zero, smul_zero, smul_zero]
    obtain ⟨h, rfl⟩ : ∃ h, p = h + 1 + j := ⟨p - j - 1, by omega⟩
    have hηp : η ∈ V.wt ((h + 1 + j : ℕ) : ℤ) := hη
    rw [E_dF_succ_of_primitive hq0 hq hηp hE j, map_smul,
      T_dF_of_primitive hq0 hq ht0 ht hη hE (j := j) (by omega),
      T_dF_of_primitive hq0 hq ht0 ht hη hE hj,
      show h + 1 + j - j = h + 1 by omega, show h + 1 + j - (j + 1) = h by omega]
    simp only [map_smul]
    rw [F_dF hq0 hq]
    simp only [smul_smul]
    rw [show ((h + 1 + j : ℕ) : ℤ) - j = ((h + 1 : ℕ) : ℤ) by push_cast; ring,
      qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 hq)]
    congr 1
    rw [hn, show -(((h + 1 + j : ℕ) : ℤ) - 2 * ((j + 1 : ℕ) : ℤ)) = ((j + 1 : ℕ) : ℤ) - (h : ℕ) by
      push_cast; ring, zpow_sub₀ ht0, zpow_natCast, zpow_natCast]
    have hne : t ^ h ≠ 0 := pow_ne_zero _ ht0
    field_simp
    ring) hm

/-- `T(F m) = -t^{n-2} E T(m)` for `m ∈ Mⁿ`. -/
theorem T_F {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    V.T t (V.F m) = -(t ^ (n - 2)) • V.E (V.T t m) :=
  eq_on_wt hq0 hq (V.T t ∘ₗ V.F) (-(t ^ (n - 2)) • (V.E ∘ₗ V.T t)) (fun p j η hj hn hη hE ↦ by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [F_dF hq0 hq, map_smul, T_dF_of_primitive hq0 hq ht0 ht hη hE hj]
    simp only [map_smul]
    rcases eq_or_lt_of_le hj with rfl | hjp
    · rw [dF_eq_zero_of_primitive hq0 hq hη hE (by push_cast; omega), map_zero, smul_zero,
        Nat.sub_self, dF_zero, hE, smul_zero, smul_zero]
    obtain ⟨h, rfl⟩ : ∃ h, p = h + 1 + j := ⟨p - j - 1, by omega⟩
    have hηp : η ∈ V.wt ((h + 1 + j : ℕ) : ℤ) := hη
    rw [T_dF_of_primitive hq0 hq ht0 ht hη hE (j := j + 1) (by omega),
      show h + 1 + j - j = h + 1 by omega, show h + 1 + j - (j + 1) = h by omega,
      E_dF_succ_of_primitive hq0 hq hηp hE h]
    simp only [smul_smul]
    rw [show ((h + 1 + j : ℕ) : ℤ) - h = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
      qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 hq)]
    congr 1
    rw [hn, show ((h + 1 + j : ℕ) : ℤ) - 2 * (j : ℤ) - 2 = (h : ℕ) - ((j + 1 : ℕ) : ℤ) by
      push_cast; ring, zpow_sub₀ ht0, zpow_natCast, zpow_natCast]
    have hne : t ^ (j + 1) ≠ 0 := pow_ne_zero _ ht0
    field_simp
    ring) hm

end Consequences

end IntegrableSl2

end LieLean.QuantumGroup
