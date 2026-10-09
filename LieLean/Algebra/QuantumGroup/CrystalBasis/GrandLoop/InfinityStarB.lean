/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinitySlice

/-!
# `B(∞)* = B(∞)`

Assume `A/ϖA` is formally real. For `P ∈ L(∞)` with `e''ᵢ P = 0` and `P ≡ b ∈ B(∞)`, the element
`P fᵢ^{(m)}` is congruent to an element of `B(∞)` (`GrandLoop.rmulF_sub_mem_of_sub_mem`;
[Kas93a] Prop. 2.1.2). Hence `B(∞)* = B(∞)` (`GrandLoop.starU_fWi_sub_mem`; [Kas93a] Thm. 2.1.1).

The printed proof of [Kas93a] Prop. 2.1.2 uses `B(∞)* ⊆ B(∞) ∪ -B(∞)` ([Kas91] Cor. 6.1.2,
proved with `ℤ`-forms), and `P u_λ ∈ B(λ)` for `⟨hᵢ, λ⟩ = 0`, `⟨hⱼ, λ⟩ ≫ 0`, which rests on the
global bases of [Kas91]. We use instead:

* the embedding `T = Φ ∘ π_{μ+λ} : U⁻ → V(μ) ⊗ V(λ)`, injective modulo `ϖ` on `L(∞)` for `μ`
  large (`GrandLoop.mem_smul_latInf_of_tensorEmb_mem`, from `Ψ ∘ Φ = 1` and [HK] Lemma 5.3.15);
* the slice `(z, ·) ⊗ 1`, `z = fᵢ^{(m)} v_μ`, which sends `T(P fᵢ^{(m)})` to `(z, z) P v_λ`
  (`GrandLoop.prL_tensorEmb_ev_mul_θ_pow`), and `T(b) ≡ b₁ ⊗ b₂` to `(z, b₁) b₂`;
* `π_λ(P) ∉ ϖ L(λ)` (`GrandLoop.evq_notMem_smul_lat`), the linear independence of `B(λ)`, the
  orthonormality of `B(∞)` and formal reality.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516.
* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858, §2.1.
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise TensorProduct LusztigF

noncomputable section

namespace LieLean.QuantumGroup

lemma qInt_inv {k : Type*} [Field k] (q : k) (n : ℕ) : qInt q⁻¹ n = qInt q n := by
  unfold qInt
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs := Finset.mem_range.1 hs
  rw [inv_inv, show n - 1 - (n - 1 - s) = s by omega, mul_comm]

lemma qFactorial_inv {k : Type*} [Field k] (q : k) (n : ℕ) :
    qFactorial q⁻¹ n = qFactorial q n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qFactorial, qFactorial, ih, qInt_inv]

namespace GrandLoop

open VermaModule TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

omit [CharZero k] [NeZero v] in
/-- A dominant weight with `⟨i, λ⟩ = 0` and `⟨j, λ⟩ ≥ N` for `j ≠ i`. -/
lemma exists_dom_wall [Finite I]
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0) (i : I)
    (N : ℕ) : ∃ Λ : Dom R, Λ.1 (R.coroot i) = 0 ∧ ∀ j, j ≠ i → (N : ℤ) ≤ Λ.1 (R.coroot j) := by
  classical
  have := Fintype.ofFinite I
  choose Λf hΛf using hfund
  refine ⟨⟨(N : ℤ) • ∑ j ∈ Finset.univ.erase i, (Λf j).1, fun l ↦ ?_⟩, ?_, fun j hj ↦ ?_⟩
  · rw [AddMonoidHom.smul_apply, AddMonoidHom.finsetSum_apply]
    exact smul_nonneg (by positivity) (Finset.sum_nonneg fun j _ ↦ (Λf j).2 l)
  · change ((N : ℤ) • ∑ j ∈ Finset.univ.erase i, (Λf j).1) (R.coroot i) = 0
    rw [AddMonoidHom.smul_apply, AddMonoidHom.finsetSum_apply]
    simp only [hΛf]
    rw [Finset.sum_eq_zero fun j hj ↦ ite_eq_right (Finset.ne_of_mem_erase hj).symm, smul_zero]
  · change (N : ℤ) ≤ ((N : ℤ) • ∑ j ∈ Finset.univ.erase i, (Λf j).1) (R.coroot j)
    rw [AddMonoidHom.smul_apply, AddMonoidHom.finsetSum_apply]
    simp only [hΛf]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), smul_eq_mul,
      mul_one]

/-! ### Right multiplication by `fᵢ^{(m)}` -/

variable (hvt) in
/-- `u ↦ u fᵢ^{(m)}` on `ker e''ᵢ`, as `* ∘ fᵢ^{(m)} ∘ *`. -/
def rmulF (i : I) (m : ℕ) : Module.End k (Um D v) :=
  starU D v ∘ₗ (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df m ∘ₗ starU D v

lemma rmulF_apply (i : I) (m : ℕ) (u : Um D v) :
    rmulF hvt i m u = starU D v ((bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df m
      (starU D v u)) := rfl

@[simp] lemma rmulF_zero (i : I) (u : Um D v) : rmulF hvt i 0 u = u := by
  simp [rmulF_apply]

lemma rmulF_mk (i : I) (m : ℕ) (y : LusztigF k I) :
    rmulF hvt i m (Submodule.Quotient.mk y : Um D v) =
      (qFactorial (v ^ D.d i)⁻¹ m)⁻¹ • Submodule.Quotient.mk (y * θ k i ^ m) := by
  have hpow : ∀ m : ℕ, rev k I (θ k i ^ m) = θ k i ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, rev_mul, ih, rev_θ, ← pow_succ', pow_succ]
  rw [rmulF_apply, starU_mk, BosonModule.df_apply, map_smul]
  change (qFactorial (v ^ D.d i)⁻¹ m)⁻¹ •
    starU D v ((NegativePart.f D v i ^ m) (Submodule.Quotient.mk (rev k I y))) = _
  rw [f_pow_mk, starU_mk, rev_mul, hpow, rev_rev]

lemma kF_pow_eq_df (i : I) {x : Um D v}
    (hx : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e x = 0) (m : ℕ) :
    (kF hvt i ^ m) x = (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df m x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    exact BosonModule.fTilde_df (NegativePart.pow_d_ne_zero (D := D) (NeZero.ne v) i)
      (NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i) hx m

lemma rmulF_mem_Uw (i : I) (m : ℕ) {ν : I →₀ ℕ} {P : Um D v} (hP : P ∈ Uw D v ν) :
    rmulF hvt i m P ∈ Uw D v (ν + m • Finsupp.single i 1) := by
  obtain ⟨y, hy, rfl⟩ := hP
  change rmulF hvt i m (Submodule.Quotient.mk y) ∈ _
  rw [rmulF_mk]
  refine Submodule.smul_mem _ _ ⟨y * θ k i ^ m, mul_mem_weightSpace hy ?_, rfl⟩
  clear hy
  induction m with
  | zero => simpa using one_mem_weightSpace
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_weightSpace ih (θ_mem_weightSpace i)

omit [CharZero k] [DecidableEq I] [NeZero v] in
lemma wordWeight_replicate (i : I) (m : ℕ) :
    wordWeight (List.replicate m i) = m • Finsupp.single i 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, wordWeight_cons, ih, succ_nsmul, add_comm]

/-- `f̃ᵢ^m v_μ = Fᵢ^{(m)} v_μ`. -/
lemma fW_replicate (μ : Dom R) (i : I) (m : ℕ) :
    fW hvt hR μ (List.replicate m i) = dFV (hvt := hvt) (hR := hR) μ i m
      (IrreducibleModule.hwv R v μ.1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, fW_cons, ih]
    exact kashiwaraF_dF (mem_nodeWt_of_mem (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v)
      (Λ := μ.1))) (IrreducibleModule.E_smul_hwv (R := R) (v := v) (Λ := μ.1) i) m

/-- `Fᵢ^m v_μ = [m]ᵢ! f̃ᵢ^m v_μ`. -/
lemma F_pow_smul_hwv_eq (μ : Dom R) (i : I) (m : ℕ) :
    F R v i ^ m • IrreducibleModule.hwv R v μ.1 =
      qFactorial (v ^ D.d i) m • fW hvt hR μ (List.replicate m i) := by
  rw [fW_replicate, IntegrableSl2.dF_apply, smul_smul,
    mul_inv_cancel₀ (qFactorial_ne_zero_of_not_root (NeZero.ne v)
      (pow_ne_one_of_transcendental' hvt) i m), one_smul]
  change _ = (act R v _ (F R v i) ^ m) _
  rw [← map_pow]
  rfl

lemma kF_mem_smul_latInf (i : I) {u : Um D v} (hu : u ∈ ϖ • latInf hvt A) :
    kF hvt i u ∈ ϖ • latInf hvt A :=
  LinearMap.map_mem_smul_of_mem ϖ (fun _ hm ↦ kashiwaraF_mem_latInf' i _ hm) hu

lemma comp_eq_comp_zero_kE_pow (i : I) (r : ℕ) (u : Um D v) :
    comp (D := D) hvt i r u = comp hvt i 0 ((kE hvt i ^ r) u) := by
  induction r generalizing u with
  | zero => simp
  | succ r ih => rw [pow_succ, Module.End.mul_apply, ← ih, comp_kE]

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
lemma rmulF_mem_latInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (m : ℕ) {P : Um D v}
    (hP : P ∈ latInf hvt A)
    (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0) :
    rmulF hvt i m P ∈ latInf hvt A := by
  have hP' := starU_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund hP
  have key : ∀ m : ℕ, (kF hvt i ^ m) (starU D v P) ∈ latInf hvt A := by
    intro m
    induction m with
    | zero => simpa using hP'
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact kashiwaraF_mem_latInf' i _ ih
  rw [rmulF_apply, ← kF_pow_eq_df (hvt := hvt) i he]
  exact starU_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund (key m)

include hR in
lemma rmulF_mem_smul_latInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (m : ℕ)
    {P : Um D v} (hP : P ∈ ϖ • latInf hvt A)
    (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0) :
    rmulF hvt i m P ∈ ϖ • latInf hvt A := by
  obtain ⟨P', hP', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hP
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have he' : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P') = 0 := by
    rw [← algebraMap_smul k, map_smul, map_smul] at he
    exact (smul_eq_zero.1 he).resolve_left hϖ0
  rw [← algebraMap_smul k, map_smul, algebraMap_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _
    (rmulF_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i m hP' he')

include hR in
/-- **Expansion in `B(∞)`**: `Q ∈ L(∞) ∩ U⁻_{-ν}` is congruent modulo `ϖ L(∞)` to
`Σ_{s ∈ S} aₛ f̃ₛ 1` over pairwise distinct classes, and `(Q, Q) ≡ Σ aₛ²`. -/
theorem exists_sum_fWi [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {ν : I →₀ ℕ} {Q : Um D v}
    (hQ : Q ∈ latInf hvt A) (hQw : Q ∈ Uw D v ν) :
    ∃ (S : Finset (List I)) (a : List I → A), (∀ s ∈ S, wordWeight s = ν) ∧
      (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → fWi (D := D) hvt s₁ - fWi hvt s₂ ∉ ϖ • latInf hvt A) ∧
      Q - ∑ s ∈ S, a s • fWi (D := D) hvt s ∈ ϖ • latInf hvt A ∧
      ∃ t : A, formU (pow_ne_one_of_transcendental' hvt) Q Q =
        algebraMap A k (∑ s ∈ S, a s ^ 2) + algebraMap A k (ϖ * t) := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨c, hcs, hc⟩ := (Finsupp.mem_span_image_iff_linearCombination A).1
    (mem_span_fWi_of_mem hQ hQw)
  set W := c.support
  obtain ⟨S, hSW, hSd, hcov⟩ := exists_reps_mod (ϖ • latInf hvt A) (fWi (D := D) hvt) W
  choose! r hrS hr using hcov
  obtain ⟨a, ha⟩ : ∃ a : List I → A, ∀ s, a s = ∑ w ∈ W with r w = s, c w := ⟨_, fun _ ↦ rfl⟩
  have hSw : ∀ s ∈ S, wordWeight s = ν := fun s hs ↦ hcs (hSW hs)
  set y : Um D v := ∑ s ∈ S, a s • fWi (D := D) hvt s with hy
  have hy' : y = ∑ w ∈ W, c w • fWi (D := D) hvt (r w) := by
    rw [hy, ← Finset.sum_fiberwise_of_maps_to (g := r) (t := S) hrS]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ha, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [(Finset.mem_filter.1 hw).2]
  have hxy : Q - y ∈ ϖ • latInf hvt A := by
    rw [hy', ← hc, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun w hw ↦ ?_
    rw [← smul_sub]
    exact Submodule.smul_mem _ _ (hr w hw)
  have hyL : y ∈ latInf hvt A := by
    rw [hy]
    exact Submodule.sum_mem _ fun s _ ↦
      Submodule.smul_mem _ _ (NegativePart.fWord_mem_latticeInf _ _ s)
  refine ⟨S, a, hSw, hSd, hxy, ?_⟩
  -- `(Q, Q) ≡ (y, y)`
  obtain ⟨t₁, ht₁⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund hQ hxy
  obtain ⟨t₂, ht₂⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund hyL hxy
  have hxy' : formU hv' Q Q - formU hv' y y = algebraMap A k (ϖ * (t₁ + t₂)) := by
    have : formU hv' Q Q - formU hv' y y = formU hv' Q (Q - y) + formU hv' y (Q - y) := by
      rw [map_sub, map_sub, formU_comm hv' y Q]; ring
    rw [this, ht₁, ht₂, ← map_add, mul_add]
  choose e he using fun s s' ↦
    formU_fWi_fWi (hR := hR) (A := A) (D := D) hinj hϖ hϖv hk hfund s s'
  have hexp : formU hv' y y = ∑ s ∈ S, ∑ s' ∈ S, algebraMap A k (a s) *
      (algebraMap A k (a s') * formU hv' (fWi (D := D) hvt s) (fWi hvt s')) := by
    rw [hy]
    simp only [map_sum, LinearMap.sum_apply, ← algebraMap_smul k (a _), map_smul,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [formU_comm hv']
  have key : ∀ s ∈ S, ∀ s' ∈ S, algebraMap A k (a s) *
      (algebraMap A k (a s') * formU hv' (fWi (D := D) hvt s) (fWi hvt s')) =
      (if s = s' then algebraMap A k (a s ^ 2) else 0) +
        algebraMap A k (ϖ * (a s * a s' * e s s')) := by
    intro s hs s' hs'
    rw [he]
    by_cases h : s = s'
    · subst h
      simp only [sub_self, zero_mem, ↓reduceIte, map_mul, map_pow]
      ring
    · rw [ite_eq_right_iff.2 (fun h' ↦ absurd h' (hSd s hs s' hs' h))]
      simp only [h, ↓reduceIte, map_mul]
      ring
  have hyy : formU hv' y y = algebraMap A k (∑ s ∈ S, a s ^ 2) +
      algebraMap A k (ϖ * ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s') := by
    rw [hexp, Finset.sum_congr rfl fun s hs ↦ Finset.sum_congr rfl fun s' hs' ↦ key s hs s' hs']
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, map_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s hs ↦ by simp [hs]
  refine ⟨t₁ + t₂ + ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s', ?_⟩
  rw [show formU hv' Q Q = (formU hv' Q Q - formU hv' y y) + formU hv' y y by ring, hxy', hyy]
  simp only [map_add, map_mul]
  ring

set_option maxHeartbeats 1600000 in
-- one long argument with many local lattice computations
include hR in
/-- **[Kas93a] Prop. 2.1.2**: if `A/ϖA` is formally real, `P ∈ L(∞) ∩ U⁻_{-ν}`, `e''ᵢ P = 0` and
`P ≡ f̃_{w₀} 1` modulo `ϖ L(∞)`, then `P fᵢ^{(m)}` is congruent to some `f̃_{w'} 1`, and for
`μ ≫ 0` and `⟨i, λ⟩ = 0`, `⟨j, λ⟩ ≫ 0` (`j ≠ i`),
`Φ(π_{μ+λ}(P fᵢ^{(m)})) ≡ f̃ᵢ^m v_μ ⊗ f̃_{w₀} v_λ` (Kashiwara's `P fᵢ^{(m)} (u_λ ⊗ u_μ) ≡
P u_λ ⊗ fᵢ^{(m)} u_μ`, library order). Our proof replaces `B(∞)* ⊆ B(∞) ∪ -B(∞)` ([Kas91]
Cor. 6.1.2) and the global bases by formal reality, the slice formula and
`GrandLoop.evq_notMem_smul_lat`. -/
theorem rmulF_tensor_congr [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (m : ℕ)
    (ν : I →₀ ℕ) (hν' : (ν + m • Finsupp.single i 1).degree ≠ 0) :
    ∃ N : ℕ, ∀ μ Λl : Dom R, (∀ j, (N : ℤ) ≤ μ.1 (R.coroot j)) →
      Λl.1 (R.coroot i) = 0 → (∀ j, j ≠ i → (N : ℤ) ≤ Λl.1 (R.coroot j)) →
      ∀ P : Um D v, P ∈ latInf hvt A → P ∈ Uw D v ν →
        (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0 →
        ∀ w₀ : List I, P - fWi hvt w₀ ∈ ϖ • latInf hvt A →
        (∃ w' : List I, rmulF hvt i m P - fWi hvt w' ∈ ϖ • latInf hvt A) ∧
        tensorEmb hvt hR μ.2 Λl.2 (evq hvt (μ + Λl) (rmulF hvt i m P)) -
          TensorModule.mk _ _ (fW hvt hR μ (List.replicate m i) ⊗ₜ[k]
            fW hvt hR Λl w₀) ∈ ϖ • LL hvt hR A μ Λl := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hϖu : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  set ν' := ν + m • Finsupp.single i 1
  obtain ⟨N₀, hinjT⟩ :=
    exists_large_mem_smul_latInf_of_tensorEmb_mem (hR := hR) hinj hϖ hϖv hk hfund hν'
  obtain ⟨m₁, hm₁⟩ := exists_form_mem_of_large (hR := hR) hinj hϖ hϖv hk hfund
    (m • Finsupp.single i 1)
  obtain ⟨m₂, hm₂⟩ := exists_form_fW_fW (hR := hR) hinj hϖ hϖv hk hfund (m • Finsupp.single i 1)
  obtain ⟨m₃, hm₃⟩ := evq_notMem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund i ν
  refine ⟨N₀ + m₁ + m₂ + m₃, fun μ Λl hμN hΛli hΛl₀ P hP hPw he w₀ hw₀ ↦ ?_⟩
  have hμN₀ : ∀ j, (N₀ : ℤ) ≤ μ.1 (R.coroot j) := fun j ↦ by
    have := hμN j; push_cast at this; omega
  have hΛl : ∀ j, j ≠ i → (m₃ : ℤ) ≤ Λl.1 (R.coroot j) := fun j hj ↦ by
    have := hΛl₀ j hj; push_cast at this; omega
  set Q := rmulF hvt i m P with hQdef
  have hQ : Q ∈ latInf hvt A := rmulF_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i m hP he
  have hQw : Q ∈ Uw D v ν' := rmulF_mem_Uw i m hPw
  have hP0 : P ∉ ϖ • latInf hvt A := fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀
    (by simpa using sub_mem h hw₀)
  have hw₀w : wordWeight w₀ = ν := wordWeight_eq_of_mem_Uw hPw hP0 hw₀
  -- 1. expansion of `Q` in `B(∞)`
  obtain ⟨S, a, hSw, hSd, hQS, t, ht⟩ :=
    exists_sum_fWi (hR := hR) hinj hϖ hϖv hk hfund hQ hQw
  -- 2. `(Q, Q) ≡ 1`
  have hQQ : ∃ t' : A, formU hv' Q Q = algebraMap A k (1 + ϖ * t') := by
    have h1 : formU hv' Q Q = coefU D v i m * formU hv' P P := by
      rw [hQdef, rmulF_apply, formU_starU, formU_df_df hv' i he he m m, ite_eq_left rfl,
        formU_starU]
    obtain ⟨c₀, hc₀⟩ := exists_coefU hϖ hϖv (D := D) i m
    obtain ⟨e₀, he₀⟩ := formU_fWi_fWi (hR := hR) (A := A) (D := D) hinj hϖ hϖv hk hfund w₀ w₀
    rw [sub_self, ite_eq_left (zero_mem _)] at he₀
    obtain ⟨t₁, ht₁⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund hP hw₀
    obtain ⟨t₂, ht₂⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund
      (NegativePart.fWord_mem_latticeInf _ _ w₀) hw₀
    have h2 : formU hv' P P = 1 + algebraMap A k (ϖ * (e₀ + t₁ + t₂)) := by
      have : formU hv' P P = formU hv' P (P - fWi hvt w₀) +
          formU hv' (fWi hvt w₀) (P - fWi hvt w₀) +
            formU hv' (fWi (D := D) hvt w₀) (fWi hvt w₀) := by
        rw [map_sub, map_sub, formU_comm hv' (fWi hvt w₀) P]; ring
      rw [this, ht₁, ht₂, he₀]
      simp only [map_add, map_mul]; ring
    refine ⟨c₀ + (e₀ + t₁ + t₂) + ϖ * c₀ * (e₀ + t₁ + t₂), ?_⟩
    rw [h1, hc₀, h2]
    simp only [map_add, map_mul, map_one]; ring
  obtain ⟨t', ht'⟩ := hQQ
  have hsumsq : ∑ s ∈ S, a s ^ 2 - 1 ∈ Ideal.span {ϖ} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨t' - t, ?_⟩
    apply hinj
    rw [ht'] at ht
    simp only [map_sub, map_mul, map_one, map_add] at ht ⊢
    linear_combination ht
  -- 3. the weights `μ`, `λ`
  have hμ : ∀ j, ((m₁ + m₂ : ℕ) : ℤ) ≤ μ.1 (R.coroot j) := fun j ↦ by
    have h1 := hμN j
    push_cast at h1 ⊢; omega
  have hμ₁ : ∀ j, (m₁ : ℤ) ≤ μ.1 (R.coroot j) := fun j ↦ by have := hμ j; push_cast at this; omega
  have hμ₂ : ∀ j, (m₂ : ℤ) ≤ μ.1 (R.coroot j) := fun j ↦ by have := hμ j; push_cast at this; omega
  -- 4. `T` and the slice
  set T : Um D v →ₗ[k] TM v μ Λl :=
    (tensorEmb hvt hR μ.2 Λl.2).restrictScalars k ∘ₗ evq hvt (μ + Λl) with hT
  have hTS : ∀ u, u ∈ ϖ • latInf hvt A → T u ∈ ϖ • LL hvt hR A μ Λl := fun u hu ↦
    tensorEmb_evq_mem_smul_LL (hR := hR) hinj hϖ hϖv hk hfund μ Λl hu
  set z := fW hvt hR μ (List.replicate m i)
  have hzL : z ∈ lat hvt hR A μ := IrreducibleModule.fWord_mem_lattice hR _ μ.2 A _
  have hzw : z ∈ wsp μ (m • Finsupp.single i 1) := by
    have := fW_mem_wsp hvt hR μ (List.replicate m i)
    rwa [wordWeight_replicate] at this
  set f := IrreducibleModule.form μ.1 hR hv' z
  have hf : ∀ x ∈ lat hvt hR A μ, ∃ a : A, f x = algebraMap A k a :=
    hm₁ μ hμ₁ z hzL hzw
  set pr := prL (IrreducibleModule R v Λl.1) f
  -- 5. `pr (T Q) = (z, z) P v_λ`
  obtain ⟨P', rfl⟩ := Submodule.Quotient.mk_surjective _ P
  have hTQ : pr (T Q) = f z • evq hvt Λl (Submodule.Quotient.mk P') := by
    rw [hQdef, rmulF_mk, map_smul, map_smul]
    change (qFactorial (v ^ D.d i)⁻¹ m)⁻¹ • prL _ f (tensorEmb hvt hR μ.2 Λl.2
      (ev R v (μ + Λl).1 (P' * θ k i ^ m))) = _
    rw [prL_tensorEmb_ev_mul_θ_pow hR hΛli m hzw, F_pow_smul_hwv_eq (hvt := hvt) (hR := hR),
      map_smul, smul_smul, smul_eq_mul, qFactorial_inv, ← mul_assoc,
      inv_mul_cancel₀ (qFactorial_ne_zero_of_not_root (NeZero.ne v) hv' i m), one_mul]
    rfl
  -- 6. `pr (T Q) ≡ Σ aₛ pr (T f̃ₛ 1)`
  have hlin : ∀ u : Um D v, ∀ c : A, T (c • u) = c • T u := fun u c ↦
    LinearMap.map_smul_of_tower T c u
  have hprlin : ∀ w : TM v μ Λl, ∀ c : A, pr (c • w) = c • pr w := fun w c ↦
    LinearMap.map_smul_of_tower pr c w
  have hprS : pr (T Q) - ∑ s ∈ S, a s • pr (T (fWi hvt s)) ∈ ϖ • lat hvt hR A Λl := by
    have h := prL_mem_smul_lat hf (hTS _ hQS)
    rwa [map_sub, map_sub, map_sum, map_sum, Finset.sum_congr rfl fun s _ ↦ by
      rw [hlin, hprlin]] at h
  -- 7. `pr (T f̃ₛ 1) ≡ δₛ f̃_{s₂} v_λ`
  choose s₁ s₂ hs12w hs12 using fun s ↦
    exists_tensorEmb_evq_fWi_sub (hR := hR) hinj hϖ hϖv hk hfund μ Λl s
  set rep := List.replicate m i
  set good : List I → Prop := fun s ↦
    wordWeight (s₁ s) = m • Finsupp.single i 1 ∧ fWi (D := D) hvt rep - fWi hvt (s₁ s) ∈
      ϖ • latInf hvt A
  have hδ : ∀ s, ∃ e : A, f (fW hvt hR μ (s₁ s)) =
      algebraMap A k (if good s then 1 else 0) + algebraMap A k (ϖ * e) := by
    intro s
    by_cases hw : wordWeight (s₁ s) = m • Finsupp.single i 1
    · obtain ⟨e, he'⟩ := hm₂ μ hμ₂ rep (s₁ s) (wordWeight_replicate i m) hw
      refine ⟨e, ?_⟩
      rw [he']
      by_cases hg : fWi (D := D) hvt rep - fWi hvt (s₁ s) ∈ ϖ • latInf hvt A
      · rw [ite_eq_left hg, ite_eq_left ⟨hw, hg⟩, map_one]
      · rw [ite_eq_right hg, ite_eq_right (fun h ↦ hg h.2), map_zero]
    · refine ⟨0, ?_⟩
      rw [ite_eq_right (fun h ↦ hw h.1), map_zero, mul_zero, map_zero, add_zero]
      refine (IrreducibleModule.isContravariant_form hR hv').eq_zero_of_ne ?_ hzw
        (fW_mem_wsp hvt hR μ (s₁ s)) hv'
      intro h
      exact hw (LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h)).symm
  choose e hes using hδ
  have hfW : ∀ c : List I, fW hvt hR Λl c ∈ lat hvt hR A Λl := fun c ↦
    IrreducibleModule.fWord_mem_lattice hR _ Λl.2 A c
  have hprs : ∀ s, pr (T (fWi hvt s)) - (if good s then (1 : A) else 0) • fW hvt hR Λl (s₂ s) ∈
      ϖ • lat hvt hR A Λl := by
    intro s
    have h := prL_mem_smul_lat hf (hs12 s)
    rw [map_sub, prL_tmul, hes s] at h
    have h2 : (algebraMap A k (ϖ * e s)) • fW hvt hR Λl (s₂ s) ∈ ϖ • lat hvt hR A Λl := by
      rw [algebraMap_smul, mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ (hfW _))
    have := add_mem h h2
    rw [add_smul, algebraMap_smul, sub_add_eq_sub_sub, sub_add_cancel] at this
    exact this
  -- `(z, z) ≡ 1` and `π_λ(P) ≡ f̃_{w₀} v_λ`
  obtain ⟨e₀, he₀⟩ := hm₂ μ hμ₂ rep rep (wordWeight_replicate i m) (wordWeight_replicate i m)
  rw [sub_self, ite_eq_left (zero_mem _)] at he₀
  have hPl : evq hvt Λl (Submodule.Quotient.mk P') ∈ lat hvt hR A Λl :=
    evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund hP Λl
  have hPw₀ : evq hvt Λl (Submodule.Quotient.mk P') - fW hvt hR Λl w₀ ∈ ϖ • lat hvt hR A Λl := by
    have h1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund hw₀ Λl
    have h2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w₀ Λl
    rw [map_sub] at h1
    simpa using add_mem h1 h2
  have hTQ' : pr (T Q) - fW hvt hR Λl w₀ ∈ ϖ • lat hvt hR A Λl := by
    rw [hTQ]
    change f (fW hvt hR μ rep) • _ - _ ∈ _
    rw [he₀, add_smul, one_smul, algebraMap_smul, mul_smul]
    have h3 : ϖ • e₀ • evq hvt Λl (Submodule.Quotient.mk P') ∈ ϖ • lat hvt hR A Λl :=
      Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ hPl)
    have := add_mem hPw₀ h3
    rwa [sub_add_eq_add_sub] at this
  -- `(**)`
  set S' := S.filter good
  have hmain : fW hvt hR Λl w₀ - ∑ s ∈ S', a s • fW hvt hR Λl (s₂ s) ∈ ϖ • lat hvt hR A Λl := by
    have h4 : ∑ s ∈ S, a s • pr (T (fWi hvt s)) -
        ∑ s ∈ S, a s • ((if good s then (1 : A) else 0) • fW hvt hR Λl (s₂ s)) ∈
          ϖ • lat hvt hR A Λl := by
      rw [← Finset.sum_sub_distrib]
      exact Submodule.sum_mem _ fun s _ ↦ by rw [← smul_sub]; exact Submodule.smul_mem _ _ (hprs s)
    have h5 : ∑ s ∈ S, a s • ((if good s then (1 : A) else 0) • fW hvt hR Λl (s₂ s)) =
        ∑ s ∈ S', a s • fW hvt hR Λl (s₂ s) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      by_cases hg : good s
      · rw [ite_eq_left hg, ite_eq_left hg, one_smul]
      · rw [ite_eq_right hg, ite_eq_right hg, zero_smul, smul_zero]
    rw [h5] at h4
    have := sub_mem (sub_mem (add_mem hprS h4) hTQ') (zero_mem (ϖ • lat hvt hR A Λl))
    have e6 : pr (T Q) - ∑ s ∈ S, a s • pr (T (fWi hvt s)) +
        (∑ s ∈ S, a s • pr (T (fWi hvt s)) - ∑ s ∈ S', a s • fW hvt hR Λl (s₂ s)) -
          (pr (T Q) - fW hvt hR Λl w₀) - 0 =
        fW hvt hR Λl w₀ - ∑ s ∈ S', a s • fW hvt hR Λl (s₂ s) := by abel
    rwa [e6] at this
  -- 8. the words `s₂ s`, `s ∈ S'`
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  have hs₂w : ∀ s ∈ S', wordWeight (s₂ s) = ν := by
    intro s hs
    have h1 := hs12w s
    rw [(Finset.mem_filter.1 hs).2.1, hSw s (hS'S hs), add_comm] at h1
    exact add_right_cancel h1
  have hTfWi : ∀ s, T (fWi hvt s) - TensorModule.mk _ _ (fW hvt hR μ (s₁ s) ⊗ₜ[k]
      fW hvt hR Λl (s₂ s)) ∈ ϖ • LL hvt hR A μ Λl := hs12
  have hfWμ : ∀ c : List I, fW hvt hR μ c ∈ lat hvt hR A μ := fun c ↦
    IrreducibleModule.fWord_mem_lattice hR _ μ.2 A c
  have h0' : ∀ s ∈ S', fW hvt hR Λl (s₂ s) ∉ ϖ • lat hvt hR A Λl := by
    intro s hs h
    have h1 : T (fWi hvt s) ∈ ϖ • LL hvt hR A μ Λl := by
      have := add_mem (hTfWi s) (tmul_mem_smul_right (hfWμ (s₁ s)) h)
      rwa [sub_add_cancel] at this
    exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund s
      (hinjT μ Λl hμN₀ _ (NegativePart.fWord_mem_latticeInf _ _ s)
        ((hSw s (hS'S hs)) ▸ fWi_mem_Uw (hvt := hvt) s) h1)
  have hd' : ∀ s ∈ S', ∀ s' ∈ S', s ≠ s' →
      fW hvt hR Λl (s₂ s) - fW hvt hR Λl (s₂ s') ∉ ϖ • lat hvt hR A Λl := by
    intro s hs s' hs' hne h
    have hg := (Finset.mem_filter.1 hs).2.2
    have hg' := (Finset.mem_filter.1 hs').2.2
    have h1 : fWi (D := D) hvt (s₁ s) - fWi hvt (s₁ s') ∈ ϖ • latInf hvt A := by
      have := sub_mem hg' hg
      rwa [sub_sub_sub_cancel_left] at this
    have h2 : fW hvt hR μ (s₁ s) - fW hvt hR μ (s₁ s') ∈ ϖ • lat hvt hR A μ := by
      have e1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund h1 μ
      have e2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (s₁ s) μ
      have e3 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (s₁ s') μ
      rw [map_sub] at e1
      have := sub_mem (sub_mem e1 e2) (neg_mem e3)
      convert this using 1; abel
    have h3 : T (fWi hvt s - fWi hvt s') ∈ ϖ • LL hvt hR A μ Λl := by
      have k1 := tmul_mem_smul_left h2 (hfW (s₂ s))
      have k2 := tmul_mem_smul_right (hfWμ (s₁ s')) h
      have := add_mem (sub_mem (hTfWi s) (hTfWi s')) (add_mem k1 k2)
      rw [map_sub]
      convert this using 1
      rw [sub_tmul, tmul_sub, map_sub, map_sub]; abel
    exact hSd s (hS'S hs) s' (hS'S hs') hne
      (hinjT μ Λl hμN₀ _ (sub_mem (NegativePart.fWord_mem_latticeInf _ _ s)
        (NegativePart.fWord_mem_latticeInf _ _ s'))
        (sub_mem ((hSw s (hS'S hs)) ▸ fWi_mem_Uw (hvt := hvt) s)
          ((hSw s' (hS'S hs')) ▸ fWi_mem_Uw (hvt := hvt) s')) h3)
  have hw₀ne : fW hvt hR Λl w₀ ∉ ϖ • lat hvt hR A Λl := by
    intro h
    exact hm₃ Λl hΛli hΛl _ hP hPw he hP0 (by simpa using add_mem hPw₀ h)
  -- 9. some `s₀ ∈ S'` has `aₛ₀ ≡ 1`
  have hone : ∃ s₀ ∈ S', a s₀ - 1 ∈ Ideal.span {ϖ} ∧
      fW hvt hR Λl w₀ - fW hvt hR Λl (s₂ s₀) ∈ ϖ • lat hvt hR A Λl := by
    by_cases hex : ∃ s₀ ∈ S', fW hvt hR Λl w₀ - fW hvt hR Λl (s₂ s₀) ∈ ϖ • lat hvt hR A Λl
    · obtain ⟨s₀, hs₀, hw⟩ := hex
      refine ⟨s₀, hs₀, ?_, hw⟩
      have hc := coeff_mem_of_sum_fW_mem (hR := hR) hinj hϖ hϖv hk hfund Λl S' s₂
        (fun s ↦ -a s + if s = s₀ then 1 else 0) hs₂w h0' hd' (by
          simp only [add_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
            ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', ite_eq_left hs₀]
          have := sub_mem hmain hw
          convert this using 1; abel) s₀ hs₀
      rw [ite_eq_left rfl] at hc
      have := neg_mem hc
      rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
    · push Not at hex
      exfalso
      have hc := coeff_mem_of_sum_fW_mem (hR := hR) hinj hϖ hϖv hk hfund Λl
        (Finset.insertNone S') (fun o ↦ o.elim w₀ s₂) (fun o ↦ o.elim 1 fun s ↦ -a s)
        (by
          intro o ho
          cases o with
          | none => exact hw₀w
          | some s => exact hs₂w s (Finset.mem_insertNone.1 ho s rfl))
        (by
          intro o ho
          cases o with
          | none => exact hw₀ne
          | some s => exact h0' s (Finset.mem_insertNone.1 ho s rfl))
        (by
          intro o ho o' ho' hne
          cases o with
          | none =>
            cases o' with
            | none => exact absurd rfl hne
            | some s' => exact hex s' (Finset.mem_insertNone.1 ho' s' rfl)
          | some s =>
            cases o' with
            | none =>
              intro h
              exact hex s (Finset.mem_insertNone.1 ho s rfl) (by
                have := neg_mem h; rwa [neg_sub] at this)
            | some s' =>
              exact hd' s (Finset.mem_insertNone.1 ho s rfl) s'
                (Finset.mem_insertNone.1 ho' s' rfl) fun h ↦ hne (h ▸ rfl))
        (by
          rw [Finset.sum_insertNone]
          simp only [Option.elim, one_smul, neg_smul, Finset.sum_neg_distrib]
          rwa [← sub_eq_add_neg])
        none (Finset.mem_insertNone.2 fun _ h ↦ by simp at h)
      obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 hc
      have hc'' : c * ϖ = 1 := by simpa using hc'
      exact hϖu (isUnit_iff_exists_inv.2 ⟨c, by rw [mul_comm]; exact hc''⟩)
  -- 10. formal reality
  obtain ⟨s₀, hs₀, ha₀, hw₀s₀⟩ := hone
  have hs₀S := hS'S hs₀
  have hrest : ∀ s ∈ S.erase s₀, a s ∈ Ideal.span {ϖ} := by
    have h1 : ∑ s ∈ S.erase s₀, a s ^ 2 ∈ Ideal.span {ϖ} := by
      have e1 : ∑ s ∈ S.erase s₀, a s ^ 2 =
          (∑ s ∈ S, a s ^ 2 - 1) - (a s₀ - 1) * (a s₀ + 1) := by
        rw [← Finset.add_sum_erase S _ hs₀S]; ring
      rw [e1]
      exact sub_mem hsumsq (Ideal.mul_mem_right _ _ ha₀)
    intro s hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine eq_zero_of_sum_sq_eq_zero (S.erase s₀) (fun s ↦ Ideal.Quotient.mk _ (a s)) ?_ s hs
    simp only [← map_pow, ← map_sum]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have hspan : ∀ c : A, c ∈ Ideal.span {ϖ} → ∀ x : Um D v, x ∈ latInf hvt A →
      c • x ∈ ϖ • latInf hvt A := by
    intro c hc x hx
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ hx)
  have hfin : ∑ s ∈ S, a s • fWi (D := D) hvt s - fWi hvt s₀ ∈ ϖ • latInf hvt A := by
    rw [← Finset.add_sum_erase S _ hs₀S]
    have e1 : a s₀ • fWi (D := D) hvt s₀ + ∑ s ∈ S.erase s₀, a s • fWi hvt s - fWi hvt s₀ =
        (a s₀ - 1) • fWi (D := D) hvt s₀ + ∑ s ∈ S.erase s₀, a s • fWi hvt s := by
      rw [sub_smul, one_smul]; abel
    rw [e1]
    exact add_mem (hspan _ ha₀ _ (NegativePart.fWord_mem_latticeInf _ _ s₀))
      (Submodule.sum_mem _ fun s hs ↦ hspan _ (hrest s hs) _
        (NegativePart.fWord_mem_latticeInf _ _ s))
  have hQs₀ : Q - fWi hvt s₀ ∈ ϖ • latInf hvt A := by
    have := add_mem hQS hfin
    rwa [sub_add_sub_cancel] at this
  refine ⟨⟨s₀, hQs₀⟩, ?_⟩
  -- the tensor congruence
  have hg := (Finset.mem_filter.1 hs₀).2.2
  have hz₁ : fW hvt hR μ (s₁ s₀) - z ∈ ϖ • lat hvt hR A μ := by
    have e1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund hg μ
    have e2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund rep μ
    have e3 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (s₁ s₀) μ
    rw [map_sub] at e1
    have := sub_mem (sub_mem e1 e2) (neg_mem e3)
    have := neg_mem this
    convert this using 1; abel
  have k1 := tmul_mem_smul_left hz₁ (hfW (s₂ s₀))
  have k2 := tmul_mem_smul_right hzL (show fW hvt hR Λl (s₂ s₀) - fW hvt hR Λl w₀ ∈
    ϖ • lat hvt hR A Λl by have := neg_mem hw₀s₀; rwa [neg_sub] at this)
  have k3 := hTS _ hQs₀
  have := add_mem (add_mem (add_mem k3 (hTfWi s₀)) k1) k2
  change T Q - _ ∈ _
  convert this using 1
  rw [map_sub, sub_tmul, tmul_sub, map_sub, map_sub]
  abel

include hR in
/-- **[Kas93a] Prop. 2.1.2** (the membership part, as used for Thm. 2.1.1). -/
theorem rmulF_sub_mem_of_sub_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (m : ℕ)
    {ν : I →₀ ℕ} {P : Um D v} (hP : P ∈ latInf hvt A) (hPw : P ∈ Uw D v ν)
    (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0)
    {w₀ : List I} (hw₀ : P - fWi hvt w₀ ∈ ϖ • latInf hvt A) :
    ∃ w' : List I, rmulF hvt i m P - fWi hvt w' ∈ ϖ • latInf hvt A := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨w₀, by simpa using hw₀⟩
  have hν' : (ν + m • Finsupp.single i 1).degree ≠ 0 := by
    simp only [map_add, map_nsmul, Finsupp.degree_single, smul_eq_mul, mul_one]; omega
  obtain ⟨N, h⟩ := rmulF_tensor_congr (hR := hR) hinj hϖ hϖv hk hfund i m ν hν'
  obtain ⟨Λl, hΛli, hΛl⟩ := exists_dom_wall hfund i N
  obtain ⟨Λb, hΛb⟩ := exists_dom_ge hfund N
  exact (h Λb Λl hΛb hΛli hΛl P hP hPw he w₀ hw₀).1

include hR in
lemma comp_mem_smul_latInf (i : I) (n : ℕ) {u : Um D v} (hu : u ∈ ϖ • latInf hvt A) :
    comp hvt i n u ∈ ϖ • latInf hvt A :=
  LinearMap.map_mem_smul_of_mem ϖ (fun _ hm ↦ comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund
    i n hm) hu

include hR in
lemma starU_mem_smul_latInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {u : Um D v}
    (hu : u ∈ ϖ • latInf hvt A) : starU D v u ∈ ϖ • latInf hvt A :=
  LinearMap.map_mem_smul_of_mem ϖ (fun _ hm ↦ starU_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund
    hm) hu

include hR in
/-- **`i`-strings of `B(∞)` in `L(∞)`**: `f̃_w 1 ≡ fᵢ^{(k)} c` with `c ≡ f̃_{w₁} 1`, i.e. the
`k`-th `i`-component of `f̃_w 1` is `≡ f̃_{w₁} 1` and the others lie in `ϖ L(∞)`. -/
theorem exists_comp_fWi (i : I) (w : List I) :
    ∃ (k : ℕ) (w₁ : List I), comp hvt i k (fWi (D := D) hvt w) - fWi hvt w₁ ∈ ϖ • latInf hvt A ∧
      (∀ r, r ≠ k → comp hvt i r (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A) ∧
      wordWeight w₁ + Finsupp.single i k = wordWeight w := by
  classical
  set u := fWi (D := D) hvt w
  have hex : ∃ j, (kE hvt i ^ (j + 1)) u ∈ ϖ • latInf hvt A :=
    ⟨wordWeight w i, by rw [kE_pow_eq_zero i (fWi_mem_Uw (hvt := hvt) w)]; exact zero_mem _⟩
  set k := Nat.find hex
  have hk1 : (kE hvt i ^ (k + 1)) u ∈ ϖ • latInf hvt A := Nat.find_spec hex
  have hnot : ∀ j ≤ k, (kE hvt i ^ j) u ∉ ϖ • latInf hvt A := by
    intro j hj h
    rcases j with _ | j
    · exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w (by simpa using h)
    · exact Nat.find_min hex (show j < k by omega) h
  have hwords : ∀ j ≤ k, ∃ c : List I, (kE hvt i ^ j) u - fWi hvt c ∈ ϖ • latInf hvt A := by
    intro j hj
    induction j with
    | zero => exact ⟨w, by simp [u]⟩
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih (by omega)
      have h1 := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i hc
      rw [map_sub] at h1
      rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i c with h | ⟨c', hc'⟩
      · exact absurd (by simpa [pow_succ', Module.End.mul_apply] using add_mem h1 h)
          (hnot (j + 1) hj)
      · refine ⟨c', ?_⟩
        rw [pow_succ', Module.End.mul_apply]
        simpa using add_mem h1 hc'
  have hpowS : ∀ r, k < r → (kE hvt i ^ r) u ∈ ϖ • latInf hvt A := by
    intro r hr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hr
    induction d with
    | zero => simpa using hk1
    | succ d ih =>
      rw [show k + (d + 1) + 1 = (k + d + 1) + 1 by ring, pow_succ', Module.End.mul_apply]
      exact kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i (ih (by omega))
  -- `comp 0 y = y - f̃ ẽ y`
  have hcomp0 : ∀ y : Um D v, comp (D := D) hvt i 0 y = y - kF hvt i (kE hvt i y) := fun y ↦ by
    rw [eq_sub_iff_add_eq, add_comm]
    exact BosonModule.fTilde_eTilde_add_component _ _ y
  obtain ⟨c, hc⟩ := hwords k le_rfl
  have hkle : k ≤ wordWeight w i := by
    by_contra h
    exact hnot k le_rfl (by
      rw [show k = (k - (wordWeight w i + 1)) + (wordWeight w i + 1) by omega, pow_add,
        Module.End.mul_apply, kE_pow_eq_zero i (fWi_mem_Uw (hvt := hvt) w)]
      simp)
  refine ⟨k, c, ?_, fun r hr ↦ ?_, ?_⟩
  · rw [comp_eq_comp_zero_kE_pow, hcomp0]
    have := kF_mem_smul_latInf i (show kE hvt i ((kE hvt i ^ k) u) ∈ ϖ • latInf hvt A by
      rw [← Module.End.mul_apply, ← pow_succ']; exact hk1)
    convert sub_mem hc this using 1; abel
  · rw [comp_eq_comp_zero_kE_pow]
    rcases lt_or_gt_of_ne hr with hr | hr
    · -- `r < k`
      obtain ⟨cr, hcr⟩ := hwords r hr.le
      obtain ⟨cr', hcr'⟩ := hwords (r + 1) hr
      have h0 : kE hvt i (fWi (D := D) hvt cr) ∉ ϖ • latInf hvt A := by
        intro h
        have h1 := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i hcr
        rw [map_sub] at h1
        exact hnot (r + 1) hr (by
          rw [pow_succ', Module.End.mul_apply]; simpa using add_mem h1 h)
      have h2 : kE hvt i (fWi (D := D) hvt cr) - fWi hvt cr' ∈ ϖ • latInf hvt A := by
        have h1 := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i hcr
        rw [map_sub] at h1
        rw [pow_succ', Module.End.mul_apply] at hcr'
        have := sub_mem hcr' h1
        convert this using 1; abel
      have h3 := fWi_sub_mem_of_kE (hR := hR) hinj hϖ hϖv hk hfund i h0 h2
      -- `y ≡ f̃_{cr} 1 ≡ f̃ᵢ f̃_{cr'} 1 ≡ f̃ᵢ ẽᵢ y`
      have h4 := kF_mem_smul_latInf i hcr'
      rw [pow_succ', Module.End.mul_apply, map_sub] at h4
      rw [hcomp0]
      have : (kE hvt i ^ r) u - kF hvt i (kE hvt i ((kE hvt i ^ r) u)) =
          ((kE hvt i ^ r) u - fWi hvt cr) + (fWi hvt cr - fWi hvt (i :: cr')) -
            (kF hvt i (kE hvt i ((kE hvt i ^ r) u)) - kF hvt i (fWi hvt cr')) := by
        rw [show fWi (D := D) hvt (i :: cr') = kF hvt i (fWi hvt cr') from rfl]; abel
      rw [this]
      exact sub_mem (add_mem hcr h3) h4
    · -- `r > k`
      exact comp_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i 0 (hpowS r hr)
  · have hw := kE_pow_mem (hvt := hvt) i (fWi_mem_Uw (D := D) (hvt := hvt) w) k hkle
    have := wordWeight_eq_of_mem_Uw hw (hnot k le_rfl) hc
    rw [this]
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hkle)

include hR in
/-- **[Kas93a] Thm. 2.1.1, `B(∞)* ⊆ B(∞)`**: if `A/ϖA` is formally real, `(f̃_w 1)*` is congruent
to some `f̃_{w'} 1` modulo `ϖ L(∞)`. By induction on `|w|` with [Kas93a] Prop. 2.1.2
(`GrandLoop.rmulF_sub_mem_of_sub_mem`) and the `i`-strings of `B(∞)`
(`GrandLoop.exists_comp_fWi`). -/
theorem starU_fWi_sub_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (w : List I) :
    ∃ w' : List I, starU D v (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf hvt A := by
  classical
  suffices h : ∀ n : ℕ, ∀ w : List I, w.length ≤ n →
      ∃ w' : List I, starU D v (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf hvt A from h _ w le_rfl
  intro n
  induction n with
  | zero =>
    intro w hw
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hw)]
    exact ⟨[], by simp [fWi, starU_mk]⟩
  | succ n ih =>
    intro w hw
    rcases w with _ | ⟨i, w₀⟩
    · exact ih [] (Nat.zero_le _)
    simp only [List.length_cons] at hw
    set u := fWi (D := D) hvt w₀
    obtain ⟨k, w₁, hk1, hkr, hwt⟩ := exists_comp_fWi (hR := hR) hinj hϖ hϖv hk hfund i w₀
    have hlen : w₁.length + k = w₀.length := by
      have := congrArg Finsupp.degree hwt
      rwa [map_add, degree_wordWeight, degree_wordWeight, Finsupp.degree_single] at this
    obtain ⟨w₂, h₂⟩ := ih w₁ (by omega)
    obtain ⟨N₀, hN₀, -⟩ := exists_sum_comp (hvt := hvt) i u
    have hkN : k < N₀ := by
      by_contra h
      have h0 := hN₀ k (by omega)
      rw [h0, zero_sub] at hk1
      exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₁ (by simpa using neg_mem hk1)
    -- `f̃ᵢ u = Σᵣ fᵢ^{(r+1)} uᵣ`
    have hsum : kF hvt i u = ∑ r ∈ Finset.range N₀,
        (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df (r + 1) (comp hvt i r u) := by
      have h := eq_sum_comp (hvt := hvt) i (kF hvt i u) (N := N₀ + 1) (fun n hn ↦ by
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ n by omega)
        rw [comp_succ_kF]; exact hN₀ r (by omega))
      rw [h, Finset.sum_range_succ', comp_zero_kF, map_zero, add_zero]
      exact Finset.sum_congr rfl fun r _ ↦ by rw [comp_succ_kF]
    have hstar : starU D v (fWi hvt (i :: w₀)) = ∑ r ∈ Finset.range N₀,
        rmulF hvt i (r + 1) (starU D v (comp hvt i r u)) := by
      change starU D v (kF hvt i u) = _
      rw [hsum, map_sum]
      exact Finset.sum_congr rfl fun r _ ↦ by rw [rmulF_apply, starU_starU]
    -- the term `r = k`
    set P := starU D v (comp hvt i k u)
    have hPL : P ∈ latInf hvt A := starU_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund
      (comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i k
        (NegativePart.fWord_mem_latticeInf _ _ w₀))
    have hPw : P ∈ Uw D v (wordWeight w₁) := by
      have h := component_mem_Uw (hvt := hvt) i (fWi_mem_Uw (D := D) (hvt := hvt) w₀) k
      rw [← hwt, add_tsub_cancel_right] at h
      exact starU_mem_Uw h
    have he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0 := by
      rw [starU_starU]; exact e_comp i k u
    have hP₂ : P - fWi hvt w₂ ∈ ϖ • latInf hvt A := by
      have h1 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hk1
      rw [map_sub] at h1
      simpa using add_mem h1 h₂
    obtain ⟨w', hw'⟩ := rmulF_sub_mem_of_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i (k + 1)
      hPL hPw he hP₂
    refine ⟨w', ?_⟩
    rw [hstar, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hkN)]
    have hrest : ∑ r ∈ (Finset.range N₀).erase k,
        rmulF hvt i (r + 1) (starU D v (comp hvt i r u)) ∈ ϖ • latInf hvt A := by
      refine Submodule.sum_mem _ fun r hr ↦ ?_
      have hrk := Finset.ne_of_mem_erase hr
      refine rmulF_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i (r + 1)
        (starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund (hkr r hrk)) ?_
      rw [starU_starU]; exact e_comp i r u
    have := add_mem hw' hrest
    convert this using 1; abel

include hR in
/-- **`B(∞)* = B(∞)`** ([Kas93a] Thm. 2.1.1): every `f̃_w 1` is congruent to the image under `*`
of some `f̃_{w'} 1`. -/
theorem exists_fWi_sub_starU_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (w : List I) :
    ∃ w' : List I, fWi hvt w - starU D v (fWi hvt w') ∈ ϖ • latInf hvt A := by
  obtain ⟨w', hw'⟩ := starU_fWi_sub_mem (hR := hR) hinj hϖ hϖv hk hfund (D := D) (A := A) w
  refine ⟨w', ?_⟩
  have := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hw'
  rwa [map_sub, starU_starU] at this

end Base

end GrandLoop

end LieLean.QuantumGroup
