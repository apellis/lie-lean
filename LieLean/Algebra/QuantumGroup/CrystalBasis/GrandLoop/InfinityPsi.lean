/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityStarOps

/-!
# `ẽᵢ` on `B(∞)` in terms of `f̃ᵢ*`

Toward the embeddings `Ψᵢ : B(∞) → B(∞) ⊗ Bᵢ` of [Kas93a] Thm. 2.2.1. Write `b = f̃ᵢ*ᵐ b₀` with
`ẽᵢ* b₀ = 0`. Then `ẽᵢ b = f̃ᵢ*ᵐ ẽᵢ b₀` if `φᵢ(b₀) ≥ m` and `ẽᵢ b = f̃ᵢ*ᵐ⁻¹ b₀` otherwise. As in
[Kas93a], the proof goes through `T = Φ ∘ π_{μ+λ}`, `⟨i, λ⟩ = 0`, under which
`T(b) ≡ f̃ᵢᵐ v_μ ⊗ π_λ(b₀)` (`GrandLoop.rmulF_tensor_congr`), and the tensor product rule.

## References

* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858, §2.2.
-/

open Finset Pointwise TensorProduct LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

open VermaModule TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
/-- **Comparison of pure tensors** `f̃ᵢᵏ v_μ ⊗ y` modulo `ϖ (L(μ) ⊗ L(λ))`, for `μ ≫ 0`. -/
theorem exists_tmul_cmp (i : I) (M : ℕ) :
    ∃ N : ℕ, ∀ μ Λl : Dom R, (∀ j, (N : ℤ) ≤ μ.1 (R.coroot j)) → ∀ k₁ ≤ M, ∀ k₂ ≤ M,
      ∀ y₁ ∈ lat hvt hR A Λl, ∀ y₂ ∈ lat hvt hR A Λl, y₁ ∉ ϖ • lat hvt hR A Λl →
        TensorModule.mk _ _ (fW hvt hR μ (List.replicate k₁ i) ⊗ₜ[k] y₁) -
          TensorModule.mk _ _ (fW hvt hR μ (List.replicate k₂ i) ⊗ₜ[k] y₂) ∈
            ϖ • LL hvt hR A μ Λl → k₁ = k₂ ∧ y₁ - y₂ ∈ ϖ • lat hvt hR A Λl := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  choose m₁ hm₁ using fun n : ℕ ↦ exists_form_mem_of_large (hR := hR) hinj hϖ hϖv hk hfund
    (n • Finsupp.single i 1)
  choose m₂ hm₂ using fun n : ℕ ↦ exists_form_fW_fW (hR := hR) hinj hϖ hϖv hk hfund
    (n • Finsupp.single i 1)
  refine ⟨∑ n ∈ Finset.range (M + 1), (m₁ n + m₂ n), fun μ Λl hμ k₁ hk₁ k₂ hk₂ y₁ hy₁ y₂ hy₂
    hy₁0 h ↦ ?_⟩
  have hle : m₁ k₁ + m₂ k₁ ≤ ∑ n ∈ Finset.range (M + 1), (m₁ n + m₂ n) :=
    Finset.single_le_sum (f := fun n ↦ m₁ n + m₂ n) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  have hμ₁ : ∀ j, (m₁ k₁ : ℤ) ≤ μ.1 (R.coroot j) := fun j ↦ by have := hμ j; omega
  have hμ₂ : ∀ j, (m₂ k₁ : ℤ) ≤ μ.1 (R.coroot j) := fun j ↦ by have := hμ j; omega
  set z₁ := fW hvt hR μ (List.replicate k₁ i)
  set z₂ := fW hvt hR μ (List.replicate k₂ i)
  have hz₁L : z₁ ∈ lat hvt hR A μ := IrreducibleModule.fWord_mem_lattice hR _ μ.2 A _
  have hz₁w : z₁ ∈ wsp μ (k₁ • Finsupp.single i 1) := by
    have := fW_mem_wsp hvt hR μ (List.replicate k₁ i)
    rwa [wordWeight_replicate] at this
  set f := IrreducibleModule.form μ.1 hR hv' z₁
  have hf : ∀ x ∈ lat hvt hR A μ, ∃ a : A, f x = algebraMap A k a := hm₁ k₁ μ hμ₁ z₁ hz₁L hz₁w
  have hpr := prL_mem_smul_lat hf h
  rw [map_sub, prL_tmul, prL_tmul] at hpr
  obtain ⟨e₀, he₀⟩ := hm₂ k₁ μ hμ₂ _ _ (wordWeight_replicate i k₁) (wordWeight_replicate i k₁)
  rw [sub_self, ite_eq_left (zero_mem _)] at he₀
  change f z₁ • y₁ - f z₂ • y₂ ∈ _ at hpr
  rw [he₀] at hpr
  have hsplit : ∀ y ∈ lat hvt hR A Λl, (1 + algebraMap A k (ϖ * e₀)) • y - y ∈
      ϖ • lat hvt hR A Λl := fun y hy ↦ by
    rw [add_smul, one_smul, add_sub_cancel_left, algebraMap_smul, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ hy)
  by_cases hk : k₁ = k₂
  · subst hk
    refine ⟨rfl, ?_⟩
    have := sub_mem (sub_mem hpr (hsplit y₁ hy₁)) (neg_mem (hsplit y₂ hy₂))
    convert this using 1
    rw [he₀]; abel
  · exfalso
    have hz0 : f z₂ = 0 := by
      refine (IrreducibleModule.isContravariant_form hR hv').eq_zero_of_ne ?_ hz₁w
        (by have := fW_mem_wsp hvt hR μ (List.replicate k₂ i); rwa [wordWeight_replicate] at this)
        hv'
      intro he
      have := LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective he)
      have := congrArg (fun f ↦ f i) this
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
      exact hk this
    rw [hz0, zero_smul, sub_zero] at hpr
    exact hy₁0 (by have := sub_mem hpr (hsplit y₁ hy₁); simpa using this)

include hR in
/-- If `π̄_λ(b) ≠ 0` and `ẽᵢ b ≠ 0`, then `π̄_λ(ẽᵢ b) ≠ 0` (since `b = f̃ᵢ ẽᵢ b`). -/
theorem fW_notMem_of_kE (Λ : Dom R) (i : I) {w w' : List I}
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (h0 : kE (D := D) hvt i (fWi hvt w) ∉ ϖ • latInf hvt A)
    (h : kE (D := D) hvt i (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf hvt A) :
    fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ := by
  intro hw'
  have h1 := fWi_sub_mem_of_kE (hR := hR) hinj hϖ hϖv hk hfund i h0 h
  have e1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund h1 Λ
  have e2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w Λ
  have e3 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (i :: w') Λ
  have e4 : fW hvt hR Λ (i :: w') ∈ ϖ • lat hvt hR A Λ := by
    rw [fW_cons]; exact kashiwaraF_mem_smul_lat Λ i hw'
  rw [map_sub] at e1
  refine hw ?_
  have := add_mem (add_mem (sub_mem e1 e2) e3) e4
  convert neg_mem (neg_mem this) using 1
  simp only [neg_neg]; abel

include hR in
/-- Along `ẽᵢ`, `π̄_λ` stays nonzero and commutes with `ẽᵢ` ([Jan] 10.13). -/
theorem exists_kE_pow_chain (Λ : Dom R) (i : I) {w : List I}
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) :
    ∀ n, (kE (D := D) hvt i ^ n) (fWi hvt w) ∉ ϖ • latInf hvt A →
      ∃ wn : List I, (kE (D := D) hvt i ^ n) (fWi hvt w) - fWi hvt wn ∈ ϖ • latInf hvt A ∧
        fW hvt hR Λ wn ∉ ϖ • lat hvt hR A Λ ∧
        (eK hvt hR Λ i ^ n) (fW hvt hR Λ w) - fW hvt hR Λ wn ∈ ϖ • lat hvt hR A Λ := by
  have hL := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ
  have heS : ∀ x, x ∈ ϖ • lat hvt hR A Λ → eK hvt hR Λ i x ∈ ϖ • lat hvt hR A Λ :=
    fun _ hx ↦ LinearMap.map_mem_smul_of_mem ϖ (fun m hm ↦ hL.kashiwaraE_mem i m hm) hx
  intro n
  induction n with
  | zero => intro _; exact ⟨w, by simp, hw, by simp⟩
  | succ n ih =>
    intro hn
    have hn' : (kE (D := D) hvt i ^ n) (fWi hvt w) ∉ ϖ • latInf hvt A := fun h ↦ hn (by
      rw [pow_succ', Module.End.mul_apply]
      exact kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i h)
    obtain ⟨wn, h1, h2, h3⟩ := ih hn'
    have h4 := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i h1
    rw [map_sub] at h4
    have h5 : kE (D := D) hvt i (fWi hvt wn) ∉ ϖ • latInf hvt A := fun h ↦ hn (by
      rw [pow_succ', Module.End.mul_apply]; simpa using add_mem h4 h)
    rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i wn with h6 | ⟨w', h6⟩
    · exact absurd h6 h5
    refine ⟨w', ?_, fW_notMem_of_kE (hR := hR) hinj hϖ hϖv hk hfund Λ i h2 h5 h6, ?_⟩
    · rw [pow_succ', Module.End.mul_apply]; simpa using add_mem h4 h6
    · -- `ẽ^{n+1} y ≡ ẽ (f̃_{wₙ} v) ≡ π(ẽ f̃_{wₙ} 1) ≡ π(f̃_{w'} 1) ≡ f̃_{w'} v`
      have k1 := heS _ h3
      rw [map_sub] at k1
      have k2 := evq_kE_fWi_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i h2
      have k3 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund h6 Λ
      rw [map_sub] at k3
      have k4 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w' Λ
      rw [pow_succ', Module.End.mul_apply]
      have := add_mem (add_mem (sub_mem k1 k2) k3) k4
      convert this using 1; abel

omit hinj hϖ hϖv hk hfund [IsDomain A] [IsDiscreteValuationRing A] [Finite I] in
lemma eK_pow_dFV {Λ : Dom R} {i : I} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1} {kk a : ℕ}
    {u : IrreducibleModule R v Λ.1} (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    ∀ n ≤ kk, (eK hvt hR Λ i ^ n) (dFV (hvt := hvt) (hR := hR) Λ i kk u) =
      dFV (hvt := hvt) (hR := hR) Λ i (kk - n) u := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [pow_succ', Module.End.mul_apply, ih (by omega),
      show kk - n = (kk - (n + 1)) + 1 by omega]
    have hle := h.le
    exact IntegrableSl2.eTilde_dF_succ (pow_d_ne_zero i)
      (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) h.E_smul h.prim.1 (by omega)

omit hinj hϖ hϖv hk hfund [IsDomain A] [IsDiscreteValuationRing A] [Finite I] in
lemma eK_pow_succ_dFV {Λ : Dom R} {i : I} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1}
    {kk a : ℕ} {u : IrreducibleModule R v Λ.1} (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    (eK hvt hR Λ i ^ (kk + 1)) (dFV (hvt := hvt) (hR := hR) Λ i kk u) = 0 := by
  rw [pow_succ', Module.End.mul_apply, eK_pow_dFV h kk le_rfl, Nat.sub_self,
    IntegrableSl2.dF_zero]
  exact IntegrableSl2.eTilde_of_primitive (pow_d_ne_zero i)
    (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) h.E_smul h.prim.1

include hR in
/-- **`εᵢ(π̄_λ b) = εᵢ(b)`**: the string position `kk` of `f̃_w v_λ ≠ 0` is `εᵢ(f̃_w 1)`. -/
theorem kE_pow_of_isStr (Λ : Dom R) (i : I) {w : List I} {ν : I →₀ ℕ} {kk a : ℕ}
    {u : IrreducibleModule R v Λ.1} (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (hstr : IsStr hvt hR ϖ Λ i ν (fW hvt hR Λ w) kk a u) :
    (kE (D := D) hvt i ^ kk) (fWi hvt w) ∉ ϖ • latInf hvt A ∧
      (kE (D := D) hvt i ^ (kk + 1)) (fWi hvt w) ∈ ϖ • latInf hvt A := by
  classical
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hL := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ
  have heS : ∀ n x, x ∈ ϖ • lat hvt hR A Λ → (eK hvt hR Λ i ^ n) x ∈ ϖ • lat hvt hR A Λ := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact LinearMap.map_mem_smul_of_mem ϖ (fun m hm ↦ hL.kashiwaraE_mem i m hm) (ih x hx)
  -- `ẽⁿ y ≡ F^{(kk-n)} u`
  have hcong : ∀ n, (eK hvt hR Λ i ^ n) (fW hvt hR Λ w) -
      (eK hvt hR Λ i ^ n) (dFV (hvt := hvt) (hR := hR) Λ i kk u) ∈ ϖ • lat hvt hR A Λ := by
    intro n; rw [← map_sub]; exact heS n _ hstr.sub
  have hnot : ∀ j ≤ kk, dFV (hvt := hvt) (hR := hR) Λ i j u ∉ ϖ • lat hvt hR A Λ :=
    hstr.dFV_notMem (fun s _ ↦ (hall s).1) rfl hϖ0
  constructor
  · intro hmem
    have hex : ∃ n, (kE (D := D) hvt i ^ n) (fWi hvt w) ∈ ϖ • latInf hvt A := ⟨kk, hmem⟩
    obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀, (kE (D := D) hvt i ^ n₀) (fWi hvt w) ∈ ϖ • latInf hvt A ∧
        ∀ m < n₀, (kE (D := D) hvt i ^ m) (fWi hvt w) ∉ ϖ • latInf hvt A :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩
    have hn₀le : n₀ ≤ kk := by
      by_contra h; exact hmin kk (by omega) hmem
    have hpos : n₀ ≠ 0 := fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w (by
      simpa [h] using hn₀)
    obtain ⟨n₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hn₁ : (kE (D := D) hvt i ^ n₁) (fWi hvt w) ∉ ϖ • latInf hvt A := hmin n₁ (by omega)
    obtain ⟨w', h1, h2, h3⟩ :=
      exists_kE_pow_chain (hR := hR) hinj hϖ hϖv hk hfund Λ i hw n₁ hn₁
    -- `ẽ (f̃_{w'} 1) ∈ ϖ L(∞)`
    have h4 : kE (D := D) hvt i (fWi hvt w') ∈ ϖ • latInf hvt A := by
      have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i h1
      rw [map_sub, ← Module.End.mul_apply, ← pow_succ'] at this
      simpa using sub_mem hn₀ this
    have h5 := evq_kE_fWi_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i h2
    have h6 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund h4 Λ
    have h7 : eK hvt hR Λ i (fW hvt hR Λ w') ∈ ϖ • lat hvt hR A Λ := by
      simpa using sub_mem h6 h5
    have h8 := LinearMap.map_mem_smul_of_mem ϖ (fun m hm ↦ hL.kashiwaraE_mem i m hm) h3
    rw [map_sub, ← Module.End.mul_apply, ← pow_succ'] at h8
    have h9 := hcong (n₁ + 1)
    rw [eK_pow_dFV hstr (n₁ + 1) hn₀le] at h9
    exact hnot (kk - (n₁ + 1)) (by omega) (by
      have := sub_mem (add_mem h8 h7) h9
      convert this using 1; abel)
  · by_contra hmem
    obtain ⟨w', -, h2, h3⟩ :=
      exists_kE_pow_chain (hR := hR) hinj hϖ hϖv hk hfund Λ i hw (kk + 1) hmem
    have h9 := hcong (kk + 1)
    rw [eK_pow_succ_dFV hstr, sub_zero] at h9
    exact h2 (by simpa using sub_mem h9 h3)

omit hϖv hk hfund [Finite I] in
/-- String data of `f̃ᵢᵐ v_μ = Fᵢ^{(m)} v_μ`. -/
lemma isStr_replicate (μ : Dom R) (i : I) (m : ℕ) (hm : (m : ℤ) ≤ μ.1 (R.coroot i)) :
    IsStr hvt hR ϖ μ i (m • Finsupp.single i 1) (fW hvt hR μ (List.replicate m i)) m
      (μ.1 (R.coroot i)).toNat (IrreducibleModule.hwv R v μ.1) where
  x_wt := by have := fW_mem_wsp hvt hR μ (List.replicate m i); rwa [wordWeight_replicate] at this
  mem := IrreducibleModule.hwv_mem_lattice hR _ μ.2 A
  wt := by
    have := IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := μ.1)
    convert this using 2
    rw [show m • Finsupp.single i 1 = Finsupp.single i m by simp, R.rootSum_single,
      sub_add_cancel]
  E_smul := IrreducibleModule.E_smul_hwv (R := R) (v := v) (Λ := μ.1) i
  node := by
    rw [show m • Finsupp.single i 1 = Finsupp.single i m by simp, R.rootSum_single,
      AddMonoidHom.sub_apply, AddMonoidHom.nsmul_apply, R.root_coroot, D.cartanMatrix_self,
      Int.toNat_of_nonneg (μ.2 i), nsmul_eq_mul]
    ring
  notMem := hwv_notMem hinj ((IsLocalRing.mem_maximalIdeal ϖ).1 hϖ) μ
  le := by omega
  sub := by rw [fW_replicate, sub_self]; exact zero_mem _

include hR in
/-- `T(ẽᵢ b) ≡ ẽᵢ T(b)` for `b = f̃_w 1` with `π̄_{μ+λ}(b) ≠ 0`. -/
theorem tensorEmb_evq_kE_sub (μ Λl : Dom R) (i : I) {w : List I}
    (hw : fW hvt hR (μ + Λl) w ∉ ϖ • lat hvt hR A (μ + Λl)) :
    tensorEmb hvt hR μ.2 Λl.2 (evq hvt (μ + Λl) (kE hvt i (fWi hvt w))) -
      eT hvt hR μ Λl i (tensorEmb hvt hR μ.2 Λl.2 (evq hvt (μ + Λl) (fWi hvt w))) ∈
        ϖ • LL hvt hR A μ Λl := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hTS : ∀ x, x ∈ ϖ • lat hvt hR A (μ + Λl) →
      tensorEmb hvt hR μ.2 Λl.2 x ∈ ϖ • LL hvt hR A μ Λl := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [← algebraMap_smul k, LinearMap.map_smul_of_tower, algebraMap_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (tensorEmb_mem_LL hϖ hϖv (fun t ↦ (hall t).1) hy)
  have h1 := hTS _ (evq_kE_fWi_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i hw)
  rw [map_sub] at h1
  have h2 : tensorEmb hvt hR μ.2 Λl.2 (eK hvt hR (μ + Λl) i (fW hvt hR (μ + Λl) w)) =
      eT hvt hR μ Λl i (tensorEmb hvt hR μ.2 Λl.2 (fW hvt hR (μ + Λl) w)) :=
    map_kashiwaraE _ _ _ _ _ _
  have h3 := hTS _ (evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w (μ + Λl))
  rw [map_sub] at h3
  have h3w : tensorEmb hvt hR μ.2 Λl.2 (evq hvt (μ + Λl) (fWi hvt w)) -
      tensorEmb hvt hR μ.2 Λl.2 (fW hvt hR (μ + Λl) w) ∈
        weightSpace R v (TM v μ Λl) (μ.1 + Λl.1 - R.rootSum (wordWeight w)) := by
    rw [← map_sub]
    exact map_mem_weightSpace _ (sub_mem (evq_mem_wsp (hvt := hvt) hR
      (fWi_mem_Uw (hvt := hvt) w) (μ + Λl)) (fW_mem_wsp hvt hR (μ + Λl) w))
  have h4 := eT_mem_smul_LL hϖ hϖv (d := (wordWeight w).degree) (fun s _ ↦ (hall s).1) i rfl h3 h3w
  rw [map_sub, ← h2] at h4
  have := sub_mem h1 h4
  convert this using 1; abel

include hR in
/-- **`*`-string data**: every `f̃_w 1` is congruent to `P fᵢ^{(m)}` with `e''ᵢ P = 0` and
`P ≡ f̃_{w₀} 1`, i.e. `b = f̃ᵢ*ᵐ b₀` with `ẽᵢ* b₀ = 0`. -/
theorem exists_starStr [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (w : List I) :
    ∃ (m : ℕ) (P : Um D v) (w₀ : List I), P ∈ latInf hvt A ∧ P ∈ Uw D v (wordWeight w₀) ∧
      (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0 ∧
      P - fWi hvt w₀ ∈ ϖ • latInf hvt A ∧ fWi hvt w - rmulF hvt i m P ∈ ϖ • latInf hvt A ∧
      wordWeight w₀ + Finsupp.single i m = wordWeight w := by
  classical
  obtain ⟨ws, hws⟩ := starU_fWi_sub_mem (hR := hR) hinj hϖ hϖv hk hfund (D := D) (A := A) w
  set u := fWi (D := D) hvt ws
  obtain ⟨m, w₁, hm1, hmr, hwt⟩ := exists_comp_fWi (hR := hR) hinj hϖ hϖv hk hfund i ws
  obtain ⟨w₂, hw₂⟩ := starU_fWi_sub_mem (hR := hR) hinj hϖ hϖv hk hfund (D := D) (A := A) w₁
  set c := comp hvt i m u
  have hcL : c ∈ latInf hvt A := comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i m
    (NegativePart.fWord_mem_latticeInf _ _ ws)
  have hcw : c ∈ Uw D v (wordWeight w₁) := by
    have h := component_mem_Uw (hvt := hvt) i (fWi_mem_Uw (D := D) (hvt := hvt) ws) m
    rwa [← hwt, add_tsub_cancel_right] at h
  -- weights of the `*`-images
  have hw₁w : wordWeight w₂ = wordWeight w₁ := by
    refine wordWeight_eq_of_mem_Uw (starU_mem_Uw (fWi_mem_Uw (hvt := hvt) w₁)) (fun h ↦ ?_) hw₂
    have := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h
    rw [starU_starU] at this
    exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₁ this
  have hwsw : wordWeight ws = wordWeight w := by
    refine (wordWeight_eq_of_mem_Uw (starU_mem_Uw (fWi_mem_Uw (hvt := hvt) w)) (fun h ↦ ?_)
      hws)
    have := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h
    rw [starU_starU] at this
    exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w this
  refine ⟨m, starU D v c, w₂, starU_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund hcL,
    hw₁w ▸ starU_mem_Uw hcw, by rw [starU_starU]; exact e_comp i m u, ?_, ?_, ?_⟩
  · have h1 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund hm1
    rw [map_sub] at h1
    simpa using add_mem h1 hw₂
  · -- `u ≡ fᵢ^{(m)} c`
    obtain ⟨N, hN, -⟩ := exists_sum_comp (hvt := hvt) i u
    have hmN : m < N := by
      by_contra h
      rw [show c = 0 from hN m (by omega), zero_sub] at hm1
      exact fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₁ (by simpa using neg_mem hm1)
    have hu := eq_sum_comp (hvt := hvt) i u (N := N) hN
    have hkFpow : ∀ n (x : Um D v), x ∈ ϖ • latInf hvt A → (kF hvt i ^ n) x ∈ ϖ • latInf hvt A := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
        intro x hx
        rw [pow_succ', Module.End.mul_apply]
        exact kF_mem_smul_latInf i (ih x hx)
    have hrest : u - (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).df m c ∈
        ϖ • latInf hvt A := by
      rw [hu, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hmN), add_sub_cancel_left]
      refine Submodule.sum_mem _ fun r hr ↦ ?_
      rw [← kF_pow_eq_df (hvt := hvt) i (e_comp i r u)]
      exact hkFpow r _ (hmr r (Finset.ne_of_mem_erase hr))
    have h1 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund (add_mem hws hrest)
    rw [sub_add_sub_cancel, map_sub, starU_starU] at h1
    rwa [rmulF_apply, starU_starU]
  · rw [hw₁w, ← hwsw, ← hwt]

include hR in
/-- **Uniqueness of `*`-string data**: `P fᵢ^{(m)} ≡ P' fᵢ^{(m')}` with `e''ᵢ P = e''ᵢ P' = 0` and
`P ∉ ϖ L(∞)` forces `m = m'` and `P ≡ P'`. -/
theorem eq_of_rmulF_sub_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {m m' : ℕ}
    {P P' : Um D v} (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0)
    (he' : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P') = 0)
    (hP0 : P ∉ ϖ • latInf hvt A)
    (h : rmulF hvt i m P - rmulF hvt i m' P' ∈ ϖ • latInf hvt A) :
    m = m' ∧ P - P' ∈ ϖ • latInf hvt A := by
  classical
  have hq0 := NegativePart.pow_d_ne_zero (D := D) (NeZero.ne v) i
  have hq := NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i
  have h1 := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h
  rw [map_sub, rmulF_apply, rmulF_apply, starU_starU, starU_starU] at h1
  have h2 := comp_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i m h1
  rw [map_sub] at h2
  change (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).component hq0 hq m _ -
    (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).component hq0 hq m _ ∈ _ at h2
  rw [BosonModule.component_df hq0 hq he, BosonModule.component_df hq0 hq he', ite_eq_left rfl]
    at h2
  by_cases hmm : m' = m
  · subst hmm
    refine ⟨rfl, ?_⟩
    rw [ite_eq_left rfl] at h2
    have := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h2
    rwa [map_sub, starU_starU, starU_starU] at this
  · rw [ite_eq_right hmm, sub_zero] at h2
    exfalso
    have := starU_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund h2
    rw [starU_starU] at this
    exact hP0 this

include hR in
/-- `T` is injective modulo `ϖ` on `L(∞) ∩ U⁻_{-ν}` for `μ ≫ 0`, including `ν = 0`. -/
theorem exists_large_inj (ν : I →₀ ℕ) :
    ∃ N : ℕ, ∀ μ Λ₂ : Dom R, (∀ j, (N : ℤ) ≤ μ.1 (R.coroot j)) →
      ∀ u ∈ latInf hvt A, u ∈ Uw D v ν →
        tensorEmb hvt hR μ.2 Λ₂.2 (evq hvt (μ + Λ₂) u) ∈ ϖ • LL hvt hR A μ Λ₂ →
          u ∈ ϖ • latInf hvt A := by
  classical
  by_cases hν : ν.degree = 0
  · have hν0 : ν = 0 := by
      ext j
      have := Finsupp.le_degree j ν
      simp only [hν, nonpos_iff_eq_zero] at this
      simpa using this
    subst hν0
    refine ⟨0, fun μ Λ₂ _ u hu huw hT ↦ ?_⟩
    have hspan := mem_span_fWi_of_mem hu huw
    have hset : fWi (D := D) hvt '' {w : List I | wordWeight w = 0} = {fWi hvt []} := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have := degree_wordWeight w
        rw [hw, map_zero] at this
        rw [List.eq_nil_of_length_eq_zero this.symm]
      · rintro rfl; exact ⟨[], by simp, rfl⟩
    rw [hset] at hspan
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hspan
    have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
    have e1 : evq hvt (μ + Λ₂) (fWi (D := D) hvt []) = IrreducibleModule.hwv R v (μ.1 + Λ₂.1) := by
      change ev R v _ 1 = _; exact ev_one _
    have e2 : tensorEmb hvt hR μ.2 Λ₂.2 (evq hvt (μ + Λ₂) (c • fWi (D := D) hvt [])) =
        algebraMap A k c • TensorModule.mk _ _ (IrreducibleModule.hwv R v μ.1 ⊗ₜ[k]
          IrreducibleModule.hwv R v Λ₂.1) := by
      rw [← algebraMap_smul k c, map_smul, LinearMap.map_smul_of_tower, e1, tensorEmb_hwv]
    have h1 := Sh_mem_smul hT
    rw [e2, map_smul, Sh_tmul, IrreducibleModule.form_hwv, one_smul, algebraMap_smul] at h1
    obtain ⟨y, hy, ey⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    have hyw : y ∈ wsp Λ₂ 0 := by
      have h2 : c • IrreducibleModule.hwv R v Λ₂.1 ∈ wsp Λ₂ 0 := by
        rw [← algebraMap_smul k]; exact Submodule.smul_mem _ _ (hwv_mem_wsp Λ₂)
      rw [← ey, ← algebraMap_smul k] at h2
      have := Submodule.smul_mem _ (algebraMap A k ϖ)⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ hϖ0, one_smul] at this
    obtain ⟨a, rfl⟩ := exists_eq_smul_hwv hy hyw
    have hc : c = ϖ * a := by
      apply hinj
      have hv0 := hwv_ne_zero hR (pow_ne_one_of_transcendental' hvt) Λ₂.1
      rw [smul_smul, ← algebraMap_smul k (ϖ * a), ← algebraMap_smul k c] at ey
      exact (smul_left_injective k hv0 ey).symm
    rw [hc, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (Submodule.smul_mem _ _ (NegativePart.fWord_mem_latticeInf _ _ []))
  · exact exists_large_mem_smul_latInf_of_tensorEmb_mem (hR := hR) hinj hϖ hϖv hk hfund hν

include hR in
/-- `rmulF_tensor_congr` including the weight `0`. -/
theorem rmulF_tensor_congr' [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (m : ℕ)
    (ν : I →₀ ℕ) :
    ∃ N : ℕ, ∀ μ Λl : Dom R, (∀ j, (N : ℤ) ≤ μ.1 (R.coroot j)) →
      Λl.1 (R.coroot i) = 0 → (∀ j, j ≠ i → (N : ℤ) ≤ Λl.1 (R.coroot j)) →
      ∀ P : Um D v, P ∈ latInf hvt A → P ∈ Uw D v ν →
        (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0 →
        ∀ w₀ : List I, P - fWi hvt w₀ ∈ ϖ • latInf hvt A →
        tensorEmb hvt hR μ.2 Λl.2 (evq hvt (μ + Λl) (rmulF hvt i m P)) -
          TensorModule.mk _ _ (fW hvt hR μ (List.replicate m i) ⊗ₜ[k]
            fW hvt hR Λl w₀) ∈ ϖ • LL hvt hR A μ Λl := by
  by_cases hν' : (ν + m • Finsupp.single i 1).degree = 0
  · have hm : m = 0 := by
      have h := hν'
      simp only [map_add, map_nsmul, Finsupp.degree_single, smul_eq_mul, mul_one] at h
      omega
    have hν0 : ν = 0 := by
      subst hm
      ext j
      have := Finsupp.le_degree j ν
      simp only [zero_smul, add_zero] at hν'
      simp only [hν', nonpos_iff_eq_zero] at this
      simpa using this
    subst hm hν0
    refine ⟨0, fun μ Λl _ _ _ P hP hPw he w₀ hw₀ ↦ ?_⟩
    have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
    have hP0 : P ∉ ϖ • latInf hvt A := fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀
      (by simpa using sub_mem h hw₀)
    have hw₀w := wordWeight_eq_of_mem_Uw hPw hP0 hw₀
    have hw₀e : w₀ = [] := by
      have := degree_wordWeight w₀
      rw [hw₀w, map_zero] at this
      exact List.eq_nil_of_length_eq_zero this.symm
    subst hw₀e
    rw [rmulF_zero, List.replicate_zero, fW_nil, fW_nil]
    have e1 : evq hvt (μ + Λl) (fWi (D := D) hvt []) = IrreducibleModule.hwv R v (μ.1 + Λl.1) := by
      change ev R v _ 1 = _; exact ev_one _
    have h1 := tensorEmb_evq_mem_smul_LL (hR := hR) hinj hϖ hϖv hk hfund μ Λl hw₀
    rw [map_sub, map_sub, e1, tensorEmb_hwv] at h1
    exact h1
  · obtain ⟨N, h⟩ := rmulF_tensor_congr (hR := hR) hinj hϖ hϖv hk hfund i m ν hν'
    exact ⟨N, fun μ Λl hμ hΛli hΛl P hP hPw he w₀ hw₀ ↦
      (h μ Λl hμ hΛli hΛl P hP hPw he w₀ hw₀).2⟩

set_option maxHeartbeats 1600000 in
-- one long argument assembling the tensor product rule through `T`
include hR in
/-- **`ẽᵢ` on `f̃ᵢ*ᵐ b₀`** ([Kas93a] Thm. 2.2.1, the case `j = i`): let `b ≡ P fᵢ^{(m)}` with
`e''ᵢ P = 0`, `P ≡ b₀ = f̃_{w₀} 1` of weight `-ν`, and `εᵢ(b₀) = kk`; put
`φ = kk - ⟨hᵢ, ν⟩ = φᵢ(b₀)`. If `m ≤ φ`, then `ẽᵢ b = 0` when `ẽᵢ b₀ = 0`, and otherwise
`ẽᵢ b ≡ P' fᵢ^{(m)}` with `e''ᵢ P' = 0`, `P' ≡ ẽᵢ P`. If `φ < m`, then `ẽᵢ b ≡ P fᵢ^{(m-1)}`. -/
theorem kE_rmulF [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {m : ℕ} {ν : I →₀ ℕ}
    {P : Um D v} (hP : P ∈ latInf hvt A) (hPw : P ∈ Uw D v ν)
    (he : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0)
    {w₀ : List I} (hw₀ : P - fWi hvt w₀ ∈ ϖ • latInf hvt A) {kk : ℕ}
    (hkk1 : (kE hvt i ^ kk) (fWi (D := D) hvt w₀) ∉ ϖ • latInf hvt A)
    (hkk2 : (kE hvt i ^ (kk + 1)) (fWi (D := D) hvt w₀) ∈ ϖ • latInf hvt A)
    {w : List I} (hw : fWi hvt w - rmulF hvt i m P ∈ ϖ • latInf hvt A) :
    ((m : ℤ) ≤ kk - R.rootSum ν (R.coroot i) →
      (kE hvt i P ∈ ϖ • latInf hvt A → kE hvt i (fWi (D := D) hvt w) ∈ ϖ • latInf hvt A) ∧
      (kE hvt i P ∉ ϖ • latInf hvt A → ∃ P' : Um D v, P' ∈ latInf hvt A ∧
        (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P') = 0 ∧
        P' - kE hvt i P ∈ ϖ • latInf hvt A ∧
        kE hvt i (fWi hvt w) - rmulF hvt i m P' ∈ ϖ • latInf hvt A)) ∧
    (kk - R.rootSum ν (R.coroot i) < (m : ℤ) →
      kE hvt i (fWi (D := D) hvt w) - rmulF hvt i (m - 1) P ∈ ϖ • latInf hvt A) := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  set ν' := ν + m • Finsupp.single i 1
  set M := ν' i
  have hmM : m ≤ M := by simp [M, ν']
  -- powers of `ẽᵢ`
  have hpow : ∀ a c (x : Um D v), (kE hvt i ^ a) x ∈ ϖ • latInf hvt A → a ≤ c →
      (kE hvt i ^ c) x ∈ ϖ • latInf hvt A := by
    intro a c x hx hac
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hac
    induction d with
    | zero => simpa using hx
    | succ d ih =>
      rw [← add_assoc, pow_succ', Module.End.mul_apply]
      exact kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i (ih (by omega))
  -- the parameters
  obtain ⟨N₁, hN₁⟩ := rmulF_tensor_congr' (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i m ν
  choose N₂ hN₂ using fun m' : ℕ ↦
    rmulF_tensor_congr' (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i m'
    (ν' - Finsupp.single i 1 - Finsupp.single i m')
  obtain ⟨N₃, hN₃⟩ := exists_tmul_cmp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i M
  obtain ⟨N₄, hN₄⟩ := exists_large_inj (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
    (ν' - Finsupp.single i 1)
  obtain ⟨N₅, hN₅⟩ := evq_notMem_smul_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i ν
  set N := N₁ + (∑ m' ∈ Finset.range (M + 1), N₂ m') + N₃ + N₄ + N₅ + M
  obtain ⟨Λl, hΛli, hΛl⟩ := exists_dom_wall hfund i N
  obtain ⟨μ, hμ⟩ := exists_dom_ge hfund N
  have hle : ∀ m' ≤ M, N₂ m' ≤ N := fun m' hm' ↦ by
    have := Finset.single_le_sum (f := N₂) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 (show m' < M + 1 by omega))
    omega
  have hμ' : ∀ c : ℕ, c ≤ N → ∀ j, (c : ℤ) ≤ μ.1 (R.coroot j) := fun c hc j ↦ by
    have := hμ j; omega
  have hΛl' : ∀ c : ℕ, c ≤ N → ∀ j, j ≠ i → (c : ℤ) ≤ Λl.1 (R.coroot j) := fun c hc j hj ↦ by
    have := hΛl j hj; omega
  -- `T`
  set T : Um D v → TM v μ Λl := fun u ↦ tensorEmb hvt hR μ.2 Λl.2 (evq hvt (μ + Λl) u)
  have hTsub : ∀ u u', T (u - u') = T u - T u' := fun u u' ↦ by simp [T]
  have hTS : ∀ u, u ∈ ϖ • latInf hvt A → T u ∈ ϖ • LL hvt hR A μ Λl := fun u hu ↦
    tensorEmb_evq_mem_smul_LL (hR := hR) hinj hϖ hϖv hk hfund μ Λl hu
  set z : ℕ → IrreducibleModule R v μ.1 := fun c ↦ fW hvt hR μ (List.replicate c i)
  have hzL : ∀ c, z c ∈ lat hvt hR A μ := fun c ↦ IrreducibleModule.fWord_mem_lattice hR _ μ.2 A _
  have hLl := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λl
  have hfWl : ∀ c : List I, fW hvt hR Λl c ∈ lat hvt hR A Λl := fun c ↦
    IrreducibleModule.fWord_mem_lattice hR _ Λl.2 A c
  -- `P` and `b₀`
  have hP0 : P ∉ ϖ • latInf hvt A := fun h ↦ fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w₀
    (by simpa using sub_mem h hw₀)
  have hw₀w : wordWeight w₀ = ν := wordWeight_eq_of_mem_Uw hPw hP0 hw₀
  set y := fW hvt hR Λl w₀
  have hPy : evq hvt Λl P - y ∈ ϖ • lat hvt hR A Λl := by
    have h1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund hw₀ Λl
    have h2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w₀ Λl
    rw [map_sub] at h1
    simpa using add_mem h1 h2
  have hy0 : y ∉ ϖ • lat hvt hR A Λl := fun h ↦
    hN₅ Λl hΛli (hΛl' N₅ (by omega)) P hP hPw he hP0 (by simpa using add_mem hPy h)
  -- `b = f̃_w 1`
  have hQ0 : rmulF hvt i m P ∉ ϖ • latInf hvt A := fun h ↦
    fWi_notMem (hR := hR) hinj hϖ hϖv hk hfund w (by simpa using add_mem hw h)
  have hww : wordWeight w = ν' := by
    have h1 := wordWeight_eq_of_mem_Uw (rmulF_mem_Uw (hvt := hvt) i m hPw) hQ0
      (show rmulF hvt i m P - fWi hvt w ∈ _ by have := neg_mem hw; rwa [neg_sub] at this)
    exact h1
  -- `T(b) ≡ zₘ ⊗ y`
  have hTx : T (fWi hvt w) - TensorModule.mk _ _ (z m ⊗ₜ[k] y) ∈ ϖ • LL hvt hR A μ Λl := by
    have h1 := hTS _ hw
    rw [hTsub] at h1
    have h2 := hN₁ μ Λl (hμ' N₁ (by omega)) hΛli (hΛl' N₁ (by omega)) P hP hPw he w₀ hw₀
    have := add_mem h1 h2
    convert this using 1; simp only [T, z]; abel
  -- string data
  have hstrz := isStr_replicate (hvt := hvt) (hR := hR) hinj hϖ μ i m (hμ' m (by omega) i)
  obtain ⟨kk', b, u', hstry⟩ := exists_isStr hϖ0 (d := ν.degree) (fun s _ ↦ (hall s).1)
    (fun s _ ↦ (hall s).2.1) (fun s _ ↦ (hall s).2.2.1) Λl i rfl (hfWl w₀)
    (hw₀w ▸ fW_mem_wsp hvt hR Λl w₀) (w := w₀) (by rw [sub_self]; exact zero_mem _) hy0
  have hkk : kk' = kk := by
    obtain ⟨h1, h2⟩ := kE_pow_of_isStr (hR := hR) hinj hϖ hϖv hk hfund Λl i hy0 hstry
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hkk1 (hpow _ _ _ h2 (by omega))
    · exact h1 (hpow _ _ _ hkk2 (by omega))
  subst hkk
  have hφ : (b : ℤ) - kk' = kk' - R.rootSum ν (R.coroot i) := by
    have := hstry.node
    rw [AddMonoidHom.sub_apply, hΛli] at this
    omega
  -- `T(ẽ b) ≡ ẽ(zₘ ⊗ y)`
  have hTlat : ∀ x, x ∈ ϖ • lat hvt hR A (μ + Λl) →
      tensorEmb hvt hR μ.2 Λl.2 x ∈ ϖ • LL hvt hR A μ Λl := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [← algebraMap_smul k, LinearMap.map_smul_of_tower, algebraMap_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (tensorEmb_mem_LL hϖ hϖv (fun t ↦ (hall t).1) hx₀)
  have hcmp0 : ∀ c ≤ M, ∀ y' ∈ lat hvt hR A Λl, y' ∉ ϖ • lat hvt hR A Λl →
      TensorModule.mk _ _ (z c ⊗ₜ[k] y') ∉ ϖ • LL hvt hR A μ Λl := by
    intro c hc y' hy' hy'0 h
    have := (hN₃ μ Λl (hμ' N₃ (by omega)) c hc c hc y' hy' 0 (zero_mem _) hy'0
      (by rw [tmul_zero, map_zero, sub_zero]; exact h)).2
    exact hy'0 (by simpa using this)
  have hfWw : fW hvt hR (μ + Λl) w ∉ ϖ • lat hvt hR A (μ + Λl) := by
    intro h
    have h1 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w (μ + Λl)
    have h2 := hTlat _ (by simpa using add_mem h1 h)
    have h3 : TensorModule.mk _ _ (z m ⊗ₜ[k] y) ∈ ϖ • LL hvt hR A μ Λl := by
      have := sub_mem h2 hTx; simpa [T] using this
    exact hcmp0 m hmM y (hfWl w₀) hy0 h3
  have hTkE := tensorEmb_evq_kE_sub (hR := hR) hinj hϖ hϖv hk hfund μ Λl i hfWw
  have hweight : T (fWi hvt w) - TensorModule.mk _ _ (z m ⊗ₜ[k] y) ∈
      weightSpace R v (TM v μ Λl) (μ.1 + Λl.1 - R.rootSum ν') := by
    refine sub_mem (map_mem_weightSpace _ (hww ▸ evq_mem_wsp (hvt := hvt) hR
      (fWi_mem_Uw (D := D) (hvt := hvt) w) (μ + Λl))) ?_
    have h := TensorModule.tmul_mem_weightSpace hstrz.x_wt hstry.x_wt
    convert h using 2
    simp only [ν', R.rootSum_add]; abel
  have hE := eT_mem_smul_LL hϖ hϖv (d := ν'.degree) (fun s _ ↦ (hall s).1) i rfl hTx hweight
  rw [map_sub] at hE
  have hrule := eT_tmul hϖ hϖv (d₁ := (m • Finsupp.single i 1).degree) (d₂ := ν.degree)
    (fun s _ ↦ (hall s).1) (fun s _ ↦ (hall s).1) rfl rfl hstrz hstry
  have hTE : T (kE hvt i (fWi hvt w)) -
      (if m ≤ b - kk' then TensorModule.mk _ _ (z m ⊗ₜ[k] eK hvt hR Λl i y)
        else TensorModule.mk _ _ (eK hvt hR μ i (z m) ⊗ₜ[k] y)) ∈ ϖ • LL hvt hR A μ Λl := by
    have := add_mem (add_mem hTkE hE) hrule
    convert this using 1; simp only [T]; abel
  -- `ẽᵢ b` lies in `U⁻_{-(ν'-αᵢ)}`
  have hkEw : kE hvt i (fWi (D := D) hvt w) ∈ Uw D v (ν' - Finsupp.single i 1) := by
    by_cases h : 1 ≤ ν' i
    · simpa using kE_pow_mem (hvt := hvt) i (hww ▸ fWi_mem_Uw (D := D) (hvt := hvt) w) 1 h
    · rw [kE_eq_zero_of_mem i (hww ▸ fWi_mem_Uw (D := D) (hvt := hvt) w) (by omega)]
      exact zero_mem _
  have hkExL : kE hvt i (fWi (D := D) hvt w) ∈ latInf hvt A :=
    kashiwaraE_mem_latInf' (hR := hR) hinj hϖ hϖv hk hfund i _
      (NegativePart.fWord_mem_latticeInf _ _ w)
  -- the decomposition of `ẽᵢ b`
  have hdec : kE hvt i (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A → ∃ (m' : ℕ) (P'' : Um D v)
      (w₀'' : List I), m' ≤ M ∧ P'' ∈ latInf hvt A ∧
      (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P'') = 0 ∧
      P'' - fWi hvt w₀'' ∈ ϖ • latInf hvt A ∧
      kE hvt i (fWi hvt w) - rmulF hvt i m' P'' ∈ ϖ • latInf hvt A ∧
      T (kE hvt i (fWi hvt w)) - TensorModule.mk _ _ (z m' ⊗ₜ[k] fW hvt hR Λl w₀'') ∈
        ϖ • LL hvt hR A μ Λl := by
    intro h0
    rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i w with h | ⟨w', hw'⟩
    · exact absurd h h0
    obtain ⟨m', P'', w₀'', hP''L, hP''w, he'', hP''₀, hw'r, hwt''⟩ :=
      exists_starStr (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i w'
    have hw'w : wordWeight w' = ν' - Finsupp.single i 1 :=
      wordWeight_eq_of_mem_Uw hkEw h0 hw'
    have hm'M : m' ≤ M := by
      have h1 := congrArg (fun f ↦ f i) hwt''
      have h2 := congrArg (fun f ↦ f i) hw'w
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply] at h1 h2
      omega
    have hP''w' : P'' ∈ Uw D v (ν' - Finsupp.single i 1 - Finsupp.single i m') := by
      rw [← hw'w, ← hwt'', add_tsub_cancel_right]; exact hP''w
    have hTP'' := hN₂ m' μ Λl (hμ' _ (hle m' hm'M)) hΛli (hΛl' _ (hle m' hm'M)) P'' hP''L hP''w'
      he'' w₀'' hP''₀
    have hsub : kE hvt i (fWi (D := D) hvt w) - rmulF hvt i m' P'' ∈ ϖ • latInf hvt A := by
      have := add_mem hw' hw'r; rwa [sub_add_sub_cancel] at this
    refine ⟨m', P'', w₀'', hm'M, hP''L, he'', hP''₀, hsub, ?_⟩
    have := add_mem (hTS _ hsub) hTP''
    rw [hTsub] at this
    convert this using 1; simp only [T]; abel
  have h11 : kE hvt i (fWi (D := D) hvt w₀) - kE hvt i P ∈ ϖ • latInf hvt A := by
    have := kashiwaraE_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i (neg_mem hw₀)
    rwa [neg_sub, map_sub] at this
  have h10 := evq_kE_fWi_sub_mem (hR := hR) hinj hϖ hϖv hk hfund i hy0
  have hle' := hstry.le
  refine ⟨fun hA ↦ ?_, fun hB ↦ ?_⟩
  · have hmb : m ≤ b - kk' := by omega
    rw [ite_eq_left hmb] at hTE
    refine ⟨fun hPA ↦ ?_, fun hPA ↦ ?_⟩
    · -- `ẽᵢ b₀ = 0`
      have h1 : kE hvt i (fWi (D := D) hvt w₀) ∈ ϖ • latInf hvt A := by
        simpa using add_mem h11 hPA
      have h2 : eK hvt hR Λl i y ∈ ϖ • lat hvt hR A Λl := by
        have := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund h1 Λl
        simpa using sub_mem this h10
      have h3 := add_mem hTE (tmul_mem_smul_right (hzL m) h2)
      rw [sub_add_cancel] at h3
      exact hN₄ μ Λl (hμ' N₄ (by omega)) _ hkExL hkEw h3
    · -- `ẽᵢ b₀ ≠ 0`
      have h12 : kE hvt i (fWi (D := D) hvt w₀) ∉ ϖ • latInf hvt A := fun h ↦
        hPA (by simpa using sub_mem h h11)
      rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund i w₀ with h | ⟨w₁, hw₁⟩
      · exact absurd h h12
      have hw₁0 := fW_notMem_of_kE (hR := hR) hinj hϖ hϖv hk hfund Λl i hy0 h12 hw₁
      have heKy : eK hvt hR Λl i y - fW hvt hR Λl w₁ ∈ ϖ • lat hvt hR A Λl := by
        have e1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund hw₁ Λl
        have e2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund w₁ Λl
        rw [map_sub] at e1
        have := add_mem (sub_mem e1 h10) e2
        convert this using 1; abel
      have heKyL : eK hvt hR Λl i y ∈ lat hvt hR A Λl := hLl.kashiwaraE_mem i y (hfWl w₀)
      have heKy0 : eK hvt hR Λl i y ∉ ϖ • lat hvt hR A Λl := fun h ↦
        hw₁0 (by simpa using sub_mem h heKy)
      have hkEx0 : kE hvt i (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A := by
        intro h
        have := sub_mem (hTS _ h) hTE
        rw [sub_sub_cancel] at this
        exact hcmp0 m hmM _ heKyL heKy0 this
      obtain ⟨m', P'', w₀'', hm'M, hP''L, he'', hP''₀, hsub, hT'⟩ := hdec hkEx0
      obtain ⟨hmm, hyy⟩ := hN₃ μ Λl (hμ' N₃ (by omega)) m hmM m' hm'M _ heKyL _ (hfWl w₀'')
        heKy0 (by have := sub_mem hT' hTE; rwa [sub_sub_sub_cancel_left] at this)
      subst hmm
      have hfW : fW hvt hR Λl w₁ - fW hvt hR Λl w₀'' ∈ ϖ • lat hvt hR A Λl := by
        have := sub_mem hyy heKy
        rwa [sub_sub_sub_cancel_left] at this
      have hfWi := fWi_sub_mem_of_fW_sub_mem (hR := hR) hinj hϖ hϖv hk hfund _ w₁ w₀'' rfl
        hw₁0 hfW
      refine ⟨P'', hP''L, he'', ?_, hsub⟩
      have := add_mem (add_mem (sub_mem hP''₀ hfWi) (neg_mem hw₁)) h11
      convert this using 1; abel
  · have hmb : ¬ m ≤ b - kk' := by omega
    have hm1 : 1 ≤ m := by omega
    rw [ite_eq_right hmb] at hTE
    have heKz : eK hvt hR μ i (z m) = z (m - 1) := by
      simp only [z]
      rw [fW_replicate, fW_replicate]
      have := eK_pow_dFV hstrz 1 hm1
      rwa [pow_one] at this
    rw [heKz] at hTE
    have hkEx0 : kE hvt i (fWi (D := D) hvt w) ∉ ϖ • latInf hvt A := by
      intro h
      have := sub_mem (hTS _ h) hTE
      rw [sub_sub_cancel] at this
      exact hcmp0 (m - 1) (by omega) y (hfWl w₀) hy0 this
    obtain ⟨m', P'', w₀'', hm'M, hP''L, he'', hP''₀, hsub, hT'⟩ := hdec hkEx0
    obtain ⟨hmm, hyy⟩ := hN₃ μ Λl (hμ' N₃ (by omega)) (m - 1) (by omega) m' hm'M y (hfWl w₀)
      _ (hfWl w₀'') hy0 (by have := sub_mem hT' hTE; rwa [sub_sub_sub_cancel_left] at this)
    subst hmm
    have hfWi := fWi_sub_mem_of_fW_sub_mem (hR := hR) hinj hϖ hϖv hk hfund _ w₀ w₀'' rfl hy0 hyy
    have hP''P : P'' - P ∈ ϖ • latInf hvt A := by
      have := add_mem (sub_mem hP''₀ hfWi) (neg_mem hw₀)
      convert this using 1; abel
    have he3 :
        (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v (P'' - P)) = 0 := by
      rw [map_sub, map_sub, he'', he, sub_self]
    have := add_mem hsub (rmulF_mem_smul_latInf (hR := hR) hinj hϖ hϖv hk hfund i (m - 1) hP''P he3)
    rw [map_sub] at this
    convert this using 1; abel

end Base

end GrandLoop

end LieLean.QuantumGroup
