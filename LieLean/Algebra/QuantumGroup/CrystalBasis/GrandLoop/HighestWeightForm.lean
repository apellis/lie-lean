/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Existence
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityStar
import LieLean.Algebra.QuantumGroup.CrystalBasis.LocalStrings

/-!
# Polarization of `(L(λ), B(λ))`

Let `( , )` be the contravariant form on `V(λ) = L_q(λ)` with `(v_λ, v_λ) = 1`
(`IrreducibleModule.form`, here `GrandLoop.formL`), and `(L(λ), B(λ))` the crystal base of
`V(λ)` constructed by the grand loop (`GrandLoop.isCrystalBase`), over a discrete valuation ring
`A ⊆ k = A[ϖ⁻¹]` with `ϖ ↦ v⁻¹`. Then:

* `(L(λ), L(λ)) ⊆ A` (`GrandLoop.formL_mem`; [HK] Lemma 5.1.5);
* `(f̃ᵢ u, w) ≡ (u, ẽᵢ w)` modulo `ϖ A` for `u, w ∈ L(λ)` (`GrandLoop.formL_fK_sub_eK_mem`;
  [HK] (5.3));
* `B(λ)` is orthonormal modulo `ϖ` (`GrandLoop.formL_fW_fW`; [HK] Lemma 5.1.6);
* `L(λ) = {u ∈ V(λ) | (u, L(λ)) ⊆ A}` (`GrandLoop.mem_lat_iff_formL_mem`; [HK] Prop. 5.1.7,
  (5.4)), and, if `A/ϖA` is formally real, `L(λ) = {u ∈ V(λ) | (u, u) ∈ A}`
  (`GrandLoop.mem_lat_iff_formL_self_mem`; [HK] Prop. 5.1.7, (5.5)).

The first two are proved together by induction on the depth: on an `i`-string decomposition
`x = Σ F^{(j)} ηⱼ`, `y = Σ F^{(j)} ζⱼ` the form is diagonal with coefficients
`(F^{(j)} η, F^{(j)} ζ) = cⱼ(n) (η, ζ)` (`IntegrableSl2.form_dF_dF`) and `cⱼ(n) ∈ 1 + ϖA`
(`IntegrableSl2.isOnePow_polCoef`); this gives the string formulas
`IsContravariant.exists_strings`. [HK] state these results for `A` the local ring of `ℚ(q)` at
`q = 0` with Kashiwara's coproduct; here the lattices are at `v = ∞`.

## Main results

* `GrandLoop.formL_mem`, `GrandLoop.formL_fK_sub_eK_mem`, `GrandLoop.formL_fW_fW`;
* `GrandLoop.mem_smul_lat_of_formL_mem`: the form on `L(λ)/ϖL(λ)` is nondegenerate;
* `GrandLoop.mem_lat_iff_formL_mem`, `GrandLoop.mem_lat_iff_formL_self_mem`.

## References

* J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, AMS 2002,
  §5.1.
-/

open Finset Pointwise

noncomputable section

namespace LieLean.QuantumGroup

/-! ### Contravariant forms on strings -/

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M}

variable (q) in
/-- `cᵣ(n) = ∏_{t < r} [t+1]⁻¹ q^{2t+1-n} [n-t]`, the value of `(F^{(r)} η, F^{(r)} ζ)/(η, ζ)` for
primitive vectors `η, ζ` of weight `n` and a form with `(F x, y) = q^{-(p+1)} (x, E y)` on
`y ∈ Mᵖ`. -/
def polCoef (n : ℤ) : ℕ → k
  | 0 => 1
  | r + 1 => polCoef n r * ((qInt q (r + 1))⁻¹ * q ^ (2 * (r : ℤ) + 1 - n) * qIntZ q (n - r))

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- `(F^{(r+1)} x, y) = [r+1]⁻¹ q^{-(p+1)} (F^{(r)} x, E y)` for `y ∈ Mᵖ`. -/
lemma form_dF_succ {B : LinearMap.BilinForm k M}
    (hF : ∀ (p : ℤ) x y, y ∈ V.wt p → B (V.F x) y = q ^ (-(p + 1)) * B x (V.E y))
    (r : ℕ) (x y : M) {p : ℤ} (hy : y ∈ V.wt p) :
    B (V.dF (r + 1) x) y = (qInt q (r + 1))⁻¹ * q ^ (-(p + 1)) * B (V.dF r x) (V.E y) := by
  have hb := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos r)
  have h : V.dF (r + 1) x = (qInt q (r + 1))⁻¹ • V.F (V.dF r x) := by
    rw [F_dF hq0 hq, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [h, map_smul, LinearMap.smul_apply, hF p _ _ hy, smul_eq_mul, mul_assoc]

/-- **Strings are orthogonal**: for a symmetric form with `(F x, y) = q^{-(p+1)} (x, E y)` on
`y ∈ Mᵖ`, and primitive vectors `η ∈ Mᵖ`, `ζ ∈ Mⁿ`,
`(F^{(r)} η, F^{(s)} ζ) = δᵣₛ cᵣ(n) (η, ζ)`. -/
theorem form_dF_dF {B : LinearMap.BilinForm k M} (hB : ∀ x y, B x y = B y x)
    (hF : ∀ (p : ℤ) x y, y ∈ V.wt p → B (V.F x) y = q ^ (-(p + 1)) * B x (V.E y))
    {p n : ℤ} {η ζ : M} (hη : η ∈ V.prim p) (hζ : ζ ∈ V.prim n) :
    ∀ r s, B (V.dF r η) (V.dF s ζ) = if r = s then polCoef q n r * B η ζ else 0 := by
  intro r
  induction r with
  | zero =>
    intro s
    rcases s with _ | s
    · simp [polCoef]
    · rw [hB, form_dF_succ hq0 hq hF s ζ _ (by simpa using hη.1), dF_zero, hη.2, map_zero,
        mul_zero]
      simp
  | succ r ih =>
    intro s
    rcases s with _ | s
    · rw [form_dF_succ hq0 hq hF r η _ (by simpa using hζ.1), dF_zero, hζ.2, map_zero, mul_zero]
      simp
    · have hs : V.dF (s + 1) ζ ∈ V.wt (n - 2 * (s + 1 : ℕ)) := V.dF_mem hζ.1 _
      rw [form_dF_succ hq0 hq hF r η _ hs, E_dF_succ_of_primitive hq0 hq hζ.1 hζ.2, map_smul,
        smul_eq_mul, ih s]
      by_cases h : r = s
      · subst h
        simp only [↓reduceIte, polCoef]
        rw [show -((n - 2 * ((r + 1 : ℕ) : ℤ)) + 1) = 2 * (r : ℤ) + 1 - n by push_cast; ring]
        ring
      · simp [h]

/-- `[m]_q = [m]_{q⁻¹}` as an element of `qᵉ`-notation for the parameter `q⁻¹`. -/
lemma qIntZ_eq_qInt_inv (m : ℕ) : qIntZ q m = qInt q⁻¹ m := by
  rw [← qIntZ_inv, qIntZ_natCast]
  rw [inv_inv, ← neg_sub]
  exact neg_ne_zero.2 (sub_inv_ne_zero_of_pow_ne_one hq0 hq)

/-- `cᵣ(n) ∈ 1 + ϖ A` for `r ≤ n`, where `ϖ ↦ q⁻¹`. -/
lemma isOnePow_polCoef {A : Type*} [CommRing A] [Algebra A k] [IsLocalRing A] {w : A}
    (hw : w ∈ IsLocalRing.maximalIdeal A) (hwq : algebraMap A k w = q⁻¹) {n : ℤ} :
    ∀ r : ℕ, (r : ℤ) ≤ n → IsOnePow w 0 (polCoef q n r) := by
  have hw0 : algebraMap A k w ≠ 0 := by rw [hwq]; exact inv_ne_zero hq0
  intro r
  induction r with
  | zero => intro _; exact isOnePow_one
  | succ r ih =>
    intro hr
    have h1 : IsOnePow w r (qInt q (r + 1))⁻¹ := by
      have h := (isOnePow_qInt hw0 (Nat.succ_pos r)).inv hw
      rw [hwq, ← qIntZ_eq_qInt_inv hq0 hq, qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 hq)]
        at h
      convert h using 1; push_cast; ring
    have h2 : IsOnePow w (n - 2 * r - 1) (q ^ (2 * (r : ℤ) + 1 - n)) := by
      have h := isOnePow_zpow (k := k) (ϖ := w) (n - 2 * r - 1)
      rw [hwq, inv_zpow', show -(n - 2 * (r : ℤ) - 1) = 2 * r + 1 - n by ring] at h
      exact h
    have h3 : IsOnePow w (1 - (n - r)) (qIntZ q (n - r)) := by
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n - r = m := ⟨(n - r).toNat, by omega⟩
      have h := isOnePow_qInt hw0 (n := m) (by omega)
      rw [hwq, ← qIntZ_eq_qInt_inv hq0 hq] at h
      rw [hm]; exact h
    have h := (ih (by omega)).mul hw0 ((h1.mul hw0 h2).mul hw0 h3)
    rw [polCoef]
    convert h using 1; ring

section Sums

variable {B : LinearMap.BilinForm k M} (hB : ∀ x y, B x y = B y x)
  (hF : ∀ (p : ℤ) x y, y ∈ V.wt p → B (V.F x) y = q ^ (-(p + 1)) * B x (V.E y))
include hB hF

/-- Pairing a string vector `F^{(r)} η` with a sum of strings `Σ_{s<K} F^{(s)} ζₛ`, `ζₛ ∈ M^{m+2s}`
primitive. -/
lemma form_dF_sum {p m : ℤ} {η : M} (hη : η ∈ V.prim p) {ζ : ℕ → M}
    (hζ : ∀ s : ℕ, ζ s ∈ V.prim (m + 2 * s)) {r K : ℕ} (hr : r < K) :
    B (V.dF r η) (∑ s ∈ range K, V.dF s (ζ s)) = polCoef q (m + 2 * r) r * B η (ζ r) := by
  rw [map_sum, sum_congr rfl fun s _ ↦ form_dF_dF hq0 hq hB hF hη (hζ s) r s]
  simp [mem_range.2 hr]

/-- `(f̃ Σ_{j<N} F^{(j)} ηⱼ, Σ_{s≤N} F^{(s)} ζₛ) = Σ_{j<N} c_{j+1}(m+2j+2) (ηⱼ, ζ_{j+1})`. -/
lemma form_fTilde_sum {n m : ℤ} {η ζ : ℕ → M} (hη : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j))
    (hζ : ∀ s : ℕ, ζ s ∈ V.prim (m + 2 * s)) (N : ℕ) :
    B (V.fTilde hq0 hq (∑ j ∈ range N, V.dF j (η j))) (∑ s ∈ range (N + 1), V.dF s (ζ s)) =
      ∑ j ∈ range N, polCoef q (m + 2 * (j + 1 : ℕ)) (j + 1) * B (η j) (ζ (j + 1)) := by
  rw [map_sum (V.fTilde hq0 hq), map_sum B, LinearMap.sum_apply]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [fTilde_dF hq0 hq (hη j).2 (hη j).1,
    form_dF_sum hq0 hq hB hF (hη j) hζ (by have := mem_range.1 hj; omega)]

/-- `(Σ_{j<N} F^{(j)} ηⱼ, ẽ Σ_{s≤N} F^{(s)} ζₛ) = Σ_{j<N} c_j(m+2j+2) (ηⱼ, ζ_{j+1})`. -/
lemma form_sum_eTilde {n m : ℤ} {η ζ : ℕ → M} (hη : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j))
    (hζ : ∀ s : ℕ, ζ s ∈ V.prim (m + 2 * s)) (hζ' : ∀ s : ℕ, ζ s ≠ 0 → 0 ≤ m + s) (N : ℕ) :
    B (∑ j ∈ range N, V.dF j (η j)) (V.eTilde hq0 hq (∑ s ∈ range (N + 1), V.dF s (ζ s))) =
      ∑ j ∈ range N, polCoef q (m + 2 * (j + 1 : ℕ)) j * B (η j) (ζ (j + 1)) := by
  rw [eTilde_sum hq0 hq hζ hζ' N, map_sum B, LinearMap.sum_apply]
  have hζ1 : ∀ s : ℕ, ζ (s + 1) ∈ V.prim (m + 2 + 2 * s) := fun s ↦ by
    convert hζ (s + 1) using 2; push_cast; ring
  refine sum_congr rfl fun j hj ↦ ?_
  rw [form_dF_sum hq0 hq hB hF (hη j) hζ1 (mem_range.1 hj)]
  congr 2; push_cast; ring

end Sums

end IntegrableSl2

/-! ### Contravariant forms on integrable modules -/

section Contravariant

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  (hM : IsIntegrable R v M) {B : LinearMap.BilinForm k M}

/-- For a contravariant form, `(Fᵢ x, y) = vᵢ^{-(p+1)} (x, Eᵢ y)` for `y` with `⟨i, wt y⟩ = p`. -/
lemma IsContravariant.nodeSl2_F (hB : IsContravariant R v B) (i : I) (p : ℤ) (x y : M)
    (hy : y ∈ (nodeSl2 R v M hv hM i).wt p) :
    B ((nodeSl2 R v M hv hM i).F x) y =
      (v ^ D.d i) ^ (-(p + 1)) * B x ((nodeSl2 R v M hv hM i).E y) := by
  have hE : E R v i • y ∈ nodeWt R v M i (p + 2) := (nodeSl2 R v M hv hM i).E_mem hy
  change B (F R v i • x) y = _ * B x (E R v i • y)
  rw [hB, rho_F, rhoF, smul_assoc, mul_smul, K_neg_ktilde_smul_of_mem_nodeWt hE, smul_smul,
    map_smul, smul_eq_mul]
  congr 1
  have h0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  rw [show -(p + 1) = 1 + -(p + 2) by ring, zpow_add₀ h0, zpow_one]

omit [DecidableEq I] in
lemma sum_range_eq_of_le {η : ℕ → M} {f : ℕ → M → M} (hf : ∀ j, f j 0 = 0) {N₁ N : ℕ}
    (hN : N₁ ≤ N) (hη : ∀ j, N₁ ≤ j → η j = 0) :
    ∑ j ∈ range N₁, f j (η j) = ∑ j ∈ range N, f j (η j) := by
  refine sum_subset (range_mono hN) fun j _ hj ↦ ?_
  rw [hη j (by simpa using hj), hf]

/-- **String expansion of `(f̃ᵢ x, y)` and `(x, ẽᵢ y)`** for a symmetric contravariant form: with
`x = Σⱼ Fᵢ^{(j)} ηⱼ ∈ M^μ` and `y = Σₛ Fᵢ^{(s)} ζₛ ∈ M^{μ-αᵢ}` the string decompositions by
weights, `(f̃ᵢ x, y) = Σⱼ c_{j+1} (ηⱼ, ζ_{j+1})` and `(x, ẽᵢ y) = Σⱼ c_j (ηⱼ, ζ_{j+1})`, where
`c_r = cᵣ(⟨i, μ⟩ + 2j)` (`IntegrableSl2.polCoef`) at `vᵢ`. -/
theorem IsContravariant.exists_strings (hB : IsContravariant R v B) (hBs : ∀ x y, B x y = B y x)
    (i : I) {μ : Y →+ ℤ} {x y : M} (hx : x ∈ weightSpace R v M μ)
    (hy : y ∈ weightSpace R v M (μ - R.root i)) :
    ∃ (N : ℕ) (η ζ : ℕ → M),
      (∀ j : ℕ, η j ∈ weightSpace R v M (μ + j • R.root i)) ∧ (∀ j, E R v i • η j = 0) ∧
      (∀ j : ℕ, η j ≠ 0 → 0 ≤ μ (R.coroot i) + j) ∧
      (∀ s : ℕ, ζ s ∈ weightSpace R v M (μ - R.root i + s • R.root i)) ∧
      (∀ s, E R v i • ζ s = 0) ∧ (∀ s : ℕ, ζ s ≠ 0 → 0 ≤ (μ - R.root i) (R.coroot i) + s) ∧
      x = ∑ j ∈ range N, (nodeSl2 R v M hv hM i).dF j (η j) ∧
      y = ∑ s ∈ range (N + 1), (nodeSl2 R v M hv hM i).dF s (ζ s) ∧
      B (kashiwaraF R v M hv hM i x) y = ∑ j ∈ range N,
        IntegrableSl2.polCoef (v ^ D.d i) (μ (R.coroot i) + 2 * j) (j + 1) * B (η j) (ζ (j + 1)) ∧
      B x (kashiwaraE R v M hv hM i y) = ∑ j ∈ range N,
        IntegrableSl2.polCoef (v ^ D.d i) (μ (R.coroot i) + 2 * j) j * B (η j) (ζ (j + 1)) := by
  obtain ⟨N₁, η, h1, hE, h2, hN₁, hxs⟩ := exists_sum_dF_weight hv hM i hx
  obtain ⟨N₂, ζ, h1', hE', h2', hN₂, hys⟩ := exists_sum_dF_weight hv hM i hy
  set V := nodeSl2 R v M hv hM i
  have hxN : x = ∑ j ∈ range (max N₁ N₂), V.dF j (η j) := by
    rw [hxs]; exact sum_range_eq_of_le (fun j ↦ map_zero _) (le_max_left _ _) hN₁
  have hyN : y = ∑ s ∈ range (max N₁ N₂ + 1), V.dF s (ζ s) := by
    rw [hys]
    exact sum_range_eq_of_le (fun j ↦ map_zero _) (by have := le_max_right N₁ N₂; omega) hN₂
  have hηp : ∀ j : ℕ, η j ∈ V.prim (μ (R.coroot i) + 2 * j) := fun j ↦
    ⟨mem_nodeWt_of_mem_add_nsmul i (h1 j), hE j⟩
  have hζp : ∀ s : ℕ, ζ s ∈ V.prim ((μ - R.root i) (R.coroot i) + 2 * s) := fun s ↦
    ⟨mem_nodeWt_of_mem_add_nsmul i (h1' s), hE' s⟩
  have hF : ∀ (p : ℤ) x y, y ∈ V.wt p →
      B (V.F x) y = (v ^ D.d i) ^ (-(p + 1)) * B x (V.E y) := fun p x y hy ↦
    IsContravariant.nodeSl2_F hv hM hB i p x y hy
  have hm : ∀ j : ℕ, (μ - R.root i) (R.coroot i) + 2 * ((j + 1 : ℕ) : ℤ) =
      μ (R.coroot i) + 2 * j := fun j ↦ by
    rw [AddMonoidHom.sub_apply, R.root_coroot, D.cartanMatrix_self]; push_cast; ring
  refine ⟨max N₁ N₂, η, ζ, h1, hE, h2, h1', hE', h2', hxN, hyN, ?_, ?_⟩
  · change B (V.fTilde (pow_d_ne_zero i) (pow_d_ne_one hv i) x) y = _
    rw [hxN, hyN, IntegrableSl2.form_fTilde_sum (pow_d_ne_zero i) (pow_d_ne_one hv i) hBs hF hηp
      hζp]
    simp only [hm]
  · change B x (V.eTilde (pow_d_ne_zero i) (pow_d_ne_one hv i) y) = _
    rw [hxN, hyN, IntegrableSl2.form_sum_eTilde (pow_d_ne_zero i) (pow_d_ne_one hv i) hBs hF hηp
      hζp h2']
    simp only [hm]

end Contravariant

/-! ### Polarization of `(L(λ), B(λ))` -/

namespace GrandLoop

section Polarization

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

variable (hvt hR) in
/-- The contravariant form `( , )` on `V(λ)`, normalized by `(v_λ, v_λ) = 1`
(`IrreducibleModule.form`). -/
abbrev formL (Λ : Dom R) : LinearMap.BilinForm k (IrreducibleModule R v Λ.1) :=
  IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt)

omit [CharZero k] [DecidableEq I] in
/-- `cᵣ(n) ∈ 1 + ϖ A` at `vᵢ` for `r ≤ n`. -/
lemma exists_polCoef [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) {n : ℤ} {r : ℕ}
    (hr : (r : ℤ) ≤ n) :
    ∃ a : A, IntegrableSl2.polCoef (v ^ D.d i) n r = algebraMap A k (1 + ϖ * a) := by
  have hd := D.d_pos i
  set w := ϖ ^ D.d i with hw_def
  have hw : w ∈ IsLocalRing.maximalIdeal A := Ideal.pow_mem_of_mem _ hϖ _ hd
  have hwv : algebraMap A k w = (v ^ D.d i)⁻¹ := by rw [map_pow, hϖv, inv_pow]
  obtain ⟨a, ha⟩ := IntegrableSl2.isOnePow_polCoef (pow_d_ne_zero i) (pow_d_ne_one hv' i) hw hwv
    r hr
  obtain ⟨d', hd'⟩ : ∃ d', D.d i = d' + 1 := ⟨D.d i - 1, by omega⟩
  refine ⟨ϖ ^ d' * a, ?_⟩
  rw [ha, zpow_zero, one_mul, hw_def, hd', pow_succ]
  ring_nf

/-- An element of `L(λ)` of depth `ν` is an `A`-combination of the `f̃_w v_λ` with
`wt(w) = ν`. -/
lemma mem_span_fW_of_mem {Λ : Dom R} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1}
    (hx : x ∈ lat hvt hR A Λ) (hxw : x ∈ wsp Λ ν) :
    x ∈ Submodule.span A (fW hvt hR Λ '' {w | LusztigF.wordWeight w = ν}) := by
  classical
  have hP : ∀ z ∈ lat hvt hR A Λ, weightSetProj (pow_ne_one_of_transcendental' hvt)
      (isInt hvt hR Λ) {Λ.1 - R.rootSum ν} z ∈
        Submodule.span A (fW hvt hR Λ '' {w | LusztigF.wordWeight w = ν}) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      rw [weightSetProj_fW (hvt := hvt)]
      split_ifs with h
      · exact Submodule.subset_span ⟨w, h, rfl⟩
      · exact zero_mem _
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c ha
  have := hP x hx
  rw [weightSetProj_of_mem _ _ _ hxw] at this
  simpa using this

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- The string expansions of `(f̃ᵢ x, y)` and `(x, ẽᵢ y)` for `x, y ∈ L(λ)`, with string vectors in
`L(λ)`. -/
lemma exists_strings_lat (Λ : Dom R) (i : I) {μ : Y →+ ℤ} {x y : IrreducibleModule R v Λ.1}
    (hxL : x ∈ lat hvt hR A Λ) (hx : x ∈ weightSpace R v _ μ) (hyL : y ∈ lat hvt hR A Λ)
    (hy : y ∈ weightSpace R v _ (μ - R.root i)) :
    ∃ (N : ℕ) (η ζ : ℕ → IrreducibleModule R v Λ.1),
      (∀ j < N, η j ∈ lat hvt hR A Λ) ∧ (∀ j < N, ζ (j + 1) ∈ lat hvt hR A Λ) ∧
      (∀ j : ℕ, η j ∈ weightSpace R v _ (μ + j • R.root i)) ∧
      (∀ j : ℕ, ζ (j + 1) ∈ weightSpace R v _ (μ + j • R.root i)) ∧
      (∀ j : ℕ, ζ (j + 1) ≠ 0 → ((j + 1 : ℕ) : ℤ) ≤ μ (R.coroot i) + 2 * j) ∧
      formL hvt hR Λ (fK hvt hR Λ i x) y = ∑ j ∈ range N,
        IntegrableSl2.polCoef (v ^ D.d i) (μ (R.coroot i) + 2 * j) (j + 1) *
          formL hvt hR Λ (η j) (ζ (j + 1)) ∧
      formL hvt hR Λ x (eK hvt hR Λ i y) = ∑ j ∈ range N,
        IntegrableSl2.polCoef (v ^ D.d i) (μ (R.coroot i) + 2 * j) j *
          formL hvt hR Λ (η j) (ζ (j + 1)) := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨N, η, ζ, h1, hE, h2, h1', hE', h2', hxs, hys, hf, he⟩ :=
    (IrreducibleModule.isContravariant_form hR hv').exists_strings hv' (isInt hvt hR Λ)
      (IrreducibleModule.form_comm hR hv') i hx hy
  have hfL : ∀ y ∈ lat hvt hR A Λ, fK hvt hR Λ i y ∈ lat hvt hR A Λ := fun _ hy ↦
    kashiwaraF_mem_lat Λ i hy
  have heL : ∀ (j : ℕ), ∀ y ∈ lat hvt hR A Λ, y ∈ weightSpace R v _ (μ + j • R.root i) →
      eK hvt hR Λ i y ∈ lat hvt hR A Λ := fun _ _ hy _ ↦
    kashiwaraE_mem_lat (fun r ↦ (hall r).1) Λ i hy
  have heL' : ∀ (j : ℕ), ∀ y ∈ lat hvt hR A Λ,
      y ∈ weightSpace R v _ (μ - R.root i + j • R.root i) → eK hvt hR Λ i y ∈ lat hvt hR A Λ :=
    fun _ _ hy _ ↦ kashiwaraE_mem_lat (fun r ↦ (hall r).1) Λ i hy
  have hηL := mem_of_sum_mem_weight hv' (isInt hvt hR Λ) i hfL N μ η h1 hE h2 heL (hxs ▸ hxL)
  have hζL := mem_of_sum_mem_weight hv' (isInt hvt hR Λ) i hfL (N + 1) (μ - R.root i) ζ h1' hE'
    h2' heL' (hys ▸ hyL)
  have hc : (μ - R.root i) (R.coroot i) = μ (R.coroot i) - 2 := by
    rw [AddMonoidHom.sub_apply, R.root_coroot, D.cartanMatrix_self]
  refine ⟨N, η, ζ, hηL, fun j hj ↦ hζL (j + 1) (by omega), h1, fun j ↦ ?_, fun j hj ↦ ?_, hf, he⟩
  · have e : μ - R.root i + (j + 1) • R.root i = μ + j • R.root i := by rw [succ_nsmul]; abel
    exact e ▸ h1' (j + 1)
  · have := h2' (j + 1) hj
    rw [hc] at this
    push_cast at this ⊢
    omega

/-- **[HK] Lemma 5.1.5**, on a weight space: `(x, y) ∈ A` for `x, y ∈ L(λ)` of depth `ν`. -/
theorem formL_mem_of_mem_wsp (Λ : Dom R) : ∀ n (ν : I →₀ ℕ), ν.degree = n →
    ∀ x y : IrreducibleModule R v Λ.1, x ∈ lat hvt hR A Λ → x ∈ wsp Λ ν →
      y ∈ lat hvt hR A Λ → y ∈ wsp Λ ν → ∃ a : A, formL hvt hR Λ x y = algebraMap A k a := by
  have hv' := pow_ne_one_of_transcendental' hvt
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hν x y hxL hxw hyL hyw
  have hspan := mem_span_fW_of_mem hxL hxw
  clear hxL hxw
  induction hspan using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by rw [map_add, LinearMap.add_apply, hp, hq, map_add]⟩
  | smul c a _ ha =>
    obtain ⟨p, hp⟩ := ha
    exact ⟨c * p, by
      rw [← algebraMap_smul k c a, map_smul, LinearMap.smul_apply, hp, smul_eq_mul, map_mul]⟩
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rcases w with _ | ⟨i, w₁⟩
    · exact exists_form_hwv (hvt := hvt) hyL
    · have hνe : ν = LusztigF.wordWeight w₁ + Finsupp.single i 1 := by
        rw [← (show LusztigF.wordWeight _ = ν from hw), LusztigF.wordWeight_cons, add_comm]
      have e2 : R.rootSum ν = R.rootSum (LusztigF.wordWeight w₁) + R.root i := by
        rw [hνe, R.rootSum_add, R.rootSum_single, one_nsmul]
      set μ := Λ.1 - R.rootSum (LusztigF.wordWeight w₁) with hμ
      have hy' : y ∈ weightSpace R v _ (μ - R.root i) := by
        have : μ - R.root i = Λ.1 - R.rootSum ν := by rw [hμ, e2]; abel
        rw [this]; exact hyw
      obtain ⟨N, η, ζ, hηL, hζL, hηw, hζw, hζn, hf, -⟩ := exists_strings_lat hinj hϖ hϖv hk hfund
        Λ i (IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A w₁) (fW_mem_wsp hvt hR Λ w₁) hyL hy'
      rw [fW_cons, hf]
      have hterm : ∀ j ∈ range N, ∃ a : A,
          IntegrableSl2.polCoef (v ^ D.d i) (μ (R.coroot i) + 2 * j) (j + 1) *
            formL hvt hR Λ (η j) (ζ (j + 1)) = algebraMap A k a := by
        intro j hj
        by_cases hz : ζ (j + 1) = 0
        · exact ⟨0, by simp [hz]⟩
        obtain ⟨c, hc⟩ := exists_polCoef hϖ hϖv hv' i (hζn j hz)
        have hzw : ζ (j + 1) ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + (j + 1) • R.root i) := by
          have : Λ.1 - R.rootSum ν + (j + 1) • R.root i = μ + j • R.root i := by
            rw [hμ, e2, succ_nsmul]; abel
          rw [this]; exact hζw j
        obtain ⟨ν'', hν''⟩ := exists_eq_add_single hR hv' Λ hzw hz
        have hdeg : ν''.degree < n := by
          rw [← hν, hν'', map_add, Finsupp.degree_single]; omega
        have hw'' : Λ.1 - R.rootSum ν'' = μ + j • R.root i := by
          have e1 : R.rootSum ν = R.rootSum ν'' + (j + 1) • R.root i := by
            rw [hν'', R.rootSum_add, R.rootSum_single]
          calc Λ.1 - R.rootSum ν'' = Λ.1 - (R.rootSum ν'' + (j + 1) • R.root i) +
                (j + 1) • R.root i := by abel
            _ = μ + j • R.root i := by rw [← e1, e2, hμ, succ_nsmul]; abel
        obtain ⟨a, ha⟩ := ih _ hdeg ν'' rfl (η j) (ζ (j + 1)) (hηL j (mem_range.1 hj))
          (show η j ∈ weightSpace R v _ (Λ.1 - R.rootSum ν'') by rw [hw'']; exact hηw j)
          (hζL j (mem_range.1 hj))
          (show ζ (j + 1) ∈ weightSpace R v _ (Λ.1 - R.rootSum ν'') by rw [hw'']; exact hζw j)
        exact ⟨(1 + ϖ * c) * a, by rw [hc, ha, map_mul]⟩
      choose! a ha using hterm
      exact ⟨∑ j ∈ range N, a j, by rw [map_sum]; exact sum_congr rfl ha⟩

/-- **[HK] Lemma 5.1.5**: `(L(λ), L(λ)) ⊆ A`. -/
theorem formL_mem (Λ : Dom R) {x y : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ)
    (hy : y ∈ lat hvt hR A Λ) : ∃ a : A, formL hvt hR Λ x y = algebraMap A k a := by
  have hv' := pow_ne_one_of_transcendental' hvt
  induction hx using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by rw [map_add, LinearMap.add_apply, hp, hq, map_add]⟩
  | smul c a _ ha =>
    obtain ⟨p, hp⟩ := ha
    exact ⟨c * p, by
      rw [← algebraMap_smul k c a, map_smul, LinearMap.smul_apply, hp, smul_eq_mul, map_mul]⟩
  | mem x hx =>
    obtain ⟨w₁, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p + q, by rw [map_add, hp, hq, map_add]⟩
    | smul c a _ ha =>
      obtain ⟨p, hp⟩ := ha
      exact ⟨c * p, by rw [← algebraMap_smul k c a, map_smul, hp, smul_eq_mul, map_mul]⟩
    | mem y hy =>
      obtain ⟨w₂, rfl⟩ := hy
      by_cases h : LusztigF.wordWeight w₁ = LusztigF.wordWeight w₂
      · exact formL_mem_of_mem_wsp hinj hϖ hϖv hk hfund Λ _ _ rfl _ _
          (IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A w₁) (fW_mem_wsp hvt hR Λ w₁)
          (IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A w₂) (h ▸ fW_mem_wsp hvt hR Λ w₂)
      · refine ⟨0, ?_⟩
        rw [map_zero]
        refine (IrreducibleModule.isContravariant_form hR hv').eq_zero_of_ne (fun e ↦ h ?_)
          (fW_mem_wsp hvt hR Λ w₁) (fW_mem_wsp hvt hR Λ w₂) hv'
        exact LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective e)

lemma formL_mem_smul (Λ : Dom R) {x y : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ)
    (hy : y ∈ ϖ • lat hvt hR A Λ) : ∃ a : A, formL hvt hR Λ x y = algebraMap A k (ϖ * a) := by
  obtain ⟨y₀, hy₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  obtain ⟨a, ha⟩ := formL_mem hinj hϖ hϖv hk hfund Λ hx hy₀
  refine ⟨a, ?_⟩
  rw [← algebraMap_smul k ϖ y₀, map_smul, ha, smul_eq_mul, map_mul]

lemma formL_smul_mem (Λ : Dom R) {x y : IrreducibleModule R v Λ.1}
    (hx : x ∈ ϖ • lat hvt hR A Λ) (hy : y ∈ lat hvt hR A Λ) :
    ∃ a : A, formL hvt hR Λ x y = algebraMap A k (ϖ * a) := by
  rw [IrreducibleModule.form_comm]
  exact formL_mem_smul hinj hϖ hϖv hk hfund Λ hy hx

/-- **[HK] (5.3)**: `(f̃ᵢ u, w) ≡ (u, ẽᵢ w)` modulo `ϖ A` for `u, w ∈ L(λ)`. -/
theorem formL_fK_sub_eK_mem (Λ : Dom R) (i : I) {x y : IrreducibleModule R v Λ.1}
    (hx : x ∈ lat hvt hR A Λ) (hy : y ∈ lat hvt hR A Λ) :
    ∃ a : A, formL hvt hR Λ (fK hvt hR Λ i x) y - formL hvt hR Λ x (eK hvt hR Λ i y) =
      algebraMap A k (ϖ * a) := by
  have hv' := pow_ne_one_of_transcendental' hvt
  induction hx using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by
      simp only [map_add, LinearMap.add_apply, mul_add]
      rw [← hp, ← hq]
      ring⟩
  | smul c a _ ha =>
    obtain ⟨p, hp⟩ := ha
    exact ⟨c * p, by
      rw [← algebraMap_smul k c a]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_sub, hp, ← map_mul]
      ring_nf⟩
  | mem x hx =>
    obtain ⟨w₁, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p + q, by simp only [map_add, mul_add]; rw [← hp, ← hq]; ring⟩
    | smul c a _ ha =>
      obtain ⟨p, hp⟩ := ha
      exact ⟨c * p, by
        rw [← algebraMap_smul k c a]
        simp only [map_smul, smul_eq_mul]
        rw [← mul_sub, hp, ← map_mul]
        ring_nf⟩
    | mem y hy =>
      obtain ⟨w₂, rfl⟩ := hy
      set μ := Λ.1 - R.rootSum (LusztigF.wordWeight w₁)
      have hx' : fW hvt hR Λ w₁ ∈ weightSpace R v _ μ := fW_mem_wsp hvt hR Λ w₁
      have hy₀ := fW_mem_wsp hvt hR Λ w₂
      by_cases h : Λ.1 - R.rootSum (LusztigF.wordWeight w₂) = μ - R.root i
      · obtain ⟨N, η, ζ, hηL, hζL, -, -, hζn, hf, he⟩ := exists_strings_lat hinj hϖ hϖv hk hfund
          Λ i (IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A w₁) hx'
          (IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A w₂) (h ▸ hy₀)
        rw [hf, he, ← sum_sub_distrib]
        have hterm : ∀ j ∈ range N, ∃ a : A,
            IntegrableSl2.polCoef (v ^ D.d i) (μ (R.coroot i) + 2 * j) (j + 1) *
              formL hvt hR Λ (η j) (ζ (j + 1)) -
            IntegrableSl2.polCoef (v ^ D.d i) (μ (R.coroot i) + 2 * j) j *
              formL hvt hR Λ (η j) (ζ (j + 1)) = algebraMap A k (ϖ * a) := by
          intro j hj
          by_cases hz : ζ (j + 1) = 0
          · exact ⟨0, by simp [hz]⟩
          have h1 := hζn j hz
          obtain ⟨c₁, hc₁⟩ := exists_polCoef hϖ hϖv hv' i h1
          obtain ⟨c₀, hc₀⟩ := exists_polCoef hϖ hϖv hv' i (n := μ (R.coroot i) + 2 * j) (r := j)
            (by push_cast at h1; omega)
          obtain ⟨b, hb⟩ := formL_mem hinj hϖ hϖv hk hfund Λ (hηL j (mem_range.1 hj))
            (hζL j (mem_range.1 hj))
          exact ⟨(c₁ - c₀) * b, by
            rw [hc₁, hc₀, hb, ← map_mul, ← map_mul, ← map_sub]; ring_nf⟩
        choose! a ha using hterm
        exact ⟨∑ j ∈ range N, a j, by rw [mul_sum, map_sum]; exact sum_congr rfl ha⟩
      · refine ⟨0, ?_⟩
        have hf0 : formL hvt hR Λ (fK hvt hR Λ i (fW hvt hR Λ w₁)) (fW hvt hR Λ w₂) = 0 :=
          (IrreducibleModule.isContravariant_form hR hv').eq_zero_of_ne (Ne.symm h)
            (kashiwaraF_mem_weightSpace hv' (isInt hvt hR Λ) i hx') hy₀ hv'
        have he0 : formL hvt hR Λ (fW hvt hR Λ w₁) (eK hvt hR Λ i (fW hvt hR Λ w₂)) = 0 :=
          (IrreducibleModule.isContravariant_form hR hv').eq_zero_of_ne
            (fun e ↦ h (by rw [e]; abel)) hx'
            (kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i hy₀) hv'
        rw [hf0, he0]; simp

open scoped Classical in
/-- **[HK] Lemma 5.1.6**: `B(λ)` is orthonormal modulo `ϖ`: for `f̃_w v_λ, f̃_{w'} v_λ ∉ ϖ L(λ)`,
`(f̃_w v_λ, f̃_{w'} v_λ) ≡ 1` if their classes in `L(λ)/ϖL(λ)` agree and `≡ 0` otherwise. -/
theorem formL_fW_fW (Λ : Dom R) (w w' : List I) (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (hw' : fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ) :
    ∃ a : A, formL hvt hR Λ (fW hvt hR Λ w) (fW hvt hR Λ w') =
      (if fW hvt hR Λ w - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ then 1 else 0) +
        algebraMap A k (ϖ * a) := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hv' := pow_ne_one_of_transcendental' hvt
  have hL : ∀ w, fW hvt hR Λ w ∈ lat hvt hR A Λ := IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A
  induction w generalizing w' with
  | nil =>
    by_cases hw'n : w' = []
    · subst hw'n
      exact ⟨0, by simp⟩
    · have hnot : fW hvt hR Λ [] - fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ := fun h ↦ by
        have h0 := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ (hwv_mem_wsp Λ) hw h
        exact hw'n (List.eq_nil_of_length_eq_zero (by rw [← degree_wordWeight, h0, map_zero]))
      refine ⟨0, ?_⟩
      simp only [hnot, ↓reduceIte, mul_zero, map_zero, add_zero]
      exact form_hwv_fW (hvt := hvt) Λ hw'n
  | cons i w₀ ih =>
    have hw₀ : fW hvt hR Λ w₀ ∉ ϖ • lat hvt hR A Λ := fun h ↦
      hw (by rw [fW_cons]; exact kashiwaraF_mem_smul_lat Λ i h)
    have hC : ∀ r, PropC hvt hR A ϖ r := fun r ↦ (hall r).2.2.1
    obtain ⟨a₁, ha₁⟩ := formL_fK_sub_eK_mem hinj hϖ hϖv hk hfund Λ i (hL w₀) (hL w')
    rw [← fW_cons] at ha₁
    have hcase : eK hvt hR Λ i (fW hvt hR Λ w') ∈ ϖ • lat hvt hR A Λ ∨
        ∃ w₁, fW hvt hR Λ w₁ ∉ ϖ • lat hvt hR A Λ ∧
          eK hvt hR Λ i (fW hvt hR Λ w') - fW hvt hR Λ w₁ ∈ ϖ • lat hvt hR A Λ := by
      rcases (hall w'.length).2.1 Λ w' rfl i with h | ⟨w₁, h⟩
      · exact Or.inl h
      · by_cases h₁ : fW hvt hR Λ w₁ ∈ ϖ • lat hvt hR A Λ
        · exact Or.inl (by simpa using add_mem h h₁)
        · exact Or.inr ⟨w₁, h₁, h⟩
    rcases hcase with h | ⟨w₁, hw₁, h⟩
    · obtain ⟨a₂, ha₂⟩ := formL_mem_smul hinj hϖ hϖv hk hfund Λ (hL w₀) h
      have hnot : fW hvt hR Λ (i :: w₀) - fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ := fun h' ↦ by
        have := (fK_sub_mem_iff hC Λ i hw₀ hw').1 h'
        exact hw₀ (by simpa using sub_mem h this)
      refine ⟨a₁ + a₂, ?_⟩
      simp only [hnot, ↓reduceIte, zero_add]
      rw [mul_add, map_add, ← ha₁, ← ha₂]
      ring
    · obtain ⟨a₂, ha₂⟩ := formL_mem_smul hinj hϖ hϖv hk hfund Λ (hL w₀) h
      obtain ⟨a₃, ha₃⟩ := ih w₁ hw₀ hw₁
      have hiff : fW hvt hR Λ w₀ - fW hvt hR Λ w₁ ∈ ϖ • lat hvt hR A Λ ↔
          fW hvt hR Λ (i :: w₀) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ := by
        constructor
        · intro h'
          refine (fK_sub_mem_iff hC Λ i hw₀ hw').2 ?_
          have := sub_mem h h'
          convert this using 1; abel
        · intro h'
          have := sub_mem ((fK_sub_mem_iff hC Λ i hw₀ hw').1 h') h
          convert neg_mem this using 1; abel
      refine ⟨a₁ + a₂ + a₃, ?_⟩
      rw [← hiff]
      have e : formL hvt hR Λ (fW hvt hR Λ w₀) (eK hvt hR Λ i (fW hvt hR Λ w')) =
          formL hvt hR Λ (fW hvt hR Λ w₀) (eK hvt hR Λ i (fW hvt hR Λ w') - fW hvt hR Λ w₁) +
            formL hvt hR Λ (fW hvt hR Λ w₀) (fW hvt hR Λ w₁) := by
        rw [map_sub]; ring
      rw [eq_add_of_sub_eq ha₁, e, ha₂, ha₃]
      simp only [map_add, map_mul]
      ring

/-- The form induced on `L(λ)/ϖL(λ)` is nondegenerate: if `z ∈ L(λ)` and `(z, b) ∈ ϖA` for every
`b ∈ B(λ)`, then `z ∈ ϖ L(λ)`. -/
theorem mem_smul_lat_of_formL_mem (Λ : Dom R) {z : IrreducibleModule R v Λ.1}
    (hz : z ∈ lat hvt hR A Λ)
    (h : ∀ w, fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ →
      ∃ a : A, formL hvt hR Λ z (fW hvt hR Λ w) = algebraMap A k (ϖ * a)) :
    z ∈ ϖ • lat hvt hR A Λ := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  have hL : ∀ w, fW hvt hR Λ w ∈ lat hvt hR A Λ := IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A
  set P := ϖ • lat hvt hR A Λ
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hz
  set W := c.support.filter fun w ↦ fW hvt hR Λ w ∉ P
  obtain ⟨S, hSW, hSd, hcov⟩ := exists_reps_mod P (fW hvt hR Λ) W
  choose! r hrS hr using hcov
  obtain ⟨a, ha⟩ : ∃ a : List I → A, ∀ s, a s = ∑ w ∈ W with r w = s, c w := ⟨_, fun _ ↦ rfl⟩
  set y := ∑ s ∈ S, a s • fW hvt hR Λ s with hy
  have hy' : y = ∑ w ∈ W, c w • fW hvt hR Λ (r w) := by
    rw [hy, ← Finset.sum_fiberwise_of_maps_to (g := r) (t := S) hrS]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ha, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [(Finset.mem_filter.1 hw).2]
  have hzy : z - y ∈ P := by
    rw [hy', ← hc, Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not c.support
      (fun w ↦ fW hvt hR Λ w ∉ P), add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine add_mem (Submodule.sum_mem _ fun w hw ↦ ?_) (Submodule.sum_mem _ fun w hw ↦ ?_)
    · rw [← smul_sub]; exact Submodule.smul_mem _ _ (hr w hw)
    · have := (Finset.mem_filter.1 hw).2
      push Not at this
      exact Submodule.smul_mem _ _ this
  choose! e he using fun s' (hs' : s' ∈ S) s (hs : s ∈ S) ↦
    formL_fW_fW hinj hϖ hϖv hk hfund Λ s' s (Finset.mem_filter.1 (hSW hs')).2
      (Finset.mem_filter.1 (hSW hs)).2
  have hyP : ∀ s ∈ S, a s ∈ Ideal.span {ϖ} := by
    intro s hs
    obtain ⟨t₀, ht₀⟩ := h s (Finset.mem_filter.1 (hSW hs)).2
    obtain ⟨t₁, ht₁⟩ := formL_smul_mem hinj hϖ hϖv hk hfund Λ hzy (hL s)
    have key : ∀ s' ∈ S, formL hvt hR Λ (a s' • fW hvt hR Λ s') (fW hvt hR Λ s) =
        (if s' = s then algebraMap A k (a s) else 0) +
          algebraMap A k (ϖ * (a s' * e s' s)) := by
      intro s' hs'
      rw [← algebraMap_smul k, map_smul, LinearMap.smul_apply, he s' hs' s hs, smul_eq_mul]
      by_cases hss : s' = s
      · subst hss; simp only [sub_self, zero_mem, ↓reduceIte, map_mul]; ring
      · have hn : fW hvt hR Λ s' - fW hvt hR Λ s ∉ ϖ • lat hvt hR A Λ := hSd s' hs' s hs hss
        simp only [hn, hss, ↓reduceIte, map_mul]; ring
    have hyy : formL hvt hR Λ y (fW hvt hR Λ s) = algebraMap A k (a s) +
        algebraMap A k (ϖ * ∑ s' ∈ S, a s' * e s' s) := by
      rw [hy, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl key, Finset.sum_add_distrib,
        Finset.sum_ite_eq' S s]
      simp only [hs, ↓reduceIte, mul_sum, map_sum]
    rw [Ideal.mem_span_singleton']
    refine ⟨t₀ - t₁ - ∑ s' ∈ S, a s' * e s' s, hinj ?_⟩
    have e1 : formL hvt hR Λ z (fW hvt hR Λ s) =
        formL hvt hR Λ (z - y) (fW hvt hR Λ s) + formL hvt hR Λ y (fW hvt hR Λ s) := by
      rw [map_sub, LinearMap.sub_apply]; ring
    rw [ht₀, ht₁, hyy] at e1
    simp only [map_mul, map_sub] at e1 ⊢
    linear_combination e1
  have hyS : y ∈ P := by
    rw [hy]
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hyP s hs)
    rw [← hb, mul_comm, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ (hL s))
  simpa using add_mem hzy hyS

/-- **[HK] Proposition 5.1.7, (5.4)**: `L(λ) = {u ∈ V(λ) | (u, L(λ)) ⊆ A}`. -/
theorem mem_lat_iff_formL_mem (Λ : Dom R) (u : IrreducibleModule R v Λ.1) :
    u ∈ lat hvt hR A Λ ↔
      ∀ y ∈ lat hvt hR A Λ, ∃ a : A, formL hvt hR Λ u y = algebraMap A k a := by
  classical
  refine ⟨fun hu y hy ↦ formL_mem hinj hϖ hϖv hk hfund Λ hu hy, fun hu ↦ ?_⟩
  by_contra hnot
  have hv' := pow_ne_one_of_transcendental' hvt
  have hL : ∀ w, fW hvt hR Λ w ∈ lat hvt hR A Λ := IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A
  have hex : ∃ n : ℕ, ϖ ^ n • u ∈ lat hvt hR A Λ := DualLattice.exists_pow_smul_mem hk
    (by rw [IrreducibleModule.span_lattice]; trivial)
  set n := Nat.find hex with hn
  have hxL : ϖ ^ n • u ∈ lat hvt hR A Λ := Nat.find_spec hex
  have hn0 : n ≠ 0 := fun h ↦ hnot (by simpa [h] using hxL)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmL : ϖ ^ m • u ∉ lat hvt hR A Λ := Nat.find_min hex (by omega)
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  refine hmL ?_
  obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (mem_smul_lat_of_formL_mem hinj hϖ hϖv hk hfund Λ hxL fun w _ ↦ by
      obtain ⟨a, ha⟩ := hu _ (hL w)
      refine ⟨ϖ ^ m * a, ?_⟩
      rw [← algebraMap_smul k, map_smul, LinearMap.smul_apply, ha, smul_eq_mul, ← map_mul, hm,
        pow_succ', mul_assoc])
  have : y = ϖ ^ m • u := by
    have e : (algebraMap A k ϖ) • y = (algebraMap A k ϖ) • (ϖ ^ m • u) := by
      rw [algebraMap_smul, algebraMap_smul, hyx, hm, pow_succ', mul_smul]
    exact smul_right_injective _ hϖ0 e
  exact this ▸ hy

/-- If `A/ϖA` is formally real, `x ∈ L(λ)` and `(x, x) ∈ ϖA`, then `x ∈ ϖ L(λ)`: the form induced
on `L(λ)/ϖL(λ)` is positive definite, `B(λ)` being orthonormal (Lemma 5.1.6). -/
theorem mem_smul_lat_of_formL_self_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (Λ : Dom R)
    {z : IrreducibleModule R v Λ.1} (hz : z ∈ lat hvt hR A Λ) {b₀ : A}
    (hzz : formL hvt hR Λ z z = algebraMap A k (ϖ * b₀)) :
    z ∈ ϖ • lat hvt hR A Λ := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  have hL : ∀ w, fW hvt hR Λ w ∈ lat hvt hR A Λ := IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A
  set P := ϖ • lat hvt hR A Λ
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hz
  set W := c.support.filter fun w ↦ fW hvt hR Λ w ∉ P
  obtain ⟨S, hSW, hSd, hcov⟩ := exists_reps_mod P (fW hvt hR Λ) W
  choose! r hrS hr using hcov
  obtain ⟨a, ha⟩ : ∃ a : List I → A, ∀ s, a s = ∑ w ∈ W with r w = s, c w := ⟨_, fun _ ↦ rfl⟩
  set y := ∑ s ∈ S, a s • fW hvt hR Λ s with hy
  have hy' : y = ∑ w ∈ W, c w • fW hvt hR Λ (r w) := by
    rw [hy, ← Finset.sum_fiberwise_of_maps_to (g := r) (t := S) hrS]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ha, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [(Finset.mem_filter.1 hw).2]
  have hzy : z - y ∈ P := by
    rw [hy', ← hc, Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not c.support
      (fun w ↦ fW hvt hR Λ w ∉ P), add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine add_mem (Submodule.sum_mem _ fun w hw ↦ ?_) (Submodule.sum_mem _ fun w hw ↦ ?_)
    · rw [← smul_sub]; exact Submodule.smul_mem _ _ (hr w hw)
    · have := (Finset.mem_filter.1 hw).2
      push Not at this
      exact Submodule.smul_mem _ _ this
  have hyL : y ∈ lat hvt hR A Λ := Submodule.sum_mem _ fun s _ ↦ Submodule.smul_mem _ _ (hL s)
  -- `(z, z) ≡ (y, y)`
  obtain ⟨t₁, ht₁⟩ := formL_mem_smul hinj hϖ hϖv hk hfund Λ hz hzy
  obtain ⟨t₂, ht₂⟩ := formL_smul_mem hinj hϖ hϖv hk hfund Λ hzy hyL
  have hzy' : formL hvt hR Λ z z - formL hvt hR Λ y y = algebraMap A k (ϖ * (t₁ + t₂)) := by
    have : formL hvt hR Λ z z - formL hvt hR Λ y y =
        formL hvt hR Λ z (z - y) + formL hvt hR Λ (z - y) y := by
      rw [map_sub, map_sub, LinearMap.sub_apply]; ring
    rw [this, ht₁, ht₂, ← map_add, mul_add]
  -- `(y, y) ≡ ∑ a_s²`
  choose! e he using fun s' (hs' : s' ∈ S) s (hs : s ∈ S) ↦
    formL_fW_fW hinj hϖ hϖv hk hfund Λ s' s (Finset.mem_filter.1 (hSW hs')).2
      (Finset.mem_filter.1 (hSW hs)).2
  have key : ∀ s ∈ S, ∀ s' ∈ S, formL hvt hR Λ (a s • fW hvt hR Λ s) (a s' • fW hvt hR Λ s') =
      (if s = s' then algebraMap A k (a s ^ 2) else 0) +
        algebraMap A k (ϖ * (a s * a s' * e s s')) := by
    intro s hs s' hs'
    rw [← algebraMap_smul k (a s), ← algebraMap_smul k (a s'), map_smul, map_smul,
      LinearMap.smul_apply, he s hs s' hs', smul_eq_mul, smul_eq_mul]
    by_cases hss : s = s'
    · subst hss; simp only [sub_self, zero_mem, ↓reduceIte, map_mul, map_pow]; ring
    · have hn : fW hvt hR Λ s - fW hvt hR Λ s' ∉ ϖ • lat hvt hR A Λ := hSd s hs s' hs' hss
      simp only [hn, hss, ↓reduceIte, map_mul]; ring
  have hyy : formL hvt hR Λ y y = algebraMap A k (∑ s ∈ S, a s ^ 2) +
      algebraMap A k (ϖ * ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s') := by
    rw [hy]
    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun s hs ↦ Finset.sum_congr rfl fun s' hs' ↦ key s hs s' hs']
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, map_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s hs ↦ by simp [hs]
  -- conclusion
  have hsum : ∑ s ∈ S, a s ^ 2 ∈ Ideal.span {ϖ} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨b₀ - (t₁ + t₂) - ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s', ?_⟩
    apply hinj
    have h1 := hzy'
    rw [hzz, hyy] at h1
    simp only [map_mul, map_sub, map_add] at h1 ⊢
    linear_combination h1
  have hall : ∀ s ∈ S, a s ∈ Ideal.span {ϖ} := by
    intro s hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine eq_zero_of_sum_sq_eq_zero S (fun s ↦ Ideal.Quotient.mk _ (a s)) ?_ s hs
    simp only [← map_pow, ← map_sum]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hsum
  have hyS : y ∈ P := by
    rw [hy]
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hall s hs)
    rw [← hb, mul_comm, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ (hL s))
  simpa using add_mem hzy hyS

/-- **[HK] Proposition 5.1.7, (5.5)**: if `A/ϖA` is formally real (for `A` the local ring of
`ℚ(v)` at `v = ∞` it is `ℚ`), then `L(λ) = {u ∈ V(λ) | (u, u) ∈ A}`. -/
theorem mem_lat_iff_formL_self_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (Λ : Dom R)
    (u : IrreducibleModule R v Λ.1) :
    u ∈ lat hvt hR A Λ ↔ ∃ a : A, formL hvt hR Λ u u = algebraMap A k a := by
  classical
  refine ⟨fun hu ↦ formL_mem hinj hϖ hϖv hk hfund Λ hu hu, fun ⟨a₀, ha₀⟩ ↦ ?_⟩
  by_contra hnot
  have hex : ∃ n : ℕ, ϖ ^ n • u ∈ lat hvt hR A Λ := DualLattice.exists_pow_smul_mem hk
    (by rw [IrreducibleModule.span_lattice]; trivial)
  set n := Nat.find hex with hn
  have hxL : ϖ ^ n • u ∈ lat hvt hR A Λ := Nat.find_spec hex
  have hn0 : n ≠ 0 := fun h ↦ hnot (by simpa [h] using hxL)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmL : ϖ ^ m • u ∉ lat hvt hR A Λ := Nat.find_min hex (by omega)
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hxx : formL hvt hR Λ (ϖ ^ n • u) (ϖ ^ n • u) =
      algebraMap A k (ϖ * (ϖ ^ (2 * n - 1) * a₀)) := by
    simp only [← algebraMap_smul k (ϖ ^ n) u, map_smul, LinearMap.smul_apply, ha₀, smul_eq_mul]
    have e2 : n + n = 2 * n - 1 + 1 := by omega
    rw [← map_mul, ← map_mul, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_succ', e2]
  obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (mem_smul_lat_of_formL_self_mem hinj hϖ hϖv hk hfund Λ hxL hxx)
  refine hmL ?_
  have : y = ϖ ^ m • u := by
    have e : (algebraMap A k ϖ) • y = (algebraMap A k ϖ) • (ϖ ^ m • u) := by
      rw [algebraMap_smul, algebraMap_smul, hyx, hm, pow_succ', mul_smul]
    exact smul_right_injective _ hϖ0 e
  exact this ▸ hy

end Polarization

end GrandLoop

end LieLean.QuantumGroup
