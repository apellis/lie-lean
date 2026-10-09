/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorModuleCrystal

/-!
# Tensor products of two `i`-strings in `U`-modules

Let `M₁`, `M₂` be integrable `U`-modules, `i ∈ I`, and `η ∈ M₁`, `ζ ∈ M₂` vectors killed by `Eᵢ`
with `⟨i, wt η⟩ = a`, `⟨i, wt ζ⟩ = b`. The `A`-span of the vectors `Fᵢ^{(s)} η ⊗ Fᵢ^{(t)} ζ`
(`QuantumGroup.TensorModule.pieceLattice`) is stable under the Kashiwara operators `ẽᵢ`, `f̃ᵢ` of
`M₁ ⊗ M₂`, and modulo `ϖ` times it they act by the tensor product rule, in the library's (Lusztig's)
order of the factors:

* `f̃ᵢ (Fᵢ^{(s)} η ⊗ Fᵢ^{(t)} ζ) ≡ Fᵢ^{(s)} η ⊗ Fᵢ^{(t+1)} ζ` if `s < b - t`, and
  `≡ Fᵢ^{(s+1)} η ⊗ Fᵢ^{(t)} ζ` otherwise (`QuantumGroup.TensorModule.kashiwaraF_piece_sub`);
* `ẽᵢ (Fᵢ^{(s)} η ⊗ Fᵢ^{(t)} ζ) ≡ Fᵢ^{(s)} η ⊗ Fᵢ^{(t-1)} ζ` (`0` if `t = 0`) if `s ≤ b - t`, and
  `≡ Fᵢ^{(s-1)} η ⊗ Fᵢ^{(t)} ζ` otherwise (`QuantumGroup.TensorModule.kashiwaraE_piece_sub`).

This is the rank-one tensor product rule ([HK] Thm. 4.4.3) transported along the flip
`M₁ ⊗ M₂ ≅ M₂ ⊗ M₁` (`QuantumGroup.TensorModule.flip_kashiwaraF`); it is the local form of the
tensor product rule used in Kashiwara's grand loop, where the factors are not yet known to have
crystal bases.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
-/

open TensorProduct Pointwise

namespace LieLean.QuantumGroup

namespace TensorModule

section Helpers

variable {k I : Type*} [Field k] {D : LusztigCartanDatum I} {v : k} (i : I) {A : Type*} [CommRing A]
  [Algebra A k]

lemma pow_d_mem_maximalIdeal [IsLocalRing A] {c : A} (hc : c ∈ IsLocalRing.maximalIdeal A) :
    c ^ D.d i ∈ IsLocalRing.maximalIdeal A :=
  Ideal.pow_mem_of_mem _ hc _ (D.d_pos i)

lemma algebraMap_pow_d {c : A} (hc : algebraMap A k c = v⁻¹) :
    algebraMap A k (c ^ D.d i) = (v ^ D.d i)⁻¹ := by
  rw [map_pow, hc, inv_pow]

lemma pow_d_smul_le {N : Type*} [AddCommGroup N] [Module A N] (c : A) (L : Submodule A N) :
    c ^ D.d i • L ≤ c • L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (D.d_pos i)
  rw [hn, zero_add, pow_succ', mul_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ hy)

end Helpers

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]
  (h₁ : IsIntegrable R v M₁) (h₂ : IsIntegrable R v M₂) (i : I)
  (A : Type*) [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂]

/-- The `A`-span of the `Fᵢ^{(s)} η ⊗ Fᵢ^{(t)} ζ`, `s ≤ a`, `t ≤ b`. -/
def pieceLattice (a b : ℕ) (η : M₁) (ζ : M₂) : Submodule A (TensorModule k M₁ M₂) :=
  Submodule.span A (Set.range fun x : Fin (a + 1) × Fin (b + 1) ↦
    mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF x.1 η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF x.2 ζ))

variable {A} {a b : ℕ} {η : M₁} {ζ : M₂}

/-- Under the flip, `pieceLattice` is the lattice of the tensor product of the two strings in
Kashiwara's order. -/
lemma mem_pieceLattice_iff (z : TensorModule k M₁ M₂) :
    z ∈ pieceLattice hv h₁ h₂ i A a b η ζ ↔
      flip M₁ M₂ z ∈ IntegrableSl2.tensorPieceLattice (nodeSl2 R v M₂ hv h₂ i).inv
        (nodeSl2 R v M₁ hv h₁ i).inv A b a ζ η := by
  let φ : TensorModule k M₁ M₂ ≃ₗ[A] M₂ ⊗[k] M₁ := (flip M₁ M₂).restrictScalars A
  have h : (pieceLattice hv h₁ h₂ i A a b η ζ).map φ.toLinearMap =
      IntegrableSl2.tensorPieceLattice (nodeSl2 R v M₂ hv h₂ i).inv
        (nodeSl2 R v M₁ hv h₁ i).inv A b a ζ η := by
    rw [pieceLattice, Submodule.map_span, IntegrableSl2.tensorPieceLattice]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_range, Prod.exists]
    constructor
    · rintro ⟨_, ⟨s, t, rfl⟩, rfl⟩
      exact ⟨t, s, by simp [φ, flip_mk_tmul, IntegrableSl2.inv_dF]⟩
    · rintro ⟨t, s, rfl⟩
      exact ⟨_, ⟨s, t, rfl⟩, by simp [φ, flip_mk_tmul, IntegrableSl2.inv_dF]⟩
  rw [← h, Submodule.mem_map_equiv]
  simp [φ]

lemma flip_smul (c : A) (z : TensorModule k M₁ M₂) : flip M₁ M₂ (c • z) = c • flip M₁ M₂ z :=
  (flip M₁ M₂).toLinearMap.map_smul_of_tower c z

lemma mem_smul_pieceLattice_iff (c : A) (z : TensorModule k M₁ M₂) :
    z ∈ c • pieceLattice hv h₁ h₂ i A a b η ζ ↔
      flip M₁ M₂ z ∈ c • IntegrableSl2.tensorPieceLattice (nodeSl2 R v M₂ hv h₂ i).inv
        (nodeSl2 R v M₁ hv h₁ i).inv A b a ζ η := by
  rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨flip M₁ M₂ y, (mem_pieceLattice_iff hv h₁ h₂ i y).1 hy, (flip_smul c y).symm⟩
  · rintro ⟨y', hy', he⟩
    refine ⟨(flip M₁ M₂).symm y', (mem_pieceLattice_iff hv h₁ h₂ i _).2
      (by rw [LinearEquiv.apply_symm_apply]; exact hy'), ?_⟩
    apply (flip M₁ M₂).injective
    rw [flip_smul, LinearEquiv.apply_symm_apply, he]

lemma prim_inv {q : k} {M : Type*} [AddCommGroup M] [Module k M] (V : IntegrableSl2 q M) (p : ℤ) :
    V.inv.prim p = V.prim p := rfl

lemma tmul_mem_pieceLattice (hη : η ∈ (nodeSl2 R v M₁ hv h₁ i).prim a)
    (hζ : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).prim b) (s t : ℕ) :
    mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF s η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF t ζ) ∈
      pieceLattice hv h₁ h₂ i A a b η ζ := by
  have hζ' : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).inv.prim b := by rw [prim_inv]; exact hζ
  have hη' : η ∈ (nodeSl2 R v M₁ hv h₁ i).inv.prim a := by rw [prim_inv]; exact hη
  rw [mem_pieceLattice_iff (A := A), flip_mk_tmul]
  simpa only [IntegrableSl2.inv_dF] using IntegrableSl2.tmul_mem_tensorPieceLattice (A := A) _ _
    (inv_ne_zero (pow_d_ne_zero i)) (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i)) hζ' hη' t s

variable [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)

include hϖ hϖv in
/-- `ẽᵢ` preserves the lattice of a tensor product of two `i`-strings. -/
theorem kashiwaraE_mem_pieceLattice (hη : η ∈ (nodeSl2 R v M₁ hv h₁ i).prim a)
    (hζ : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).prim b) (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0)
    {z : TensorModule k M₁ M₂} (hz : z ∈ pieceLattice hv h₁ h₂ i A a b η ζ) :
    kashiwaraE R v _ hv (isIntegrable h₁ h₂) i z ∈ pieceLattice hv h₁ h₂ i A a b η ζ := by
  have hζ' : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).inv.prim b := by rw [prim_inv]; exact hζ
  have hη' : η ∈ (nodeSl2 R v M₁ hv h₁ i).inv.prim a := by rw [prim_inv]; exact hη
  rw [mem_pieceLattice_iff] at hz ⊢
  rw [flip_kashiwaraE hv h₁ h₂ i]
  exact IntegrableSl2.eTilde_mem_tensorPieceLattice (nodeSl2 R v M₂ hv h₂ i).inv
    (nodeSl2 R v M₁ hv h₁ i).inv (inv_ne_zero (pow_d_ne_zero i))
    (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i)) (pow_d_mem_maximalIdeal (D := D) i hϖ)
    (algebraMap_pow_d (D := D) i hϖv) hζ' hη' hζ0 hη0 hz

include hϖ hϖv in
/-- `f̃ᵢ` preserves the lattice of a tensor product of two `i`-strings. -/
theorem kashiwaraF_mem_pieceLattice (hη : η ∈ (nodeSl2 R v M₁ hv h₁ i).prim a)
    (hζ : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).prim b) (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0)
    {z : TensorModule k M₁ M₂} (hz : z ∈ pieceLattice hv h₁ h₂ i A a b η ζ) :
    kashiwaraF R v _ hv (isIntegrable h₁ h₂) i z ∈ pieceLattice hv h₁ h₂ i A a b η ζ := by
  have hζ' : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).inv.prim b := by rw [prim_inv]; exact hζ
  have hη' : η ∈ (nodeSl2 R v M₁ hv h₁ i).inv.prim a := by rw [prim_inv]; exact hη
  rw [mem_pieceLattice_iff] at hz ⊢
  rw [flip_kashiwaraF hv h₁ h₂ i]
  exact IntegrableSl2.fTilde_mem_tensorPieceLattice (nodeSl2 R v M₂ hv h₂ i).inv
    (nodeSl2 R v M₁ hv h₁ i).inv (inv_ne_zero (pow_d_ne_zero i))
    (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i)) (pow_d_mem_maximalIdeal (D := D) i hϖ)
    (algebraMap_pow_d (D := D) i hϖv) hζ' hη' hζ0 hη0 hz

include hϖ hϖv in
/-- **Tensor product rule for `f̃ᵢ`** on two `i`-strings, in the library's order of the factors:
modulo `ϖ L`, `f̃ᵢ (Fᵢ^{(s)} η ⊗ Fᵢ^{(t)} ζ)` is `Fᵢ^{(s)} η ⊗ Fᵢ^{(t+1)} ζ` if `s < b - t` and
`Fᵢ^{(s+1)} η ⊗ Fᵢ^{(t)} ζ` otherwise. -/
theorem kashiwaraF_piece_sub (hη : η ∈ (nodeSl2 R v M₁ hv h₁ i).prim a)
    (hζ : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).prim b) (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0) {s t : ℕ}
    (hs : s ≤ a) (ht : t ≤ b) :
    kashiwaraF R v _ hv (isIntegrable h₁ h₂) i
        (mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF s η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF t ζ)) -
      (if s < b - t then
        mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF s η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF (t + 1) ζ)
      else
        mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF (s + 1) η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF t ζ)) ∈
      ϖ • pieceLattice hv h₁ h₂ i A a b η ζ := by
  have hζ' : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).inv.prim b := by rw [prim_inv]; exact hζ
  have hη' : η ∈ (nodeSl2 R v M₁ hv h₁ i).inv.prim a := by rw [prim_inv]; exact hη
  rw [mem_smul_pieceLattice_iff, map_sub, flip_kashiwaraF hv h₁ h₂ i, flip_mk_tmul]
  have h := IntegrableSl2.fTilde_tensorPiece_sub (nodeSl2 R v M₂ hv h₂ i).inv
    (nodeSl2 R v M₁ hv h₁ i).inv (inv_ne_zero (pow_d_ne_zero i))
    (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i)) (pow_d_mem_maximalIdeal (D := D) i hϖ)
    (algebraMap_pow_d (D := D) i hϖv) hζ' hη' hζ0 hη0 ht hs
  simp only [IntegrableSl2.inv_dF] at h
  refine pow_d_smul_le (D := D) i ϖ _ ?_
  convert h using 2
  split_ifs <;> simp [flip_mk_tmul]

include hϖ hϖv in
/-- **Tensor product rule for `ẽᵢ`** on two `i`-strings, in the library's order of the factors:
modulo `ϖ L`, `ẽᵢ (Fᵢ^{(s)} η ⊗ Fᵢ^{(t)} ζ)` is `Fᵢ^{(s)} η ⊗ Fᵢ^{(t-1)} ζ` (`0` if `t = 0`) if
`s ≤ b - t` and `Fᵢ^{(s-1)} η ⊗ Fᵢ^{(t)} ζ` otherwise. -/
theorem kashiwaraE_piece_sub (hη : η ∈ (nodeSl2 R v M₁ hv h₁ i).prim a)
    (hζ : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).prim b) (hη0 : η ≠ 0) (hζ0 : ζ ≠ 0) {s t : ℕ}
    (hs : s ≤ a) (ht : t ≤ b) :
    kashiwaraE R v _ hv (isIntegrable h₁ h₂) i
        (mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF s η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF t ζ)) -
      (if s ≤ b - t then
        (if t = 0 then 0 else
          mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF s η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF (t - 1) ζ))
      else
        mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF (s - 1) η ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF t ζ)) ∈
      ϖ • pieceLattice hv h₁ h₂ i A a b η ζ := by
  have hζ' : ζ ∈ (nodeSl2 R v M₂ hv h₂ i).inv.prim b := by rw [prim_inv]; exact hζ
  have hη' : η ∈ (nodeSl2 R v M₁ hv h₁ i).inv.prim a := by rw [prim_inv]; exact hη
  rw [mem_smul_pieceLattice_iff, map_sub, flip_kashiwaraE hv h₁ h₂ i, flip_mk_tmul]
  have h := IntegrableSl2.eTilde_tensorPiece_sub (nodeSl2 R v M₂ hv h₂ i).inv
    (nodeSl2 R v M₁ hv h₁ i).inv (inv_ne_zero (pow_d_ne_zero i))
    (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i)) (pow_d_mem_maximalIdeal (D := D) i hϖ)
    (algebraMap_pow_d (D := D) i hϖv) hζ' hη' hζ0 hη0 ht hs
  simp only [IntegrableSl2.inv_dF] at h
  refine pow_d_smul_le (D := D) i ϖ _ ?_
  convert h using 2
  split_ifs <;> simp [flip_mk_tmul]

end TensorModule

end LieLean.QuantumGroup
