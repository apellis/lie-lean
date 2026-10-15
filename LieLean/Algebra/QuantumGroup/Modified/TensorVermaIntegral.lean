/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.TensorVerma
import LieLean.Algebra.QuantumGroup.Modified.Triangular

/-!
# The `𝒜`-form of `U̇ 1_ζ` and tensor products of Verma modules

Over `ℚ(v)`, with `𝒜 = ℤ[v, v⁻¹]`, let `𝒜M_Λ ⊆ M_Λ` be the `𝒜`-span of the vectors
`F_w η_Λ` (`F_w` a monomial in the divided powers `Fᵢ^{(n)}`, `η_Λ` the highest weight vector);
it is the image of `𝒜f` under `f ≅ M_Λ`. **[Lus] 23.3.2 (a)**: for `Λ, Λ' ∈ X` and
`ζ = Λ' - Λ`, the isomorphism `U̇ 1_ζ ≃ ʷM_Λ ⊗ M_{Λ'}`, `u 1_ζ ↦ u (ξ ⊗ η)`, of [Lus] 23.3.1 (c)
(`Modified.vermaTensorEquiv`) maps `𝒜U̇ 1_ζ` onto the `𝒜`-span of the `a ⊗ b`,
`a ∈ 𝒜M_Λ`, `b ∈ 𝒜M_{Λ'}`.

`𝒜`-spans are encoded as `ℤ`-spans of the multiples by the powers `v^k` (`laurentSpan`), as for
`LusztigF.fIntegral`. `𝒜U̇ 1_ζ` is `𝒜U̇ ∩ U̇ 1_ζ`, since `1_ζ ∈ 𝒜U̇`.

## Main definitions and results

* `QuantumGroup.laurentSpan`: the `𝒜`-span of a subset of a `ℚ(v)`-vector space.
* `QuantumGroup.TensorModule.qDivPow_F_smul_tmul`: `Fᵢ^{(n)} (x ⊗ y) =
  Σ_{s+t=n} vᵢ^{st - s⟨i,μ⟩} Fᵢ^{(s)} x ⊗ Fᵢ^{(t)} y` for `y` of weight `μ` (any field, `v` not
  a root of unity).
* `QuantumGroup.Modified.vermaLattice`: `𝒜M_Λ`; `qDivPow_E_smul_mem_vermaLattice`: it is
  stable under the `Eᵢ^{(n)}` ([Lus] 23.3.2, from the commutation formulas 23.1.3).
* `QuantumGroup.Modified.vermaTensorLattice`: the `𝒜`-span of the `a ⊗ b`.
* `QuantumGroup.Modified.leftActOne_mem_aForm_iff`, `vermaTensorEquiv_mem_iff`:
  **[Lus] 23.3.2 (a)**.

## Proof

As in [Lus] 23.3.2, the argument of 23.3.1 (c) is repeated over `𝒜`. The `𝒜`-span of the
`F_w E_{w'} 1_ζ` is `𝒜U̇ 1_ζ` ([Lus] 23.2.2 (a), `Modified.aForm_eq_aFormFE`). Since
`E_{w'}(ξ ⊗ η) = F_{w'}η_Λ ⊗ η` (in `ʷM_Λ`) and the lattice is stable under the `Fᵢ^{(n)}` (by
the coproduct formula and the stability of `𝒜M_Λ` under the `Eᵢ^{(n)}`), these elements map into
the lattice. Conversely, `F_w (a ⊗ η) = a ⊗ F_w η` modulo the `𝒜`-span of the `a' ⊗ F_{w''} η`
with `w''` of smaller degree, which gives the reverse inclusion by induction on the degree.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.3, 23.2.2, 23.3.
-/

open LieLean TensorProduct Finset

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X

/-! ### `𝒜`-spans -/

section LaurentSpan

variable {V W : Type*} [AddCommGroup V] [Module 𝕂 V] [AddCommGroup W] [Module 𝕂 W]

/-- The `𝒜`-span of `S ⊆ V`: the `ℤ`-span of the `v^k s`, `k ∈ ℤ`, `s ∈ S`. -/
def laurentSpan (S : Set V) : Submodule ℤ V :=
  Submodule.span ℤ {x | ∃ (k : ℤ), ∃ s ∈ S, x = (𝕧 ^ k) • s}

lemma mem_laurentSpan_of_mem {S : Set V} {s : V} (hs : s ∈ S) : s ∈ laurentSpan S :=
  Submodule.subset_span ⟨0, s, hs, by rw [zpow_zero, one_smul]⟩

lemma zpow_smul_mem_laurentSpan {S : Set V} (k : ℤ) {x : V} (hx : x ∈ laurentSpan S) :
    (𝕧 ^ k) • x ∈ laurentSpan S := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, s, hs, rfl⟩ := hx
    exact Submodule.subset_span ⟨k + l, s, hs, by rw [smul_smul, ← zpow_add₀ RatFunc.X_ne_zero]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

lemma laurent_smul_mem_laurentSpan {S : Set V} {c : 𝕂} (hc : Modified.IsLaurent c) {x : V}
    (hx : x ∈ laurentSpan S) : c • x ∈ laurentSpan S := by
  obtain ⟨a, rfl⟩ := hc
  induction a using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_smul]; exact add_mem hp hq
  | C_mul_T n c =>
    have hC : LusztigF.integralLaurentEval (LaurentPolynomial.C c) = (c : 𝕂) := by
      simp [LusztigF.integralLaurentEval]
    rw [_root_.map_mul, hC, LusztigF.integralLaurentEval_T, mul_smul, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ c (zpow_smul_mem_laurentSpan n hx)

/-- A `ℚ(v)`-linear map sending `S` into the `𝒜`-span of `T` sends the `𝒜`-span of `S` into it. -/
lemma map_mem_laurentSpan {S : Set V} {T : Set W} (f : V →ₗ[𝕂] W)
    (hf : ∀ s ∈ S, f s ∈ laurentSpan T) {x : V} (hx : x ∈ laurentSpan S) :
    f x ∈ laurentSpan T := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, s, hs, rfl⟩ := hx
    rw [map_smul]; exact zpow_smul_mem_laurentSpan k (hf s hs)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ c hx

end LaurentSpan

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}

/-! ### Divided powers of `Fᵢ` on modules -/

section DividedPowers

variable {k : Type*} [Field k] {R : D.RootDatum Y} {v : k} [NeZero v]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-- `Fᵢ^{(n)} M^μ ⊆ M^{μ - n i'}`. -/
lemma qDivPow_F_smul_mem_weightSpace {μ : Y →+ ℤ} {m : M}
    (hm : m ∈ weightSpace R v M μ) (i : I) (n : ℕ) :
    qDivPow (v ^ D.d i) n (F R v i) • m ∈ weightSpace R v M (μ - n • R.root i) := by
  rw [qDivPow, smul_assoc]
  refine Submodule.smul_mem _ _ ?_
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ', mul_smul, succ_nsmul, sub_add_eq_sub_sub]
    exact F_smul_mem_weightSpace ih i

/-- `Fᵢ Fᵢ^{(m)} = [m+1]ᵢ Fᵢ^{(m+1)}` on a module. -/
lemma F_smul_qDivPow_F_smul (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) (m : ℕ) (z : M) :
    F R v i • (qDivPow (v ^ D.d i) m (F R v i) • z) =
      qInt (v ^ D.d i) (m + 1) • (qDivPow (v ^ D.d i) (m + 1) (F R v i) • z) := by
  rw [← mul_smul, mul_qDivPow _ _ _ (qInt_vd_ne_zero hv i m.succ_pos), smul_assoc]

end DividedPowers

/-! ### Divided powers of `Fᵢ` on tensor products -/

namespace TensorModule

variable {k : Type*} [Field k] {R : D.RootDatum Y} {v : k} [NeZero v]
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁] [AddCommGroup M₂] [Module k M₂]
  [Module (QuantumGroup R v) M₂] [IsScalarTower k (QuantumGroup R v) M₂]

/-- **`Fᵢ^{(n)}` on `M₁ ⊗ M₂`**: for `y ∈ M₂^μ`,
`Fᵢ^{(n)} (x ⊗ y) = Σ_{s+t=n} vᵢ^{st - s⟨i,μ⟩} Fᵢ^{(s)} x ⊗ Fᵢ^{(t)} y`. -/
theorem qDivPow_F_smul_tmul (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) (x : M₁) {μ : Y →+ ℤ}
    {y : M₂} (hy : y ∈ weightSpace R v M₂ μ) (n : ℕ) :
    qDivPow (v ^ D.d i) n (F R v i) • mk M₁ M₂ (x ⊗ₜ[k] y) =
      ∑ p ∈ antidiagonal n, (v ^ D.d i) ^ ((p.1 : ℤ) * p.2 - p.1 * μ (R.coroot i)) •
        mk M₁ M₂ ((qDivPow (v ^ D.d i) p.1 (F R v i) • x) ⊗ₜ[k]
          (qDivPow (v ^ D.d i) p.2 (F R v i) • y)) := by
  set q := v ^ D.d i with hqdef
  set h := μ (R.coroot i) with hh
  have hq0 : q ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  induction n with
  | zero => simp [qDivPow_zero']
  | succ n ih =>
    have hne : qInt q (n + 1) ≠ 0 := qInt_vd_ne_zero hv i n.succ_pos
    have hK : ∀ t : ℕ, K R v (-ktilde R i) • (qDivPow q t (F R v i) • y) =
        q ^ (-(h - 2 * t)) • (qDivPow q t (F R v i) • y) := by
      intro t
      rw [K_neg_ktilde_smul_of_mem_weightSpace (qDivPow_F_smul_mem_weightSpace hy i t),
        AddMonoidHom.sub_apply, AddMonoidHom.nsmul_apply, R.root_coroot, D.cartanMatrix_self]
      congr 2
      rw [nsmul_eq_mul]; ring
    refine smul_right_injective _ hne ?_
    simp only
    rw [← F_smul_qDivPow_F_smul hv, ih, Finset.smul_sum]
    have hL : ∀ p ∈ antidiagonal n, F R v i • (q ^ ((p.1 : ℤ) * p.2 - p.1 * h) •
        mk M₁ M₂ ((qDivPow q p.1 (F R v i) • x) ⊗ₜ[k] (qDivPow q p.2 (F R v i) • y))) =
        (q ^ ((p.1 : ℤ) * p.2 - p.1 * h) * qInt q (p.1 + 1) * q ^ (-(h - 2 * p.2))) •
          mk M₁ M₂ ((qDivPow q (p.1 + 1) (F R v i) • x) ⊗ₜ[k] (qDivPow q p.2 (F R v i) • y)) +
        (q ^ ((p.1 : ℤ) * p.2 - p.1 * h) * qInt q (p.2 + 1)) •
          mk M₁ M₂ ((qDivPow q p.1 (F R v i) • x) ⊗ₜ[k]
            (qDivPow q (p.2 + 1) (F R v i) • y)) := by
      intro p _
      rw [smul_comm, F_smul_tmul, hK, F_smul_qDivPow_F_smul hv, F_smul_qDivPow_F_smul hv]
      simp only [← smul_tmul', tmul_smul, map_add, LinearEquiv.map_smul, smul_add, smul_smul]
      congr 2
      ring
    rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib, Finset.smul_sum]
    have hR : ∀ p ∈ antidiagonal (n + 1), qInt q (n + 1) • (q ^ ((p.1 : ℤ) * p.2 - p.1 * h) •
        mk M₁ M₂ ((qDivPow q p.1 (F R v i) • x) ⊗ₜ[k] (qDivPow q p.2 (F R v i) • y))) =
        (q ^ ((p.1 : ℤ) * p.2 - p.1 * h) * q ^ (p.2 : ℤ) * qInt q p.1) •
          mk M₁ M₂ ((qDivPow q p.1 (F R v i) • x) ⊗ₜ[k] (qDivPow q p.2 (F R v i) • y)) +
        (q ^ ((p.1 : ℤ) * p.2 - p.1 * h) * q ^ (-(p.1 : ℤ)) * qInt q p.2) •
          mk M₁ M₂ ((qDivPow q p.1 (F R v i) • x) ⊗ₜ[k] (qDivPow q p.2 (F R v i) • y)) := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [smul_smul, ← add_smul, ← hp, add_comm p.1 p.2, qInt_add, zpow_neg, zpow_natCast,
        zpow_natCast, inv_pow]
      congr 1
      ring
    rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ']
    simp only [qInt_zero, mul_zero, zero_smul, zero_add]
    congr 1
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      congr 1
      rw [mul_right_comm, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
      congr 2
      push_cast
      ring
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      congr 1
      rw [← zpow_add₀ hq0]
      congr 2
      push_cast
      ring

end TensorModule

namespace Modified

variable {R : D.RootDatum Y}

attribute [local instance] decEqIdx

/-! ### The lattice `𝒜M_Λ` -/

section Lattice

variable (Λ Λ' : Y →+ ℤ)

variable (R) in
/-- **`𝒜M_Λ`**: the `𝒜`-span of the vectors `F_w η_Λ` of the Verma module `M_Λ`, the image of
`𝒜f` under `f ≅ M_Λ` ([Lus] 23.3.2). -/
def vermaLattice : Submodule ℤ (VermaModule R 𝕧 Λ) :=
  laurentSpan {x | ∃ w : List (I × ℕ), x = fPow R w • VermaModule.hwv R 𝕧 Λ}

lemma fPow_smul_hwv_mem_vermaLattice (w : List (I × ℕ)) :
    fPow R w • VermaModule.hwv R 𝕧 Λ ∈ vermaLattice R Λ :=
  mem_laurentSpan_of_mem ⟨w, rfl⟩

lemma fPow_smul_hwv_mem_weightSpace (w : List (I × ℕ)) :
    fPow R w • VermaModule.hwv R 𝕧 Λ ∈ weightSpace R 𝕧 (VermaModule R 𝕧 Λ) (-wtW R w + Λ) :=
  smul_mem_weightSpace_of_mem_adWeightSpace (fPow_mem w) VermaModule.hwv_mem_weightSpace

lemma fPow_append (w w' : List (I × ℕ)) : fPow R (w ++ w') = fPow R w * fPow R w' := by
  simp [fPow, List.prod_append]

variable {Λ}

/-- `𝒜M_Λ` is stable under the `F_w`. -/
lemma fPow_smul_mem_vermaLattice (w : List (I × ℕ)) {x : VermaModule R 𝕧 Λ}
    (hx : x ∈ vermaLattice R Λ) : fPow R w • x ∈ vermaLattice R Λ := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (fPow R w)) ?_ hx
  rintro _ ⟨w', rfl⟩
  rw [DistribSMul.toLinearMap_apply, ← mul_smul, ← fPow_append]
  exact fPow_smul_hwv_mem_vermaLattice Λ _

/-- `𝒜M_Λ` is stable under the `Fᵢ^{(n)}`. -/
lemma qDivPow_F_smul_mem_vermaLattice (i : I) (n : ℕ) {x : VermaModule R 𝕧 Λ}
    (hx : x ∈ vermaLattice R Λ) : qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • x ∈ vermaLattice R Λ := by
  simpa [fPow] using fPow_smul_mem_vermaLattice [(i, n)] hx

/-- **`𝒜M_Λ` is stable under the `Eᵢ^{(n)}`** ([Lus] 23.3.2, by the commutation formulas
23.1.3). -/
theorem qDivPow_E_smul_mem_vermaLattice (i : I) (N : ℕ) {x : VermaModule R 𝕧 Λ}
    (hx : x ∈ vermaLattice R Λ) : qDivPow (𝕧 ^ D.d i) N (E R 𝕧 i) • x ∈ vermaLattice R Λ := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (qDivPow (𝕧 ^ D.d i) N (E R 𝕧 i)))
    ?_ hx
  rintro _ ⟨w, rfl⟩
  rw [DistribSMul.toLinearMap_apply]
  induction w generalizing N with
  | nil =>
    rcases N with _ | N
    · rw [qDivPow_zero', one_smul]; exact fPow_smul_hwv_mem_vermaLattice Λ []
    · rw [fPow_nil, one_smul, qDivPow, smul_assoc, pow_succ, mul_smul, VermaModule.E_smul_hwv,
        smul_zero, smul_zero]
      exact zero_mem _
  | cons p w ih =>
    obtain ⟨j, M⟩ := p
    rw [fPow_cons, mul_smul]
    by_cases hij : i = j
    · subst hij
      rw [qDivPow_E_smul_qDivPow_F_smul ratFunc_X_not_root (fPow_smul_hwv_mem_weightSpace Λ w)]
      refine sum_mem fun t _ ↦ ?_
      unfold efTerm
      split_ifs
      · exact laurent_smul_mem_laurentSpan (isLaurent_qBinomZ _ (D.d_pos i) _ _)
          (qDivPow_F_smul_mem_vermaLattice _ _ (ih _))
      · exact zero_mem _
    · have hc : Commute (qDivPow (𝕧 ^ D.d i) N (E R 𝕧 i)) (qDivPow (𝕧 ^ D.d j) M (F R 𝕧 j)) :=
        ((Commute.pow_pow (E_mul_F_of_ne (R := R) (v := 𝕧) hij) N M).smul_left _).smul_right _
      rw [← mul_smul, hc.eq, mul_smul]
      exact qDivPow_F_smul_mem_vermaLattice _ _ (ih N)

end Lattice

/-! ### The lattice in `ʷM_Λ ⊗ M_{Λ'}` -/

section TensorLattice

variable (Λ Λ' : Y →+ ℤ)

local notation "VT" =>
  TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ')

local notation "tw" => ChevalleyTwist.toTwist R 𝕧 (VermaModule R 𝕧 Λ)

variable (R) in
/-- The `𝒜`-span of the `a ⊗ b`, `a ∈ 𝒜M_Λ`, `b ∈ 𝒜M_{Λ'}`, in `ʷM_Λ ⊗ M_{Λ'}`
(`ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}` in [Lus] 23.3.2). -/
def vermaTensorLattice : Submodule ℤ VT :=
  laurentSpan {z | ∃ w w' : List (I × ℕ), z = TensorModule.mk _ _
    (tw (fPow R w • VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] (fPow R w' • VermaModule.hwv R 𝕧 Λ'))}

variable {Λ Λ'}

lemma tmul_mem_vermaTensorLattice {a : VermaModule R 𝕧 Λ} {b : VermaModule R 𝕧 Λ'}
    (ha : a ∈ vermaLattice R Λ) (hb : b ∈ vermaLattice R Λ') :
    TensorModule.mk _ _ (tw a ⊗ₜ[𝕂] b) ∈ vermaTensorLattice R Λ Λ' := by
  have h := map_mem_laurentSpan (T := {z | ∃ w w' : List (I × ℕ), z = TensorModule.mk _ _
    (tw (fPow R w • VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] (fPow R w' • VermaModule.hwv R 𝕧 Λ'))})
    ((TensorModule.mk _ _).toLinearMap ∘ₗ (TensorProduct.mk 𝕂 _ _).flip b ∘ₗ (tw).toLinearMap)
    ?_ ha
  · exact h
  rintro _ ⟨w, rfl⟩
  have h' := map_mem_laurentSpan (T := {z | ∃ w w' : List (I × ℕ), z = TensorModule.mk _ _
    (tw (fPow R w • VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] (fPow R w' • VermaModule.hwv R 𝕧 Λ'))})
    ((TensorModule.mk _ _).toLinearMap ∘ₗ
      TensorProduct.mk 𝕂 _ _ (tw (fPow R w • VermaModule.hwv R 𝕧 Λ))) ?_ hb
  · exact h'
  rintro _ ⟨w', rfl⟩
  exact mem_laurentSpan_of_mem ⟨w, w', rfl⟩

lemma qDivPow_F_smul_toTwist (i : I) (n : ℕ) (a : VermaModule R 𝕧 Λ) :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • tw a = tw (qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i) • a) := by
  rw [ChevalleyTwist.smul_toTwist, map_qDivPow', chevalley_F]

/-- The lattice is stable under the `Fᵢ^{(n)}`. -/
theorem qDivPow_F_smul_mem_vermaTensorLattice (i : I) (n : ℕ) {z : VT}
    (hz : z ∈ vermaTensorLattice R Λ Λ') :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • z ∈ vermaTensorLattice R Λ Λ' := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)))
    ?_ hz
  rintro _ ⟨w, w', rfl⟩
  rw [DistribSMul.toLinearMap_apply, TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _
    (fPow_smul_hwv_mem_weightSpace Λ' w')]
  refine sum_mem fun p _ ↦ laurent_smul_mem_laurentSpan (isLaurent_vd_zpow _ _) ?_
  rw [qDivPow_F_smul_toTwist]
  exact tmul_mem_vermaTensorLattice
    (qDivPow_E_smul_mem_vermaLattice _ _ (fPow_smul_hwv_mem_vermaLattice Λ w))
    (qDivPow_F_smul_mem_vermaLattice _ _ (fPow_smul_hwv_mem_vermaLattice Λ' w'))

lemma fPow_smul_mem_vermaTensorLattice (w : List (I × ℕ)) {z : VT}
    (hz : z ∈ vermaTensorLattice R Λ Λ') : fPow R w • z ∈ vermaTensorLattice R Λ Λ' := by
  induction w with
  | nil => rwa [fPow_nil, one_smul]
  | cons p w ih => rw [fPow_cons, mul_smul]; exact qDivPow_F_smul_mem_vermaTensorLattice _ _ ih

/-- `E_w (ξ ⊗ η) = F_w η_Λ ⊗ η` in `ʷM_Λ ⊗ M_{Λ'}`. -/
lemma ePow_smul_vermaTensorHwv (w : List (I × ℕ)) :
    ePow R w • vermaTensorHwv R 𝕧 Λ Λ' =
      TensorModule.mk _ _ (tw (fPow R w • VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂]
        VermaModule.hwv R 𝕧 Λ') := by
  have e : ePow R w = plusHom R 𝕧
      ((w.map fun p ↦ qDivPow (𝕧 ^ D.d p.1) p.2 (LusztigF.θ 𝕂 p.1)).prod) := by
    simp only [ePow, map_list_prod, List.map_map, Function.comp_def, map_qDivPow', plusHom_θ]
  rw [vermaTensorHwv, e, plusHom_smul_tmul_hwv, ← e, ChevalleyTwist.smul_toTwist, chevalley_ePow]

lemma fPow_mul_ePow_smul_mem (w w' : List (I × ℕ)) :
    (fPow R w * ePow R w') • vermaTensorHwv R 𝕧 Λ Λ' ∈ vermaTensorLattice R Λ Λ' := by
  rw [mul_smul, ePow_smul_vermaTensorHwv]
  refine fPow_smul_mem_vermaTensorLattice w (tmul_mem_vermaTensorLattice
    (fPow_smul_hwv_mem_vermaLattice Λ w') ?_)
  simpa using fPow_smul_hwv_mem_vermaLattice Λ' []

/-- **[Lus] 23.3.2 (a)**, first inclusion: `u (ξ ⊗ η)` lies in the lattice if `u 1_ζ ∈ 𝒜U̇`. -/
theorem smul_vermaTensorHwv_mem_of_mem_aForm {u : QuantumGroup R 𝕧}
    (hu : leftActOne R ratFunc_X_not_root (Λ' - Λ) u ∈ aForm R) :
    u • vermaTensorHwv R 𝕧 Λ Λ' ∈ vermaTensorLattice R Λ Λ' := by
  rw [← weightAct_leftActOne ratFunc_X_not_root _ _ (vermaTensorHwv_mem_weightSpace Λ Λ')]
  have hu' : leftActOne R ratFunc_X_not_root (Λ' - Λ) u ∈ (aForm R).toSubmodule := hu
  rw [aForm_eq_aFormFE] at hu'
  generalize leftActOne R ratFunc_X_not_root (Λ' - Λ) u = x at hu' ⊢
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, w', L, l, h, rfl⟩ := hx
    rw [weightAct_elt]
    split_ifs
    · exact fPow_mul_ePow_smul_mem w w'
    · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [laurent_smul, map_smul]; exact laurent_smul_mem_laurentSpan ⟨a, rfl⟩ hx

end TensorLattice

/-! ### The reverse inclusion -/

/-- The degree `n₁ + ⋯ + nₖ` of `w = [(i₁, n₁), …, (iₖ, nₖ)]`. -/
def degW (w : List (I × ℕ)) : ℕ := (w.map Prod.snd).sum

omit [DecidableEq I] in
lemma degW_cons (p : I × ℕ) (w : List (I × ℕ)) : degW (p :: w) = degW w + p.2 := by
  simp [degW, add_comm]

lemma fPow_cons' (i : I) (n : ℕ) (w : List (I × ℕ)) :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) * fPow R w = fPow R ((i, n) :: w) := by
  rw [fPow_cons]

variable (R) in
/-- The `𝒜`-span of the `F_w E_{w'}` in `U`. -/
def fePowSpan : Submodule ℤ (QuantumGroup R 𝕧) :=
  laurentSpan {u | ∃ w w' : List (I × ℕ), u = fPow R w * ePow R w'}

/-- `u 1_ζ ∈ 𝒜U̇` for `u` in the `𝒜`-span of the `F_w E_{w'}` ([Lus] 23.2.2 (a)). -/
lemma leftActOne_mem_aForm_of_mem_fePowSpan (ζ : Y →+ ℤ) {u : QuantumGroup R 𝕧}
    (hu : u ∈ fePowSpan R) : leftActOne R ratFunc_X_not_root ζ u ∈ aForm R := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, _, ⟨w, w', rfl⟩, rfl⟩ := hx
    rw [map_smul, leftActOne_eq_elt ratFunc_X_not_root (fPow_mul_ePow_mem w w')]
    refine smul_mem_aForm (isLaurent_zpow k) ?_
    have h := elt_fPow_ePow_mem (R := R) (L := ζ + (wtW R w' - wtW R w)) (l := ζ)
      (by simpa using fPow_mul_ePow_mem w w')
    rw [← aForm_eq_aFormFE] at h
    exact h
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c

section Reverse

variable {Λ Λ' : Y →+ ℤ}

local notation "VT" =>
  TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ')

local notation "tw" => ChevalleyTwist.toTwist R 𝕧 (VermaModule R 𝕧 Λ)

local notation "mkT" =>
  TensorModule.mk (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ')

variable (R Λ Λ') in
/-- The vectors `u (ξ ⊗ η)`, `u` in the `𝒜`-span of the `F_w E_{w'}`. -/
def fePowImage : Submodule ℤ VT :=
  (fePowSpan R).map (LinearMap.toSpanSingleton (QuantumGroup R 𝕧) _
    (vermaTensorHwv R 𝕧 Λ Λ')).toAddMonoidHom.toIntLinearMap

lemma mem_fePowImage {z : VT} :
    z ∈ fePowImage R Λ Λ' ↔ ∃ u ∈ fePowSpan R, u • vermaTensorHwv R 𝕧 Λ Λ' = z := by
  simp [fePowImage]

lemma zpow_smul_mem_fePowImage (k : ℤ) {z : VT} (hz : z ∈ fePowImage R Λ Λ') :
    (𝕧 ^ k) • z ∈ fePowImage R Λ Λ' := by
  obtain ⟨u, hu, rfl⟩ := mem_fePowImage.1 hz
  exact mem_fePowImage.2 ⟨(𝕧 ^ k) • u, zpow_smul_mem_laurentSpan k hu, smul_assoc _ _ _⟩

lemma fPow_mul_ePow_smul_mem_fePowImage (w w' : List (I × ℕ)) :
    (fPow R w * ePow R w') • vermaTensorHwv R 𝕧 Λ Λ' ∈ fePowImage R Λ Λ' :=
  mem_fePowImage.2 ⟨_, mem_laurentSpan_of_mem ⟨w, w', rfl⟩, rfl⟩

variable (Λ Λ') in
/-- The span of the `a ⊗ F_w η`, `a ∈ 𝒜M_Λ`, `w` of degree `< d`. -/
def degTensorSpan (d : ℕ) : Submodule ℤ VT :=
  Submodule.span ℤ {z | ∃ a ∈ vermaLattice R Λ, ∃ w : List (I × ℕ), degW w < d ∧
    z = mkT (tw a ⊗ₜ[𝕂] (fPow R w • VermaModule.hwv R 𝕧 Λ'))}

lemma degTensorSpan_mono {d d' : ℕ} (h : d ≤ d') :
    degTensorSpan (R := R) Λ Λ' d ≤ degTensorSpan Λ Λ' d' :=
  Submodule.span_mono fun _ ⟨a, ha, w, hw, e⟩ ↦ ⟨a, ha, w, lt_of_lt_of_le hw h, e⟩

lemma smul_tmul_mem_degTensorSpan {c : 𝕂} (hc : IsLaurent c) {a : VermaModule R 𝕧 Λ}
    (ha : a ∈ vermaLattice R Λ) {w : List (I × ℕ)} {d : ℕ} (hw : degW w < d) :
    c • mkT (tw a ⊗ₜ[𝕂] (fPow R w • VermaModule.hwv R 𝕧 Λ')) ∈ degTensorSpan Λ Λ' d := by
  rw [← LinearEquiv.map_smul, smul_tmul', ← LinearEquiv.map_smul]
  exact Submodule.subset_span ⟨c • a, laurent_smul_mem_laurentSpan hc ha, w, hw, rfl⟩

lemma qDivPow_F_smul_mem_degTensorSpan (i : I) (n : ℕ) {d : ℕ} {z : VT}
    (hz : z ∈ degTensorSpan Λ Λ' d) :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • z ∈ degTensorSpan Λ Λ' (d + n) := by
  have h : degTensorSpan Λ Λ' d ≤ (degTensorSpan Λ Λ' (d + n)).comap
      ((DistribSMul.toLinearMap 𝕂 VT (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i))).restrictScalars ℤ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      DistribSMul.toLinearMap_apply]
    rw [TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _
      (fPow_smul_hwv_mem_weightSpace Λ' w)]
    refine sum_mem fun p hp ↦ ?_
    rw [qDivPow_F_smul_toTwist, ← mul_smul, fPow_cons']
    refine smul_tmul_mem_degTensorSpan (isLaurent_vd_zpow _ _)
      (qDivPow_E_smul_mem_vermaLattice _ _ ha) ?_
    rw [degW_cons]
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    omega
  exact h hz

lemma qDivPow_F_smul_tmul_sub_mem (i : I) (n : ℕ) {a : VermaModule R 𝕧 Λ}
    (ha : a ∈ vermaLattice R Λ) (w : List (I × ℕ)) :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • mkT (tw a ⊗ₜ[𝕂] (fPow R w • VermaModule.hwv R 𝕧 Λ')) -
      mkT (tw a ⊗ₜ[𝕂] (fPow R ((i, n) :: w) • VermaModule.hwv R 𝕧 Λ')) ∈
      degTensorSpan Λ Λ' (degW w + n) := by
  have h0 : ((0, n) : ℕ × ℕ) ∈ antidiagonal n :=
    Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add n)
  rw [TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _
    (fPow_smul_hwv_mem_weightSpace Λ' w), ← Finset.add_sum_erase _ _ h0]
  simp only [Nat.cast_zero, zero_mul, sub_self, zpow_zero, one_smul, qDivPow_zero']
  rw [fPow_cons, mul_smul, add_sub_cancel_left]
  refine sum_mem fun p hp ↦ ?_
  obtain ⟨hp0, hp⟩ := Finset.mem_erase.1 hp
  rw [qDivPow_F_smul_toTwist, ← mul_smul, fPow_cons']
  refine smul_tmul_mem_degTensorSpan (isLaurent_vd_zpow _ _)
    (qDivPow_E_smul_mem_vermaLattice _ _ ha) ?_
  rw [degW_cons]
  have h1 := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have h2 : p.1 ≠ 0 := fun h ↦ hp0 (Prod.ext h (by simp only; omega))
  omega

/-- `F_w (a ⊗ η) = a ⊗ F_w η` modulo the span of the `a' ⊗ F_{w''} η` with `w''` of smaller
degree. -/
lemma fPow_smul_tmul_hwv_sub_mem {a : VermaModule R 𝕧 Λ} (ha : a ∈ vermaLattice R Λ)
    (w : List (I × ℕ)) :
    fPow R w • mkT (tw a ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ') -
      mkT (tw a ⊗ₜ[𝕂] (fPow R w • VermaModule.hwv R 𝕧 Λ')) ∈ degTensorSpan Λ Λ' (degW w) := by
  induction w with
  | nil => rw [fPow_nil, one_smul, one_smul, sub_self]; exact zero_mem _
  | cons p w ih =>
    obtain ⟨i, n⟩ := p
    have e : fPow R ((i, n) :: w) • mkT (tw a ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ') -
        mkT (tw a ⊗ₜ[𝕂] (fPow R ((i, n) :: w) • VermaModule.hwv R 𝕧 Λ')) =
        qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • (fPow R w • mkT (tw a ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ') -
          mkT (tw a ⊗ₜ[𝕂] (fPow R w • VermaModule.hwv R 𝕧 Λ'))) +
        (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) •
          mkT (tw a ⊗ₜ[𝕂] (fPow R w • VermaModule.hwv R 𝕧 Λ')) -
          mkT (tw a ⊗ₜ[𝕂] (fPow R ((i, n) :: w) • VermaModule.hwv R 𝕧 Λ'))) := by
      rw [smul_sub, fPow_cons, mul_smul]
      abel
    rw [e, degW_cons]
    exact add_mem (qDivPow_F_smul_mem_degTensorSpan i n ih) (qDivPow_F_smul_tmul_sub_mem i n ha w)

lemma degTensorSpan_le_fePowImage (d : ℕ) :
    degTensorSpan (R := R) Λ Λ' d ≤ fePowImage R Λ Λ' := by
  induction d with
  | zero => exact Submodule.span_le.2 fun _ ⟨_, _, _, hw, _⟩ ↦ absurd hw (Nat.not_lt_zero _)
  | succ d ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, w', hw', rfl⟩
    have key : vermaLattice R Λ ≤ (fePowImage R Λ Λ').comap
        (((TensorModule.mk _ _).toLinearMap ∘ₗ
          (TensorProduct.mk 𝕂 _ _).flip (fPow R w' • VermaModule.hwv R 𝕧 Λ') ∘ₗ
            (tw).toLinearMap).restrictScalars ℤ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, _, ⟨w, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.flip_apply,
        TensorProduct.mk_apply, LinearEquiv.map_smul, ← smul_tmul']
      refine zpow_smul_mem_fePowImage k ?_
      have hg := fPow_smul_tmul_hwv_sub_mem (Λ' := Λ')
        (fPow_smul_hwv_mem_vermaLattice (R := R) Λ w) w'
      rw [← ePow_smul_vermaTensorHwv, ← mul_smul] at hg
      have hT := ih (degTensorSpan_mono (Nat.lt_succ_iff.1 hw') hg)
      have := sub_mem (fPow_mul_ePow_smul_mem_fePowImage w' w) hT
      rwa [sub_sub_cancel] at this
    exact key ha

lemma vermaTensorLattice_le_fePowImage :
    vermaTensorLattice R Λ Λ' ≤ fePowImage R Λ Λ' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, _, ⟨w, w', rfl⟩, rfl⟩
  exact degTensorSpan_le_fePowImage (degW w' + 1) (smul_tmul_mem_degTensorSpan (isLaurent_zpow k)
    (fPow_smul_hwv_mem_vermaLattice Λ w) (Nat.lt_succ_self _))

end Reverse

/-! ### [Lus] 23.3.2 (a) -/

/-- **[Lus] 23.3.2 (a)**: for `u ∈ U` and `ζ = Λ' - Λ`, `u 1_ζ ∈ 𝒜U̇` if and only if
`u (ξ ⊗ η)` lies in the `𝒜`-span of the `a ⊗ b`, `a ∈ 𝒜M_Λ`, `b ∈ 𝒜M_{Λ'}`. With
`smul_vermaTensorHwv_eq_zero_iff` and `surjective_smul_vermaTensorHwv` ([Lus] 23.3.1 (c)), the map
`u 1_ζ ↦ u (ξ ⊗ η)` restricts to a bijection from `𝒜U̇ 1_ζ` onto this `𝒜`-span
(`vermaTensorEquiv_mem_iff`). Lusztig works over `ℚ(v)` with `𝒜 = ℤ[v, v⁻¹]`, as here. -/
theorem leftActOne_mem_aForm_iff (Λ Λ' : Y →+ ℤ) (u : QuantumGroup R 𝕧) :
    leftActOne R ratFunc_X_not_root (Λ' - Λ) u ∈ aForm R ↔
      u • vermaTensorHwv R 𝕧 Λ Λ' ∈ vermaTensorLattice R Λ Λ' := by
  refine ⟨smul_vermaTensorHwv_mem_of_mem_aForm, fun h ↦ ?_⟩
  obtain ⟨u', hu', e⟩ := mem_fePowImage.1 (vermaTensorLattice_le_fePowImage h)
  have h0 : (u - u') • vermaTensorHwv R 𝕧 Λ Λ' = 0 := by rw [sub_smul, e, sub_self]
  rw [smul_vermaTensorHwv_eq_zero_iff ratFunc_X_not_root, map_sub, sub_eq_zero] at h0
  rw [h0]
  exact leftActOne_mem_aForm_of_mem_fePowSpan _ hu'

/-- **[Lus] 23.3.2 (a)**: the isomorphism `U̇ 1_ζ ≃ ʷM_Λ ⊗ M_{Λ'}` of [Lus] 23.3.1 (c)
(`vermaTensorEquiv`) maps `𝒜U̇ 1_ζ = 𝒜U̇ ∩ U̇ 1_ζ` onto the `𝒜`-span of the `a ⊗ b`,
`a ∈ 𝒜M_Λ`, `b ∈ 𝒜M_{Λ'}`. -/
theorem vermaTensorEquiv_mem_iff (Λ Λ' : Y →+ ℤ)
    (x : LinearMap.range (leftActOne R ratFunc_X_not_root (Λ' - Λ))) :
    vermaTensorEquiv ratFunc_X_not_root Λ Λ' x ∈ vermaTensorLattice R Λ Λ' ↔
      (x : Modified R 𝕧) ∈ aForm R := by
  obtain ⟨_, u, rfl⟩ := x
  rw [vermaTensorEquiv_apply, leftActOne_mem_aForm_iff]

end Modified

end LieLean.QuantumGroup
