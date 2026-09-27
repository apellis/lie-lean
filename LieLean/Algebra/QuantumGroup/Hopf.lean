/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import LieLean.Algebra.QuantumGroup.Basic

/-!
# The bialgebra structure of `U_q(𝔤)`

Following [Lus] 3.1.4 (check) (see also [Jan] 4.8 (check)), `U = U_q(𝔤)` has a unique algebra
homomorphism `Δ : U → U ⊗ U` with
`Δ(Eᵢ) = Eᵢ ⊗ 1 + K̃ᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ K̃₋ᵢ + 1 ⊗ Fᵢ`, `Δ(K_μ) = K_μ ⊗ K_μ`,
and an algebra homomorphism `ε : U → k` with `ε(Eᵢ) = ε(Fᵢ) = 0`, `ε(K_μ) = 1`. Together they
make `U` a bialgebra (`QuantumGroup.instBialgebra`, for `v ≠ 0`).

The only nontrivial point in the construction of `Δ` is that it respects the quantum Serre
relations; this follows from the additivity of Serre elements `QuantumGroup.qSerre_add`: for
`x = Eᵢ ⊗ 1`, `y = K̃ᵢ ⊗ Eᵢ` we have `y x = vᵢ² x y`, and `Eⱼ ⊗ 1`, `K̃ⱼ ⊗ Eⱼ` are
eigenvectors for commutation with `y`, `x` with eigenvalues `vᵢ^{aᵢⱼ}`, `vᵢ^{-aᵢⱼ}` (using the
symmetry `dᵢ aᵢⱼ = dⱼ aⱼᵢ`). This argument is our own (cf. [Jan] Lemma 4.10 (check)).

## Main definitions

* `QuantumGroup.comul`: `Δ : U → U ⊗ U`.
* `QuantumGroup.counit`: `ε : U → k`.
* `QuantumGroup.instBialgebra`: the bialgebra structure.

## Main results

* `QuantumGroup.comul_E`, `comul_F`, `comul_K`, `counit_E`, `counit_F`, `counit_K`.
* `QuantumGroup.comul_coassoc`, `QuantumGroup.counit_rTensor_comul`,
  `QuantumGroup.counit_lTensor_comul`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 4.
-/

noncomputable section

open TensorProduct

namespace QuantumGroup

variable {k I : Type*} [Field k]

section TensorSerre

variable {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

/-- Serre elements of pure tensors with commuting left factors. -/
lemma qSerre_tmul_left (ν : k) (M : ℕ) {g h : A} (hgh : Commute g h) (a b : B) :
    qSerre ν M (g ⊗ₜ[k] a) (h ⊗ₜ[k] b) = (g ^ M * h) ⊗ₜ qSerre ν M a b := by
  simp only [qSerre, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  rw [mul_assoc, ← (hgh.pow_left r).eq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]

/-- Serre elements of pure tensors with commuting right factors. -/
lemma qSerre_tmul_right (ν : k) (M : ℕ) {g h : B} (hgh : Commute g h) (a b : A) :
    qSerre ν M (a ⊗ₜ[k] g) (b ⊗ₜ[k] h) = qSerre ν M a b ⊗ₜ (g ^ M * h) := by
  simp only [qSerre, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.sum_tmul, TensorProduct.smul_tmul']
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  rw [mul_assoc (g ^ (M - r)), ← (hgh.pow_left r).eq, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hr]

end TensorSerre

variable {Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : CartanDatum I}
  (R : D.RootDatum Y) (v : k)

omit [DecidableEq I] in
lemma root_ktilde (i j : I) : R.root j (ktilde R i) = D.d i * D.cartanMatrix i j := by
  simp [ktilde, R.root_coroot]

omit [DecidableEq I] in
lemma root_ktilde_comm (i j : I) : R.root j (ktilde R i) = R.root i (ktilde R j) := by
  rw [root_ktilde, root_ktilde, D.d_mul_cartanMatrix_comm]

variable {R v}

lemma E_mul_K (hv : v ≠ 0) (μ : Y) (i : I) :
    E R v i * K R v μ = v ^ (-R.root i μ) • (K R v μ * E R v i) := by
  rw [K_mul_E, smul_smul, ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]

lemma F_mul_K (hv : v ≠ 0) (μ : Y) (i : I) :
    F R v i * K R v μ = v ^ R.root i μ • (K R v μ * F R v i) := by
  rw [K_mul_F, smul_smul, ← zpow_add₀ hv, add_neg_cancel, zpow_zero, one_smul]

variable (R v)

/-- The group-like elements `K_μ ⊗ K_μ` of `U ⊗ U`. -/
def KHom₂ : Multiplicative Y →* QuantumGroup R v ⊗[k] QuantumGroup R v where
  toFun μ := K R v μ.toAdd ⊗ₜ K R v μ.toAdd
  map_one' := by simp [Algebra.TensorProduct.one_def]
  map_mul' μ ν := by simp [Algebra.TensorProduct.tmul_mul_tmul, K_add]

/-- The images `Δ(Eᵢ) = Eᵢ ⊗ 1 + K̃ᵢ ⊗ Eᵢ`. -/
def comulE (i : I) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  E R v i ⊗ₜ 1 + Kt R v i ⊗ₜ E R v i

/-- The images `Δ(Fᵢ) = Fᵢ ⊗ K̃₋ᵢ + 1 ⊗ Fᵢ`. -/
def comulF (i : I) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  F R v i ⊗ₜ K R v (-ktilde R i) + 1 ⊗ₜ F R v i

variable {R v}

omit [DecidableEq I] in
lemma zpow_root_ktilde_eq (hv : v ≠ 0) {i j : I} (hij : i ≠ j) {m : ℕ}
    (hm : (1 - D.cartanMatrix i j).toNat = m + 1) :
    v ^ R.root j (ktilde R i) = (v ^ D.d i)⁻¹ ^ m := by
  have hA := (D.isGeneralizedCartan_cartanMatrix).offDiag_nonpos i j hij
  have ha : D.cartanMatrix i j = -(m : ℤ) := by omega
  have := hv
  rw [root_ktilde, ha, show (D.d i : ℤ) * -(m : ℤ) = -((D.d i * m : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, pow_mul, inv_pow]

omit [DecidableEq I] in
lemma zpow_root_ktilde_self (i : I) : v ^ R.root i (ktilde R i) = (v ^ D.d i) ^ 2 := by
  rw [root_ktilde, D.cartanMatrix_self, show (D.d i : ℤ) * 2 = ((D.d i * 2 : ℕ) : ℤ) by
    push_cast; ring, zpow_natCast, pow_mul]

theorem comul_relations (hv : v ≠ 0) :
    Relations R v (comulE R v) (comulF R v) (KHom₂ R v) where
  K_mul_E μ i := by
    simp only [KHom₂, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, comulE, mul_add, add_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, K_mul_E, smul_add]
    rw [K_comm, TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  K_mul_F μ i := by
    simp only [KHom₂, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, comulF, mul_add, add_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, K_mul_F, smul_add]
    rw [K_comm R v μ (-ktilde R i), TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  E_mul_F i j := by
    have hcross : (Kt R v i * F R v j) ⊗ₜ (E R v i * K R v (-ktilde R j)) =
        (F R v j * Kt R v i) ⊗ₜ[k] (K R v (-ktilde R j) * E R v i) := by
      rw [K_mul_F, E_mul_K hv, ← smul_tmul', tmul_smul, smul_smul, ← zpow_add₀ hv, map_neg,
        neg_neg, root_ktilde_comm R i j, neg_add_cancel, zpow_zero, one_smul]
    have hdiff : comulE R v i * comulF R v j - comulF R v j * comulE R v i =
        (E R v i * F R v j - F R v j * E R v i) ⊗ₜ K R v (-ktilde R j) +
          Kt R v i ⊗ₜ (E R v i * F R v j - F R v j * E R v i) := by
      simp only [comulE, comulF, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, sub_tmul, tmul_sub, hcross]
      abel
    rw [hdiff, E_mul_F_sub]
    split_ifs with h
    · subst h
      rw [← smul_tmul', tmul_smul, ← smul_add]
      congr 1
      simp only [KHom₂, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Kt, sub_tmul, tmul_sub]
      abel
    · simp
  serre_E i j hij := by
    have hA := (D.isGeneralizedCartan_cartanMatrix).offDiag_nonpos i j hij
    set m := (-D.cartanMatrix i j).toNat
    have hM : (1 - D.cartanMatrix i j).toNat = m + 1 := by omega
    have hν : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
    rw [hM]
    have hwu : Kt R v i ⊗ₜ[k] E R v i * E R v i ⊗ₜ[k] (1 : QuantumGroup R v) =
        (v ^ D.d i) ^ 2 • (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) * Kt R v i ⊗ₜ[k] E R v i) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Kt, K_mul_E,
        zpow_root_ktilde_self, smul_tmul']
    have hb : Kt R v i ⊗ₜ[k] E R v i * E R v j ⊗ₜ[k] (1 : QuantumGroup R v) =
        (v ^ D.d i)⁻¹ ^ m • (E R v j ⊗ₜ[k] (1 : QuantumGroup R v) * Kt R v i ⊗ₜ[k] E R v i) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Kt, K_mul_E,
        zpow_root_ktilde_eq hv hij hM, smul_tmul']
    have hb' : E R v i ⊗ₜ[k] (1 : QuantumGroup R v) * Kt R v j ⊗ₜ[k] E R v j =
        (v ^ D.d i) ^ m • (Kt R v j ⊗ₜ[k] E R v j * E R v i ⊗ₜ[k] (1 : QuantumGroup R v)) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Kt, K_mul_E,
        root_ktilde_comm R j i, zpow_root_ktilde_eq hv hij hM, smul_tmul', smul_smul, ← mul_pow,
        mul_inv_cancel₀ hν, one_pow, one_smul]
    rw [comulE, comulE, qSerre_add hν hwu hb hb', qSerre_tmul_right _ _ (Commute.one_left 1),
      qSerre_tmul_left _ _ (K_comm R v _ _), ← hM, serre_E R v hij, zero_tmul, tmul_zero,
      add_zero]
  serre_F i j hij := by
    have hA := (D.isGeneralizedCartan_cartanMatrix).offDiag_nonpos i j hij
    set m := (-D.cartanMatrix i j).toNat
    have hM : (1 - D.cartanMatrix i j).toNat = m + 1 := by omega
    have hν : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
    rw [hM]
    have hwu : F R v i ⊗ₜ[k] K R v (-ktilde R i) * (1 : QuantumGroup R v) ⊗ₜ[k] F R v i =
        (v ^ D.d i) ^ 2 •
          ((1 : QuantumGroup R v) ⊗ₜ[k] F R v i * F R v i ⊗ₜ[k] K R v (-ktilde R i)) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, K_mul_F, map_neg,
        neg_neg, zpow_root_ktilde_self, tmul_smul]
    have hb : F R v i ⊗ₜ[k] K R v (-ktilde R i) * (1 : QuantumGroup R v) ⊗ₜ[k] F R v j =
        (v ^ D.d i)⁻¹ ^ m •
          ((1 : QuantumGroup R v) ⊗ₜ[k] F R v j * F R v i ⊗ₜ[k] K R v (-ktilde R i)) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, K_mul_F, map_neg,
        neg_neg, zpow_root_ktilde_eq hv hij hM, tmul_smul]
    have hb' : (1 : QuantumGroup R v) ⊗ₜ[k] F R v i * F R v j ⊗ₜ[k] K R v (-ktilde R j) =
        (v ^ D.d i) ^ m •
          (F R v j ⊗ₜ[k] K R v (-ktilde R j) * (1 : QuantumGroup R v) ⊗ₜ[k] F R v i) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, K_mul_F, map_neg,
        neg_neg, root_ktilde_comm R j i, zpow_root_ktilde_eq hv hij hM, tmul_smul, smul_smul,
        ← mul_pow, mul_inv_cancel₀ hν, one_pow, one_smul]
    rw [comulF, comulF, add_comm (F R v i ⊗ₜ _), add_comm (F R v j ⊗ₜ _),
      qSerre_add hν hwu hb hb', qSerre_tmul_left _ _ (Commute.one_left 1),
      qSerre_tmul_right _ _ (K_comm R v _ _), ← hM, serre_F R v hij, zero_tmul, tmul_zero,
      add_zero]

variable (R v) [NeZero v]

/-- The comultiplication `Δ : U → U ⊗ U` ([Lus] 3.1.4 (check)). -/
def comul : QuantumGroup R v →ₐ[k] QuantumGroup R v ⊗[k] QuantumGroup R v :=
  lift (comul_relations (NeZero.ne v))

@[simp] theorem comul_E (i : I) : comul R v (E R v i) = E R v i ⊗ₜ 1 + Kt R v i ⊗ₜ E R v i := by
  simp [comul, comulE]

@[simp] theorem comul_F (i : I) :
    comul R v (F R v i) = F R v i ⊗ₜ K R v (-ktilde R i) + 1 ⊗ₜ F R v i := by
  simp [comul, comulF]

@[simp] theorem comul_K (μ : Y) : comul R v (K R v μ) = K R v μ ⊗ₜ K R v μ := by
  simp [comul, KHom₂]

omit [NeZero v] in
theorem counit_relations :
    Relations R v (0 : I → k) (0 : I → k) (1 : Multiplicative Y →* k) where
  K_mul_E _ _ := by simp
  K_mul_F _ _ := by simp
  E_mul_F i j := by split_ifs <;> simp
  serre_E _ _ _ := by simp
  serre_F _ _ _ := by simp

omit [NeZero v] in
/-- The counit `ε : U → k`, `ε(Eᵢ) = ε(Fᵢ) = 0`, `ε(K_μ) = 1` ([Lus] 3.1.4 (check)). -/
def counit : QuantumGroup R v →ₐ[k] k := lift (counit_relations R v)

omit [NeZero v] in
@[simp] theorem counit_E (i : I) : counit R v (E R v i) = 0 := by simp [counit]

omit [NeZero v] in
@[simp] theorem counit_F (i : I) : counit R v (F R v i) = 0 := by simp [counit]

omit [NeZero v] in
@[simp] theorem counit_K (μ : Y) : counit R v (K R v μ) = 1 := by simp [counit]

/-- Coassociativity of `Δ`. -/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc k k k (QuantumGroup R v) (QuantumGroup R v)
      (QuantumGroup R v)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R v) (.id k _)).comp (comul R v)) =
      (Algebra.TensorProduct.map (.id k _) (comul R v)).comp (comul R v) := by
  ext i <;> simp [add_tmul, tmul_add, Algebra.TensorProduct.one_def, add_assoc]

/-- The counit law `(ε ⊗ 1) ∘ Δ = id`. -/
theorem counit_rTensor_comul :
    (Algebra.TensorProduct.map (counit R v) (.id k _)).comp (comul R v) =
      (Algebra.TensorProduct.lid k (QuantumGroup R v)).symm := by
  ext i <;> simp

/-- The counit law `(1 ⊗ ε) ∘ Δ = id`. -/
theorem counit_lTensor_comul :
    (Algebra.TensorProduct.map (.id k _) (counit R v)).comp (comul R v) =
      (Algebra.TensorProduct.rid k k (QuantumGroup R v)).symm := by
  ext i <;> simp

/-- `U_q(𝔤)` is a bialgebra ([Lus] 3.1.4 (check)). -/
instance instBialgebra : Bialgebra k (QuantumGroup R v) :=
  Bialgebra.ofAlgHom (comul R v) (counit R v) (comul_coassoc R v) (counit_rTensor_comul R v)
    (counit_lTensor_comul R v)

end QuantumGroup
