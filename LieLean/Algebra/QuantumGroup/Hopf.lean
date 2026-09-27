/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import LieLean.Algebra.QuantumGroup.Basic

/-!
# The Hopf algebra structure of `U_q(𝔤)`

Following [Lus] 3.1.4 (check) (see also [Jan] 4.8 (check)), `U = U_q(𝔤)` has a unique algebra
homomorphism `Δ : U → U ⊗ U` with
`Δ(Eᵢ) = Eᵢ ⊗ 1 + K̃ᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ K̃₋ᵢ + 1 ⊗ Fᵢ`, `Δ(K_μ) = K_μ ⊗ K_μ`,
and an algebra homomorphism `ε : U → k` with `ε(Eᵢ) = ε(Fᵢ) = 0`, `ε(K_μ) = 1`. Together they
make `U` a bialgebra (`QuantumGroup.instBialgebra`, for `v ≠ 0`). The antipode is the
anti-automorphism `S(Eᵢ) = -K̃₋ᵢ Eᵢ`, `S(Fᵢ) = -Fᵢ K̃ᵢ`, `S(K_μ) = K_{-μ}` ([Lus] 3.1.12 (check)),
making `U` a Hopf algebra (`QuantumGroup.instHopfAlgebra`).

That `S` respects the Serre relations follows from `QuantumGroup.qSerre_mul_mul` (Serre elements
of `gᵢ Eᵢ` with `q`-commuting `gᵢ`) and `QuantumGroup.qSerre_op`; the antipode axioms are
checked on generators, using that the set where they hold is closed under products because `S`
is an anti-homomorphism (`mul'_rTensor_antipode_mul`).

The only nontrivial point in the construction of `Δ` is that it respects the quantum Serre
relations; this follows from the additivity of Serre elements `QuantumGroup.qSerre_add`: for
`x = Eᵢ ⊗ 1`, `y = K̃ᵢ ⊗ Eᵢ` we have `y x = vᵢ² x y`, and `Eⱼ ⊗ 1`, `K̃ⱼ ⊗ Eⱼ` are
eigenvectors for commutation with `y`, `x` with eigenvalues `vᵢ^{aᵢⱼ}`, `vᵢ^{-aᵢⱼ}` (using the
symmetry `dᵢ aᵢⱼ = dⱼ aⱼᵢ`). This argument is our own (cf. [Jan] Lemma 4.10 (check)).

## Main definitions

* `QuantumGroup.comul`: `Δ : U → U ⊗ U`.
* `QuantumGroup.counit`: `ε : U → k`.
* `QuantumGroup.instBialgebra`: the bialgebra structure.
* `QuantumGroup.antipodeOp`, `QuantumGroup.antipode`: the antipode `S`.
* `QuantumGroup.instHopfAlgebra`: the Hopf algebra structure.

## Main results

* `QuantumGroup.comul_E`, `comul_F`, `comul_K`, `counit_E`, `counit_F`, `counit_K`.
* `QuantumGroup.comul_coassoc`, `QuantumGroup.counit_rTensor_comul`,
  `QuantumGroup.counit_lTensor_comul`.
* `QuantumGroup.antipode_E`, `antipode_F`, `antipode_K`, `antipode_mul`,
  `mul'_rTensor_antipode_comul`, `mul'_lTensor_antipode_comul`.

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

/-! ### The antipode -/

section Antipode

open MulOpposite

omit [NeZero v] in
/-- The images `S(K_μ) = K_{-μ}` of the antipode, in `Uᵐᵒᵖ`. -/
def antipodeK : Multiplicative Y →* (QuantumGroup R v)ᵐᵒᵖ where
  toFun μ := op (K R v (-μ.toAdd))
  map_one' := by simp
  map_mul' μ ν := by
    apply unop_injective
    simp only [toAdd_mul, unop_mul, unop_op, K_add, neg_add, add_comm]

variable {R v}

omit [NeZero v] in
theorem antipode_relations (hv : v ≠ 0) :
    Relations R v (fun i ↦ op (-(K R v (-ktilde R i) * E R v i)))
      (fun i ↦ op (-(F R v i * Kt R v i))) (antipodeK R v) where
  K_mul_E μ i := by
    apply unop_injective
    simp only [antipodeK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, unop_mul, unop_op,
      unop_smul, neg_mul, mul_neg, smul_neg, neg_inj]
    rw [mul_assoc, E_mul_K hv, map_neg, neg_neg, mul_smul_comm, ← mul_assoc, ← mul_assoc,
      K_comm]
  K_mul_F μ i := by
    apply unop_injective
    simp only [antipodeK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, unop_mul, unop_op,
      unop_smul, neg_mul, mul_neg, smul_neg, neg_inj]
    rw [← mul_assoc, K_mul_F, map_neg, neg_neg, smul_mul_assoc, smul_smul, ← zpow_add₀ hv,
      neg_add_cancel, zpow_zero, one_smul, mul_assoc, mul_assoc, K_comm]
  E_mul_F i j := by
    apply unop_injective
    simp only [antipodeK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, unop_mul, unop_op,
      unop_sub, neg_mul, mul_neg, neg_neg]
    -- `b a - a b` with `a = K̃₋ᵢ Eᵢ`, `b = Fⱼ K̃ⱼ`
    have hEF := E_mul_F_sub R v i j
    have h1 : F R v j * Kt R v j * (K R v (-ktilde R i) * E R v i) =
        v ^ (R.root i (ktilde R j) - R.root i (ktilde R i)) •
          (F R v j * E R v i * K R v (ktilde R j - ktilde R i)) := by
      rw [mul_assoc, ← mul_assoc (Kt R v j), K_add, K_mul_E, map_add, map_neg, ← sub_eq_add_neg,
        ← sub_eq_add_neg, mul_smul_comm, ← mul_assoc]
    have h2 : K R v (-ktilde R i) * (F R v j * E R v i) * Kt R v j =
        v ^ (R.root i (ktilde R j) - R.root i (ktilde R i)) •
          (F R v j * E R v i * K R v (ktilde R j - ktilde R i)) := by
      rw [← mul_assoc, K_mul_F, smul_mul_assoc, mul_assoc, K_mul_E, mul_smul_comm, smul_smul,
        smul_mul_assoc, mul_assoc, mul_assoc, K_add, map_neg, map_neg, neg_neg, ← mul_assoc,
        ← zpow_add₀ hv, root_ktilde_comm R i j, sub_eq_add_neg (ktilde R j), add_comm (-ktilde R i),
        ← sub_eq_add_neg]
    have h3 : K R v (-ktilde R i) * E R v i * (F R v j * Kt R v j) =
        K R v (-ktilde R i) * (F R v j * E R v i) * Kt R v j +
          K R v (-ktilde R i) * (E R v i * F R v j - F R v j * E R v i) * Kt R v j := by
      simp only [mul_sub, sub_mul, mul_assoc]; abel
    rw [h3, h1, h2, hEF, sub_add_cancel_left]
    split_ifs with h
    · subst h
      have e1 : K R v (-ktilde R i) * Kt R v i * Kt R v i = Kt R v i := by
        rw [K_add, K_add]; congr 1; abel
      have e2 : K R v (-ktilde R i) * K R v (-ktilde R i) * Kt R v i = K R v (-ktilde R i) := by
        rw [K_add, K_add]; congr 1; abel
      simp only [unop_smul, unop_sub, unop_op]
      rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, e1, e2, ← smul_neg, neg_sub]
    · simp
  serre_E i j hij := by
    rw [qSerre_op, ← neg_mul, ← neg_mul]
    rw [qSerre_mul_mul (t := v ^ R.root i (-ktilde R i)) (s := v ^ R.root i (ktilde R j))
      (zpow_ne_zero _ hv), serre_E R v hij, mul_zero, smul_zero, op_zero, smul_zero]
    · rw [neg_mul, mul_neg, K_mul_E, smul_neg]
    · rw [neg_mul, mul_neg, E_mul_K hv, smul_neg, map_neg, neg_neg]
    · rw [neg_mul, mul_neg, E_mul_K hv, smul_neg, map_neg, neg_neg, root_ktilde_comm R i j]
    · rw [neg_mul_neg, neg_mul_neg, K_comm]
  serre_F i j hij := by
    have hop : ∀ l, op (-(F R v l * Kt R v l)) = op (-Kt R v l) * op (F R v l) := fun l ↦ by
      rw [← op_mul, mul_neg]
    rw [hop, hop, qSerre_mul_mul (t := v ^ R.root i (ktilde R i))
      (s := v ^ (-R.root i (ktilde R j))) (zpow_ne_zero _ hv), qSerre_op, serre_F R v hij,
      op_zero, smul_zero, mul_zero, smul_zero]
    · apply unop_injective
      simp only [unop_mul, unop_op, unop_smul, neg_mul, mul_neg, smul_neg, neg_inj]
      rw [F_mul_K hv]
    · apply unop_injective
      simp only [unop_mul, unop_op, unop_smul, neg_mul, mul_neg, smul_neg, neg_inj]
      rw [K_mul_F]
    · apply unop_injective
      simp only [unop_mul, unop_op, unop_smul, neg_mul, mul_neg, smul_neg, neg_inj]
      rw [K_mul_F, root_ktilde_comm R j i]
    · rw [← op_mul, ← op_mul, neg_mul_neg, neg_mul_neg, K_comm]

variable (R v)

/-- The antipode `S : U → Uᵐᵒᵖ`, `S(Eᵢ) = -K̃₋ᵢ Eᵢ`, `S(Fᵢ) = -Fᵢ K̃ᵢ`, `S(K_μ) = K_{-μ}`
([Lus] 3.1.12 (check)), as an algebra homomorphism to the opposite algebra. -/
def antipodeOp : QuantumGroup R v →ₐ[k] (QuantumGroup R v)ᵐᵒᵖ :=
  lift (antipode_relations (NeZero.ne v))

/-- The antipode `S : U → U` as a linear map. -/
def antipode : QuantumGroup R v →ₗ[k] QuantumGroup R v :=
  (opLinearEquiv k).symm.toLinearMap ∘ₗ (antipodeOp R v).toLinearMap

lemma antipode_apply (x : QuantumGroup R v) : antipode R v x = unop (antipodeOp R v x) := rfl

@[simp] theorem antipode_E (i : I) :
    antipode R v (E R v i) = -(K R v (-ktilde R i) * E R v i) := by
  simp [antipode_apply, antipodeOp]

@[simp] theorem antipode_F (i : I) : antipode R v (F R v i) = -(F R v i * Kt R v i) := by
  simp [antipode_apply, antipodeOp]

@[simp] theorem antipode_K (μ : Y) : antipode R v (K R v μ) = K R v (-μ) := by
  simp [antipode_apply, antipodeOp, antipodeK]

@[simp] theorem antipode_one : antipode R v 1 = 1 := by simp [antipode_apply]

@[simp] theorem antipode_algebraMap (c : k) :
    antipode R v (algebraMap k _ c) = algebraMap k _ c := by
  simp [antipode_apply]

/-- The antipode is an anti-homomorphism. -/
theorem antipode_mul (x y : QuantumGroup R v) :
    antipode R v (x * y) = antipode R v y * antipode R v x := by
  simp [antipode_apply]

/-- The map `Y ↦ (z ↦ Σ S(y) z y')` for `Y = Σ y ⊗ y'`. -/
def antipodeConjLeft :
    QuantumGroup R v ⊗[k] QuantumGroup R v →ₗ[k] Module.End k (QuantumGroup R v) :=
  TensorProduct.lift (LinearMap.mk₂ k
    (fun y y' ↦ LinearMap.mulLeft k (antipode R v y) ∘ₗ LinearMap.mulRight k y')
    (fun y₁ y₂ y' ↦ by ext z; simp [add_mul])
    (fun c y y' ↦ by ext z; simp)
    (fun y y₁ y₂ ↦ by ext z; simp [mul_add])
    (fun c y y' ↦ by ext z; simp))

/-- The map `X ↦ (z ↦ Σ x z S(x'))` for `X = Σ x ⊗ x'`. -/
def antipodeConjRight :
    QuantumGroup R v ⊗[k] QuantumGroup R v →ₗ[k] Module.End k (QuantumGroup R v) :=
  TensorProduct.lift (LinearMap.mk₂ k
    (fun x x' ↦ LinearMap.mulLeft k x ∘ₗ LinearMap.mulRight k (antipode R v x'))
    (fun x₁ x₂ x' ↦ by ext z; simp [add_mul])
    (fun c x x' ↦ by ext z; simp)
    (fun x x₁ x₂ ↦ by ext z; simp [mul_add])
    (fun c x x' ↦ by ext z; simp))

lemma mul'_rTensor_antipode_mul (X Y : QuantumGroup R v ⊗[k] QuantumGroup R v) :
    LinearMap.mul' k _ ((antipode R v).rTensor _ (X * Y)) =
      antipodeConjLeft R v Y (LinearMap.mul' k _ ((antipode R v).rTensor _ X)) := by
  induction X with
  | tmul x x' =>
    induction Y with
    | tmul y y' =>
      simp [antipodeConjLeft, Algebra.TensorProduct.tmul_mul_tmul, antipode_mul, mul_assoc]
    | add Y Y' hY hY' => simp only [mul_add, map_add, LinearMap.add_apply, hY, hY']
  | add X X' hX hX' => simp only [add_mul, map_add, hX, hX']

lemma mul'_lTensor_antipode_mul (X Y : QuantumGroup R v ⊗[k] QuantumGroup R v) :
    LinearMap.mul' k _ ((antipode R v).lTensor _ (X * Y)) =
      antipodeConjRight R v X (LinearMap.mul' k _ ((antipode R v).lTensor _ Y)) := by
  induction X with
  | tmul x x' =>
    induction Y with
    | tmul y y' =>
      simp [antipodeConjRight, Algebra.TensorProduct.tmul_mul_tmul, antipode_mul, mul_assoc]
    | add Y Y' hY hY' => simp only [mul_add, map_add, hY, hY']
  | add X X' hX hX' => simp only [add_mul, map_add, LinearMap.add_apply, hX, hX']

lemma antipodeConjLeft_one (Y : QuantumGroup R v ⊗[k] QuantumGroup R v) :
    antipodeConjLeft R v Y 1 = LinearMap.mul' k _ ((antipode R v).rTensor _ Y) := by
  induction Y with
  | tmul y y' => simp [antipodeConjLeft]
  | add Y Y' hY hY' => simp only [map_add, LinearMap.add_apply, hY, hY']

lemma antipodeConjRight_one (X : QuantumGroup R v ⊗[k] QuantumGroup R v) :
    antipodeConjRight R v X 1 = LinearMap.mul' k _ ((antipode R v).lTensor _ X) := by
  induction X with
  | tmul x x' => simp [antipodeConjRight]
  | add X X' hX hX' => simp only [map_add, LinearMap.add_apply, hX, hX']

/-- The antipode axiom `m ∘ (S ⊗ 1) ∘ Δ = η ∘ ε`. -/
theorem mul'_rTensor_antipode_comul (x : QuantumGroup R v) :
    LinearMap.mul' k _ ((antipode R v).rTensor _ (comul R v x)) =
      algebraMap k _ (counit R v x) := by
  induction x using induction_on with
  | algebraMap c =>
    simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  | E i => simp [neg_add_cancel]
  | F i =>
    simp only [comul_F, map_add, LinearMap.rTensor_tmul, antipode_F, antipode_one,
      LinearMap.mul'_apply, counit_F, map_zero, one_mul]
    rw [neg_mul, mul_assoc, K_add, add_neg_cancel, K_zero, mul_one, neg_add_cancel]
  | K μ => simp [K_add]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy =>
    rw [map_mul, mul'_rTensor_antipode_mul, hx, Algebra.algebraMap_eq_smul_one, map_smul,
      antipodeConjLeft_one, hy, map_mul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]

/-- The antipode axiom `m ∘ (1 ⊗ S) ∘ Δ = η ∘ ε`. -/
theorem mul'_lTensor_antipode_comul (x : QuantumGroup R v) :
    LinearMap.mul' k _ ((antipode R v).lTensor _ (comul R v x)) =
      algebraMap k _ (counit R v x) := by
  induction x using induction_on with
  | algebraMap c =>
    simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  | E i =>
    simp only [comul_E, map_add, LinearMap.lTensor_tmul, antipode_E, antipode_one,
      LinearMap.mul'_apply, counit_E, map_zero, mul_one]
    rw [mul_neg, ← mul_assoc, K_add, add_neg_cancel, K_zero, one_mul, add_neg_cancel]
  | F i => simp
  | K μ => simp [K_add]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy =>
    rw [map_mul, mul'_lTensor_antipode_mul, hy, Algebra.algebraMap_eq_smul_one, map_smul,
      antipodeConjRight_one, hx, map_mul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]

/-- `U_q(𝔤)` is a Hopf algebra ([Lus] 3.1.12 (check)). -/
instance instHopfAlgebra : HopfAlgebra k (QuantumGroup R v) where
  antipode := antipode R v
  mul_antipode_rTensor_comul := LinearMap.ext fun x ↦ mul'_rTensor_antipode_comul R v x
  mul_antipode_lTensor_comul := LinearMap.ext fun x ↦ mul'_lTensor_antipode_comul R v x

end Antipode

end QuantumGroup
