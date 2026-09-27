/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Triangular

/-!
# A representation of `U_q(𝔤)` on `'f ⊗ k[Y] ⊗ 'f`

We construct operators `Eᵢ, Fᵢ, K_μ` on `V = ('f ⊗ k[Y]) ⊗ 'f` which model left multiplication
in `U` on the elements `y⁻ K_μ x⁺ ↔ y ⊗ e^μ ⊗ x` (`y, x ∈ 'f`), following the formula
`Eᵢ y⁻ = y⁻ Eᵢ + (K̃ᵢ ᵢr(y)⁻ - rᵢ(y)⁻ K̃₋ᵢ)/(vᵢ - vᵢ⁻¹)` ([Lus] 3.1.6 (check)):
* `Fᵢ (y ⊗ e^μ ⊗ x) = θᵢ y ⊗ e^μ ⊗ x`;
* `K_ν (y ⊗ e^μ ⊗ x) = τ_ν y ⊗ e^{ν+μ} ⊗ x`, where `τ_ν(θⱼ) = v^{-⟨ν, j'⟩} θⱼ`;
* `Eᵢ (y ⊗ e^μ ⊗ x) = v^{-⟨μ, i'⟩} y ⊗ e^μ ⊗ θᵢ x
    + (τ_{dᵢ i} ᵢr(y) ⊗ e^{dᵢ i + μ} ⊗ x - rᵢ(y) ⊗ e^{-dᵢ i + μ} ⊗ x)/(vᵢ - vᵢ⁻¹)`.
These operators satisfy the relations (b)–(d) of `U` (`QuantumGroup.preRelations_op`); the
construction is our own rendering of the standard argument ([Jan] 4.21 (check)).

## Main definitions

* `QuantumGroup.opE`, `QuantumGroup.opF`, `QuantumGroup.opKHom`: the operators on
  `'f ⊗ k[Y] ⊗ 'f`.

## Main results

* `QuantumGroup.preRelations_op`: they satisfy the relations (b)–(d) of `U`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.1–3.2.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 4.
-/

noncomputable section

open LusztigF TensorProduct

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

variable (k I Y) in
/-- The space `V = 'f ⊗ (k[Y] ⊗ 'f)`. -/
abbrev TriSpace := LusztigF k I ⊗[k] (AddMonoidAlgebra k Y ⊗[k] LusztigF k I)

/-- The automorphism `τ_ν : θⱼ ↦ v^{-⟨ν, j'⟩} θⱼ` of `'f`, so that `K_ν y⁻ = (τ_ν y)⁻ K_ν`. -/
def tau (ν : Y) : LusztigF k I →ₐ[k] LusztigF k I := diagTwist fun j ↦ v ^ (-R.root j ν)

/-- The shift `e^μ ↦ e^{ν + μ}` of `k[Y]`. -/
def shift (ν : Y) : AddMonoidAlgebra k Y →ₗ[k] AddMonoidAlgebra k Y :=
  LinearMap.mulLeft k (AddMonoidAlgebra.single ν 1)

variable [NeZero v]

/-- The character twist `e^μ ↦ v^{-⟨μ, i'⟩} e^μ` of `k[Y]`. -/
def chi (i : I) : AddMonoidAlgebra k Y →ₐ[k] AddMonoidAlgebra k Y :=
  AddMonoidAlgebra.lift k _ Y
    { toFun := fun μ ↦ v ^ (-R.root i μ.toAdd) • AddMonoidAlgebra.single μ.toAdd 1
      map_one' := by simp [AddMonoidAlgebra.one_def]
      map_mul' := fun μ ν ↦ by
        simp only [toAdd_mul, map_add, neg_add, zpow_add₀ (NeZero.ne v),
          AddMonoidAlgebra.single_mul_single, smul_mul_smul_comm, mul_one] }

omit [DecidableEq I] in
lemma chi_single (i : I) (μ : Y) :
    chi R v i (AddMonoidAlgebra.single μ 1) =
      v ^ (-R.root i μ) • AddMonoidAlgebra.single μ 1 := by
  simp [chi, AddMonoidAlgebra.lift_single]

/-! ### Identities between operators on the factors -/

variable {R v}

omit [DecidableEq I] [NeZero v] in
lemma tau_apply_θ (ν : Y) (j : I) : tau R v ν (θ k j) = v ^ (-R.root j ν) • θ k j := by
  simp [tau]

omit [DecidableEq I] in
lemma tau_mul_tau (ν ν' : Y) :
    (tau R v ν).toLinearMap * (tau R v ν').toLinearMap = (tau R v (ν + ν')).toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, tau, diagTwist_diagTwist]
  rw [show ((fun j ↦ v ^ (-R.root j ν)) * fun j ↦ v ^ (-R.root j ν')) =
    fun j ↦ v ^ (-R.root j (ν + ν')) from funext fun j ↦ by
      simp only [Pi.mul_apply, map_add, neg_add, zpow_add₀ (NeZero.ne v)]]

omit [DecidableEq I] [NeZero v] in
lemma tau_zero : (tau R v 0).toLinearMap = 1 := by
  ext x; simp [tau]

omit [DecidableEq I] [NeZero v] in
lemma tau_comm (ν ν' : Y) :
    (tau R v ν).toLinearMap * (tau R v ν').toLinearMap =
      (tau R v ν').toLinearMap * (tau R v ν).toLinearMap := by
  ext x; simp [tau, diagTwist_comm]

omit [DecidableEq I] [NeZero v] in
lemma tau_mul_mulLeft (ν : Y) (j : I) :
    (tau R v ν).toLinearMap * LinearMap.mulLeft k (θ k j) =
      v ^ (-R.root j ν) • (LinearMap.mulLeft k (θ k j) * (tau R v ν).toLinearMap) := by
  ext x; simp [tau]

omit [NeZero v] in
lemma lDeriv_mul_tau (i : I) (ν : Y) :
    (lDeriv D v i : Module.End k (LusztigF k I)) * (tau R v ν).toLinearMap =
      v ^ (-R.root i ν) • ((tau R v ν).toLinearMap * lDeriv D v i) := by
  ext x; simp [tau, lDeriv_diagTwist]

omit [NeZero v] in
lemma rDeriv_mul_tau (i : I) (ν : Y) :
    (rDeriv D v i : Module.End k (LusztigF k I)) * (tau R v ν).toLinearMap =
      v ^ (-R.root i ν) • ((tau R v ν).toLinearMap * rDeriv D v i) := by
  ext x; simp [tau, rDeriv_diagTwist]

omit [NeZero v] in
lemma lDeriv_mul_mulLeft (i j : I) :
    (lDeriv D v i : Module.End k (LusztigF k I)) * LinearMap.mulLeft k (θ k j) =
      (if i = j then 1 else 0) + v ^ D.dot i j • (LinearMap.mulLeft k (θ k j) * lDeriv D v i) := by
  ext x; simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, lDeriv_θ_mul]
  split_ifs <;> simp

omit [NeZero v] in
lemma rDeriv_mul_mulLeft (i j : I) :
    (rDeriv D v i : Module.End k (LusztigF k I)) * LinearMap.mulLeft k (θ k j) =
      LinearMap.mulLeft k (θ k j) * rDeriv D v i +
        (if i = j then (twist D v i).toLinearMap else 0) := by
  ext x; simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, rDeriv_θ_mul]
  split_ifs <;> simp

omit [DecidableEq I] [NeZero v] in
lemma tau_neg_ktilde (i : I) : tau R v (-ktilde R i) = twist D v i := by
  rw [tau, twist_eq_diagTwist]
  congr 1
  funext j
  rw [map_neg, neg_neg, root_ktilde_eq_dot]

omit [DecidableEq I] [NeZero v] in
lemma shift_mul_shift (ν ν' : Y) :
    shift (k := k) ν * shift ν' = shift (ν + ν') := by
  refine LinearMap.ext fun g ↦ ?_
  simp only [shift, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc,
    AddMonoidAlgebra.single_mul_single, one_mul]

omit [DecidableEq I] [NeZero v] in
lemma shift_zero : shift (k := k) (0 : Y) = 1 := by
  refine LinearMap.ext fun g ↦ ?_
  simp [shift, ← AddMonoidAlgebra.one_def]

omit [DecidableEq I] [NeZero v] in
lemma shift_comm (ν ν' : Y) : shift (k := k) ν * shift ν' = shift ν' * shift ν := by
  rw [shift_mul_shift, shift_mul_shift, add_comm]

omit [DecidableEq I] in
lemma chi_mul_shift (i : I) (ν : Y) :
    (chi R v i).toLinearMap * shift ν =
      v ^ (-R.root i ν) • (shift ν * (chi R v i).toLinearMap) := by
  refine LinearMap.ext fun g ↦ ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, shift, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, map_mul, chi_single, smul_mul_assoc]

omit [DecidableEq I] in
lemma chi_comm (i j : I) :
    (chi R v i).toLinearMap * (chi R v j).toLinearMap =
      (chi R v j).toLinearMap * (chi R v i).toLinearMap := by
  refine LinearMap.ext fun g ↦ ?_
  induction g using AddMonoidAlgebra.induction_on with
  | of μ =>
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply]
    rw [show AddMonoidAlgebra.of k Y (Multiplicative.ofAdd μ) = AddMonoidAlgebra.single μ 1
      from rfl, chi_single, map_smul, chi_single, map_smul, chi_single, smul_smul, smul_smul,
      mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul c x hx => rw [map_smul, map_smul, hx]

/-! ### Operators on `V` -/

/-- The operator `a ⊗ b ⊗ c` on `V`. -/
def tri (a : Module.End k (LusztigF k I)) (b : Module.End k (AddMonoidAlgebra k Y))
    (c : Module.End k (LusztigF k I)) : Module.End k (TriSpace k I Y) :=
  TensorProduct.map a (TensorProduct.map b c)

omit [DecidableEq I] [NeZero v] [AddCommGroup Y] in
lemma tri_mul (a a' b b' c c') :
    tri (k := k) (I := I) (Y := Y) a b c * tri a' b' c' = tri (a * a') (b * b') (c * c') := by
  simp only [tri, TensorProduct.map_mul]

omit [DecidableEq I] [NeZero v] [AddCommGroup Y] in
lemma tri_one : tri (k := k) (I := I) (Y := Y) 1 1 1 = 1 := by
  simp [tri]

omit [DecidableEq I] [NeZero v] [AddCommGroup Y] in
lemma tri_smul_left (s : k) (a b c) :
    tri (k := k) (I := I) (Y := Y) (s • a) b c = s • tri a b c := by
  simp [tri, TensorProduct.map_smul_left]

omit [DecidableEq I] [NeZero v] [AddCommGroup Y] in
lemma tri_smul_mid (s : k) (a b c) :
    tri (k := k) (I := I) (Y := Y) a (s • b) c = s • tri a b c := by
  simp [tri, TensorProduct.map_smul_left, TensorProduct.map_smul_right]

omit [DecidableEq I] [NeZero v] [AddCommGroup Y] in
lemma tri_add_left (a a' b c) :
    tri (k := k) (I := I) (Y := Y) (a + a') b c = tri a b c + tri a' b c := by
  simp [tri, TensorProduct.map_add_left]

omit [DecidableEq I] [NeZero v] [AddCommGroup Y] in
lemma tri_zero_left (b c) : tri (k := k) (I := I) (Y := Y) 0 b c = 0 := by
  simp [tri]

omit [DecidableEq I] [NeZero v] [AddCommGroup Y] in
@[simp] lemma tri_tmul (a b c) (y : LusztigF k I) (g : AddMonoidAlgebra k Y) (x : LusztigF k I) :
    tri a b c (y ⊗ₜ (g ⊗ₜ x)) = a y ⊗ₜ (b g ⊗ₜ c x) := rfl

variable (R v)

/-- The operator `Fᵢ` on `V`. -/
def opF (i : I) : Module.End k (TriSpace k I Y) := tri (LinearMap.mulLeft k (θ k i)) 1 1

/-- The operator `K_ν` on `V`. -/
def opK (ν : Y) : Module.End k (TriSpace k I Y) := tri (tau R v ν).toLinearMap (shift ν) 1

/-- The constant `(vᵢ - vᵢ⁻¹)⁻¹`. -/
abbrev cst (D : LusztigCartanDatum I) (i : I) : k := (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹

/-- The part `y⁻ Eᵢ K_μ x⁺` of `Eᵢ y⁻ K_μ x⁺`. -/
def opE0 (i : I) : Module.End k (TriSpace k I Y) :=
  tri 1 (chi R v i).toLinearMap (LinearMap.mulLeft k (θ k i))

/-- The part `K̃ᵢ ᵢr(y)⁻ K_μ x⁺`. -/
def opEp (i : I) : Module.End k (TriSpace k I Y) :=
  tri ((tau R v (ktilde R i)).toLinearMap * lDeriv D v i) (shift (ktilde R i)) 1

/-- The part `rᵢ(y)⁻ K̃₋ᵢ K_μ x⁺`. -/
def opEm (i : I) : Module.End k (TriSpace k I Y) := tri (rDeriv D v i) (shift (-ktilde R i)) 1

/-- The operator `Eᵢ` on `V`. -/
def opE (i : I) : Module.End k (TriSpace k I Y) :=
  opE0 R v i + cst v D i • opEp R v i + (-cst v D i) • opEm R v i

/-- The operators `K_ν` as a monoid homomorphism. -/
def opKHom : Multiplicative Y →* Module.End k (TriSpace k I Y) where
  toFun ν := opK R v ν.toAdd
  map_one' := by simp [opK, tau_zero, shift_zero, tri_one]
  map_mul' ν ν' := by simp [opK, tri_mul, tau_mul_tau, shift_mul_shift]

omit [DecidableEq I] in
lemma opKHom_apply (μ : Multiplicative Y) : opKHom R v μ = opK R v μ.toAdd := rfl

/-! ### The relations (b)–(d) -/

variable {R v}

omit [DecidableEq I] in
lemma opK_mul_opE0 (ν : Y) (i : I) :
    opK R v ν * opE0 R v i = v ^ R.root i ν • (opE0 R v i * opK R v ν) := by
  simp only [opE0, opK, tri_mul, mul_one, one_mul]
  rw [chi_mul_shift, tri_smul_mid, smul_smul, ← zpow_add₀ (NeZero.ne v), add_neg_cancel,
    zpow_zero, one_smul]

lemma opK_mul_opEp (ν : Y) (i : I) :
    opK R v ν * opEp R v i = v ^ R.root i ν • (opEp R v i * opK R v ν) := by
  simp only [opEp, opK, tri_mul, mul_one]
  rw [mul_assoc, lDeriv_mul_tau, mul_smul_comm, ← mul_assoc, ← mul_assoc, tau_comm, shift_comm,
    tri_smul_left, smul_smul, ← zpow_add₀ (NeZero.ne v), add_neg_cancel, zpow_zero, one_smul]

lemma opK_mul_opEm (ν : Y) (i : I) :
    opK R v ν * opEm R v i = v ^ R.root i ν • (opEm R v i * opK R v ν) := by
  simp only [opEm, opK, tri_mul, mul_one]
  rw [rDeriv_mul_tau, shift_comm, tri_smul_left, smul_smul, ← zpow_add₀ (NeZero.ne v),
    add_neg_cancel, zpow_zero, one_smul]

lemma opK_mul_opE (ν : Y) (i : I) :
    opK R v ν * opE R v i = v ^ R.root i ν • (opE R v i * opK R v ν) := by
  rw [opE, mul_add, mul_add, mul_smul_comm, mul_smul_comm, opK_mul_opE0, opK_mul_opEp,
    opK_mul_opEm, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_add, smul_add,
    smul_comm (cst v D i), smul_comm (-cst v D i)]

omit [DecidableEq I] [NeZero v] in
lemma opK_mul_opF (ν : Y) (i : I) :
    opK R v ν * opF i = v ^ (-R.root i ν) • (opF i * opK R v ν) := by
  simp only [opF, opK, tri_mul, mul_one, one_mul]
  rw [tau_mul_mulLeft, tri_smul_left]

omit [DecidableEq I] in
lemma opE0_mul_opF (i j : I) : opE0 R v i * opF j = opF j * opE0 R v i := by
  simp only [opE0, opF, tri_mul, mul_one, one_mul]

lemma opEp_mul_opF (i j : I) :
    opEp R v i * opF j = opF j * opEp R v i + if i = j then opK R v (ktilde R i) else 0 := by
  simp only [opEp, opF, opK, tri_mul, mul_one, one_mul]
  rw [mul_assoc, lDeriv_mul_mulLeft, mul_add, mul_smul_comm, ← mul_assoc, tau_mul_mulLeft,
    smul_mul_assoc, smul_smul, root_ktilde_eq_dot, ← zpow_add₀ (NeZero.ne v), add_neg_cancel,
    zpow_zero, one_smul, tri_add_left, add_comm, mul_assoc]
  split_ifs <;> simp [tri_zero_left]

omit [NeZero v] in
lemma opEm_mul_opF (i j : I) :
    opEm R v i * opF j = opF j * opEm R v i + if i = j then opK R v (-ktilde R i) else 0 := by
  simp only [opEm, opF, opK, tri_mul, mul_one, one_mul]
  rw [rDeriv_mul_mulLeft, tri_add_left, tau_neg_ktilde]
  split_ifs <;> simp [tri_zero_left]

lemma opE_mul_opF (i j : I) :
    opE R v i * opF j = opF j * opE R v i + if i = j then
      cst v D i • opK R v (ktilde R i) + (-cst v D i) • opK R v (-ktilde R i) else 0 := by
  rw [opE, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, opE0_mul_opF, opEp_mul_opF,
    opEm_mul_opF, mul_add, mul_add, mul_smul_comm, mul_smul_comm]
  split_ifs
  · simp only [smul_add]; abel
  · simp only [add_zero]

variable (R v)

/-- The operators `opE`, `opF`, `opKHom` satisfy the relations (b)–(d) of `U`. -/
theorem preRelations_op : PreRelations R v (opE R v) (opF (k := k) (Y := Y)) (opKHom R v) where
  K_mul_E ν i := opK_mul_opE ν i
  K_mul_F ν i := opK_mul_opF ν i
  E_mul_F i j := by
    rw [opE_mul_opF]
    split_ifs
    · rw [opKHom_apply, opKHom_apply, toAdd_ofAdd, toAdd_ofAdd]
      module
    · module

end QuantumGroup
