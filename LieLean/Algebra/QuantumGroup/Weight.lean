/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Triangular

/-!
# Weight spaces of `U_q(𝔤)`-modules

Let `U = U_q(𝔤)` be the quantized enveloping algebra of a root datum `(Y, …)` of type `(I, ·)`
(`QuantumGroup R v`) and let `X = Hom(Y, ℤ)` be the weight lattice. For a `U`-module `M` and
`Λ ∈ X` the weight space ([Lus] 3.4.1, [Jan] 5.1) is
`M^Λ = {m ∈ M | K_μ m = v^{⟨μ, Λ⟩} m for all μ ∈ Y}`.
Here a `U`-module is a `k`-vector space `M` with `[Module U M]` and `[IsScalarTower k U M]`.

## Main definitions

* `QuantumGroup.weightSpace R v M Λ`: the weight space `M^Λ`.
* `QuantumGroup.charHom v Λ`: the character `k[Y] → k`, `e^μ ↦ v^{⟨μ, Λ⟩}`, by which `U⁰` acts on
  `M^Λ`.
* `LusztigCartanDatum.RootDatum.rootSum`: the element `Σᵢ νᵢ i' ∈ X` of `ν ∈ ℕ[I]`.
* `LusztigCartanDatum.RootDatum.IsXRegular`: the simple roots `i' ∈ X` are linearly independent
  ([Lus] 2.2.2).

## Main results

* `QuantumGroup.E_smul_mem_weightSpace`, `QuantumGroup.F_smul_mem_weightSpace`:
  `Eᵢ M^Λ ⊆ M^{Λ + i'}`, `Fᵢ M^Λ ⊆ M^{Λ - i'}`.
* `QuantumGroup.zeroHom_smul_of_mem_weightSpace`: `U⁰` acts on `M^Λ` through `charHom v Λ`.
* `QuantumGroup.exists_charHom_eq_one_eq_zero`, `QuantumGroup.iSupIndep_weightSpace`: if `v` is
  not a root of unity, `U⁰` separates weights and the weight spaces are independent.
* `LusztigCartanDatum.RootDatum.exists_rootSum_ne`: for `X`-regular root data,
  `ν ↦ Σᵢ νᵢ i'` is injective on `ℕ[I]`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §2.2, §3.4.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 5.
-/

noncomputable section

namespace LusztigCartanDatum.RootDatum

variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} (R : D.RootDatum Y)

/-- The element `Σᵢ νᵢ i'` of `X = Hom(Y, ℤ)` attached to `ν ∈ ℕ[I]`. -/
def rootSum (ν : I →₀ ℕ) : Y →+ ℤ := ν.sum fun i n ↦ n • R.root i

@[simp] lemma rootSum_zero : R.rootSum 0 = 0 := by simp [rootSum]

lemma rootSum_add (ν ν' : I →₀ ℕ) : R.rootSum (ν + ν') = R.rootSum ν + R.rootSum ν' :=
  Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ add_smul _ _ _)

@[simp] lemma rootSum_single (i : I) (n : ℕ) : R.rootSum (Finsupp.single i n) = n • R.root i := by
  simp [rootSum]

/-- A root datum is `X`-regular if the simple roots `i' ∈ X = Hom(Y, ℤ)` are linearly independent
([Lus] 2.2.2). -/
def IsXRegular : Prop := LinearIndependent ℤ R.root

/-- For an `X`-regular root datum, `ν ↦ Σᵢ νᵢ i'` is injective on `ℕ[I]`: if `ν ≠ ν'`, some
`μ ∈ Y` has `⟨μ, Σᵢ νᵢ i'⟩ ≠ ⟨μ, Σᵢ ν'ᵢ i'⟩`. -/
theorem exists_rootSum_ne (hR : R.IsXRegular) {ν ν' : I →₀ ℕ} (hν : ν ≠ ν') :
    ∃ μ, R.rootSum ν μ ≠ R.rootSum ν' μ := by
  by_contra! h
  have h0 : R.rootSum ν - R.rootSum ν' = 0 := AddMonoidHom.ext fun μ ↦ by simp [h μ]
  have key : ∀ ν : I →₀ ℕ, Finsupp.linearCombination ℤ R.root
      (ν.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp)) = R.rootSum ν := fun ν ↦ by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
    simp only [rootSum, natCast_zsmul]
  have h2 := linearIndependent_iff.1 hR (ν.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp) -
    ν'.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp)) (by rw [map_sub, key, key, h0])
  apply hν
  ext i
  simpa [sub_eq_zero] using congr($h2 i)

end LusztigCartanDatum.RootDatum

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

section Weight

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-- The weight space `M^Λ = {m | K_μ m = v^{⟨μ, Λ⟩} m for all μ ∈ Y}` of a `U`-module `M`, for
`Λ ∈ X = Hom(Y, ℤ)` ([Lus] 3.4.1, [Jan] 5.1). -/
def weightSpace (Λ : Y →+ ℤ) : Submodule k M where
  carrier := {m | ∀ μ, K R v μ • m = v ^ Λ μ • m}
  add_mem' {a b} ha hb μ := by simp [smul_add, ha μ, hb μ]
  zero_mem' μ := by simp
  smul_mem' c m hm μ := by rw [smul_comm, hm μ, smul_comm]

variable {R v M}

lemma mem_weightSpace {Λ : Y →+ ℤ} {m : M} :
    m ∈ weightSpace R v M Λ ↔ ∀ μ, K R v μ • m = v ^ Λ μ • m := Iff.rfl

variable [NeZero v]

/-- `Eᵢ M^Λ ⊆ M^{Λ + i'}`. -/
theorem E_smul_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (i : I) :
    E R v i • m ∈ weightSpace R v M (Λ + R.root i) := fun μ ↦ by
  rw [← mul_smul, K_mul_E, smul_assoc, mul_smul, hm μ, smul_comm (E R v i), smul_smul,
    AddMonoidHom.add_apply, zpow_add₀ (NeZero.ne v), mul_comm]

/-- `Fᵢ M^Λ ⊆ M^{Λ - i'}`. -/
theorem F_smul_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (i : I) :
    F R v i • m ∈ weightSpace R v M (Λ - R.root i) := fun μ ↦ by
  rw [← mul_smul, K_mul_F, smul_assoc, mul_smul, hm μ, smul_comm (F R v i), smul_smul,
    AddMonoidHom.sub_apply, sub_eq_add_neg, zpow_add₀ (NeZero.ne v), mul_comm]

omit [NeZero v] in
/-- `K_ν M^Λ ⊆ M^Λ`. -/
theorem K_smul_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (ν : Y) :
    K R v ν • m ∈ weightSpace R v M Λ := by
  rw [hm ν]; exact Submodule.smul_mem _ _ hm

variable (v) in
/-- The character `k[Y] → k`, `e^μ ↦ v^{⟨μ, Λ⟩}`, of `Λ ∈ X`. -/
def charHom (Λ : Y →+ ℤ) : AddMonoidAlgebra k Y →ₐ[k] k :=
  AddMonoidAlgebra.lift k k Y
    { toFun := fun μ ↦ v ^ Λ μ.toAdd
      map_one' := by simp
      map_mul' := fun μ ν ↦ by simp [zpow_add₀ (NeZero.ne v)] }

omit [DecidableEq I] in
@[simp] lemma charHom_single (Λ : Y →+ ℤ) (μ : Y) (c : k) :
    charHom v Λ (AddMonoidAlgebra.single μ c) = c * v ^ Λ μ := by
  simp [charHom, AddMonoidAlgebra.lift_single, smul_eq_mul]

/-- `U⁰` acts on `M^Λ` through the character `charHom v Λ`. -/
theorem zeroHom_smul_of_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ)
    (g : AddMonoidAlgebra k Y) : zeroHom R v g • m = charHom v Λ g • m := by
  induction g using AddMonoidAlgebra.induction_on with
  | of μ =>
    change zeroHom R v (AddMonoidAlgebra.single μ 1) • m = _
    rw [zeroHom_single, hm, AddMonoidAlgebra.of_apply, charHom_single, one_mul]; rfl
  | add f g hf hg => rw [map_add, add_smul, hf, hg, map_add, add_smul]
  | smul c f hf => rw [map_smul, smul_assoc, hf, map_smul, smul_assoc]

omit [NeZero v] in
/-- On `M^Λ`, `K̃ᵢ` acts by `vᵢ^{⟨i, Λ⟩}`. -/
theorem Kt_smul_of_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (i : I) :
    Kt R v i • m = (v ^ D.d i) ^ Λ (R.coroot i) • m := by
  rw [Kt, hm, ktilde, map_nsmul, nsmul_eq_mul, ← zpow_natCast, ← zpow_mul]

omit [NeZero v] in
/-- On `M^Λ`, `K̃ᵢ⁻¹ = K_{-dᵢ i}` acts by `vᵢ^{-⟨i, Λ⟩}`. -/
theorem K_neg_ktilde_smul_of_mem_weightSpace {Λ : Y →+ ℤ} {m : M}
    (hm : m ∈ weightSpace R v M Λ) (i : I) :
    K R v (-ktilde R i) • m = (v ^ D.d i) ^ (-Λ (R.coroot i)) • m := by
  rw [hm, map_neg, ktilde, map_nsmul, nsmul_eq_mul, ← zpow_natCast, ← zpow_mul, neg_mul_eq_mul_neg]

omit [DecidableEq I] [NeZero v] in
/-- If `v` is not a root of unity, `v^n ≠ 1` for all integers `n ≠ 0`. -/
lemma zpow_ne_one_of_not_root (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {n : ℤ} (hn : n ≠ 0) :
    v ^ n ≠ 1 := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast]; exact hv' _ (Int.natAbs_pos.2 hn)
  · rw [h, zpow_neg, zpow_natCast, inv_ne_one]; exact hv' _ (Int.natAbs_pos.2 hn)

omit [DecidableEq I] in
/-- Distinct weights are separated by `U⁰ = k[Y]` if `v` is not a root of unity: there is
`g ∈ k[Y]` acting by `1` on `M^{Λ₁}` and by `0` on `M^{Λ₂}`. -/
theorem exists_charHom_eq_one_eq_zero (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ₁ Λ₂ : Y →+ ℤ}
    (h : Λ₁ ≠ Λ₂) : ∃ g, charHom v Λ₁ g = 1 ∧ charHom v Λ₂ g = 0 := by
  obtain ⟨μ, hμ⟩ := DFunLike.ne_iff.1 h
  have hv0 := NeZero.ne v
  have hab : v ^ Λ₁ μ - v ^ Λ₂ μ ≠ 0 := by
    rw [sub_ne_zero]
    intro hab
    refine zpow_ne_one_of_not_root hv' (sub_ne_zero.2 hμ) ?_
    rw [zpow_sub₀ hv0, hab, div_self (zpow_ne_zero _ hv0)]
  refine ⟨(v ^ Λ₁ μ - v ^ Λ₂ μ)⁻¹ • (AddMonoidAlgebra.single μ 1 -
    AddMonoidAlgebra.single 0 (v ^ Λ₂ μ)), ?_, ?_⟩
  · simp only [map_smul, map_sub, charHom_single, one_mul, AddMonoidHom.map_zero, zpow_zero,
      mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hab
  · simp [charHom_single]

/-- The weight spaces of any `U`-module are independent, if `v` is not a root of unity. -/
theorem iSupIndep_weightSpace (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    iSupIndep (weightSpace R v M) := by
  intro Λ
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have comb : ∀ y z : M, (∃ g, charHom v Λ g = 1 ∧ zeroHom R v g • y = 0) →
      (∃ g, charHom v Λ g = 1 ∧ zeroHom R v g • z = 0) →
      ∃ g, charHom v Λ g = 1 ∧ zeroHom R v g • (y + z) = 0 := by
    rintro y z ⟨g₁, hg₁, hy⟩ ⟨g₂, hg₂, hz⟩
    refine ⟨g₁ * g₂, by rw [map_mul, hg₁, hg₂, one_mul], ?_⟩
    have e1 : zeroHom R v (g₁ * g₂) • y = zeroHom R v g₂ • zeroHom R v g₁ • y := by
      rw [← mul_smul, ← map_mul, mul_comm]
    have e2 : zeroHom R v (g₁ * g₂) • z = zeroHom R v g₁ • zeroHom R v g₂ • z := by
      rw [← mul_smul, ← map_mul]
    rw [smul_add, e1, e2, hy, hz, smul_zero, smul_zero, add_zero]
  -- every element of `⨆_{Λ' ≠ Λ} M^{Λ'}` is killed by some `g` with `Λ(g) = 1`
  have key : ∀ y ∈ ⨆ Λ', ⨆ (_ : Λ' ≠ Λ), weightSpace R v M Λ',
      ∃ g, charHom v Λ g = 1 ∧ zeroHom R v g • y = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem Λ' y hy =>
      induction hy using Submodule.iSup_induction' with
      | mem hΛ' y hy =>
        obtain ⟨g, hg1, hg2⟩ := exists_charHom_eq_one_eq_zero hv' (Ne.symm hΛ')
        exact ⟨g, hg1, by rw [zeroHom_smul_of_mem_weightSpace hy, hg2, zero_smul]⟩
      | zero => exact ⟨1, map_one _, smul_zero _⟩
      | add y z _ _ hy hz => exact comb y z hy hz
    | zero => exact ⟨1, map_one _, smul_zero _⟩
    | add y z _ _ hy hz => exact comb y z hy hz
  obtain ⟨g, hg, hgx⟩ := key x hx'
  rwa [zeroHom_smul_of_mem_weightSpace hx, hg, one_smul] at hgx

end Weight

end QuantumGroup
