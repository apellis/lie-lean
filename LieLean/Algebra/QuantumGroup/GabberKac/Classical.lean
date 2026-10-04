/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.SerreAssociative.HighestWeight
import LieLean.Algebra.Lie.KacMoody.Shapovalov
import LieLean.Algebra.QuantumGroup.GabberKac.Quantum
import LieLean.Algebra.QuantumGroup.GabberKac.SerreSpan

/-!
# The classical Shapovalov pairing on the free algebra

Let `(I, ·)` be a Cartan datum with (symmetrizable, generalized) Cartan matrix `A = (aᵢⱼ)`, `K` a
field of characteristic zero, `(𝔥, Π, Π^∨)` a realization of `A` over `K` and `Λ ∈ 𝔥*` dominant
integral with `⟨Λ, αᵢ^∨⟩ = nᵢ`. Let `L(Λ)` be the irreducible highest-weight module of the
Kac–Moody algebra `𝔤(A)` and `Y : K⟨θᵢ⟩ → L(Λ)`, `y ↦ y(f) v_Λ` (the free algebra acting through
`θᵢ ↦ fᵢ`).

The classical Verma-type operators `Eᵢ = LusztigF.vermaOp i cᵢ` with coefficients
`cᵢ(μ) = nᵢ - ⟨μ, αᵢ^∨⟩` describe the action of `eᵢ` (`LusztigF.lie_e_toIrreducible`):
`eᵢ Y(y) = Y(Eᵢ y)`, and the pairing `S(w, y) = ε(E_w y)` is the contravariant form
`(Y(w), Y(y))` of `L(Λ)` (`LusztigF.contravariantForm_toIrreducible`).

**Theorem** (`LusztigF.mem_serreSpan_of_vermaForm_eq_zero`). If `y` has weight `ν ≤ n` (i.e.
`νᵢ ≤ nᵢ` for all `i`) and `S(w, y) = 0` for all words `w` of weight `ν`, then `y` lies in the span
of the products `a sᵢⱼ b` of weight `ν` with the classical Serre elements `sᵢⱼ`.

Proof: `Y(y)` is orthogonal to `L(Λ) = Y(K⟨θ⟩)`, hence zero since the contravariant form of `L(Λ)`
is nondegenerate ([Kac] §9.4). By the associative presentation of `L(Λ)`
(`Matrix.Realization.KacMoodyAlgebra.serreAssocQuotientEquiv`, which rests on the Gabber–Kac
theorem [Kac] Thm. 9.11 and on [Kac] Cor. 10.4), `y ∈ Serre ideal + Σᵢ K⟨θ⟩ θᵢ^{nᵢ+1}`; taking
weight-`ν` components, the second summand disappears since `νᵢ < nᵢ + 1`, and the first lands in
the span of the Serre products (`LusztigF.weightProj_mem_serreSpan`). This argument is our own.

## Main results

* `LusztigCartanDatum.isSymmetrizable_cartanMatrix`.
* `LusztigF.lie_e_toIrreducible`, `LusztigF.contravariantForm_toIrreducible`.
* `LusztigF.mem_serreSpan_of_vermaForm_eq_zero`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.4, Thm. 9.11,
  Cor. 10.4.
-/

open LieLean

noncomputable section

open FreeAlgebra LieLean.QuantumGroup Matrix Matrix.Realization Matrix.Realization.KacMoodyAlgebra

namespace LusztigCartanDatum

variable {I : Type*} [Fintype I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The Cartan matrix of a Cartan datum is symmetrizable: `dᵢ aᵢⱼ = i · j` is symmetric. -/
theorem isSymmetrizable_cartanMatrix : D.cartanMatrix.IsSymmetrizable := by
  refine ⟨fun i ↦ D.d i, fun i ↦ Int.natCast_pos.2 (D.d_pos i), Matrix.IsSymm.ext fun i j ↦ ?_⟩
  simp only [Matrix.diagonal_mul, D.d_mul_cartanMatrix, D.dot_comm]

end LusztigCartanDatum

namespace LusztigF

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] (D : LusztigCartanDatum I)
  (P : Realization D.cartanMatrix K H) {Λ : Module.Dual K H} {n : I → ℕ}
  (hn : ∀ i, Λ (P.coroot i) = n i)

variable (K) in
/-- The classical Verma coefficients `cᵢ(μ) = nᵢ - ⟨μ, αᵢ^∨⟩`. -/
def classicalCoeff (n : I → ℕ) (i : I) (μ : I →₀ ℕ) : K := ((n i : ℤ) - D.coPairing i μ : ℤ)

/-- The linear map `Y : K⟨θᵢ⟩ → L(Λ)`, `y ↦ y(f) v_Λ`. -/
def toIrreducible : LusztigF K I →ₗ[K] IrreducibleModule P Λ :=
  serreAssocToIrreducibleModule P D.isGeneralizedCartan_cartanMatrix
      D.isSymmetrizable_cartanMatrix hn ∘ₗ
    (SerreAssocAlgebra.mkAlgHom K D.cartanMatrix).toLinearMap

lemma toIrreducible_apply (y : LusztigF K I) :
    toIrreducible D P hn y = serreAssocToIrreducibleModule P D.isGeneralizedCartan_cartanMatrix
      D.isSymmetrizable_cartanMatrix hn (SerreAssocAlgebra.mkAlgHom K D.cartanMatrix y) := rfl

lemma toIrreducible_one : toIrreducible D P hn 1 = IrreducibleModule.hwv P Λ := by
  rw [toIrreducible_apply, map_one, ← serreAssocQuotientEquiv_mk, serreAssocQuotientEquiv_mk_one]

lemma toIrreducible_θ_mul (j : I) (y : LusztigF K I) :
    toIrreducible D P hn (θ K j * y) = ⁅f P j, toIrreducible D P hn y⁆ := by
  rw [toIrreducible_apply, toIrreducible_apply, ← serreAssocQuotientEquiv_mk,
    ← serreAssocQuotientEquiv_mk, ← serreAssocQuotientEquiv_θ_smul, ← Submodule.Quotient.mk_smul,
    map_mul, smul_eq_mul]
  rfl

lemma toIrreducible_surjective : Function.Surjective (toIrreducible D P hn) :=
  (serreAssocToIrreducibleModule_surjective P _ _ hn).comp
    (SerreAssocAlgebra.mkAlgHom_surjective K D.cartanMatrix)

omit [FiniteDimensional K H] [CharZero K] in
lemma lie_h_irreducible_hwv (a : H) :
    ⁅h P a, IrreducibleModule.hwv P Λ⁆ = Λ a • IrreducibleModule.hwv P Λ := by
  rw [IrreducibleModule.hwv, ← LieModuleHom.map_lie, VermaModule.lie_h_hwv, map_smul]

omit [FiniteDimensional K H] [CharZero K] in
lemma lie_e_irreducible_hwv (i : I) : ⁅e P i, IrreducibleModule.hwv P Λ⁆ = 0 := by
  rw [IrreducibleModule.hwv, ← LieModuleHom.map_lie, VermaModule.lie_e_hwv, map_zero]

/-- `Y(w)` has weight `Λ - |w|`: `hᵢ Y(w) = (nᵢ - ⟨|w|, αᵢ^∨⟩) Y(w)`. -/
lemma lie_h_toIrreducible (i : I) (w : List I) :
    ⁅h P (P.coroot i), toIrreducible D P hn (wordBasis K I w)⁆ =
      classicalCoeff K D n i (wordWeight w) • toIrreducible D P hn (wordBasis K I w) := by
  induction w with
  | nil =>
    rw [wordBasis_nil, toIrreducible_one, lie_h_irreducible_hwv, hn]
    simp [classicalCoeff]
  | cons j w ih =>
    rw [← ι_mul_wordBasis, toIrreducible_θ_mul, leibniz_lie, lie_h_f, neg_lie, smul_lie, ih,
      lie_smul, P.root_coroot]
    simp only [classicalCoeff, D.coPairing_wordWeight_cons]
    push_cast
    module

/-- `eᵢ Y(y) = Y(Eᵢ y)` for the classical Verma-type operator `Eᵢ`. -/
theorem lie_e_toIrreducible (i : I) (y : LusztigF K I) :
    ⁅e P i, toIrreducible D P hn y⁆ =
      toIrreducible D P hn (vermaOp i (classicalCoeff K D n i) y) := by
  induction y using induction_wordBasis with
  | zero => simp
  | add y z hy hz => rw [map_add, lie_add, hy, hz, map_add, map_add]
  | smul c y hy => rw [map_smul, lie_smul, hy, map_smul, map_smul]
  | word w =>
    induction w with
    | nil =>
      rw [wordBasis_nil, toIrreducible_one, lie_e_irreducible_hwv, vermaOp_one, map_zero]
    | cons j w ih =>
      rw [← ι_mul_wordBasis, toIrreducible_θ_mul, leibniz_lie, lie_e_f, ih, vermaOp_ι_mul,
        map_add, toIrreducible_θ_mul, weightScale_wordBasis]
      split_ifs with hij
      · subst hij
        rw [lie_h_toIrreducible, map_smul, add_comm]
      · rw [zero_lie, zero_add, map_zero, add_zero]

/-- The contravariant form of `L(Λ)` against the highest-weight vector is the augmentation. -/
lemma contravariantForm_hwv_toIrreducible (y : LusztigF K I) :
    IrreducibleModule.contravariantForm P Λ (IrreducibleModule.hwv P Λ)
      (toIrreducible D P hn y) = counit y := by
  induction y using induction_left with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, toIrreducible_one,
      IrreducibleModule.contravariantForm_hwv_hwv]
    simp
  | smul c y hy => rw [map_smul, map_smul, hy, map_smul, smul_eq_mul]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]
  | θ_mul j y _ =>
    rw [toIrreducible_θ_mul, (IrreducibleModule.isSymm_contravariantForm P Λ).eq,
      IrreducibleModule.contravariantForm_lie_left, transpose_f,
      lie_e_irreducible_hwv, map_zero, map_mul, counit_θ, zero_mul]

/-- The classical Shapovalov pairing is the contravariant form of `L(Λ)`:
`S(w, y) = (Y(w), Y(y))`. -/
theorem contravariantForm_toIrreducible (w : List I) (y : LusztigF K I) :
    IrreducibleModule.contravariantForm P Λ (toIrreducible D P hn (wordBasis K I w))
      (toIrreducible D P hn y) = vermaForm (classicalCoeff K D n) w y := by
  induction w generalizing y with
  | nil => rw [wordBasis_nil, toIrreducible_one, contravariantForm_hwv_toIrreducible]; rfl
  | cons i w ih =>
    rw [← ι_mul_wordBasis, toIrreducible_θ_mul, IrreducibleModule.contravariantForm_lie_left,
      transpose_f, lie_e_toIrreducible, ih, vermaForm_cons]

omit [Fintype I] [CharZero K] [DecidableEq I] in
/-- The classical Serre element `Σ (-1)^r (m choose r) θᵢ^r θⱼ θᵢ^{m-r}` of
`Matrix.serreAssocElem` is `(-1)^m` times the binomial Serre word `LusztigF.serreWord` at
`q = 1`. -/
lemma serreAssocElem_eq_smul_serreWord {i j : I} (hij : i ≠ j) :
    serreAssocElem K D.cartanMatrix i j =
      (-1 : K) ^ serreExp D i j • serreWord D (fun _ ↦ (1 : K)) i j := by
  have hN : (-D.cartanMatrix i j).toNat + 1 = serreExp D i j :=
    D.isGeneralizedCartan_cartanMatrix.toNat_neg_add_one hij
  rw [serreAssocElem, hN, serreWord, qSerre, Finset.smul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ serreExp D i j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  set N := serreExp D i j
  rw [show N + 1 - 1 - r = N - r by omega, Nat.sub_sub_self hr, qBinomial_one,
    Nat.choose_symm hr, smul_smul]
  have hs : (-1 : K) ^ N * (-1) ^ r = (-1) ^ (N - r) := by
    rw [← pow_add, show N + r = 2 * r + (N - r) by omega, pow_add, pow_mul, neg_one_sq,
      one_pow, one_mul]
  rw [← mul_assoc, hs]

omit [Fintype I] [CharZero K] [DecidableEq I] in
lemma serreAssocIdeal_le_span_serreWord :
    serreAssocIdeal K D.cartanMatrix ≤
      TwoSidedIdeal.span {y | ∃ i j, i ≠ j ∧ serreWord D (fun _ ↦ (1 : K)) i j = y} := by
  rw [serreAssocIdeal, TwoSidedIdeal.span_le]
  rintro _ ⟨i, j, hij, rfl⟩
  rw [serreAssocElem_eq_smul_serreWord D hij, Algebra.smul_def]
  exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨i, j, hij, rfl⟩)

/-- **The classical kernel.** If `y ∈ K⟨θ⟩` has weight `ν` with `νᵢ ≤ nᵢ` for all `i`, and the
classical Shapovalov pairing `S(w, y)` vanishes for all words `w` of weight `ν`, then `y` is a
linear combination of products `a sᵢⱼ b` of weight `ν` with classical Serre elements `sᵢⱼ`
(`i ≠ j`) and words `a`, `b`. This uses the Gabber–Kac theorem ([Kac] Thm. 9.11) and the
presentation of `L(Λ)` ([Kac] Cor. 10.4). -/
theorem mem_serreSpan_of_vermaForm_eq_zero (P : Realization D.cartanMatrix K H)
    (hn : ∀ i, Λ (P.coroot i) = n i) {ν : I →₀ ℕ} (hν : ∀ i, ν i ≤ n i)
    {y : LusztigF K I} (hy : y ∈ weightSpace K ν)
    (h : ∀ w, wordWeight w = ν → vermaForm (classicalCoeff K D n) w y = 0) :
    y ∈ serreSpan D (fun _ ↦ (1 : K)) ν := by
  have h' : ∀ w, vermaForm (classicalCoeff K D n) w y = 0 := fun w ↦ by
    by_cases hw : wordWeight w = ν
    · exact h w hw
    · exact vermaForm_eq_zero_of_ne _ w hw hy
  -- `Y(y)` is orthogonal to `L(Λ)`, hence zero
  have hY : toIrreducible D P hn y = 0 := by
    refine (IrreducibleModule.nondegenerate_contravariantForm P Λ).2 _ fun u ↦ ?_
    obtain ⟨x, rfl⟩ := toIrreducible_surjective D P hn u
    induction x using induction_wordBasis with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', add_zero]
    | smul c x hx => simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]
    | word w => rw [contravariantForm_toIrreducible, h' w]
  -- so `y ∈ Serre ideal + Σᵢ K⟨θ⟩ θᵢ^{nᵢ+1}`
  have hker : SerreAssocAlgebra.mkAlgHom K D.cartanMatrix y ∈
      SerreAssocAlgebra.thetaPowLeftIdeal K D.cartanMatrix n := by
    have hmem : SerreAssocAlgebra.mkAlgHom K D.cartanMatrix y ∈ LinearMap.ker
        (serreAssocToIrreducibleModule P D.isGeneralizedCartan_cartanMatrix
          D.isSymmetrizable_cartanMatrix hn) := hY
    rw [ker_serreAssocToIrreducibleModule] at hmem
    exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hker
  choose b hb using fun i ↦ SerreAssocAlgebra.mkAlgHom_surjective K D.cartanMatrix (c i)
  have hz : y - ∑ i, b i * θ K i ^ (n i + 1) ∈ serreAssocIdeal K D.cartanMatrix := by
    rw [← SerreAssocAlgebra.mkAlgHom_eq_zero_iff, map_sub, map_sum, ← hc, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, hb, smul_eq_mul]
    rfl
  -- take weight-`ν` components
  have := weightProj_mem_serreSpan D _ (serreAssocIdeal_le_span_serreWord D hz) ν
  rwa [map_sub, map_sum, weightProj_self hy,
    Finset.sum_eq_zero fun i _ ↦ weightProj_mul_ι_pow (by have := hν i; omega) _,
    sub_zero] at this

end LusztigF
