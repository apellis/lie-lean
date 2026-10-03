/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Integrable
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Classical

/-!
# The quantum Shapovalov pairing on Verma modules

Let `U = U_q(𝔤)` for a root datum `R` of type `(I, ·)` over a field `k` of characteristic zero,
`v ∈ k` not a root of unity, and `Λ ∈ X = Hom(Y, ℤ)`. On the quantum Verma module
`M_q(Λ) = U⁻ v_Λ` the raising operators act by ([Jan] 4.3 (R4), 5.5, 5.12(8), [Lus] 3.4.2, 3.4.5)
`Eᵢ Fⱼ y⁻ v_Λ = Fⱼ Eᵢ y⁻ v_Λ + δᵢⱼ [⟨i, Λ⟩ - ⟨μ, αᵢ^∨⟩]_{vᵢ} y⁻ v_Λ` for `y ∈ 'f_μ`, i.e.
`Eᵢ (y⁻ v_Λ) = (Eᵢ y)⁻ v_Λ` for the Verma-type operator `Eᵢ = LusztigF.vermaOp i cᵢ` with the
coefficients `cᵢ(μ) = [⟨i, Λ⟩ - ⟨μ, αᵢ^∨⟩]_{vᵢ}` (`QuantumGroup.qCoeff`,
`QuantumGroup.VermaModule.E_smul_toVerma`). These are the coefficients of the quantum Shapovalov
pairing `S(w, y) = ε(E_w y)` of the quantum Gabber–Kac proof (`LusztigF.vermaCoeff`), now for the
highest weight `Λ`.

Consequently (for an `X`-regular root datum):

* `y⁻ v_Λ` lies in the maximal submodule `M'_q(Λ)` iff `S(w, y) = 0` for all words `w`
  (`QuantumGroup.VermaModule.toVerma_mem_maxSubmodule_iff`): the radical of the Shapovalov pairing
  is the maximal submodule;
* for any submodule `N`, the weight space `(M_q(Λ) ⧸ N)^{Λ - ν}` is the image of `'f_ν`
  (`QuantumGroup.VermaModule.weightSpace_quotient_eq_map`), so
  `dim L_q(Λ)^{Λ - ν}` is the rank of the Shapovalov pairing on the words of weight `ν`
  (`QuantumGroup.VermaModule.finrank_weightSpace_irreducibleModule`);
* for dominant `Λ`, the images of the Serre products and of the words `a θᵢ^{⟨i,Λ⟩+1}` lie in
  `Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ` (`QuantumGroup.VermaModule.toVerma_mem_fPowSubmodule`).

The arguments are standard; the formulation through `'f` is ours.

## Main definitions

* `QuantumGroup.qCoeff R v Λ`: the coefficients `[⟨i, Λ⟩ - ⟨μ, αᵢ^∨⟩]_{vᵢ}`.

## Main results

* `QuantumGroup.VermaModule.E_smul_toVerma`, `QuantumGroup.VermaModule.plusHom_smul_toVerma`.
* `QuantumGroup.VermaModule.toVerma_mem_maxSubmodule_iff`.
* `QuantumGroup.VermaModule.weightSpace_quotient_eq_map`,
  `QuantumGroup.VermaModule.finrank_weightSpace_irreducibleModule`.
* `QuantumGroup.VermaModule.toVerma_mem_fPowSubmodule`.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 4–5.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.4.
-/

noncomputable section

open LusztigF FreeAlgebra Module

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}

omit [DecidableEq I] in
/-- `⟨i, Σₗ νₗ l'⟩ = Σₗ νₗ aᵢₗ = ⟨ν, αᵢ^∨⟩`. -/
lemma rootSum_coroot (R : D.RootDatum Y) (ν : I →₀ ℕ) (i : I) :
    R.rootSum ν (R.coroot i) = D.coPairing i ν := by
  rw [LusztigCartanDatum.RootDatum.rootSum, LusztigCartanDatum.coPairing, Finsupp.sum,
    Finsupp.sum, AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [AddMonoidHom.nsmul_apply, R.root_coroot, nsmul_eq_mul]

omit [DecidableEq I] in
/-- `vᵢ - vᵢ⁻¹ ≠ 0` if `v` is not a root of unity. -/
lemma qDenom_ne_zero {v : k} (hv0 : v ≠ 0) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    qDenom D v i ≠ 0 := by
  have hvd : v ^ D.d i ≠ 0 := pow_ne_zero _ hv0
  intro h0
  apply hv' (2 * D.d i) (by have := D.d_pos i; omega)
  rw [qDenom, sub_eq_zero] at h0
  rw [pow_mul', sq]
  nth_rewrite 2 [h0]
  exact mul_inv_cancel₀ hvd

variable [CharZero k] (R : D.RootDatum Y) (v : k) [NeZero v] (Λ : Y →+ ℤ)

/-- The quantum Verma coefficients `cᵢ(μ) = [⟨i, Λ⟩ - ⟨μ, αᵢ^∨⟩]_{vᵢ}`, as the images of the
Laurent polynomials `LusztigF.vermaCoeff` under `T ↦ v`. -/
def qCoeff (i : I) (μ : I →₀ ℕ) : k :=
  evalAt v (NeZero.ne v) (vermaCoeff D (fun i ↦ Λ (R.coroot i)) i μ)

variable {R v Λ}

namespace VermaModule

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

omit [CharZero k] [NeZero v] hv' in
lemma toVerma_ι_mul (j : I) (y : LusztigF k I) :
    toVerma R v Λ (ι k j * y) = F R v j • toVerma R v Λ y := by
  rw [toVerma_apply, toVerma_apply, map_mul, mul_smul, minusHom_θ]

/-- The raising operators on `M_q(Λ) = U⁻ v_Λ`: `Eᵢ (y⁻ v_Λ) = (Eᵢ y)⁻ v_Λ` for the Verma-type
operator `Eᵢ = LusztigF.vermaOp i cᵢ` with the coefficients `cᵢ = qCoeff R v Λ i`. -/
theorem E_smul_toVerma (i : I) (y : LusztigF k I) :
    E R v i • toVerma R v Λ y = toVerma R v Λ (vermaOp i (qCoeff R v Λ i) y) := by
  have hq := qDenom_ne_zero (D := D) (NeZero.ne v) hv' i
  induction y using induction_wordBasis with
  | zero => simp
  | add y z hy hz => rw [map_add, smul_add, hy, hz, map_add, map_add]
  | smul c y hy => rw [map_smul, smul_comm, hy, map_smul, map_smul]
  | word w =>
    induction w with
    | nil => rw [wordBasis_nil, toVerma_one, E_smul_hwv, vermaOp_one, map_zero]
    | cons j w ih =>
      rw [← ι_mul_wordBasis, toVerma_ι_mul, vermaOp_ι_mul, map_add, toVerma_ι_mul, ← ih,
        ← mul_smul, ← mul_smul]
      have h := E_mul_F_sub R v i j
      rw [sub_eq_iff_eq_add] at h
      rw [h, add_smul, add_comm]
      congr 1
      split_ifs with hij
      · subst hij
        rw [weightScale_wordBasis, map_smul]
        have hw := toVerma_mem_weightSpace (R := R) (v := v) (Λ := Λ)
          (wordBasis_mem_wordSpan (R := k) w)
        rw [smul_assoc, sub_smul, Kt_smul_of_mem_weightSpace hw,
          K_neg_ktilde_smul_of_mem_weightSpace hw, ← sub_smul, smul_smul, qCoeff,
          evalAt_vermaCoeff D (NeZero.ne v) hq]
        simp only [AddMonoidHom.sub_apply, rootSum_coroot]
      · rw [zero_smul, map_zero]

omit hv' in
lemma vermaWordOp_append {R' : Type*} [CommRing R'] (c : I → (I →₀ ℕ) → R') (w w' : List I)
    (y : FreeAlgebra R' I) :
    vermaWordOp c (w ++ w') y = vermaWordOp c w' (vermaWordOp c w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons i w ih => rw [List.cons_append, vermaWordOp_cons, ih, vermaWordOp_cons]

/-- The action of `x⁺` on `M_q(Λ)`, `x` a word: `x⁺ (y⁻ v_Λ) = (E_{rev x} y)⁻ v_Λ`. -/
theorem plusHom_smul_toVerma (w : List I) (y : LusztigF k I) :
    plusHom R v (wordBasis k I w) • toVerma R v Λ y =
      toVerma R v Λ (vermaWordOp (qCoeff R v Λ) w.reverse y) := by
  induction w generalizing y with
  | nil => simp
  | cons j w ih =>
    rw [← ι_mul_wordBasis, map_mul, mul_smul, ih, List.reverse_cons, vermaWordOp_append,
      vermaWordOp_cons, vermaWordOp_nil, Module.End.one_apply, ← E_smul_toVerma hv', plusHom_θ]

omit [CharZero k] in
/-- The `v_Λ`-coefficient of `x⁻ m` is `ε(x)` times that of `m`. -/
lemma hwCoord_minusHom_smul (a : LusztigF k I) (m : VermaModule R v Λ) :
    hwCoord Λ hv' (minusHom R v a • m) = LusztigF.counit a * hwCoord Λ hv' m := by
  obtain ⟨y, rfl⟩ := toVerma_surjective hv' m
  rw [show minusHom R v a • toVerma R v Λ y = toVerma R v Λ (a * y) by
    rw [toVerma_apply, toVerma_apply, map_mul, mul_smul], hwCoord_toVerma, hwCoord_toVerma,
    map_mul]

omit [CharZero k] in
/-- The `v_Λ`-coefficient of `K_μ m` is `v^{⟨μ, Λ⟩}` times that of `m`. -/
lemma hwCoord_K_smul (μ : Y) (m : VermaModule R v Λ) :
    hwCoord Λ hv' (K R v μ • m) = v ^ Λ μ * hwCoord Λ hv' m := by
  obtain ⟨y, rfl⟩ := toVerma_surjective hv' m
  have hy : y ∈ ⨆ ν, LusztigF.weightSpace k (I := I) ν := by
    rw [LusztigF.iSup_weightSpace]; trivial
  induction hy using Submodule.iSup_induction' with
  | mem ν y hy =>
    rw [toVerma_mem_weightSpace hy μ, map_smul, hwCoord_toVerma, smul_eq_mul]
    by_cases hν : ν = 0
    · subst hν; simp
    · rw [counit_eq_zero_of_mem hν hy, mul_zero, mul_zero]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add, map_add, hy, hz, map_add, mul_add]

variable (hR : R.IsXRegular)
include hR

/-- **The maximal submodule is the radical of the Shapovalov pairing.** For an `X`-regular root
datum, `y⁻ v_Λ ∈ M'_q(Λ)` iff `S(w, y) = ε(E_w y) = 0` for all words `w`. -/
theorem toVerma_mem_maxSubmodule_iff (y : LusztigF k I) :
    toVerma R v Λ y ∈ maxSubmodule R v Λ ↔ ∀ w, vermaForm (qCoeff R v Λ) w y = 0 := by
  rw [mem_maxSubmodule_iff hR hv']
  constructor
  · intro h w
    have := h (plusHom R v (wordBasis k I w.reverse))
    rwa [plusHom_smul_toVerma hv', List.reverse_reverse, hwCoord_toVerma] at this
  · intro h u
    induction mem_triangularSpan_of u (NeZero.ne v) using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨w, μ, w', rfl⟩ := hu
      have e : LusztigF.monomial k w' = wordBasis k I w' := by rw [wordBasis_apply]; rfl
      rw [mul_smul, mul_smul, e, plusHom_smul_toVerma hv', hwCoord_minusHom_smul hv',
        hwCoord_K_smul hv', hwCoord_toVerma]
      change _ * (_ * vermaForm _ _ y) = 0
      rw [h, mul_zero, mul_zero]
    | zero => simp
    | add x x' _ _ hx hx' => rw [add_smul, map_add, hx, hx', add_zero]
    | smul c x _ hx => rw [smul_assoc, map_smul, hx, smul_zero]

omit [CharZero k] in
/-- The weight spaces of a quotient of `M_q(Λ)`: `(M_q(Λ) ⧸ N)^{Λ - ν}` is the image of `'f_ν`
under `y ↦ y⁻ v_Λ`. -/
theorem weightSpace_quotient_eq_map (N : Submodule (QuantumGroup R v) (VermaModule R v Λ))
    (ν : I →₀ ℕ) :
    weightSpace R v (VermaModule R v Λ ⧸ N) (Λ - R.rootSum ν) =
      (LusztigF.weightSpace k ν).map ((N.mkQ.restrictScalars k) ∘ₗ toVerma R v Λ) := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := toVerma_surjective hv' m
    obtain ⟨g, hg, hgy⟩ := exists_zeroHom_smul_eq hR hv' ν y
    have := zeroHom_smul_of_mem_weightSpace hx g
    rw [hg, one_smul, ← Submodule.Quotient.mk_smul, hgy] at this
    exact ⟨_, LusztigF.weightProj_mem ν y, this⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro y hy μ
    change K R v μ • Submodule.Quotient.mk (p := N) (toVerma R v Λ y) = _
    rw [← Submodule.Quotient.mk_smul, toVerma_mem_weightSpace hy μ, Submodule.Quotient.mk_smul]
    rfl

/-- `dim L_q(Λ)^{Λ - ν}` is the rank of the quantum Shapovalov pairing on the words of
weight `ν`. -/
theorem finrank_weightSpace_irreducibleModule (ν : I →₀ ℕ) :
    finrank k (weightSpace R v (IrreducibleModule R v Λ) (Λ - R.rootSum ν)) =
      shapovalovRank (qCoeff R v Λ) ν := by
  rw [weightSpace_quotient_eq_map hv' hR, ← LinearMap.range_domRestrict, shapovalovRank]
  refine LinearMap.finrank_range_eq_of_ker_eq _ _ ?_
  ext y
  simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [toVerma_mem_maxSubmodule_iff hv' hR, shapovalovMap_eq_zero_iff _ y.2]

omit [CharZero k] hR in
/-- For `n = (⟨i, Λ⟩)ᵢ`, the images in `M_q(Λ)` of the quantum Serre products and of the words
`a θᵢ^{nᵢ+1}` lie in `Σᵢ U Fᵢ^{nᵢ+1} v_Λ`. -/
theorem toVerma_mem_fPowSubmodule {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ tildeSpan D (fun i ↦ v ^ D.d i) (fun i ↦ (Λ (R.coroot i)).toNat) ν) :
    toVerma R v Λ y ∈ fPowSubmodule R v Λ := by
  have h1 : serreSpan D (fun i ↦ v ^ D.d i) ν ≤
      ((fPowSubmodule R v Λ).restrictScalars k).comap (toVerma R v Λ) := fun z hz ↦ by
    have := (toVerma_eq_zero_iff (R := R) (Λ := Λ) hv' z).2
      (serreSpan_le_serreIdeal D (NeZero.ne v) hv' hz)
    change toVerma R v Λ z ∈ fPowSubmodule R v Λ
    rw [this]
    exact zero_mem _
  have h2 : powSpan k (fun i ↦ (Λ (R.coroot i)).toNat) ν ≤
      ((fPowSubmodule R v Λ).restrictScalars k).comap (toVerma R v Λ) := by
    rw [powSpan, Submodule.span_le]
    rintro _ ⟨⟨a, i⟩, -, rfl⟩
    change toVerma R v Λ (wordBasis k I (a ++ _)) ∈ fPowSubmodule R v Λ
    rw [wordBasis_append, toVerma_apply, map_mul, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    have e : minusHom R v (wordBasis k I (List.replicate ((Λ (R.coroot i)).toNat + 1) i)) =
        F R v i ^ ((Λ (R.coroot i)).toNat + 1) := by simp
    rw [e]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact (sup_le h1 h2) hy

end VermaModule

end QuantumGroup
