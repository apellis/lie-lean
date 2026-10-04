/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Recovery

/-!
# Lusztig's `Tᵢ` is an automorphism once the transformed Serre relations hold

For any node `i` of any Cartan datum (arbitrary rank, any field, any root-datum lattice), with
`v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0` and `[-aᵢⱼ]ᵢ! ≠ 0` for all `j ≠ i` (`BraidGeneric`), the candidate
images `Tᵢ(Eₗ)`, `Tᵢ(Fₗ)`, `Tᵢ(K_μ) = K_{sᵢ μ}` satisfy all defining relations of `U` except
possibly the neighbor-first transformed Serre relations `S(Tᵢ Eₗ, Tᵢ Eₘ) = 0`, `l ≠ i`
(`TransformedSerre`). Given those, `Tᵢ` is an algebra automorphism of `U` whose inverse is the
conjugate of `Tᵢ` by the product-reversal anti-automorphism.

## Main definitions and results

* `QuantumGroup.braidImage_relations`: the defining relations for the images, from
  `Mixed.lean`, `Diagonal.lean` and `Recovery.lean` (all in every degree) and the hypothesis.
* `QuantumGroup.braidHom`, `QuantumGroup.braidInvHom`: `Tᵢ` and its reversal conjugate.
* `QuantumGroup.braidHom_comp_braidInvHom`, `QuantumGroup.braidInvHom_comp_braidHom`.
* `QuantumGroup.braidEquiv`: `Tᵢ` as an algebra equivalence.

The earlier special constructions (`BraidAction/{A2,DoubleEdge,Star,...}.lean`) prove their
Serre relations case by case; here the remaining input is exactly `TransformedSerre`.

## References

Reconstructed from the quotient presentation (the statement that `Tᵢ` is an automorphism is
[Lus] Prop. 37.1.2, [Jan] Prop. 8.13, proved there differently).
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]

variable (R v) in
/-- The proposed images `Tᵢ(Eₗ)`: `braidEi` at `l = i`, `braidEj` otherwise. -/
def braidImageE (i l : I) : QuantumGroup R v := if l = i then braidEi R i else braidEj R v i l

variable (R v) in
/-- The proposed images `Tᵢ(Fₗ)`: `braidFi` at `l = i`, `braidFj` otherwise. -/
def braidImageF (i l : I) : QuantumGroup R v := if l = i then braidFi R i else braidFj R v i l

variable (R v) in
/-- The transformed quantum Serre relations `S_{1-aₗₘ}(Tᵢ Eₗ, Tᵢ Eₘ) = 0` (and for `F`) with
`l ≠ i`: the only defining relations of `U` whose preservation by `Tᵢ` is not proved here in
every degree (the centre-first ones, `l = i`, are `qSerre_braidEi_braidEj`). -/
structure TransformedSerre (i : I) : Prop where
  serre_E : ∀ l m, l ≠ m → l ≠ i → qSerre (v ^ D.d l) (1 - D.cartanMatrix l m).toNat
    (braidImageE R v i l) (braidImageE R v i m) = 0
  serre_F : ∀ l m, l ≠ m → l ≠ i → qSerre (v ^ D.d l) (1 - D.cartanMatrix l m).toNat
    (braidImageF R v i l) (braidImageF R v i m) = 0

/-- The generic parameter hypotheses at the node `i`: `vᵢ - vᵢ⁻¹ ≠ 0` and `[rⱼ]ᵢ! ≠ 0` for
all `j ≠ i`, `rⱼ = -aᵢⱼ`. -/
structure BraidGeneric (D : LusztigCartanDatum I) (v : k) (i : I) : Prop where
  sub_ne : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0
  qFactorial_ne : ∀ j, j ≠ i → qFactorial (v ^ D.d i) (negA D i j) ≠ 0

variable {i : I}

/-- All defining relations of `U` hold for the images of `Tᵢ`, given the transformed Serre
relations: relations (b)–(d) are proved here in every degree. -/
theorem braidImage_relations (hg : BraidGeneric D v i) (hS : TransformedSerre R v i) :
    Relations R v (braidImageE R v i) (braidImageF R v i) (braidK R v i) where
  K_mul_E μ l := by
    by_cases hl : l = i
    · simp only [braidImageE, hl, ↓reduceIte]
      exact braidK_mul_braidEi (R := R) (v := v) i μ
    · simpa [braidImageE, hl] using braidK_mul_braidEj (R := R) (NeZero.ne v) (Ne.symm hl) μ
  K_mul_F μ l := by
    by_cases hl : l = i
    · simp only [braidImageF, hl, ↓reduceIte]
      exact braidK_mul_braidFi (R := R) (v := v) i μ
    · simpa [braidImageF, hl] using braidK_mul_braidFj (R := R) (NeZero.ne v) (Ne.symm hl) μ
  E_mul_F l m := by
    by_cases hl : l = i <;> by_cases hm : m = i
    · simp only [braidImageE, braidImageF, hl, hm, ↓reduceIte]
      exact braidEi_mul_braidFi_sub (R := R) (v := v) i
    · rw [hl]
      simpa [braidImageE, braidImageF, hm, Ne.symm hm] using
        braidEi_mul_braidFj_sub (R := R) (v := v) (Ne.symm hm)
    · rw [hm]
      simpa [braidImageE, braidImageF, hl] using
        braidEj_mul_braidFi_sub (R := R) (v := v) (Ne.symm hl)
    · by_cases hlm : l = m
      · subst hlm
        simpa [braidImageE, braidImageF, hl] using
          braidEj_mul_braidFj_sub (R := R) (NeZero.ne v) (Ne.symm hl) hg.sub_ne
            (hg.qFactorial_ne l hl)
      · simp only [braidImageE, braidImageF, hl, hm, hlm, ↓reduceIte, sub_eq_zero]
        exact braidEj_commute_braidFj (NeZero.ne v) (Ne.symm hl) (Ne.symm hm) hlm
  serre_E l m hlm := by
    by_cases hl : l = i
    · rw [hl] at hlm ⊢
      simpa [braidImageE, Ne.symm hlm] using
        qSerre_braidEi_braidEj (R := R) (v := v) hlm hg.sub_ne
    · exact hS.serre_E l m hlm hl
  serre_F l m hlm := by
    by_cases hl : l = i
    · rw [hl] at hlm ⊢
      simpa [braidImageF, Ne.symm hlm] using
        qSerre_braidFi_braidFj (R := R) (v := v) hlm hg.sub_ne
    · exact hS.serre_F l m hlm hl

variable (hg : BraidGeneric D v i) (hS : TransformedSerre R v i)

/-- Lusztig's braid algebra homomorphism `Tᵢ = T''_{i,1}` on the quotient presentation, for any
node of any Cartan datum at which the transformed Serre relations hold. -/
def braidHom : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (braidImage_relations hg hS)

@[simp] theorem braidHom_E (l : I) : braidHom hg hS (E R v l) = braidImageE R v i l := lift_E _ l

@[simp] theorem braidHom_F (l : I) : braidHom hg hS (F R v l) = braidImageF R v i l := lift_F _ l

@[simp] theorem braidHom_K (μ : Y) : braidHom hg hS (K R v μ) = K R v (reflY R i μ) :=
  lift_K _ μ

/-- The inverse `Tᵢ⁻¹`, obtained by conjugating `Tᵢ` with the product-reversal
anti-automorphism. -/
def braidInvHom : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp ((braidHom hg hS).op.comp braidReversalOp)

theorem braidInvHom_apply (x : QuantumGroup R v) :
    braidInvHom hg hS x = braidReversal (braidHom hg hS (braidReversal x)) := rfl

/-- `Tᵢ ∘ Tᵢ⁻¹ = id`, checked on generators using the recovery theorems
`serreAux_braidEi_braidEj`, `serreAux_braidFi_braidFj`. -/
theorem braidHom_comp_braidInvHom :
    (braidHom hg hS).comp (braidInvHom hg hS) = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hl : l = i
    · rw [hl]
      simp [braidInvHom_apply, braidImageE, braidImageF, braidEi, braidFi, braidReversal_mul, Kt,
        ← mul_assoc, K_mul_K_neg]
    · have hli : i ≠ l := Ne.symm hl
      simp only [AlgHom.comp_apply, braidInvHom_apply, braidReversal_E, braidHom_E,
        braidImageE, hl, ↓reduceIte, braidReversal_braidEj, map_smul, map_serreAux,
        AlgHom.id_apply]
      simpa [braidImageE, hl] using
        serreAux_braidEi_braidEj (R := R) hli hg.sub_ne (hg.qFactorial_ne l hl)
  · by_cases hl : l = i
    · rw [hl]
      simp [braidInvHom_apply, braidImageE, braidImageF, braidEi, braidFi, braidReversal_mul, Kt,
        mul_assoc, K_mul_K_neg]
    · have hli : i ≠ l := Ne.symm hl
      simp only [AlgHom.comp_apply, braidInvHom_apply, braidReversal_F, braidHom_F,
        braidImageF, hl, ↓reduceIte, braidReversal_braidFj, map_smul, map_serreAux,
        AlgHom.id_apply]
      simpa [braidImageF, hl] using
        serreAux_braidFi_braidFj (R := R) hli hg.sub_ne (hg.qFactorial_ne l hl)
  · simp [braidInvHom_apply]

/-- `Tᵢ⁻¹ ∘ Tᵢ = id`, by conjugating `Tᵢ ∘ Tᵢ⁻¹ = id` with the involutive product reversal. -/
theorem braidInvHom_comp_braidHom :
    (braidInvHom hg hS).comp (braidHom hg hS) = AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun (braidHom_comp_braidInvHom hg hS) (braidReversal x))
  simpa only [AlgHom.comp_apply, braidInvHom_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- **Lusztig's braid automorphism** `Tᵢ` as an algebra equivalence, for any node `i` of any
Cartan datum and generic parameter, as soon as the transformed quantum Serre relations hold. -/
def braidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (braidHom hg hS) (braidInvHom hg hS) (braidHom_comp_braidInvHom hg hS)
    (braidInvHom_comp_braidHom hg hS)

end LieLean.QuantumGroup
