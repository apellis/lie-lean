/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Sl2.SimpleModule

/-!
# Lusztig's braid group automorphisms `Tᵢ`: the rank-one part

We use the variant `Tᵢ = T''_{i,1}` of [Lus] 37.1.3, which is the automorphism `Tᵢ` of
[Jan] 8.14:
* `Tᵢ(K_μ) = K_{sᵢ(μ)}`, `sᵢ(μ) = μ - ⟨μ, i'⟩ i`;
* `Tᵢ(Eᵢ) = -Fᵢ K̃ᵢ`, `Tᵢ(Fᵢ) = -K̃ᵢ⁻¹ Eᵢ`;
* `Tᵢ(Eⱼ) = Σ_{s=0}^{r} (-1)^s vᵢ^{-s} Eᵢ^{(r-s)} Eⱼ Eᵢ^{(s)}`,
  `Tᵢ(Fⱼ) = Σ_{s=0}^{r} (-1)^s vᵢ^{s} Fᵢ^{(s)} Fⱼ Fᵢ^{(r-s)}` for `j ≠ i`, `r = -aᵢⱼ`.

This file treats the part of the construction that involves only the index `i`:
* the reflection `sᵢ` of `Y` and `μ ↦ K_{sᵢ(μ)}` (`QuantumGroup.reflY`, `QuantumGroup.braidK`);
* the relations (a)–(d) of `U` between `Tᵢ(K_μ)`, `Tᵢ(Eᵢ)`, `Tᵢ(Fᵢ)`
  (`QuantumGroup.braidK_mul_braidEi` etc.), and likewise for the candidate inverse
  `Eᵢ ↦ -K̃ᵢ⁻¹ Fᵢ`, `Fᵢ ↦ -Eᵢ K̃ᵢ`;
* for a root datum of rank one (`I = Unit`, e.g. `U_v(𝔰𝔩₂)`) this gives the algebra automorphism
  `Tᵢ` with explicit inverse (`QuantumGroup.rankOneBraidEquiv`).

The images `Tᵢ(Eⱼ)`, `Tᵢ(Fⱼ)` for `j ≠ i` and the relations involving them are in
`QuantumGroup/BraidAction/Mixed.lean`.

## Main definitions

* `QuantumGroup.reflY R i`: `sᵢ(μ) = μ - ⟨μ, i'⟩ i`.
* `QuantumGroup.braidK R v i`: `μ ↦ K_{sᵢ(μ)}`.
* `QuantumGroup.rankOneBraidEquiv`: `Tᵢ` as an algebra automorphism for rank-one root data.

## Main results

* `QuantumGroup.braidK_mul_braidEi`, `QuantumGroup.braidK_mul_braidFi`,
  `QuantumGroup.braidEi_mul_braidFi_sub`: the relations of `U` between `Tᵢ(K_μ)`, `Tᵢ(Eᵢ)`,
  `Tᵢ(Fᵢ)`, and their analogues for the inverse.
* `QuantumGroup.rankOneBraidInv_comp_rankOneBraid`, `rankOneBraid_comp_rankOneBraidInv`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §37.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 8.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-! ### The reflection `sᵢ` of `Y` -/

omit [DecidableEq I] in
variable {v} in
/-- The simple reflection `sᵢ(μ) = μ - ⟨μ, i'⟩ i` of the coweight lattice `Y`. -/
def reflY (i : I) : Y →+ Y := AddMonoidHom.id Y - (zmultiplesHom Y (R.coroot i)).comp (R.root i)

variable {R}

omit [DecidableEq I] in
lemma reflY_apply (i : I) (μ : Y) : reflY R i μ = μ - R.root i μ • R.coroot i := rfl

omit [DecidableEq I] in
lemma root_reflY (i j : I) (μ : Y) :
    R.root j (reflY R i μ) = R.root j μ - R.root i μ * D.cartanMatrix i j := by
  rw [reflY_apply, map_sub, map_zsmul, R.root_coroot, smul_eq_mul]

omit [DecidableEq I] in
@[simp] lemma root_reflY_self (i : I) (μ : Y) : R.root i (reflY R i μ) = -R.root i μ := by
  rw [root_reflY, D.cartanMatrix_self]; ring

omit [DecidableEq I] in
@[simp] lemma reflY_reflY (i : I) (μ : Y) : reflY R i (reflY R i μ) = μ := by
  rw [reflY_apply (μ := reflY R i μ), root_reflY_self, reflY_apply, neg_smul, sub_neg_eq_add,
    sub_add_cancel]

omit [DecidableEq I] in
@[simp] lemma reflY_ktilde (i : I) : reflY R i (ktilde R i) = -ktilde R i := by
  rw [reflY_apply, root_ktilde, D.cartanMatrix_self, ktilde, ← natCast_zsmul]
  module

omit [DecidableEq I] in
@[simp] lemma reflY_neg_ktilde (i : I) : reflY R i (-ktilde R i) = ktilde R i := by
  rw [map_neg, reflY_ktilde, neg_neg]

variable (R) in
/-- `μ ↦ K_{sᵢ(μ)}`, the value of `Tᵢ` on `U⁰`. -/
def braidK (i : I) : Multiplicative Y →* QuantumGroup R v :=
  (KHom R v).comp (reflY R i).toMultiplicative

@[simp] lemma braidK_apply (i : I) (μ : Y) :
    braidK R v i (.ofAdd μ) = K R v (reflY R i μ) := rfl

/-! ### Commutation of `K̃ᵢ^{±1}` with `Eᵢ`, `Fᵢ` -/

section Rank

variable {v}

omit [DecidableEq I] in
lemma zpow_root_neg_ktilde_self (i : I) :
    v ^ R.root i (-ktilde R i) = ((v ^ D.d i) ^ 2)⁻¹ := by
  rw [map_neg, zpow_neg, zpow_root_ktilde_self]

lemma Kt_mul_E (i : I) : Kt R v i * E R v i = (v ^ D.d i) ^ 2 • (E R v i * Kt R v i) := by
  rw [Kt, K_mul_E, zpow_root_ktilde_self]

lemma K_neg_ktilde_mul_E (i : I) :
    K R v (-ktilde R i) * E R v i = ((v ^ D.d i) ^ 2)⁻¹ • (E R v i * K R v (-ktilde R i)) := by
  rw [K_mul_E, zpow_root_neg_ktilde_self]

lemma Kt_mul_K_neg (i : I) : Kt R v i * K R v (-ktilde R i) = 1 := K_mul_K_neg R v _

lemma K_neg_mul_Kt (i : I) : K R v (-ktilde R i) * Kt R v i = 1 := K_neg_mul_K R v _

/-- `K̃ᵢ⁻¹ (Eᵢ Fᵢ) K̃ᵢ = Eᵢ Fᵢ`. -/
lemma K_neg_mul_E_mul_F_mul_Kt (hv : v ≠ 0) (i : I) :
    K R v (-ktilde R i) * (E R v i * F R v i) * Kt R v i = E R v i * F R v i := by
  have hq : (v ^ D.d i) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hv)
  rw [← mul_assoc, K_neg_ktilde_mul_E, smul_mul_assoc, mul_assoc, K_neg_ktilde_mul_F,
    mul_smul_comm, smul_smul, inv_mul_cancel₀ hq, one_smul, mul_assoc, mul_assoc,
    K_neg_mul_Kt, mul_one]

/-- `K̃ᵢ⁻¹ (Fᵢ Eᵢ) K̃ᵢ = Fᵢ Eᵢ`. -/
lemma K_neg_mul_F_mul_E_mul_Kt (hv : v ≠ 0) (i : I) :
    K R v (-ktilde R i) * (F R v i * E R v i) * Kt R v i = F R v i * E R v i := by
  have hq : (v ^ D.d i) ^ 2 * ((v ^ D.d i) ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hv))
  rw [← mul_assoc, K_neg_ktilde_mul_F, smul_mul_assoc, mul_assoc, K_neg_ktilde_mul_E,
    mul_smul_comm, smul_smul, hq, one_smul, mul_assoc, mul_assoc, K_neg_mul_Kt, mul_one]

end Rank

/-! ### The relations involving only `i` -/

section OnlyI

variable {v} [NeZero v] (i : I)

variable (R) in
/-- `Tᵢ(Eᵢ) = -Fᵢ K̃ᵢ`. -/
abbrev braidEi : QuantumGroup R v := -(F R v i * Kt R v i)

variable (R) in
/-- `Tᵢ(Fᵢ) = -K̃ᵢ⁻¹ Eᵢ`. -/
abbrev braidFi : QuantumGroup R v := -(K R v (-ktilde R i) * E R v i)

variable (R) in
/-- `Tᵢ⁻¹(Eᵢ) = -K̃ᵢ⁻¹ Fᵢ`. -/
abbrev braidInvEi : QuantumGroup R v := -(K R v (-ktilde R i) * F R v i)

variable (R) in
/-- `Tᵢ⁻¹(Fᵢ) = -Eᵢ K̃ᵢ`. -/
abbrev braidInvFi : QuantumGroup R v := -(E R v i * Kt R v i)

omit [NeZero v] in
theorem braidK_mul_braidEi (μ : Y) :
    braidK R v i (.ofAdd μ) * braidEi R i =
      v ^ R.root i μ • (braidEi R i * braidK R v i (.ofAdd μ)) := by
  rw [braidK_apply, mul_neg, ← mul_assoc, K_mul_F, root_reflY_self, neg_neg, smul_mul_assoc,
    mul_assoc, K_comm, ← mul_assoc, neg_mul, smul_neg, mul_assoc]

omit [NeZero v] in
theorem braidK_mul_braidFi (μ : Y) :
    braidK R v i (.ofAdd μ) * braidFi R i =
      v ^ (-R.root i μ) • (braidFi R i * braidK R v i (.ofAdd μ)) := by
  rw [braidK_apply, mul_neg, ← mul_assoc, K_comm, mul_assoc, K_mul_E, root_reflY_self,
    mul_smul_comm, ← mul_assoc, neg_mul, smul_neg, mul_assoc]

omit [NeZero v] in
theorem braidK_mul_braidInvEi (μ : Y) :
    braidK R v i (.ofAdd μ) * braidInvEi R i =
      v ^ R.root i μ • (braidInvEi R i * braidK R v i (.ofAdd μ)) := by
  rw [braidK_apply, mul_neg, ← mul_assoc, K_comm, mul_assoc, K_mul_F, root_reflY_self, neg_neg,
    mul_smul_comm, ← mul_assoc, neg_mul, smul_neg, mul_assoc]

omit [NeZero v] in
theorem braidK_mul_braidInvFi (μ : Y) :
    braidK R v i (.ofAdd μ) * braidInvFi R i =
      v ^ (-R.root i μ) • (braidInvFi R i * braidK R v i (.ofAdd μ)) := by
  rw [braidK_apply, mul_neg, ← mul_assoc, K_mul_E, root_reflY_self, smul_mul_assoc,
    mul_assoc, K_comm, ← mul_assoc, neg_mul, smul_neg, mul_assoc]

/-- The relation (d) for `Tᵢ(Eᵢ)`, `Tᵢ(Fᵢ)`. -/
theorem braidEi_mul_braidFi_sub :
    braidEi R i * braidFi R i - braidFi R i * braidEi R i =
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ •
        (braidK R v i (.ofAdd (ktilde R i)) - braidK R v i (.ofAdd (-ktilde R i))) := by
  have hv := NeZero.ne v
  have h1 : braidEi R i * braidFi R i = F R v i * E R v i := by
    rw [neg_mul_neg, mul_assoc, ← mul_assoc (Kt R v i), Kt_mul_K_neg, one_mul]
  have h2 : braidFi R i * braidEi R i = E R v i * F R v i := by
    rw [neg_mul_neg, ← K_neg_mul_E_mul_F_mul_Kt hv i]
    simp only [mul_assoc]
  have h := E_mul_F_sub R v i i
  simp only [↓reduceIte] at h
  rw [h1, h2, braidK_apply, braidK_apply, reflY_ktilde, reflY_neg_ktilde, ← neg_sub, h,
    ← smul_neg, neg_sub]

/-- The relation (d) for `Tᵢ⁻¹(Eᵢ)`, `Tᵢ⁻¹(Fᵢ)`. -/
theorem braidInvEi_mul_braidInvFi_sub :
    braidInvEi R i * braidInvFi R i - braidInvFi R i * braidInvEi R i =
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ •
        (braidK R v i (.ofAdd (ktilde R i)) - braidK R v i (.ofAdd (-ktilde R i))) := by
  have hv := NeZero.ne v
  have h1 : braidInvEi R i * braidInvFi R i = F R v i * E R v i := by
    rw [neg_mul_neg, ← K_neg_mul_F_mul_E_mul_Kt hv i]
    simp only [mul_assoc]
  have h2 : braidInvFi R i * braidInvEi R i = E R v i * F R v i := by
    rw [neg_mul_neg, mul_assoc, ← mul_assoc (Kt R v i), Kt_mul_K_neg, one_mul]
  have h := E_mul_F_sub R v i i
  simp only [↓reduceIte] at h
  rw [h1, h2, braidK_apply, braidK_apply, reflY_ktilde, reflY_neg_ktilde, ← neg_sub, h,
    ← smul_neg, neg_sub]

end OnlyI

/-! ### Rank one: `Tᵢ` is an algebra automorphism -/

section RankOne

variable {D₁ : LusztigCartanDatum Unit} (R₁ : D₁.RootDatum Y) {v} [NeZero v]

/-- For a rank-one root datum, `Tᵢ` respects the defining relations of `U`. -/
theorem rankOneBraid_relations :
    Relations R₁ v (fun _ ↦ braidEi R₁ ()) (fun _ ↦ braidFi R₁ ()) (braidK R₁ v ()) where
  K_mul_E μ i := by obtain rfl := Subsingleton.elim i (); exact braidK_mul_braidEi (R := R₁) () μ
  K_mul_F μ i := by obtain rfl := Subsingleton.elim i (); exact braidK_mul_braidFi (R := R₁) () μ
  E_mul_F i j := by
    obtain rfl := Subsingleton.elim i ()
    obtain rfl := Subsingleton.elim j ()
    simp only [↓reduceIte]
    exact braidEi_mul_braidFi_sub (R := R₁) ()
  serre_E i j h := absurd (Subsingleton.elim i j) h
  serre_F i j h := absurd (Subsingleton.elim i j) h

/-- For a rank-one root datum, `Tᵢ⁻¹` respects the defining relations of `U`. -/
theorem rankOneBraidInv_relations :
    Relations R₁ v (fun _ ↦ braidInvEi R₁ ()) (fun _ ↦ braidInvFi R₁ ()) (braidK R₁ v ()) where
  K_mul_E μ i := by obtain rfl := Subsingleton.elim i (); exact braidK_mul_braidInvEi (R := R₁) () μ
  K_mul_F μ i := by obtain rfl := Subsingleton.elim i (); exact braidK_mul_braidInvFi (R := R₁) () μ
  E_mul_F i j := by
    obtain rfl := Subsingleton.elim i ()
    obtain rfl := Subsingleton.elim j ()
    simp only [↓reduceIte]
    exact braidInvEi_mul_braidInvFi_sub (R := R₁) ()
  serre_E i j h := absurd (Subsingleton.elim i j) h
  serre_F i j h := absurd (Subsingleton.elim i j) h

/-- Lusztig's automorphism `Tᵢ = T''_{i,1}` ([Lus] 37.1.3, [Jan] 8.14) of a
quantum group of rank one (e.g. `U_v(𝔰𝔩₂)`): `E ↦ -F K̃`, `F ↦ -K̃⁻¹ E`, `K_μ ↦ K_{s(μ)}`. -/
def rankOneBraid : QuantumGroup R₁ v →ₐ[k] QuantumGroup R₁ v := lift (rankOneBraid_relations R₁)

/-- The inverse of `rankOneBraid`: `E ↦ -K̃⁻¹ F`, `F ↦ -E K̃`, `K_μ ↦ K_{s(μ)}`. -/
def rankOneBraidInv : QuantumGroup R₁ v →ₐ[k] QuantumGroup R₁ v :=
  lift (rankOneBraidInv_relations R₁)

@[simp] lemma rankOneBraid_E (i : Unit) : rankOneBraid R₁ (E R₁ v i) = -(F R₁ v () * Kt R₁ v ()) :=
  lift_E _ i

@[simp] lemma rankOneBraid_F (i : Unit) :
    rankOneBraid R₁ (F R₁ v i) = -(K R₁ v (-ktilde R₁ ()) * E R₁ v ()) :=
  lift_F _ i

@[simp] lemma rankOneBraid_K (μ : Y) : rankOneBraid R₁ (K R₁ v μ) = K R₁ v (reflY R₁ () μ) :=
  lift_K _ μ

@[simp] lemma rankOneBraidInv_E (i : Unit) :
    rankOneBraidInv R₁ (E R₁ v i) = -(K R₁ v (-ktilde R₁ ()) * F R₁ v ()) :=
  lift_E _ i

@[simp] lemma rankOneBraidInv_F (i : Unit) :
    rankOneBraidInv R₁ (F R₁ v i) = -(E R₁ v () * Kt R₁ v ()) :=
  lift_F _ i

@[simp] lemma rankOneBraidInv_K (μ : Y) :
    rankOneBraidInv R₁ (K R₁ v μ) = K R₁ v (reflY R₁ () μ) :=
  lift_K _ μ

theorem rankOneBraidInv_comp_rankOneBraid :
    (rankOneBraidInv R₁).comp (rankOneBraid R₁) = AlgHom.id k (QuantumGroup R₁ v) := by
  refine hom_ext (fun i ↦ ?_) (fun i ↦ ?_) (fun μ ↦ ?_)
  · obtain rfl := Subsingleton.elim i ()
    simp only [AlgHom.comp_apply, rankOneBraid_E, map_neg, map_mul, rankOneBraidInv_F, Kt,
      rankOneBraidInv_K, reflY_ktilde, neg_mul, neg_neg, AlgHom.id_apply, mul_assoc,
      K_mul_K_neg, mul_one]
  · obtain rfl := Subsingleton.elim i ()
    simp only [AlgHom.comp_apply, rankOneBraid_F, map_neg, map_mul, rankOneBraidInv_E,
      rankOneBraidInv_K, reflY_ktilde, mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc,
      K_mul_K_neg, one_mul]
  · simp

theorem rankOneBraid_comp_rankOneBraidInv :
    (rankOneBraid R₁).comp (rankOneBraidInv R₁) = AlgHom.id k (QuantumGroup R₁ v) := by
  refine hom_ext (fun i ↦ ?_) (fun i ↦ ?_) (fun μ ↦ ?_)
  · obtain rfl := Subsingleton.elim i ()
    simp only [AlgHom.comp_apply, rankOneBraidInv_E, map_neg, map_mul, rankOneBraid_F,
      rankOneBraid_K, reflY_ktilde, mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc,
      K_mul_K_neg, one_mul]
  · obtain rfl := Subsingleton.elim i ()
    simp only [AlgHom.comp_apply, rankOneBraidInv_F, map_neg, map_mul, rankOneBraid_E, Kt,
      rankOneBraid_K, reflY_ktilde, neg_mul, neg_neg, AlgHom.id_apply, mul_assoc,
      K_mul_K_neg, mul_one]
  · simp

/-- **Lusztig's automorphism `Tᵢ` in rank one** ([Lus] 37.1.3, [Jan] 8.14), as an
algebra automorphism of `U`, with inverse `E ↦ -K̃⁻¹ F`, `F ↦ -E K̃`, `K_μ ↦ K_{s(μ)}`. -/
def rankOneBraidEquiv : QuantumGroup R₁ v ≃ₐ[k] QuantumGroup R₁ v :=
  AlgEquiv.ofAlgHom (rankOneBraid R₁) (rankOneBraidInv R₁) (rankOneBraid_comp_rankOneBraidInv R₁)
    (rankOneBraidInv_comp_rankOneBraid R₁)

@[simp] lemma reflY_sl2 (μ : ℤ) : reflY sl2RootDatum () μ = -μ := by
  rw [reflY_apply, sl2RootDatum_root]
  simp [sl2RootDatum]
  ring

/-- Lusztig's automorphism `T` of `U_v(𝔰𝔩₂)`: `E ↦ -F K`, `F ↦ -K⁻¹ E`, `K ↦ K⁻¹`
([Jan] 8.14). -/
def Sl2.braidEquiv : Sl2 v ≃ₐ[k] Sl2 v := rankOneBraidEquiv sl2RootDatum

end RankOne

end LieLean.QuantumGroup
