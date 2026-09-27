/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterDenominator
import LieLean.Algebra.Lie.KacMoody.CharacterWeyl
import LieLean.Algebra.Lie.KacMoody.InvariantForm
import LieLean.Algebra.Lie.KacMoody.WeylLength

/-!
# Anti-invariance of `e^ρ R` under the Weyl group

Let `A` be a generalized Cartan matrix, `K` a field of characteristic zero, `W` the Weyl group
with its length function `ℓ` (`Matrix.Realization.coxeterSystem`), and
`R = ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α}` the denominator (`KacMoodyAlgebra.denominator`). The Weyl
group does not act on the algebra `ℰ` of formal characters, but it acts on coefficient functions,
and we say that `c ∈ ℰ` is `W`-anti-invariant if `c_{w μ} = (-1)^{ℓ(w)} c_μ` for all `w ∈ W` and
`μ ∈ 𝔥*`. We prove ([Kac] §10.2 (check)) that `e^ρ R` is `W`-anti-invariant, where `ρ` is any
element with `⟨ρ, αᵢ^∨⟩ = 1` (`Matrix.Realization.rho`), and deduce that so is `e^ρ R ch V` for
every integrable module `V` in the category `𝒪`.

## Proof

It suffices to treat the fundamental reflections `rᵢ`, since `ℓ(rᵢ w) = ℓ(w) ± 1`. Recall that
`R = ∑_S (-1)^{|S|} e^{-wt S}`, the sum running over the finite sets `S` of indices of a basis of
`𝔫₋` consisting of root vectors (`NegRootIndex`). Since `rᵢ` permutes `Δ₊ \ {αᵢ}` preserving
multiplicities ([Kac] Lemma 3.7 (check), `KacMoodyAlgebra.reflection_mem_posWeights`,
`KacMoodyAlgebra.rank_rootSpace_weylGroup`) and `mult αᵢ = 1`, there is a permutation `σ` of the
index set with `root (σ x) = rᵢ (root x)` for `root x ≠ αᵢ`, fixing the unique index `xᵢ` of root
`αᵢ`. The bijection `Φ(S) = σ(S) ∆ {xᵢ}` of the finite sets of indices satisfies
`wt Φ(S) = rᵢ (wt S) + αᵢ` and `|Φ(S)| ≡ |S| + 1 (mod 2)`. Hence the coefficients of `R` satisfy
`R_{rᵢ μ - αᵢ} = -R_μ`, and since `rᵢ ρ = ρ - αᵢ`, `(e^ρ R)_{rᵢ μ} = -(e^ρ R)_μ`. This is the
coefficientwise form of Kac's argument `rᵢ(e^ρ R) = e^{ρ - αᵢ} (1 - e^{αᵢ}) ∏_{α ≠ αᵢ} ⋯
= -e^ρ R`.

## Main definitions

* `Matrix.Realization.CharacterRing.IsWeylAntiInvariant`: `c_{w μ} = (-1)^{ℓ(w)} c_μ`.

## Main results

* `Matrix.Realization.CharacterRing.isWeylAntiInvariant_of_reflection`: it suffices to check
  anti-invariance under the fundamental reflections.
* `Matrix.Realization.CharacterRing.IsWeylAntiInvariant.mul`: the product of a `W`-anti-invariant
  and a `W`-invariant element of `ℰ` is `W`-anti-invariant.
* `Matrix.Realization.KacMoodyAlgebra.coeffAt_denominator_reflection`: `R_{rᵢ μ - αᵢ} = -R_μ`.
* `Matrix.Realization.KacMoodyAlgebra.isWeylAntiInvariant_exp_rho_mul_denominator`: `e^ρ R` is
  `W`-anti-invariant ([Kac] §10.2 (check)).
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.isWeylAntiInvariant_exp_rho_mul_character`:
  `e^ρ R ch V` is `W`-anti-invariant for `V` integrable in `𝒪` ([Kac] §10.4 (check)).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.7, §10.2–10.4.
-/

open Module HahnSeries

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

namespace CharacterRing

variable {R : Type*} [CommRing R]

/-- An element `c ∈ ℰ` is `W`-anti-invariant if `c_{w μ} = (-1)^{ℓ(w)} c_μ` for all `w ∈ W` and
`μ ∈ 𝔥*` ([Kac] §10.2 (check)). -/
def IsWeylAntiInvariant (c : P.CharacterRing R) : Prop :=
  ∀ w : P.weylGroup hA, ∀ μ, c.coeffAt ((w : Dual K H ≃ₗ[K] Dual K H) μ) =
    (-1) ^ (P.coxeterSystem hA).length w * c.coeffAt μ

variable {P hA}

/-- An element of `ℰ` is `W`-anti-invariant as soon as `c_{rᵢ μ} = -c_μ` for all fundamental
reflections `rᵢ`. -/
theorem isWeylAntiInvariant_of_reflection {c : P.CharacterRing R}
    (hc : ∀ i μ, c.coeffAt (P.reflection hA i μ) = -c.coeffAt μ) :
    c.IsWeylAntiInvariant P hA := by
  intro w
  induction w using (P.coxeterSystem hA).simple_induction_left with
  | one => intro μ; simp
  | mul_simple_left w i ih =>
    intro μ
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple, hc, ih]
    rcases (P.coxeterSystem hA).length_simple_mul w i with h | h
    · rw [h, pow_succ]; ring
    · rw [← h, pow_succ]; ring

/-- The product of a `W`-anti-invariant and a `W`-invariant element of `ℰ` is `W`-anti-invariant.
(The sum `∑_ν c_ν d_{μ - ν}` is reindexed by `ν ↦ w ν`.) -/
theorem IsWeylAntiInvariant.mul {c d : P.CharacterRing R} (hc : c.IsWeylAntiInvariant P hA)
    (hd : d.IsWeylInvariant P hA) : (c * d).IsWeylAntiInvariant P hA := by
  intro w μ
  set w' : Dual K H ≃ₗ[K] Dual K H := (w : Dual K H ≃ₗ[K] Dual K H)
  rw [coeff_mul, coeff_mul, ← finsum_comp_equiv w'.toEquiv]
  have h : ∀ ν, c.coeffAt (w'.toEquiv ν) * d.coeffAt (w' μ - w'.toEquiv ν) =
      (-1) ^ (P.coxeterSystem hA).length w * (c.coeffAt ν * d.coeffAt (μ - ν)) := by
    intro ν
    rw [LinearEquiv.coe_toEquiv, hc w ν, ← map_sub, hd w' w.2 (μ - ν)]
    ring
  simp_rw [h]
  rcases neg_one_pow_eq_or R ((P.coxeterSystem hA).length w) with h1 | h1
  · simp [h1]
  · simp [h1, finsum_neg_distrib]

end CharacterRing

namespace KacMoodyAlgebra

open CharacterRing WeightOrd

variable {P}

/-! ### The coefficients of the denominator -/

open Classical in
/-- The coefficients of the denominator: `R_μ = ∑_{S, -wt S = μ} (-1)^{|S|}`. -/
lemma coeffAt_denominator (μ : Dual K H) :
    (denominator P).coeffAt μ =
      ∑ᶠ S : Finset (NegRootIndex P), if -finsetWt P S = μ then (-1) ^ S.card else 0 := by
  classical
  rw [coeffAt, denominator, SummableFamily.coeff_hsum]
  refine finsum_congr fun S ↦ ?_
  simp only [denominatorFamily, SummableFamily.coe_mk, coeff_single]
  exact if_congr ⟨fun h ↦ ((toWeightOrd P).injective h).symm, fun h ↦ by rw [h]⟩ rfl rfl

/-! ### The index of the simple root `αᵢ` -/

omit [CharZero K] in
lemma NegRootIndex.root_mem_posWeights (x : NegRootIndex P) : x.root ∈ P.posWeights := x.1.2

/-- The positive root attached to an index is a root. -/
lemma NegRootIndex.root_mem_roots (x : NegRootIndex P) : x.root ∈ roots P := by
  refine ⟨fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ x.root_mem_posWeights), fun hbot ↦ ?_⟩
  have hj : x.2.val < finrank K (rootSpace P x.root) :=
    lt_of_lt_of_eq x.2.isLt (finrank_rootSpace_neg_eq P x.root_mem_posWeights)
  rw [hbot, finrank_bot] at hj
  exact Nat.not_lt_zero _ hj

omit [CharZero K] in
/-- Two indices with the same root and the same position in the basis of the root space are
equal. -/
lemma NegRootIndex.ext {x y : NegRootIndex P} (h : x.root = y.root) (hj : x.2.val = y.2.val) :
    x = y := by
  obtain ⟨⟨α, hα⟩, j⟩ := x
  obtain ⟨⟨β, hβ⟩, k⟩ := y
  change α = β at h
  subst h
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hj))

variable (P) in
/-- The unique index `xᵢ` of the basis of `𝔫₋` whose root is the simple root `αᵢ`. -/
def simpleIndex (i : ι) : NegRootIndex P :=
  ⟨⟨P.root i, P.root_mem_posWeights i⟩, ⟨0, by
    change 0 < finrank K (rootSpace P (-P.root i))
    rw [finrank_rootSpace_neg_root]
    exact one_pos⟩⟩

@[simp] lemma root_simpleIndex (i : ι) : (simpleIndex P i).root = P.root i := rfl

/-- `xᵢ` is the only index whose root is `αᵢ`, since `mult αᵢ = 1`. -/
lemma eq_simpleIndex {x : NegRootIndex P} {i : ι} (hx : x.root = P.root i) :
    x = simpleIndex P i := by
  have hj : x.2.val < 1 :=
    lt_of_lt_of_eq x.2.isLt (by rw [← finrank_rootSpace_neg_root P i, ← hx]; rfl)
  exact NegRootIndex.ext hx (by change x.2.val = 0; omega)

lemma root_eq_iff_eq_simpleIndex {x : NegRootIndex P} {i : ι} :
    x.root = P.root i ↔ x = simpleIndex P i :=
  ⟨eq_simpleIndex, fun h ↦ h ▸ rfl⟩

/-! ### The action of `rᵢ` on indices -/

omit [DecidableEq ι] in
lemma reflection_ne_root (i : ι) {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    P.reflection hA i μ ≠ P.root i := by
  intro h
  have : μ = -P.root i := by rw [← P.reflection_reflection hA i μ, h, reflection_root_self]
  rw [this] at hμ
  exact Set.disjoint_left.mp P.disjoint_posWeights_negWeights hμ
    ((neg_mem_negWeights_iff P).mpr (P.root_mem_posWeights i))

lemma reflection_root_mem_posWeights (i : ι) (x : NegRootIndex P) (hx : ¬x.root = P.root i) :
    P.reflection hA i x.root ∈ P.posWeights :=
  reflection_mem_posWeights P hA x.root_mem_roots x.root_mem_posWeights hx

/-- `mult (rᵢ α) = mult α`. -/
lemma finrank_rootSpace_neg_reflection (i : ι) (μ : Dual K H) :
    finrank K (rootSpace P (-P.reflection hA i μ)) = finrank K (rootSpace P (-μ)) := by
  rw [← map_neg]
  simp only [Module.finrank]
  rw [rank_rootSpace_weylGroup P hA (P.reflection_mem_weylGroup hA i)]

/-- The action of `rᵢ` on the indices whose root is not `αᵢ`. -/
def reflectIndex (i : ι) (x : {x : NegRootIndex P // ¬x.root = P.root i}) :
    {x : NegRootIndex P // ¬x.root = P.root i} :=
  ⟨⟨⟨P.reflection hA i x.1.root, reflection_root_mem_posWeights hA i x.1 x.2⟩,
    Fin.cast (finrank_rootSpace_neg_reflection hA i x.1.root).symm x.1.2⟩,
    reflection_ne_root hA i x.1.root_mem_posWeights⟩

lemma root_reflectIndex (i : ι) (x : {x : NegRootIndex P // ¬x.root = P.root i}) :
    (reflectIndex hA i x).1.root = P.reflection hA i x.1.root := rfl

lemma val_reflectIndex (i : ι) (x : {x : NegRootIndex P // ¬x.root = P.root i}) :
    (reflectIndex hA i x).1.2.val = x.1.2.val :=
  Fin.val_cast (finrank_rootSpace_neg_reflection hA i x.1.root).symm x.1.2

lemma reflectIndex_reflectIndex (i : ι) (x : {x : NegRootIndex P // ¬x.root = P.root i}) :
    reflectIndex hA i (reflectIndex hA i x) = x := by
  refine Subtype.ext (NegRootIndex.ext ?_ ?_)
  · rw [root_reflectIndex, root_reflectIndex, reflection_reflection]
  · rw [val_reflectIndex, val_reflectIndex]

open Classical in
/-- A permutation of the index set lifting `rᵢ` on the indices whose root is not `αᵢ`, and
fixing `xᵢ`. -/
def reflectPerm (i : ι) : Equiv.Perm (NegRootIndex P) :=
  Equiv.Perm.subtypeCongr (Equiv.refl _)
    (Function.Involutive.toPerm _ (reflectIndex_reflectIndex hA i))

lemma reflectPerm_simpleIndex (i : ι) : reflectPerm hA i (simpleIndex P i) = simpleIndex P i := by
  classical
  rw [reflectPerm,
    Equiv.Perm.subtypeCongr.left_apply (a := simpleIndex P i) _ _ (root_simpleIndex i)]
  rfl

lemma root_reflectPerm (i : ι) (x : NegRootIndex P) :
    (reflectPerm hA i x).root = P.reflection hA i x.root +
      if x = simpleIndex P i then (2 : ℕ) • P.root i else 0 := by
  classical
  split_ifs with hx
  · rw [hx, reflectPerm_simpleIndex, root_simpleIndex, reflection_root_self]
    simp only [two_nsmul]
    abel
  · rw [add_zero, ← root_eq_iff_eq_simpleIndex] at *
    rw [reflectPerm, Equiv.Perm.subtypeCongr.right_apply (a := x) _ _ hx]
    rfl

/-! ### The bijection `Φ` of finite sets of indices -/

omit [CharZero K] in
lemma symmDiff_singleton_eq (T : Finset (NegRootIndex P)) (x : NegRootIndex P) :
    symmDiff T {x} = if x ∈ T then T.erase x else insert x T := by
  classical
  ext y
  split_ifs with hx
  · simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro (⟨hy, hyx⟩ | ⟨rfl, hy⟩)
      · exact ⟨hyx, hy⟩
      · exact absurd hx hy
    · rintro ⟨hyx, hy⟩
      exact Or.inl ⟨hy, hyx⟩
  · simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · rintro (⟨hy, -⟩ | ⟨rfl, -⟩)
      · exact Or.inr hy
      · exact Or.inl rfl
    · rintro (rfl | hy)
      · exact Or.inr ⟨rfl, hx⟩
      · exact Or.inl ⟨hy, fun h ↦ hx (h ▸ hy)⟩

omit [CharZero K] in
lemma finsetWt_symmDiff_singleton (T : Finset (NegRootIndex P)) (x : NegRootIndex P) :
    finsetWt P (symmDiff T {x}) =
      if x ∈ T then finsetWt P T - x.root else finsetWt P T + x.root := by
  classical
  rw [symmDiff_singleton_eq]
  split_ifs with hx
  · rw [finsetWt, finsetWt, Finset.sum_erase_eq_sub hx]
  · rw [finsetWt, finsetWt, Finset.sum_insert hx, add_comm]

omit [CharZero K] in
lemma neg_one_pow_card_symmDiff_singleton (T : Finset (NegRootIndex P)) (x : NegRootIndex P) :
    (-1 : ℤ) ^ (symmDiff T {x}).card = -(-1) ^ T.card := by
  classical
  rw [symmDiff_singleton_eq]
  split_ifs with hx
  · obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 :=
      ⟨T.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨x, hx⟩)).symm⟩
    rw [Finset.card_erase_of_mem hx, hn, Nat.add_sub_cancel, pow_succ]
    ring
  · rw [Finset.card_insert_of_notMem hx, pow_succ]
    ring

/-- The bijection `Φ(S) = σ(S) ∆ {xᵢ}` of the finite sets of indices. -/
def reflectFinset (i : ι) : Finset (NegRootIndex P) ≃ Finset (NegRootIndex P) :=
  (Equiv.finsetCongr (reflectPerm hA i)).trans
    (Function.Involutive.toPerm (fun T ↦ symmDiff T {simpleIndex P i})
      fun _ ↦ symmDiff_symmDiff_cancel_right _ _)

lemma reflectFinset_apply (i : ι) (S : Finset (NegRootIndex P)) :
    reflectFinset hA i S = symmDiff (S.map (reflectPerm hA i).toEmbedding) {simpleIndex P i} :=
  rfl

lemma simpleIndex_mem_map_iff (i : ι) (S : Finset (NegRootIndex P)) :
    simpleIndex P i ∈ S.map (reflectPerm hA i).toEmbedding ↔ simpleIndex P i ∈ S := by
  conv_lhs => rw [← reflectPerm_simpleIndex hA i]
  exact Finset.mem_map' _

lemma finsetWt_map_reflectPerm (i : ι) (S : Finset (NegRootIndex P)) :
    finsetWt P (S.map (reflectPerm hA i).toEmbedding) = P.reflection hA i (finsetWt P S) +
      if simpleIndex P i ∈ S then (2 : ℕ) • P.root i else 0 := by
  classical
  simp only [finsetWt, Finset.sum_map, Equiv.coe_toEmbedding, root_reflectPerm,
    Finset.sum_add_distrib, map_sum]
  congr 1
  rw [Finset.sum_ite_eq']

/-- `wt Φ(S) = rᵢ (wt S) + αᵢ`. -/
lemma finsetWt_reflectFinset (i : ι) (S : Finset (NegRootIndex P)) :
    finsetWt P (reflectFinset hA i S) = P.reflection hA i (finsetWt P S) + P.root i := by
  rw [reflectFinset_apply, finsetWt_symmDiff_singleton, finsetWt_map_reflectPerm,
    root_simpleIndex]
  by_cases h : simpleIndex P i ∈ S
  · rw [ite_eq_left ((simpleIndex_mem_map_iff hA i S).mpr h), ite_eq_left h]
    simp only [two_nsmul]
    abel
  · rw [ite_eq_right (mt (simpleIndex_mem_map_iff hA i S).mp h), ite_eq_right h, add_zero]

/-- `|Φ(S)| ≡ |S| + 1 (mod 2)`. -/
lemma neg_one_pow_card_reflectFinset (i : ι) (S : Finset (NegRootIndex P)) :
    (-1 : ℤ) ^ (reflectFinset hA i S).card = -(-1) ^ S.card := by
  rw [reflectFinset_apply, neg_one_pow_card_symmDiff_singleton, Finset.card_map]

/-! ### Anti-invariance -/

/-- The coefficients of the denominator satisfy `R_{rᵢ μ - αᵢ} = -R_μ` ([Kac] §10.2 (check)). -/
theorem coeffAt_denominator_reflection (i : ι) (μ : Dual K H) :
    (denominator P).coeffAt (P.reflection hA i μ - P.root i) = -(denominator P).coeffAt μ := by
  classical
  rw [coeffAt_denominator, coeffAt_denominator, ← finsum_comp_equiv (reflectFinset hA i),
    ← finsum_neg_distrib]
  refine finsum_congr fun S ↦ ?_
  rw [finsetWt_reflectFinset, neg_one_pow_card_reflectFinset]
  have : -(P.reflection hA i (finsetWt P S) + P.root i) = P.reflection hA i μ - P.root i ↔
      -finsetWt P S = μ := by
    rw [neg_add, sub_eq_add_neg, add_left_inj, ← map_neg, (P.reflection hA i).injective.eq_iff]
  rw [if_congr this rfl rfl]
  split_ifs <;> simp

/-- `(e^ρ R)_{rᵢ μ} = -(e^ρ R)_μ`, since `rᵢ ρ = ρ - αᵢ` ([Kac] §10.2 (check)). -/
theorem coeffAt_exp_rho_mul_denominator_reflection (i : ι) (μ : Dual K H) :
    (exp P ℤ P.rho * denominator P).coeffAt (P.reflection hA i μ) =
      -(exp P ℤ P.rho * denominator P).coeffAt μ := by
  rw [coeff_exp_mul, coeff_exp_mul, ← coeffAt_denominator_reflection hA i (μ - P.rho)]
  congr 1
  rw [map_sub, reflection_apply P hA i P.rho, rho_coroot, one_smul]
  abel

/-- **Anti-invariance of `e^ρ R`** ([Kac] §10.2 (check)): `(e^ρ R)_{w μ} = (-1)^{ℓ(w)} (e^ρ R)_μ`
for all `w ∈ W`. -/
theorem isWeylAntiInvariant_exp_rho_mul_denominator :
    (exp P ℤ P.rho * denominator P).IsWeylAntiInvariant P hA :=
  isWeylAntiInvariant_of_reflection (coeffAt_exp_rho_mul_denominator_reflection hA)

/-- For an integrable module `V` in the category `𝒪`, `e^ρ R ch V` is `W`-anti-invariant
([Kac] §10.4 (check)). -/
theorem IsCategoryO.isWeylAntiInvariant_exp_rho_mul_character {V : Type*} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (hV : IsCategoryO P V) (hI : IsIntegrable P V) :
    (exp P ℤ P.rho * denominator P * hV.character).IsWeylAntiInvariant P hA :=
  (isWeylAntiInvariant_exp_rho_mul_denominator hA).mul (hV.isWeylInvariant_character hA hI)

end KacMoodyAlgebra

end Matrix.Realization
