/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Uniqueness

/-!
# Verma homomorphisms two distinct simple roots below the highest weight

## Main results

For distinct connected nodes `i, j`, the actual space
`Hom(M(Λ - (αᵢ + αⱼ)), M(Λ))` has dimension at most one, for every highest weight `Λ`.
This is not restricted to dominant integral dot-orbits or to simple reflections.

## References

The finite-type specialization is a case of Humphreys, *Representations of semisimple
Lie algebras in the BGG category O*, Chapter 4, Theorem 4.2(b). The local two-letter proof
below is reconstructed directly from the defining relations and the existing Verma PBW API.
No unrestricted Kac–Moody uniqueness theorem is assumed.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (Λ : Dual K H) {i j : ι}

/-- The two-letter weight space is spanned by the two possible orders of its letters. -/
theorem weightSpace_sub_root_add_root :
    weightSpace P Λ (Λ - (P.root i + P.root j)) =
      Submodule.span K {fWord P [i, j] • hwv P Λ, fWord P [j, i] • hwv P Λ} := by
  apply le_antisymm
  · rw [weightSpace_eq_wordSpan, wordSpan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hc : AuxLieAlgebra.counts w = AuxLieAlgebra.counts [i, j] := by
      apply P.rootOf_injective
      rw [← AuxLieAlgebra.wordWt_eq_rootOf, ← AuxLieAlgebra.wordWt_eq_rootOf]
      apply sub_right_injective (b := Λ)
      simpa [AuxLieAlgebra.wordWt_cons] using hw
    have hp : w.Perm [i, j] := List.perm_iff_count.mpr fun a ↦ by
      have := congrFun hc a
      dsimp [AuxLieAlgebra.counts] at this
      exact_mod_cast this
    rcases List.perm_pair.mp hp with rfl | rfl
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rw [Submodule.span_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · simpa [AuxLieAlgebra.wordWt_cons] using fWord_smul_mem_weightSpace P Λ [i, j]
    · rcases Set.mem_singleton_iff.mp hx with rfl
      simpa [AuxLieAlgebra.wordWt_cons, add_comm] using
        fWord_smul_mem_weightSpace P Λ [j, i]

/-- There are at most two independent vectors at a two-letter weight. -/
theorem finrank_weightSpace_sub_root_add_root_le_two :
    finrank K (weightSpace P Λ (Λ - (P.root i + P.root j))) ≤ 2 := by
  classical
  rw [weightSpace_sub_root_add_root]
  exact (finrank_span_le_card _).trans (by
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp))

omit [CharZero K] in
/-- The raising operator distinguishes the two orders at a connected pair of nodes. -/
theorem lie_e_fWord_pair_sub (hij : i ≠ j) :
    ⁅e P i, fWord P [i, j] • hwv P Λ - fWord P [j, i] • hwv P Λ⁆ =
      -(A i j : K) • ⁅f P j, hwv P Λ⁆ := by
  simp only [fWord_smul_cons, fWord_nil, one_smul, lie_sub]
  have heij : ⁅e P i, f P j⁆ = 0 := by simp [lie_e_f, hij]
  have heii : ⁅e P i, f P i⁆ = h P (P.coroot i) := by simp
  have h1 : ⁅e P i, ⁅f P j, hwv P Λ⁆⁆ = 0 := by
    rw [leibniz_lie, heij, zero_lie, lie_e_hwv, lie_zero, add_zero]
  have h2 : ⁅e P i, ⁅f P i, hwv P Λ⁆⁆ = Λ (P.coroot i) • hwv P Λ := by
    rw [leibniz_lie, heii, lie_h_hwv, lie_e_hwv, lie_zero, add_zero]
  have h3 : ⁅h P (P.coroot i), ⁅f P j, hwv P Λ⁆⁆ =
      (Λ (P.coroot i) - (A i j : K)) • ⁅f P j, hwv P Λ⁆ := by
    have hwt := fWord_smul_mem_weightSpace P Λ [j] (P.coroot i)
    simpa [fWord_smul_cons, AuxLieAlgebra.wordWt_cons, P.root_coroot] using hwt
  rw [leibniz_lie, heii, h1, lie_zero, add_zero, h3,
    leibniz_lie, heij, zero_lie, zero_add, h2, lie_smul]
  module

/-- **Two-letter Verma Hom bound.** For two distinct connected nodes, uniqueness holds
at weight difference `αᵢ + αⱼ`, with no dominance or integrality assumption on `Λ`.
Reconstructed from two-letter PBW spanning and the Chevalley relations; the finite-type
specialization belongs to Humphreys, Chapter 4, Theorem 4.2(b). -/
theorem finrank_hom_sub_root_add_root_le_one (hij : i ≠ j) (hAij : A i j ≠ 0) :
    finrank K (VermaModule P (Λ - (P.root i + P.root j)) →ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule P Λ) ≤ 1 := by
  rw [finrank_hom]
  have := finiteDimensional_weightSpace P Λ (Λ - (P.root i + P.root j))
  have hlt : primitiveVectors P (VermaModule P Λ) (Λ - (P.root i + P.root j)) <
      weightSpace P Λ (Λ - (P.root i + P.root j)) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hm : fWord P [i, j] • hwv P Λ - fWord P [j, i] • hwv P Λ ∈
        weightSpace P Λ (Λ - (P.root i + P.root j)) := by
      rw [weightSpace_sub_root_add_root]
      exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rw [← heq] at hm
    have hz := (mem_primitiveVectors.mp hm).2 i
    rw [lie_e_fWord_pair_sub P Λ hij] at hz
    have hf : ⁅f P j, hwv P Λ⁆ ≠ 0 := by
      simpa using toEnd_f_pow_hwv_ne_zero P Λ j 1
    exact hf ((smul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr
      (Int.cast_ne_zero.mpr hAij)))
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have htwo := finrank_weightSpace_sub_root_add_root_le_two P Λ (i := i) (j := j)
  omega

omit [CharZero K] in
/-- The raising action on a two-letter word starting with the same node. -/
theorem lie_e_fWord_pair_left (hij : i ≠ j) :
    ⁅e P i, fWord P [i, j] • hwv P Λ⁆ =
      (Λ (P.coroot i) - (A i j : K)) • ⁅f P j, hwv P Λ⁆ := by
  simp only [fWord_smul_cons, fWord_nil, one_smul]
  have heij : ⁅e P i, f P j⁆ = 0 := by simp [lie_e_f, hij]
  have heii : ⁅e P i, f P i⁆ = h P (P.coroot i) := by simp
  have h1 : ⁅e P i, ⁅f P j, hwv P Λ⁆⁆ = 0 := by
    rw [leibniz_lie, heij, zero_lie, lie_e_hwv, lie_zero, add_zero]
  rw [leibniz_lie, heii, h1, lie_zero, add_zero]
  have hwt := fWord_smul_mem_weightSpace P Λ [j] (P.coroot i)
  simpa [fWord_smul_cons, AuxLieAlgebra.wordWt_cons, P.root_coroot] using hwt

omit [CharZero K] in
/-- The raising action on the reverse two-letter word. -/
theorem lie_e_fWord_pair_right (hij : i ≠ j) :
    ⁅e P i, fWord P [j, i] • hwv P Λ⁆ =
      Λ (P.coroot i) • ⁅f P j, hwv P Λ⁆ := by
  simp only [fWord_smul_cons, fWord_nil, one_smul]
  have heij : ⁅e P i, f P j⁆ = 0 := by simp [lie_e_f, hij]
  have heii : ⁅e P i, f P i⁆ = h P (P.coroot i) := by simp
  have h2 : ⁅e P i, ⁅f P i, hwv P Λ⁆⁆ = Λ (P.coroot i) • hwv P Λ := by
    rw [leibniz_lie, heii, lie_h_hwv, lie_e_hwv, lie_zero, add_zero]
  rw [leibniz_lie, heij, zero_lie, zero_add, h2, lie_smul]

omit [CharZero K] in
/-- Other raising generators kill a two-letter word. -/
theorem lie_e_fWord_pair_other {k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    ⁅e P k, fWord P [i, j] • hwv P Λ⁆ = 0 := by
  simp only [fWord_smul_cons, fWord_nil, one_smul]
  have hei : ⁅e P k, f P i⁆ = 0 := by simp [lie_e_f, hki]
  have hej : ⁅e P k, f P j⁆ = 0 := by simp [lie_e_f, hkj]
  have hj : ⁅e P k, ⁅f P j, hwv P Λ⁆⁆ = 0 := by
    rw [leibniz_lie, hej, zero_lie, lie_e_hwv, lie_zero, add_zero]
  rw [leibniz_lie, hei, zero_lie, zero_add, hj, lie_zero]

/-- The symmetric two-letter vector is nonzero at a connected pair, even when singular.
The proof transports its PBW preimage to highest weight zero,
where a raising operator detects it. -/
theorem fWord_pair_add_ne_zero (hij : i ≠ j) (hAij : A i j ≠ 0) :
    fWord P [i, j] • hwv P Λ + fWord P [j, i] • hwv P Λ ≠ 0 := by
  let u (k : ι) : UniversalEnvelopingAlgebra K (nNeg P) :=
    UniversalEnvelopingAlgebra.ι K ⟨f P k, f_mem_nNeg P k⟩
  have heq (ν : Dual K H) :
      equivEnvNNeg P ν (u i * u j + u j * u i) =
        fWord P [i, j] • hwv P ν + fWord P [j, i] • hwv P ν := by
    simp only [equivEnvNNeg_apply, map_add, map_mul, u, UniversalEnvelopingAlgebra.map_ι]
    simp [fWord, mul_smul]
  intro hz
  have hu : u i * u j + u j * u i = 0 :=
    (equivEnvNNeg P Λ).injective (by simpa only [heq, map_zero] using hz)
  have hzero : fWord P [i, j] • hwv P 0 + fWord P [j, i] • hwv P 0 = 0 := by
    rw [← heq, hu, map_zero]
  have hh := congrArg (fun x : VermaModule P 0 ↦ ⁅e P i, x⁆) hzero
  rw [lie_add, lie_e_fWord_pair_left P 0 hij, lie_e_fWord_pair_right P 0 hij] at hh
  simp only [LinearMap.zero_apply, zero_sub, zero_smul, add_zero, lie_zero] at hh
  have hf : ⁅f P j, hwv P 0⁆ ≠ 0 := by
    simpa using toEnd_f_pow_hwv_ne_zero P 0 j 1
  exact hf ((smul_eq_zero.mp hh).resolve_left
    (neg_ne_zero.mpr (Int.cast_ne_zero.mpr hAij)))

/-- A nonintegral `A₂`-edge singular vector, not covered by the dominant integral dot-orbit
or simple-reflection uniqueness theorems. Its weight difference is `αᵢ + αⱼ`.
This explicit calculation is reconstructed from the defining relations. -/
theorem fWord_pair_add_mem_primitiveVectors (hij : i ≠ j)
    (hAij : A i j = -1) (hAji : A j i = -1)
    (hΛi : Λ (P.coroot i) = -(2 : K)⁻¹) (hΛj : Λ (P.coroot j) = -(2 : K)⁻¹) :
    fWord P [i, j] • hwv P Λ + fWord P [j, i] • hwv P Λ ∈
      primitiveVectors P (VermaModule P Λ) (Λ - (P.root i + P.root j)) := by
  refine mem_primitiveVectors.mpr ⟨?_, fun k ↦ ?_⟩
  · change _ ∈ weightSpace P Λ (Λ - (P.root i + P.root j))
    rw [weightSpace_sub_root_add_root]
    exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · rw [lie_add]
    by_cases hki : k = i
    · subst k
      rw [lie_e_fWord_pair_left P Λ hij, lie_e_fWord_pair_right P Λ hij,
        hΛi, hAij, ← add_smul]
      norm_num
    · by_cases hkj : k = j
      · subst k
        rw [lie_e_fWord_pair_right P Λ hij.symm, lie_e_fWord_pair_left P Λ hij.symm,
          hΛj, hAji, ← add_smul]
        norm_num
      · rw [lie_e_fWord_pair_other P Λ hki hkj,
          lie_e_fWord_pair_other P Λ hkj hki, add_zero]

/-- **Nonintegral two-root Hom dimension.** At an `A₂` edge with both highest-weight
coroot values `-1/2`, the Hom space two simple roots below has dimension exactly one.
In finite type this supplies a nonzero proper embedding outside the already implemented
regular integral BGG orbit. No existence or uniqueness premise is assumed. -/
theorem finrank_hom_sub_root_add_root_eq_one_half (hij : i ≠ j)
    (hAij : A i j = -1) (hAji : A j i = -1)
    (hΛi : Λ (P.coroot i) = -(2 : K)⁻¹) (hΛj : Λ (P.coroot j) = -(2 : K)⁻¹) :
    finrank K (VermaModule P (Λ - (P.root i + P.root j)) →ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule P Λ) = 1 := by
  have hne : A i j ≠ 0 := by omega
  refine le_antisymm (finrank_hom_sub_root_add_root_le_one P Λ hij hne) ?_
  obtain ⟨φ, hφ⟩ := (exists_ne_zero_iff P (Λ - (P.root i + P.root j))).mpr
    ⟨_, (mem_primitiveVectors.mp
      (fWord_pair_add_mem_primitiveVectors P Λ hij hAij hAji hΛi hΛj)).1,
      fWord_pair_add_ne_zero P Λ hij hne, (mem_primitiveVectors.mp
        (fWord_pair_add_mem_primitiveVectors P Λ hij hAij hAji hΛi hΛj)).2⟩
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨φ, hφ⟩

omit Λ in
/-- A canonical nonintegral weight realizing the two-root Hom theorem: `Λ = -ρ/2`.
Only the two Cartan entries are premises; no prescribed Hom dimension or embedding is assumed. -/
theorem finrank_hom_sub_root_add_root_neg_half_rho (hij : i ≠ j)
    (hAij : A i j = -1) (hAji : A j i = -1) :
    finrank K
      (VermaModule P (-(2 : K)⁻¹ • P.rho - (P.root i + P.root j)) →ₗ⁅K,P.KacMoodyAlgebra⁆
        VermaModule P (-(2 : K)⁻¹ • P.rho)) = 1 := by
  apply finrank_hom_sub_root_add_root_eq_one_half P _ hij hAij hAji
  all_goals simp

/-- The nonintegral two-root singular vector gives a genuine embedding of Verma modules. -/
theorem exists_injective_sub_root_add_root_half (hij : i ≠ j)
    (hAij : A i j = -1) (hAji : A j i = -1)
    (hΛi : Λ (P.coroot i) = -(2 : K)⁻¹) (hΛj : Λ (P.coroot j) = -(2 : K)⁻¹) :
    ∃ φ : VermaModule P (Λ - (P.root i + P.root j)) →ₗ⁅K,P.KacMoodyAlgebra⁆
        VermaModule P Λ, Function.Injective φ ∧
      φ (hwv P _) = fWord P [i, j] • hwv P Λ + fWord P [j, i] • hwv P Λ := by
  let φ := (homEquiv P (VermaModule P Λ) _).symm
    ⟨_, fWord_pair_add_mem_primitiveVectors P Λ hij hAij hAji hΛi hΛj⟩
  have hφ : φ (hwv P _) = fWord P [i, j] • hwv P Λ + fWord P [j, i] • hwv P Λ := by
    rw [← homEquiv_apply, LinearEquiv.apply_symm_apply]
  refine ⟨φ, injective_of_ne_zero P ?_, hφ⟩
  intro hz
  apply fWord_pair_add_ne_zero P Λ hij (by omega)
  rw [← hφ, hz, _root_.zero_apply]

end Matrix.Realization.KacMoodyAlgebra.VermaModule

/-- Concrete nonvacuity check: the standard `A₂` realization over `ℚ`, at weight `-ρ/2`.
This uses the actual Verma modules, not an abstract vector space with a dimension premise. -/
theorem vermaHomNext_A2_rational :
    let P := Matrix.Realization.std (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ) ℚ
    finrank ℚ
      (Matrix.Realization.KacMoodyAlgebra.VermaModule P
        (-(2 : ℚ)⁻¹ • P.rho - (P.root 0 + P.root 1)) →ₗ⁅ℚ,P.KacMoodyAlgebra⁆
        Matrix.Realization.KacMoodyAlgebra.VermaModule P (-(2 : ℚ)⁻¹ • P.rho)) = 1 := by
  dsimp only
  apply Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_hom_sub_root_add_root_neg_half_rho
  all_goals decide
