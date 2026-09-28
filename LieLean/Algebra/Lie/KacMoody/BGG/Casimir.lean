/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG
import LieLean.Algebra.Lie.KacMoody.BGG.Character
import LieLean.Algebra.Lie.KacMoody.GabberKac

/-!
# Casimir vanishing for actual positive-degree BGG homology

## Main definitions and results

`Homology` is the actual Lie-module quotient of `ker (bggDiff k)` by the incoming range
pulled back along the cycle inclusion. The terms, cycles and homology lie in category `𝒪`.
Their weights lie below `Λ`, and positive-degree terms and homology have no `Λ` weight.
The Casimir acts with scalar `(Λ + 2ρ | Λ)` on the terms and their actual homology.

`exact_of_nilpotent_mod_boundaries_symmetrizable` proves positive-degree BGG exactness
assuming only local negative-generator nilpotence on actual cycles modulo actual boundaries.
It does not assume exactness, syzygy-generator detection, weight support, or a Casimir identity.
No Kostant homology theorem is used.

## References

The proof of Theorem 3.2 for symmetrizable Kac–Moody algebras in arXiv:math/0605460
uses Proposition 3.4 (integrability of the homology) and complete reducibility.
Here the final vanishing argument is reconstructed directly using a maximal occupied
weight and the Casimir inequality from `CasimirIrreducible.lean`. It only needs local
`fᵢ` nilpotence at that primitive vector, not a separate proof of complete reducibility
or full integrability. The independent Proposition 3.4 obligation remains explicit.
-/

open Module LieModule
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra.BGGCasimir
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

/-- A fixed length stratum is finite because there are finitely many words of that length. -/
instance finite_level (k : ℕ) : Finite {w : P.weylGroup hA //
    (P.coxeterSystem hA).length w = k} := by
  apply Set.Finite.to_subtype
  apply ((List.finite_length_eq ι k).image (P.coxeterSystem hA).wordProd).subset
  intro w hw
  obtain ⟨l, hl, rfl⟩ := (P.coxeterSystem hA).exists_isReduced w
  exact ⟨l, hl.symm.trans hw, rfl⟩

/-- Every BGG term belongs to category `𝒪`, as a finite direct sum of Verma modules. -/
theorem term_categoryO (k : ℕ) : IsCategoryO P (BGGTerm P hA Λ k) := by
  have := finite_level P hA k
  exact IsCategoryO.directSum _ fun _ ↦ VermaModule.isCategoryO P _

include hΛ

/-- A nonidentity dot-orbit Verma summand has no vector of the original highest weight. -/
theorem verma_top_absent (w : P.weylGroup hA) (hw : w ≠ 1) :
    VermaModule.weightSpace P (P.weylDot hA w Λ) Λ = ⊥ := by
  obtain ⟨l, hl, hdiff⟩ := exists_sub_weylDot_eq_rootOf P hA hΛ w
  have hdown : P.weylDot hA w Λ ∈ cone P Λ := by
    refine ⟨l, hl, ?_⟩
    rw [← hdiff]
    abel
  apply VermaModule.weightSpace_eq_bot
  intro k hk heq
  have hfix : P.weylDot hA w Λ = Λ :=
    eq_of_mem_cone_of_mem_cone hdown ⟨k, hk, heq⟩
  apply hw
  apply weylDot_injective P hA hΛ
  simpa only [Matrix.Realization.weylDot_one] using hfix

/-- Every occupied weight of a BGG term lies in the cone below the highest weight. -/
theorem term_weight_below (k : ℕ) {μ : Dual K H} {v : BGGTerm P hA Λ k}
    (hv : v ∈ weightSpace P (BGGTerm P hA Λ k) μ) (hv0 : v ≠ 0) : μ ∈ cone P Λ := by
  obtain ⟨w, hw⟩ : ∃ w, v w ≠ 0 := by
    by_contra! hz
    exact hv0 (DFinsupp.ext hz)
  let c := DirectSum.lieModuleComponent K _ P.KacMoodyAlgebra
    (fun w : {w : P.weylGroup hA // (P.coxeterSystem hA).length w = k} ↦
      VermaModule P (P.weylDot hA w Λ)) w
  have hvw := map_mem_weightSpaceOfMap P c hv
  have hm := map_mem_weightSpaceOfMap P (bggEmb P hA hΛ w) hvw
  exact VermaModule.exists_eq_sub_of_mem_weightSpace P Λ LieModuleHom.id
    Function.surjective_id hm (fun hz ↦ hw (bggEmb_injective P hA hΛ w
      (hz.trans (map_zero _).symm)))

/-- Positive-degree BGG terms have no vector of the original highest weight. -/
theorem term_top_absent (k : ℕ) : weightSpace P (BGGTerm P hA Λ (k + 1)) Λ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  apply DFinsupp.ext
  intro w
  have hw : (w : P.weylGroup hA) ≠ 1 := by
    intro he
    have := w.2
    rw [he, (P.coxeterSystem hA).length_one] at this
    omega
  have hvw := map_mem_weightSpaceOfMap P
    (DirectSum.lieModuleComponent K _ P.KacMoodyAlgebra
      (fun w : {w : P.weylGroup hA // (P.coxeterSystem hA).length w = k + 1} ↦
        VermaModule P (P.weylDot hA w Λ)) w) hv
  exact ((Submodule.eq_bot_iff _).mp (verma_top_absent P hA hΛ w hw)) _ hvw

section CasimirTerm
variable [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra} (hB : IsStandardForm P S B)

set_option maxHeartbeats 8000000 in
-- Comparing actual direct-sum coefficient actions with Verma actions is expensive.
/-- The Casimir has the original Verma scalar on every BGG term, by its actual embeddings. -/
theorem term_casimir (k : ℕ) (v : BGGTerm P hA Λ k) :
    hB.casimir _ (term_categoryO P hA k).isPosFinite v =
      P.dualBilinForm S (Λ + 2 • P.rho) Λ • v := by
  apply DFinsupp.ext
  intro w
  let c := DirectSum.lieModuleComponent K _ P.KacMoodyAlgebra
    (fun w : {w : P.weylGroup hA // (P.coxeterSystem hA).length w = k} ↦
      VermaModule P (P.weylDot hA w Λ)) w
  change c (hB.casimir _ (term_categoryO P hA k).isPosFinite v) =
    c (P.dualBilinForm S (Λ + 2 • P.rho) Λ • v)
  rw [hB.map_casimir c (term_categoryO P hA k).isPosFinite
    (VermaModule.isCategoryO P _).isPosFinite, map_smul]
  apply bggEmb_injective P hA hΛ w
  rw [hB.map_casimir _ (VermaModule.isCategoryO P _).isPosFinite
    (VermaModule.isCategoryO P Λ).isPosFinite, map_smul,
    hB.casimir_eq_smul_of_surjective hA _ LieModuleHom.id Function.surjective_id]

end CasimirTerm

/-- Actual cycles in positive degree `k+1`. -/
abbrev Cycles (k : ℕ) := (bggDiff P hA hΛ k).ker
/-- Actual boundaries viewed inside cycles. -/
def boundaries (k : ℕ) : LieSubmodule K P.KacMoodyAlgebra (Cycles P hA hΛ k) :=
  (bggDiff P hA hΛ (k + 1)).range.comap (Cycles P hA hΛ k).incl
/-- The actual positive-degree BGG homology Lie module. -/
abbrev Homology (k : ℕ) := Cycles P hA hΛ k ⧸ boundaries P hA hΛ k

/-- Actual BGG cycles inherit category `𝒪` from their containing term. -/
theorem cycles_categoryO (k : ℕ) : IsCategoryO P (Cycles P hA hΛ k) :=
  (term_categoryO P hA (k + 1)).lieSubmodule _

/-- Actual BGG homology inherits category `𝒪` as a quotient of cycles. -/
theorem homology_categoryO (k : ℕ) : IsCategoryO P (Homology P hA hΛ k) :=
  (cycles_categoryO P hA hΛ k).quotient _

/-- Every homology weight vector lifts to a cycle of the same weight. -/
theorem homology_weight_lift (k : ℕ) {μ : Dual K H}
    {x : Homology P hA hΛ k} (hx : x ∈ weightSpace P (Homology P hA hΛ k) μ) :
    ∃ y : Cycles P hA hΛ k, y ∈ weightSpace P (Cycles P hA hΛ k) μ ∧
      LieSubmodule.Quotient.mk' (boundaries P hA hΛ k) y = x := by
  rw [weightSpace, ← map_weightSpaceOfMap_quotient P _
    (cycles_categoryO P hA hΛ k).iSup_weightSpaceOfMap_eq_top] at hx
  exact hx

/-- Every occupied positive-degree homology weight is strictly below the highest weight. -/
theorem homology_weight_below (k : ℕ) {μ : Dual K H}
    {x : Homology P hA hΛ k} (hx : x ∈ weightSpace P (Homology P hA hΛ k) μ)
    (hx0 : x ≠ 0) : μ ∈ cone P Λ ∧ μ ≠ Λ := by
  obtain ⟨y, hy, rfl⟩ := homology_weight_lift P hA hΛ k hx
  have hy0 : (y : BGGTerm P hA Λ (k+1)) ≠ 0 := by
    intro hz
    apply hx0
    have : y = 0 := Subtype.ext hz
    rw [this, map_zero]
  have hyw := mem_weightSpaceOfMap_lieSubmodule_iff.mp hy
  refine ⟨term_weight_below P hA hΛ _ hyw hy0, ?_⟩
  intro he
  subst μ
  exact hy0 ((Submodule.eq_bot_iff _).mp (term_top_absent P hA hΛ k) y hyw)

variable [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra} (hB : IsStandardForm P S B)
include hB

set_option maxHeartbeats 8000000 in
-- Definitional equality through the cycle subtype and quotient actions needs extra fuel.
/-- The common Verma Casimir scalar descends to actual BGG homology. -/
theorem homology_casimir (k : ℕ) (x : Homology P hA hΛ k) :
    hB.casimir _ (homology_categoryO P hA hΛ k).isPosFinite x =
      P.dualBilinForm S (Λ + 2 • P.rho) Λ • x := by
  obtain ⟨y, rfl⟩ := LieSubmodule.Quotient.surjective_mk' (boundaries P hA hΛ k) x
  have hy : hB.casimir _ (cycles_categoryO P hA hΛ k).isPosFinite y =
      P.dualBilinForm S (Λ + 2 • P.rho) Λ • y := by
    apply (Cycles P hA hΛ k).injective_incl
    rw [hB.map_casimir _ (cycles_categoryO P hA hΛ k).isPosFinite
      (term_categoryO P hA (k+1)).isPosFinite, map_smul, term_casimir P hA hΛ hB]
  rw [← hB.map_casimir _ (cycles_categoryO P hA hΛ k).isPosFinite
    (homology_categoryO P hA hΛ k).isPosFinite, hy, map_smul]

set_option maxHeartbeats 8000000 in
-- The actual cycle quotient's Lie-module instances make the primitive-vector step expensive.
/-- Casimir vanishing with only local negative-generator nilpotence on actual homology.
The positive-generator nilpotence part of full integrability is unnecessary: only the
primitive-vector `sl₂` argument is used. -/
theorem homology_subsingleton (k : ℕ)
    (hf : ∀ i (x : Homology P hA hΛ k), ∃ n : ℕ,
      (toEnd K P.KacMoodyAlgebra _ (f P i) ^ n) x = 0) :
    Subsingleton (Homology P hA hΛ k) := by
  by_contra hn
  let : Nontrivial (Homology P hA hΛ k) := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨μ, x, hx, hx0, he⟩ := (homology_categoryO P hA hΛ k).exists_lie_e_eq_zero
  have hμ : P.IsDominantIntegral μ := fun i ↦
    IsSl2Triple.HasPrimitiveVectorWith.exists_nat_of_exists_pow_eq_zero
      (t := isSl2Triple P hA i) ⟨hx0, hx _, he i⟩ (hf i x)
  obtain ⟨⟨l, hl, hml⟩, hne⟩ := homology_weight_below P hA hΛ k hx hx0
  have hl0 : l ≠ 0 := by
    intro hz
    apply hne
    simpa [hz] using hml
  apply dualBilinForm_add_two_rho_ne S hΛ hμ ⟨hl, hl0⟩
    (show Λ = μ + P.rootOf l by rw [hml, sub_add_cancel])
  exact smul_left_injective K hx0 ((homology_casimir P hA hΛ hB k x).symm.trans
    (hB.casimir_apply_of_lie_e_eq_zero _ hx he))

set_option maxHeartbeats 8000000 in
-- Transport of operator powers through the nested actual cycle quotient is expensive.
/-- Local nilpotence modulo the range of the actual incoming BGG differential
implies actual positive-degree exactness. -/
theorem exact_of_nilpotent_mod_boundaries (k : ℕ)
    (hf : ∀ (x : BGGTerm P hA Λ (k + 1)), bggDiff P hA hΛ k x = 0 →
      ∀ i, ∃ n : ℕ, (toEnd K P.KacMoodyAlgebra _ (f P i) ^ n) x ∈
        (bggDiff P hA hΛ (k + 1)).range) :
    (bggDiff P hA hΛ k).ker = (bggDiff P hA hΛ (k + 1)).range := by
  have hnil : ∀ i (x : Homology P hA hΛ k), ∃ n : ℕ,
      (toEnd K P.KacMoodyAlgebra _ (f P i) ^ n) x = 0 := by
    intro i x
    obtain ⟨y, rfl⟩ := LieSubmodule.Quotient.surjective_mk' (boundaries P hA hΛ k) x
    have hy : bggDiff P hA hΛ k y = 0 := (LieModuleHom.mem_ker).mp y.property
    obtain ⟨n, hn⟩ := hf y.val hy i
    refine ⟨n, ?_⟩
    rw [toEnd_pow_apply_map, LieSubmodule.Quotient.mk_eq_zero]
    change (Cycles P hA hΛ k).incl ((toEnd K P.KacMoodyAlgebra _ (f P i) ^ n) y) ∈
      (bggDiff P hA hΛ (k + 1)).range
    rw [← toEnd_pow_apply_map]
    exact hn
  have := homology_subsingleton P hA hΛ hB k hnil
  apply le_antisymm
  · intro y hy
    have hz : LieSubmodule.Quotient.mk' (boundaries P hA hΛ k) ⟨y, hy⟩ = 0 :=
      Subsingleton.elim _ _
    exact (LieSubmodule.Quotient.mk_eq_zero (boundaries P hA hΛ k)).mp hz
  · rintro _ ⟨y, rfl⟩
    change bggDiff P hA hΛ k (bggDiff P hA hΛ (k+1) y) = 0
    exact LieModuleHom.congr_fun (bggDiff_comp_bggDiff P hA hΛ k) y

omit hB in
/-- For a symmetrizable generalized Cartan matrix and finite-dimensional Cartan space,
local negative-generator nilpotence modulo actual boundaries proves BGG exactness.
This is the final Casimir step of the proof of Theorem 3.2 in arXiv:math/0605460;
the local nilpotence premise is the separate Proposition 3.4 obligation. -/
theorem exact_of_nilpotent_mod_boundaries_symmetrizable (hS : A.IsSymmetrizable) (k : ℕ)
    (hf : ∀ (x : BGGTerm P hA Λ (k + 1)), bggDiff P hA hΛ k x = 0 →
      ∀ i, ∃ n : ℕ, (toEnd K P.KacMoodyAlgebra _ (f P i) ^ n) x ∈
        (bggDiff P hA hΛ (k + 1)).range) :
    (bggDiff P hA hΛ k).ker = (bggDiff P hA hΛ (k + 1)).range :=
  exact_of_nilpotent_mod_boundaries P hA hΛ
    (isStandardForm_invForm P (isSymmetrizable_iff_nonempty_symmetrization.mp hS).some) k hf

end Matrix.Realization.KacMoodyAlgebra.BGGCasimir

