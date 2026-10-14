/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.EnoughProjectives
import LieLean.Algebra.Lie.KacMoody.StandardFiltrationSummand

/-!
# Standard filtrations of projective modules in `𝒪`

Humphreys, GSM 94, Theorem 3.10, first sentence: every projective module in `𝒪` has a standard
filtration. (The statement about `P(λ)` is `ProjectiveCover.exists_isStdFiltered`.)

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.directSum`: a finite direct sum of modules
  with standard filtrations has a standard filtration.
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveO.exists_isStdFiltered`: **Theorem 3.10**,
  first sentence.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.10.
-/

noncomputable section

open Module LieModule DirectSum

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

section DirectSum

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {κ : Type*} [Fintype κ] {Q : κ → Type*} [∀ j, AddCommGroup (Q j)]
  [∀ j, Module K (Q j)] [∀ j, LieRingModule P.KacMoodyAlgebra (Q j)]
  [∀ j, LieModule K P.KacMoodyAlgebra (Q j)]

local notation "𝔤" => KacMoodyAlgebra P

/-- A finite direct sum `⊕ⱼ Qⱼ` of modules with standard filtrations with weights `sⱼ` has a
standard filtration with weights `Σⱼ sⱼ`. -/
theorem IsStdFiltered.directSum {s : κ → Multiset (Dual K H)}
    (hQ : ∀ j, IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (Q j)) (s j)) :
    IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (⨁ j, Q j)) (∑ j, s j) := by
  classical
  let R : Finset κ → LieSubmodule K 𝔤 (⨁ j, Q j) := fun T ↦
    ⨆ j ∈ T, (DirectSum.lieModuleOf K κ 𝔤 Q j).range
  have hR : ∀ T : Finset κ, IsStdFiltered P (R T) (∑ j ∈ T, s j) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa [R] using IsStdFiltered.bot (P := P) (X := ⨁ j, Q j)
    | insert a T haT ih =>
      set g := (LieSubmodule.Quotient.mk' (R T)).comp (DirectSum.lieModuleOf K κ 𝔤 Q a)
      have hRa : ∀ x ∈ R T, x a = 0 := by
        intro x hx
        have hle : R T ≤ (DirectSum.lieModuleComponent K κ 𝔤 Q a).ker := by
          refine iSup₂_le fun j hj ↦ ?_
          rintro _ ⟨q, rfl⟩
          rw [LieModuleHom.mem_ker]
          exact DirectSum.of_eq_of_ne _ _ _ (fun h : a = j ↦ haT (by rw [h]; exact hj))
        exact hle hx
      have hg : ∀ q ∈ (⊤ : LieSubmodule K 𝔤 (Q a)), g q = 0 → q = 0 := by
        intro q _ hq
        change LieSubmodule.Quotient.mk' (R T) (DirectSum.of Q a q) = 0 at hq
        rw [LieSubmodule.Quotient.mk_eq_zero] at hq
        have := hRa _ hq
        rwa [DirectSum.of_eq_same] at this
      have h := IsStdFiltered.comap_mk P ih ((hQ a).map_of_injOn P g hg le_rfl)
      have hcomap : ((⊤ : LieSubmodule K 𝔤 (Q a)).map g).comap
          (LieSubmodule.Quotient.mk' (R T)) = R (insert a T) := by
        have hins : R (insert a T) = (DirectSum.lieModuleOf K κ 𝔤 Q a).range ⊔ R T := by
          simp only [R, Finset.iSup_insert]
        rw [hins]
        ext x
        rw [LieSubmodule.mem_comap, LieSubmodule.mem_sup]
        constructor
        · rintro ⟨q, -, hq⟩
          change LieSubmodule.Quotient.mk' (R T) (DirectSum.of Q a q) = _ at hq
          rw [← sub_eq_zero, ← map_sub, LieSubmodule.Quotient.mk_eq_zero] at hq
          exact ⟨DirectSum.of Q a q, ⟨q, rfl⟩, x - DirectSum.of Q a q, by
            rw [← neg_mem_iff, neg_sub]; exact hq, add_sub_cancel _ _⟩
        · rintro ⟨y, ⟨q, rfl⟩, z, hz, rfl⟩
          refine ⟨q, LieSubmodule.mem_top q, ?_⟩
          change LieSubmodule.Quotient.mk' (R T) (DirectSum.of Q a q) = _
          rw [map_add, (LieSubmodule.Quotient.mk_eq_zero (R T)).mpr hz, add_zero]
          rfl
      rw [Finset.sum_insert haT, ← hcomap]
      exact h
  have htop : R Finset.univ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using DirectSum.induction_on with
    | zero => exact zero_mem _
    | of j q =>
      exact (le_iSup₂_of_le j (Finset.mem_univ j) le_rfl :
        (DirectSum.lieModuleOf K κ 𝔤 Q j).range ≤ R Finset.univ) ⟨q, rfl⟩
    | add x y hx hy => exact add_mem hx hy
  rw [← htop]
  exact hR Finset.univ

end DirectSum

section Projective

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **Humphreys, GSM 94, Theorem 3.10** (first sentence). In finite type over an algebraically
closed field of characteristic zero, every finitely generated projective module in `𝒪` has a
standard filtration. Humphreys works over `ℂ`. As in the source, `V` is a direct summand of a
direct sum of modules `M(μ) ⊗ L` (Theorem 3.8), which have standard filtrations (Theorem 3.6), and
direct summands inherit them (Proposition 3.7 (b)). -/
theorem IsProjectiveO.exists_isStdFiltered {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (hVproj : IsProjectiveO.{max u₁ u₂} P V) (hV : IsCategoryO P V) {S : Finset V}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set V) = ⊤) :
    ∃ s : Multiset (Dual K H), IsStdFiltered P (⊤ : LieSubmodule K 𝔤 V) s := by
  classical
  obtain ⟨κ, _, _, τ, hQ, -, -, π, hπ⟩ :=
    exists_isProjectiveO_surjective.{max u₁ u₂, 0} P hA hV hS
  have hj : ∀ j, ∃ s, IsStdFiltered P
      (⊤ : LieSubmodule K 𝔤 (projectiveCoverAmbient' P hA (τ j))) s := by
    intro j
    set n := projectiveCoverShift P hA (τ j)
    have := IrreducibleModule.finiteDimensional (P := P) hA (isDominantIntegral_nsmul_rho P n)
    obtain ⟨s, hs, -⟩ := exists_isStdFiltered_tensorVerma P
      (isCategoryO_dual_irreducible_nsmul_rho P hA n).iSup_weightSpaceOfMap_eq_top
      (τ j + (n : K) • P.rho)
    exact ⟨_, hs⟩
  choose s hs using hj
  obtain ⟨σ, hσ⟩ := hVproj hQ hV π hπ LieModuleHom.id
  have hπσ (v : V) : π (σ v) = v := LieModuleHom.congr_fun hσ v
  set p := σ.comp π
  have hp : p.comp p = p := by
    refine LieModuleHom.ext fun x ↦ ?_
    change σ (π (σ (π x))) = σ (π x)
    rw [hπσ]
  obtain ⟨t, -, ht, -, -⟩ := exists_isStdFiltered_range_add P hQ
    (IsStdFiltered.directSum P hs) p hp
  have hinj : ∀ x ∈ p.range, π x = 0 → x = 0 := by
    rintro _ ⟨y, rfl⟩ hy
    change σ (π y) = 0
    change π (σ (π y)) = 0 at hy
    rw [hπσ] at hy
    rw [hy, map_zero]
  have hmap : p.range.map π = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    exact ⟨σ v, ⟨σ v, by change σ (π (σ v)) = σ v; rw [hπσ]⟩, hπσ v⟩
  exact ⟨t, hmap ▸ ht.map_of_injOn P π hinj le_rfl⟩

end Projective

end Matrix.Realization.KacMoodyAlgebra
