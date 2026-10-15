/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGGReciprocity
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType
import LieLean.Algebra.Lie.KacMoody.VermaSimple
import LieLean.Algebra.Lie.KacMoody.SelfDualProjective
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralWeylGroupAntidominant

/-!
# The socle of an indecomposable projective

Humphreys, GSM 94, Corollary 4.8, in the form proved here: for antidominant `λ` and `w ∈ W_[λ]`,
each simple submodule of `P(w·λ)` is isomorphic to `L(λ)`. As `soc P(w·λ)` is the sum of the simple
submodules, `soc P(w·λ)` is then a direct sum of copies of `L(λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.exists_injective_of_isAtom`: a simple
  submodule of a module with a standard filtration embeds into one of the Verma factors.
* `Matrix.Realization.KacMoodyAlgebra.ProjectiveCover.nonempty_equiv_irreducibleModule_of_isAtom`:
  **Humphreys, GSM 94, Corollary 4.8**.

## Proof

As in Humphreys: a simple submodule `L` of `P(w·λ)` embeds into a factor `M(μ)` of a standard
filtration (Theorem 3.10), at the first step containing it. A Verma module mapping onto `L`
(highest weight `ξ`) then embeds into `M(μ)` (Theorem 4.2 (a)), so `L ≅ M(ξ)` and `M(ξ)` is simple,
hence `ξ` is antidominant (Theorem 4.8) and `L ≅ L(ξ)`. Humphreys concludes `ξ = λ` from the
fact that the factors of the filtration are the `M(x·λ)`, `x ∈ W_[λ]`; here this is derived from
BGG reciprocity (`[M(μ) : L(w·λ)] ≠ 0`) and the Kac–Kazhdan criterion (`ξ` and `w·λ` lie in the
dot orbit of `μ` and in `μ - Q₊`), so `ξ ∈ W_[λ]·λ`, and the antidominant weight of a
`W_[λ]`-orbit is unique (Proposition 3.5).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §4.8.
-/

noncomputable section

open Module LieModule

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]


omit [CharZero K] in
/-- A simple submodule `S` of a submodule `N` with a standard filtration embeds into one of the
Verma modules of the filtration (proof of Humphreys, GSM 94, Corollary 4.8). -/
theorem IsStdFiltered.exists_injective_of_isAtom {N : LieSubmodule K P.KacMoodyAlgebra X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) {S : LieSubmodule K P.KacMoodyAlgebra X}
    (hS : IsAtom S) (hSN : S ≤ N) :
    ∃ μ ∈ s, ∃ f : S →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ, Function.Injective f := by
  induction hN with
  | bot => exact absurd (le_bot_iff.mp hSN) hS.1
  | @step N N' s μ _ hle he ih =>
    by_cases h : S ≤ N
    · obtain ⟨μ', hμ', f, hf⟩ := ih h
      exact ⟨μ', Multiset.mem_cons_of_mem hμ', f, hf⟩
    · have hinf : S ⊓ N = ⊥ := by
        rcases hS.le_iff.mp (inf_le_left : S ⊓ N ≤ S) with h' | h'
        · exact h'
        · exact absurd (h' ▸ inf_le_right) h
      obtain ⟨e⟩ := he
      let g : S →ₗ⁅K,P.KacMoodyAlgebra⁆ N'.map (LieSubmodule.Quotient.mk' N) :=
        ((LieSubmodule.Quotient.mk' N).comp S.incl).codRestrict _ fun x ↦
          LieSubmodule.mem_map_of_mem (hSN x.2)
      have hg : Function.Injective g := by
        rw [← LieModuleHom.ker_eq_bot, LieSubmodule.eq_bot_iff]
        intro x hx
        have hx0 : LieSubmodule.Quotient.mk' N (x : X) = 0 :=
          congrArg Subtype.val (LieModuleHom.mem_ker.mp hx)
        have hxN : (x : X) ∈ N := by
          rwa [LieSubmodule.Quotient.mk_eq_zero] at hx0
        have hxSN : (x : X) ∈ S ⊓ N := ⟨x.2, hxN⟩
        rw [hinf, LieSubmodule.mem_bot] at hxSN
        exact Subtype.ext hxSN
      exact ⟨μ, Multiset.mem_cons_self _ _, e.symm.toLieModuleHom.comp g,
        fun a b hab ↦ hg (e.symm.injective hab)⟩

end Generic

section Main

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

variable {Q : Type*} [AddCommGroup Q] [Module K Q] [LieRingModule P.KacMoodyAlgebra Q]
  [LieModule K P.KacMoodyAlgebra Q]

include hA in
/-- A simple submodule `S` of a module in `𝒪` that embeds into a Verma module `M(μ)` is
isomorphic to `L(ξ)` for an antidominant `ξ` with `[M(μ) : L(ξ)] ≠ 0` (proof of Humphreys,
GSM 94, Corollary 4.8, via Theorems 4.2 and 4.8). -/
theorem exists_isAntidominant_of_isAtom_of_injective (hQ : IsCategoryO P Q)
    {S : LieSubmodule K P.KacMoodyAlgebra Q} (hS : IsAtom S) {μ : Dual K H}
    {f : S →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ} (hf : Function.Injective f) :
    ∃ ξ, P.IsAntidominant hA.isGeneralizedCartan ξ ∧
      (VermaModule.isCategoryO P μ).multiplicity ξ ≠ 0 ∧
        Nonempty (S ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P ξ) := by
  have : Nontrivial S := (LieSubmodule.nontrivial_iff_ne_bot K P.KacMoodyAlgebra _).mpr hS.1
  obtain ⟨ξ, ψ, hψ⟩ := (hQ.lieSubmodule S).exists_lieModuleHom_verma
  have hφ0 : f.comp ψ (hwv P ξ) ≠ 0 := fun h0 ↦
    hψ (hf (by rw [LieModuleHom.comp_apply] at h0; rw [h0, map_zero]))
  have hφ : f.comp ψ ≠ 0 := fun h ↦ hφ0 (by rw [h, _root_.zero_apply])
  have hψinj : Function.Injective ψ := fun a b hab ↦
    injective_of_ne_zero P hφ (by simp only [LieModuleHom.comp_apply, hab])
  have hψsurj : Function.Surjective ψ := by
    have hle : (S.incl.comp ψ).range ≤ S := by
      intro x hx
      obtain ⟨m, rfl⟩ := (LieModuleHom.mem_range _ _).mp hx
      exact (ψ m).2
    have hrange : (S.incl.comp ψ).range = S := by
      rcases hS.le_iff.mp hle with h | h
      · exact absurd (Subtype.ext ((LieSubmodule.mem_bot _).mp (h ▸
          (LieModuleHom.mem_range _ _).mpr ⟨hwv P ξ, rfl⟩))) hψ
      · exact h
    intro s
    have hs : (s : Q) ∈ (S.incl.comp ψ).range := by rw [hrange]; exact s.2
    obtain ⟨m, hm⟩ := (LieModuleHom.mem_range _ _).mp hs
    exact ⟨m, Subtype.ext hm⟩
  let e := LieModuleEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hmax : maxSubmodule P ξ = ⊥ := by
    let T : LieSubmodule K P.KacMoodyAlgebra Q := (maxSubmodule P ξ).map (S.incl.comp ψ)
    have hT : T ≤ S := by
      rintro _ ⟨m, -, rfl⟩
      exact (ψ m).2
    rcases hS.le_iff.mp hT with h | h
    · rw [LieSubmodule.eq_bot_iff]
      intro m hm
      have hmT : (S.incl.comp ψ) m ∈ T := LieSubmodule.mem_map_of_mem hm
      rw [h, LieSubmodule.mem_bot] at hmT
      exact hψinj (Subtype.ext (by rw [map_zero]; exact hmT))
    · exfalso
      have hv : (ψ (hwv P ξ) : Q) ∈ T := by rw [h]; exact (ψ (hwv P ξ)).2
      obtain ⟨m, hm, hme⟩ := (LieSubmodule.mem_map _).mp hv
      have : m = hwv P ξ := hψinj (Subtype.ext hme)
      exact hwv_notMem_maxSubmodule P ξ (by rwa [← this])
  have hξ : P.IsAntidominant hA.isGeneralizedCartan ξ :=
    (maxSubmodule_eq_bot_iff_isAntidominant P hA).mp hmax
  obtain ⟨e'⟩ := VermaModule.nonempty_equiv_irreducible_of_isAntidominant P hA hξ
  exact ⟨ξ, hξ, multiplicity_ne_zero_of_hom_ne_zero P hφ, ⟨e.symm.trans e'⟩⟩

include hA in
/-- If `ξ` and `w·λ` (`w ∈ W_[λ]`) are both composition factors of `M(μ)` and `λ`, `ξ` are
antidominant, then `ξ = λ`: both lie in the dot orbit of `μ` and in `μ - Q₊`, so
`ξ ∈ W_[λ]·λ`. -/
theorem eq_of_multiplicity_ne_zero_of_isAntidominant {lam ξ μ : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hξ : P.IsAntidominant hA.isGeneralizedCartan ξ) {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (hmξ : (VermaModule.isCategoryO P μ).multiplicity ξ ≠ 0)
    (hmwl : (VermaModule.isCategoryO P μ).multiplicity
      (P.weylDot hA.isGeneralizedCartan w lam) ≠ 0) :
    ξ = lam := by
  have hA' := hA.isGeneralizedCartan
  obtain ⟨d, hdpos, hposDef⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hposDef.isHermitian
  set Sym := Symmetrization.ofDiagonal d hdpos hsymm
  obtain ⟨x, hx⟩ := exists_weylDot_of_multiplicity_ne_zero P hA Sym hmξ
  obtain ⟨y, hy⟩ := exists_weylDot_of_multiplicity_ne_zero P hA Sym hmwl
  obtain ⟨k₁, -, hk₁⟩ := mem_cone_of_multiplicity_ne_zero hmξ
  obtain ⟨k₂, -, hk₂⟩ := mem_cone_of_multiplicity_ne_zero hmwl
  have hμ : μ = P.weylDot hA' y⁻¹ (P.weylDot hA' w lam) := by
    rw [hy, ← weylDot_mul, inv_mul_cancel, weylDot_one]
  set z := x * y⁻¹ * w
  have hzξ : ξ = P.weylDot hA' z lam := by
    rw [hx, hμ, ← weylDot_mul, ← weylDot_mul]
  have hz : z ∈ P.integralWeylGroup hA' lam := by
    rw [mem_integralWeylGroup_iff_dot]
    have hwQ := (mem_integralWeylGroup_iff_dot P hA').mp hw
    have h1 : (z : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - P.rho = μ - P.rootOf k₁ := by
      rw [← hk₁, hzξ]; rfl
    have h2 : (w : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - P.rho = μ - P.rootOf k₂ := by
      rw [← hk₂]; rfl
    have e1 : (z : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - P.rho - lam =
        -P.rootOf k₁ + P.rootOf k₂ +
          ((w : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - P.rho - lam) := by
      rw [h1, h2]
      abel
    rw [e1]
    exact add_mem (add_mem (neg_mem (P.rootOf_mem_rootLattice k₁)) (P.rootOf_mem_rootLattice k₂))
      hwQ
  have hzfix := hlam.eq_of_weylDot_eq hA hz (by rw [← weylDot, ← hzξ]; exact hξ)
  rw [hzξ, weylDot, hzfix, add_sub_cancel_right]

/-- **Humphreys, GSM 94, Corollary 4.8.** Let `λ` be antidominant and `w ∈ W_[λ]`. Then every
simple submodule of `P(w·λ)` is isomorphic to `L(λ)`; equivalently, `soc P(w·λ)` is a direct
sum of copies of `L(λ)`. Finite type, finite-dimensional Cartan subalgebra, algebraically closed
field of characteristic zero (Humphreys works over `ℂ`). -/
theorem ProjectiveCover.nonempty_equiv_irreducibleModule_of_isAtom {lam : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam) {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    {S : LieSubmodule K P.KacMoodyAlgebra
      (ProjectiveCover P hA (P.weylDot hA.isGeneralizedCartan w lam))}
    (hS : IsAtom S) : Nonempty (S ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P lam) := by
  classical
  obtain ⟨t, ht, -, -⟩ :=
    ProjectiveCover.exists_isStdFiltered P (P.weylDot hA.isGeneralizedCartan w lam) hA
  obtain ⟨μ, hμt, f, hf⟩ := ht.exists_injective_of_isAtom P hS le_top
  obtain ⟨ξ, hξ, hmξ, ⟨e⟩⟩ := exists_isAntidominant_of_isAtom_of_injective P hA
    (ProjectiveCover.isCategoryO P hA _) hS hf
  have hmwl : (VermaModule.isCategoryO P μ).multiplicity
      (P.weylDot hA.isGeneralizedCartan w lam) ≠ 0 := by
    rw [← ProjectiveCover.count_eq_multiplicity P _ hA ht μ]
    exact (Multiset.count_pos.mpr hμt).ne'
  obtain rfl := eq_of_multiplicity_ne_zero_of_isAntidominant P hA hlam hξ hw hmξ hmwl
  exact ⟨e⟩

end Main

end Matrix.Realization.KacMoodyAlgebra
