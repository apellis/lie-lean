/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.StrongLinkage
import LieLean.Algebra.Lie.KacMoody.BGGReciprocity
import LieLean.Algebra.Lie.KacMoody.ExtHighestWeight
import LieLean.Algebra.Lie.KacMoody.TranslationWallExt

/-!
# Extensions of Verma modules

Humphreys, GSM 94, §6.5: a nonsplit extension of `M(μ)` by `M(λ)` in `𝒪` forces `μ ↑ λ` with
`μ ≠ λ`; for `λ` dominant integral, `Ext¹_𝒪(M(w'·λ), M(w·λ)) ≠ 0` forces `w < w'` in the Bruhat
order. Here `Ext¹_𝒪` is the `𝔥`-relative `Ext¹` `LieModule.ExtOne`, which classifies the
extensions in `𝒪` (`IsCategoryO.extension`, `ExtOne.mk_eq_zero_iff`).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.exists_section_or_eq_zero`: the induction
  along a standard filtration used in the proof.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.isStronglyLinked_of_extOne_ne_zero`:
  **Humphreys, GSM 94, Theorem 6.5 (a)**.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.bruhatLT_of_extOne_ne_zero`:
  **Humphreys, GSM 94, Theorem 6.5 (b)**.

## Proof

Let `0 → M(λ) → E → M(μ) → 0` be nonsplit. By projectivity of `P(μ)` there is `φ : P(μ) → E`
whose composite with `E → M(μ)` is nonzero. By Theorem 3.10, BGG reciprocity and Theorem 5.1,
`P(μ)` has a standard filtration whose factors `M(ν)` all have `μ ↑ ν`. Humphreys looks at the
first step of the filtration whose image under `φ` meets `M(λ)`. Here the induction runs
differently (reconstructed): if no factor `M(ν)` maps nonzero to `M(λ)`, then going up the
filtration, `φ` vanishes on each step until the step with factor `M(μ)` (a nonzero map
`M(ν) → M(μ)` forces `ν = μ`), and there `φ` induces a splitting `M(μ) → E`. So some `M(ν)`
maps nonzero into `M(λ)`, whence `ν ↑ λ` by Theorem 5.1 and `μ ↑ ν ↑ λ`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §6.5.
-/

noncomputable section

open Module LieModule

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X E : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X] [AddCommGroup E] [Module K E]
  [LieRingModule P.KacMoodyAlgebra E] [LieModule K P.KacMoodyAlgebra E]

/-- If `g : M(μ) → E` and `q : E → M(μ)` have `q ∘ g ≠ 0`, then `q` has a section: `q ∘ g` is a
nonzero scalar, since `M(μ)_μ` is spanned by the highest weight vector. -/
theorem exists_section_of_comp_ne_zero {μ : Dual K H}
    {q : E →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ} {g : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ E}
    (hg : q.comp g ≠ 0) :
    ∃ σ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ E, ∀ m, q (σ m) = m := by
  have hmem : q (g (hwv P μ)) ∈ K ∙ hwv P μ := by
    rw [← weightSpace_self]
    exact ExtOne.map_mem_weightSpaceOfMap (h P) (q.comp g) (hwv_mem_weightSpace P μ)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hg
    refine VermaModule.hom_ext P μ ?_
    rw [LieModuleHom.comp_apply, ← hc, zero_smul, _root_.zero_apply]
  refine ⟨c⁻¹ • g, fun m ↦ ?_⟩
  have : q.comp (c⁻¹ • g) = LieModuleHom.id := by
    refine VermaModule.hom_ext P μ ?_
    change q (c⁻¹ • g (hwv P μ)) = hwv P μ
    rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  exact LieModuleHom.congr_fun this m

/-- Induction along a standard filtration (proof of Humphreys, GSM 94, Theorem 6.5 (a)). Let
`φ : X → E` and `q : E → M(μ)`. Suppose every map `M(ν) → E` (`ν ∈ s`) killed by `q` is zero, and
every nonzero map `M(ν) → M(μ)` (`ν ∈ s`) has `ν = μ`. Then either `q` has a section, or `φ`
vanishes on `N`. -/
theorem IsStdFiltered.exists_section_or_eq_zero {N : LieSubmodule K P.KacMoodyAlgebra X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) {μ : Dual K H}
    (q : E →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ) (φ : X →ₗ⁅K,P.KacMoodyAlgebra⁆ E)
    (hker : ∀ ν ∈ s, ∀ g : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ E, q.comp g = 0 → g = 0)
    (heq : ∀ ν ∈ s, ∀ g : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ, g ≠ 0 →
      ν = μ) :
    (∃ σ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ E, ∀ m, q (σ m) = m) ∨
      ∀ x ∈ N, φ x = 0 := by
  induction hN with
  | bot => exact Or.inr fun x hx ↦ by rw [(LieSubmodule.mem_bot x).mp hx, map_zero]
  | @step N₀ N₁ s₀ ν _ hle he ih =>
    rcases ih (fun ν' hν' ↦ hker ν' (Multiset.mem_cons_of_mem hν'))
      (fun ν' hν' ↦ heq ν' (Multiset.mem_cons_of_mem hν')) with hsec | h0
    · exact Or.inl hsec
    obtain ⟨e⟩ := he
    have hker₀ : N₀ ≤ φ.ker := fun x hx ↦ LieModuleHom.mem_ker.mpr (h0 x hx)
    let φ' : (X ⧸ N₀) →ₗ⁅K,P.KacMoodyAlgebra⁆ E := LieSubmodule.Quotient.lift N₀ φ hker₀
    let g : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ E :=
      φ'.comp ((N₁.map (LieSubmodule.Quotient.mk' N₀)).incl.comp e.toLieModuleHom)
    by_cases hqg : q.comp g = 0
    · have hg0 := hker ν (Multiset.mem_cons_self _ _) g hqg
      refine Or.inr fun x hx ↦ ?_
      have hmem : LieSubmodule.Quotient.mk' N₀ x ∈ N₁.map (LieSubmodule.Quotient.mk' N₀) :=
        LieSubmodule.mem_map_of_mem hx
      have hgx : g (e.symm ⟨_, hmem⟩) = φ x := by
        simp only [g, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
          LieModuleEquiv.apply_symm_apply, LieSubmodule.incl_apply]
        rfl
      rw [← hgx, hg0, _root_.zero_apply]
    · have hν := heq ν (Multiset.mem_cons_self _ _) (q.comp g) hqg
      subst hν
      exact Or.inl (exists_section_of_comp_ne_zero P hqg)

end Generic

section Main

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

namespace VermaModule

/-- **Humphreys, GSM 94, Theorem 6.5 (a).** If `Ext¹_𝒪(M(μ), M(λ)) ≠ 0`, then `μ ↑ λ` and
`μ ≠ λ`. Finite type, algebraically closed field of characteristic zero (Humphreys works over
`ℂ`); `Ext¹_𝒪` is `LieModule.ExtOne` relative to the Cartan subalgebra. The induction along the
standard filtration of `P(μ)` is reconstructed (see the module docstring). -/
theorem isStronglyLinked_of_extOne_ne_zero {lam μ : Dual K H}
    {y : ExtOne (h P) (VermaModule P μ) (VermaModule P lam)} (hy : y ≠ 0) :
    P.IsStronglyLinked hA.isGeneralizedCartan μ lam ∧ μ ≠ lam := by
  classical
  refine ⟨?_, fun hμ ↦ hy ?_⟩
  swap
  · subst hμ
    exact extOne_verma_eq_zero P LieModuleHom.id Function.surjective_id
      (fun h ↦ h.2 rfl) y
  obtain ⟨c, rfl⟩ := ExtOne.mk_surjective y
  set q := ExtOne.Extension.snd c
  have hE : IsCategoryO P (ExtOne.Extension c) :=
    (isCategoryO P lam).extension P (isCategoryO P μ) c
  obtain ⟨t, ht, -, -⟩ := ProjectiveCover.exists_isStdFiltered P μ hA
  -- every factor `M(ν)` of `P(μ)` has `[M(ν) : L(μ)] ≠ 0`
  have hmult : ∀ ν ∈ t, (isCategoryO P ν).multiplicity μ ≠ 0 := fun ν hν ↦ by
    rw [← ProjectiveCover.count_eq_multiplicity P μ hA ht ν]
    exact (Multiset.count_pos.mpr hν).ne'
  by_cases hhom : ∃ ν ∈ t, ∃ g : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P lam,
      g ≠ 0
  · obtain ⟨ν, hν, g, hg⟩ := hhom
    exact Relation.ReflTransGen.trans (isStronglyLinked_of_multiplicity_ne_zero P hA
      (multiplicity_ne_zero_of_hom_ne_zero P (φ := g) hg))
      (isStronglyLinked_of_multiplicity_ne_zero P hA (hmult ν hν))
  exfalso
  push Not at hhom
  -- maps `M(ν) → E` killed by `q` land in `M(λ)`, hence vanish
  have hker : ∀ ν ∈ t, ∀ g : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ ExtOne.Extension c,
      q.comp g = 0 → g = 0 := by
    intro ν hν g hg
    let i := ExtOne.Extension.inl c
    let r : i.range ≃ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P lam :=
      (LieModuleEquiv.ofBijective (i.codRestrict i.range fun m ↦ ⟨m, rfl⟩)
        ⟨fun a b hab ↦ ExtOne.Extension.injective_inl c (congrArg Subtype.val hab),
          fun x ↦ by
            obtain ⟨m, hm⟩ := (LieModuleHom.mem_range _ _).mp x.2
            exact ⟨m, Subtype.ext hm⟩⟩).symm
    have hmem : ∀ m, g m ∈ i.range := fun m ↦ by
      obtain ⟨n, hn⟩ := ExtOne.Extension.exists_inl_eq_of_snd_eq_zero c
        (LieModuleHom.congr_fun hg m)
      exact (LieModuleHom.mem_range _ _).mpr ⟨n, hn⟩
    have h0 := hhom ν hν (r.toLieModuleHom.comp (g.codRestrict i.range hmem))
    ext m
    have hm := LieModuleHom.congr_fun h0 m
    rw [LieModuleHom.comp_apply, _root_.zero_apply, LieModuleEquiv.coe_toLieModuleHom] at hm
    have hm' : g.codRestrict i.range hmem m = 0 := by
      simpa using congrArg r.symm hm
    rw [_root_.zero_apply]
    exact congrArg Subtype.val hm'
  -- a nonzero map `M(ν) → M(μ)` forces `ν = μ`
  have heq : ∀ ν ∈ t, ∀ g : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ, g ≠ 0 →
      ν = μ := fun ν hν g hg ↦
    eq_of_mem_cone_of_mem_cone (mem_cone_of_multiplicity_ne_zero
      (multiplicity_ne_zero_of_hom_ne_zero P (φ := g) hg)) (mem_cone_of_multiplicity_ne_zero
        (hmult ν hν))
  -- a map `P(μ) → E` whose composite with `q` is nonzero
  obtain ⟨φ₀, hφ₀⟩ := ProjectiveCover.isProjectiveO P hA μ (isCategoryO P μ)
    (IrreducibleModule.isCategoryO P μ) (LieSubmodule.Quotient.mk' (maxSubmodule P μ))
    (LieSubmodule.Quotient.surjective_mk' _) (ProjectiveCover.π P hA μ)
  obtain ⟨φ, hφ⟩ := ProjectiveCover.isProjectiveO P hA μ hE (isCategoryO P μ) q
    (ExtOne.Extension.surjective_snd c) φ₀
  rcases IsStdFiltered.exists_section_or_eq_zero P ht q φ hker heq with ⟨σ, hσ⟩ | h0
  · exact hy ((ExtOne.mk_eq_zero_iff c).mpr ⟨σ, hσ⟩)
  · apply ProjectiveCover.π_ne_zero P hA μ
    rw [← hφ₀, ← hφ]
    ext x
    rw [LieModuleHom.comp_apply, LieModuleHom.comp_apply, h0 x (LieSubmodule.mem_top x),
      map_zero, map_zero, _root_.zero_apply]

/-- **Humphreys, GSM 94, Theorem 6.5 (b).** Let `λ` be dominant integral and `w, w' ∈ W`. A
nonzero class in `Ext¹_𝒪(M(w'·λ), M(w·λ))` forces `w` strictly below `w'` (Bruhat), hence
`ℓ(w) < ℓ(w')`. Same setting as `isStronglyLinked_of_extOne_ne_zero`. -/
theorem bruhatLT_of_extOne_ne_zero {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
    {w w' : P.weylGroup hA.isGeneralizedCartan}
    {y : ExtOne (h P) (VermaModule P (P.weylDot hA.isGeneralizedCartan w' Λ))
      (VermaModule P (P.weylDot hA.isGeneralizedCartan w Λ))} (hy : y ≠ 0) :
    (P.coxeterSystem hA.isGeneralizedCartan).BruhatLE w w' ∧ w ≠ w' ∧
      (P.coxeterSystem hA.isGeneralizedCartan).length w <
        (P.coxeterSystem hA.isGeneralizedCartan).length w' := by
  obtain ⟨hlink, hne⟩ := isStronglyLinked_of_extOne_ne_zero P hA hy
  obtain ⟨z, hwz, hz⟩ := IsStronglyLinked.exists_bruhatLE_weylDot P hA hΛ hlink
  rw [← weylDot_injective P hA.isGeneralizedCartan hΛ hz] at hwz
  have hww' : w ≠ w' := fun h ↦ hne (by rw [h])
  exact ⟨hwz, hww', hwz.eq_or_length_lt.resolve_left hww'⟩

end VermaModule

end Main

end Matrix.Realization.KacMoodyAlgebra
