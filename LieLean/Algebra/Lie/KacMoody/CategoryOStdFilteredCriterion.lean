/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExtCriterion
import LieLean.Algebra.Lie.KacMoody.DominantVermaTensor

/-!
# The `Ext` criterion for standard filtrations

**[HumO] Theorem 6.13.** For `M ∈ 𝒪` the following are equivalent:
(a) `M` has a standard filtration;
(b) `Extⁿ_𝒪(M, M(λ)^∨) = 0` for all `n > 0` and all `λ ∈ 𝔥*`;
(c) `Ext¹_𝒪(M, M(λ)^∨) = 0` for all `λ ∈ 𝔥*`
(`CategoryO.tfae_isStdFiltered`).

(a) ⇒ (b) is Theorem 6.12 (`CategoryO.ext_dualVerma_eq_zero_of_isStdFiltered`). For (c) ⇒ (a)
Humphreys inducts on the length of `M`; here the induction runs over the submodules `N` of a fixed
object `X`, ordered by inclusion (an artinian lattice), and proves that `N` has a standard
filtration if `Ext¹(N, M(λ)^∨) = 0` for all `λ` (`CategoryO.isStdFiltered_of_ext_one`). For
`N ≠ 0`, choose `λ` minimal with `Hom(N, L(λ)) ≠ 0` (step (1)); steps (2) and (3)
(`CategoryO.ext_one_simple_eq_zero`, `CategoryO.exists_lift_verma`) lift a nonzero morphism
`N → L(λ)` to a surjection `N → M(λ)`, and its kernel `N₀ < N` satisfies the hypothesis again,
by the long exact sequence and `Ext²(M(λ), M(μ)^∨) = 0` (step (4)).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.13.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe w u

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

/-- `Extⁿ(X₁, Y) = 0` if `Extⁿ(X₂, Y) = 0 = Extⁿ⁺¹(X₃, Y)` for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`. -/
theorem eq_zero_of_shortExact_left_succ {S : ShortComplex C} (hS : S.ShortExact) {Y : C}
    {n : ℕ} (h₂ : ∀ x : Ext.{w} S.X₂ Y n, x = 0) (h₃ : ∀ x : Ext.{w} S.X₃ Y (1 + n), x = 0)
    (x : Ext.{w} S.X₁ Y n) : x = 0 := by
  obtain ⟨x₂, rfl⟩ := contravariant_sequence_exact₁ hS Y x rfl (h₃ _)
  rw [h₂ x₂]
  simp

end CategoryTheory.Abelian.Ext

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-- `Extⁿ(-, Z)` vanishes together on objects of `𝒪` with isomorphic underlying `𝔤`-modules. -/
theorem ext_eq_zero_of_equiv_left {Y Y' Z : CategoryO.{u} P} (e : Y.obj ≃ₗ⁅K,𝔤⁆ Y'.obj) {n : ℕ}
    (h : ∀ x : Abelian.Ext.{u} Y Z n, x = 0) (x : Abelian.Ext.{u} Y' Z n) : x = 0 := by
  let f : Y ⟶ Y' := (IsObj.{u} P).homMk (ofLieModuleHom e.toLieModuleHom)
  let g : Y' ⟶ Y := (IsObj.{u} P).homMk (ofLieModuleHom e.symm.toLieModuleHom)
  have hgf : g ≫ f = 𝟙 Y' := by
    ext y
    exact e.apply_symm_apply y
  have hx : x = (Abelian.Ext.mk₀ g).comp ((Abelian.Ext.mk₀ f).comp x (zero_add n))
      (zero_add n) := by
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, hgf, Abelian.Ext.mk₀_id_comp]
  rw [hx, h ((Abelian.Ext.mk₀ f).comp x _)]
  simp

/-- Step (1) of the proof of [HumO] Theorem 6.13: a nonzero object of `𝒪` has a nonzero morphism
to some `L(λ)` with `λ` minimal among such weights. -/
theorem exists_minimal_hom_simple (Y : CategoryO.{u} P) (hY : ¬ Subsingleton Y.obj) :
    ∃ lam : Dual K H, ∃ φ : Y.obj →ₗ⁅K,𝔤⁆ IrreducibleModule P lam, φ ≠ 0 ∧
      ∀ ν ∈ cone P lam, ν ≠ lam → ∀ ψ : Y.obj →ₗ⁅K,𝔤⁆ IrreducibleModule P ν, ψ = 0 := by
  have hA : A.IsFiniteCartan := Fact.out
  obtain ⟨S, hS⟩ := Y.property.2
  have := Y.property.1.wellFoundedGT_lieSubmodule P hA hS
  obtain ⟨f, hf⟩ := Y.property.1.exists_strictMono_lieSubmodule P hA hS
  let T : Set (Dual K H) := {ν | ∃ ψ : Y.obj →ₗ⁅K,𝔤⁆ IrreducibleModule P ν, ψ ≠ 0}
  have hT : T.Nonempty := by
    by_contra hT
    refine hY ⟨fun a b ↦ ?_⟩
    have hid := Y.property.1.lieModuleHom_eq_zero (fun ν _ ψ ↦ by
      by_contra hψ
      exact hT ⟨ν, ψ, hψ⟩) (LieModuleHom.id : Y.obj →ₗ⁅K,𝔤⁆ Y.obj)
    have ha : a = 0 := LieModuleHom.congr_fun hid a
    have hb : b = 0 := LieModuleHom.congr_fun hid b
    rw [ha, hb]
  obtain ⟨lam, ⟨φ, hφ⟩, hmin⟩ := Y.property.1.exists_minimal_of_multiplicity_ne_zero hf
    (S := T) (fun ν ⟨ψ, hψ⟩ ↦ Y.property.1.multiplicity_ne_zero_of_lieModuleHom ψ hψ) hT
  refine ⟨lam, φ, hφ, fun ν hν hne ψ ↦ ?_⟩
  by_contra hψ
  exact hne (hmin ν ⟨ψ, hψ⟩ hν)

/-- The induction of [HumO] Theorem 6.13 (c) ⇒ (a), over the submodules of a fixed object `X`:
a submodule `N` with `Ext¹(N, M(λ)^∨) = 0` for all `λ` has a standard filtration. -/
theorem isStdFiltered_of_ext_one (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj)
    (hN : ∀ (lam : Dual K H) (x : Abelian.Ext.{u} (ofSub X N) (dualVerma P lam) 1), x = 0) :
    ∃ s, IsStdFiltered P N s := by
  have hA : A.IsFiniteCartan := Fact.out
  obtain ⟨S, hS⟩ := X.property.2
  have := X.property.1.wellFoundedLT_lieSubmodule P hA hS
  revert hN
  induction N using WellFoundedLT.induction with
  | ind N ih =>
  intro hN
  by_cases h0 : N = ⊥
  · subst h0
    exact ⟨0, IsStdFiltered.bot⟩
  let Y := ofSub X N
  have hY : ¬ Subsingleton Y.obj := by
    intro hsub
    refine h0 (eq_bot_iff.mpr fun x hx ↦ ?_)
    have h1 : ofLieEquiv (P := P) N ⟨x, hx⟩ = 0 := @Subsingleton.elim _ hsub _ _
    rw [LieSubmodule.mem_bot]
    exact congrArg Subtype.val ((ofLieEquiv (P := P) N).injective
      (h1.trans (map_zero (ofLieEquiv (P := P) N)).symm))
  -- step (1): a minimal `λ` with `Hom(N, L(λ)) ≠ 0`
  obtain ⟨lam, φ, hφ, hbelow⟩ := exists_minimal_hom_simple Y hY
  -- step (2): `Ext¹(N, L(μ)) = 0` for `μ < λ`
  have hext : ∀ μ ∈ cone P lam, μ ≠ lam → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P μ) → ∀ x : Abelian.Ext.{u} Y Z 1, x = 0 :=
    fun μ hμ hne Z e ↦ ext_one_simple_eq_zero Y μ (hN μ) (fun ν hν hνne ↦
      hbelow ν (mem_cone_trans hν hμ) fun h ↦ hne (eq_of_mem_cone_of_mem_cone hμ (h ▸ hν))) Z e
  -- step (3): a surjection `N → M(λ)`
  obtain ⟨ψ, hψ⟩ := exists_lift_verma Y lam hext φ
  have hψs : Function.Surjective ψ := by
    rw [← LieModuleHom.range_eq_top]
    by_contra hr
    refine hφ ?_
    rw [← hψ]
    ext y
    exact (LieSubmodule.Quotient.mk_eq_zero (N := VermaModule.maxSubmodule P lam)).mpr
      ((VermaModule.le_maxSubmodule_iff P lam _).mpr hr
        ((LieModuleHom.mem_range ψ (ψ y)).mpr ⟨y, rfl⟩))
  let g : N →ₗ⁅K,𝔤⁆ VermaModule P lam := ψ.comp (ofLieEquiv (P := P) N).toLieModuleHom
  have hgs : Function.Surjective g := hψs.comp (ofLieEquiv (P := P) N).surjective
  -- step (4): the kernel `N₀` of `N → M(λ)`
  let N₀ : LieSubmodule K 𝔤 X.obj := g.ker.map N.incl
  have hmem (y : N) : (y : X.obj) ∈ N₀ ↔ g y = 0 := by
    rw [LieSubmodule.mem_map]
    refine ⟨fun ⟨z, hz, hzy⟩ ↦ ?_, fun hy ↦ ⟨y, hy, rfl⟩⟩
    rw [← LieModuleHom.mem_ker, ← Subtype.ext hzy]
    exact hz
  have hle : N₀ ≤ N := fun x hx ↦ by
    obtain ⟨z, -, rfl⟩ := (LieSubmodule.mem_map x).mp hx
    exact z.2
  have hlt : N₀ < N := lt_of_le_of_ne hle fun heq ↦ by
    obtain ⟨y, hy⟩ := hgs (VermaModule.hwv P lam)
    have hy0 : g y = 0 := (hmem y).mp (by rw [heq]; exact y.2)
    exact VermaModule.hwv_ne_zero P lam (hy.symm.trans hy0)
  let g' : N →ₗ⁅K,𝔤⁆ (verma P lam).obj :=
    (ofLieEquiv (P := P) (VermaModule P lam)).toLieModuleHom.comp g
  have hS' := shortExact_subComplex X hle (verma P lam) g'
    (fun x hx ↦ by
      change ofLieEquiv (P := P) (VermaModule P lam) (g ⟨x, hle hx⟩) = 0
      rw [(hmem ⟨x, hle hx⟩).mp hx, map_zero])
    ((ofLieEquiv (P := P) (VermaModule P lam)).surjective.comp hgs)
    fun y hy ↦ (hmem y).mpr ((ofLieEquiv (P := P) (VermaModule P lam)).injective
      (hy.trans (map_zero (ofLieEquiv (P := P) (VermaModule P lam))).symm))
  obtain ⟨s, hs⟩ := ih N₀ hlt fun μ ↦ Abelian.Ext.eq_zero_of_shortExact_left_succ hS' (hN μ)
    (ext_verma_dualVerma_eq_zero lam μ (by norm_num))
  -- the step `N / N₀ ≅ M(λ)`
  have hker : g.ker = N₀.comap N.incl := by
    ext y
    rw [LieModuleHom.mem_ker, LieSubmodule.mem_comap]
    exact (hmem y).symm
  obtain ⟨e₁⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective _ g hgs hker
  obtain ⟨e₂⟩ := LieSubmodule.nonempty_subquotientEquivMap N₀ N
  exact ⟨lam ::ₘ s, hs.step hle ⟨e₁.symm.trans e₂⟩⟩

/-- **[HumO] Theorem 6.13** (Ext criterion for standard filtrations). For `X ∈ 𝒪` the following
are equivalent: (a) `X` has a standard filtration; (b) `Extⁿ_𝒪(X, M(λ)^∨) = 0` for all `n > 0`
and all `λ`; (c) `Ext¹_𝒪(X, M(λ)^∨) = 0` for all `λ`. Finite type, algebraically closed field of
characteristic zero (Humphreys works over `ℂ`). -/
theorem tfae_isStdFiltered (X : CategoryO.{u} P) :
    List.TFAE [∃ s, IsStdFiltered P (⊤ : LieSubmodule K 𝔤 X.obj) s,
      ∀ (lam : Dual K H) (n : ℕ), 0 < n → ∀ x : Abelian.Ext.{u} X (dualVerma P lam) n, x = 0,
      ∀ (lam : Dual K H) (x : Abelian.Ext.{u} X (dualVerma P lam) 1), x = 0] := by
  tfae_have 1 → 2 := fun ⟨s, hs⟩ lam n hn x ↦ ext_dualVerma_eq_zero_of_isStdFiltered X hs lam hn x
  tfae_have 2 → 3 := fun h lam x ↦ h lam 1 Nat.one_pos x
  tfae_have 3 → 1 := fun h ↦ isStdFiltered_of_ext_one X ⊤ fun lam ↦
    ext_eq_zero_of_equiv_left (Y := X) ((LieModuleEquiv.ofBijective
      (⊤ : LieSubmodule K 𝔤 X.obj).incl
      ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, LieSubmodule.mem_top y⟩, rfl⟩⟩).symm.trans
      (ofLieEquiv (P := P) (⊤ : LieSubmodule K 𝔤 X.obj))) (h lam)
  tfae_finish

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
