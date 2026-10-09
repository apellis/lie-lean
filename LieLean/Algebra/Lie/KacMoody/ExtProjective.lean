/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationWallExt
import LieLean.Algebra.Lie.KacMoody.Projective

/-!
# `Ext¹` in `𝒪` from a projective presentation

The relative `Ext¹` (`LieModule.ExtOne` relative to the Cartan subalgebra, the Yoneda `Ext¹` of
`𝒪`) agrees with the `Ext¹` computed from a projective presentation: if `0 → A → B → C → 0` is
exact with `B ∈ 𝒪` projective in `𝒪`, then for `N ∈ 𝒪`
`Ext¹(C, N) ≅ Hom(A, N) / {g ∘ i | g ∈ Hom(B, N)}`.
In particular, when `C` has a projective resolution `⋯ → P₁ → P₀ → C → 0` in `𝒪` (with
`A = im(P₁ → P₀)`), `ExtOne` is the first right derived functor of `Hom(−, N)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.extOne_eq_zero_of_isProjectiveO`: `Ext¹(P, N) = 0` for `P`
  projective in `𝒪` and `N ∈ 𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.extOneEquivQuotient`: the isomorphism above, given by the
  connecting map.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_extOne_equiv_quotient_ker`: the same for a
  surjection `p : B → C` from a projective, with `A = ker p`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.1, §6.1.
-/

noncomputable section

open Module LieModule

universe w

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

/-- **`Ext¹` vanishes on projectives**: for `X` projective in `𝒪` and `N ∈ 𝒪`, every extension of
`X` by `N` (which lies in `𝒪`, `IsCategoryO.extension`) splits. -/
theorem extOne_eq_zero_of_isProjectiveO {X N : Type w} [AddCommGroup X] [Module K X]
    [LieRingModule 𝔤 X] [LieModule K 𝔤 X] [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N]
    [LieModule K 𝔤 N] (hX : IsCategoryO P X) (hN : IsCategoryO P N)
    (hXp : IsProjectiveO.{w} P X) (y : ExtOne (h P) X N) : y = 0 := by
  obtain ⟨c, rfl⟩ := ExtOne.mk_surjective y
  obtain ⟨σ, hσ⟩ := hXp (hN.extension P hX c) hX (ExtOne.Extension.snd c)
    (ExtOne.Extension.surjective_snd c) LieModuleHom.id
  exact (ExtOne.mk_eq_zero_iff c).mpr ⟨σ, fun m ↦ LieModuleHom.congr_fun hσ m⟩

variable {M M' N : Type*} [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M] [AddCommGroup M'] [Module K M']
  [LieRingModule P.KacMoodyAlgebra M'] [LieModule K P.KacMoodyAlgebra M'] [AddCommGroup N]
  [Module K N] [LieRingModule P.KacMoodyAlgebra N] [LieModule K P.KacMoodyAlgebra N]

variable (N) in
/-- Precomposition `Hom(M', N) → Hom(M, N)`, `g ↦ g ∘ i`. -/
def precompHom (i : M →ₗ⁅K,𝔤⁆ M') : (M' →ₗ⁅K,𝔤⁆ N) →ₗ[K] (M →ₗ⁅K,𝔤⁆ N) where
  toFun g := g.comp i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- **`Ext¹` from a projective presentation.** For an exact sequence `0 → M → B → C → 0` (with an
`𝔥`-equivariant splitting `S`) in which `B ∈ 𝒪` is projective in `𝒪`, and `N ∈ 𝒪`, the connecting
map induces `Hom(M, N) / {g ∘ i} ≅ Ext¹(C, N)`. -/
def extOneEquivQuotient {B C N' : Type w} [AddCommGroup B] [Module K B] [LieRingModule 𝔤 B]
    [LieModule K 𝔤 B] [AddCommGroup C] [Module K C] [LieRingModule 𝔤 C] [LieModule K 𝔤 C]
    [AddCommGroup N'] [Module K N'] [LieRingModule 𝔤 N'] [LieModule K 𝔤 N']
    (hB : IsCategoryO P B) (hN : IsCategoryO P N') (hBp : IsProjectiveO.{w} P B)
    {i : M →ₗ⁅K,𝔤⁆ B} {p : B →ₗ⁅K,𝔤⁆ C} (S : ExtOne.SplitData (h P) i p) :
    ExtOne (h P) C N' ≃ₗ[K] (M →ₗ⁅K,𝔤⁆ N') ⧸ LinearMap.range (precompHom P N' i) :=
  have hsurj : Function.Surjective (S.connecting (N := N')) := fun y ↦
    S.exists_connecting_eq (extOne_eq_zero_of_isProjectiveO P hB hN hBp _)
  have hker : LinearMap.ker (S.connecting (N := N')) = LinearMap.range (precompHom P N' i) := by
    ext f
    rw [LinearMap.mem_ker, S.connecting_eq_zero_iff, LinearMap.mem_range]
    rfl
  ((Submodule.quotEquivOfEq _ _ hker).symm.trans
    ((S.connecting (N := N')).quotKerEquivOfSurjective hsurj)).symm

theorem extOneEquivQuotient_symm_mk {B C N' : Type w} [AddCommGroup B] [Module K B]
    [LieRingModule 𝔤 B] [LieModule K 𝔤 B] [AddCommGroup C] [Module K C] [LieRingModule 𝔤 C]
    [LieModule K 𝔤 C] [AddCommGroup N'] [Module K N'] [LieRingModule 𝔤 N'] [LieModule K 𝔤 N']
    (hB : IsCategoryO P B) (hN : IsCategoryO P N') (hBp : IsProjectiveO.{w} P B)
    {i : M →ₗ⁅K,𝔤⁆ B} {p : B →ₗ⁅K,𝔤⁆ C} (S : ExtOne.SplitData (h P) i p)
    (f : M →ₗ⁅K,𝔤⁆ N') :
    (extOneEquivQuotient P hB hN hBp S).symm (Submodule.Quotient.mk f) = S.connecting f :=
  rfl

/-- **`Ext¹` from a projective cover-type presentation**: for a surjection `p : B → C` in `𝒪` with
`B` projective in `𝒪`, and `N ∈ 𝒪`, `Ext¹(C, N) ≅ Hom(ker p, N) / {g|_{ker p}}`. -/
theorem nonempty_extOne_equiv_quotient_ker {B C N' : Type w} [AddCommGroup B] [Module K B]
    [LieRingModule 𝔤 B] [LieModule K 𝔤 B] [AddCommGroup C] [Module K C] [LieRingModule 𝔤 C]
    [LieModule K 𝔤 C] [AddCommGroup N'] [Module K N'] [LieRingModule 𝔤 N'] [LieModule K 𝔤 N']
    (hB : IsCategoryO P B) (hC : IsCategoryO P C) (hN : IsCategoryO P N')
    (hBp : IsProjectiveO.{w} P B) {p : B →ₗ⁅K,𝔤⁆ C} (hp : Function.Surjective p) :
    Nonempty (ExtOne (h P) C N' ≃ₗ[K]
      (p.ker →ₗ⁅K,𝔤⁆ N') ⧸ LinearMap.range (precompHom P N' p.ker.incl)) := by
  obtain ⟨S⟩ := ExtOne.exists_splitData (h P) hB.1 hC.1 (i := p.ker.incl) (p := p)
    Subtype.val_injective hp fun b ↦ ⟨fun hb ↦ ⟨⟨b, hb⟩, rfl⟩, fun ⟨a, ha⟩ ↦ by
      rw [← ha]; exact a.2⟩
  exact ⟨extOneEquivQuotient P hB hN hBp S⟩

end Matrix.Realization.KacMoodyAlgebra
