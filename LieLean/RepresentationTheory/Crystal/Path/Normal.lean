/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.FiniteRankTwo
import LieLean.RepresentationTheory.Crystal.Levi
import LieLean.RepresentationTheory.Crystal.Path.LittelmannIsomorphism
import LieLean.RepresentationTheory.Crystal.Path.WeylGroupAction

/-!
# Normal crystals and Kashiwara's action of the Weyl group

A crystal `B` over a generalized Cartan matrix `A` is *normal* in Kashiwara's sense
([Kas94] §1.5, [Kas] §7.6) if it is seminormal and, for every subset `J` of the index set of
finite type, the restriction of `B` to the colours in `J` is isomorphic to the crystal of the
crystal base of an integrable `U_q(𝔤_J)`-module, i.e. is a disjoint union of crystals `B_J(ν)` of
irreducible highest weight modules.

Crystal bases of `U_q`-modules are not formalized in this library. We define normality relative
to Littelmann's path model [Lit95] instead (`Crystal.IsNormal`): `B` is seminormal and, for every
`J : Finset ι` such that the principal submatrix `A_J` is of finite type (Mathlib's
`Matrix.IsFiniteCartan`), every element of `B` lies in the image of an injective Levi morphism
(`Crystal.IsLeviHom`) `B_J(ν) → B` from the path crystal `B_J(ν)` of a dominant integral weight
`ν` of the standard realization of `A_J` (`Crystal.leviPathCrystal`). This agrees with
Kashiwara's definition by the theorems identifying `B_J(ν)` with the crystal of the crystal base
of the irreducible `U_q(𝔤_J)`-module of highest weight `ν` (Kashiwara; Joseph), which are not
formalized here. Since `B_J(ν)` is connected and a Levi morphism intertwines the operators of
the colours in `J`, its image is a `J`-component of `B`; so the condition says that every
`J`-component of `B` is a copy of some `B_J(ν)`.

## Main definitions

* `Crystal.leviPathCrystal`: the path crystal `B_J(ν)` of the standard realization of `A_J`.
* `Crystal.IsNormal`: normal crystals, relative to the path model.
* `Crystal.IsNormal.weylAction`: **Kashiwara's action of the Weyl group** on a normal crystal,
  `W →* Perm B` with `sᵢ ↦ Sᵢ` ([Kas] Thm. 11.1, [Kas94] §7).

## Main results

* `Crystal.IsNormal.reflectionPerm_mul_pow`: Kashiwara's reflections satisfy the Coxeter relations
  `(SᵢSⱼ)^{mᵢⱼ} = 1` of the Weyl group on every normal crystal ([Kas94] Thm. 7.2.2); they are
  transported from the braid relations on the path crystals of the rank-two Levi data
  (`Matrix.Realization.pathBraidRelations`).
* `Crystal.IsNormal.coe_wt_weylAction`: `wt (w • b) = w (wt b)`.
* `Matrix.Realization.isNormal_pathCrystal`: Littelmann's path crystals `B(Λ)` are normal, by
  Levi restriction (`LSGeneralClass.LeviMap.exists_leviHom_pathCrystal`).
* `Crystal.IsNormal.sum`, `Crystal.IsNormal.sigma`, `Crystal.IsNormal.tensor`: disjoint unions and
  tensor products of normal crystals are normal; the tensor product case uses Littelmann's
  decomposition of `B_J(ν₁) ⊗ B_J(ν₂)` (`LSGeneralClass.nonempty_equiv_sigma_of_finiteDimensional`).

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.6 (normal crystals;
  Prop. 7.1: it suffices to consider `J` with at most two elements), §11, Thm. 11.1 (the action of
  the Weyl group).
* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413, §1.5 (normal crystals), §7.1 (the reflections `Sᵢ`), Thm. 7.2.2 (the
  braid relations).
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2)
  **142** (1995), 499–525.

Kashiwara works with symmetrizable Cartan data and the crystals of `U_q(𝔤)`; here `A` is an
arbitrary generalized Cartan matrix. The finite-type subsets `J` are those for which `A_J` is
symmetrizable with positive definite symmetrization, as in [Kas94] §1.5. The braid relations are
proved via the path model (folding for `B₂` and `G₂`), not by Kashiwara's argument, which uses
tensor powers and the lowest weight elements of rank-two crystals.
-/

open Set Module LittelmannPath

/-! ### Levi restriction of path crystals -/

namespace Matrix.Realization.LSGeneralClass

variable {ι κ H H' : Type*} [Fintype ι] [Fintype κ] [AddCommGroup H] [Module ℝ H]
  [AddCommGroup H'] [Module ℝ H']
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}
  {e : κ → ι} {Q : Realization (A.submatrix e e) ℝ H'}
  {hA' : (A.submatrix e e).IsGeneralizedCartan}

/-- Every realization of a principal submatrix admits a restriction map (for `κ` empty the
restriction map is `0`; otherwise `𝔥` is finite-dimensional and `exists_leviMap` applies). -/
theorem nonempty_leviMap (he : Function.Injective e) (Q : Realization (A.submatrix e e) ℝ H') :
    Nonempty (LeviMap P e Q) := by
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨k⟩⟩
  · exact ⟨⟨0, fun k => isEmptyElim k, fun _ k => isEmptyElim k⟩⟩
  · have : FiniteDimensional ℝ H := by
      apply Module.finite_of_finrank_pos
      have h1 := P.finrank_add_rank
      have h2 := (A.map (Int.cast : ℤ → ℝ)).rank_le_card_width
      have h3 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨e k⟩
      omega
    exact exists_leviMap he Q

omit [Fintype κ] in
theorem mem_jComponent_self (y : LittelmannPath (P.pathSpace hA)) : y ∈ jComponent e y :=
  ⟨[], rfl⟩

omit [Fintype κ] in
/-- The `J`-component of `y` lies in every stable set containing `y`. -/
theorem jComponent_subset {U : Set (LittelmannPath (P.pathSpace hA))}
    (hU : (crystal (P.pathSpace hA)).IsStable U) {y : LittelmannPath (P.pathSpace hA)}
    (hy : y ∈ U) : jComponent e y ⊆ U := by
  rintro x ⟨u, hu⟩
  induction u generalizing y with
  | nil =>
    cases hu
    exact hy
  | cons a u ih =>
    obtain ⟨ρ, ha, hl⟩ := Option.bind_eq_some_iff.mp hu
    exact ih (rootStep_mem hU hy ha) hl

omit [Fintype κ] in
/-- The `J`-component of `y` is stable under the root operators of colours in `J`. -/
theorem mem_jComponent_of_rootStep {y z z' : LittelmannPath (P.pathSpace hA)}
    (hz : z ∈ jComponent e y) (a : κ ⊕ κ) (h : rootStep (Sum.map e e a) z = some z') :
    z' ∈ jComponent e y := by
  obtain ⟨u, hu⟩ := hz
  refine ⟨u ++ [a], ?_⟩
  rw [LeviMap.liftWord] at hu
  rw [LeviMap.liftWord, List.map_append, rootWord_append, hu, Option.bind_some]
  change (rootStep (Sum.map e e a) z).bind (rootWord []) = some z'
  rw [h]
  rfl

/-- **Levi restriction of `B(Λ)` as Levi morphisms**: for a restriction map `L` to a
finite-dimensional realization `Q` of `A_J`, every element of `B(Λ)` lies in the image of an
injective Levi morphism `B_Q(ν) → B(Λ)` from the path crystal of a dominant integral weight `ν`
of `Q`. This is a reformulation of `LeviMap.exists_jHighest_componentIso`: the morphism is the
inverse of the restriction `π ↦ r ∘ π` on a `J`-component, composed with the isomorphism
`B_Q(ν) ≅ B(r ∘ y)`, `y` a `J`-highest path. -/
theorem LeviMap.exists_leviHom_pathCrystal [FiniteDimensional ℝ H'] (L : LeviMap P e Q)
    {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ∃ (ν : Dual ℝ H') (hν : Q.IsDominantIntegral ν)
      (Φ : (straightLine (Q.pathSpace hA') ⟨ν, hν.mem_integralWeights⟩).component →
        (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component),
      Function.Injective Φ ∧
        Crystal.IsLeviHom (Q.pathCrystal hA' hν) (P.pathCrystal hA hΛ) e Φ ∧ b ∈ range Φ := by
  obtain ⟨y, hyB, hye, hJ, hbij, ψ, -⟩ := L.exists_jHighest_componentIso (hA' := hA') hΛ b.2
  have hsemi := isSeminormal_pathCrystal hA hΛ
  -- the highest weight `r(y(1))` of the Levi component is dominant
  have hν : Q.IsDominantIntegral ((L.restrict (hA' := hA') y).wt : Dual ℝ H') := by
    intro k
    have he : (P.pathCrystal hA hΛ).e (e k) ⟨y, hyB⟩ = none := by
      have h := Crystal.restrict_e (isStable_component _) (e k) ⟨y, hyB⟩
      rw [crystal_e, hye k] at h
      exact Option.map_eq_none_iff.mp h
    have hφ := hsemi.φ_nonneg (e k) ⟨y, hyB⟩
    rw [(P.pathCrystal hA hΛ).φ_eq, hsemi.ε_eq_zero he, zero_add] at hφ
    have hφ' : 0 ≤ (P.cartanDatum hA).coroot (e k) ((P.pathCrystal hA hΛ).wt ⟨y, hyB⟩) := by
      exact_mod_cast hφ
    refine ⟨((P.cartanDatum hA).coroot (e k) ((P.pathCrystal hA hΛ).wt ⟨y, hyB⟩)).toNat, ?_⟩
    have hcast : ((((P.cartanDatum hA).coroot (e k)
        ((P.pathCrystal hA hΛ).wt ⟨y, hyB⟩)).toNat : ℕ) : ℝ) =
        (((P.cartanDatum hA).coroot (e k) ((P.pathCrystal hA hΛ).wt ⟨y, hyB⟩) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hφ'
    rw [hcast, coroot_cartanDatum_cast]
    exact L.apply_coroot _ k
  have : Nonempty (LittelmannPath (P.pathSpace hA)) := ⟨y⟩
  let g : (straightLine (Q.pathSpace hA') ⟨_, hν.mem_integralWeights⟩).component →
      LittelmannPath (P.pathSpace hA) := fun x =>
    Function.invFunOn (L.restrict (hA' := hA')) (jComponent e y) (ψ x).1
  have hg : ∀ x, g x ∈ jComponent e y ∧ L.restrict (hA' := hA') (g x) = (ψ x).1 := fun x => by
    have hex : ∃ z ∈ jComponent e y, L.restrict (hA' := hA') z = (ψ x).1 := hbij.surjOn (ψ x).2
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hsub := jComponent_subset (e := e) (isStable_component _) hyB
  let Φ : (straightLine (Q.pathSpace hA') ⟨_, hν.mem_integralWeights⟩).component →
      (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component :=
    fun x => ⟨g x, hsub (hg x).1⟩
  -- the root operators on the three component crystals involved
  have hPe : ∀ (i : ι) (c : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component),
      ((P.pathCrystal hA hΛ).e i c).map Subtype.val = LittelmannPath.e i c.1 :=
    fun i c => Crystal.restrict_e (isStable_component _) i c
  have hPf : ∀ (i : ι) (c : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component),
      ((P.pathCrystal hA hΛ).f i c).map Subtype.val = LittelmannPath.f i c.1 :=
    fun i c => Crystal.restrict_f (isStable_component _) i c
  have hRe : ∀ (k : κ) (c : (L.restrict (hA' := hA') y).component),
      ((L.restrict (hA' := hA') y).componentCrystal.e k c).map Subtype.val =
        LittelmannPath.e k c.1 :=
    fun k c => Crystal.restrict_e (isStable_component _) k c
  have hRf : ∀ (k : κ) (c : (L.restrict (hA' := hA') y).component),
      ((L.restrict (hA' := hA') y).componentCrystal.f k c).map Subtype.val =
        LittelmannPath.f k c.1 :=
    fun k c => Crystal.restrict_f (isStable_component _) k c
  refine ⟨_, hν, Φ, fun x x' hxx' => ?_, ⟨fun k x => ?_, fun k x => ?_, fun k x => ?_⟩, ?_⟩
  · -- injectivity
    have h1 : g x = g x' := congrArg Subtype.val hxx'
    have h2 : (ψ x).1 = (ψ x').1 := by rw [← (hg x).2, ← (hg x').2, h1]
    exact EquivLike.injective ψ (Subtype.ext h2)
  · -- `ẽₖ`
    have key : ((Q.pathCrystal hA' hν).e k x).map (fun x => (ψ x).1) =
        (LittelmannPath.e (e k) (g x)).map (L.restrict (hA' := hA')) := by
      rw [← L.e_restrict, (hg x).2, ← hRe k (ψ x), ψ.e_apply, Option.map_map]
      rfl
    apply Option.map_injective Subtype.val_injective
    rw [Option.map_map, hPe]
    change ((Q.pathCrystal hA' hν).e k x).map g = LittelmannPath.e (e k) (g x)
    cases hx' : (Q.pathCrystal hA' hν).e k x with
    | none =>
      rw [hx', Option.map_none] at key
      rw [Option.map_none, eq_comm, ← Option.map_eq_none_iff (f := L.restrict (hA' := hA')),
        ← key]
    | some x' =>
      rw [hx', Option.map_some] at key
      obtain ⟨z', hz', hrz'⟩ := Option.map_eq_some_iff.mp key.symm
      have hz'mem : z' ∈ jComponent e y := mem_jComponent_of_rootStep (hg x).1 (Sum.inl k) hz'
      have : g x' = z' := hbij.injOn (hg x').1 hz'mem ((hg x').2.trans hrz'.symm)
      rw [Option.map_some, hz', this]
  · -- `f̃ₖ`
    have key : ((Q.pathCrystal hA' hν).f k x).map (fun x => (ψ x).1) =
        (LittelmannPath.f (e k) (g x)).map (L.restrict (hA' := hA')) := by
      rw [← L.f_restrict, (hg x).2, ← hRf k (ψ x), ψ.f_apply, Option.map_map]
      rfl
    apply Option.map_injective Subtype.val_injective
    rw [Option.map_map, hPf]
    change ((Q.pathCrystal hA' hν).f k x).map g = LittelmannPath.f (e k) (g x)
    cases hx' : (Q.pathCrystal hA' hν).f k x with
    | none =>
      rw [hx', Option.map_none] at key
      rw [Option.map_none, eq_comm, ← Option.map_eq_none_iff (f := L.restrict (hA' := hA')),
        ← key]
    | some x' =>
      rw [hx', Option.map_some] at key
      obtain ⟨z', hz', hrz'⟩ := Option.map_eq_some_iff.mp key.symm
      have hz'mem : z' ∈ jComponent e y := mem_jComponent_of_rootStep (hg x).1 (Sum.inr k) hz'
      have : g x' = z' := hbij.injOn (hg x').1 hz'mem ((hg x').2.trans hrz'.symm)
      rw [Option.map_some, hz', this]
  · -- weights
    apply Int.cast_injective (α := ℝ)
    rw [coroot_cartanDatum_cast, coroot_cartanDatum_cast]
    have hw : (Q.pathCrystal hA' hν).wt x = (L.restrict (hA' := hA') y).componentCrystal.wt (ψ x) :=
      (ψ.wt_apply x).symm
    rw [hw]
    change ((g x).wt : Dual ℝ H) (P.coroot (e k)) =
      (((ψ x).1.wt : Dual ℝ H') (Q.coroot k))
    rw [← (hg x).2]
    exact (L.apply_coroot _ k).symm
  · -- `b` is in the image
    have hb : b.1 ∈ jComponent e y := hJ ▸ mem_jComponent_self b.1
    obtain ⟨x, hx⟩ := EquivLike.surjective ψ ⟨_, hbij.mapsTo hb⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact hbij.injOn (hg x).1 hb ((hg x).2.trans (congrArg Subtype.val hx))

end Matrix.Realization.LSGeneralClass

/-! ### Disjoint unions of families -/

namespace Crystal

section Sigma

variable {ι κ X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {D : CartanDatum ι X}
  {D' : CartanDatum κ Y} {α : Type*} {e : κ → ι}

/-- A disjoint union of seminormal crystals is seminormal. -/
theorem IsSeminormal.sigma {B : α → Type*} {C : ∀ a, Crystal D (B a)}
    (h : ∀ a, (C a).IsSeminormal) : (Crystal.sigma C).IsSeminormal := by
  rw [isSeminormal_iff]
  rintro i ⟨a, b⟩
  refine ⟨(h a).ε_nonneg i b, (h a).φ_nonneg i b, fun he => (h a).ε_eq_zero ?_,
    fun hf => (h a).φ_eq_zero ?_⟩
  · exact Option.map_eq_none_iff.mp he
  · exact Option.map_eq_none_iff.mp hf

/-- Composition with the inclusion of a member of a disjoint union. -/
theorem IsLeviHom.sigmaMk {B : α → Type*} {C : ∀ a, Crystal D (B a)} {B' : Type*}
    {C' : Crystal D' B'} {a : α} {Φ : B' → B a} (h : IsLeviHom C' (C a) e Φ) :
    IsLeviHom C' (Crystal.sigma C) e (Sigma.mk a ∘ Φ) where
  map_e k b := by
    change _ = ((C a).e (e k) (Φ b)).map (Sigma.mk a)
    rw [← h.map_e, Option.map_map]
  map_f k b := by
    change _ = ((C a).f (e k) (Φ b)).map (Sigma.mk a)
    rw [← h.map_f, Option.map_map]
  coroot_wt k b := h.coroot_wt k b

/-- The restriction of a Levi morphism out of a disjoint union to one member. -/
theorem IsLeviHom.comp_sigmaMk {B' : α → Type*} {C' : ∀ a, Crystal D' (B' a)} {B : Type*}
    {C : Crystal D B} {Φ : (Σ a, B' a) → B} (h : IsLeviHom (Crystal.sigma C') C e Φ) (a : α) :
    IsLeviHom (C' a) C e (Φ ∘ Sigma.mk a) where
  map_e k b := by
    rw [Function.comp_apply, ← h.map_e]
    change _ = (((C' a).e k b).map (Sigma.mk a)).map Φ
    rw [Option.map_map]
  map_f k b := by
    rw [Function.comp_apply, ← h.map_f]
    change _ = (((C' a).f k b).map (Sigma.mk a)).map Φ
    rw [Option.map_map]
  coroot_wt k b := h.coroot_wt k ⟨a, b⟩

end Sigma

end Crystal

/-! ### Normal crystals -/

namespace Crystal

open Matrix Matrix.Realization

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} (hA : A.IsGeneralizedCartan)

/-- The path crystal `B_J(ν)` of a dominant integral weight `ν` of the standard realization of
the principal submatrix `A_J = (aᵢⱼ)_{i, j ∈ J}`. -/
noncomputable abbrev leviPathCrystal (J : Finset ι)
    {ν : Dual ℝ (StdSpace (A.submatrix ((↑) : J → ι) (↑)) ℝ)}
    (hν : (Realization.std (A.submatrix ((↑) : J → ι) (↑)) ℝ).IsDominantIntegral ν) :=
  (Realization.std (A.submatrix ((↑) : J → ι) (↑)) ℝ).pathCrystal
    (LSGeneralClass.isGeneralizedCartan_submatrix hA Subtype.val_injective) hν

variable {hA} {B B₁ B₂ : Type*}

/-- **Normal crystals, relative to the path model.** A crystal `C` over the Cartan datum of a
realization of a generalized Cartan matrix `A` is normal if it is seminormal and, for every
`J ⊆ ι` such that `A_J` is of finite type, every element of `C` lies in the image of an injective
Levi morphism `B_J(ν) → C` (`Crystal.IsLeviHom` along the inclusion `J ⊆ ι`) from the path crystal
`B_J(ν)` of a dominant integral weight `ν` of the standard realization of `A_J`.

Kashiwara's definition ([Kas94] §1.5, [Kas] §7.6) asks instead that the restriction of `C` to `J`
be isomorphic to the crystal of the crystal base of an integrable `U_q(𝔤_J)`-module. The two agree
by the theorems identifying `B_J(ν)` with the crystal of the crystal base of the irreducible
`U_q(𝔤_J)`-module of highest weight `ν` (Kashiwara; Joseph), which are not formalized here. -/
structure IsNormal (C : Crystal (P.cartanDatum hA) B) : Prop where
  isSeminormal : C.IsSeminormal
  exists_leviHom : ∀ J : Finset ι, (A.submatrix ((↑) : J → ι) (↑)).IsFiniteCartan → ∀ b : B,
    ∃ (ν : Dual ℝ (StdSpace (A.submatrix ((↑) : J → ι) (↑)) ℝ))
      (hν : (Realization.std (A.submatrix ((↑) : J → ι) (↑)) ℝ).IsDominantIntegral ν)
      (Φ : (straightLine ((Realization.std (A.submatrix ((↑) : J → ι) (↑)) ℝ).pathSpace
          (LSGeneralClass.isGeneralizedCartan_submatrix hA Subtype.val_injective))
          ⟨ν, hν.mem_integralWeights⟩).component → B),
      Function.Injective Φ ∧ IsLeviHom (leviPathCrystal hA J hν) C (↑) Φ ∧ b ∈ Set.range Φ

namespace IsNormal

variable {C : Crystal (P.cartanDatum hA) B}

/-- **The braid relations on normal crystals** ([Kas94] Thm. 7.2.2): Kashiwara's reflections
satisfy `(SᵢSⱼ)^{mᵢⱼ} = 1` for all `i, j`, where `(mᵢⱼ)` is the Coxeter matrix of the Weyl group.
For `mᵢⱼ < ∞` the subset `J = {i, j}` is of finite type, and the relation is transported along
the Levi morphisms `B_J(ν) → C` from the path crystals `B_J(ν)`
(`Matrix.Realization.pathBraidRelations`). -/
theorem reflectionPerm_mul_pow (hC : C.IsNormal) (i j : ι) :
    (hC.isSeminormal.reflectionPerm i * hC.isSeminormal.reflectionPerm j) ^ A.coxeterMatrix i j =
      1 := by
  by_cases hij : i = j
  · subst hij
    rw [A.coxeterMatrix.diagonal, pow_one]
    ext b
    simp only [Equiv.Perm.mul_apply, IsSeminormal.reflectionPerm_apply, Equiv.Perm.one_apply]
    exact hC.isSeminormal.reflection_reflection i b
  by_cases hM : A.coxeterMatrix i j = 0
  · rw [hM, pow_zero]
  have h3 : A i j * A j i ≤ 3 := by
    by_contra h
    exact hM (by rw [A.coxeterMatrix_apply_of_ne hij]; exact coxeterEntry_of_four_le (by omega))
  set J : Finset ι := {i, j} with hJdef
  have hi : i ∈ J := by simp [hJdef]
  have hj : j ∈ J := by simp [hJdef]
  have hij' : (⟨i, hi⟩ : J) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
  have hA' := LSGeneralClass.isGeneralizedCartan_submatrix (e := ((↑) : J → ι)) hA
    Subtype.val_injective
  have hJ : (A.submatrix ((↑) : J → ι) (↑)).IsFiniteCartan :=
    hA'.isFiniteCartan_of_mul_le_three hij'
      (fun k => by
        rcases Finset.mem_insert.mp k.2 with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp h)))
      (by simpa using h3)
  ext b
  obtain ⟨ν, hν, Φ, -, hΦ, x, rfl⟩ := hC.exists_leviHom J hJ b
  have hQ := isLiftable_pathReflectionPerm hA' hν (pathBraidRelations hA' hν) ⟨i, hi⟩ ⟨j, hj⟩
  have hm : (A.submatrix ((↑) : J → ι) (↑)).coxeterMatrix ⟨i, hi⟩ ⟨j, hj⟩ =
      A.coxeterMatrix i j := by
    rw [coxeterMatrix_apply_of_ne _ hij', coxeterMatrix_apply_of_ne _ hij]
    rfl
  rw [hm] at hQ
  have hsemi : Function.Semiconj Φ
      (pathReflectionPerm _ hA' hν ⟨i, hi⟩ * pathReflectionPerm _ hA' hν ⟨j, hj⟩)
      (hC.isSeminormal.reflectionPerm i * hC.isSeminormal.reflectionPerm j) := fun y => by
    simp only [Equiv.Perm.mul_apply, IsSeminormal.reflectionPerm_apply]
    rw [hΦ.map_reflection (isSeminormal_pathCrystal hA' hν) hC.isSeminormal,
      hΦ.map_reflection (isSeminormal_pathCrystal hA' hν) hC.isSeminormal]
  rw [Equiv.Perm.coe_pow, ← (hsemi.iterate_right _) x, ← Equiv.Perm.coe_pow, hQ]
  rfl

/-- **Kashiwara's action of the Weyl group on a normal crystal** ([Kas] Thm. 11.1,
[Kas94] §7): the reflections `Sᵢ` extend to a homomorphism `W →* Perm B` with `sᵢ ↦ Sᵢ`. -/
noncomputable def weylAction (hC : C.IsNormal) : P.weylGroup hA →* Equiv.Perm B :=
  hC.isSeminormal.weylAction (P.coxeterSystem hA) hC.reflectionPerm_mul_pow

@[simp] theorem weylAction_simple (hC : C.IsNormal) (i : ι) :
    hC.weylAction ((P.coxeterSystem hA).simple i) = hC.isSeminormal.reflectionPerm i :=
  IsSeminormal.weylAction_simple _ _ _ i

theorem weylAction_simple_apply (hC : C.IsNormal) (i : ι) (b : B) :
    hC.weylAction ((P.coxeterSystem hA).simple i) b = C.reflection i b := by
  rw [weylAction_simple, IsSeminormal.reflectionPerm_apply]

/-- The action of the Weyl group is the unique one with `sᵢ ↦ Sᵢ`. -/
theorem eq_weylAction (hC : C.IsNormal) (φ : P.weylGroup hA →* Equiv.Perm B)
    (h : ∀ i, φ ((P.coxeterSystem hA).simple i) = hC.isSeminormal.reflectionPerm i) :
    φ = hC.weylAction := by
  ext w b
  refine (P.coxeterSystem hA).simple_induction_left
    (p := fun w => ∀ b, φ w b = hC.weylAction w b) w (fun b => by simp) (fun w i ih b => ?_) b
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, h, weylAction_simple]

/-- The action is compatible with weights: `wt (w • b) = w (wt b)` ([Kas] (11.3)). -/
theorem coe_wt_weylAction (hC : C.IsNormal) (w : P.weylGroup hA) (b : B) :
    ((C.wt (hC.weylAction w b) : P.integralWeights) : Dual ℝ H) =
      (w : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) (C.wt b : Dual ℝ H) := by
  refine (P.coxeterSystem hA).simple_induction_left
    (p := fun w => ∀ b, ((C.wt (hC.weylAction w b) : P.integralWeights) : Dual ℝ H) =
      (w : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) (C.wt b : Dual ℝ H)) w ?_ ?_ b
  · intro b
    simp
  · intro w i ih b
    rw [map_mul, Equiv.Perm.mul_apply, weylAction_simple, IsSeminormal.reflectionPerm_apply,
      hC.isSeminormal.wt_reflection, coe_reflection_cartanDatum, ih, Subgroup.coe_mul,
      coxeterSystem_simple, LinearEquiv.mul_apply]

/-! ### Disjoint unions and tensor products -/

variable {C₁ : Crystal (P.cartanDatum hA) B₁} {C₂ : Crystal (P.cartanDatum hA) B₂}

/-- The disjoint union of two normal crystals is normal. -/
theorem sum (h₁ : C₁.IsNormal) (h₂ : C₂.IsNormal) : (C₁.sum C₂).IsNormal where
  isSeminormal := h₁.isSeminormal.sum h₂.isSeminormal
  exists_leviHom J hJ b := by
    rcases b with b | b
    · obtain ⟨ν, hν, Φ, hinj, hΦ, x, rfl⟩ := h₁.exists_leviHom J hJ b
      exact ⟨ν, hν, Sum.inl ∘ Φ, Sum.inl_injective.comp hinj, hΦ.inl C₂, x, rfl⟩
    · obtain ⟨ν, hν, Φ, hinj, hΦ, x, rfl⟩ := h₂.exists_leviHom J hJ b
      exact ⟨ν, hν, Sum.inr ∘ Φ, Sum.inr_injective.comp hinj, hΦ.inr C₁, x, rfl⟩

/-- A disjoint union of normal crystals is normal. -/
theorem sigma {α : Type*} {Bα : α → Type*} {Cα : ∀ a, Crystal (P.cartanDatum hA) (Bα a)}
    (h : ∀ a, (Cα a).IsNormal) : (Crystal.sigma Cα).IsNormal where
  isSeminormal := IsSeminormal.sigma fun a => (h a).isSeminormal
  exists_leviHom J hJ b := by
    obtain ⟨a, b⟩ := b
    obtain ⟨ν, hν, Φ, hinj, hΦ, x, rfl⟩ := (h a).exists_leviHom J hJ b
    exact ⟨ν, hν, Sigma.mk a ∘ Φ, sigma_mk_injective.comp hinj, hΦ.sigmaMk, x, rfl⟩

/-- The tensor product of two normal crystals is normal. For `b₁ ⊗ b₂` with `bᵢ = Φᵢ(xᵢ)`, the
element `x₁ ⊗ x₂` of `B_J(ν₁) ⊗ B_J(ν₂)` lies in a summand `B_J(ν)` of Littelmann's
decomposition (`LSGeneralClass.nonempty_equiv_sigma_of_finiteDimensional`), and `Φ₁ ⊗ Φ₂`
restricted to that summand is the required Levi morphism. -/
theorem tensor (h₁ : C₁.IsNormal) (h₂ : C₂.IsNormal) : (C₁.tensor C₂).IsNormal where
  isSeminormal := h₁.isSeminormal.tensor h₂.isSeminormal
  exists_leviHom J hJ b := by
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨ν₁, hν₁, Φ₁, hinj₁, hΦ₁, x₁, rfl⟩ := h₁.exists_leviHom J hJ b₁
    obtain ⟨ν₂, hν₂, Φ₂, hinj₂, hΦ₂, x₂, rfl⟩ := h₂.exists_leviHom J hJ b₂
    have hA' := LSGeneralClass.isGeneralizedCartan_submatrix (e := ((↑) : J → ι)) hA
      Subtype.val_injective
    obtain ⟨E⟩ := LSGeneralClass.nonempty_equiv_sigma_of_finiteDimensional (hA := hA') hν₁ hν₂
    have hT₀ : IsLeviHom ((leviPathCrystal hA J hν₁).tensor (leviPathCrystal hA J hν₂))
        (C₁.tensor C₂) (↑) (Prod.map Φ₁ Φ₂) :=
      hΦ₁.tensor hΦ₂ (isSeminormal_pathCrystal _ hν₁) h₁.isSeminormal
        (isSeminormal_pathCrystal _ hν₂) h₂.isSeminormal
    have hT₁ := hT₀.comp_strictHom E.symm.toStrictHom
    obtain ⟨⟨η, z⟩, hq⟩ : ∃ q, E (x₁, x₂) = q := ⟨_, rfl⟩
    have hT := hT₁.comp_sigmaMk η
    refine ⟨_, isDominantIntegral_add_wt hA' hν₁ hν₂ η.1 η.2, _, ?_, hT, z, ?_⟩
    · exact ((hinj₁.prodMap hinj₂).comp (EquivLike.injective E.symm)).comp sigma_mk_injective
    · have h : E.toEquiv.symm ⟨η, z⟩ = (x₁, x₂) := (Equiv.symm_apply_eq _).mpr hq.symm
      change Prod.map Φ₁ Φ₂ (E.toEquiv.symm ⟨η, z⟩) = _
      rw [h]
      rfl

end IsNormal

end Crystal

/-! ### Path crystals are normal -/

namespace Matrix.Realization

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} (hA : A.IsGeneralizedCartan)

/-- **Littelmann's path crystals `B(Λ)` are normal**: by Levi restriction, every `J`-component of
`B(Λ)` is a copy of a path crystal `B_J(ν)` (`LSGeneralClass.LeviMap.exists_leviHom_pathCrystal`),
for every `J ⊆ ι`, of finite type or not. -/
theorem isNormal_pathCrystal {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ) :
    (P.pathCrystal hA hΛ).IsNormal where
  isSeminormal := isSeminormal_pathCrystal hA hΛ
  exists_leviHom J _ b := by
    obtain ⟨L⟩ := LSGeneralClass.nonempty_leviMap (P := P) Subtype.val_injective
      (Realization.std (A.submatrix ((↑) : J → ι) (↑)) ℝ)
    exact L.exists_leviHom_pathCrystal hΛ b

/-- On `B(Λ)`, Kashiwara's action of the Weyl group on normal crystals is
`Matrix.Realization.pathWeylAction`. -/
theorem weylAction_isNormal_pathCrystal {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ) :
    (isNormal_pathCrystal hA hΛ).weylAction = P.pathWeylAction hA hΛ :=
  ((isNormal_pathCrystal hA hΛ).eq_weylAction _ (pathWeylAction_simple hA hΛ)).symm

end Matrix.Realization
