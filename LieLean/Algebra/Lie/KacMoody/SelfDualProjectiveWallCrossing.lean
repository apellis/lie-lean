/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOProjDimensionEq
import LieLean.Algebra.Lie.KacMoody.SelfDualProjective
import LieLean.Algebra.Lie.KacMoody.SelfDualProjectiveCriterion
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralSimpleRoots
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralWall

/-!
# Self-dual projective covers by iterated wall-crossing

Placeholder docstring.
-/

noncomputable section

open CategoryTheory Limits Module LieModule

universe u

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

open VermaModule

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-- A monomorphism of `𝒪` is injective on the underlying modules. -/
theorem injective_of_mono {X Y : CategoryO.{u} P} (f : X ⟶ Y) [Mono f] :
    Function.Injective f.hom.hom := by
  have : PreservesFiniteLimits (IsObj.{u} P).ι :=
    ((Functor.preservesFiniteLimits_tfae (IsObj.{u} P).ι).out 3 4).mp
      (IsObj.{u} P).preservesKernels_ι
  exact (ModuleCat.mono_iff_injective ((IsObj.{u} P).ι.map f)).mp inferInstance

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- A morphism of `𝒪` that is injective on the underlying modules is a monomorphism. -/
theorem mono_of_injective {X Y : CategoryO.{u} P} (f : X ⟶ Y) (hf : Function.Injective f.hom.hom) :
    Mono f :=
  have : Mono ((IsObj.{u} P).ι.map f) := (ModuleCat.mono_iff_injective _).mpr hf
  (IsObj.{u} P).ι.mono_of_mono_map this

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- A morphism of `𝒪` given by an injective `𝔤`-module map is a monomorphism. -/
theorem mono_homMk_of_injective {X Y : CategoryO.{u} P} (φ : X.obj →ₗ⁅K,𝔤⁆ Y.obj)
    (hφ : Function.Injective φ) : Mono ((IsObj.{u} P).homMk (ofLieModuleHom φ)) :=
  mono_of_injective _ hφ

variable (P) in
/-- An object `X` of `𝒪` is self-dual: `X ≅ X^∨`. -/
def IsSelfDual (X : CategoryO.{u} P) : Prop :=
  Nonempty (X.obj ≃ₗ⁅K,𝔤⁆ restrictedDual P X.obj)

variable (P) in
/-- An endofunctor of `𝒪` preserving monomorphisms, projective objects and self-dual objects.
Translation functors by simple finite-dimensional modules are of this kind
(`isPreserving_translationFunctor`). -/
structure IsPreserving (F : CategoryO.{u} P ⥤ CategoryO.{u} P) : Prop where
  mono : F.PreservesMonomorphisms
  projective : ∀ X : CategoryO.{u} P, IsProjectiveO.{u} P X.obj →
    IsProjectiveO.{u} P (F.obj X).obj
  selfDual : ∀ X : CategoryO.{u} P, IsSelfDual P X → IsSelfDual P (F.obj X)
  fg : ∀ X : CategoryO.{u} P, (∃ S : Finset X.obj, LieSubmodule.lieSpan K 𝔤 (S : Set X.obj) = ⊤) →
    ∃ S : Finset (F.obj X).obj, LieSubmodule.lieSpan K 𝔤 (S : Set (F.obj X).obj) = ⊤

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem isPreserving_id : IsPreserving P (𝟭 (CategoryO.{u} P)) :=
  ⟨inferInstance, fun _ h ↦ h, fun _ h ↦ h, fun _ h ↦ h⟩

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem IsPreserving.comp {F G : CategoryO.{u} P ⥤ CategoryO.{u} P} (hF : IsPreserving P F)
    (hG : IsPreserving P G) : IsPreserving P (F ⋙ G) :=
  have := hF.mono
  have := hG.mono
  ⟨inferInstance, fun X h ↦ hG.projective _ (hF.projective X h),
    fun X h ↦ hG.selfDual _ (hF.selfDual X h), fun X h ↦ hG.fg _ (hF.fg X h)⟩

/-- **Translation functors by simple finite-dimensional modules preserve projectivity and
self-duality** (Humphreys, GSM 94, §3.8 and §7.1). -/
theorem isPreserving_translationFunctor {ν : Dual K H} (hν : P.IsDominantIntegral ν)
    [FiniteDimensional K (IrreducibleModule P ν)]
    (χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K 𝔤) →ₐ[K] K) :
    IsPreserving P (translationFunctor (IrreducibleModule P ν) χ₁ χ₂) where
  mono := inferInstance
  projective X hX := by
    have h₁ := isProjectiveO_centralBlock P (hV := X.property.1) hX χ₁
    have h₂ := h₁.tensorProduct P (L := IrreducibleModule P ν)
      (isCategoryO_of_finiteDimensional' (P := P) (Module.Dual K (IrreducibleModule P ν)))
    have h₃ := isProjectiveO_centralBlock P
      (hV := (X.property.1.centralBlock P χ₁).tensorProduct (IrreducibleModule.isCategoryO P ν))
      h₂ χ₂
    exact h₃.of_equiv (ofLieEquiv (P := P) _)
  selfDual X := by
    rintro ⟨e⟩
    exact ⟨(ofLieEquiv (P := P) _).symm.trans <|
      (centralTranslationEquiv P (IrreducibleModule P ν) χ₁ χ₂ e).trans <|
      (restrictedDualCentralTranslationEquiv P Fact.out hν X.property.1 χ₁ χ₂).symm.trans
      (restrictedDualEquiv P (ofLieEquiv (P := P) _).symm)⟩
  fg X := by
    classical
    rintro ⟨S, hS⟩
    obtain ⟨T, hT⟩ := exists_finset_lieSpan_centralTranslation_eq_top_of_fg P χ₁ χ₂
      X.property.1 (IrreducibleModule.isCategoryO P ν) hS
    refine ⟨T.image (ofLieEquiv (P := P) _), ?_⟩
    rw [Finset.coe_image]
    exact lieSpan_image_eq_top_of_surjective (ofLieEquiv (P := P) _).toLieModuleHom
      (ofLieEquiv (P := P) _).surjective hT

variable (hA : A.IsFiniteCartan)

include hA in
/-- **The wall-crossing step** (Humphreys, GSM 94, §7.14 (a) and §7.16). Let `λ` be
antidominant and regular and let `μ` lie on the wall of the positive root `β = v αᵢ` and on no
other wall, with `μ - λ` integral. There are an endofunctor `F = T_μ^λ T_λ^μ` of `𝒪` preserving
monomorphisms, projectives and self-dual objects and a right adjoint `G` of `F` such that
`M(w s_β·λ)` embeds into `G M(w·λ)` whenever `w β > 0`. (`G` is the wall-crossing functor built
from the duals of the coefficient modules of `F`.) -/
theorem exists_adjunction_mono_wallCrossing {lam μ : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hint : ∀ t, ∃ z : ℤ, (μ - lam) (P.coroot t) = z)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0) :
    ∃ (F G : CategoryO.{u} P ⥤ CategoryO.{u} P) (_ : F ⊣ G), IsPreserving P F ∧
      ∀ w : P.weylGroup hA.isGeneralizedCartan, P.IsPosRoot hA.isGeneralizedCartan (w * v) i →
        ∃ φ : verma P (P.weylDot hA.isGeneralizedCartan
            (w * P.reflectionOf hA.isGeneralizedCartan v i) lam) ⟶
          G.obj (verma P (P.weylDot hA.isGeneralizedCartan w lam)), Mono φ := by
  have hA' := hA.isGeneralizedCartan
  have hint' : ∀ t, ∃ z : ℤ, (lam - μ) (P.coroot t) = z := fun t ↦ by
    obtain ⟨z, hz⟩ := hint t
    exact ⟨-z, by rw [show lam - μ = -(μ - lam) by abel, LinearMap.neg_apply, hz]; push_cast; rfl⟩
  obtain ⟨z, hν⟩ := exists_dominantIntegral_weylGroup (P := P) hA' hint'
  obtain ⟨z', hν'⟩ := exists_dominantIntegral_weylGroup (P := P) hA' hint
  set ν := z.val (lam - μ)
  set ν' := z'.val (μ - lam)
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν'
  obtain ⟨z₁, hz₁, hν₁, ⟨e₁⟩⟩ := IrreducibleModule.exists_equiv_dual (P := P) hA hν
  obtain ⟨z₂, hz₂, hν₂, ⟨e₂⟩⟩ := IrreducibleModule.exists_equiv_dual (P := P) hA hν'
  set chiL := centralCharacter P lam
  set chiM := centralCharacter P μ
  let F := translationFunctor (IrreducibleModule P ν') chiL chiM ⋙
    translationFunctor (IrreducibleModule P ν) chiM chiL
  let G := translationFunctor (Module.Dual K (IrreducibleModule P ν)) chiL chiM ⋙
    translationFunctor (Module.Dual K (IrreducibleModule P ν')) chiM chiL
  have adj : F ⊣ G := (translationAdj (IrreducibleModule P ν') chiL chiM).comp
    (translationAdj (IrreducibleModule P ν) chiM chiL)
  refine ⟨F, G, adj, (isPreserving_translationFunctor hν' chiL chiM).comp
    (isPreserving_translationFunctor hν chiM chiL), fun w hw ↦ ?_⟩
  -- the inner translation, with coefficient `L(ν)^* ≅ L(ν₁)`
  let Xo := (translationFunctor (Module.Dual K (IrreducibleModule P ν)) chiL chiM).obj
    (verma P (P.weylDot hA' w lam))
  let eX : Xo.obj ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P (z₁ (-ν))) chiL chiM
      (VermaModule P (P.weylDot hA' w lam)) :=
    (ofLieEquiv (P := P) _).symm.trans <|
      (centralTranslationEquiv P (Module.Dual K (IrreducibleModule P ν)) chiL chiM
        (ofLieEquiv (P := P) (VermaModule P (P.weylDot hA' w lam))).symm).trans
      (centralTranslationCoeffEquiv P (VermaModule P (P.weylDot hA' w lam)) chiL chiM e₁)
  have hzν₁ : (z₁ * z.val) (μ - lam) = z₁ (-ν) := by
    rw [LinearEquiv.mul_apply, show μ - lam = -(lam - μ) by abel, map_neg]
  have hzν₂ : (z₂ * z'.val) (lam - μ) = z₂ (-ν') := by
    rw [LinearEquiv.mul_apply, show lam - μ = -(μ - lam) by abel, map_neg]
  obtain ⟨f, -, hf, -, -⟩ := wallCrossing_verma_shortExact P hA hlam hμ hfacet hν₂
    (mul_mem hz₂ z'.2) hzν₂ hν₁ (mul_mem hz₁ z.2) hzν₁ hv hμα hwall hlamα hw eX
  let Yo := (translationFunctor (Module.Dual K (IrreducibleModule P ν')) chiM chiL).obj Xo
  obtain ⟨φ, hφ⟩ : ∃ φ : (verma P (P.weylDot hA' (w * P.reflectionOf hA' v i) lam)).obj →ₗ⁅K,𝔤⁆
      Yo.obj, Function.Injective φ :=
    ⟨(ofLieEquiv (P := P) _).toLieModuleHom.comp <|
      (centralTranslationCoeffEquiv P Xo.obj chiM chiL e₂.symm).toLieModuleHom.comp <|
        f.comp (ofLieEquiv (P := P) (VermaModule P _)).symm.toLieModuleHom,
      fun a b hab ↦ (ofLieEquiv (P := P) (VermaModule P _)).symm.injective <| hf <|
        (centralTranslationCoeffEquiv P Xo.obj chiM chiL e₂.symm).injective <|
          (ofLieEquiv (P := P) _).injective hab⟩
  let φo : verma P (P.weylDot hA' (w * P.reflectionOf hA' v i) lam) ⟶ Yo :=
    (IsObj.{u} P).homMk (ofLieModuleHom φ)
  have hφo : Mono φo :=
    mono_homMk_of_injective (X := verma P (P.weylDot hA' (w * P.reflectionOf hA' v i) lam))
      (Y := Yo) φ hφ
  have hG : G.obj (verma P (P.weylDot hA' w lam)) = Yo := rfl
  rw [hG]
  exact ⟨φo, hφo⟩

include hA in
/-- **Iterated wall-crossing.** Let `λ` be regular antidominant, `⟨λ + ρ, β^∨⟩ ∈ ℤ_{<0}` for
the positive roots `β` integral for `λ`, and suppose that each simple integral root `γ` admits
a weight `μ = λ + c`, `c` integral, lying on the wall of `γ` and on no other wall. Then for every
`y ∈ W_[λ]` there are an endofunctor `F` of `𝒪` preserving monomorphisms, projectives and
self-dual objects and a right adjoint `G` of `F` with `M(y·λ) ↪ G M(λ)`. Induction on `ℓ(y)`,
writing `y = y' s_γ` with `γ` simple integral, `y γ < 0`
(`Matrix.Realization.exists_isPosRoot_reflectionOf_mul`), and composing with the wall-crossing
step `exists_adjunction_mono_wallCrossing` (Humphreys, GSM 94, §7.16). -/
theorem exists_adjunction_mono_weylDot {lam : Dual K H}
    (hreg : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n → n < 0)
    (hwalls : ∀ (u : P.weylGroup hA.isGeneralizedCartan) (j : ι),
      P.IsPosRoot hA.isGeneralizedCartan u j →
      P.IsIntegralRoot hA.isGeneralizedCartan (lam + P.rho) u j →
      (∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
        P.IsIntegralRoot hA.isGeneralizedCartan (lam + P.rho) v i →
        (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ≠ (u : Dual K H ≃ₗ[K] Dual K H) (P.root j) →
          P.IsPosRoot hA.isGeneralizedCartan (P.reflectionOf hA.isGeneralizedCartan u j * v) i) →
      ∃ c : Dual K H, (∀ t, ∃ z : ℤ, c (P.coroot t) = z) ∧
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho + c) u j = 0 ∧
        ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ m : ℤ,
          P.corootPairing hA.isGeneralizedCartan (lam + P.rho + c) v i = m →
          m < 0 ∨ (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) =
            (u : Dual K H ≃ₗ[K] Dual K H) (P.root j))
    {y : P.weylGroup hA.isGeneralizedCartan}
    (hy : y ∈ P.integralWeylGroup hA.isGeneralizedCartan (lam + P.rho)) :
    ∃ (F G : CategoryO.{u} P ⥤ CategoryO.{u} P) (_ : F ⊣ G), IsPreserving P F ∧
      ∃ φ : verma P (P.weylDot hA.isGeneralizedCartan y lam) ⟶ G.obj (verma P lam), Mono φ := by
  have hA' := hA.isGeneralizedCartan
  induction hlen : (P.coxeterSystem hA').length y using Nat.strong_induction_on
    generalizing y with
  | _ n ih =>
  by_cases hy1 : y = 1
  · subst hy1
    refine ⟨𝟭 _, 𝟭 _, Adjunction.id, isPreserving_id, ?_⟩
    rw [weylDot_one]
    exact ⟨𝟙 _, inferInstance⟩
  obtain ⟨u, j, hu, hux, hyu, hsimple⟩ := exists_isPosRoot_reflectionOf_mul hA hreg hy hy1
  obtain ⟨c, hc, hcu, hcw⟩ := hwalls u j hu hux hsimple
  set s := P.reflectionOf hA' u j with hsdef
  have hs : s ∈ P.integralWeylGroup hA' (lam + P.rho) :=
    (P.reflectionOf_mem_integralWeylGroup_iff _ u j).mpr hux
  obtain ⟨F', G', adj', hF', φ', hφ'⟩ :=
    ih _ (hlen ▸ length_mul_reflectionOf_lt hu hyu) (mul_mem hy hs) rfl
  set μ := lam + c with hμdef
  have hμρ : μ + P.rho = lam + P.rho + c := add_right_comm _ _ _
  have hlam : P.IsAntidominant hA' lam := fun v i hv n hn ↦ (hreg v i hv n hn).le
  have hμ : P.IsAntidominant hA' μ := fun v i hv n hn ↦ by
    rw [hμρ] at hn
    rcases hcw v i hv n hn with h | h
    · exact h.le
    rw [corootPairing_eq_of_apply_root_eq hA h, hcu] at hn
    have : (n : K) = 0 := hn.symm
    exact (Int.cast_eq_zero.mp this).le
  have hfacet : ∀ v i, P.IsPosRoot hA' v i → P.corootPairing hA' (lam + P.rho) v i = 0 →
      P.corootPairing hA' (μ + P.rho) v i = 0 := fun v i hv h0 ↦ by
    have := hreg v i hv 0 (by rw [h0, Int.cast_zero])
    omega
  have hint : ∀ t, ∃ z : ℤ, (μ - lam) (P.coroot t) = z := by
    rw [hμdef, add_sub_cancel_left]
    exact hc
  have hμα : P.corootPairing hA' (μ + P.rho) u j = 0 := by rw [hμρ]; exact hcu
  have hwall : ∀ v' i', P.corootPairing hA' (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (u : Dual K H ≃ₗ[K] Dual K H) (P.root j) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') =
          -(u : Dual K H ≃ₗ[K] Dual K H) (P.root j) := fun v' i' h0 ↦ by
    rw [hμρ] at h0
    rcases P.isPosRoot_or v' i' with hp | hn
    · rcases hcw v' i' hp 0 (by rw [h0, Int.cast_zero]) with h | h
      · omega
      · exact Or.inl h
    · have h0' : P.corootPairing hA' (lam + P.rho + c)
          (v' * (P.coxeterSystem hA').simple i') i' = ((0 : ℤ) : K) := by
        rw [corootPairing_mul_simple, h0, Int.cast_zero, neg_zero]
      rcases hcw _ _ hn 0 h0' with h | h
      · omega
      · rw [mul_simple_apply_root] at h
        exact Or.inr (by rw [← h, neg_neg])
  have hlamα : P.corootPairing hA' (lam + P.rho) u j ≠ 0 := fun h0 ↦ by
    have := hreg u j hu 0 (by rw [h0, Int.cast_zero])
    omega
  obtain ⟨Fs, Gs, adjs, hFs, hmono⟩ :=
    exists_adjunction_mono_wallCrossing hA hlam hμ hfacet hint hu hμα hwall hlamα
  have hsimp : (⟨P.reflection hA' j, P.reflection_mem_weylGroup hA' j⟩ :
      P.weylGroup hA') = (P.coxeterSystem hA').simple j :=
    Subtype.ext (by rw [coxeterSystem_simple])
  have hw : P.IsPosRoot hA' (y * s * u) j := by
    have : y * s * u = y * u * (P.coxeterSystem hA').simple j := by
      rw [hsdef, reflectionOf, hsimp]
      group
    rw [this]
    exact (P.isPosRoot_or (y * u) j).resolve_left hyu
  have hmono' := hmono (y * s) hw
  rw [mul_assoc, reflectionOf_mul_self, mul_one] at hmono'
  obtain ⟨φs, hφs⟩ := hmono'
  have := adjs.isRightAdjoint
  refine ⟨Fs ⋙ F', G' ⋙ Gs, adjs.comp adj', hFs.comp hF', φs ≫ Gs.map φ', ?_⟩
  exact mono_comp _ _

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
