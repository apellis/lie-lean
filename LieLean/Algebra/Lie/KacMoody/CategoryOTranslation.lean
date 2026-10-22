/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryODelorme
import LieLean.Algebra.Lie.KacMoody.CategoryOExt
import LieLean.Algebra.Lie.KacMoody.TranslationAdjunction
import LieLean.Algebra.Lie.KacMoody.TranslationDuality
import LieLean.Algebra.Lie.KacMoody.TranslationProjectiveCover
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Translation functors on `𝒪` and `Extⁿ`

[HumO] Proposition 7.2 (b): translation functors `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L)` and
`T' = pr_{χ₁}(pr_{χ₂}(−) ⊗ L^*)`, for a finite-dimensional module `L`, are exact functors on the
category `𝒪` and adjoint to each other, so
`Extⁿ_𝒪(T M, N) ≅ Extⁿ_𝒪(M, T' N)` for all `n` (`CategoryO.extTranslationEquiv`).

Part (a) of the proposition (the adjunction on `Hom`) was proved for modules lying in the blocks
`χ₁`, `χ₂` (`translationAdjunction`). Here it is proved for all modules
(`homTranslationEquiv`: `Hom(T M, N) ≅ Hom(M, T' N)`), naturally in both variables, which is what
an adjunction of functors on `𝒪` needs.

## Main definitions and results

* `homCentralBlockEquiv`: `Hom(pr_χ M, N) ≅ Hom(M, pr_χ N)` for `M` locally finite under the centre.
* `tensorHomAdjunction_comp_left`, `tensorHomAdjunction_comp_right`: naturality of the tensor–Hom
  adjunction `Hom(M ⊗ L, N) ≅ Hom(M, N ⊗ L^*)`.
* `homTranslationEquiv`: [HumO] Prop 7.2 (a) for all modules, with naturality.
* `CategoryO.translationFunctor`: the translation functor `pr_{χ₂}(pr_{χ₁}(−) ⊗ L)` on `𝒪`, exact
  (`CategoryO.translationFunctor_shortExact`) and `K`-linear.
* `CategoryO.translationAdj`: `T ⊣ T'`.
* `CategoryO.extTranslationEquiv`: **[HumO] Proposition 7.2 (b)**.

Finite type, algebraically closed field of characteristic zero (Humphreys works over `ℂ`); every
finite-dimensional module lies in `𝒪` in finite type, so `L` is any finite-dimensional module.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §7.1–7.2.
-/

open CategoryTheory Limits LieModule Module TensorProduct

noncomputable section

universe u

/-! ### Generalities -/

section Generic

variable {R L M N Q : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

theorem TensorProduct.LieModule.liftLie_symm_apply_apply (g : M ⊗[R] N →ₗ⁅R,L⁆ Q) (m : M)
    (n : N) : (TensorProduct.LieModule.liftLie R L M N Q).symm g m n = g (m ⊗ₜ n) := by
  obtain ⟨F, rfl⟩ := (TensorProduct.LieModule.liftLie R L M N Q).surjective g
  rw [LinearEquiv.symm_apply_apply, TensorProduct.LieModule.liftLie_apply]

end Generic

section GenericField

variable {K L V W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- If finitely many vectors generate `V` and `W` is finite-dimensional, then `V ⊗ W` is generated
by finitely many vectors. -/
theorem Matrix.Realization.KacMoodyAlgebra.exists_finset_lieSpan_tensor_eq_top
    [FiniteDimensional K W] {S : Finset V} (hS : LieSubmodule.lieSpan K L (S : Set V) = ⊤) :
    ∃ T : Finset (V ⊗[K] W), LieSubmodule.lieSpan K L (T : Set (V ⊗[K] W)) = ⊤ := by
  classical
  let b := Module.finBasis K W
  refine ⟨(S ×ˢ Finset.univ).image fun p ↦ p.1 ⊗ₜ[K] b p.2, ?_⟩
  set N := LieSubmodule.lieSpan K L
    (((S ×ˢ Finset.univ).image fun p ↦ p.1 ⊗ₜ[K] b p.2 : Finset (V ⊗[K] W)) : Set (V ⊗[K] W))
  have hvN : ∀ v ∈ S, ∀ l : W, v ⊗ₜ[K] l ∈ N := by
    intro v hv l
    rw [← b.sum_repr l, tmul_sum]
    refine N.sum_mem fun i _ ↦ ?_
    rw [tmul_smul]
    refine N.smul_mem _ (LieSubmodule.subset_lieSpan ?_)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_univ, and_true, Prod.exists]
    exact ⟨v, i, hv, rfl⟩
  let S' : LieSubmodule K L V :=
    { carrier := {x | ∀ l : W, x ⊗ₜ[K] l ∈ N}
      add_mem' := fun {x y} hx hy l ↦ by
        rw [add_tmul]
        exact N.add_mem (hx l) (hy l)
      zero_mem' := fun l ↦ by
        rw [zero_tmul]
        exact N.zero_mem
      smul_mem' := fun c x hx l ↦ by
        rw [← smul_tmul']
        exact N.smul_mem c (hx l)
      lie_mem := fun {y x} hx l ↦ by
        have h := N.sub_mem (N.lie_mem (x := y) (hx l)) (hx ⁅y, l⁆)
        rwa [TensorProduct.LieModule.lie_tmul_right, add_sub_cancel_right] at h }
  have hS' : S' = ⊤ := by
    rw [eq_top_iff, ← hS, LieSubmodule.lieSpan_le]
    exact fun v hv ↦ hvN v hv
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | zero => exact N.zero_mem
  | tmul x l =>
    have hx : x ∈ S' := hS' ▸ LieSubmodule.mem_top x
    exact hx l
  | add x y hx hy => exact N.add_mem hx hy

end GenericField

namespace Matrix.Realization.KacMoodyAlgebra

/-! ### Translation of `𝔤`-modules -/

section Lie

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {M M' N N' L : Type*}
  [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]
  [AddCommGroup M'] [Module K M'] [LieRingModule P.KacMoodyAlgebra M']
  [LieModule K P.KacMoodyAlgebra M']
  [AddCommGroup N] [Module K N] [LieRingModule P.KacMoodyAlgebra N]
  [LieModule K P.KacMoodyAlgebra N]
  [AddCommGroup N'] [Module K N'] [LieRingModule P.KacMoodyAlgebra N']
  [LieModule K P.KacMoodyAlgebra N']
  [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

theorem centralTranslationMap_add (χ₁ χ₂ : 𝓩 →ₐ[K] K) (f g : M →ₗ⁅K,𝔤⁆ N) :
    centralTranslationMap P L χ₁ χ₂ (f + g) =
      centralTranslationMap P L χ₁ χ₂ f + centralTranslationMap P L χ₁ χ₂ g := by
  ext ⟨t, ht⟩
  change TensorProduct.map _ _ t = TensorProduct.map _ _ t + TensorProduct.map _ _ t
  clear ht
  induction t using TensorProduct.inductionOn with
  | zero => simp
  | tmul v z =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, ← add_tmul]
    rfl
  | add s t hs ht =>
    simp only [map_add, hs, ht]
    abel

theorem centralTranslationMap_smul (χ₁ χ₂ : 𝓩 →ₐ[K] K) (c : K) (f : M →ₗ⁅K,𝔤⁆ N) :
    centralTranslationMap P L χ₁ χ₂ (c • f) = c • centralTranslationMap P L χ₁ χ₂ f := by
  ext ⟨t, ht⟩
  change TensorProduct.map _ _ t = c • TensorProduct.map _ _ t
  clear ht
  induction t using TensorProduct.inductionOn with
  | zero => simp
  | tmul v z =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, smul_tmul']
    rfl
  | add s t hs ht => simp only [map_add, hs, ht, smul_add]

/-! #### The tensor–Hom adjunction -/

section Tensor

variable [FiniteDimensional K L]

theorem tensorDualEquivHom_tensorHomAdjunction_apply (g : M ⊗[K] L →ₗ⁅K,𝔤⁆ N) (m : M) :
    tensorDualEquivHom P N L (tensorHomAdjunction P g m) =
      (TensorProduct.LieModule.liftLie K 𝔤 M L N).symm g m :=
  (tensorDualEquivHom P N L).apply_symm_apply _

/-- Naturality of the tensor–Hom adjunction in `M`. -/
theorem tensorHomAdjunction_comp_left (f : M' →ₗ⁅K,𝔤⁆ M) (g : M ⊗[K] L →ₗ⁅K,𝔤⁆ N) :
    tensorHomAdjunction P
        (g.comp (TensorProduct.LieModule.map f (LieModuleHom.id : L →ₗ⁅K,𝔤⁆ L))) =
      (tensorHomAdjunction P g).comp f := by
  refine LieModuleHom.ext fun m ↦ (tensorDualEquivHom P N L).injective ?_
  rw [tensorDualEquivHom_tensorHomAdjunction_apply, LieModuleHom.comp_apply,
    tensorDualEquivHom_tensorHomAdjunction_apply]
  ext l
  simp only [TensorProduct.LieModule.liftLie_symm_apply_apply, LieModuleHom.comp_apply,
    TensorProduct.LieModule.map_tmul, LieModuleHom.id_apply]

/-- Naturality of the tensor–Hom adjunction in `N`. -/
theorem tensorHomAdjunction_comp_right (k : N →ₗ⁅K,𝔤⁆ N') (g : M ⊗[K] L →ₗ⁅K,𝔤⁆ N) :
    tensorHomAdjunction P (k.comp g) =
      (TensorProduct.LieModule.map k (LieModuleHom.id : Module.Dual K L →ₗ⁅K,𝔤⁆ _)).comp
        (tensorHomAdjunction P g) := by
  refine LieModuleHom.ext fun m ↦ (tensorDualEquivHom P N' L).injective ?_
  rw [tensorDualEquivHom_tensorHomAdjunction_apply, LieModuleHom.comp_apply,
    tensorDualEquivHom_map, tensorDualEquivHom_tensorHomAdjunction_apply]
  ext l
  simp only [TensorProduct.LieModule.liftLie_symm_apply_apply, LieModuleHom.comp_apply,
    LinearMap.comp_apply, LieModuleHom.coe_toLinearMap]

end Tensor

/-! #### Central blocks on either side of `Hom` -/

section Block

theorem mem_centralBlock_centralBlock (χ : 𝓩 →ₐ[K] K) (y : centralBlock P N χ) :
    y ∈ centralBlock P (centralBlock P N χ) χ := by
  rw [centralBlock_centralBlock_eq_top P χ]
  exact LieSubmodule.mem_top _

variable [IsAlgClosed K]

/-- `Hom(pr_χ M, N) ≅ Hom(M, pr_χ N)` for `M` locally finite under the centre:
`g ↦ g ∘ pr_χ` and `h ↦ h|_{pr_χ M}`. -/
def homCentralBlockEquiv (hM : IsCentralLocallyFinite P M) (χ : 𝓩 →ₐ[K] K) :
    (centralBlock P M χ →ₗ⁅K,𝔤⁆ N) ≃ₗ[K] (M →ₗ⁅K,𝔤⁆ centralBlock P N χ) where
  toFun g := (g.comp ((centralBlockProjection P hM χ).codRestrict _
      (centralBlockProjection_mem P hM χ))).codRestrict (centralBlock P N χ) fun m ↦
    map_mem_centralBlock P g χ (mem_centralBlock_centralBlock P χ _)
  invFun h := (centralBlock P N χ).incl.comp (h.comp (centralBlock P M χ).incl)
  map_add' _ _ := LieModuleHom.ext fun _ ↦ rfl
  map_smul' _ _ := LieModuleHom.ext fun _ ↦ rfl
  left_inv g := LieModuleHom.ext fun v ↦
    congrArg g (Subtype.ext (centralBlockProjection_self P hM χ v.property))
  right_inv h := by
    refine LieModuleHom.ext fun m ↦ Subtype.ext ?_
    change (h (centralBlockProjection P hM χ m) : N) = h m
    have hm : m ∈ ⨆ θ, (centralBlock P M θ).toSubmodule := by
      rw [iSup_centralBlock_eq_top P hM]; trivial
    induction hm using Submodule.iSup_induction' with
    | mem θ v hv =>
      by_cases hθ : θ = χ
      · subst hθ
        rw [centralBlockProjection_self P hM θ hv]
      · rw [centralBlockProjection_other P hM hθ hv, map_zero]
        have h1 : h v ∈ centralBlock P (centralBlock P N χ) θ := map_mem_centralBlock P h θ hv
        have h3 : h v = 0 := (LieSubmodule.mem_bot _).mp ((disjoint_centralBlock P hθ).le_bot
          ((LieSubmodule.mem_inf _ _ _).mpr ⟨h1, mem_centralBlock_centralBlock P χ _⟩))
        rw [h3]
    | zero => simp
    | add v w _ _ hv hw => simp only [map_add, LieSubmodule.coe_add, hv, hw]

theorem homCentralBlockEquiv_comp_left (hM' : IsCentralLocallyFinite P M')
    (hM : IsCentralLocallyFinite P M) (χ : 𝓩 →ₐ[K] K) (f : M' →ₗ⁅K,𝔤⁆ M)
    (g : centralBlock P M χ →ₗ⁅K,𝔤⁆ N) :
    homCentralBlockEquiv P hM' χ (g.comp (centralBlockMap P f χ)) =
      (homCentralBlockEquiv P hM χ g).comp f :=
  LieModuleHom.ext fun m ↦ Subtype.ext (congrArg (fun y ↦ (g y : N))
    (Subtype.ext (LieModuleHom.congr_fun (centralBlockProjection_natural P hM' hM f χ) m)))

theorem homCentralBlockEquiv_comp_right (hM : IsCentralLocallyFinite P M) (χ : 𝓩 →ₐ[K] K)
    (k : N →ₗ⁅K,𝔤⁆ N') (g : centralBlock P M χ →ₗ⁅K,𝔤⁆ N) :
    homCentralBlockEquiv P hM χ (k.comp g) =
      (centralBlockMap P k χ).comp (homCentralBlockEquiv P hM χ g) :=
  LieModuleHom.ext fun _ ↦ rfl

end Block

/-! #### Adjointness of translation functors -/

section Adjunction

variable [CharZero K] [IsAlgClosed K]

/-- The translation of a finitely generated module in `𝒪` by a finite-dimensional module in `𝒪`
is finitely generated. -/
theorem exists_finset_lieSpan_centralTranslation_eq_top_of_fg (χ₁ χ₂ : 𝓩 →ₐ[K] K)
    [FiniteDimensional K L]
    (hM : IsCategoryO P M) (hL : IsCategoryO P L) {S : Finset M}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) :
    ∃ T : Finset (centralTranslation P L χ₁ χ₂ M),
      LieSubmodule.lieSpan K 𝔤 (T : Set (centralTranslation P L χ₁ χ₂ M)) = ⊤ := by
  classical
  have hS₁ : LieSubmodule.lieSpan K 𝔤
      ((S.image (blockRetr P hM χ₁) : Finset (centralBlock P M χ₁)) :
        Set (centralBlock P M χ₁)) = ⊤ := by
    rw [Finset.coe_image]
    exact lieSpan_image_eq_top_of_surjective _ (fun y ↦ ⟨y, blockRetr_incl P hM χ₁ y⟩) hS
  obtain ⟨T, hT⟩ := exists_finset_lieSpan_tensor_eq_top (L := 𝔤) (W := L) hS₁
  have hXO : IsCategoryO P (centralBlock P M χ₁ ⊗[K] L) := (hM.centralBlock P χ₁).tensorProduct hL
  refine ⟨T.image (blockRetr P hXO χ₂), ?_⟩
  rw [Finset.coe_image]
  exact lieSpan_image_eq_top_of_surjective _ (fun y ↦ ⟨y, blockRetr_incl P hXO χ₂ y⟩) hT

variable [FiniteDimensional K L]

/-- **Adjointness of translation functors** ([HumO] Prop 7.2 (a)), for all modules: for `M` in
`𝒪` and a finite-dimensional `L` in `𝒪`,
`Hom(pr_{χ₂}(pr_{χ₁} M ⊗ L), N) ≅ Hom(M, pr_{χ₁}(pr_{χ₂} N ⊗ L^*))`, `K`-linearly. -/
def homTranslationEquiv (χ₁ χ₂ : 𝓩 →ₐ[K] K) (hM : IsCategoryO P M) (hL : IsCategoryO P L) :
    (centralTranslation P L χ₁ χ₂ M →ₗ⁅K,𝔤⁆ N) ≃ₗ[K]
      (M →ₗ⁅K,𝔤⁆ centralTranslation P (Module.Dual K L) χ₂ χ₁ N) :=
  (homCentralBlockEquiv P (((hM.centralBlock P χ₁).tensorProduct hL).isCentralLocallyFinite P)
      χ₂).trans <|
    (tensorHomAdjunction P).trans (homCentralBlockEquiv P (hM.isCentralLocallyFinite P) χ₁)

/-- Naturality of `homTranslationEquiv` in `M`. -/
theorem homTranslationEquiv_comp_left (χ₁ χ₂ : 𝓩 →ₐ[K] K) (hM' : IsCategoryO P M')
    (hM : IsCategoryO P M) (hL : IsCategoryO P L) (f : M' →ₗ⁅K,𝔤⁆ M)
    (g : centralTranslation P L χ₁ χ₂ M →ₗ⁅K,𝔤⁆ N) :
    homTranslationEquiv P χ₁ χ₂ hM' hL (g.comp (centralTranslationMap P L χ₁ χ₂ f)) =
      (homTranslationEquiv P χ₁ χ₂ hM hL g).comp f := by
  simp only [homTranslationEquiv, LinearEquiv.trans_apply, centralTranslationMap]
  rw [homCentralBlockEquiv_comp_left P _
      (((hM.centralBlock P χ₁).tensorProduct hL).isCentralLocallyFinite P),
    tensorHomAdjunction_comp_left,
    homCentralBlockEquiv_comp_left P (hM'.isCentralLocallyFinite P) (hM.isCentralLocallyFinite P)]

/-- Naturality of `homTranslationEquiv` in `N`. -/
theorem homTranslationEquiv_comp_right (χ₁ χ₂ : 𝓩 →ₐ[K] K) (hM : IsCategoryO P M)
    (hL : IsCategoryO P L)
    (g : centralTranslation P L χ₁ χ₂ M →ₗ⁅K,𝔤⁆ N) (k : N →ₗ⁅K,𝔤⁆ N') :
    homTranslationEquiv P χ₁ χ₂ hM hL (k.comp g) =
      (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ k).comp
        (homTranslationEquiv P χ₁ χ₂ hM hL g) := by
  simp only [homTranslationEquiv, LinearEquiv.trans_apply, centralTranslationMap]
  rw [homCentralBlockEquiv_comp_right, tensorHomAdjunction_comp_right,
    homCentralBlockEquiv_comp_right]

end Adjunction

end Lie

/-! ### Translation functors on the category `𝒪` -/

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- Short exact sequences in `𝒪` are short exact on the underlying modules. -/
theorem lie_of_shortExact {S : ShortComplex (CategoryO.{u} P)} (hS : S.ShortExact) :
    Function.Injective S.f.hom.hom ∧ Function.Exact S.f.hom.hom S.g.hom.hom ∧
      Function.Surjective S.g.hom.hom := by
  have : PreservesFiniteLimits (IsObj.{u} P).ι :=
    ((Functor.preservesFiniteLimits_tfae (IsObj.{u} P).ι).out 3 4).mp
      (IsObj.{u} P).preservesKernels_ι
  have : PreservesFiniteColimits (IsObj.{u} P).ι :=
    ((Functor.preservesFiniteColimits_tfae (IsObj.{u} P).ι).out 3 4).mp
      (IsObj.{u} P).preservesCokernels_ι
  have h := hS.map (IsObj.{u} P).ι
  exact ⟨h.moduleCat_injective_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact,
    h.moduleCat_surjective_g⟩

variable (L : Type u) [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L] [FiniteDimensional K L]
  (χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) →ₐ[K] K)

omit [IsAlgClosed K] in
theorem isCategoryO_of_finiteDimensional' : IsCategoryO P L :=
  isCategoryO_of_finiteDimensional (P := P) (V := L) Fact.out

/-- The translation `pr_{χ₂}(pr_{χ₁} X ⊗ L)` of an object of `𝒪`. -/
def translationObj (X : CategoryO.{u} P) : CategoryO.{u} P :=
  mk (centralTranslation P L χ₁ χ₂ X.obj)
    (((X.property.1.centralBlock P χ₁).tensorProduct
      (isCategoryO_of_finiteDimensional' L)).centralBlock P χ₂)
    (exists_finset_lieSpan_centralTranslation_eq_top_of_fg P χ₁ χ₂ X.property.1
      (isCategoryO_of_finiteDimensional' L) X.property.2.choose_spec)

/-- The translation of a morphism of `𝒪`. -/
def translationMap {X Y : CategoryO.{u} P} (f : X ⟶ Y) :
    translationObj L χ₁ χ₂ X ⟶ translationObj L χ₁ χ₂ Y :=
  (IsObj.{u} P).homMk (ofLieModuleHom
    ((ofLieEquiv (P := P) (centralTranslation P L χ₁ χ₂ Y.obj)).toLieModuleHom.comp
      ((centralTranslationMap P L χ₁ χ₂ (toLieModuleHom f.hom)).comp
        (ofLieEquiv (P := P) (centralTranslation P L χ₁ χ₂ X.obj)).symm.toLieModuleHom)))

/-- The **translation functor** `pr_{χ₂}(pr_{χ₁}(−) ⊗ L)` on `𝒪` ([HumO] §7.1). -/
def translationFunctor : CategoryO.{u} P ⥤ CategoryO.{u} P where
  obj X := translationObj L χ₁ χ₂ X
  map f := translationMap L χ₁ χ₂ f
  map_id X := by
    ext x
    exact LieModuleHom.congr_fun (centralTranslationMap_id P L χ₁ χ₂) x
  map_comp f g := by
    ext x
    exact LieModuleHom.congr_fun (centralTranslationMap_comp P L χ₁ χ₂ (toLieModuleHom f.hom)
      (toLieModuleHom g.hom)) x

instance : (translationFunctor L χ₁ χ₂).Additive where
  map_add {X Y f g} := by
    ext x
    exact LieModuleHom.congr_fun (centralTranslationMap_add P χ₁ χ₂ (toLieModuleHom f.hom)
      (toLieModuleHom g.hom)) x

instance : (translationFunctor L χ₁ χ₂).Linear K where
  map_smul {X Y} f c := by
    ext x
    exact LieModuleHom.congr_fun (centralTranslationMap_smul P χ₁ χ₂ c (toLieModuleHom f.hom)) x

/-- **Translation functors are exact** ([HumO] §7.1). -/
theorem translationFunctor_shortExact {S : ShortComplex (CategoryO.{u} P)} (hS : S.ShortExact) :
    (S.map (translationFunctor L χ₁ χ₂)).ShortExact := by
  obtain ⟨hf, hex, hg⟩ := lie_of_shortExact hS
  obtain ⟨hf', hex', hg'⟩ := centralTranslationMap_shortExact P L S.X₂.property.1
    (isCategoryO_of_finiteDimensional' L) (toLieModuleHom S.f.hom) (toLieModuleHom S.g.hom) hf
    ((exact_iff_ker_eq_range P _ _).mp hex) hg χ₁ χ₂
  exact shortExact_of_lie hf' hg' fun y hy ↦ ((exact_iff_ker_eq_range P _ _).mpr hex' y).mp hy

instance : PreservesFiniteLimits (translationFunctor L χ₁ χ₂) :=
  (((Functor.exact_tfae _).out 1 4).mp fun _ hS ↦ translationFunctor_shortExact L χ₁ χ₂ hS).1

instance : PreservesFiniteColimits (translationFunctor L χ₁ χ₂) :=
  (((Functor.exact_tfae _).out 1 4).mp fun _ hS ↦ translationFunctor_shortExact L χ₁ χ₂ hS).2

/-- `Hom(T X, Y) ≅ Hom(X, T' Y)` in `𝒪`, from `homTranslationEquiv`. -/
def translationHomEquiv (X Y : CategoryO.{u} P) :
    ((translationFunctor L χ₁ χ₂).obj X ⟶ Y) ≃ₗ[K]
      (X ⟶ (translationFunctor (Module.Dual K L) χ₂ χ₁).obj Y) :=
  (homEquivLie _ _).trans <|
    (lieModuleHomCongr P (ofLieEquiv (P := P) (centralTranslation P L χ₁ χ₂ X.obj)).symm
      LieModuleEquiv.refl).trans <|
    (homTranslationEquiv P χ₁ χ₂ X.property.1 (isCategoryO_of_finiteDimensional' L)).trans <|
    (lieModuleHomCongr P LieModuleEquiv.refl
      (ofLieEquiv (P := P) (centralTranslation P (Module.Dual K L) χ₂ χ₁ Y.obj))).trans
    (homEquivLie _ _).symm

theorem translationHomEquiv_comp_left {X' X Y : CategoryO.{u} P} (f : X' ⟶ X)
    (h : (translationFunctor L χ₁ χ₂).obj X ⟶ Y) :
    translationHomEquiv L χ₁ χ₂ X' Y ((translationFunctor L χ₁ χ₂).map f ≫ h) =
      f ≫ translationHomEquiv L χ₁ χ₂ X Y h := by
  ext x
  exact LieModuleHom.congr_fun (homTranslationEquiv_comp_left P χ₁ χ₂ X'.property.1
    X.property.1 (isCategoryO_of_finiteDimensional' L) (toLieModuleHom f.hom)
    ((toLieModuleHom h.hom).comp
      (ofLieEquiv (P := P) (centralTranslation P L χ₁ χ₂ X.obj)).toLieModuleHom)) x

theorem translationHomEquiv_comp_right {X Y Y' : CategoryO.{u} P}
    (h : (translationFunctor L χ₁ χ₂).obj X ⟶ Y) (k : Y ⟶ Y') :
    translationHomEquiv L χ₁ χ₂ X Y' (h ≫ k) =
      translationHomEquiv L χ₁ χ₂ X Y h ≫ (translationFunctor (Module.Dual K L) χ₂ χ₁).map k := by
  ext x
  exact LieModuleHom.congr_fun (homTranslationEquiv_comp_right P χ₁ χ₂ X.property.1
    (isCategoryO_of_finiteDimensional' L)
    ((toLieModuleHom h.hom).comp
      (ofLieEquiv (P := P) (centralTranslation P L χ₁ χ₂ X.obj)).toLieModuleHom)
    (toLieModuleHom k.hom)) x

/-- **Translation functors are adjoint** on `𝒪` ([HumO] Prop 7.2 (a)):
`pr_{χ₂}(pr_{χ₁}(−) ⊗ L) ⊣ pr_{χ₁}(pr_{χ₂}(−) ⊗ L^*)`. -/
def translationAdj :
    translationFunctor L χ₁ χ₂ ⊣ translationFunctor (Module.Dual K L) χ₂ χ₁ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦ (translationHomEquiv L χ₁ χ₂ X Y).toEquiv
      homEquiv_naturality_left_symm := fun {X' X Y} f g ↦ by
        apply (translationHomEquiv L χ₁ χ₂ X' Y).injective
        simp only [LinearEquiv.coe_toEquiv_symm, LinearEquiv.apply_symm_apply,
          translationHomEquiv_comp_left]
      homEquiv_naturality_right := fun f g ↦ translationHomEquiv_comp_right L χ₁ χ₂ f g }

/-- **[HumO] Proposition 7.2 (b).** For a finite-dimensional module `L` and central characters
`χ₁, χ₂`, the translation functors `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L)` and
`T' = pr_{χ₁}(pr_{χ₂}(−) ⊗ L^*)` satisfy `Extⁿ_𝒪(T X, Y) ≅ Extⁿ_𝒪(X, T' Y)` for all `n`.
Finite type, algebraically closed field of characteristic zero (Humphreys works over `ℂ`). -/
def extTranslationEquiv (X Y : CategoryO.{u} P) (n : ℕ) :
    Abelian.Ext.{u} ((translationFunctor L χ₁ χ₂).obj X) Y n ≃ₗ[K]
      Abelian.Ext.{u} X ((translationFunctor (Module.Dual K L) χ₂ χ₁).obj Y) n :=
  (translationAdj L χ₁ χ₂).extLinearEquiv K

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
