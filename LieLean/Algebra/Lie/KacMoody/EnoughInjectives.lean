/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.FiniteLength
import LieLean.Algebra.Lie.KacMoody.DualVerma

/-!
# Enough injectives in category `𝒪`

We prove the injective half of Humphreys, GSM 94, Theorem 3.8: every finitely generated module in
`𝒪` embeds into an injective module in `𝒪`, namely the dual `Q^∨` of a finite direct sum `Q` of the
projectives `M(λ + nρ) ⊗ L(nρ)^*`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsInjectiveO`: injectivity in `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.restrictedDualAnnihilator`: the annihilator in `V` of a
  submodule of `V^∨`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.surjective_restrictedDualMap`: the dual of an injection of
  `𝔥`-diagonalizable modules is surjective.
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveO.isInjectiveO_restrictedDual`: the dual of a
  projective module is injective.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.exists_strictMono_restrictedDual`: if `V ∈ 𝒪` has
  finite length, so does `V^∨`.
* `Matrix.Realization.KacMoodyAlgebra.exists_isInjectiveO_injective`: **enough injectives**
  (Humphreys, GSM 94, Theorem 3.8).

## Proof notes

Humphreys deduces enough injectives from enough projectives by the duality of §3.2. We follow
this: `M^∨` is finitely generated because `M` has finite length (Theorem 1.11) and taking
annihilators is strictly antitone; a cover `Q ↠ M^∨` (Theorem 3.8) gives `M ↪ Q^∨`, and `Q^∨` is
injective since `Hom(N, Q^∨) ≅ Hom(Q, N^∨)` (`dualSwap`) and `N^∨ ↠ M^∨` for `M ↪ N`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.2, §3.8.
-/

noncomputable section

open Module LieModule

universe w

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]

/-- A module whose lattice of submodules admits a strictly monotone `ℕ`-valued function is finitely
generated. -/
theorem exists_finset_lieSpan_eq_top_of_strictMono {f : LieSubmodule R L M → ℕ}
    (hf : StrictMono f) : ∃ S : Finset M, lieSpan R L (S : Set M) = ⊤ := by
  classical
  have : WellFoundedGT (LieSubmodule R L M) := by
    refine StrictAnti.wellFoundedGT (f := fun N ↦ f ⊤ - f N) fun a b hab ↦ ?_
    have h1 := hf hab
    have h2 := hf.monotone (le_top : b ≤ ⊤)
    change f ⊤ - f b < f ⊤ - f a
    omega
  obtain ⟨N, ⟨S, rfl⟩, hmax⟩ := (wellFounded_gt (α := LieSubmodule R L M)).has_min
    (Set.range fun S : Finset M ↦ lieSpan R L (S : Set M)) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨S, eq_top_iff.mpr fun x _ ↦ ?_⟩
  by_contra hx
  refine hmax _ ⟨insert x S, rfl⟩ (lt_of_le_of_ne (lieSpan_mono ?_) fun he ↦ hx ?_)
  · rw [Finset.coe_insert]
    exact Set.subset_insert _ _
  · have he' : lieSpan R L (S : Set M) = lieSpan R L ((insert x S : Finset M) : Set M) := he
    rw [he']
    exact subset_lieSpan (by simp)

end LieSubmodule

namespace Matrix.Realization.KacMoodyAlgebra

open TwistedDual

/-! ### Duality and injectivity -/

section Generic

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

local notation "𝔤" => KacMoodyAlgebra P

variable (V) in
/-- `V` is **injective in `𝒪`** (Humphreys, GSM 94, §3.8): for every injection `f : M → N` of
modules in `𝒪` (in the universe `w`), every morphism `φ : M → V` extends to `ψ : N → V` with
`ψ ∘ f = φ`. -/
def IsInjectiveO : Prop :=
  ∀ ⦃M N : Type w⦄ [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N] [LieModule K 𝔤 N],
    IsCategoryO P M → IsCategoryO P N → ∀ f : M →ₗ⁅K,𝔤⁆ N, Function.Injective f →
      ∀ φ : M →ₗ⁅K,𝔤⁆ V, ∃ ψ : N →ₗ⁅K,𝔤⁆ V, ψ.comp f = φ

/-- The dual of an injection of `𝔥`-diagonalizable modules is surjective (Humphreys, GSM 94, §3.2:
the duality functor is exact). -/
theorem surjective_restrictedDualMap (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤) (f : V →ₗ⁅K,𝔤⁆ W)
    (hf : Function.Injective f) : Function.Surjective (restrictedDualMap P f) := by
  rintro ⟨φ, hφ⟩
  suffices H : ∀ φ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P V) (h P) μ,
      ∃ ψ : restrictedDual P W, (restrictedDualMap P f ψ).1 = φ by
    obtain ⟨ψ, hψ⟩ := H φ hφ
    exact ⟨ψ, Subtype.ext hψ⟩
  intro φ hφ
  induction hφ using Submodule.iSup_induction' with
  | mem κ φ hφ =>
    let fκ : weightSpaceOfMap V (h P) κ →ₗ[K] weightSpaceOfMap W (h P) κ :=
      ((f : V →ₗ[K] W).comp (weightSpaceOfMap V (h P) κ).subtype).codRestrict _
        fun x ↦ map_mem_weightSpaceOfMap P f x.2
    have hfκ : LinearMap.ker fκ = ⊥ := LinearMap.ker_eq_bot.mpr fun x y hxy ↦
      Subtype.ext (hf (congrArg Subtype.val hxy))
    obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective fκ hfκ
    let g : Module.Dual K (weightSpaceOfMap W (h P) κ) :=
      ((TwistedDual.toDual P V φ).comp (weightSpaceOfMap V (h P) κ).subtype).comp r
    refine ⟨⟨(TwistedDual.toDual P W).symm (g ∘ₗ weightProj P hW κ),
      Submodule.mem_iSup_of_mem κ (mem_weightSpace_twistedDual_comp hW κ g)⟩, ?_⟩
    apply TwistedDual.ext
    intro v
    rw [toDual_restrictedDualMap, LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
    have hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := hV ▸ Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem ν v hv =>
      by_cases hν : ν = κ
      · subst hν
        rw [weightProj_of_mem hW (map_mem_weightSpaceOfMap P f hv)]
        have hfv : (⟨f v, map_mem_weightSpaceOfMap P f hv⟩ : weightSpaceOfMap W (h P) ν) =
            fκ ⟨v, hv⟩ := rfl
        have hrv : r (fκ ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hr ⟨v, hv⟩
        simp only [g, LinearMap.comp_apply]
        rw [hfv, hrv]
        rfl
      · rw [weightProj_of_mem_ne hW (map_mem_weightSpaceOfMap P f hv) hν, map_zero,
          TwistedDual.apply_eq_zero_of_ne hφ hv (Ne.symm hν)]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [map_add]
      rw [hx, hy]
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨ψ₁, e₁⟩ := h₁
    obtain ⟨ψ₂, e₂⟩ := h₂
    exact ⟨ψ₁ + ψ₂, by rw [map_add]; exact congrArg₂ (· + ·) e₁ e₂⟩

/-- **The dual of a projective module in `𝒪` is injective in `𝒪`** (Humphreys, GSM 94, §3.8):
`Hom(N, Q^∨) ≅ Hom(Q, N^∨)` and `N^∨ → M^∨` is surjective for `M ↪ N`. -/
theorem IsProjectiveO.isInjectiveO_restrictedDual {Q : Type*} [AddCommGroup Q] [Module K Q]
    [LieRingModule 𝔤 Q] [LieModule K 𝔤 Q] (hQ : IsProjectiveO.{w} P Q)
    (hQw : ⨆ μ, weightSpaceOfMap Q (h P) μ = ⊤) : IsInjectiveO.{w} P (restrictedDual P Q) := by
  intro M N _ _ _ _ _ _ _ _ hM hN f hf φ
  obtain ⟨g, hg⟩ := hQ (isCategoryO_restrictedDual hN) (isCategoryO_restrictedDual hM)
    (restrictedDualMap P f) (surjective_restrictedDualMap P hM.iSup_weightSpaceOfMap_eq_top
      hN.iSup_weightSpaceOfMap_eq_top f hf) (dualSwap hQw φ)
  refine ⟨dualSwap hN.iSup_weightSpaceOfMap_eq_top g,
    LieModuleHom.ext fun m ↦ restrictedDual_ext P fun q ↦ ?_⟩
  exact congrArg (fun F : restrictedDual P M ↦ TwistedDual.toDual P M F.1 m)
    (LieModuleHom.congr_fun hg q)

variable (V) in
/-- The annihilator `{v | φ(v) = 0 for all φ ∈ S}` in `V` of a submodule `S` of `V^∨`. -/
def restrictedDualAnnihilator (S : LieSubmodule K 𝔤 (restrictedDual P V)) :
    LieSubmodule K 𝔤 V where
  carrier := {v | ∀ φ ∈ S, TwistedDual.toDual P V φ.1 v = 0}
  add_mem' {x y} hx hy φ hφ := by rw [map_add, hx φ hφ, hy φ hφ, add_zero]
  zero_mem' _ _ := map_zero _
  smul_mem' c v hv φ hφ := by rw [map_smul, hv φ hφ, smul_zero]
  lie_mem {x v} hv φ hφ := by
    have h1 := hv _ (S.lie_mem (x := transpose P x) hφ)
    rwa [LieSubmodule.coe_bracket, TwistedDual.lie_apply, transpose_transpose] at h1

lemma mem_restrictedDualAnnihilator {S : LieSubmodule K 𝔤 (restrictedDual P V)} {v : V} :
    v ∈ restrictedDualAnnihilator P V S ↔ ∀ φ ∈ S, TwistedDual.toDual P V φ.1 v = 0 :=
  Iff.rfl

/-- For `V ∈ 𝒪`, taking annihilators is strictly antitone on submodules of `V^∨`. -/
theorem restrictedDualAnnihilator_strictAnti (hV : IsCategoryO P V) :
    StrictAnti (restrictedDualAnnihilator P V) := by
  intro S₁ S₂ hlt
  refine lt_of_le_of_ne (fun v hv ↦ mem_restrictedDualAnnihilator P |>.mpr fun φ hφ ↦
    (mem_restrictedDualAnnihilator P).mp hv φ (hlt.le hφ)) fun he ↦ ?_
  have hR := isCategoryO_restrictedDual hV
  have hdec : ∀ S : LieSubmodule K 𝔤 (restrictedDual P V),
      S.toSubmodule ≤ ⨆ μ, S.toSubmodule ⊓ weightSpaceOfMap (restrictedDual P V) (h P) μ := by
    intro S φ hφ
    have hmem : φ ∈ S.toSubmodule ⊓
        ⨆ μ ∈ Set.univ, weightSpaceOfMap (restrictedDual P V) (h P) μ := by
      refine ⟨hφ, ?_⟩
      simp only [Set.mem_univ, iSup_pos]
      rw [hR.iSup_weightSpaceOfMap_eq_top]
      trivial
    have := inf_iSup_weightSpaceOfMap_le (h P) S.toSubmodule (fun a m hm ↦ S.lie_mem hm)
      Set.univ hmem
    simpa only [Set.mem_univ, iSup_pos] using this
  obtain ⟨κ, φ, hφ₂, hφκ, hφ₁⟩ : ∃ κ, ∃ φ ∈ S₂,
      φ ∈ weightSpaceOfMap (restrictedDual P V) (h P) κ ∧ φ ∉ S₁ := by
    by_contra hcon
    push Not at hcon
    refine hlt.not_ge fun φ hφ ↦ ?_
    refine (iSup_le fun μ ↦ ?_ : ⨆ μ, S₂.toSubmodule ⊓
      weightSpaceOfMap (restrictedDual P V) (h P) μ ≤ S₁.toSubmodule) (hdec S₂ hφ)
    rintro ψ ⟨hψ₂, hψμ⟩
    exact hcon μ ψ hψ₂ hψμ
  have := hV.finiteDimensional_weightSpaceOfMap κ
  let ρ : restrictedDual P V →ₗ[K] Module.Dual K (weightSpaceOfMap V (h P) κ) :=
    { toFun := fun ψ ↦
        (TwistedDual.toDual P V ψ.1).comp (weightSpaceOfMap V (h P) κ).subtype
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hρ : ∀ μ, μ ≠ κ → ∀ ψ ∈ weightSpaceOfMap (restrictedDual P V) (h P) μ, ρ ψ = 0 := by
    intro μ hμ ψ hψ
    exact LinearMap.ext fun x ↦ TwistedDual.apply_eq_zero_of_ne
      (mem_weightSpaceOfMap_lieSubmodule_iff.mp hψ) x.2 hμ
  set W₁ := S₁.toSubmodule.map ρ
  have hW₁ : W₁ ≤ (S₁.toSubmodule ⊓ weightSpaceOfMap (restrictedDual P V) (h P) κ).map ρ := by
    rintro _ ⟨ψ, hψ, rfl⟩
    refine (iSup_le fun μ ↦ ?_ : ⨆ μ, S₁.toSubmodule ⊓
      weightSpaceOfMap (restrictedDual P V) (h P) μ ≤
        ((S₁.toSubmodule ⊓ weightSpaceOfMap (restrictedDual P V) (h P) κ).map ρ).comap ρ)
      (hdec S₁ hψ)
    by_cases hμ : μ = κ
    · subst hμ
      exact Submodule.le_comap_map _ _
    · rintro ψ' ⟨-, hψ'⟩
      rw [Submodule.mem_comap, hρ μ hμ ψ' hψ']
      exact zero_mem _
  have hφW : ρ φ ∉ W₁ := by
    intro hφ'
    obtain ⟨ψ, ⟨hψ₁, hψκ⟩, hψφ⟩ := hW₁ hφ'
    apply hφ₁
    have h0 := eq_zero_of_mem_weightSpace_twistedDual hV.iSup_weightSpaceOfMap_eq_top
      (κ := κ) (φ := (φ - ψ).1)
      (mem_weightSpaceOfMap_lieSubmodule_iff.mp (sub_mem hφκ hψκ)) fun v hv ↦ by
        have := LinearMap.congr_fun hψφ ⟨v, hv⟩
        change TwistedDual.toDual P V ψ.1 v = TwistedDual.toDual P V φ.1 v at this
        change TwistedDual.toDual P V (φ.1 - ψ.1) v = 0
        rw [map_sub, LinearMap.sub_apply, this, sub_self]
    have hφψ : φ = ψ := sub_eq_zero.mp (Subtype.ext h0)
    rw [hφψ]
    exact hψ₁
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W₁), Submodule.mem_dualAnnihilator]
    at hφW
  push Not at hφW
  obtain ⟨u, hu, hφu⟩ := hφW
  have hu₁ : (u : V) ∈ restrictedDualAnnihilator P V S₁ :=
    (mem_restrictedDualAnnihilator P).mpr fun ψ hψ ↦
      ((Submodule.mem_dualCoannihilator _).mp hu) (ρ ψ) ⟨ψ, hψ, rfl⟩
  rw [← he] at hu₁
  exact hφu ((mem_restrictedDualAnnihilator P).mp hu₁ φ hφ₂)

/-- **Duality preserves finite length**: if the submodules of `V ∈ 𝒪` admit a strictly monotone
`ℕ`-valued function, so do those of `V^∨`. -/
theorem IsCategoryO.exists_strictMono_restrictedDual (hV : IsCategoryO P V)
    {f : LieSubmodule K 𝔤 V → ℕ} (hf : StrictMono f) :
    ∃ F : LieSubmodule K 𝔤 (restrictedDual P V) → ℕ, StrictMono F :=
  ⟨fun S ↦ f ⊤ - f (restrictedDualAnnihilator P V S), fun S₁ S₂ hlt ↦ by
    have h1 := hf (restrictedDualAnnihilator_strictAnti P hV hlt)
    have h2 := hf.monotone (le_top : restrictedDualAnnihilator P V S₁ ≤ ⊤)
    change f ⊤ - f _ < f ⊤ - f _
    omega⟩

/-- `V^∨` separates the points of `V ∈ 𝒪`. -/
theorem IsCategoryO.eq_zero_of_forall_restrictedDual (hV : IsCategoryO P V) {v : V}
    (hv : ∀ φ : restrictedDual P V, TwistedDual.toDual P V φ.1 v = 0) : v = 0 := by
  set N := restrictedDualAnnihilator P V ⊤
  have hvN : v ∈ N := (mem_restrictedDualAnnihilator P).mpr fun φ _ ↦ hv φ
  suffices hN : N = ⊥ by
    rw [hN] at hvN
    exact (LieSubmodule.mem_bot v).mp hvN
  by_contra hN
  have hNO := hV.lieSubmodule N
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff N.toSubmodule).mp
    fun h ↦ hN ((LieSubmodule.toSubmodule_eq_bot N).mp h)
  obtain ⟨κ, hκ⟩ : ∃ κ, weightSpaceOfMap N (h P) κ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Submodule K N) = ⊥ := by
      rw [← hNO.iSup_weightSpaceOfMap_eq_top]
      exact iSup_eq_bot.mpr hcon
    have : (⟨x, hx⟩ : N) ∈ (⊥ : Submodule K N) := htop ▸ Submodule.mem_top
    exact hx0 (congrArg Subtype.val ((Submodule.mem_bot K).mp this))
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hκ
  have hyV : (y : V) ∈ weightSpaceOfMap V (h P) κ := mem_weightSpaceOfMap_lieSubmodule_iff.mp hy
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual K (weightSpaceOfMap V (h P) κ), g ⟨y, hyV⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := (Module.forall_dual_apply_eq_zero_iff K
      (⟨y, hyV⟩ : weightSpaceOfMap V (h P) κ)).mp hcon
    exact hy0 (Subtype.ext (congrArg Subtype.val h : (y : V) = 0))
  have h0 := (mem_restrictedDualAnnihilator P).mp y.2
    ⟨(TwistedDual.toDual P V).symm (g ∘ₗ weightProj P hV.iSup_weightSpaceOfMap_eq_top κ),
    Submodule.mem_iSup_of_mem κ
      (mem_weightSpace_twistedDual_comp hV.iSup_weightSpaceOfMap_eq_top κ g)⟩
    (LieSubmodule.mem_top _)
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    weightProj_of_mem hV.iSup_weightSpaceOfMap_eq_top hyV] at h0
  exact hg h0

end Generic

/-! ### Enough injectives -/

section Existence

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]

local notation "𝔤" => KacMoodyAlgebra P

universe w'

/-- **Enough injectives in `𝒪`** (Humphreys, GSM 94, Theorem 3.8, injective part). In finite type
over an algebraically closed field of characteristic zero, every finitely generated module `M` in
`𝒪` embeds into the dual `I = Q^∨` of a finite direct sum `Q` of the modules `M(λ + nρ) ⊗ L(nρ)^*`.
The module `I` is finitely generated and lies in `𝒪`, and it is injective against all injections
between modules satisfying `IsCategoryO`. Humphreys works over `ℂ`. -/
theorem exists_isInjectiveO_injective (hM : IsCategoryO P M) {S : Finset M}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : κ → Dual K H),
      IsCategoryO P (restrictedDual P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))) ∧
      IsInjectiveO.{w'} P
        (restrictedDual P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))) ∧
      (∃ T : Finset (restrictedDual P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))),
        LieSubmodule.lieSpan K 𝔤 (T : Set (restrictedDual P
          (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)))) = ⊤) ∧
      ∃ e : M →ₗ⁅K,𝔤⁆ restrictedDual P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)),
        Function.Injective e := by
  have hMd := isCategoryO_restrictedDual hM
  have h1 := IsCategoryO.exists_strictMono_lieSubmodule P hA hM hS
  obtain ⟨f, hf⟩ := h1
  have h2 := hM.exists_strictMono_restrictedDual P hf
  obtain ⟨Fd, hFd⟩ := h2
  have h3 := LieSubmodule.exists_finset_lieSpan_eq_top_of_strictMono hFd
  obtain ⟨Sd, hSd⟩ := h3
  have h4 := hMd.isCovered P hA hSd
  obtain ⟨κ, _, _, τ, π, hπ⟩ := h4
  have hQO : IsCategoryO P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) :=
    IsCategoryO.directSum _ fun j ↦ isCategoryO_projectiveCoverAmbient P hA _ _
  have hQproj : IsProjectiveO.{w'} P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) :=
    IsProjectiveO.directSum fun j ↦ isProjectiveO_projectiveCoverAmbient' P hA _
  have h5 := exists_finset_lieSpan_directSum_eq_top fun j ↦
    exists_finset_lieSpan_projectiveCoverAmbient'_eq_top P hA (τ j)
  obtain ⟨T, hT⟩ := h5
  have h6 := hQO.exists_strictMono_lieSubmodule P hA hT
  obtain ⟨fQ, hfQ⟩ := h6
  have h7 := hQO.exists_strictMono_restrictedDual P hfQ
  obtain ⟨FQ, hFQ⟩ := h7
  refine ⟨κ, inferInstance, inferInstance, τ, isCategoryO_restrictedDual hQO,
    hQproj.isInjectiveO_restrictedDual P hQO.iSup_weightSpaceOfMap_eq_top,
    LieSubmodule.exists_finset_lieSpan_eq_top_of_strictMono hFQ,
    dualSwap hM.iSup_weightSpaceOfMap_eq_top π, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro m hm
  refine hM.eq_zero_of_forall_restrictedDual P fun φ ↦ ?_
  have h8 := hπ φ
  obtain ⟨q, rfl⟩ := h8
  have h0 : TwistedDual.toDual P _ (dualSwap hM.iSup_weightSpaceOfMap_eq_top π m).1 q = 0 := by
    rw [hm]
    rfl
  exact h0

end Existence

end Matrix.Realization.KacMoodyAlgebra
