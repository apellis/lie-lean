/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOEulerChar
import LieLean.Algebra.Lie.KacMoody.CategoryOExtCriterion
import LieLean.Algebra.Lie.KacMoody.DualVermaSocle
import LieLean.Algebra.Lie.KacMoody.TranslationAdjunction

/-!
# Delorme's character formula

[HumO] Proposition 6.14. For every `N ∈ 𝒪`,
`ch N = ∑_μ χ(Ext•_𝒪(M(μ), N)) ch M(μ)`, where `χ` is the Euler characteristic
`∑ₙ (-1)ⁿ dim Extⁿ_𝒪(M(μ), N)` (`CategoryO.eulerChar`) and only finitely many terms are nonzero
(`CategoryO.character_eq_sum_eulerChar`). Equivalently, for the multiplicities,
`[N : L(ν)] = ∑_μ χ(Ext•_𝒪(M(μ), N)) [M(μ) : L(ν)]` (`CategoryO.multiplicity_eq_sum_eulerChar`).

## Proof

Both sides are additive on short exact sequences (`CategoryO.eulerChar_eq_add`), so the formula
holds for the middle term, or for the first term, of a short exact sequence once it holds for the
other two (`CategoryO.hasDelormeFormula_of_shortExact`). For a dual Verma module `M(λ)^∨` it holds
since `Extⁿ(M(μ), M(λ)^∨) = 0` for `n > 0` and `dim Hom(M(μ), M(λ)^∨) = δ_{λμ}` ([HumO] Thm 3.3).
For a simple module `L(λ)` it follows from `0 → L(λ) → M(λ)^∨ → Q → 0`, by induction on the number
of weights of the dot orbit `W·λ` below `λ`, since the composition factors `L(ν)` of `Q` have
`ν ∈ W·λ`, `ν < λ`. For general `N` it follows by induction on the submodules of `N`.

Humphreys deduces the formula from BGG reciprocity for the injective hulls of the simple modules.
The argument here avoids injective hulls; it uses the same two inputs, additivity of the Euler
characteristic and the computation for dual Verma modules.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.14.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe u

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### `Ext` along isomorphisms -/

theorem postcompLinear_comp (X : CategoryO.{u} P) {Y Y' Y'' : CategoryO.{u} P} (f : Y ⟶ Y')
    (g : Y' ⟶ Y'') (n : ℕ) (x : Abelian.Ext.{u} X Y n) :
    postcompLinear X g n (postcompLinear X f n x) = postcompLinear X (f ≫ g) n x := by
  simp only [postcompLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

theorem postcompLinear_id (X Y : CategoryO.{u} P) (n : ℕ) (x : Abelian.Ext.{u} X Y n) :
    postcompLinear X (𝟙 Y) n x = x :=
  Abelian.Ext.comp_mk₀_id x

/-- `dim Extⁿ(X, -)` agrees on objects of `𝒪` with isomorphic underlying `𝔤`-modules. -/
theorem finrank_ext_congr (X : CategoryO.{u} P) {Z Z' : CategoryO.{u} P}
    (e : Z.obj ≃ₗ⁅K,𝔤⁆ Z'.obj) (n : ℕ) :
    finrank K (Abelian.Ext.{u} X Z n) = finrank K (Abelian.Ext.{u} X Z' n) := by
  let f : Z ⟶ Z' := (IsObj.{u} P).homMk (ofLieModuleHom e.toLieModuleHom)
  let g : Z' ⟶ Z := (IsObj.{u} P).homMk (ofLieModuleHom e.symm.toLieModuleHom)
  have hfg : f ≫ g = 𝟙 Z := by
    ext z
    exact e.symm_apply_apply z
  have hgf : g ≫ f = 𝟙 Z' := by
    ext z
    exact e.apply_symm_apply z
  exact LinearEquiv.finrank_eq
    { postcompLinear X f n with
      invFun := postcompLinear X g n
      left_inv := fun x ↦ by
        change postcompLinear X g n (postcompLinear X f n x) = x
        rw [postcompLinear_comp, hfg, postcompLinear_id]
      right_inv := fun x ↦ by
        change postcompLinear X f n (postcompLinear X g n x) = x
        rw [postcompLinear_comp, hgf, postcompLinear_id] }

/-- Morphisms in `𝒪` are the morphisms of the underlying `𝔤`-modules. -/
def homEquivLie (X Y : CategoryO.{u} P) : (X ⟶ Y) ≃ₗ[K] (X.obj →ₗ⁅K,𝔤⁆ Y.obj) :=
  LinearEquiv.ofBijective (homToLie X Y) ⟨injective_homToLie X Y, fun φ ↦
    ⟨(IsObj.{u} P).homMk (ofLieModuleHom φ), LieModuleHom.ext fun _ ↦ rfl⟩⟩

variable (hA : A.IsFiniteCartan)

theorem eulerChar_congr (μ : Dual K H) {Z Z' : CategoryO.{u} P} (e : Z.obj ≃ₗ⁅K,𝔤⁆ Z'.obj) :
    eulerChar hA μ Z = eulerChar hA μ Z' :=
  Finset.sum_congr rfl fun n _ ↦ by rw [finrank_ext_congr (verma P μ) e n]

/-! ### Multiplicities along short exact sequences -/

theorem multiplicity_kerComplex (X Z : CategoryO.{u} P) (φ : X.obj →ₗ⁅K,𝔤⁆ Z.obj)
    (hφ : Function.Surjective φ) (ν : Dual K H) :
    X.property.1.multiplicity ν =
      (ofSub X φ.ker).property.1.multiplicity ν + Z.property.1.multiplicity ν := by
  rw [IsCategoryO.multiplicity_eq_add_of_exact (X.property.1.lieSubmodule φ.ker) X.property.1
      Z.property.1 φ.ker.incl φ Subtype.val_injective φ.ker.range_incl.symm hφ,
    IsCategoryO.multiplicity_congr (X.property.1.lieSubmodule φ.ker) (ofSub X φ.ker).property.1
      (ofLieEquiv (P := P) φ.ker)]

theorem multiplicity_subComplex (X : CategoryO.{u} P) {N N' : LieSubmodule K 𝔤 X.obj}
    (hle : N ≤ N') (Z : CategoryO.{u} P) (g : N' →ₗ⁅K,𝔤⁆ Z.obj)
    (hg : ∀ x (hx : x ∈ N), g ⟨x, hle hx⟩ = 0) (hgs : Function.Surjective g)
    (hker : ∀ y : N', g y = 0 → (y : X.obj) ∈ N) (ν : Dual K H) :
    (ofSub X N').property.1.multiplicity ν =
      (ofSub X N).property.1.multiplicity ν + Z.property.1.multiplicity ν := by
  rw [← IsCategoryO.multiplicity_congr (X.property.1.lieSubmodule N') (ofSub X N').property.1
      (ofLieEquiv (P := P) N'),
    ← IsCategoryO.multiplicity_congr (X.property.1.lieSubmodule N) (ofSub X N).property.1
      (ofLieEquiv (P := P) N),
    IsCategoryO.multiplicity_eq_add_of_exact (X.property.1.lieSubmodule N)
      (X.property.1.lieSubmodule N') Z.property.1 (LieSubmodule.inclusion hle) g
      (LieSubmodule.inclusion_injective hle) ?_ hgs]
  ext y
  rw [LieModuleHom.mem_ker, LieModuleHom.mem_range]
  constructor
  · intro hy
    exact ⟨⟨y, hker y hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact hg x.1 x.2

/-! ### The formula as a property of objects -/

/-- `∑_{μ ∈ T} χ(Ext•(M(μ), N)) [M(μ) : L(ν)]`. -/
def delormeSum (N : CategoryO.{u} P) (T : Finset (Dual K H)) (ν : Dual K H) : ℤ :=
  ∑ μ ∈ T, eulerChar hA μ N * ((VermaModule.isCategoryO P μ).multiplicity ν : ℤ)

/-- `N` satisfies Delorme's formula `[N : L(ν)] = ∑_μ χ(Ext•(M(μ), N)) [M(μ) : L(ν)]`, with
finitely many nonzero Euler characteristics. -/
def HasDelormeFormula (N : CategoryO.{u} P) : Prop :=
  ∃ T : Finset (Dual K H), (∀ μ ∉ T, eulerChar hA μ N = 0) ∧
    ∀ ν, (N.property.1.multiplicity ν : ℤ) = delormeSum hA N T ν

theorem delormeSum_eq_of_subset {N : CategoryO.{u} P} {T T' : Finset (Dual K H)}
    (hTT' : T ⊆ T') (hT : ∀ μ ∉ T, eulerChar hA μ N = 0) (ν : Dual K H) :
    delormeSum hA N T ν = delormeSum hA N T' ν :=
  Finset.sum_subset hTT' fun μ _ hμ ↦ by rw [hT μ hμ, zero_mul]

theorem delormeSum_eq_add {S : ShortComplex (CategoryO.{u} P)} (hS : S.ShortExact)
    (T : Finset (Dual K H)) (ν : Dual K H) :
    delormeSum hA S.X₂ T ν = delormeSum hA S.X₁ T ν + delormeSum hA S.X₃ T ν := by
  rw [delormeSum, delormeSum, delormeSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ ↦ by rw [eulerChar_eq_add hA μ hS, add_mul]

/-- **Two out of three.** For a short exact sequence `0 → A → B → C → 0`, Delorme's formula for
`A` and `C` gives it for `B`, and Delorme's formula for `B` and `C` gives it for `A`. -/
theorem hasDelormeFormula_of_shortExact {S : ShortComplex (CategoryO.{u} P)}
    (hS : S.ShortExact) (hm : ∀ ν, S.X₂.property.1.multiplicity ν =
      S.X₁.property.1.multiplicity ν + S.X₃.property.1.multiplicity ν) :
    (HasDelormeFormula hA S.X₁ → HasDelormeFormula hA S.X₃ → HasDelormeFormula hA S.X₂) ∧
      (HasDelormeFormula hA S.X₂ → HasDelormeFormula hA S.X₃ → HasDelormeFormula hA S.X₁) := by
  classical
  constructor
  · rintro ⟨T₁, hT₁, h₁⟩ ⟨T₃, hT₃, h₃⟩
    refine ⟨T₁ ∪ T₃, fun μ hμ ↦ ?_, fun ν ↦ ?_⟩
    · rw [Finset.mem_union, not_or] at hμ
      rw [eulerChar_eq_add hA μ hS, hT₁ μ hμ.1, hT₃ μ hμ.2, add_zero]
    · rw [hm ν, Nat.cast_add, h₁ ν, h₃ ν,
        delormeSum_eq_of_subset hA Finset.subset_union_left hT₁,
        delormeSum_eq_of_subset hA Finset.subset_union_right hT₃, delormeSum_eq_add hA hS]
  · rintro ⟨T₂, hT₂, h₂⟩ ⟨T₃, hT₃, h₃⟩
    refine ⟨T₂ ∪ T₃, fun μ hμ ↦ ?_, fun ν ↦ ?_⟩
    · rw [Finset.mem_union, not_or] at hμ
      have := eulerChar_eq_add hA μ hS
      rw [hT₂ μ hμ.1, hT₃ μ hμ.2] at this
      linarith
    · have h := delormeSum_eq_add hA hS (T₂ ∪ T₃) ν
      rw [← delormeSum_eq_of_subset hA Finset.subset_union_left hT₂,
        ← delormeSum_eq_of_subset hA Finset.subset_union_right hT₃, ← h₂ ν, ← h₃ ν, hm ν,
        Nat.cast_add] at h
      linarith

theorem HasDelormeFormula.of_equiv {N N' : CategoryO.{u} P} (e : N.obj ≃ₗ⁅K,𝔤⁆ N'.obj)
    (h : HasDelormeFormula hA N) : HasDelormeFormula hA N' := by
  obtain ⟨T, hT, hN⟩ := h
  refine ⟨T, fun μ hμ ↦ by rw [← eulerChar_congr hA μ e, hT μ hμ], fun ν ↦ ?_⟩
  rw [← IsCategoryO.multiplicity_congr N.property.1 N'.property.1 e ν, hN ν]
  exact Finset.sum_congr rfl fun μ _ ↦ by rw [eulerChar_congr hA μ e]

/-! ### The zero object and dual Verma modules -/

theorem eulerChar_ofSub_bot (X : CategoryO.{u} P) (μ : Dual K H) :
    eulerChar hA μ (ofSub X ⊥) = 0 := by
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  have : Subsingleton (Abelian.Ext.{u} (verma P μ) (ofSub X ⊥) n) :=
    ⟨fun x y ↦ (Abelian.Ext.eq_zero_of_isZero_right (isZero_ofSub_bot X) x).trans
      (Abelian.Ext.eq_zero_of_isZero_right (isZero_ofSub_bot X) y).symm⟩
  rw [finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

theorem multiplicity_ofSub_bot (X : CategoryO.{u} P) (ν : Dual K H) :
    (ofSub X ⊥).property.1.multiplicity ν = 0 := by
  have : Subsingleton (ofSub X ⊥).obj :=
    inferInstanceAs (Subsingleton (⊥ : LieSubmodule K 𝔤 X.obj))
  have h := IsCategoryO.multiplicity_eq_add_of_exact (ofSub X ⊥).property.1
    (ofSub X ⊥).property.1 (ofSub X ⊥).property.1 0 0 (fun a b _ ↦ Subsingleton.elim a b) ?_
    (fun a ↦ ⟨a, Subsingleton.elim _ _⟩) ν
  · omega
  · ext y
    rw [Subsingleton.elim y 0]
    exact iff_of_true (zero_mem _) (zero_mem _)

theorem hasDelormeFormula_ofSub_bot (X : CategoryO.{u} P) : HasDelormeFormula hA (ofSub X ⊥) :=
  ⟨∅, fun μ _ ↦ eulerChar_ofSub_bot hA X μ, fun ν ↦ by
    rw [multiplicity_ofSub_bot, delormeSum, Finset.sum_empty, Nat.cast_zero]⟩

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem multiplicity_dualVerma (lam ν : Dual K H) :
    (dualVerma P lam).property.1.multiplicity ν =
      (VermaModule.isCategoryO P lam).multiplicity ν := by
  rw [← multiplicity_restrictedDual (VermaModule.isCategoryO P lam) ν,
    IsCategoryO.multiplicity_congr (isCategoryO_restrictedDual (VermaModule.isCategoryO P lam))
      (dualVerma P lam).property.1 (ofLieEquiv (P := P) (restrictedDual P (VermaModule P lam)))]

/-- `dim Hom_𝒪(M(μ), M(λ)^∨) = δ_{λμ}` ([HumO] Thm 3.3 (c)), for `Ext⁰`. -/
theorem finrank_ext_zero_verma_dualVerma [DecidableEq (Dual K H)] (μ lam : Dual K H) :
    finrank K (Abelian.Ext.{u} (verma P μ) (dualVerma P lam) 0) = if lam = μ then 1 else 0 := by
  rw [((Abelian.Ext.linearEquiv₀ (R := K)).trans
    ((homEquivLie (verma P μ) (dualVerma P lam)).trans
      (lieModuleHomCongr P (ofLieEquiv (P := P) (VermaModule P μ)).symm
        (ofLieEquiv (P := P) (restrictedDual P (VermaModule P lam))).symm))).finrank_eq,
    finrank_hom_verma_restrictedDual_verma P lam μ]

theorem eulerChar_dualVerma (μ lam : Dual K H) :
    eulerChar hA μ (dualVerma P lam) =
      finrank K (Abelian.Ext.{u} (verma P μ) (dualVerma P lam) 0) := by
  rw [eulerChar, Finset.sum_eq_single 0 (fun n _ hn ↦ ?_)
    (fun h ↦ absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h)]
  · simp
  have : Subsingleton (Abelian.Ext.{u} (verma P μ) (dualVerma P lam) n) :=
    ⟨fun x y ↦ (ext_verma_dualVerma_eq_zero μ lam (Nat.pos_of_ne_zero hn) x).trans
      (ext_verma_dualVerma_eq_zero μ lam (Nat.pos_of_ne_zero hn) y).symm⟩
  rw [finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

theorem hasDelormeFormula_dualVerma (lam : Dual K H) :
    HasDelormeFormula hA (dualVerma P lam) := by
  classical
  refine ⟨{lam}, fun μ hμ ↦ ?_, fun ν ↦ ?_⟩
  · rw [eulerChar_dualVerma, finrank_ext_zero_verma_dualVerma,
      if_neg (Ne.symm (Finset.notMem_singleton.mp hμ)), Nat.cast_zero]
  · rw [delormeSum, Finset.sum_singleton, eulerChar_dualVerma, finrank_ext_zero_verma_dualVerma,
      if_pos rfl, Nat.cast_one, one_mul, multiplicity_dualVerma]

/-! ### Induction on composition factors -/

/-- Delorme's formula holds for `W` if it holds for every `Z ≅ L(ν)` with `L(ν)` a composition
factor of `W`. -/
theorem hasDelormeFormula_of_multiplicity (W : CategoryO.{u} P)
    (h : ∀ ν, W.property.1.multiplicity ν ≠ 0 → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν) → HasDelormeFormula hA Z) :
    HasDelormeFormula hA W := by
  obtain ⟨S, hS⟩ := W.property.2
  have := W.property.1.wellFoundedLT_lieSubmodule P hA hS
  have := W.property.1.wellFoundedGT_lieSubmodule P hA hS
  refine HasDelormeFormula.of_equiv hA
    ((ofLieEquiv (P := P) (⊤ : LieSubmodule K 𝔤 W.obj)).symm.trans
      (LieModuleEquiv.ofBijective (⊤ : LieSubmodule K 𝔤 W.obj).incl
        ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, LieSubmodule.mem_top y⟩, rfl⟩⟩))
    (WellFoundedLT.induction (motive := fun M ↦ HasDelormeFormula hA (ofSub W M)) ⊤
      fun M ih ↦ ?_)
  by_cases hM : M = ⊥
  · subst hM
    exact hasDelormeFormula_ofSub_bot hA W
  obtain ⟨M', hM'M, ν, hν, ⟨ψ⟩⟩ := W.property.1.exists_subquotient_equiv_of_ne_bot hM
  have hg : ∀ y (hy : y ∈ M'), toSubquotient W M' M ⟨y, hM'M.le hy⟩ = 0 :=
    fun y hy ↦ (toSubquotient_eq_zero_iff W M' M ⟨y, hM'M.le hy⟩).mpr hy
  have hker : ∀ y : M, toSubquotient W M' M y = 0 → (y : W.obj) ∈ M' :=
    fun y hy ↦ (toSubquotient_eq_zero_iff W M' M y).mp hy
  have hS := shortExact_subComplex W hM'M.le (ofSubquotient W M' M) (toSubquotient W M' M) hg
    (surjective_toSubquotient W M' M) hker
  exact (hasDelormeFormula_of_shortExact hA hS (multiplicity_subComplex W hM'M.le
    (ofSubquotient W M' M) (toSubquotient W M' M) hg (surjective_toSubquotient W M' M)
      hker)).1 (ih M' hM'M) (h ν hν _ ((ofLieEquiv (P := P) (M'.Subquotient M)).symm.trans ψ))

/-! ### Simple modules -/

variable (P) in
/-- The weights of the dot orbit `W·μ` strictly below `μ`. -/
def dotOrbitBelow (μ : Dual K H) : Set (Dual K H) :=
  {κ | (∃ w : P.weylGroup hA.isGeneralizedCartan, κ = P.weylDot hA.isGeneralizedCartan w μ) ∧
    κ ∈ cone P μ ∧ κ ≠ μ}

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem finite_dotOrbitBelow (μ : Dual K H) : (dotOrbitBelow P hA μ).Finite := by
  have := P.finite_weylGroup hA
  refine (Set.finite_range fun w : P.weylGroup hA.isGeneralizedCartan ↦
    P.weylDot hA.isGeneralizedCartan w μ).subset ?_
  rintro κ ⟨⟨w, rfl⟩, -⟩
  exact ⟨w, rfl⟩

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- Going down the dot orbit shrinks the set of weights below. -/
theorem ncard_dotOrbitBelow_lt {μ κ : Dual K H} (hκ : κ ∈ dotOrbitBelow P hA μ) :
    (dotOrbitBelow P hA κ).ncard < (dotOrbitBelow P hA μ).ncard := by
  obtain ⟨⟨x, hx⟩, hκμ, hne⟩ := hκ
  have hsub : dotOrbitBelow P hA κ ⊆ dotOrbitBelow P hA μ := by
    rintro ν ⟨⟨y, rfl⟩, hνκ, -⟩
    refine ⟨⟨y * x, by rw [hx, weylDot_mul]⟩, mem_cone_trans hνκ hκμ, fun h ↦ hne ?_⟩
    rw [h] at hνκ
    exact eq_of_mem_cone_of_mem_cone hκμ hνκ
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr
    ⟨κ, ⟨⟨x, hx⟩, hκμ, hne⟩, fun h ↦ h.2.2 rfl⟩) (finite_dotOrbitBelow hA μ)

omit [IsAlgClosed K] in
theorem mem_dotOrbitBelow_of_multiplicity {lam ν : Dual K H}
    (h : (VermaModule.isCategoryO P lam).multiplicity ν ≠ 0) (hne : ν ≠ lam) :
    ν ∈ dotOrbitBelow P hA lam := by
  have hlink := VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA h
  rw [← weylDot_one P hA.isGeneralizedCartan ν] at hlink
  obtain ⟨x, hx⟩ := IsStronglyLinked.exists_weylDot_eq P hA.isGeneralizedCartan hlink
  refine ⟨⟨x⁻¹, ?_⟩, VermaModule.mem_cone_of_multiplicity_ne_zero h, hne⟩
  rw [hx, ← weylDot_mul, inv_mul_cancel, weylDot_one]

theorem hasDelormeFormula_simple_aux : ∀ (n : ℕ) (lam : Dual K H),
    (dotOrbitBelow P hA lam).ncard < n → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P lam) → HasDelormeFormula hA Z := by
  intro n
  induction n with
  | zero => intro lam h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
  intro lam hlam Z e
  let D := dualVerma P lam
  let ι := simpleToDualVerma (P := P) lam
  let Q := ofQuotient D ι.range
  let φ := toQuotient D ι.range
  have hφ : Function.Surjective φ := surjective_toQuotient D ι.range
  have hker (y : D.obj) : y ∈ φ.ker ↔ ∃ m, ι m = y := by
    rw [LieModuleHom.mem_ker, toQuotient_eq_zero_iff, LieModuleHom.mem_range]
  -- the kernel of `M(λ)^∨ → Q` is `L(λ)`
  let eK : IrreducibleModule P lam ≃ₗ⁅K,𝔤⁆ φ.ker := LieModuleEquiv.ofBijective
    (ι.codRestrict φ.ker fun m ↦ (hker (ι m)).mpr ⟨m, rfl⟩)
    ⟨fun a b hab ↦ injective_simpleToDualVerma lam (congrArg Subtype.val hab), fun y ↦ by
      obtain ⟨m, hm⟩ := (hker y).mp y.2
      exact ⟨m, Subtype.ext hm⟩⟩
  have hS := shortExact_kerComplex D Q φ hφ
  have hD := D.property.1
  have hQ := Q.property.1
  have hmult (ν : Dual K H) : (VermaModule.isCategoryO P lam).multiplicity ν =
      (IrreducibleModule.isCategoryO P lam).multiplicity ν + hQ.multiplicity ν := by
    rw [← multiplicity_restrictedDual (VermaModule.isCategoryO P lam),
      IsCategoryO.multiplicity_congr (isCategoryO_restrictedDual (VermaModule.isCategoryO P lam))
        hD (ofLieEquiv (P := P) (restrictedDual P (VermaModule P lam))),
      IsCategoryO.multiplicity_eq_add_of_exact (hD.lieSubmodule φ.ker) hD hQ φ.ker.incl φ
        Subtype.val_injective φ.ker.range_incl.symm hφ,
      IsCategoryO.multiplicity_congr (hD.lieSubmodule φ.ker) (IrreducibleModule.isCategoryO P lam)
        eK.symm]
  -- the composition factors `L(ν)` of `Q` have `ν ∈ W·λ`, `ν < λ`
  have hQD : HasDelormeFormula hA Q := by
    refine hasDelormeFormula_of_multiplicity hA Q fun ν hν Z' e' ↦ ?_
    have h := hmult ν
    rw [IrreducibleModule.multiplicity_eq] at h
    have hne : ν ≠ lam := by
      rintro rfl
      rw [VermaModule.multiplicity_self] at h
      simp at h
      omega
    rw [if_neg hne] at h
    have hmem := mem_dotOrbitBelow_of_multiplicity hA
      (by omega : (VermaModule.isCategoryO P lam).multiplicity ν ≠ 0) hne
    exact ih ν (by have := ncard_dotOrbitBelow_lt hA hmem; omega) Z' e'
  exact HasDelormeFormula.of_equiv hA ((ofLieEquiv (P := P) φ.ker).symm.trans
    (eK.symm.trans e.symm)) ((hasDelormeFormula_of_shortExact hA hS
      (multiplicity_kerComplex D Q φ hφ)).2 (hasDelormeFormula_dualVerma hA lam) hQD)

/-- Delorme's formula for every `Z ≅ L(λ)`. -/
theorem hasDelormeFormula_of_equiv_simple (lam : Dual K H) (Z : CategoryO.{u} P)
    (e : Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P lam) : HasDelormeFormula hA Z :=
  hasDelormeFormula_simple_aux hA _ lam (Nat.lt_succ_self _) Z e

/-! ### Delorme's formula -/

theorem hasDelormeFormula (N : CategoryO.{u} P) : HasDelormeFormula hA N :=
  hasDelormeFormula_of_multiplicity hA N fun ν _ Z e ↦ hasDelormeFormula_of_equiv_simple hA ν Z e

/-- **[HumO] Proposition 6.14**, multiplicity form. For `N ∈ 𝒪`, only finitely many Euler
characteristics `χ(Ext•_𝒪(M(μ), N))` are nonzero, and
`[N : L(ν)] = ∑_μ χ(Ext•_𝒪(M(μ), N)) [M(μ) : L(ν)]` for every `ν`. Finite type, algebraically
closed field of characteristic zero (Humphreys works over `ℂ`). -/
theorem multiplicity_eq_sum_eulerChar (N : CategoryO.{u} P) :
    ∃ T : Finset (Dual K H), (∀ μ ∉ T, eulerChar hA μ N = 0) ∧ ∀ ν,
      (N.property.1.multiplicity ν : ℤ) =
        ∑ μ ∈ T, eulerChar hA μ N * ((VermaModule.isCategoryO P μ).multiplicity ν : ℤ) :=
  hasDelormeFormula hA N

/-- **[HumO] Proposition 6.14** (Delorme). For `N ∈ 𝒪`,
`ch N = ∑_μ χ(Ext•_𝒪(M(μ), N)) ch M(μ)`, a finite sum. Finite type, algebraically closed field of
characteristic zero. -/
theorem character_eq_sum_eulerChar (N : CategoryO.{u} P) :
    ∃ T : Finset (Dual K H), (∀ μ ∉ T, eulerChar hA μ N = 0) ∧
      N.property.1.character =
        ∑ μ ∈ T, eulerChar hA μ N • (VermaModule.isCategoryO P μ).character := by
  obtain ⟨T, hT, h⟩ := hasDelormeFormula hA N
  refine ⟨T, hT, ?_⟩
  have hsum : ∑ μ ∈ T, eulerChar hA μ N • (VermaModule.isCategoryO P μ).character =
      sumIrreducibleCharacter P
        (∑ μ ∈ T, eulerChar hA μ N • (VermaModule.isCategoryO P μ).multiplicities) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [map_zsmul, ← (VermaModule.isCategoryO P μ).character_eq_sumIrreducibleCharacter]
  rw [N.property.1.character_eq_sumIrreducibleCharacter, hsum]
  congr 1
  ext ν
  change (N.property.1.multiplicity ν : ℤ) = _
  rw [h ν, delormeSum]
  simp only [CharacterRing.coeffAt, HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun μ _ ↦ rfl

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
