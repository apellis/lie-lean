/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExtCriterion
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimensions in a regular integral block of `𝒪`

[HumO] Proposition 6.9. Let `Λ` be dominant integral and `m = ℓ(w₀)`. In the block of `𝒪` whose
simple modules are the `L(w·Λ)`, `w ∈ W`:

* `pd M(w·Λ) ≤ ℓ(w)` (`CategoryO.hasProjectiveDimensionLT_verma_weylDot`);
* `pd L(w·Λ) ≤ 2m - ℓ(w)` (`CategoryO.hasProjectiveDimensionLT_simple_weylDot`);
* every object all of whose composition factors are `L(w·Λ)`s has `pd ≤ 2m`, i.e. the global
  dimension of the block is at most `2m` (`CategoryO.hasProjectiveDimensionLT_of_multiplicity`).

Projective dimension is Mathlib's `HasProjectiveDimensionLT X n` (`pd X < n`), defined by the
vanishing of `Extⁱ(X, -)` for `i ≥ n` in the derived category of `𝒪`. Humphreys works with the
principal block `w·0`; as he remarks after the proposition, `0` may be replaced by any dominant
integral weight, which is the generality here.

## Proof

As in Humphreys, with his lemma on projective dimensions in short exact sequences replaced by the
long exact `Ext` sequences.

(a) Induction on `ℓ(w)`. Dimension shifting along `P(w·Λ) → M(w·Λ)`
(`CategoryO.ext_succ_verma_eq_zero`) reduces `Extⁿ⁺¹(M(w·Λ), -) = 0` to `Extⁿ(M(κ), -) = 0` for
the factors `M(κ) ≠ M(w·Λ)` of a standard filtration of `P(w·Λ)`, i.e. for `κ ≠ w·Λ` with
`[M(κ) : L(w·Λ)] ≠ 0`. Such `κ` is in the dot orbit of `Λ` (BGG theorem;
`IsStronglyLinked.exists_weylDot_eq`), `κ = y·Λ` with `y < w`, so `ℓ(y) < ℓ(w)`.

(b) Downward induction on `ℓ(w)`, along `0 → N(w·Λ) → M(w·Λ) → L(w·Λ) → 0`: the composition
factors of `N(w·Λ)` are `L(y·Λ)` with `w < y`, so `ℓ(y) > ℓ(w)`
(`CategoryO.ext_eq_zero_of_multiplicity_left` reduces to them).

(c) `CategoryO.ext_eq_zero_of_multiplicity_left` and (b).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.9.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe w u

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

/-- `Extⁿ⁺¹(X₃, Y) = 0` if `Extⁿ(X₁, Y) = 0 = Extⁿ⁺¹(X₂, Y)` for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`. -/
theorem eq_zero_of_shortExact_left_X₃ {S : ShortComplex C} (hS : S.ShortExact) {Y : C} {n : ℕ}
    (h₁ : ∀ x : Ext.{w} S.X₁ Y n, x = 0) (h₂ : ∀ x : Ext.{w} S.X₂ Y (n + 1), x = 0)
    (x : Ext.{w} S.X₃ Y (n + 1)) : x = 0 := by
  obtain ⟨x₁, rfl⟩ := contravariant_sequence_exact₃ hS Y x (h₂ _) (n₀ := n) (by omega)
  rw [h₁ x₁]
  simp

end CategoryTheory.Abelian.Ext

namespace Matrix.Realization

section Orbit

variable {ι K H : Type*} [Fintype ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- A strong linkage step `λ ↦ μ = s_β · λ` can be reversed in the dot orbit:
`λ = s_β · μ`. -/
theorem StrongLinkStep.exists_weylDot_eq {lam μ : Dual K H} (h : P.StrongLinkStep hA lam μ) :
    ∃ s : P.weylGroup hA, lam = P.weylDot hA s μ := by
  obtain ⟨v, i, n, -, -, hn, rfl⟩ := h
  refine ⟨P.reflectionOf hA v i, ?_⟩
  have hs : P.weylDot hA (P.reflectionOf hA v i) lam =
      lam - n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) := by
    rw [weylDot, reflectionOf_apply', hn, ← Nat.cast_smul_eq_nsmul K]
    abel
  rw [← hs, ← weylDot_mul, reflectionOf_mul_self, weylDot_one]

/-- A weight to which a weight of the dot orbit of `Λ` is strongly linked lies in that orbit. -/
theorem IsStronglyLinked.exists_weylDot_eq {Λ κ : Dual K H} {w : P.weylGroup hA}
    (h : P.IsStronglyLinked hA (P.weylDot hA w Λ) κ) : ∃ x : P.weylGroup hA,
      κ = P.weylDot hA x Λ := by
  unfold IsStronglyLinked at h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨w, rfl⟩
  | head hstep _ ih =>
    obtain ⟨x, rfl⟩ := ih
    obtain ⟨s, hs⟩ := hstep.exists_weylDot_eq P hA
    exact ⟨s * x, by rw [hs, weylDot_mul]⟩

end Orbit

namespace KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### `Ext` along composition factors, first variable -/

/-- `Extⁿ(W, Y) = 0` if `Extⁿ(Z, Y) = 0` for every `Z ≅ L(ν)` with `L(ν)` a composition factor
of `W`: induction on the submodules of `W`, which form an artinian and noetherian lattice. -/
theorem ext_eq_zero_of_multiplicity_left (W Y : CategoryO.{u} P) (n : ℕ)
    (h : ∀ ν, W.property.1.multiplicity ν ≠ 0 → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν) → ∀ x : Abelian.Ext.{u} Z Y n, x = 0)
    (x : Abelian.Ext.{u} W Y n) : x = 0 := by
  obtain ⟨S, hS⟩ := W.property.2
  have := W.property.1.wellFoundedLT_lieSubmodule P (Fact.out : A.IsFiniteCartan) hS
  have := W.property.1.wellFoundedGT_lieSubmodule P (Fact.out : A.IsFiniteCartan) hS
  refine ext_eq_zero_of_ofSub_top W Y (WellFoundedLT.induction
    (motive := fun M ↦ ∀ x : Abelian.Ext.{u} (ofSub W M) Y n, x = 0) ⊤ fun M ih ↦ ?_) x
  by_cases hM : M = ⊥
  · subst hM
    exact Abelian.Ext.eq_zero_of_isZero_left (isZero_ofSub_bot W)
  obtain ⟨M', hM'M, ν, hν, ⟨ψ⟩⟩ := W.property.1.exists_subquotient_equiv_of_ne_bot hM
  have hS := shortExact_subComplex W hM'M.le (ofSubquotient W M' M) (toSubquotient W M' M)
    (fun y hy ↦ (toSubquotient_eq_zero_iff W M' M ⟨y, hM'M.le hy⟩).mpr hy)
    (surjective_toSubquotient W M' M) fun y hy ↦ (toSubquotient_eq_zero_iff W M' M y).mp hy
  exact Abelian.Ext.eq_zero_of_shortExact_left hS (ih M' hM'M)
    (h ν hν _ ((ofLieEquiv (P := P) (M'.Subquotient M)).symm.trans ψ))

/-! ### [HumO] Proposition 6.9 -/

variable (hA : A.IsFiniteCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hΛ

/-- [HumO] Proposition 6.9 (a), in terms of `Ext`: `Extⁿ(M(w·Λ), -) = 0` for `n > ℓ(w)`. -/
theorem ext_verma_weylDot_eq_zero : ∀ (l : ℕ) (w : P.weylGroup hA.isGeneralizedCartan),
    (P.coxeterSystem hA.isGeneralizedCartan).length w = l → ∀ n, l < n → ∀ (Y : CategoryO.{u} P)
      (x : Abelian.Ext.{u} (verma P (P.weylDot hA.isGeneralizedCartan w Λ)) Y n), x = 0 := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro w hw n hn Y x
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ext_succ_verma_eq_zero Y _ n (fun κ hκ hne z ↦ ?_) x
  obtain ⟨y, rfl⟩ := IsStronglyLinked.exists_weylDot_eq P hA.isGeneralizedCartan
    (VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA hκ)
  have hyw := (VermaModule.multiplicity_weylDot_ne_zero_iff_of_isDominantIntegral P hA hΛ).mp hκ
  have hlt := hyw.eq_or_length_lt.resolve_left fun h ↦ hne (by rw [h])
  exact ih _ (by omega) y rfl n (by omega) Y z

/-- **[HumO] Proposition 6.9 (a).** For `Λ` dominant integral and `w ∈ W`,
`pd M(w·Λ) ≤ ℓ(w)`. Finite type, algebraically closed field of characteristic zero (Humphreys
works over `ℂ`, with `Λ = 0`). -/
theorem hasProjectiveDimensionLT_verma_weylDot (w : P.weylGroup hA.isGeneralizedCartan) :
    HasProjectiveDimensionLT (verma.{u} P (P.weylDot hA.isGeneralizedCartan w Λ))
      ((P.coxeterSystem hA.isGeneralizedCartan).length w + 1) :=
  HasProjectiveDimensionLT.mk fun i hi ⦃Y⦄ x ↦
    ext_verma_weylDot_eq_zero hA hΛ _ w rfl i (by omega) Y x

variable [Finite (P.weylGroup hA.isGeneralizedCartan)]

/-- [HumO] Proposition 6.9 (b), in terms of `Ext`: for `Z ≅ L(w·Λ)`, `Extⁿ(Z, -) = 0` for
`n > 2m - ℓ(w)`, where `m = ℓ(w₀)`. -/
theorem ext_simple_weylDot_eq_zero : ∀ (d : ℕ) (w : P.weylGroup hA.isGeneralizedCartan),
    (P.coxeterSystem hA.isGeneralizedCartan).length
        (P.coxeterSystem hA.isGeneralizedCartan).longestElement -
      (P.coxeterSystem hA.isGeneralizedCartan).length w = d → ∀ Z : CategoryO.{u} P,
    (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w Λ)) → ∀ n,
    2 * (P.coxeterSystem hA.isGeneralizedCartan).length
        (P.coxeterSystem hA.isGeneralizedCartan).longestElement -
      (P.coxeterSystem hA.isGeneralizedCartan).length w < n →
    ∀ (Y : CategoryO.{u} P) (x : Abelian.Ext.{u} Z Y n), x = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro w hw Z e n hn Y x
  have hA' := hA.isGeneralizedCartan
  have hwm := (P.coxeterSystem hA').length_le_length_longestElement w
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  let lam := P.weylDot hA' w Λ
  let φ := toSimple P lam Z e
  have hφ : Function.Surjective φ := surjective_toSimple lam Z e
  let N := ofSub (verma P lam) φ.ker
  have hV := (verma P lam).property.1
  -- the composition factors `L(ν)` of `N(w·Λ)` are factors of `M(w·Λ)` with `ν ≠ w·Λ`
  have hmult (ν : Dual K H) : (VermaModule.isCategoryO P lam).multiplicity ν =
      N.property.1.multiplicity ν + (IrreducibleModule.isCategoryO P lam).multiplicity ν := by
    rw [IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P lam) hV
        (ofLieEquiv (P := P) (VermaModule P lam)),
      IsCategoryO.multiplicity_eq_add_of_exact (hV.lieSubmodule φ.ker) hV Z.property.1
        φ.ker.incl φ Subtype.val_injective φ.ker.range_incl.symm hφ,
      IsCategoryO.multiplicity_congr (hV.lieSubmodule φ.ker) N.property.1
        (ofLieEquiv (P := P) φ.ker),
      IsCategoryO.multiplicity_congr Z.property.1 (IrreducibleModule.isCategoryO P lam) e]
  refine Abelian.Ext.eq_zero_of_shortExact_left_X₃
    (shortExact_kerComplex (verma P lam) Z φ hφ) ?_
    (ext_verma_weylDot_eq_zero hA hΛ _ w rfl _ (by omega) Y) x
  refine ext_eq_zero_of_multiplicity_left N Y n fun ν hν Z' e' x' ↦ ?_
  have h := hmult ν
  have hνV : (VermaModule.isCategoryO P lam).multiplicity ν ≠ 0 := by omega
  have hνne : ν ≠ lam := by
    rintro rfl
    rw [VermaModule.multiplicity_self, IrreducibleModule.multiplicity_eq] at h
    simp at h
    omega
  obtain ⟨y, hwy, rfl⟩ := IsStronglyLinked.exists_bruhatLE_weylDot P hA hΛ
    (VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA hνV)
  have hlt := hwy.eq_or_length_lt.resolve_left fun h ↦ hνne (by subst h; rfl)
  have hym := (P.coxeterSystem hA').length_le_length_longestElement y
  exact ih _ (by omega) y rfl Z' e' n (by omega) Y x'

/-- **[HumO] Proposition 6.9 (b).** For `Λ` dominant integral and `w ∈ W`,
`pd L(w·Λ) ≤ 2m - ℓ(w)` with `m = ℓ(w₀)`. Finite type (so that `W` is finite, which the
statement records as an instance), algebraically closed field of characteristic zero (Humphreys
works over `ℂ`, with `Λ = 0`). -/
theorem hasProjectiveDimensionLT_simple_weylDot (w : P.weylGroup hA.isGeneralizedCartan) :
    HasProjectiveDimensionLT (simple.{u} P (P.weylDot hA.isGeneralizedCartan w Λ))
      (2 * (P.coxeterSystem hA.isGeneralizedCartan).length
          (P.coxeterSystem hA.isGeneralizedCartan).longestElement -
        (P.coxeterSystem hA.isGeneralizedCartan).length w + 1) :=
  HasProjectiveDimensionLT.mk fun i hi ⦃Y⦄ x ↦
    ext_simple_weylDot_eq_zero hA hΛ _ w rfl _
      (ofLieEquiv (P := P) (IrreducibleModule P _)).symm i (by omega) Y x

/-- **[HumO] Proposition 6.9**, global dimension. For `Λ` dominant integral, every object `X` of
`𝒪` all of whose composition factors are of the form `L(w·Λ)`, `w ∈ W`, has `pd X ≤ 2m` with
`m = ℓ(w₀)`: the block of `Λ` has global dimension at most `2m`. -/
theorem hasProjectiveDimensionLT_of_multiplicity (X : CategoryO.{u} P)
    (hX : ∀ ν, X.property.1.multiplicity ν ≠ 0 →
      ∃ w : P.weylGroup hA.isGeneralizedCartan, ν = P.weylDot hA.isGeneralizedCartan w Λ) :
    HasProjectiveDimensionLT X
      (2 * (P.coxeterSystem hA.isGeneralizedCartan).length
        (P.coxeterSystem hA.isGeneralizedCartan).longestElement + 1) :=
  HasProjectiveDimensionLT.mk fun i hi ⦃Y⦄ x ↦
    ext_eq_zero_of_multiplicity_left X Y i (fun ν hν Z e ↦ by
      obtain ⟨w, rfl⟩ := hX ν hν
      exact ext_simple_weylDot_eq_zero hA hΛ _ w rfl Z e i (by omega) Y) x

end CategoryO

end KacMoodyAlgebra

end Matrix.Realization
