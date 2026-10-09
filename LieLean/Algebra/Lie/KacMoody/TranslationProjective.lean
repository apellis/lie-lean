/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGGReciprocity
import LieLean.Algebra.Lie.KacMoody.TranslationUpperClosureNonintegral
import LieLean.Algebra.Lie.KacMoody.TranslationFacetClosureNonintegral
import LieLean.Algebra.Lie.KacMoody.TranslationSameFacet

/-!
# Translation of projectives

Humphreys, GSM 94, Proposition 7.13: for antidominant `λ`, `μ` with `μ♮` in the closure of the
facet of `λ♮`, translating a projective Verma module `M(w·μ)` (`w ∈ W_[λ]`, `w·μ` maximal in its
dot orbit, e.g. `w = w_λ`) gives an indecomposable projective: `T_μ^λ M(w·μ) ≅ P(x·λ)`, where `x`
is characterized by `x·μ = w·μ` and `x·μ` lying in the upper closure of the facet of `x·λ`
(Humphreys writes `x = w_λ w_μ°`; this identification is not formalized here). Its standard
filtration multiplicities are those of Theorem 7.12.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.exists_surjective_verma`: a nonzero module
  with a standard filtration maps onto a Verma module.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_projectiveCover_of_hom`: a projective module
  in `𝒪` with a standard filtration and a unique simple quotient `L(x)`, occurring once, is
  `≅ P(x)`.
* `Matrix.Realization.KacMoodyAlgebra.isProjectiveO_centralBlock`: central blocks of projectives
  are projective.
* `Matrix.Realization.KacMoodyAlgebra.exists_isStdFiltered_translation_verma`: `T_μ^λ M(w·μ)` has
  a standard filtration.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_projectiveCover_translation_verma`:
  **Proposition 7.13**.

## Proof

Reconstructed: instead of Verma's theorem and BGG reciprocity, `dim Hom(T_μ^λ M(w·μ), L(η))` is
computed by adjunction and Theorem 3.9 (c) as `[T_λ^μ L(η) : L(w·μ)]`, which Theorem 7.9 and the
minimality of the upper closure show to be `1` for one `η = x·λ` and `0` otherwise.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.13.
-/

noncomputable section

open Module LieModule TensorProduct

universe u₁ u₂ w

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] in
/-- A submodule with a nonempty standard filtration maps onto a Verma module (its top factor). -/
theorem IsStdFiltered.exists_surjective_verma {X : Type*} [AddCommGroup X] [Module K X]
    [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X]
    {N : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) (hs : s ≠ 0) :
    ∃ (μ : Dual K H) (q : N →ₗ⁅K,𝔤⁆ VermaModule P μ), Function.Surjective q := by
  cases hN with
  | bot => exact absurd rfl hs
  | @step N₀ _ _ μ _ h01 he =>
    obtain ⟨e⟩ := he
    refine ⟨μ, e.symm.toLieModuleHom.comp (LieModuleHom.codRestrict _
      ((LieSubmodule.Quotient.mk' N₀).comp N.incl) fun y ↦ LieSubmodule.mem_map_of_mem y.2), ?_⟩
    intro m
    obtain ⟨y, hy, hyx⟩ := (LieSubmodule.mem_map _).mp (e m).2
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom, LieModuleEquiv.symm_apply_eq]
    exact Subtype.ext hyx

variable [IsAlgClosed K] [FiniteDimensional K H] (hA : A.IsFiniteCartan)

/-- **Recognizing `P(x)`.** Let `V ∈ 𝒪` be projective with a standard filtration, mapping onto
`L(x)`, such that `L(x)` is its only simple quotient and `Hom(V, L(x))` is one-dimensional.
Then `V ≅ P(x)`. (A complement of `P(x)` in `V` would have a standard filtration, hence a
simple quotient.) -/
theorem nonempty_equiv_projectiveCover_of_hom {V : Type (max u₁ u₂)} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (hVO : IsCategoryO P V) (hproj : IsProjectiveO.{max u₁ u₂} P V) {s : Multiset (Dual K H)}
    (hs : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 V) s) {x : Dual K H}
    (φ : V →ₗ⁅K,𝔤⁆ IrreducibleModule P x) (hφ : Function.Surjective φ)
    (hdim : ∀ f g : V →ₗ⁅K,𝔤⁆ IrreducibleModule P x, f ≠ 0 → ∃ c : K, g = c • f)
    (huniq : ∀ (η : Dual K H) (f : V →ₗ⁅K,𝔤⁆ IrreducibleModule P η), f ≠ 0 → η = x) :
    Nonempty (ProjectiveCover P hA x ≃ₗ⁅K,𝔤⁆ V) := by
  obtain ⟨s', r, hrs⟩ := (ProjectiveCover.isProjectiveCover P x hA).exists_retract
    (ProjectiveCover.isProjectiveO P hA x) hproj hVO φ hφ
  have hrs' (y : ProjectiveCover P hA x) : r (s' y) = y := LieModuleHom.congr_fun hrs y
  let p := s'.comp r
  have hp : p.comp p = p := by
    ext y
    change s' (r (s' (r y))) = s' (r y)
    rw [hrs']
  obtain ⟨t, t', -, ht', -⟩ := exists_isStdFiltered_range_add P hVO hs p hp
  have ht'0 : t' = 0 := by
    by_contra hne
    obtain ⟨μ, q, hq⟩ := ht'.exists_surjective_verma P hne
    let k : V →ₗ⁅K,𝔤⁆ p.ker := LieModuleHom.codRestrict _ (LieModuleHom.id - p) fun y ↦ by
      change p (y - p y) = 0
      rw [map_sub, ← LieModuleHom.comp_apply p p, hp, sub_self]
    let f := (LieSubmodule.Quotient.mk' (maxSubmodule P μ)).comp (q.comp k)
    have hk (y : p.ker) : k y = y := by
      refine Subtype.ext ?_
      change (y : V) - p y = y
      rw [LieModuleHom.mem_ker.mp y.2, sub_zero]
    have hf0 : f ≠ 0 := fun h0 ↦ by
      obtain ⟨y, hy⟩ := hq (hwv P μ)
      apply IrreducibleModule.hwv_ne_zero P μ
      have := LieModuleHom.congr_fun h0 (y : V)
      change LieSubmodule.Quotient.mk' (maxSubmodule P μ) (q (k y)) = 0 at this
      rw [hk, hy] at this
      exact this
    have hfs : f.comp s' = 0 := by
      ext y
      change LieSubmodule.Quotient.mk' (maxSubmodule P μ) (q (k (s' y))) = 0
      have : k (s' y) = 0 := Subtype.ext (by
        change s' y - s' (r (s' y)) = 0
        rw [hrs', sub_self])
      rw [this, map_zero, map_zero]
    have hμ := huniq μ f hf0
    subst hμ
    obtain ⟨c, hc⟩ := hdim f ((ProjectiveCover.π P hA μ).comp r) hf0
    apply (ProjectiveCover.isProjectiveCover P μ hA).π_ne_zero
    ext y
    have := LieModuleHom.congr_fun hc (s' y)
    change ProjectiveCover.π P hA μ (r (s' y)) = c • f (s' y) at this
    rw [hrs', show f (s' y) = 0 from LieModuleHom.congr_fun hfs y, smul_zero] at this
    exact this
  have hker := IsStdFiltered.eq_bot_of_zero P (ht'0 ▸ ht')
  refine ⟨LieModuleEquiv.ofBijective s' ⟨fun a b hab ↦ ?_, fun y ↦ ⟨r y, ?_⟩⟩⟩
  · rw [← hrs' a, ← hrs' b, hab]
  · have hmem : y - s' (r y) ∈ p.ker := by
      change s' (r (y - s' (r y))) = 0
      rw [map_sub, hrs', sub_self, map_zero]
    rw [hker, LieSubmodule.mem_bot, sub_eq_zero] at hmem
    exact hmem.symm

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- Every Verma module is a projective cover of its simple quotient in the sense of
`IsProjectiveCover` (up to projectivity). -/
theorem VermaModule.isProjectiveCover (Λ : Dual K H) :
    IsProjectiveCover P (VermaModule P Λ) (LieSubmodule.Quotient.mk' (maxSubmodule P Λ)) :=
  ⟨VermaModule.isCategoryO P Λ, LieSubmodule.Quotient.surjective_mk' _, fun N hN ↦ by
    rw [LieSubmodule.Quotient.mk'_ker] at hN
    by_contra hne
    exact hN ((le_maxSubmodule_iff P Λ N).mpr hne)⟩

end Generic

section Block

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [IsAlgClosed K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- The retraction `V → pr_χ V` of a module in `𝒪` onto a central block. -/
def blockRetr (hV : IsCategoryO P V) (χ : 𝓩 →ₐ[K] K) :
    V →ₗ⁅K,P.KacMoodyAlgebra⁆ centralBlock P V χ :=
  LieModuleHom.codRestrict _ (hV.centralBlockProjection P χ)
    (centralBlockProjection_mem P (hV.isCentralLocallyFinite P) χ)

omit [CharZero K] in
lemma blockRetr_incl (hV : IsCategoryO P V) (χ : 𝓩 →ₐ[K] K) (y : centralBlock P V χ) :
    blockRetr P hV χ y = y :=
  Subtype.ext (centralBlockProjection_self P (hV.isCentralLocallyFinite P) χ y.2)

omit [CharZero K] in
/-- Central blocks of projectives in `𝒪` are projective (Humphreys, GSM 94, §3.8: direct
summands). -/
theorem isProjectiveO_centralBlock {hV : IsCategoryO P V} (hVp : IsProjectiveO.{w} P V)
    (χ : 𝓩 →ₐ[K] K) : IsProjectiveO.{w} P (centralBlock P V χ) :=
  hVp.of_retract (centralBlock P V χ).incl (blockRetr P hV χ)
    (LieModuleHom.ext (blockRetr_incl P hV χ))

end Block

section Filtration

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

/-- A filtration indexed by `Fin (n + 1)` whose steps are Verma modules for `j ∈ S` and zero for
`j ∉ S` gives `IsStdFiltered`. -/
theorem isStdFiltered_of_fin_of_zero {n : ℕ} (F : Fin (n + 1) → LieSubmodule K P.KacMoodyAlgebra X)
    (wt' : Fin n → Dual K H) (S : Set (Fin n)) [DecidablePred (· ∈ S)] (hF : Monotone F)
    (h0 : F 0 = ⊥)
    (hstep : ∀ j ∈ S, Nonempty (VermaModule P (wt' j) ≃ₗ⁅K,P.KacMoodyAlgebra⁆
      (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc))))
    (hzero : ∀ j ∉ S, (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) = ⊥) :
    IsStdFiltered P (F (Fin.last n)) ((Finset.univ.filter (· ∈ S)).val.map wt') := by
  classical
  have key : ∀ k (hk : k ≤ n), IsStdFiltered P (F ⟨k, Nat.lt_succ_of_le hk⟩)
      ((Finset.univ.filter fun j : Fin n ↦ j ∈ S ∧ j.val < k).val.map wt') := by
    intro k
    induction k with
    | zero =>
      intro _
      have : (Finset.univ.filter fun j : Fin n ↦ j ∈ S ∧ j.val < 0) = ∅ := by
        ext j; simp
      rw [this]
      simpa [h0] using IsStdFiltered.bot (P := P) (X := X)
    | succ k ih =>
      intro hk
      set j : Fin n := ⟨k, hk⟩
      have h1 := ih (Nat.le_of_succ_le hk)
      have hle : F j.castSucc ≤ F j.succ := hF (Fin.mk_le_mk.mpr (Nat.le_succ k))
      by_cases hj : j ∈ S
      · have hfilt : (Finset.univ.filter fun i : Fin n ↦ i ∈ S ∧ i.val < k + 1) =
            Finset.cons j (Finset.univ.filter fun i : Fin n ↦ i ∈ S ∧ i.val < k) (by simp [j]) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons, j]
          constructor
          · rintro ⟨hiS, hi⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
            · exact Or.inr ⟨hiS, hi⟩
            · exact Or.inl (Fin.ext hi)
          · rintro (rfl | ⟨hiS, hi⟩)
            · exact ⟨hj, Nat.lt_succ_self _⟩
            · exact ⟨hiS, Nat.lt_succ_of_lt hi⟩
        rw [hfilt, Finset.cons_val, Multiset.map_cons]
        exact IsStdFiltered.step h1 hle (hstep j hj)
      · have hfilt : (Finset.univ.filter fun i : Fin n ↦ i ∈ S ∧ i.val < k + 1) =
            (Finset.univ.filter fun i : Fin n ↦ i ∈ S ∧ i.val < k) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hiS, hi⟩
            refine ⟨hiS, lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) fun he ↦ hj ?_⟩
            have : i = j := Fin.ext he
            exact this ▸ hiS
          · rintro ⟨hiS, hi⟩
            exact ⟨hiS, Nat.lt_succ_of_lt hi⟩
        have heq : F j.succ = F j.castSucc := by
          refine le_antisymm (fun x hx ↦ ?_) hle
          have := hzero j hj
          have hmem : LieSubmodule.Quotient.mk' (F j.castSucc) x ∈
              (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) :=
            LieSubmodule.mem_map_of_mem hx
          rw [this, LieSubmodule.mem_bot, LieSubmodule.Quotient.mk_eq_zero] at hmem
          exact hmem
        rw [hfilt]
        change IsStdFiltered P (F j.succ) _
        rw [heq]
        exact h1
  have := key n le_rfl
  have hfull : (Finset.univ.filter fun j : Fin n ↦ j ∈ S ∧ j.val < n) =
      Finset.univ.filter (· ∈ S) := by
    ext j; simp
  rwa [hfull] at this

end Filtration

section Translation

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- `T_μ^λ M(w·μ)` has a standard filtration (Humphreys, GSM 94, Theorem 7.12). -/
theorem exists_isStdFiltered_translation_verma {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    ∃ s, IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (centralTranslation P (IrreducibleModule P ν)
      (centralCharacter P μ) (centralCharacter P lam)
      (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ)))) s := by
  classical
  have hA' := hA.isGeneralizedCartan
  set Λw := P.weylDot hA' w μ
  have hMχ : centralBlock P (VermaModule P Λw) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_verma P _
  have hLO := IrreducibleModule.isCategoryO P ν
  have hXO := (VermaModule.isCategoryO P Λw).tensorProduct hLO
  obtain ⟨n, F, x, S, hmono, h0, hlast, hstep, hzero, -⟩ :=
    exists_translation_verma_filtration_of_isAntidominant (P := P) hA hlam hμ hν hz hzν w
  have h1 := isStdFiltered_of_fin_of_zero P F x S hmono h0 hstep hzero
  rw [hlast] at h1
  -- transport to the block as a module
  have h2 := h1.map_of_injOn P (blockRetr P hXO (centralCharacter P lam))
    (B := centralBlock P _ (centralCharacter P lam)) (fun y hy hy0 ↦ by
      have := congrArg Subtype.val hy0
      rwa [show (blockRetr P hXO (centralCharacter P lam) y : _) = y from
        congrArg Subtype.val (blockRetr_incl P hXO _ ⟨y, hy⟩)] at this) le_rfl
  have hmap : (centralBlock P (VermaModule P Λw ⊗[K] IrreducibleModule P ν)
      (centralCharacter P lam)).map (blockRetr P hXO (centralCharacter P lam)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact ⟨y.1, y.2, blockRetr_incl P hXO _ y⟩
  rw [hmap] at h2
  -- transport along `pr_λ(M ⊗ L) ≅ pr_λ(pr_μ M ⊗ L)`
  let e := centralBlockEquiv P (rTensorEquiv P (IrreducibleModule P ν)
    (equivCentralBlockOfEqTop P hMχ).symm) (centralCharacter P lam)
  have h3 := h2.map_of_injOn P e.toLieModuleHom (B := ⊤)
    (fun y _ hy0 ↦ (e.toLinearEquiv.map_eq_zero_iff).mp hy0) le_rfl
  have hmap' : (⊤ : LieSubmodule K 𝔤 (centralBlock P (VermaModule P Λw ⊗[K]
      IrreducibleModule P ν) (centralCharacter P lam))).map e.toLieModuleHom = ⊤ := by
    rw [LieModuleHom.map_top, LieModuleHom.range_eq_top]
    exact e.surjective
  rw [hmap'] at h3
  exact ⟨_, h3⟩

include hA in
/-- **Humphreys, GSM 94, Proposition 7.13.** Let `λ`, `μ` be antidominant, with every positive root
orthogonal to `λ + ρ` orthogonal to `μ + ρ` (`μ♮` in the closure of the facet of `λ♮`), let
`ν = z (λ - μ)` (`z ∈ W`) be dominant integral and `T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))`. Let
`w ∈ W_[λ]` with `w·μ` maximal in its dot orbit (e.g. `w = w_λ`, the longest element of `W_[λ]`).
Then `T_μ^λ M(w·μ)` is an indecomposable projective: `T_μ^λ M(w·μ) ≅ P(x·λ)` for the `x ∈ W`
with `x·μ = w·μ` and `x·μ` in the upper closure of the facet of `x·λ` (for regular `λ` this is
`x = w_λ w_μ°`); `x·λ` is uniquely determined. The standard filtration multiplicities are those
of Theorem 7.12 (`exists_translation_verma_filtration_of_isAntidominant`).

Proof (reconstructed, via Theorem 7.9 instead of Verma's theorem and BGG reciprocity):
`T_μ^λ M(w·μ)` is projective with a standard filtration, and by adjunction and Theorem 3.9 (c)
`dim Hom(T_μ^λ M(w·μ), L(η)) = [T_λ^μ L(η) : L(w·μ)]`, which by Theorem 7.9 and the minimality of
the upper closure is `1` for `η = x·λ` and `0` otherwise. -/
theorem nonempty_equiv_projectiveCover_translation_verma {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {w : P.weylGroup hA.isGeneralizedCartan}
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (hmax : ∀ w' ∈ P.weylGroup hA.isGeneralizedCartan, ∀ k : ι → ℤ, 0 ≤ k →
      w' (P.weylDot hA.isGeneralizedCartan w μ + P.rho) =
        P.weylDot hA.isGeneralizedCartan w μ + P.rho + P.rootOf k → k = 0) :
    ∃ x : P.weylGroup hA.isGeneralizedCartan,
      P.weylDot hA.isGeneralizedCartan x μ = P.weylDot hA.isGeneralizedCartan w μ ∧
      P.MemUpperClosure hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan x lam)
        (P.weylDot hA.isGeneralizedCartan x μ) ∧
      Nonempty (ProjectiveCover P hA (P.weylDot hA.isGeneralizedCartan x lam) ≃ₗ⁅K,𝔤⁆
        centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
          (centralCharacter P lam) (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  set Λw := P.weylDot hA' w μ with hΛw
  -- the dual of `L(ν)` and the integrality of `λ - μ`
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  have hint := sub_rho_integral P hA hν' hzz hzν'
  have ha : ∀ v i, P.IsPosRoot hA' v i → ∀ n : ℤ, P.corootPairing hA' (lam + P.rho) v i = n →
      n ≤ 0 := hlam
  -- `W_[λ] = W_[λ + ρ] = W_[μ + ρ]`
  have hWl : P.integralWeylGroup hA' lam = P.integralWeylGroup hA' (lam + P.rho) :=
    P.integralWeylGroup_eq_of_integral hA' fun j ↦ ⟨-1, by simp⟩
  have hWm : P.integralWeylGroup hA' (lam + P.rho) = P.integralWeylGroup hA' (μ + P.rho) :=
    P.integralWeylGroup_eq_of_integral hA' hint
  have hwb : w ∈ P.integralWeylGroup hA' (μ + P.rho) := hWm ▸ hWl ▸ hwint
  -- the modules
  have hMχ : centralBlock P (VermaModule P Λw) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_verma P _
  have hLO := IrreducibleModule.isCategoryO P ν
  have hL'O : IsCategoryO P (Module.Dual K (IrreducibleModule P ν)) :=
    IsCategoryO.of_equiv (IrreducibleModule.isCategoryO P _) eν.symm
  have hMO := VermaModule.isCategoryO P Λw
  have hP'O := hMO.centralTranslation P hLO (centralCharacter P μ) (centralCharacter P lam)
  have hMp : IsProjectiveO.{max u₁ u₂} P (VermaModule P Λw) :=
    VermaModule.isProjectiveO_of_forall P hA hmax
  have hP'p : IsProjectiveO.{max u₁ u₂} P (centralTranslation P (IrreducibleModule P ν)
      (centralCharacter P μ) (centralCharacter P lam) (VermaModule P Λw)) :=
    isProjectiveO_centralBlock P (hV := (hMO.centralBlock P _).tensorProduct hLO)
      ((hMp.of_equiv (equivCentralBlockOfEqTop P hMχ).symm).tensorProduct P hL'O) _
  -- multiplicities of the adjoint translation
  let mult : Dual K H → ℕ := fun η ↦ ((IrreducibleModule.isCategoryO P η).centralTranslation P
    (IrreducibleModule.isCategoryO P (z' (-ν))) (centralCharacter P lam)
    (centralCharacter P μ)).multiplicity Λw
  -- `dim Hom(T M(w·μ), L(η)) = [T' L(η) : L(w·μ)]` and the finite-dimensionality
  have hHom : ∀ η, centralBlock P (IrreducibleModule P η) (centralCharacter P lam) = ⊤ →
      FiniteDimensional K (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P Λw) →ₗ⁅K,𝔤⁆ IrreducibleModule P η) ∧
      finrank K (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P Λw) →ₗ⁅K,𝔤⁆ IrreducibleModule P η) = mult η := by
    intro η hNχ
    let adj := translationAdjunction P hMO hLO hMχ hNχ
    let E := centralTranslationCoeffEquiv P (IrreducibleModule P η)
      (centralCharacter P lam) (centralCharacter P μ) eν
    have hT'O := (IrreducibleModule.isCategoryO P η).centralTranslation P hL'O
      (centralCharacter P lam) (centralCharacter P μ)
    have hcov := VermaModule.isProjectiveCover P Λw
    have := hcov.finiteDimensional_hom hT'O
    refine ⟨LinearEquiv.finiteDimensional adj.symm, ?_⟩
    rw [adj.finrank_eq, hcov.finrank_hom_eq_multiplicity hMp hT'O]
    exact IsCategoryO.multiplicity_congr hT'O _ E Λw
  -- maps to simple modules outside the block of `λ` vanish
  have hblock : ∀ η, centralBlock P (IrreducibleModule P η) (centralCharacter P lam) ≠ ⊤ →
      ∀ f : centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P Λw) →ₗ⁅K,𝔤⁆ IrreducibleModule P η, f = 0 := by
    intro η hη f
    have hne : centralCharacter P η ≠ centralCharacter P lam := fun h ↦
      hη (h ▸ centralBlock_irreducible P η)
    have hbot := centralBlock_irreducible_eq_bot P η _ hne
    ext y
    have hy : y ∈ centralBlock P _ (centralCharacter P lam) := by
      rw [centralBlock_centralBlock_eq_top]; trivial
    have := map_mem_centralBlock P f _ hy
    rw [hbot, LieSubmodule.mem_bot] at this
    exact this
  have hmult1 : ∀ w' : P.weylGroup hA',
      P.UpperClosureCondition hA' (w'.val (lam + P.rho)) (w'.val (μ + P.rho)) →
      P.weylDot hA' w' μ = Λw → mult (P.weylDot hA' w' lam) = 1 := by
    intro w' hC hw'μ
    obtain ⟨e⟩ := translation_irreducible_of_upperClosureCondition_of_isAntidominant P hA hlam hμ
      hfacet hν' hzz hzν' w' hC
    exact (IsCategoryO.multiplicity_congr ((IrreducibleModule.isCategoryO P
      (P.weylDot hA' w' lam)).centralTranslation P (IrreducibleModule.isCategoryO P (z' (-ν)))
      (centralCharacter P lam) (centralCharacter P μ)) (IrreducibleModule.isCategoryO P _)
      e.symm Λw).trans (by simp [IrreducibleModule.multiplicity_eq, hw'μ])
  -- (K1) nonzero multiplicity: `η = w'·λ` with `w'·μ = w·μ` and the upper-closure condition
  have hK1 : ∀ η, mult η ≠ 0 → ∃ w' : P.weylGroup hA', η = P.weylDot hA' w' lam ∧
      P.weylDot hA' w' μ = Λw ∧
      P.UpperClosureCondition hA' (w'.val (lam + P.rho)) (w'.val (μ + P.rho)) ∧ mult η = 1 := by
    intro η hη
    obtain ⟨w', rfl, hw'μ, hns⟩ :=
      exists_weylDot_of_multiplicity_translation_ne_zero_of_isAntidominant P hA hlam hμ hfacet hν'
        hzz hzν' hη
    have hw'b : w'.val (μ + P.rho) = w.val (μ + P.rho) := by
      have := congrArg (· + P.rho) hw'μ
      simpa [weylDot, hΛw] using this
    have hw'int : w' ∈ P.integralWeylGroup hA' lam := by
      rw [hWl, hWm, mem_integralWeylGroup, hw'b]
      exact hwb
    have hC : P.UpperClosureCondition hA' (w'.val (lam + P.rho)) (w'.val (μ + P.rho)) := by
      by_contra hC
      exact hns (translation_irreducible_of_not_upperClosureCondition_of_isAntidominant P hA hlam
        hμ hfacet hν' hzz hzν' w' hw'int hC)
    exact ⟨w', rfl, hw'μ, hC, hmult1 w' hC hw'μ⟩
  -- (K3) existence
  obtain ⟨x, hxint, hxb, hxC, -⟩ := exists_upperClosureCondition_of_integral (P := P) hA hint ha
    (hWl ▸ hwint)
  rw [← hxb] at hxC
  have hxμ : P.weylDot hA' x μ = Λw := by
    simp only [hΛw, weylDot, hxb]
  have hxmult : mult (P.weylDot hA' x lam) = 1 := hmult1 x hxC hxμ
  -- (K4) uniqueness
  have hK4 : ∀ w' : P.weylGroup hA', P.weylDot hA' w' μ = Λw →
      P.UpperClosureCondition hA' (w'.val (lam + P.rho)) (w'.val (μ + P.rho)) →
      P.weylDot hA' w' lam = P.weylDot hA' x lam := by
    intro w' hw'μ hC
    have hb : w'.val (μ + P.rho) = x.val (μ + P.rho) := by
      have h1 := congrArg (· + P.rho) hw'μ
      have h2 := congrArg (· + P.rho) hxμ
      simp only [weylDot, sub_add_cancel] at h1 h2
      rw [h1, h2]
    obtain ⟨c₁, hc₁, h₁⟩ := exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral
      (P := P) hA hint ha hxC hb
    obtain ⟨c₂, hc₂, h₂⟩ := exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral
      (P := P) hA hint ha hC hb.symm
    have h0 : P.rootOf (c₁ + c₂) = P.rootOf 0 := by
      rw [map_add, ← h₁, ← h₂, map_zero]; abel
    have hc0 : c₁ = 0 := by
      have := P.rootOf_injective h0
      ext j
      have h1 := congrFun this j
      have h2 : (0 : ℤ) ≤ c₁ j := hc₁ j
      have h3 : (0 : ℤ) ≤ c₂ j := hc₂ j
      simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
      omega
    rw [hc0, map_zero, sub_eq_zero] at h₁
    simp only [weylDot, h₁]
  -- the module `T M(w·μ)`
  have hxblock : centralBlock P (IrreducibleModule P (P.weylDot hA' x lam))
      (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' x.property lam) ▸ centralBlock_irreducible P _
  obtain ⟨hfdx, hdimx⟩ := hHom _ hxblock
  rw [hxmult] at hdimx
  obtain ⟨φ, hφ0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (hdimx ▸ Nat.one_pos)
  have hφ : Function.Surjective φ := by
    have := IrreducibleModule.isIrreducible P (P.weylDot hA' x lam)
    rw [← LieModuleHom.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top φ.range).resolve_left fun h0 ↦ hφ0 ?_
    ext y
    have : φ y ∈ φ.range := (LieModuleHom.mem_range _ _).mpr ⟨y, rfl⟩
    rw [h0, LieSubmodule.mem_bot] at this
    exact this
  obtain ⟨s, hs⟩ := exists_isStdFiltered_translation_verma P hA hlam hμ hν hz hzν w
  refine ⟨x, hxμ, (memUpperClosure_weylDot_iff_of_isAntidominant hA hlam hμ hint hfacet x).mpr hxC,
    nonempty_equiv_projectiveCover_of_hom P hA hP'O hP'p hs φ hφ (fun f g hf ↦ ?_)
      (fun η f hf ↦ ?_)⟩
  · obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' f hf).mp hdimx g
    exact ⟨c, hc.symm⟩
  · by_cases hηb : centralBlock P (IrreducibleModule P η) (centralCharacter P lam) = ⊤
    · obtain ⟨hfd, hdim⟩ := hHom η hηb
      have hpos : mult η ≠ 0 := by
        rw [← hdim]
        exact (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨f, hf⟩).ne'
      obtain ⟨w', rfl, hw'μ, hC, -⟩ := hK1 η hpos
      exact hK4 w' hw'μ hC
    · exact absurd (hblock η hηb f) hf

end Translation

end Matrix.Realization.KacMoodyAlgebra
