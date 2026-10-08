/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationWall
import LieLean.Algebra.Lie.KacMoody.TranslationSameFacet
import LieLean.Algebra.Lie.KacMoody.TranslationUpperClosureNonintegral

/-!
# Translation from a wall: the head of `T_μ^λ M(w·μ)`

In the setting of
`Matrix.Realization.KacMoodyAlgebra.translation_verma_shortExact_of_isAntidominant` (`μ♮` on the
single wall `H_α`, `w α > 0`), with moreover `w ∈ W_[λ]` and every positive root orthogonal
to `λ + ρ` orthogonal to `μ + ρ`: the only simple quotient of
`T_μ^λ M(w·μ) = pr_{χ_λ}(pr_{χ_μ} M(w·μ) ⊗ L(ν))` linked to `λ` is `L(w·λ)`, i.e. its head is
`L(w·λ)` (Humphreys, GSM 94, Theorem 7.14 (b)).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.eq_of_hom_irreducible_ne_zero`: a nonzero
  morphism `M(a) → L(b)` forces `a = b`.
* `Matrix.Realization.upperClosureCondition_of_wall`,
  `Matrix.Realization.not_upperClosureCondition_of_wall`: `w·μ` lies in the upper closure of the
  facet of `w·λ`, and `ws·μ = w·μ` does not lie in that of `ws·λ`.
* `Matrix.Realization.KacMoodyAlgebra.translation_irreducible_wall`: `T_λ^μ L(x·λ)` is
  `L(w·μ)` if `x·λ = w·λ`, and otherwise `0` or a simple module `L(y)`, `y ≠ w·μ`.
* `Matrix.Realization.KacMoodyAlgebra.exists_hom_translation_verma_ne_zero_iff`: for `x ∈ W`,
  there is a nonzero morphism `T_μ^λ M(w·μ) → L(x·λ)` iff `x·λ = w·λ` (Theorem 7.14 (b)).
* `Matrix.Realization.KacMoodyAlgebra.exists_hom_translation_irreducible_ne_zero_iff`,
  `Matrix.Realization.KacMoodyAlgebra.exists_hom_irreducible_translation_ne_zero_iff`: the head
  and the socle of `T_μ^λ L(w·μ)` are `L(w·λ)` (Theorem 7.14 (c); self-duality of
  `T_μ^λ L(w·μ)` is not formalized).

## Proof

As in Humphreys: by adjunction, `Hom(T_μ^λ M(w·μ), L(x·λ)) ≅ Hom(M(w·μ), T_λ^μ L(x·λ))` with
`T_λ^μ` the translation by `L(ν)^* ≅ L(ν')`. By Theorem 7.9 / Proposition 7.7,
`T_λ^μ L(x·λ)` is `0` or `L(x·μ)`, and a nonzero morphism `M(w·μ) → L(x·μ)` forces
`x·μ = w·μ`, i.e. `x ∈ {w, ws}`; the upper closure condition holds for `w` and fails for `ws`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.14.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization

section Combinatorics

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  {P : Realization A K H} (hA : A.IsFiniteCartan)

include hA in
/-- With `±α` (`α = v αᵢ`) the only roots orthogonal to `b`, `⟨a, α^∨⟩ = n < 0` and `w α > 0`:
every positive root `β` with `⟨w b, β^∨⟩ = 0` has `⟨w a, β^∨⟩ ∈ -ℕ`. -/
theorem upperClosureCondition_of_wall {a b : Dual K H}
    {v w : P.weylGroup hA.isGeneralizedCartan} {i : ι}
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan b v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    {n : ℤ} (hn : n < 0) (ha : P.corootPairing hA.isGeneralizedCartan a v i = n)
    (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i) :
    P.UpperClosureCondition hA.isGeneralizedCartan (w.val a) (w.val b) := by
  intro u hu j hpos hb0
  set u' : P.weylGroup hA.isGeneralizedCartan := ⟨u, hu⟩
  have hpos' : P.IsPosRoot hA.isGeneralizedCartan u' j := isPosRoot_iff_mem_posWeights.mpr hpos
  have hb0' : P.corootPairing hA.isGeneralizedCartan b (w⁻¹ * u') j = 0 := by
    rw [← corootPairing_apply]
    exact hb0
  have hroot : (u' : Dual K H ≃ₗ[K] Dual K H) (P.root j) =
      ((w * v : P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) (P.root i) := by
    rcases hwall _ _ hb0' with h | h
    · have := congrArg (w : Dual K H ≃ₗ[K] Dual K H) h
      rwa [Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply] at this
    · exfalso
      have h' : ((w * v * (P.coxeterSystem hA.isGeneralizedCartan).simple i :
          P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) (P.root i) =
          (u' : Dual K H ≃ₗ[K] Dual K H) (P.root j) := by
        rw [mul_simple_apply_root]
        have := congrArg (w : Dual K H ≃ₗ[K] Dual K H) h
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply, map_neg] at this
        rw [this, Subgroup.coe_mul, LinearEquiv.mul_apply]
      obtain ⟨k, hk, hk'⟩ := hpos'
      exact not_isPosRoot_and hw ⟨k, hk, h'.trans hk'⟩
  have hc : P.corootPairing hA.isGeneralizedCartan (w.val a) u' j = n := by
    rw [corootPairing_eq_of_apply_root_eq hA hroot]
    rw [corootPairing_apply, inv_mul_cancel_left, ha]
  refine ⟨(-n).toNat, ?_⟩
  change P.corootPairing _ (w.val a) u' j = _
  rw [hc]
  have : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  have : (((-n).toNat : ℕ) : K) = ((-n : ℤ) : K) := by exact_mod_cast this
  rw [this]
  push_cast
  ring

omit [FiniteDimensional K H] in
include hA in
/-- With `⟨b, α^∨⟩ = 0`, `⟨a, α^∨⟩ = n < 0` (`α = v αᵢ`) and `w α > 0`, the root `β = w α > 0`
has `⟨ws b, β^∨⟩ = 0` but `⟨ws a, β^∨⟩ = -n > 0`, `s = s_α`. -/
theorem not_upperClosureCondition_of_wall {a b : Dual K H}
    {v w : P.weylGroup hA.isGeneralizedCartan} {i : ι}
    (hb : P.corootPairing hA.isGeneralizedCartan b v i = 0)
    {n : ℤ} (hn : n < 0) (ha : P.corootPairing hA.isGeneralizedCartan a v i = n)
    (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i) :
    ¬P.UpperClosureCondition hA.isGeneralizedCartan
      ((w * P.reflectionOf hA.isGeneralizedCartan v i).val a)
      ((w * P.reflectionOf hA.isGeneralizedCartan v i).val b) := by
  intro hU
  have hsv : (w * P.reflectionOf hA.isGeneralizedCartan v i)⁻¹ * (w * v) =
      v * (P.coxeterSystem hA.isGeneralizedCartan).simple i := by
    have hs : (⟨P.reflection hA.isGeneralizedCartan i,
          P.reflection_mem_weylGroup hA.isGeneralizedCartan i⟩ :
        P.weylGroup hA.isGeneralizedCartan)⁻¹ =
        (P.coxeterSystem hA.isGeneralizedCartan).simple i := by
      rw [← CoxeterSystem.inv_simple]
      congr 1
    rw [← hs, reflectionOf]
    group
  have hpair : ∀ x : Dual K H, P.corootPairing hA.isGeneralizedCartan
      ((w * P.reflectionOf hA.isGeneralizedCartan v i).val x) (w * v) i =
        -P.corootPairing hA.isGeneralizedCartan x v i := by
    intro x
    rw [corootPairing_apply, hsv, corootPairing_mul_simple]
  obtain ⟨m, hm⟩ := hU _ (w * v).2 i (isPosRoot_iff_mem_posWeights.mp hw)
    (by change P.corootPairing _ _ (w * v) i = 0; rw [hpair, hb, neg_zero])
  change P.corootPairing _ _ (w * v) i = _ at hm
  rw [hpair, ha] at hm
  have : ((-n : ℤ) : K) = ((-(m : ℤ)) : ℤ) := by push_cast; rw [← hm]
  have := Int.cast_injective (α := K) this
  omega

end Combinatorics

namespace KacMoodyAlgebra

open VermaModule

section Hom

/-- Composition with an equivalence detects vanishing. -/
lemma _root_.LieModuleEquiv.comp_eq_zero_iff {R L M N M' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']
    (e : M ≃ₗ⁅R,L⁆ N) (g : M' →ₗ⁅R,L⁆ M) : e.toLieModuleHom.comp g = 0 ↔ g = 0 := by
  constructor
  · intro h
    ext u
    have h1 : e (g u) = 0 := LieModuleHom.congr_fun h u
    simpa using h1
  · rintro rfl
    ext u
    simp

/-- Precomposition with an equivalence detects vanishing. -/
lemma _root_.LieModuleEquiv.comp_toLieModuleHom_eq_zero_iff {R L M N M' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']
    (e : M ≃ₗ⁅R,L⁆ N) (g : N →ₗ⁅R,L⁆ M') : g.comp e.toLieModuleHom = 0 ↔ g = 0 := by
  constructor
  · intro h
    ext u
    have h1 : g (e (e.symm u)) = 0 := LieModuleHom.congr_fun h (e.symm u)
    simpa using h1
  · rintro rfl
    ext u
    simp

/-- An equivalence out of a nontrivial module is a nonzero morphism. -/
lemma _root_.LieModuleEquiv.eq_zero_of_toLieModuleHom_eq_zero {R L M N : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    (e : M ≃ₗ⁅R,L⁆ N) (h : e.toLieModuleHom = 0) (m : M) : m = 0 := by
  have h1 : e m = 0 := LieModuleHom.congr_fun h m
  simpa using h1

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- A nonzero morphism `M(a) → L(b)` forces `a = b`. -/
theorem VermaModule.eq_of_hom_irreducible_ne_zero {a b : Dual K H}
    {g : VermaModule P a →ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P b} (hg : g ≠ 0) :
    a = b := by
  have hv : g (VermaModule.hwv P a) ≠ 0 := fun h ↦ hg ((VermaModule.eq_zero_iff P g).mpr h)
  have hsurj : Function.Surjective g := by
    have := IrreducibleModule.isIrreducible P b
    rcases IsSimpleOrder.eq_bot_or_eq_top g.range with h | h
    · refine absurd (LieModuleHom.ext fun m ↦ ?_) hg
      have hm : g m ∈ g.range := (LieModuleHom.mem_range _ _).mpr ⟨m, rfl⟩
      rw [h] at hm
      exact (LieSubmodule.mem_bot _).mp hm
    · exact (LieModuleHom.range_eq_top g).mp h
  obtain ⟨k, hk, hab⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P b
    (LieSubmodule.Quotient.mk' _) (LieSubmodule.Quotient.surjective_mk' _)
    (map_mem_weightSpaceOfMap P g (VermaModule.hwv_mem_weightSpace P a)) hv
  obtain ⟨l, hl, hba⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P a g hsurj
    (IrreducibleModule.hwv_mem_weightSpace P b) (IrreducibleModule.hwv_ne_zero P b)
  have h1 : P.rootOf k = b - a := by rw [hab]; abel
  have h2 : P.rootOf l = a - b := by rw [hba]; abel
  have hkl : k + l = 0 := P.rootOf_injective (by rw [map_add, h1, h2, map_zero]; abel)
  have hk0 : k = 0 := by
    ext i
    have := congrFun hkl i
    have := hk i
    have := hl i
    simp only [Pi.add_apply, Pi.zero_apply] at *
    omega
  rw [hab, hk0, map_zero, sub_zero]

end Hom

section Head

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- A nonzero morphism `L(a) → L(b)` forces `a = b`. -/
theorem IrreducibleModule.eq_of_hom_ne_zero {a b : Dual K H}
    {g : IrreducibleModule P a →ₗ⁅K,𝔤⁆ IrreducibleModule P b} (hg : g ≠ 0) : a = b := by
  refine VermaModule.eq_of_hom_irreducible_ne_zero P
    (g := g.comp (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P a))) fun h ↦ hg ?_
  ext u
  obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ u
  exact LieModuleHom.congr_fun h m

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- The quotient map `M(a) → L(a)` is nonzero. -/
theorem IrreducibleModule.mk'_ne_zero (a : Dual K H) :
    (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P a) :
      VermaModule P a →ₗ⁅K,𝔤⁆ IrreducibleModule P a) ≠ 0 := fun h ↦
  IrreducibleModule.hwv_ne_zero P a (LieModuleHom.congr_fun h (VermaModule.hwv P a))

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- The identity of `L(a)` is nonzero. -/
theorem IrreducibleModule.id_ne_zero (a : Dual K H) :
    (LieModuleHom.id : IrreducibleModule P a →ₗ⁅K,𝔤⁆ IrreducibleModule P a) ≠ 0 := fun h ↦
  IrreducibleModule.hwv_ne_zero P a (LieModuleHom.congr_fun h (IrreducibleModule.hwv P a))

include hA in
/-- **Translation of simple modules onto the wall** (the case of Humphreys, GSM 94, Theorem 7.9,
used in Theorem 7.14). In the setting of `exists_hom_translation_verma_ne_zero_iff`, let `ν'` be
dominant integral in `W (μ - λ)`, `T = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν'))`, and `x ∈ W`. If
`x·λ = w·λ` then `T L(x·λ) ≅ L(w·μ)`; otherwise `T L(x·λ)` is `0` or `≅ L(y)` with
`y ≠ w·μ`. -/
theorem translation_irreducible_wall {lam μ ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (x : P.weylGroup hA.isGeneralizedCartan) :
    (P.weylDot hA.isGeneralizedCartan x lam = P.weylDot hA.isGeneralizedCartan w lam →
      Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
        centralTranslation P (IrreducibleModule P ν') (centralCharacter P lam)
          (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam)))) ∧
    (P.weylDot hA.isGeneralizedCartan x lam ≠ P.weylDot hA.isGeneralizedCartan w lam →
      Subsingleton (centralTranslation P (IrreducibleModule P ν') (centralCharacter P lam)
          (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam))) ∨
        ∃ y ≠ P.weylDot hA.isGeneralizedCartan w μ, Nonempty (IrreducibleModule P y ≃ₗ⁅K,𝔤⁆
          centralTranslation P (IrreducibleModule P ν') (centralCharacter P lam)
            (centralCharacter P μ)
              (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam)))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  set s := P.reflectionOf hA' v i with hs
  -- `λ - μ` is integral and `⟨λ + ρ, α^∨⟩ ∈ ℤ_{<0}`
  have hint := sub_rho_integral P hA hν' hz' hzν'
  obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hint v i).mpr ⟨0, by rw [Int.cast_zero]; exact hμα⟩
  change P.corootPairing _ (lam + P.rho) v i = n at hn
  have hn0 : n < 0 := lt_of_le_of_ne (hlam v i hv n hn)
    (by rintro rfl; exact hlamα (by simp [hn]))
  have hU : ∀ x' : P.weylGroup hA',
      (P.MemUpperClosure hA' (P.weylDot hA' x' lam) (P.weylDot hA' x' μ) ↔
        P.UpperClosureCondition hA' (x'.val (lam + P.rho)) (x'.val (μ + P.rho))) :=
    fun x' ↦ memUpperClosure_weylDot_iff_of_isAntidominant hA hlam hμ hint hfacet x'
  have hsint : s ∈ P.integralWeylGroup hA' lam := by
    rw [P.integralWeylGroup_eq_of_integral hA' (μ' := lam + P.rho) fun j ↦ ⟨-1, by simp⟩]
    exact (P.reflectionOf_mem_integralWeylGroup_iff _ v i).mpr ⟨n, hn⟩
  refine ⟨fun hxw ↦ ?_, fun hxw ↦ ?_⟩
  · -- `w⁻¹ x` fixes `λ + ρ`, hence `μ + ρ`
    have h1 : (x : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) =
        (w : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) := by
      have := congrArg (· + P.rho) hxw
      simpa [weylDot] using this
    have hfixl : ((w⁻¹ * x : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) =
        lam + P.rho := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h1, ← LinearEquiv.mul_apply,
        ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    have hfixm : ((w⁻¹ * x : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) =
        μ + P.rho := by
      refine (apply_eq_self_iff_mem_closure_reflectionOf hA (μ + P.rho) _).mpr
        (Subgroup.closure_mono ?_ ((apply_eq_self_iff_mem_closure_reflectionOf hA
          (lam + P.rho) _).mp hfixl))
      rintro _ ⟨v', i', h0, rfl⟩
      refine ⟨v', i', ?_, rfl⟩
      rcases isPosRoot_or v' i' with hp | hp
      · exact hfacet v' i' hp h0
      · have := hfacet _ _ hp (by rw [corootPairing_mul_simple, h0, neg_zero])
        rwa [corootPairing_mul_simple, neg_eq_zero] at this
    have hxμ : P.weylDot hA' x μ = P.weylDot hA' w μ := by
      simp only [weylDot]
      congr 1
      rw [← mul_inv_cancel_left w x, Subgroup.coe_mul, LinearEquiv.mul_apply, hfixm]
    have hmem : P.MemUpperClosure hA' (P.weylDot hA' x lam) (P.weylDot hA' x μ) := by
      rw [hxw, hxμ]
      exact (hU w).mpr (upperClosureCondition_of_wall hA hwall hn0 hn hw)
    have he := translation_irreducible_of_memUpperClosure_of_isAntidominant P hA hlam hμ hfacet
      hν' hz' hzν' x hmem
    rwa [hxμ] at he
  · obtain hsub | he :=
      translation_irreducible_of_isAntidominant P hA hlam hμ hfacet hν' hz' hzν' x
    · exact Or.inl hsub
    by_cases hxμ : P.weylDot hA' x μ = P.weylDot hA' w μ
    · -- `w⁻¹ x` fixes `μ`, so `x ∈ {w, ws}`
      have hfix : P.weylDot hA' (w⁻¹ * x) μ = μ := by
        have h1 := congrArg (· + P.rho) hxμ
        simp only [weylDot, sub_add_cancel] at h1 ⊢
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h1, ← LinearEquiv.mul_apply,
          ← Subgroup.coe_mul, inv_mul_cancel]
        simp
      rcases eq_one_or_eq_of_weylDot_eq hA
          (fun v' i' h0 ↦ reflectionOf_eq_of_apply_root_eq hA (hwall v' i' h0)) hfix with h | h
      · exact absurd (by rw [← mul_inv_cancel_left w x, h, mul_one]) hxw
      · have hx : x = w * s := by rw [← mul_inv_cancel_left w x, h]
        subst hx
        exact Or.inl (translation_irreducible_of_not_memUpperClosure_of_isAntidominant P hA hlam
          hμ hfacet hν' hz' hzν' (w * s) (mul_mem hwint hsint)
          (fun hmem ↦ not_upperClosureCondition_of_wall hA hμα hn0 hn hw ((hU _).mp hmem)))
    · exact Or.inr ⟨_, hxμ, he⟩

include hA in
/-- **The head of `T_μ^λ M(w·μ)`** (Humphreys, GSM 94, Theorem 7.14 (b), arbitrary weights).
Let `λ`, `μ` be antidominant with every positive root orthogonal to `λ + ρ` orthogonal to
`μ + ρ`, `ν = z (λ - μ)` (`z ∈ W`) dominant integral, `α = v αᵢ > 0` with `⟨μ + ρ, α^∨⟩ = 0`,
`±α` the only roots orthogonal to `μ + ρ`, `⟨λ + ρ, α^∨⟩ ≠ 0`, and `w ∈ W_[λ]` with `w α > 0`.
Then for `x ∈ W` there is a nonzero morphism
`T_μ^λ M(w·μ) = pr_{χ_λ}(pr_{χ_μ} M(w·μ) ⊗ L(ν)) → L(x·λ)` iff `x·λ = w·λ`. (Every simple
quotient of `T_μ^λ M(w·μ)` lies in the block of `λ`, so its head is `L(w·λ)`.) -/
theorem exists_hom_translation_verma_ne_zero_iff {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (x : P.weylGroup hA.isGeneralizedCartan) :
    (∃ f : centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ)) →ₗ⁅K,𝔤⁆
          IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam), f ≠ 0) ↔
      P.weylDot hA.isGeneralizedCartan x lam = P.weylDot hA.isGeneralizedCartan w lam := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  have key := translation_irreducible_wall P hA hlam hμ hfacet hν' hzz hzν' hv hμα hwall hlamα hw
    hwint x
  have hMχ : centralBlock P (VermaModule P (P.weylDot hA' w μ)) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_verma P _
  have hNχ : centralBlock P (IrreducibleModule P (P.weylDot hA' x lam))
      (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' x.property lam) ▸ centralBlock_irreducible P _
  let adj := translationAdjunction P (VermaModule.isCategoryO P (P.weylDot hA' w μ))
    (IrreducibleModule.isCategoryO P ν) hMχ hNχ
  let E := centralTranslationCoeffEquiv P (IrreducibleModule P (P.weylDot hA' x lam))
    (centralCharacter P lam) (centralCharacter P μ) eν
  constructor
  · rintro ⟨f, hf⟩
    have hg : E.toLieModuleHom.comp (adj f) ≠ 0 := fun h ↦ hf ((LinearEquiv.map_eq_zero_iff adj).mp
      ((LieModuleEquiv.comp_eq_zero_iff E (adj f)).mp h))
    by_contra hxw
    rcases key.2 hxw with hsub | ⟨y, hy, ⟨e⟩⟩
    · exact hg (LieModuleHom.ext fun u ↦ Subsingleton.elim _ _)
    · exact hy (VermaModule.eq_of_hom_irreducible_ne_zero P
        (g := e.symm.toLieModuleHom.comp (E.toLieModuleHom.comp (adj f))) fun h ↦ hg
          ((LieModuleEquiv.comp_eq_zero_iff e.symm _).mp h)).symm
  · intro hxw
    obtain ⟨e⟩ := key.1 hxw
    let g := E.symm.toLieModuleHom.comp (e.toLieModuleHom.comp
      (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P (P.weylDot hA' w μ))))
    refine ⟨adj.symm g, fun h ↦ IrreducibleModule.mk'_ne_zero P (P.weylDot hA' w μ) ?_⟩
    exact (LieModuleEquiv.comp_eq_zero_iff e _).mp ((LieModuleEquiv.comp_eq_zero_iff E.symm _).mp
      ((LinearEquiv.map_eq_zero_iff adj.symm).mp h))

include hA in
/-- **The head of `T_μ^λ L(w·μ)`** (Humphreys, GSM 94, Theorem 7.14 (c), head). Under the
hypotheses of `exists_hom_translation_verma_ne_zero_iff`, for `x ∈ W` there is a nonzero
morphism `T_μ^λ L(w·μ) → L(x·λ)` iff `x·λ = w·λ`. -/
theorem exists_hom_translation_irreducible_ne_zero_iff {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (x : P.weylGroup hA.isGeneralizedCartan) :
    (∃ f : centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ))
          →ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam), f ≠ 0) ↔
      P.weylDot hA.isGeneralizedCartan x lam = P.weylDot hA.isGeneralizedCartan w lam := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  have key := translation_irreducible_wall P hA hlam hμ hfacet hν' hzz hzν' hv hμα hwall hlamα hw
    hwint x
  have hMχ : centralBlock P (IrreducibleModule P (P.weylDot hA' w μ))
      (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_irreducible P _
  have hNχ : centralBlock P (IrreducibleModule P (P.weylDot hA' x lam))
      (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' x.property lam) ▸ centralBlock_irreducible P _
  let adj := translationAdjunction P (IrreducibleModule.isCategoryO P (P.weylDot hA' w μ))
    (IrreducibleModule.isCategoryO P ν) hMχ hNχ
  let E := centralTranslationCoeffEquiv P (IrreducibleModule P (P.weylDot hA' x lam))
    (centralCharacter P lam) (centralCharacter P μ) eν
  constructor
  · rintro ⟨f, hf⟩
    have hg : E.toLieModuleHom.comp (adj f) ≠ 0 := fun h ↦ hf ((LinearEquiv.map_eq_zero_iff adj).mp
      ((LieModuleEquiv.comp_eq_zero_iff E (adj f)).mp h))
    by_contra hxw
    rcases key.2 hxw with hsub | ⟨y, hy, ⟨e⟩⟩
    · exact hg (LieModuleHom.ext fun u ↦ Subsingleton.elim _ _)
    · exact hy (IrreducibleModule.eq_of_hom_ne_zero P
        (g := e.symm.toLieModuleHom.comp (E.toLieModuleHom.comp (adj f))) fun h ↦ hg
          ((LieModuleEquiv.comp_eq_zero_iff e.symm _).mp h)).symm
  · intro hxw
    obtain ⟨e⟩ := key.1 hxw
    let g := E.symm.toLieModuleHom.comp e.toLieModuleHom
    refine ⟨adj.symm g, fun h ↦ IrreducibleModule.id_ne_zero P (P.weylDot hA' w μ) ?_⟩
    have h0 : E.symm.toLieModuleHom.comp (e.toLieModuleHom.comp LieModuleHom.id) = 0 :=
      (LinearEquiv.map_eq_zero_iff adj.symm).mp h
    exact (LieModuleEquiv.comp_eq_zero_iff e _).mp ((LieModuleEquiv.comp_eq_zero_iff E.symm _).mp
      h0)

set_option maxHeartbeats 400000 in
-- Unifying the translated modules produced by the adjunction and by Theorem 7.9 is expensive.
include hA in
/-- **The socle of `T_μ^λ L(w·μ)`** (Humphreys, GSM 94, Theorem 7.14 (c), socle). Under the
hypotheses of `exists_hom_translation_verma_ne_zero_iff`, for `x ∈ W` there is a nonzero
morphism `L(x·λ) → T_μ^λ L(w·μ)` iff `x·λ = w·λ`. Here `T_μ^λ` is right adjoint to the
translation `T_λ^μ` by `L(ν') ≅ L(ν)^*` (`L(ν) ≅ L(ν')^*`). -/
theorem exists_hom_irreducible_translation_ne_zero_iff {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (x : P.weylGroup hA.isGeneralizedCartan) :
    (∃ f : IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam) →ₗ⁅K,𝔤⁆
        centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
          (centralCharacter P lam) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ)),
          f ≠ 0) ↔
      P.weylDot hA.isGeneralizedCartan x lam = P.weylDot hA.isGeneralizedCartan w lam := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν'
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  have key := translation_irreducible_wall P hA hlam hμ hfacet hν' hzz hzν' hv hμα hwall hlamα hw
    hwint x
  have hMχ : centralBlock P (IrreducibleModule P (P.weylDot hA' x lam))
      (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' x.property lam) ▸ centralBlock_irreducible P _
  have hNχ : centralBlock P (IrreducibleModule P (P.weylDot hA' w μ))
      (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_irreducible P _
  -- `Hom(T' L(x·λ), L(w·μ)) ≅ Hom(L(x·λ), T L(w·μ))`, `T'` by `L(ν')`, `T` by `L(ν')^* ≅ L(ν)`
  let adj := translationAdjunction P (IrreducibleModule.isCategoryO P (P.weylDot hA' x lam))
    (IrreducibleModule.isCategoryO P (z' (-ν))) hMχ hNχ
  let eD : Module.Dual K (IrreducibleModule P (z' (-ν))) ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν :=
    (dualEquiv eν).trans evalEquiv.symm
  let E := centralTranslationCoeffEquiv P (IrreducibleModule P (P.weylDot hA' w μ))
    (centralCharacter P μ) (centralCharacter P lam) eD
  constructor
  · rintro ⟨f, hf⟩
    -- `g : T' L(x·λ) → L(w·μ)` nonzero
    let g := adj.symm (E.symm.toLieModuleHom.comp f)
    have hg : g ≠ 0 := fun h ↦ hf ((LieModuleEquiv.comp_eq_zero_iff E.symm f).mp
      ((LinearEquiv.map_eq_zero_iff adj.symm).mp h))
    by_contra hxw
    rcases key.2 hxw with hsub | ⟨y, hy, ⟨e⟩⟩
    · exact hg (LieModuleHom.ext fun u ↦ by rw [Subsingleton.elim u 0, map_zero]; rfl)
    · exact hy (IrreducibleModule.eq_of_hom_ne_zero P (g := g.comp e.toLieModuleHom) fun h ↦
        hg ((LieModuleEquiv.comp_toLieModuleHom_eq_zero_iff e g).mp h))
  · intro hxw
    obtain ⟨e⟩ := key.1 hxw
    let g : centralTranslation P (IrreducibleModule P (z' (-ν))) (centralCharacter P lam)
        (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA' x lam)) →ₗ⁅K,𝔤⁆
          IrreducibleModule P (P.weylDot hA' w μ) := e.symm.toLieModuleHom
    have hg : g ≠ 0 := fun h ↦ IrreducibleModule.hwv_ne_zero P (P.weylDot hA' w μ)
      ((LinearEquiv.map_eq_zero_iff e.toLinearEquiv).mp
        (LieModuleEquiv.eq_zero_of_toLieModuleHom_eq_zero e.symm h _))
    refine ⟨E.toLieModuleHom.comp (adj g), fun h ↦ hg ?_⟩
    exact (LinearEquiv.map_eq_zero_iff adj).mp ((LieModuleEquiv.comp_eq_zero_iff E _).mp h)

end Head

end KacMoodyAlgebra

end Matrix.Realization
