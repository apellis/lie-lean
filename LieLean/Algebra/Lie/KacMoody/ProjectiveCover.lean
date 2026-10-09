/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Projective
import LieLean.Algebra.Lie.KacMoody.StandardFiltrationSummand

/-!
# Indecomposable projectives in category `𝒪`

For each weight `λ` we construct a projective cover `π_λ : P(λ) → L(λ)` in `𝒪` (Humphreys, GSM 94,
§3.9) as a direct summand of the projective module `M(λ + nρ) ⊗ L(nρ)^*` of Theorem 3.8, cut out
by an idempotent endomorphism `e` with `π ∘ e ≠ 0` which is minimal for the dimension of `e ∘ End`.
The endomorphism algebras involved are finite-dimensional, and Fitting's lemma for left
multiplication shows that `P(λ)` has no proper submodule mapping onto `L(λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.exists_fitting`: Fitting's trichotomy for an
  endomorphism `f` of a Lie module with finite-dimensional endomorphism algebra: `f` is
  surjective, or some iterate of `f` vanishes, or there is an idempotent `a ≠ 0, 1`.
* `Matrix.Realization.KacMoodyAlgebra.finiteDimensional_hom_projectiveCoverAmbient`: morphisms
  from `M(λ + nρ) ⊗ L(nρ)^*` to a module in `𝒪` form a finite-dimensional space.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.8, §3.9.
-/

noncomputable section

open Module LieModule TensorProduct

universe w

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Fitting

variable {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

/-- Left composition with `f`, as a linear endomorphism of the endomorphism space. -/
def compLeftₗ (f : V →ₗ⁅K,L⁆ V) : (V →ₗ⁅K,L⁆ V) →ₗ[K] (V →ₗ⁅K,L⁆ V) where
  toFun g := f.comp g
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

@[simp] lemma compLeftₗ_apply (f g : V →ₗ⁅K,L⁆ V) : compLeftₗ f g = f.comp g := rfl

lemma compLeftₗ_pow_apply (f g : V →ₗ⁅K,L⁆ V) (m : ℕ) (v : V) :
    ((compLeftₗ f ^ m) g) v = (⇑f)^[m] (g v) := by
  induction m generalizing g with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, compLeftₗ_apply, LieModuleHom.comp_apply, ih,
      Function.iterate_succ_apply']

lemma compLeftₗ_pow_comp (f g g' : V →ₗ⁅K,L⁆ V) (m : ℕ) :
    (compLeftₗ f ^ m) (g.comp g') = ((compLeftₗ f ^ m) g).comp g' := by
  ext v
  rw [compLeftₗ_pow_apply, LieModuleHom.comp_apply, LieModuleHom.comp_apply, compLeftₗ_pow_apply]

/-- **Fitting's trichotomy.** Let `V` be a Lie module whose endomorphism space is
finite-dimensional, and `f` an endomorphism. Then `f` is surjective, or some iterate of `f`
vanishes, or there is an idempotent endomorphism `a` with `a ≠ 0`, `a ≠ 1`. (Fitting
decomposition of left multiplication by `f`; the two components of `1` are idempotents.) -/
theorem exists_fitting [FiniteDimensional K (V →ₗ⁅K,L⁆ V)] (f : V →ₗ⁅K,L⁆ V) :
    Function.Surjective f ∨ (∃ m : ℕ, ∀ v, (⇑f)^[m] v = 0) ∨
      ∃ a : V →ₗ⁅K,L⁆ V, a.comp a = a ∧ a ≠ 0 ∧ a ≠ LieModuleHom.id := by
  set F := compLeftₗ f
  obtain ⟨n, hn⟩ := (LinearMap.eventually_isCompl_ker_pow_range_pow F).exists_forall_of_atTop
  set m := max n 1
  have hc := hn m (le_max_left _ _)
  have hm1 : 1 ≤ m := le_max_right _ _
  have hid : (LieModuleHom.id : V →ₗ⁅K,L⁆ V) ∈ LinearMap.ker (F ^ m) ⊔ LinearMap.range (F ^ m) :=
    by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hid
  -- the kernel and range are right ideals
  have hker (x y : V →ₗ⁅K,L⁆ V) (hx : x ∈ LinearMap.ker (F ^ m)) :
      x.comp y ∈ LinearMap.ker (F ^ m) := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [compLeftₗ_pow_comp, hx]; rfl
  have hrange (x y : V →ₗ⁅K,L⁆ V) (hx : x ∈ LinearMap.range (F ^ m)) :
      x.comp y ∈ LinearMap.range (F ^ m) := by
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c.comp y, compLeftₗ_pow_comp f c y m⟩
  -- `a` is idempotent
  have haa : a.comp a = a := by
    have h1 : a.comp a + b.comp a = a := by
      ext v
      have := LieModuleHom.congr_fun hab (a v)
      simpa using this
    have h2 : a.comp a - a = -(b.comp a) := by
      rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, h1, sub_self]
    have hmem1 : a.comp a - a ∈ LinearMap.ker (F ^ m) := Submodule.sub_mem _ (hker a a ha) ha
    have hmem2 : a.comp a - a ∈ LinearMap.range (F ^ m) := by
      rw [h2]; exact Submodule.neg_mem _ (hrange b a hb)
    have := hc.disjoint.eq_bot ▸ Submodule.mem_inf.mpr ⟨hmem1, hmem2⟩
    exact sub_eq_zero.mp ((Submodule.mem_bot K).mp this)
  by_cases ha0 : a = 0
  · -- `1 = f^m c`, so `f` is surjective
    left
    subst ha0
    rw [zero_add] at hab
    subst hab
    obtain ⟨c, hc'⟩ := hb
    intro v
    refine ⟨(⇑f)^[m - 1] (c v), ?_⟩
    have := congrArg (fun g : V →ₗ⁅K,L⁆ V ↦ g v) hc'
    change ((compLeftₗ f ^ m) c) v = v at this
    rw [compLeftₗ_pow_apply] at this
    rw [← Function.iterate_succ_apply' f, Nat.succ_eq_add_one, Nat.sub_add_cancel hm1]
    exact this
  · by_cases hb0 : b = 0
    · -- `1 ∈ ker (F^m)`: `f^m = 0`
      right; left
      subst hb0
      rw [add_zero] at hab
      subst hab
      refine ⟨m, fun v ↦ ?_⟩
      have := congrArg (fun g : V →ₗ⁅K,L⁆ V ↦ g v) (LinearMap.mem_ker.mp ha)
      change ((compLeftₗ f ^ m) LieModuleHom.id) v = (0 : V →ₗ⁅K,L⁆ V) v at this
      rw [compLeftₗ_pow_apply] at this
      simpa using this
    · right; right
      refine ⟨a, haa, ha0, fun ha1 ↦ hb0 ?_⟩
      rw [ha1] at hab
      exact add_eq_left.mp hab

end Fitting

section Summand

/-! ### Minimal idempotents

Let `Q` be a module with finite-dimensional endomorphism algebra, `ψ : Q → L` a morphism, and `e`
an idempotent with `ψ ∘ e ≠ 0` for which `dim (e ∘ End Q)` is minimal. Then the summand `e(Q)`
has no proper idempotent `c` with `ψ ∘ c ≠ 0`. -/

variable {K 𝔤 Q L : Type*} [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]
  [AddCommGroup Q] [Module K Q] [LieRingModule 𝔤 Q] [LieModule K 𝔤 Q]
  [AddCommGroup L] [Module K L] [LieRingModule 𝔤 L] [LieModule K 𝔤 L]

/-- `dim (e ∘ End)`, the rank of left composition with `e`. -/
def idemRank (e : Q →ₗ⁅K,𝔤⁆ Q) : ℕ :=
  finrank K (LinearMap.range (compLeftₗ e))

variable (e : Q →ₗ⁅K,𝔤⁆ Q)

/-- The retraction `Q → e(Q)`. -/
def rangeRetr : Q →ₗ⁅K,𝔤⁆ e.range :=
  LieModuleHom.codRestrict _ e fun x ↦ (LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩

variable {e}

omit [LieAlgebra K 𝔤] [LieModule K 𝔤 Q] in
lemma incl_rangeRetr (x : Q) : e.range.incl (rangeRetr e x) = e x := rfl

omit [LieAlgebra K 𝔤] [LieModule K 𝔤 Q] in
lemma rangeRetr_incl (he : e.comp e = e) (y : e.range) : rangeRetr e (e.range.incl y) = y := by
  obtain ⟨_, x, rfl⟩ := y
  exact Subtype.ext (LieModuleHom.congr_fun he x)

omit [LieAlgebra K 𝔤] [LieModule K 𝔤 Q] in
lemma apply_incl (he : e.comp e = e) (y : e.range) : e (e.range.incl y) = e.range.incl y := by
  rw [← incl_rangeRetr, rangeRetr_incl he]

omit [LieAlgebra K 𝔤] [LieModule K 𝔤 Q] in
lemma rangeRetr_apply (he : e.comp e = e) (x : Q) : rangeRetr e (e x) = rangeRetr e x := by
  rw [← incl_rangeRetr, rangeRetr_incl he]

omit [LieAlgebra K 𝔤] [LieModule K 𝔤 Q] in
lemma rangeRetr_comp_incl (he : e.comp e = e) :
    (rangeRetr e).comp e.range.incl = LieModuleHom.id :=
  LieModuleHom.ext (rangeRetr_incl he)

omit [LieAlgebra K 𝔤] [LieModule K 𝔤 Q] in
lemma surjective_rangeRetr (he : e.comp e = e) : Function.Surjective (rangeRetr e) :=
  fun y ↦ ⟨_, rangeRetr_incl he y⟩

/-- A proper idempotent `a` of `End(e(Q))` gives the idempotent `ι a r` of `Q` with a smaller
`dim (e ∘ End)`. -/
theorem idemRank_lt [FiniteDimensional K (Q →ₗ⁅K,𝔤⁆ Q)] (he : e.comp e = e)
    {a : e.range →ₗ⁅K,𝔤⁆ e.range} (ha : a.comp a = a) (ha1 : a ≠ LieModuleHom.id) :
    idemRank (e.range.incl.comp (a.comp (rangeRetr e))) < idemRank e := by
  let e' := e.range.incl.comp (a.comp (rangeRetr e))
  have he₀e' : e.comp e' = e' := by
    ext x
    exact apply_incl he _
  have he'e₀ : e'.comp e = e' := by
    ext x
    change e.range.incl (a (rangeRetr e (e x))) = e.range.incl (a (rangeRetr e x))
    rw [rangeRetr_apply he]
  have he'e' : e'.comp e' = e' := by
    ext x
    change e.range.incl (a (rangeRetr e (e.range.incl (a (rangeRetr e x))))) =
      e.range.incl (a (rangeRetr e x))
    rw [rangeRetr_incl he, ← LieModuleHom.comp_apply a a, ha]
  have hle : LinearMap.range (compLeftₗ e') ≤ LinearMap.range (compLeftₗ e) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨e'.comp g, ?_⟩
    ext x
    exact apply_incl he _
  have hne : e ∉ LinearMap.range (compLeftₗ e') := by
    rintro ⟨g, hg⟩
    simp only [compLeftₗ_apply] at hg
    have h1 : e' = e := by
      rw [← he'e₀, ← hg]
      ext x
      exact LieModuleHom.congr_fun he'e' (g x)
    apply ha1
    ext y
    have := LieModuleHom.congr_fun h1 (e.range.incl y)
    change e.range.incl (a (rangeRetr e (e.range.incl y))) = e (e.range.incl y) at this
    rw [rangeRetr_incl he, apply_incl he] at this
    exact congrArg Subtype.val (Subtype.ext this)
  have h₀ : e ∈ LinearMap.range (compLeftₗ e) := ⟨e, he⟩
  exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle fun h ↦ hne (h ▸ h₀))

omit [LieModule K 𝔤 L] in
/-- If `dim (e ∘ End)` is minimal among the idempotents `e'` with `ψ ∘ e' ≠ 0`, then no
idempotent `c ≠ 1` of `End(e(Q))` has `ψ ∘ ι ∘ c ≠ 0`. -/
theorem false_of_idempotent [FiniteDimensional K (Q →ₗ⁅K,𝔤⁆ Q)] (he : e.comp e = e)
    {ψ : Q →ₗ⁅K,𝔤⁆ L}
    (hmin : ∀ e' : Q →ₗ⁅K,𝔤⁆ Q, e'.comp e' = e' → ψ.comp e' ≠ 0 → idemRank e ≤ idemRank e')
    {c : e.range →ₗ⁅K,𝔤⁆ e.range} (hc : c.comp c = c) (hc1 : c ≠ LieModuleHom.id)
    (hπc : (ψ.comp e.range.incl).comp c ≠ 0) : False := by
  refine absurd (hmin _ ?_ ?_) (not_le.mpr (idemRank_lt he hc hc1))
  · ext x
    change e.range.incl (c (rangeRetr e (e.range.incl (c (rangeRetr e x))))) =
      e.range.incl (c (rangeRetr e x))
    rw [rangeRetr_incl he, ← LieModuleHom.comp_apply c c, hc]
  · intro h0
    apply hπc
    ext y
    have := LieModuleHom.congr_fun h0 (e.range.incl y)
    change ψ (e.range.incl (c (rangeRetr e (e.range.incl y)))) = 0 at this
    rw [rangeRetr_incl he] at this
    exact this

omit [LieModule K 𝔤 L] in
/-- **Essentiality of a minimal summand.** Under the minimality hypothesis, if `e(Q)` is
projective relative to `ψ ∘ ι : e(Q) → L` with `L` having no submodules other than `0` and `L`,
then every submodule `N` of `e(Q)` not killed by `ψ ∘ ι` is all of `e(Q)`. -/
theorem eq_top_of_minimal [FiniteDimensional K (Q →ₗ⁅K,𝔤⁆ Q)]
    [FiniteDimensional K (e.range →ₗ⁅K,𝔤⁆ e.range)] (he : e.comp e = e) {ψ : Q →ₗ⁅K,𝔤⁆ L}
    (hmin : ∀ e' : Q →ₗ⁅K,𝔤⁆ Q, e'.comp e' = e' → ψ.comp e' ≠ 0 → idemRank e ≤ idemRank e')
    (hψ : ψ.comp e.range.incl ≠ 0) (N : LieSubmodule K 𝔤 e.range)
    (hlift : ∀ φ : e.range →ₗ⁅K,𝔤⁆ L, ∃ g : e.range →ₗ⁅K,𝔤⁆ N,
      ((ψ.comp e.range.incl).comp N.incl).comp g = φ) : N = ⊤ := by
  let π := ψ.comp e.range.incl
  obtain ⟨g, hg⟩ := hlift π
  let f := N.incl.comp g
  have hπf : π.comp f = π := by
    ext y
    exact LieModuleHom.congr_fun hg y
  rcases exists_fitting f with hsurj | ⟨m, hm⟩ | ⟨a, haa, ha0, ha1⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact (g x).2
  · exfalso
    apply hψ
    ext y
    have key : ∀ k, π ((⇑f)^[k] y) = π y := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', ← LieModuleHom.comp_apply π f, hπf, ih]
    have := key m
    rw [hm, map_zero] at this
    exact this.symm
  · exfalso
    by_cases hπa : π.comp a = 0
    · refine false_of_idempotent he hmin (c := LieModuleHom.id - a) ?_ ?_ ?_
      · ext y
        have := LieModuleHom.congr_fun haa y
        simp only [LieModuleHom.comp_apply] at this
        simp [this]
      · intro h
        apply ha0
        ext y
        have := LieModuleHom.congr_fun h y
        simpa using this
      · intro h
        apply hψ
        ext y
        have h2 : ψ (e.range.incl (a y)) = 0 := LieModuleHom.congr_fun hπa y
        have h1 : ψ (e.range.incl y) - ψ (e.range.incl (a y)) = 0 := by
          simpa using LieModuleHom.congr_fun h y
        rw [h2, sub_zero] at h1
        simpa using h1
    · exact false_of_idempotent he hmin haa ha1 hπa

end Summand

section Construction

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
omit [IsAlgClosed K] in
/-- Morphisms from `M(λ + nρ) ⊗ L(nρ)^*` to a module in `𝒪` form a finite-dimensional space:
`Hom(M(μ) ⊗ L', X) ≅ Hom(M(μ), X ⊗ L'^*)` is the space of primitive vectors of weight `μ` of
`X ⊗ L'^*`. -/
theorem finiteDimensional_hom_projectiveCoverAmbient (Λ : Dual K H) (n : ℕ) {X : Type*}
    [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
    [LieModule K P.KacMoodyAlgebra X] (hX : IsCategoryO P X) :
    FiniteDimensional K (projectiveCoverAmbient P Λ n →ₗ⁅K,𝔤⁆ X) := by
  have := IrreducibleModule.finiteDimensional (P := P) hA (isDominantIntegral_nsmul_rho P n)
  have hL : IsCategoryO P (Module.Dual K (Module.Dual K
      (IrreducibleModule P ((n : K) • P.rho)))) :=
    IsCategoryO.of_equiv (IrreducibleModule.isCategoryO P _) LieModule.evalEquiv
  have hT := hX.tensorProduct hL
  have := hT.finiteDimensional_weightSpaceOfMap (Λ + (n : K) • P.rho)
  have : FiniteDimensional K (primitiveVectors P (X ⊗[K] Module.Dual K (Module.Dual K
      (IrreducibleModule P ((n : K) • P.rho)))) (Λ + (n : K) • P.rho)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  exact LinearEquiv.finiteDimensional ((tensorHomAdjunction P).trans (homEquiv P _ _)).symm

/-- The integer `n` with `λ + nρ` maximal in its dot orbit used to construct `P(λ)`. -/
def projectiveCoverShift (Λ : Dual K H) : ℕ := (exists_forall_add_nsmul_rho P hA Λ).choose

/-- The ambient projective module `M(λ + nρ) ⊗ L(nρ)^*` of `P(λ)`. -/
abbrev projectiveCoverAmbient' (Λ : Dual K H) : Type _ :=
  projectiveCoverAmbient P Λ (projectiveCoverShift P hA Λ)

theorem isProjectiveO_projectiveCoverAmbient' (Λ : Dual K H) :
    IsProjectiveO.{w} P (projectiveCoverAmbient' P hA Λ) := by
  have := IrreducibleModule.finiteDimensional (P := P) hA
    (isDominantIntegral_nsmul_rho P (projectiveCoverShift P hA Λ))
  exact IsProjectiveO.tensorProduct P (VermaModule.isProjectiveO_of_forall P hA
    (exists_forall_add_nsmul_rho P hA Λ).choose_spec)
    (IsCategoryO.of_equiv (IrreducibleModule.isCategoryO P _) LieModule.evalEquiv)

omit [IsAlgClosed K] in
theorem finiteDimensional_end_projectiveCoverAmbient' (Λ : Dual K H) :
    FiniteDimensional K (projectiveCoverAmbient' P hA Λ →ₗ⁅K,𝔤⁆ projectiveCoverAmbient' P hA Λ) :=
  finiteDimensional_hom_projectiveCoverAmbient P hA Λ _
    (isCategoryO_projectiveCoverAmbient P hA Λ _)

/-- The surjection `M(λ + nρ) ⊗ L(nρ)^* → L(λ)`. -/
def projectiveCoverAmbientMap (Λ : Dual K H) :
    projectiveCoverAmbient' P hA Λ →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ :=
  (LieSubmodule.Quotient.mk' _).comp
    (exists_surjective_projectiveCoverAmbient P hA Λ (projectiveCoverShift P hA Λ)).choose

omit [IsAlgClosed K] in
theorem surjective_projectiveCoverAmbientMap (Λ : Dual K H) :
    Function.Surjective (projectiveCoverAmbientMap P hA Λ) :=
  (LieSubmodule.Quotient.surjective_mk' _).comp
    (exists_surjective_projectiveCoverAmbient P hA Λ (projectiveCoverShift P hA Λ)).choose_spec

omit [IsAlgClosed K] in
theorem exists_idemRank (Λ : Dual K H) : ∃ k, ∃ e : projectiveCoverAmbient' P hA Λ →ₗ⁅K,𝔤⁆
    projectiveCoverAmbient' P hA Λ, e.comp e = e ∧ (projectiveCoverAmbientMap P hA Λ).comp e ≠ 0 ∧
      idemRank e = k := by
  refine ⟨_, LieModuleHom.id, rfl, fun h0 ↦ ?_, rfl⟩
  obtain ⟨x, hx⟩ := surjective_projectiveCoverAmbientMap P hA Λ (IrreducibleModule.hwv P Λ)
  apply IrreducibleModule.hwv_ne_zero P Λ
  rw [← hx]
  exact LieModuleHom.congr_fun h0 x

open Classical in
/-- The idempotent cutting out `P(λ)`: among the idempotents `e` of `M(λ + nρ) ⊗ L(nρ)^*` with
`π ∘ e ≠ 0`, one for which `dim (e ∘ End)` is minimal. -/
def projectiveCoverIdem (Λ : Dual K H) :
    projectiveCoverAmbient' P hA Λ →ₗ⁅K,𝔤⁆ projectiveCoverAmbient' P hA Λ :=
  (Nat.find_spec (exists_idemRank P hA Λ)).choose

omit [IsAlgClosed K] in
theorem projectiveCoverIdem_idem (Λ : Dual K H) :
    (projectiveCoverIdem P hA Λ).comp (projectiveCoverIdem P hA Λ) = projectiveCoverIdem P hA Λ :=
  by classical exact (Nat.find_spec (exists_idemRank P hA Λ)).choose_spec.1

omit [IsAlgClosed K] in
theorem projectiveCoverIdem_ne_zero (Λ : Dual K H) :
    (projectiveCoverAmbientMap P hA Λ).comp (projectiveCoverIdem P hA Λ) ≠ 0 :=
  by classical exact (Nat.find_spec (exists_idemRank P hA Λ)).choose_spec.2.1

omit [IsAlgClosed K] in
theorem idemRank_projectiveCoverIdem_le (Λ : Dual K H)
    (e : projectiveCoverAmbient' P hA Λ →ₗ⁅K,𝔤⁆ projectiveCoverAmbient' P hA Λ) (he : e.comp e = e)
    (hψ : (projectiveCoverAmbientMap P hA Λ).comp e ≠ 0) :
    idemRank (projectiveCoverIdem P hA Λ) ≤ idemRank e := by
  classical
  rw [show idemRank (projectiveCoverIdem P hA Λ) = Nat.find (exists_idemRank P hA Λ) from
    (Nat.find_spec (exists_idemRank P hA Λ)).choose_spec.2.2]
  exact Nat.find_min' _ ⟨e, he, hψ, rfl⟩

/-- **The indecomposable projective `P(λ)`** (Humphreys, GSM 94, §3.9): the direct summand of
`M(λ + nρ) ⊗ L(nρ)^*` cut out by `projectiveCoverIdem`. It is a projective cover of `L(λ)`
(`ProjectiveCover.eq_top_of_not_le_ker`). -/
abbrev ProjectiveCover (Λ : Dual K H) : Type _ := (projectiveCoverIdem P hA Λ).range

namespace ProjectiveCover

variable (Λ : Dual K H)

omit [IsAlgClosed K] in
theorem isCategoryO : IsCategoryO P (ProjectiveCover P hA Λ) :=
  (isCategoryO_projectiveCoverAmbient P hA Λ _).lieSubmodule _

theorem isProjectiveO : IsProjectiveO.{w} P (ProjectiveCover P hA Λ) :=
  (isProjectiveO_projectiveCoverAmbient' P hA Λ).of_retract (projectiveCoverIdem P hA Λ).range.incl
    (rangeRetr _) (rangeRetr_comp_incl (projectiveCoverIdem_idem P hA Λ))

/-- The surjection `π_λ : P(λ) → L(λ)`. -/
def π : ProjectiveCover P hA Λ →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ :=
  (projectiveCoverAmbientMap P hA Λ).comp (projectiveCoverIdem P hA Λ).range.incl

omit [IsAlgClosed K] in
theorem π_ne_zero : π P hA Λ ≠ 0 := fun h0 ↦ projectiveCoverIdem_ne_zero P hA Λ (by
  ext x
  have h := LieModuleHom.congr_fun h0 (rangeRetr _ x)
  change projectiveCoverAmbientMap P hA Λ ((projectiveCoverIdem P hA Λ).range.incl
    (rangeRetr _ x)) = 0 at h
  rw [incl_rangeRetr] at h
  exact h)

omit [IsAlgClosed K] in
theorem surjective_π : Function.Surjective (π P hA Λ) := by
  have := IrreducibleModule.isIrreducible P Λ
  rw [← LieModuleHom.range_eq_top]
  refine (IsSimpleOrder.eq_bot_or_eq_top (π P hA Λ).range).resolve_left fun h0 ↦ π_ne_zero P hA Λ ?_
  ext y
  have : π P hA Λ y ∈ (π P hA Λ).range := (LieModuleHom.mem_range _ _).mpr ⟨y, rfl⟩
  rw [h0, LieSubmodule.mem_bot] at this
  exact this

omit [IsAlgClosed K] in
theorem finiteDimensional_hom {X : Type*} [AddCommGroup X] [Module K X]
    [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X] (hX : IsCategoryO P X) :
    FiniteDimensional K (ProjectiveCover P hA Λ →ₗ⁅K,𝔤⁆ X) := by
  have := finiteDimensional_hom_projectiveCoverAmbient P hA Λ (projectiveCoverShift P hA Λ) hX
  let φ : (ProjectiveCover P hA Λ →ₗ⁅K,𝔤⁆ X) →ₗ[K] (projectiveCoverAmbient' P hA Λ →ₗ⁅K,𝔤⁆ X) :=
    { toFun f := f.comp (rangeRetr _)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine Module.Finite.of_injective φ fun f g hfg ↦ ?_
  ext y
  obtain ⟨x, rfl⟩ := surjective_rangeRetr (projectiveCoverIdem_idem P hA Λ) y
  exact LieModuleHom.congr_fun hfg x

/-- **`P(λ)` is a projective cover of `L(λ)`** (Humphreys, GSM 94, §3.9): no proper submodule of
`P(λ)` maps onto `L(λ)`, i.e. every submodule not contained in `ker π_λ` is all of `P(λ)`. -/
theorem eq_top_of_not_le_ker (N : LieSubmodule K 𝔤 (ProjectiveCover P hA Λ))
    (hN : ¬ N ≤ (π P hA Λ).ker) : N = ⊤ := by
  have hO := isCategoryO P hA Λ
  have := finiteDimensional_hom P hA Λ hO
  have := finiteDimensional_end_projectiveCoverAmbient' P hA Λ
  refine eq_top_of_minimal (projectiveCoverIdem_idem P hA Λ)
    (fun e' he' hψ ↦ idemRank_projectiveCoverIdem_le P hA Λ e' he' hψ) (π_ne_zero P hA Λ) N
    fun φ ↦ ?_
  have hπN : Function.Surjective ((π P hA Λ).comp N.incl) := by
    have := IrreducibleModule.isIrreducible P Λ
    rw [← LieModuleHom.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top ((π P hA Λ).comp N.incl).range).resolve_left
      fun h0 ↦ hN fun y hy ↦ ?_
    have : ((π P hA Λ).comp N.incl) ⟨y, hy⟩ ∈ ((π P hA Λ).comp N.incl).range :=
      (LieModuleHom.mem_range _ _).mpr ⟨_, rfl⟩
    rw [h0, LieSubmodule.mem_bot] at this
    exact this
  exact isProjectiveO P hA Λ (hO.lieSubmodule N) (IrreducibleModule.isCategoryO P Λ)
    ((π P hA Λ).comp N.incl) hπN φ

end ProjectiveCover

end Construction

end Matrix.Realization.KacMoodyAlgebra
