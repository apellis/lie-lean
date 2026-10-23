/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNaturalEval
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNaturalNilpotent

/-!
# Natural transformations between tensoring functors

A natural transformation `φ : − ⊗ V → − ⊗ W` of functors on `L`-modules (`TensorNatTrans`) is
determined, on modules killed by a two-sided ideal `I` of `U(L)`, by its value at one module
`M₀` whose annihilator is `I` (`TensorNatTrans.app_eq_of_app_eq`).

Summands `F = e(− ⊗ V)`, `G = e'(− ⊗ W)` of tensoring functors are given by natural idempotents
`e`, `e'`. Morphisms `φ : F → G`, `φ' : G → F` that are mutually inverse at `M₀` are mutually
inverse at every module `M` with a finite filtration whose subquotients are killed by `I`
(`TensorNatTrans.exists_inverse_of_hasKilledFiltration`): the defect `φ' φ - e` vanishes on
modules killed by `I`, hence is nilpotent on `M`. This is the argument of Humphreys' proof of
Theorem 10.7 (b), with `M₀ = M(λ)` for `λ` dominant.

## Main definitions

* `UniversalEnvelopingAlgebra.TensorNatTrans`: natural transformations `− ⊗ V → − ⊗ W`;
  `TensorNatTrans.ofTensorNatMap`, the one attached to `g : V → U^{ad} ⊗ W`.
* `UniversalEnvelopingAlgebra.IsKilledByPow I n M`: products of `n` elements of `I` kill `M`.

## Main results

* `UniversalEnvelopingAlgebra.hasKilledFiltration_of_isKilledByPow`: such an `M` has the
  filtration `M ⊇ I M ⊇ ⋯ ⊇ Iⁿ M = 0`.
* `UniversalEnvelopingAlgebra.TensorNatTrans.app_eq_of_app_eq`.
* `exists_mul_eq_of_isNilpotent_sub`: a nilpotent perturbation of an idempotent `e` in the
  corner `eAe` is invertible there.
* `UniversalEnvelopingAlgebra.TensorNatTrans.exists_inverse_of_hasKilledFiltration`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct

/-- If `e` is idempotent, `a = e a e` and `a - e` is nilpotent, then `a` is invertible in the
corner ring `e A e`: some `b` satisfies `b a = e = a b`. -/
theorem exists_mul_eq_of_isNilpotent_sub {A : Type*} [Ring A] {e a : A} (he : e * e = e)
    (ha : e * a * e = a) (hn : IsNilpotent (a - e)) : ∃ b : A, b * a = e ∧ a * b = e := by
  have hea : e * a = a := by rw [← ha, ← mul_assoc, ← mul_assoc, he]
  have hae : a * e = a := by rw [← ha, mul_assoc, he]
  obtain ⟨u, hu⟩ := hn.isUnit_one_add
  have hue : (u : A) * e = a := by rw [hu, add_mul, one_mul, sub_mul, hae, he, add_sub_cancel]
  have hc : Commute e (u : A) := by
    rw [hu]
    refine (Commute.one_right e).add_right ?_
    change e * (a - e) = (a - e) * e
    rw [mul_sub, sub_mul, hea, hae, he]
  refine ⟨e * ↑u⁻¹, ?_, ?_⟩
  · rw [← hue, mul_assoc, ← mul_assoc _ (u : A), Units.inv_mul, one_mul, he]
  · rw [← mul_assoc, hae, ← hue, ← hc.eq, mul_assoc, Units.mul_inv, mul_one]

namespace UniversalEnvelopingAlgebra

universe u v

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  {V W X : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X]

universe w

variable (K L V W) in
/-- A natural transformation `M ⊗ V → M ⊗ W` of functors on `L`-modules in `Type w`. -/
structure TensorNatTrans where
  /-- The component at `M`. -/
  app : ∀ (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M],
    M ⊗[K] V →ₗ⁅K,L⁆ M ⊗[K] W
  naturality : ∀ (M N : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
    (f : M →ₗ⁅K,L⁆ N) (t : M ⊗[K] V),
    (f : M →ₗ[K] N).rTensor W (app M t) = app N ((f : M →ₗ[K] N).rTensor V t)

/-! ### Modules killed by a power of `I` -/

section Power

variable (I : TwoSidedIdeal (UniversalEnvelopingAlgebra K L)) (n : ℕ)
  (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- Every product of `n` elements of `I` acts by zero on `M`. -/
def IsKilledByPow : Prop :=
  ∀ l : List (UniversalEnvelopingAlgebra K L), l.length = n → (∀ a ∈ l, a ∈ I) →
    actionHom (R := K) (L := L) M l.prod = 0

/-- The Lie submodule `I M`, spanned by the vectors `a m` with `a ∈ I`. -/
def idealSMul : LieSubmodule K L M where
  toSubmodule := Submodule.span K {m | ∃ a ∈ I, ∃ m', actionHom (R := K) (L := L) M a m' = m}
  lie_mem {x m} hm := by
    change m ∈ Submodule.span K _ at hm
    change ⁅x, m⁆ ∈ Submodule.span K _
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨a, ha, m', rfl⟩ := hm
      have hx : ⁅x, actionHom (R := K) (L := L) M a m'⁆ =
          actionHom (R := K) (L := L) M (ι K x * a - a * ι K x) m' +
            actionHom (R := K) (L := L) M a ⁅x, m'⁆ := by
        rw [map_sub, LinearMap.sub_apply, map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply, actionHom_ι, LieModule.toEnd_apply_apply,
          LieModule.toEnd_apply_apply, sub_add_cancel]
      rw [hx]
      refine add_mem (Submodule.subset_span ⟨_, ?_, m', rfl⟩)
        (Submodule.subset_span ⟨a, ha, _, rfl⟩)
      exact sub_mem (I.mul_mem_left _ _ ha) (I.mul_mem_right _ _ ha)
    | zero => rw [lie_zero]; exact zero_mem _
    | add m m' _ _ hm hm' => rw [lie_add]; exact add_mem hm hm'
    | smul c m _ hm => rw [lie_smul]; exact Submodule.smul_mem _ c hm

variable {I n M}

/-- A module killed by all products of `n` elements of `I` has the filtration
`M ⊇ I M ⊇ I² M ⊇ ⋯ ⊇ Iⁿ M = 0` with subquotients killed by `I`. -/
theorem hasKilledFiltration_of_isKilledByPow (hM : IsKilledByPow I n M) :
    HasKilledFiltration I M n := by
  induction n generalizing M with
  | zero =>
    have h := hM [] rfl (by simp)
    rw [List.prod_nil, map_one] at h
    have hz : ∀ z : M, z = 0 := fun z ↦ LinearMap.congr_fun h z
    have : Subsingleton M := ⟨fun x y ↦ by rw [hz x, hz y]⟩
    exact HasKilledFiltration.zero (R := K) (L := L) (I := I) M
  | succ n ih =>
    refine .succ M (idealSMul I M) n (ih fun l hl hlI ↦ LinearMap.ext fun ⟨m, hm⟩ ↦ ?_) ?_
    · refine Subtype.ext ?_
      change (idealSMul I M).incl (actionHom _ l.prod ⟨m, hm⟩) = 0
      rw [LieModuleHom.map_actionHom]
      change actionHom (R := K) (L := L) M l.prod m = 0
      induction hm using Submodule.span_induction with
      | mem m hm =>
        obtain ⟨a, ha, m', rfl⟩ := hm
        rw [← Module.End.mul_apply, ← map_mul, ← List.prod_concat]
        rw [hM _ (by simp [hl]) (fun b hb ↦ by
          rcases List.mem_append.mp (List.concat_eq_append ▸ hb) with hb | hb
          exacts [hlI b hb, (List.mem_singleton.mp hb) ▸ ha]), LinearMap.zero_apply]
      | zero => rw [map_zero]
      | add m m' _ _ hm hm' => rw [map_add, hm, hm', add_zero]
      | smul c m _ hm => rw [map_smul, hm, smul_zero]
    · intro a ha
      refine LinearMap.ext fun q ↦ ?_
      induction q using Submodule.Quotient.induction_on with
      | H m =>
        change actionHom _ a (LieSubmodule.Quotient.mk' (idealSMul I M) m) = 0
        rw [← LieModuleHom.map_actionHom]
        change LieSubmodule.Quotient.mk _ = 0
        rw [LieSubmodule.Quotient.mk_eq_zero']
        exact Submodule.subset_span ⟨a, ha, m, rfl⟩

end Power

namespace TensorNatTrans

/-- The composite of two natural transformations. -/
def comp (ψ : TensorNatTrans.{u, v, w} K L W X) (φ : TensorNatTrans.{u, v, w} K L V W) :
    TensorNatTrans.{u, v, w} K L V X where
  app M _ _ _ _ := (ψ.app M).comp (φ.app M)
  naturality M N _ _ _ _ _ _ _ _ f t := by
    rw [LieModuleHom.comp_apply, ψ.naturality, φ.naturality, LieModuleHom.comp_apply]

@[simp] theorem comp_app (ψ : TensorNatTrans.{u, v, w} K L W X)
    (φ : TensorNatTrans.{u, v, w} K L V W)
    (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    (ψ.comp φ).app M = (ψ.app M).comp (φ.app M) := rfl

/-- The natural transformation on all modules attached to `g : V → U^{ad} ⊗ W`. -/
def ofTensorNatMap (g : V →ₗ⁅K,L⁆ AdQuotient K L ⊥ ⊗[K] W) : TensorNatTrans.{u, v, w} K L V W where
  app _ _ _ _ _ := tensorNatMap g isKilledBy_bot
  naturality _ _ _ _ _ _ _ _ _ _ f t := tensorNatMap_naturality g _ _ f t

@[simp] theorem ofTensorNatMap_app (g : V →ₗ⁅K,L⁆ AdQuotient K L ⊥ ⊗[K] W)
    (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    (ofTensorNatMap g).app M = tensorNatMap g (isKilledBy_bot (M := M)) := rfl

variable {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K L)}

/-- On a module killed by `I`, a natural transformation is `tensorNatMap` of its value at
`U / I`. -/
theorem exists_tensorNatMap_eq (φ : TensorNatTrans.{u, v, max u v} K L V W) :
    ∃ g : V →ₗ⁅K,L⁆ AdQuotient K L I ⊗[K] W, ∀ (M : Type (max u v)) [AddCommGroup M] [Module K M]
      [LieRingModule L M] [LieModule K L M] (hM : IsKilledBy I M), tensorNatMap g hM = φ.app M :=
  ⟨evalNat (φ.app (LeftQuotient K L I)) (fun u t ↦ φ.naturality _ _ (quotientMulRight I u) t),
    fun _ _ _ _ _ hM ↦ tensorNatMap_evalNat _ _ hM _ fun _ t ↦ φ.naturality _ _ _ t⟩

/-- Two natural transformations that agree at a module `M₀` with annihilator `I` agree at every
module killed by `I`. -/
theorem app_eq_of_app_eq (φ ψ : TensorNatTrans.{u, v, max u v} K L V W) {M₀ : Type (max u v)}
    [AddCommGroup M₀] [Module K M₀] [LieRingModule L M₀] [LieModule K L M₀] (hM₀ : IsKilledBy I M₀)
    (hI : ∀ a, actionHom (R := K) (L := L) M₀ a = 0 → a ∈ I) (h : φ.app M₀ = ψ.app M₀)
    {M : Type (max u v)} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (hM : IsKilledBy I M) : φ.app M = ψ.app M := by
  obtain ⟨g, hg⟩ := exists_tensorNatMap_eq (I := I) φ
  obtain ⟨g', hg'⟩ := exists_tensorNatMap_eq (I := I) ψ
  have : g = g' := tensorNatLinear_injective (V := V) (W := W) hM₀ hI (by
    rw [tensorNatLinear_apply, tensorNatLinear_apply, hg, hg', h])
  rw [← hg _ hM, ← hg' _ hM, this]

omit [LieModule K L X] in
/-- If `β ∘ α` agrees with `ε` at a module `M₀` with annihilator `I`, then `β ∘ α - ε` is
nilpotent at every module with a filtration whose subquotients are killed by `I`. -/
theorem isNilpotent_comp_sub (ε : TensorNatTrans.{u, v, max u v} K L V V)
    (α : TensorNatTrans.{u, v, max u v} K L V W) (β : TensorNatTrans.{u, v, max u v} K L W V)
    {M₀ : Type (max u v)} [AddCommGroup M₀] [Module K M₀] [LieRingModule L M₀] [LieModule K L M₀]
    (hM₀ : IsKilledBy I M₀) (hI : ∀ a, actionHom (R := K) (L := L) M₀ a = 0 → a ∈ I)
    (h : (β.app M₀).comp (α.app M₀) = ε.app M₀)
    {M : Type (max u v)} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {n : ℕ}
    (hM : HasKilledFiltration I M n) :
    IsNilpotent (((β.comp α).app M : M ⊗[K] V →ₗ[K] M ⊗[K] V) - ε.app M) :=
  ⟨n, pow_eq_zero_of_hasKilledFiltration (V := V)
    (fun N _ _ _ _ ↦ (β.comp α).app N - ε.app N)
    (fun N N' _ _ _ _ _ _ _ _ f t ↦ by
      rw [sub_apply, sub_apply, map_sub, (β.comp α).naturality, ε.naturality])
    (fun N _ _ _ _ hN ↦ by rw [app_eq_of_app_eq (β.comp α) ε hM₀ hI h hN, sub_self]) hM⟩

/-- **Humphreys, proof of Theorem 10.7 (b)**: let `e`, `e'` be natural idempotents of `− ⊗ V`,
`− ⊗ W`, and `φ : e(− ⊗ V) → e'(− ⊗ W)`, `φ' : e'(− ⊗ W) → e(− ⊗ V)` natural transformations
that are mutually inverse at a module `M₀` with annihilator `I`. Then `φ_M` is an isomorphism
`e_M(M ⊗ V) ≅ e'_M(M ⊗ W)` for every module `M` with a finite filtration whose subquotients are
killed by `I`: some `ψ` satisfies `ψ φ_M = e_M` and `φ_M ψ = e'_M`. -/
theorem exists_inverse_of_hasKilledFiltration (e : TensorNatTrans.{u, v, max u v} K L V V)
    (e' : TensorNatTrans.{u, v, max u v} K L W W) (φ : TensorNatTrans.{u, v, max u v} K L V W)
    (φ' : TensorNatTrans.{u, v, max u v} K L W V)
    {M₀ : Type (max u v)} [AddCommGroup M₀] [Module K M₀] [LieRingModule L M₀] [LieModule K L M₀]
    (hM₀ : IsKilledBy I M₀) (hI : ∀ a, actionHom (R := K) (L := L) M₀ a = 0 → a ∈ I)
    (h₁ : (φ'.app M₀).comp (φ.app M₀) = e.app M₀) (h₂ : (φ.app M₀).comp (φ'.app M₀) = e'.app M₀)
    {M : Type (max u v)} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {n : ℕ}
    (hM : HasKilledFiltration I M n)
    (he : ∀ x, e.app M (e.app M x) = e.app M x) (he' : ∀ y, e'.app M (e'.app M y) = e'.app M y)
    (hφ : ∀ x, e'.app M (φ.app M (e.app M x)) = φ.app M x)
    (hφ' : ∀ y, e.app M (φ'.app M (e'.app M y)) = φ'.app M y) :
    ∃ ψ : M ⊗[K] W →ₗ[K] M ⊗[K] V, ψ ∘ₗ (φ.app M : M ⊗[K] V →ₗ[K] M ⊗[K] W) = e.app M ∧
      (φ.app M : M ⊗[K] V →ₗ[K] M ⊗[K] W) ∘ₗ ψ = e'.app M := by
  have hφe : ∀ x, φ.app M (e.app M x) = φ.app M x := fun x ↦ by
    have h := hφ (e.app M x)
    rw [he] at h
    rw [← h, hφ]
  have he'φ : ∀ x, e'.app M (φ.app M x) = φ.app M x := fun x ↦ by rw [← hφ, he', hφ]
  have hφ'e' : ∀ y, φ'.app M (e'.app M y) = φ'.app M y := fun y ↦ by
    have h := hφ' (e'.app M y)
    rw [he'] at h
    rw [← h, hφ']
  have heφ' : ∀ y, e.app M (φ'.app M y) = φ'.app M y := fun y ↦ by rw [← hφ', he, hφ']
  obtain ⟨b, hb₁, -⟩ := exists_mul_eq_of_isNilpotent_sub (A := Module.End K (M ⊗[K] V))
    (e := e.app M) (a := (φ'.comp φ).app M) (LinearMap.ext he)
    (LinearMap.ext fun x ↦ by
      change e.app M (φ'.app M (φ.app M (e.app M x))) = φ'.app M (φ.app M x)
      rw [hφe, heφ'])
    (isNilpotent_comp_sub e φ φ' hM₀ hI h₁ hM)
  obtain ⟨c, -, hc₂⟩ := exists_mul_eq_of_isNilpotent_sub (A := Module.End K (M ⊗[K] W))
    (e := e'.app M) (a := (φ.comp φ').app M) (LinearMap.ext he')
    (LinearMap.ext fun y ↦ by
      change e'.app M (φ.app M (φ'.app M (e'.app M y))) = φ.app M (φ'.app M y)
      rw [hφ'e', he'φ])
    (isNilpotent_comp_sub e' φ' φ hM₀ hI h₂ hM)
  have hb : ∀ x, b (φ'.app M (φ.app M x)) = e.app M x := fun x ↦ LinearMap.congr_fun hb₁ x
  have hc : ∀ y, φ.app M (φ'.app M (c y)) = e'.app M y := fun y ↦ LinearMap.congr_fun hc₂ y
  -- the left inverse `b φ'` equals the right inverse `φ' c`
  have hL : ∀ y, b (φ'.app M y) = φ'.app M (c y) := fun y ↦ by
    rw [← hφ'e', ← hc, hb, heφ']
  refine ⟨b ∘ₗ (φ'.app M : M ⊗[K] W →ₗ[K] M ⊗[K] V), LinearMap.ext hb, LinearMap.ext fun y ↦ ?_⟩
  change φ.app M (b (φ'.app M y)) = e'.app M y
  rw [hL, hc]

end TensorNatTrans

end UniversalEnvelopingAlgebra
