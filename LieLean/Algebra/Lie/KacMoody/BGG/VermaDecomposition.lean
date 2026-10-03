/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Nilradical
import LieLean.Algebra.Lie.UniversalEnveloping.Free

/-!
# Verma modules as induced modules along a simple root

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra over a field `K` of characteristic zero, `i` a simple index
and `𝔲ᵢ⁻ ⊆ 𝔫₋` the subalgebra of `LieLean.Algebra.Lie.KacMoody.BGG.Nilradical`, so that
`𝔫₋ = K fᵢ ⊕ 𝔲ᵢ⁻`. By PBW, `U(𝔫₋) = K[fᵢ] ⊗ U(𝔲ᵢ⁻)`, hence every element of the Verma module
`M(λ) ≅ U(𝔫₋)` can be written uniquely as `∑ₐ fᵢᵃ uₐ v_λ` with `uₐ ∈ U(𝔲ᵢ⁻)`
(`Matrix.Realization.KacMoodyAlgebra.VermaModule.nilradDecomp`). The image `Rᵢ` of `U(𝔲ᵢ⁻)` in
`U(𝔤)` is stable under the commutators with `eᵢ`, `fᵢ` and `𝔥`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.nilradNegSub`, `Matrix.Realization.KacMoodyAlgebra.fLine`:
  `𝔲ᵢ⁻` and `K fᵢ` as Lie subalgebras of `𝔫₋`.
* `Matrix.Realization.KacMoodyAlgebra.envNilrad`: the injective algebra map `U(𝔲ᵢ⁻) → U(𝔤)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.nilradDecomp`: the linear isomorphism
  `(ℕ →₀ U(𝔲ᵢ⁻)) ≃ M(λ)`, `(uₐ)ₐ ↦ ∑ₐ fᵢᵃ uₐ v_λ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.isCompl_fLine_nilradNegSub`: `𝔫₋ = K fᵢ ⊕ 𝔲ᵢ⁻`.
* `Matrix.Realization.KacMoodyAlgebra.envNilrad_injective`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.nilradDecomp_single`.
* `Matrix.Realization.KacMoodyAlgebra.commutator_mem_range_envNilrad`: the commutator of `U(𝔲ᵢ⁻)`
  with an element `x ∈ 𝔤` normalizing `𝔲ᵢ⁻` lies in `U(𝔲ᵢ⁻)`.

## References

* J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §17.3,
  Corollary D (PBW for complementary subalgebras).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (i : ι)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))

/-- `𝔲ᵢ⁻` as a Lie subalgebra of `𝔫₋`. -/
def nilradNegSub : LieSubalgebra K (nNeg P) where
  carrier := {x | (x : P.KacMoodyAlgebra) ∈ nilradNeg P i}
  add_mem' hx hy := (nilradNeg P i).add_mem hx hy
  zero_mem' := (nilradNeg P i).zero_mem
  smul_mem' c _ hx := (nilradNeg P i).smul_mem c hx
  lie_mem' hx hy := lie_mem_nilradNeg i hx hy

/-- `fᵢ` as an element of `𝔫₋`. -/
def fNeg : nNeg P := ⟨f P i, f_mem_nNeg P i⟩

lemma fNeg_ne_zero : fNeg P i ≠ 0 := fun h ↦ f_ne_zero P i (congrArg Subtype.val h)

/-- The line `K fᵢ` as a Lie subalgebra of `𝔫₋`. -/
def fLine : LieSubalgebra K (nNeg P) where
  toSubmodule := K ∙ fNeg P i
  lie_mem' {x y} hx hy := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero]
    exact Submodule.zero_mem _

/-- `𝔫₋ = K fᵢ ⊕ 𝔲ᵢ⁻`. -/
theorem isCompl_fLine_nilradNegSub :
    IsCompl (fLine P i).toSubmodule (nilradNegSub P i).toSubmodule := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have h1 : ((a • fNeg P i : nNeg P) : P.KacMoodyAlgebra) ∈ K ∙ f P i :=
      Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
    have := Submodule.disjoint_def.mp (disjoint_span_f_nilradNeg (P := P) i) _ h1 hx'
    exact Subtype.ext this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : (x : P.KacMoodyAlgebra) ∈ (K ∙ f P i) ⊔ nilradNeg P i := by
      rw [← nNeg_eq_span_f_sup_nilradNeg (P := P) i]; exact x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine Submodule.mem_sup.mpr ⟨a • fNeg P i, Submodule.smul_mem _ a
      (Submodule.mem_span_singleton_self _), ⟨z, nilradNeg_le_nNeg i hz⟩, hz, Subtype.ext ?_⟩
    simpa [fNeg] using hyz

/-- The basis `fᵢ` of `K fᵢ`. -/
def fLineBasis : Basis Unit K (fLine P i) :=
  (Basis.singleton Unit K).map (LinearEquiv.toSpanNonzeroSingleton K (nNeg P) (fNeg P i)
    (fNeg_ne_zero P i))

@[simp] lemma coe_fLineBasis (u : Unit) :
    ((fLineBasis P i u : fLine P i) : nNeg P) = fNeg P i := by
  change (((LinearEquiv.toSpanNonzeroSingleton K (nNeg P) (fNeg P i) (fNeg_ne_zero P i))
    ((Basis.singleton Unit K) u) : K ∙ fNeg P i) : nNeg P) = fNeg P i
  rw [Basis.singleton_apply, LinearEquiv.toSpanNonzeroSingleton_one]

lemma pbwMonomial_fLineBasis (n : ℕ) :
    UniversalEnvelopingAlgebra.pbwMonomial K (fLineBasis P i) (Finsupp.single () n) =
      (UniversalEnvelopingAlgebra.ι K (fLineBasis P i ())) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show Finsupp.single () (n + 1) = Finsupp.single () n + Finsupp.single () 1 by
      rw [Finsupp.single_add],
      UniversalEnvelopingAlgebra.PBW.pbwMonomial_add_single (fun _ _ ↦ le_rfl), ih, pow_succ']

/-- The injective algebra map `U(𝔲ᵢ⁻) → U(𝔤)`. -/
def envNilrad : UniversalEnvelopingAlgebra K (nilradNegSub P i) →ₐ[K] 𝓤 :=
  AlgHom.comp mapN (UniversalEnvelopingAlgebra.map (nilradNegSub P i).incl)

theorem envNilrad_injective : Function.Injective (envNilrad P i) := by
  rw [envNilrad, AlgHom.coe_comp]
  exact (UniversalEnvelopingAlgebra.map_incl_injective (nNeg P)).comp
    (UniversalEnvelopingAlgebra.map_incl_injective (nilradNegSub P i))

@[simp] lemma envNilrad_ι (x : nilradNegSub P i) :
    envNilrad P i (ιᵤ x) = ιᵤ ((x : nNeg P) : P.KacMoodyAlgebra) := by
  rw [envNilrad, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    UniversalEnvelopingAlgebra.map_ι]
  rfl

/-- The commutator `[x, u]` of an element `x ∈ 𝔤` normalizing `𝔲ᵢ⁻` with an element `u` of (the
image of) `U(𝔲ᵢ⁻)` lies in `U(𝔲ᵢ⁻)`. -/
theorem commutator_mem_range_envNilrad {x : P.KacMoodyAlgebra}
    (hx : ∀ y ∈ nilradNeg P i, ⁅x, y⁆ ∈ nilradNeg P i)
    (u : UniversalEnvelopingAlgebra K (nilradNegSub P i)) :
    ιᵤ x * envNilrad P i u - envNilrad P i u * ιᵤ x ∈ (envNilrad P i).range := by
  induction u using UniversalEnvelopingAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes, sub_self]; exact zero_mem _
  | ι y =>
    rw [envNilrad_ι, ← Ring.lie_def, ← LieHom.map_lie]
    have hy : ⁅x, ((y : nNeg P) : P.KacMoodyAlgebra)⁆ ∈ nilradNeg P i := hx _ y.2
    refine ⟨ιᵤ ⟨⟨_, nilradNeg_le_nNeg i hy⟩, show _ ∈ nilradNeg P i from hy⟩, ?_⟩
    change envNilrad P i _ = _
    rw [envNilrad_ι]
  | mul a b ha hb =>
    rw [map_mul, show ιᵤ x * (envNilrad P i a * envNilrad P i b) -
        envNilrad P i a * envNilrad P i b * ιᵤ x =
        (ιᵤ x * envNilrad P i a - envNilrad P i a * ιᵤ x) * envNilrad P i b +
          envNilrad P i a * (ιᵤ x * envNilrad P i b - envNilrad P i b * ιᵤ x) by noncomm_ring]
    exact add_mem (mul_mem ha ⟨b, rfl⟩) (mul_mem ⟨a, rfl⟩ hb)
  | add a b ha hb =>
    rw [map_add, show ιᵤ x * (envNilrad P i a + envNilrad P i b) -
        (envNilrad P i a + envNilrad P i b) * ιᵤ x =
        (ιᵤ x * envNilrad P i a - envNilrad P i a * ιᵤ x) +
          (ιᵤ x * envNilrad P i b - envNilrad P i b * ιᵤ x) by noncomm_ring]
    exact add_mem ha hb

namespace VermaModule

/-- The auxiliary linear isomorphism `((Unit →₀ ℕ) →₀ U(𝔲ᵢ⁻)) ≃ U(𝔫₋)`,
`single s u ↦ fᵢ^{s ()} u`. -/
def nilradDecompAux :
    ((Unit →₀ ℕ) →₀ UniversalEnvelopingAlgebra K (nilradNegSub P i)) ≃ₗ[K]
      UniversalEnvelopingAlgebra K (nNeg P) :=
  (TensorProduct.finsuppScalarLeft K _ (Unit →₀ ℕ)).symm ≪≫ₗ
    TensorProduct.congr (UniversalEnvelopingAlgebra.pbwBasis (fLineBasis P i)).repr.symm
      (LinearEquiv.refl K _) ≪≫ₗ
    UniversalEnvelopingAlgebra.tensorEquivOfIsCompl (isCompl_fLine_nilradNegSub P i)

lemma nilradDecompAux_single (n : ℕ) (u : UniversalEnvelopingAlgebra K (nilradNegSub P i)) :
    nilradDecompAux P i (Finsupp.single (Finsupp.single () n) u) =
      (ιᵤ (fNeg P i)) ^ n * UniversalEnvelopingAlgebra.map (nilradNegSub P i).incl u := by
  simp only [nilradDecompAux, LinearEquiv.trans_apply,
    TensorProduct.finsuppScalarLeft_symm_apply_single, TensorProduct.congr_tmul,
    Basis.repr_symm_apply, Finsupp.linearCombination_single, one_smul,
    UniversalEnvelopingAlgebra.pbwBasis_apply, pbwMonomial_fLineBasis, LinearEquiv.refl_apply,
    UniversalEnvelopingAlgebra.tensorEquivOfIsCompl_apply_tmul, map_pow,
    UniversalEnvelopingAlgebra.map_ι, LieSubalgebra.coe_incl, coe_fLineBasis]

/-- `(Unit →₀ ℕ) ≃ ℕ`. -/
def unitFinsuppEquiv : (Unit →₀ ℕ) ≃ ℕ := Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)

lemma unitFinsuppEquiv_symm_apply (n : ℕ) : unitFinsuppEquiv.symm n = Finsupp.single () n := by
  ext
  simp [unitFinsuppEquiv]

variable (Λ : Dual K H)

/-- **`M(λ) = ⊕ₐ fᵢᵃ U(𝔲ᵢ⁻) v_λ`**: the linear isomorphism `(ℕ →₀ U(𝔲ᵢ⁻)) ≃ M(λ)` sending
`(uₐ)ₐ` to `∑ₐ fᵢᵃ uₐ v_λ`. -/
def nilradDecomp :
    (ℕ →₀ UniversalEnvelopingAlgebra K (nilradNegSub P i)) ≃ₗ[K] VermaModule P Λ :=
  Finsupp.domLCongr unitFinsuppEquiv.symm ≪≫ₗ nilradDecompAux P i ≪≫ₗ equivEnvNNeg P Λ

theorem nilradDecomp_single (n : ℕ) (u : UniversalEnvelopingAlgebra K (nilradNegSub P i)) :
    nilradDecomp P i Λ (Finsupp.single n u) =
      (ιᵤ (f P i)) ^ n • (envNilrad P i u • hwv P Λ) := by
  rw [nilradDecomp, LinearEquiv.trans_apply, LinearEquiv.trans_apply, Finsupp.domLCongr_single,
    unitFinsuppEquiv_symm_apply, nilradDecompAux_single, equivEnvNNeg_apply, map_mul, mul_smul,
    map_pow, UniversalEnvelopingAlgebra.map_ι]
  rfl

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
