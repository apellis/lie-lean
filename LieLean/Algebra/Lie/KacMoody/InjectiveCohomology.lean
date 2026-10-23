/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DualVermaCohomology
import LieLean.Algebra.Lie.KacMoody.TensorVerma
import LieLean.Algebra.Lie.Homology.TrivialTensor

/-!
# `𝔫`-cohomology of duals of `⊕ⱼ M(λⱼ) ⊗ Fⱼ`

Let `Q = ⊕ⱼ M(λⱼ) ⊗ Fⱼ` be a direct sum of tensor products of Verma modules with arbitrary
`𝔤`-modules. The injective modules of `𝒪` constructed in `exists_isInjectiveO_injective` are the
duals `Q^∨` of such modules. We prove `H^n(𝔫, Q^∨)_μ = 0` for `n > 0`
(`isZero_nPosCohomology_restrictedDual_directSum`), the input for dimension shifting in
Humphreys GSM 94 Prop. 6.15 (b).

As for `M(λ)^∨` (`DualVermaCohomology.lean`) the argument is by duality with homology
(`exists_δ_eq_restrictedDual`, for any `V` whose `ω`-twist is acyclic): as a `𝔫₊`-module,
`Q^ω = ⊕ⱼ M(λⱼ)^ω ⊗ Fⱼ^ω ≅ ⊕ⱼ U(𝔫₊) ⊗ Fⱼ^ω`, and by the tensor identity
(`UniversalEnvelopingAlgebra.TensorIdentity.equiv`) `U(𝔫₊) ⊗ Fⱼ^ω` is the free module
`U(𝔫₊) ⊗ (Fⱼ)_triv`, which is acyclic in positive degrees.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.subsingleton_homology_omegaTwist_directSum`:
  `H_q(𝔫₊, Q^ω) = 0` for `q > 0`.
* `Matrix.Realization.KacMoodyAlgebra.exists_δ_eq_restrictedDual`: weight cocycles of positive
  degree with coefficients in `V^∨` are coboundaries when `V^ω` is acyclic.
* `Matrix.Realization.KacMoodyAlgebra.isZero_nPosCohomology_restrictedDual_directSum`:
  `H^n(𝔫, Q^∨)_μ = 0` for `n > 0`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Prop. 6.15 (b). The argument is our own.
-/

open Module LieModule LieModule.ChevalleyEilenberg CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open UniversalEnvelopingAlgebra TwistedDual

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Twisting commutes with tensor products and direct sums -/

section Twist

variable (V W : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

/-- The linear identification `(V ⊗ W)^ω = V^ω ⊗ W^ω`. -/
def omegaTwistTensorLinearEquiv :
    OmegaTwist P (V ⊗[K] W) ≃ₗ[K] OmegaTwist P V ⊗[K] OmegaTwist P W :=
  (OmegaTwist.of P (V ⊗[K] W)).symm.trans
    (TensorProduct.congr (OmegaTwist.of P V) (OmegaTwist.of P W))

lemma omegaTwistTensorLinearEquiv_lie (x : nPos P) (t : V ⊗[K] W) :
    omegaTwistTensorLinearEquiv P V W ⁅x, OmegaTwist.of P _ t⁆ =
      ⁅x, omegaTwistTensorLinearEquiv P V W (OmegaTwist.of P _ t)⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
    change TensorProduct.congr (OmegaTwist.of P V) (OmegaTwist.of P W)
      ⁅chevalleyInvolution P x, v ⊗ₜ[K] w⁆ = _
    rw [TensorProduct.LieModule.lie_tmul_right]
    simp only [omegaTwistTensorLinearEquiv, map_add, TensorProduct.congr_tmul,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  | add t s ht hs =>
    rw [map_add, lie_add, map_add, ht, hs, map_add, lie_add]

/-- `(V ⊗ W)^ω = V^ω ⊗ W^ω` as `𝔫₊`-modules. -/
def omegaTwistTensorEquiv :
    OmegaTwist P (V ⊗[K] W) ≃ₗ⁅K,nPos P⁆ OmegaTwist P V ⊗[K] OmegaTwist P W :=
  { omegaTwistTensorLinearEquiv P V W with
    map_lie' := by
      intro x t
      obtain ⟨t, rfl⟩ := (OmegaTwist.of P (V ⊗[K] W)).surjective t
      exact omegaTwistTensorLinearEquiv_lie P V W x t }

variable {κ : Type*} (V : κ → Type*) [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)] [∀ j, LieRingModule P.KacMoodyAlgebra (V j)]
  [∀ j, LieModule K P.KacMoodyAlgebra (V j)]

/-- `(⊕ⱼ Vⱼ)^ω = ⊕ⱼ Vⱼ^ω` as `𝔫₊`-modules. -/
def omegaTwistDirectSumEquiv :
    OmegaTwist P (⨁ j, V j) ≃ₗ⁅K,nPos P⁆ ⨁ j, OmegaTwist P (V j) :=
  { (OmegaTwist.of P (⨁ j, V j)).symm.trans
      (DFinsupp.mapRange.linearEquiv fun j ↦ OmegaTwist.of P (V j)) with
    map_lie' := by
      intro x t
      ext j
      rfl }

end Twist

/-! ### Acyclicity of `Q^ω` -/

section Acyclic

variable (Λ : Dual K H) (F : Type*) [AddCommGroup F] [Module K F]
  [LieRingModule P.KacMoodyAlgebra F] [LieModule K P.KacMoodyAlgebra F]

/-- `(M(λ) ⊗ F)^ω ≅ U(𝔫₊) ⊗ (F^ω)_triv` as `𝔫₊`-modules. -/
def omegaTwistVermaTensorEquiv :
    OmegaTwist P (VermaModule P Λ ⊗[K] F) ≃ₗ⁅K,nPos P⁆
      LeftRegular K (nPos P) ⊗[K] TrivialLieModule K (nPos P) (OmegaTwist P F) :=
  (omegaTwistTensorEquiv P _ F).trans
    (((omegaTwistVermaEquiv P Λ).symm.tensorCongr LieModuleEquiv.refl).trans
      (TensorIdentity.equiv (R := K) (L := nPos P) (Z := OmegaTwist P F)).symm)

/-- `H_q(𝔫₊, (M(λ) ⊗ F)^ω) = 0` for `q > 0`. -/
theorem subsingleton_homology_omegaTwist_verma_tensor (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology K (nPos P) (OmegaTwist P (VermaModule P Λ ⊗[K] F)) q) :=
  (homologyEquiv (omegaTwistVermaTensorEquiv P Λ F) q).toEquiv.subsingleton_congr.mpr
    (subsingleton_homology_tensor_trivial K (nPos P) _ _ q
      (subsingleton_homology_leftRegular q hq))

variable {κ : Type*} (lam : κ → Dual K H) (F : κ → Type*)
  [∀ j, AddCommGroup (F j)] [∀ j, Module K (F j)] [∀ j, LieRingModule P.KacMoodyAlgebra (F j)]
  [∀ j, LieModule K P.KacMoodyAlgebra (F j)]

/-- `H_q(𝔫₊, Q^ω) = 0` for `q > 0`, `Q = ⊕ⱼ M(λⱼ) ⊗ Fⱼ`. -/
theorem subsingleton_homology_omegaTwist_directSum (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology K (nPos P)
      (OmegaTwist P (⨁ j, VermaModule P (lam j) ⊗[K] F j)) q) :=
  (homologyEquiv (omegaTwistDirectSumEquiv P fun j ↦ VermaModule P (lam j) ⊗[K] F j)
    q).toEquiv.subsingleton_congr.mpr
    (subsingleton_homology_directSum _ q fun j ↦
      subsingleton_homology_omegaTwist_verma_tensor P (lam j) (F j) q hq)

end Acyclic

/-! ### Vanishing of cohomology -/

section Vanishing

variable {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- **Weight cocycles of positive degree on `V^∨` are coboundaries** when `V` is the sum of its
weight spaces and `V^ω` has no positive-degree `𝔫₊`-homology. -/
theorem exists_δ_eq_restrictedDual (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤)
    (hacyc : ∀ q, 0 < q → Subsingleton (homology K (nPos P) (OmegaTwist P V) q)) {k : ℕ}
    {μ : Dual K H} {f : Cochains K (nPos P) (restrictedDual P V) (k + 1)}
    (hf : f ∈ (nPosDerivAction P (restrictedDual P V)).cochainWeightSpace (k + 1) μ)
    (hδ : δ K (nPos P) _ (k + 1) f = 0) :
    ∃ g ∈ (nPosDerivAction P (restrictedDual P V)).cochainWeightSpace k μ,
      δ K (nPos P) _ k g = f :=
  (nPosDerivAction P (OmegaTwist P V)).exists_δ_eq_of_subsingleton_homology
    (ρN := nPosDerivAction P (restrictedDual P V)) (fun _ ↦ rfl)
    (fun x φ m ↦ dualPairing_lie P (x : P.KacMoodyAlgebra) φ m)
    (fun a φ m ↦ dualPairing_lie P (h P a) φ m) (dualPairing_injective P)
    (fun _ _ hψ ↦ mem_range_dualPairing P hψ) (iSup_weightSpaceOf_adNPos P)
    (iSup_weightSpaceOf_omegaTwist P hV) (hacyc (k + 1) k.succ_pos) hf hδ

/-- `H^n(𝔫, V^∨)_μ = 0` for `n > 0` when `V` is the sum of its weight spaces and `V^ω` has no
positive-degree `𝔫₊`-homology. -/
theorem isZero_nPosCohomology_restrictedDual (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤)
    (hacyc : ∀ q, 0 < q → Subsingleton (homology K (nPos P) (OmegaTwist P V) q))
    (μ : Dual K H) {n : ℕ} (hn : 0 < n) :
    IsZero (nPosCohomology P (restrictedDual P V) μ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add]
  exact (nPosDerivAction P _).isZero_weightComplex_homology_succ fun f hf hδ ↦
    exists_δ_eq_restrictedDual P hV hacyc hf hδ

variable {κ : Type*} (lam : κ → Dual K H) (F : κ → Type*)
  [∀ j, AddCommGroup (F j)] [∀ j, Module K (F j)] [∀ j, LieRingModule P.KacMoodyAlgebra (F j)]
  [∀ j, LieModule K P.KacMoodyAlgebra (F j)]

/-- **`H^n(𝔫, Q^∨)_μ = 0` for `n > 0`**, `Q = ⊕ⱼ M(λⱼ) ⊗ Fⱼ` a sum of weight spaces. -/
theorem isZero_nPosCohomology_restrictedDual_directSum
    (hV : ⨆ ν, weightSpaceOfMap (⨁ j, VermaModule P (lam j) ⊗[K] F j) (h P) ν = ⊤)
    (μ : Dual K H) {n : ℕ} (hn : 0 < n) :
    IsZero (nPosCohomology P (restrictedDual P (⨁ j, VermaModule P (lam j) ⊗[K] F j)) μ n) :=
  isZero_nPosCohomology_restrictedDual P hV
    (fun q hq ↦ subsingleton_homology_omegaTwist_directSum P lam F q hq) μ hn

end Vanishing

end Matrix.Realization.KacMoodyAlgebra
