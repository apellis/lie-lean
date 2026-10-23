/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.CochainDuality
import LieLean.Algebra.Lie.KacMoody.NPosCohomology
import LieLean.Algebra.Lie.KacMoody.RestrictedDual
import LieLean.Algebra.Lie.KacMoody.BGG.VermaHomology
import LieLean.Algebra.Lie.KacMoody.SerreAssociative.NegativePart
import LieLean.Algebra.Lie.Homology.RegularAcyclic

/-!
# `𝔫`-cohomology of dual Verma modules

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra, `𝔫 = 𝔫₊` its positive nilpotent subalgebra and
`M(λ)^∨` the restricted twisted dual of the Verma module `M(λ)`. We prove that
`H^n(𝔫, M(λ)^∨)_μ = 0` for `n > 0` and every weight `μ`, the vanishing step in the proof of
Humphreys GSM 94 Prop. 6.15 (b).

The argument is by duality with homology. The Chevalley involution `ω` exchanges `𝔫₊` and `𝔫₋`
(`nPosEquivNNeg`). Let `M(λ)^ω` be `M(λ)` with `𝔤` acting through `ω`; as a `𝔫₊`-module it is
the left-regular module of `U(𝔫₊)` (`omegaTwistVermaEquiv`, via PBW for `M(λ)`), so its
positive-degree homology vanishes. The evaluation pairing `M(λ)^∨ × M(λ)^ω → K` is invariant, and
every weight functional on `M(λ)^ω` lies in `M(λ)^∨`, so
`LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_subsingleton_homology` applies.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.nPosEquivNNeg`: `ω : 𝔫₊ ≃ 𝔫₋`.
* `Matrix.Realization.KacMoodyAlgebra.OmegaTwist`: a `𝔤`-module with the action twisted by `ω`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.subsingleton_homology_omegaTwist_verma`:
  `H_q(𝔫₊, M(λ)^ω) = 0` for `q > 0`.
* `Matrix.Realization.KacMoodyAlgebra.exists_δ_eq_dualVerma`: every weight cocycle of positive
  degree in `C^•(𝔫, M(λ)^∨)` is a coboundary of a cochain of the same weight.
* `Matrix.Realization.KacMoodyAlgebra.isZero_nPosCohomology_dualVerma`:
  `H^n(𝔫, M(λ)^∨)_μ = 0` for `n > 0`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Prop. 6.15 (b). Humphreys states the result in finite type; the proof here
  works for every generalized Cartan matrix, and the duality argument is our own.
-/

open Module LieModule LieModule.ChevalleyEilenberg CategoryTheory CategoryTheory.Limits

noncomputable section

namespace LieModule.ChevalleyEilenberg.DerivAction

variable {K H L N : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N] (ρ : DerivAction K H L N)

/-- If every weight-`μ` cocycle of degree `k + 1` is a coboundary of a weight-`μ` cochain, then
the weight-`μ` cohomology vanishes in degree `k + 1`. -/
theorem isZero_weightComplex_homology_succ {μ : Dual K H} {k : ℕ}
    (h : ∀ f ∈ ρ.cochainWeightSpace (k + 1) μ, δ K L N (k + 1) f = 0 →
      ∃ g ∈ ρ.cochainWeightSpace k μ, δ K L N k g = f) :
    IsZero ((ρ.weightComplex μ).homology (k + 1)) := by
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro f₀ hf
  let f : ρ.cochainWeightSpace (k + 1) μ := f₀
  have h1 : ρ.δWeight (k + 1) μ f = 0 := by
    have h := hf
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_g,
      ρ.weightComplex_d] at h
    exact h
  have hf' : δ K L N (k + 1) (f : Cochains K L N (k + 1)) = 0 := congrArg Subtype.val h1
  obtain ⟨g, hg, hgf⟩ := h f f.2 hf'
  refine ⟨⟨g, hg⟩, ?_⟩
  have h2 : ρ.δWeight k μ ⟨g, hg⟩ = f := Subtype.ext hgf
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_f,
    ρ.weightComplex_d]
  exact h2

end LieModule.ChevalleyEilenberg.DerivAction

namespace Matrix.Realization.KacMoodyAlgebra

open UniversalEnvelopingAlgebra TwistedDual

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### The Chevalley involution exchanges `𝔫₊` and `𝔫₋` -/

lemma chevalleyInvolution_comp_eHom :
    (chevalleyInvolution P).comp (eHom P) =
      (fHom P).comp (FreeLieAlgebra.lift K fun i ↦ -FreeLieAlgebra.of K i) :=
  FreeLieAlgebra.hom_ext fun i ↦ by simp

lemma chevalleyInvolution_comp_fHom :
    (chevalleyInvolution P).comp (fHom P) =
      (eHom P).comp (FreeLieAlgebra.lift K fun i ↦ -FreeLieAlgebra.of K i) :=
  FreeLieAlgebra.hom_ext fun i ↦ by simp

lemma chevalleyInvolution_mem_nNeg {x : P.KacMoodyAlgebra} (hx : x ∈ nPos P) :
    chevalleyInvolution P x ∈ nNeg P := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨FreeLieAlgebra.lift K (fun i ↦ -FreeLieAlgebra.of K i) z,
    (LieHom.congr_fun (chevalleyInvolution_comp_eHom P) z).symm⟩

lemma chevalleyInvolution_mem_nPos {x : P.KacMoodyAlgebra} (hx : x ∈ nNeg P) :
    chevalleyInvolution P x ∈ nPos P := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨FreeLieAlgebra.lift K (fun i ↦ -FreeLieAlgebra.of K i) z,
    (LieHom.congr_fun (chevalleyInvolution_comp_fHom P) z).symm⟩

/-- The Chevalley involution `ω : 𝔫₊ ≃ 𝔫₋`. -/
def nPosEquivNNeg : nPos P ≃ₗ⁅K⁆ nNeg P where
  toFun x := ⟨chevalleyInvolution P x, chevalleyInvolution_mem_nNeg P x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  map_lie' := Subtype.ext (LieHom.map_lie _ _ _)
  invFun y := ⟨chevalleyInvolution P y, chevalleyInvolution_mem_nPos P y.2⟩
  left_inv x := Subtype.ext (chevalleyInvolution_chevalleyInvolution P x)
  right_inv y := Subtype.ext (chevalleyInvolution_chevalleyInvolution P y)

@[simp] lemma coe_nPosEquivNNeg_apply (x : nPos P) :
    (nPosEquivNNeg P x : P.KacMoodyAlgebra) = chevalleyInvolution P x := rfl

/-! ### Twisting by the Chevalley involution -/

/-- A `𝔤(A)`-module `V` with the action twisted by the Chevalley involution:
`x · v = ω(x) v`. -/
@[nolint unusedArguments]
def OmegaTwist (_P : Realization A K H) (V : Type*) : Type _ := V

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

namespace OmegaTwist

instance : AddCommGroup (OmegaTwist P V) := inferInstanceAs (AddCommGroup V)

instance : Module K (OmegaTwist P V) := inferInstanceAs (Module K V)

instance : LieRingModule P.KacMoodyAlgebra (OmegaTwist P V) :=
  LieRingModule.compLieHom V (chevalleyInvolution P)

instance : LieModule K P.KacMoodyAlgebra (OmegaTwist P V) :=
  LieModule.compLieHom V (chevalleyInvolution P)

/-- The identification of `V` with its twist. -/
def of : V ≃ₗ[K] OmegaTwist P V := LinearEquiv.refl K V

variable {P V}

omit [LieModule K P.KacMoodyAlgebra V] in
lemma lie_of (x : P.KacMoodyAlgebra) (v : V) :
    ⁅x, of P V v⁆ = of P V ⁅chevalleyInvolution P x, v⁆ := rfl

end OmegaTwist

/-! ### The twisted Verma module is left-regular over `U(𝔫₊)` -/

variable (Λ : Dual K H)

/-- `M(λ)^ω` is the left-regular `U(𝔫₊)`-module: `u ↦ ω(u) v_λ`. -/
def omegaTwistVermaEquiv :
    LeftRegular K (nPos P) ≃ₗ⁅K,nPos P⁆ OmegaTwist P (VermaModule P Λ) :=
  { ((LeftRegular.equiv K (nPos P)).trans (mapEquiv (nPosEquivNNeg P)).toLinearEquiv).trans
      ((VermaModule.equivEnvNNeg P Λ).trans (OmegaTwist.of P _)) with
    map_lie' := by
      intro x u
      change OmegaTwist.of P _ (VermaModule.equivEnvNNeg P Λ (mapEquiv (nPosEquivNNeg P)
        (UniversalEnvelopingAlgebra.ι K x * LeftRegular.equiv K (nPos P) u))) =
          ⁅(x : P.KacMoodyAlgebra), OmegaTwist.of P _ (VermaModule.equivEnvNNeg P Λ
            (mapEquiv (nPosEquivNNeg P) (LeftRegular.equiv K (nPos P) u)))⁆
      rw [map_mul, mapEquiv_ι, VermaModule.equivEnvNNeg_mul, UniversalEnvelopingAlgebra.map_ι]
      rfl }

/-- `H_q(𝔫₊, M(λ)^ω) = 0` for `q > 0`. -/
theorem subsingleton_homology_omegaTwist_verma (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology K (nPos P) (OmegaTwist P (VermaModule P Λ)) q) :=
  (homologyEquiv (omegaTwistVermaEquiv P Λ) q).toEquiv.subsingleton_congr.mp
    (subsingleton_homology_leftRegular q hq)

/-! ### Duality -/

/-- The roots `nPosBasis` show that `𝔫₊` is the sum of its `𝔥`-weight spaces. -/
theorem iSup_weightSpaceOf_adNPos : ⨆ γ, Module.End.weightSpaceOf (adNPos K P) γ = ⊤ := by
  refine eq_top_iff.mpr fun y _ ↦ ?_
  have hy : y ∈ Submodule.span K (Set.range (nPosBasis P)) := (nPosBasis P).mem_span y
  refine Submodule.span_le.mpr ?_ hy
  rintro _ ⟨x, rfl⟩
  exact Submodule.mem_iSup_of_mem x.root (nPosBasis_mem_weightSpaceOf P P.KacMoodyAlgebra x)

variable {V}

/-- The weight spaces of `V^ω` are those of `V`, with weights negated. -/
lemma weightSpaceOfMap_le_weightSpaceOf_omegaTwist (ν : Dual K H) :
    (weightSpaceOfMap V (h P) ν).map (OmegaTwist.of P V).toLinearMap ≤
      Module.End.weightSpaceOf (nPosDerivAction P (OmegaTwist P V)).φ (-ν) := by
  rintro _ ⟨v, hv, rfl⟩ a
  rw [nPosDerivAction_φ_apply]
  change OmegaTwist.of P V ⁅chevalleyInvolution P (h P a), v⁆ = _
  rw [chevalleyInvolution_h, neg_lie, hv a]
  simp

lemma iSup_weightSpaceOf_omegaTwist (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤) :
    ⨆ ν, Module.End.weightSpaceOf (nPosDerivAction P (OmegaTwist P V)).φ ν = ⊤ := by
  refine eq_top_iff.mpr fun m _ ↦ ?_
  have hm : (OmegaTwist.of P V).symm m ∈ ⨆ ν, weightSpaceOfMap V (h P) ν := hV ▸ trivial
  have : m ∈ (⨆ ν, weightSpaceOfMap V (h P) ν).map (OmegaTwist.of P V).toLinearMap :=
    ⟨_, hm, (OmegaTwist.of P V).apply_symm_apply m⟩
  rw [Submodule.map_iSup] at this
  exact (iSup_mono fun ν ↦ weightSpaceOfMap_le_weightSpaceOf_omegaTwist P ν).trans
    (iSup_le fun ν ↦ le_iSup (fun ν ↦ Module.End.weightSpaceOf
      (nPosDerivAction P (OmegaTwist P V)).φ ν) (-ν)) this

variable (V) in
/-- The evaluation pairing `V^∨ × V^ω → K`. -/
def dualPairing : restrictedDual P V →ₗ[K] OmegaTwist P V →ₗ[K] K :=
  LinearMap.lcomp K K (OmegaTwist.of P V).symm.toLinearMap ∘ₗ
    (TwistedDual.toDual P V).toLinearMap ∘ₗ (restrictedDual P V).subtype

@[simp] lemma dualPairing_apply (φ : restrictedDual P V) (m : OmegaTwist P V) :
    dualPairing P V φ m = TwistedDual.toDual P V φ.1 ((OmegaTwist.of P V).symm m) := rfl

lemma dualPairing_lie (x : P.KacMoodyAlgebra) (φ : restrictedDual P V) (m : OmegaTwist P V) :
    dualPairing P V ⁅x, φ⁆ m = -dualPairing P V φ ⁅x, m⁆ := rfl

lemma dualPairing_injective : Function.Injective (dualPairing P V) := fun _ _ hφψ ↦
  restrictedDual_ext P fun v ↦ LinearMap.congr_fun hφψ (OmegaTwist.of P V v)

lemma mem_range_dualPairing {γ : Dual K H} {ψ : OmegaTwist P V →ₗ[K] K}
    (hψ : ∀ a m, ψ ((nPosDerivAction P (OmegaTwist P V)).φ a m) = γ a * ψ m) :
    ψ ∈ LinearMap.range (dualPairing P V) := by
  let φ : TwistedDual P V := (TwistedDual.toDual P V).symm (ψ ∘ₗ (OmegaTwist.of P V).toLinearMap)
  have hφ : φ ∈ weightSpaceOfMap (TwistedDual P V) (h P) (-γ) := fun a ↦ by
    refine TwistedDual.ext fun v ↦ ?_
    have h1 := hψ a (OmegaTwist.of P V v)
    rw [nPosDerivAction_φ_apply, OmegaTwist.lie_of, chevalleyInvolution_h, neg_lie, map_neg,
      map_neg] at h1
    rw [TwistedDual.lie_apply, transpose_h]
    simp only [φ, LinearEquiv.apply_symm_apply, LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, LinearEquiv.coe_coe]
    rw [neg_eq_iff_eq_neg.mp h1]
    simp
  exact ⟨⟨φ, (mem_restrictedDual P).mpr (Submodule.mem_iSup_of_mem _ hφ)⟩, rfl⟩

/-- **Weight cocycles of positive degree on `M(λ)^∨` are coboundaries** (the vanishing step of
Humphreys GSM 94 Prop. 6.15 (b)). -/
theorem exists_δ_eq_dualVerma {k : ℕ} {μ : Dual K H}
    {f : Cochains K (nPos P) (restrictedDual P (VermaModule P Λ)) (k + 1)}
    (hf : f ∈ (nPosDerivAction P (restrictedDual P (VermaModule P Λ))).cochainWeightSpace
      (k + 1) μ)
    (hδ : δ K (nPos P) _ (k + 1) f = 0) :
    ∃ g ∈ (nPosDerivAction P (restrictedDual P (VermaModule P Λ))).cochainWeightSpace k μ,
      δ K (nPos P) _ k g = f :=
  (nPosDerivAction P (OmegaTwist P (VermaModule P Λ))).exists_δ_eq_of_subsingleton_homology
    (ρN := nPosDerivAction P (restrictedDual P (VermaModule P Λ))) (fun _ ↦ rfl)
    (fun x φ m ↦ dualPairing_lie P (x : P.KacMoodyAlgebra) φ m)
    (fun a φ m ↦ dualPairing_lie P (h P a) φ m) (dualPairing_injective P)
    (fun _ _ hψ ↦ mem_range_dualPairing P hψ) (iSup_weightSpaceOf_adNPos P)
    (iSup_weightSpaceOf_omegaTwist P
      (VermaModule.isCategoryO P Λ).iSup_weightSpaceOfMap_eq_top)
    (subsingleton_homology_omegaTwist_verma P Λ (k + 1) k.succ_pos) hf hδ

/-- **`H^n(𝔫, M(λ)^∨)_μ = 0` for `n > 0`** (Humphreys GSM 94 Prop. 6.15 (b), vanishing part). -/
theorem isZero_nPosCohomology_dualVerma (μ : Dual K H) {n : ℕ} (hn : 0 < n) :
    IsZero (nPosCohomology P (restrictedDual P (VermaModule P Λ)) μ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add]
  exact (nPosDerivAction P _).isZero_weightComplex_homology_succ fun f hf hδ ↦
    exists_δ_eq_dualVerma P Λ hf hδ

end Matrix.Realization.KacMoodyAlgebra
