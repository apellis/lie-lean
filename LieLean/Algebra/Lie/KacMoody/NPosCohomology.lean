/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.CochainWeights
import LieLean.Algebra.Lie.KacMoody.CharacterVerma
import LieLean.Algebra.Lie.KacMoody.VermaHom

/-!
# The weight spaces of `𝔫`-cohomology

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra with Cartan subalgebra `𝔥` and positive nilpotent
subalgebra `𝔫 = 𝔫₊`, and let `V` be a `𝔤`-module. Since `[𝔥, 𝔫] ⊆ 𝔫`, `𝔥` acts on the
Chevalley–Eilenberg cochain complex `C^•(𝔫, V) = Hom(⋀^•𝔫, V)` compatibly with the
codifferential, and the weight-`μ` cochains form a subcomplex `C^•(𝔫, V)_μ`
(`LieModule.ChevalleyEilenberg.DerivAction.weightComplex`). Its cohomology is the weight space
`H^n(𝔫, V)_μ` of [HumO] Prop. 6.15 (b).

We choose a basis of `𝔫` consisting of root vectors, `𝔫 = ⊕_{α ∈ Q₊ \ 0} 𝔤_α`, so that the
weight-`μ` cochains are described by `cochainWeightEquiv`, and we identify the degree-zero part:
a weight-`μ` cocycle of degree `0` is a primitive vector of weight `μ`, so
`H^0(𝔫, V)_μ ≅ Hom_𝔤(M(μ), V)`, the case `n = 0` of [HumO] Prop. 6.15 (b).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.nPosBasis`: a basis of `𝔫` consisting of root vectors.
* `Matrix.Realization.KacMoodyAlgebra.nPosDerivAction`: the action of `𝔥` on `𝔫` and on `V`.
* `Matrix.Realization.KacMoodyAlgebra.nPosCohomology`: `H^n(𝔫, V)_μ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.isInternal_nPosRootSpace`: `𝔫 = ⊕_{α > 0} 𝔤_α`.
* `Matrix.Realization.KacMoodyAlgebra.nPosCocycleZeroEquiv`: the weight-`μ` cocycles of degree
  `0` are the primitive vectors of weight `μ`.
* `Matrix.Realization.KacMoodyAlgebra.nPosCohomologyZeroPrimEquiv`: `H^0(𝔫, V)_μ` is the space
  of primitive vectors of weight `μ`.
* `Matrix.Realization.KacMoodyAlgebra.nPosCohomologyZeroEquiv`:
  `H^0(𝔫, V)_μ ≅ Hom_𝔤(M(μ), V)`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.15.
-/

open Module LieModule LieModule.ChevalleyEilenberg CategoryTheory

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### A basis of `𝔫` consisting of root vectors -/

/-- The inclusion `𝔫 → 𝔤`, as a linear map. -/
abbrev nPosIncl : nPos P →ₗ[K] P.KacMoodyAlgebra := (nPos P).incl

lemma range_nPosIncl : LinearMap.range (nPosIncl P) = (nPos P).toSubmodule := by
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

lemma nPosIncl_injective : Function.Injective (nPosIncl P) := Subtype.val_injective

variable [CharZero K]

lemma rootSpace_le_nPos {α : Dual K H} (hα : α ∈ P.posWeights) :
    rootSpace P α ≤ (nPos P).toSubmodule := by
  rw [nPos_toSubmodule_eq]
  exact le_iSup₂ (f := fun μ (_ : μ ∈ P.posWeights) ↦ rootSpace P μ) _ hα

/-- The root space `𝔤_α`, `α ∈ Q₊ \ 0`, as a subspace of `𝔫`. -/
def nPosRootSpace (α : P.posWeights) : Submodule K (nPos P) :=
  (rootSpace P (α : Dual K H)).comap (nPosIncl P)

lemma map_nPosRootSpace (α : P.posWeights) :
    (nPosRootSpace P α).map (nPosIncl P) = rootSpace P (α : Dual K H) := by
  rw [nPosRootSpace, Submodule.map_comap_eq, range_nPosIncl]
  exact inf_eq_right.mpr (rootSpace_le_nPos P α.2)

open Classical in
/-- The root space decomposition `𝔫 = ⊕_{α ∈ Q₊ \ 0} 𝔤_α` ([Kac] §1.3). -/
theorem isInternal_nPosRootSpace : DirectSum.IsInternal (nPosRootSpace P) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · refine iSupIndep.of_map (nPosIncl_injective P) ?_
    simp_rw [map_nPosRootSpace]
    exact (iSupIndep_weightSpaceOfMap (M := P.KacMoodyAlgebra) (h P)).comp
      (f := fun α : P.posWeights ↦ (α : Dual K H)) fun α β hαβ ↦ Subtype.ext hαβ
  · apply Submodule.map_injective_of_injective (nPosIncl_injective P)
    rw [Submodule.map_iSup, Submodule.map_top, range_nPosIncl, nPos_toSubmodule_eq]
    simp_rw [map_nPosRootSpace]
    refine le_antisymm (iSup_le fun α ↦ ?_) (iSup₂_le fun μ hμ ↦ ?_)
    · exact le_iSup₂ (f := fun μ (_ : μ ∈ P.posWeights) ↦ rootSpace P μ) _ α.2
    · exact le_iSup (fun α : P.posWeights ↦ rootSpace P (α : Dual K H)) ⟨μ, hμ⟩

instance (α : P.posWeights) : FiniteDimensional K (nPosRootSpace P α) := by
  have := finiteDimensional_rootSpace P α.2
  rw [← map_nPosRootSpace] at this
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (nPosIncl_injective P) (nPosRootSpace P α)).symm

lemma finrank_nPosRootSpace (α : P.posWeights) :
    finrank K (nPosRootSpace P α) = finrank K (rootSpace P (α : Dual K H)) := by
  rw [← map_nPosRootSpace, LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (nPosIncl_injective P) (nPosRootSpace P α))]

/-- The index set `{(α, j) | α ∈ Q₊ \ 0, j < dim 𝔤_α}` of a basis of `𝔫` consisting of root
vectors. -/
def PosRootIndex : Type _ :=
  Σ α : P.posWeights, Fin (finrank K (rootSpace P (α : Dual K H)))

/-- An (arbitrary) linear order on `PosRootIndex`. -/
instance : LinearOrder (PosRootIndex P) := IsWellOrder.linearOrder WellOrderingRel

/-- The positive root `α` attached to an index `(α, j)`. -/
def PosRootIndex.root {P : Realization A K H} (x : PosRootIndex P) : Dual K H := x.1

open Classical in
/-- A basis of `𝔫` consisting of root vectors: the basis vector of index `(α, j)` lies in
`𝔤_α`. -/
def nPosBasis : Basis (PosRootIndex P) K (nPos P) :=
  (isInternal_nPosRootSpace P).collectedBasis fun α ↦
    Module.finBasisOfFinrankEq K _ (finrank_nPosRootSpace P α)

open Classical in
lemma nPosBasis_mem (x : PosRootIndex P) :
    ((nPosBasis P x : nPos P) : P.KacMoodyAlgebra) ∈ rootSpace P x.root :=
  (isInternal_nPosRootSpace P).collectedBasis_mem
    (fun α ↦ Module.finBasisOfFinrankEq K _ (finrank_nPosRootSpace P α)) x

/-! ### The action of `𝔥` -/

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

variable (K) in
/-- `ad a` restricted to `𝔫`, for `a ∈ 𝔥`, as a linear map in `a`. -/
def adNPos : H →ₗ[K] Module.End K (nPos P) where
  toFun a :=
    { toFun x := ⟨⁅h P a, (x : P.KacMoodyAlgebra)⁆, lie_h_mem_nPos P a x.2⟩
      map_add' _ _ := Subtype.ext (lie_add _ _ _)
      map_smul' _ _ := Subtype.ext (lie_smul _ _ _) }
  map_add' a b := LinearMap.ext fun x ↦ Subtype.ext (by simp [add_lie])
  map_smul' c a := LinearMap.ext fun x ↦ Subtype.ext (by simp [smul_lie])

omit [CharZero K] in
@[simp] lemma coe_adNPos_apply (a : H) (x : nPos P) :
    (adNPos K P a x : P.KacMoodyAlgebra) = ⁅h P a, (x : P.KacMoodyAlgebra)⁆ := rfl

/-- The action of `𝔥` on `𝔫` (by `ad`) and on a `𝔤`-module `V`, compatible with the action of
`𝔫` on `V`. -/
def nPosDerivAction : DerivAction K H (nPos P) V where
  D := adNPos K P
  φ := (toEnd K P.KacMoodyAlgebra V : P.KacMoodyAlgebra →ₗ[K] Module.End K V) ∘ₗ h P
  D_lie a x y := Subtype.ext (leibniz_lie (h P a) (x : P.KacMoodyAlgebra) (y : P.KacMoodyAlgebra))
  φ_lie a x v := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap, toEnd_apply_apply,
      LieSubalgebra.coe_bracket_of_module, coe_adNPos_apply]
    exact leibniz_lie _ _ _

omit [CharZero K] in
@[simp] lemma nPosDerivAction_φ_apply (a : H) (v : V) :
    (nPosDerivAction P V).φ a v = ⁅h P a, v⁆ := rfl

omit [CharZero K] in
/-- The weight spaces of `V` for the action of `𝔥` are the usual weight spaces. -/
lemma weightSpaceOf_nPosDerivAction_φ (ν : Dual K H) :
    Module.End.weightSpaceOf (nPosDerivAction P V).φ ν = weightSpaceOfMap V (h P) ν := rfl

/-- The root vectors `nPosBasis` are weight vectors for the action of `𝔥` on `𝔫`. -/
lemma nPosBasis_mem_weightSpaceOf (x : PosRootIndex P) :
    nPosBasis P x ∈ Module.End.weightSpaceOf (nPosDerivAction P V).D x.root :=
  fun a ↦ Subtype.ext (by
    rw [show ((nPosDerivAction P V).D a (nPosBasis P x) : P.KacMoodyAlgebra) =
      ⁅h P a, (nPosBasis P x : P.KacMoodyAlgebra)⁆ from rfl]
    simpa using nPosBasis_mem P x a)

/-! ### Cohomology -/

variable (μ : Dual K H) in
/-- The weight space `H^n(𝔫, V)_μ` of the cohomology of `𝔫 = 𝔫₊` with coefficients in `V`,
the cohomology of the weight-`μ` cochain complex. -/
abbrev nPosCohomology (n : ℕ) : ModuleCat K :=
  ((nPosDerivAction P V).weightComplex μ).homology n

variable {P V}

variable (P V) in
/-- **The weight-`μ` cocycles of degree `0` are the primitive vectors of weight `μ`**:
`f ↦ f(1)`. -/
def nPosCocycleZeroEquiv (μ : Dual K H) :
    LinearMap.ker ((nPosDerivAction P V).δWeight 0 μ) ≃ₗ[K] primitiveVectors P V μ where
  toFun f := ⟨(f.1 : Cochains K (nPos P) V 0) ⟨1, by simp⟩, mem_primitiveVectors.mpr
    ⟨(nPosDerivAction P V).mem_cochainWeightSpace_zero_iff.mp f.1.2, fun i ↦ by
      have h : δ K (nPos P) V 0 f.1 = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.mp f.2)
      exact δ_zero_eq_zero_iff.mp h ⟨e P i, e_mem_nPos P i⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨⟨cochainZero K (nPos P) (v : V),
      (nPosDerivAction P V).mem_cochainWeightSpace_zero_iff.mpr (by
      rw [cochainZero_one]; exact (mem_primitiveVectors.mp v.2).1)⟩,
    LinearMap.mem_ker.mpr (Subtype.ext (δ_zero_eq_zero_iff.mpr fun x ↦ by
      change ⁅(x : P.KacMoodyAlgebra), cochainZero K (nPos P) (v : V) ⟨1, by simp⟩⁆ = 0
      rw [cochainZero_one]
      exact lie_eq_zero_of_mem_nPos (mem_primitiveVectors.mp v.2).2 x.2))⟩
  left_inv f := Subtype.ext (Subtype.ext (cochainZero_apply_one _))
  right_inv v := Subtype.ext (cochainZero_one _)

omit [CharZero K] in
@[simp] lemma nPosCocycleZeroEquiv_apply (μ : Dual K H)
    (f : LinearMap.ker ((nPosDerivAction P V).δWeight 0 μ)) :
    (nPosCocycleZeroEquiv P V μ f : V) = (f.1 : Cochains K (nPos P) V 0) ⟨1, by simp⟩ := rfl

variable (P V) in
/-- **`H^0(𝔫, V)_μ` is the space of primitive vectors of weight `μ`**. -/
def nPosCohomologyZeroPrimEquiv (μ : Dual K H) :
    nPosCohomology P V μ 0 ≃ₗ[K] primitiveVectors P V μ :=
  (((CochainComplex.isoHomologyπ₀ _).symm ≪≫
    ((nPosDerivAction P V).weightComplex μ).cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    (((nPosDerivAction P V).weightComplex μ).sc' 0 0 1).moduleCatCyclesIso).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (by
      change LinearMap.ker (((nPosDerivAction P V).weightComplex μ).d 0 (0 + 1)).hom = _
      rw [DerivAction.weightComplex_d]
      rfl))).trans (nPosCocycleZeroEquiv P V μ)

variable (P V) in
/-- **[HumO] Prop. 6.15 (b) in degree `0`**: `H^0(𝔫, V)_μ ≅ Hom_𝔤(M(μ), V)`. -/
def nPosCohomologyZeroEquiv (μ : Dual K H) :
    nPosCohomology P V μ 0 ≃ₗ[K] (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) :=
  (nPosCohomologyZeroPrimEquiv P V μ).trans (VermaModule.homEquiv P V μ).symm

end Matrix.Realization.KacMoodyAlgebra
