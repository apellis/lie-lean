/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.Cocycle
import LieLean.Algebra.Lie.KacMoody.Kostant.Euler

/-!
# Kostant's Laplacian acts by scalars on the weight spaces of the chains

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` with a standard invariant form,
and `V` a `𝔤`-module in the category `𝒪` on which the Casimir operator `Ω` acts by a scalar `κ`
(e.g. `V = L(Λ)`, `κ = (Λ + 2ρ|Λ)`). Kostant's Laplacian `□ = dδ + δd` on the chains
`⋀𝔫₋ ⊗ V` (`IsStandardForm.kostantLaplacian`) acts on the weight-`μ` chains by the scalar

  `s(μ) = ½(κ - (μ + 2ρ|μ))`.

Consequently (`δ` being a contracting homotopy on the eigenspaces of `□` with nonzero eigenvalue)
`H_k(𝔫₋, V)_μ = 0` unless `(μ + 2ρ|μ) = κ`.

*Proof (reconstructed).* For a root vector `y ∈ 𝔤_{-β}`, Kostant's identity
`R(y) := [□, ε(y)] = ε(y) ∘ (θ(ν⁻¹β) + (ρ|β) - ½(β|β))` holds on all chains: on `1 ⊗ v` this is
`laplacianComm_one_tmul_eq`, and both sides satisfy the same recursion
`R(y) ε(z) = -ε(z) R(y) + X(y, z)` with `X(y, z) = ε(y) ε([ν⁻¹β, z])`
(`laplacianComm_wedge`, `kostantG_lie_sub_lieAction`). On `1 ⊗ v`, `v ∈ V_ν`,
`□(1 ⊗ v) = d δ₀ v = 1 ⊗ ∑_{α>0} ∑ₖ e_{-α}^{(k)} e_α^{(k)} v = ½(κ - (ν + 2ρ|ν)) (1 ⊗ v)` by the
formula for `Ω`. Inductively, if `c` has weight `μ` and `□ c = s(μ) c`, then
`□(y ∧ c) = y ∧ □c + R(y) c = (s(μ) + (μ|β) + (ρ|β) - ½(β|β)) (y ∧ c) = s(μ - β) (y ∧ c)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.laplacianComm_kostant_eq`: Kostant's
  identity `[□, ε(y)] = ε(y) ∘ (θ(ν⁻¹β) + (ρ|β) - ½(β|β))` for `y ∈ 𝔤_{-β}`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantLaplacian_eq_smul`: `□` acts on the
  weight-`μ` chains by `½(κ - (μ + 2ρ|μ))`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.homologyWeightSpace_eq_bot`:
  `H_k(𝔫₋, V)_μ = 0` unless `(μ + 2ρ|μ) = κ`.

## References

* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387, Thm. 4.4, Thm. 5.7, Cor. 5.7 (semisimple `𝔤`).
* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76, Prop. 7.9, Lemma A.1 (vanishing off the Casimir sphere, by a
  Casimir argument in place of Kostant's Laplacian).
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, proof of Thm. 3.2.7, Thm. 3.4.2, Cor. 3.4.11.
* The arguments above are our own.
-/

open Module LieModule LieModule.ChevalleyEilenberg TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The map `z ↦ G([y, z]) c - [θ(y), G(z)] c + [θ(z), G(y)] c`, linear in `z`. -/
def cocycleMap (G : L →ₗ[R] Module.End R (ExteriorAlgebra R L ⊗[R] M)) (y : L)
    (c : ExteriorAlgebra R L ⊗[R] M) : L →ₗ[R] ExteriorAlgebra R L ⊗[R] M where
  toFun z := G ⁅y, z⁆ c - (lieAction R L M y (G z c) - G z (lieAction R L M y c)) +
    (lieAction R L M z (G y c) - G y (lieAction R L M z c))
  map_add' z z' := by
    simp only [lie_add, map_add, LinearMap.add_apply]
    abel
  map_smul' r z := by
    simp only [lie_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply]
    module

lemma cocycleMap_apply (G : L →ₗ[R] Module.End R (ExteriorAlgebra R L ⊗[R] M)) (y : L)
    (c : ExteriorAlgebra R L ⊗[R] M) (z : L) :
    cocycleMap G y c z = G ⁅y, z⁆ c - (lieAction R L M y (G z c) - G z (lieAction R L M y c)) +
      (lieAction R L M z (G y c) - G y (lieAction R L M z c)) := rfl

omit [LieRingModule L M] [LieModule R L M] in
/-- The algebra behind the inductive step of `laplacianComm_kostant_eq`. -/
lemma neg_wedge_add_wedge_eq (θ' : Module.End R (ExteriorAlgebra R L ⊗[R] M)) (D : L →ₗ[R] L)
    (s : R) (y z : L) (c : ExteriorAlgebra R L ⊗[R] M)
    (hθ' : θ' (wedge R L M z c) = wedge R L M (D z) c + wedge R L M z (θ' c)) :
    -wedge R L M z ((wedge R L M y ∘ₗ (θ' + s • LinearMap.id)) c) +
        wedge R L M y (wedge R L M (D z) c) =
      (wedge R L M y ∘ₗ (θ' + s • LinearMap.id)) (wedge R L M z c) := by
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    hθ', map_add, map_smul, wedge_wedge_comm z y, smul_neg, neg_add, neg_neg]
  abel

omit [LieRingModule L M] [LieModule R L M] in
lemma wedge_smul_add_eq (θ' : Module.End R (ExteriorAlgebra R L ⊗[R] M)) (s t u : R) (y : L)
    (c : ExteriorAlgebra R L ⊗[R] M) (hc : θ' c = t • c) :
    wedge R L M y (s • c) + (wedge R L M y ∘ₗ (θ' + u • LinearMap.id)) c =
      (s + t + u) • wedge R L M y c := by
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    hc, map_add, map_smul, add_smul, add_assoc]

end LieModule.ChevalleyEilenberg

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {S : A.Symmetrization} {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

namespace IsStandardForm

variable (hB : IsStandardForm P S B)
include hB

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- The cocycle identity of `kostantG_lie_sub_lieAction` for arbitrary `z ∈ 𝔫₋`. -/
theorem kostantG_lie_sub_lieAction' {β : Dual K H} (hβ : β ∈ P.posWeights) (y : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β)) (z : nNeg P)
    (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantG V ⁅y, z⁆ c -
        (lieAction K (nNeg P) V y (hB.kostantG V z c) -
          hB.kostantG V z (lieAction K (nNeg P) V y c)) +
        (lieAction K (nNeg P) V z (hB.kostantG V y c) -
          hB.kostantG V y (lieAction K (nNeg P) V z c)) =
      wedge K (nNeg P) V y (wedge K (nNeg P) V (adNNeg P ((P.toDual S).symm β) z) c) := by
  have h : cocycleMap (hB.kostantG V) y c = wedge K (nNeg P) V y ∘ₗ
      (wedge K (nNeg P) V).flip c ∘ₗ adNNeg P ((P.toDual S).symm β) :=
    (nNegBasis P).ext fun i ↦ hB.kostantG_lie_sub_lieAction V hβ i.1.2 y (nNegBasis P i) hy
      (nNegBasis_mem P i) c
  exact LinearMap.congr_fun h z

/-- **Kostant's identity** (reconstructed): for a root vector `y ∈ 𝔤_{-β}` (`β > 0`), the
commutator `R(y) = [□, ε(y)]` equals `ε(y) ∘ (θ(ν⁻¹β) + (ρ|β) - ½(β|β))`, where `θ` is the action
of `𝔥` on the chains. -/
theorem laplacianComm_kostant_eq (hA : A.IsGeneralizedCartan) (hV : IsPosFinite P V)
    {β : Dual K H} (hβ : β ∈ P.posWeights) (y : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β)) :
    laplacianComm (hB.kostantCoDiff₀ V hV) (hB.kostantG V)
        (fun y ↦ hB.kostantG_comp_wedge V y y) y =
      wedge K (nNeg P) V y ∘ₗ ((nNegDerivAction P V).θ ((P.toDual S).symm β) +
        (P.dualBilinForm S P.rho β - (2 : K)⁻¹ * P.dualBilinForm S β β) • LinearMap.id) := by
  refine ext_of (fun v ↦ (hB.laplacianComm_one_tmul_eq V hA hV hβ y hy v).trans ?_)
    fun z c hc ↦ ?_
  · simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, DerivAction.θ_one_tmul, tmul_add, tmul_smul]
    rfl
  · refine (laplacianComm_wedge _ _ _ (fun y z ↦ hB.kostantG_comp_wedge V y z) y z c).trans ?_
    refine (congrArg₂ (· + ·) (congrArg (-wedge K (nNeg P) V z ·) hc)
      ((cocycleMap_apply _ _ _ _).symm.trans
        (hB.kostantG_lie_sub_lieAction' V hβ y hy z c))).trans ?_
    exact neg_wedge_add_wedge_eq _ (adNNeg P ((P.toDual S).symm β)) _ y z c
      ((nNegDerivAction P V).θ_wedge _ z c)

omit hB [FiniteDimensional K H] in
lemma diff_wedgeProj_one_tmul {f : P.KacMoodyAlgebra} (hf : f ∈ nNeg P) (m : V) :
    diff K (nNeg P) V (wedgeProj V f (1 ⊗ₜ m)) = -(1 ⊗ₜ ⁅f, m⁆) := by
  rw [wedgeProj_apply, nNegProj_of_mem hf, diff_wedge_one_tmul]
  rfl

lemma diff_coDiffTerm {α : Dual K H} (hα : α ∈ P.posWeights) (v : V) :
    diff K (nNeg P) V (hB.coDiffTerm V α v) = -(1 ⊗ₜ hB.casimirTerm V α v) := by
  rw [coDiffTerm, casimirTerm_apply, casimirSum_def, casimirSum_def, map_sum, tmul_sum,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ diff_wedgeProj_one_tmul V
    (rootSpace_le_nNeg ((neg_mem_negWeights_iff P).mpr hα) (hB.dualBasis_mem α k)) _

/-- `d δ₀ v = 1 ⊗ ∑_{α > 0} ∑ₖ e_{-α}^{(k)} e_α^{(k)} v`. -/
lemma diff_kostantCoDiff₀ (hV : IsPosFinite P V) (v : V) :
    diff K (nNeg P) V (hB.kostantCoDiff₀ V hV v) =
      1 ⊗ₜ ∑ᶠ α ∈ P.posWeights, hB.casimirTerm V α v := by
  rw [kostantCoDiff₀_apply, map_neg, map_finsum_mem_of_finite _ (hB.finite_coDiffTerm V hV v),
    finsum_mem_congr rfl fun α hα ↦ hB.diff_coDiffTerm V hα v, finsum_mem_neg, neg_neg]
  exact (map_finsum_mem_of_finite (TensorProduct.mk K (ExteriorAlgebra K (nNeg P)) V 1)
    (hB.finite_casimirTerm hV v)).symm

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional K H] hB in
private lemma eq_smul_of_casimir {M : Type*} [AddCommGroup M] [Module K M] (x v : M)
    (a b κ : K) (h : (2 : K) • (a • v) + b • v + (2 : K) • x = κ • v) :
    x = ((2 : K)⁻¹ * (κ - (b + 2 * a))) • v := by
  have h2 : (2 : K) • x = (κ - (b + 2 * a)) • v := by
    rw [sub_smul, ← h]; module
  rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- `∑_{α > 0} ∑ₖ e_{-α}^{(k)} e_α^{(k)} v = ½(κ - (ν + 2ρ|ν)) v` for a weight vector `v` of
weight `ν` on which the Casimir operator acts by `κ`. -/
lemma finsum_casimirTerm_eq_smul (hV : IsPosFinite P V) {ν : Dual K H} {v : V}
    (hv : v ∈ weightSpace P V ν) {κ : K} (hΩ : hB.casimir V hV v = κ • v) :
    ∑ᶠ α ∈ P.posWeights, hB.casimirTerm V α v =
      ((2 : K)⁻¹ * (κ - P.dualBilinForm S (ν + 2 • P.rho) ν)) • v := by
  rw [casimir_apply, hB.casimirTerm_zero_apply hv, hv, hv] at hΩ
  convert eq_smul_of_casimir _ v _ _ κ hΩ using 4
  rw [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, dualBilinForm_apply_eq,
    (P.isSymm_dualBilinForm S).eq P.rho ν, dualBilinForm_apply_eq]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]

/-- The Laplacian on `1 ⊗ v` for a weight vector `v` of weight `ν` with `Ω v = κ v`:
`□ (1 ⊗ v) = ½(κ - (ν + 2ρ|ν)) (1 ⊗ v)`. -/
lemma kostantLaplacian_one_tmul (hV : IsPosFinite P V) {ν : Dual K H} {v : V}
    (hv : v ∈ weightSpace P V ν) {κ : K} (hΩ : hB.casimir V hV v = κ • v) :
    hB.kostantLaplacian V hV (1 ⊗ₜ v) =
      ((2 : K)⁻¹ * (κ - P.dualBilinForm S (ν + 2 • P.rho) ν)) • (1 ⊗ₜ v) := by
  rw [kostantLaplacian, laplacian_one_tmul, diff_kostantCoDiff₀,
    hB.finsum_casimirTerm_eq_smul V hV hv hΩ, tmul_smul]

omit hB [DecidableEq ι] in
/-- The eigenvalue `s(μ) = ½(κ - (μ + 2ρ|μ))` satisfies
`s(μ - β) = s(μ) + (μ|β) + (ρ|β) - ½(β|β)`. -/
private lemma scalar_sub (κ : K) (β μ : Dual K H) :
    (2 : K)⁻¹ * (κ - P.dualBilinForm S (-β + μ + 2 • P.rho) (-β + μ)) =
      (2 : K)⁻¹ * (κ - P.dualBilinForm S (μ + 2 • P.rho) μ) + μ ((P.toDual S).symm β) +
        (P.dualBilinForm S P.rho β - (2 : K)⁻¹ * P.dualBilinForm S β β) := by
  rw [← dualBilinForm_apply_eq]
  have h1 := (P.isSymm_dualBilinForm S).eq β μ
  simp only [map_add, map_neg, map_nsmul, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, h1]
  ring

/-- The inductive step for `kostantLaplacian_eq_smul`. -/
lemma kostantLaplacian_wedge_eq (hA : A.IsGeneralizedCartan) (hV : IsPosFinite P V) (κ : K)
    (i : NegRootIndex P) (μ : Dual K H) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    (hc : c ∈ (nNegDerivAction P V).chainWeightSpace μ)
    (hTc : hB.kostantLaplacian V hV c =
      ((2 : K)⁻¹ * (κ - P.dualBilinForm S (μ + 2 • P.rho) μ)) • c) :
    hB.kostantLaplacian V hV (wedge K (nNeg P) V (nNegBasis P i) c) =
      ((2 : K)⁻¹ * (κ - P.dualBilinForm S (-i.root + μ + 2 • P.rho) (-i.root + μ))) •
        wedge K (nNeg P) V (nNegBasis P i) c := by
  have hR := LinearMap.congr_fun (hB.laplacianComm_kostant_eq V hA hV i.1.2
    (nNegBasis P i) (nNegBasis_mem P i)) c
  refine (laplacian_wedge _ _ _ (nNegBasis P i) c).trans
    ((congrArg₂ (· + ·) (congrArg (wedge K (nNeg P) V (nNegBasis P i)) hTc) hR).trans ?_)
  exact (wedge_smul_add_eq _ _ _ _ _ _ (DerivAction.mem_chainWeightSpace.mp hc _)).trans
    (congrArg (· • _) (scalar_sub κ i.root μ).symm)

/-- **Kostant's Laplacian acts by scalars on weight spaces** (reconstructed; cf. [GL] Appendix):
if `V` is in the category `𝒪` and the Casimir operator acts on `V` by the scalar `κ`, then `□`
acts on the weight-`μ` chains by `½(κ - (μ + 2ρ|μ))`. -/
theorem kostantLaplacian_eq_smul (hA : A.IsGeneralizedCartan) (hV : IsCategoryO P V) {κ : K}
    (hΩ : ∀ v, hB.casimir V hV.isPosFinite v = κ • v) {μ : Dual K H}
    {c : ExteriorAlgebra K (nNeg P) ⊗[K] V} (hc : c ∈ (nNegDerivAction P V).chainWeightSpace μ) :
    hB.kostantLaplacian V hV.isPosFinite c =
      ((2 : K)⁻¹ * (κ - P.dualBilinForm S (μ + 2 • P.rho) μ)) • c :=
  DerivAction.apply_eq_smul_of_mem_chainWeightSpace (nNegBasis P) hV.weightBasis
    (nNegBasis_mem_weightSpaceOf P) hV.weightBasis_mem_weightSpaceOf _
    (fun μ ↦ (2 : K)⁻¹ * (κ - P.dualBilinForm S (μ + 2 • P.rho) μ))
    (fun j ↦ hB.kostantLaplacian_one_tmul V hV.isPosFinite (hV.weightBasis_mem j) (hΩ _))
    (hB.kostantLaplacian_wedge_eq V hA hV.isPosFinite κ) hc

/-- **Vanishing of `𝔫₋`-homology off the Casimir sphere** (reconstructed; [GL] Prop. 7.9,
[Kum] Cor. 3.4.11 and proof of Thm. 3.2.7, for `V = L(Λ)`): if `V` is in the category `𝒪`
and the Casimir operator acts on `V` by the scalar `κ`, then `H_k(𝔫₋, V)_μ = 0` unless
`(μ + 2ρ|μ) = κ`. ([GL] state this for `V = L(Λ)`, `Λ` dominant integral, and prove it with the
Casimir operator, not Kostant's Laplacian.) -/
theorem homologyWeightSpace_eq_bot (hA : A.IsGeneralizedCartan) (hV : IsCategoryO P V) {κ : K}
    (hΩ : ∀ v, hB.casimir V hV.isPosFinite v = κ • v) (k : ℕ) {μ : Dual K H}
    (hμ : P.dualBilinForm S (μ + 2 • P.rho) μ ≠ κ) :
    (nNegDerivAction P V).homologyWeightSpace k μ = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨c, ⟨hcZ, hcμ⟩, rfl⟩
  refine (Submodule.mem_bot K).mpr ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
  refine mem_boundaries_of_laplacian_eq_smul _ _ _
    (fun _ _ hc ↦ hB.kostantCoDiff_mem_chainsIn V hV.isPosFinite hc) hcZ ?_
    (hB.kostantLaplacian_eq_smul V hA hV hΩ hcμ)
  exact mul_ne_zero (inv_ne_zero two_ne_zero) (sub_ne_zero.mpr hμ.symm)

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
