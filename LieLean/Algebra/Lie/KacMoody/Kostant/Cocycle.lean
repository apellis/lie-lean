/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.LaplacianIdentity

/-!
# Kostant's identity: the cocycle term

With the notation of `LieLean.Algebra.Lie.KacMoody.Kostant.Identity` (`θ` the action of `𝔫₋` on
the chains `⋀𝔫₋ ⊗ V`, `ε(y)` left multiplication, `G(y)` Kostant's operators, `π : 𝔤 → 𝔫₋` the
projection along the Borel subalgebra), the commutator of the Laplacian with `ε(y)` satisfies
`[□, ε(y)] ε(z) = -ε(z) [□, ε(y)] + X(y, z)` (`laplacianComm_wedge`), where
`X(y, z) = G([y, z]) - [θ(y), G(z)] + [θ(z), G(y)]`. We prove that for root vectors
`y ∈ 𝔤_{-β}`, `z ∈ 𝔤_{-γ}` (`β, γ > 0`)

  `X(y, z) = ε(y) ε([ν⁻¹(β), z])`.

*Proof (reconstructed).* Expanding with dual bases, `2[θ(y), G(z)] = ∑_α (A_α(y, z) + B_α(y, z))`
with `A_α(y, z) = ∑ₖ ε([y, π e_{-α}]) ε(π[e_α, z])` and
`B_α(y, z) = ∑ₖ ε(π e_{-α}) ε([y, π[e_α, z]])`, and by the Jacobi identity
`2G([y, z]) = ∑_α (L_α + R_α)` with `L_α = ∑ₖ ε(π e_{-α}) ε(π[[e_α, y], z])` and
`R_α = ∑ₖ ε(π e_{-α}) ε(π[y, [e_α, z]])`. Split `∑_{α > 0} L_α` as in
`finsum_casimirSum_lie_eq` into the term `α = β`, which is `ε(y) ε([ν⁻¹β, z])`
(`casimirSum_lie_self`), the terms `α + β` with `α > 0`, which by [Kac] Lemma 2.4
(`casimirSum_lie_left`) equal `A_α(y, z)`, and the terms `0 < α < β`, which equal `-B_α(z, y)`.
Similarly `∑_α R_α = (β|γ) ε(z) ε(y) - ∑_α A_α(z, y) + ∑_α B_α(y, z)`. Since
`[ν⁻¹β, z] = -(β|γ) z` and `ε(z) ε(y) = -ε(y) ε(z)`, all the terms `A`, `B` cancel in `X(y, z)`
and the two remaining terms are both equal to `ε(y) ε([ν⁻¹β, z])`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantG_lie_sub_lieAction`: the identity
  `X(y, z) = ε(y) ε([ν⁻¹(β), z])`.

## References

* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387 (cf. §4, Thm. 4.4).
* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76 (a Casimir argument, §7 and Appendix, in place of Kostant's
  Laplacian).
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Lemma 2.4.
* The computation above is reconstructed by us; the sources were not consulted.
-/

open Module LieModule LieModule.ChevalleyEilenberg TensorProduct ExteriorAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {S : A.Symmetrization} {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

omit [Fintype ι] [DecidableEq ι] in
private lemma half_combination {M : Type*} [AddCommGroup M] [Module K M] (w w' a b c d : M)
    (hw : w' = w) :
    (2 : K)⁻¹ • ((w + a - d) + (w' - b + c)) - (2 : K)⁻¹ • (a + c) + (2 : K)⁻¹ • (b + d) =
      w := by
  subst hw
  module

namespace IsStandardForm

variable (hB : IsStandardForm P S B)
include hB

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- The term `∑ₖ ε([y, π e_{-α}]) ε(π[e_α, z]) c` of `[θ(y), G(z)] c`. -/
def cocycleTermA (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) (α : Dual K H) :
    ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  hB.casimirSum (fun f e ↦ wedge K (nNeg P) V ⁅y, nNegProj P f⁆
    (wedgeProj V ⁅e, (z : P.KacMoodyAlgebra)⁆ c)) α

/-- The term `∑ₖ ε(π e_{-α}) ε([y, π[e_α, z]]) c` of `[θ(y), G(z)] c`. -/
def cocycleTermB (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) (α : Dual K H) :
    ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  hB.casimirSum (fun f e ↦ wedgeProj V f
    (wedge K (nNeg P) V ⁅y, nNegProj P ⁅e, (z : P.KacMoodyAlgebra)⁆⁆ c)) α

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma finite_cocycleTermA (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    (P.posWeights ∩ Function.support (hB.cocycleTermA V y z c)).Finite :=
  hB.finite_casimirSum_nNegProj z (fun f x ↦ wedge K (nNeg P) V ⁅y, nNegProj P f⁆
    (wedgeProj V x c)) fun f x hx ↦ by simp [hx]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma finite_cocycleTermB (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    (P.posWeights ∩ Function.support (hB.cocycleTermB V y z c)).Finite :=
  hB.finite_casimirSum_nNegProj z (fun f x ↦ wedgeProj V f
    (wedge K (nNeg P) V ⁅y, nNegProj P x⁆ c)) fun f x hx ↦ by simp [hx]

lemma lieAction_kostantGTerm_sub (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    (α : Dual K H) :
    lieAction K (nNeg P) V y (hB.kostantGTerm V α z c) -
        hB.kostantGTerm V α z (lieAction K (nNeg P) V y c) =
      hB.cocycleTermA V y z c α + hB.cocycleTermB V y z c α := by
  simp only [kostantGTerm, cocycleTermA, cocycleTermB, casimirSum_def, map_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, wedgeProj_apply, lieAction_wedge_wedge]
  exact Finset.sum_congr rfl fun k _ ↦ add_sub_cancel_right _ _

/-- `[θ(y), G(z)] c = ½ ∑_α (A_α + B_α)`. -/
lemma lieAction_kostantG_sub (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    lieAction K (nNeg P) V y (hB.kostantG V z c) -
        hB.kostantG V z (lieAction K (nNeg P) V y c) =
      (2 : K)⁻¹ • (∑ᶠ α ∈ P.posWeights, hB.cocycleTermA V y z c α +
        ∑ᶠ α ∈ P.posWeights, hB.cocycleTermB V y z c α) := by
  have h1 := map_finsum_mem_of_finite (lieAction K (nNeg P) V y)
    (hB.finite_kostantGTerm V z c)
  have h2 := finsum_mem_sub_distrib'
    (F := fun α ↦ lieAction K (nNeg P) V y (hB.kostantGTerm V α z c))
    ((hB.finite_kostantGTerm V z c).subset fun α ⟨hα, hne⟩ ↦
      ⟨hα, fun h ↦ hne (by simp only [h, map_zero])⟩)
    (hB.finite_kostantGTerm V z (lieAction K (nNeg P) V y c))
  have h3 := finsum_mem_add_distrib' (hB.finite_cocycleTermA V y z c)
    (hB.finite_cocycleTermB V y z c)
  simp only [kostantG_apply, map_smul, h1]
  refine (smul_sub _ _ _).symm.trans (congrArg _ (h2.symm.trans ((finsum_mem_congr rfl
    fun α _ ↦ hB.lieAction_kostantGTerm_sub V y z c α).trans h3)))

/-- `x ↦ ε(π[x, z]) c`. -/
def wedgeLieRight (z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    P.KacMoodyAlgebra →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V where
  toFun x := wedgeProj V ⁅x, (z : P.KacMoodyAlgebra)⁆ c
  map_add' x x' := by simp only [add_lie, map_add, LinearMap.add_apply]
  map_smul' r x := by simp only [smul_lie, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- `x ↦ ε(π[y, x]) c`. -/
def wedgeLieLeft (y : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    P.KacMoodyAlgebra →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V where
  toFun x := wedgeProj V ⁅(y : P.KacMoodyAlgebra), x⁆ c
  map_add' x x' := by simp only [lie_add, map_add, LinearMap.add_apply]
  map_smul' r x := by simp only [lie_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The `α`-term `∑ₖ ε(π e_{-α}) ε(π[[e_α, y], z]) c`. -/
def cocycleTermLeft (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) (α : Dual K H) :
    ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  hB.casimirSum (fun f e ↦ bilinComp (wedgeProj V) (wedgeLieRight V z c) f
    ⁅e, (y : P.KacMoodyAlgebra)⁆) α

/-- The `α`-term `∑ₖ ε(π e_{-α}) ε(π[y, [e_α, z]]) c`. -/
def cocycleTermRight (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) (α : Dual K H) :
    ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  hB.casimirSum (fun f e ↦ bilinComp (wedgeProj V) (wedgeLieLeft V y c) f
    ⁅e, (z : P.KacMoodyAlgebra)⁆) α

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma kostantGTerm_lie (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) (α : Dual K H) :
    hB.kostantGTerm V α (⁅y, z⁆ : nNeg P) c =
      hB.cocycleTermLeft V y z c α + hB.cocycleTermRight V y z c α := by
  simp only [kostantGTerm, cocycleTermLeft, cocycleTermRight, casimirSum_def,
    ← Finset.sum_add_distrib, bilinComp_apply, wedgeLieRight, wedgeLieLeft, LinearMap.coe_mk,
    AddHom.coe_mk, LieSubalgebra.coe_bracket, leibniz_lie _ (y : P.KacMoodyAlgebra), map_add,
    LinearMap.add_apply]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma finite_cocycleTermLeft {β γ : Dual K H} (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    (P.posWeights ∩ Function.support (hB.cocycleTermLeft V y z c)).Finite := by
  refine (finite_window (β + γ)).subset fun α ⟨hα, hne⟩ ↦ ⟨hα, ?_⟩
  refine sub_mem_negWeights_iff.mp (by_contra fun hn ↦ hne ?_)
  rw [cocycleTermLeft, casimirSum_def]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hx := lie_mem_rootSpace_sub (lie_mem_rootSpace_sub (rootSpaceBasis_mem P α k) hy) hz
  rw [sub_sub] at hx
  simp only [bilinComp_apply, wedgeLieRight, LinearMap.coe_mk, AddHom.coe_mk, wedgeProj_apply,
    nNegProj_eq_zero_of_mem_rootSpace hx hn, map_zero, LinearMap.zero_apply]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma finite_cocycleTermRight {β γ : Dual K H} (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    (P.posWeights ∩ Function.support (hB.cocycleTermRight V y z c)).Finite := by
  refine (finite_window (β + γ)).subset fun α ⟨hα, hne⟩ ↦ ⟨hα, ?_⟩
  refine sub_mem_negWeights_iff.mp (by_contra fun hn ↦ hne ?_)
  rw [cocycleTermRight, casimirSum_def]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hx := lie_mem_weightSpaceOfMap (h P) hy
    (lie_mem_rootSpace_sub (rootSpaceBasis_mem P α k) hz)
  rw [show -β + (α - γ) = α - (β + γ) by abel] at hx
  simp only [bilinComp_apply, wedgeLieLeft, LinearMap.coe_mk, AddHom.coe_mk, wedgeProj_apply,
    nNegProj_eq_zero_of_mem_rootSpace hx hn, map_zero, LinearMap.zero_apply]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
/-- `G([y, z]) c = ½ ∑_α (L_α + R_α)`. -/
lemma kostantG_lie {β γ : Dual K H} (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantG V ⁅y, z⁆ c = (2 : K)⁻¹ • (∑ᶠ α ∈ P.posWeights, hB.cocycleTermLeft V y z c α +
      ∑ᶠ α ∈ P.posWeights, hB.cocycleTermRight V y z c α) := by
  rw [kostantG_apply]
  exact congrArg _ ((finsum_mem_congr rfl fun α _ ↦ hB.kostantGTerm_lie V y z c α).trans
    (finsum_mem_add_distrib' (hB.finite_cocycleTermLeft V y z hy hz c)
      (hB.finite_cocycleTermRight V y z hy hz c)))

omit hB [FiniteDimensional K H] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] in
lemma wedgeProj_lie_coe (u w : nNeg P) :
    wedgeProj V ⁅(u : P.KacMoodyAlgebra), (w : P.KacMoodyAlgebra)⁆ = wedge K (nNeg P) V ⁅u, w⁆ := by
  rw [LinearMap.comp_apply, ← LieSubalgebra.coe_bracket, nNegProj_coe]

omit hB [FiniteDimensional K H] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] in
lemma wedgeProj_lie_coe_swap (u w : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    wedgeProj V ⁅(u : P.KacMoodyAlgebra), (w : P.KacMoodyAlgebra)⁆ c =
      -wedge K (nNeg P) V ⁅w, u⁆ c := by
  rw [wedgeProj_lie_coe, ← lie_skew, map_neg, LinearMap.neg_apply]

omit hB [FiniteDimensional K H] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] in
lemma wedgeProj_lie_of_mem (y : nNeg P) {f : P.KacMoodyAlgebra} (hf : f ∈ nNeg P)
    (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    wedgeProj V ⁅f, (y : P.KacMoodyAlgebra)⁆ c = -wedge K (nNeg P) V ⁅y, nNegProj P f⁆ c := by
  simp only [LinearMap.comp_apply, lie_nNegProj_of_mem y hf, map_neg, LinearMap.neg_apply,
    neg_neg]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
/-- Termwise negation of a sum over dual bases. -/
lemma casimirSum_eq_neg {M : Type*} [AddCommGroup M]
    {Φ Ψ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M} {μ : Dual K H}
    (h : ∀ f ∈ rootSpace P (-μ), ∀ e, Φ f e = -Ψ f e) :
    hB.casimirSum Φ μ = -hB.casimirSum Ψ μ := by
  rw [casimirSum_def, casimirSum_def, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ h _ (hB.dualBasis_mem μ k) _

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma casimirSum_lie_skew {M : Type*} [AddCommGroup M] [Module K M]
    (Ψ : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] M) (y : P.KacMoodyAlgebra)
    (μ : Dual K H) :
    hB.casimirSum (fun f e ↦ Ψ f ⁅y, e⁆) μ = -hB.casimirSum (fun f e ↦ Ψ f ⁅e, y⁆) μ :=
  hB.casimirSum_eq_neg fun f _ e ↦ by rw [← lie_skew, map_neg]

/-- The bilinear map `(a, x) ↦ ε(π a) ε(π[x, z]) c`. -/
abbrev leftBilin (z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  bilinComp (wedgeProj (P := P) V) (wedgeLieRight V z c)

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma cocycleTermLeft_self {β : Dual K H} (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.cocycleTermLeft V y z c β =
      wedge K (nNeg P) V y (wedge K (nNeg P) V (adNNeg P ((P.toDual S).symm β) z) c) := by
  rw [cocycleTermLeft, hB.casimirSum_lie_self (leftBilin V z c) hy]
  simp only [bilinComp_apply, wedgeLieRight, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, nNegProj_coe]
  rw [nNegProj_of_mem (lie_h_mem_nNeg P _ z.2)]
  rfl

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma casimirSum_leftBilin_lie_left (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    {α : Dual K H} (hα : α ∈ P.posWeights) :
    hB.casimirSum (fun f e ↦ leftBilin V z c ⁅f, (y : P.KacMoodyAlgebra)⁆ e) α =
      -hB.cocycleTermA V y z c α :=
  hB.casimirSum_eq_neg fun _ hf _ ↦ wedgeProj_lie_of_mem V y
    (rootSpace_le_nNeg ((neg_mem_negWeights_iff P).mpr hα) hf) _

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma cocycleTermLeft_add {β : Dual K H} (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    {α : Dual K H} (hα : α ∈ P.posWeights) :
    hB.cocycleTermLeft V y z c (α + β) = hB.cocycleTermA V y z c α := by
  have h24 := hB.casimirSum_lie_left (leftBilin V z c) hy α
  have h1 := hB.casimirSum_lie_skew (leftBilin V z c) (y : P.KacMoodyAlgebra) (α - -β)
  have h2 := hB.casimirSum_leftBilin_lie_left V y z c hα
  rw [← sub_neg_eq_add α β]
  exact neg_injective (h1.symm.trans (h24.symm.trans h2))

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma casimirSum_leftBilin_nNegProj (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    (α : Dual K H) :
    hB.casimirSum (fun f e ↦ leftBilin V z c f (nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆ :
      P.KacMoodyAlgebra)) α = -hB.cocycleTermB V z y c α :=
  hB.casimirSum_eq_neg fun f _ e ↦ (congrArg (wedgeProj V f)
    (wedgeProj_lie_coe_swap V (nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆) z c)).trans (map_neg _ _)

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
/-- The sum of the terms `L_α` along the root string through `β`. -/
lemma finsum_cocycleTermLeft {β γ : Dual K H} (hβ : β ∈ P.posWeights) (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    ∑ᶠ α ∈ P.posWeights, hB.cocycleTermLeft V y z c α =
      wedge K (nNeg P) V y (wedge K (nNeg P) V (adNNeg P ((P.toDual S).symm β) z) c) +
        ∑ᶠ α ∈ P.posWeights, hB.cocycleTermA V y z c α -
        ∑ᶠ α ∈ P.posWeights, hB.cocycleTermB V z y c α := by
  have hSL := hB.finsum_casimirSum_lie_eq (fun f x ↦ leftBilin V z c f x) (fun f ↦ map_zero _) hβ
    hy (hB.finite_cocycleTermLeft V y z hy hz c)
  have h1 := hB.cocycleTermLeft_self V y z hy c
  have h2 := finsum_mem_congr (s := P.posWeights) rfl fun α hα ↦
    hB.cocycleTermLeft_add V y z hy c hα
  have h3 := finsum_mem_congr (s := P.posWeights) rfl fun α _ ↦
    hB.casimirSum_leftBilin_nNegProj V y z c α
  calc _ = _ := hSL
    _ = _ := by
      change hB.cocycleTermLeft V y z c β +
        ∑ᶠ α ∈ P.posWeights, hB.cocycleTermLeft V y z c (α + β) + _ = _
      simp only [h1, h2, h3, finsum_mem_neg, ← sub_eq_add_neg]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
/-- Termwise equality of sums over dual bases. -/
lemma casimirSum_congr {M : Type*} [AddCommGroup M]
    {Φ Ψ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M} {μ : Dual K H}
    (h : ∀ f ∈ rootSpace P (-μ), ∀ e, Φ f e = Ψ f e) :
    hB.casimirSum Φ μ = hB.casimirSum Ψ μ :=
  Finset.sum_congr rfl fun k _ ↦ h _ (hB.dualBasis_mem μ k) _

omit hB [FiniteDimensional K H] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] in
lemma wedgeProj_lie_swap (a b : P.KacMoodyAlgebra) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    wedgeProj V ⁅a, b⁆ c = -wedgeProj V ⁅b, a⁆ c := by
  rw [← lie_skew, map_neg, LinearMap.neg_apply]

omit hB [CharZero K] [FiniteDimensional K H] in
lemma lie_h_of_mem_rootSpace {β : Dual K H} {y : P.KacMoodyAlgebra} (hy : y ∈ rootSpace P (-β))
    (a : H) : ⁅y, h P a⁆ = β a • y := by
  rw [← lie_skew, hy a, LinearMap.neg_apply, neg_smul, neg_neg]

/-- The bilinear map `(a, x) ↦ ε(π a) ε(π[y, x]) c`. -/
abbrev rightBilin (y : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  bilinComp (wedgeProj (P := P) V) (wedgeLieLeft V y c)

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma cocycleTermRight_self {β γ : Dual K H} (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.cocycleTermRight V y z c γ =
      β ((P.toDual S).symm γ) • wedge K (nNeg P) V z (wedge K (nNeg P) V y c) := by
  rw [cocycleTermRight, hB.casimirSum_lie_self (rightBilin V y c) hz]
  simp only [bilinComp_apply, wedgeLieLeft, LinearMap.coe_mk, AddHom.coe_mk,
    lie_h_of_mem_rootSpace hy, map_smul, LinearMap.comp_apply, nNegProj_coe,
    LinearMap.smul_apply]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma casimirSum_rightBilin_lie_left (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    {α : Dual K H} (hα : α ∈ P.posWeights) :
    hB.casimirSum (fun f e ↦ rightBilin V y c ⁅f, (z : P.KacMoodyAlgebra)⁆ e) α =
      hB.cocycleTermA V z y c α :=
  hB.casimirSum_congr fun _ hf e ↦ (wedgeProj_lie_of_mem V z
    (rootSpace_le_nNeg ((neg_mem_negWeights_iff P).mpr hα) hf) _).trans <| by
      change -(wedge K (nNeg P) V _ (wedgeProj V ⁅(y : P.KacMoodyAlgebra), e⁆ c)) = _
      rw [wedgeProj_lie_swap, map_neg, neg_neg]

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma cocycleTermRight_add {γ : Dual K H} (y z : nNeg P)
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    {α : Dual K H} (hα : α ∈ P.posWeights) :
    hB.cocycleTermRight V y z c (α + γ) = -hB.cocycleTermA V z y c α := by
  have h24 := hB.casimirSum_lie_left (rightBilin V y c) hz α
  have h1 := hB.casimirSum_lie_skew (rightBilin V y c) (z : P.KacMoodyAlgebra) (α - -γ)
  have h2 := hB.casimirSum_rightBilin_lie_left V y z c hα
  rw [← sub_neg_eq_add α γ]
  exact neg_eq_iff_eq_neg.mp (h1.symm.trans (h24.symm.trans h2))

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma casimirSum_rightBilin_nNegProj (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V)
    (α : Dual K H) :
    hB.casimirSum (fun f e ↦ rightBilin V y c f (nNegProj P ⁅e, (z : P.KacMoodyAlgebra)⁆ :
      P.KacMoodyAlgebra)) α = hB.cocycleTermB V y z c α :=
  hB.casimirSum_congr fun f _ e ↦ congrArg (fun T ↦ wedgeProj V f (T c))
    (wedgeProj_lie_coe V y (nNegProj P ⁅e, (z : P.KacMoodyAlgebra)⁆))

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
/-- The sum of the terms `R_α` along the root string through `γ`. -/
lemma finsum_cocycleTermRight {β γ : Dual K H} (hγ : γ ∈ P.posWeights) (y z : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    ∑ᶠ α ∈ P.posWeights, hB.cocycleTermRight V y z c α =
      β ((P.toDual S).symm γ) • wedge K (nNeg P) V z (wedge K (nNeg P) V y c) -
        ∑ᶠ α ∈ P.posWeights, hB.cocycleTermA V z y c α +
        ∑ᶠ α ∈ P.posWeights, hB.cocycleTermB V y z c α := by
  have hSR := hB.finsum_casimirSum_lie_eq (fun f x ↦ rightBilin V y c f x) (fun f ↦ map_zero _)
    hγ hz (hB.finite_cocycleTermRight V y z hy hz c)
  have h1 := hB.cocycleTermRight_self V y z hy hz c
  have h2 := finsum_mem_congr (s := P.posWeights) rfl fun α hα ↦
    hB.cocycleTermRight_add V y z hz c hα
  have h3 := finsum_mem_congr (s := P.posWeights) rfl fun α _ ↦
    hB.casimirSum_rightBilin_nNegProj V y z c α
  calc _ = _ := hSR
    _ = _ := by
      change hB.cocycleTermRight V y z c γ +
        ∑ᶠ α ∈ P.posWeights, hB.cocycleTermRight V y z c (α + γ) + _ = _
      simp only [h1, h2, h3, finsum_mem_neg, ← sub_eq_add_neg]

omit hB [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma smul_wedge_wedge_eq {β γ : Dual K H} (y z : nNeg P)
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    β ((P.toDual S).symm γ) • wedge K (nNeg P) V z (wedge K (nNeg P) V y c) =
      wedge K (nNeg P) V y (wedge K (nNeg P) V (adNNeg P ((P.toDual S).symm β) z) c) := by
  have hs : γ ((P.toDual S).symm β) = β ((P.toDual S).symm γ) := by
    rw [← dualBilinForm_apply_eq, ← dualBilinForm_apply_eq, (P.isSymm_dualBilinForm S).eq]
  have had : adNNeg P ((P.toDual S).symm β) z = (-β ((P.toDual S).symm γ)) • z :=
    Subtype.ext ((hz _).trans (by rw [LinearMap.neg_apply, hs]; rfl))
  calc _ = β ((P.toDual S).symm γ) • -wedge K (nNeg P) V y (wedge K (nNeg P) V z c) :=
        congrArg _ (wedge_wedge_comm _ _ _)
    _ = wedge K (nNeg P) V y (wedge K (nNeg P) V ((-β ((P.toDual S).symm γ)) • z) c) := by
        simp only [map_smul, map_neg, LinearMap.smul_apply, LinearMap.neg_apply, smul_neg, neg_smul]
    _ = _ := by rw [had]

/-- **Kostant's cocycle identity** (reconstructed): for `y ∈ 𝔤_{-β}`, `z ∈ 𝔤_{-γ}`,
`G([y, z]) - [θ(y), G(z)] + [θ(z), G(y)] = ε(y) ε([ν⁻¹(β), z])`. -/
theorem kostantG_lie_sub_lieAction {β γ : Dual K H} (hβ : β ∈ P.posWeights)
    (hγ : γ ∈ P.posWeights) (y z : nNeg P) (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (hz : (z : P.KacMoodyAlgebra) ∈ rootSpace P (-γ)) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantG V ⁅y, z⁆ c -
        (lieAction K (nNeg P) V y (hB.kostantG V z c) -
          hB.kostantG V z (lieAction K (nNeg P) V y c)) +
        (lieAction K (nNeg P) V z (hB.kostantG V y c) -
          hB.kostantG V y (lieAction K (nNeg P) V z c)) =
      wedge K (nNeg P) V y (wedge K (nNeg P) V (adNNeg P ((P.toDual S).symm β) z) c) := by
  have hL := hB.finsum_cocycleTermLeft V hβ y z hy hz c
  have hR := hB.finsum_cocycleTermRight V hγ y z hy hz c
  have hG := (hB.kostantG_lie V y z hy hz c).trans (congrArg _ (congrArg₂ (· + ·) hL hR))
  exact (congrArg₂ (· + ·) (congrArg₂ (· - ·) hG (hB.lieAction_kostantG_sub V y z c))
    (hB.lieAction_kostantG_sub V z y c)).trans
    (half_combination _ _ _ _ _ _ (smul_wedge_wedge_eq (S := S) V y z hz c))

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
