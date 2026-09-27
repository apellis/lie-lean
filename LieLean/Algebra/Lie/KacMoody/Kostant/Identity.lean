/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.Laplacian
import LieLean.Algebra.Lie.KacMoody.Kostant.RhoShift
import LieLean.Algebra.Lie.KacMoody.Kostant.Chains

/-!
# Kostant's codifferential on `𝔫₋`-chains

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` with a standard invariant form
`(·|·)` and dual bases `{e_α^{(k)}}`, `{e_{-α}^{(k)}}` of the root spaces, and let `V` be a
`𝔤`-module on which `𝔫₊` acts locally finitely (`IsPosFinite`). On the chains `⋀𝔫₋ ⊗ V` we define
Kostant's codifferential `δ` (the transpose of the differential of `𝔫₊`-cohomology, transported to
`𝔫₋`-chains by the invariant form) by the recursion of `LieModule.ChevalleyEilenberg.coDiff`:
* `δ(1 ⊗ v) = δ₀ v = -∑_{α > 0} ∑ₖ e_{-α}^{(k)} ⊗ e_α^{(k)} v`;
* `δ(y ∧ c) = -G(y) c - y ∧ δ c`, where
  `G(y) = ½ ∑_{α > 0} ∑ₖ ε(e_{-α}^{(k)}) ε(π[e_α^{(k)}, y])` and `π : 𝔤 → 𝔫₋` is the projection
  along the Borel subalgebra.

All sums are finite on each vector. Kostant's identity for the Laplacian `□ = dδ + δd` is proved
in `LieLean.Algebra.Lie.KacMoody.Kostant.LaplacianIdentity` and
`LieLean.Algebra.Lie.KacMoody.Kostant.Cocycle`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantG`: the operators `G(y)`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantCoDiff₀`: `δ₀`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantCoDiff`: Kostant's codifferential.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantLaplacian`: `□ = dδ + δd`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantG_wedge`: the `G(y)` commute with the
  `ε(z)`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.kostantCoDiff_mem_chainsIn`: `δ` raises the
  degree by one.

## References

* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387 (check).
* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76, §§5–8 (check).
* The recursive description of `δ` is reconstructed by us.
-/

open Module LieModule LieModule.ChevalleyEilenberg TensorProduct ExteriorAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {S : A.Symmetrization} {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

/-! ### Finiteness -/

omit [FiniteDimensional K H] in
/-- For `y ∈ 𝔫₋`, only finitely many `α > 0` have `π[𝔤_α, y] ≠ 0`. -/
lemma finite_nNegProj_lie (y : nNeg P) :
    {α | α ∈ P.posWeights ∧ ∃ e ∈ rootSpace P α,
      nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆ ≠ 0}.Finite := by
  induction (nNegBasis P).mem_span y using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    refine (finite_window x.root).subset fun α ⟨hα, e, he, hne⟩ ↦ ⟨hα, ?_⟩
    refine sub_mem_negWeights_iff.mp (by_contra fun h ↦ hne ?_)
    exact nNegProj_eq_zero_of_mem_rootSpace (lie_mem_rootSpace_sub he (nNegBasis_mem P x)) h
  | zero => simp
  | add y y' _ _ hy hy' =>
    refine (hy.union hy').subset fun α ⟨hα, e, he, hne⟩ ↦ ?_
    rw [Submodule.coe_add, lie_add, map_add] at hne
    by_cases h : nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆ = 0
    · rw [h, zero_add] at hne; exact Or.inr ⟨hα, e, he, hne⟩
    · exact Or.inl ⟨hα, e, he, h⟩
  | smul c y _ hy =>
    refine hy.subset fun α ⟨hα, e, he, hne⟩ ↦ ⟨hα, e, he, fun h ↦ hne ?_⟩
    rw [Submodule.coe_smul, lie_smul, map_smul, h, smul_zero]

namespace IsStandardForm

variable (hB : IsStandardForm P S B)
include hB

/-- If `Φ f x` only depends on `π x`, the sum `∑_{α>0} ∑ₖ Φ(e_{-α}, [e_α, y])` has finite
support, for `y ∈ 𝔫₋`. -/
lemma finite_casimirSum_nNegProj {M : Type*} [AddCommGroup M] (y : nNeg P)
    (Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M) (hΦ : ∀ f x, nNegProj P x = 0 → Φ f x = 0) :
    (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ Φ f ⁅e, (y : P.KacMoodyAlgebra)⁆) α).Finite :=
  (finite_nNegProj_lie y).subset fun α ⟨hα, hne⟩ ↦ by
    obtain ⟨f, -, e, he, hne⟩ := hB.exists_ne_zero_of_casimirSum_ne_zero hne
    exact ⟨hα, e, he, fun h ↦ hne (hΦ f _ h)⟩

/-- For `v` in a module on which `𝔫₊` acts locally finitely, the sum
`∑_{α>0} ∑ₖ Φ(e_{-α}, e_α v)` has finite support. -/
lemma finite_casimirSum_lie_apply {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] (hV : IsPosFinite P V)
    (v : V) (Φ : P.KacMoodyAlgebra → V → M) (hΦ : ∀ f, Φ f 0 = 0) :
    (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ Φ f ⁅e, v⁆) α).Finite :=
  (hV v).subset fun α ⟨hα, hne⟩ ↦ by
    obtain ⟨f, -, e, he, hne⟩ := hB.exists_ne_zero_of_casimirSum_ne_zero hne
    exact ⟨hα, e, he, fun h ↦ hne (by rw [h, hΦ])⟩

variable (V : Type*) [AddCommGroup V] [Module K V]

/-- `ε'(x) = ε(π x)`: wedging with the `𝔫₋`-component of `x ∈ 𝔤`. -/
abbrev wedgeProj : P.KacMoodyAlgebra →ₗ[K] Module.End K (ExteriorAlgebra K (nNeg P) ⊗[K] V) :=
  wedge K (nNeg P) V ∘ₗ nNegProj P

omit hB [FiniteDimensional K H] in
lemma wedgeProj_apply (x : P.KacMoodyAlgebra) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    wedgeProj V x c = wedge K (nNeg P) V (nNegProj P x) c := rfl

omit hB [FiniteDimensional K H] in
lemma wedgeProj_eq_zero {x : P.KacMoodyAlgebra} (hx : nNegProj P x = 0) : wedgeProj V x = 0 := by
  rw [LinearMap.comp_apply, hx, map_zero]

/-- The `α`-term `∑ₖ ε(π e_{-α}^{(k)}) ε(π[e_α^{(k)}, y]) c` of `kostantG`. -/
def kostantGTerm (α : Dual K H) (y : P.KacMoodyAlgebra) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  hB.casimirSum (fun f e ↦ wedgeProj V f (wedgeProj V ⁅e, y⁆ c)) α

lemma kostantGTerm_add_left (α : Dual K H) (y y' : P.KacMoodyAlgebra)
    (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantGTerm V α (y + y') c = hB.kostantGTerm V α y c + hB.kostantGTerm V α y' c := by
  simp only [kostantGTerm, casimirSum_def, ← Finset.sum_add_distrib, lie_add, map_add,
    LinearMap.add_apply]

lemma kostantGTerm_smul_left (α : Dual K H) (r : K) (y : P.KacMoodyAlgebra)
    (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantGTerm V α (r • y) c = r • hB.kostantGTerm V α y c := by
  simp only [kostantGTerm, casimirSum_def, Finset.smul_sum, lie_smul, map_smul,
    LinearMap.smul_apply]

lemma kostantGTerm_add_right (α : Dual K H) (y : P.KacMoodyAlgebra)
    (c c' : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantGTerm V α y (c + c') = hB.kostantGTerm V α y c + hB.kostantGTerm V α y c' := by
  simp only [kostantGTerm, casimirSum_def, ← Finset.sum_add_distrib, map_add]

lemma kostantGTerm_smul_right (α : Dual K H) (r : K) (y : P.KacMoodyAlgebra)
    (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantGTerm V α y (r • c) = r • hB.kostantGTerm V α y c := by
  simp only [kostantGTerm, casimirSum_def, Finset.smul_sum, map_smul]

lemma finite_kostantGTerm (y : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    (P.posWeights ∩ Function.support fun α ↦ hB.kostantGTerm V α y c).Finite :=
  hB.finite_casimirSum_nNegProj y (fun f x ↦ wedgeProj V f (wedgeProj V x c))
    fun f x hx ↦ by rw [wedgeProj_eq_zero V hx]; simp

/-- The operator `G(y) = ½ ∑_{α > 0} ∑ₖ ε(π e_{-α}^{(k)}) ε(π[e_α^{(k)}, y])` on `⋀𝔫₋ ⊗ V`
(the "cobracket" term of Kostant's codifferential). -/
def kostantG : nNeg P →ₗ[K] Module.End K (ExteriorAlgebra K (nNeg P) ⊗[K] V) :=
  LinearMap.mk₂ K (fun y c ↦ (2 : K)⁻¹ • ∑ᶠ α ∈ P.posWeights, hB.kostantGTerm V α y c)
    (fun y y' c ↦ by
      rw [← smul_add, ← finsum_mem_add_distrib' (hB.finite_kostantGTerm V y c)
        (hB.finite_kostantGTerm V y' c)]
      exact congrArg _ (finsum_mem_congr rfl fun α _ ↦ by
        rw [Submodule.coe_add, kostantGTerm_add_left]))
    (fun r y c ↦ by
      have h : ∑ᶠ α ∈ P.posWeights, hB.kostantGTerm V α ((r • y : nNeg P) : P.KacMoodyAlgebra) c =
          r • ∑ᶠ α ∈ P.posWeights, hB.kostantGTerm V α y c :=
        (finsum_mem_congr rfl fun α _ ↦ by rw [Submodule.coe_smul, kostantGTerm_smul_left]).trans
          (smul_finsum_mem_of_field r _ _).symm
      rw [h, smul_comm])
    (fun y c c' ↦ by
      rw [← smul_add, ← finsum_mem_add_distrib' (hB.finite_kostantGTerm V y c)
        (hB.finite_kostantGTerm V y c')]
      exact congrArg _ (finsum_mem_congr rfl fun α _ ↦ by rw [kostantGTerm_add_right]))
    (fun r y c ↦ by
      have h : ∑ᶠ α ∈ P.posWeights, hB.kostantGTerm V α y (r • c) =
          r • ∑ᶠ α ∈ P.posWeights, hB.kostantGTerm V α y c :=
        (finsum_mem_congr rfl fun α _ ↦ by rw [kostantGTerm_smul_right]).trans
          (smul_finsum_mem_of_field r _ _).symm
      rw [h, smul_comm])

lemma kostantG_apply (y : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantG V y c = (2 : K)⁻¹ • ∑ᶠ α ∈ P.posWeights, hB.kostantGTerm V α y c := rfl

/-- The operators `G(y)` commute with the operators `ε(z)`. -/
lemma kostantG_wedge (y z : nNeg P) (c : ExteriorAlgebra K (nNeg P) ⊗[K] V) :
    hB.kostantG V y (wedge K (nNeg P) V z c) = wedge K (nNeg P) V z (hB.kostantG V y c) := by
  rw [kostantG_apply, kostantG_apply, map_smul]
  rw [map_finsum_mem_of_finite (wedge K (nNeg P) V z) (hB.finite_kostantGTerm V y c)]
  refine congrArg ((2 : K)⁻¹ • ·) (finsum_mem_congr rfl fun α _ ↦ ?_)
  simp only [kostantGTerm, casimirSum_def, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [wedgeProj_apply]
  exact wedge_wedge_wedge_comm _ _ z c

lemma kostantG_comp_wedge (y z : nNeg P) :
    hB.kostantG V y ∘ₗ wedge K (nNeg P) V z = wedge K (nNeg P) V z ∘ₗ hB.kostantG V y :=
  LinearMap.ext (hB.kostantG_wedge V y z)

omit [CharZero K] [FiniteDimensional K H] hB in
lemma finsum_mem_mem_submodule {N : Type*} [AddCommGroup N] [Module K N] (p : Submodule K N)
    (s : Set (Dual K H)) (F : Dual K H → N) (h : ∀ α ∈ s, F α ∈ p) : ∑ᶠ α ∈ s, F α ∈ p :=
  finsum_mem_induction (· ∈ p) (zero_mem _) (fun _ _ ↦ add_mem) h

/-- `G(y)` raises the degree by two. -/
lemma kostantG_mem_chainsIn (y : nNeg P) {k : ℕ} {c : ExteriorAlgebra K (nNeg P) ⊗[K] V}
    (hc : c ∈ chainsIn K (nNeg P) V k) : hB.kostantG V y c ∈ chainsIn K (nNeg P) V (k + 2) := by
  rw [kostantG_apply]
  refine Submodule.smul_mem _ _ (finsum_mem_mem_submodule _ _ _ fun α _ ↦ ?_)
  rw [kostantGTerm, casimirSum_def]
  exact Submodule.sum_mem _ fun k _ ↦ wedge_mem_chainsIn _ (wedge_mem_chainsIn _ hc)

variable [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]

/-- The `α`-term `∑ₖ π e_{-α}^{(k)} ⊗ e_α^{(k)} v` of `kostantCoDiff₀`. -/
def coDiffTerm (α : Dual K H) (v : V) : ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  hB.casimirSum (fun f e ↦ wedgeProj V f (1 ⊗ₜ ⁅e, v⁆)) α

lemma finite_coDiffTerm (hV : IsPosFinite P V) (v : V) :
    (P.posWeights ∩ Function.support fun α ↦ hB.coDiffTerm V α v).Finite :=
  hB.finite_casimirSum_lie_apply hV v (fun f w ↦ wedgeProj V f (1 ⊗ₜ w)) fun f ↦ by simp

omit [LieModule K P.KacMoodyAlgebra V] in
lemma coDiffTerm_add (α : Dual K H) (v w : V) :
    hB.coDiffTerm V α (v + w) = hB.coDiffTerm V α v + hB.coDiffTerm V α w := by
  simp only [coDiffTerm, casimirSum_def, ← Finset.sum_add_distrib, lie_add, tmul_add, map_add]

lemma coDiffTerm_smul (α : Dual K H) (r : K) (v : V) :
    hB.coDiffTerm V α (r • v) = r • hB.coDiffTerm V α v := by
  simp only [coDiffTerm, casimirSum_def, Finset.smul_sum, lie_smul, tmul_smul, map_smul]

/-- The degree-raising part `δ₀ v = -∑_{α > 0} ∑ₖ e_{-α}^{(k)} ⊗ e_α^{(k)} v` of Kostant's
codifferential, for `V` with `IsPosFinite`. -/
def kostantCoDiff₀ (hV : IsPosFinite P V) : V →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V where
  toFun v := -∑ᶠ α ∈ P.posWeights, hB.coDiffTerm V α v
  map_add' v w := by
    rw [← neg_add, ← finsum_mem_add_distrib' (hB.finite_coDiffTerm V hV v)
      (hB.finite_coDiffTerm V hV w)]
    exact congrArg _ (finsum_mem_congr rfl fun α _ ↦ hB.coDiffTerm_add V α v w)
  map_smul' r v := by
    have h : ∑ᶠ α ∈ P.posWeights, hB.coDiffTerm V α (r • v) =
        r • ∑ᶠ α ∈ P.posWeights, hB.coDiffTerm V α v :=
      (finsum_mem_congr rfl fun α _ ↦ hB.coDiffTerm_smul V α r v).trans
        (smul_finsum_mem_of_finite r (hB.finite_coDiffTerm V hV v)).symm
    rw [h, RingHom.id_apply, smul_neg]

lemma kostantCoDiff₀_apply (hV : IsPosFinite P V) (v : V) :
    hB.kostantCoDiff₀ V hV v = -∑ᶠ α ∈ P.posWeights, hB.coDiffTerm V α v := rfl

lemma kostantCoDiff₀_mem_chainsIn (hV : IsPosFinite P V) (v : V) :
    hB.kostantCoDiff₀ V hV v ∈ chainsIn K (nNeg P) V 1 := by
  rw [kostantCoDiff₀_apply]
  refine neg_mem (finsum_mem_mem_submodule _ _ _ fun α _ ↦ ?_)
  rw [coDiffTerm, casimirSum_def]
  exact Submodule.sum_mem _ fun k _ ↦ wedge_mem_chainsIn _ (one_tmul_mem_chainsIn _)

/-- **Kostant's codifferential** `δ` on `⋀𝔫₋ ⊗ V`: `δ(1 ⊗ v) = δ₀ v`,
`δ(y ∧ c) = -G(y) c - y ∧ δ c`. -/
def kostantCoDiff (hV : IsPosFinite P V) : Module.End K (ExteriorAlgebra K (nNeg P) ⊗[K] V) :=
  coDiff (hB.kostantCoDiff₀ V hV) (hB.kostantG V) fun y ↦ hB.kostantG_comp_wedge V y y

/-- **Kostant's Laplacian** `□ = dδ + δd` on `⋀𝔫₋ ⊗ V`. -/
def kostantLaplacian (hV : IsPosFinite P V) : Module.End K (ExteriorAlgebra K (nNeg P) ⊗[K] V) :=
  laplacian (hB.kostantCoDiff₀ V hV) (hB.kostantG V) fun y ↦ hB.kostantG_comp_wedge V y y

lemma kostantCoDiff_mem_chainsIn (hV : IsPosFinite P V) {k : ℕ}
    {c : ExteriorAlgebra K (nNeg P) ⊗[K] V} (hc : c ∈ chainsIn K (nNeg P) V k) :
    hB.kostantCoDiff V hV c ∈ chainsIn K (nNeg P) V (k + 1) :=
  coDiff_mem_chainsIn _ _ _ (hB.kostantCoDiff₀_mem_chainsIn V hV)
    (fun y _ _ hc ↦ hB.kostantG_mem_chainsIn V y hc) hc

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
