/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.Identity

/-!
# Kostant's identity in degree zero

With the notation of `LieLean.Algebra.Lie.KacMoody.Kostant.Identity`, let
`R(y) = [□, ε(y)]` (`LieModule.ChevalleyEilenberg.laplacianComm`) for `y ∈ 𝔫₋`. We compute it on
chains of degree zero: for a root vector `y ∈ 𝔤_{-β}` (`β > 0`) and `v ∈ V`,

  `R(y)(1 ⊗ v) = y ⊗ (ν⁻¹(β) v + ((ρ|β) - ½(β|β)) v)`.

*Proof (reconstructed).* `R(y)(1 ⊗ v) = θ(y) δ₀ v - δ₀(y v) - d G(y)(1 ⊗ v)`. Using
[Kac] Lemma 2.4 the first two terms combine into the sum over the root string through `β`:
the term `α = β` gives `y ⊗ ν⁻¹(β) v` (`casimirSum_lie_self`), the terms `α > β` cancel, and the
terms `0 < α < β` give `-½ ∑ₖ [π e_{-α}, π[e_α, y]] ⊗ v` together with `d G(y)`. By the ρ-shift
identity (`coe_rhoShiftSum`), `∑_{0<α<β} ∑ₖ [e_{-α}, [e_α, y]] = (2(ρ|β) - (β|β)) y`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.laplacianComm_one_tmul_eq`: the formula
  above.

## References

* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387 (cf. §4, Thm. 4.4).
* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76 (a Casimir argument, §7 and Appendix, in place of Kostant's
  Laplacian).
* The computation above is our own.
-/

open Module LieModule LieModule.ChevalleyEilenberg TensorProduct ExteriorAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {S : A.Symmetrization} {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

/-- The bilinear map `(a, b) ↦ T a (U b)`. -/
def bilinComp {R X N : Type*} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup N]
    [Module R N] (T : X →ₗ[R] Module.End R N) (U : X →ₗ[R] N) : X →ₗ[R] X →ₗ[R] N :=
  LinearMap.mk₂ R (fun a b ↦ T a (U b)) (fun a a' b ↦ by rw [map_add, LinearMap.add_apply])
    (fun r a b ↦ by rw [map_smul, LinearMap.smul_apply]) (fun a b b' ↦ by rw [map_add, map_add])
    (fun r a b ↦ by rw [map_smul, map_smul])

@[simp] lemma bilinComp_apply {R X N : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup N] [Module R N] (T : X →ₗ[R] Module.End R N) (U : X →ₗ[R] N) (a b : X) :
    bilinComp T U a b = T a (U b) := rfl

namespace IsStandardForm

variable (hB : IsStandardForm P S B)
include hB

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

omit hB in
/-- `x ↦ 1 ⊗ x v`. -/
def oneTmulLie (v : V) : P.KacMoodyAlgebra →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  TensorProduct.mk K (ExteriorAlgebra K (nNeg P)) V 1 ∘ₗ
    (LinearMap.applyₗ v ∘ₗ (toEnd K P.KacMoodyAlgebra V : P.KacMoodyAlgebra →ₗ[K] Module.End K V))

omit hB [CharZero K] [FiniteDimensional K H] in
@[simp] lemma oneTmulLie_apply (v : V) (x : P.KacMoodyAlgebra) :
    oneTmulLie V v x = 1 ⊗ₜ ⁅x, v⁆ := rfl

omit hB [FiniteDimensional K H] in
lemma lie_nNegProj_of_mem (y : nNeg P) {f : P.KacMoodyAlgebra} (hf : f ∈ nNeg P) :
    ⁅y, nNegProj P f⁆ = -nNegProj P ⁅f, (y : P.KacMoodyAlgebra)⁆ := by
  have h : ⁅f, (y : P.KacMoodyAlgebra)⁆ ∈ nNeg P := (nNeg P).lie_mem hf y.2
  rw [nNegProj_of_mem hf, nNegProj_of_mem h]
  ext
  exact (lie_skew (y : P.KacMoodyAlgebra) f).symm

omit [Module K V] [LieModule K P.KacMoodyAlgebra V] in
/-- Finiteness of `∑_α ∑ₖ Φ(e_{-α}, [e_α, y])` when `Φ f x` only depends on `x v`. -/
lemma finite_casimirSum_lie_lie_apply {M : Type*} [AddCommGroup M] (hV : IsPosFinite P V)
    (v : V) (y : P.KacMoodyAlgebra) (Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M)
    (hΦ : ∀ f x, ⁅x, v⁆ = 0 → Φ f x = 0) :
    (P.posWeights ∩ Function.support fun α ↦ hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α).Finite := by
  refine ((hV v).union (hV ⁅y, v⁆)).subset fun α ⟨hα, hne⟩ ↦ ?_
  obtain ⟨f, -, e, he, hne⟩ := hB.exists_ne_zero_of_casimirSum_ne_zero hne
  by_cases h1 : ⁅e, v⁆ = 0
  · refine Or.inr ⟨hα, e, he, fun h2 ↦ hne (hΦ f _ ?_)⟩
    rw [lie_lie, h1, lie_zero, sub_zero, h2]
  · exact Or.inl ⟨hα, e, he, h1⟩

/-- The bilinear map `(f, x) ↦ π f ⊗ x v`. -/
abbrev coDiffBilin (v : V) : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K]
    ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  bilinComp (wedgeProj (P := P) V) (oneTmulLie (P := P) V v)

lemma coDiffTerm_sub_lieAction {β : Dual K H} (y : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β)) (v : V) {α : Dual K H}
    (hα : α ∈ P.posWeights) :
    hB.coDiffTerm V α ⁅y, v⁆ - lieAction K (nNeg P) V y (hB.coDiffTerm V α v) =
      hB.casimirSum (fun f e ↦ coDiffBilin (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆) α -
        hB.casimirSum (fun f e ↦ coDiffBilin (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆)
          (α + β) := by
  have h24 := hB.casimirSum_lie_left (coDiffBilin (P := P) V v) hy α
  rw [sub_neg_eq_add] at h24
  have h25 : hB.casimirSum (fun f e ↦ coDiffBilin (P := P) V v f ⁅(y : P.KacMoodyAlgebra), e⁆)
      (α + β) = -hB.casimirSum
        (fun f e ↦ coDiffBilin (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆) (α + β) := by
    simp only [casimirSum_def, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← lie_skew, map_neg]
  have hmain : hB.coDiffTerm V α ⁅y, v⁆ - lieAction K (nNeg P) V y (hB.coDiffTerm V α v) =
      hB.casimirSum (fun f e ↦ coDiffBilin (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆) α +
        hB.casimirSum (fun (f e : P.KacMoodyAlgebra) ↦
          coDiffBilin (P := P) V v ⁅f, (y : P.KacMoodyAlgebra)⁆ e) α := by
    simp only [coDiffTerm, casimirSum_def, map_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hf : hB.dualBasis α k ∈ nNeg P :=
      rootSpace_le_nNeg ((neg_mem_negWeights_iff P).mpr hα) (hB.dualBasis_mem α k)
    have hw : ⁅(rootSpaceBasis P α k : P.KacMoodyAlgebra), ⁅y, v⁆⁆ -
        ⁅y, ⁅(rootSpaceBasis P α k : P.KacMoodyAlgebra), v⁆⁆ =
        ⁅⁅(rootSpaceBasis P α k : P.KacMoodyAlgebra), (y : P.KacMoodyAlgebra)⁆, v⁆ := by
      rw [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket_of_module, lie_lie]
    simp only [coDiffBilin, bilinComp_apply, oneTmulLie_apply, wedgeProj_apply,
      wedge_one_tmul_sub_lieAction, hw, lie_nNegProj_of_mem y hf, map_neg, LinearMap.neg_apply,
      sub_neg_eq_add]
  rw [hmain]
  exact (congrArg (_ + ·) (h24.trans h25)).trans (sub_eq_add_neg _ _).symm

lemma lieAction_kostantCoDiff₀_sub_eq (hV : IsPosFinite P V) (y : nNeg P) (v : V) :
    lieAction K (nNeg P) V y (hB.kostantCoDiff₀ V hV v) - hB.kostantCoDiff₀ V hV ⁅y, v⁆ =
      ∑ᶠ α ∈ P.posWeights, (hB.coDiffTerm V α ⁅y, v⁆ -
        lieAction K (nNeg P) V y (hB.coDiffTerm V α v)) := by
  have hfinT := hB.finite_coDiffTerm V hV v
  have h := map_finsum_mem_of_finite (lieAction K (nNeg P) V y) hfinT
  have h' := finsum_mem_sub_distrib' (hB.finite_coDiffTerm V hV ⁅y, v⁆)
    (G := fun α ↦ lieAction K (nNeg P) V y (hB.coDiffTerm V α v)) (hfinT.subset
    fun α ⟨hα, hne⟩ ↦ ⟨hα, fun h ↦ hne (by simp only [h, map_zero])⟩)
  simp only [kostantCoDiff₀_apply, LinearMap.map_neg, h, h']
  abel

/-- The degree-one part of the Laplacian commutator, first half: for `y ∈ 𝔤_{-β} ⊆ 𝔫₋`,
`θ(y) δ₀ v - δ₀ (y v) = y ⊗ ν⁻¹(β) v + ∑_{α > 0} ∑ₖ e_{-α} ⊗ π[e_α, y] v`. -/
theorem lieAction_kostantCoDiff₀_sub (hV : IsPosFinite P V) {β : Dual K H}
    (hβ : β ∈ P.posWeights) (y : nNeg P) (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β))
    (v : V) :
    lieAction K (nNeg P) V y (hB.kostantCoDiff₀ V hV v) - hB.kostantCoDiff₀ V hV ⁅y, v⁆ =
      wedge K (nNeg P) V y (1 ⊗ₜ ⁅h P ((P.toDual S).symm β), v⁆) +
        ∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦
          coDiffBilin (P := P) V v f
            (nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆ : P.KacMoodyAlgebra)) α := by
  have hfinF := hB.finite_casimirSum_lie_lie_apply V hV v y
    (fun f x ↦ coDiffBilin (P := P) V v f x) fun f x hx ↦ by simp [hx]
  have hfinF' : (P.posWeights ∩ Function.support fun α ↦ hB.casimirSum
      (fun f e ↦ coDiffBilin (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆) (α + β)).Finite :=
    (hfinF.preimage (f := fun α ↦ α + β) (add_left_injective β).injOn).subset
      fun α ⟨hα, hne⟩ ↦ ⟨P.posWeights_add hα hβ, hne⟩
  have h2 := finsum_mem_congr (s := P.posWeights) rfl fun α hα ↦
    hB.coDiffTerm_sub_lieAction V y hy v hα
  have h3 := finsum_mem_sub_distrib' hfinF hfinF'
  have hSL := hB.finsum_casimirSum_lie_eq (fun f x ↦ coDiffBilin (P := P) V v f x)
    (fun f ↦ map_zero _) hβ hy hfinF
  have hself := hB.casimirSum_lie_self (coDiffBilin (P := P) V v) hy
  have hy' : coDiffBilin (P := P) V v y (h P ((P.toDual S).symm β)) =
      wedge K (nNeg P) V y (1 ⊗ₜ ⁅h P ((P.toDual S).symm β), v⁆) := by
    simp
  calc _ = ∑ᶠ α ∈ P.posWeights, (hB.coDiffTerm V α ⁅y, v⁆ -
        lieAction K (nNeg P) V y (hB.coDiffTerm V α v)) :=
        hB.lieAction_kostantCoDiff₀_sub_eq V hV y v
      _ = _ := h2
      _ = _ := h3
      _ = _ := sub_eq_of_eq_add (hSL.trans ?_)
  exact (congrArg (· + _ + _) (hself.trans hy')).trans (add_right_comm _ _ _)

/-- `x ↦ 1 ⊗ (π x) v`. -/
abbrev oneTmulLieProj (v : V) : P.KacMoodyAlgebra →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  oneTmulLie (P := P) V v ∘ₗ (nNeg P).subtype ∘ₗ nNegProj P

/-- The bilinear map `(a, b) ↦ π a ⊗ (π b) v`. -/
abbrev coDiffBilinProj (v : V) : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K]
    ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  bilinComp (wedgeProj (P := P) V) (oneTmulLieProj V v)

/-- The `α`-term of `d(G(y)(1 ⊗ v))`. -/
lemma diff_kostantGTerm_one_tmul (y : nNeg P) (v : V) (α : Dual K H) :
    diff K (nNeg P) V (hB.kostantGTerm V α y (1 ⊗ₜ v)) =
      -hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v ⁅e, (y : P.KacMoodyAlgebra)⁆ f) α +
        hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆) α -
        wedge K (nNeg P) V (hB.casimirSum
          (fun f e ↦ ⁅nNegProj P f, nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆⁆) α) (1 ⊗ₜ v) := by
  simp only [kostantGTerm, casimirSum_def, map_sum, LinearMap.sum_apply,
    diff_wedge_wedge_one_tmul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, coDiffBilinProj, bilinComp_apply, oneTmulLieProj,
    LinearMap.comp_apply, oneTmulLie_apply, Submodule.subtype_apply,
    LieSubalgebra.coe_bracket_of_module]

omit hB [FiniteDimensional K H] in
lemma coDiffBilinProj_eq_zero_left {x : P.KacMoodyAlgebra} (hx : nNegProj P x = 0) (v : V)
    (b : P.KacMoodyAlgebra) : coDiffBilinProj (P := P) V v x b = 0 := by
  simp [hx]

omit hB [FiniteDimensional K H] in
lemma coDiffBilinProj_eq_zero_right {x : P.KacMoodyAlgebra} (hx : nNegProj P x = 0) (v : V)
    (a : P.KacMoodyAlgebra) : coDiffBilinProj (P := P) V v a x = 0 := by
  simp [hx]

/-- The terms `∑ₖ π e_{-α} ⊗ π[e_α, y] v` vanish unless `0 < α < β`. -/
lemma casimirSum_coDiffBilinProj_mem_window {β : Dual K H} {y : P.KacMoodyAlgebra}
    (hy : y ∈ rootSpace P (-β)) (v : V) {γ : Dual K H}
    (hγ : hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, y⁆) γ ≠ 0) :
    γ ∈ P.posWeights ∧ β - γ ∈ P.posWeights := by
  by_contra hc
  refine hγ (Finset.sum_eq_zero fun k _ ↦ ?_)
  by_cases hγp : γ ∈ P.posWeights
  · have h' : γ - β ∉ P.negWeights := fun h' ↦ hc ⟨hγp, sub_mem_negWeights_iff.mp h'⟩
    exact coDiffBilinProj_eq_zero_right V (nNegProj_eq_zero_of_mem_rootSpace
      (lie_mem_rootSpace_sub (rootSpaceBasis_mem P γ k) hy) h') v _
  · exact coDiffBilinProj_eq_zero_left V (nNegProj_eq_zero_of_mem_rootSpace
      (hB.dualBasis_mem γ k) (by rwa [neg_mem_negWeights_iff])) v _

/-- The antisymmetry `∑_α ∑ₖ π[e_α, y] ⊗ (π e_{-α}) v = -∑_α ∑ₖ π e_{-α} ⊗ π[e_α, y] v`. -/
lemma finsum_casimirSum_coDiffBilinProj_swap {β : Dual K H} {y : P.KacMoodyAlgebra}
    (hy : y ∈ rootSpace P (-β)) (v : V) :
    ∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v ⁅e, y⁆ f) α =
      -∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, y⁆) α :=
  calc _ = ∑ᶠ α ∈ P.posWeights,
        -hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, y⁆) (β - α) :=
      finsum_mem_congr rfl fun α _ ↦ hB.casimirSum_lie_swap _ hy α
    _ = -∑ᶠ α ∈ P.posWeights,
        hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, y⁆) (β - α) :=
      finsum_mem_neg _ _
    _ = _ := congrArg Neg.neg (finsum_posWeights_sub _ β fun _ hγ ↦
      hB.casimirSum_coDiffBilinProj_mem_window V hy v hγ)

lemma finite_casimirSum_nNegProj_lie {β : Dual K H} {y : P.KacMoodyAlgebra}
    (hy : y ∈ rootSpace P (-β)) :
    (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ ⁅nNegProj P f, nNegProj P ⁅e, y⁆⁆) α).Finite :=
  (finite_window β).subset fun _ ⟨hα, hne⟩ ↦ hB.casimirSum_nNegProj_ne_zero_mem_window hy hα hne

omit [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] in
lemma finsum_wedge_casimirSum {β : Dual K H} {y : P.KacMoodyAlgebra}
    (hy : y ∈ rootSpace P (-β)) (v : V) :
    ∑ᶠ α ∈ P.posWeights, wedge K (nNeg P) V
        (hB.casimirSum (fun f e ↦ ⁅nNegProj P f, nNegProj P ⁅e, y⁆⁆) α) (1 ⊗ₜ v) =
      wedge K (nNeg P) V (hB.rhoShiftSum y) (1 ⊗ₜ v) :=
  (map_finsum_mem_of_finite ((wedge K (nNeg P) V).flip (1 ⊗ₜ v))
    (hB.finite_casimirSum_nNegProj_lie hy)).symm

lemma finite_casimirSum_coDiffBilinProj {β : Dual K H} {y : P.KacMoodyAlgebra}
    (hy : y ∈ rootSpace P (-β)) (v : V) :
    (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, y⁆) α).Finite :=
  (finite_window β).subset fun _ ⟨_, hne⟩ ↦ hB.casimirSum_coDiffBilinProj_mem_window V hy v hne

lemma finite_casimirSum_coDiffBilinProj_swap {β : Dual K H} {y : P.KacMoodyAlgebra}
    (hy : y ∈ rootSpace P (-β)) (v : V) :
    (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ coDiffBilinProj (P := P) V v ⁅e, y⁆ f) α).Finite :=
  (finite_window β).subset fun α ⟨hα, hne⟩ ↦ by
    rw [Function.mem_support, hB.casimirSum_lie_swap _ hy α, neg_ne_zero] at hne
    exact ⟨hα, (hB.casimirSum_coDiffBilinProj_mem_window V hy v hne).1⟩

/-- `d(G(y)(1 ⊗ v)) = ∑_α ∑ₖ π e_{-α} ⊗ π[e_α, y] v - ½ ρShift(y) ⊗ v` for `y ∈ 𝔤_{-β}`. -/
lemma diff_kostantG_one_tmul {β : Dual K H} (y : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β)) (v : V) :
    diff K (nNeg P) V (hB.kostantG V y (1 ⊗ₜ v)) =
      ∑ᶠ α ∈ P.posWeights, hB.casimirSum
          (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆) α -
        (2 : K)⁻¹ • wedge K (nNeg P) V (hB.rhoShiftSum y) (1 ⊗ₜ v) := by
  have h1 := map_finsum_mem_of_finite (diff K (nNeg P) V)
    (hB.finite_kostantGTerm V y (1 ⊗ₜ v))
  have h2 := finsum_mem_neg_add_sub (hB.finite_casimirSum_coDiffBilinProj_swap V hy v)
    (hB.finite_casimirSum_coDiffBilinProj V hy v) (I := fun α ↦ wedge K (nNeg P) V
      (hB.casimirSum (fun f e ↦ ⁅nNegProj P f, nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆⁆) α)
      (1 ⊗ₜ v))
    ((hB.finite_casimirSum_nNegProj_lie hy).subset fun α ⟨hα, hne⟩ ↦
      ⟨hα, fun h ↦ hne (by simp only [h, map_zero, LinearMap.zero_apply])⟩)
  have h3 := hB.finsum_casimirSum_coDiffBilinProj_swap V hy v
  have h4 := hB.finsum_wedge_casimirSum V hy v
  calc _ = (2 : K)⁻¹ • ∑ᶠ α ∈ P.posWeights,
        diff K (nNeg P) V (hB.kostantGTerm V α y (1 ⊗ₜ v)) := by
        rw [kostantG_apply, map_smul, h1]
    _ = _ := by
        simp only [diff_kostantGTerm_one_tmul, h2, h3, h4]
        module

/-- **Kostant's identity in degree zero**: for `y ∈ 𝔤_{-β} ⊆ 𝔫₋`,
`R(y)(1 ⊗ v) = y ⊗ (ν⁻¹(β) v + ((ρ | β) - ½ (β | β)) v)`, where `R(y) = [θ(y), δ] - d G(y) + G(y) d`
(`LieModule.ChevalleyEilenberg.laplacianComm`). -/
theorem laplacianComm_one_tmul_eq (hA : A.IsGeneralizedCartan) (hV : IsPosFinite P V)
    {β : Dual K H} (hβ : β ∈ P.posWeights) (y : nNeg P)
    (hy : (y : P.KacMoodyAlgebra) ∈ rootSpace P (-β)) (v : V) :
    laplacianComm (hB.kostantCoDiff₀ V hV) (hB.kostantG V)
        (fun y ↦ hB.kostantG_comp_wedge V y y) y (1 ⊗ₜ v) =
      wedge K (nNeg P) V y (1 ⊗ₜ (⁅h P ((P.toDual S).symm β), v⁆ +
        (P.dualBilinForm S P.rho β - (2 : K)⁻¹ * P.dualBilinForm S β β) • v)) := by
  have hA' := hB.lieAction_kostantCoDiff₀_sub V hV hβ y hy v
  have hB' := hB.diff_kostantG_one_tmul V y hy v
  have hY : hB.rhoShiftSum (y : P.KacMoodyAlgebra) =
      (2 * P.dualBilinForm S P.rho β - P.dualBilinForm S β β) • y :=
    Subtype.ext (hB.coe_rhoShiftSum hA hβ hy)
  rw [laplacianComm_one_tmul, hA', hB']
  have hS : ∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦ coDiffBilin (P := P) V v f
      (nNegProj P ⁅e, (y : P.KacMoodyAlgebra)⁆ : P.KacMoodyAlgebra)) α =
      ∑ᶠ α ∈ P.posWeights, hB.casimirSum
        (fun f e ↦ coDiffBilinProj (P := P) V v f ⁅e, (y : P.KacMoodyAlgebra)⁆) α := rfl
  simp only [hY, map_smul, tmul_add, tmul_smul, map_add, LinearMap.smul_apply, hS]
  module

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
