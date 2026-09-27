/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Sl2
import LieLean.Algebra.Lie.KacMoody.CompleteReducibility
import LieLean.Algebra.Lie.KacMoody.FiniteType

/-!
# Finite-dimensional modules over `𝔤(A)` of finite type: Weyl's theorem

Let `A` be a Cartan matrix of finite type (`Matrix.IsFiniteCartan`), `K` a field of characteristic
zero and `(𝔥, Π, Π^∨)` a realization of `A` with `𝔥` finite-dimensional, so that `𝔤(A)` is a
finite-dimensional semisimple Lie algebra (`KacMoody/FiniteType.lean`). We prove Weyl's complete
reducibility theorem for `𝔤(A)`: every finite-dimensional `𝔤(A)`-module is a direct sum of
irreducible modules `L(Λ)` with `Λ` dominant integral, and every submodule has a complement.

## The argument

We reduce to complete reducibility of integrable modules in the category `𝒪` ([Kac] Thm. 10.7,
`IsCategoryO.exists_isInternal_irreducibleModule`). Let `V` be finite-dimensional. For each `i`,
`(αᵢ^∨, eᵢ, fᵢ)` is an `𝔰𝔩₂`-triple, so by `LieLean/Algebra/Lie/Sl2.lean` `eᵢ` and `fᵢ` act
nilpotently and `αᵢ^∨` acts diagonalizably with integer eigenvalues. The `αᵢ^∨` commute and, `A`
being nonsingular, form a basis of `𝔥`; hence `V` is the sum of simultaneous eigenspaces, which are
weight spaces. So `V` is integrable; it lies in `𝒪` since it has finitely many weights, each with
a finite-dimensional weight space. This route (via [Kac] Thm. 10.7 rather than the classical
Casimir argument of [Hum] §6.3) was chosen by us; the statement is classical.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.isHDiagonalizable_of_finiteDimensional`,
  `Matrix.Realization.KacMoodyAlgebra.isIntegrable_of_finiteDimensional`,
  `Matrix.Realization.KacMoodyAlgebra.isCategoryO_of_finiteDimensional`: a finite-dimensional
  `𝔤(A)`-module is `𝔥`-diagonalizable, integrable, and lies in `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.exists_isInternal_irreducibleModule_of_finiteDimensional`:
  **Weyl's theorem**: a finite-dimensional `𝔤(A)`-module is the internal direct sum of submodules
  isomorphic to modules `L(Λ)` with `Λ` dominant integral.
* `Matrix.Realization.KacMoodyAlgebra.complementedLattice_of_finiteDimensional`: every submodule
  of a finite-dimensional `𝔤(A)`-module has a complement.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.6, §10.7.
* [Hum] J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §6.3,
  §7.2.
-/

open Module LieModule

noncomputable section

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- For a diagonalizable endomorphism, generalized eigenspaces are eigenspaces. -/
lemma maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top {f : Module.End K V}
    (hf : ⨆ μ, f.eigenspace μ = ⊤) (μ : K) : f.maxGenEigenspace μ = f.eigenspace μ := by
  refine le_antisymm ?_ ((f.genEigenspace μ).mono le_top)
  have hp : ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ :=
    fun x hx ↦ mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hx
  have := Submodule.inf_iSup_genEigenspace hp 1
  rw [show ⨆ μ, f.genEigenspace μ 1 = ⊤ from hf, inf_top_eq] at this
  rw [this]
  refine iSup_le fun ν ↦ ?_
  by_cases hν : ν = μ
  · subst hν; exact inf_le_right
  · rw [(f.disjoint_genEigenspace (Ne.symm hν) ⊤ 1).eq_bot]
    exact bot_le

/-- A commuting family of diagonalizable endomorphisms of a finite-dimensional space is
simultaneously diagonalizable. -/
theorem iSup_iInf_eigenspace_eq_top_of_commute {ι : Type*} (f : ι → Module.End K V)
    (h : Pairwise fun i j ↦ Commute (f i) (f j)) (h' : ∀ i, ⨆ μ, (f i).eigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
  have := iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f h
    fun i ↦ by simp_rw [maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top (h' i), h' i]
  simpa only [maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top (h' _)] using this

end Module.End

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [FiniteDimensional K V]

/-- In a finite-dimensional `𝔤(A)`-module, the Chevalley generators `eᵢ` act nilpotently. -/
theorem isNilpotent_toEnd_e (hA : A.IsGeneralizedCartan) (i : ι) :
    IsNilpotent (toEnd K P.KacMoodyAlgebra V (e P i)) :=
  (isSl2Triple P hA i).isNilpotent_toEnd_e

/-- In a finite-dimensional `𝔤(A)`-module, the Chevalley generators `fᵢ` act nilpotently. -/
theorem isNilpotent_toEnd_f (hA : A.IsGeneralizedCartan) (i : ι) :
    IsNilpotent (toEnd K P.KacMoodyAlgebra V (f P i)) :=
  (isSl2Triple P hA i).isNilpotent_toEnd_f

variable [FiniteDimensional K H] (hA : A.IsFiniteCartan)
include hA

/-- For `A` of finite type, a finite-dimensional `𝔤(A)`-module is `𝔥`-diagonalizable: each
coroot `αᵢ^∨` acts diagonalizably (it is the `h` of an `𝔰𝔩₂`-triple), the coroots commute and
span `𝔥`. -/
theorem isHDiagonalizable_of_finiteDimensional : IsHDiagonalizable P V := by
  let T : ι → Module.End K V := fun i ↦ toEnd K P.KacMoodyAlgebra V (h P (P.coroot i))
  have hcomm : Pairwise fun i j ↦ Commute (T i) (T j) := fun i j _ ↦ by
    ext v
    simp only [T, Module.End.mul_apply, toEnd_apply_apply]
    rw [leibniz_lie, lie_h_h, zero_lie, zero_add]
  have hdiag : ∀ i, ⨆ μ, (T i).eigenspace μ = ⊤ := fun i ↦ eq_top_iff.mpr <|
    ((isSl2Triple P hA.isGeneralizedCartan i).iSup_eigenspace_toEnd_h_eq_top (M := V)).ge.trans
      (iSup_le fun k ↦ le_iSup (fun μ ↦ (T i).eigenspace μ) (k : K))
  let b : Basis ι K H := basisOfLinearIndependentOfCardEqFinrank' P.coroot
    P.linearIndependent_coroot (P.finrank_eq_card_of_isFiniteCartan hA).symm
  have hb : ∀ i, b i = P.coroot i := fun i ↦ by simp [b]
  rw [IsHDiagonalizable, eq_top_iff, ← Module.End.iSup_iInf_eigenspace_eq_top_of_commute T
    hcomm hdiag]
  refine iSup_le fun χ ↦ le_iSup_of_le (b.constr K χ) fun v hv ↦ ?_
  rw [Submodule.mem_iInf] at hv
  have hext : (LinearMap.smulRight (b.constr K χ) v : H →ₗ[K] V) =
      (LinearMap.applyₗ v : Module.End K V →ₗ[K] V) ∘ₗ
        ((toEnd K P.KacMoodyAlgebra V : P.KacMoodyAlgebra →ₗ[K] Module.End K V) ∘ₗ h P) :=
    b.ext fun i ↦ by
      have := Module.End.mem_eigenspace_iff.mp (hv i)
      simp only [T, toEnd_apply_apply] at this
      rw [LinearMap.smulRight_apply, Basis.constr_basis, hb]
      simp [this]
  intro a
  have := LinearMap.congr_fun hext a
  simp only [LinearMap.smulRight_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.applyₗ_apply_apply, LieHom.coe_toLinearMap, toEnd_apply_apply] at this
  exact this.symm

/-- For `A` of finite type, every finite-dimensional `𝔤(A)`-module is integrable. -/
theorem isIntegrable_of_finiteDimensional : IsIntegrable P V where
  isHDiagonalizable := isHDiagonalizable_of_finiteDimensional hA
  exists_pow_e_eq_zero i v := by
    obtain ⟨n, hn⟩ := isNilpotent_toEnd_e (P := P) (V := V) hA.isGeneralizedCartan i
    exact ⟨n, by rw [hn, LinearMap.zero_apply]⟩
  exists_pow_f_eq_zero i v := by
    obtain ⟨n, hn⟩ := isNilpotent_toEnd_f (P := P) (V := V) hA.isGeneralizedCartan i
    exact ⟨n, by rw [hn, LinearMap.zero_apply]⟩

/-- For `A` of finite type, every finite-dimensional `𝔤(A)`-module lies in the category `𝒪`. -/
theorem isCategoryO_of_finiteDimensional : IsCategoryO P V where
  iSup_weightSpaceOfMap_eq_top := isHDiagonalizable_of_finiteDimensional hA
  finiteDimensional_weightSpaceOfMap _ := inferInstance
  exists_finset := by
    have hind := iSupIndep_weightSpaceOfMap (M := V) (h P)
    have := hind.fintypeNeBotOfFiniteDimensional
    have hfin : {μ | weightSpaceOfMap V (h P) μ ≠ ⊥}.Finite :=
      Set.finite_coe_iff.mp (inferInstance : Finite {μ // weightSpaceOfMap V (h P) μ ≠ ⊥})
    exact ⟨hfin.toFinset, fun μ hμ ↦ ⟨μ, hfin.mem_toFinset.mpr hμ, 0, le_rfl, by simp⟩⟩

variable (V) in
open scoped Classical in
/-- **Weyl's complete reducibility theorem** for `𝔤(A)`, `A` of finite type ([Kac] §10.7
(check); [Hum] §6.3, Thm.): over a field of characteristic zero, every finite-dimensional
`𝔤(A)`-module `V` is the internal direct sum of a family of submodules, each isomorphic to `L(Λ)`
for some dominant integral `Λ`. We deduce it from complete reducibility of integrable modules in
the category `𝒪` ([Kac] Thm. 10.7). -/
theorem exists_isInternal_irreducibleModule_of_finiteDimensional :
    ∃ s : Set (LieSubmodule K P.KacMoodyAlgebra V),
      DirectSum.IsInternal (fun N : s ↦ (N : Submodule K V)) ∧
      ∀ N ∈ s, ∃ Λ, P.IsDominantIntegral Λ ∧
        Nonempty (N ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ) :=
  IsCategoryO.exists_isInternal_irreducibleModule hA.isGeneralizedCartan hA.isSymmetrizable
    (isCategoryO_of_finiteDimensional hA) (isIntegrable_of_finiteDimensional hA)

variable (V) in
/-- **Weyl's theorem** for `𝔤(A)`, `A` of finite type ([Hum] §6.3, Thm.): over a field of
characteristic zero, every submodule of a finite-dimensional `𝔤(A)`-module has a complementary
submodule. -/
theorem complementedLattice_of_finiteDimensional :
    ComplementedLattice (LieSubmodule K P.KacMoodyAlgebra V) :=
  IsCategoryO.complementedLattice hA.isGeneralizedCartan hA.isSymmetrizable
    (isCategoryO_of_finiteDimensional hA) (isIntegrable_of_finiteDimensional hA)

end Matrix.Realization.KacMoodyAlgebra
