/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNaturalNilpotent
import LieLean.Algebra.Lie.UniversalEnveloping.Filtration
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Lifting morphisms into `(U / I)^{ad} ⊗ W`

Let `π : X → Y` be a surjective morphism of Lie modules over a field, where every element of
`X` lies in a finite-dimensional Lie submodule and the finite-dimensional Lie submodules of `X`
are semisimple (their lattices of Lie submodules are complemented). Then every morphism from a
finite-dimensional module `V` to `Y` lifts along `π` (`LieModuleHom.exists_comp_eq_of_surjective`).

For a finite-dimensional Lie algebra `L` the adjoint module `U(L)^{ad}` is locally finite: the
PBW filtration consists of finite-dimensional Lie submodules (`adFiltration`), so the same holds
for `U(L)^{ad} ⊗ W` with `W` finite-dimensional (`exists_finiteDimensional_mem_adRegular_tensor`).
This is the input that lets a morphism `V → (U / I)^{ad} ⊗ W`, i.e. a natural transformation on
`U / I`-modules, be extended to a natural transformation on all modules (Humphreys, proof of
Theorem 10.7 (a)).

## Main results

* `LieModuleHom.exists_comp_eq_of_surjective`.
* `UniversalEnvelopingAlgebra.adFiltration`, `finiteDimensional_adFiltration`.
* `UniversalEnvelopingAlgebra.exists_finiteDimensional_mem_adRegular_tensor`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct Module

namespace LieModuleHom

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {X Y V : Type*} [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X]
  [AddCommGroup Y] [Module K Y] [LieRingModule L Y] [LieModule K L Y]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

omit [LieAlgebra K L] [LieModule K L X] [LieModule K L Y] [LieModule K L V] in
/-- **Lifting along a surjection of locally finite semisimple modules**: if every element of `X`
lies in a finite-dimensional Lie submodule and finite-dimensional Lie submodules of `X` are
semisimple, every morphism from a finite-dimensional module to `Y` lifts along a surjection
`π : X → Y`. -/
theorem exists_comp_eq_of_surjective (π : X →ₗ⁅K,L⁆ Y) (hπ : Function.Surjective π)
    (hX : ∀ x : X, ∃ N : LieSubmodule K L X, x ∈ N ∧ FiniteDimensional K N)
    (hC : ∀ N : LieSubmodule K L X, FiniteDimensional K N →
      ComplementedLattice (LieSubmodule K L N))
    [FiniteDimensional K V] (f : V →ₗ⁅K,L⁆ Y) : ∃ g : V →ₗ⁅K,L⁆ X, π.comp g = f := by
  let b := Module.finBasis K V
  choose x hx using fun i ↦ hπ (f (b i))
  choose N hxN hN using fun i ↦ hX (x i)
  let S : LieSubmodule K L X := ⨆ i, N i
  have hxS : ∀ i, x i ∈ S := fun i ↦ LieSubmodule.mem_iSup_of_mem i (hxN i)
  have : FiniteDimensional K S := by
    change FiniteDimensional K (S : Submodule K X)
    rw [LieSubmodule.iSup_toSubmodule]
    exact Submodule.finiteDimensional_iSup _
  have := hC S inferInstance
  let πS : S →ₗ⁅K,L⁆ Y := π.comp S.incl
  obtain ⟨C, hCk⟩ := exists_isCompl πS.ker
  let e₀ : C →ₗ⁅K,L⁆ πS.range := codRestrict πS.range (πS.comp C.incl) fun c ↦
    (πS.mem_range _).mpr ⟨c, rfl⟩
  have he₀ : Function.Bijective e₀ := by
    constructor
    · intro c c' h
      have h' : πS (c - c' : C) = 0 := by
        have := congrArg Subtype.val h
        simp only [e₀, codRestrict_apply, comp_apply] at this
        rw [LieSubmodule.coe_sub, map_sub, sub_eq_zero]
        exact this
      have hk : ((c - c' : C) : S) ∈ πS.ker := h'
      have hmem : ((c - c' : C) : S) ∈ πS.ker ⊓ C := ⟨hk, (c - c').2⟩
      rw [hCk.inf_eq_bot, LieSubmodule.mem_bot] at hmem
      exact sub_eq_zero.mp (Subtype.ext hmem)
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := (πS.mem_range y).mp hy
      have hs : s ∈ πS.ker ⊔ C := by rw [hCk.sup_eq_top]; exact LieSubmodule.mem_top s
      obtain ⟨a, ha, c, hc, rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hs
      refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
      simp only [e₀, codRestrict_apply, comp_apply, LieSubmodule.incl_apply]
      rw [map_add, (LieModuleHom.mem_ker).mp ha, zero_add]
  let e := LieModuleEquiv.ofBijective e₀ he₀
  have hf : ∀ v, f v ∈ πS.range := by
    intro v
    rw [← b.sum_repr v, map_sum]
    refine Submodule.sum_mem (πS.range : Submodule K Y) fun i _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem (πS.range : Submodule K Y) _
      ((πS.mem_range _).mpr ⟨⟨x i, hxS i⟩, hx i⟩)
  refine ⟨S.incl.comp (C.incl.comp ((e.symm : πS.range →ₗ⁅K,L⁆ C).comp
    (codRestrict πS.range f hf))), ?_⟩
  ext v
  exact congrArg Subtype.val (e.apply_symm_apply (codRestrict πS.range f hf v))

end LieModuleHom

namespace UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The `n`-th piece of the PBW filtration as a Lie submodule of the adjoint module. -/
def adFiltration (n : ℕ) : LieSubmodule R L (AdRegular R L) where
  toSubmodule := (filtration R L n).comap (AdRegular.equiv R L).toLinearMap
  lie_mem {x u} hu := by
    change AdRegular.equiv R L ⁅x, u⁆ ∈ filtration R L n
    rw [AdRegular.equiv_lie]
    exact commutator_mem_filtration_of_mem_one (ι_mem_filtration_one x) hu

variable {R L}

theorem mem_adFiltration {n : ℕ} {u : AdRegular R L} :
    u ∈ adFiltration R L n ↔ AdRegular.equiv R L u ∈ filtration R L n := Iff.rfl

variable {K : Type*} [Field K] [LieAlgebra K L]

instance finiteDimensional_adFiltration [FiniteDimensional K L] (n : ℕ) :
    FiniteDimensional K (adFiltration K L n) := by
  have hfg : (filtration K L n).FG := by
    refine Submodule.FG.pow (Submodule.FG.sup ⟨{1}, by simp [Submodule.one_eq_span]⟩ ?_) n
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  change FiniteDimensional K ((filtration K L n).comap (AdRegular.equiv K L).toLinearMap)
  rw [Submodule.comap_equiv_eq_map_symm]
  have : FiniteDimensional K (filtration K L n) := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.iff_fg.mpr (hfg.map _)

/-- For `L` and `W` finite-dimensional, every element of `U(L)^{ad} ⊗ W` lies in a
finite-dimensional Lie submodule. -/
theorem exists_finiteDimensional_mem_adRegular_tensor [FiniteDimensional K L]
    {W : Type*} [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
    [FiniteDimensional K W] (t : AdRegular K L ⊗[K] W) :
    ∃ N : LieSubmodule K L (AdRegular K L ⊗[K] W), t ∈ N ∧ FiniteDimensional K N := by
  induction t with
  | add s t hs ht =>
    obtain ⟨N, hsN, hN⟩ := hs
    obtain ⟨N', htN', hN'⟩ := ht
    refine ⟨N ⊔ N', add_mem (LieSubmodule.mem_sup_left hsN) (LieSubmodule.mem_sup_right htN'),
      ?_⟩
    have h := Submodule.finiteDimensional_sup (N : Submodule K (AdRegular K L ⊗[K] W)) N'
    rwa [← LieSubmodule.sup_toSubmodule] at h
  | tmul u w =>
    obtain ⟨n, hn⟩ := exists_mem_filtration (AdRegular.equiv K L u)
    let φ := TensorProduct.LieModule.map (adFiltration K L n).incl
      (LieModuleHom.id : W →ₗ⁅K,L⁆ W)
    refine ⟨φ.range, (φ.mem_range _).mpr ⟨⟨u, hn⟩ ⊗ₜ w, rfl⟩, ?_⟩
    change FiniteDimensional K
      (LinearMap.range (φ : adFiltration K L n ⊗[K] W →ₗ[K] AdRegular K L ⊗[K] W))
    have : FiniteDimensional K (adFiltration K L n ⊗[K] W) := inferInstance
    exact LinearMap.finiteDimensional_range _

end UniversalEnvelopingAlgebra
