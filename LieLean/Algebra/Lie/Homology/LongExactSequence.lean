/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Comparison
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.Basic

/-!
# Exact coefficient sequences for Lie algebra homology

## Main results

* `coefficientChainSequence_shortExact`: short exact coefficient sequences induce short exact
  sequences of the actual Chevalley–Eilenberg complexes whenever their exterior powers are flat.
* `homologyConnecting`: the connecting map on the concrete CE homology modules.
* `homologyMap_exact`, `homologyMap_connecting_exact`, `connecting_homologyMap_exact`:
  the three exactness assertions of the long exact coefficient sequence.
* `homologyConnectingEquiv`: dimension shifting when the two middle-module homology groups vanish.

## References

Reconstructed from flatness of tensor products and Mathlib's homology sequence. No acyclicity
of Verma modules, BGG exactness, or Cartan-equivariance statement is assumed.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

universe u v w
variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M N P : Type w}
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]
variable (f : M →ₗ⁅R,L⁆ N) (g : N →ₗ⁅R,L⁆ P) (hfg : Function.Exact f g)

/-- The actual CE chain maps form a short complex when the coefficient maps are exact. -/
def coefficientChainSequence : ShortComplex (ChainComplex (ModuleCat.{max u v w} R) ℕ) :=
  ShortComplex.mk (chainComplexMap f) (chainComplexMap g) (by
    ext k : 2
    change (g.toLinearMap.lTensor _).comp (f.toLinearMap.lTensor _) = 0
    rw [← LinearMap.lTensor_comp]
    have hz : g.toLinearMap.comp f.toLinearMap = 0 := by
      ext m
      exact hfg.apply_apply_eq_zero m
    rw [hz, LinearMap.lTensor_zero])

/-- Tensoring each coefficient sequence with a flat exterior power preserves short exactness.
In particular the flatness hypotheses hold over a field. -/
theorem coefficientChainSequence_shortExact
    [∀ k : ℕ, Module.Flat R (⋀[R]^k L)]
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (coefficientChainSequence f g hfg).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact Module.Flat.lTensor_exact (⋀[R]^k L) hfg
  · rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  · rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.lTensor_surjective (⋀[R]^k L) hg

private theorem exact_transport
    {S : ShortComplex (ModuleCat.{w} R)} (hS : S.Exact)
    {A B C : ModuleCat.{w} R}
    (a : S.X₁ ≅ A) (b : S.X₂ ≅ B) (c : S.X₃ ≅ C)
    (p : A ⟶ B) (q : B ⟶ C)
    (hp : S.f ≫ b.hom = a.hom ≫ p) (hq : S.g ≫ c.hom = b.hom ≫ q) :
    Function.Exact p q := by
  have hz : p ≫ q = 0 := by
    rw [← cancel_epi a.hom, ← Category.assoc, ← hp, Category.assoc, ← hq,
      ← Category.assoc, S.zero, zero_comp, comp_zero]
  let T := ShortComplex.mk p q hz
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
    (ShortComplex.exact_of_iso (ShortComplex.isoMk a b c hp.symm hq.symm) hS)

/-- Surjective coefficient maps induce surjections on degree-zero CE homology over any
commutative ring, without a flatness assumption. This is the terminal map of the sequence. -/
theorem homologyMap_zero_surjective (hg : Function.Surjective g) :
    Function.Surjective (homologyMap R L 0 g) := by
  rintro ⟨x, c, hc, rfl⟩
  rw [cycles_zero] at hc
  obtain ⟨t, rfl⟩ := hc
  obtain ⟨s, hs⟩ := LinearMap.lTensor_surjective (⋀[R]^0 L) hg t
  have hc : incl R L N 0 s ∈ cycles R L N 0 := by
    rw [cycles_zero]
    exact LinearMap.mem_range_self _ _
  refine ⟨⟨(boundaries R L N 0).mkQ (incl R L N 0 s), ⟨_, hc, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change Submodule.Quotient.mk (g.toLinearMap.lTensor _ (incl R L N 0 s)) =
    Submodule.Quotient.mk (incl R L P 0 t)
  rw [← incl_mapChains, hs]

variable [∀ k : ℕ, Module.Flat R (⋀[R]^k L)]
variable (hf : Function.Injective f) (hg : Function.Surjective g)

/-- The connecting map on concrete CE homology, obtained by the natural comparison with
Mathlib's snake-lemma connecting map. No coefficient splitting is chosen. -/
def homologyConnecting (k : ℕ) : homology R L P (k + 1) →ₗ[R] homology R L M k :=
  ((chainComplexHomologyIso R L P (k + 1)).inv ≫
    (coefficientChainSequence_shortExact f g hfg hf hg).δ (k + 1) k rfl ≫
    (chainComplexHomologyIso R L M k).hom).hom

/-- The concrete connecting map is conjugate to the categorical connecting map. -/
lemma homologyConnecting_comparison (k : ℕ) :
    (chainComplexHomologyIso R L P (k + 1)).hom ≫
        ModuleCat.ofHom (homologyConnecting f g hfg hf hg k) =
      (coefficientChainSequence_shortExact f g hfg hf hg).δ (k + 1) k rfl ≫
        (chainComplexHomologyIso R L M k).hom := by
  simp [homologyConnecting]
  rfl

include hfg hf hg in
/-- Exactness at the middle coefficient module's concrete homology, in every degree. -/
theorem homologyMap_exact (k : ℕ) :
    Function.Exact (homologyMap R L k f) (homologyMap R L k g) := by
  exact exact_transport
    ((coefficientChainSequence_shortExact f g hfg hf hg).homology_exact₂ k)
    (chainComplexHomologyIso R L M k) (chainComplexHomologyIso R L N k)
    (chainComplexHomologyIso R L P k)
    (ModuleCat.ofHom (homologyMap R L k f)) (ModuleCat.ofHom (homologyMap R L k g))
    (chainComplexHomologyIso_naturality k f) (chainComplexHomologyIso_naturality k g)

/-- Exactness at the source of the connecting map in the concrete homology sequence. -/
theorem homologyMap_connecting_exact (k : ℕ) :
    Function.Exact (homologyMap R L (k + 1) g) (homologyConnecting f g hfg hf hg k) := by
  exact exact_transport
    ((coefficientChainSequence_shortExact f g hfg hf hg).homology_exact₃ (k + 1) k rfl)
    (chainComplexHomologyIso R L N (k + 1)) (chainComplexHomologyIso R L P (k + 1))
    (chainComplexHomologyIso R L M k)
    (ModuleCat.ofHom (homologyMap R L (k + 1) g))
    (ModuleCat.ofHom (homologyConnecting f g hfg hf hg k))
    (chainComplexHomologyIso_naturality (k + 1) g)
    (homologyConnecting_comparison f g hfg hf hg k).symm

/-- Exactness at the target of the connecting map, including degree zero. -/
theorem connecting_homologyMap_exact (k : ℕ) :
    Function.Exact (homologyConnecting f g hfg hf hg k) (homologyMap R L k f) := by
  exact exact_transport
    ((coefficientChainSequence_shortExact f g hfg hf hg).homology_exact₁ (k + 1) k rfl)
    (chainComplexHomologyIso R L P (k + 1)) (chainComplexHomologyIso R L M k)
    (chainComplexHomologyIso R L N k)
    (ModuleCat.ofHom (homologyConnecting f g hfg hf hg k))
    (ModuleCat.ofHom (homologyMap R L k f))
    (homologyConnecting_comparison f g hfg hf hg k).symm
    (chainComplexHomologyIso_naturality k f)

/-- Vanishing of the middle module's upper homology makes the connecting map injective. -/
theorem homologyConnecting_injective (k : ℕ) [Subsingleton (homology R L N (k + 1))] :
    Function.Injective (homologyConnecting f g hfg hf hg k) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := (homologyMap_connecting_exact f g hfg hf hg k x).mp hx
  rw [Subsingleton.elim y 0, map_zero]
  exact Submodule.zero_mem _

/-- Vanishing of the middle module's lower homology makes the connecting map surjective. -/
theorem homologyConnecting_surjective (k : ℕ) [Subsingleton (homology R L N k)] :
    Function.Surjective (homologyConnecting f g hfg hf hg k) := by
  intro x
  exact (connecting_homologyMap_exact f g hfg hf hg k x).mp (Subsingleton.elim _ _)

/-- Dimension shifting for actual CE homology: if the middle coefficient module has zero
homology in both adjacent degrees, the connecting map is a linear equivalence. -/
def homologyConnectingEquiv (k : ℕ) [Subsingleton (homology R L N (k + 1))]
    [Subsingleton (homology R L N k)] : homology R L P (k + 1) ≃ₗ[R] homology R L M k :=
  LinearEquiv.ofBijective (homologyConnecting f g hfg hf hg k)
    ⟨homologyConnecting_injective f g hfg hf hg k,
      homologyConnecting_surjective f g hfg hf hg k⟩

end LieModule.ChevalleyEilenberg
