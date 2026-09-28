/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CentralBlocks
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Full-central decomposition and projections

## Main results
Character-indexed decomposition for locally finite central actions and natural full-Lie
projections. Arguments reconstructed; no primary source consulted.
-/

open Module LieModule
noncomputable section

namespace AlgHom
variable {K B M : Type*} [Field K] [CommRing B] [Algebra K B]
  [AddCommGroup M] [Module K M]

/-- A simultaneous scalar value modulo nilpotent operators is an algebra character.
The nilpotent inverse image is an ideal because the source algebra is commutative. -/
def characterOfNilpotent [Nontrivial M] (ρ : B →ₐ[K] Module.End K M)
    (μ : B → K) (hμ : ∀ z, IsNilpotent (ρ (z - algebraMap K B (μ z)))) : B →ₐ[K] K := by
  let I : Ideal B :=
    { carrier := {z | IsNilpotent (ρ z)}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simpa only [Set.mem_ofPred_eq, map_add] using
          ((Commute.all x y).map ρ).isNilpotent_add hx hy
      smul_mem' := by
        intro x y hy
        simpa only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] using
          ((Commute.all x y).map ρ).isNilpotent_mul_left hy }
  have hI : I ≠ ⊤ := by
    intro h
    have hn : IsNilpotent (ρ (1 : B)) := (show (1 : B) ∈ I from h ▸ Submodule.mem_top)
    exact not_isNilpotent_one (by simpa using hn)
  let := Ideal.Quotient.nontrivial_iff.mpr hI
  have hinj := FaithfulSMul.algebraMap_injective K (B ⧸ I)
  have hs (z : B) : algebraMap K (B ⧸ I) (μ z) = Ideal.Quotient.mk I z := by
    symm
    apply Ideal.Quotient.eq.mpr
    exact hμ z
  exact
    { toFun := μ
      map_zero' := hinj (by rw [hs]; simp)
      map_one' := hinj (by rw [hs]; simp)
      map_add' := fun x y ↦ hinj (by rw [map_add, hs, hs, hs, map_add])
      map_mul' := fun x y ↦ hinj (by rw [map_mul, hs, hs, hs, map_mul])
      commutes' := fun c ↦ hinj (by rw [hs]; rfl) }

/-- Every nonzero finite-dimensional joint generalized spectral space of a commutative
algebra representation has an algebra character as its spectral function. Reconstructed. -/
theorem exists_character_of_joint_ne_bot [FiniteDimensional K M]
    (ρ : B →ₐ[K] Module.End K M) (μ : B → K)
    (hne : (⨅ z, (ρ z).maxGenEigenspace (μ z)) ≠ ⊥) :
    ∃ χ : B →ₐ[K] K, (χ : B → K) = μ := by
  let E : Submodule K M := ⨅ z, (ρ z).maxGenEigenspace (μ z)
  have hE (z : B) : Set.MapsTo (ρ z) E E := by
    intro x hx
    simp only [E, Submodule.mem_iInf, SetLike.mem_coe] at hx ⊢
    intro t
    exact Module.End.mapsTo_maxGenEigenspace_of_comm
      ((Commute.all t z).map ρ) (μ t) (hx t)
  let τ : B →ₐ[K] Module.End K E :=
    { toFun := fun z ↦ (ρ z).restrict (hE z)
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intros; ext; simp; rfl
      map_mul' := by intros; ext; simp; rfl
      commutes' := by intro c; ext; simp }
  have hn (z : B) : IsNilpotent (τ (z - algebraMap K B (μ z))) := by
    have hh : Set.MapsTo (ρ z - algebraMap K (Module.End K M) (μ z)) E E :=
      fun x hx ↦ E.sub_mem (hE z hx) (E.smul_mem _ hx)
    have heq : τ (z - algebraMap K B (μ z)) =
        (ρ z - algebraMap K (Module.End K M) (μ z)).restrict hh := by
      ext; simp [τ]; rfl
    rw [heq]
    exact Module.End.isNilpotent_restrict_of_le (iInf_le _ z)
      ((ρ z).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (μ z))
  let := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact ⟨characterOfNilpotent τ μ hn, rfl⟩

/-- Character-indexed simultaneous generalized eigenspaces span a finite-dimensional
representation of a commutative algebra over an algebraically closed field. -/
theorem iSup_joint_character_eq_top [FiniteDimensional K M] [IsAlgClosed K]
    (ρ : B →ₐ[K] Module.End K M) :
    (⨆ χ : B →ₐ[K] K, ⨅ z, (ρ z).maxGenEigenspace (χ z)) = ⊤ := by
  have ht :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun z ↦ ρ z) (fun z t _ ↦ (Commute.all z t).map ρ)
      (fun z ↦ (ρ z).iSup_maxGenEigenspace_eq_top)
  apply top_unique
  rw [← ht]
  refine iSup_le fun μ ↦ ?_
  by_cases he : (⨅ z, (ρ z).maxGenEigenspace (μ z)) = ⊥
  · rw [he]; exact bot_le
  obtain ⟨χ, rfl⟩ := ρ.exists_character_of_joint_ne_bot μ he
  exact le_iSup (fun χ : B →ₐ[K] K ↦ ⨅ z, (ρ z).maxGenEigenspace (χ z)) χ

end AlgHom

namespace Matrix.Realization.KacMoodyAlgebra
open VermaModule
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

variable [IsAlgClosed K]

/-- Local finiteness under the entire centre implies character-indexed spanning.
Only the chosen central-invariant subspaces, not the whole module, are finite-dimensional. -/
theorem iSup_centralBlock_eq_top (hV : IsCentralLocallyFinite P V) :
    (⨆ χ : 𝓩 →ₐ[K] K, (centralBlock P V χ).toSubmodule) = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨p, hp, hvp, hpc⟩ := hV v
  let := hp
  let τ : 𝓩 →ₐ[K] Module.End K p :=
    { toFun := fun z ↦ (rep P V (z : 𝓤)).restrict (hpc z)
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intros; ext; simp; rfl
      map_mul' := by intros; ext; simp; rfl
      commutes' := by intro c; ext; simp }
  have hv : (⟨v, hvp⟩ : p) ∈ ⨆ χ : 𝓩 →ₐ[K] K, ⨅ z, (τ z).maxGenEigenspace (χ z) := by
    rw [τ.iSup_joint_character_eq_top]; trivial
  have hm : (⨆ χ : 𝓩 →ₐ[K] K, ⨅ z, (τ z).maxGenEigenspace (χ z)).map p.subtype ≤
      ⨆ χ : 𝓩 →ₐ[K] K, (centralBlock P V χ).toSubmodule := by
    rw [Submodule.map_iSup]
    refine iSup_le fun χ ↦ le_trans ?_ (le_iSup _ χ)
    rintro _ ⟨x, hx, rfl⟩
    change x.val ∈ ⨅ z : 𝓩, (rep P V (z : 𝓤)).maxGenEigenspace (χ z)
    simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
    intro z
    exact Module.End.mapsTo_genEigenspace_of_comp (f := τ z) p.subtype
      (by ext; rfl) (χ z) ⊤ (hx z)
  exact hm (Submodule.mem_map_of_mem hv)

open Classical in
/-- The actual full-centre generalized blocks form an internal direct sum. -/
theorem isInternal_centralBlock (hV : IsCentralLocallyFinite P V) :
    DirectSum.IsInternal (fun χ : 𝓩 →ₐ[K] K ↦ (centralBlock P V χ).toSubmodule) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_centralBlock P))
    (iSup_centralBlock_eq_top P hV)

open Classical in
/-- Category O has a full-central character-indexed internal direct-sum decomposition. -/
theorem IsCategoryO.isInternal_centralBlock (hV : IsCategoryO P V) :
    DirectSum.IsInternal
      (fun χ : 𝓩 →ₐ[K] K ↦ (KacMoodyAlgebra.centralBlock P V χ).toSubmodule) :=
  KacMoodyAlgebra.isInternal_centralBlock P (hV.isCentralLocallyFinite P)

/-- The linear coordinate map into one actual full-central block. -/
def centralBlockComponent (hV : IsCentralLocallyFinite P V) (χ : 𝓩 →ₐ[K] K) :
    V →ₗ[K] centralBlock P V χ := by
  classical
  let := (isInternal_centralBlock P hV).chooseDecomposition
  exact
    { toFun := fun v ↦ DirectSum.decompose (fun ψ ↦ (centralBlock P V ψ).toSubmodule) v χ
      map_add' := fun x y ↦ by simp
      map_smul' := fun c v ↦ by simp; rfl }

/-- A coordinate is the identity on its own generalized central block. -/
theorem centralBlockComponent_self (hV : IsCentralLocallyFinite P V)
    (χ : 𝓩 →ₐ[K] K) {v : V} (hv : v ∈ centralBlock P V χ) :
    (centralBlockComponent P hV χ v : V) = v := by
  classical
  let := (isInternal_centralBlock P hV).chooseDecomposition
  exact DirectSum.decompose_of_mem_same (fun ψ ↦ (centralBlock P V ψ).toSubmodule) hv

/-- A coordinate vanishes on each distinct generalized central block. -/
theorem centralBlockComponent_other (hV : IsCentralLocallyFinite P V)
    {χ ψ : 𝓩 →ₐ[K] K} (hne : ψ ≠ χ) {v : V} (hv : v ∈ centralBlock P V ψ) :
    centralBlockComponent P hV χ v = 0 := by
  classical
  let := (isInternal_centralBlock P hV).chooseDecomposition
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne (fun ψ ↦ (centralBlock P V ψ).toSubmodule) hv hne

/-- The block coordinate intertwines the full Lie algebra, not just the centre. -/
theorem centralBlockComponent_lie (hV : IsCentralLocallyFinite P V)
    (χ : 𝓩 →ₐ[K] K) (x : P.KacMoodyAlgebra) (v : V) :
    centralBlockComponent P hV χ ⁅x, v⁆ = ⁅x, centralBlockComponent P hV χ v⁆ := by
  classical
  have hv : v ∈ ⨆ ψ : 𝓩 →ₐ[K] K, (centralBlock P V ψ).toSubmodule := by
    rw [iSup_centralBlock_eq_top P hV]; trivial
  refine Submodule.iSup_induction _ (motive := fun v ↦
    centralBlockComponent P hV χ ⁅x, v⁆ = ⁅x, centralBlockComponent P hV χ v⁆)
    hv ?_ ?_ ?_
  · intro ψ v hv
    by_cases h : ψ = χ
    · subst ψ
      apply Subtype.ext
      change (centralBlockComponent P hV χ ⁅x, v⁆ : V) =
        ⁅x, (centralBlockComponent P hV χ v : V)⁆
      rw [centralBlockComponent_self P hV χ ((centralBlock P V χ).lie_mem hv),
        centralBlockComponent_self P hV χ hv]
    · rw [centralBlockComponent_other P hV h ((centralBlock P V ψ).lie_mem hv),
        centralBlockComponent_other P hV h hv, lie_zero]
  · simp
  · intro a b ha hb
    simp only [lie_add, map_add, ha, hb]

/-- Canonical full-Lie-module idempotent projecting onto a specified central character.
It is defined for every character, including those whose block is zero. -/
def centralBlockProjection (hV : IsCentralLocallyFinite P V) (χ : 𝓩 →ₐ[K] K) :
    V →ₗ⁅K,P.KacMoodyAlgebra⁆ V :=
  (centralBlock P V χ).incl.comp
    { toLinearMap := centralBlockComponent P hV χ
      map_lie' := fun {x v} ↦ centralBlockComponent_lie P hV χ x v }

/-- The projected vector belongs to the specified generalized block. -/
theorem centralBlockProjection_mem (hV : IsCentralLocallyFinite P V)
    (χ : 𝓩 →ₐ[K] K) (v : V) :
    centralBlockProjection P hV χ v ∈ centralBlock P V χ :=
  (centralBlockComponent P hV χ v).property

/-- The projection fixes its own block pointwise. -/
theorem centralBlockProjection_self (hV : IsCentralLocallyFinite P V)
    (χ : 𝓩 →ₐ[K] K) {v : V} (hv : v ∈ centralBlock P V χ) :
    centralBlockProjection P hV χ v = v :=
  centralBlockComponent_self P hV χ hv

/-- The projection kills every other block. -/
theorem centralBlockProjection_other (hV : IsCentralLocallyFinite P V)
    {χ ψ : 𝓩 →ₐ[K] K} (hne : ψ ≠ χ) {v : V} (hv : v ∈ centralBlock P V ψ) :
    centralBlockProjection P hV χ v = 0 :=
  congrArg Subtype.val (centralBlockComponent_other P hV hne hv)

/-- Each actual full-Lie projection is idempotent. -/
theorem centralBlockProjection_idempotent (hV : IsCentralLocallyFinite P V)
    (χ : 𝓩 →ₐ[K] K) :
    (centralBlockProjection P hV χ).comp (centralBlockProjection P hV χ) =
      centralBlockProjection P hV χ := by
  ext v
  exact centralBlockProjection_self P hV χ (centralBlockProjection_mem P hV χ v)

/-- Projections commute with every actual Lie-module morphism. -/
theorem centralBlockProjection_natural (hV : IsCentralLocallyFinite P V)
    (hW : IsCentralLocallyFinite P W) (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (χ : 𝓩 →ₐ[K] K) :
    f.comp (centralBlockProjection P hV χ) = (centralBlockProjection P hW χ).comp f := by
  classical
  ext v
  have hv : v ∈ ⨆ ψ : 𝓩 →ₐ[K] K, (centralBlock P V ψ).toSubmodule := by
    rw [iSup_centralBlock_eq_top P hV]; trivial
  change f (centralBlockProjection P hV χ v) = centralBlockProjection P hW χ (f v)
  refine Submodule.iSup_induction _ (motive := fun v ↦
    f (centralBlockProjection P hV χ v) = centralBlockProjection P hW χ (f v))
    hv ?_ ?_ ?_
  · intro ψ v hv
    by_cases h : ψ = χ
    · subst ψ
      rw [centralBlockProjection_self P hV χ hv,
        centralBlockProjection_self P hW χ (map_mem_centralBlock P f χ hv)]
    · rw [centralBlockProjection_other P hV h hv,
        centralBlockProjection_other P hW h (map_mem_centralBlock P f ψ hv), map_zero]
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]

/-- The image of the idempotent is exactly the requested full-central generalized block. -/
theorem range_centralBlockProjection (hV : IsCentralLocallyFinite P V)
    (χ : 𝓩 →ₐ[K] K) : (centralBlockProjection P hV χ).range = centralBlock P V χ := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact centralBlockProjection_mem P hV χ v
  · intro v hv
    exact ⟨v, centralBlockProjection_self P hV χ hv⟩

/-- Distinct full-central projections are orthogonal. -/
theorem centralBlockProjection_comp_eq_zero (hV : IsCentralLocallyFinite P V)
    {χ ψ : 𝓩 →ₐ[K] K} (hne : ψ ≠ χ) :
    (centralBlockProjection P hV χ).comp (centralBlockProjection P hV ψ) = 0 := by
  ext v
  exact centralBlockProjection_other P hV hne (centralBlockProjection_mem P hV ψ v)

/-- Every vector is the finite sum of its projected components, with all other projections
zero. This is pointwise finite support; no finite-dimensionality of the whole module is used. -/
theorem exists_finset_sum_centralBlockProjection (hV : IsCentralLocallyFinite P V) (v : V) :
    ∃ s : Finset (𝓩 →ₐ[K] K),
      (∀ χ ∉ s, centralBlockProjection P hV χ v = 0) ∧
      ∑ χ ∈ s, centralBlockProjection P hV χ v = v := by
  classical
  let := (isInternal_centralBlock P hV).chooseDecomposition
  let d := DirectSum.decompose (fun χ ↦ (centralBlock P V χ).toSubmodule) v
  refine ⟨d.support, ?_, ?_⟩
  · intro χ hχ
    have hd : d χ = 0 := DFinsupp.notMem_support_iff.mp hχ
    exact congrArg Subtype.val hd
  · exact DirectSum.sum_support_decompose (fun χ ↦ (centralBlock P V χ).toSubmodule) v

/-- Usable category-O projection, obtained from the proved local central finiteness theorem. -/
def IsCategoryO.centralBlockProjection (hV : IsCategoryO P V) (χ : 𝓩 →ₐ[K] K) :
    V →ₗ⁅K,P.KacMoodyAlgebra⁆ V :=
  KacMoodyAlgebra.centralBlockProjection P (hV.isCentralLocallyFinite P) χ

/-- Category-O projections are natural under all Lie-module morphisms. -/
theorem IsCategoryO.centralBlockProjection_natural (hV : IsCategoryO P V)
    (hW : IsCategoryO P W) (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (χ : 𝓩 →ₐ[K] K) :
    f.comp (hV.centralBlockProjection P χ) = (hW.centralBlockProjection P χ).comp f :=
  KacMoodyAlgebra.centralBlockProjection_natural P
    (hV.isCentralLocallyFinite P) (hW.isCentralLocallyFinite P) f χ

end Matrix.Realization.KacMoodyAlgebra
