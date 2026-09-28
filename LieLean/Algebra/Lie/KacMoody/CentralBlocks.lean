/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaCentralCharacter
import LieLean.Algebra.Lie.KacMoody.CategoryOSubmodule
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# Genuine generalized full-central-character submodules

## Main definitions
`centralBlock` is the intersection of Mathlib's maximal generalized eigenspaces for
EVERY element of the full enveloping centre, indexed by algebra characters.

## Main results
Naturality, reflection under injections, left exactness, independence and scalar-action
identification. Category O implies local finiteness of the full centre; over an algebraically
closed field this proves surjective lifting and actual short exactness of block restriction.
These are reconstructed arguments; no primary source was consulted.
No assertion about Harish-Chandra, linkage classification, or Casimir blocks is made.
-/

open Module LieModule
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra
open VermaModule
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {U V W : Type*}
  [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- Every Lie-module map intertwines the actual enveloping action. -/
theorem map_rep (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (u : 𝓤) (v : V) :
    f (rep P V u v) = rep P W u (f v) := by
  induction u using UniversalEnvelopingAlgebra.induction generalizing v with
  | algebraMap c => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι x => simp only [rep_ι, LieModuleHom.map_lie]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Central action commutes with every enveloping action. -/
theorem rep_center_commute (z : 𝓩) (u : 𝓤) :
    Commute (rep P V (z : 𝓤)) (rep P V u) := by
  change rep P V (z : 𝓤) * rep P V u = rep P V u * rep P V (z : 𝓤)
  rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.mp z.property u]

/-- The actual simultaneous generalized character space, stable under the full Lie action.
Each vector may have a different nilpotence exponent for each central element. -/
def centralBlock (V : Type*) [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (χ : 𝓩 →ₐ[K] K) : LieSubmodule K P.KacMoodyAlgebra V where
  toSubmodule := ⨅ z : 𝓩, (rep P V (z : 𝓤)).maxGenEigenspace (χ z)
  lie_mem := by
    intro x v hv
    change v ∈ (⨅ z : 𝓩, (rep P V (z : 𝓤)).maxGenEigenspace (χ z)) at hv
    change ⁅x, v⁆ ∈ (⨅ z : 𝓩, (rep P V (z : 𝓤)).maxGenEigenspace (χ z))
    simp only [Submodule.mem_iInf] at hv ⊢
    intro z
    simpa only [rep_ι, SetLike.mem_coe] using Module.End.mapsTo_maxGenEigenspace_of_comm
      (rep_center_commute P z (UniversalEnvelopingAlgebra.ι K x)) (χ z) (hv z)

/-- Membership is simultaneous local nilpotence of all shifted central actions. -/
theorem mem_centralBlock (χ : 𝓩 →ₐ[K] K) (v : V) :
    v ∈ centralBlock P V χ ↔ ∀ z : 𝓩, ∃ n : ℕ,
      ((rep P V (z : 𝓤) - χ z • 1) ^ n) v = 0 := by
  exact Module.End.mem_iInf_maxGenEigenspace_iff _ _ _

/-- Every actual Lie-module map preserves every generalized central character. -/
theorem map_mem_centralBlock (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (χ : 𝓩 →ₐ[K] K) {v : V} (hv : v ∈ centralBlock P V χ) :
    f v ∈ centralBlock P W χ := by
  change v ∈ (⨅ z : 𝓩, (rep P V (z : 𝓤)).maxGenEigenspace (χ z)) at hv
  change f v ∈ (⨅ z : 𝓩, (rep P W (z : 𝓤)).maxGenEigenspace (χ z))
  simp only [Submodule.mem_iInf] at hv ⊢
  intro z
  exact Module.End.mapsTo_genEigenspace_of_comp (f : V →ₗ[K] W)
    (by ext v; exact (map_rep P f (z : 𝓤) v).symm) (χ z) ⊤ (hv z)

/-- Restriction of actual morphisms to full-central generalized blocks. -/
def centralBlockMap (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (χ : 𝓩 →ₐ[K] K) :
    centralBlock P V χ →ₗ⁅K,P.KacMoodyAlgebra⁆ centralBlock P W χ :=
  (f.comp (centralBlock P V χ).incl).codRestrict _
    fun v ↦ map_mem_centralBlock P f χ v.property

/-- Restriction respects identity maps. -/
theorem centralBlockMap_id (χ : 𝓩 →ₐ[K] K) :
    centralBlockMap P (LieModuleHom.id : V →ₗ⁅K,P.KacMoodyAlgebra⁆ V) χ =
      LieModuleHom.id := by
  ext; rfl

/-- Restriction respects composition of actual morphisms. -/
theorem centralBlockMap_comp (f : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V)
    (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (χ : 𝓩 →ₐ[K] K) :
    centralBlockMap P (g.comp f) χ =
      (centralBlockMap P g χ).comp (centralBlockMap P f χ) := by
  ext; rfl

/-- Block restriction preserves injections, with no finiteness assumptions. -/
theorem injective_centralBlockMap (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (hf : Function.Injective f) (χ : 𝓩 →ₐ[K] K) :
    Function.Injective (centralBlockMap P f χ) := by
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

/-- A Lie-module map intertwines all powers of shifted central operators. -/
theorem map_rep_center_sub_pow (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (z : 𝓩) (c : K) (n : ℕ) (v : V) :
    f (((rep P V (z : 𝓤) - c • 1) ^ n) v) =
      ((rep P W (z : 𝓤) - c • 1) ^ n) (f v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply, ih, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, map_rep]

/-- Injections reflect simultaneous generalized character membership. -/
theorem mem_centralBlock_of_injective (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (hf : Function.Injective f) (χ : 𝓩 →ₐ[K] K) {v : V}
    (hv : f v ∈ centralBlock P W χ) : v ∈ centralBlock P V χ := by
  rw [mem_centralBlock] at hv ⊢
  intro z
  obtain ⟨n, hn⟩ := hv z
  exact ⟨n, hf (by rw [map_rep_center_sub_pow, hn, map_zero])⟩

/-- Actual left exactness, expressed as equality of the kernel and image of restricted maps.
The injective first map is the ordinary hypothesis for a left exact sequence. -/
theorem ker_centralBlockMap_eq_range (f : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V)
    (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (hf : Function.Injective f)
    (hex : g.ker = f.range) (χ : 𝓩 →ₐ[K] K) :
    (centralBlockMap P g χ).ker = (centralBlockMap P f χ).range := by
  ext v
  constructor
  · intro hv
    have hgv : g v.val = 0 := congrArg Subtype.val hv
    have hvRange : v.val ∈ f.range := hex ▸ hgv
    obtain ⟨u, hu⟩ := hvRange
    exact ⟨⟨u, mem_centralBlock_of_injective P f hf χ (hu ▸ v.property)⟩,
      Subtype.ext hu⟩
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    have hfu : f u.val ∈ g.ker := hex.symm ▸
      (show f u.val ∈ f.range from ⟨u.val, rfl⟩)
    exact hfu

/-- Distinct characters of the full centre have disjoint generalized blocks. -/
theorem disjoint_centralBlock {χ ψ : 𝓩 →ₐ[K] K} (hne : χ ≠ ψ) :
    Disjoint (centralBlock P V χ) (centralBlock P V ψ) := by
  have hh : (χ : 𝓩 → K) ≠ (ψ : 𝓩 → K) := fun h ↦ hne (AlgHom.ext (congrFun h))
  have hd := Module.End.disjoint_iInf_maxGenEigenspace
    (fun z : 𝓩 ↦ rep P V (z : 𝓤)) hh
  rw [disjoint_iff] at hd ⊢
  ext v
  exact SetLike.ext_iff.mp hd v

/-- Full-central blocks form an independent family, not merely a pairwise-disjoint one. -/
theorem iSupIndep_centralBlock :
    iSupIndep (fun χ : 𝓩 →ₐ[K] K ↦ centralBlock P V χ) := by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  exact (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun z : 𝓩 ↦ rep P V (z : 𝓤))
    (fun z t c ↦ Module.End.mapsTo_maxGenEigenspace_of_comm
      (rep_center_commute P t (z : 𝓤)) c)).comp
    (fun _ _ h ↦ AlgHom.ext (congrFun h))

/-- A scalar central action puts the entire module in the corresponding genuine block. -/
theorem centralBlock_eq_top_of_scalar (χ : 𝓩 →ₐ[K] K)
    (hχ : ∀ (z : 𝓩) (v : V), rep P V (z : 𝓤) v = χ z • v) :
    centralBlock P V χ = ⊤ := by
  apply top_unique
  intro v _
  rw [mem_centralBlock]
  intro z
  exact ⟨1, by simp [hχ]⟩

/-- Honest local finiteness of the full centre: every vector belongs to some finite-dimensional
central-invariant vector subspace. This does not assume any block decomposition. -/
def IsCentralLocallyFinite (V : Type*) [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] : Prop :=
  ∀ v : V, ∃ p : Submodule K V, FiniteDimensional K p ∧ v ∈ p ∧
    ∀ z : 𝓩, Set.MapsTo (rep P V (z : 𝓤)) p p

/-- Central action preserves each Cartan weight space, by centrality alone. -/
theorem rep_center_mem_weightSpace (z : 𝓩) (μ : Dual K H) {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) μ) :
    rep P V (z : 𝓤) v ∈ weightSpaceOfMap V (h P) μ := by
  intro a
  have hc := congrArg (fun t : Module.End K V ↦ t v)
    (rep_center_commute P (V := V) z (UniversalEnvelopingAlgebra.ι K (h P a))).eq
  simpa only [Module.End.mul_apply, rep_ι, hv a, map_smul] using hc.symm

/-- The actual category-O axioms imply local finiteness for the whole centre.
Only finite-dimensionality and spanning of Cartan weight spaces are used. -/
theorem IsCategoryO.isCentralLocallyFinite (hV : IsCategoryO P V) :
    IsCentralLocallyFinite P V := by
  intro v
  have hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := by
    rw [hV.iSup_weightSpaceOfMap_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun v ↦ ∃ p : Submodule K V,
    FiniteDimensional K p ∧ v ∈ p ∧
      ∀ z : 𝓩, Set.MapsTo (rep P V (z : 𝓤)) p p) hv ?_ ?_ ?_
  · intro μ v hv
    exact ⟨weightSpaceOfMap V (h P) μ, hV.finiteDimensional_weightSpaceOfMap μ,
      hv, fun z _ hx ↦ rep_center_mem_weightSpace P z μ hx⟩
  · exact ⟨⊥, inferInstance, by simp, fun z ↦ by simp [Set.MapsTo]⟩
  · rintro x y ⟨p, hp, hxp, hpc⟩ ⟨q, hq, hyq, hqc⟩
    let := hp
    let := hq
    refine ⟨p ⊔ q, inferInstance,
      Submodule.add_mem_sup hxp hyq, ?_⟩
    intro z t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp ht
    rw [map_add]
    exact Submodule.add_mem_sup (hpc z ha) (hqc z hb)

/-- Surjective maps lift genuine generalized central characters when the source is locally
finite under the centre and the field is algebraically closed. Reconstructed from the
finite-dimensional simultaneous generalized eigenspace decomposition in Mathlib; no block
spanning or decomposition conclusion is assumed as a hypothesis. -/
theorem surjective_centralBlockMap [IsAlgClosed K]
    (hV : IsCentralLocallyFinite P V) (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (hf : Function.Surjective f) (χ : 𝓩 →ₐ[K] K) :
    Function.Surjective (centralBlockMap P f χ) := by
  intro w
  obtain ⟨v, hv⟩ := hf w.val
  obtain ⟨p, hp, hvp, hpc⟩ := hV v
  let := hp
  let T (z : 𝓩) : Module.End K p := (rep P V (z : 𝓤)).restrict (hpc z)
  let E (μ : 𝓩 → K) : Submodule K p := ⨅ z, (T z).maxGenEigenspace (μ z)
  let F (μ : 𝓩 → K) : Submodule K W :=
    ⨅ z : 𝓩, (rep P W (z : 𝓤)).maxGenEigenspace (μ z)
  let g : p →ₗ[K] W := (f : V →ₗ[K] W).comp p.subtype
  have hT : Pairwise (fun z t ↦ Commute (T z) (T t)) := by
    intro z t _
    ext x
    exact congrArg (fun a : Module.End K V ↦ a x.val)
      (rep_center_commute P (V := V) z (t : 𝓤)).eq
  have htop : ⨆ μ, E μ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      T hT (fun z ↦ (T z).iSup_maxGenEigenspace_eq_top)
  have hF : iSupIndep F :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
      (fun z : 𝓩 ↦ rep P W (z : 𝓤))
      (fun z t c ↦ Module.End.mapsTo_maxGenEigenspace_of_comm
        (rep_center_commute P t (z : 𝓤)) c)
  have hmap (μ : 𝓩 → K) : (E μ).map g ≤ F μ := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [E, F, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
    intro z
    exact Module.End.mapsTo_genEigenspace_of_comp (f := T z) g
      (by ext x; exact (map_rep P f (z : 𝓤) x.val).symm) (μ z) ⊤ (hx z)
  have hw : w.val ∈ ⨆ μ, (E μ).map g := by
    rw [← Submodule.map_iSup, htop]
    exact ⟨⟨v, hvp⟩, Submodule.mem_top, hv⟩
  have hwχ : w.val ∈ (E (χ : 𝓩 → K)).map g :=
    hF.mem_of_mem_iSup_of_le hmap w.property hw
  obtain ⟨x, hx, hgx⟩ := hwχ
  have hxV : x.val ∈ centralBlock P V χ := by
    change x.val ∈ ⨅ z : 𝓩, (rep P V (z : 𝓤)).maxGenEigenspace (χ z)
    simp only [E, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
    intro z
    exact Module.End.mapsTo_genEigenspace_of_comp (f := T z) p.subtype
      (by ext; rfl) (χ z) ⊤ (hx z)
  exact ⟨⟨x.val, hxV⟩, Subtype.ext hgx⟩

/-- Actual category-O surjective lifting for the full centre, not for a Casimir surrogate. -/
theorem IsCategoryO.surjective_centralBlockMap [IsAlgClosed K]
    (hV : IsCategoryO P V) (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (hf : Function.Surjective f) (χ : 𝓩 →ₐ[K] K) :
    Function.Surjective (centralBlockMap P f χ) :=
  KacMoodyAlgebra.surjective_centralBlockMap P (hV.isCentralLocallyFinite P) f hf χ

/-- A generalized central block of a category-O module is again in category O. -/
theorem IsCategoryO.centralBlock (hV : IsCategoryO P V) (χ : 𝓩 →ₐ[K] K) :
    IsCategoryO P (centralBlock P V χ) :=
  hV.lieSubmodule _

/-- Full-central block restriction preserves actual short exact sequences in category O
over an algebraically closed field. Only the middle term needs the category-O hypothesis;
left exactness is unconditional, and local finiteness of that term gives the last surjection. -/
theorem IsCategoryO.shortExact_centralBlockMap [IsAlgClosed K]
    (hV : IsCategoryO P V) (f : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V)
    (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (hf : Function.Injective f)
    (hex : g.ker = f.range) (hg : Function.Surjective g) (χ : 𝓩 →ₐ[K] K) :
    Function.Injective (centralBlockMap P f χ) ∧
      (centralBlockMap P g χ).ker = (centralBlockMap P f χ).range ∧
      Function.Surjective (centralBlockMap P g χ) :=
  ⟨injective_centralBlockMap P f hf χ, ker_centralBlockMap_eq_range P f g hf hex χ,
    hV.surjective_centralBlockMap P g hg χ⟩

variable [CharZero K]

/-- The constructed Verma character identifies its full-central generalized block as all of M. -/
theorem centralBlock_verma (Λ : Dual K H) :
    centralBlock P (VermaModule P Λ) (centralCharacter P Λ) = ⊤ := by
  apply centralBlock_eq_top_of_scalar
  intro z v
  exact (map_smul_eq_rep P Λ LieModuleHom.id (z : 𝓤) v).symm.trans
    (centralCharacter_smul P Λ z v)

/-- Surjective highest-weight images lie entirely in the constructed Verma-character block. -/
theorem centralBlock_eq_top_of_verma_surjective (Λ : Dual K H)
    (f : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hf : Function.Surjective f) :
    centralBlock P V (centralCharacter P Λ) = ⊤ :=
  centralBlock_eq_top_of_scalar P _ (rep_center_eq_of_surjective P Λ f hf)

/-- The actual irreducible highest-weight quotient lies in its constructed central block. -/
theorem centralBlock_irreducible (Λ : Dual K H) :
    centralBlock P (IrreducibleModule P Λ) (centralCharacter P Λ) = ⊤ :=
  centralBlock_eq_top_of_verma_surjective P Λ (LieSubmodule.Quotient.mk' _)
    (LieSubmodule.Quotient.surjective_mk' _)

omit [CharZero K] in
/-- A module entirely in one full-central block has zero block at any distinct character. -/
theorem centralBlock_eq_bot_of_ne {χ ψ : 𝓩 →ₐ[K] K} (hne : χ ≠ ψ)
    (hχ : centralBlock P V χ = ⊤) : centralBlock P V ψ = ⊥ := by
  have hd := disjoint_centralBlock P (V := V) hne
  simpa only [hχ, top_inf_eq] using hd.eq_bot

/-- A Verma module has no generalized part for a distinct full-centre character.
This does not claim that distinct highest weights have distinct characters. -/
theorem centralBlock_verma_eq_bot (Λ : Dual K H) (ψ : 𝓩 →ₐ[K] K)
    (hne : centralCharacter P Λ ≠ ψ) : centralBlock P (VermaModule P Λ) ψ = ⊥ :=
  centralBlock_eq_bot_of_ne P hne (centralBlock_verma P Λ)

/-- The analogous wrong-character vanishing for the irreducible quotient. -/
theorem centralBlock_irreducible_eq_bot (Λ : Dual K H) (ψ : 𝓩 →ₐ[K] K)
    (hne : centralCharacter P Λ ≠ ψ) : centralBlock P (IrreducibleModule P Λ) ψ = ⊥ :=
  centralBlock_eq_bot_of_ne P hne (centralBlock_irreducible P Λ)

end Matrix.Realization.KacMoodyAlgebra
