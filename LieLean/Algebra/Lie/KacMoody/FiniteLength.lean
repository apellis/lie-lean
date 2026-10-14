/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.EnoughProjectives
import LieLean.Algebra.Lie.KacMoody.HarishChandraLinkage
import LieLean.Algebra.Lie.KacMoody.CategoryOSubmodule

/-!
# Finite length in category `𝒪`

Humphreys' category `𝒪` consists of the finitely generated modules satisfying `IsCategoryO`
(GSM 94, §1.1). We prove that every such module has finite length (Humphreys, GSM 94,
Theorem 1.11): there is a strictly monotone `ℕ`-valued function on its lattice of submodules, so
the module is artinian and noetherian. We also prove that `Hom` spaces from a finitely generated
module in `𝒪` are finite-dimensional.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_strictMono_lieSubmodule`: Verma modules
  have finite length.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.exists_strictMono_lieSubmodule`,
  `IsCategoryO.wellFoundedLT_lieSubmodule`, `IsCategoryO.wellFoundedGT_lieSubmodule`: modules in
  `𝒪` have finite length, and are artinian and noetherian (Humphreys, GSM 94, Theorem 1.11).
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.finiteDimensional_hom`: `dim Hom(M, N) < ∞`
  (Humphreys, GSM 94, Theorem 1.11).

## Proof notes

For a Verma module `M(λ)` we follow Humphreys: if `N' ⊊ N` are submodules, `N/N'` has a nonzero
primitive vector of some weight `μ`; the centre acts on it by both `χ_λ` and `χ_μ`, so `μ ∈ W·λ`
(Theorem 1.10 (b)), and `N` meets `⊕_{w} M(λ)_{w·λ}` in a larger subspace than `N'` does.
Humphreys then reduces to Verma modules through Corollary 1.2; we instead use the cover of
Theorem 3.8 (`IsCategoryO.isCovered`) by finite sums of modules `M(λ + nρ) ⊗ L(nρ)^*`, which have
standard filtrations (Theorem 3.6), and glue the measures along filtrations and finite sums in the
modular lattice of submodules (reconstructed). The bound on `Hom` is reconstructed: a morphism is
determined by its restrictions to finitely many generating weight spaces.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §1.1, §1.10, §1.11.
-/

noncomputable section

open Module LieModule

/-! ### Measures on modular lattices -/

section Lattice

variable {α : Type*} [Lattice α] [IsModularLattice α]

/-- Gluing strictly monotone measures along `a ≤ b`: from measures on `[⊥, a]` and `[a, b]` we
get one on `[⊥, b]`. -/
theorem StrictMonoOn.inf_add_sup {a b : α} (hab : a ≤ b) {f g : α → ℕ}
    (hf : StrictMonoOn f (Set.Iic a)) (hg : StrictMonoOn g (Set.Icc a b)) :
    StrictMonoOn (fun x ↦ f (x ⊓ a) + g (x ⊔ a)) (Set.Iic b) := by
  intro x hx y hy hxy
  have hfx : x ⊓ a ∈ Set.Iic a := inf_le_right
  have hfy : y ⊓ a ∈ Set.Iic a := inf_le_right
  have hgx : x ⊔ a ∈ Set.Icc a b := ⟨le_sup_right, sup_le hx hab⟩
  have hgy : y ⊔ a ∈ Set.Icc a b := ⟨le_sup_right, sup_le hy hab⟩
  have h2 := hg.monotoneOn hgx hgy (sup_le_sup_right hxy.le a)
  change f (x ⊓ a) + g (x ⊔ a) < f (y ⊓ a) + g (y ⊔ a)
  by_cases he : x ⊓ a = y ⊓ a
  · have := hg hgx hgy (sup_lt_sup_of_lt_of_inf_le_inf hxy he.ge)
    rw [he]
    omega
  · have := hf hfx hfy (lt_of_le_of_ne (inf_le_inf_right a hxy.le) he)
    omega

/-- A strictly monotone measure on `[⊥, b]` gives one on `[a, a ⊔ b]`. -/
theorem StrictMonoOn.comp_inf_Icc_sup {a b : α} {g : α → ℕ} (hg : StrictMonoOn g (Set.Iic b)) :
    StrictMonoOn (fun x ↦ g (x ⊓ b)) (Set.Icc a (a ⊔ b)) := by
  intro x hx y hy hxy
  refine hg inf_le_right inf_le_right (lt_of_le_of_ne (inf_le_inf_right b hxy.le) fun he ↦
    hxy.ne ?_)
  calc x = (a ⊔ b) ⊓ x := (inf_eq_right.mpr hx.2).symm
    _ = a ⊔ b ⊓ x := sup_inf_assoc_of_le b hx.1
    _ = a ⊔ b ⊓ y := by rw [inf_comm b x, he, inf_comm]
    _ = (a ⊔ b) ⊓ y := (sup_inf_assoc_of_le b hy.1).symm
    _ = y := inf_eq_right.mpr hy.2

/-- Strictly monotone measures on `[⊥, a]` and `[⊥, b]` give one on `[⊥, a ⊔ b]`. -/
theorem StrictMonoOn.exists_Iic_sup {a b : α} {f g : α → ℕ} (hf : StrictMonoOn f (Set.Iic a))
    (hg : StrictMonoOn g (Set.Iic b)) : ∃ F : α → ℕ, StrictMonoOn F (Set.Iic (a ⊔ b)) :=
  ⟨_, hf.inf_add_sup le_sup_left hg.comp_inf_Icc_sup⟩

end Lattice

/-! ### Measures on submodule lattices -/

namespace LieSubmodule

variable {R L M N : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [AddCommGroup N] [Module R N] [LieRingModule L N]

/-- A strictly monotone measure on the submodules of `M` gives one on the submodules of `N`
contained in the range of a morphism `φ : M → N`. -/
theorem strictMonoOn_comap {f : LieSubmodule R L M → ℕ} (hf : StrictMono f)
    (φ : M →ₗ⁅R,L⁆ N) {Q : LieSubmodule R L N} (hQ : Q ≤ φ.range) :
    StrictMonoOn (fun Q' ↦ f (Q'.comap φ)) (Set.Iic Q) := by
  intro Q₁ h₁ Q₂ h₂ hlt
  refine hf (lt_of_le_of_ne (fun _ hx ↦ hlt.le hx) fun he ↦ hlt.ne ?_)
  rw [← map_comap_eq _ _ ((Set.mem_Iic.mp h₁).trans hQ),
    ← map_comap_eq _ _ ((Set.mem_Iic.mp h₂).trans hQ), he]

variable [LieAlgebra R L] [LieModule R L M]

/-- Passing to the quotient by `N` is strictly monotone on the submodules containing `N`. -/
theorem strictMonoOn_map_mk' (N : LieSubmodule R L M) :
    StrictMonoOn (fun Q ↦ Q.map (LieSubmodule.Quotient.mk' N)) (Set.Ici N) := by
  intro Q₁ h₁ Q₂ h₂ hlt
  refine lt_of_le_of_ne (map_mono hlt.le) fun he ↦ hlt.ne (le_antisymm hlt.le fun x hx ↦ ?_)
  have he' : Q₁.map (LieSubmodule.Quotient.mk' N) = Q₂.map (LieSubmodule.Quotient.mk' N) := he
  have hx' : LieSubmodule.Quotient.mk' N x ∈ Q₁.map (LieSubmodule.Quotient.mk' N) := by
    rw [he']
    exact mem_map_of_mem hx
  obtain ⟨q, hq, hqx⟩ := (mem_map _).mp hx'
  have hxq : x - q ∈ N := by
    rw [← LieSubmodule.Quotient.mk_eq_zero (N := N), map_sub, hqx, sub_self]
  have := Q₁.add_mem hq (h₁ hxq)
  rwa [add_sub_cancel] at this

end LieSubmodule

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

/-! ### Verma modules -/

section Verma

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

include hA

local notation "𝔤" => KacMoodyAlgebra P

/-- The sum `⊕_{w ∈ W} M(λ)_{w·λ}` of the weight spaces of `M(λ)` linked to `λ`. -/
def vermaLinkedSpan (Λ : Dual K H) : Submodule K (VermaModule P Λ) :=
  ⨆ w : P.weylGroup hA.isGeneralizedCartan,
    weightSpaceOfMap (VermaModule P Λ) (h P) ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho)

omit [FiniteDimensional K H] in
theorem finiteDimensional_vermaLinkedSpan (Λ : Dual K H) :
    FiniteDimensional K (vermaLinkedSpan P hA Λ) := by
  have := P.finite_weylGroup hA
  have := fun w : P.weylGroup hA.isGeneralizedCartan ↦
    (VermaModule.isCategoryO P Λ).finiteDimensional_weightSpaceOfMap
      ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho)
  exact Submodule.finiteDimensional_iSup _

/-- If `N₁ ⊊ N₂` are submodules of `M(λ)`, some vector of `N₂ \ N₁` has a weight linked to `λ`
(proof of Humphreys, GSM 94, Theorem 1.11). -/
theorem exists_mem_vermaLinkedSpan_of_lt {Λ : Dual K H}
    {N₁ N₂ : LieSubmodule K 𝔤 (VermaModule P Λ)} (hlt : N₁ < N₂) :
    ∃ x ∈ N₂, x ∉ N₁ ∧ x ∈ vermaLinkedSpan P hA Λ := by
  classical
  set Q := N₂.map (LieSubmodule.Quotient.mk' N₁)
  have hV := VermaModule.isCategoryO P Λ
  have hQ : IsCategoryO P Q := (hV.quotient N₁).lieSubmodule Q
  obtain ⟨m, hm₂, hm₁⟩ := SetLike.exists_of_lt hlt
  have hq0 : (⟨LieSubmodule.Quotient.mk' N₁ m, LieSubmodule.mem_map_of_mem hm₂⟩ : Q) ≠ 0 :=
    fun h ↦ hm₁ ((LieSubmodule.Quotient.mk_eq_zero (N := N₁)).mp (congrArg Subtype.val h))
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ, weightSpace P Q μ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Submodule K Q) = ⊥ := by
      rw [← hQ.iSup_weightSpaceOfMap_eq_top]
      exact iSup_eq_bot.mpr hcon
    exact hq0 ((Submodule.mem_bot K).mp (htop ▸ Submodule.mem_top))
  have hW : aboveSpan P Q {μ₀} ≠ ⊥ := by
    intro hb
    apply hμ₀
    rw [eq_bot_iff, ← hb]
    exact le_iSup_of_le ⟨μ₀, Finset.mem_singleton_self μ₀⟩
      (le_iSup₂_of_le (0 : ι → ℤ) le_rfl (by simp))
  obtain ⟨ν, v, hv, hv0, -⟩ := hQ.exists_primitive_mem_aboveSpan P {μ₀} hW
  have hcb : (v : VermaModule P Λ ⧸ N₁) ∈
      centralBlock P (VermaModule P Λ ⧸ N₁) (centralCharacter P Λ) := by
    obtain ⟨m', -, hm'v⟩ := (LieSubmodule.mem_map _).mp v.2
    rw [← hm'v]
    refine map_mem_centralBlock P (LieSubmodule.Quotient.mk' N₁) _ ?_
    rw [mem_centralBlock]
    intro z
    refine ⟨1, ?_⟩
    have := rep_center_map P Λ LieModuleHom.id z m'
    rw [LieModuleHom.id_apply] at this
    rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, sub_self]
  have hcb' : v ∈ centralBlock P Q (centralCharacter P Λ) :=
    mem_centralBlock_of_injective P Q.incl (LieSubmodule.injective_incl Q) _ hcb
  have hχ := centralCharacter_eq_of_mem_centralBlock P hv hv0 hcb'
  obtain ⟨w, hw, hwν⟩ := (VermaModule.centralCharacter_eq_iff P hA Λ ν).mp hχ.symm
  have hN₂ : IsCategoryO P N₂ := hV.lieSubmodule N₂
  let φ : N₂ →ₗ⁅K,𝔤⁆ Q := ((LieSubmodule.Quotient.mk' N₁).comp N₂.incl).codRestrict Q
    fun x ↦ LieSubmodule.mem_map_of_mem x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨m', hm', rfl⟩ := (LieSubmodule.mem_map _).mp hq
    exact ⟨⟨m', hm'⟩, rfl⟩
  have hvW : v ∈ weightSpace P Q ν := (mem_primitiveVectors.mp hv).1
  rw [weightSpace, ← map_weightSpace_of_surjective P hN₂.iSup_weightSpaceOfMap_eq_top φ hφ ν]
    at hvW
  obtain ⟨y, hy, hyv⟩ := hvW
  refine ⟨y.1, y.2, fun hy₁ ↦ hv0 ?_, ?_⟩
  · rw [← hyv]
    exact Subtype.ext ((LieSubmodule.Quotient.mk_eq_zero (N := N₁)).mpr hy₁)
  · have hy' : y.1 ∈ weightSpaceOfMap (VermaModule P Λ) (h P) ν :=
      map_mem_weightSpaceOfMap P N₂.incl hy
    refine (le_iSup_of_le (⟨w, hw⟩ : P.weylGroup hA.isGeneralizedCartan) ?_ :
      _ ≤ vermaLinkedSpan P hA Λ) hy'
    rw [show ((⟨w, hw⟩ : P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) = w
      from rfl, hwν, add_sub_cancel_right]

/-- **Verma modules have finite length** (Humphreys, GSM 94, proof of Theorem 1.11): the
dimension of `N ∩ ⊕_{w} M(λ)_{w·λ}` is strictly monotone in the submodule `N`. -/
theorem VermaModule.exists_strictMono_lieSubmodule (Λ : Dual K H) :
    ∃ f : LieSubmodule K 𝔤 (VermaModule P Λ) → ℕ, StrictMono f := by
  have := finiteDimensional_vermaLinkedSpan P hA Λ
  refine ⟨fun N ↦ finrank K (N.toSubmodule.comap (vermaLinkedSpan P hA Λ).subtype),
    fun N₁ N₂ hlt ↦ Submodule.finrank_lt_finrank_of_lt ?_⟩
  obtain ⟨x, hx₂, hx₁, hxV⟩ := exists_mem_vermaLinkedSpan_of_lt P hA hlt
  refine lt_of_le_of_ne (fun y hy ↦ hlt.le hy) fun he ↦ hx₁ ?_
  have hx : (⟨x, hxV⟩ : vermaLinkedSpan P hA Λ) ∈
      N₂.toSubmodule.comap (vermaLinkedSpan P hA Λ).subtype := hx₂
  rw [← he] at hx
  exact hx

variable {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

/-- A submodule with a standard filtration has finite length. -/
theorem IsStdFiltered.exists_strictMonoOn {N : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)}
    (hN : IsStdFiltered P N s) : ∃ f : LieSubmodule K 𝔤 X → ℕ, StrictMonoOn f (Set.Iic N) := by
  induction hN with
  | bot => exact ⟨fun _ ↦ 0, fun _ _ _ hy hxy ↦ absurd (hxy.trans_le hy) not_lt_bot⟩
  | @step N N' s μ _ hle he ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨e⟩ := he
    obtain ⟨g, hg⟩ := VermaModule.exists_strictMono_lieSubmodule P hA μ
    set R := N'.map (LieSubmodule.Quotient.mk' N)
    let ψ : VermaModule P μ →ₗ⁅K,𝔤⁆ X ⧸ N := R.incl.comp e.toLieModuleHom
    have hR : R ≤ ψ.range := fun x hx ↦
      (LieModuleHom.mem_range ψ x).mpr ⟨e.symm ⟨x, hx⟩, by simp [ψ]⟩
    have hg' : StrictMonoOn (fun Q ↦ g ((Q.map (LieSubmodule.Quotient.mk' N)).comap ψ))
        (Set.Icc N N') := fun Q₁ h₁ Q₂ h₂ hlt ↦
      LieSubmodule.strictMonoOn_comap hg ψ hR (LieSubmodule.map_mono h₁.2)
        (LieSubmodule.map_mono h₂.2) (LieSubmodule.strictMonoOn_map_mk' N h₁.1 h₂.1 hlt)
    exact ⟨_, hf.inf_add_sup hle hg'⟩

end Verma

/-! ### Finite length -/

section FiniteLength

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)
  {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]

include hA

local notation "𝔤" => KacMoodyAlgebra P

/-- **Modules in `𝒪` have finite length** (Humphreys, GSM 94, Theorem 1.11). In finite type over an
algebraically closed field of characteristic zero, the lattice of submodules of a finitely
generated module in `𝒪` admits a strictly monotone `ℕ`-valued function. Humphreys works over `ℂ`;
the reduction to Verma modules is reconstructed (see the module docstring). -/
theorem IsCategoryO.exists_strictMono_lieSubmodule (hM : IsCategoryO P M) {S : Finset M}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) :
    ∃ f : LieSubmodule K 𝔤 M → ℕ, StrictMono f := by
  classical
  obtain ⟨κ, _, _, τ, π, hπ⟩ := hM.isCovered P hA hS
  have hj : ∀ j, ∃ f : LieSubmodule K 𝔤 (projectiveCoverAmbient' P hA (τ j)) → ℕ,
      StrictMono f := by
    intro j
    set n := projectiveCoverShift P hA (τ j)
    have := IrreducibleModule.finiteDimensional (P := P) hA (isDominantIntegral_nsmul_rho P n)
    obtain ⟨s, hs, -⟩ := exists_isStdFiltered_tensorVerma P
      (isCategoryO_dual_irreducible_nsmul_rho P hA n).iSup_weightSpaceOfMap_eq_top
      (τ j + (n : K) • P.rho)
    obtain ⟨f, hf⟩ := hs.exists_strictMonoOn P hA
    exact ⟨f, fun a b hab ↦ hf (Set.mem_Iic.mpr le_top) (Set.mem_Iic.mpr le_top) hab⟩
  choose f hf using hj
  let R : κ → LieSubmodule K 𝔤 M := fun j ↦
    (π.comp (DirectSum.lieModuleOf K κ 𝔤 (fun j ↦ projectiveCoverAmbient' P hA (τ j)) j)).range
  have hR : ∀ s : Finset κ, ∃ F : LieSubmodule K 𝔤 M → ℕ, StrictMonoOn F (Set.Iic (s.sup R)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ ↦ 0, fun _ _ _ hy hxy ↦ absurd (hxy.trans_le hy) not_lt_bot⟩
    | insert j s _ ih =>
      obtain ⟨F, hF⟩ := ih
      rw [Finset.sup_insert]
      exact (LieSubmodule.strictMonoOn_comap (hf j) _ le_rfl).exists_Iic_sup hF
  have htop : Finset.univ.sup R = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ := hπ x
    induction y using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of j q =>
      exact (Finset.le_sup (f := R) (Finset.mem_univ j))
        ((LieModuleHom.mem_range _ _).mpr ⟨q, rfl⟩)
    | add y z hy hz => rw [map_add]; exact add_mem hy hz
  obtain ⟨F, hF⟩ := hR Finset.univ
  rw [htop] at hF
  exact ⟨F, fun a b hab ↦ hF (Set.mem_Iic.mpr le_top) (Set.mem_Iic.mpr le_top) hab⟩

/-- **Modules in `𝒪` are artinian** (Humphreys, GSM 94, Theorem 1.11). -/
theorem IsCategoryO.wellFoundedLT_lieSubmodule (hM : IsCategoryO P M) {S : Finset M}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) : WellFoundedLT (LieSubmodule K 𝔤 M) := by
  obtain ⟨f, hf⟩ := hM.exists_strictMono_lieSubmodule P hA hS
  exact hf.wellFoundedLT

/-- **Modules in `𝒪` are noetherian** (Humphreys, GSM 94, Theorem 1.11). -/
theorem IsCategoryO.wellFoundedGT_lieSubmodule (hM : IsCategoryO P M) {S : Finset M}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) : WellFoundedGT (LieSubmodule K 𝔤 M) := by
  obtain ⟨f, hf⟩ := hM.exists_strictMono_lieSubmodule P hA hS
  refine StrictAnti.wellFoundedGT (f := fun N ↦ f ⊤ - f N) fun a b hab ↦ ?_
  have h1 := hf hab
  have h2 := hf.monotone (le_top : b ≤ ⊤)
  change f ⊤ - f b < f ⊤ - f a
  omega

end FiniteLength

/-! ### Finite-dimensional `Hom` spaces -/

section Hom

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {M N : Type*} [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M] [AddCommGroup N] [Module K N]
  [LieRingModule P.KacMoodyAlgebra N] [LieModule K P.KacMoodyAlgebra N]

local notation "𝔤" => KacMoodyAlgebra P

/-- **`Hom` spaces in `𝒪` are finite-dimensional** (Humphreys, GSM 94, Theorem 1.11): if `M` is a
finitely generated module in `𝒪` and `N` satisfies `IsCategoryO`, then `Hom(M, N)` is
finite-dimensional. Reconstructed: a morphism is determined by its restrictions to finitely many
generating weight spaces `M_μ → N_μ`. -/
theorem IsCategoryO.finiteDimensional_hom (hM : IsCategoryO P M) {S : Finset M}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) (hN : IsCategoryO P N) :
    FiniteDimensional K (M →ₗ⁅K,𝔤⁆ N) := by
  obtain ⟨F, hspan⟩ := hM.exists_finset_lieSpan_weightSpace_eq_top P hS
  have := hM.finiteDimensional_weightSpaceOfMap
  have := hN.finiteDimensional_weightSpaceOfMap
  let Φ : (M →ₗ⁅K,𝔤⁆ N) →ₗ[K] ((μ : F) → weightSpace P M μ →ₗ[K] weightSpace P N μ) :=
    { toFun := fun φ μ ↦ ((φ : M →ₗ[K] N).comp (weightSpace P M μ).subtype).codRestrict
        (weightSpace P N μ) fun x ↦ map_mem_weightSpaceOfMap P φ x.2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).mpr fun φ hφ ↦ ?_)
  have hker : LieSubmodule.lieSpan K 𝔤 (⋃ μ ∈ F, (weightSpace P M μ : Set M)) ≤ φ.ker := by
    rw [LieSubmodule.lieSpan_le]
    intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨μ, hμ, hx⟩ := hx
    have := congrArg Subtype.val (LinearMap.congr_fun (congrFun hφ ⟨μ, hμ⟩) ⟨x, hx⟩)
    exact LieModuleHom.mem_ker.mpr this
  rw [hspan] at hker
  ext m
  exact LieModuleHom.mem_ker.mp (hker (LieSubmodule.mem_top m))

end Hom

end Matrix.Realization.KacMoodyAlgebra
