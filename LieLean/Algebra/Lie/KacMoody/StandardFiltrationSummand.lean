/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.StandardFiltration
import LieLean.Algebra.Lie.KacMoody.CharacterFormula

/-!
# Direct summands of modules with standard filtrations

Humphreys, GSM 94, Proposition 3.7: if `M ∈ 𝒪` has a standard filtration and `λ` is maximal among
its weights, then `M` has a submodule `≅ M(λ)` with quotient having a standard filtration (a); and
direct summands of `M` have standard filtrations (b).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.map_of_injOn`: standard filtrations are
  transported along morphisms injective on the filtered submodule.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.comap_mk`: an extension of a module with a
  standard filtration by one with a standard filtration has one.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.exists_mem_cone`: the weights of `N` lie in the
  cones `μ - Q₊`, `μ ∈ s`.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.lie_e_eq_zero_of_maximal`: vectors of a weight
  maximal in `s` are primitive.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.verma_of_maximal`: Proposition 3.7 (a).
* `Matrix.Realization.KacMoodyAlgebra.exists_isStdFiltered_range`: Proposition 3.7 (b), for the
  range of an idempotent endomorphism, with the multiplicities splitting
  (`exists_isStdFiltered_range_add`).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.7.
-/

noncomputable section

open Module LieModule

universe u

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X Y : Type*}
  [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup Y] [Module K Y] [LieRingModule P.KacMoodyAlgebra Y]
  [LieModule K P.KacMoodyAlgebra Y]

local notation "𝔤" => KacMoodyAlgebra P

section Helpers

variable {P}

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
/-- A morphism injective on a Lie submodule `S` restricts to `S ≃ S.map φ`. -/
def equivMapOfInjOn (φ : X →ₗ⁅K,𝔤⁆ Y) (S : LieSubmodule K 𝔤 X)
    (hφ : ∀ x ∈ S, φ x = 0 → x = 0) : S ≃ₗ⁅K,𝔤⁆ S.map φ :=
  LieModuleEquiv.ofBijective
    (LieModuleHom.codRestrict (S.map φ) (φ.comp S.incl)
      fun x ↦ LieSubmodule.mem_map_of_mem x.2)
    ⟨fun a b hab ↦ by
      have h1 : φ (a - b) = 0 := by
        have : φ a = φ b := congrArg Subtype.val hab
        rw [map_sub, this, sub_self]
      exact sub_eq_zero.mp (Subtype.ext (by
        simpa using hφ _ (S.sub_mem a.2 b.2) h1)),
    fun ⟨y, hy⟩ ↦ by
      obtain ⟨x, hx, rfl⟩ := (LieSubmodule.mem_map _).mp hy
      exact ⟨⟨x, hx⟩, rfl⟩⟩

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
/-- Equal Lie submodules are isomorphic. -/
def equivLieSubmoduleOfEq {S T : LieSubmodule K 𝔤 X} (h : S = T) : S ≃ₗ⁅K,𝔤⁆ T := by
  subst h; exact LieModuleEquiv.refl

end Helpers

omit [CharZero K] in
/-- A Lie submodule isomorphic to `M(μ)` has a standard filtration of length one. -/
theorem isStdFiltered_of_equiv {N : LieSubmodule K 𝔤 X} {μ : Dual K H}
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N) : IsStdFiltered P N {μ} := by
  have hinj : Function.Injective (LieSubmodule.Quotient.mk' (⊥ : LieSubmodule K 𝔤 X)) :=
    (LieModuleHom.ker_eq_bot _).mp (LieSubmodule.Quotient.mk'_ker ⊥)
  exact IsStdFiltered.step IsStdFiltered.bot bot_le
    ⟨e.trans (LieSubmodule.equivMapOfInjective N hinj)⟩

omit [CharZero K] in
/-- The image of an injective morphism `M(μ) → X` has a standard filtration of length one. -/
theorem isStdFiltered_range_of_injective {μ : Dual K H} (φ : VermaModule P μ →ₗ⁅K,𝔤⁆ X)
    (hφ : Function.Injective φ) : IsStdFiltered P φ.range {μ} :=
  isStdFiltered_of_equiv P (LieModuleEquiv.ofBijective
    (LieModuleHom.codRestrict φ.range φ fun m ↦ (LieModuleHom.mem_range φ _).mpr ⟨m, rfl⟩)
    ⟨fun a b hab ↦ hφ (congrArg Subtype.val hab), fun ⟨y, hy⟩ ↦ by
      obtain ⟨m, rfl⟩ := (LieModuleHom.mem_range φ y).mp hy
      exact ⟨m, rfl⟩⟩)

omit [CharZero K] in
lemma IsStdFiltered.eq_bot_of_zero {N : LieSubmodule K 𝔤 X} (hN : IsStdFiltered P N 0) :
    N = ⊥ := by
  generalize hs : (0 : Multiset (Dual K H)) = s at hN
  cases hN with
  | bot => rfl
  | step _ _ _ => exact absurd hs.symm (Multiset.cons_ne_zero)

omit [CharZero K] in
/-- **Transport along morphisms injective on the filtered submodule.** -/
theorem IsStdFiltered.map_of_injOn (g : X →ₗ⁅K,𝔤⁆ Y) {B : LieSubmodule K 𝔤 X}
    (hg : ∀ x ∈ B, g x = 0 → x = 0) {N : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)}
    (hN : IsStdFiltered P N s) (hNB : N ≤ B) : IsStdFiltered P (N.map g) s := by
  induction hN with
  | bot => simpa using IsStdFiltered.bot (P := P) (X := Y)
  | @step N₀ N₁ s₀ μ hN₀ h01 he ih =>
    obtain ⟨e⟩ := he
    refine IsStdFiltered.step (ih (h01.trans hNB)) (LieSubmodule.map_mono h01) ⟨e.trans ?_⟩
    have hker : N₀ ≤ ((LieSubmodule.Quotient.mk' (N₀.map g)).comp g).ker := fun x hx ↦ by
      rw [LieModuleHom.mem_ker, LieModuleHom.comp_apply, LieSubmodule.Quotient.mk_eq_zero]
      exact LieSubmodule.mem_map_of_mem hx
    set ψ := LieSubmodule.Quotient.lift N₀ ((LieSubmodule.Quotient.mk' (N₀.map g)).comp g) hker
    have hψmk (x : X) : ψ (LieSubmodule.Quotient.mk' N₀ x) =
        LieSubmodule.Quotient.mk' (N₀.map g) (g x) := rfl
    have hmap : (N₁.map (LieSubmodule.Quotient.mk' N₀)).map ψ =
        (N₁.map g).map (LieSubmodule.Quotient.mk' (N₀.map g)) := by
      rw [← LieSubmodule.map_comp, ← LieSubmodule.map_comp]
      rfl
    refine (equivMapOfInjOn ψ _ fun y hy hψy ↦ ?_).trans (equivLieSubmoduleOfEq hmap)
    obtain ⟨x, hx, rfl⟩ := (LieSubmodule.mem_map _).mp hy
    rw [hψmk, LieSubmodule.Quotient.mk_eq_zero] at hψy
    obtain ⟨x₀, hx₀, hgx₀⟩ := (LieSubmodule.mem_map _).mp hψy
    have hsub : x₀ - x = 0 :=
      hg _ (B.sub_mem (hNB (h01 hx₀)) (hNB hx)) (by rw [map_sub, hgx₀, sub_self])
    rw [LieSubmodule.Quotient.mk_eq_zero]
    rwa [sub_eq_zero.mp hsub] at hx₀

omit [CharZero K] in
/-- **Extensions.** If `R ⊆ X` has a standard filtration with weights `s` and `T ⊆ X/R` one
with weights `t`, then the preimage of `T` in `X` has one with weights `t + s`. -/
theorem IsStdFiltered.comap_mk {R : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)}
    (hR : IsStdFiltered P R s) {T : LieSubmodule K 𝔤 (X ⧸ R)} {t : Multiset (Dual K H)}
    (hT : IsStdFiltered P T t) :
    IsStdFiltered P (T.comap (LieSubmodule.Quotient.mk' R)) (t + s) := by
  induction hT with
  | bot =>
    have : (⊥ : LieSubmodule K 𝔤 (X ⧸ R)).comap (LieSubmodule.Quotient.mk' R) = R := by
      ext x
      simp
    simpa [this] using hR
  | @step T₀ T₁ t₀ μ hT₀ h01 he ih =>
    obtain ⟨e⟩ := he
    rw [Multiset.cons_add]
    refine IsStdFiltered.step ih (fun x hx ↦ h01 hx) ⟨e.trans ?_⟩
    set C₀ := T₀.comap (LieSubmodule.Quotient.mk' R)
    have hker : C₀ ≤ ((LieSubmodule.Quotient.mk' T₀).comp (LieSubmodule.Quotient.mk' R)).ker :=
      fun x hx ↦ by
        rw [LieModuleHom.mem_ker, LieModuleHom.comp_apply, LieSubmodule.Quotient.mk_eq_zero]
        exact hx
    set χ := LieSubmodule.Quotient.lift C₀
      ((LieSubmodule.Quotient.mk' T₀).comp (LieSubmodule.Quotient.mk' R)) hker
    have hχ : Function.Injective χ := by
      rw [← LieModuleHom.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' C₀ y
      rw [LieModuleHom.mem_ker] at hy
      change LieSubmodule.Quotient.mk' T₀ (LieSubmodule.Quotient.mk' R x) = 0 at hy
      rw [LieSubmodule.Quotient.mk_eq_zero] at hy
      rw [LieSubmodule.mem_bot, LieSubmodule.Quotient.mk_eq_zero]
      exact hy
    have hmap : ((T₁.comap (LieSubmodule.Quotient.mk' R)).map
        (LieSubmodule.Quotient.mk' C₀)).map χ = T₁.map (LieSubmodule.Quotient.mk' T₀) := by
      rw [← LieSubmodule.map_comp]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨LieSubmodule.Quotient.mk' R x, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' R z
        exact ⟨x, hz, rfl⟩
    exact ((LieSubmodule.equivMapOfInjective _ hχ).trans (equivLieSubmoduleOfEq hmap)).symm

omit [CharZero K] in
/-- The weights of a submodule with a standard filtration with weights `s` lie in the cones
`μ - Q₊`, `μ ∈ s`. -/
theorem IsStdFiltered.exists_mem_cone {N : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)}
    (hN : IsStdFiltered P N s) {κ : Dual K H} {x : X} (hxN : x ∈ N)
    (hxw : x ∈ weightSpaceOfMap X (h P) κ) (hx0 : x ≠ 0) : ∃ μ ∈ s, κ ∈ cone P μ := by
  induction hN with
  | bot => exact absurd ((LieSubmodule.mem_bot x).mp hxN) hx0
  | @step N₀ N₁ s₀ μ hN₀ h01 he ih =>
    by_cases hx₀ : x ∈ N₀
    · obtain ⟨ν, hν, hκ⟩ := ih hx₀
      exact ⟨ν, Multiset.mem_cons_of_mem hν, hκ⟩
    · obtain ⟨e⟩ := he
      refine ⟨μ, Multiset.mem_cons_self _ _, ?_⟩
      set ι' : VermaModule P μ →ₗ⁅K,𝔤⁆ X ⧸ N₀ :=
        (N₁.map (LieSubmodule.Quotient.mk' N₀)).incl.comp e.toLieModuleHom
      have hι' : Function.Injective ι' := fun a b hab ↦ e.injective (Subtype.ext hab)
      have hmem : LieSubmodule.Quotient.mk' N₀ x ∈ N₁.map (LieSubmodule.Quotient.mk' N₀) :=
        LieSubmodule.mem_map_of_mem hxN
      set m := e.symm ⟨_, hmem⟩
      have hιm : ι' m = LieSubmodule.Quotient.mk' N₀ x := by simp [ι', m]
      have hm0 : m ≠ 0 := by
        intro h0
        apply hx₀
        rw [← LieSubmodule.Quotient.mk_eq_zero, ← hιm, h0, map_zero]
      have hmw : m ∈ weightSpaceOfMap (VermaModule P μ) (h P) κ :=
        mem_weightSpaceOfMap_of_injective P ι' hι' (by
          rw [hιm]; exact map_mem_weightSpaceOfMap P (LieSubmodule.Quotient.mk' N₀) hxw)
      by_contra hκ
      have hbot := weightSpace_eq_bot P μ (μ := κ) fun k hk h ↦ hκ ⟨k, hk, h⟩
      exact hm0 ((Submodule.mem_bot K).mp (hbot ▸ hmw))

/-- A weight vector of a weight maximal among the weights `s` of a standard filtration is
primitive. -/
theorem IsStdFiltered.lie_e_eq_zero_of_maximal {N : LieSubmodule K 𝔤 X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) {Λ : Dual K H}
    (hmax : ∀ μ ∈ s, Λ ∈ cone P μ → Λ = μ) {v : X} (hvN : v ∈ N)
    (hvw : v ∈ weightSpaceOfMap X (h P) Λ) (i : ι) : ⁅e P i, v⁆ = 0 := by
  by_contra hne
  obtain ⟨μ, hμ, hcone⟩ := hN.exists_mem_cone P (N.lie_mem hvN) (toEnd_e_mem_weightSpace i hvw)
    hne
  have h1 : Λ ∈ cone P (Λ + P.root i) := ⟨Pi.single i 1, Pi.single_nonneg.mpr zero_le_one,
    by rw [rootOf_single]; abel⟩
  have hΛμ := hmax μ hμ (mem_cone_trans h1 hcone)
  subst hΛμ
  obtain ⟨k, hk, hkΛ⟩ := hcone
  have h2 : P.rootOf (k + Pi.single i 1) = P.rootOf 0 := by
    rw [map_add, rootOf_single, map_zero]
    rw [eq_sub_iff_add_eq, add_assoc, add_eq_left] at hkΛ
    rw [add_comm]; exact hkΛ
  have h3 := congrFun (P.rootOf_injective h2) i
  have h4 : (0 : ℤ) ≤ k i := hk i
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at h3
  omega

/-- **Humphreys, GSM 94, Proposition 3.7 (a).** Let `N` have a standard filtration with weights
`s`, and let `v ∈ N` be a nonzero primitive vector of a weight `λ` maximal in `s`. Then `λ ∈ s`,
the morphism `φ : M(λ) → X`, `v_λ ↦ v`, is injective with image `R ⊆ N`, and `N / R` has a
standard filtration with weights `s - {λ}`. -/
theorem IsStdFiltered.verma_of_maximal [DecidableEq (Dual K H)] {N : LieSubmodule K 𝔤 X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) {Λ : Dual K H}
    (hmax : ∀ μ ∈ s, Λ ∈ cone P μ → Λ = μ) {v : X} (hv : v ∈ primitiveVectors P X Λ)
    (hv0 : v ≠ 0) (hvN : v ∈ N) :
    Λ ∈ s ∧ Function.Injective ((homEquiv P X Λ).symm ⟨v, hv⟩) ∧
      ((homEquiv P X Λ).symm ⟨v, hv⟩).range ≤ N ∧
      IsStdFiltered P (N.map (LieSubmodule.Quotient.mk' ((homEquiv P X Λ).symm ⟨v, hv⟩).range))
        (s.erase Λ) := by
  set φ := (homEquiv P X Λ).symm ⟨v, hv⟩
  have hφv : φ (hwv P Λ) = v := congrArg Subtype.val ((homEquiv P X Λ).apply_symm_apply ⟨v, hv⟩)
  set R := φ.range
  have hRle {M : LieSubmodule K 𝔤 X} (hvM : v ∈ M) : R ≤ M := by
    change φ.range ≤ M
    rw [VermaModule.range_eq_lieSpan, hφv, LieSubmodule.lieSpan_le, Set.singleton_subset_iff]
    exact hvM
  have hvw : v ∈ weightSpaceOfMap X (h P) Λ := (mem_primitiveVectors.mp hv).1
  induction hN with
  | bot => exact absurd ((LieSubmodule.mem_bot v).mp hvN) hv0
  | @step N₀ N₁ s₀ μ hN₀ h01 he ih =>
    obtain ⟨e⟩ := he
    by_cases hvN₀ : v ∈ N₀
    · obtain ⟨hΛ, hinj, -, hfilt⟩ :=
        ih (fun μ' hμ' ↦ hmax μ' (Multiset.mem_cons_of_mem hμ')) hvN₀
      have hRN₀ := hRle hvN₀
      refine ⟨Multiset.mem_cons_of_mem hΛ, hinj, hRle hvN, ?_⟩
      have hs : (μ ::ₘ s₀).erase Λ = μ ::ₘ s₀.erase Λ := by
        by_cases hμΛ : μ = Λ
        · subst hμΛ; rw [Multiset.erase_cons_head, Multiset.cons_erase hΛ]
        · exact Multiset.erase_cons_tail s₀ hμΛ
      rw [hs]
      refine IsStdFiltered.step hfilt (LieSubmodule.map_mono h01) ⟨e.trans ?_⟩
      have hker : N₀ ≤ ((LieSubmodule.Quotient.mk' (N₀.map (LieSubmodule.Quotient.mk' R))).comp
          (LieSubmodule.Quotient.mk' R)).ker := fun x hx ↦ by
        rw [LieModuleHom.mem_ker, LieModuleHom.comp_apply, LieSubmodule.Quotient.mk_eq_zero]
        exact LieSubmodule.mem_map_of_mem hx
      set ψ := LieSubmodule.Quotient.lift N₀ ((LieSubmodule.Quotient.mk'
        (N₀.map (LieSubmodule.Quotient.mk' R))).comp (LieSubmodule.Quotient.mk' R)) hker
      have hψ : Function.Injective ψ := by
        rw [← LieModuleHom.ker_eq_bot, eq_bot_iff]
        intro y hy
        obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N₀ y
        rw [LieModuleHom.mem_ker] at hy
        change LieSubmodule.Quotient.mk' (N₀.map (LieSubmodule.Quotient.mk' R))
          (LieSubmodule.Quotient.mk' R x) = 0 at hy
        rw [LieSubmodule.Quotient.mk_eq_zero] at hy
        obtain ⟨x₀, hx₀, hxx₀⟩ := (LieSubmodule.mem_map _).mp hy
        have hd : x₀ - x ∈ R := by
          rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub, hxx₀, sub_self]
        rw [LieSubmodule.mem_bot, LieSubmodule.Quotient.mk_eq_zero]
        simpa using N₀.sub_mem hx₀ (hRN₀ hd)
      have hmap : (N₁.map (LieSubmodule.Quotient.mk' N₀)).map ψ =
          (N₁.map (LieSubmodule.Quotient.mk' R)).map
            (LieSubmodule.Quotient.mk' (N₀.map (LieSubmodule.Quotient.mk' R))) := by
        rw [← LieSubmodule.map_comp, ← LieSubmodule.map_comp]
        rfl
      exact (LieSubmodule.equivMapOfInjective _ hψ).trans (equivLieSubmoduleOfEq hmap)
    · set ι' : VermaModule P μ →ₗ⁅K,𝔤⁆ X ⧸ N₀ :=
        (N₁.map (LieSubmodule.Quotient.mk' N₀)).incl.comp e.toLieModuleHom
      have hι' : Function.Injective ι' := fun a b hab ↦ e.injective (Subtype.ext hab)
      have hrange (y : X ⧸ N₀) (hy : y ∈ N₁.map (LieSubmodule.Quotient.mk' N₀)) :
          ∃ m, ι' m = y := ⟨e.symm ⟨y, hy⟩, by simp [ι']⟩
      obtain ⟨m, hm⟩ := hrange _ (LieSubmodule.mem_map_of_mem hvN)
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [map_zero, eq_comm, LieSubmodule.Quotient.mk_eq_zero] at hm
        exact hvN₀ hm
      have hmw : m ∈ weightSpaceOfMap (VermaModule P μ) (h P) Λ :=
        mem_weightSpaceOfMap_of_injective P ι' hι' (by
          rw [hm]; exact map_mem_weightSpaceOfMap P (LieSubmodule.Quotient.mk' N₀) hvw)
      have hΛμ : Λ = μ := by
        refine hmax μ (Multiset.mem_cons_self _ _) ?_
        by_contra hκ
        have hbot := weightSpace_eq_bot P μ (μ := Λ) fun k hk h ↦ hκ ⟨k, hk, h⟩
        exact hm0 ((Submodule.mem_bot K).mp (hbot ▸ hmw))
      subst hΛμ
      have hm' : m ∈ K ∙ hwv P Λ := by rw [← weightSpace_self]; exact hmw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm'
      have hc : c ≠ 0 := by rintro rfl; exact hm0 (zero_smul K _)
      have hcomp : (LieSubmodule.Quotient.mk' N₀).comp φ = c • ι' := by
        refine hom_ext P Λ ?_
        rw [LieModuleHom.comp_apply, hφv]
        change _ = c • ι' (hwv P Λ)
        rw [← map_smul, hm]
      have hφι (a : VermaModule P Λ) : LieSubmodule.Quotient.mk' N₀ (φ a) = c • ι' a :=
        LieModuleHom.congr_fun hcomp a
      have hinj : Function.Injective φ := fun a b hab ↦ by
        have := hφι a
        rw [hab, hφι b] at this
        exact hι' (smul_right_injective _ hc this.symm)
      refine ⟨Multiset.mem_cons_self _ _, hinj, hRle hvN, ?_⟩
      rw [Multiset.erase_cons_head]
      -- `N₁ / R = N₀ / R ≅ N₀`
      have hN₁ : N₁.map (LieSubmodule.Quotient.mk' R) = N₀.map (LieSubmodule.Quotient.mk' R) := by
        refine le_antisymm ?_ (LieSubmodule.map_mono h01)
        rintro _ ⟨n, hn, rfl⟩
        obtain ⟨m', hm'⟩ := hrange _ (LieSubmodule.mem_map_of_mem hn)
        have hmem : n - φ (c⁻¹ • m') ∈ N₀ := by
          rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub, hφι, map_smul, smul_smul,
            mul_inv_cancel₀ hc, one_smul, hm', sub_self]
        refine ⟨n - φ (c⁻¹ • m'), hmem, ?_⟩
        have h0 : LieSubmodule.Quotient.mk' R (φ (c⁻¹ • m')) = 0 :=
          (LieSubmodule.Quotient.mk_eq_zero R).mpr ((LieModuleHom.mem_range φ _).mpr ⟨_, rfl⟩)
        change LieSubmodule.Quotient.mk' R (n - φ (c⁻¹ • m')) = LieSubmodule.Quotient.mk' R n
        rw [map_sub, h0, sub_zero]
      rw [hN₁]
      refine hN₀.map_of_injOn P (LieSubmodule.Quotient.mk' R) (B := N₀) (fun x hx hx0 ↦ ?_) le_rfl
      rw [LieSubmodule.Quotient.mk_eq_zero] at hx0
      obtain ⟨a, rfl⟩ := (LieModuleHom.mem_range φ x).mp hx0
      have h0 : c • ι' a = 0 := by
        rw [← hφι, LieSubmodule.Quotient.mk_eq_zero]; exact hx
      have ha : a = 0 := hι' (by rw [map_zero]; exact (smul_eq_zero.mp h0).resolve_left hc)
      rw [ha, map_zero]

omit [DecidableEq ι] in
/-- A nonempty multiset of weights has an element maximal for the order `μ ≤ ν ↔ μ ∈ ν - Q₊`. -/
theorem exists_maximal_mem {s : Multiset (Dual K H)} (hs : s ≠ 0) :
    ∃ Λ ∈ s, ∀ μ ∈ s, Λ ∈ cone P μ → Λ = μ := by
  classical
  obtain ⟨m, hm, hmin⟩ := (s.toFinset.image (WeightOrd.toWeightOrd P)).exists_minimal
    (by simpa [Finset.image_nonempty, Multiset.toFinset_nonempty] using hs)
  obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.mp hm
  refine ⟨Λ, Multiset.mem_toFinset.mp hΛ, fun μ hμ hΛμ ↦ ?_⟩
  have h1 : WeightOrd.toWeightOrd P μ ≤ WeightOrd.toWeightOrd P Λ :=
    (WeightOrd.toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr hΛμ
  have h2 := hmin (Finset.mem_image_of_mem _ (Multiset.mem_toFinset.mpr hμ)) h1
  exact eq_of_mem_cone_of_mem_cone hΛμ
    ((WeightOrd.toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mp h2)

/-- A module in `𝒪` with a standard filtration in which `λ` occurs has a nonzero vector of
weight `λ`. -/
theorem IsStdFiltered.exists_ne_zero (hX : IsCategoryO P X)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 X) s) {Λ : Dual K H}
    (hΛ : Λ ∈ s) : ∃ v ∈ weightSpaceOfMap X (h P) Λ, v ≠ 0 := by
  classical
  have h1 := hs.count_eq_coinvDim P hX Λ
  have h2 : 0 < s.count Λ := Multiset.count_pos.mpr hΛ
  rw [h1, coinvDim] at h2
  by_contra hcon
  push Not at hcon
  have hbot : (⊤ : LieSubmodule K 𝔤 X).toSubmodule ⊓ weightSpaceOfMap X (h P) Λ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨-, hv⟩
    exact (Submodule.mem_bot K).mpr (hcon v hv)
  rw [(LinearEquiv.ofEq _ _ hbot).finrank_eq, finrank_bot] at h2
  omega

/-- **Humphreys, GSM 94, Proposition 3.7 (b)**, for the range of an idempotent endomorphism:
if `X ∈ 𝒪` has a standard filtration, so does every direct summand `p(X)`, `p² = p`. Induction
on the length, splitting off `M(λ)` for `λ` maximal (Proposition 3.7 (a)) inside `p(X)` or
inside `ker p`. -/
theorem exists_isStdFiltered_range (n : ℕ) :
    ∀ {X : Type u} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
      [LieModule K P.KacMoodyAlgebra X], IsCategoryO P X → ∀ s : Multiset (Dual K H),
      Multiset.card s = n → IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra X) s →
      ∀ p : X →ₗ⁅K,P.KacMoodyAlgebra⁆ X, p.comp p = p → ∃ t, IsStdFiltered P p.range t := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ _ hX s hsn hs p hp
  have hpp (x : X) : p (p x) = p x := LieModuleHom.congr_fun hp x
  by_cases hs0 : s = 0
  · subst hs0
    have htop := hs.eq_bot_of_zero
    refine ⟨0, ?_⟩
    have : p.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ (⊤ : LieSubmodule K P.KacMoodyAlgebra X) := trivial
      rw [htop, LieSubmodule.mem_bot] at hx
      simp [hx]
    rw [this]
    exact IsStdFiltered.bot
  obtain ⟨Λ, hΛs, hmax⟩ := exists_maximal_mem P hs0
  obtain ⟨v, hvw, hv0⟩ := hs.exists_ne_zero P hX hΛs
  have hcard : Multiset.card (s.erase Λ) < n := by
    have : 0 < Multiset.card s := Multiset.card_pos.mpr hs0
    rw [Multiset.card_erase_of_mem hΛs, Nat.pred_eq_sub_one]
    omega
  have hprim (w : X) (hw : w ∈ weightSpaceOfMap X (h P) Λ) : w ∈ primitiveVectors P X Λ :=
    mem_primitiveVectors.mpr ⟨hw, fun i ↦ hs.lie_e_eq_zero_of_maximal P hmax trivial hw i⟩
  -- the quotient by a copy of `M(λ)` and the induced idempotent
  have key (w : X) (hw : w ∈ weightSpaceOfMap X (h P) Λ) (hw0 : w ≠ 0)
      (hpR : ∀ x ∈ ((homEquiv P X Λ).symm ⟨w, hprim w hw⟩).range,
        LieSubmodule.Quotient.mk' ((homEquiv P X Λ).symm ⟨w, hprim w hw⟩).range (p x) = 0) :
      ∃ t, IsStdFiltered P (p.range.map (LieSubmodule.Quotient.mk'
        ((homEquiv P X Λ).symm ⟨w, hprim w hw⟩).range)) t := by
    set φ := (homEquiv P X Λ).symm ⟨w, hprim w hw⟩
    set R := φ.range
    obtain ⟨-, -, -, hfilt⟩ := hs.verma_of_maximal P hmax (hprim w hw) hw0 trivial
    have hfilt' : IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra (X ⧸ R)) (s.erase Λ) := by
      have : (⊤ : LieSubmodule K P.KacMoodyAlgebra X).map (LieSubmodule.Quotient.mk' R) = ⊤ := by
        rw [LieModuleHom.map_top, LieModuleHom.range_eq_top]
        exact LieSubmodule.Quotient.surjective_mk' R
      rwa [this] at hfilt
    set q := LieSubmodule.Quotient.lift R ((LieSubmodule.Quotient.mk' R).comp p) fun x hx ↦ by
      rw [LieModuleHom.mem_ker, LieModuleHom.comp_apply]; exact hpR x hx
    have hq (x : X) : q (LieSubmodule.Quotient.mk' R x) = LieSubmodule.Quotient.mk' R (p x) := rfl
    have hqq : q.comp q = q := by
      ext y
      obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' R y
      rw [LieModuleHom.comp_apply, hq, hq, hpp]
    obtain ⟨t, ht⟩ := ih _ hcard (hX.quotient R) (s.erase Λ) rfl hfilt' q hqq
    have hrange : q.range = p.range.map (LieSubmodule.Quotient.mk' R) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' R z
        exact ⟨p x, ⟨x, rfl⟩, (hq x).symm⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨LieSubmodule.Quotient.mk' R x, hq x⟩
    exact ⟨t, hrange ▸ ht⟩
  by_cases hpv : p v = 0
  · -- `v ∈ ker p`: transport back along `X/R → X` induced by `p`
    set φ := (homEquiv P X Λ).symm ⟨v, hprim v hvw⟩
    have hφv : φ (hwv P Λ) = v :=
      congrArg Subtype.val ((homEquiv P X Λ).apply_symm_apply ⟨v, hprim v hvw⟩)
    have hRker : φ.range ≤ p.ker := by
      rw [VermaModule.range_eq_lieSpan, hφv, LieSubmodule.lieSpan_le, Set.singleton_subset_iff]
      exact hpv
    obtain ⟨t, ht⟩ := key v hvw hv0 fun x hx ↦ by
      rw [LieModuleHom.mem_ker.mp (hRker hx), map_zero]
    set g := LieSubmodule.Quotient.lift φ.range p hRker
    have hg (x : X) : g (LieSubmodule.Quotient.mk' φ.range x) = p x := rfl
    have hmap : (p.range.map (LieSubmodule.Quotient.mk' φ.range)).map g = p.range := by
      rw [← LieSubmodule.map_comp]
      ext y
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨p x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨p x, ⟨x, rfl⟩, hpp x⟩
    refine ⟨t, hmap ▸ ht.map_of_injOn P g (B := p.range.map (LieSubmodule.Quotient.mk' φ.range))
      (fun y hy hgy ↦ ?_) le_rfl⟩
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hy
    change p (p x) = 0 at hgy
    rw [hpp] at hgy
    change LieSubmodule.Quotient.mk' φ.range (p x) = 0
    rw [hgy, map_zero]
  · -- `p v ∈ p(X)`: an extension of `p(X)/R` by `R ≅ M(λ)`
    have hpvw : p v ∈ weightSpaceOfMap X (h P) Λ := map_mem_weightSpaceOfMap P p hvw
    set φ := (homEquiv P X Λ).symm ⟨p v, hprim (p v) hpvw⟩
    have hφv : φ (hwv P Λ) = p v :=
      congrArg Subtype.val ((homEquiv P X Λ).apply_symm_apply ⟨p v, hprim (p v) hpvw⟩)
    have hRp : φ.range ≤ p.range := by
      rw [VermaModule.range_eq_lieSpan, hφv, LieSubmodule.lieSpan_le, Set.singleton_subset_iff]
      exact ⟨v, rfl⟩
    have hpR : ∀ x ∈ φ.range, p x = x := fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hRp hx
      exact hpp y
    obtain ⟨t, ht⟩ := key (p v) hpvw hpv fun x hx ↦ by
      rw [hpR x hx, LieSubmodule.Quotient.mk_eq_zero]; exact hx
    obtain ⟨hΛ, hinj, -, -⟩ := hs.verma_of_maximal P hmax (hprim (p v) hpvw) hpv trivial
    have hext := (isStdFiltered_range_of_injective P φ hinj).comap_mk P ht
    have hcomap : (p.range.map (LieSubmodule.Quotient.mk' φ.range)).comap
        (LieSubmodule.Quotient.mk' φ.range) = p.range := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyx' : LieSubmodule.Quotient.mk' φ.range y = LieSubmodule.Quotient.mk' φ.range x :=
          hyx
        have hd : y - x ∈ φ.range := by
          rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub, hyx', sub_self]
        simpa using p.range.sub_mem hy (hRp hd)
      · intro hx
        exact ⟨x, hx, rfl⟩
    exact ⟨_, hcomap ▸ hext⟩

/-- **Humphreys, GSM 94, Proposition 3.7 (b)**, with multiplicities: for an idempotent
endomorphism `p` of a module `X ∈ 𝒪` with a standard filtration with weights `s`, both `p(X)`
and `ker p` have standard filtrations, with weights `t`, `t'` and `s = t + t'`. -/
theorem exists_isStdFiltered_range_add {X : Type u} [AddCommGroup X]
    [Module K X] [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X]
    (hX : IsCategoryO P X) {s : Multiset (Dual K H)}
    (hs : IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra X) s)
    (p : X →ₗ⁅K,P.KacMoodyAlgebra⁆ X) (hp : p.comp p = p) :
    ∃ t t', IsStdFiltered P p.range t ∧ IsStdFiltered P p.ker t' ∧ s = t + t' := by
  classical
  have hpp (x : X) : p (p x) = p x := LieModuleHom.congr_fun hp x
  set q : X →ₗ⁅K,P.KacMoodyAlgebra⁆ X := LieModuleHom.id - p
  have hq (x : X) : q x = x - p x := rfl
  have hqq : q.comp q = q := by
    ext x
    rw [LieModuleHom.comp_apply, hq, hq, map_sub, hpp, sub_self, sub_zero]
  have hqker : q.range = p.ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [LieModuleHom.mem_ker, hq, map_sub, hpp, sub_self]
    · intro hx
      exact ⟨x, by rw [hq, LieModuleHom.mem_ker.mp hx, sub_zero]⟩
  obtain ⟨t, ht⟩ := exists_isStdFiltered_range P _ hX s rfl hs p hp
  obtain ⟨t', ht'⟩ := exists_isStdFiltered_range P _ hX s rfl hs q hqq
  rw [hqker] at ht'
  refine ⟨t, t', ht, ht', ?_⟩
  have hinj : ∀ x ∈ p.ker, LieSubmodule.Quotient.mk' p.range x = 0 → x = 0 := by
    intro x hx hx0
    rw [LieSubmodule.Quotient.mk_eq_zero] at hx0
    obtain ⟨y, rfl⟩ := hx0
    have := LieModuleHom.mem_ker.mp hx
    rwa [hpp] at this
  have hT := ht'.map_of_injOn P (LieSubmodule.Quotient.mk' p.range) hinj le_rfl
  have hext := ht.comap_mk P hT
  have htop : (p.ker.map (LieSubmodule.Quotient.mk' p.range)).comap
      (LieSubmodule.Quotient.mk' p.range) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨x - p x, ?_, ?_⟩
    · change p (x - p x) = 0
      rw [map_sub, hpp, sub_self]
    · change LieSubmodule.Quotient.mk' p.range (x - p x) = LieSubmodule.Quotient.mk' p.range x
      have : LieSubmodule.Quotient.mk' p.range (p x) = 0 :=
        (LieSubmodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
      rw [map_sub, this, sub_zero]
  rw [htop] at hext
  ext μ
  rw [hs.count_eq_coinvDim P hX, ← hext.count_eq_coinvDim P hX, add_comm]

end Matrix.Realization.KacMoodyAlgebra
