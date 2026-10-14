/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ProjectiveDecomposition
import LieLean.Algebra.Lie.KacMoody.ProjectiveStdFiltration
import LieLean.Algebra.Lie.KacMoody.BGGReciprocity
import LieLean.Algebra.Lie.KacMoody.TranslationFacetClosure

/-!
# Projective modules in `𝒪` are determined by their characters

Humphreys, GSM 94, Corollary 3.10: two projective modules in `𝒪` with the same formal character
are isomorphic.

## Main definitions

* `LieModuleHom.retractCompl`: for a retraction `r ∘ s = 1`, the projection `v ↦ v - s (r v)` onto
  `ker r`.
* `LieModuleHom.homRetractEquiv`: `Hom(V, Y) ≃ Hom(X, Y) × Hom(ker r, Y)` for `r ∘ s = 1_X`.
* `LieModuleHom.equivOfRetract`: modules with a common retract and isomorphic complements are
  isomorphic.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveO.nonempty_equiv_of_finrank_hom_eq`: finitely
  generated projectives `V, V'` in `𝒪` with `dim Hom(V, L(λ)) = dim Hom(V', L(λ))` for all `λ` are
  isomorphic.
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveO.nonempty_equiv_of_character_eq`:
  **Corollary 3.10**.

## Proof notes

Humphreys decomposes `V ≅ ⊕_λ P(λ)^{d_λ}` (Theorem 3.9 (b)) and shows by induction on the length
that the character determines the `d_λ`, via the standard filtrations of Theorem 3.10. Here the
decomposition is replaced by splitting off one `P(λ)` at a time (`V = P(λ) ⊕ C` whenever
`V ↠ L(λ)`, Theorem 3.9 (a)), by induction on a strictly monotone measure on submodules
(Theorem 1.11). The Verma multiplicities of `V` are `Σ_λ d_λ (P(λ) : M(μ))`, and the matrix
`(P(λ) : M(μ))` is unitriangular (Theorem 3.10), so the character, which determines the Verma
multiplicities, determines the `d_λ = dim Hom(V, L(λ))`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.10.
-/

noncomputable section

open Module LieModule

universe u₁ u₂

/-! ### Unitriangular systems -/

namespace Multiset

/-- **Unitriangularity.** Let `o : α → β` be injective into a partial order and `w : α → α → ℕ`
with `w a a = 1` and `w a b ≠ 0 → o b ≤ o a`. Then a multiset `s` is determined by the sums
`Σ_{a ∈ s} w a b`, `b ∈ α`. -/
theorem eq_of_forall_sum_map_eq {α β : Type*} [PartialOrder β] {o : α → β}
    (ho : Function.Injective o) {w : α → α → ℕ} (hw₁ : ∀ a, w a a = 1)
    (hw : ∀ a b, w a b ≠ 0 → o b ≤ o a) (s s' : Multiset α)
    (h : ∀ b, (s.map (w · b)).sum = (s'.map (w · b)).sum) : s = s' := by
  classical
  induction s using Multiset.strongInductionOn generalizing s' with
  | ih s ih =>
  by_cases h0 : s + s' = 0
  · rw [add_eq_zero] at h0
    rw [h0.1, h0.2]
  obtain ⟨a, ha⟩ := (s + s').toFinset.exists_maximalFor o
    (Multiset.toFinset_nonempty.mpr h0)
  have ha' : a ∈ s + s' := Multiset.mem_toFinset.mp ha.1
  have hmax : ∀ x ∈ s + s', o a ≤ o x → x = a := fun x hx hle ↦
    ho (le_antisymm (ha.2 (Multiset.mem_toFinset.mpr hx) hle) hle)
  have hsum : ∀ t, t ≤ s + s' → (t.map (w · a)).sum = t.count a := by
    intro t ht
    rw [Multiset.sum_map_eq_nsmul_single a fun x hxa hx ↦ ?_, hw₁, smul_eq_mul, mul_one]
    by_contra hne
    exact hxa (hmax x (Multiset.mem_of_le ht hx) (hw x a hne))
  have hc : s.count a = s'.count a := by
    rw [← hsum s (Multiset.le_add_right s s'), ← hsum s' (Multiset.le_add_left s' s), h a]
  have has : a ∈ s := by
    rcases Multiset.mem_add.mp ha' with h' | h'
    · exact h'
    · rw [← Multiset.count_pos, hc]
      exact Multiset.count_pos.mpr h'
  have has' : a ∈ s' := by
    rw [← Multiset.count_pos, ← hc]
    exact Multiset.count_pos.mpr has
  rw [← Multiset.cons_erase has, ← Multiset.cons_erase has',
    ih _ (Multiset.erase_lt.mpr has) (s'.erase a) fun b ↦ ?_]
  have hb := h b
  rw [← Multiset.cons_erase has, ← Multiset.cons_erase has', Multiset.map_cons,
    Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons] at hb
  omega

end Multiset

/-! ### Retracts -/

namespace LieModuleHom

variable {R L V V' X Y : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
  [AddCommGroup V'] [Module R V'] [LieRingModule L V'] [LieModule R L V']
  [AddCommGroup X] [Module R X] [LieRingModule L X] [LieModule R L X]
  [AddCommGroup Y] [Module R Y] [LieRingModule L Y] [LieModule R L Y]
  {s : X →ₗ⁅R,L⁆ V} {r : V →ₗ⁅R,L⁆ X}

/-- For a retraction `r ∘ s = 1_X`, the projection `v ↦ v - s (r v)` of `V` onto `ker r`. -/
def retractCompl (hrs : r.comp s = LieModuleHom.id) : V →ₗ⁅R,L⁆ r.ker :=
  (LieModuleHom.id - s.comp r).codRestrict r.ker fun v ↦ by
    rw [LieModuleHom.mem_ker]
    change r (v - s (r v)) = 0
    rw [map_sub, ← LieModuleHom.comp_apply r s, hrs, LieModuleHom.id_apply, sub_self]

omit [LieAlgebra R L] [LieModule R L V] [LieModule R L X] in
lemma coe_retractCompl_apply (hrs : r.comp s = LieModuleHom.id) (v : V) :
    (retractCompl hrs v : V) = v - s (r v) := rfl

omit [LieAlgebra R L] [LieModule R L V] [LieModule R L X] in
lemma retractCompl_apply_coe (hrs : r.comp s = LieModuleHom.id) (c : r.ker) :
    retractCompl hrs (c : V) = c := by
  ext
  rw [coe_retractCompl_apply, LieModuleHom.mem_ker.mp c.2, map_zero, sub_zero]

omit [LieAlgebra R L] [LieModule R L V] [LieModule R L X] in
lemma retractCompl_apply_apply (hrs : r.comp s = LieModuleHom.id) (x : X) :
    retractCompl hrs (s x) = 0 := by
  ext
  rw [coe_retractCompl_apply, ← LieModuleHom.comp_apply r s, hrs, LieModuleHom.id_apply,
    sub_self]
  rfl

omit [LieAlgebra R L] [LieModule R L V] [LieModule R L X] in
lemma apply_add_retractCompl (hrs : r.comp s = LieModuleHom.id) (v : V) :
    s (r v) + (retractCompl hrs v : V) = v := by
  rw [coe_retractCompl_apply, add_sub_cancel]

/-- For a retraction `r ∘ s = 1_X` of `V`, `Hom(V, Y) ≃ Hom(X, Y) × Hom(ker r, Y)`. -/
def homRetractEquiv (hrs : r.comp s = LieModuleHom.id) :
    (V →ₗ⁅R,L⁆ Y) ≃ₗ[R] (X →ₗ⁅R,L⁆ Y) × (r.ker →ₗ⁅R,L⁆ Y) where
  toFun f := (f.comp s, f.comp r.ker.incl)
  invFun g := g.1.comp r + g.2.comp (retractCompl hrs)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    ext v
    change f (s (r v)) + f (retractCompl hrs v : V) = f v
    rw [← map_add, apply_add_retractCompl]
  right_inv g := by
    refine Prod.ext (LieModuleHom.ext fun x ↦ ?_) (LieModuleHom.ext fun c ↦ ?_)
    · change g.1 (r (s x)) + g.2 (retractCompl hrs (s x)) = g.1 x
      rw [← LieModuleHom.comp_apply r s, hrs, LieModuleHom.id_apply, retractCompl_apply_apply,
        map_zero, add_zero]
    · change g.1 (r c) + g.2 (retractCompl hrs (c : V)) = g.2 c
      rw [LieModuleHom.mem_ker.mp c.2, map_zero, zero_add, retractCompl_apply_coe]

/-- Two modules `V, V'` with retractions `r ∘ s = 1_X`, `r' ∘ s' = 1_X` onto the same module `X`
and isomorphic complements `ker r ≅ ker r'` are isomorphic. -/
def equivOfRetract (hrs : r.comp s = LieModuleHom.id) {s' : X →ₗ⁅R,L⁆ V'}
    {r' : V' →ₗ⁅R,L⁆ X} (hrs' : r'.comp s' = LieModuleHom.id) (e : r.ker ≃ₗ⁅R,L⁆ r'.ker) :
    V ≃ₗ⁅R,L⁆ V' :=
  { s'.comp r + r'.ker.incl.comp (e.toLieModuleHom.comp (retractCompl hrs)) with
    invFun := s.comp r' + r.ker.incl.comp (e.symm.toLieModuleHom.comp (retractCompl hrs'))
    left_inv := fun v ↦ by
      change s (r' (s' (r v) + (e (retractCompl hrs v) : V'))) +
        (e.symm (retractCompl hrs' (s' (r v) + (e (retractCompl hrs v) : V'))) : V) = v
      have h1 : r' (s' (r v) + (e (retractCompl hrs v) : V')) = r v := by
        rw [map_add, ← LieModuleHom.comp_apply r' s', hrs', LieModuleHom.id_apply,
          LieModuleHom.mem_ker.mp (e (retractCompl hrs v)).2, add_zero]
      have h2 : retractCompl hrs' (s' (r v) + (e (retractCompl hrs v) : V')) =
          e (retractCompl hrs v) := by
        rw [map_add, retractCompl_apply_apply, zero_add, retractCompl_apply_coe]
      rw [h1, h2, LieModuleEquiv.symm_apply_apply, apply_add_retractCompl]
    right_inv := fun v ↦ by
      change s' (r (s (r' v) + (e.symm (retractCompl hrs' v) : V))) +
        (e (retractCompl hrs (s (r' v) + (e.symm (retractCompl hrs' v) : V))) : V') = v
      have h1 : r (s (r' v) + (e.symm (retractCompl hrs' v) : V)) = r' v := by
        rw [map_add, ← LieModuleHom.comp_apply r s, hrs, LieModuleHom.id_apply,
          LieModuleHom.mem_ker.mp (e.symm (retractCompl hrs' v)).2, add_zero]
      have h2 : retractCompl hrs (s (r' v) + (e.symm (retractCompl hrs' v) : V)) =
          e.symm (retractCompl hrs' v) := by
        rw [map_add, retractCompl_apply_apply, zero_add, retractCompl_apply_coe]
      rw [h1, h2, LieModuleEquiv.apply_symm_apply, apply_add_retractCompl] }

end LieModuleHom

namespace Matrix.Realization.KacMoodyAlgebra

open WeightOrd

/-! ### Weight multiplicities of modules with a standard filtration -/

section StdFiltered

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] in
/-- If `N ⊆ X` has a standard filtration with weights `s`, then
`dim (N ∩ X_ν) = Σ_{μ ∈ s} dim M(μ)_ν`. -/
theorem IsStdFiltered.finrank_inf_weightSpaceOfMap (hX : IsCategoryO P X)
    {N : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s)
    (ν : Dual K H) :
    finrank K ↥(N.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) =
      (s.map fun μ ↦ finrank K (weightSpaceOfMap (VermaModule P μ) (h P) ν)).sum := by
  induction hN with
  | bot => simp
  | @step N N' s μ _ hle he ih =>
    obtain ⟨e⟩ := he
    rw [finrank_inf_weightSpaceOfMap_eq_add hX hle ν, ih, Multiset.map_cons, Multiset.sum_cons,
      ← finrank_weightSpaceOfMap_lieSubmodule P, finrank_weightSpaceOfMap_equiv P e.symm ν,
      add_comm]

end StdFiltered

/-! ### Splitting off `P(λ)` -/

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-- The hypotheses "finitely generated projective module in `𝒪`" on `V`. -/
structure IsFGProjectiveO (V : Type (max u₁ u₂)) [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] : Prop where
  isProjectiveO : IsProjectiveO.{max u₁ u₂} P V
  isCategoryO : IsCategoryO P V
  fg : ∃ S : Finset V, LieSubmodule.lieSpan K 𝔤 (S : Set V) = ⊤

namespace IsFGProjectiveO

variable {P} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
/-- The complement `ker r` of a retract of a finitely generated projective module in `𝒪` is a
finitely generated projective module in `𝒪`. -/
theorem ker {X : Type (max u₁ u₂)} [AddCommGroup X] [Module K X]
    [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X] (hV : IsFGProjectiveO P V)
    {s : X →ₗ⁅K,𝔤⁆ V} {r : V →ₗ⁅K,𝔤⁆ X} (hrs : r.comp s = LieModuleHom.id) :
    IsFGProjectiveO P r.ker := by
  classical
  have hq : (LieModuleHom.retractCompl hrs).comp r.ker.incl = LieModuleHom.id :=
    LieModuleHom.ext fun c ↦ LieModuleHom.retractCompl_apply_coe hrs c
  refine ⟨hV.isProjectiveO.of_retract _ _ hq, hV.isCategoryO.lieSubmodule _, ?_⟩
  obtain ⟨S, hS⟩ := hV.fg
  refine ⟨S.image (LieModuleHom.retractCompl hrs), ?_⟩
  rw [eq_top_iff]
  rintro c -
  have hle : LieSubmodule.lieSpan K 𝔤 (S : Set V) ≤ (LieSubmodule.lieSpan K 𝔤
      ((S.image (LieModuleHom.retractCompl hrs) : Finset r.ker) : Set r.ker)).comap
        (LieModuleHom.retractCompl hrs) := by
    rw [LieSubmodule.lieSpan_le]
    intro x hx
    exact LieSubmodule.subset_lieSpan (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
  have := hle (hS ▸ LieSubmodule.mem_top (c : V))
  rwa [LieSubmodule.mem_comap, LieModuleHom.retractCompl_apply_coe] at this

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
/-- `Hom(V, Y)` is finite-dimensional for `Y ∈ 𝒪`. -/
theorem finiteDimensional_hom (hV : IsFGProjectiveO P V) {Y : Type*} [AddCommGroup Y] [Module K Y]
    [LieRingModule P.KacMoodyAlgebra Y] [LieModule K P.KacMoodyAlgebra Y] (hY : IsCategoryO P Y) :
    FiniteDimensional K (V →ₗ⁅K,𝔤⁆ Y) :=
  hV.isCategoryO.finiteDimensional_hom P hV.fg.choose_spec hY

include hA in
/-- If `V ↠ L(λ)`, then `V` has `P(λ)` as a retract. -/
theorem exists_retract (hV : IsFGProjectiveO P V) {Λ : Dual K H}
    (φ : V →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) (hφ : Function.Surjective φ) :
    ∃ (s : ProjectiveCover P hA Λ →ₗ⁅K,𝔤⁆ V) (r : V →ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ),
      r.comp s = LieModuleHom.id :=
  (ProjectiveCover.isProjectiveCover P Λ hA).exists_retract (ProjectiveCover.isProjectiveO P hA Λ)
    hV.isProjectiveO hV.isCategoryO φ hφ

omit [IsAlgClosed K] in
/-- `dim Hom(V, Y) = dim Hom(P(λ), Y) + dim Hom(C, Y)` for `V = P(λ) ⊕ C`. -/
theorem finrank_hom_eq_add (hV : IsFGProjectiveO P V) {Λ : Dual K H}
    {s : ProjectiveCover P hA Λ →ₗ⁅K,𝔤⁆ V} {r : V →ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ}
    (hrs : r.comp s = LieModuleHom.id) {Y : Type*} [AddCommGroup Y] [Module K Y]
    [LieRingModule P.KacMoodyAlgebra Y] [LieModule K P.KacMoodyAlgebra Y] (hY : IsCategoryO P Y) :
    finrank K (V →ₗ⁅K,𝔤⁆ Y) =
      finrank K (ProjectiveCover P hA Λ →ₗ⁅K,𝔤⁆ Y) + finrank K (r.ker →ₗ⁅K,𝔤⁆ Y) := by
  have := ProjectiveCover.finiteDimensional_hom P hA Λ hY
  have := (hV.ker hrs).finiteDimensional_hom hY
  rw [(LieModuleHom.homRetractEquiv hrs).finrank_eq, Module.finrank_prod]

omit [IsAlgClosed K] [LieModule K P.KacMoodyAlgebra V] in
/-- The complement of `P(λ)` is a proper submodule. -/
theorem ker_ne_top {Λ : Dual K H}
    {s : ProjectiveCover P hA Λ →ₗ⁅K,𝔤⁆ V} {r : V →ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ}
    (hrs : r.comp s = LieModuleHom.id) : r.ker ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := ProjectiveCover.surjective_π P hA Λ (IrreducibleModule.hwv P Λ)
  have h0 : r (s x) = 0 := LieModuleHom.mem_ker.mp (htop ▸ LieSubmodule.mem_top (s x))
  rw [← LieModuleHom.comp_apply r s, hrs, LieModuleHom.id_apply] at h0
  rw [h0, map_zero] at hx
  exact IrreducibleModule.hwv_ne_zero P Λ hx.symm

end IsFGProjectiveO

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- A nonzero morphism into `L(λ)` is surjective. -/
theorem surjective_of_ne_zero_irreducibleModule {W : Type*} [AddCommGroup W] [Module K W]
    [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W] {Λ : Dual K H}
    {f : W →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ} (hf0 : f ≠ 0) : Function.Surjective f := by
  have := IrreducibleModule.isIrreducible P Λ
  rw [← LieModuleHom.range_eq_top]
  refine (IsSimpleOrder.eq_bot_or_eq_top f.range).resolve_left fun h0 ↦ hf0 ?_
  ext y
  have : f y ∈ f.range := (LieModuleHom.mem_range _ _).mpr ⟨y, rfl⟩
  rw [h0, LieSubmodule.mem_bot] at this
  exact this

/-- A strictly monotone measure on the submodules of `V` restricts to one on the submodules of
`N ⊆ V`, with value `f N` at the top. -/
theorem _root_.LieSubmodule.strictMono_map_incl {R L M : Type*} [CommRing R] [LieRing L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] (N : LieSubmodule R L M)
    {f : LieSubmodule R L M → ℕ} (hf : StrictMono f) :
    StrictMono fun N' : LieSubmodule R L N ↦ f (N'.map N.incl) := by
  intro a b hab
  refine hf (lt_of_le_of_ne (LieSubmodule.map_mono hab.le) fun heq ↦ hab.ne ?_)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (LieSubmodule.mem_map _).mp (heq ▸ LieSubmodule.mem_map_of_mem hx :
      (x : M) ∈ b.map N.incl)
    rwa [Subtype.val_injective hyx] at hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (LieSubmodule.mem_map _).mp (heq.symm ▸ LieSubmodule.mem_map_of_mem hx :
      (x : M) ∈ a.map N.incl)
    rwa [Subtype.val_injective hyx] at hy

include hA in
/-- Finitely generated projectives `V, V'` in `𝒪` with `dim Hom(V, L(λ)) = dim Hom(V', L(λ))` for
all `λ` are isomorphic (cf. Humphreys, GSM 94, proof of Corollary 3.10). -/
theorem IsFGProjectiveO.nonempty_equiv_of_finrank_hom_eq {V V' : Type (max u₁ u₂)}
    [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V] [AddCommGroup V'] [Module K V']
    [LieRingModule P.KacMoodyAlgebra V'] [LieModule K P.KacMoodyAlgebra V']
    (hV : IsFGProjectiveO P V) (hV' : IsFGProjectiveO P V')
    (h : ∀ Λ, finrank K (V →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) =
      finrank K (V' →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ)) :
    Nonempty (V ≃ₗ⁅K,𝔤⁆ V') := by
  obtain ⟨f, hf⟩ := hV.isCategoryO.exists_strictMono_lieSubmodule P hA hV.fg.choose_spec
  suffices key : ∀ n : ℕ, ∀ (V V' : Type (max u₁ u₂)) [AddCommGroup V] [Module K V]
      [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] [AddCommGroup V']
      [Module K V'] [LieRingModule P.KacMoodyAlgebra V'] [LieModule K P.KacMoodyAlgebra V'],
      IsFGProjectiveO P V → IsFGProjectiveO P V' →
      (∀ Λ, finrank K (V →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) =
        finrank K (V' →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ)) →
      ∀ f : LieSubmodule K 𝔤 V → ℕ, StrictMono f → f ⊤ < n → Nonempty (V ≃ₗ⁅K,𝔤⁆ V') from
    key _ V V' hV hV' h f hf (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
  intro V V' _ _ _ _ _ _ _ _ hV hV' h f hf hn
  by_cases hVt : Nontrivial V
  · obtain ⟨Λ, φ, hφ⟩ := hV.isCategoryO.exists_surjective_irreducibleModule P hA
      hV.fg.choose_spec
    have hφ0 : φ ≠ 0 := fun h0 ↦ IrreducibleModule.hwv_ne_zero P Λ (by
      obtain ⟨x, hx⟩ := hφ (IrreducibleModule.hwv P Λ)
      rw [← hx, h0]; rfl)
    have := hV.finiteDimensional_hom (IrreducibleModule.isCategoryO P Λ)
    have := hV'.finiteDimensional_hom (IrreducibleModule.isCategoryO P Λ)
    have hpos : 0 < finrank K (V' →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) := by
      rw [← h Λ]
      exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨φ, hφ0⟩
    obtain ⟨ψ, hψ0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨s, r, hrs⟩ := hV.exists_retract hA φ hφ
    obtain ⟨s', r', hrs'⟩ := hV'.exists_retract hA ψ
      (surjective_of_ne_zero_irreducibleModule P hψ0)
    have hC : ∀ μ, finrank K (r.ker →ₗ⁅K,𝔤⁆ IrreducibleModule P μ) =
        finrank K (r'.ker →ₗ⁅K,𝔤⁆ IrreducibleModule P μ) := by
      intro μ
      have h1 := hV.finrank_hom_eq_add hA hrs (IrreducibleModule.isCategoryO P μ)
      have h2 := hV'.finrank_hom_eq_add hA hrs' (IrreducibleModule.isCategoryO P μ)
      have := h μ
      omega
    have hlt : f ((⊤ : LieSubmodule K 𝔤 r.ker).map r.ker.incl) < n := by
      rw [LieSubmodule.map_incl_top]
      have := hf (lt_top_iff_ne_top.mpr (IsFGProjectiveO.ker_ne_top hA hrs))
      omega
    obtain ⟨e⟩ := ih r.ker r'.ker (hV.ker hrs) (hV'.ker hrs') hC _
      (r.ker.strictMono_map_incl hf) hlt
    exact ⟨LieModuleHom.equivOfRetract hrs hrs' e⟩
  · rw [not_nontrivial_iff_subsingleton] at hVt
    have hV't : Subsingleton V' := by
      by_contra hcon
      rw [not_subsingleton_iff_nontrivial] at hcon
      obtain ⟨Λ, φ, hφ⟩ := hV'.isCategoryO.exists_surjective_irreducibleModule P hA
        hV'.fg.choose_spec
      have := hV'.finiteDimensional_hom (IrreducibleModule.isCategoryO P Λ)
      have hpos : 0 < finrank K (V' →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) :=
        Module.finrank_pos_iff_exists_ne_zero.mpr ⟨φ, fun h0 ↦ IrreducibleModule.hwv_ne_zero P Λ
          (by obtain ⟨x, hx⟩ := hφ (IrreducibleModule.hwv P Λ); rw [← hx, h0]; rfl)⟩
      have : Subsingleton (V →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) :=
        ⟨fun a b ↦ LieModuleHom.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      rw [← h Λ, Module.finrank_zero_of_subsingleton] at hpos
      exact Nat.lt_irrefl 0 hpos
    exact ⟨LieModuleEquiv.ofBijective 0 ⟨fun a b _ ↦ Subsingleton.elim a b,
      fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩

include hA in
/-- For a finitely generated projective `V ∈ 𝒪` there is a multiset `d` of weights with
`dim Hom(V, L(λ)) = d(λ)` (the number of summands `P(λ)`, Humphreys, GSM 94, Theorem 3.9 (b)), and
the Verma multiplicities `dim Hom(V, M(μ)^∨)` of `V` are those of `⊕_{λ ∈ d} P(λ)`. Here `t λ` are
the weights of a standard filtration of `P(λ)`. -/
theorem IsFGProjectiveO.exists_multiset [DecidableEq (Dual K H)] {V : Type (max u₁ u₂)}
    [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V] (hV : IsFGProjectiveO P V)
    {t : Dual K H → Multiset (Dual K H)}
    (ht : ∀ Λ, IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (ProjectiveCover P hA Λ)) (t Λ)) :
    ∃ d : Multiset (Dual K H),
      (∀ Λ, finrank K (V →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) = d.count Λ) ∧
      ∀ μ, finrank K (V →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P μ)) = (d.bind t).count μ := by
  obtain ⟨f, hf⟩ := hV.isCategoryO.exists_strictMono_lieSubmodule P hA hV.fg.choose_spec
  suffices key : ∀ n : ℕ, ∀ (V : Type (max u₁ u₂)) [AddCommGroup V] [Module K V]
      [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V],
      IsFGProjectiveO P V → ∀ f : LieSubmodule K 𝔤 V → ℕ, StrictMono f → f ⊤ < n →
      ∃ d : Multiset (Dual K H),
        (∀ Λ, finrank K (V →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) = d.count Λ) ∧
        ∀ μ, finrank K (V →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P μ)) = (d.bind t).count μ from
    key _ V hV f hf (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
  intro V _ _ _ _ hV f hf hn
  by_cases hVt : Nontrivial V
  · obtain ⟨Λ, φ, hφ⟩ := hV.isCategoryO.exists_surjective_irreducibleModule P hA
      hV.fg.choose_spec
    obtain ⟨s, r, hrs⟩ := hV.exists_retract hA φ hφ
    have hlt : f ((⊤ : LieSubmodule K 𝔤 r.ker).map r.ker.incl) < n := by
      rw [LieSubmodule.map_incl_top]
      have := hf (lt_top_iff_ne_top.mpr (IsFGProjectiveO.ker_ne_top hA hrs))
      omega
    obtain ⟨d, hd₁, hd₂⟩ := ih r.ker (hV.ker hrs) _ (r.ker.strictMono_map_incl hf) hlt
    refine ⟨Λ ::ₘ d, fun μ ↦ ?_, fun μ ↦ ?_⟩
    · rw [hV.finrank_hom_eq_add hA hrs (IrreducibleModule.isCategoryO P μ),
        ProjectiveCover.finrank_hom_irreducible P Λ hA μ, hd₁ μ, Multiset.count_cons]
      split_ifs <;> omega
    · have hdual := isCategoryO_restrictedDual (VermaModule.isCategoryO P μ)
      rw [hV.finrank_hom_eq_add hA hrs hdual, hd₂ μ, Multiset.cons_bind, Multiset.count_add,
        ← (ht Λ).count_eq_finrank_hom (ProjectiveCover.isCategoryO P hA Λ) μ]
  · rw [not_nontrivial_iff_subsingleton] at hVt
    have hzero {Y : Type (max u₁ u₂)} [AddCommGroup Y] [Module K Y]
        [LieRingModule P.KacMoodyAlgebra Y] [LieModule K P.KacMoodyAlgebra Y] :
        finrank K (V →ₗ⁅K,𝔤⁆ Y) = 0 := by
      have : Subsingleton (V →ₗ⁅K,𝔤⁆ Y) :=
        ⟨fun a b ↦ LieModuleHom.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      exact Module.finrank_zero_of_subsingleton
    exact ⟨0, fun Λ ↦ by rw [hzero, Multiset.count_zero],
      fun μ ↦ by rw [hzero, Multiset.zero_bind, Multiset.count_zero]⟩

include hA in
/-- **Humphreys, GSM 94, Corollary 3.10.** In finite type over an algebraically closed field of
characteristic zero, two finitely generated projective modules in `𝒪` with the same formal
character are isomorphic. Humphreys works over `ℂ`; the proof is reconstructed (see the module
docstring). -/
theorem IsProjectiveO.nonempty_equiv_of_character_eq {V V' : Type (max u₁ u₂)}
    [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V] [AddCommGroup V'] [Module K V']
    [LieRingModule P.KacMoodyAlgebra V'] [LieModule K P.KacMoodyAlgebra V']
    (hVproj : IsProjectiveO.{max u₁ u₂} P V) (hV : IsCategoryO P V) {S : Finset V}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set V) = ⊤)
    (hV'proj : IsProjectiveO.{max u₁ u₂} P V') (hV' : IsCategoryO P V') {S' : Finset V'}
    (hS' : LieSubmodule.lieSpan K 𝔤 (S' : Set V') = ⊤)
    (hch : hV.character = hV'.character) : Nonempty (V ≃ₗ⁅K,𝔤⁆ V') := by
  classical
  have hW : IsFGProjectiveO P V := ⟨hVproj, hV, S, hS⟩
  have hW' : IsFGProjectiveO P V' := ⟨hV'proj, hV', S', hS'⟩
  -- standard filtrations of `V` and `V'` have the same weights
  obtain ⟨s, hs⟩ := hVproj.exists_isStdFiltered P hA hV hS
  obtain ⟨s', hs'⟩ := hV'proj.exists_isStdFiltered P hA hV' hS'
  have hss' : s = s' := by
    refine Multiset.eq_of_forall_sum_map_eq (o := fun μ ↦ OrderDual.toDual (toWeightOrd P μ))
      (fun a b hab ↦ (toWeightOrd P).injective (OrderDual.toDual.injective hab))
      (w := fun μ ν ↦ finrank K (weightSpaceOfMap (VermaModule P μ) (h P) ν))
      (fun μ ↦ VermaModule.finrank_weightSpace_self P μ) (fun μ ν hne ↦ ?_) s s' fun ν ↦ ?_
    · change finrank K (weightSpaceOfMap (VermaModule P μ) (h P) ν) ≠ 0 at hne
      have hne' : weightSpaceOfMap (VermaModule P μ) (h P) ν ≠ ⊥ := fun h0 ↦ hne (by
        rw [h0, finrank_bot])
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
      exact (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
        (VermaModule.exists_eq_sub_of_mem_weightSpace P μ LieModuleHom.id Function.surjective_id
          hx hx0)
    · have h1 := hs.finrank_inf_weightSpaceOfMap P hV ν
      have h2 := hs'.finrank_inf_weightSpaceOfMap P hV' ν
      have h3 := congrArg (fun c ↦ c.coeffAt ν) hch
      simp only [IsCategoryO.coeffAt_character, Nat.cast_inj] at h3
      simp only [LieSubmodule.top_toSubmodule] at h1 h2
      rw [← h1, ← h2]
      convert h3 using 3 <;> exact top_inf_eq _
  -- the multisets of indecomposable summands agree
  choose t ht using fun Λ ↦ ProjectiveCover.exists_isStdFiltered P Λ hA
  obtain ⟨d, hd₁, hd₂⟩ := hW.exists_multiset P hA fun Λ ↦ (ht Λ).1
  obtain ⟨d', hd'₁, hd'₂⟩ := hW'.exists_multiset P hA fun Λ ↦ (ht Λ).1
  have hbind : d.bind t = d'.bind t := by
    ext μ
    rw [← hd₂, ← hd'₂, ← hs.count_eq_finrank_hom hV, ← hs'.count_eq_finrank_hom hV', hss']
  have hdd' : d = d' := by
    refine Multiset.eq_of_forall_sum_map_eq (o := toWeightOrd P) (toWeightOrd P).injective
      (w := fun Λ ν ↦ (t Λ).count ν) (fun Λ ↦ (ht Λ).2.1) (fun Λ ν hne ↦ ?_) d d' fun ν ↦ ?_
    · exact (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
        ((ht Λ).2.2 ν (Multiset.count_ne_zero.mp hne))
    · rw [← Multiset.count_bind, ← Multiset.count_bind, hbind]
  exact hW.nonempty_equiv_of_finrank_hom_eq P hA hW' fun Λ ↦ by rw [hd₁, hd'₁, hdd']

end Matrix.Realization.KacMoodyAlgebra
