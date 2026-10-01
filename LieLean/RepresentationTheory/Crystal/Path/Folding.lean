/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Folding
import LieLean.RepresentationTheory.Crystal.Path.WeylAction

/-!
# Folding path crystals

Let `A` (on `ι`) and `A'` (on `ι'`) be generalized Cartan matrices with realizations `Q` and `R`,
and `o : ι' → ι` a surjection whose fibres (the *orbits*) consist of pairwise orthogonal colours
(`A'_{ab} = 0` for `a ≠ b` in one orbit). A *folding map* (`Matrix.Realization.FoldMap`) is a
linear map `ψ : 𝔥_Q* → 𝔥_R*` with `⟨ψ v, α_a^∨⟩ = ⟨v, α_{o a}^∨⟩` and
`ψ(αₖ) = ∑_{a ∈ o⁻¹(k)} α_a`. (Typical examples are the foldings `A₃ → B₂` and `D₄ → G₂` of
Dynkin diagrams along an automorphism.)

Composing paths with `ψ` (`FoldMap.fold`) sends Littelmann's root operators `eₖ, fₖ` to the
products `∏_{a ∈ o⁻¹(k)} e_a`, `∏_{a ∈ o⁻¹(k)} f_a` (`FoldMap.e_fold`, `FoldMap.f_fold`): the
functions `h_a` of `ψ ∘ π` for `a` in the orbit of `k` all equal `hₖ` of `π`, and applying `e_a`
does not change `h_b` for `b` orthogonal to `a`. Consequently `ψ ∘ ·` maps `B(μ)` into
`B(ψ μ)` (`FoldMap.fold_mem_component`) and sends Kashiwara's reflection `Sₖ` to the product of
the commuting reflections `S_a`, `a ∈ o⁻¹(k)` (`FoldMap.fold_reflection_of_orbit_eq_singleton`,
`FoldMap.fold_reflection_of_orbit_eq_pair`, `FoldMap.fold_reflection_of_orbit_eq_triple`).

## Main definitions

* `LittelmannPath.eList`, `LittelmannPath.fList`: products of root operators along a list.
* `Matrix.Realization.FoldMap`: a folding map between realizations.
* `Matrix.Realization.FoldMap.fold`: the folded path `ψ ∘ π`.
* `Matrix.Realization.FoldMap.ofSpan`: a folding map exists whenever the coroots of `R` span
  `𝔥_R` and `A_{o(b), k} = ∑_{a ∈ o⁻¹(k)} A'_{b a}`.

The folding argument is standard for crystals (e.g. for Lakshmibai–Seshadri paths of orbit Lie
algebras); the statements and proofs here are reconstructed for the path model.
-/

open Set Module

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}
  {ι₀ X₀ V₀ : Type*} [AddCommGroup X₀] [AddCommGroup V₀] [Module 𝕜 V₀]
  {D₀ : CartanDatum ι₀ X₀} {S₀ : D₀.PathSpace 𝕜 V₀}

/-! ### Products of root operators along a list -/

/-- The product `e_{a₁} ⋯ e_{aₙ}` of root operators along the list `[a₁, …, aₙ]` (the last
entry is applied first). -/
noncomputable def eList : List ι → LittelmannPath S → Option (LittelmannPath S)
  | [], π => some π
  | a :: L, π => (eList L π).bind (e a)

/-- The product `f_{a₁} ⋯ f_{aₙ}` of root operators along the list `[a₁, …, aₙ]` (the last
entry is applied first). -/
noncomputable def fList : List ι → LittelmannPath S → Option (LittelmannPath S)
  | [], π => some π
  | a :: L, π => (fList L π).bind (f a)

@[simp] lemma eList_nil (π : LittelmannPath S) : eList [] π = some π := rfl

lemma eList_cons (a : ι) (L : List ι) (π : LittelmannPath S) :
    eList (a :: L) π = (eList L π).bind (e a) := rfl

@[simp] lemma fList_nil (π : LittelmannPath S) : fList [] π = some π := rfl

lemma fList_cons (a : ι) (L : List ι) (π : LittelmannPath S) :
    fList (a :: L) π = (fList L π).bind (f a) := rfl

/-- `f`-products are `e`-products conjugated by the time reversal. -/
lemma fList_eq (L : List ι) (π : LittelmannPath S) : fList L π = (eList L π.rev).map rev := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [fList_cons, eList_cons, ih]
    cases eList L π.rev with
    | none => rfl
    | some y =>
      rw [Option.map_some, Option.bind_some, Option.bind_some, f_rev]

/-- **Products of orthogonal root operators with a common function `h`**: if the colours of a
list `L` are pairwise orthogonal and `h_a(ξ) = hₖ(ρ)` for all `a ∈ L` (for a path `ρ` in any
path space), then `∏_{a ∈ L} e_a` acts on `ξ` by `ξ ↦ ξ - c ∑_{a ∈ L} α_a`, where
`eₖ ρ = ρ - c αₖ`; and it vanishes on `ξ` if `eₖ ρ = 0` and `L ≠ []`. -/
theorem eList_of_pairing_eq {ρ : LittelmannPath S₀} {k : ι₀} {ξ : LittelmannPath S} :
    ∀ {L : List ι}, L.Nodup → (∀ a ∈ L, ∀ b ∈ L, a ≠ b → S.coroot a (S.root b) = 0) →
      (∀ a ∈ L, ξ.pairing a = ρ.pairing k) →
      (ρ.minPairing k ≤ -1 → ∃ y, eList L ξ = some y ∧
        ∀ t, y t = ξ t - ρ.eCoeff k t • (L.map S.root).sum) ∧
      (¬ ρ.minPairing k ≤ -1 → L ≠ [] → eList L ξ = none)
  | [], _, _, _ => ⟨fun _ => ⟨ξ, rfl, fun t => by simp⟩, fun _ h => absurd rfl h⟩
  | a :: L, hL, horth, hg => by
    obtain ⟨haL, hL'⟩ := List.nodup_cons.mp hL
    have ih := eList_of_pairing_eq hL'
      (fun x hx y hy hxy => horth x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
      (fun x hx => hg x (List.mem_cons_of_mem a hx))
    have hga := hg a List.mem_cons_self
    refine ⟨fun hQ => ?_, fun hQ _ => ?_⟩
    · obtain ⟨y, hy, hyt⟩ := ih.1 hQ
      have hpa : y.pairing a = ρ.pairing k := by
        funext t
        have h0 : S.coroot a ((L.map S.root).sum) = 0 := by
          rw [map_list_sum, List.map_map]
          refine List.sum_eq_zero fun x hx => ?_
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact horth a List.mem_cons_self b (List.mem_cons_of_mem a hb)
            (fun h => haL (h ▸ hb))
        rw [← hga]
        simp only [pairing, hyt, map_sub, map_smul, h0, smul_zero, sub_zero]
      have hmin : y.minPairing a = ρ.minPairing k := by simp only [minPairing, runningMin, hpa]
      have hc : ∀ t, y.eCoeff a t = ρ.eCoeff k t := fun t => by
        simp only [eCoeff, runningMin, minPairing, hpa]
      have hQ' : y.minPairing a ≤ -1 := hmin ▸ hQ
      refine ⟨y.eRaw a hQ', by rw [eList_cons, hy, Option.bind_some, e_of_le hQ'], fun t => ?_⟩
      rw [eRaw_apply, hyt, hc, List.map_cons, List.sum_cons, smul_add]
      abel
    · by_cases hne : L = []
      · subst hne
        have hm : ξ.minPairing a = ρ.minPairing k := by simp only [minPairing, runningMin, hga]
        rw [eList_cons, eList_nil, Option.bind_some, e_eq_none_iff, hm]
        exact not_le.mp hQ
      · rw [eList_cons, ih.2 hQ hne, Option.bind_none]

variable [FloorRing 𝕜]

/-- Products of root operators stay in a stable set. -/
lemma eList_mem {T : Set (LittelmannPath S)} (hT : (crystal S).IsStable T) :
    ∀ (L : List ι) {π y : LittelmannPath S}, π ∈ T → eList L π = some y → y ∈ T
  | [], _, _, hπ, h => by
    cases h
    exact hπ
  | a :: L, π, y, hπ, h => by
    rw [eList_cons] at h
    obtain ⟨z, hz, hzy⟩ := Option.bind_eq_some_iff.mp h
    exact hT.e_mem a z y (eList_mem hT L hπ hz) hzy

/-- Products of root operators stay in a stable set. -/
lemma fList_mem {T : Set (LittelmannPath S)} (hT : (crystal S).IsStable T) :
    ∀ (L : List ι) {π y : LittelmannPath S}, π ∈ T → fList L π = some y → y ∈ T
  | [], _, _, hπ, h => by
    cases h
    exact hπ
  | a :: L, π, y, hπ, h => by
    rw [fList_cons] at h
    obtain ⟨z, hz, hzy⟩ := Option.bind_eq_some_iff.mp h
    exact hT.f_mem a z y (fList_mem hT L hπ hz) hzy

end LittelmannPath

/-! ### Folding maps between realizations -/

namespace Matrix.Realization

open LittelmannPath

variable {ι ι' H H' : Type*} [Fintype ι] [Fintype ι'] [AddCommGroup H] [Module ℝ H]
  [AddCommGroup H'] [Module ℝ H'] {A : Matrix ι ι ℤ} {A' : Matrix ι' ι' ℤ}
  {hA : A.IsGeneralizedCartan} {hA' : A'.IsGeneralizedCartan}

lemma pathSpace_coroot_root {P : Realization A ℝ H} (i j : ι) :
    (P.pathSpace hA).coroot i ((P.pathSpace hA).root j) = A i j := by
  change P.root j (P.coroot i) = _
  rw [P.root_coroot]

lemma list_sum_apply (L : List (Dual ℝ H)) (x : H) : L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

/-- The coroots of a realization of a nonsingular matrix span `𝔥`. -/
theorem span_coroot_eq_top_of_det_ne_zero [DecidableEq ι] [Nonempty ι] (P : Realization A ℝ H)
    (hdet : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0) : Submodule.span ℝ (Set.range P.coroot) = ⊤ := by
  have hrank : (A.map (Int.cast : ℤ → ℝ)).rank = Fintype.card ι :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hfin := P.finrank_add_rank
  exact P.linearIndependent_coroot.span_eq_top_of_card_eq_finrank (by omega)

variable (Q : Realization A ℝ H) (R : Realization A' ℝ H') in
/-- A **folding map** from a realization `Q` of `A` (colours `ι`) to a realization `R` of `A'`
(colours `ι'`): a colour map `ι' → ι` whose fibres, the orbits (listed without repetition by
`orbit`), are nonempty and consist of pairwise orthogonal colours, and a linear map
`ψ : 𝔥_Q* → 𝔥_R*` with `⟨ψ v, α_a^∨⟩ = ⟨v, α_{o a}^∨⟩` and `ψ(αₖ) = ∑_{a ∈ orbit k} α_a`. -/
structure FoldMap where
  /-- The colour map `ι' → ι`. -/
  colour : ι' → ι
  /-- The orbit of a colour of `A`, as a list. -/
  orbit : ι → List ι'
  mem_orbit : ∀ k a, a ∈ orbit k ↔ colour a = k
  nodup_orbit : ∀ k, (orbit k).Nodup
  orbit_ne_nil : ∀ k, orbit k ≠ []
  orthogonal : ∀ a b, a ≠ b → colour a = colour b → A' a b = 0
  /-- The linear map `ψ : 𝔥_Q* → 𝔥_R*`. -/
  toLinearMap : Dual ℝ H →ₗ[ℝ] Dual ℝ H'
  apply_coroot : ∀ v a, toLinearMap v (R.coroot a) = v (Q.coroot (colour a))
  map_root : ∀ k, toLinearMap (Q.root k) = ((orbit k).map R.root).sum

namespace FoldMap

variable {Q : Realization A ℝ H} {R : Realization A' ℝ H'} (F : FoldMap Q R)

/-- Folding preserves integrality. -/
theorem map_mem_integralWeights {v : Dual ℝ H} (hv : v ∈ Q.integralWeights) :
    F.toLinearMap v ∈ R.integralWeights := fun a => by
  rw [F.apply_coroot]
  exact hv (F.colour a)

/-- Folding preserves dominant integrality. -/
theorem isDominantIntegral {v : Dual ℝ H} (hv : Q.IsDominantIntegral v) :
    R.IsDominantIntegral (F.toLinearMap v) := fun a => by
  rw [F.apply_coroot]
  exact hv (F.colour a)

/-- The folded path `ψ ∘ π`. -/
noncomputable def fold (π : LittelmannPath (Q.pathSpace hA)) :
    LittelmannPath (R.pathSpace hA') where
  toFun t := F.toLinearMap (π t)
  wt := ⟨F.toLinearMap π.wt, F.map_mem_integralWeights π.wt.2⟩
  toFun_of_nonpos' t ht := by rw [π.apply_of_nonpos ht, map_zero]
  toFun_of_one_le' t ht := by rw [π.apply_of_one_le ht, pathSpace_embed, pathSpace_embed]
  continuous_coroot' a := by
    simp only [pathSpace_coroot, F.apply_coroot]
    exact π.continuous_pairing (F.colour a)

theorem fold_apply (π : LittelmannPath (Q.pathSpace hA)) (t : ℝ) :
    F.fold (hA' := hA') π t = F.toLinearMap (π t) := rfl

theorem pairing_fold (π : LittelmannPath (Q.pathSpace hA)) (a : ι') :
    (F.fold (hA' := hA') π).pairing a = π.pairing (F.colour a) := by
  funext t
  simp only [pairing, pathSpace_coroot, fold_apply, F.apply_coroot]

theorem coroot_wt_fold (π : LittelmannPath (Q.pathSpace hA)) (a : ι') :
    (R.cartanDatum hA').coroot a (F.fold (hA' := hA') π).wt =
      (Q.cartanDatum hA).coroot (F.colour a) π.wt := by
  apply Int.cast_injective (α := ℝ)
  rw [coroot_cartanDatum_cast, coroot_cartanDatum_cast]
  exact F.apply_coroot _ a

theorem fold_rev (π : LittelmannPath (Q.pathSpace hA)) :
    F.fold (hA' := hA') π.rev = (F.fold π).rev := by
  apply LittelmannPath.ext
  intro t
  rw [fold_apply, rev_apply, rev_apply, fold_apply, fold_apply, map_sub]

/-- Folding sends `eₖ` to the product of the `e_a`, `a` in the orbit of `k`. -/
theorem e_fold (π : LittelmannPath (Q.pathSpace hA)) (k : ι) :
    (e k π).map (F.fold (hA' := hA')) = eList (F.orbit k) (F.fold π) := by
  have horth : ∀ a ∈ F.orbit k, ∀ b ∈ F.orbit k, a ≠ b →
      (R.pathSpace hA').coroot a ((R.pathSpace hA').root b) = 0 := fun a ha b hb hab => by
    rw [pathSpace_coroot_root, F.orthogonal a b hab (by
      rw [(F.mem_orbit k a).1 ha, (F.mem_orbit k b).1 hb]), Int.cast_zero]
  have hg : ∀ a ∈ F.orbit k, (F.fold (hA' := hA') π).pairing a = π.pairing k := fun a ha => by
    rw [pairing_fold, (F.mem_orbit k a).1 ha]
  have H := eList_of_pairing_eq (ρ := π) (k := k) (F.nodup_orbit k) horth hg
  by_cases hQ : π.minPairing k ≤ -1
  · obtain ⟨y, hy, hyt⟩ := H.1 hQ
    rw [e_of_le hQ, Option.map_some, hy]
    congr 1
    apply LittelmannPath.ext
    intro t
    rw [hyt, fold_apply, fold_apply, eRaw_apply, map_sub, map_smul]
    congr 2
    exact F.map_root k
  · rw [H.2 hQ (F.orbit_ne_nil k), e_eq_none_iff.mpr (not_le.mp hQ), Option.map_none]

/-- Folding sends `fₖ` to the product of the `f_a`, `a` in the orbit of `k`. -/
theorem f_fold (π : LittelmannPath (Q.pathSpace hA)) (k : ι) :
    (f k π).map (F.fold (hA' := hA')) = fList (F.orbit k) (F.fold π) := by
  rw [fList_eq, ← fold_rev, ← e_fold, f, Option.map_map, Option.map_map]
  congr 1
  funext ρ
  exact F.fold_rev ρ

/-- Folding maps `B(π)` into `B(ψ ∘ π)`. -/
theorem fold_mem_component {π₀ π : LittelmannPath (Q.pathSpace hA)} (hπ : π ∈ π₀.component) :
    F.fold (hA' := hA') π ∈ (F.fold (hA' := hA') π₀).component := by
  have hT : (crystal (Q.pathSpace hA)).IsStable
      {x | F.fold (hA' := hA') x ∈ (F.fold (hA' := hA') π₀).component} :=
    { e_mem := fun k x y hx h => by
        change e k x = some y at h
        have h' := F.e_fold (hA' := hA') x k
        rw [h, Option.map_some] at h'
        exact eList_mem (isStable_component _) _ hx h'.symm
      f_mem := fun k x y hx h => by
        change f k x = some y at h
        have h' := F.f_fold (hA' := hA') x k
        rw [h, Option.map_some] at h'
        exact fList_mem (isStable_component _) _ hx h'.symm }
  exact Crystal.closure_subset hT (singleton_subset_iff.mpr (mem_component_self _)) hπ

/-- Folding a straight line path gives a straight line path. -/
theorem fold_straightLine (μ : Q.integralWeights) :
    F.fold (hA' := hA') (straightLine (Q.pathSpace hA) μ) =
      straightLine (R.pathSpace hA') ⟨F.toLinearMap μ, F.map_mem_integralWeights μ.2⟩ := by
  apply LittelmannPath.ext
  intro t
  simp only [fold_apply, straightLine_apply, map_smul, pathSpace_embed]

theorem fold_injective (hF : Function.Injective F.toLinearMap) :
    Function.Injective (F.fold (hA := hA) (hA' := hA')) := fun π π' h => by
  apply LittelmannPath.ext
  intro t
  apply hF
  rw [← fold_apply, ← fold_apply, h]

/-- `ψ` is injective when the coroots of `Q` span `𝔥_Q`. -/
theorem injective_of_span (hspan : Submodule.span ℝ (Set.range Q.coroot) = ⊤) :
    Function.Injective F.toLinearMap := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  refine LinearMap.ext_on hspan ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (F.orbit_ne_nil k)
  have h := congrArg (fun φ : Dual ℝ H' => φ (R.coroot a)) hv
  simp only [F.apply_coroot, (F.mem_orbit k a).1 ha, LinearMap.zero_apply] at h
  exact h

lemma orthogonal_pathSpace {a b : ι'} (hab : a ≠ b) (h : F.colour a = F.colour b) :
    (R.pathSpace hA').coroot a ((R.pathSpace hA').root b) = 0 := by
  rw [pathSpace_coroot_root, F.orthogonal a b hab h, Int.cast_zero]

lemma orthogonal_cartanDatum {a b : ι'} (hab : a ≠ b) (h : F.colour a = F.colour b) :
    (R.cartanDatum hA').coroot a ((R.cartanDatum hA').root b) = 0 := by
  rw [← CartanDatum.cartanMatrix_apply, cartanMatrix_cartanDatum, F.orthogonal a b hab h]

/-- Folding sends `Sₖ` to `S_a` when the orbit of `k` is `{a}`. -/
theorem fold_reflection_of_orbit_eq_singleton {k : ι} {a : ι'} (hk : F.orbit k = [a])
    (π : LittelmannPath (Q.pathSpace hA)) :
    F.fold (hA' := hA') ((crystal (Q.pathSpace hA)).reflection k π) =
      (crystal (R.pathSpace hA')).reflection a (F.fold π) := by
  have ha : F.colour a = k := (F.mem_orbit k a).1 (by rw [hk]; exact List.mem_singleton_self a)
  refine (isSeminormal_crystal _).map_reflection_of_eq (isSeminormal_crystal _)
    (fun x => ?_) (fun x => ?_) (fun x => ?_) π
  · have h := F.e_fold (hA' := hA') x k
    rw [hk] at h
    exact h
  · have h := F.f_fold (hA' := hA') x k
    rw [hk] at h
    exact h
  · simp only [crystal_wt]
    rw [coroot_wt_fold, ha]

/-- Folding sends `Sₖ` to `S_a S_c` when the orbit of `k` is `{a, c}`. -/
theorem fold_reflection_of_orbit_eq_pair {k : ι} {a c : ι'} (hk : F.orbit k = [a, c])
    (π : LittelmannPath (Q.pathSpace hA)) :
    F.fold (hA' := hA') ((crystal (Q.pathSpace hA)).reflection k π) =
      (crystal (R.pathSpace hA')).reflection a
        ((crystal (R.pathSpace hA')).reflection c (F.fold π)) := by
  have ha : F.colour a = k := (F.mem_orbit k a).1 (by rw [hk]; simp)
  have hc : F.colour c = k := (F.mem_orbit k c).1 (by rw [hk]; simp)
  have hac : a ≠ c := by
    have := F.nodup_orbit k
    rw [hk] at this
    simpa using this
  refine (isSeminormal_crystal _).map_reflection_of_bind₂ (isSeminormal_crystal _)
    (fun x => ?_) (fun x => ?_)
    (operatorsCommute (F.orthogonal_pathSpace hac.symm (hc.trans ha.symm))
      (F.orthogonal_pathSpace hac (ha.trans hc.symm)))
    (F.orthogonal_cartanDatum hac (ha.trans hc.symm)) (fun x => ?_) (fun x => ?_) π
  · have h := F.e_fold (hA' := hA') x k
    rw [hk] at h
    exact h
  · have h := F.f_fold (hA' := hA') x k
    rw [hk] at h
    exact h
  · simp only [crystal_wt]
    rw [coroot_wt_fold, ha]
  · simp only [crystal_wt]
    rw [coroot_wt_fold, hc]

/-- Folding sends `Sₖ` to `S_a S_c S_d` when the orbit of `k` is `{a, c, d}`. -/
theorem fold_reflection_of_orbit_eq_triple {k : ι} {a c d : ι'} (hk : F.orbit k = [a, c, d])
    (π : LittelmannPath (Q.pathSpace hA)) :
    F.fold (hA' := hA') ((crystal (Q.pathSpace hA)).reflection k π) =
      (crystal (R.pathSpace hA')).reflection a ((crystal (R.pathSpace hA')).reflection c
        ((crystal (R.pathSpace hA')).reflection d (F.fold π))) := by
  have ha : F.colour a = k := (F.mem_orbit k a).1 (by rw [hk]; simp)
  have hc : F.colour c = k := (F.mem_orbit k c).1 (by rw [hk]; simp)
  have hd : F.colour d = k := (F.mem_orbit k d).1 (by rw [hk]; simp)
  have hnd := F.nodup_orbit k
  rw [hk] at hnd
  have hac : a ≠ c := fun h => by subst h; simp at hnd
  have had : a ≠ d := fun h => by subst h; simp at hnd
  have hcd : c ≠ d := fun h => by subst h; simp at hnd
  have comm : ∀ {x y : ι'}, x ≠ y → F.colour x = k → F.colour y = k →
      (crystal (R.pathSpace hA')).OperatorsCommute x y := fun hxy hx hy =>
    operatorsCommute (F.orthogonal_pathSpace hxy (hx.trans hy.symm))
      (F.orthogonal_pathSpace (Ne.symm hxy) (hy.trans hx.symm))
  refine (isSeminormal_crystal _).map_reflection_of_bind₃ (isSeminormal_crystal _)
    (fun x => ?_) (fun x => ?_) (comm (Ne.symm hcd) hd hc) (comm (Ne.symm had) hd ha)
    (comm (Ne.symm hac) hc ha) (F.orthogonal_cartanDatum hcd (hc.trans hd.symm))
    (F.orthogonal_cartanDatum had (ha.trans hd.symm))
    (F.orthogonal_cartanDatum hac (ha.trans hc.symm)) (fun x => ?_) (fun x => ?_)
    (fun x => ?_) π
  · have h := F.e_fold (hA' := hA') x k
    rw [hk] at h
    exact h
  · have h := F.f_fold (hA' := hA') x k
    rw [hk] at h
    exact h
  · simp only [crystal_wt]
    rw [coroot_wt_fold, ha]
  · simp only [crystal_wt]
    rw [coroot_wt_fold, hc]
  · simp only [crystal_wt]
    rw [coroot_wt_fold, hd]

end FoldMap

/-- **Existence of folding maps**: if the coroots of `R` span `𝔥_R` and
`A_{o(b), k} = ∑_{a ∈ orbit k} A'_{b a}` for all `b, k`, then a folding map with the given colour
map and orbits exists. -/
noncomputable def FoldMap.ofSpan (Q : Realization A ℝ H) (R : Realization A' ℝ H')
    (hspan : Submodule.span ℝ (Set.range R.coroot) = ⊤) (colour : ι' → ι) (orbit : ι → List ι')
    (mem_orbit : ∀ k a, a ∈ orbit k ↔ colour a = k) (nodup_orbit : ∀ k, (orbit k).Nodup)
    (orbit_ne_nil : ∀ k, orbit k ≠ [])
    (orthogonal : ∀ a b, a ≠ b → colour a = colour b → A' a b = 0)
    (hfold : ∀ b k, A (colour b) k = ((orbit k).map fun a => A' b a).sum) : FoldMap Q R :=
  let bR := Basis.mk R.linearIndependent_coroot (by rw [hspan])
  let χ : H' →ₗ[ℝ] H := bR.constr ℝ fun a => Q.coroot (colour a)
  have hχ : ∀ a, χ (R.coroot a) = Q.coroot (colour a) := fun a => by
    rw [← Basis.mk_apply R.linearIndependent_coroot (by rw [hspan]) a]
    exact bR.constr_basis ℝ _ a
  { colour, orbit, mem_orbit, nodup_orbit, orbit_ne_nil, orthogonal
    toLinearMap := χ.dualMap
    apply_coroot := fun v a => by rw [LinearMap.dualMap_apply, hχ]
    map_root := fun k => by
      refine bR.ext fun b => ?_
      rw [Basis.mk_apply, LinearMap.dualMap_apply, hχ, Q.root_coroot, list_sum_apply,
        List.map_map, hfold, Int.cast_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun a _ => ?_
      simp [R.root_coroot] }

end Matrix.Realization
