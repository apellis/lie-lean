/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Levi
import LieLean.RepresentationTheory.Crystal.WeylGroupAction

/-!
# Kashiwara's reflections on path crystals: braid relations

Kashiwara's reflections `Sᵢ` (`Crystal.reflection`) act on the crystal of Littelmann paths and
on each `B(λ)`.

## Main results

* `LittelmannPath.reflection_straightLine`: `Sᵢ π_ν = π_{rᵢ ν}` for every integral `ν`.
* `LittelmannPath.rootStep_bind_comm`: root operators of colours `i, j` with
  `⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = 0` commute on all paths; hence
  `LittelmannPath.reflection_comm`: `Sᵢ Sⱼ = Sⱼ Sᵢ` (the braid relation for `mᵢⱼ = 2`).
* `Matrix.Realization.PathBraidRelations`: for a realization of a generalized Cartan matrix over
  `ℝ` and dominant integral `Λ`, the braid relations `(SᵢSⱼ)^{mᵢⱼ} = 1` on `B(Λ)` for the pairs
  with `mᵢⱼ ∈ {3, 4, 6}`. With them the `Sᵢ` satisfy all Coxeter relations of the Weyl group
  (`isLiftable_pathReflectionPerm`): the relations for `mᵢⱼ = 1, 2, ∞` are proved here. They are
  vacuous when no pair has `aᵢⱼ aⱼᵢ ∈ {1, 2, 3}` (`pathBraidRelations_of_forall`), e.g. for
  `A₁ × ⋯ × A₁` and for generalized Cartan matrices all of whose nonzero off-diagonal products
  are `≥ 4`.
* `Matrix.Realization.LSGeneralClass.LeviMap.iterate_reflection_eq_of_levi`: reduction of the
  braid relation for `Sᵢ, Sⱼ` on `B(Λ)` to the rank-two Levi path crystals `B_J(μ)`,
  `J = {i, j}`, via Levi restriction.

The braid relations of lengths `3, 4, 6` (types `A₂`, `B₂`, `G₂`) are proved in
`LieLean.RepresentationTheory.Crystal.Path.BraidA2` and, by folding,
`LieLean.RepresentationTheory.Crystal.Path.BraidFolding`
(`Matrix.Realization.pathBraidRelations`, every generalized Cartan matrix); the resulting action
of the Weyl group on `B(Λ)` is `Matrix.Realization.pathWeylAction` in
`LieLean.RepresentationTheory.Crystal.Path.WeylGroupAction`.

## References

* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413, §7.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2)
  **142** (1995), 499–525, §8.

The arguments are reconstructed.
-/

open Set Module

namespace LittelmannPath

variable {ι X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V] {D : CartanDatum ι X}
  {S : D.PathSpace ℝ V}

/-! ### Shifting a path by a multiple of another root -/

section Shift

variable {i : ι} {π₁ π₂ : LittelmannPath S}

/-- If `⟨π₂(t), αᵢ^∨⟩ = ⟨π₁(t), αᵢ^∨⟩` for all `t`, then `eᵢ` acts on `π₁` and `π₂` by the same
correction. -/
theorem e_shift (h : ∀ t, S.coroot i (π₂ t) = S.coroot i (π₁ t)) :
    (e i π₁ = none → e i π₂ = none) ∧ ∀ ρ₁, e i π₁ = some ρ₁ →
      ∃ ρ₂, e i π₂ = some ρ₂ ∧ ∀ t, ρ₂ t - ρ₁ t = π₂ t - π₁ t := by
  have hp : π₂.pairing i = π₁.pairing i := funext h
  have hrun : ∀ t, π₂.runningMin i t = π₁.runningMin i t := fun t => by
    simp only [runningMin, hp]
  have hmin : π₂.minPairing i = π₁.minPairing i := hrun 1
  have hc : ∀ t, π₂.eCoeff i t = π₁.eCoeff i t := fun t => by
    simp only [eCoeff, hrun, hmin]
  refine ⟨fun h1 => ?_, fun ρ₁ h1 => ?_⟩
  · rw [e_eq_none_iff] at h1 ⊢
    rwa [hmin]
  · obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp h1
    have hQ₂ : π₂.minPairing i ≤ -1 := by rwa [hmin]
    refine ⟨π₂.eRaw i hQ₂, e_of_le hQ₂, fun t => ?_⟩
    rw [eRaw_apply, eRaw_apply, hc]
    abel

/-- If `⟨π₂(t), αᵢ^∨⟩ = ⟨π₁(t), αᵢ^∨⟩` for all `t`, then `fᵢ` acts on `π₁` and `π₂` by the same
correction. -/
theorem f_shift (h : ∀ t, S.coroot i (π₂ t) = S.coroot i (π₁ t)) :
    (f i π₁ = none → f i π₂ = none) ∧ ∀ ρ₁, f i π₁ = some ρ₁ →
      ∃ ρ₂, f i π₂ = some ρ₂ ∧ ∀ t, ρ₂ t - ρ₁ t = π₂ t - π₁ t := by
  have hrev : ∀ t, S.coroot i (π₂.rev t) = S.coroot i (π₁.rev t) := fun t => by
    simp only [rev_apply, map_sub, h]
  obtain ⟨hn, hs⟩ := e_shift hrev
  refine ⟨fun h1 => ?_, fun ρ₁ h1 => ?_⟩
  · simp only [f, Option.map_eq_none_iff] at h1 ⊢
    exact hn h1
  · obtain ⟨σ₁, hσ₁, rfl⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨σ₂, hσ₂, hd⟩ := hs σ₁ hσ₁
    refine ⟨σ₂.rev, by rw [f, hσ₂, Option.map_some], fun t => ?_⟩
    have h1' := hd (1 - t)
    have h2' := hd 1
    rw [rev_apply, rev_apply, sub_sub_cancel] at h1'
    rw [rev_apply, rev_apply, sub_self, apply_zero, apply_zero] at h2'
    rw [rev_apply, rev_apply,
      show σ₂ (1 - t) - σ₂ 1 - (σ₁ (1 - t) - σ₁ 1) =
        (σ₂ (1 - t) - σ₁ (1 - t)) - (σ₂ 1 - σ₁ 1) by abel, h1', h2']
    abel

/-- The colour of a signed root letter. -/
def letterColour : ι ⊕ ι → ι := Sum.elim id id

/-- A root letter acts on two paths with the same pairing for its colour by the same
correction. -/
theorem rootStep_shift (a : ι ⊕ ι)
    (h : ∀ t, S.coroot (letterColour a) (π₂ t) = S.coroot (letterColour a) (π₁ t)) :
    (rootStep a π₁ = none → rootStep a π₂ = none) ∧ ∀ ρ₁, rootStep a π₁ = some ρ₁ →
      ∃ ρ₂, rootStep a π₂ = some ρ₂ ∧ ∀ t, ρ₂ t - ρ₁ t = π₂ t - π₁ t := by
  cases a with
  | inl i => exact e_shift h
  | inr i => exact f_shift h

/-- A root letter changes a path pointwise by a multiple of the root of its colour. -/
theorem exists_rootStep_sub (a : ι ⊕ ι) {π ρ : LittelmannPath S}
    (h : rootStep a π = some ρ) (t : ℝ) :
    ∃ c : ℝ, ρ t - π t = c • S.root (letterColour a) := by
  cases a with
  | inl i =>
    change e i π = some ρ at h
    obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp h
    exact ⟨-π.eCoeff i t, by rw [eRaw_apply, neg_smul]; abel⟩
  | inr i =>
    change f i π = some ρ at h
    have key : ∀ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, ρ s - π s = c • S.root i := fun s hs =>
      ⟨-(min (π.rightMin i s) (π.minPairing i + 1) - π.minPairing i), by
        rw [f_apply h hs, neg_smul]; abel⟩
    rcases le_or_gt t 0 with ht | ht
    · exact ⟨0, by rw [ρ.apply_of_nonpos ht, π.apply_of_nonpos ht, sub_zero, zero_smul]⟩
    rcases le_or_gt t 1 with ht1 | ht1
    · exact key t ⟨ht.le, ht1⟩
    · rw [ρ.apply_of_one_le ht1.le, π.apply_of_one_le ht1.le, ← ρ.apply_one, ← π.apply_one]
      exact key 1 ⟨zero_le_one, le_rfl⟩

end Shift

/-! ### Commuting colours -/

/-- **Root operators of orthogonal colours commute**: if `⟨α_b, α_a^∨⟩ = ⟨α_a, α_b^∨⟩ = 0` for
the colours of two root letters `a, b`, then `a b = b a` as partial maps on paths. -/
theorem rootStep_bind_comm {a b : ι ⊕ ι}
    (hab : S.coroot (letterColour b) (S.root (letterColour a)) = 0)
    (hba : S.coroot (letterColour a) (S.root (letterColour b)) = 0) (π : LittelmannPath S) :
    (rootStep a π).bind (rootStep b) = (rootStep b π).bind (rootStep a) := by
  have inv : ∀ (c d : ι ⊕ ι), S.coroot (letterColour d) (S.root (letterColour c)) = 0 →
      ∀ {π ρ : LittelmannPath S}, rootStep c π = some ρ →
        ∀ t, S.coroot (letterColour d) (ρ t) = S.coroot (letterColour d) (π t) := by
    intro c d hcd π ρ h t
    obtain ⟨k, hk⟩ := exists_rootStep_sub c h t
    rw [← sub_eq_zero, ← map_sub, hk, map_smul, hcd, smul_zero]
  cases ha : rootStep a π with
  | none =>
    rw [Option.bind_none]
    cases hb : rootStep b π with
    | none => rfl
    | some σ =>
      rw [Option.bind_some]
      exact ((rootStep_shift a (inv b a hba hb)).1 ha).symm
  | some ρ =>
    rw [Option.bind_some]
    cases hb : rootStep b π with
    | none => exact (rootStep_shift b (inv a b hab ha)).1 hb
    | some σ =>
      rw [Option.bind_some]
      obtain ⟨ρ', hρ', hd₁⟩ := (rootStep_shift b (inv a b hab ha)).2 σ hb
      obtain ⟨τ, hτ, hd₂⟩ := (rootStep_shift a (inv b a hba hb)).2 ρ ha
      rw [hρ', hτ]
      congr 1
      apply LittelmannPath.ext
      intro t
      have e1 := hd₁ t
      have e2 := hd₂ t
      rw [sub_eq_iff_eq_add] at e1 e2
      rw [e1, e2]
      abel

/-- The path crystal's operators of orthogonal colours commute. -/
theorem operatorsCommute {i j : ι} (hij : S.coroot i (S.root j) = 0)
    (hji : S.coroot j (S.root i) = 0) : (crystal S).OperatorsCommute i j where
  e_e π := rootStep_bind_comm (a := .inl i) (b := .inl j) hji hij π
  e_f π := rootStep_bind_comm (a := .inl i) (b := .inr j) hji hij π
  f_e π := rootStep_bind_comm (a := .inr i) (b := .inl j) hji hij π
  f_f π := rootStep_bind_comm (a := .inr i) (b := .inr j) hji hij π

/-- **The braid relation of length two on paths**: `Sᵢ Sⱼ = Sⱼ Sᵢ` when
`⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = 0`. -/
theorem reflection_comm {i j : ι} (hij : D.cartanMatrix i j = 0) (hji : D.cartanMatrix j i = 0)
    (π : LittelmannPath S) :
    (crystal S).reflection i ((crystal S).reflection j π) =
      (crystal S).reflection j ((crystal S).reflection i π) := by
  have h1 : S.coroot i (S.root j) = 0 := by rw [S.coroot_root, hij, Int.cast_zero]
  have h2 : S.coroot j (S.root i) = 0 := by rw [S.coroot_root, hji, Int.cast_zero]
  exact (isSeminormal_crystal S).reflection_comm (operatorsCommute h1 h2) hij hji π

/-- Kashiwara's reflection of a straight line path: `Sᵢ π_ν = π_{rᵢ ν}`. -/
theorem reflection_straightLine (i : ι) (ν : X) :
    (crystal S).reflection i (straightLine S ν) = straightLine S (D.reflection i ν) := by
  have hC := isSeminormal_crystal S
  have key : ∀ μ : X, 0 ≤ D.coroot i μ →
      (crystal S).reflection i (straightLine S μ) = straightLine S (D.reflection i μ) := by
    intro μ hμ
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hμ
    have h := fIter_straightLine (S := S) (μ := μ) (i := i) hk.symm.le
    rw [stringPath_eq_straightLine hk.symm] at h
    have h' := hC.fIter_reflection (b := straightLine S μ) (i := i) hμ
    change (crystal S).fIter i (D.coroot i μ).toNat (straightLine S μ) = _ at h'
    rw [hk, Int.toNat_natCast, h] at h'
    exact (Option.some_injective _ h').symm
  rcases le_total 0 (D.coroot i ν) with hν | hν
  · exact key ν hν
  · have h := key (D.reflection i ν) (by rw [D.coroot_reflection]; linarith)
    rw [D.reflection_reflection] at h
    rw [← h, hC.reflection_reflection]

end LittelmannPath

/-! ### The Weyl group action on `B(Λ)` -/

namespace Matrix.Realization

open LittelmannPath

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} (hA : A.IsGeneralizedCartan) {Λ : Dual ℝ H}

omit [DecidableEq ι] in
lemma cartanMatrix_cartanDatum_apply (i j : ι) : (P.cartanDatum hA).cartanMatrix i j = A i j := by
  rw [cartanMatrix_cartanDatum]

variable (P) in
/-- Kashiwara's reflection `Sᵢ` of `B(Λ)`, as a permutation. -/
noncomputable abbrev pathReflectionPerm (hΛ : P.IsDominantIntegral Λ) (i : ι) :
    Equiv.Perm (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component :=
  (isSeminormal_pathCrystal hA hΛ).reflectionPerm i

omit [DecidableEq ι] in
lemma coe_reflection_pathCrystal (hΛ : P.IsDominantIntegral Λ) (i : ι)
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ((P.pathCrystal hA hΛ).reflection i b : LittelmannPath (P.pathSpace hA)) =
      (crystal (P.pathSpace hA)).reflection i b :=
  Crystal.coe_reflection_restrict _ (isStable_component _) i b

omit [DecidableEq ι] in
/-- The braid relation of length two on `B(Λ)`: `Sᵢ Sⱼ = Sⱼ Sᵢ` when `aᵢⱼ = 0`. -/
theorem pathCrystal_reflection_comm (hΛ : P.IsDominantIntegral Λ) {i j : ι} (hij : A i j = 0)
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    (P.pathCrystal hA hΛ).reflection i ((P.pathCrystal hA hΛ).reflection j b) =
      (P.pathCrystal hA hΛ).reflection j ((P.pathCrystal hA hΛ).reflection i b) := by
  apply Subtype.ext
  rw [coe_reflection_pathCrystal, coe_reflection_pathCrystal, coe_reflection_pathCrystal,
    coe_reflection_pathCrystal]
  exact LittelmannPath.reflection_comm (by rw [cartanMatrix_cartanDatum_apply, hij])
    (by rw [cartanMatrix_cartanDatum_apply, (hA.zero_comm i j).mp hij]) _

variable (P) in
/-- The braid relations for Kashiwara's reflections on `B(Λ)` at the pairs `i ≠ j` with
`aᵢⱼ ≠ 0` and `mᵢⱼ < ∞`, i.e. `aᵢⱼ aⱼᵢ ∈ {1, 2, 3}` (types `A₂`, `B₂`, `G₂`):
`(SᵢSⱼ)^{mᵢⱼ} = 1`. -/
def PathBraidRelations (hΛ : P.IsDominantIntegral Λ) : Prop :=
  ∀ i j, i ≠ j → A i j ≠ 0 → A.coxeterMatrix i j ≠ 0 →
    (pathReflectionPerm P hA hΛ i * pathReflectionPerm P hA hΛ j) ^ A.coxeterMatrix i j = 1

/-- The remaining braid relations are vacuous when no pair has `aᵢⱼ aⱼᵢ ∈ {1, 2, 3}`. -/
theorem pathBraidRelations_of_forall (hΛ : P.IsDominantIntegral Λ)
    (h : ∀ i j, i ≠ j → A i j ≠ 0 → 4 ≤ A i j * A j i) : P.PathBraidRelations hA hΛ := by
  intro i j hij hA0 hM
  exfalso
  apply hM
  rw [A.coxeterMatrix_apply_of_ne hij]
  exact coxeterEntry_of_four_le (by have := h i j hij hA0; omega)

/-- With the braid relations of lengths `3, 4, 6`, Kashiwara's reflections satisfy all Coxeter
relations of the Weyl group: those with `mᵢⱼ = 1, 2, ∞` are proved. -/
theorem isLiftable_pathReflectionPerm (hΛ : P.IsDominantIntegral Λ)
    (h : P.PathBraidRelations hA hΛ) : A.coxeterMatrix.IsLiftable (pathReflectionPerm P hA hΛ) := by
  rw [Crystal.IsSeminormal.isLiftable_iff]
  intro i j hij hM
  by_cases hA0 : A i j = 0
  · have hm : A.coxeterMatrix i j = 2 := by
      rw [A.coxeterMatrix_apply_of_ne hij, hA0, zero_mul]
      rfl
    rw [hm]
    exact Crystal.IsSeminormal.reflectionPerm_mul_pow_two _
      (pathCrystal_reflection_comm hA hΛ hA0)
  · exact h i j hij hA0 hM

end Matrix.Realization

/-! ### Reduction of the braid relations to rank-two Levi crystals -/

namespace Matrix.Realization.LSGeneralClass

open LittelmannPath

variable {ι κ H H' : Type*} [Fintype ι] [Fintype κ] [AddCommGroup H] [Module ℝ H]
  [AddCommGroup H'] [Module ℝ H']
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}
  {e : κ → ι} {Q : Realization (A.submatrix e e) ℝ H'}
  {hA' : (A.submatrix e e).IsGeneralizedCartan}

omit [Fintype κ] in
/-- Kashiwara's reflection of a `J`-colour stays in the `J`-component. -/
theorem reflection_mem_jComponent (k : κ) (π : LittelmannPath (P.pathSpace hA)) :
    (crystal (P.pathSpace hA)).reflection (e k) π ∈ jComponent e π := by
  have h := (isSeminormal_crystal (P.pathSpace hA)).stringMap_reflection (e k) π
  unfold Crystal.stringMap at h
  split_ifs at h
  · rw [fIter_eq_rootWord] at h
    exact ⟨List.replicate _ (.inr k), by rw [LeviMap.liftWord, List.map_replicate]; exact h⟩
  · rw [eIter_eq_rootWord] at h
    exact ⟨List.replicate _ (.inl k), by rw [LeviMap.liftWord, List.map_replicate]; exact h⟩

namespace LeviMap

variable (L : LeviMap P e Q)

lemma fIter_restrict (k : κ) (n : ℕ) (π : LittelmannPath (P.pathSpace hA)) :
    (crystal (Q.pathSpace hA')).fIter k n (L.restrict π) =
      ((crystal (P.pathSpace hA)).fIter (e k) n π).map L.restrict := by
  rw [fIter_eq_rootWord, fIter_eq_rootWord, L.rootWord_restrict, liftWord, List.map_replicate]
  rfl

lemma eIter_restrict (k : κ) (n : ℕ) (π : LittelmannPath (P.pathSpace hA)) :
    (crystal (Q.pathSpace hA')).eIter k n (L.restrict π) =
      ((crystal (P.pathSpace hA)).eIter (e k) n π).map L.restrict := by
  rw [eIter_eq_rootWord, eIter_eq_rootWord, L.rootWord_restrict, liftWord, List.map_replicate]
  rfl

lemma coroot_wt_restrict (k : κ) (π : LittelmannPath (P.pathSpace hA)) :
    (Q.cartanDatum hA').coroot k (L.restrict (hA' := hA') π).wt =
      (P.cartanDatum hA).coroot (e k) π.wt := by
  apply Int.cast_injective (α := ℝ)
  rw [coroot_cartanDatum_cast, coroot_cartanDatum_cast]
  exact L.apply_coroot _ k

/-- Restriction intertwines Kashiwara's reflections `S_{e k}` and the Levi reflections `S_k`. -/
theorem restrict_reflection (k : κ) (π : LittelmannPath (P.pathSpace hA)) :
    L.restrict (hA' := hA') ((crystal (P.pathSpace hA)).reflection (e k) π) =
      (crystal (Q.pathSpace hA')).reflection k (L.restrict π) := by
  have hco : (Q.cartanDatum hA').coroot k ((crystal (Q.pathSpace hA')).wt (L.restrict π)) =
      (P.cartanDatum hA).coroot (e k) ((crystal (P.pathSpace hA)).wt π) :=
    L.coroot_wt_restrict k π
  rw [Crystal.reflection_eq_getD_stringMap, Crystal.reflection_eq_getD_stringMap, hco]
  have hs : ∀ n : ℤ, (crystal (Q.pathSpace hA')).stringMap k n (L.restrict π) =
      ((crystal (P.pathSpace hA)).stringMap (e k) n π).map L.restrict := by
    intro n
    unfold Crystal.stringMap
    split_ifs
    · exact L.fIter_restrict k _ π
    · exact L.eIter_restrict k _ π
  rw [hs]
  cases (crystal (P.pathSpace hA)).stringMap (e k) _ π <;> rfl

/-- **Reduction of the braid relations to rank two** (via Levi restriction): if the relation
`(S_k S_l)^m = 1` holds on every Levi path crystal `B_J(μ)`, then `(S_{e k} S_{e l})^m = 1`
holds on `B(Λ)`. -/
theorem iterate_reflection_eq_of_levi [FiniteDimensional ℝ H'] (L : LeviMap P e Q) (k l : κ)
    (m : ℕ)
    (hQ : ∀ (μ : Dual ℝ H') (hμ : Q.IsDominantIntegral μ),
      ∀ z ∈ (straightLine (Q.pathSpace hA') ⟨μ, hμ.mem_integralWeights⟩).component,
        ((crystal (Q.pathSpace hA')).reflection k ∘
          (crystal (Q.pathSpace hA')).reflection l)^[m] z = z)
    {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ) {x : LittelmannPath (P.pathSpace hA)}
    (hx : x ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ((crystal (P.pathSpace hA)).reflection (e k) ∘
      (crystal (P.pathSpace hA)).reflection (e l))^[m] x = x := by
  obtain ⟨y, hyB, hye, hjeq, hbij, hiso⟩ := L.exists_jHighest_componentIso (hA' := hA') hΛ hx
  set F := (crystal (P.pathSpace hA)).reflection (e k) ∘
    (crystal (P.pathSpace hA)).reflection (e l) with hF
  set G := (crystal (Q.pathSpace hA')).reflection k ∘
    (crystal (Q.pathSpace hA')).reflection l with hG
  have hsemi : Function.Semiconj (L.restrict (hA' := hA')) F G := fun π => by
    simp only [hF, hG, Function.comp_apply, L.restrict_reflection]
  -- `F` stays in the `J`-component.
  have hFmem : ∀ π, F π ∈ jComponent e π := fun π => by
    have h1 := reflection_mem_jComponent (hA := hA) (e := e) l π
    have h2 := reflection_mem_jComponent (hA := hA) (e := e) k
      ((crystal (P.pathSpace hA)).reflection (e l) π)
    rw [jComponent_eq_of_mem h1] at h2
    exact h2
  have hiter : ∀ n, F^[n] x ∈ jComponent e y := by
    intro n
    induction n with
    | zero => rw [← hjeq]; exact ⟨[], rfl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have := hFmem (F^[n] x)
      rw [jComponent_eq_of_mem ih] at this
      exact this
  have hxy : x ∈ jComponent e y := hiter 0
  -- The restricted endpoint is dominant.
  have hdom : Q.IsDominantIntegral ((L.restrict (hA' := hA') y).wt : Dual ℝ H') := by
    intro k'
    have hI := Matrix.Realization.isIntegral_of_mem_pathCrystal hA hΛ ⟨y, hyB⟩
    have hm : -1 < y.minPairing (e k') := e_eq_none_iff.mp (hye k')
    obtain ⟨z, hz⟩ := hI (e k')
    obtain ⟨n, hn⟩ := y.wt.2 (e k')
    have hle := y.minPairing_le (i := e k') ⟨zero_le_one, le_rfl⟩
    simp only [pairing, pathSpace_coroot, apply_one, pathSpace_embed] at hle
    rw [hz] at hm hle
    rw [hn] at hle
    have hz0 : (-1 : ℤ) < z := by exact_mod_cast hm
    have hzn : z ≤ n := by exact_mod_cast hle
    refine ⟨n.toNat, ?_⟩
    change L.toLinearMap y.wt (Q.coroot k') = _
    rw [L.apply_coroot, hn]
    exact_mod_cast (Int.toNat_of_nonneg (by omega)).symm
  obtain ⟨ψ, -⟩ := hiso
  -- The relation on the Levi component of `r ∘ y`, transported along `ψ`.
  have hGsub : ∀ z' ∈ (L.restrict (hA' := hA') y).component, G^[m] z' = z' := by
    intro z' hz'
    set C₁ := (straightLine (Q.pathSpace hA') (L.restrict (hA' := hA') y).wt).componentCrystal
    set C₂ := (L.restrict (hA' := hA') y).componentCrystal
    set G₁ := C₁.reflection k ∘ C₁.reflection l with hG₁
    set G₂ := C₂.reflection k ∘ C₂.reflection l with hG₂
    have hv₁ : Function.Semiconj Subtype.val G₁ G := fun b => by
      simp only [hG₁, hG, Function.comp_apply, C₁, componentCrystal,
        Crystal.coe_reflection_restrict]
    have hv₂ : Function.Semiconj Subtype.val G₂ G := fun b => by
      simp only [hG₂, hG, Function.comp_apply, C₂, componentCrystal,
        Crystal.coe_reflection_restrict]
    have hψs : Function.Semiconj ψ G₁ G₂ := fun b => by
      simp only [hG₁, hG₂, Function.comp_apply]
      rw [← Crystal.Equiv.coe_toStrictHom, ψ.toStrictHom.map_reflection,
        ψ.toStrictHom.map_reflection]
    set z₀ := ψ.toEquiv.symm ⟨z', hz'⟩
    have hz₀ : ψ z₀ = ⟨z', hz'⟩ := ψ.toEquiv.apply_symm_apply _
    have h₁ : G₁^[m] z₀ = z₀ := by
      apply Subtype.ext
      rw [(hv₁.iterate_right m) z₀]
      exact hQ _ hdom _ z₀.2
    have h₃ := (hψs.iterate_right m) z₀
    rw [h₁, hz₀] at h₃
    have h₂ := (hv₂.iterate_right m) ⟨z', hz'⟩
    rw [← h₃] at h₂
    exact h₂.symm
  have hrx : L.restrict (hA' := hA') x ∈ (L.restrict (hA' := hA') y).component :=
    hbij.mapsTo hxy
  have key : L.restrict (hA' := hA') (F^[m] x) = L.restrict x := by
    rw [(hsemi.iterate_right m) x]
    exact hGsub _ hrx
  exact hbij.injOn (hiter m) hxy key

end LeviMap

end Matrix.Realization.LSGeneralClass
