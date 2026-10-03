/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.ComponentWords

/-!
# Stretching paths and component isomorphisms

For `N ∈ ℕ` the stretched path `Nπ` is `t ↦ N π(t)`. Littelmann's definition of the root
operators is compatible with stretching: `N(f_α π) = f_α^N (Nπ)` and `N(e_α π) = e_α^N (Nπ)`
(Lemma 2.4). Consequently a component isomorphism `B(Nπ₁) ≅ B(Nπ₂)` with `Nπ₁ ↦ Nπ₂`
descends to `B(π₁) ≅ B(π₂)` with `π₁ ↦ π₂` (Lemma 2.5 b)).

## Main results

* `stretch`, `pairing_stretch`, `minPairing_stretch`, `rightMin_stretch`.
* `fIter_stretch`, `eIter_stretch`: [Lit95] Lemma 2.4, including the vanishing cases.
* `rootWord_stretchWord`: a mixed word `u` on `π` corresponds to the word `u` with every letter
  repeated `N` times on `Nπ`.
* `ComponentIso.rootWord_eq_none_iff`, `ComponentIso.rootWord_eq_iff`: a component isomorphism
  preserves vanishing of words and word relations (the converse of `componentIso_of_rootWord`).
* `componentIso_of_componentIso_stretch`: [Lit95] Lemma 2.5 b).

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2) 142
(1995), no. 3, 499–525, §2, Lemmas 2.4 and 2.5, pp. 504–505. The proofs here are
reconstructed from the closed root-operator formulas of the library.
-/

open Set Module LittelmannPath

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- The stretched path `Nπ : t ↦ N π(t)` of [Lit95] §2, p. 504. -/
noncomputable def stretch (N : ℕ) (π : LittelmannPath (P.pathSpace hA)) :
    LittelmannPath (P.pathSpace hA) where
  toFun t := N • π t
  wt := N • π.wt
  toFun_of_nonpos' t ht := by rw [π.apply_of_nonpos ht, smul_zero]
  toFun_of_one_le' t ht := by
    rw [π.apply_of_one_le ht, pathSpace_embed, pathSpace_embed, AddSubgroup.coe_nsmul]
  continuous_coroot' i := by
    simp only [map_nsmul]
    exact (π.continuous_pairing i).nsmul N

theorem stretch_apply (N : ℕ) (π : LittelmannPath (P.pathSpace hA)) (t : ℝ) :
    stretch N π t = N • π t := rfl

@[simp] theorem wt_stretch (N : ℕ) (π : LittelmannPath (P.pathSpace hA)) :
    (stretch N π).wt = N • π.wt := rfl

theorem pairing_stretch (N : ℕ) (π : LittelmannPath (P.pathSpace hA)) (i : ι) (t : ℝ) :
    (stretch N π).pairing i t = N * π.pairing i t := by
  simp only [pairing, stretch_apply, map_nsmul, nsmul_eq_mul]

theorem minPairing_stretch (N : ℕ) (π : LittelmannPath (P.pathSpace hA)) (i : ι) :
    (stretch N π).minPairing i = N * π.minPairing i := by
  apply le_antisymm
  · obtain ⟨s, hs, hmin⟩ := π.exists_minPairing i
    calc (stretch N π).minPairing i ≤ (stretch N π).pairing i s :=
          (stretch N π).minPairing_le hs
      _ = N * π.minPairing i := by rw [pairing_stretch, hmin]
  · change _ ≤ (stretch N π).runningMin i 1
    apply (stretch N π).le_runningMin zero_le_one
    intro s hs
    rw [pairing_stretch]
    exact mul_le_mul_of_nonneg_left (π.minPairing_le hs) (Nat.cast_nonneg N)

theorem rightMin_stretch (N : ℕ) (π : LittelmannPath (P.pathSpace hA)) (i : ι) {t : ℝ}
    (ht : t ≤ 1) : (stretch N π).rightMin i t = N * π.rightMin i t := by
  apply le_antisymm
  · obtain ⟨s, hs, hmin⟩ := π.exists_rightMin i ht
    calc (stretch N π).rightMin i t ≤ (stretch N π).pairing i s :=
          (stretch N π).rightMin_le hs
      _ = N * π.rightMin i t := by rw [pairing_stretch, hmin]
  · apply (stretch N π).le_rightMin ht
    intro s hs
    rw [pairing_stretch]
    exact mul_le_mul_of_nonneg_left (π.rightMin_le hs) (Nat.cast_nonneg N)

/-- Stretching by a positive integer is injective. -/
theorem stretch_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (stretch (P := P) (hA := hA) N) := by
  intro π π' h
  refine LittelmannPath.ext fun t => ?_
  have ht := congrArg (fun ρ : LittelmannPath (P.pathSpace hA) => ρ t) h
  simp only [stretch_apply] at ht
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at ht
  exact smul_right_injective _ (by exact_mod_cast hN.ne') ht

/-- [Lit95] Lemma 2.4 a): `N (f_α π) = f_α^N (N π)`, including the case `f_α π = 0`. -/
theorem fIter_stretch {N : ℕ} (hN : 0 < N) (i : ι) (π : LittelmannPath (P.pathSpace hA)) :
    (crystal (P.pathSpace hA)).fIter i N (stretch N π) = (f i π).map (stretch N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  cases hf : f i π with
  | some ζ =>
    have h1 : π.minPairing i + 1 ≤ π.pairing i 1 := by
      have hn := (f_eq_none_iff (i := i) (π := π)).not.mp (by rw [hf]; simp)
      push Not at hn
      linarith
    obtain ⟨η, hη, -, -, hform⟩ := exists_fIter_formula (stretch N π) i N (by
      rw [minPairing_stretch, pairing_stretch]
      nlinarith)
    rw [hη, Option.map_some]
    congr 1
    apply ext_of_eqOn
    intro t ht
    rw [hform t ht, stretch_apply, stretch_apply, f_apply hf ht, rightMin_stretch _ _ _ ht.2,
      minPairing_stretch, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ,
      show (N : ℝ) * π.minPairing i + N = N * (π.minPairing i + 1) by ring,
      ← mul_min_of_nonneg _ _ hNR.le]
    change _ = (N : ℝ) • (π t - _ • P.root i)
    rw [smul_sub, smul_smul, ← mul_sub]
  | none =>
    have h1 : π.pairing i 1 - π.minPairing i < 1 := f_eq_none_iff.mp hf
    rw [Option.map_none, ← Option.not_isSome_iff_eq_none,
      ((isSeminormal_crystal (P.pathSpace hA)) i (stretch N π) N).2, crystal_φ, φ,
      pairing_stretch, minPairing_stretch, ← mul_sub, ← WithBot.coe_natCast,
      WithBot.coe_le_coe, not_le, Int.floor_lt]
    push_cast
    nlinarith

/-- [Lit95] Lemma 2.4 b): `N (e_α π) = e_α^N (N π)`, including the case `e_α π = 0`. -/
theorem eIter_stretch {N : ℕ} (hN : 0 < N) (i : ι) (π : LittelmannPath (P.pathSpace hA)) :
    (crystal (P.pathSpace hA)).eIter i N (stretch N π) = (e i π).map (stretch N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  cases he : e i π with
  | some π' =>
    have hf : f i π' = some π := f_eq_some_iff.mpr he
    have h := fIter_stretch hN i π'
    rw [hf, Option.map_some] at h
    rw [Option.map_some]
    exact (Crystal.fIter_eq_some_iff _ _ _ _).mp h
  | none =>
    have h1 : -1 < π.minPairing i := e_eq_none_iff.mp he
    rw [Option.map_none, ← Option.not_isSome_iff_eq_none,
      ((isSeminormal_crystal (P.pathSpace hA)) i (stretch N π) N).1, crystal_ε, ε,
      minPairing_stretch, ← WithBot.coe_natCast, WithBot.coe_le_coe, not_le, Int.floor_lt]
    push_cast
    nlinarith

/-- The crystal iterate `f̃ᵢⁿ` is the mixed word of `n` lowering letters. -/
theorem fIter_eq_rootWord (i : ι) (n : ℕ) (π : LittelmannPath (P.pathSpace hA)) :
    (crystal (P.pathSpace hA)).fIter i n π = rootWord (List.replicate n (.inr i)) π := by
  induction n generalizing π with
  | zero => rfl
  | succ n ih =>
    change ((crystal (P.pathSpace hA)).f i π).bind ((crystal (P.pathSpace hA)).fIter i n) =
      (rootStep (.inr i) π).bind (rootWord (List.replicate n (.inr i)))
    congr 1
    funext ρ
    exact ih ρ

/-- Every letter repeated `N` times. -/
def stretchWord (N : ℕ) (u : List (ι ⊕ ι)) : List (ι ⊕ ι) :=
  u.flatMap fun a => List.replicate N a

/-- A mixed word on `π` corresponds to its stretched word on `Nπ`. -/
theorem rootWord_stretchWord {N : ℕ} (hN : 0 < N) (u : List (ι ⊕ ι))
    (π : LittelmannPath (P.pathSpace hA)) :
    rootWord (stretchWord N u) (stretch N π) = (rootWord u π).map (stretch N) := by
  induction u generalizing π with
  | nil => rfl
  | cons a u ih =>
    have hs : stretchWord N (a :: u) = List.replicate N a ++ stretchWord N u := by
      simp [stretchWord]
    have hstep : rootWord (List.replicate N a) (stretch N π) =
        (rootStep a π).map (stretch N) := by
      cases a with
      | inl i => rw [← eIter_eq_rootWord, eIter_stretch hN]; rfl
      | inr i => rw [← fIter_eq_rootWord, fIter_stretch hN]; rfl
    rw [hs, rootWord_append_eq_bind, hstep]
    change _ = ((rootStep a π).bind (rootWord u)).map (stretch N)
    cases rootStep a π with
    | none => rfl
    | some ρ => exact ih ρ

/-- A component isomorphism is realized by a map on paths which maps the component
injectively into the other component, preserves `wt` and `ε`, and intertwines every root
operator. -/
theorem ComponentIso.exists_map {π π' : LittelmannPath (P.pathSpace hA)}
    (h : ComponentIso π π') :
    ∃ g : LittelmannPath (P.pathSpace hA) → LittelmannPath (P.pathSpace hA),
      MapsTo g π.component π'.component ∧ InjOn g π.component ∧ g π = π' ∧
      ∀ x ∈ π.component, (g x).wt = x.wt ∧ (∀ i, ε i (g x) = ε i x) ∧
        ∀ a : ι ⊕ ι, rootStep a (g x) = (rootStep a x).map g := by
  classical
  obtain ⟨ψ, hψ⟩ := h
  let g : LittelmannPath (P.pathSpace hA) → LittelmannPath (P.pathSpace hA) := fun x =>
    if hx : x ∈ π.component then (ψ ⟨x, hx⟩).1 else x
  have hg : ∀ (b : π.component), g b.1 = (ψ b).1 := fun b => by simp [g, b.2]
  have hstep : ∀ x ∈ π.component, ∀ a : ι ⊕ ι, rootStep a (g x) = (rootStep a x).map g := by
    intro x hx a
    have hmap : ∀ o : Option π.component, Option.map (fun c => (ψ c).1) o =
        Option.map g (Option.map Subtype.val o) := by
      intro o
      cases o <;> simp [hg]
    cases a with
    | inl i =>
      have h1 := congrArg (Option.map Subtype.val) (ψ.e_map i ⟨x, hx⟩)
      change (π'.componentCrystal.e i (ψ ⟨x, hx⟩)).map Subtype.val = _ at h1
      simp only [componentCrystal, Crystal.restrict_e, Option.map_map] at h1
      change e i (g x) = Option.map g (e i x)
      rw [hg ⟨x, hx⟩]
      refine h1.trans ?_
      rw [show (Subtype.val ∘ ψ.toFun) = (fun c => (ψ c).1) from rfl, hmap, Crystal.restrict_e]
      rfl
    | inr i =>
      have h1 := congrArg (Option.map Subtype.val) (ψ.f_map i ⟨x, hx⟩)
      change (π'.componentCrystal.f i (ψ ⟨x, hx⟩)).map Subtype.val = _ at h1
      simp only [componentCrystal, Crystal.restrict_f, Option.map_map] at h1
      change f i (g x) = Option.map g (f i x)
      rw [hg ⟨x, hx⟩]
      refine h1.trans ?_
      rw [show (Subtype.val ∘ ψ.toFun) = (fun c => (ψ c).1) from rfl, hmap, Crystal.restrict_f]
      rfl
  refine ⟨g, fun x hx => ?_, ?_, (hg ⟨π, π.mem_component_self⟩).trans hψ,
    fun x hx => ⟨?_, fun i => ?_, hstep x hx⟩⟩
  · rw [hg ⟨x, hx⟩]
    exact (ψ ⟨x, hx⟩).2
  · intro x hx y hy hxy
    have := ψ.toEquiv.injective (Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩))))
    exact congrArg Subtype.val this
  · rw [hg ⟨x, hx⟩]
    exact ψ.wt_map ⟨x, hx⟩
  · rw [hg ⟨x, hx⟩]
    exact ψ.ε_map i ⟨x, hx⟩

/-- A component isomorphism is realized by a map on paths, injective on the component,
which intertwines all mixed words. -/
theorem ComponentIso.exists_rootWord_map {π π' : LittelmannPath (P.pathSpace hA)}
    (h : ComponentIso π π') :
    ∃ g : LittelmannPath (P.pathSpace hA) → LittelmannPath (P.pathSpace hA),
      InjOn g π.component ∧ ∀ u, rootWord u π' = (rootWord u π).map g := by
  obtain ⟨g, -, hinj, h0, hx⟩ := ComponentIso.exists_map h
  have hword : ∀ u, ∀ x ∈ π.component, rootWord u (g x) = (rootWord u x).map g := by
    intro u
    induction u with
    | nil => intro x _; rfl
    | cons a u ih =>
      intro x hx'
      change (rootStep a (g x)).bind (rootWord u) = ((rootStep a x).bind (rootWord u)).map g
      rw [(hx x hx').2.2 a]
      cases hr : rootStep a x with
      | none => rfl
      | some y =>
        have hy : y ∈ π.component := rootStep_mem π.isStable_component hx' hr
        exact ih y hy
  refine ⟨g, hinj, fun u => ?_⟩
  rw [← h0]
  exact hword u π π.mem_component_self

/-- A component isomorphism preserves vanishing of every mixed word. -/
theorem ComponentIso.rootWord_eq_none_iff {π π' : LittelmannPath (P.pathSpace hA)}
    (h : ComponentIso π π') (u : List (ι ⊕ ι)) :
    rootWord u π = none ↔ rootWord u π' = none := by
  obtain ⟨g, -, hg⟩ := ComponentIso.exists_rootWord_map h
  rw [hg u, Option.map_eq_none_iff]

/-- A component isomorphism preserves every relation between mixed words. -/
theorem ComponentIso.rootWord_eq_iff {π π' : LittelmannPath (P.pathSpace hA)}
    (h : ComponentIso π π') (u v : List (ι ⊕ ι)) :
    rootWord u π = rootWord v π ↔ rootWord u π' = rootWord v π' := by
  obtain ⟨g, hinj, hg⟩ := ComponentIso.exists_rootWord_map h
  rw [hg u, hg v]
  constructor
  · intro huv
    rw [huv]
  · intro huv
    cases hu : rootWord u π with
    | none =>
      rw [hu, Option.map_none] at huv
      exact (Option.map_eq_none_iff.mp huv.symm).symm
    | some x =>
      cases hv : rootWord v π with
      | none =>
        rw [hv, hu] at huv
        simp at huv
      | some y =>
        rw [hu, hv, Option.map_some, Option.map_some, Option.some_inj] at huv
        have hx : x ∈ π.component := (mem_component_iff_rootWord _ _).mpr ⟨u, hu⟩
        have hy : y ∈ π.component := (mem_component_iff_rootWord _ _).mpr ⟨v, hv⟩
        rw [hinj hx hy huv]

/-- [Lit95] Lemma 2.5 b): an isomorphism `B(Nπ₁) ≅ B(Nπ₂)` with `Nπ₁ ↦ Nπ₂` gives an
isomorphism `B(π₁) ≅ B(π₂)` with `π₁ ↦ π₂`. -/
theorem componentIso_of_componentIso_stretch {N : ℕ} (hN : 0 < N)
    {π₁ π₂ : LittelmannPath (P.pathSpace hA)}
    (h : ComponentIso (stretch N π₁) (stretch N π₂)) : ComponentIso π₁ π₂ := by
  have hinj := stretch_injective (P := P) (hA := hA) hN
  have hmapinj : Function.Injective (Option.map (stretch (P := P) (hA := hA) N)) :=
    Option.map_injective hinj
  refine componentIso_of_rootWord ?_ (fun u => ?_) (fun u v => ?_)
  · obtain ⟨ψ, hψ⟩ := h
    have hw : (stretch N π₂).wt = (stretch N π₁).wt := by
      have h1 := ψ.wt_map ⟨_, (stretch N π₁).mem_component_self⟩
      change (ψ ⟨_, _⟩ : LittelmannPath (P.pathSpace hA)).wt = _ at h1
      rwa [hψ] at h1
    apply Subtype.ext
    have hw1 := congrArg (fun x : P.integralWeights => (x : Dual ℝ H)) hw.symm
    simp only [wt_stretch, AddSubgroup.coe_nsmul] at hw1
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at hw1
    exact smul_right_injective _ (by exact_mod_cast hN.ne') hw1
  · have h1 := ComponentIso.rootWord_eq_none_iff h (stretchWord N u)
    rw [rootWord_stretchWord hN, rootWord_stretchWord hN, Option.map_eq_none_iff,
      Option.map_eq_none_iff] at h1
    exact h1
  · have h1 := ComponentIso.rootWord_eq_iff h (stretchWord N u) (stretchWord N v)
    rw [rootWord_stretchWord hN, rootWord_stretchWord hN, rootWord_stretchWord hN,
      rootWord_stretchWord hN, hmapinj.eq_iff, hmapinj.eq_iff] at h1
    exact h1

end Matrix.Realization.LSGeneralClass
