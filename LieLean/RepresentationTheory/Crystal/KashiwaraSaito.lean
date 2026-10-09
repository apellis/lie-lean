/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Tensor

/-!
# The Kashiwara–Saito characterization of `B(∞)`

Let `B` be a crystal with an element `b₀` such that ([KS97] Prop. 3.2.3)

1. `wt(B) ⊆ Q₋ = {-Σᵢ νᵢ αᵢ | νᵢ ∈ ℕ}`;
2. `b₀` has weight `0` and is the only element of weight `0`;
3. `εᵢ(b₀) = 0` for every `i`;
4. `εᵢ(b) ∈ ℤ` for all `i` and `b`;
5. for every `i` there is a strict embedding `Ψᵢ : B → B ⊗ Bᵢ`;
6. `Ψᵢ(B) ⊆ B × {f̃ᵢⁿ bᵢ | n ≥ 0}`;
7. for `b ≠ b₀` there is `i` with `Ψᵢ(b) = b' ⊗ f̃ᵢⁿ bᵢ`, `n > 0`.

These conditions are bundled as `Crystal.KSData`. If the simple roots are linearly independent,
two crystals with such data are isomorphic by an isomorphism sending `b₀` to `b₀`
(`Crystal.KSData.equiv`, `Crystal.KSData.equiv_b₀`). Applied to `B(∞)`, which satisfies 1–7, this
is [KS97] Prop. 3.2.3.

## Proof

As in [KS97], every `b ≠ b₀` has `ẽᵢ b ≠ 0` for some `i` (`Crystal.KSData.exists_e_ne_none`), so
every element is `f̃_{i₁} ⋯ f̃_{iₗ} b₀` (`Crystal.KSData.exists_fw_eq`); we also show that the
`f̃ᵢ` never vanish (`Crystal.KSData.f_ne_none`). [KS97] then embed `B` into an infinite tensor
product `⋯ ⊗ B_{i₂} ⊗ B_{i₁}`. We argue instead by induction on `l`: for a word `w` of length
`l + 1`, the tensor product rule computes `Ψᵢ(f̃_w b₀) = f̃_u b₀ ⊗ bᵢ(-n)` from the values of the
`εⱼ` on words of length `≤ l`, and for the `i` of condition 7 the word `u` is shorter than `w`.
Hence whether two words give the same element, and the `εⱼ` of the elements they give, are the
same in any two crystals with Kashiwara–Saito data (`Crystal.KSData.fw_eq_fw_of_fw_eq`,
`Crystal.KSData.ε_fw_eq`).

## References

* [KS97] M. Kashiwara, Y. Saito, *Geometric construction of crystal bases*, Duke Math. J. 89
  (1997); arXiv:q-alg/9606009v1, §3.2.
-/

namespace CartanDatum

variable {ι X : Type*} [AddCommGroup X] (D : CartanDatum ι X)

/-- `Σᵢ νᵢ αᵢ` for `ν ∈ ℕ[ι]`. -/
def rootSum (ν : ι →₀ ℕ) : X := ν.sum fun i n ↦ n • D.root i

@[simp] lemma rootSum_zero : D.rootSum 0 = 0 := by simp [rootSum]

lemma rootSum_add (ν ν' : ι →₀ ℕ) : D.rootSum (ν + ν') = D.rootSum ν + D.rootSum ν' :=
  Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ add_smul _ _ _)

@[simp] lemma rootSum_single (i : ι) (n : ℕ) : D.rootSum (Finsupp.single i n) = n • D.root i := by
  simp [rootSum]

/-- If the simple roots are linearly independent, `ν ↦ Σᵢ νᵢ αᵢ` is injective on `ℕ[ι]`. -/
theorem rootSum_injective (hD : LinearIndependent ℤ D.root) : Function.Injective D.rootSum := by
  intro ν ν' he
  have key : ∀ ν : ι →₀ ℕ, Finsupp.linearCombination ℤ D.root
      (ν.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp)) = D.rootSum ν := fun ν ↦ by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
    simp only [rootSum, natCast_zsmul]
  have h2 := linearIndependent_iff.1 hD (ν.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp) -
    ν'.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp)) (by rw [map_sub, key, key, he, sub_self])
  ext i
  simpa [sub_eq_zero] using congr($h2 i)

end CartanDatum

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] [DecidableEq ι] {D : CartanDatum ι X} {B B' : Type*}

lemma tensor_elementary_e (C : Crystal D B) (i j : ι) (b : B) (n : ℤ) :
    (C.tensor (elementary D i)).e j (b, n) =
      if (elementary D i).ε j n ≤ C.φ j b then (C.e j b).map (·, n)
      else ((elementary D i).e j n).map (b, ·) := rfl

lemma tensor_elementary_f (C : Crystal D B) (i j : ι) (b : B) (n : ℤ) :
    (C.tensor (elementary D i)).f j (b, n) =
      if (elementary D i).ε j n < C.φ j b then (C.f j b).map (·, n)
      else ((elementary D i).f j n).map (b, ·) := rfl

lemma tensor_elementary_ε (C : Crystal D B) (i j : ι) (b : B) (n : ℤ) :
    (C.tensor (elementary D i)).ε j (b, n) =
      max (C.ε j b) ((elementary D i).ε j n + ((-D.coroot j (C.wt b) : ℤ) : WithBot ℤ)) := rfl

lemma tensor_elementary_wt (C : Crystal D B) (i : ι) (b : B) (n : ℤ) :
    (C.tensor (elementary D i)).wt (b, n) = C.wt b + n • D.root i := rfl

lemma elementary_ε_self (i : ι) (n : ℤ) : (elementary D i).ε i n = ((-n : ℤ) : WithBot ℤ) := by
  simp [elementary]

lemma elementary_ε_of_ne {i j : ι} (h : j ≠ i) (n : ℤ) : (elementary D i).ε j n = ⊥ := by
  simp [elementary, h]

lemma elementary_e_self (i : ι) (n : ℤ) : (elementary D i).e i n = some (n + 1) := by
  simp [elementary]

lemma elementary_f_self (i : ι) (n : ℤ) : (elementary D i).f i n = some (n - 1) := by
  simp [elementary]

/-- The data of [KS97] Prop. 3.2.3 on a crystal `C` with an element `b₀`: conditions (1)–(4), and
strict embeddings `Ψᵢ : B → B ⊗ Bᵢ` satisfying (6) and (7). -/
structure KSData (C : Crystal D B) (b₀ : B) where
  /-- The strict embeddings `Ψᵢ : B → B ⊗ Bᵢ` (condition (5)). -/
  Ψ : ∀ i, C.StrictHom (C.tensor (elementary D i))
  Ψ_injective : ∀ i, Function.Injective (Ψ i)
  /-- Condition (1): `wt(B) ⊆ Q₋`. -/
  wt_mem : ∀ b, ∃ ν : ι →₀ ℕ, C.wt b = -D.rootSum ν
  wt_b₀ : C.wt b₀ = 0
  /-- Condition (2): `b₀` is the only element of weight `0`. -/
  eq_b₀ : ∀ b, C.wt b = 0 → b = b₀
  /-- Condition (3). -/
  ε_b₀ : ∀ i, C.ε i b₀ = 0
  /-- Condition (4). -/
  ε_ne_bot : ∀ i b, C.ε i b ≠ ⊥
  /-- Condition (6): `Ψᵢ(b) ∈ B ⊗ {bᵢ(-n) | n ≥ 0}`. -/
  Ψ_snd_nonpos : ∀ i b, (Ψ i b).2 ≤ 0
  /-- Condition (7). -/
  exists_Ψ_snd_neg : ∀ b, b ≠ b₀ → ∃ i, (Ψ i b).2 < 0

namespace KSData

variable {C : Crystal D B} {b₀ : B} (K : KSData C b₀) (hD : LinearIndependent ℤ D.root)

/-! ### Heights -/

/-- The height `Σᵢ νᵢ` of `-wt b = Σᵢ νᵢ αᵢ`. -/
noncomputable def ht (b : B) : ℕ := (K.wt_mem b).choose.degree

include K hD

lemma ht_eq {b : B} {ν : ι →₀ ℕ} (h : C.wt b = -D.rootSum ν) : K.ht b = ν.degree := by
  have := (K.wt_mem b).choose_spec
  rw [ht, D.rootSum_injective hD (neg_injective (this.symm.trans h))]

lemma ht_b₀ : K.ht b₀ = 0 := by
  rw [K.ht_eq hD (ν := 0) (by rw [K.wt_b₀, D.rootSum_zero, neg_zero])]
  simp

omit hD in
lemma eq_b₀_of_ht {b : B} (h : K.ht b = 0) : b = b₀ := by
  apply K.eq_b₀
  have hs := (K.wt_mem b).choose_spec
  rw [ht, Finsupp.degree_eq_zero_iff] at h
  rw [hs, h, D.rootSum_zero, neg_zero]

/-- `ht b = ht b' + 1` if `wt b = wt b' - αⱼ`. -/
lemma ht_of_wt_sub {b b' : B} {j : ι} (h : C.wt b = C.wt b' - D.root j) :
    K.ht b = K.ht b' + 1 := by
  obtain ⟨ν, hν⟩ := K.wt_mem b'
  rw [K.ht_eq hD hν, K.ht_eq hD (ν := ν + Finsupp.single j 1)]
  · simp
  · rw [h, hν, D.rootSum_add, D.rootSum_single, one_smul]; abel

/-- `Ψᵢ(b) = b' ⊗ bᵢ(-n)` gives `ht b = ht b' + n`. -/
lemma ht_Ψ (i : ι) (b : B) : K.ht b = K.ht (K.Ψ i b).1 + (-(K.Ψ i b).2).toNat := by
  have hwt := (K.Ψ i).wt_apply b
  rcases hp : K.Ψ i b with ⟨c, n⟩
  rw [hp, tensor_elementary_wt] at hwt
  have hn : n ≤ 0 := by have := K.Ψ_snd_nonpos i b; rw [hp] at this; exact this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -m := ⟨(-n).toNat, by omega⟩
  obtain ⟨ν, hν⟩ := K.wt_mem c
  rw [K.ht_eq hD hν, K.ht_eq hD (ν := ν + Finsupp.single i m)]
  · simp
  · rw [← hwt, hν, D.rootSum_add, D.rootSum_single, neg_smul, natCast_zsmul]; abel

lemma Ψ_b₀ (i : ι) : K.Ψ i b₀ = (b₀, 0) := by
  have h := K.ht_Ψ hD i b₀
  rw [K.ht_b₀ hD] at h
  have h2 := K.Ψ_snd_nonpos i b₀
  exact Prod.ext (K.eq_b₀_of_ht (by omega)) (by simp only; omega)

omit hD in
lemma φ_b₀ (i : ι) : C.φ i b₀ = 0 := by
  rw [C.φ_eq, K.ε_b₀, K.wt_b₀, map_zero]; rfl

omit hD in
lemma φ_ne_bot (i : ι) (b : B) : C.φ i b ≠ ⊥ := by
  rw [Ne, C.φ_eq_bot_iff]; exact K.ε_ne_bot i b

/-! ### Generation by the `f̃ᵢ` -/

/-- Every `b ≠ b₀` has `ẽⱼ b ≠ 0` for some `j` ([KS97], proof of Prop. 3.2.3). -/
theorem exists_e_ne_none (b : B) (hb : b ≠ b₀) : ∃ j, C.e j b ≠ none := by
  induction h : K.ht b using Nat.strong_induction_on generalizing b with
  | _ L ih =>
  obtain ⟨i, hi⟩ := K.exists_Ψ_snd_neg b hb
  have key : ∀ j, (C.tensor (elementary D i)).e j (K.Ψ i b) ≠ none → C.e j b ≠ none := by
    intro j hj he
    rw [(K.Ψ i).e_apply, he] at hj
    exact hj rfl
  have hht := K.ht_Ψ hD i b
  rcases hp : K.Ψ i b with ⟨c, n⟩
  rw [hp] at hi hht key
  simp only at hi hht
  by_cases hc : c = b₀
  · subst hc
    refine ⟨i, key i ?_⟩
    rw [tensor_elementary_e, K.φ_b₀, elementary_ε_self, ite_eq_right]
    · simp [elementary_e_self]
    · rw [← WithBot.coe_zero, WithBot.coe_le_coe]; omega
  · obtain ⟨j, hj⟩ := ih (K.ht c) (by omega) c hc rfl
    refine ⟨j, key j ?_⟩
    rw [tensor_elementary_e]
    split_ifs with hle
    · simpa using hj
    · by_cases hji : j = i
      · subst hji; simp [elementary_e_self]
      · rw [elementary_ε_of_ne hji] at hle
        exact absurd bot_le hle

/-- The `f̃ⱼ` never vanish. -/
theorem f_ne_none (j : ι) (b : B) : C.f j b ≠ none := by
  induction h : K.ht b using Nat.strong_induction_on generalizing b with
  | _ L ih =>
  by_cases hb : b = b₀
  · subst hb
    intro hf
    have := (K.Ψ j).f_apply j b
    rw [hf, K.Ψ_b₀ hD, tensor_elementary_f, K.φ_b₀, elementary_ε_self, ite_eq_right (by simp),
      elementary_f_self] at this
    simp at this
  obtain ⟨i, hi⟩ := K.exists_Ψ_snd_neg b hb
  have hht := K.ht_Ψ hD i b
  intro hf
  have hfi := (K.Ψ i).f_apply j b
  rw [hf] at hfi
  rcases hp : K.Ψ i b with ⟨c, n⟩
  rw [hp] at hi hht hfi
  simp only at hi hht
  have hc := ih (K.ht c) (by omega) c rfl
  rw [tensor_elementary_f] at hfi
  split_ifs at hfi with hlt
  · simp [Option.map_eq_none_iff, hc] at hfi
  · by_cases hji : j = i
    · subst hji; simp [elementary_f_self] at hfi
    · rw [elementary_ε_of_ne hji] at hlt
      exact hlt (bot_lt_iff_ne_bot.2 (K.φ_ne_bot j c))

/-- `f̃ⱼ b`, as an element of `B`. -/
noncomputable def fT (j : ι) (b : B) : B :=
  (C.f j b).get (Option.isSome_iff_ne_none.2 (K.f_ne_none hD j b))

lemma f_eq_fT (j : ι) (b : B) : C.f j b = some (K.fT hD j b) := (Option.some_get _).symm

/-- `f̃_w b₀ = f̃_{i₁} ⋯ f̃_{iₗ} b₀` for `w = [i₁, …, iₗ]`. -/
noncomputable def fw : List ι → B
  | [] => b₀
  | j :: w => K.fT hD j (fw w)

@[simp] lemma fw_nil : K.fw hD [] = b₀ := rfl

lemma f_fw (j : ι) (w : List ι) : C.f j (K.fw hD w) = some (K.fw hD (j :: w)) :=
  K.f_eq_fT hD j _

lemma wt_fw (w : List ι) : C.wt (K.fw hD w) = -(w.map D.root).sum := by
  induction w with
  | nil => simp [K.wt_b₀]
  | cons j w ih =>
    rw [C.wt_f (K.f_fw hD j w), ih, List.map_cons, List.sum_cons]; abel

lemma ht_fw (w : List ι) : K.ht (K.fw hD w) = w.length := by
  induction w with
  | nil => exact K.ht_b₀ hD
  | cons j w ih =>
    rw [K.ht_of_wt_sub hD (C.wt_f (K.f_fw hD j w)), ih, List.length_cons]

/-- Every element is `f̃_w b₀` for some word `w` ([KS97], proof of Prop. 3.2.3). -/
theorem exists_fw_eq (b : B) : ∃ w, K.fw hD w = b := by
  induction h : K.ht b using Nat.strong_induction_on generalizing b with
  | _ L ih =>
  by_cases hb : b = b₀
  · exact ⟨[], hb.symm⟩
  obtain ⟨j, hj⟩ := K.exists_e_ne_none hD b hb
  obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 hj
  have hht := K.ht_of_wt_sub hD (b := b) (b' := b') (j := j)
    (by rw [C.wt_e j b b' hb', add_sub_cancel_right])
  obtain ⟨w, rfl⟩ := ih (K.ht b') (by omega) b' rfl
  refine ⟨j :: w, ?_⟩
  have := K.f_fw hD j w
  rw [(C.f_eq_some_iff j _ b).2 hb', Option.some_inj] at this
  exact this.symm

/-! ### Comparison of two crystals with Kashiwara–Saito data -/

variable {C' : Crystal D B'} {b₀' : B'} (K' : KSData C' b₀')

/-- `Ψᵢ` on `f̃_w b₀` and `f̃_w b₀'` is computed in the same way, as long as the `εⱼ` agree on
shorter words. -/
theorem exists_Ψ_fw (L : ℕ)
    (hE : ∀ w : List ι, w.length ≤ L → ∀ k, C.ε k (K.fw hD w) = C'.ε k (K'.fw hD w))
    (i : ι) (w : List ι) (hw : w.length ≤ L + 1) :
    ∃ (u : List ι) (n : ℤ), K.Ψ i (K.fw hD w) = (K.fw hD u, n) ∧
      K'.Ψ i (K'.fw hD w) = (K'.fw hD u, n) := by
  induction w with
  | nil => exact ⟨[], 0, K.Ψ_b₀ hD i, K'.Ψ_b₀ hD i⟩
  | cons j w ih =>
    rw [List.length_cons] at hw
    obtain ⟨u, n, h1, h1'⟩ := ih (by omega)
    have hlen : u.length ≤ L := by
      have := K.ht_Ψ hD i (K.fw hD w)
      rw [h1, K.ht_fw, K.ht_fw] at this
      simp only at this
      omega
    have hf := (K.Ψ i).f_apply j (K.fw hD w)
    have hf' := (K'.Ψ i).f_apply j (K'.fw hD w)
    rw [h1, K.f_fw, Option.map_some, tensor_elementary_f] at hf
    rw [h1', K'.f_fw, Option.map_some, tensor_elementary_f] at hf'
    have hφ : C.φ j (K.fw hD u) = C'.φ j (K'.fw hD u) := by
      rw [C.φ_eq, C'.φ_eq, hE u hlen j, K.wt_fw, K'.wt_fw]
    rw [← hφ] at hf'
    split_ifs at hf hf' with hc
    · rw [K.f_fw, Option.map_some, Option.some_inj] at hf
      rw [K'.f_fw, Option.map_some, Option.some_inj] at hf'
      exact ⟨j :: u, n, hf.symm, hf'.symm⟩
    · obtain ⟨n', hn', hΨ⟩ := Option.map_eq_some_iff.1 hf
      rw [hn', Option.map_some, Option.some_inj] at hf'
      exact ⟨u, n', hΨ.symm, hf'.symm⟩

lemma fw_ne_b₀ {w : List ι} (hw : w ≠ []) : K.fw hD w ≠ b₀ := fun h ↦ by
  have := congrArg K.ht h
  rw [K.ht_fw, K.ht_b₀ hD] at this
  exact hw (List.eq_nil_of_length_eq_zero this)

/-- The step of the induction for equalities of words. -/
theorem fw_eq_fw_step (L : ℕ)
    (hE : ∀ w : List ι, w.length ≤ L → ∀ k, C.ε k (K.fw hD w) = C'.ε k (K'.fw hD w))
    (hS : ∀ w w' : List ι, w.length ≤ L → w'.length ≤ L → K.fw hD w = K.fw hD w' →
      K'.fw hD w = K'.fw hD w')
    (w w' : List ι) (hw : w.length ≤ L + 1) (hw' : w'.length ≤ L + 1)
    (heq : K.fw hD w = K.fw hD w') : K'.fw hD w = K'.fw hD w' := by
  have hlen : w.length = w'.length := by
    have := congrArg K.ht heq
    rwa [K.ht_fw, K.ht_fw] at this
  by_cases hL : w.length ≤ L
  · exact hS w w' hL (hlen ▸ hL) heq
  have hne : K.fw hD w ≠ b₀ := K.fw_ne_b₀ hD (fun h ↦ by simp [h] at hL)
  obtain ⟨i, hi⟩ := K.exists_Ψ_snd_neg _ hne
  obtain ⟨u, n, h1, h1'⟩ := K.exists_Ψ_fw hD K' L hE i w hw
  obtain ⟨u', n', h2, h2'⟩ := K.exists_Ψ_fw hD K' L hE i w' hw'
  have hn : n < 0 := by rw [h1] at hi; exact hi
  have h12 : (K.fw hD u, n) = (K.fw hD u', n') := by rw [← h1, ← h2, heq]
  obtain ⟨hfu, rfl⟩ := Prod.mk.inj h12
  have hu : u.length ≤ L := by
    have := K.ht_Ψ hD i (K.fw hD w)
    rw [h1, K.ht_fw, K.ht_fw] at this
    simp only at this
    omega
  have hu' : u'.length ≤ L := by
    have := K.ht_Ψ hD i (K.fw hD w')
    rw [h2, K.ht_fw, K.ht_fw] at this
    simp only at this
    omega
  have hfu' := hS u u' hu hu' hfu
  apply K'.Ψ_injective i
  rw [h1', h2', hfu']

/-- The step of the induction for the `εₖ`. -/
theorem ε_fw_step (L : ℕ)
    (hE : ∀ w : List ι, w.length ≤ L → ∀ k, C.ε k (K.fw hD w) = C'.ε k (K'.fw hD w))
    (w : List ι) (hw : w.length ≤ L + 1) (k : ι) :
    C.ε k (K.fw hD w) = C'.ε k (K'.fw hD w) := by
  by_cases hL : w.length ≤ L
  · exact hE w hL k
  have hne : K.fw hD w ≠ b₀ := K.fw_ne_b₀ hD (fun h ↦ by simp [h] at hL)
  obtain ⟨i, hi⟩ := K.exists_Ψ_snd_neg _ hne
  obtain ⟨u, n, h1, h1'⟩ := K.exists_Ψ_fw hD K' L hE i w hw
  have hu : u.length ≤ L := by
    have := K.ht_Ψ hD i (K.fw hD w)
    rw [h1, K.ht_fw, K.ht_fw] at this
    rw [h1] at hi
    simp only at this hi
    omega
  rw [← (K.Ψ i).ε_apply, ← (K'.Ψ i).ε_apply, h1, h1', tensor_elementary_ε, tensor_elementary_ε,
    hE u hu k, K.wt_fw, K'.wt_fw]

theorem fw_eq_fw_and_ε (L : ℕ) :
    (∀ w : List ι, w.length ≤ L → ∀ k, C.ε k (K.fw hD w) = C'.ε k (K'.fw hD w)) ∧
    (∀ w w' : List ι, w.length ≤ L → w'.length ≤ L → K.fw hD w = K.fw hD w' →
      K'.fw hD w = K'.fw hD w') ∧
    (∀ w w' : List ι, w.length ≤ L → w'.length ≤ L → K'.fw hD w = K'.fw hD w' →
      K.fw hD w = K.fw hD w') := by
  induction L with
  | zero =>
    refine ⟨fun w hw k ↦ ?_, fun w w' hw hw' _ ↦ ?_, fun w w' hw hw' _ ↦ ?_⟩
    · rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw), fw_nil, fw_nil, K.ε_b₀, K'.ε_b₀]
    all_goals rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw),
      List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw')]
  | succ L ih =>
    obtain ⟨hE, hS, hS'⟩ := ih
    exact ⟨K.ε_fw_step hD K' L hE, K.fw_eq_fw_step hD K' L hE hS,
      K'.fw_eq_fw_step hD K L (fun w hw k ↦ (hE w hw k).symm) hS'⟩

theorem ε_fw_eq (w : List ι) (k : ι) : C.ε k (K.fw hD w) = C'.ε k (K'.fw hD w) :=
  (K.fw_eq_fw_and_ε hD K' w.length).1 w le_rfl k

theorem fw_eq_fw_of_fw_eq {w w' : List ι} (h : K.fw hD w = K.fw hD w') :
    K'.fw hD w = K'.fw hD w' :=
  (K.fw_eq_fw_and_ε hD K' (max w.length w'.length)).2.1 w w' (le_max_left _ _)
    (le_max_right _ _) h

/-- A word for `b`. -/
noncomputable def word (b : B) : List ι := (K.exists_fw_eq hD b).choose

lemma fw_word (b : B) : K.fw hD (K.word hD b) = b := (K.exists_fw_eq hD b).choose_spec

/-- The map `f̃_w b₀ ↦ f̃_w b₀'`. -/
noncomputable def toFun' (b : B) : B' := K'.fw hD (K.word hD b)

lemma toFun'_fw (w : List ι) : K.toFun' hD K' (K.fw hD w) = K'.fw hD w :=
  K.fw_eq_fw_of_fw_eq hD K' (K.fw_word hD _)

/-- **The Kashiwara–Saito characterization** ([KS97] Prop. 3.2.3): two crystals with
Kashiwara–Saito data are isomorphic, by `f̃_w b₀ ↦ f̃_w b₀'`. -/
noncomputable def equiv : Crystal.Equiv C C' where
  toFun := K.toFun' hD K'
  invFun := K'.toFun' hD K
  left_inv b := by
    change K'.toFun' hD K (K'.fw hD (K.word hD b)) = b
    rw [K'.toFun'_fw, K.fw_word]
  right_inv c := by
    change K.toFun' hD K' (K.fw hD (K'.word hD c)) = c
    rw [K.toFun'_fw, K'.fw_word]
  wt_map b := by
    conv_rhs => rw [← K.fw_word hD b]
    rw [toFun', K'.wt_fw, K.wt_fw]
  ε_map i b := by
    conv_rhs => rw [← K.fw_word hD b]
    exact (K.ε_fw_eq hD K' _ i).symm
  e_map i b := by
    obtain ⟨w, rfl⟩ := K.exists_fw_eq hD b
    rw [K.toFun'_fw]
    cases he : C.e i (K.fw hD w) with
    | some b'' =>
      obtain ⟨u, rfl⟩ := K.exists_fw_eq hD b''
      have h1 := K.f_fw hD i u
      rw [(C.f_eq_some_iff i _ _).2 he, Option.some_inj] at h1
      rw [Option.map_some, K.toFun'_fw, K.fw_eq_fw_of_fw_eq hD K' h1, C'.e_eq_some_iff,
        K'.f_fw]
    | none =>
      rw [Option.map_none, Option.eq_none_iff_forall_ne_some]
      intro c hc
      obtain ⟨u, rfl⟩ := K'.exists_fw_eq hD c
      have h1 := K'.f_fw hD i u
      rw [(C'.f_eq_some_iff i _ _).2 hc, Option.some_inj] at h1
      have h2 := K'.fw_eq_fw_of_fw_eq hD K h1
      have h3 := K.f_fw hD i u
      rw [← h2, ← C.e_eq_some_iff, he] at h3
      exact absurd h3 (by simp)
  f_map i b := by
    obtain ⟨w, rfl⟩ := K.exists_fw_eq hD b
    rw [K.toFun'_fw, K.f_fw, K'.f_fw, Option.map_some, K.toFun'_fw]

lemma equiv_b₀ : K.equiv hD K' b₀ = b₀' := K.toFun'_fw hD K' []

end KSData

end Crystal
