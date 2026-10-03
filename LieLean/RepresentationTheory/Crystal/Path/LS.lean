/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Character

/-!
# Lakshmibai–Seshadri paths and the structure of `B(λ)`

Littelmann ([Lit94], [Lit95]) showed that the connected component `B(λ)` of the straight line
path `π_λ` (for `λ` dominant integral) is the set of *Lakshmibai–Seshadri paths* of shape `λ`,
that it is the set of paths `f_{i₁} ⋯ f_{iₖ} π_λ`, and that `π_λ` is its only highest weight
element. This file proves these statements in an axiomatic setting (`LittelmannPath.LSData`):
the Bruhat order on `W/W_λ` enters only through a handful of properties, which are verified for
realizations of generalized Cartan matrices in
`LieLean.RepresentationTheory.Crystal.Path.Stability`.

## The argument

We work with parametrized paths. An LS path (`LittelmannPath.IsLS`) is locally linear on both
sides of every time `t`, with directions in the orbit `O = Wλ`, and at every `t ∈ (0,1)` the left
direction `x` and the right direction `y` are joined by a chain of Bruhat covering steps
`x = κ₀ → κ₁ → ⋯ → κₛ = y`, `κₗ = s_{βₗ} κₗ₋₁`, with `⟨η(t), βₗ^∨⟩ ∈ ℤ`
(`LittelmannPath.LSData.Chain`). This is Littelmann's `a`-chain condition, written in terms of
the position `η(t)` rather than the time `a` (the two agree because `η(a) ≡ a κ λ` modulo the root
lattice for LS paths in Littelmann's normalization).

1. *Deodhar's lemma* (axioms `step_neg_pos`, `coroot_nonpos_of_step`, `coroot_ne_zero_of_step`):
   along a covering step `x → y` the sign of `⟨·, αᵢ^∨⟩` can only increase from `< 0` to `> 0`,
   and then `y = sᵢ x` with coroot `±αᵢ^∨`. Hence a chain along which the sign goes from `≤ 0` to
   `> 0` (or `< 0` to `≥ 0`) forces `⟨η(t), αᵢ^∨⟩ ∈ ℤ` (`LittelmannPath.LSData.Chain.exists_int`):
   *local minima of `hᵢ = ⟨η, αᵢ^∨⟩` are integers* (`LittelmannPath.IsLS.exists_int_of_isMin`),
   in particular `mᵢ = min hᵢ ∈ ℤ`.
2. If `fᵢ η ≠ 0`, let `p` be the last time with `hᵢ(p) = mᵢ` and `q` the first later time with
   `hᵢ(q) = mᵢ + 1`. By 1, `hᵢ` is strictly increasing on `[p, q]` and `≥ mᵢ + 1` after `q`
   (`LittelmannPath.IsLS.exists_f_times`), so by the closed formula for `fᵢ`, `fᵢ η` is `η` on
   `[0, p]`, `sᵢ η + mᵢ αᵢ` on `[p, q]` and `η - αᵢ` on `[q, 1]`.
3. The new chains: at `p` the old chain goes from sign `≤ 0` to `> 0` and is modified after its
   last `sᵢ`-step (`LittelmannPath.LSData.Chain.reflection`); inside `(p, q)`, `hᵢ ∉ ℤ`, so by 1
   the old chains stay in the region `⟨·, αᵢ^∨⟩ > 0` and are reflected step by step
   (`LittelmannPath.LSData.Chain.reflection_of_not_int`, axiom `step_reflection_pos`); at `q` the
   step `sᵢ x → x` is prepended (axiom `step_simple`). So `fᵢ` preserves LS paths
   (`LittelmannPath.IsLS.f`); by time reversal, which exchanges the data with its dual
   (`LittelmannPath.LSData.dual`, `LittelmannPath.IsLS.rev`), so does `eᵢ`
   (`LittelmannPath.IsLS.e`).
4. An LS path with all `eᵢ η = 0` has `mᵢ ∈ ℤ ∩ (-1, 0]`, i.e. lies in the dominant chamber; its
   initial direction is then dominant, hence `λ`, and since no step starts at `λ` (`λ` is the
   minimum of the Bruhat order) all directions are `λ`: `η = π_λ`
   (`LittelmannPath.IsLS.eq_straightLine`).
5. With a linear form `g` with `g(αᵢ) = 1` and `g ≤ g(λ)` on `O`, `g(λ) - g(wt η)` is a
   nonnegative integer on `B(π_λ)`; induction on it gives `B(π_λ) = {f_{i₁} ⋯ f_{iₖ} π_λ}`
   (`LittelmannPath.component_straightLine_eq_fOrbit`).

Steps 1–3 follow the strategy of [Lit94] §4; the formulation with positions, the handling of
continuous parametrized paths and the proofs are our reconstruction.

## Main definitions

* `LittelmannPath.LSData S`: the Bruhat-order data (orbit `O`, covering steps `Step x y β^∨`).
* `LittelmannPath.LSData.Chain`: chains of steps with integrality at a position.
* `LittelmannPath.LSData.dual`: the data for time-reversed paths.
* `LittelmannPath.HasRightDir`, `LittelmannPath.HasLeftDir`: one-sided directions of a path.
* `LittelmannPath.IsLS L η`: `η` is a Lakshmibai–Seshadri path for `L`.

## Main results

* `LittelmannPath.IsLS.exists_int_minPairing`: the minima `mᵢ` of LS paths are integers.
* `LittelmannPath.IsLS.f`, `LittelmannPath.IsLS.e`: the root operators preserve LS paths.
* `LittelmannPath.IsLS.eq_straightLine`: `π_λ` is the only dominant LS path.
* `LittelmannPath.component_straightLine_eq_fOrbit`: `B(π_λ) = {f_{i₁} ⋯ f_{iₖ} π_λ}`, and it
  consists of LS paths.

## References

* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* V. Lakshmibai, C. S. Seshadri, *Standard monomial theory*, in Proc. Hyderabad Conf. on Algebraic
  Groups (1991), 279–322.
-/

open Set Pointwise

namespace CartanDatum.PathSpace

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] {D : CartanDatum ι X} {V : Type*}
  [AddCommGroup V] [Module 𝕜 V] (S : D.PathSpace 𝕜 V)

/-- The simple reflection `sᵢ v = v - ⟨v, αᵢ^∨⟩ αᵢ` of the space `V` of a path space. -/
noncomputable def reflection (i : ι) : V ≃ₗ[𝕜] V := Module.reflection (S.coroot_root_self i)

lemma reflection_apply (i : ι) (v : V) : S.reflection i v = v - S.coroot i v • S.root i := rfl

@[simp] lemma reflection_reflection (i : ι) (v : V) : S.reflection i (S.reflection i v) = v :=
  Module.involutive_reflection (S.coroot_root_self i) v

lemma coroot_reflection (i : ι) (v : V) : S.coroot i (S.reflection i v) = -S.coroot i v := by
  rw [reflection_apply, map_sub, map_smul, coroot_root_self, smul_eq_mul]
  ring

lemma embed_reflection (i : ι) (x : X) :
    S.embed (D.reflection i x) = S.reflection i (S.embed x) := by
  rw [reflection_apply, D.reflection_apply, map_sub, map_zsmul, S.coroot_embed, root,
    Int.cast_smul_eq_zsmul]

end CartanDatum.PathSpace

namespace LittelmannPath

section LSData

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] {D : CartanDatum ι X} {V : Type*}
  [AddCommGroup V] [Module 𝕜 V]

variable (S : D.PathSpace 𝕜 V) in
/-- The combinatorial data behind Lakshmibai–Seshadri paths, axiomatized. For a dominant weight
`λ`, `O` is the orbit `Wλ` and `Step x y c` means that `y = s_β x` is covered by `x` in the Bruhat
order of `W/W_λ` (so `y` is closer to `λ`), where `β` is a real root with coroot `c = β^∨`
(seen as a linear form on `V`). The axioms are the properties of the Bruhat order used in the
proof that the root operators preserve Lakshmibai–Seshadri paths (`[Lit94] §4`, `[Lit95] §4`);
they are verified for realizations in `LieLean.RepresentationTheory.Crystal.Path.
Stability`. Signs refer to `⟨x, αᵢ^∨⟩`: e.g. `0 < ⟨x, αᵢ^∨⟩` means `sᵢ x > x`. -/
structure LSData where
  /-- The set of possible directions (the orbit `Wλ`). -/
  O : Set X
  /-- `Step x y c`: `x` covers `y = s_β x` in the Bruhat order, with `c = β^∨`. -/
  Step : X → X → Module.Dual 𝕜 V → Prop
  reflection_mem : ∀ i x, x ∈ O → D.reflection i x ∈ O
  step_mem : ∀ x y c, Step x y c → x ∈ O ∧ y ∈ O
  exists_int : ∀ x y c, Step x y c → ∀ μ : X, ∃ n : ℤ, c (S.embed μ) = n
  step_reflection_pos : ∀ i x y c, Step x y c → 0 < D.coroot i x → 0 < D.coroot i y →
    Step (D.reflection i x) (D.reflection i y) (c ∘ₗ (S.reflection i : V →ₗ[𝕜] V))
  step_reflection_neg : ∀ i x y c, Step x y c → D.coroot i x < 0 → D.coroot i y < 0 →
    Step (D.reflection i x) (D.reflection i y) (c ∘ₗ (S.reflection i : V →ₗ[𝕜] V))
  step_simple : ∀ i x, x ∈ O → 0 < D.coroot i x → Step (D.reflection i x) x (S.coroot i)
  step_neg_pos : ∀ i x y c, Step x y c → D.coroot i x < 0 → 0 < D.coroot i y →
    y = D.reflection i x ∧ (c = S.coroot i ∨ c = -S.coroot i)
  coroot_nonpos_of_step : ∀ i x y c, Step x y c → D.coroot i x = 0 → D.coroot i y ≤ 0
  coroot_ne_zero_of_step : ∀ i x y c, Step x y c → D.coroot i x < 0 → D.coroot i y ≠ 0

variable {S : D.PathSpace 𝕜 V} (L : LSData S)

namespace LSData

/-- `L.Chain p x y`: there is a chain of steps `x = κ₀ → κ₁ → ⋯ → κₛ = y` whose coroots `β^∨`
all satisfy `⟨p, β^∨⟩ ∈ ℤ` (Littelmann's `a`-chains, stated in terms of the position `p` of the
path at the break point). -/
def Chain (p : V) : X → X → Prop :=
  Relation.ReflTransGen fun x y ↦ ∃ c, L.Step x y c ∧ ∃ n : ℤ, c p = n

variable {L} {i : ι} {p p' : V} {x y : X}

lemma exists_int_coroot_reflection {c : Module.Dual 𝕜 V} (hc : ∃ x y, L.Step x y c)
    (hcp : ∃ n : ℤ, c p = n) (hp : ∃ n : ℤ, S.coroot i p = n) :
    ∃ n : ℤ, (c ∘ₗ (S.reflection i : V →ₗ[𝕜] V)) p = n := by
  obtain ⟨x, y, hxy⟩ := hc
  obtain ⟨a, ha⟩ := hcp
  obtain ⟨b, hb⟩ := hp
  obtain ⟨k, hk⟩ := L.exists_int x y c hxy (D.root i)
  refine ⟨a - b * k, ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, S.reflection_apply, map_sub, map_smul,
    ha, hb, smul_eq_mul]
  rw [CartanDatum.PathSpace.root, hk]
  push_cast
  ring

lemma Chain.mono (h : L.Chain p x y)
    (hp : ∀ c x y, L.Step x y c → (∃ n : ℤ, c p = n) → ∃ n : ℤ, c p' = n) : L.Chain p' x y := by
  induction h with
  | refl => exact .refl
  | tail _ hyz ih =>
    obtain ⟨c, hc, hn⟩ := hyz
    exact ih.tail ⟨c, hc, hp c _ _ hc hn⟩

/-- Translating the position by an element of `X` preserves chains. -/
lemma Chain.add_embed (h : L.Chain p x y) (μ : X) : L.Chain (p + S.embed μ) x y :=
  h.mono fun c a b hc ⟨n, hn⟩ ↦ by
    obtain ⟨k, hk⟩ := L.exists_int a b c hc μ
    exact ⟨n + k, by rw [map_add, hn, hk]; push_cast; ring⟩

lemma Chain.sub_embed (h : L.Chain p x y) (μ : X) : L.Chain (p - S.embed μ) x y := by
  simpa [sub_eq_add_neg] using h.add_embed (-μ)

/-- The elements of a chain starting in `O` lie in `O`. -/
lemma Chain.mem (h : L.Chain p x y) (hx : x ∈ L.O) : y ∈ L.O := by
  induction h with
  | refl => exact hx
  | tail _ hyz ih =>
    obtain ⟨c, hc, -⟩ := hyz
    exact (L.step_mem _ _ _ hc).2

/-- A chain along which `⟨·, αᵢ^∨⟩` goes from `≤ 0` to `> 0`, or from `< 0` to `≥ 0`, contains a
step by `sᵢ`; hence `⟨p, αᵢ^∨⟩` is an integer. This is the path-model form of Deodhar's lemma used
by Littelmann to show that local minima of `hᵢ` on Lakshmibai–Seshadri paths are integers. -/
theorem Chain.exists_int (h : L.Chain p x y) :
    (D.coroot i x ≤ 0 ∧ 0 < D.coroot i y) ∨ (D.coroot i x < 0 ∧ 0 ≤ D.coroot i y) →
      ∃ n : ℤ, S.coroot i p = n := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro hxy; omega
  | @head x z hxz _ ih =>
    intro hxy
    obtain ⟨c, hc, n, hn⟩ := hxz
    rcases lt_trichotomy (D.coroot i z) 0 with hz | hz | hz
    · exact ih (Or.inr ⟨hz, by omega⟩)
    · have hx0 : D.coroot i x = 0 := by
        rcases lt_or_ge (D.coroot i x) 0 with hx | hx
        · exact absurd hz (L.coroot_ne_zero_of_step i x z c hc hx)
        · omega
      exact ih (Or.inl ⟨hz.le, by omega⟩)
    · have hx : D.coroot i x < 0 := by
        rcases lt_or_ge (D.coroot i x) 0 with hx | hx
        · exact hx
        · have hx0 : D.coroot i x = 0 := by omega
          exact absurd (L.coroot_nonpos_of_step i x z c hc hx0) (not_le.mpr hz)
      obtain ⟨-, hc'⟩ := L.step_neg_pos i x z c hc hx hz
      rcases hc' with rfl | rfl
      · exact ⟨n, hn⟩
      · exact ⟨-n, by rw [LinearMap.neg_apply] at hn; push_cast; linear_combination -hn⟩

/-- Reflecting chains at a position `p` with `⟨p, αᵢ^∨⟩ ∈ ℤ`: a chain from `x` to `y` with
`⟨y, αᵢ^∨⟩ > 0` gives a chain from `sᵢ x` to `sᵢ y` if `⟨x, αᵢ^∨⟩ > 0`, and a chain from `x` to
`sᵢ y` if `⟨x, αᵢ^∨⟩ ≤ 0`. (Our reconstruction of the corresponding step in [Lit94] §4.) -/
theorem Chain.reflection (hp : ∃ n : ℤ, S.coroot i p = n) (h : L.Chain p x y) :
    x ∈ L.O →
      (0 < D.coroot i x → 0 < D.coroot i y →
        L.Chain p (D.reflection i x) (D.reflection i y)) ∧
      (D.coroot i x ≤ 0 → 0 < D.coroot i y → L.Chain p x (D.reflection i y)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ ↦ ⟨fun _ _ ↦ Relation.ReflTransGen.refl, fun h₁ h₂ ↦ by omega⟩
  | @head x z hxz _ ih =>
    intro hxO
    obtain ⟨c, hc, hcp⟩ := hxz
    have hzO := (L.step_mem x z c hc).2
    obtain ⟨ih₁, ih₂⟩ := ih hzO
    refine ⟨fun hx hy ↦ ?_, fun hx hy ↦ ?_⟩
    · rcases lt_or_ge 0 (D.coroot i z) with hz | hz
      · exact Relation.ReflTransGen.head ⟨_, L.step_reflection_pos i x z c hc hx hz,
          exists_int_coroot_reflection ⟨x, z, hc⟩ hcp hp⟩ (ih₁ hz hy)
      · refine Relation.ReflTransGen.head ⟨_, L.step_simple i x hxO hx, hp⟩ ?_
        exact Relation.ReflTransGen.head ⟨c, hc, hcp⟩ (ih₂ hz hy)
    · rcases lt_or_ge 0 (D.coroot i z) with hz | hz
      · have hx' : D.coroot i x < 0 := by
          rcases lt_or_eq_of_le hx with hx' | hx'
          · exact hx'
          · exact absurd (L.coroot_nonpos_of_step i x z c hc hx') (not_le.mpr hz)
        obtain ⟨rfl, -⟩ := L.step_neg_pos i x z c hc hx' hz
        simpa using ih₁ hz hy
      · exact Relation.ReflTransGen.head ⟨c, hc, hcp⟩ (ih₂ hz hy)

/-- If `⟨p, αᵢ^∨⟩ ∉ ℤ`, a chain from `x` to `y` with `⟨x, αᵢ^∨⟩, ⟨y, αᵢ^∨⟩ > 0` stays in the
region `⟨·, αᵢ^∨⟩ > 0`, so it can be reflected by `sᵢ` step by step. -/
theorem Chain.reflection_of_not_int (hp : ¬ ∃ n : ℤ, S.coroot i p = n)
    (hp' : ∀ c x y, L.Step x y c → (∃ n : ℤ, c p = n) →
      ∃ n : ℤ, (c ∘ₗ (S.reflection i : V →ₗ[𝕜] V)) p' = n)
    (h : L.Chain p x y) :
    0 < D.coroot i x → 0 < D.coroot i y → L.Chain p' (D.reflection i x) (D.reflection i y) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ _ ↦ Relation.ReflTransGen.refl
  | @head x z hxz hzy ih =>
    intro hx hy
    obtain ⟨c, hc, hcp⟩ := hxz
    rcases lt_or_ge 0 (D.coroot i z) with hz | hz
    · exact Relation.ReflTransGen.head ⟨_, L.step_reflection_pos i x z c hc hx hz,
        hp' c x z hc hcp⟩ (ih hz hy)
    · exact absurd (Chain.exists_int (L := L) hzy (Or.inl ⟨hz, hy⟩)) hp

/-- The dual data (for time-reversed paths): directions `-O`, and steps reversed and negated. -/
def dual : LSData S where
  O := -L.O
  Step x y c := L.Step (-y) (-x) c
  reflection_mem i x hx := by
    simpa [Set.mem_neg, map_neg] using L.reflection_mem i (-x) hx
  step_mem x y c h := ⟨(L.step_mem _ _ _ h).2, (L.step_mem _ _ _ h).1⟩
  exists_int x y c h := L.exists_int _ _ _ h
  step_reflection_pos i x y c h hx hy := by
    have := L.step_reflection_neg i (-y) (-x) c h (by simpa using hy) (by simpa using hx)
    simpa [map_neg] using this
  step_reflection_neg i x y c h hx hy := by
    have := L.step_reflection_pos i (-y) (-x) c h (by simp; omega) (by simp; omega)
    simpa [map_neg] using this
  step_simple i x hx hxi := by
    have hz : D.reflection i (-x) ∈ L.O := L.reflection_mem i (-x) hx
    have := L.step_simple i _ hz (by simp [CartanDatum.coroot_reflection, hxi])
    simpa [map_neg] using this
  step_neg_pos i x y c h hx hy := by
    obtain ⟨h₁, h₂⟩ := L.step_neg_pos i (-y) (-x) c h (by simpa using hy) (by simp; omega)
    refine ⟨?_, h₂⟩
    have := congrArg (fun z ↦ -D.reflection i z) h₁
    simpa [map_neg] using this.symm
  coroot_nonpos_of_step i x y c h hx := by
    by_contra hy
    exact L.coroot_ne_zero_of_step i (-y) (-x) c h (by simp; omega) (by simp [hx])
  coroot_ne_zero_of_step i x y c h hx hy := by
    have := L.coroot_nonpos_of_step i (-y) (-x) c h (by simp [hy])
    simp at this
    omega

@[simp] lemma mem_dual_O {x : X} : x ∈ L.dual.O ↔ -x ∈ L.O := Set.mem_neg

lemma dual_step {x y : X} {c : Module.Dual 𝕜 V} : L.dual.Step x y c ↔ L.Step (-y) (-x) c :=
  Iff.rfl

@[simp] lemma dual_dual : L.dual.dual = L := by
  cases L
  simp only [dual, neg_neg]

/-- A chain from `x` to `y` gives a chain for the dual data from `-y` to `-x`. -/
lemma Chain.dual {p : V} {x y : X} (h : L.Chain p x y) : L.dual.Chain p (-y) (-x) := by
  induction h with
  | refl => exact .refl
  | tail _ hyz ih =>
    obtain ⟨c, hc, hn⟩ := hyz
    exact Relation.ReflTransGen.head ⟨c, by simpa [dual_step] using hc, hn⟩ ih

end LSData

end LSData

/-! ### Directions of paths -/

section Directions

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-- `η` is linear with direction `x ∈ X` on a right neighbourhood of `t`. -/
def HasRightDir (η : LittelmannPath S) (t : 𝕜) (x : X) : Prop :=
  ∃ δ > 0, ∀ s ∈ Icc t (t + δ), η s = η t + (s - t) • S.embed x

/-- `η` is linear with direction `x ∈ X` on a left neighbourhood of `t`. -/
def HasLeftDir (η : LittelmannPath S) (t : 𝕜) (x : X) : Prop :=
  ∃ δ > 0, ∀ s ∈ Icc (t - δ) t, η s = η t + (s - t) • S.embed x

variable {η η' : LittelmannPath S} {t : 𝕜} {x y : X} {i : ι}

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
lemma HasRightDir.pairing (h : η.HasRightDir t x) :
    ∃ δ > 0, ∀ s ∈ Icc t (t + δ), η.pairing i s = η.pairing i t + (s - t) * D.coroot i x := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun s hs ↦ by simp [LittelmannPath.pairing, h s hs, S.coroot_embed]⟩

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
lemma HasLeftDir.pairing (h : η.HasLeftDir t x) :
    ∃ δ > 0, ∀ s ∈ Icc (t - δ) t, η.pairing i s = η.pairing i t + (s - t) * D.coroot i x := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun s hs ↦ by simp [LittelmannPath.pairing, h s hs, S.coroot_embed]⟩

omit [OrderTopology 𝕜] in
lemma HasRightDir.unique (h : η.HasRightDir t x) (h' : η.HasRightDir t y) : x = y := by
  obtain ⟨δ, hδ, h⟩ := h
  obtain ⟨δ', hδ', h'⟩ := h'
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  have hs : t + min δ δ' ∈ Icc t (t + δ) := ⟨by linarith, by linarith [min_le_left δ δ']⟩
  have hs' : t + min δ δ' ∈ Icc t (t + δ') := ⟨by linarith, by linarith [min_le_right δ δ']⟩
  have := (h _ hs).symm.trans (h' _ hs')
  rw [add_sub_cancel_left, add_right_inj] at this
  exact S.embed_injective (smul_right_injective V hm.ne' this)

omit [OrderTopology 𝕜] in
lemma HasLeftDir.unique (h : η.HasLeftDir t x) (h' : η.HasLeftDir t y) : x = y := by
  obtain ⟨δ, hδ, h⟩ := h
  obtain ⟨δ', hδ', h'⟩ := h'
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  have hs : t - min δ δ' ∈ Icc (t - δ) t := ⟨by linarith [min_le_left δ δ'], by linarith⟩
  have hs' : t - min δ δ' ∈ Icc (t - δ') t := ⟨by linarith [min_le_right δ δ'], by linarith⟩
  have := (h _ hs).symm.trans (h' _ hs')
  rw [add_right_inj] at this
  exact S.embed_injective (smul_right_injective V (by linarith : t - min δ δ' - t ≠ 0) this)

omit [OrderTopology 𝕜] in
/-- If `η'` is obtained from `η` near the right of `t` by an affine map whose linear part maps
`x` to `x'`, then `η'` has direction `x'` there. -/
lemma HasRightDir.of_eq (h : η.HasRightDir t x) {ε : 𝕜} (hε : 0 < ε) (A : V →ₗ[𝕜] V) (v : V)
    (hA : ∀ s ∈ Icc t (t + ε), η' s = A (η s) + v) {x' : X} (hx' : A (S.embed x) = S.embed x') :
    η'.HasRightDir t x' := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨min δ ε, lt_min hδ hε, fun s hs ↦ ?_⟩
  have hs₁ : s ∈ Icc t (t + δ) := ⟨hs.1, hs.2.trans (by linarith [min_le_left δ ε])⟩
  have hs₂ : s ∈ Icc t (t + ε) := ⟨hs.1, hs.2.trans (by linarith [min_le_right δ ε])⟩
  rw [hA s hs₂, hA t ⟨le_rfl, by linarith⟩, h s hs₁, map_add, map_smul, hx']
  abel

omit [OrderTopology 𝕜] in
lemma HasLeftDir.of_eq (h : η.HasLeftDir t x) {ε : 𝕜} (hε : 0 < ε) (A : V →ₗ[𝕜] V) (v : V)
    (hA : ∀ s ∈ Icc (t - ε) t, η' s = A (η s) + v) {x' : X} (hx' : A (S.embed x) = S.embed x') :
    η'.HasLeftDir t x' := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨min δ ε, lt_min hδ hε, fun s hs ↦ ?_⟩
  have hs₁ : s ∈ Icc (t - δ) t := ⟨(by linarith [min_le_left δ ε] : t - δ ≤ t - min δ ε).trans hs.1,
    hs.2⟩
  have hs₂ : s ∈ Icc (t - ε) t :=
    ⟨(by linarith [min_le_right δ ε] : t - ε ≤ t - min δ ε).trans hs.1, hs.2⟩
  rw [hA s hs₂, hA t ⟨by linarith, le_rfl⟩, h s hs₁, map_add, map_smul, hx']
  abel

omit [OrderTopology 𝕜] in
/-- If `hᵢ > hᵢ(t)` just to the right of `t`, the right direction `y` has `⟨y, αᵢ^∨⟩ > 0`. -/
lemma HasRightDir.coroot_pos (h : η.HasRightDir t y) {ε : 𝕜} (hε : 0 < ε)
    (hlt : ∀ s ∈ Ioc t (t + ε), η.pairing i t < η.pairing i s) : 0 < D.coroot i y := by
  obtain ⟨δ, hδ, h⟩ := h.pairing (i := i)
  have hm : 0 < min δ ε := lt_min hδ hε
  have h₁ := h (t + min δ ε) ⟨by linarith, by linarith [min_le_left δ ε]⟩
  have h₂ := hlt (t + min δ ε) ⟨by linarith, by linarith [min_le_right δ ε]⟩
  rw [h₁, add_sub_cancel_left] at h₂
  have : (0 : 𝕜) < D.coroot i y := pos_of_mul_pos_right (by linarith) hm.le
  exact_mod_cast this

omit [OrderTopology 𝕜] in
/-- If `hᵢ ≥ hᵢ(t)` just to the right of `t`, then `⟨y, αᵢ^∨⟩ ≥ 0`. -/
lemma HasRightDir.coroot_nonneg (h : η.HasRightDir t y) {ε : 𝕜} (hε : 0 < ε)
    (hle : ∀ s ∈ Ioc t (t + ε), η.pairing i t ≤ η.pairing i s) : 0 ≤ D.coroot i y := by
  obtain ⟨δ, hδ, h⟩ := h.pairing (i := i)
  have hm : 0 < min δ ε := lt_min hδ hε
  have h₁ := h (t + min δ ε) ⟨by linarith, by linarith [min_le_left δ ε]⟩
  have h₂ := hle (t + min δ ε) ⟨by linarith, by linarith [min_le_right δ ε]⟩
  rw [h₁, add_sub_cancel_left] at h₂
  have : (0 : 𝕜) ≤ D.coroot i y := nonneg_of_mul_nonneg_right (by linarith) hm
  exact_mod_cast this

omit [OrderTopology 𝕜] in
/-- If `hᵢ ≥ hᵢ(t)` just to the left of `t`, the left direction `x` has `⟨x, αᵢ^∨⟩ ≤ 0`. -/
lemma HasLeftDir.coroot_nonpos (h : η.HasLeftDir t x) {ε : 𝕜} (hε : 0 < ε)
    (hle : ∀ s ∈ Ico (t - ε) t, η.pairing i t ≤ η.pairing i s) : D.coroot i x ≤ 0 := by
  obtain ⟨δ, hδ, h⟩ := h.pairing (i := i)
  have hm : 0 < min δ ε := lt_min hδ hε
  have h₁ := h (t - min δ ε) ⟨by linarith [min_le_left δ ε], by linarith⟩
  have h₂ := hle (t - min δ ε) ⟨by linarith [min_le_right δ ε], by linarith⟩
  rw [h₁] at h₂
  have : 0 ≤ (t - min δ ε - t) * D.coroot i x := by linarith
  have h₃ : (0 : 𝕜) ≤ -min δ ε * D.coroot i x := by linarith
  have : (D.coroot i x : 𝕜) ≤ 0 := by nlinarith
  exact_mod_cast this

omit [OrderTopology 𝕜] in
/-- If `hᵢ < hᵢ(t)` just to the left of `t`, then `⟨x, αᵢ^∨⟩ > 0`. -/
lemma HasLeftDir.coroot_pos (h : η.HasLeftDir t x) {ε : 𝕜} (hε : 0 < ε)
    (hlt : ∀ s ∈ Ico (t - ε) t, η.pairing i s < η.pairing i t) : 0 < D.coroot i x := by
  obtain ⟨δ, hδ, h⟩ := h.pairing (i := i)
  have hm : 0 < min δ ε := lt_min hδ hε
  have h₁ := h (t - min δ ε) ⟨by linarith [min_le_left δ ε], by linarith⟩
  have h₂ := hlt (t - min δ ε) ⟨by linarith [min_le_right δ ε], by linarith⟩
  rw [h₁] at h₂
  have : (0 : 𝕜) < D.coroot i x := by nlinarith
  exact_mod_cast this

/-! ### Time reversal -/

lemma HasLeftDir.rev (h : η.HasLeftDir t x) : η.rev.HasRightDir (1 - t) (-x) := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun s hs ↦ ?_⟩
  rw [rev_apply, rev_apply, h (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩, sub_sub_cancel,
    map_neg]
  module

lemma HasRightDir.rev (h : η.HasRightDir t x) : η.rev.HasLeftDir (1 - t) (-x) := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun s hs ↦ ?_⟩
  rw [rev_apply, rev_apply, h (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩, sub_sub_cancel,
    map_neg]
  module

end Directions

section Helpers

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

omit [IsStrictOrderedRing 𝕜] in
/-- Real induction on `[0, 1]`. -/
lemma induction_Icc {P : 𝕜 → Prop} (h0 : P 0)
    (hright : ∀ t ∈ Ico (0 : 𝕜) 1, (∀ s ∈ Icc 0 t, P s) → ∃ t' > t, ∀ s ∈ Icc t t', P s)
    (hleft : ∀ t ∈ Ioc (0 : 𝕜) 1, (∀ s ∈ Ico 0 t, P s) → P t) :
    ∀ t ∈ Icc (0 : 𝕜) 1, P t := by
  by_cases h01 : (0 : 𝕜) ≤ 1
  swap
  · intro t ht; exact absurd (ht.1.trans ht.2) h01
  set A := {t ∈ Icc (0 : 𝕜) 1 | ∀ s ∈ Icc 0 t, P s}
  have h0A : (0 : 𝕜) ∈ A := ⟨⟨le_rfl, h01⟩, fun s hs ↦ le_antisymm hs.2 hs.1 ▸ h0⟩
  have hbdd : BddAbove A := ⟨1, fun t ht ↦ ht.1.2⟩
  set τ := sSup A
  have hτ0 : 0 ≤ τ := le_csSup hbdd h0A
  have hτ1 : τ ≤ 1 := csSup_le ⟨0, h0A⟩ fun t ht ↦ ht.1.2
  have hlt : ∀ s ∈ Ico 0 τ, P s := fun s hs ↦ by
    obtain ⟨a, ha, hsa⟩ := exists_lt_of_lt_csSup ⟨0, h0A⟩ hs.2
    exact ha.2 s ⟨hs.1, hsa.le⟩
  have hPτ : P τ := by
    rcases eq_or_lt_of_le hτ0 with h | h
    · rw [← h]; exact h0
    · exact hleft τ ⟨h, hτ1⟩ hlt
  have hτA : τ ∈ A := ⟨⟨hτ0, hτ1⟩, fun s hs ↦ by
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]; exact hPτ
    · exact hlt s ⟨hs.1, h⟩⟩
  have hτ : τ = 1 := by
    by_contra hne
    have hτ1' : τ < 1 := lt_of_le_of_ne hτ1 hne
    obtain ⟨t', ht', hP⟩ := hright τ ⟨hτ0, hτ1'⟩ hτA.2
    have hmem : min t' 1 ∈ A := ⟨⟨hτ0.trans (le_min ht'.le hτ1), min_le_right _ _⟩,
      fun s hs ↦ by
        rcases le_total s τ with h | h
        · exact hτA.2 s ⟨hs.1, h⟩
        · exact hP s ⟨h, hs.2.trans (min_le_left _ _)⟩⟩
    have := le_csSup hbdd hmem
    exact absurd this (not_le.mpr (lt_min ht' hτ1'))
  intro t ht
  exact hτA.2 t ⟨ht.1, hτ ▸ ht.2⟩

omit [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private lemma eq_of_two_points {v w a : V} {s₁ s₂ t : 𝕜} (hs : s₁ ≠ s₂)
    (h₁ : a + (s₁ - t) • v = s₁ • w) (h₂ : a + (s₂ - t) • v = s₂ • w) : v = w ∧ a = t • w := by
  have : (s₁ - s₂) • v = (s₁ - s₂) • w := calc
    (s₁ - s₂) • v = (a + (s₁ - t) • v) - (a + (s₂ - t) • v) := by module
    _ = s₁ • w - s₂ • w := by rw [h₁, h₂]
    _ = (s₁ - s₂) • w := by module
  have hvw := smul_right_injective V (sub_ne_zero.mpr hs) this
  refine ⟨hvw, ?_⟩
  rw [hvw] at h₁
  calc a = (a + (s₁ - t) • w) - (s₁ - t) • w := by module
    _ = s₁ • w - (s₁ - t) • w := by rw [h₁]
    _ = t • w := by module

end Helpers

/-! ### Lakshmibai–Seshadri paths -/

section IsLS

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-- A (parametrized) Lakshmibai–Seshadri path for the data `L` ([Lit94] §2, [Lit95] §4):
`η` is piecewise linear with directions in `O` (locally on both sides of every time `t`), and at
every time `t ∈ (0,1)` its left direction `x` and right direction `y` are joined by a chain of
Bruhat steps `x → ⋯ → y` whose coroots `β^∨` satisfy `⟨η(t), β^∨⟩ ∈ ℤ`. For the data of a
dominant weight `λ` these are Littelmann's LS paths of shape `λ`: a direction change `τ > σ` at
time `a` with an `a`-chain (the condition `a ⟨κλ, β^∨⟩ ∈ ℤ` of [Lit94] is equivalent to
`⟨η(a), β^∨⟩ ∈ ℤ`, since `η(a) ≡ aκλ` modulo the root lattice). -/
structure IsLS (L : LSData S) (η : LittelmannPath S) : Prop where
  right : ∀ t ∈ Ico (0 : 𝕜) 1, ∃ x ∈ L.O, η.HasRightDir t x
  left : ∀ t ∈ Ioc (0 : 𝕜) 1, ∃ x ∈ L.O, η.HasLeftDir t x
  chain : ∀ t ∈ Ioo (0 : 𝕜) 1, ∀ x y, η.HasLeftDir t x → η.HasRightDir t y →
    L.Chain (η t) x y

variable {L : LSData S} {η : LittelmannPath S} {i : ι}

/-- Time reversal maps Lakshmibai–Seshadri paths for `L` to those for the dual data. -/
theorem IsLS.rev (h : IsLS L η) : IsLS L.dual η.rev where
  right t ht := by
    obtain ⟨x, hx, hx'⟩ := h.left (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact ⟨-x, by simpa using hx, by simpa using hx'.rev⟩
  left t ht := by
    obtain ⟨x, hx, hx'⟩ := h.right (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact ⟨-x, by simpa using hx, by simpa using hx'.rev⟩
  chain t ht x y hx hy := by
    have hx' := hx.rev
    have hy' := hy.rev
    rw [rev_rev] at hx' hy'
    have := (h.chain (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ _ _ hy' hx').dual
    simp only [neg_neg] at this
    rw [rev_apply, apply_one]
    exact this.sub_embed _

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A continuous function on `[a, b]` has a last minimizer. -/
lemma exists_last_minimizer {g : 𝕜 → 𝕜} (hg : Continuous g) {a b : 𝕜} (hab : a ≤ b) :
    ∃ w ∈ Icc a b, (∀ s ∈ Icc a b, g w ≤ g s) ∧ ∀ s ∈ Ioc w b, g w < g s := by
  obtain ⟨u, hu, hu'⟩ := exists_eq_sInf_image_Icc hg hab
  set K := Icc a b ∩ g ⁻¹' {sInf (g '' Icc a b)}
  have hK : IsClosed K := isClosed_Icc.inter (isClosed_singleton.preimage hg)
  have hKne : K.Nonempty := ⟨u, hu, hu'⟩
  have hKb : BddAbove K := ⟨b, fun x hx ↦ hx.1.2⟩
  have hw := hK.csSup_mem hKne hKb
  refine ⟨sSup K, hw.1, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rw [show g (sSup K) = sInf (g '' Icc a b) from hw.2]
    exact sInf_image_Icc_le hg hs
  · have hs' : s ∈ Icc a b := ⟨hw.1.1.trans hs.1.le, hs.2⟩
    rw [show g (sSup K) = sInf (g '' Icc a b) from hw.2]
    refine lt_of_le_of_ne (sInf_image_Icc_le hg hs') fun h ↦ ?_
    exact absurd (le_csSup hKb ⟨hs', h.symm⟩) (not_le.mpr hs.1)

omit [OrderTopology 𝕜] in
/-- On a Lakshmibai–Seshadri path, a strict local minimum from the right (weak from the left) of
`hᵢ` at a time `w ∈ (0,1)` is attained at an integer value ([Lit95] Lemma 4.5(d)). -/
theorem IsLS.exists_int_of_isMin (hη : IsLS L η) {a b w : 𝕜} (hw : w ∈ Ioo (0 : 𝕜) 1)
    (haw : a < w) (hwb : w < b) (hmin : ∀ s ∈ Icc a b, η.pairing i w ≤ η.pairing i s)
    (hlt : ∀ s ∈ Ioc w b, η.pairing i w < η.pairing i s) : ∃ n : ℤ, η.pairing i w = n := by
  obtain ⟨x, -, hx⟩ := hη.left w ⟨hw.1, hw.2.le⟩
  obtain ⟨y, -, hy⟩ := hη.right w ⟨hw.1.le, hw.2⟩
  have hx' : D.coroot i x ≤ 0 := hx.coroot_nonpos (sub_pos.mpr haw) fun s hs ↦
    hmin s ⟨by linarith [hs.1], hs.2.le.trans hwb.le⟩
  have hy' : 0 < D.coroot i y := hy.coroot_pos (sub_pos.mpr hwb) fun s hs ↦
    hlt s ⟨hs.1, by linarith [hs.2]⟩
  exact (hη.chain w hw x y hx hy).exists_int (Or.inl ⟨hx', hy'⟩)

/-- The minimum `mᵢ` of `hᵢ` on a Lakshmibai–Seshadri path is an integer. -/
theorem IsLS.exists_int_minPairing (hη : IsLS L η) (i : ι) :
    ∃ n : ℤ, η.minPairing i = n := by
  obtain ⟨w, hw, hmin, hlt⟩ := exists_last_minimizer (η.continuous_pairing i)
    (zero_le_one (α := 𝕜))
  have hm : η.minPairing i = η.pairing i w :=
    le_antisymm (η.minPairing_le hw) (η.le_runningMin zero_le_one fun s hs ↦ hmin s hs)
  rw [hm]
  rcases eq_or_lt_of_le hw.1 with h0 | h0
  · exact ⟨0, by rw [← h0, pairing_zero, Int.cast_zero]⟩
  rcases eq_or_lt_of_le hw.2 with h1 | h1
  · exact ⟨_, by rw [h1, pairing_one]⟩
  exact hη.exists_int_of_isMin ⟨h0, h1⟩ h0 h1 hmin hlt

/-- The shape of `hᵢ` on a Lakshmibai–Seshadri path with `fᵢ η ≠ 0` ([Lit94] §4, [Lit95]
Prop. 4.7; reconstructed): with `m = mᵢ`, let `p` be the last time with `hᵢ(p) = m` and `q > p` the
first time with `hᵢ(q) = m + 1`. Then `hᵢ` is strictly increasing on `[p, q]` and `hᵢ ≥ m + 1` on
`[q, 1]`; this uses that local minima of `hᵢ` are integers. -/
theorem IsLS.exists_f_times (hη : IsLS L η) (i : ι)
    (h1 : η.minPairing i + 1 ≤ η.pairing i 1) :
    ∃ p q : 𝕜, 0 ≤ p ∧ p < q ∧ q ≤ 1 ∧ η.pairing i p = η.minPairing i ∧
      (∀ s ∈ Ioc p 1, η.minPairing i < η.pairing i s) ∧
      η.pairing i q = η.minPairing i + 1 ∧ StrictMonoOn (η.pairing i) (Icc p q) ∧
      ∀ s ∈ Icc q 1, η.minPairing i + 1 ≤ η.pairing i s := by
  obtain ⟨n, hn⟩ := hη.exists_int_minPairing i
  set m := η.minPairing i with hm_def
  set h := η.pairing i with hh
  have hcont : Continuous h := η.continuous_pairing i
  have hge : ∀ s ∈ Icc (0 : 𝕜) 1, m ≤ h s := fun s hs ↦ η.minPairing_le hs
  -- the last minimum `p`
  obtain ⟨p, hp, hpmin, hplt⟩ := exists_last_minimizer hcont (zero_le_one (α := 𝕜))
  have hpm : h p = m :=
    le_antisymm (by obtain ⟨u, hu, hu'⟩ := η.exists_minPairing i; exact (hpmin u hu).trans hu'.le)
      (hge p hp)
  -- the first time `q ≥ p` with `h q = m + 1`
  obtain ⟨q, hq, hqv, hqlt⟩ := exists_first_eq (g := fun s ↦ -h s) hcont.neg hp.2
    (c := -(m + 1)) (show -(m + 1) ≤ -h p by linarith) (show -h 1 ≤ -(m + 1) by linarith)
  simp only [neg_inj] at hqv
  have hqlt' : ∀ v ∈ Ico p q, h v < m + 1 := fun v hv ↦ by linarith [hqlt v hv]
  have hpq : p < q := lt_of_le_of_ne hq.1 fun h' ↦ by rw [← h', hpm] at hqv; linarith
  have hnoint : ∀ w ∈ Ioo p q, ¬ ∃ k : ℤ, h w = k := fun w hw ⟨k, hk⟩ ↦ by
    have h₁ : m < h w := by rw [← hpm]; exact hplt w ⟨hw.1, hw.2.le.trans hq.2⟩
    have h₂ : h w < m + 1 := hqlt' w ⟨hw.1.le, hw.2⟩
    rw [hk, hn] at h₁ h₂
    have h₁' : n < k := by exact_mod_cast h₁
    have h₂' : k < n + 1 := by exact_mod_cast h₂
    omega
  have hmono : StrictMonoOn h (Icc p q) := by
    intro u hu v hv huv
    by_contra hvu
    replace hvu := not_lt.mp hvu
    obtain ⟨w, hw, hwmin, hwlt⟩ := exists_last_minimizer hcont hu.2
    have hvq : v < q := lt_of_le_of_ne hv.2 fun h' ↦ by
      have := hqlt' u ⟨hu.1, huv.trans_le hv.2⟩
      rw [h'] at hvu
      linarith
    have hwv : h w ≤ h v := hwmin v ⟨huv.le, hv.2⟩
    have hwq : w ≠ q := fun h' ↦ by
      have := hqlt' v ⟨hv.1, hvq⟩
      rw [h'] at hwv
      linarith
    have hwu : w ≠ u := fun h' ↦ by
      have := hwlt v ⟨h' ▸ huv, hv.2⟩
      rw [h'] at this
      linarith
    have huw : u < w := lt_of_le_of_ne hw.1 (Ne.symm hwu)
    have hwq' : w < q := lt_of_le_of_ne hw.2 hwq
    exact hnoint w ⟨hu.1.trans_lt huw, hwq'⟩ (hη.exists_int_of_isMin
      ⟨hp.1.trans_lt (hu.1.trans_lt huw), hwq'.trans_le hq.2⟩ huw hwq' hwmin hwlt)
  refine ⟨p, q, hp.1, hpq, hq.2, hpm, fun s hs ↦ hpm ▸ hplt s hs, hqv, hmono, ?_⟩
  -- after `q`, `h ≥ m + 1`
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hslt⟩ := hcon
  obtain ⟨w, hw, hwmin, hwlt⟩ := exists_last_minimizer hcont hq.2
  have hws : h w < m + 1 := (hwmin s hs).trans_lt hslt
  have hwm : m < h w := by rw [← hpm]; exact hplt w ⟨hpq.trans_le hw.1, hw.2⟩
  have hwq : q < w := lt_of_le_of_ne hw.1 fun h' ↦ by rw [← h', hqv] at hws; linarith
  have hint : ∃ k : ℤ, h w = k := by
    rcases eq_or_lt_of_le hw.2 with h' | h'
    · exact ⟨_, by rw [h', hh, pairing_one]⟩
    · exact hη.exists_int_of_isMin ⟨(hp.1.trans_lt hpq).trans hwq, h'⟩ hwq h' hwmin hwlt
  obtain ⟨k, hk⟩ := hint
  rw [hk, hn] at hws hwm
  have h₁' : n < k := by exact_mod_cast hwm
  have h₂' : k < n + 1 := by exact_mod_cast hws
  omega

/-- **The root operators `fᵢ` preserve Lakshmibai–Seshadri paths** ([Lit94] §4, [Lit95] §4
Cor. 2). With `p < q` as in `LittelmannPath.IsLS.exists_f_times`, `fᵢ η` is `η` on `[0, p]`,
`sᵢ η + mᵢ αᵢ` on `[p, q]` and `η - αᵢ` on `[q, 1]`; the chain conditions at `p`, inside
`(p, q)` and at `q` are provided by `LSData.Chain.reflection`,
`LSData.Chain.reflection_of_not_int` and `LSData.step_simple`. (Our reconstruction.) -/
theorem IsLS.f (hη : IsLS L η) {η' : LittelmannPath S} (hf : LittelmannPath.f i η = some η') :
    IsLS L η' := by
  have h1 : η.minPairing i + 1 ≤ η.pairing i 1 := by
    have := (f_eq_none_iff (i := i) (π := η)).not.mp (by rw [hf]; simp)
    push Not at this
    linarith
  obtain ⟨p, q, hp0, hpq, hq1, hpm, hplt, hqm, hmono, hqge⟩ := hη.exists_f_times i h1
  obtain ⟨n, hn⟩ := hη.exists_int_minPairing i
  set m := η.minPairing i with hm_def
  have hint : ∀ c a b, L.Step a b c → ∃ k : ℤ, c (S.root i) = k :=
    fun c a b hc ↦ L.exists_int a b c hc (D.root i)
  -- the three regions
  have hA : ∀ s ∈ Icc (0 : 𝕜) p, η' s = (LinearMap.id : V →ₗ[𝕜] V) (η s) + 0 := fun s hs ↦ by
    have hr : η.rightMin i s = m := le_antisymm
      ((η.rightMin_le ⟨hs.2, hpq.le.trans hq1⟩).trans hpm.le)
      (η.le_rightMin (hs.2.trans (hpq.le.trans hq1)) fun u hu ↦
        η.minPairing_le ⟨hs.1.trans hu.1, hu.2⟩)
    rw [f_apply hf ⟨hs.1, hs.2.trans (hpq.le.trans hq1)⟩, hr, min_eq_left (by linarith)]
    simp [hm_def]
  have hB : ∀ s ∈ Icc p q, η' s = (S.reflection i : V →ₗ[𝕜] V) (η s) + m • S.root i :=
      fun s hs ↦ by
    have hsq : η.pairing i s ≤ m + 1 := hqm ▸ hmono.monotoneOn hs ⟨hpq.le, le_rfl⟩ hs.2
    have hr : η.rightMin i s = η.pairing i s := le_antisymm
      (η.rightMin_le ⟨le_rfl, hs.2.trans hq1⟩)
      (η.le_rightMin (hs.2.trans hq1) fun u hu ↦ by
        rcases le_total u q with huq | huq
        · exact hmono.monotoneOn hs ⟨hs.1.trans hu.1, huq⟩ hu.1
        · exact hsq.trans (hqge u ⟨huq, hu.2⟩))
    rw [f_apply hf ⟨hp0.trans hs.1, hs.2.trans hq1⟩, hr, min_eq_left hsq, LinearEquiv.coe_coe,
      S.reflection_apply]
    simp only [pairing]
    module
  have hC : ∀ s ∈ Icc q 1, η' s = (LinearMap.id : V →ₗ[𝕜] V) (η s) + -S.root i := fun s hs ↦ by
    have hr : m + 1 ≤ η.rightMin i s := η.le_rightMin hs.2 fun u hu ↦ hqge u ⟨hs.1.trans hu.1, hu.2⟩
    rw [f_apply hf ⟨(hp0.trans hpq.le).trans hs.1, hs.2⟩, min_eq_right hr, LinearMap.id_apply]
    module
  have hAe : ∀ x : X, (LinearMap.id : V →ₗ[𝕜] V) (S.embed x) = S.embed x := fun _ ↦ rfl
  have hBe : ∀ x : X, (S.reflection i : V →ₗ[𝕜] V) (S.embed x) = S.embed (D.reflection i x) :=
    fun x ↦ (S.embed_reflection i x).symm
  -- directions of `η'` in the three regions
  have hRA : ∀ t ∈ Ico (0 : 𝕜) p, ∀ x, η.HasRightDir t x → η'.HasRightDir t x :=
    fun t ht x hx ↦ hx.of_eq (sub_pos.mpr ht.2) _ _
      (fun s hs ↦ hA s ⟨ht.1.trans hs.1, by linarith [hs.2]⟩) (hAe x)
  have hRB : ∀ t ∈ Ico p q, ∀ x, η.HasRightDir t x → η'.HasRightDir t (D.reflection i x) :=
    fun t ht x hx ↦ hx.of_eq (sub_pos.mpr ht.2) _ _
      (fun s hs ↦ hB s ⟨ht.1.trans hs.1, by linarith [hs.2]⟩) (hBe x)
  have hRC : ∀ t ∈ Ico q 1, ∀ x, η.HasRightDir t x → η'.HasRightDir t x :=
    fun t ht x hx ↦ hx.of_eq (sub_pos.mpr ht.2) _ _
      (fun s hs ↦ hC s ⟨ht.1.trans hs.1, by linarith [hs.2]⟩) (hAe x)
  have hLA : ∀ t ∈ Ioc (0 : 𝕜) p, ∀ x, η.HasLeftDir t x → η'.HasLeftDir t x :=
    fun t ht x hx ↦ hx.of_eq ht.1 _ _
      (fun s hs ↦ hA s ⟨by linarith [hs.1], hs.2.trans ht.2⟩) (hAe x)
  have hLB : ∀ t ∈ Ioc p q, ∀ x, η.HasLeftDir t x → η'.HasLeftDir t (D.reflection i x) :=
    fun t ht x hx ↦ hx.of_eq (sub_pos.mpr ht.1) _ _
      (fun s hs ↦ hB s ⟨by linarith [hs.1], hs.2.trans ht.2⟩) (hBe x)
  have hLC : ∀ t ∈ Ioc q 1, ∀ x, η.HasLeftDir t x → η'.HasLeftDir t x :=
    fun t ht x hx ↦ hx.of_eq (sub_pos.mpr ht.1) _ _
      (fun s hs ↦ hC s ⟨by linarith [hs.1], hs.2.trans ht.2⟩) (hAe x)
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht x' y' hx' hy' ↦ ?_⟩
  · obtain ⟨x, hx, hxd⟩ := hη.right t ht
    rcases lt_or_ge t p with htp | htp
    · exact ⟨x, hx, hRA t ⟨ht.1, htp⟩ x hxd⟩
    rcases lt_or_ge t q with htq | htq
    · exact ⟨_, L.reflection_mem i x hx, hRB t ⟨htp, htq⟩ x hxd⟩
    · exact ⟨x, hx, hRC t ⟨htq, ht.2⟩ x hxd⟩
  · obtain ⟨x, hx, hxd⟩ := hη.left t ht
    rcases le_or_gt t p with htp | htp
    · exact ⟨x, hx, hLA t ⟨ht.1, htp⟩ x hxd⟩
    rcases le_or_gt t q with htq | htq
    · exact ⟨_, L.reflection_mem i x hx, hLB t ⟨htp, htq⟩ x hxd⟩
    · exact ⟨x, hx, hLC t ⟨htq, ht.2⟩ x hxd⟩
  -- the chain conditions
  obtain ⟨x, hxO, hx⟩ := hη.left t ⟨ht.1, ht.2.le⟩
  obtain ⟨y, hyO, hy⟩ := hη.right t ⟨ht.1.le, ht.2⟩
  have hc := hη.chain t ht x y hx hy
  rcases lt_trichotomy t p with htp | rfl | htp
  · -- before `p`: nothing changes
    obtain rfl := (hx'.unique (hLA t ⟨ht.1, htp.le⟩ x hx)).symm
    obtain rfl := (hy'.unique (hRA t ⟨ht.1.le, htp⟩ y hy)).symm
    rw [hA t ⟨ht.1.le, htp.le⟩]
    simpa using hc
  · -- at `p`
    obtain rfl := (hx'.unique (hLA t ⟨ht.1, le_rfl⟩ x hx)).symm
    obtain rfl := (hy'.unique (hRB t ⟨le_rfl, hpq⟩ y hy)).symm
    rw [hA t ⟨ht.1.le, le_rfl⟩, LinearMap.id_apply, add_zero]
    have hxn : D.coroot i x ≤ 0 := hx.coroot_nonpos ht.1 fun s hs ↦ by
      rw [hpm]; exact η.minPairing_le ⟨by linarith [hs.1], hs.2.le.trans ht.2.le⟩
    have hyp : 0 < D.coroot i y := hy.coroot_pos (sub_pos.mpr ht.2) fun s hs ↦ by
      rw [hpm]; exact hplt s ⟨hs.1, by linarith [hs.2]⟩
    exact ((hc.reflection ⟨n, by rw [← hn]; exact hpm⟩) hxO).2 hxn hyp
  rcases lt_trichotomy t q with htq | rfl | htq
  · -- strictly between `p` and `q`
    obtain rfl := (hx'.unique (hLB t ⟨htp, htq.le⟩ x hx)).symm
    obtain rfl := (hy'.unique (hRB t ⟨htp.le, htq⟩ y hy)).symm
    rw [hB t ⟨htp.le, htq.le⟩]
    have hxp : 0 < D.coroot i x := hx.coroot_pos (sub_pos.mpr htp) fun s hs ↦
      hmono ⟨by linarith [hs.1], by linarith [hs.2]⟩ ⟨htp.le, htq.le⟩ hs.2
    have hyp : 0 < D.coroot i y := hy.coroot_pos (sub_pos.mpr htq) fun s hs ↦
      hmono ⟨htp.le, htq.le⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩ hs.1
    have hnot : ¬ ∃ k : ℤ, S.coroot i (η t) = k := fun ⟨k, hk⟩ ↦ by
      have h₁ : m < η.pairing i t := hpm ▸ hmono ⟨le_rfl, hpq.le⟩ ⟨htp.le, htq.le⟩ htp
      have h₂ : η.pairing i t < m + 1 := hqm ▸ hmono ⟨htp.le, htq.le⟩ ⟨hpq.le, le_rfl⟩ htq
      simp only [pairing] at h₁ h₂
      rw [hk, hn] at h₁ h₂
      have h₁' : n < k := by exact_mod_cast h₁
      have h₂' : k < n + 1 := by exact_mod_cast h₂
      omega
    refine LSData.Chain.reflection_of_not_int hnot (fun c a b hc' ⟨k, hk⟩ ↦ ?_) hc hxp hyp
    obtain ⟨k', hk'⟩ := hint c a b hc'
    refine ⟨k - n * k', ?_⟩
    have hr : S.reflection i (S.root i) = -S.root i := Module.reflection_apply_self _
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_add, map_smul,
      S.reflection_reflection, hr, map_neg, hk, hk', smul_eq_mul, hn]
    push_cast
    ring
  · -- at `q`
    obtain rfl := (hx'.unique (hLB t ⟨htp, le_rfl⟩ x hx)).symm
    obtain rfl := (hy'.unique (hRC t ⟨le_rfl, ht.2⟩ y hy)).symm
    rw [hC t ⟨le_rfl, ht.2.le⟩, LinearMap.id_apply, ← sub_eq_add_neg]
    have hxp : 0 < D.coroot i x := hx.coroot_pos (sub_pos.mpr htp) fun s hs ↦
      hmono ⟨by linarith [hs.1], by linarith [hs.2]⟩ ⟨hpq.le, le_rfl⟩ hs.2
    refine Relation.ReflTransGen.head ⟨S.coroot i, L.step_simple i x hxO hxp, n - 1, ?_⟩
      (hc.sub_embed (D.root i))
    rw [map_sub, S.coroot_root_self]
    change η.pairing i t - 2 = _
    rw [hqm, hn]
    push_cast
    ring
  · -- after `q`
    obtain rfl := (hx'.unique (hLC t ⟨htq, ht.2.le⟩ x hx)).symm
    obtain rfl := (hy'.unique (hRC t ⟨htq.le, ht.2⟩ y hy)).symm
    rw [hC t ⟨htq.le, ht.2.le⟩, LinearMap.id_apply, ← sub_eq_add_neg]
    exact hc.sub_embed (D.root i)

/-- **The root operators `eᵢ` preserve Lakshmibai–Seshadri paths** ([Lit94] §4, [Lit95] §4
Cor. 2): by time reversal, `eᵢ η = (fᵢ η^∨)^∨`, and time reversal exchanges the data `L` with
its dual. -/
theorem IsLS.e (hη : IsLS L η) {η' : LittelmannPath S} (he : LittelmannPath.e i η = some η') :
    IsLS L η' := by
  have hf : LittelmannPath.f i η.rev = some η'.rev := by rw [f_rev, he, Option.map_some]
  have := (hη.rev.f hf).rev
  rwa [LSData.dual_dual, rev_rev] at this

omit [OrderTopology 𝕜] in
/-- A linear form bounded by `C` on the directions of a Lakshmibai–Seshadri path is bounded by
`t C` along the path. -/
theorem IsLS.le_mul (hη : IsLS L η) (g : V →ₗ[𝕜] 𝕜) {C : 𝕜}
    (hC : ∀ x ∈ L.O, g (S.embed x) ≤ C) : ∀ t ∈ Icc (0 : 𝕜) 1, g (η t) ≤ t * C := by
  refine induction_Icc (by simp) (fun t ht hP ↦ ?_) (fun t ht hP ↦ ?_)
  · obtain ⟨x, hx, δ, hδ, h⟩ := hη.right t ht
    refine ⟨t + δ, by linarith, fun s hs ↦ ?_⟩
    rw [h s hs, map_add, map_smul, smul_eq_mul]
    have := hP t ⟨ht.1, le_rfl⟩
    have := hC x hx
    nlinarith [hs.1]
  · obtain ⟨x, hx, δ, hδ, h⟩ := hη.left t ht
    set s₀ := t - min δ t
    have hs₀ : s₀ ∈ Icc (t - δ) t := ⟨by linarith [min_le_left δ t], by linarith [lt_min hδ ht.1]⟩
    have h₁ := hP s₀ ⟨by linarith [min_le_right δ t], by linarith [lt_min hδ ht.1]⟩
    rw [h s₀ hs₀, map_add, map_smul, smul_eq_mul] at h₁
    have := hC x hx
    have hts : 0 ≤ t - s₀ := by linarith [lt_min hδ ht.1]
    nlinarith

/-- A Lakshmibai–Seshadri path with all `hᵢ ≥ 0` (i.e. with image in the dominant chamber) is the
straight line path `π_λ`, if `λ` is the only dominant direction and no step starts at `λ`
(`λ` is the minimum of the Bruhat order). -/
theorem IsLS.eq_straightLine (hη : IsLS L η) {μ : X}
    (hdom : ∀ x ∈ L.O, (∀ i, 0 ≤ D.coroot i x) → x = μ) (hmin : ∀ y c, ¬ L.Step μ y c)
    (h : ∀ i, 0 ≤ η.minPairing i) : η = straightLine S μ := by
  have key : ∀ t ∈ Icc (0 : 𝕜) 1, η t = t • S.embed μ := by
    refine induction_Icc (by simp) (fun t ht hP ↦ ?_) (fun t ht hP ↦ ?_)
    · obtain ⟨y, hy, hyd⟩ := hη.right t ht
      have hyμ : y = μ := by
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · refine hdom y hy fun i ↦ hyd.coroot_nonneg (sub_pos.mpr ht.2) fun s hs ↦ ?_
          rw [← h0, pairing_zero]
          exact (h i).trans (η.minPairing_le ⟨h0.le.trans hs.1.le, by linarith [hs.2]⟩)
        · obtain ⟨x, hx, hxd⟩ := hη.left t ⟨h0, ht.2.le⟩
          obtain ⟨δ, hδ, hxd'⟩ := hxd
          set s₁ := t - min δ t with hs₁d
          set s₂ := t - min δ t / 2 with hs₂d
          have hm := lt_min hδ h0
          have h₁ := hxd' s₁ ⟨by linarith [min_le_left δ t], by linarith⟩
          have h₂ := hxd' s₂ ⟨by linarith [min_le_left δ t], by linarith⟩
          rw [hP s₁ ⟨by linarith [min_le_right δ t], by linarith⟩] at h₁
          rw [hP s₂ ⟨by linarith [min_le_right δ t], by linarith⟩] at h₂
          obtain ⟨hxμ, -⟩ := eq_of_two_points (by linarith : s₁ ≠ s₂) h₁.symm h₂.symm
          have hxμ' : x = μ := S.embed_injective hxμ
          subst hxμ'
          rcases (hη.chain t ⟨h0, ht.2⟩ x y ⟨δ, hδ, hxd'⟩ hyd).cases_head with
            h' | ⟨z, ⟨c, hc, -⟩, -⟩
          · exact h'.symm
          · exact absurd hc (hmin z c)
      subst hyμ
      obtain ⟨δ, hδ, hyd⟩ := hyd
      refine ⟨t + δ, by linarith, fun s hs ↦ ?_⟩
      rw [hyd s hs, hP t ⟨ht.1, le_rfl⟩, ← add_smul, add_sub_cancel]
    · obtain ⟨x, -, δ, hδ, hxd⟩ := hη.left t ht
      set s₁ := t - min δ t with hs₁d
      set s₂ := t - min δ t / 2 with hs₂d
      have hm := lt_min hδ ht.1
      have h₁ := hxd s₁ ⟨by linarith [min_le_left δ t], by linarith⟩
      have h₂ := hxd s₂ ⟨by linarith [min_le_left δ t], by linarith⟩
      rw [hP s₁ ⟨by linarith [min_le_right δ t], by linarith⟩] at h₁
      rw [hP s₂ ⟨by linarith [min_le_right δ t], by linarith⟩] at h₂
      exact (eq_of_two_points (by linarith : s₁ ≠ s₂) h₁.symm h₂.symm).2
  refine ext_of_eqOn fun t ht ↦ ?_
  rw [key t ht, straightLine_apply, min_eq_right ht.2, max_eq_right ht.1]

/-- The straight line path `π_λ` is a Lakshmibai–Seshadri path if `λ ∈ O`. -/
theorem isLS_straightLine {μ : X} (hμ : μ ∈ L.O) : IsLS L (straightLine S μ) := by
  have hR : ∀ t ∈ Ico (0 : 𝕜) 1, (straightLine S μ).HasRightDir t μ := fun t ht ↦
    ⟨1 - t, by linarith [ht.2], fun s hs ↦ by
      rw [straightLine_apply, straightLine_apply, min_eq_right (by linarith [hs.2]),
        max_eq_right (ht.1.trans hs.1), min_eq_right ht.2.le, max_eq_right ht.1, ← add_smul,
        add_sub_cancel]⟩
  have hL : ∀ t ∈ Ioc (0 : 𝕜) 1, (straightLine S μ).HasLeftDir t μ := fun t ht ↦
    ⟨t, ht.1, fun s hs ↦ by
      rw [straightLine_apply, straightLine_apply, min_eq_right (hs.2.trans ht.2),
        max_eq_right (by linarith [hs.1]), min_eq_right ht.2, max_eq_right ht.1.le, ← add_smul,
        add_sub_cancel]⟩
  refine ⟨fun t ht ↦ ⟨μ, hμ, hR t ht⟩, fun t ht ↦ ⟨μ, hμ, hL t ht⟩, fun t ht x y hx hy ↦ ?_⟩
  obtain rfl := (hx.unique (hL t ⟨ht.1, ht.2.le⟩)).symm
  obtain rfl := (hy.unique (hR t ⟨ht.1.le, ht.2⟩)).symm
  exact .refl

end IsLS

/-! ### The crystal `B(λ)` -/

section Main

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}
  (L : LSData S)

/-- The Lakshmibai–Seshadri paths for `L` form a subcrystal of the crystal of all paths. -/
theorem isStable_setOf_isLS : (crystal S).IsStable {η | IsLS L η} :=
  ⟨fun _ _ _ hη he ↦ IsLS.e hη he, fun _ _ _ hη hf ↦ IsLS.f hη hf⟩

/-- **Littelmann's theorem on `B(λ)`** ([Lit94] §4–5, [Lit95] §4, Cor. 2 and 3; reconstructed in the
abstract setting of `LSData`). Let `λ ∈ O` be the only direction with all `⟨λ, αᵢ^∨⟩ ≥ 0`, let no
step start at `λ`, and let `g` be a linear form with `g(αᵢ) = 1` and `g ≤ g(λ)` on `O`. Then the
connected component `B(π_λ)` of the straight line path consists of Lakshmibai–Seshadri paths, and
it equals the set of paths `f_{i₁} ⋯ f_{iₖ} π_λ`; in particular this set is stable under all
root operators `eⱼ`.

Proof: `B(π_λ)` consists of LS paths (`LittelmannPath.IsLS.e`, `LittelmannPath.IsLS.f`). An LS
path `η` with all `eᵢ η = 0` has integral minima `mᵢ > -1`, so `mᵢ = 0`: it lies in the dominant
chamber, hence equals `π_λ` (`LittelmannPath.IsLS.eq_straightLine`). Since `g(λ) - g(wt η)` is a
nonnegative integer on `B(π_λ)` (`LittelmannPath.IsLS.le_mul`) which drops by one under each
`eᵢ`, every `η ∈ B(π_λ)` is `fᵢ η'` for some `η'` closer to `π_λ`, unless `η = π_λ`. -/
theorem component_straightLine_eq_fOrbit {μ : X} (hμ : μ ∈ L.O)
    (hdom : ∀ x ∈ L.O, (∀ i, 0 ≤ D.coroot i x) → x = μ) (hmin : ∀ y c, ¬ L.Step μ y c)
    (g : V →ₗ[𝕜] 𝕜) (hg : ∀ i, g (S.root i) = 1)
    (hgO : ∀ x ∈ L.O, g (S.embed x) ≤ g (S.embed μ)) :
    (straightLine S μ).component = (straightLine S μ).fOrbit ∧
      ∀ η ∈ (straightLine S μ).component, IsLS L η := by
  set π := straightLine S μ
  have hLS : ∀ η ∈ π.component, IsLS L η :=
    Crystal.closure_subset (isStable_setOf_isLS L)
      (singleton_subset_iff.mpr (isLS_straightLine hμ))
  -- the height `g(λ) - g(wt η)` is an integer
  have hint : ∀ η ∈ π.component, ∃ z : ℤ, g (S.embed μ) - g (S.embed η.wt) = z := by
    refine Crystal.closure_subset (C := crystal S) (S := {η | ∃ z : ℤ,
      g (S.embed μ) - g (S.embed η.wt) = z}) ⟨fun j η η' ⟨z, hz⟩ he ↦ ⟨z - 1, ?_⟩,
        fun j η η' ⟨z, hz⟩ hf ↦ ⟨z + 1, ?_⟩⟩ (singleton_subset_iff.mpr ⟨0, by simp [π]⟩)
    · rw [wt_of_e_eq_some (π := η) he]
      simp only [map_add]
      rw [← CartanDatum.PathSpace.root, hg]
      push_cast
      linarith
    · have hw := (crystal S).wt_f hf
      simp only [crystal_wt] at hw
      rw [hw]
      simp only [map_sub]
      rw [← CartanDatum.PathSpace.root, hg]
      push_cast
      linarith
  -- and nonnegative
  have hnonneg : ∀ η ∈ π.component, g (S.embed η.wt) ≤ g (S.embed μ) := fun η hη ↦ by
    have := (hLS η hη).le_mul g hgO 1 ⟨zero_le_one, le_rfl⟩
    rwa [apply_one, one_mul] at this
  have key : ∀ n : ℕ, ∀ η ∈ π.component, g (S.embed μ) - g (S.embed η.wt) = n →
      η ∈ π.fOrbit := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro η hη hn
      by_cases hall : ∀ j, e j η = none
      · have hdomη : ∀ j, 0 ≤ η.minPairing j := fun j ↦ by
          obtain ⟨k, hk⟩ := (hLS η hη).exists_int_minPairing j
          have h₁ := e_eq_none_iff.mp (hall j)
          rw [hk] at h₁ ⊢
          have : (-1 : ℤ) < k := by exact_mod_cast h₁
          exact_mod_cast (show (0 : ℤ) ≤ k by omega)
        rw [(hLS η hη).eq_straightLine hdom hmin hdomη]
        exact ⟨[], rfl⟩
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        obtain ⟨η', hη'⟩ := Option.ne_none_iff_exists'.mp hj
        have hη'c : η' ∈ π.component := π.isStable_component.e_mem j η η' hη hη'
        have hwt : η'.wt = η.wt + D.root j := wt_of_e_eq_some hη'
        have h₁ : g (S.embed μ) - g (S.embed η'.wt) = (n : 𝕜) - 1 := by
          rw [hwt, map_add, map_add, ← CartanDatum.PathSpace.root, hg]
          linarith
        have hn1 : 1 ≤ n := by
          have := hnonneg η' hη'c
          have : (1 : 𝕜) ≤ n := by linarith
          exact_mod_cast this
        obtain ⟨l, hl⟩ := ih (n - 1) (by omega) η' hη'c (by rw [h₁]; push_cast [hn1]; ring)
        exact ⟨j :: l, by rw [fWord, hl, Option.bind_some]; exact f_eq_some_iff.mpr hη'⟩
  refine ⟨subset_antisymm (fun η hη ↦ ?_) fOrbit_subset_component, hLS⟩
  obtain ⟨z, hz⟩ := hint η hη
  have hz0 : 0 ≤ z := by
    have := hnonneg η hη
    have : (0 : 𝕜) ≤ z := by linarith
    exact_mod_cast this
  exact key z.toNat η hη (by rw [hz]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm)

end Main

end LittelmannPath
