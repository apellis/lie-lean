/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Isomorphism
import LieLean.RepresentationTheory.Crystal.Path.Concatenation
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Root-operator continuity for Littelmann's linking argument

## Main results

* `pairing_bound_of_e`, `pairing_bound_of_f`: uniform root-operator estimates with
  factor `1 + 2c`, at most the source's `3c` when `c ≥ 1`.
* `eIter_isSome_iff_of_bound_lt_one`, `fIter_isSome_iff_of_bound_lt_one`:
  all same-color string lengths agree for integral minima and perturbation below one.
* `rootWord_bound`: quantitative continuity and zero/nonzero agreement for arbitrary
  mixed words in integral stable sets.
* `rootWord_eq_none_iff_of_linked`: the fixed-parametrization linking-chain lemma.

These prove the analytic input of Proposition 3.1 and the fixed-parametrization form
of Lemma 6.1, used in Theorem 6.3 and hence Theorem 7.1. They neither construct the
required integral linking chains nor establish equality of word relations. The latter
uses the separate endpoint-fiber uniqueness result, Proposition 6.2, in the source.

## Scope and references

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Proposition 3.1, pp. 507–508, and Lemma 6.1, p. 517.
Proofs below reconstruct the estimates from the repository's closed running-minimum formulas. This
analytic part extends to continuous coroot evaluations; it does NOT extend the source isomorphism
theorem beyond rational piecewise-linear paths in its symmetrizable setting.
-/

open Set

namespace LittelmannPath

variable {ι X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
  {D : CartanDatum ι X} {S : D.PathSpace ℝ V}
  {π η π' η' : LittelmannPath S} {r c : ℝ}

/-- Minima on any initial interval are nonexpansive in the uniform bound.
Analytic input to [Lit95], Proposition 3.1. -/
theorem abs_runningMin_sub_le {i : ι}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |π.runningMin i t - η.runningMin i t| ≤ r := by
  obtain ⟨u, hu, hπ⟩ := π.exists_runningMin i ht.1
  obtain ⟨v, hv, hη⟩ := η.exists_runningMin i ht.1
  have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans ht.2⟩
  have hv1 : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.trans ht.2⟩
  have hp := π.runningMin_le (i := i) hv
  have he := η.runningMin_le (i := i) hu
  have ha := abs_le.mp (h u hu1)
  have hb := abs_le.mp (h v hv1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The global height minimum is nonexpansive in the uniform bound. -/
theorem abs_minPairing_sub_le {i : ι}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r) :
    |π.minPairing i - η.minPairing i| ≤ r :=
  abs_runningMin_sub_le h ⟨zero_le_one, le_rfl⟩

/-- Minima on final intervals are nonexpansive in the uniform bound. -/
theorem abs_rightMin_sub_le {i : ι}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |π.rightMin i t - η.rightMin i t| ≤ r := by
  obtain ⟨u, hu, hπ⟩ := π.exists_rightMin i ht.2
  obtain ⟨v, hv, hη⟩ := η.exists_rightMin i ht.2
  have hu0 : u ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hu.1, hu.2⟩
  have hv0 : v ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hv.1, hv.2⟩
  have hp := π.rightMin_le (i := i) hv
  have he := η.rightMin_le (i := i) hu
  have ha := abs_le.mp (h u hu0)
  have hb := abs_le.mp (h v hv0)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Clipping two pairs of nearby real numbers changes their difference by at most `2r`.
This is the coefficient estimate in [Lit95], Proposition 3.1. -/
lemma abs_clipped_sub_le {a b a' b' : ℝ}
    (ha : |a - a'| ≤ r) (hb : |b - b'| ≤ r) :
    |(min a (b + 1) - b) - (min a' (b' + 1) - b')| ≤ 2 * r := by
  have hmin : |min a (b + 1) - min a' (b' + 1)| ≤ r := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ha ?_)
    simpa only [add_sub_add_right_eq_sub] using hb
  calc
    _ = |(min a (b + 1) - min a' (b' + 1)) - (b - b')| := by congr 1; ring
    _ ≤ |min a (b + 1) - min a' (b' + 1)| + |b - b'| := abs_sub _ _
    _ ≤ 2 * r := by linarith

/-- Uniform continuity estimate for the raising coefficient; no integrality is needed. -/
theorem abs_eCoeff_sub_le {i : ι}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |π.eCoeff i t - η.eCoeff i t| ≤ 2 * r := by
  have hclip := abs_clipped_sub_le (abs_runningMin_sub_le h ht) (abs_minPairing_sub_le h)
  unfold eCoeff
  convert hclip using 1
  congr 1
  ring

/-- The elementary perturbation bound for subtracting a root multiple. -/
lemma abs_root_correction_sub_le {a b x y k : ℝ}
    (hab : |a - b| ≤ r) (hxy : |x - y| ≤ 2 * r) (hk : |k| ≤ c) :
    |(a - x * k) - (b - y * k)| ≤ (1 + 2 * c) * r := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hab
  calc
    _ = |(a - b) - (x - y) * k| := by congr 1; ring
    _ ≤ |a - b| + |(x - y) * k| := abs_sub _ _
    _ = |a - b| + |x - y| * |k| := by rw [abs_mul]
    _ ≤ r + (2 * r) * c :=
      add_le_add hab (mul_le_mul hxy hk (abs_nonneg _) (by positivity))
    _ = (1 + 2 * c) * r := by ring

/-- [Lit95], Proposition 3.1(c), with the sharper constant `1 + 2c`.
The estimate is for any two successful raising operations. -/
theorem pairing_bound_of_e (hC : ∀ i j, |(D.cartanMatrix j i : ℝ)| ≤ c)
    (h : ∀ j t, t ∈ Icc (0 : ℝ) 1 → |π.pairing j t - η.pairing j t| ≤ r)
    {i : ι} (hπ : e i π = some π') (hη : e i η = some η') :
    ∀ j t, t ∈ Icc (0 : ℝ) 1 →
      |π'.pairing j t - η'.pairing j t| ≤ (1 + 2 * c) * r := by
  obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp hπ
  obtain ⟨hR, rfl⟩ := e_eq_some_iff.mp hη
  intro j t ht
  rw [pairing_eRaw, pairing_eRaw]
  exact abs_root_correction_sub_le (h j t ht) (abs_eCoeff_sub_le (h i) ht) (hC i j)

/-- [Lit95], Proposition 3.1(b), with the sharper constant `1 + 2c`.
The estimate is for any two successful lowering operations. -/
theorem pairing_bound_of_f (hC : ∀ i j, |(D.cartanMatrix j i : ℝ)| ≤ c)
    (h : ∀ j t, t ∈ Icc (0 : ℝ) 1 → |π.pairing j t - η.pairing j t| ≤ r)
    {i : ι} (hπ : f i π = some π') (hη : f i η = some η') :
    ∀ j t, t ∈ Icc (0 : ℝ) 1 →
      |π'.pairing j t - η'.pairing j t| ≤ (1 + 2 * c) * r := by
  intro j t ht
  have hc := abs_clipped_sub_le (abs_rightMin_sub_le (h i) ht)
    (abs_minPairing_sub_le (h i))
  rw [pairing, pairing, f_apply hπ ht, f_apply hη ht, map_sub, map_sub,
    map_smul, map_smul, CartanDatum.PathSpace.coroot_root]
  exact abs_root_correction_sub_le (h j t ht) hc (hC i j)

/-- Integer-valued height minima cannot change under a uniform perturbation below one.
This is the first discrete step of [Lit95], Proposition 3.1(a). -/
theorem minPairing_eq_of_bound_lt_one {i : ι}
    (hπ : ∃ z : ℤ, π.minPairing i = z) (hη : ∃ z : ℤ, η.minPairing i = z)
    (hr : r < 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r) :
    π.minPairing i = η.minPairing i := by
  obtain ⟨m, hm⟩ := hπ
  obtain ⟨n, hn⟩ := hη
  have hh := lt_of_le_of_lt (abs_minPairing_sub_le h) hr
  rw [hm, hn] at hh ⊢
  have hmn : |m - n| < (1 : ℤ) := by exact_mod_cast hh
  have heq : m = n := by have := abs_lt.mp hmn; omega
  rw [heq]

/-- The integral endpoint heights likewise cannot change under perturbation below one. -/
theorem pairing_one_eq_of_bound_lt_one {i : ι} (hr : r < 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r) :
    π.pairing i 1 = η.pairing i 1 := by
  have hh := lt_of_le_of_lt (h 1 ⟨zero_le_one, le_rfl⟩) hr
  rw [pairing_one, pairing_one] at hh ⊢
  have hmn : |D.coroot i π.wt - D.coroot i η.wt| < (1 : ℤ) := by exact_mod_cast hh
  have heq : D.coroot i π.wt = D.coroot i η.wt := by have := abs_lt.mp hmn; omega
  rw [heq]

/-- [Lit95], Proposition 3.1(a), for one raising and one lowering step. -/
theorem root_eq_none_iff_of_bound_lt_one {i : ι}
    (hπ : ∃ z : ℤ, π.minPairing i = z) (hη : ∃ z : ℤ, η.minPairing i = z)
    (hr : r < 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r) :
    (e i π = none ↔ e i η = none) ∧ (f i π = none ↔ f i η = none) := by
  have hm := minPairing_eq_of_bound_lt_one hπ hη hr h
  have hw := pairing_one_eq_of_bound_lt_one hr h
  simp only [e_eq_none_iff, f_eq_none_iff, hm, hw, iff_self, and_self]

/-- Full [Lit95], Proposition 3.1(a): all same-color string lengths agree.
Only the chosen color's minima must be integral. -/
theorem eIter_isSome_iff_of_bound_lt_one {i : ι}
    (hπ : ∃ z : ℤ, π.minPairing i = z) (hη : ∃ z : ℤ, η.minPairing i = z)
    (hr : r < 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r) (n : ℕ) :
    ((crystal S).eIter i n π).isSome ↔ ((crystal S).eIter i n η).isSome := by
  rw [(isSeminormal_crystal S i π n).1, (isSeminormal_crystal S i η n).1]
  simp only [crystal, ε, minPairing_eq_of_bound_lt_one hπ hη hr h]

/-- Full lowering-string version of [Lit95], Proposition 3.1(a). -/
theorem fIter_isSome_iff_of_bound_lt_one {i : ι}
    (hπ : ∃ z : ℤ, π.minPairing i = z) (hη : ∃ z : ℤ, η.minPairing i = z)
    (hr : r < 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |π.pairing i t - η.pairing i t| ≤ r) (n : ℕ) :
    ((crystal S).fIter i n π).isSome ↔ ((crystal S).fIter i n η).isSome := by
  rw [(isSeminormal_crystal S i π n).2, (isSeminormal_crystal S i η n).2]
  simp only [crystal, φ, minPairing_eq_of_bound_lt_one hπ hη hr h,
    pairing_one_eq_of_bound_lt_one hr h]

/-- A signed root letter: `inl i` raises and `inr i` lowers. -/
noncomputable def rootStep : ι ⊕ ι → LittelmannPath S → Option (LittelmannPath S)
  | .inl i => e i
  | .inr i => f i

/-- An arbitrary mixed root word, evaluated from left to right.
Unlike `fWord`, the head letter is applied first. -/
noncomputable def rootWord : List (ι ⊕ ι) → LittelmannPath S → Option (LittelmannPath S)
  | [], π => some π
  | a :: l, π => (rootStep a π).bind (rootWord l)

/-- Both signs preserve a stable subset of the path crystal. -/
lemma rootStep_mem {U : Set (LittelmannPath S)} (hU : (crystal S).IsStable U)
    {a : ι ⊕ ι} (hπ : π ∈ U) (hs : rootStep a π = some π') : π' ∈ U := by
  cases a with
  | inl i => exact hU.e_mem i π π' hπ hs
  | inr i => exact hU.f_mem i π π' hπ hs

/-- The uniform estimate for either sign of a root letter. -/
lemma pairing_bound_of_rootStep (hC : ∀ i j, |(D.cartanMatrix j i : ℝ)| ≤ c)
    (h : ∀ j t, t ∈ Icc (0 : ℝ) 1 → |π.pairing j t - η.pairing j t| ≤ r)
    {a : ι ⊕ ι} (hπ : rootStep a π = some π') (hη : rootStep a η = some η') :
    ∀ j t, t ∈ Icc (0 : ℝ) 1 →
      |π'.pairing j t - η'.pairing j t| ≤ (1 + 2 * c) * r := by
  cases a with
  | inl i => exact pairing_bound_of_e hC h hπ hη
  | inr i => exact pairing_bound_of_f hC h hπ hη

/-- The discrete nonvanishing test for either sign of a root letter. -/
lemma rootStep_eq_none_iff_of_bound_lt_one (hπ : π.IsIntegral) (hη : η.IsIntegral)
    (hr : r < 1)
    (h : ∀ j t, t ∈ Icc (0 : ℝ) 1 → |π.pairing j t - η.pairing j t| ≤ r)
    (a : ι ⊕ ι) : rootStep a π = none ↔ rootStep a η = none := by
  cases a with
  | inl i => exact (root_eq_none_iff_of_bound_lt_one (hπ i) (hη i) hr (h i)).1
  | inr i => exact (root_eq_none_iff_of_bound_lt_one (hπ i) (hη i) hr (h i)).2

/-- Quantitative mixed-word continuity and nonvanishing, the local input to
[Lit95], Lemma 6.1. Word length is arbitrary. Integrality is required on stable sets,
not assumed to follow from dominance. No component isomorphism is a premise. -/
theorem rootWord_bound
    {U W : Set (LittelmannPath S)} (hU : (crystal S).IsStable U)
    (hW : (crystal S).IsStable W)
    (hUI : ∀ ρ ∈ U, IsIntegral ρ) (hWI : ∀ ρ ∈ W, IsIntegral ρ)
    (hc : 0 ≤ c) (hC : ∀ i j, |(D.cartanMatrix j i : ℝ)| ≤ c)
    (l : List (ι ⊕ ι)) (hπ : π ∈ U) (hη : η ∈ W) (hr : 0 ≤ r)
    (hsmall : (1 + 2 * c) ^ l.length * r < 1)
    (h : ∀ j t, t ∈ Icc (0 : ℝ) 1 → |π.pairing j t - η.pairing j t| ≤ r) :
    (rootWord l π = none ↔ rootWord l η = none) ∧
      ∀ π' η', rootWord l π = some π' → rootWord l η = some η' →
        ∀ j t, t ∈ Icc (0 : ℝ) 1 →
          |π'.pairing j t - η'.pairing j t| ≤ (1 + 2 * c) ^ l.length * r := by
  induction l generalizing π η r with
  | nil =>
    constructor
    · simp [rootWord]
    · intro π' η' hπ' hη'
      cases hπ'
      cases hη'
      simpa using h
  | cons a l ih =>
    have hk : 1 ≤ 1 + 2 * c := by linarith
    have hr1 : r < 1 := lt_of_le_of_lt
      (le_mul_of_one_le_left hr (one_le_pow₀ hk)) hsmall
    have heq := rootStep_eq_none_iff_of_bound_lt_one (hUI π hπ) (hWI η hη) hr1 h a
    cases hp : rootStep a π with
    | none =>
      have hq := heq.mp hp
      simp [rootWord, hp, hq]
    | some ρ =>
      obtain ⟨σ, hq⟩ := Option.ne_none_iff_exists'.mp (by
        intro hh
        have := heq.mpr hh
        rw [hp] at this
        contradiction)
      have hi := ih (rootStep_mem hU hπ hp) (rootStep_mem hW hη hq)
        (mul_nonneg (by linarith) hr)
        (by simpa only [List.length_cons, pow_succ, mul_assoc] using hsmall)
        (pairing_bound_of_rootStep hC h hp hq)
      simpa only [rootWord, hp, hq, Option.bind_some, List.length_cons,
        pow_succ, mul_assoc] using hi

/-- One link at level `L`: equal weights, integral connected components and a small
uniform perturbation. This is the fixed-parametrization version of [Lit95], §6's link,
with the improved factor `1 + 2c` rather than `3c`. -/
def IsLink (c : ℝ) (L : ℕ) (π η : LittelmannPath S) : Prop :=
  π.wt = η.wt ∧ (∀ ρ ∈ π.component, IsIntegral ρ) ∧
    (∀ ρ ∈ η.component, IsIntegral ρ) ∧
    ∃ r : ℝ, 0 ≤ r ∧ (1 + 2 * c) ^ L * r < 1 ∧
      ∀ j t, t ∈ Icc (0 : ℝ) 1 → |π.pairing j t - η.pairing j t| ≤ r

/-- [Lit95], Lemma 6.1 for one link. The length is not bounded by a fixed numeral. -/
theorem IsLink.rootWord_eq_none_iff (hc : 0 ≤ c)
    (hC : ∀ i j, |(D.cartanMatrix j i : ℝ)| ≤ c)
    {L : ℕ} (hlink : IsLink c L π η) (l : List (ι ⊕ ι)) (hlen : l.length ≤ L) :
    rootWord l π = none ↔ rootWord l η = none := by
  obtain ⟨_, hπ, hη, r, hr, hsmall, hbound⟩ := hlink
  have hpow : (1 + 2 * c) ^ l.length ≤ (1 + 2 * c) ^ L :=
    pow_le_pow_right₀ (by linarith) hlen
  exact (rootWord_bound π.isStable_component η.isStable_component hπ hη hc hC l
    π.mem_component_self η.mem_component_self hr
    ((mul_le_mul_of_nonneg_right hpow hr).trans_lt hsmall) hbound).1

/-- [Lit95], Lemma 6.1 for an arbitrary finite linking chain.
This proves invariance of vanishing for all mixed root words of length at most `L`;
it does not construct the integral linking chains required by Theorems 6.3 and 7.1. -/
theorem rootWord_eq_none_iff_of_linked (hc : 0 ≤ c)
    (hC : ∀ i j, |(D.cartanMatrix j i : ℝ)| ≤ c)
    {L : ℕ} (hlink : Relation.ReflTransGen (IsLink c L) π η)
    (l : List (ι ⊕ ι)) (hlen : l.length ≤ L) :
    rootWord l π = none ↔ rootWord l η = none := by
  induction hlink with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.rootWord_eq_none_iff hc hC l hlen)

end LittelmannPath
