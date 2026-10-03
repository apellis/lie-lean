/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Bruhat
import Mathlib.Tactic.ReduceModChar

/-!
# Squares in the Bruhat order and the BGG signs

Let `cs : CoxeterSystem M W` be a Coxeter system (possibly infinite), with the Bruhat order `≤`
(`CoxeterSystem.BruhatLE`). Write `u ⋖ w` (`CoxeterSystem.BruhatCovBy`) if `u ≤ w` and
`ℓ(w) = ℓ(u) + 1`; by the chain property these are exactly the Bruhat steps `u → w = u t`
(`t` a reflection) that increase the length by one. These are the *arrows* of [BGG] Def. 8.9,
which BGG draw from the longer to the shorter element.

* **Squares** ([BGG] Lemma 10.3, [HumO] Prop. 0.4 (d), §6.7, [BB] Lemma 2.7.3): if
  `a ≤ d` and `ℓ(d) = ℓ(a) + 2`, there are exactly two elements `x` with `a ⋖ x ⋖ d`. Together
  with `a, d` they form a *square*.
* **Signs** ([BGG] Lemma 10.4, [HumO] §6.8): there is a function `ε` from the
  arrows to `ℤ/2` such that for every square `a ⋖ b ⋖ d`, `a ⋖ c ⋖ d` (`b ≠ c`),
  `ε(a, b) + ε(b, d) + ε(a, c) + ε(c, d) = 1`, i.e. every square anticommutes for the signs
  `(-1)^ε`. These are the signs in the differential of the BGG resolution.

## Main definitions

* `CoxeterSystem.BruhatCovBy`: the covering relation `u ⋖ w` of the Bruhat order.
* `CoxeterSystem.bruhatSign`: a sign function `ε : W → W → ZMod 2` on the arrows.

## Main results

* `CoxeterSystem.exists_middle_pair`: a Bruhat interval of length two has exactly two middle
  elements; `CoxeterSystem.ncard_middle_eq_two`: the same, as a cardinality.
* `CoxeterSystem.bruhatSign_square`: every square anticommutes for `ε`.
* `CoxeterSystem.neg_one_pow_bruhatSign_square`: the same for the signs `(-1)^ε` in any ring.

## Proofs

Both proofs are by induction on `ℓ(d)`, choosing a left descent `s` of `d` and using the
lifting property (`CoxeterSystem.BruhatLE.lifting_left`). We reconstructed the arguments.

*Squares.* If `s a > a`, the middle elements of `[a, d]` are `s a` and `s d`. If `s a < a`,
multiplication by `s` is a bijection between the middle elements of `[s a, s d]` other than `a`
and the middle elements of `[a, d]` other than `s d`, and `a` is a middle element of `[s a, s d]`
iff `s d` is one of `[a, d]`.

*Signs.* For `d ≠ 1` choose a left descent `s = s(d)`. Put `ε(s d, d) = 0` and, for any other
arrow `b ⋖ d` (then `s b ⋖ b` and `s b ⋖ s d`), `ε(b, d) = ε(s b, b) + ε(s b, s d) + 1`, so that
the square `s b ⋖ b, s d ⋖ d` anticommutes. Every other square `a ⋖ b, c ⋖ d` is a face of a
"cube" (or, if `b = s d`, of a "prism") whose other faces anticommute by induction or by
construction; as every arrow lies on exactly two faces, the sum of the relations of all faces is
`0`, which gives the relation for the remaining face.

## References

* [BGG] I. N. Bernstein, I. M. Gelfand, S. I. Gelfand, *Differential operators on the base
  affine space and a study of 𝔤-modules*, in: Lie groups and their representations (Budapest,
  1971), Halsted 1975, 21–64, §§10–11 (for the Weyl group of a complex semisimple Lie
  algebra).
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Ch. 6.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, §2.7.
-/

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

/-- The covering relation of the Bruhat order: `u ⋖ w` if `u ≤ w` and `ℓ(w) = ℓ(u) + 1`
(`CoxeterSystem.bruhatCovBy_iff` relates it to Bruhat steps, and
`CoxeterSystem.BruhatOrder.covBy_iff` to `CovBy` in `cs.BruhatOrder`). -/
def BruhatCovBy (u w : W) : Prop := cs.BruhatLE u w ∧ ℓ w = ℓ u + 1

variable {cs}

/-- `u ⋖ w` iff `u → w` is a Bruhat step with `ℓ(w) = ℓ(u) + 1`, i.e. `w = u t` for a
reflection `t` and `ℓ(w) = ℓ(u) + 1`. -/
theorem bruhatCovBy_iff {u w : W} :
    cs.BruhatCovBy u w ↔ cs.BruhatStep u w ∧ ℓ w = ℓ u + 1 := by
  refine ⟨fun ⟨h, hl⟩ ↦ ?_, fun ⟨h, hl⟩ ↦ ⟨h.bruhatLE, hl⟩⟩
  obtain ⟨v, huv, hvw, hl'⟩ := h.exists_bruhatStep_length_eq (by rintro rfl; omega)
  obtain rfl := huv.eq_of_length_le (by omega)
  exact ⟨hvw, hl⟩

/-- In `cs.BruhatOrder`, `u ⋖ w` is `CoxeterSystem.BruhatCovBy`. -/
theorem BruhatOrder.covBy_iff_bruhatCovBy {u w : cs.BruhatOrder} :
    u ⋖ w ↔ cs.BruhatCovBy (BruhatOrder.ofBruhatOrder cs u) (BruhatOrder.ofBruhatOrder cs w) := by
  rw [BruhatOrder.covBy_iff, bruhatCovBy_iff]

theorem BruhatCovBy.bruhatLE {u w : W} (h : cs.BruhatCovBy u w) : cs.BruhatLE u w := h.1

theorem BruhatCovBy.length_eq {u w : W} (h : cs.BruhatCovBy u w) : ℓ w = ℓ u + 1 := h.2

theorem BruhatCovBy.ne {u w : W} (h : cs.BruhatCovBy u w) : u ≠ w := by
  rintro rfl; have := h.2; omega

/-- `sᵢ w ⋖ w` if `sᵢ` is a left descent of `w`. -/
theorem bruhatCovBy_simple_mul_of_isLeftDescent {w : W} {i : B} (h : cs.IsLeftDescent w i) :
    cs.BruhatCovBy (s i * w) w :=
  ⟨simple_mul_bruhatLE h, ((cs.isLeftDescent_iff).mp h).symm⟩

/-- `w ⋖ sᵢ w` if `sᵢ` is not a left descent of `w`. -/
theorem bruhatCovBy_simple_mul_of_not_isLeftDescent {w : W} {i : B}
    (h : ¬cs.IsLeftDescent w i) : cs.BruhatCovBy w (s i * w) :=
  ⟨bruhatLE_simple_mul h, (cs.not_isLeftDescent_iff).mp h⟩

/-- If `x ⋖ y`, `sᵢ` is a left descent of `y` but not of `x`, then `x = sᵢ y` (lifting
property). -/
theorem BruhatCovBy.eq_simple_mul {x y : W} {i : B} (h : cs.BruhatCovBy x y)
    (hy : cs.IsLeftDescent y i) (hx : ¬cs.IsLeftDescent x i) : x = s i * y := by
  refine (h.1.lifting_left hy hx).1.eq_of_length_le ?_
  have := (cs.isLeftDescent_iff).mp hy
  have := h.2
  omega

/-- If `x ⋖ y` and `sᵢ` is a left descent of both, then `sᵢ x ⋖ sᵢ y`. -/
theorem BruhatCovBy.simple_mul {x y : W} {i : B} (h : cs.BruhatCovBy x y)
    (hx : cs.IsLeftDescent x i) (hy : cs.IsLeftDescent y i) :
    cs.BruhatCovBy (s i * x) (s i * y) := by
  refine ⟨(simple_mul_bruhatLE_simple_mul_iff hx hy).mpr h.1, ?_⟩
  have := (cs.isLeftDescent_iff).mp hx
  have := (cs.isLeftDescent_iff).mp hy
  have := h.2
  omega

/-- If `sᵢ` is a left descent of `d`, `b ⋖ d` and `b ≠ sᵢ d`, then `sᵢ` is a left descent of
`b`. -/
theorem BruhatCovBy.isLeftDescent_of_ne {b d : W} {i : B} (h : cs.BruhatCovBy b d)
    (hd : cs.IsLeftDescent d i) (hb : b ≠ s i * d) : cs.IsLeftDescent b i := by
  by_contra hb'
  exact hb (h.eq_simple_mul hd hb')

/-! ### Squares -/

/-- **Squares in the Bruhat order** ([BGG] Lemma 10.3, [BB] Lemma 2.7.3): if
`a ≤ d` and `ℓ(d) = ℓ(a) + 2`, there are exactly two elements `x` with `a ⋖ x ⋖ d`. -/
theorem exists_middle_pair {a d : W} (h : cs.BruhatLE a d) (hl : ℓ d = ℓ a + 2) :
    ∃ b c, b ≠ c ∧ ∀ x, (cs.BruhatCovBy a x ∧ cs.BruhatCovBy x d) ↔ x = b ∨ x = c := by
  classical
  induction hn : ℓ d using Nat.strong_induction_on generalizing a d with
  | _ n ih =>
  subst hn
  have hd1 : d ≠ 1 := by rintro rfl; simp at hl
  obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hd1
  have hdi := (cs.isLeftDescent_iff).mp hi
  have hsd : cs.BruhatCovBy (s i * d) d := bruhatCovBy_simple_mul_of_isLeftDescent hi
  by_cases ha : cs.IsLeftDescent a i
  · have hai := (cs.isLeftDescent_iff).mp ha
    have h' : cs.BruhatLE (s i * a) (s i * d) := (simple_mul_bruhatLE_simple_mul_iff ha hi).mpr h
    obtain ⟨m₁, m₂, hm, hmid⟩ := ih _ (by omega) h' (by omega) rfl
    have hsa : cs.BruhatCovBy (s i * a) a := bruhatCovBy_simple_mul_of_isLeftDescent ha
    -- middle elements of `[s a, s d]` other than `a` have no descent `s`
    have hF1 : ∀ m, cs.BruhatCovBy (s i * a) m → m ≠ a → ¬cs.IsLeftDescent m i := by
      intro m hm hma hmi
      refine hma ?_
      have := hm.eq_simple_mul hmi (by
        rw [cs.isLeftDescent_iff_not_isLeftDescent_mul, simple_mul_simple_cancel_left]
        exact not_not.mpr ha)
      rw [← simple_mul_simple_cancel_left (cs := cs) (w := m) i, ← this,
        simple_mul_simple_cancel_left]
    let φ : W → W := fun m ↦ if m = a then s i * d else s i * m
    have hφa : φ a = s i * d := ite_eq_left rfl
    have hφ : ∀ m, m ≠ a → φ m = s i * m := fun m hm ↦ ite_eq_right hm
    have hF2 : ∀ m, cs.BruhatCovBy (s i * a) m ∧ cs.BruhatCovBy m (s i * d) →
        cs.BruhatCovBy a (φ m) ∧ cs.BruhatCovBy (φ m) d := by
      rintro m ⟨hm₁, hm₂⟩
      by_cases hma : m = a
      · subst hma
        rw [hφa]
        exact ⟨hm₂, hsd⟩
      · rw [hφ m hma]
        have hmi := hF1 m hm₁ hma
        have hmi' := (cs.not_isLeftDescent_iff).mp hmi
        have hm₁l := hm₁.2
        have hsm : cs.IsLeftDescent (s i * m) i := by
          rw [cs.isLeftDescent_iff_not_isLeftDescent_mul, simple_mul_simple_cancel_left]
          exact hmi
        refine ⟨⟨(simple_mul_bruhatLE_simple_mul_iff ha hsm).mp ?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [simple_mul_simple_cancel_left]; exact hm₁.1
        · omega
        · exact (simple_mul_bruhatLE_iff_of_isLeftDescent hi).mpr (hm₂.1.trans hsd.1)
        · omega
    have hlen : ∀ m, (m = m₁ ∨ m = m₂) → ℓ m = ℓ a := fun m hm ↦ by
      have := ((hmid m).mpr hm).1.2
      omega
    refine ⟨φ m₁, φ m₂, ?_, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
    · have hl₁ := hlen m₁ (.inl rfl)
      have hl₂ := hlen m₂ (.inr rfl)
      by_cases h₁ : m₁ = a
      · have h₂ : m₂ ≠ a := fun h₂ ↦ hm (h₁.trans h₂.symm)
        rw [h₁, hφa, hφ _ h₂]
        intro e
        have := congrArg (s i * ·) e
        simp only [simple_mul_simple_cancel_left] at this
        subst this; omega
      · rw [hφ _ h₁]
        by_cases h₂ : m₂ = a
        · rw [h₂, hφa]
          intro e
          have := congrArg (s i * ·) e
          simp only [simple_mul_simple_cancel_left] at this
          subst this; omega
        · rw [hφ _ h₂]
          intro e
          exact hm (by simpa using congrArg (s i * ·) e)
    · obtain ⟨hx₁, hx₂⟩ := hx
      by_cases hxd : x = s i * d
      · subst hxd
        rcases (hmid a).mp ⟨hsa, hx₁⟩ with e | e
        · left; rw [← e, hφa]
        · right; rw [← e, hφa]
      · have hxi := hx₂.isLeftDescent_of_ne hi hxd
        have hsx : cs.BruhatCovBy (s i * a) (s i * x) ∧ cs.BruhatCovBy (s i * x) (s i * d) :=
          ⟨hx₁.simple_mul ha hxi, hx₂.simple_mul hxi hi⟩
        have hsxa : s i * x ≠ a := by
          intro e
          have hx : x = s i * a := by rw [← e, simple_mul_simple_cancel_left]
          have := hx₁.2
          rw [hx] at this
          omega
        rcases (hmid _).mp hsx with e | e
        · left; rw [← e, hφ _ hsxa, simple_mul_simple_cancel_left]
        · right; rw [← e, hφ _ hsxa, simple_mul_simple_cancel_left]
    · rintro (rfl | rfl)
      · exact hF2 _ ((hmid m₁).mpr (.inl rfl))
      · exact hF2 _ ((hmid m₂).mpr (.inr rfl))
  · have hl' := (cs.not_isLeftDescent_iff).mp ha
    obtain ⟨h₁, h₂⟩ := h.lifting_left hi ha
    refine ⟨s i * a, s i * d, fun e ↦ ?_, fun x ↦ ⟨fun ⟨hx₁, hx₂⟩ ↦ ?_, ?_⟩⟩
    · have := congrArg (s i * ·) e
      simp only [simple_mul_simple_cancel_left] at this
      subst this; omega
    · by_cases hxi : cs.IsLeftDescent x i
      · left
        rw [hx₁.eq_simple_mul hxi ha, simple_mul_simple_cancel_left]
      · right
        exact hx₂.eq_simple_mul hi hxi
    · rintro (rfl | rfl)
      · exact ⟨bruhatCovBy_simple_mul_of_not_isLeftDescent ha, h₂, by omega⟩
      · exact ⟨⟨h₁, by omega⟩, hsd⟩

/-- **Squares in the Bruhat order** ([BGG] Lemma 10.3): if `a ≤ d` and `ℓ(d) = ℓ(a) + 2`, the set
`{x | a ⋖ x ⋖ d}` has exactly two elements. -/
theorem ncard_middle_eq_two {a d : W} (h : cs.BruhatLE a d) (hl : ℓ d = ℓ a + 2) :
    {x | cs.BruhatCovBy a x ∧ cs.BruhatCovBy x d}.ncard = 2 := by
  obtain ⟨b, c, hbc, hmid⟩ := exists_middle_pair h hl
  have : {x | cs.BruhatCovBy a x ∧ cs.BruhatCovBy x d} = {b, c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hmid x
  rw [this, Set.ncard_pair hbc]

/-! ### The BGG signs -/

variable (cs) in
open Classical in
/-- A sign function `ε : W → W → ZMod 2` on the arrows `b ⋖ d` of the Bruhat order such that
every square anticommutes (`CoxeterSystem.bruhatSign_square`), following the inductive
construction in the proof of [BGG] Lemma 10.4 (§11): for `d ≠ 1` let `s` be a (chosen) left
descent of `d`; then `ε(s d, d) = 0` and `ε(b, d) = ε(s b, b) + ε(s b, s d) + 1` for the other `b`
with `ℓ(b) < ℓ(d)`.
(The values for pairs which are not arrows are irrelevant.) -/
noncomputable def bruhatSign (b d : W) : ZMod 2 :=
  if h : ∃ i, cs.IsLeftDescent d i then
    if b = s h.choose * d then 0
    else if hb : ℓ b < ℓ d then
      bruhatSign (s h.choose * b) b + bruhatSign (s h.choose * b) (s h.choose * d) + 1
    else 0
  else 0
termination_by cs.length d
decreasing_by
  · exact hb
  · exact h.choose_spec

/-- The left descent of `d ≠ 1` used in the construction of `ε(·, d)`. -/
private lemma bruhatSign_spec {d : W} (hd : d ≠ 1) :
    ∃ i, cs.IsLeftDescent d i ∧ cs.bruhatSign (s i * d) d = 0 ∧
      ∀ b, b ≠ s i * d → ℓ b < ℓ d →
        cs.bruhatSign b d = cs.bruhatSign (s i * b) b + cs.bruhatSign (s i * b) (s i * d) + 1 := by
  classical
  have h : ∃ i, cs.IsLeftDescent d i := cs.exists_leftDescent_of_ne_one hd
  refine ⟨h.choose, h.choose_spec, ?_, fun b hb hl ↦ ?_⟩
  · rw [bruhatSign.eq_1, dite_eq_left h, ite_eq_left rfl]
  · rw [bruhatSign.eq_1, dite_eq_left h, ite_eq_right hb, dite_eq_left hl]

/-- **The BGG signs** ([BGG] Lemma 10.4, [HumO] §6.8): for every square `a ⋖ b ⋖ d`, `a ⋖ c ⋖ d`
with `b ≠ c` of the Bruhat order, `ε(a, b) + ε(b, d) + ε(a, c) + ε(c, d) = 1` in `ZMod 2`. -/
theorem bruhatSign_square {a b c d : W} (hab : cs.BruhatCovBy a b) (hbd : cs.BruhatCovBy b d)
    (hac : cs.BruhatCovBy a c) (hcd : cs.BruhatCovBy c d) (hbc : b ≠ c) :
    cs.bruhatSign a b + cs.bruhatSign b d + cs.bruhatSign a c + cs.bruhatSign c d = 1 := by
  induction hn : ℓ d using Nat.strong_induction_on generalizing a b c d with
  | _ n ih =>
  subst hn
  have hd1 : d ≠ 1 := by
    rintro rfl
    have := hbd.2
    simp at this
  obtain ⟨i, hi, hsd, hrec⟩ := bruhatSign_spec (cs := cs) hd1
  have hdi := (cs.isLeftDescent_iff).mp hi
  -- the case `b = s d` (the case `c = s d` follows by symmetry)
  have key : ∀ b c, cs.BruhatCovBy a b → cs.BruhatCovBy b d → cs.BruhatCovBy a c →
      cs.BruhatCovBy c d → b ≠ c → b = s i * d →
      cs.bruhatSign a b + cs.bruhatSign b d + cs.bruhatSign a c + cs.bruhatSign c d = 1 := by
    intro b c hab hbd hac hcd hbc hb
    subst hb
    have hcs : c ≠ s i * d := hbc.symm
    have hci := hcd.isLeftDescent_of_ne hi hcs
    have hcl := (cs.isLeftDescent_iff).mp hci
    rw [hsd, hrec c hcs (by have := hcd.2; omega)]
    by_cases has : a = s i * c
    · subst has
      reduce_mod_char
      ring_nf
      reduce_mod_char
    · have hai : cs.IsLeftDescent a i := by
        by_contra hai
        exact has (hac.eq_simple_mul hci hai)
      have hsa := bruhatCovBy_simple_mul_of_isLeftDescent hai
      have hsasc := hac.simple_mul hai hci
      have hscsd := hcd.simple_mul hci hi
      have hne : a ≠ s i * c := has
      have h₁ := ih _ (by omega) hsa hab hsasc hscsd hne rfl
      have h₂ := ih _ (by have := hcd.2; omega) hsa hac hsasc
        (bruhatCovBy_simple_mul_of_isLeftDescent hci) hne rfl
      linear_combination (norm := skip) h₁ + h₂
      ring_nf
      reduce_mod_char
  by_cases hb : b = s i * d
  · exact key b c hab hbd hac hcd hbc hb
  by_cases hc : c = s i * d
  · have := key c b hac hcd hab hbd hbc.symm hc
    linear_combination this
  -- the case `b ≠ s d ≠ c`: the cube
  have hbi := hbd.isLeftDescent_of_ne hi hb
  have hci := hcd.isLeftDescent_of_ne hi hc
  have hbl := (cs.isLeftDescent_iff).mp hbi
  have hcl := (cs.isLeftDescent_iff).mp hci
  have hai : cs.IsLeftDescent a i := by
    by_contra hai
    apply hbc
    rw [← simple_mul_simple_cancel_left (cs := cs) (w := b) i,
      ← simple_mul_simple_cancel_left (cs := cs) (w := c) i,
      ← hab.eq_simple_mul hbi hai, ← hac.eq_simple_mul hci hai]
  have hal := (cs.isLeftDescent_iff).mp hai
  have hasb : a ≠ s i * b := by
    intro e; have := hab.2; rw [e, simple_mul_simple_cancel_left] at hal; rw [e] at this; omega
  have hasc : a ≠ s i * c := by
    intro e; have := hac.2; rw [e, simple_mul_simple_cancel_left] at hal; rw [e] at this; omega
  have hsbsc : s i * b ≠ s i * c := fun e ↦ hbc (by simpa using congrArg (s i * ·) e)
  rw [hrec b hb (by have := hbd.2; omega), hrec c hc (by have := hcd.2; omega)]
  have hsa := bruhatCovBy_simple_mul_of_isLeftDescent hai
  have h₁ := ih _ (by omega) (hab.simple_mul hai hbi) (hbd.simple_mul hbi hi)
    (hac.simple_mul hai hci) (hcd.simple_mul hci hi) hsbsc rfl
  have h₂ := ih _ (by have := hbd.2; omega) hsa hab (hab.simple_mul hai hbi)
    (bruhatCovBy_simple_mul_of_isLeftDescent hbi) hasb rfl
  have h₃ := ih _ (by have := hcd.2; omega) hsa hac (hac.simple_mul hai hci)
    (bruhatCovBy_simple_mul_of_isLeftDescent hci) hasc rfl
  linear_combination (norm := skip) h₁ + h₂ + h₃
  ring_nf
  reduce_mod_char

/-- **The BGG signs** ([BGG] Lemma 10.4): with `ε = bruhatSign`, every square of the
Bruhat order anticommutes for the signs `(-1)^ε` in any ring:
`(-1)^ε(a, b) (-1)^ε(b, d) + (-1)^ε(a, c) (-1)^ε(c, d) = 0`. -/
theorem neg_one_pow_bruhatSign_square {R : Type*} [Ring R] {a b c d : W}
    (hab : cs.BruhatCovBy a b) (hbd : cs.BruhatCovBy b d) (hac : cs.BruhatCovBy a c)
    (hcd : cs.BruhatCovBy c d) (hbc : b ≠ c) :
    (-1 : R) ^ (cs.bruhatSign a b).val * (-1) ^ (cs.bruhatSign b d).val +
      (-1) ^ (cs.bruhatSign a c).val * (-1) ^ (cs.bruhatSign c d).val = 0 := by
  have h := bruhatSign_square hab hbd hac hcd hbc
  have hmul : ∀ x y : ZMod 2, (-1 : R) ^ x.val * (-1) ^ y.val = (-1) ^ (x + y).val := by
    intro x y
    rw [← pow_add, ZMod.val_add, neg_one_pow_eq_pow_mod_two (R := R) (n := x.val + y.val)]
  rw [hmul, hmul]
  have e : cs.bruhatSign a b + cs.bruhatSign b d =
      (cs.bruhatSign a c + cs.bruhatSign c d) + 1 := by
    linear_combination (norm := skip) h
    ring_nf
    reduce_mod_char
  rw [e]
  rw [← hmul, ZMod.val_one, pow_one, mul_neg_one, neg_add_cancel]

end CoxeterSystem
