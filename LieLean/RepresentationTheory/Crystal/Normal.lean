/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Tensor

/-!
# Seminormal crystals

A crystal is *seminormal* if `εᵢ(b) = max {n ≥ 0 | ẽᵢⁿ b ≠ 0}` and
`φᵢ(b) = max {n ≥ 0 | f̃ᵢⁿ b ≠ 0}` for all `i` and `b` ([Kas] §7.6, [HK] §4.5, where it is
called *semiregular*).
(A crystal is *normal* if moreover it is a disjoint union of crystals of integrable highest
weight modules for all Levi subalgebras of finite type; normality is not treated here.)

## Main definitions

* `Crystal.IsSeminormal`: seminormality, in the form "`ẽᵢⁿ b ≠ 0 ↔ n ≤ εᵢ(b)` and
  `f̃ᵢⁿ b ≠ 0 ↔ n ≤ φᵢ(b)` for all `n ∈ ℕ`".

## Main results

* `Crystal.isSeminormal_iff_isGreatest`: the definition agrees with the formulation by maxima.
* `Crystal.isSeminormal_iff`: a local characterization: `εᵢ, φᵢ ≥ 0`, `ẽᵢ b = 0 → εᵢ(b) = 0` and
  `f̃ᵢ b = 0 → φᵢ(b) = 0`.
* `Crystal.IsSeminormal.tensor`: the tensor product of seminormal crystals is seminormal.
* `Crystal.isSeminormal_trivial`: the crystal `C = {c}` is seminormal.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, Ch. 4.
-/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B₁ B₂ : Type*}
  (C : Crystal D B) {i : ι} {b : B}

/-- A crystal is seminormal ([Kas] §7.6, [HK] §4.5) if for all `i` and `b`,
`εᵢ(b) = max {n ≥ 0 | ẽᵢⁿ b ≠ 0}` and `φᵢ(b) = max {n ≥ 0 | f̃ᵢⁿ b ≠ 0}`. We state this as:
`ẽᵢⁿ b ≠ 0 ↔ n ≤ εᵢ(b)` and `f̃ᵢⁿ b ≠ 0 ↔ n ≤ φᵢ(b)` for all `n ∈ ℕ`; see
`Crystal.isSeminormal_iff_isGreatest` for the equivalence with the formulation by maxima. -/
def IsSeminormal : Prop :=
  ∀ i b (n : ℕ), ((C.eIter i n b).isSome ↔ (n : WithBot ℤ) ≤ C.ε i b) ∧
    ((C.fIter i n b).isSome ↔ (n : WithBot ℤ) ≤ C.φ i b)

lemma eIter_eq_none_of_le {m n : ℕ} (hmn : m ≤ n) (h : C.eIter i m b = none) :
    C.eIter i n b = none := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => rw [eIter_succ', ih, Option.bind_none]

lemma fIter_eq_none_of_le {m n : ℕ} (hmn : m ≤ n) (h : C.fIter i m b = none) :
    C.fIter i n b = none := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => rw [fIter_succ', ih, Option.bind_none]

lemma isSome_eIter_of_le {m n : ℕ} (hmn : m ≤ n) (h : (C.eIter i n b).isSome) :
    (C.eIter i m b).isSome := by
  by_contra h'
  simp [C.eIter_eq_none_of_le hmn (Option.not_isSome_iff_eq_none.mp h')] at h

lemma isSome_fIter_of_le {m n : ℕ} (hmn : m ≤ n) (h : (C.fIter i n b).isSome) :
    (C.fIter i m b).isSome := by
  by_contra h'
  simp [C.fIter_eq_none_of_le hmn (Option.not_isSome_iff_eq_none.mp h')] at h

private lemma nonneg_iff_exists {x : WithBot ℤ} : 0 ≤ x ↔ ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    refine ⟨fun h ↦ ⟨a.toNat, ?_⟩, ?_⟩
    · have h' : (0 : ℤ) ≤ a := by exact_mod_cast h
      rw [← WithBot.coe_natCast, Int.toNat_of_nonneg h']
    rintro ⟨n, hn⟩
    rw [hn]; exact_mod_cast n.zero_le

private lemma natCast_le_iff_isGreatest {x : WithBot ℤ} {s : Set ℕ} (h0 : 0 ∈ s)
    (hs : ∀ m n, m ≤ n → n ∈ s → m ∈ s) :
    (∀ n : ℕ, n ∈ s ↔ (n : WithBot ℤ) ≤ x) ↔ ∃ n : ℕ, x = n ∧ IsGreatest s n := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := nonneg_iff_exists.mp (by simpa using (h 0).mp h0)
    refine ⟨n, rfl, (h n).mpr le_rfl, fun m hm ↦ ?_⟩
    exact_mod_cast (h m).mp hm
  · rintro ⟨n, rfl, hn, hn'⟩ m
    exact ⟨fun hm ↦ by exact_mod_cast hn' hm, fun hm ↦ hs m n (by exact_mod_cast hm) hn⟩

/-- Seminormality in the form of [Kas] §7.6: `εᵢ(b) = max {n ≥ 0 | ẽᵢⁿ b ≠ 0}` and
`φᵢ(b) = max {n ≥ 0 | f̃ᵢⁿ b ≠ 0}` (in particular these maxima exist). -/
theorem isSeminormal_iff_isGreatest : C.IsSeminormal ↔ ∀ i b,
    (∃ n : ℕ, C.ε i b = n ∧ IsGreatest {m | (C.eIter i m b).isSome} n) ∧
      ∃ n : ℕ, C.φ i b = n ∧ IsGreatest {m | (C.fIter i m b).isSome} n := by
  refine forall_congr' fun i ↦ forall_congr' fun b ↦ ?_
  rw [forall_and]
  exact and_congr
    (natCast_le_iff_isGreatest rfl fun m n hmn hn ↦ C.isSome_eIter_of_le hmn hn)
    (natCast_le_iff_isGreatest rfl fun m n hmn hn ↦ C.isSome_fIter_of_le hmn hn)

private lemma isSome_eIter_iff (h0 : ∀ b, 0 ≤ C.ε i b)
    (hnone : ∀ b, C.e i b = none → C.ε i b = 0) (n : ℕ) (b : B) :
    (C.eIter i n b).isSome ↔ (n : WithBot ℤ) ≤ C.ε i b := by
  induction n generalizing b with
  | zero => simpa using h0 b
  | succ n ih =>
    rw [eIter_succ]
    cases he : C.e i b with
    | none =>
      rw [hnone b he]
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff, not_le]
      exact_mod_cast n.succ_pos
    | some b' =>
      rw [Option.bind_some, ih, C.ε_e i b b' he]
      induction C.ε i b' using WithBot.recBotCoe
      · simp
      · simp only [Nat.cast_add, Nat.cast_one]
        norm_cast
        omega

private lemma isSome_fIter_iff (h0 : ∀ b, 0 ≤ C.φ i b)
    (hnone : ∀ b, C.f i b = none → C.φ i b = 0) (n : ℕ) (b : B) :
    (C.fIter i n b).isSome ↔ (n : WithBot ℤ) ≤ C.φ i b := by
  induction n generalizing b with
  | zero => simpa using h0 b
  | succ n ih =>
    rw [fIter_succ]
    cases hf : C.f i b with
    | none =>
      rw [hnone b hf]
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff, not_le]
      exact_mod_cast n.succ_pos
    | some b' =>
      rw [Option.bind_some, ih, C.φ_f hf]
      induction C.φ i b' using WithBot.recBotCoe
      · simp
      · simp only [Nat.cast_add, Nat.cast_one]
        norm_cast
        omega

/-- A local characterization of seminormality: `εᵢ(b), φᵢ(b) ≥ 0`, and `εᵢ(b) = 0` (resp.
`φᵢ(b) = 0`) whenever `ẽᵢ b = 0` (resp. `f̃ᵢ b = 0`). -/
theorem isSeminormal_iff : C.IsSeminormal ↔ ∀ i b, 0 ≤ C.ε i b ∧ 0 ≤ C.φ i b ∧
    (C.e i b = none → C.ε i b = 0) ∧ (C.f i b = none → C.φ i b = 0) := by
  constructor
  · intro h i b
    have h0e := (h i b 0).1.mp (by simp)
    have h0f := (h i b 0).2.mp (by simp)
    simp only [Nat.cast_zero] at h0e h0f
    refine ⟨h0e, h0f, fun he ↦ ?_, fun hf ↦ ?_⟩
    · have := (h i b 1).1
      simp only [eIter_one, he, Option.isSome_none, Bool.false_eq_true, false_iff, not_le,
        Nat.cast_one] at this
      obtain ⟨n, hn⟩ := nonneg_iff_exists.mp h0e
      rw [hn] at this ⊢
      norm_cast at this ⊢
      omega
    · have := (h i b 1).2
      simp only [fIter_one, hf, Option.isSome_none, Bool.false_eq_true, false_iff, not_le,
        Nat.cast_one] at this
      obtain ⟨n, hn⟩ := nonneg_iff_exists.mp h0f
      rw [hn] at this ⊢
      norm_cast at this ⊢
      omega
  · intro h i b n
    exact ⟨C.isSome_eIter_iff (fun b ↦ (h i b).1) (fun b ↦ (h i b).2.2.1) n b,
      C.isSome_fIter_iff (fun b ↦ (h i b).2.1) (fun b ↦ (h i b).2.2.2) n b⟩

namespace IsSeminormal

variable {C}

lemma ε_nonneg (hC : C.IsSeminormal) (i : ι) (b : B) : 0 ≤ C.ε i b :=
  ((C.isSeminormal_iff.mp hC) i b).1

lemma φ_nonneg (hC : C.IsSeminormal) (i : ι) (b : B) : 0 ≤ C.φ i b :=
  ((C.isSeminormal_iff.mp hC) i b).2.1

lemma ε_eq_zero (hC : C.IsSeminormal) (h : C.e i b = none) : C.ε i b = 0 :=
  ((C.isSeminormal_iff.mp hC) i b).2.2.1 h

lemma φ_eq_zero (hC : C.IsSeminormal) (h : C.f i b = none) : C.φ i b = 0 :=
  ((C.isSeminormal_iff.mp hC) i b).2.2.2 h

lemma exists_ε_eq (hC : C.IsSeminormal) (i : ι) (b : B) : ∃ n : ℕ, C.ε i b = n :=
  nonneg_iff_exists.mp (hC.ε_nonneg i b)

lemma exists_φ_eq (hC : C.IsSeminormal) (i : ι) (b : B) : ∃ n : ℕ, C.φ i b = n :=
  nonneg_iff_exists.mp (hC.φ_nonneg i b)

lemma isSome_eIter_iff (hC : C.IsSeminormal) (n : ℕ) :
    (C.eIter i n b).isSome ↔ (n : WithBot ℤ) ≤ C.ε i b :=
  (hC i b n).1

lemma isSome_fIter_iff (hC : C.IsSeminormal) (n : ℕ) :
    (C.fIter i n b).isSome ↔ (n : WithBot ℤ) ≤ C.φ i b :=
  (hC i b n).2

variable {C₁ : Crystal D B₁} {C₂ : Crystal D B₂}

/-- The tensor product of two seminormal crystals is seminormal (for seminormality see [Kas]
§7.6). -/
theorem tensor (h₁ : C₁.IsSeminormal) (h₂ : C₂.IsSeminormal) : (C₁.tensor C₂).IsSeminormal := by
  rw [isSeminormal_iff]
  rintro i ⟨b₁, b₂⟩
  refine ⟨le_max_of_le_left (h₁.ε_nonneg i b₁), le_max_of_le_left (h₂.φ_nonneg i b₂),
    fun he ↦ ?_, fun hf ↦ ?_⟩
  · rw [tensor_e] at he
    rw [tensor_ε]
    dsimp only at he ⊢
    split_ifs at he with h
    · have h0 := h₁.ε_eq_zero (Option.map_eq_none_iff.mp he)
      rw [C₁.φ_eq, h0] at h
      rw [h0]
      obtain ⟨n, hn⟩ := h₂.exists_ε_eq i b₂
      rw [hn] at h ⊢
      simp only [zero_add] at h
      norm_cast at h ⊢
      simp only [max_eq_left_iff]
      exact_mod_cast (by omega : (n : ℤ) + -D.coroot i (C₁.wt b₁) ≤ 0)
    · have h0 := h₂.ε_eq_zero (Option.map_eq_none_iff.mp he)
      rw [h0] at h
      exact absurd (h₁.φ_nonneg i b₁) h
  · rw [tensor_f] at hf
    rw [tensor_φ]
    dsimp only at hf ⊢
    split_ifs at hf with h
    · have h0 := h₁.φ_eq_zero (Option.map_eq_none_iff.mp hf)
      rw [h0] at h
      exact absurd (h₂.ε_nonneg i b₂) (not_le.mpr h)
    · have h0 := h₂.φ_eq_zero (Option.map_eq_none_iff.mp hf)
      have h2 := C₂.φ_eq i b₂
      rw [h0] at h2
      rw [h0]
      obtain ⟨n, hn⟩ := h₂.exists_ε_eq i b₂
      obtain ⟨m, hm⟩ := h₁.exists_φ_eq i b₁
      rw [hn] at h h2
      rw [hm] at h ⊢
      norm_cast at h h2 ⊢
      simp only [max_eq_left_iff]
      exact_mod_cast (by omega : (m : ℤ) + D.coroot i (C₂.wt b₂) ≤ 0)

end IsSeminormal

/-- The crystal `C = {c}` is seminormal. -/
theorem isSeminormal_trivial : (trivial D).IsSeminormal := by
  rw [isSeminormal_iff]
  intro i b
  simp [trivial]

end Crystal
