/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Isomorphism

/-!
# Highest weight elements of tensor products of crystals

Hong–Kang, GSM 42, Corollary 4.4.4: in the tensor product `B₁ ⊗ B₂` of seminormal crystals
(Kashiwara's convention), `b₁ ⊗ b₂` is a maximal vector (`ẽᵢ (b₁ ⊗ b₂) = 0` for all `i`) if and
only if `ẽᵢ b₁ = 0` and `εᵢ(b₂) ≤ ⟨hᵢ, wt b₁⟩` for all `i`; consequently, if
`b₁ ⊗ ⋯ ⊗ b_N` is maximal, then so is every `b₁ ⊗ ⋯ ⊗ b_k`.

Hong–Kang state this for the crystals of crystal bases of modules in `𝒪_int`; for these the
crystal of a tensor product of crystal bases is the tensor product of the crystals
(`LieLean.QuantumGroup.TensorModule.nonempty_crystalEquiv`, where the factors are exchanged since
the library uses Lusztig's coproduct), and those crystals are seminormal. The statement here is
for arbitrary seminormal crystals.

## Main results

* `Crystal.IsSeminormal.tensor_e_eq_none_iff`: `ẽᵢ (b₁ ⊗ b₂) = 0` iff `ẽᵢ b₁ = 0` and
  `εᵢ(b₂) ≤ ⟨hᵢ, wt b₁⟩`.
* `Crystal.IsSeminormal.isHighestWeight_tensor_iff`: **Corollary 4.4.4 (1)**.
* `Crystal.IsSeminormal.isHighestWeight_fst_of_isHighestWeight_tensor`: **Corollary 4.4.4 (2)**,
  stated for two factors; the `N`-fold statement follows by applying it to
  `(b₁ ⊗ ⋯ ⊗ b_{N-1}) ⊗ b_N`.

## References

* J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, AMS 2002,
  Corollary 4.4.4.
-/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B₁ B₂ : Type*}
  {C : Crystal D B} {C₁ : Crystal D B₁} {C₂ : Crystal D B₂}

namespace IsSeminormal

/-- In a seminormal crystal, `ẽᵢ b ≠ 0` as soon as `εᵢ(b) > 0`. -/
lemma e_ne_none_of_pos (hC : C.IsSeminormal) {i : ι} {b : B} (h : 0 < C.ε i b) :
    C.e i b ≠ none := by
  have h1 := (hC.isSome_eIter_iff (i := i) (b := b) 1).mpr (by
    induction hε : C.ε i b using WithBot.recBotCoe with
    | bot => rw [hε] at h; exact absurd h (not_lt_bot)
    | coe a =>
      rw [hε] at h
      have : (0 : ℤ) < a := by exact_mod_cast h
      exact_mod_cast this)
  rw [eIter_one] at h1
  exact Option.isSome_iff_ne_none.mp h1

/-- **The tensor product rule for `ẽᵢ = 0`**: in a tensor product of seminormal crystals,
`ẽᵢ (b₁ ⊗ b₂) = 0` iff `ẽᵢ b₁ = 0` and `εᵢ(b₂) ≤ ⟨hᵢ, wt b₁⟩`. -/
theorem tensor_e_eq_none_iff (h₁ : C₁.IsSeminormal) (h₂ : C₂.IsSeminormal) (i : ι) (b₁ : B₁)
    (b₂ : B₂) :
    (C₁.tensor C₂).e i (b₁, b₂) = none ↔
      C₁.e i b₁ = none ∧ C₂.ε i b₂ ≤ (D.coroot i (C₁.wt b₁) : WithBot ℤ) := by
  rw [tensor_e]
  dsimp only
  constructor
  · intro h
    split_ifs at h with hc
    · have he : C₁.e i b₁ = none := Option.map_eq_none_iff.mp h
      refine ⟨he, ?_⟩
      rwa [C₁.φ_eq, h₁.ε_eq_zero he, zero_add] at hc
    · exfalso
      have he : C₂.e i b₂ = none := Option.map_eq_none_iff.mp h
      rw [h₂.ε_eq_zero he] at hc
      exact hc (h₁.φ_nonneg i b₁)
  · rintro ⟨he, hle⟩
    have hc : C₂.ε i b₂ ≤ C₁.φ i b₁ := by rwa [C₁.φ_eq, h₁.ε_eq_zero he, zero_add]
    simp [hc, he]

/-- **Hong–Kang, Corollary 4.4.4 (1).** In a tensor product of seminormal crystals, `b₁ ⊗ b₂` is
a maximal vector iff `ẽᵢ b₁ = 0` and `εᵢ(b₂) ≤ ⟨hᵢ, wt b₁⟩` for all `i`. -/
theorem isHighestWeight_tensor_iff (h₁ : C₁.IsSeminormal) (h₂ : C₂.IsSeminormal) (b₁ : B₁)
    (b₂ : B₂) :
    (C₁.tensor C₂).IsHighestWeight (b₁, b₂) ↔
      C₁.IsHighestWeight b₁ ∧ ∀ i, C₂.ε i b₂ ≤ (D.coroot i (C₁.wt b₁) : WithBot ℤ) := by
  simp only [IsHighestWeight, tensor_e_eq_none_iff h₁ h₂, forall_and]

/-- **Hong–Kang, Corollary 4.4.4 (2)**, for two factors: if `b₁ ⊗ b₂` is a maximal vector, so
is `b₁`. Applied to `(b₁ ⊗ ⋯ ⊗ b_{N-1}) ⊗ b_N` and iterated, it shows that `b₁ ⊗ ⋯ ⊗ b_k` is
maximal for every `k ≤ N` when `b₁ ⊗ ⋯ ⊗ b_N` is. -/
theorem isHighestWeight_fst_of_isHighestWeight_tensor (h₁ : C₁.IsSeminormal)
    (h₂ : C₂.IsSeminormal) {b : B₁ × B₂} (hb : (C₁.tensor C₂).IsHighestWeight b) :
    C₁.IsHighestWeight b.1 :=
  ((isHighestWeight_tensor_iff h₁ h₂ b.1 b.2).mp hb).1

end IsSeminormal

end Crystal
