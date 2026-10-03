/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Basic

/-!
# Tensor products of crystals

We define the tensor product `B₁ ⊗ B₂` of two abstract crystals by the tensor product rule
(signature rule) and prove that it is again a crystal and that the tensor product is associative
up to isomorphism.

## Convention

We use **Kashiwara's convention** ([Kas] §7.3, [HK] Def. 4.5.3 / Thm. 4.4.1),
not the "anti-Kashiwara" convention of Bump–Schilling (which is obtained by swapping the two
tensor factors). For `b₁ ∈ B₁`, `b₂ ∈ B₂`, writing `b₁ ⊗ b₂` for the pair `(b₁, b₂)`:

* `wt(b₁ ⊗ b₂) = wt b₁ + wt b₂`;
* `εᵢ(b₁ ⊗ b₂) = max(εᵢ(b₁), εᵢ(b₂) - ⟨wt b₁, αᵢ^∨⟩)`;
* `φᵢ(b₁ ⊗ b₂) = max(φᵢ(b₂), φᵢ(b₁) + ⟨wt b₂, αᵢ^∨⟩)`;
* `ẽᵢ(b₁ ⊗ b₂) = ẽᵢ b₁ ⊗ b₂` if `φᵢ(b₁) ≥ εᵢ(b₂)`, and `b₁ ⊗ ẽᵢ b₂` if `φᵢ(b₁) < εᵢ(b₂)`;
* `f̃ᵢ(b₁ ⊗ b₂) = f̃ᵢ b₁ ⊗ b₂` if `φᵢ(b₁) > εᵢ(b₂)`, and `b₁ ⊗ f̃ᵢ b₂` if `φᵢ(b₁) ≤ εᵢ(b₂)`;

with `0 ⊗ b₂ = b₁ ⊗ 0 = 0`.

## Main definitions

* `Crystal.tensor C₁ C₂`: the tensor product crystal on `B₁ × B₂`.
* `Crystal.StrictHom.tensorMap`, `Crystal.Equiv.tensorCongr`: functoriality.
* `Crystal.tensorAssoc`: the associativity isomorphism `(B₁ ⊗ B₂) ⊗ B₃ ≅ B₁ ⊗ (B₂ ⊗ B₃)`.
* `Crystal.tensorT`: `T_λ ⊗ T_μ ≅ T_{λ+μ}`.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, Ch. 4.
-/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B₁ B₂ B₃ B₁' B₂' : Type*}
  (C₁ : Crystal D B₁) (C₂ : Crystal D B₂) (C₃ : Crystal D B₃)

/-! ### Arithmetic in `ℤ ⊔ {-∞}` -/

private lemma le_of_lt_add_one' {x y : WithBot ℤ} (h : x < y + 1) : x ≤ y := by
  induction x using WithBot.recBotCoe <;> induction y using WithBot.recBotCoe <;> simp at h ⊢
  norm_cast at h
  omega

private lemma lt_add_one_of_ne_bot {x : WithBot ℤ} (hx : x ≠ ⊥) : x < x + 1 := by
  induction x using WithBot.recBotCoe
  · exact absurd rfl hx
  · norm_cast; omega

variable {C₁ C₂} in
private lemma tensor_f_eq_some_iff (i : ι) (b₁ : B₁) (b₂ : B₂) (c₁ : B₁) (c₂ : B₂) :
    (if C₂.ε i b₂ < C₁.φ i b₁ then (C₁.f i b₁).map (·, b₂) else (C₂.f i b₂).map (b₁, ·)) =
        some (c₁, c₂) ↔
      (if C₂.ε i c₂ ≤ C₁.φ i c₁ then (C₁.e i c₁).map (·, c₂) else (C₂.e i c₂).map (c₁, ·)) =
        some (b₁, b₂) := by
  constructor
  · intro hf
    split_ifs at hf with h
    · obtain ⟨c₁', hc₁, hc⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      rw [C₁.φ_f hc₁] at h
      replace h := le_of_lt_add_one' h
      simp [h, (C₁.f_eq_some_iff i b₁ c₁').mp hc₁]
    · obtain ⟨c₂', hc₂, hc⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have h' : ¬ C₂.ε i c₂' ≤ C₁.φ i b₁ := by
        rw [not_le, C₂.ε_f hc₂]
        exact (not_lt.mp h).trans_lt (lt_add_one_of_ne_bot (C₂.ε_ne_bot_of_f_eq_some hc₂))
      simp [h', (C₂.f_eq_some_iff i b₂ c₂').mp hc₂]
  · intro he
    split_ifs at he with h
    · obtain ⟨b₁', hb₁, hb⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have h' : C₂.ε i c₂ < C₁.φ i b₁' := by
        rw [C₁.φ_e hb₁]
        exact h.trans_lt (lt_add_one_of_ne_bot (C₁.φ_ne_bot_of_e_eq_some hb₁))
      simp [h', (C₁.f_eq_some_iff i b₁' c₁).mpr hb₁]
    · obtain ⟨b₂', hb₂, hb⟩ := Option.map_eq_some_iff.mp he
      simp only [Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have h' : ¬ C₂.ε i b₂' < C₁.φ i c₁ := by
        rw [C₂.ε_e i c₂ b₂' hb₂, not_le] at h
        exact not_lt.mpr (le_of_lt_add_one' h)
      simp [h', (C₂.f_eq_some_iff i b₂' c₂).mpr hb₂]

/-- The tensor product `B₁ ⊗ B₂` of two crystals, with Kashiwara's tensor product rule
([Kas] §7.3, [HK] Def. 4.5.3); see the module docstring for the formulas. The
element `b₁ ⊗ b₂` is the pair `(b₁, b₂)`. The verification of the crystal axioms is our own. -/
def tensor : Crystal D (B₁ × B₂) where
  wt b := C₁.wt b.1 + C₂.wt b.2
  ε i b := max (C₁.ε i b.1) (C₂.ε i b.2 + ((-D.coroot i (C₁.wt b.1) : ℤ) : WithBot ℤ))
  φ i b := max (C₂.φ i b.2) (C₁.φ i b.1 + (D.coroot i (C₂.wt b.2) : WithBot ℤ))
  e i b := if C₂.ε i b.2 ≤ C₁.φ i b.1 then (C₁.e i b.1).map (·, b.2)
    else (C₂.e i b.2).map (b.1, ·)
  f i b := if C₂.ε i b.2 < C₁.φ i b.1 then (C₁.f i b.1).map (·, b.2)
    else (C₂.f i b.2).map (b.1, ·)
  φ_eq i b := by
    rw [C₁.φ_eq, C₂.φ_eq, map_add]
    induction C₁.ε i b.1 using WithBot.recBotCoe <;>
      induction C₂.ε i b.2 using WithBot.recBotCoe <;> simp <;> norm_cast <;> omega
  f_eq_some_iff i b c := tensor_f_eq_some_iff i b.1 b.2 c.1 c.2
  wt_e i b c h := by
    obtain ⟨b₁, b₂⟩ := b
    dsimp only at h ⊢
    split_ifs at h
    · obtain ⟨c₁, hc₁, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [C₁.wt_e i b₁ c₁ hc₁]; abel
    · obtain ⟨c₂, hc₂, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [C₂.wt_e i b₂ c₂ hc₂]; abel
  ε_e i b c h := by
    obtain ⟨b₁, b₂⟩ := b
    dsimp only at h ⊢
    split_ifs at h with hle
    · obtain ⟨c₁, hc₁, rfl⟩ := Option.map_eq_some_iff.mp h
      dsimp only
      have hne := C₁.ε_ne_bot_of_e_eq_some hc₁
      rw [C₁.φ_eq] at hle
      rw [C₁.wt_e i b₁ c₁ hc₁, map_add, D.coroot_root_self]
      rw [C₁.ε_e i b₁ c₁ hc₁] at hle hne ⊢
      generalize C₁.ε i c₁ = x at *
      generalize D.coroot i (C₁.wt b₁) = w at *
      generalize C₂.ε i b₂ = y at *
      induction x using WithBot.recBotCoe
      · simp at hne
      · induction y using WithBot.recBotCoe
        · simp
        · simp at hle ⊢; norm_cast at *; omega
    · obtain ⟨c₂, hc₂, rfl⟩ := Option.map_eq_some_iff.mp h
      dsimp only
      rw [C₁.φ_eq, C₂.ε_e i b₂ c₂ hc₂] at hle
      rw [C₂.ε_e i b₂ c₂ hc₂]
      generalize C₂.ε i c₂ = x at *
      generalize D.coroot i (C₁.wt b₁) = w at *
      generalize C₁.ε i b₁ = y at *
      induction x using WithBot.recBotCoe <;>
        induction y using WithBot.recBotCoe <;> simp at hle ⊢ <;> norm_cast at * <;> omega
  e_eq_none_of_φ_eq_bot i b h := by
    obtain ⟨b₁, b₂⟩ := b
    simp only [max_eq_bot, WithBot.add_eq_bot, WithBot.coe_ne_bot, or_false] at h
    simp [C₁.e_eq_none_of_φ_eq_bot i b₁ h.2, C₂.e_eq_none_of_φ_eq_bot i b₂ h.1]

variable {C₁ C₂ C₃}

@[simp] lemma tensor_wt (b : B₁ × B₂) : (C₁.tensor C₂).wt b = C₁.wt b.1 + C₂.wt b.2 := rfl

lemma tensor_ε (i : ι) (b : B₁ × B₂) : (C₁.tensor C₂).ε i b =
    max (C₁.ε i b.1) (C₂.ε i b.2 + ((-D.coroot i (C₁.wt b.1) : ℤ) : WithBot ℤ)) := rfl

lemma tensor_φ (i : ι) (b : B₁ × B₂) : (C₁.tensor C₂).φ i b =
    max (C₂.φ i b.2) (C₁.φ i b.1 + (D.coroot i (C₂.wt b.2) : WithBot ℤ)) := rfl

lemma tensor_e (i : ι) (b : B₁ × B₂) : (C₁.tensor C₂).e i b =
    if C₂.ε i b.2 ≤ C₁.φ i b.1 then (C₁.e i b.1).map (·, b.2) else (C₂.e i b.2).map (b.1, ·) :=
  rfl

lemma tensor_f (i : ι) (b : B₁ × B₂) : (C₁.tensor C₂).f i b =
    if C₂.ε i b.2 < C₁.φ i b.1 then (C₁.f i b.1).map (·, b.2) else (C₂.f i b.2).map (b.1, ·) :=
  rfl

/-! ### Functoriality -/

variable {C₁' : Crystal D B₁'} {C₂' : Crystal D B₂'}

/-- The tensor product `ψ₁ ⊗ ψ₂` of two strict morphisms. -/
def StrictHom.tensorMap (ψ₁ : StrictHom C₁ C₁') (ψ₂ : StrictHom C₂ C₂') :
    StrictHom (C₁.tensor C₂) (C₁'.tensor C₂') where
  toFun b := (ψ₁ b.1, ψ₂ b.2)
  wt_map b := by simp
  ε_map i b := by simp [tensor_ε]
  e_map i b := by
    simp only [tensor_e, ψ₁.φ_map, ψ₂.ε_apply, ψ₁.e_apply, ψ₂.e_apply]
    split_ifs <;> simp [Option.map_map, Function.comp_def]
  f_map i b := by
    simp only [tensor_f, ψ₁.φ_map, ψ₂.ε_apply, ψ₁.f_apply, ψ₂.f_apply]
    split_ifs <;> simp [Option.map_map, Function.comp_def]

@[simp] lemma StrictHom.tensorMap_apply (ψ₁ : StrictHom C₁ C₁') (ψ₂ : StrictHom C₂ C₂')
    (b : B₁ × B₂) : ψ₁.tensorMap ψ₂ b = (ψ₁ b.1, ψ₂ b.2) := rfl

/-- The tensor product `ψ₁ ⊗ ψ₂` of two isomorphisms of crystals. -/
def Equiv.tensorCongr (ψ₁ : Equiv C₁ C₁') (ψ₂ : Equiv C₂ C₂') :
    Equiv (C₁.tensor C₂) (C₁'.tensor C₂') where
  toEquiv := ψ₁.toEquiv.prodCongr ψ₂.toEquiv
  wt_map := (ψ₁.toStrictHom.tensorMap ψ₂.toStrictHom).wt_map
  ε_map := (ψ₁.toStrictHom.tensorMap ψ₂.toStrictHom).ε_map
  e_map := (ψ₁.toStrictHom.tensorMap ψ₂.toStrictHom).e_map
  f_map := (ψ₁.toStrictHom.tensorMap ψ₂.toStrictHom).f_map

/-! ### Associativity -/

private lemma assoc_e_cond₁ (x₁ x₂ x₃ : WithBot ℤ) (w₁ w₂ : ℤ) :
    (x₃ ≤ max (x₂ + w₂) (x₁ + w₁ + w₂) ∧ x₂ ≤ x₁ + w₁) ↔
      max x₂ (x₃ + ((-w₂ : ℤ) : WithBot ℤ)) ≤ x₁ + w₁ := by
  induction x₁ using WithBot.recBotCoe <;> induction x₂ using WithBot.recBotCoe <;>
    induction x₃ using WithBot.recBotCoe <;> simp <;> norm_cast <;> omega

private lemma assoc_e_cond₂ (x₁ x₂ x₃ : WithBot ℤ) (w₁ w₂ : ℤ) :
    (x₃ ≤ max (x₂ + w₂) (x₁ + w₁ + w₂) ∧ ¬ x₂ ≤ x₁ + w₁) ↔
      (¬ max x₂ (x₃ + ((-w₂ : ℤ) : WithBot ℤ)) ≤ x₁ + w₁ ∧ x₃ ≤ x₂ + w₂) := by
  induction x₁ using WithBot.recBotCoe <;> induction x₂ using WithBot.recBotCoe <;>
    induction x₃ using WithBot.recBotCoe <;> simp
  norm_cast
  omega

private lemma assoc_f_cond₁ (x₁ x₂ x₃ : WithBot ℤ) (w₁ w₂ : ℤ) :
    (x₃ < max (x₂ + w₂) (x₁ + w₁ + w₂) ∧ x₂ < x₁ + w₁) ↔
      max x₂ (x₃ + ((-w₂ : ℤ) : WithBot ℤ)) < x₁ + w₁ := by
  induction x₁ using WithBot.recBotCoe <;> induction x₂ using WithBot.recBotCoe <;>
    induction x₃ using WithBot.recBotCoe <;> simp <;> norm_cast <;> omega

private lemma assoc_f_cond₂ (x₁ x₂ x₃ : WithBot ℤ) (w₁ w₂ : ℤ) :
    (x₃ < max (x₂ + w₂) (x₁ + w₁ + w₂) ∧ ¬ x₂ < x₁ + w₁) ↔
      (¬ max x₂ (x₃ + ((-w₂ : ℤ) : WithBot ℤ)) < x₁ + w₁ ∧ x₃ < x₂ + w₂) := by
  induction x₁ using WithBot.recBotCoe <;> induction x₂ using WithBot.recBotCoe <;>
    induction x₃ using WithBot.recBotCoe <;> simp
  norm_cast
  omega

variable (C₁ C₂ C₃) in
/-- The tensor product of crystals is associative: `(b₁ ⊗ b₂) ⊗ b₃ ↦ b₁ ⊗ (b₂ ⊗ b₃)` is an
isomorphism of crystals `(B₁ ⊗ B₂) ⊗ B₃ ≅ B₁ ⊗ (B₂ ⊗ B₃)` ([Kas] Lemma 7.1).
-/
def tensorAssoc : Equiv ((C₁.tensor C₂).tensor C₃) (C₁.tensor (C₂.tensor C₃)) where
  toEquiv := _root_.Equiv.prodAssoc B₁ B₂ B₃
  wt_map b := by simp [add_assoc]
  ε_map i b := by
    obtain ⟨⟨b₁, b₂⟩, b₃⟩ := b
    simp only [tensor_ε, tensor_wt, _root_.Equiv.toFun_as_coe, _root_.Equiv.prodAssoc_apply,
      map_add]
    generalize C₁.ε i b₁ = x₁
    generalize C₂.ε i b₂ = x₂
    generalize C₃.ε i b₃ = x₃
    induction x₁ using WithBot.recBotCoe <;> induction x₂ using WithBot.recBotCoe <;>
      induction x₃ using WithBot.recBotCoe <;> simp <;> norm_cast <;> omega
  e_map i b := by
    obtain ⟨⟨b₁, b₂⟩, b₃⟩ := b
    simp only [tensor_e, tensor_ε, tensor_φ, C₁.φ_eq, C₂.φ_eq, add_assoc]
    have h₁ := assoc_e_cond₁ (C₁.ε i b₁) (C₂.ε i b₂) (C₃.ε i b₃) (D.coroot i (C₁.wt b₁))
      (D.coroot i (C₂.wt b₂))
    have h₂ := assoc_e_cond₂ (C₁.ε i b₁) (C₂.ε i b₂) (C₃.ε i b₃) (D.coroot i (C₁.wt b₁))
      (D.coroot i (C₂.wt b₂))
    simp only [add_assoc] at h₁ h₂
    split_ifs <;> first | tauto | simp [Option.map_map, Function.comp_def]
  f_map i b := by
    obtain ⟨⟨b₁, b₂⟩, b₃⟩ := b
    simp only [tensor_f, tensor_ε, tensor_φ, C₁.φ_eq, C₂.φ_eq, add_assoc]
    have h₁ := assoc_f_cond₁ (C₁.ε i b₁) (C₂.ε i b₂) (C₃.ε i b₃) (D.coroot i (C₁.wt b₁))
      (D.coroot i (C₂.wt b₂))
    have h₂ := assoc_f_cond₂ (C₁.ε i b₁) (C₂.ε i b₂) (C₃.ε i b₃) (D.coroot i (C₁.wt b₁))
      (D.coroot i (C₂.wt b₂))
    simp only [add_assoc] at h₁ h₂
    split_ifs <;> first | tauto | simp [Option.map_map, Function.comp_def]

@[simp] lemma tensorAssoc_apply (b : (B₁ × B₂) × B₃) :
    tensorAssoc C₁ C₂ C₃ b = (b.1.1, (b.1.2, b.2)) := rfl

/-! ### The crystals `T_λ` -/

variable (D) in
/-- `T_λ ⊗ T_μ ≅ T_{λ + μ}` ([Kas] (7.11)). -/
def tensorT (μ ν : X) : Equiv ((T D μ).tensor (T D ν)) (T D (μ + ν)) where
  toEquiv := _root_.Equiv.prodPUnit Unit
  wt_map _ := rfl
  ε_map _ _ := by simp [tensor_ε, T]
  e_map _ _ := by simp [tensor_e, T]
  f_map _ _ := by simp [tensor_f, T]

end Crystal
