/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.KashiwaraSaito
import LieLean.RepresentationTheory.Crystal.WeylGroupAction

/-!
# Similarities of crystals

For a positive integer `m`, an `m`-similarity `σ : B₁ → B₂` between crystals multiplies weights and
the `εᵢ`, `φᵢ` by `m` and intertwines `ẽᵢ`, `f̃ᵢ` with `ẽᵢᵐ`, `f̃ᵢᵐ` ([Kas96] Thm. 3.1, (3.1) and
(3.2)). Littelmann's stretching of paths `π ↦ mπ` is an example, and so is Kashiwara's map
`B(λ) → B(mλ)` ([Kas96] Thm. 3.1).

## Main definitions

* `Crystal.stretchWord m w`: the word `w` with every letter repeated `m` times.
* `Crystal.Similarity C₁ C₂ m`: `m`-similarities `C₁ → C₂`.

## Main results

* `Crystal.Similarity.fWord_stretchWord`: `f̃_{wᵐ} σ(b) = σ(f̃_w b)` for every word `w`.
* `Crystal.Similarity.tensorMap`: the tensor product of two `m`-similarities is an
  `m`-similarity.
* `Crystal.KSData.similarity`: if `C` and `C'` carry Kashiwara–Saito data (`Crystal.KSData`) and
  `εᵢ(b) = 0` exactly when `ẽᵢ b = 0`, then `f̃_w b₀ ↦ f̃_{wᵐ} b₀'` is a well-defined injective
  `m`-similarity `C → C'`. Applied to `B(∞)` this is [Kas96] Thm. 3.2.

## Proof of `Crystal.KSData.similarity`

[Kas96] embeds `B(∞)` into an infinite tensor product `⋯ ⊗ B_{i₂} ⊗ B_{i₁}` and scales each
factor `bᵢ(n) ↦ bᵢ(mn)`. We argue instead as in `Crystal.KSData.equiv`, by induction on the
length of words: `Ψᵢ(f̃_w b₀) = f̃_u b₀ ⊗ bᵢ(n)` gives `Ψᵢ(f̃_{wᵐ} b₀') = f̃_{uᵐ} b₀' ⊗ bᵢ(mn)`,
because with all `εⱼ`, `φⱼ` multiplied by `m` the tensor product rule makes `f̃ⱼᵐ` act `m` times
on the same factor.

## References

* [Kas96] M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194 (1996), 177–186, §3.
-/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X}
  {B B' B₁ B₂ B₃ B₁' B₂' : Type*}

/-! ### Words -/

/-- The word `w` with every letter repeated `m` times. -/
def stretchWord (m : ℕ) (w : List ι) : List ι := w.flatMap (List.replicate m)

@[simp] lemma stretchWord_nil (m : ℕ) : stretchWord m ([] : List ι) = [] := rfl

lemma stretchWord_cons (m : ℕ) (j : ι) (w : List ι) :
    stretchWord m (j :: w) = List.replicate m j ++ stretchWord m w := rfl

lemma length_stretchWord (m : ℕ) (w : List ι) : (stretchWord m w).length = m * w.length := by
  induction w with
  | nil => simp
  | cons j w ih => rw [stretchWord_cons, List.length_append, List.length_replicate, ih,
      List.length_cons, mul_add, mul_one, add_comm]

lemma stretchWord_append (m : ℕ) (w w' : List ι) :
    stretchWord m (w ++ w') = stretchWord m w ++ stretchWord m w' := by
  simp [stretchWord]

lemma stretchWord_replicate (m n : ℕ) (j : ι) :
    stretchWord m (List.replicate n j) = List.replicate (m * n) j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, stretchWord_cons, ih, Nat.mul_succ, Nat.add_comm, List.replicate_add]

lemma stretchWord_mul (m n : ℕ) (w : List ι) :
    stretchWord (m * n) w = stretchWord m (stretchWord n w) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [stretchWord_cons, stretchWord_cons, stretchWord_append, ih, stretchWord_replicate]

variable (C : Crystal D B) {C₁ : Crystal D B₁} {C₂ : Crystal D B₂} {C₃ : Crystal D B₃}

lemma fWord_append (l₁ l₂ : List ι) (b : B) :
    C.fWord (l₁ ++ l₂) b = (C.fWord l₂ b).bind (C.fWord l₁) := by
  induction l₁ with
  | nil => rw [List.nil_append]; cases C.fWord l₂ b <;> rfl
  | cons i l ih => rw [List.cons_append, fWord_cons, ih, Option.bind_assoc]; rfl

lemma fWord_replicate (i : ι) (n : ℕ) (b : B) : C.fWord (List.replicate n i) b = C.fIter i n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, fWord_cons, ih, fIter_succ']

lemma fWord_stretchWord_cons (m : ℕ) (j : ι) (w : List ι) (b : B) :
    C.fWord (stretchWord m (j :: w)) b = (C.fWord (stretchWord m w) b).bind (C.fIter j m) := by
  rw [stretchWord_cons, fWord_append]
  congr 1
  funext x
  exact C.fWord_replicate j m x

/-! ### Arithmetic in `ℤ ∪ {-∞}` -/

section Arith

lemma nsmul_bot_withBot {m : ℕ} (hm : 0 < m) : m • (⊥ : WithBot ℤ) = ⊥ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [succ_nsmul, WithBot.add_bot]

lemma nsmul_coe_withBot (m : ℕ) (z : ℤ) : m • (z : WithBot ℤ) = ((m * z : ℤ) : WithBot ℤ) := by
  rw [← WithBot.coe_nsmul, nsmul_eq_mul]

lemma nsmul_max_add_withBot {m : ℕ} (hm : 0 < m) (a b : WithBot ℤ) (z : ℤ) :
    m • max a (b + (z : WithBot ℤ)) = max (m • a) (m • b + ((m * z : ℤ) : WithBot ℤ)) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => simp [nsmul_bot_withBot hm]
    | coe b =>
      rw [← WithBot.coe_add, max_eq_right bot_le, nsmul_coe_withBot, nsmul_coe_withBot,
        nsmul_bot_withBot hm, ← WithBot.coe_add, max_eq_right bot_le, mul_add]
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp [nsmul_bot_withBot hm]
    | coe b =>
      rw [← WithBot.coe_add, ← WithBot.coe_max, nsmul_coe_withBot, nsmul_coe_withBot,
        nsmul_coe_withBot, ← WithBot.coe_add, ← WithBot.coe_max,
        mul_max_of_nonneg _ _ (by positivity : (0 : ℤ) ≤ m), mul_add]

lemma nsmul_lt_of_lt_of_eq_add {m k : ℕ} (hk : k < m) {a b c : WithBot ℤ} (hab : a < b)
    (hc : m • b = c + k) : m • a < c := by
  induction b using WithBot.recBotCoe with
  | bot => exact absurd hab not_lt_bot
  | coe b =>
    induction c using WithBot.recBotCoe with
    | bot => rw [nsmul_coe_withBot, WithBot.bot_add] at hc; exact absurd hc WithBot.coe_ne_bot
    | coe c =>
      rw [nsmul_coe_withBot, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at hc
      induction a using WithBot.recBotCoe with
      | bot => rw [nsmul_bot_withBot (by omega)]; exact WithBot.bot_lt_coe c
      | coe a =>
        rw [nsmul_coe_withBot, WithBot.coe_lt_coe]
        have hab' : a < b := by exact_mod_cast hab
        have : (m : ℤ) * (a + 1) ≤ m * b :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        have hk' : (k : ℤ) < m := by exact_mod_cast hk
        linarith

lemma nsmul_le_nsmul_add_of_le (m k : ℕ) {a b : WithBot ℤ} (hab : a ≤ b) :
    m • a ≤ m • b + k :=
  (nsmul_le_nsmul_right hab m).trans (le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le k))

lemma not_lt_nsmul_of_le {m k : ℕ} {a b c : WithBot ℤ} (hab : a ≤ b) (hc : c = m • b + k) :
    ¬ c < m • a := by
  rw [not_lt, hc]; exact nsmul_le_nsmul_add_of_le m k hab

lemma not_le_nsmul_of_lt {m k : ℕ} (hk : k < m) {a b c : WithBot ℤ} (hab : a < b)
    (hc : m • b = c + k) : ¬ c ≤ m • a := by
  rw [not_le]; exact nsmul_lt_of_lt_of_eq_add hk hab hc

end Arith

/-! ### Iterates on tensor products -/

section TensorIter

variable (i : ι)

lemma tensor_fIter_left (n : ℕ) (x : B₁) (y : B₂)
    (h : ∀ k < n, ∀ x', C₁.fIter i k x = some x' → C₂.ε i y < C₁.φ i x') :
    (C₁.tensor C₂).fIter i n (x, y) = (C₁.fIter i n x).map (·, y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fIter_succ', ih fun k hk ↦ h k (by omega), fIter_succ']
    cases hx : C₁.fIter i n x with
    | none => rfl
    | some x' =>
      simp only [Option.map_some, Option.bind_some]
      simp only [tensor_f, h n (by omega) x' hx, ↓reduceIte]

lemma tensor_fIter_right (n : ℕ) (x : B₁) (y : B₂)
    (h : ∀ k < n, ∀ y', C₂.fIter i k y = some y' → ¬ C₂.ε i y' < C₁.φ i x) :
    (C₁.tensor C₂).fIter i n (x, y) = (C₂.fIter i n y).map (x, ·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fIter_succ', ih fun k hk ↦ h k (by omega), fIter_succ']
    cases hy : C₂.fIter i n y with
    | none => rfl
    | some y' =>
      simp only [Option.map_some, Option.bind_some]
      simp only [tensor_f, h n (by omega) y' hy, ↓reduceIte]

lemma tensor_eIter_left (n : ℕ) (x : B₁) (y : B₂)
    (h : ∀ k < n, ∀ x', C₁.eIter i k x = some x' → C₂.ε i y ≤ C₁.φ i x') :
    (C₁.tensor C₂).eIter i n (x, y) = (C₁.eIter i n x).map (·, y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [eIter_succ', ih fun k hk ↦ h k (by omega), eIter_succ']
    cases hx : C₁.eIter i n x with
    | none => rfl
    | some x' =>
      simp only [Option.map_some, Option.bind_some]
      simp only [tensor_e, h n (by omega) x' hx, ↓reduceIte]

lemma tensor_eIter_right (n : ℕ) (x : B₁) (y : B₂)
    (h : ∀ k < n, ∀ y', C₂.eIter i k y = some y' → ¬ C₂.ε i y' ≤ C₁.φ i x) :
    (C₁.tensor C₂).eIter i n (x, y) = (C₂.eIter i n y).map (x, ·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [eIter_succ', ih fun k hk ↦ h k (by omega), eIter_succ']
    cases hy : C₂.eIter i n y with
    | none => rfl
    | some y' =>
      simp only [Option.map_some, Option.bind_some]
      simp only [tensor_e, h n (by omega) y' hy, ↓reduceIte]

end TensorIter

/-! ### Similarities -/

variable (C₁ C₂) in
/-- An `m`-similarity of crystals ([Kas96] Thm. 3.1, conditions (3.1) and (3.2)): a map
`σ : B₁ → B₂` with `wt(σ b) = m wt(b)`, `εᵢ(σ b) = m εᵢ(b)`, `ẽᵢᵐ σ(b) = σ(ẽᵢ b)` and
`f̃ᵢᵐ σ(b) = σ(f̃ᵢ b)` (with `σ(0) = 0`). -/
structure Similarity (m : ℕ) where
  /-- The underlying map. -/
  toFun : B₁ → B₂
  wt_map : ∀ b, C₂.wt (toFun b) = m • C₁.wt b
  ε_map : ∀ i b, C₂.ε i (toFun b) = m • C₁.ε i b
  e_map : ∀ i b, C₂.eIter i m (toFun b) = (C₁.e i b).map toFun
  f_map : ∀ i b, C₂.fIter i m (toFun b) = (C₁.f i b).map toFun

namespace Similarity

variable {m : ℕ}

instance : FunLike (Similarity C₁ C₂ m) B₁ B₂ where
  coe σ := σ.toFun
  coe_injective σ σ' h := by cases σ; cases σ'; congr

@[simp] lemma toFun_eq_coe (σ : Similarity C₁ C₂ m) : σ.toFun = σ := rfl

lemma wt_apply (σ : Similarity C₁ C₂ m) (b : B₁) : C₂.wt (σ b) = m • C₁.wt b := σ.wt_map b

lemma ε_apply (σ : Similarity C₁ C₂ m) (i : ι) (b : B₁) : C₂.ε i (σ b) = m • C₁.ε i b :=
  σ.ε_map i b

lemma eIter_apply (σ : Similarity C₁ C₂ m) (i : ι) (b : B₁) :
    C₂.eIter i m (σ b) = (C₁.e i b).map σ := σ.e_map i b

lemma fIter_apply (σ : Similarity C₁ C₂ m) (i : ι) (b : B₁) :
    C₂.fIter i m (σ b) = (C₁.f i b).map σ := σ.f_map i b

/-- `φᵢ(σ b) = m φᵢ(b)`. -/
lemma φ_apply (σ : Similarity C₁ C₂ m) (i : ι) (b : B₁) : C₂.φ i (σ b) = m • C₁.φ i b := by
  rw [C₂.φ_eq, C₁.φ_eq, σ.ε_apply, σ.wt_apply, map_nsmul, nsmul_add, ← WithBot.coe_nsmul]

/-- `f̃_{wᵐ} σ(b) = σ(f̃_w b)`. -/
theorem fWord_stretchWord (σ : Similarity C₁ C₂ m) (w : List ι) (b : B₁) :
    C₂.fWord (stretchWord m w) (σ b) = (C₁.fWord w b).map σ := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [fWord_stretchWord_cons, ih, fWord_cons]
    cases C₁.fWord w b with
    | none => rfl
    | some x => exact σ.fIter_apply j x

/-- The composition of a similarity with a strict morphism. -/
def compStrictHom (ψ : StrictHom C₂ C₃) (σ : Similarity C₁ C₂ m) : Similarity C₁ C₃ m where
  toFun b := ψ (σ b)
  wt_map b := by rw [ψ.wt_apply, σ.wt_apply]
  ε_map i b := by rw [ψ.ε_apply, σ.ε_apply]
  e_map i b := by rw [ψ.eIter_apply, σ.eIter_apply, Option.map_map]; rfl
  f_map i b := by rw [ψ.fIter_apply, σ.fIter_apply, Option.map_map]; rfl

@[simp] lemma compStrictHom_apply (ψ : StrictHom C₂ C₃) (σ : Similarity C₁ C₂ m) (b : B₁) :
    σ.compStrictHom ψ b = ψ (σ b) := rfl

/-- The composition of a strict morphism with a similarity. -/
def strictHomComp (σ : Similarity C₂ C₃ m) (ψ : StrictHom C₁ C₂) : Similarity C₁ C₃ m where
  toFun b := σ (ψ b)
  wt_map b := by rw [σ.wt_apply, ψ.wt_apply]
  ε_map i b := by rw [σ.ε_apply, ψ.ε_apply]
  e_map i b := by rw [σ.eIter_apply, ψ.e_apply, Option.map_map]; rfl
  f_map i b := by rw [σ.fIter_apply, ψ.f_apply, Option.map_map]; rfl

@[simp] lemma strictHomComp_apply (σ : Similarity C₂ C₃ m) (ψ : StrictHom C₁ C₂) (b : B₁) :
    σ.strictHomComp ψ b = σ (ψ b) := rfl

/-! ### Tensor products of similarities -/

variable {C₁' : Crystal D B₁'} {C₂' : Crystal D B₂'}

/-- The tensor product of two `m`-similarities is an `m`-similarity. -/
def tensorMap (hm : 0 < m) (σ₁ : Similarity C₁ C₁' m) (σ₂ : Similarity C₂ C₂' m) :
    Similarity (C₁.tensor C₂) (C₁'.tensor C₂') m where
  toFun b := (σ₁ b.1, σ₂ b.2)
  wt_map b := by simp [σ₁.wt_apply, σ₂.wt_apply]
  ε_map i b := by
    rw [tensor_ε, tensor_ε, σ₁.ε_apply, σ₂.ε_apply, σ₁.wt_apply, map_nsmul, nsmul_eq_mul,
      ← mul_neg, nsmul_max_add_withBot hm]
  e_map i b := by
    obtain ⟨b₁, b₂⟩ := b
    rw [tensor_e]
    split_ifs with h
    · rw [tensor_eIter_left]
      · rw [σ₁.eIter_apply, Option.map_map, Option.map_map]; rfl
      · intro k _ x' hx'
        rw [σ₂.ε_apply, C₁'.φ_eIter hx', σ₁.φ_apply]
        exact nsmul_le_nsmul_add_of_le m k h
    · rw [tensor_eIter_right]
      · rw [σ₂.eIter_apply, Option.map_map, Option.map_map]; rfl
      · intro k hk y' hy'
        rw [σ₁.φ_apply]
        exact not_le_nsmul_of_lt hk (not_le.mp h) (by rw [← σ₂.ε_apply]; exact C₂'.ε_eIter hy')
  f_map i b := by
    obtain ⟨b₁, b₂⟩ := b
    rw [tensor_f]
    split_ifs with h
    · rw [tensor_fIter_left]
      · rw [σ₁.fIter_apply, Option.map_map, Option.map_map]; rfl
      · intro k hk x' hx'
        rw [σ₂.ε_apply]
        exact nsmul_lt_of_lt_of_eq_add hk h (by rw [← σ₁.φ_apply]; exact C₁'.φ_fIter hx')
    · rw [tensor_fIter_right]
      · rw [σ₂.fIter_apply, Option.map_map, Option.map_map]; rfl
      · intro k _ y' hy'
        rw [σ₁.φ_apply]
        exact not_lt_nsmul_of_le (not_lt.mp h) (by rw [C₂'.ε_fIter hy', σ₂.ε_apply])

@[simp] lemma tensorMap_apply (hm : 0 < m) (σ₁ : Similarity C₁ C₁' m) (σ₂ : Similarity C₂ C₂' m)
    (b : B₁ × B₂) : tensorMap hm σ₁ σ₂ b = (σ₁ b.1, σ₂ b.2) := rfl

end Similarity

/-! ### Similarities from Kashiwara–Saito data -/

section KS

variable [DecidableEq ι]

lemma elementary_fIter_self (i : ι) (n : ℕ) (a : ℤ) :
    (elementary D i).fIter i n a = some (a - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [fIter_succ', ih, Option.bind_some, elementary_f_self]
    congr 1
    push_cast
    ring

lemma elementary_ε_nsmul {m : ℕ} (hm : 0 < m) (i k : ι) (n : ℤ) :
    (elementary D i).ε k (m * n) = m • (elementary D i).ε k n := by
  by_cases hki : k = i
  · subst hki
    rw [elementary_ε_self, elementary_ε_self, nsmul_coe_withBot, mul_neg]
  · rw [elementary_ε_of_ne hki, elementary_ε_of_ne hki, nsmul_bot_withBot hm]

lemma ε_tensor_elementary_nsmul {C : Crystal D B} {C' : Crystal D B'} {m : ℕ} (hm : 0 < m)
    (i k : ι) {b : B} {b' : B'} (n : ℤ) (hε : C'.ε k b' = m • C.ε k b)
    (hwt : C'.wt b' = m • C.wt b) :
    (C'.tensor (elementary D i)).ε k (b', m * n) = m • (C.tensor (elementary D i)).ε k (b, n) := by
  rw [tensor_elementary_ε, tensor_elementary_ε, hε, hwt, map_nsmul, nsmul_eq_mul, ← mul_neg,
    nsmul_max_add_withBot hm, elementary_ε_nsmul hm]

namespace KSData

variable {C : Crystal D B} {b₀ : B} (K : KSData C b₀) (hD : LinearIndependent ℤ D.root)
  {C' : Crystal D B'} {b₀' : B'} (K' : KSData C' b₀') {m : ℕ}

include hD

lemma fWord_eq_some_fw (w : List ι) : C.fWord w b₀ = some (K.fw hD w) := by
  induction w with
  | nil => rfl
  | cons j w ih => rw [fWord_cons, ih, Option.bind_some, K.f_fw]

lemma fIter_fw_stretchWord (j : ι) (w : List ι) :
    C.fIter j m (K.fw hD (stretchWord m w)) = some (K.fw hD (stretchWord m (j :: w))) := by
  have h := K.fWord_eq_some_fw hD (stretchWord m (j :: w))
  rwa [fWord_stretchWord_cons, K.fWord_eq_some_fw hD, Option.bind_some] at h

lemma wt_fw_stretchWord (w : List ι) :
    C.wt (K.fw hD (stretchWord m w)) = m • C.wt (K.fw hD w) := by
  rw [K.wt_fw, K.wt_fw, smul_neg]
  congr 1
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [stretchWord_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      nsmul_add, List.map_replicate, List.sum_replicate]

lemma wt_fw_stretchWord_eq (w : List ι) :
    C'.wt (K'.fw hD (stretchWord m w)) = m • C.wt (K.fw hD w) := by
  rw [K'.wt_fw_stretchWord hD, K'.wt_fw, K.wt_fw]

lemma ht_fw_stretchWord (w : List ι) : K.ht (K.fw hD (stretchWord m w)) = m * w.length := by
  rw [K.ht_fw, length_stretchWord]

omit hD [DecidableEq ι] in
lemma φ_eq_nsmul_of_ε_eq {b : B} {b' : B'} (j : ι)
    (hε : C'.ε j b' = m • C.ε j b) (hwt : C'.wt b' = m • C.wt b) :
    C'.φ j b' = m • C.φ j b := by
  rw [C'.φ_eq, C.φ_eq, hε, hwt, map_nsmul, nsmul_add, ← WithBot.coe_nsmul]

/-- `Ψᵢ` on `f̃_w b₀` and on `f̃_{wᵐ} b₀'` correspond, as long as
`εⱼ(f̃_{uᵐ} b₀') = m εⱼ(f̃_u b₀)` on shorter words `u`. -/
theorem exists_Ψ_fw_stretchWord (hm : 0 < m) (L : ℕ)
    (hE : ∀ w : List ι, w.length ≤ L →
      ∀ k, C'.ε k (K'.fw hD (stretchWord m w)) = m • C.ε k (K.fw hD w))
    (i : ι) (w : List ι) (hw : w.length ≤ L + 1) :
    ∃ (u : List ι) (n : ℤ), K.Ψ i (K.fw hD w) = (K.fw hD u, n) ∧
      K'.Ψ i (K'.fw hD (stretchWord m w)) = (K'.fw hD (stretchWord m u), m * n) := by
  induction w with
  | nil =>
    refine ⟨[], 0, K.Ψ_b₀ hD i, ?_⟩
    change K'.Ψ i b₀' = (b₀', (m : ℤ) * 0)
    rw [K'.Ψ_b₀ hD i, mul_zero]
  | cons j w ih =>
    rw [List.length_cons] at hw
    obtain ⟨u, n, h1, h1'⟩ := ih (by omega)
    have hlen : u.length ≤ L := by
      have := K.ht_Ψ hD i (K.fw hD w)
      rw [h1, K.ht_fw, K.ht_fw] at this
      simp only at this
      omega
    have hf := (K.Ψ i).f_apply j (K.fw hD w)
    rw [h1, K.f_fw, Option.map_some, tensor_elementary_f] at hf
    have hf' := (K'.Ψ i).fIter_apply j m (K'.fw hD (stretchWord m w))
    rw [K'.fIter_fw_stretchWord hD, Option.map_some, h1'] at hf'
    have hφ : C'.φ j (K'.fw hD (stretchWord m u)) = m • C.φ j (K.fw hD u) :=
      φ_eq_nsmul_of_ε_eq j (hE u hlen j) (K.wt_fw_stretchWord_eq hD K' u)
    split_ifs at hf with hc
    · -- `f̃ⱼ` acts on the first factor
      rw [K.f_fw, Option.map_some, Option.some_inj] at hf
      refine ⟨j :: u, n, hf.symm, ?_⟩
      rw [tensor_fIter_left, K'.fIter_fw_stretchWord hD, Option.map_some, Option.some_inj] at hf'
      · exact hf'.symm
      · intro k hk x' hx'
        rw [elementary_ε_nsmul hm]
        refine nsmul_lt_of_lt_of_eq_add hk hc ?_
        rw [← hφ]
        exact C'.φ_fIter hx'
    · -- `f̃ᵢ` acts on the second factor
      by_cases hji : j = i
      · subst hji
        rw [elementary_f_self, Option.map_some, Option.some_inj] at hf
        refine ⟨u, n - 1, hf.symm, ?_⟩
        rw [tensor_fIter_right, elementary_fIter_self, Option.map_some, Option.some_inj] at hf'
        · rw [← hf', mul_sub, mul_one]
        · intro k _ y' hy'
          rw [hφ]
          rw [elementary_fIter_self, Option.some_inj] at hy'
          subst hy'
          refine not_lt_nsmul_of_le (k := k) (not_lt.mp hc) ?_
          rw [elementary_ε_self, elementary_ε_self, nsmul_coe_withBot, ← WithBot.coe_natCast,
            ← WithBot.coe_add]
          congr 1
          ring
      · rw [elementary_ε_of_ne hji] at hc
        exact absurd (bot_lt_iff_ne_bot.2 (K.φ_ne_bot j _)) hc

/-- The induction for the scaled comparison of `C` and `C'`. -/
theorem fw_stretchWord_and_ε (hm : 0 < m) (L : ℕ) :
    (∀ w : List ι, w.length ≤ L →
      ∀ k, C'.ε k (K'.fw hD (stretchWord m w)) = m • C.ε k (K.fw hD w)) ∧
    (∀ w w' : List ι, w.length ≤ L → w'.length ≤ L → K.fw hD w = K.fw hD w' →
      K'.fw hD (stretchWord m w) = K'.fw hD (stretchWord m w')) ∧
    (∀ w w' : List ι, w.length ≤ L → w'.length ≤ L →
      K'.fw hD (stretchWord m w) = K'.fw hD (stretchWord m w') → K.fw hD w = K.fw hD w') := by
  induction L with
  | zero =>
    refine ⟨fun w hw k ↦ ?_, fun w w' hw hw' _ ↦ ?_, fun w w' hw hw' _ ↦ ?_⟩
    · rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw), stretchWord_nil, fw_nil, fw_nil,
        K.ε_b₀, K'.ε_b₀, nsmul_zero]
    all_goals rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw),
      List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw')]
  | succ L ih =>
    obtain ⟨hE, hS, hS'⟩ := ih
    have hu : ∀ {w u : List ι} {n : ℤ} {i : ι}, w.length ≤ L + 1 →
        K.Ψ i (K.fw hD w) = (K.fw hD u, n) → n < 0 → u.length ≤ L := by
      intro w u n i hw h hn
      have := K.ht_Ψ hD i (K.fw hD w)
      rw [h, K.ht_fw, K.ht_fw] at this
      simp only at this
      omega
    refine ⟨fun w hw k ↦ ?_, fun w w' hw hw' heq ↦ ?_, fun w w' hw hw' heq ↦ ?_⟩
    · -- the `εₖ`
      by_cases hL : w.length ≤ L
      · exact hE w hL k
      have hne : K.fw hD w ≠ b₀ := K.fw_ne_b₀ hD (fun h ↦ by simp [h] at hL)
      obtain ⟨i, hi⟩ := K.exists_Ψ_snd_neg _ hne
      obtain ⟨u, n, h1, h1'⟩ := K.exists_Ψ_fw_stretchWord hD K' hm L hE i w hw
      rw [h1] at hi
      have hlu := hu hw h1 hi
      rw [← (K.Ψ i).ε_apply, ← (K'.Ψ i).ε_apply, h1, h1']
      exact ε_tensor_elementary_nsmul hm i k n (hE u hlu k) (K.wt_fw_stretchWord_eq hD K' u)
    · -- equalities of words
      have hlen : w.length = w'.length := by
        have := congrArg K.ht heq
        rwa [K.ht_fw, K.ht_fw] at this
      by_cases hL : w.length ≤ L
      · exact hS w w' hL (hlen ▸ hL) heq
      have hne : K.fw hD w ≠ b₀ := K.fw_ne_b₀ hD (fun h ↦ by simp [h] at hL)
      obtain ⟨i, hi⟩ := K.exists_Ψ_snd_neg _ hne
      obtain ⟨u, n, h1, h1'⟩ := K.exists_Ψ_fw_stretchWord hD K' hm L hE i w hw
      obtain ⟨u', n', h2, h2'⟩ := K.exists_Ψ_fw_stretchWord hD K' hm L hE i w' hw'
      have h12 : (K.fw hD u, n) = (K.fw hD u', n') := by rw [← h1, ← h2, heq]
      obtain ⟨hfu, rfl⟩ := Prod.mk.inj h12
      rw [h1] at hi
      have hlu := hu hw h1 hi
      have hlu' := hu hw' h2 hi
      apply K'.Ψ_injective i
      rw [h1', h2', hS u u' hlu hlu' hfu]
    · -- the converse
      have hlen : w.length = w'.length := by
        have := congrArg K'.ht heq
        rw [K'.ht_fw_stretchWord hD, K'.ht_fw_stretchWord hD] at this
        exact Nat.eq_of_mul_eq_mul_left hm this
      by_cases hL : w.length ≤ L
      · exact hS' w w' hL (hlen ▸ hL) heq
      have hne : K.fw hD w ≠ b₀ := K.fw_ne_b₀ hD (fun h ↦ by simp [h] at hL)
      obtain ⟨i, hi⟩ := K.exists_Ψ_snd_neg _ hne
      obtain ⟨u, n, h1, h1'⟩ := K.exists_Ψ_fw_stretchWord hD K' hm L hE i w hw
      obtain ⟨u', n', h2, h2'⟩ := K.exists_Ψ_fw_stretchWord hD K' hm L hE i w' hw'
      have h12 : (K'.fw hD (stretchWord m u), (m : ℤ) * n) =
          (K'.fw hD (stretchWord m u'), m * n') := by rw [← h1', ← h2', heq]
      obtain ⟨hfu, hn⟩ := Prod.mk.inj h12
      have hnn : n = n' := mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) hn
      subst hnn
      rw [h1] at hi
      have hlu := hu hw h1 hi
      have hlu' := hu hw' h2 hi
      apply K.Ψ_injective i
      rw [h1, h2, hS' u u' hlu hlu' hfu]

theorem ε_fw_stretchWord (hm : 0 < m) (w : List ι) (k : ι) :
    C'.ε k (K'.fw hD (stretchWord m w)) = m • C.ε k (K.fw hD w) :=
  (K.fw_stretchWord_and_ε hD K' hm w.length).1 w le_rfl k

theorem fw_stretchWord_eq_of_fw_eq (hm : 0 < m) {w w' : List ι} (h : K.fw hD w = K.fw hD w') :
    K'.fw hD (stretchWord m w) = K'.fw hD (stretchWord m w') :=
  (K.fw_stretchWord_and_ε hD K' hm (max w.length w'.length)).2.1 w w' (le_max_left _ _)
    (le_max_right _ _) h

theorem fw_eq_of_fw_stretchWord_eq (hm : 0 < m) {w w' : List ι}
    (h : K'.fw hD (stretchWord m w) = K'.fw hD (stretchWord m w')) : K.fw hD w = K.fw hD w' :=
  (K.fw_stretchWord_and_ε hD K' hm (max w.length w'.length)).2.2 w w' (le_max_left _ _)
    (le_max_right _ _) h

variable (m) in
/-- The map `f̃_w b₀ ↦ f̃_{wᵐ} b₀'`. -/
noncomputable def stretchFun (b : B) : B' := K'.fw hD (stretchWord m (K.word hD b))

lemma stretchFun_fw (hm : 0 < m) (w : List ι) :
    K.stretchFun hD K' m (K.fw hD w) = K'.fw hD (stretchWord m w) :=
  K.fw_stretchWord_eq_of_fw_eq hD K' hm (K.fw_word hD _)

/-- **Similarity from Kashiwara–Saito data** (cf. [Kas96] Thm. 3.2): if `C` and `C'` carry
Kashiwara–Saito data, `εᵢ(b) = 0` whenever `ẽᵢ b = 0` in `C`, and `ẽᵢ b = 0` whenever `εᵢ(b) = 0`
in `C'`, then `f̃_w b₀ ↦ f̃_{wᵐ} b₀'` is an `m`-similarity `C → C'` (injective by
`Crystal.KSData.similarity_injective`). Our proof, by induction on the length of words (see the
module docstring). -/
noncomputable def similarity (hm : 0 < m) (hC : ∀ i b, C.e i b = none → C.ε i b = 0)
    (hC' : ∀ i b, C'.ε i b = 0 → C'.e i b = none) : Similarity C C' m where
  toFun := K.stretchFun hD K' m
  wt_map b := by
    obtain ⟨w, rfl⟩ := K.exists_fw_eq hD b
    rw [K.stretchFun_fw hD K' hm, K.wt_fw_stretchWord_eq hD K']
  ε_map i b := by
    obtain ⟨w, rfl⟩ := K.exists_fw_eq hD b
    rw [K.stretchFun_fw hD K' hm, K.ε_fw_stretchWord hD K' hm]
  e_map i b := by
    obtain ⟨w, rfl⟩ := K.exists_fw_eq hD b
    cases he : C.e i (K.fw hD w) with
    | some b'' =>
      obtain ⟨u, rfl⟩ := K.exists_fw_eq hD b''
      have h1 : K.fw hD (i :: u) = K.fw hD w := by
        have := K.f_fw hD i u
        rw [(C.f_eq_some_iff i _ _).2 he] at this
        exact (Option.some_inj.1 this).symm
      rw [Option.map_some, K.stretchFun_fw hD K' hm, K.stretchFun_fw hD K' hm,
        K.fw_stretchWord_eq_of_fw_eq hD K' hm h1.symm, ← C'.fIter_eq_some_iff]
      exact K'.fIter_fw_stretchWord hD i u
    | none =>
      rw [Option.map_none]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      have hε : C'.ε i (K.stretchFun hD K' (n + 1) (K.fw hD w)) = 0 := by
        rw [K.stretchFun_fw hD K' hm, K.ε_fw_stretchWord hD K' hm, hC i _ he, nsmul_zero]
      rw [eIter_succ, hC' i _ hε, Option.bind_none]
  f_map i b := by
    obtain ⟨w, rfl⟩ := K.exists_fw_eq hD b
    rw [K.stretchFun_fw hD K' hm, K'.fIter_fw_stretchWord hD, K.f_fw, Option.map_some,
      K.stretchFun_fw hD K' hm]

lemma similarity_apply (hm : 0 < m) (hC : ∀ i b, C.e i b = none → C.ε i b = 0)
    (hC' : ∀ i b, C'.ε i b = 0 → C'.e i b = none) (b : B) :
    K.similarity hD K' hm hC hC' b = K.stretchFun hD K' m b := rfl

theorem similarity_injective (hm : 0 < m) (hC : ∀ i b, C.e i b = none → C.ε i b = 0)
    (hC' : ∀ i b, C'.ε i b = 0 → C'.e i b = none) :
    Function.Injective (K.similarity hD K' hm hC hC') := by
  intro b b' h
  obtain ⟨w, rfl⟩ := K.exists_fw_eq hD b
  obtain ⟨w', rfl⟩ := K.exists_fw_eq hD b'
  rw [similarity_apply, similarity_apply, K.stretchFun_fw hD K' hm,
    K.stretchFun_fw hD K' hm] at h
  exact K.fw_eq_of_fw_stretchWord_eq hD K' hm h

theorem similarity_b₀ (hm : 0 < m) (hC : ∀ i b, C.e i b = none → C.ε i b = 0)
    (hC' : ∀ i b, C'.ε i b = 0 → C'.e i b = none) :
    K.similarity hD K' hm hC hC' b₀ = b₀' := by
  exact K.stretchFun_fw hD K' hm []

end KSData

end KS

end Crystal
