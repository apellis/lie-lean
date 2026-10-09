/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Similarity

/-!
# Tensor powers of crystals

The tensor power `B^{⊗n} = B ⊗ (B ⊗ (⋯ ⊗ (B ⊗ T₀)))` of a crystal, with elements modelled as
iterated pairs (`Crystal.TPow`), and the facts about it used in Kashiwara's proof that the
crystal of an irreducible highest weight module is the path crystal ([Kas96] §4).

## Main definitions

* `Crystal.TPow B n`: `n`-tuples `(b₁, (b₂, … (bₙ, ())))`, with `TPow.toList`, `TPow.replicate`,
  `TPow.append`, `TPow.flatten`, `TPow.Forall₂`.
* `Crystal.unit D`: the crystal `T₀` on `PUnit`.
* `Crystal.tensorPow C n`: the crystal `B^{⊗n}`.
* `Crystal.appendEquiv`: `B^{⊗a} ⊗ B^{⊗b} ≅ B^{⊗(b+a)}`, `(x, y) ↦ x ++ y`.
* `Crystal.Similarity.powMap`: an `m`-similarity `T : B → B^{⊗m}` induces the `m`-similarity
  `B^{⊗n} → B^{⊗mn}`, `b₁ ⊗ ⋯ ⊗ bₙ ↦ T(b₁) ⊗ ⋯ ⊗ T(bₙ)`.

## Main results

* `Crystal.fIter_replicate`: if `εᵢ(x) = 0` and `φᵢ(x) = a`, then
  `f̃ᵢ^{aq} (x ⊗ ⋯ ⊗ x) = f̃ᵢᵃx ⊗ ⋯ ⊗ f̃ᵢᵃx ⊗ x ⊗ ⋯ ⊗ x` (`q` factors `f̃ᵢᵃx`).
* `Crystal.IsColourRel.fIter_tensorPow`: if a relation between `B` and `B'` is compatible with
  `εᵢ`, `⟨wt, αᵢ^∨⟩` and `f̃ᵢ`, then so is its entrywise extension to tensor powers; so `f̃ᵢʳ`
  acts on related tuples in the same way.

## References

* [Kas96] M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194 (1996), 177–186.
-/

universe u v

namespace Crystal

/-! ### Tuples -/

/-- `n`-tuples `(b₁, (b₂, … (bₙ, ())))` of elements of `B`. -/
def TPow (B : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => B × TPow B n

namespace TPow

variable {B : Type u} {B' : Type v}

/-- The list of entries of a tuple. -/
def toList : {n : ℕ} → TPow B n → List B
  | 0, _ => []
  | _ + 1, x => x.1 :: toList x.2

@[simp] lemma toList_zero (x : TPow B 0) : toList x = [] := rfl

@[simp] lemma toList_succ {n : ℕ} (x : TPow B (n + 1)) : toList x = x.1 :: toList x.2 := rfl

lemma length_toList : {n : ℕ} → (x : TPow B n) → (toList x).length = n
  | 0, _ => rfl
  | _ + 1, x => by rw [toList_succ, List.length_cons, length_toList x.2]

lemma toList_injective : {n : ℕ} → Function.Injective (toList : TPow B n → List B)
  | 0, _, _, _ => rfl
  | _ + 1, x, y, h => by
    rw [toList_succ, toList_succ, List.cons.injEq] at h
    exact Prod.ext h.1 (toList_injective h.2)

/-- The constant tuple `(b, …, b)`. -/
def replicate (b : B) : (n : ℕ) → TPow B n
  | 0 => PUnit.unit
  | n + 1 => (b, replicate b n)

@[simp] lemma toList_replicate (b : B) : (n : ℕ) → toList (replicate b n) = List.replicate n b
  | 0 => rfl
  | n + 1 => by
    change b :: toList (replicate b n) = _
    rw [toList_replicate b n, List.replicate_succ]

/-- The tuple `(y, …, y, x, …, x)` with `q` entries `y` and `n - q` entries `x`. -/
def replicate₂ (y x : B) : (q n : ℕ) → TPow B n
  | _, 0 => PUnit.unit
  | 0, n + 1 => (x, replicate x n)
  | q + 1, n + 1 => (y, replicate₂ y x q n)

lemma toList_replicate₂ (y x : B) : (q n : ℕ) → q ≤ n →
    toList (replicate₂ y x q n) = List.replicate q y ++ List.replicate (n - q) x
  | _, 0, h => by rw [Nat.le_zero.1 h]; rfl
  | 0, n + 1, _ => by
    change x :: toList (replicate x n) = _
    rw [toList_replicate]
    simp [List.replicate_succ]
  | q + 1, n + 1, h => by
    change y :: toList (replicate₂ y x q n) = _
    rw [toList_replicate₂ y x q n (by omega)]
    simp [List.replicate_succ]

@[simp] lemma replicate₂_zero (y x : B) : (n : ℕ) → replicate₂ y x 0 n = replicate x n
  | 0 => rfl
  | _ + 1 => rfl

lemma replicate₂_self (y x : B) : (n : ℕ) → replicate₂ y x n n = replicate y n
  | 0 => rfl
  | n + 1 => by rw [replicate₂, replicate₂_self y x n]; rfl

/-- Concatenation of tuples. -/
def append : {a b : ℕ} → TPow B a → TPow B b → TPow B (b + a)
  | 0, _, _, y => y
  | _ + 1, _, x, y => (x.1, append x.2 y)

@[simp] lemma toList_append : {a b : ℕ} → (x : TPow B a) → (y : TPow B b) →
    toList (append x y) = toList x ++ toList y
  | 0, _, _, _ => rfl
  | _ + 1, _, x, y => by
    change x.1 :: toList (append x.2 y) = _
    rw [toList_append x.2 y]
    rfl

/-- Flattening a tuple of `k`-tuples. -/
def flatten {k : ℕ} : {n : ℕ} → TPow (TPow B k) n → TPow B (k * n)
  | 0, _ => PUnit.unit
  | _ + 1, x => append x.1 (flatten x.2)

/-- Applying a map to every entry. -/
def map {B₂ : Type v} (f : B → B₂) : {n : ℕ} → TPow B n → TPow B₂ n
  | 0, _ => PUnit.unit
  | _ + 1, x => (f x.1, map f x.2)

@[simp] lemma toList_map {B₂ : Type v} (f : B → B₂) : {n : ℕ} → (x : TPow B n) →
    toList (map f x) = (toList x).map f
  | 0, _ => rfl
  | _ + 1, x => by
    change f x.1 :: toList (map f x.2) = _
    rw [toList_map f x.2]
    rfl

/-- The entrywise extension of a relation. -/
def Forall₂ (r : B → B' → Prop) : {n : ℕ} → TPow B n → TPow B' n → Prop
  | 0, _, _ => True
  | _ + 1, x, y => r x.1 y.1 ∧ Forall₂ r x.2 y.2

lemma forall₂_iff (r : B → B' → Prop) : {n : ℕ} → (x : TPow B n) → (y : TPow B' n) →
    Forall₂ r x y ↔ List.Forall₂ r (toList x) (toList y)
  | 0, _, _ => by simp [Forall₂]
  | _ + 1, x, y => by
    rw [Forall₂, toList_succ, toList_succ, List.forall₂_cons, forall₂_iff r x.2 y.2]

lemma forall₂_replicate {r : B → B' → Prop} {b : B} {b' : B'} (h : r b b') :
    (n : ℕ) → Forall₂ r (replicate b n) (replicate b' n)
  | 0 => True.intro
  | n + 1 => ⟨h, forall₂_replicate h n⟩

lemma forall₂_replicate₂ {r : B → B' → Prop} {y x : B} {y' x' : B'} (hy : r y y')
    (hx : r x x') : (q n : ℕ) → Forall₂ r (replicate₂ y x q n) (replicate₂ y' x' q n)
  | _, 0 => True.intro
  | 0, n + 1 => ⟨hx, forall₂_replicate hx n⟩
  | q + 1, n + 1 => ⟨hy, forall₂_replicate₂ hy hx q n⟩

lemma forall₂_append {r : B → B' → Prop} : {a b : ℕ} → {x : TPow B a} → {x' : TPow B' a} →
    {y : TPow B b} → {y' : TPow B' b} → Forall₂ r x x' → Forall₂ r y y' →
    Forall₂ r (append x y) (append x' y')
  | 0, _, _, _, _, _, _, hy => hy
  | _ + 1, _, _, _, _, _, hx, hy => ⟨hx.1, forall₂_append hx.2 hy⟩

lemma forall₂_flatten {r : B → B' → Prop} {k : ℕ} : {n : ℕ} → {x : TPow (TPow B k) n} →
    {x' : TPow (TPow B' k) n} → Forall₂ (Forall₂ r) x x' → Forall₂ r (flatten x) (flatten x')
  | 0, _, _, _ => True.intro
  | _ + 1, _, _, h => forall₂_append h.1 (forall₂_flatten h.2)

lemma forall₂_map {B₂ : Type u} {B₂' : Type v} {r : B → B' → Prop} {s : B₂ → B₂' → Prop}
    {f : B → B₂} {f' : B' → B₂'} (hf : ∀ b b', r b b' → s (f b) (f' b')) :
    {n : ℕ} → {x : TPow B n} → {x' : TPow B' n} → Forall₂ r x x' →
    Forall₂ s (map f x) (map f' x')
  | 0, _, _, _ => True.intro
  | _ + 1, _, _, h => ⟨hf _ _ h.1, forall₂_map hf h.2⟩

lemma forall₂_mono {r s : B → B' → Prop} (hrs : ∀ b b', r b b' → s b b') :
    {n : ℕ} → {x : TPow B n} → {x' : TPow B' n} → Forall₂ r x x' → Forall₂ s x x'
  | 0, _, _, _ => True.intro
  | _ + 1, _, _, h => ⟨hrs _ _ h.1, forall₂_mono hrs h.2⟩

end TPow

/-! ### The crystal `T₀` on `PUnit` -/

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B : Type u} {B' : Type v}

variable (D) in
/-- The crystal `T₀ = {t₀}` on `PUnit` (`wt t₀ = 0`, `εᵢ = φᵢ = -∞`, `ẽᵢ = f̃ᵢ = 0`), the unit of
the tensor product. -/
def unit : Crystal D PUnit.{u + 1} where
  wt _ := 0
  ε _ _ := ⊥
  φ _ _ := ⊥
  e _ _ := none
  f _ _ := none
  φ_eq _ _ := by simp
  f_eq_some_iff _ _ _ := by simp
  wt_e _ _ _ h := by simp at h
  ε_e _ _ _ h := by simp at h
  e_eq_none_of_φ_eq_bot _ _ _ := rfl

/-- `T₀ ⊗ B ≅ B`. -/
def unitTensor (C : Crystal D B) : Equiv ((unit.{u} D).tensor C) C where
  toEquiv := _root_.Equiv.punitProd B
  wt_map b := by simp [unit]
  ε_map i b := by
    obtain ⟨_, b⟩ := b
    change C.ε i b = max ⊥ (C.ε i b + _)
    simp [unit]
  e_map i b := by
    obtain ⟨_, b⟩ := b
    change C.e i b = (if C.ε i b ≤ ⊥ then none else (C.e i b).map (PUnit.unit, ·)).map _
    split_ifs with h
    · rw [le_bot_iff] at h
      simp [C.e_eq_none_of_ε_eq_bot h]
    · simp [Option.map_map, Function.comp_def]
  f_map i b := by
    obtain ⟨_, b⟩ := b
    change C.f i b = (if C.ε i b < ⊥ then none else (C.f i b).map (PUnit.unit, ·)).map _
    simp [Option.map_map, Function.comp_def]

/-! ### Tensor powers -/

/-- The tensor power `B^{⊗n} = B ⊗ (B ⊗ (⋯ ⊗ (B ⊗ T₀)))`. -/
def tensorPow (C : Crystal D B) : (n : ℕ) → Crystal D (TPow B n)
  | 0 => unit D
  | n + 1 => C.tensor (tensorPow C n)

variable (C : Crystal D B)

@[simp] lemma tensorPow_zero : C.tensorPow 0 = unit D := rfl

lemma tensorPow_succ (n : ℕ) : C.tensorPow (n + 1) = C.tensor (C.tensorPow n) := rfl

/-- `B^{⊗a} ⊗ B^{⊗b} ≅ B^{⊗(b+a)}`, `(x, y) ↦ x ++ y`. -/
def appendEquiv (b : ℕ) : (a : ℕ) →
    Equiv ((C.tensorPow a).tensor (C.tensorPow b)) (C.tensorPow (b + a))
  | 0 => unitTensor (C.tensorPow b)
  | a + 1 => (tensorAssoc C (C.tensorPow a) (C.tensorPow b)).trans
      (Equiv.tensorCongr (Equiv.refl C) (appendEquiv b a))

lemma appendEquiv_apply (b : ℕ) : (a : ℕ) → (x : TPow B a) → (y : TPow B b) →
    C.appendEquiv b a (x, y) = TPow.append x y
  | 0, _, _ => rfl
  | a + 1, x, y => by
    change (x.1, C.appendEquiv b a (x.2, y)) = _
    rw [appendEquiv_apply b a x.2 y]
    rfl

/-! ### Iterates on tensor powers of a single element -/

section Replicate

variable {C} (i : ι)

lemma fIter_add (m n : ℕ) (b : B) : C.fIter i (m + n) b = (C.fIter i n b).bind (C.fIter i m) := by
  rw [← C.fWord_replicate, List.replicate_add, fWord_append, C.fWord_replicate]
  congr 1
  funext x
  exact C.fWord_replicate i m x

lemma ε_replicate_le {x : B} (hε : C.ε i x = 0) (hφ : 0 ≤ C.φ i x) :
    (n : ℕ) → (C.tensorPow n).ε i (TPow.replicate x n) ≤ 0
  | 0 => bot_le
  | n + 1 => by
    change max (C.ε i x) ((C.tensorPow n).ε i (TPow.replicate x n) + _) ≤ 0
    rw [hε, max_le_iff]
    refine ⟨le_rfl, ?_⟩
    have h1 := ε_replicate_le hε hφ n
    have h2 : ((-D.coroot i (C.wt x) : ℤ) : WithBot ℤ) ≤ 0 := by
      rw [C.φ_eq, hε, zero_add] at hφ
      exact_mod_cast neg_nonpos.2 (by exact_mod_cast hφ)
    calc _ ≤ (0 : WithBot ℤ) + 0 := add_le_add h1 h2
      _ = 0 := add_zero 0

lemma ε_replicate_succ {x : B} (hε : C.ε i x = 0) (hφ : 0 ≤ C.φ i x) (n : ℕ) :
    (C.tensorPow (n + 1)).ε i (TPow.replicate x (n + 1)) = 0 := by
  change max (C.ε i x) ((C.tensorPow n).ε i (TPow.replicate x n) + _) = 0
  rw [hε]
  refine max_eq_left ?_
  have h1 := ε_replicate_le i hε hφ n
  have h2 : ((-D.coroot i (C.wt x) : ℤ) : WithBot ℤ) ≤ 0 := by
    rw [C.φ_eq, hε, zero_add] at hφ
    exact_mod_cast neg_nonpos.2 (by exact_mod_cast hφ)
  calc _ ≤ (0 : WithBot ℤ) + 0 := add_le_add h1 h2
    _ = 0 := add_zero 0

lemma eq_coe_sub_of_coe_eq_add {c : WithBot ℤ} {a : ℤ} {k : ℕ}
    (h : (a : WithBot ℤ) = c + k) : c = ((a - k : ℤ) : WithBot ℤ) := by
  induction c using WithBot.recBotCoe with
  | bot => rw [WithBot.bot_add] at h; exact absurd h WithBot.coe_ne_bot
  | coe c =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at h
    rw [WithBot.coe_inj]
    omega

/-- **The string lemma for tensor powers**: if `εᵢ(x) = 0`, `φᵢ(x) = a` and `f̃ᵢᵃ x = y`, then
`f̃ᵢ^{aq} (x ⊗ ⋯ ⊗ x) = y ⊗ ⋯ ⊗ y ⊗ x ⊗ ⋯ ⊗ x` (`q` factors `y`, `n - q` factors `x`). -/
theorem fIter_replicate {x y : B} {a : ℕ} (hε : C.ε i x = 0)
    (hφ : C.φ i x = ((a : ℤ) : WithBot ℤ)) (hy : C.fIter i a x = some y) :
    (n q : ℕ) → q ≤ n →
      (C.tensorPow n).fIter i (a * q) (TPow.replicate x n) = some (TPow.replicate₂ y x q n)
  | 0, q, h => by rw [Nat.le_zero.1 h]; rfl
  | n + 1, 0, _ => rfl
  | n + 1, q + 1, h => by
    have hφ0 : (0 : WithBot ℤ) ≤ C.φ i x := by rw [hφ]; exact_mod_cast Nat.zero_le a
    have hφy : C.φ i y = 0 := by
      have h1 := C.φ_fIter hy
      rw [hφ] at h1
      rw [eq_coe_sub_of_coe_eq_add h1, sub_self, WithBot.coe_zero]
    have hleft : ∀ k < a, ∀ x', C.fIter i k x = some x' →
        (C.tensorPow n).ε i (TPow.replicate x n) < C.φ i x' := by
      intro k hk x' hx'
      have h1 := C.φ_fIter hx'
      rw [hφ] at h1
      rw [eq_coe_sub_of_coe_eq_add h1]
      refine lt_of_le_of_lt (ε_replicate_le i hε hφ0 n) ?_
      exact_mod_cast (show (0 : ℤ) < a - k by omega)
    have hright : ∀ k < a * q, ∀ y', (C.tensorPow n).fIter i k (TPow.replicate x n) = some y' →
        ¬ (C.tensorPow n).ε i y' < C.φ i y := by
      intro k hk y' hy'
      rw [hφy, not_lt]
      rcases n with _ | n
      · have : q = 0 := by omega
        subst this
        simp at hk
      · rw [(C.tensorPow (n + 1)).ε_fIter hy', ε_replicate_succ i hε hφ0 n, zero_add]
        exact_mod_cast Nat.zero_le k
    have key : (C.tensor (C.tensorPow n)).fIter i (a * q + a) (x, TPow.replicate x n) =
        some (y, TPow.replicate₂ y x q n) := by
      rw [fIter_add, tensor_fIter_left i a x _ hleft, hy, Option.map_some, Option.bind_some,
        tensor_fIter_right i _ y _ hright, fIter_replicate hε hφ hy n q (by omega),
        Option.map_some]
    exact key

end Replicate

/-! ### Similarities into tensor powers -/

namespace Similarity

variable {C} {m : ℕ}

/-- The identity of `T₀`, as an `m`-similarity (`m > 0`). -/
def unitMap (hm : 0 < m) : Similarity (unit.{u} D) (unit.{u} D) m where
  toFun _ := PUnit.unit
  wt_map _ := by simp [unit]
  ε_map _ _ := by simp [unit, nsmul_bot_withBot hm]
  e_map _ _ := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rfl
  f_map _ _ := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rfl

/-- An `m`-similarity `T : B → B^{⊗m}` induces the `m`-similarity `B^{⊗n} → B^{⊗mn}`,
`b₁ ⊗ ⋯ ⊗ bₙ ↦ T(b₁) ⊗ ⋯ ⊗ T(bₙ)`. -/
def powMap (hm : 0 < m) (T : Similarity C (C.tensorPow m) m) :
    (n : ℕ) → Similarity (C.tensorPow n) (C.tensorPow (m * n)) m
  | 0 => unitMap hm
  | n + 1 => (tensorMap hm T (powMap hm T n)).compStrictHom
      (C.appendEquiv (m * n) m).toStrictHom

lemma powMap_apply (hm : 0 < m) (T : Similarity C (C.tensorPow m) m) :
    (n : ℕ) → (x : TPow B n) → powMap hm T n x = TPow.flatten (TPow.map T x)
  | 0, _ => rfl
  | n + 1, x => by
    change C.appendEquiv (m * n) m (T x.1, powMap hm T n x.2) = _
    rw [appendEquiv_apply, powMap_apply hm T n x.2]
    rfl

lemma toList_powMap (hm : 0 < m) (T : Similarity C (C.tensorPow m) m) :
    (n : ℕ) → (x : TPow B n) →
      TPow.toList (powMap hm T n x) = (TPow.toList x).flatMap fun b ↦ TPow.toList (T b)
  | 0, _ => rfl
  | n + 1, x => by
    change TPow.toList (C.appendEquiv (m * n) m (T x.1, powMap hm T n x.2)) = _
    rw [appendEquiv_apply, TPow.toList_append, toList_powMap hm T n x.2]
    rfl

lemma powMap_replicate (hm : 0 < m) (T : Similarity C (C.tensorPow m) m) {b : B}
    (hb : T b = TPow.replicate b m) (n : ℕ) :
    powMap hm T n (TPow.replicate b n) = TPow.replicate b (m * n) := by
  apply TPow.toList_injective
  rw [toList_powMap, TPow.toList_replicate, TPow.toList_replicate]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, hb, TPow.toList_replicate, Nat.mul_succ,
      Nat.add_comm, List.replicate_add]

lemma powMap_injective (hm : 0 < m) (T : Similarity C (C.tensorPow m) m)
    (hT : Function.Injective T) (n : ℕ) : Function.Injective (powMap hm T n) := by
  intro x y h
  have h' := congrArg TPow.toList h
  rw [toList_powMap, toList_powMap] at h'
  apply TPow.toList_injective
  have hinj : Function.Injective fun b ↦ TPow.toList (T b) :=
    fun b b' hb ↦ hT (TPow.toList_injective hb)
  have hlen : ∀ b, (TPow.toList (T b)).length = m := fun b ↦ TPow.length_toList _
  clear h
  generalize TPow.toList x = l at h'
  generalize TPow.toList y = l' at h'
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons b l' =>
      have := congrArg List.length h'
      simp only [List.flatMap_nil, List.flatMap_cons, List.length_append, List.length_nil,
        hlen] at this
      omega
  | cons b l ih =>
    cases l' with
    | nil =>
      have := congrArg List.length h'
      simp only [List.flatMap_nil, List.flatMap_cons, List.length_append, List.length_nil,
        hlen] at this
      omega
    | cons b' l' =>
      rw [List.flatMap_cons, List.flatMap_cons] at h'
      obtain ⟨h1, h2⟩ := List.append_inj h' (by rw [hlen, hlen])
      rw [hinj h1, ih l' h2]

/-- `f̃ᵢ^{mn} σ(b) = σ(f̃ᵢⁿ b)`. -/
lemma fIter_mul {B₂ : Type*} {C₂ : Crystal D B₂} (σ : Similarity C C₂ m) (i : ι) (n : ℕ)
    (b : B) : C₂.fIter i (m * n) (σ b) = (C.fIter i n b).map σ := by
  rw [← C₂.fWord_replicate, ← C.fWord_replicate, ← σ.fWord_stretchWord, stretchWord_replicate]

end Similarity

/-! ### Relations compatible with one colour -/

section ColourRel

variable {C} {B₁ B₁' B₂ B₂' : Type*} {C₁ : Crystal D B₁} {C₁' : Crystal D B₁'}
  {C₂ : Crystal D B₂} {C₂' : Crystal D B₂'}

/-- `(o, o')` are both `0`, or both nonzero and related by `r`. -/
def OptRel {β β' : Type*} (r : β → β' → Prop) (o : Option β) (o' : Option β') : Prop :=
  (o = none ∧ o' = none) ∨ ∃ y y', o = some y ∧ o' = some y' ∧ r y y'

variable (C₁ C₁') in
/-- A relation between `B₁` and `B₁'` compatible with the colour `i`: related elements have the
same `εᵢ` and `⟨wt, αᵢ^∨⟩`, and their images under `f̃ᵢ` are both `0` or related. -/
structure IsColourRel (i : ι) (r : B₁ → B₁' → Prop) : Prop where
  ε_eq : ∀ x x', r x x' → C₁.ε i x = C₁'.ε i x'
  coroot_eq : ∀ x x', r x x' → D.coroot i (C₁.wt x) = D.coroot i (C₁'.wt x')
  f_rel : ∀ x x', r x x' → OptRel r (C₁.f i x) (C₁'.f i x')

namespace IsColourRel

variable {i : ι} {r₁ : B₁ → B₁' → Prop} {r₂ : B₂ → B₂' → Prop}

lemma φ_eq (h : IsColourRel C₁ C₁' i r₁) {x : B₁} {x' : B₁'} (hx : r₁ x x') :
    C₁.φ i x = C₁'.φ i x' := by
  rw [C₁.φ_eq, C₁'.φ_eq, h.ε_eq x x' hx, h.coroot_eq x x' hx]

lemma unit : IsColourRel (unit.{u} D) (unit.{v} D) i fun _ _ ↦ True where
  ε_eq _ _ _ := rfl
  coroot_eq _ _ _ := rfl
  f_rel _ _ _ := Or.inl ⟨rfl, rfl⟩

lemma tensor (h₁ : IsColourRel C₁ C₁' i r₁) (h₂ : IsColourRel C₂ C₂' i r₂) :
    IsColourRel (C₁.tensor C₂) (C₁'.tensor C₂') i fun x x' ↦ r₁ x.1 x'.1 ∧ r₂ x.2 x'.2 where
  ε_eq x x' hx := by
    rw [tensor_ε, tensor_ε, h₁.ε_eq _ _ hx.1, h₂.ε_eq _ _ hx.2, h₁.coroot_eq _ _ hx.1]
  coroot_eq x x' hx := by
    rw [tensor_wt, tensor_wt, map_add, map_add, h₁.coroot_eq _ _ hx.1, h₂.coroot_eq _ _ hx.2]
  f_rel x x' hx := by
    rw [tensor_f, tensor_f, h₂.ε_eq _ _ hx.2, h₁.φ_eq hx.1]
    split_ifs
    · rcases h₁.f_rel _ _ hx.1 with ⟨h, h'⟩ | ⟨y, y', h, h', hy⟩
      · exact Or.inl ⟨by rw [h]; rfl, by rw [h']; rfl⟩
      · exact Or.inr ⟨(y, x.2), (y', x'.2), by rw [h]; rfl, by rw [h']; rfl, hy, hx.2⟩
    · rcases h₂.f_rel _ _ hx.2 with ⟨h, h'⟩ | ⟨y, y', h, h', hy⟩
      · exact Or.inl ⟨by rw [h]; rfl, by rw [h']; rfl⟩
      · exact Or.inr ⟨(x.1, y), (x'.1, y'), by rw [h]; rfl, by rw [h']; rfl, hx.1, hy⟩

variable {C' : Crystal D B'} {r : B → B' → Prop}

lemma tensorPow (h : IsColourRel C C' i r) :
    (n : ℕ) → IsColourRel (C.tensorPow n) (C'.tensorPow n) i (TPow.Forall₂ r)
  | 0 => unit
  | n + 1 => h.tensor (tensorPow h n)

lemma fIter {β β' : Type*} {E : Crystal D β} {E' : Crystal D β'} {s : β → β' → Prop}
    (h : IsColourRel E E' i s) (n : ℕ) {x : β} {x' : β'} (hx : s x x') :
    OptRel s (E.fIter i n x) (E'.fIter i n x') := by
  induction n with
  | zero => exact Or.inr ⟨x, x', rfl, rfl, hx⟩
  | succ n ih =>
    rw [fIter_succ', fIter_succ']
    rcases ih with ⟨h1, h1'⟩ | ⟨y, y', h1, h1', hy⟩
    · exact Or.inl ⟨by rw [h1]; rfl, by rw [h1']; rfl⟩
    · rw [h1, h1', Option.bind_some, Option.bind_some]
      exact h.f_rel y y' hy

/-- `f̃ᵢʳ` acts in the same way on tuples related entrywise by a relation compatible with `i`. -/
theorem fIter_tensorPow (h : IsColourRel C C' i r) {n : ℕ} (k : ℕ) {x : TPow B n}
    {x' : TPow B' n} (hx : TPow.Forall₂ r x x') :
    OptRel (TPow.Forall₂ r) ((C.tensorPow n).fIter i k x) ((C'.tensorPow n).fIter i k x') :=
  (h.tensorPow n).fIter k hx

end IsColourRel

end ColourRel

end Crystal
