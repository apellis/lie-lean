/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Words
import LieLean.Algebra.Lie.KacMoody.InvariantForm

/-!
# The leading term of `⟨v_λ^*, x_{k₁} ⋯ x_{kₚ} y_{l₁} ⋯ y_{lₚ} v_λ⟩`

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra over a field of characteristic zero. Suppose given root
vectors `x_k ∈ 𝔤_{α_k}` and `y_k ∈ 𝔤_{-α_k}` (`α_k ∈ Q₊ \ 0`) and elements `t_k ∈ 𝔥`, indexed by a
type `κ`, with `[x_k, y_k] = t_k` and `[x_k, y_l] = 0` if `k ≠ l` and `α_k = α_l`
(`Matrix.Realization.KacMoodyAlgebra.PairedRootVectors`). For lists `k₁, …, kₚ` and `l₁, …, lₚ`
of indices, the function `λ ↦ ⟨v_λ^*, x_{k₁} ⋯ x_{kₚ} y_{l₁} ⋯ y_{lₚ} v_λ⟩` is a polynomial of
degree at most `p` (`wordFn_mem_polyLE`), and its homogeneous component of degree `p` is
`∏_k m_k! ∏ᵢ λ(t_{kᵢ})` if the multisets `{kᵢ}` and `{lᵢ}` agree (`m_k` being the multiplicity
of `k`), and zero otherwise (`Matrix.Realization.KacMoodyAlgebra.PairedRootVectors.hasTop_wordFn`).

This is the key computation for the leading term of the Shapovalov determinant ([KK];
cf. [Kum] Thm. 2.3.4, proof, Step 2 (3)).
The proof is by induction: moving `x_{k₁}` to the right, the commutators `[x_{k₁}, x_{kᵢ}] ∈ 𝔫₊`
and `[x_{k₁}, y_{lⱼ}] ∈ 𝔫₊ ∪ 𝔫₋` (for `α_{k₁} ≠ α_{lⱼ}`) lower the degree bound, and only the
commutators `[x_{k₁}, y_{lⱼ}] = t_{k₁}` with `lⱼ = k₁` contribute to the top component. To run the
induction we allow further letters `h(a) ∈ 𝔥` among the `y`'s. The argument is our
reconstruction.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.PairedRootVectors`: the data `(α_k, t_k, x_k, y_k)`.
* `Matrix.Realization.KacMoodyAlgebra.PairedRootVectors.word`: the word
  `x_{k₁} ⋯ x_{kₚ} z₁ ⋯ z_q` with each `zⱼ` of the form `y_l` or `h(a)`.
* `Matrix.Realization.KacMoodyAlgebra.PairedRootVectors.topPoly`: its top homogeneous component.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.PairedRootVectors.hasTop_wordFn`: the leading term.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §2.3.
-/

open Module LieModule Module.Dual MvPolynomial

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- An element of a root space `𝔤_μ`, `μ ≠ 0`, lies in `𝔫₊` or in `𝔫₋`. -/
lemma mem_nPos_or_mem_nNeg_of_mem_rootSpace [CharZero K] {μ : Dual K H} (hμ : μ ≠ 0)
    {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P μ) : z ∈ nPos P ∨ z ∈ nNeg P := by
  by_cases hp : μ ∈ P.posWeights
  · left
    rw [← LieSubalgebra.mem_toSubmodule, nPos_toSubmodule_eq]
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hp hz)
  by_cases hn : μ ∈ P.negWeights
  · right
    rw [← LieSubalgebra.mem_toSubmodule, nNeg_toSubmodule_eq]
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hn hz)
  have hμ' : μ ∉ AuxLieAlgebra.allWeights P := by
    simp [AuxLieAlgebra.allWeights, hp, hn, hμ]
  rw [rootSpace_eq_map, AuxLieAlgebra.rootSpace_eq_bot P hμ', Submodule.map_bot] at hz
  left
  rw [(Submodule.mem_bot K).mp hz]
  exact zero_mem _

/-- Root vectors `x_k ∈ 𝔤_{α_k} ⊆ 𝔫₊`, `y_k ∈ 𝔤_{-α_k} ⊆ 𝔫₋` and `t_k ∈ 𝔥` with `[x_k, y_k] = t_k`
and `[x_k, y_l] = 0` for `k ≠ l` with `α_k = α_l`. -/
structure PairedRootVectors (κ : Type*) where
  /-- The root `α_k`. -/
  root : κ → Dual K H
  /-- The element `t_k ∈ 𝔥`. -/
  coroot : κ → H
  /-- The root vector `x_k ∈ 𝔤_{α_k}`. -/
  left : κ → nPos P
  /-- The root vector `y_k ∈ 𝔤_{-α_k}`. -/
  right : κ → nNeg P
  root_ne_zero : ∀ k, root k ≠ 0
  left_mem : ∀ k, (left k : P.KacMoodyAlgebra) ∈ rootSpace P (root k)
  right_mem : ∀ k, (right k : P.KacMoodyAlgebra) ∈ rootSpace P (-root k)
  lie_left_right_self : ∀ k, ⁅(left k : P.KacMoodyAlgebra), (right k : P.KacMoodyAlgebra)⁆ =
    h P (coroot k)
  lie_left_right_of_ne : ∀ k l, k ≠ l → root k = root l →
    ⁅(left k : P.KacMoodyAlgebra), (right l : P.KacMoodyAlgebra)⁆ = 0

/-- The product `∏_k (m_k)!` of the factorials of the multiplicities of a multiset. -/
def Multiset.factorialProd {κ : Type*} [DecidableEq κ] (m : Multiset κ) : ℕ :=
  ∏ k ∈ m.toFinset, (m.count k).factorial

lemma Multiset.factorialProd_cons {κ : Type*} [DecidableEq κ] (k : κ) (m : Multiset κ) :
    Multiset.factorialProd (k ::ₘ m) = (m.count k + 1) * Multiset.factorialProd m := by
  unfold Multiset.factorialProd
  by_cases hk : k ∈ m
  · have hts : (k ::ₘ m).toFinset = m.toFinset := by
      ext; simp only [Multiset.mem_toFinset, Multiset.mem_cons]
      exact ⟨fun h ↦ h.elim (· ▸ hk) id, Or.inr⟩
    rw [hts, ← Finset.mul_prod_erase _ _ (Multiset.mem_toFinset.mpr hk),
      ← Finset.mul_prod_erase _ _ (Multiset.mem_toFinset.mpr hk), Multiset.count_cons_self,
      Nat.factorial_succ, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun j hj ↦ by
      rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hj)]
  · rw [Multiset.toFinset_cons, Finset.prod_insert (by simpa using hk), Multiset.count_cons_self,
      Multiset.count_eq_zero.mpr hk, zero_add, Nat.factorial_one, one_mul, one_mul]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hjk : j ≠ k := fun h ↦ hk (h ▸ Multiset.mem_toFinset.mp hj)
    rw [Multiset.count_cons_of_ne hjk]

namespace PairedRootVectors

section Lists

variable {κ α : Type*}

/-- The indices `l` of the letters `y_l` in `r`. -/
def lefts (r : List (κ ⊕ α)) : List κ := r.filterMap Sum.getLeft?

/-- The elements `a` of the letters `h(a)` in `r`. -/
def rights (r : List (κ ⊕ α)) : List α := r.filterMap Sum.getRight?

@[simp] lemma lefts_nil : lefts ([] : List (κ ⊕ α)) = [] := rfl
@[simp] lemma rights_nil : rights ([] : List (κ ⊕ α)) = [] := rfl
@[simp] lemma lefts_cons_inl (k : κ) (r : List (κ ⊕ α)) : lefts (.inl k :: r) = k :: lefts r :=
  rfl
@[simp] lemma lefts_cons_inr (a : α) (r : List (κ ⊕ α)) : lefts (.inr a :: r) = lefts r := rfl
@[simp] lemma rights_cons_inl (k : κ) (r : List (κ ⊕ α)) : rights (.inl k :: r) = rights r := rfl
@[simp] lemma rights_cons_inr (a : α) (r : List (κ ⊕ α)) : rights (.inr a :: r) = a :: rights r :=
  rfl
@[simp] lemma lefts_append (r r' : List (κ ⊕ α)) : lefts (r ++ r') = lefts r ++ lefts r' :=
  List.filterMap_append
@[simp] lemma rights_append (r r' : List (κ ⊕ α)) : rights (r ++ r') = rights r ++ rights r' :=
  List.filterMap_append

end Lists

end PairedRootVectors


section Step

variable [CharZero K]

open TriLetter

/-- A word whose degree bound is smaller than `d` has no component of degree `d`. -/
lemma hasTop_zero_of_deg_lt {w : List (TriLetter P)} {d : ℕ} (hw : deg w < d) :
    HasTop d 0 (wordFn P (w.map val)) :=
  HasTop.of_mem_polyLE (wordFn_mem_polyLE P w) hw

/-- Moving a letter `x ∈ 𝔫₊` to the right across letters of `𝔫₊` does not change the top
component, when the word has at least as many letters in `𝔫₋` as in `𝔫₊`. -/
lemma hasTop_wordFn_pos_cons_append (x : nPos P) (L : List (nPos P))
    (u R : List (TriLetter P)) {d : ℕ} {q : MvPolynomial (PolyIdx K H) K}
    (hd : deg (u ++ TriLetter.pos x :: (L.map TriLetter.pos ++ R)) = d)
    (hle : numPos (u ++ TriLetter.pos x :: (L.map TriLetter.pos ++ R)) ≤
      numNeg (u ++ TriLetter.pos x :: (L.map TriLetter.pos ++ R)))
    (h : HasTop d q (wordFn P ((u ++ L.map TriLetter.pos ++ TriLetter.pos x :: R).map val))) :
    HasTop d q (wordFn P ((u ++ TriLetter.pos x :: (L.map TriLetter.pos ++ R)).map val)) := by
  induction L generalizing u with
  | nil => simpa using h
  | cons x' L ih =>
    have e : (u ++ TriLetter.pos x :: ((x' :: L).map TriLetter.pos ++ R)).map val =
        u.map val ++ (x : P.KacMoodyAlgebra) :: (x' : P.KacMoodyAlgebra) ::
          (L.map TriLetter.pos ++ R).map val := by simp [val]
    rw [e, wordFn_append_cons_cons]
    have h1 := ih (u ++ [TriLetter.pos x']) (by
        rw [← hd]
        simp only [deg, numPos_append, numCart_append, numNeg_append, numPos_cons_pos,
          numCart_cons_pos, numNeg_cons_pos, List.map_cons, List.cons_append, numPos_nil,
          numCart_nil, numNeg_nil]
        omega)
      (by
        simp only [numPos_append, numNeg_append, numPos_cons_pos, numNeg_cons_pos,
          List.map_cons, List.cons_append, numPos_nil, numNeg_nil] at hle ⊢
        omega)
      (by simpa using h)
    have e1 : (u ++ [TriLetter.pos x'] ++ TriLetter.pos x :: (L.map TriLetter.pos ++ R)).map val =
        u.map val ++ [(x' : P.KacMoodyAlgebra)] ++ (x : P.KacMoodyAlgebra) ::
          (L.map TriLetter.pos ++ R).map val := by simp [val]
    rw [e1] at h1
    have h2 := hasTop_zero_of_deg_lt P (w := u ++ TriLetter.pos ⟨⁅(x : P.KacMoodyAlgebra), x'⁆,
      (nPos P).lie_mem x.2 x'.2⟩ :: (L.map TriLetter.pos ++ R)) (d := d) (by
        rw [← hd]
        simp only [deg, numPos_append, numCart_append, numNeg_append, numPos_cons_pos,
          numCart_cons_pos, numNeg_cons_pos, List.map_cons, List.cons_append] at hle ⊢
        omega)
    have e2 : (u ++ TriLetter.pos ⟨⁅(x : P.KacMoodyAlgebra), x'⁆, (nPos P).lie_mem x.2 x'.2⟩ ::
        (L.map TriLetter.pos ++ R)).map val =
          u.map val ++ ⁅(x : P.KacMoodyAlgebra), (x' : P.KacMoodyAlgebra)⁆ ::
          (L.map TriLetter.pos ++ R).map val := by simp [val]
    rw [e2] at h2
    simpa using h1.add h2

end Step

namespace PairedRootVectors

variable {P} {κ : Type*} (D : PairedRootVectors P κ)

open TriLetter

/-- The letter `y_l` (for `inl l`) or `h(a)` (for `inr a`). -/
def rightLetter : κ ⊕ H → TriLetter P
  | .inl k => TriLetter.neg (D.right k)
  | .inr a => TriLetter.cart a

/-- The word `x_{k₁} ⋯ x_{kₚ} z₁ ⋯ z_q`, where `zⱼ = y_l` for `rⱼ = inl l` and `zⱼ = h(a)` for
`rⱼ = inr a`. -/
def word (xs : List κ) (r : List (κ ⊕ H)) : List (TriLetter P) :=
  xs.map (fun k ↦ TriLetter.pos (D.left k)) ++ r.map D.rightLetter

@[simp] lemma numPos_map_pos (xs : List κ) :
    numPos (xs.map (fun k ↦ (TriLetter.pos (D.left k) : TriLetter P))) = xs.length := by
  induction xs <;> simp_all
@[simp] lemma numCart_map_pos (xs : List κ) :
    numCart (xs.map (fun k ↦ (TriLetter.pos (D.left k) : TriLetter P))) = 0 := by
  induction xs <;> simp_all
@[simp] lemma numNeg_map_pos (xs : List κ) :
    numNeg (xs.map (fun k ↦ (TriLetter.pos (D.left k) : TriLetter P))) = 0 := by
  induction xs <;> simp_all
@[simp] lemma numPos_map_rightLetter (r : List (κ ⊕ H)) : numPos (r.map D.rightLetter) = 0 := by
  induction r with
  | nil => rfl
  | cons e r ih => cases e <;> simp [rightLetter, ih]
@[simp] lemma numCart_map_rightLetter (r : List (κ ⊕ H)) :
    numCart (r.map D.rightLetter) = (rights r).length := by
  induction r with
  | nil => rfl
  | cons e r ih => cases e <;> simp [rightLetter, ih]
@[simp] lemma numNeg_map_rightLetter (r : List (κ ⊕ H)) :
    numNeg (r.map D.rightLetter) = (lefts r).length := by
  induction r with
  | nil => rfl
  | cons e r ih => cases e <;> simp [rightLetter, ih]

variable [CharZero K]

/-- `∏ⱼ λ(aⱼ)` over the letters `h(aⱼ)` of `r`, as a polynomial. -/
def cartPoly (r : List (κ ⊕ H)) : MvPolynomial (PolyIdx K H) K :=
  ((rights r).map (linPoly K H)).prod

/-- `∏ᵢ λ(t_{kᵢ})`, as a polynomial. -/
def corootPoly (xs : List κ) : MvPolynomial (PolyIdx K H) K :=
  (xs.map fun k ↦ linPoly K H (D.coroot k)).prod

/-- The top homogeneous component of `λ ↦ ⟨v_λ^*, x_{k₁} ⋯ x_{kₚ} z₁ ⋯ z_q v_λ⟩`:
`∏_k m_k! ∏ⱼ λ(aⱼ) ∏ᵢ λ(t_{kᵢ})` if the multiset of the `kᵢ` is the multiset of the indices of the
letters `y_l` among the `zⱼ`, and `0` otherwise. -/
def topPoly [DecidableEq κ] (xs : List κ) (r : List (κ ⊕ H)) : MvPolynomial (PolyIdx K H) K :=
  if (xs : Multiset κ) = (lefts r : Multiset κ) then
    C (Multiset.factorialProd (xs : Multiset κ) : K) * cartPoly r * D.corootPoly xs
  else 0

omit [CharZero K] in
lemma isHomogeneous_cartPoly (r : List (κ ⊕ H)) :
    (cartPoly (K := K) r).IsHomogeneous (rights r).length := by
  unfold cartPoly
  induction rights r with
  | nil => simpa using isHomogeneous_one (σ := PolyIdx K H) (R := K)
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, add_comm]
    exact (isHomogeneous_linPoly a).mul ih

omit [CharZero K] in
lemma evalPoly_cartPoly (r : List (κ ⊕ H)) (Λ : Dual K H) :
    evalPoly K H (cartPoly r) Λ = ((rights r).map Λ).prod := by
  unfold cartPoly
  induction rights r with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The word consisting only of letters `h(a)`. -/
lemma wordFn_map_rightLetter_of_lefts_eq_nil (r : List (κ ⊕ H)) (hr : lefts r = []) :
    wordFn P ((r.map D.rightLetter).map val) = evalPoly K H (cartPoly r) := by
  ext Λ
  rw [evalPoly_cartPoly]
  induction r with
  | nil => simp
  | cons e r ih =>
    cases e with
    | inl k => simp at hr
    | inr a =>
      simp only [List.map_cons, rightLetter, val, rights_cons_inr, List.prod_cons]
      rw [wordFn_h_cons, Pi.mul_apply, ih (by simpa using hr)]


/-- **The leading term** of `λ ↦ ⟨v_λ^*, x_{k₁} ⋯ x_{kₚ} z₁ ⋯ z_q v_λ⟩`, where each `zⱼ` is a
root vector `y_l` or an element `h(a)` of `𝔥`, and there are as many `y_l`'s as `x_k`'s: it is a
polynomial function of degree at most `p + #{j | zⱼ ∈ 𝔥}`, and its homogeneous component of that
degree is `topPoly`. -/
theorem hasTop_wordFn [DecidableEq κ] (xs : List κ) (r : List (κ ⊕ H))
    (hbal : xs.length = (lefts r).length) :
    HasTop (deg (D.word xs r)) (D.topPoly xs r) (wordFn P ((D.word xs r).map val)) := by
  induction xs generalizing r with
  | nil =>
    have hr : lefts r = [] := List.eq_nil_of_length_eq_zero hbal.symm
    have hdeg : deg (D.word [] r) = (rights r).length := by simp [word, deg, hr]
    have htop : D.topPoly [] r = cartPoly r := by
      simp [topPoly, hr, Multiset.factorialProd, corootPoly]
    rw [hdeg, htop, word, List.map_nil, List.nil_append,
      D.wordFn_map_rightLetter_of_lefts_eq_nil r hr]
    exact HasTop.of_isHomogeneous (isHomogeneous_cartPoly r)
  | cons k xs ih =>
    set d := (rights r).length + (xs.length + 1) with hd
    have hdeg : deg (D.word (k :: xs) r) = d := by
      simp only [word, deg, List.map_cons, List.cons_append, numCart_cons_pos, numPos_cons_pos,
        numNeg_cons_pos, numCart_append, numPos_append, numNeg_append, numCart_map_pos,
        numPos_map_pos, numNeg_map_pos, numCart_map_rightLetter, numPos_map_rightLetter,
        numNeg_map_rightLetter, List.length_cons] at hbal ⊢
      omega
    set V : MvPolynomial (PolyIdx K H) K :=
      if k ::ₘ (xs : Multiset κ) = (lefts r : Multiset κ) then
        C (Multiset.factorialProd (xs : Multiset κ) : K) * cartPoly r *
          (linPoly K H (D.coroot k) * D.corootPoly xs)
      else 0 with hV
    -- moving `x_k` across the letters `zⱼ`
    have step2 : ∀ r₂ r₁ : List (κ ⊕ H), r₁ ++ r₂ = r →
        HasTop d ((lefts r₂).count k • V) (wordFn P ((xs.map (fun k ↦ TriLetter.pos (D.left k)) ++
          r₁.map D.rightLetter ++ TriLetter.pos (D.left k) :: r₂.map D.rightLetter).map val)) := by
      intro r₂
      induction r₂ with
      | nil =>
        intro r₁ _
        have : (xs.map (fun k ↦ (TriLetter.pos (D.left k) : TriLetter P)) ++ r₁.map D.rightLetter ++
            [TriLetter.pos (D.left k)]).map val =
              (xs.map (fun k ↦ (TriLetter.pos (D.left k) : TriLetter P)) ++
              r₁.map D.rightLetter).map val ++ [(D.left k : P.KacMoodyAlgebra)] := by simp [val]
        simp only [List.map_nil, lefts_nil, List.count_nil, zero_smul]
        rw [this, wordFn_append_singleton_of_mem_nPos P (D.left k).2]
        exact HasTop.zero d
      | cons e r₂ ihr =>
        intro r₁ hr
        set U := xs.map (fun k ↦ (TriLetter.pos (D.left k) : TriLetter P)) ++ r₁.map D.rightLetter
        have hsplit := wordFn_append_cons_cons P (U.map val) ((r₂.map D.rightLetter).map val)
          (D.left k) (val (D.rightLetter e))
        have e0 : (U ++ TriLetter.pos (D.left k) :: (e :: r₂).map D.rightLetter).map val =
            U.map val ++ (D.left k : P.KacMoodyAlgebra) :: val (D.rightLetter e) ::
              (r₂.map D.rightLetter).map val := by simp [val]
        rw [e0, hsplit]
        have h1 := ihr (r₁ ++ [e]) (by rw [List.append_assoc]; exact hr)
        have e1 : (xs.map (fun k ↦ (TriLetter.pos (D.left k) : TriLetter P)) ++
            (r₁ ++ [e]).map D.rightLetter ++ TriLetter.pos (D.left k) ::
              r₂.map D.rightLetter).map val =
            U.map val ++ [val (D.rightLetter e)] ++ (D.left k : P.KacMoodyAlgebra) ::
              (r₂.map D.rightLetter).map val := by simp [U, val]
        rw [e1] at h1
        -- the counts of the whole word
        have hcount : xs.length + 1 = (lefts r₁).length + (lefts (e :: r₂)).length := by
          rw [← List.length_append, ← lefts_append, hr]; simpa using hbal
        have hcart : (rights r).length = (rights r₁).length + (rights (e :: r₂)).length := by
          rw [← List.length_append, ← rights_append, hr]
        -- words of smaller degree bound
        have hsmall : ∀ t : TriLetter P, deg (U ++ t :: r₂.map D.rightLetter) < d →
            HasTop d 0 (wordFn P (U.map val ++ val t :: (r₂.map D.rightLetter).map val)) :=
          fun t ht ↦ by simpa using hasTop_zero_of_deg_lt P ht
        cases e with
        | inr a =>
          have h2 := hsmall (TriLetter.pos ⟨⁅(D.left k : P.KacMoodyAlgebra), h P a⁆,
            lie_h_mem_nPos' P (D.left k).2 a⟩) (by
              simp only [U, deg, numCart_append, numPos_append, numNeg_append, numPos_cons_pos,
                numCart_cons_pos, numNeg_cons_pos, numCart_map_pos, numPos_map_pos,
                numNeg_map_pos, numCart_map_rightLetter, numPos_map_rightLetter,
                numNeg_map_rightLetter, lefts_cons_inr, rights_cons_inr,
                List.length_cons] at hcount hcart ⊢
              omega)
          simpa [rightLetter, val] using h1.add h2
        | inl l =>
          by_cases hroot : D.root k = D.root l
          · by_cases hkl : k = l
            · subst hkl
              have hbr : ⁅(D.left k : P.KacMoodyAlgebra), val (D.rightLetter (.inl k))⁆ =
                  val (TriLetter.cart (D.coroot k) : TriLetter P) := D.lie_left_right_self k
              rw [hbr]
              have h2 := ih (r₁ ++ .inr (D.coroot k) :: r₂) (by
                simp only [lefts_append, lefts_cons_inr, List.length_append]
                simp only [lefts_cons_inl, List.length_cons] at hcount
                omega)
              have hw : D.word xs (r₁ ++ .inr (D.coroot k) :: r₂) =
                  U ++ TriLetter.cart (D.coroot k) :: r₂.map D.rightLetter := by
                simp [word, U, rightLetter]
              have hd2 : deg (D.word xs (r₁ ++ .inr (D.coroot k) :: r₂)) = d := by
                rw [hw]
                simp only [U, deg, numCart_append, numPos_append, numNeg_append,
                  numCart_cons_cart, numPos_cons_cart, numNeg_cons_cart, numCart_map_pos,
                  numPos_map_pos, numNeg_map_pos, numCart_map_rightLetter,
                  numPos_map_rightLetter, numNeg_map_rightLetter, lefts_cons_inl,
                  rights_cons_inl, List.length_cons] at hcount hcart ⊢
                omega
              have htop : D.topPoly xs (r₁ ++ .inr (D.coroot k) :: r₂) = V := by
                have hms : ((xs : Multiset κ) = (lefts (r₁ ++ .inr (D.coroot k) :: r₂) :
                    Multiset κ)) ↔ k ::ₘ (xs : Multiset κ) = (lefts r : Multiset κ) := by
                  rw [← hr]
                  simp only [lefts_append, lefts_cons_inr, lefts_cons_inl, ← Multiset.coe_add,
                    ← Multiset.cons_coe]
                  rw [Multiset.add_cons, Multiset.cons_inj_right]
                simp only [topPoly, hV, hms]
                split_ifs
                · rw [← hr]
                  simp only [cartPoly, rights_append, rights_cons_inr, rights_cons_inl,
                    List.map_append, List.map_cons, List.prod_append, List.prod_cons]
                  ring
                · rfl
              rw [hd2, hw, htop] at h2
              have e2 : (U ++ TriLetter.cart (D.coroot k) :: r₂.map D.rightLetter).map val =
                  U.map val ++ val (TriLetter.cart (D.coroot k) : TriLetter P) ::
                    (r₂.map D.rightLetter).map val := by simp
              rw [e2] at h2
              have := h1.add h2
              convert this using 1
              simp only [lefts_cons_inl, List.count_cons_self, add_smul, one_smul]
            · have hbr : ⁅(D.left k : P.KacMoodyAlgebra), val (D.rightLetter (.inl l))⁆ = 0 :=
                D.lie_left_right_of_ne k l hkl hroot
              rw [hbr, wordFn_append_zero]
              have := h1.add (HasTop.zero d)
              convert this using 1
              simp [lefts_cons_inl, Ne.symm hkl]
          · have hmem : ⁅(D.left k : P.KacMoodyAlgebra), val (D.rightLetter (.inl l))⁆ ∈
                rootSpace P (D.root k + -D.root l) :=
              lie_mem_weightSpaceOfMap (h P) (D.left_mem k) (D.right_mem l)
            have hne : D.root k + -D.root l ≠ 0 := by
              rw [← sub_eq_add_neg, sub_ne_zero]; exact hroot
            have hsm : ∀ t : TriLetter P, deg (U ++ t :: r₂.map D.rightLetter) < d →
                val t = ⁅(D.left k : P.KacMoodyAlgebra), val (D.rightLetter (.inl l))⁆ →
                HasTop d ((lefts (.inl l :: r₂)).count k • V)
                  (wordFn P (U.map val ++ [val (D.rightLetter (.inl l))] ++
                    (D.left k : P.KacMoodyAlgebra) :: (r₂.map D.rightLetter).map val) +
                  wordFn P (U.map val ++ ⁅(D.left k : P.KacMoodyAlgebra),
                    val (D.rightLetter (.inl l))⁆ :: (r₂.map D.rightLetter).map val)) := by
              intro t ht hval
              have := h1.add (hsmall t ht)
              rw [hval] at this
              convert this using 1
              have hlk : l ≠ k := fun h ↦ hroot (by rw [h])
              simp [lefts_cons_inl, hlk]
            rcases mem_nPos_or_mem_nNeg_of_mem_rootSpace P hne hmem with hp | hn
            · exact hsm (TriLetter.pos ⟨_, hp⟩) (by
                simp only [U, deg, numCart_append, numPos_append, numNeg_append,
                  numCart_cons_pos, numPos_cons_pos, numNeg_cons_pos, numCart_map_pos,
                  numPos_map_pos, numNeg_map_pos, numCart_map_rightLetter,
                  numPos_map_rightLetter, numNeg_map_rightLetter, lefts_cons_inl,
                  rights_cons_inl, List.length_cons] at hcount hcart ⊢
                omega) rfl
            · exact hsm (TriLetter.neg ⟨_, hn⟩) (by
                simp only [U, deg, numCart_append, numPos_append, numNeg_append,
                  numCart_cons_neg, numPos_cons_neg, numNeg_cons_neg, numCart_map_pos,
                  numPos_map_pos, numNeg_map_pos, numCart_map_rightLetter,
                  numPos_map_rightLetter, numNeg_map_rightLetter, lefts_cons_inl,
                  rights_cons_inl, List.length_cons] at hcount hcart ⊢
                omega) rfl
    -- moving `x_k` across the `x`'s
    have h0 := step2 r [] (List.nil_append r)
    have hmove := hasTop_wordFn_pos_cons_append P (D.left k) (xs.map D.left) []
      (r.map D.rightLetter) (d := d) (q := (lefts r).count k • V)
      (by rw [← hdeg]; simp [word, Function.comp_def])
      (by
        simp only [List.nil_append, numPos_cons_pos, numNeg_cons_pos, numPos_append,
          numNeg_append, List.map_map, Function.comp_def, numPos_map_pos, numNeg_map_pos,
          numPos_map_rightLetter, numNeg_map_rightLetter, List.length_cons] at hbal ⊢
        omega)
      (by simpa [Function.comp_def] using h0)
    have hw : D.word (k :: xs) r = [] ++ TriLetter.pos (D.left k) ::
        ((xs.map D.left).map TriLetter.pos ++
        r.map D.rightLetter) := by simp [word, Function.comp_def]
    rw [hdeg, hw]
    convert hmove using 1
    -- the combinatorial identity
    simp only [topPoly, hV, corootPoly, List.map_cons, List.prod_cons, ← Multiset.cons_coe]
    split_ifs with hms
    · rw [Multiset.factorialProd_cons, ← Multiset.coe_count, ← hms, Multiset.count_cons_self,
        nsmul_eq_mul]
      push_cast
      rw [map_mul, map_add, map_one, map_natCast]
      simp only [Multiset.coe_count]
      ring
    · simp

end PairedRootVectors

end Matrix.Realization.KacMoodyAlgebra
