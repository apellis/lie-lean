/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.RootSpace

/-!
# The supersymmetric form on `G̃(A, τ)`: invariance

We prove that the form `(·|·)` of `Super/InvariantForm.lean` on `G̃ = G̃(A, τ)` satisfies
`[x, y] = (x | y) ν⁻¹(μ)` for `x ∈ G̃_μ`, `y ∈ G̃_{-μ}` (`C_μ`), is invariant,
`([x, y] | z) = (x | [y, z])` for all `x, y, z ∈ G̃`, and has radical the maximal ideal `R`
([Kac78] Prop. 1.5).

The proof follows the even case (`LieLean/Algebra/Lie/KacMoody/InvariantFormAux.lean`), with super
signs. For homogeneous `x, y, z` of weights `α, β, γ` with `α + β + γ = 0`, the super Jacobi
identity and `C_α, C_β, C_γ` give
`(x | [y, z]) α = ([x, y] | z) (α + β) + (-1)^{|x||y|} (y | [x, z]) β`,
so `(x | [y, z]) = ([x, y] | z)` and `([x, y] | z) = -(-1)^{|x||y|} (y | [x, z])` when `α, β` are
linearly independent. When `y` has weight `±αₖ` and `α, β` are dependent, either one of `x, z`
has weight `0`, or two of `x, y, z` are proportional (they lie in `G̃_{±αₖ} = K e_k` or `K f_k`),
and the super Jacobi identity for a repeated odd element gives the claim; here
`G̃_{±2αₖ} = K [eₖ, eₖ]` (resp. `K [fₖ, fₖ]`) is used, which vanishes for `k` even. `C_μ` is then
proved by induction on the height of `μ`. Full invariance follows since the elements `y` with
`([x, y] | z) = (x | [y, z])` for all `x, z` contain the generators and are closed under the
super bracket. The radical is an ideal meeting `𝔥` trivially, so it lies in `R`; conversely
`([R, G̃] | 𝔥) = 0` and nondegeneracy on `𝔥` give `(R | G̃) = 0`.

## Main results

* `Matrix.Realization.SuperEnveloping.lieEqForm_root`: `C_{αᵢ}`.
* `Matrix.Realization.SuperEnveloping.invTriple_of_root`: invariance for a triple whose middle
  element has weight `±αₖ`.
* `Matrix.Realization.SuperEnveloping.lieEqForm`: `C_μ` for every `μ`.
* `Matrix.Realization.SuperEnveloping.invForm_superBracket`: invariance on `G̃`.
* `Matrix.Realization.SuperEnveloping.invForm_eq_zero_of_mem_maxIdeal`,
  `Matrix.Realization.SuperEnveloping.mem_maxIdeal_iff`: the radical of the form on `G̃` is `R`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.4–1.5.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Thm. 2.2.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2) [CharZero K]

namespace SuperEnveloping

/-! ### Negative root spaces -/

lemma omega_mem_gTilde {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) :
    omega P p x ∈ gTilde P p := by
  have h1 : nPlus P p ≤ (gTilde P p).comap (omega P p).toLinearMap := fun y hy ↦
    nMinus_le_gTilde P p (omega_mem_nMinus P p hy)
  have h2 : nMinus P p ≤ (gTilde P p).comap (omega P p).toLinearMap := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply]
    have : omega P p (omega P p y) = parity P p y :=
      congrArg (fun φ : P.SuperEnveloping p →ₐ[K] _ ↦ φ y) (omega_comp_omega P p)
    rw [this]
    exact parity_mem_gTilde P p (nPlus_le_gTilde P p hy)
  have h3 : LinearMap.range (h P p) ≤ (gTilde P p).comap (omega P p).toLinearMap := by
    rintro _ ⟨a, rfl⟩
    simpa using neg_mem (h_mem_gTilde P p a)
  exact (sup_le (sup_le h2 h3) h1 : gTilde P p ≤ _) hx

/-- Every element of `G̃_{-μ}` is the image under `ω` of an element of `G̃_μ`. -/
lemma exists_omega_eq {μ : Dual K H} {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxμ : x ∈ weightSpace P p (-μ)) :
    ∃ y ∈ gTilde P p, y ∈ weightSpace P p μ ∧ omega P p y = x := by
  refine ⟨omega P p (parity P p x), omega_mem_gTilde P p (parity_mem_gTilde P p hx), ?_, ?_⟩
  · simpa using omega_mem_weightSpace P p (parity_mem_weightSpace P p hxμ)
  · have : omega P p (omega P p (parity P p x)) = parity P p (parity P p x) :=
      congrArg (fun φ : P.SuperEnveloping p →ₐ[K] _ ↦ φ _) (omega_comp_omega P p)
    rw [this, parity_parity]

/-- `G̃_{-αᵢ} = K fᵢ`. -/
theorem mem_weightSpace_neg_root {i : ι} {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxi : x ∈ weightSpace P p (-P.root i)) : ∃ c : K, x = c • f P p i := by
  obtain ⟨y, hy, hyi, rfl⟩ := exists_omega_eq P p hx hxi
  obtain ⟨c, rfl⟩ := mem_weightSpace_root P p hy hyi
  exact ⟨c, by simp⟩

/-- `G̃_{-2αᵢ} = K [fᵢ, fᵢ]`. -/
theorem mem_weightSpace_neg_two_root {i : ι} {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxi : x ∈ weightSpace P p (-(2 • P.root i))) :
    ∃ c : K, x = c • superBracket P p (f P p i) (f P p i) := by
  obtain ⟨y, hy, hyi, rfl⟩ := exists_omega_eq P p hx hxi
  obtain ⟨c, rfl⟩ := mem_weightSpace_two_root P p hy hyi
  exact ⟨c, by simp [omega_superBracket]⟩

/-- `G̃_{-mαᵢ} = 0` for `m ≥ 3`. -/
theorem eq_zero_of_mem_weightSpace_neg_nsmul_root {i : ι} {m : ℕ} (hm : 3 ≤ m)
    {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxi : x ∈ weightSpace P p (-(m • P.root i))) : x = 0 := by
  obtain ⟨y, hy, hyi, rfl⟩ := exists_omega_eq P p hx hxi
  rw [eq_zero_of_mem_weightSpace_nsmul_root P p hm hy hyi, map_zero]

/-! ### Weights proportional to a simple root -/

/-- A positive weight of `G̃` which is a multiple of `αₖ` is `αₖ` or `2αₖ`. -/
lemma eq_nsmul_root_of_mem_posWeights {μ : Dual K H} (hμ : μ ∈ P.posWeights)
    {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) (hxμ : x ∈ weightSpace P p μ) (hx0 : x ≠ 0)
    {k : ι} {c : K} (hc : μ = c • P.root k) : μ = P.root k ∨ μ = 2 • P.root k := by
  obtain ⟨a, ⟨ha0, ha⟩, rfl⟩ := hμ
  have hsum' : ∑ l, (a l : K) • P.root l - ∑ l, (if l = k then c else 0) • P.root l = 0 := by
    rw [← rootOf_apply, hc]
    simp [ite_smul]
  have hsum : ∑ l, ((a l : K) - if l = k then c else 0) • P.root l = 0 := by
    rw [← hsum', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ ↦ by module
  have hal : ∀ l, l ≠ k → a l = 0 := fun l hl ↦ by
    have := Fintype.linearIndependent_iff.mp P.linearIndependent_root _ hsum l
    simpa [hl] using this
  set n := (a k).toNat with hn
  have hak : a = n • Pi.single k 1 := by
    ext l
    by_cases hl : l = k
    · subst hl; simp [hn, Int.toNat_of_nonneg (ha0 l)]
    · simp [hl, hal l hl]
  have hμn : P.rootOf a = n • P.root k := by rw [hak, rootOf_nsmul_single]
  have hn0 : n ≠ 0 := by
    rintro h0
    exact ha (by rw [hak, h0, zero_smul])
  rw [hμn] at hxμ ⊢
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · rcases (show n = 1 ∨ n = 2 by omega) with h1 | h2
    · left; rw [h1, one_smul]
    · right; rw [h2]
  · exact absurd (eq_zero_of_mem_weightSpace_nsmul_root P p hn3 hx hxμ) hx0

/-- A nonzero weight of `G̃` which is a multiple of `αₖ` is `±αₖ` or `±2αₖ`. -/
lemma eq_nsmul_root_or_neg {μ : Dual K H} {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxμ : x ∈ weightSpace P p μ) (hx0 : x ≠ 0) (hμ0 : μ ≠ 0) {k : ι} {c : K}
    (hc : μ = c • P.root k) :
    μ = P.root k ∨ μ = 2 • P.root k ∨ μ = -P.root k ∨ μ = -(2 • P.root k) := by
  rcases mem_allWeights P p hx hxμ hx0 with (hμ | hμ) | hμ
  · obtain ⟨y, hy, hyμ, rfl⟩ := exists_omega_eq P p hx (show x ∈ weightSpace P p (-(-μ)) by
      rwa [neg_neg])
    have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
    rcases eq_nsmul_root_of_mem_posWeights P p ((AuxLieAlgebra.mem_negWeights_iff P).mp hμ)
      hy hyμ hy0 (c := -c) (by rw [hc]; module) with h | h
    · right; right; left; rw [← h, neg_neg]
    · right; right; right; rw [← h, neg_neg]
  · exact absurd hμ hμ0
  · rcases eq_nsmul_root_of_mem_posWeights P p hμ hx hxμ hx0 hc with h | h
    · left; exact h
    · right; left; exact h

/-! ### Parities in `G̃_{±αₖ}` -/

lemma zSign_injective : Function.Injective (zSign K) := by
  intro a b hab
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [zSign_zero, zSign_one] at hab; norm_num at hab
  · rw [zSign_zero, zSign_one] at hab; norm_num at hab
  · rfl

lemma eq_of_isHomog_of_isHomog {a b : ZMod 2} {x : P.SuperEnveloping p} (hx0 : x ≠ 0)
    (ha : IsHomog P p a x) (hb : IsHomog P p b x) : a = b := by
  refine zSign_injective (K := K) ?_
  have : (zSign K a - zSign K b) • x = 0 := by rw [sub_smul, ← ha, ← hb, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hx0)

/-- A nonzero homogeneous element of `G̃_{αₖ}` or `G̃_{-αₖ}` has parity `p k`. -/
lemma parity_eq_of_mem_root {k : ι} {b : ZMod 2} {y : P.SuperEnveloping p} (hy : y ∈ gTilde P p)
    (hyk : y ∈ weightSpace P p (P.root k) ∨ y ∈ weightSpace P p (-P.root k)) (hy0 : y ≠ 0)
    (hyb : IsHomog P p b y) : b = p k := by
  refine eq_of_isHomog_of_isHomog P p hy0 hyb ?_
  rcases hyk with hyk | hyk
  · obtain ⟨c, rfl⟩ := mem_weightSpace_root P p hy hyk
    exact (isHomog_e P p k).smul c
  · obtain ⟨c, rfl⟩ := mem_weightSpace_neg_root P p hy hyk
    exact (isHomog_f P p k).smul c

/-- For `k` even, `[eₖ, eₖ] = 0`. -/
lemma superBracket_e_e_of_even {k : ι} (hk : p k = 0) :
    superBracket P p (e P p k) (e P p k) = 0 := by
  rw [superBracket_of_isHomog (isHomog_e P p k) (isHomog_e P p k), hk, mul_zero, zSign_zero,
    one_smul, sub_self]

/-- For `k` even, `[fₖ, fₖ] = 0`. -/
lemma superBracket_f_f_of_even {k : ι} (hk : p k = 0) :
    superBracket P p (f P p k) (f P p k) = 0 := by
  rw [superBracket_of_isHomog (isHomog_f P p k) (isHomog_f P p k), hk, mul_zero, zSign_zero,
    one_smul, sub_self]

/-- For `k` even, `G̃_{2αₖ} = G̃_{-2αₖ} = 0`. -/
lemma eq_zero_of_mem_two_root_of_even {k : ι} (hk : p k = 0) {x : P.SuperEnveloping p}
    (hx : x ∈ gTilde P p)
    (hxk : x ∈ weightSpace P p (2 • P.root k) ∨ x ∈ weightSpace P p (-(2 • P.root k))) :
    x = 0 := by
  rcases hxk with hxk | hxk
  · obtain ⟨c, rfl⟩ := mem_weightSpace_two_root P p hx hxk
    rw [superBracket_e_e_of_even P p hk, smul_zero]
  · obtain ⟨c, rfl⟩ := mem_weightSpace_neg_two_root P p hx hxk
    rw [superBracket_f_f_of_even P p hk, smul_zero]

omit [CharZero K] in
@[simp] lemma superBracket_zero_right (x : P.SuperEnveloping p) : superBracket P p x 0 = 0 :=
  (superBracketRight P p x).map_zero

/-- Two elements of `G̃_{±αₖ}` are proportional. -/
lemma exists_smul_eq_of_mem_root {β : Dual K H} {k : ι} (hβk : β = P.root k ∨ β = -P.root k)
    {x y : P.SuperEnveloping p} (hx : x ∈ gTilde P p) (hxβ : x ∈ weightSpace P p β)
    (hy : y ∈ gTilde P p) (hyβ : y ∈ weightSpace P p β) (hy0 : y ≠ 0) : ∃ c : K, x = c • y := by
  rcases hβk with rfl | rfl
  · obtain ⟨c, rfl⟩ := mem_weightSpace_root P p hx hxβ
    obtain ⟨d, rfl⟩ := mem_weightSpace_root P p hy hyβ
    have hd : d ≠ 0 := by rintro rfl; exact hy0 (zero_smul _ _)
    exact ⟨c / d, by rw [smul_smul, div_mul_cancel₀ c hd]⟩
  · obtain ⟨c, rfl⟩ := mem_weightSpace_neg_root P p hx hxβ
    obtain ⟨d, rfl⟩ := mem_weightSpace_neg_root P p hy hyβ
    have hd : d ≠ 0 := by rintro rfl; exact hy0 (zero_smul _ _)
    exact ⟨c / d, by rw [smul_smul, div_mul_cancel₀ c hd]⟩

/-- For `β = ±αₖ` with `k` even, `G̃_{±2β} = 0`. -/
lemma eq_zero_of_mem_two_of_even {β : Dual K H} {k : ι} (hk : p k = 0)
    (hβk : β = P.root k ∨ β = -P.root k) {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxβ : x ∈ weightSpace P p (β + β) ∨ x ∈ weightSpace P p (-(β + β))) : x = 0 := by
  refine eq_zero_of_mem_two_root_of_even P p hk hx ?_
  rcases hβk with rfl | rfl <;> rcases hxβ with h | h
  · left; rwa [two_nsmul]
  · right; rwa [two_nsmul]
  · right; rwa [two_nsmul, neg_add]
  · left; rwa [two_nsmul, ← neg_neg (P.root k + P.root k), neg_add]

/-- For `β = ±αₖ`, `G̃_{-3β} = 0`. -/
lemma eq_zero_of_mem_three {β : Dual K H} {k : ι} (hβk : β = P.root k ∨ β = -P.root k)
    {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxβ : x ∈ weightSpace P p (-(β + β + β))) : x = 0 := by
  rcases hβk with rfl | rfl
  · rw [show P.root k + P.root k + P.root k = 3 • P.root k by abel] at hxβ
    exact eq_zero_of_mem_weightSpace_neg_nsmul_root P p le_rfl hx hxβ
  · rw [show -(-P.root k + -P.root k + -P.root k) = 3 • P.root k by abel] at hxβ
    exact eq_zero_of_mem_weightSpace_nsmul_root P p le_rfl hx hxβ

/-! ### `C_{αᵢ}` and invariance for triples -/

section Invariance

variable [FiniteDimensional K H] (S : A.Symmetrization)

/-- `C_{αᵢ}`. -/
lemma lieEqForm_root (i : ι) : LieEqForm P p S (P.root i) := by
  refine lieEqForm_of_exists (P.linearIndependent_root.ne_zero i) fun x hx hxμ y hy hyμ ↦ ?_
  obtain ⟨c, rfl⟩ := mem_weightSpace_root P p hx hxμ
  obtain ⟨d, rfl⟩ := mem_weightSpace_neg_root P p hy hyμ
  have hε : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  have hef : superBracket P p (e P p i) (f P p i) = h P p (P.coroot i) := by
    simp [superBracket_e_f]
  refine ⟨c * d * S.ε i, ?_⟩
  rw [superBracket_smul_left, superBracket_smul_right, hef, toDual_symm_root, map_smul, smul_smul,
    smul_smul, mul_assoc, mul_inv_cancel₀ hε, mul_one]

/-- The invariance identities for a triple of homogeneous elements `x, y, z` of parities `a, b`
and `c`: `(x | [y, z]) = ([x, y] | z)` and `([x, y] | z) = -(-1)^{ab} (y | [x, z])`. -/
def InvTriple (a b : ZMod 2) (x y z : P.SuperEnveloping p) : Prop :=
  invForm P p S x (superBracket P p y z) = invForm P p S (superBracket P p x y) z ∧
    invForm P p S (superBracket P p x y) z =
      -(zSign K (a * b) * invForm P p S y (superBracket P p x z))

variable {P p S}

omit [CharZero K] in
lemma invTriple_of_left_eq_zero {a b : ZMod 2} {x y z : P.SuperEnveloping p} (hx : x = 0) :
    InvTriple P p S a b x y z := by
  subst hx; simp [InvTriple, superBracket_zero_left]

omit [CharZero K] in
lemma invTriple_of_middle_eq_zero {a b : ZMod 2} {x y z : P.SuperEnveloping p} (hy : y = 0) :
    InvTriple P p S a b x y z := by
  subst hy; simp [InvTriple, superBracket_zero_left]

omit [CharZero K] in
lemma invTriple_of_right_eq_zero {a b : ZMod 2} {x y z : P.SuperEnveloping p} (hz : z = 0) :
    InvTriple P p S a b x y z := by
  subst hz; simp [InvTriple]

lemma eq_of_smul_h_eq {μ : Dual K H} (hμ : μ ≠ 0) {A B : K}
    (h2 : (2 : K) • ((A - B) • h P p ((P.toDual S).symm μ)) = 0) : A = B := by
  have hu : h P p ((P.toDual S).symm μ) ≠ 0 := fun h0 ↦ hμ (by
    simpa using (injective_iff_map_eq_zero _).1 (h_injective P p) _ h0)
  exact sub_eq_zero.1 ((smul_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left two_ne_zero)).resolve_right
    hu)

/-- Invariance for a triple whose first two weights are linearly independent. -/
lemma invTriple_of_linearIndependent {α β : Dual K H} {a b c : ZMod 2}
    {x y z : P.SuperEnveloping p}
    (hα : LieEqForm P p S α) (hβ : LieEqForm P p S β) (hαβ : LieEqForm P p S (α + β))
    (hx : x ∈ gTilde P p) (hxα : x ∈ weightSpace P p α) (hxa : IsHomog P p a x)
    (hy : y ∈ gTilde P p) (hyβ : y ∈ weightSpace P p β) (hyb : IsHomog P p b y)
    (hz : z ∈ gTilde P p) (hzγ : z ∈ weightSpace P p (-(α + β))) (hzc : IsHomog P p c z)
    (hind : LinearIndependent K ![α, β]) : InvTriple P p S a b x y z := by
  have e1 := hα x hx hxα _ (superBracket_mem_gTilde P p hy hz)
    ((show β + -(α + β) = -α by abel) ▸ superBracket_mem_weightSpace hyβ hzγ)
  have e2 := hαβ _ (superBracket_mem_gTilde P p hx hy) (superBracket_mem_weightSpace hxα hyβ) z
    hz hzγ
  have e3 := hβ y hy hyβ _ (superBracket_mem_gTilde P p hx hz)
    ((show α + -(α + β) = -β by abel) ▸ superBracket_mem_weightSpace hxα hzγ)
  have hJ := superBracket_jacobi hxa hyb hzc
  rw [e1, e2, e3, map_add, map_add] at hJ
  set A := invForm P p S x (superBracket P p y z)
  set B := invForm P p S (superBracket P p x y) z
  set C := invForm P p S y (superBracket P p x z)
  have key : (A - B) • α + (-B - zSign K (a * b) * C) • β = 0 := by
    have : h P p ((P.toDual S).symm ((A - B) • α + (-B - zSign K (a * b) * C) • β)) = 0 := by
      rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
      linear_combination (norm := module) hJ
    exact (P.toDual S).symm.map_eq_zero_iff.1
      ((injective_iff_map_eq_zero _).1 (h_injective P p) _ this)
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hind _ _ key
  exact ⟨sub_eq_zero.1 h1, by linear_combination -h2⟩

/-- Invariance when the first element has weight `0`. -/
lemma invTriple_of_weight_zero_left {β : Dual K H} {a b : ZMod 2} {x y z : P.SuperEnveloping p}
    (hβ : LieEqForm P p S β) (hx : x ∈ gTilde P p) (hx0 : x ∈ weightSpace P p 0)
    (hxa : IsHomog P p a x) (hy : y ∈ gTilde P p) (hyβ : y ∈ weightSpace P p β)
    (hz : z ∈ gTilde P p) (hzβ : z ∈ weightSpace P p (-β)) : InvTriple P p S a b x y z := by
  obtain ⟨t, rfl⟩ : x ∈ LinearMap.range (h P p) := by
    rw [← gTilde_inf_weightSpace_zero P p]; exact ⟨hx, hx0⟩
  by_cases ht : h P p t = 0
  · exact invTriple_of_left_eq_zero ht
  obtain rfl : a = 0 := eq_of_isHomog_of_isHomog P p ht hxa (isHomog_h P p t)
  have e1 : invForm P p S (h P p t) (superBracket P p y z) = β t * invForm P p S y z := by
    rw [hβ y hy hyβ z hz hzβ, map_smul, invForm_h_h, bilinForm_toDual_symm_right, smul_eq_mul,
      mul_comm]
  have e2 : invForm P p S (superBracket P p (h P p t) y) z = β t * invForm P p S y z := by
    rw [superBracket_h_of_mem_weightSpace P p t hyβ, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have e3 : invForm P p S y (superBracket P p (h P p t) z) = -(β t * invForm P p S y z) := by
    rw [superBracket_h_of_mem_weightSpace P p t hzβ, map_smul, smul_eq_mul, LinearMap.neg_apply,
      neg_mul]
  refine ⟨e1.trans e2.symm, ?_⟩
  rw [e2, e3, zero_mul, zSign_zero, one_mul, neg_neg]

/-- Invariance when the third element has weight `0`. -/
lemma invTriple_of_weight_zero_right {α : Dual K H} {a b : ZMod 2} {x y z : P.SuperEnveloping p}
    (hα : LieEqForm P p S α) (hx : x ∈ gTilde P p) (hxα : x ∈ weightSpace P p α)
    (hxa : IsHomog P p a x) (hy : y ∈ gTilde P p) (hyα : y ∈ weightSpace P p (-α))
    (hyb : IsHomog P p b y) (hz : z ∈ gTilde P p) (hz0 : z ∈ weightSpace P p 0) :
    InvTriple P p S a b x y z := by
  obtain ⟨t, rfl⟩ : z ∈ LinearMap.range (h P p) := by
    rw [← gTilde_inf_weightSpace_zero P p]; exact ⟨hz, hz0⟩
  have hs := invForm_swap P p S hx hxα hxa hy hyα hyb
  unfold InvTriple
  rw [superBracket_swap (isHomog_h P p t) hyb, superBracket_swap (isHomog_h P p t) hxa,
    superBracket_h_of_mem_weightSpace P p t hyα, superBracket_h_of_mem_weightSpace P p t hxα,
    hα x hx hxα y hy hyα]
  simp only [zero_mul, zSign_zero, one_smul, map_neg, map_smul, LinearMap.neg_apply,
    LinearMap.smul_apply, smul_eq_mul, invForm_h_h, bilinForm_toDual_symm_left, hs]
  refine ⟨by ring, ?_⟩
  linear_combination (-(α t * invForm P p S x y)) * zSign_mul_self (K := K) (a * b)

/-- Invariance for `x = c • y` with `y` odd of weight `β` and `z` of weight `-2β`. -/
lemma invTriple_smul_left {β : Dual K H} (hβ0 : β ≠ 0) {a c' : ZMod 2} {c : K}
    {y z : P.SuperEnveloping p} (hβ : LieEqForm P p S β) (hββ : LieEqForm P p S (β + β))
    (hxa : IsHomog P p a (c • y)) (hy : y ∈ gTilde P p) (hyβ : y ∈ weightSpace P p β)
    (hyb : IsHomog P p 1 y) (hz : z ∈ gTilde P p) (hzβ : z ∈ weightSpace P p (-(β + β)))
    (hzc : IsHomog P p c' z) : InvTriple P p S a 1 (c • y) y z := by
  rcases eq_or_ne (c • y) 0 with h0 | h0
  · exact invTriple_of_left_eq_zero h0
  obtain rfl : a = 1 := eq_of_isHomog_of_isHomog P p h0 hxa (hyb.smul c)
  have e1 := hβ y hy hyβ _ (superBracket_mem_gTilde P p hy hz)
    ((show β + -(β + β) = -β by abel) ▸ superBracket_mem_weightSpace hyβ hzβ)
  have e2 := hββ _ (superBracket_mem_gTilde P p hy hy) (superBracket_mem_weightSpace hyβ hyβ) z
    hz hzβ
  have hJ := superBracket_jacobi hyb hyb hzc
  rw [e1, e2, map_add, map_add, mul_one, zSign_one] at hJ
  have hAB : invForm P p S y (superBracket P p y z) = invForm P p S (superBracket P p y y) z :=
    eq_of_smul_h_eq (P := P) (p := p) (S := S) hβ0 (by linear_combination (norm := module) hJ)
  simp only [InvTriple, superBracket_smul_left, map_smul, LinearMap.smul_apply, smul_eq_mul,
    mul_one, zSign_one]
  rw [hAB]
  exact ⟨rfl, by ring⟩

/-- Invariance for `z = c • y` with `y` odd of weight `β` and `x` of weight `-2β`. -/
lemma invTriple_smul_right {β : Dual K H} (hβ0 : β ≠ 0) {a : ZMod 2} {c : K}
    {x y : P.SuperEnveloping p} (hβ : LieEqForm P p S β) (hββ : LieEqForm P p S (β + β))
    (hx : x ∈ gTilde P p) (hxβ : x ∈ weightSpace P p (-(β + β))) (hxa : IsHomog P p a x)
    (hy : y ∈ gTilde P p) (hyβ : y ∈ weightSpace P p β) (hyb : IsHomog P p 1 y) :
    InvTriple P p S a 1 x y (c • y) := by
  have hxy := superBracket_mem_gTilde P p hx hy
  have hxyβ : superBracket P p x y ∈ weightSpace P p (-β) :=
    (show -(β + β) + β = -β by abel) ▸ superBracket_mem_weightSpace hxβ hyβ
  have e1 := hββ.neg x hx hxβ _ (superBracket_mem_gTilde P p hy hy)
    (by rw [neg_neg]; exact superBracket_mem_weightSpace hyβ hyβ)
  have e2 := hβ.neg _ hxy hxyβ y hy (by rwa [neg_neg])
  have hJ := superBracket_jacobi hxa hyb hyb
  rw [superBracket_swap (hxa.superBracket hyb) hyb, e1, e2] at hJ
  have hs := invForm_swap P p S hy hyβ hyb hxy hxyβ (hxa.superBracket hyb)
  have hAB : invForm P p S x (superBracket P p y y) = invForm P p S (superBracket P p x y) y := by
    refine eq_of_smul_h_eq (P := P) (p := p) (S := S) hβ0 ?_
    rcases zmod_two_cases a with rfl | rfl <;>
      simp only [map_neg, map_add, zero_add, mul_one, zSign_zero, zSign_one,
        show (1 : ZMod 2) + 1 = 0 from rfl] at hJ <;>
      linear_combination (norm := module) (-1 : K) • hJ
  simp only [InvTriple, superBracket_smul_right, map_smul, smul_eq_mul, mul_one]
  rw [hAB, hs]
  refine ⟨rfl, ?_⟩
  rcases zmod_two_cases a with rfl | rfl <;>
    simp only [one_mul, zero_add, zSign_zero, zSign_one, show (1 : ZMod 2) + 1 = 0 from rfl] <;>
    ring

/-- Invariance for a triple whose middle element has weight `±αₖ`, given `C_α`, `C_β` and
`C_{α+β}`. -/
lemma invTriple_of_root {α β : Dual K H} {a b c : ZMod 2} {x y z : P.SuperEnveloping p}
    (hα : LieEqForm P p S α) (hβ : LieEqForm P p S β) (hαβ : LieEqForm P p S (α + β))
    (hx : x ∈ gTilde P p) (hxα : x ∈ weightSpace P p α) (hxa : IsHomog P p a x)
    (hy : y ∈ gTilde P p) (hyβ : y ∈ weightSpace P p β) (hyb : IsHomog P p b y)
    (hz : z ∈ gTilde P p) (hzγ : z ∈ weightSpace P p (-(α + β))) (hzc : IsHomog P p c z)
    {k : ι} (hβk : β = P.root k ∨ β = -P.root k) : InvTriple P p S a b x y z := by
  by_cases hx0 : x = 0
  · exact invTriple_of_left_eq_zero hx0
  by_cases hy0 : y = 0
  · exact invTriple_of_middle_eq_zero hy0
  by_cases hz0 : z = 0
  · exact invTriple_of_right_eq_zero hz0
  by_cases hα0 : α = 0
  · subst hα0
    exact invTriple_of_weight_zero_left hβ hx hxα hxa hy hyβ hz (by simpa using hzγ)
  by_cases hγ0 : α + β = 0
  · obtain rfl : β = -α := eq_neg_of_add_eq_zero_right hγ0
    exact invTriple_of_weight_zero_right hα hx hxα hxa hy hyβ hyb hz (by simpa using hzγ)
  have hβ0 : β ≠ 0 := by
    rcases hβk with rfl | rfl <;> simp [P.linearIndependent_root.ne_zero k]
  by_cases hind : LinearIndependent K ![α, β]
  · exact invTriple_of_linearIndependent hα hβ hαβ hx hxα hxa hy hyβ hyb hz hzγ hzc hind
  have hc : ∃ c : K, α = c • P.root k := by
    rw [LinearIndependent.pair_iff] at hind
    simp only [not_forall] at hind
    obtain ⟨s, t, hst, hne⟩ := hind
    have hs : s ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hst
      exact hne ⟨rfl, (smul_eq_zero.1 hst).resolve_right hβ0⟩
    have hαβ' : α = (-(s⁻¹ * t)) • β := by
      have h1 : s • α = -(t • β) := eq_neg_of_add_eq_zero_left hst
      calc α = s⁻¹ • (s • α) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = _ := by rw [h1]; module
    rcases hβk with rfl | rfl
    · exact ⟨_, hαβ'⟩
    · exact ⟨s⁻¹ * t, by rw [hαβ', smul_neg, neg_smul, neg_neg]⟩
  obtain ⟨c₀, hc⟩ := hc
  have hdep : α = β ∨ α = β + β ∨ α = -β ∨ α = -(β + β) := by
    rcases eq_nsmul_root_or_neg P p hx hxα hx0 hα0 hc with h | h | h | h <;>
      rcases hβk with rfl | rfl <;> subst h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl (neg_neg _).symm))
    · exact Or.inr (Or.inl (two_nsmul _))
    · exact Or.inr (Or.inr (Or.inr (by rw [two_nsmul, neg_add, neg_neg])))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (by rw [two_nsmul])))
    · exact Or.inr (Or.inl (by rw [two_nsmul, neg_add]))
  have hyk : y ∈ weightSpace P p (P.root k) ∨ y ∈ weightSpace P p (-P.root k) := by
    rcases hβk with rfl | rfl
    exacts [Or.inl hyβ, Or.inr hyβ]
  have hb := parity_eq_of_mem_root P p hy hyk hy0 hyb
  rcases hdep with rfl | rfl | rfl | rfl
  · rcases zmod_two_cases (p k) with hk | hk
    · exact absurd (eq_zero_of_mem_two_of_even P p hk hβk hz (Or.inr hzγ)) hz0
    obtain ⟨c', rfl⟩ := exists_smul_eq_of_mem_root P p hβk hx hxα hy hyβ hy0
    rw [hb, hk] at hyb ⊢
    exact invTriple_smul_left hβ0 hβ hαβ hxa hy hyβ hyb hz hzγ hzc
  · exact absurd (eq_zero_of_mem_three P p hβk hz hzγ) hz0
  · exact absurd (neg_add_cancel β) hγ0
  · rcases zmod_two_cases (p k) with hk | hk
    · exact absurd (eq_zero_of_mem_two_of_even P p hk hβk hx (Or.inr hxα)) hx0
    have hzβ : z ∈ weightSpace P p β := by
      rwa [show -(-(β + β) + β) = β by abel] at hzγ
    obtain ⟨c', rfl⟩ := exists_smul_eq_of_mem_root P p hβk hz hzβ hy hyβ hy0
    rw [hb, hk] at hyb ⊢
    have hββ : LieEqForm P p S (β + β) := by simpa using hα.neg
    exact invTriple_smul_right hβ0 hβ hββ hx hxα hxa hy hyβ hyb

/-! ### Proof of `C_μ` by induction on the height -/

omit [FiniteDimensional K H] in
variable (P p) in
/-- For `μ > 0` not a simple root, `G̃_μ` is spanned by the `[eⱼ, x]` with `x ∈ G̃_{μ - αⱼ}`
homogeneous. -/
lemma gTilde_induction_e {μ : Dual K H} {q : P.SuperEnveloping p → Prop}
    (hμ : μ ∈ P.posWeights) (hμ1 : ∀ j, μ ≠ P.root j) (zero : q 0)
    (add : ∀ x y, q x → q y → q (x + y)) (smul : ∀ (c : K) x, q x → q (c • x))
    (gen : ∀ j ν (a : ZMod 2), ν ∈ P.posWeights → μ = P.root j + ν → ∀ x ∈ gTilde P p,
      x ∈ weightSpace P p ν → IsHomog P p a x → q (superBracket P p (e P p j) x)) :
    ∀ x ∈ gTilde P p, x ∈ weightSpace P p μ → q x := by
  obtain ⟨k, hk, rfl⟩ := hμ
  intro x hx hxμ
  have hx' : x ∈ nPlusRoot P p k := by
    rw [← gTilde_inf_weightSpace_rootOf P p hk]; exact ⟨hx, hxμ⟩
  clear hx hxμ
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, w, hkw, rfl⟩ := hx
    cases w with
    | nil => exact absurd (by rw [← hkw]; simp) (hμ1 i)
    | cons j w =>
      rw [eLie_cons]
      refine gen j _ _ ⟨_, wordVec_cons_mem_posCone i w, rfl⟩ ?_ _
        (nPlus_le_gTilde P p (eLie_mem_nPlus P p i w)) (eLie_mem_weightSpace_rootOf P p i w)
        (isHomog_eLie P p i w)
      rw [← hkw, ← rootOf_single P j, ← map_add]
      congr 1
      simp only [wordVec_cons]
      abel
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul c x _ hx => exact smul c x hx

omit [FiniteDimensional K H] in
variable (P p) in
/-- For `μ > 0` not a simple root, `G̃_{-μ}` is spanned by the `[fⱼ, y]` with
`y ∈ G̃_{-(μ - αⱼ)}` homogeneous. -/
lemma gTilde_induction_f {μ : Dual K H} {q : P.SuperEnveloping p → Prop}
    (hμ : μ ∈ P.posWeights) (hμ1 : ∀ j, μ ≠ P.root j) (zero : q 0)
    (add : ∀ x y, q x → q y → q (x + y)) (smul : ∀ (c : K) x, q x → q (c • x))
    (gen : ∀ j ν (a : ZMod 2), ν ∈ P.posWeights → μ = P.root j + ν → ∀ y ∈ gTilde P p,
      y ∈ weightSpace P p (-ν) → IsHomog P p a y → q (superBracket P p (f P p j) y)) :
    ∀ y ∈ gTilde P p, y ∈ weightSpace P p (-μ) → q y := by
  intro y hy hyμ
  obtain ⟨y, hy', hyμ', rfl⟩ := exists_omega_eq P p hy hyμ
  refine gTilde_induction_e P p (q := fun x ↦ q (omega P p x)) hμ hμ1 (by simpa using zero)
    (fun x y hx hy ↦ by simpa using add _ _ hx hy) (fun c x hx ↦ by simpa using smul c _ hx)
    (fun j ν a hν hμν x hx hxν hxa ↦ ?_) y hy' hyμ'
  rw [omega_superBracket, omega_e]
  exact gen j ν a hν hμν _ (omega_mem_gTilde P p hx) (omega_mem_weightSpace P p hxν) hxa.omega

omit [FiniteDimensional K H] [CharZero K] in
lemma zSign_mul_mul_zSign (a b c : ZMod 2) :
    zSign K (c * b) = zSign K (c * a) * zSign K ((a + b) * c) := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    rcases zmod_two_cases c with rfl | rfl <;> simp [show (1 : ZMod 2) + 1 = 0 from rfl]

omit [FiniteDimensional K H] [CharZero K] in
lemma zSign_mul_zSign_mul_comm (a b : ZMod 2) : zSign K (a * b) * zSign K (b * a) = 1 := by
  rw [mul_comm b a, zSign_mul_self]

/-- The inductive step of the proof of `C_μ`: for `μ = αⱼ + ν = αᵢ + κ`, homogeneous
`x ∈ G̃_ν` and `y ∈ G̃_{-κ}`, `[[eⱼ, x], [fᵢ, y]] = (eⱼ | [x, [fᵢ, y]]) ν⁻¹(μ)`. -/
lemma superBracket_e_superBracket_f {μ ν κ : Dual K H} {i j : ι} {a b : ZMod 2}
    (hν : μ = P.root j + ν) (hκ : μ = P.root i + κ) (hCi : LieEqForm P p S (P.root i))
    (hCj : LieEqForm P p S (P.root j)) (hCν : LieEqForm P p S ν) (hCκ : LieEqForm P p S κ)
    (hCνi : LieEqForm P p S (ν - P.root i)) {x y : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxν : x ∈ weightSpace P p ν) (hxa : IsHomog P p a x) (hy : y ∈ gTilde P p)
    (hyκ : y ∈ weightSpace P p (-κ)) (hyb : IsHomog P p b y) :
    superBracket P p (superBracket P p (e P p j) x) (superBracket P p (f P p i) y) =
      invForm P p S (e P p j) (superBracket P p x (superBracket P p (f P p i) y)) •
        h P p ((P.toDual S).symm μ) := by
  have hκ' : κ = P.root j + ν - P.root i := by rw [← hν, hκ]; abel
  subst hκ' hν
  have he := nPlus_le_gTilde P p (e_mem_nPlus P p j)
  have hf := nMinus_le_gTilde P p (f_mem_nMinus P p i)
  set w := superBracket P p (f P p i) y with hw
  set u := superBracket P p x (f P p i) with hu
  set z := superBracket P p (e P p j) y with hz
  have hwG : w ∈ gTilde P p := superBracket_mem_gTilde P p hf hy
  have hwμ : w ∈ weightSpace P p (-(P.root j + ν)) := by
    have := superBracket_mem_weightSpace (f_mem_weightSpace P p i) hyκ
    rwa [show -P.root i + -(P.root j + ν - P.root i) = -(P.root j + ν) by abel] at this
  have hwd : IsHomog P p (p i + b) w := (isHomog_f P p i).superBracket hyb
  have hxw : superBracket P p x w ∈ weightSpace P p (-P.root j) := by
    have := superBracket_mem_weightSpace hxν hwμ
    rwa [show ν + -(P.root j + ν) = -P.root j by abel] at this
  have hew : superBracket P p (e P p j) w ∈ weightSpace P p (-ν) := by
    have := superBracket_mem_weightSpace (e_mem_weightSpace P p j) hwμ
    rwa [show P.root j + -(P.root j + ν) = -ν by abel] at this
  have huG : u ∈ gTilde P p := superBracket_mem_gTilde P p hx hf
  have huν : u ∈ weightSpace P p (ν + -P.root i) :=
    superBracket_mem_weightSpace hxν (f_mem_weightSpace P p i)
  have hzG : z ∈ gTilde P p := superBracket_mem_gTilde P p he hy
  have hzν : z ∈ weightSpace P p (-(ν + -P.root i)) := by
    have := superBracket_mem_weightSpace (e_mem_weightSpace P p j) hyκ
    rwa [show P.root j + -(P.root j + ν - P.root i) = -(ν + -P.root i) by abel] at this
  -- `(x | [fᵢ, z]) = (u | z)`
  have h1 : invForm P p S x (superBracket P p (f P p i) z) = invForm P p S u z :=
    (invTriple_of_root hCν hCi.neg (by rwa [← sub_eq_add_neg]) hx hxν hxa hf
      (f_mem_weightSpace P p i) (isHomog_f P p i) hzG hzν ((isHomog_e P p j).superBracket hyb)
      (Or.inr rfl)).1
  -- `(u | z) = -(-1)^{(|x| + |fᵢ|)|eⱼ|} (eⱼ | [u, y])`
  have h2 : invForm P p S u z =
      -(zSign K ((a + p i) * p j) * invForm P p S (e P p j) (superBracket P p u y)) := by
    have ht := invTriple_of_root (a := a + p i) (b := p j) (c := b) (by
      rw [← sub_eq_add_neg]; exact hCνi) hCj
      (by convert hCκ using 2; abel) huG huν (hxa.superBracket (isHomog_f P p i))
      he (e_mem_weightSpace P p j) (isHomog_e P p j) hy
      (by rwa [show ν + -P.root i + P.root j = P.root j + ν - P.root i by abel]) hyb
      (Or.inl rfl)
    rw [ht.1, ht.2]
  -- the key identity `(x | [eⱼ, w]) = -(-1)^{|eⱼ||x|} (eⱼ | [x, w])`
  have key : invForm P p S x (superBracket P p (e P p j) w) =
      -(zSign K (p j * a) * invForm P p S (e P p j) (superBracket P p x w)) := by
    have hew' := superBracket_jacobi (isHomog_e P p j) (isHomog_f P p i) hyb
    have hxw' := superBracket_jacobi hxa (isHomog_f P p i) hyb
    rw [← hw] at hew' hxw'
    rw [← hu] at hxw'
    rw [← hz] at hew'
    rw [hew', hxw', map_add, map_add, map_smul, map_smul, h1, smul_eq_mul, smul_eq_mul]
    have hs := zSign_mul_mul_zSign (K := K) a (p i) (p j)
    have hsq := zSign_mul_self (K := K) ((a + p i) * p j)
    by_cases hij : i = j
    · subst hij
      have hyν : y ∈ weightSpace P p (-ν) := by
        rwa [show P.root i + ν - P.root i = ν by abel] at hyκ
      have hε : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
      have hroot : P.root i ((P.toDual S).symm ν) = (S.ε i : K)⁻¹ * ν (P.coroot i) := by
        rw [← P.bilinForm_toDual_symm_left S (P.root i) ((P.toDual S).symm ν),
          toDual_symm_root, map_smul, LinearMap.smul_apply, bilinForm_toDual_symm_right,
          smul_eq_mul]
      have hef : superBracket P p (e P p i) (f P p i) = h P p (P.coroot i) := by
        simp [superBracket_e_f]
      have e1 : invForm P p S x (superBracket P p (superBracket P p (e P p i) (f P p i)) y) =
          -(ν (P.coroot i) * invForm P p S x y) := by
        rw [hef, superBracket_h_of_mem_weightSpace P p _ hyν, map_smul, smul_eq_mul,
          LinearMap.neg_apply, neg_mul]
      have e2 : invForm P p S (e P p i) (superBracket P p (f P p i) (superBracket P p x y)) =
          ν (P.coroot i) * invForm P p S x y := by
        have hxy := hCν x hx hxν y hy hyν
        have hei : invForm P p S (e P p i) (f P p i) = S.ε i := by simp [invForm_e_f]
        rw [hxy, superBracket_smul_right, superBracket_swap (isHomog_h P p _) (isHomog_f P p i),
          superBracket_h_of_mem_weightSpace P p _ (f_mem_weightSpace P p i), zero_mul, zSign_zero,
          one_smul, map_smul, map_neg, map_smul, hei, LinearMap.neg_apply, hroot]
        simp only [smul_eq_mul]
        field_simp
      have hpa := zSign_mul_zSign_mul_comm (K := K) (p i) a
      rw [e1, e2, h2]
      linear_combination zSign K (p i * p i) * h2 * 0 -
        (zSign K ((a + p i) * p i) * invForm P p S (e P p i) (superBracket P p u y)) * hs -
        (zSign K (p i * a) * invForm P p S (e P p i) (superBracket P p u y)) * hsq +
        ν (P.coroot i) * invForm P p S x y * hpa
    · have hef : superBracket P p (e P p j) (f P p i) = 0 := by
        simp [superBracket_e_f, Ne.symm hij]
      have hxy : superBracket P p x y = 0 := by
        by_contra h0
        have hmem := superBracket_mem_weightSpace hxν hyκ
        rw [show ν + -(P.root j + ν - P.root i) = P.root i - P.root j by abel] at hmem
        exact AuxLieAlgebra.root_sub_root_notMem P hij
          (mem_allWeights P p (superBracket_mem_gTilde P p hx hy) hmem h0)
      rw [hef, hxy, superBracket_zero_left, superBracket_zero_right]
      simp only [map_zero, mul_zero, zero_add, add_zero]
      rw [h2]
      linear_combination
        -(zSign K ((a + p i) * p j) * invForm P p S (e P p j) (superBracket P p u y)) * hs -
        (zSign K (p j * a) * invForm P p S (e P p j) (superBracket P p u y)) * hsq
  have hJ := superBracket_jacobi (isHomog_e P p j) hxa hwd
  rw [hCj _ he (e_mem_weightSpace P p j) _ (superBracket_mem_gTilde P p hx hwG) hxw,
    hCν _ hx hxν _ (superBracket_mem_gTilde P p he hwG) hew, key] at hJ
  have hs := zSign_mul_self (K := K) (p j * a)
  rw [map_add, map_add]
  linear_combination (norm := module) -hJ +
    hs • (invForm P p S (e P p j) (superBracket P p x w) • h P p ((P.toDual S).symm ν))

variable (P p S) in
/-- `C_μ` for all `μ`: `[x, y] = (x | y) ν⁻¹(μ)` for `x ∈ G̃_μ` and `y ∈ G̃_{-μ}`, in the auxiliary
Lie superalgebra `G̃(A, τ)` (the super analogue of [Kac] Thm. 2.2 e); the argument is the
height induction of [Kac] §2.2 with the signs of the super Jacobi identity). -/
theorem lieEqForm (μ : Dual K H) : LieEqForm P p S μ := by
  have hpos : ∀ n : ℕ, ∀ μ ∈ P.posWeights, μ P.rhoCheck = n → LieEqForm P p S μ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
    intro μ hμ hμn
    have low : ∀ ν : Dual K H, ∀ m : ℤ, ν P.rhoCheck = m → |m| < n → LieEqForm P p S ν := by
      intro ν m hν hm
      by_cases hνw : ν ∈ AuxLieAlgebra.allWeights P
      · rcases hνw with (hν' | hν') | hν'
        · obtain ⟨m', -, hνm'⟩ := AuxLieAlgebra.exists_nat_eq_of_mem_negWeights P hν'
          have hmm : (m' : ℤ) = -m := by
            have : ((m' : ℤ) : K) = ((-m : ℤ) : K) := by
              push_cast; rw [← hν, hνm', neg_neg]
            exact_mod_cast this
          have := (IH m' (by rw [abs_lt] at hm; omega) _
            ((AuxLieAlgebra.mem_negWeights_iff P).mp hν')
            (by rw [LinearMap.neg_apply, hνm', neg_neg])).neg
          rwa [neg_neg] at this
        · rw [Set.mem_singleton_iff.mp hν']
          exact lieEqForm_zero P p S
        · obtain ⟨m', -, hνm'⟩ := AuxLieAlgebra.exists_nat_of_mem_posWeights P hν'
          have hmm : (m' : ℤ) = m := by
            have : ((m' : ℤ) : K) = ((m : ℤ) : K) := by push_cast; rw [← hν, hνm']
            exact_mod_cast this
          exact IH m' (by rw [abs_lt] at hm; omega) _ hν' hνm'
      · exact lieEqForm_of_notMem S hνw
    by_cases hμ1 : ∃ j, μ = P.root j
    · obtain ⟨j, rfl⟩ := hμ1
      exact lieEqForm_root P p S j
    simp only [not_exists] at hμ1
    refine lieEqForm_of_exists (fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ hμ)) ?_
    refine gTilde_induction_e P p (q := fun x ↦ ∀ y ∈ gTilde P p, y ∈ weightSpace P p (-μ) →
      ∃ c : K, superBracket P p x y = c • h P p ((P.toDual S).symm μ)) hμ hμ1 ?_ ?_ ?_ ?_
    · exact fun y _ _ ↦ ⟨0, by simp [superBracket_zero_left]⟩
    · intro x₁ x₂ h₁ h₂ y hy hyμ
      obtain ⟨c₁, hc₁⟩ := h₁ y hy hyμ
      obtain ⟨c₂, hc₂⟩ := h₂ y hy hyμ
      exact ⟨c₁ + c₂, by rw [superBracket_add_left, hc₁, hc₂, add_smul]⟩
    · intro c x hx y hy hyμ
      obtain ⟨c', hc'⟩ := hx y hy hyμ
      exact ⟨c * c', by rw [superBracket_smul_left, hc', smul_smul]⟩
    intro j ν a hν hμν x hx hxν hxa
    refine gTilde_induction_f P p (q := fun y ↦ ∃ c : K,
      superBracket P p (superBracket P p (e P p j) x) y = c • h P p ((P.toDual S).symm μ))
      hμ hμ1 ?_ ?_ ?_ ?_
    · exact ⟨0, by simp⟩
    · rintro y₁ y₂ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
      exact ⟨c₁ + c₂, by rw [superBracket_add_right, hc₁, hc₂, add_smul]⟩
    · rintro c y ⟨c', hc'⟩
      exact ⟨c * c', by rw [superBracket_smul_right, hc', smul_smul]⟩
    intro i κ b hκ hμκ y hy hyκ hyb
    obtain ⟨mν, hmν, hνm⟩ := AuxLieAlgebra.exists_nat_of_mem_posWeights P hν
    have hνρ : ν P.rhoCheck = ((n : ℤ) - 1 : ℤ) := by
      rw [show ν = μ - P.root j by rw [hμν]; abel, LinearMap.sub_apply, hμn, root_rhoCheck]
      push_cast; ring
    have hn2 : 2 ≤ n := by
      have : ((mν : ℤ) : K) = ((n : ℤ) - 1 : ℤ) := by rw [← hνρ, hνm, Int.cast_natCast]
      have := (Int.cast_injective (α := K)) this
      omega
    have hκρ : κ P.rhoCheck = ((n : ℤ) - 1 : ℤ) := by
      rw [show κ = μ - P.root i by rw [hμκ]; abel, LinearMap.sub_apply, hμn, root_rhoCheck]
      push_cast; ring
    have hνiρ : (ν - P.root i) P.rhoCheck = ((n : ℤ) - 2 : ℤ) := by
      rw [LinearMap.sub_apply, hνρ, root_rhoCheck]
      push_cast; ring
    have hrρ : ∀ k, P.root k P.rhoCheck = ((1 : ℤ) : K) := fun k ↦ by simp
    have hlt : ∀ m : ℤ, (m = 1 ∨ m = n - 1 ∨ m = n - 2) → |m| < n := by
      intro m hm
      rw [abs_lt]
      omega
    exact ⟨_, superBracket_e_superBracket_f hμν hμκ (low _ _ (hrρ i) (hlt _ (Or.inl rfl)))
      (low _ _ (hrρ j) (hlt _ (Or.inl rfl))) (low _ _ hνρ (hlt _ (Or.inr (Or.inl rfl))))
      (low _ _ hκρ (hlt _ (Or.inr (Or.inl rfl))))
      (low _ _ hνiρ (hlt _ (Or.inr (Or.inr rfl)))) hx hxν hxa hy hyκ hyb⟩
  by_cases hμw : μ ∈ AuxLieAlgebra.allWeights P
  · rcases hμw with (hμ | hμ) | hμ
    · obtain ⟨n, -, hμn⟩ := AuxLieAlgebra.exists_nat_of_mem_posWeights P
        ((AuxLieAlgebra.mem_negWeights_iff P).mp hμ)
      simpa using (hpos n _ ((AuxLieAlgebra.mem_negWeights_iff P).mp hμ) hμn).neg
    · rw [Set.mem_singleton_iff.mp hμ]
      exact lieEqForm_zero P p S
    · obtain ⟨n, -, hμn⟩ := AuxLieAlgebra.exists_nat_of_mem_posWeights P hμ
      exact hpos n μ hμ hμn
  · exact lieEqForm_of_notMem S hμw

/-! ### Invariance -/

variable (P p S) in
/-- `y` satisfies invariance in the middle: `([x, y] | z) = (x | [y, z])` for `x, z ∈ G̃`. -/
def MidInv (y : P.SuperEnveloping p) : Prop :=
  ∀ x ∈ gTilde P p, ∀ z ∈ gTilde P p,
    invForm P p S (superBracket P p x y) z = invForm P p S x (superBracket P p y z)

omit [FiniteDimensional K H] in
variable (P p) in
/-- A property of pairs of elements of `G̃`, additive in each variable, holds as soon as it holds
for homogeneous weight vectors. -/
lemma forall_gTilde_of_homog {q : P.SuperEnveloping p → P.SuperEnveloping p → Prop}
    (add_left : ∀ x₁ x₂ z, q x₁ z → q x₂ z → q (x₁ + x₂) z)
    (add_right : ∀ x z₁ z₂, q x z₁ → q x z₂ → q x (z₁ + z₂))
    (hom : ∀ (α γ : Dual K H) (a c : ZMod 2), ∀ x ∈ gTilde P p, x ∈ weightSpace P p α →
      IsHomog P p a x → ∀ z ∈ gTilde P p, z ∈ weightSpace P p γ → IsHomog P p c z → q x z)
    {x z : P.SuperEnveloping p} (hx : x ∈ gTilde P p) (hz : z ∈ gTilde P p) : q x z := by
  refine induction_on_gTilde P p (q := fun x ↦ q x z) hx (fun α x hx hxα ↦ ?_)
    (fun x₁ x₂ h₁ h₂ ↦ add_left _ _ _ h₁ h₂)
  refine induction_homog P p (q := fun x ↦ q x z) hx hxα (fun a x hx hxα hxa ↦ ?_)
    (fun x₁ x₂ h₁ h₂ ↦ add_left _ _ _ h₁ h₂)
  refine induction_on_gTilde P p (q := fun z ↦ q x z) hz (fun γ z hz hzγ ↦ ?_)
    (fun z₁ z₂ h₁ h₂ ↦ add_right _ _ _ h₁ h₂)
  exact induction_homog P p (q := fun z ↦ q x z) hz hzγ
    (fun c z hz hzγ hzc ↦ hom α γ a c x hx hxα hxa z hz hzγ hzc)
    (fun z₁ z₂ h₁ h₂ ↦ add_right _ _ _ h₁ h₂)

/-- Invariance in the middle may be checked on homogeneous weight vectors of opposite weights. -/
lemma midInv_of_weight {β : Dual K H} {y : P.SuperEnveloping p} (hyβ : y ∈ weightSpace P p β)
    (hinv : ∀ (α : Dual K H) (a c : ZMod 2), ∀ x ∈ gTilde P p, x ∈ weightSpace P p α →
      IsHomog P p a x → ∀ z ∈ gTilde P p, z ∈ weightSpace P p (-(α + β)) → IsHomog P p c z →
      invForm P p S (superBracket P p x y) z = invForm P p S x (superBracket P p y z)) :
    MidInv P p S y := by
  intro x hx z hz
  refine forall_gTilde_of_homog P p (q := fun x z ↦ invForm P p S (superBracket P p x y) z =
    invForm P p S x (superBracket P p y z)) ?_ ?_ ?_ hx hz
  · intro x₁ x₂ z h₁ h₂
    simp only [superBracket_add_left, map_add, LinearMap.add_apply, h₁, h₂]
  · intro x z₁ z₂ h₁ h₂
    simp only [superBracket_add_right, map_add, h₁, h₂]
  intro α γ a c x hx hxα hxa z hz hzγ hzc
  by_cases hs : α + β + γ = 0
  · obtain rfl : γ = -(α + β) := eq_neg_of_add_eq_zero_right hs
    exact hinv α a c x hx hxα hxa z hz hzγ hzc
  · rw [invForm_eq_zero P p S (superBracket_mem_weightSpace hxα hyβ) hzγ hs,
      invForm_eq_zero P p S hxα (superBracket_mem_weightSpace hyβ hzγ) (by rwa [← add_assoc])]

lemma midInv_e (k : ι) : MidInv P p S (e P p k) :=
  midInv_of_weight (e_mem_weightSpace P p k) fun α _ _ _ hx hxα hxa _ hz hzγ hzc ↦
    ((invTriple_of_root (lieEqForm P p S α) (lieEqForm P p S _) (lieEqForm P p S _) hx hxα hxa
      (nPlus_le_gTilde P p (e_mem_nPlus P p k)) (e_mem_weightSpace P p k) (isHomog_e P p k)
      hz hzγ hzc (Or.inl rfl)).1).symm

lemma midInv_f (k : ι) : MidInv P p S (f P p k) :=
  midInv_of_weight (f_mem_weightSpace P p k) fun α _ _ _ hx hxα hxa _ hz hzγ hzc ↦
    ((invTriple_of_root (lieEqForm P p S α) (lieEqForm P p S _) (lieEqForm P p S _) hx hxα hxa
      (nMinus_le_gTilde P p (f_mem_nMinus P p k)) (f_mem_weightSpace P p k) (isHomog_f P p k)
      hz hzγ hzc (Or.inr rfl)).1).symm

lemma midInv_h (t : H) : MidInv P p S (h P p t) := by
  refine midInv_of_weight (h_mem_weightSpace P p t) fun α a _ x _ hxα hxa z _ hzγ _ ↦ ?_
  rw [add_zero] at hzγ
  rw [superBracket_swap (isHomog_h P p t) hxa, superBracket_h_of_mem_weightSpace P p t hxα,
    superBracket_h_of_mem_weightSpace P p t hzγ, zero_mul, zSign_zero, one_smul]
  simp

/-- The super Leibniz rule for invariance in the middle. -/
lemma MidInv.bracket {a b : ZMod 2} {y₁ y₂ : P.SuperEnveloping p} (hy₁ : y₁ ∈ gTilde P p)
    (hy₂ : y₂ ∈ gTilde P p) (ha : IsHomog P p a y₁) (hb : IsHomog P p b y₂)
    (h₁ : MidInv P p S y₁) (h₂ : MidInv P p S y₂) : MidInv P p S (superBracket P p y₁ y₂) := by
  intro x hx z hz
  refine forall_gTilde_of_homog P p (q := fun x z ↦
    invForm P p S (superBracket P p x (superBracket P p y₁ y₂)) z =
      invForm P p S x (superBracket P p (superBracket P p y₁ y₂) z)) ?_ ?_ ?_ hx hz
  · intro x₁ x₂ z e₁ e₂
    simp only [superBracket_add_left, map_add, LinearMap.add_apply, e₁, e₂]
  · intro x z₁ z₂ e₁ e₂
    simp only [superBracket_add_right, map_add, e₁, e₂]
  intro α γ c d x hx _ hxc z hz _ hzd
  have J₁ := superBracket_jacobi hxc ha hb
  have J₂ := superBracket_jacobi ha hb hzd
  have hsw := superBracket_swap (hxc.superBracket hb) ha
  rw [J₁, eq_sub_of_add_eq J₂.symm, hsw]
  simp only [map_add, map_sub, map_neg, map_smul, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [h₂ _ (superBracket_mem_gTilde P p hx hy₁) _ hz,
    h₁ x hx _ (superBracket_mem_gTilde P p hy₂ hz),
    h₁ _ (superBracket_mem_gTilde P p hx hy₂) _ hz,
    h₂ x hx _ (superBracket_mem_gTilde P p hy₁ hz)]
  have hs : zSign K (c * a) * zSign K ((c + b) * a) = zSign K (a * b) := by
    rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
      rcases zmod_two_cases c with rfl | rfl <;> simp [show (1 : ZMod 2) + 1 = 0 from rfl]
  linear_combination (-(invForm P p S x (superBracket P p y₂ (superBracket P p y₁ z)))) * hs

variable (P p S) in
/-- The elements satisfying invariance in the middle, as a subspace. -/
def midInvSubmodule : Submodule K (P.SuperEnveloping p) where
  carrier := {y | MidInv P p S y}
  add_mem' {y₁ y₂} h₁ h₂ x hx z hz := by
    rw [superBracket_add_right, superBracket_add_left, map_add, LinearMap.add_apply, map_add,
      h₁ x hx z hz, h₂ x hx z hz]
  zero_mem' x _ z _ := by simp [superBracket_zero_left]
  smul_mem' c y hy x hx z hz := by
    rw [superBracket_smul_right, superBracket_smul_left, map_smul, LinearMap.smul_apply, map_smul,
      hy x hx z hz]

variable (P p S) in
/-- The form on `G̃(A, τ)` is invariant: `([x, y] | z) = (x | [y, z])` ([Kac78] Prop. 1.5). -/
theorem invForm_superBracket {x y z : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hy : y ∈ gTilde P p) (hz : z ∈ gTilde P p) :
    invForm P p S (superBracket P p x y) z = invForm P p S x (superBracket P p y z) := by
  suffices gTilde P p ≤ midInvSubmodule P p S from this hy x hx z hz
  have hplus : ∀ i w, MidInv P p S (eLie P p i w) := by
    intro i w
    induction w with
    | nil => exact midInv_e i
    | cons j w ih =>
      exact MidInv.bracket (nPlus_le_gTilde P p (e_mem_nPlus P p j))
        (nPlus_le_gTilde P p (eLie_mem_nPlus P p i w)) (isHomog_e P p j) (isHomog_eLie P p i w)
        (midInv_e j) ih
  have hminus : ∀ i w, MidInv P p S (omega P p (eLie P p i w)) := by
    intro i w
    induction w with
    | nil => rw [eLie_nil, omega_e]; exact midInv_f i
    | cons j w ih =>
      rw [omega_eLie_cons]
      exact MidInv.bracket (nMinus_le_gTilde P p (f_mem_nMinus P p j))
        (nMinus_le_gTilde P p (omega_mem_nMinus P p (eLie_mem_nPlus P p i w))) (isHomog_f P p j)
        (isHomog_eLie P p i w).omega (midInv_f j) ih
  refine sup_le (sup_le ?_ ?_) ?_
  · exact Submodule.map_le_iff_le_comap.2 ((nPlus_le_iff P p).2 fun i w ↦ hminus i w)
  · rintro _ ⟨t, rfl⟩
    exact midInv_h t
  · exact (nPlus_le_iff P p).2 hplus

/-! ### The radical of the form -/

omit [FiniteDimensional K H] in
variable (P p) in
/-- Induction over the homogeneous elements of a subspace stable under the parity involution. -/
lemma induction_parity {N : Submodule K (P.SuperEnveloping p)}
    (hN : ∀ x ∈ N, parity P p x ∈ N) {q : P.SuperEnveloping p → Prop}
    (hom : ∀ a, ∀ x ∈ N, IsHomog P p a x → q x) (add : ∀ x y, q x → q y → q (x + y))
    {x : P.SuperEnveloping p} (hx : x ∈ N) : q x := by
  have hdec : x = (2 : K)⁻¹ • (x + parity P p x) + (2 : K)⁻¹ • (x - parity P p x) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul K x, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]
  rw [hdec]
  have hσ := hN x hx
  refine add _ _ (hom 0 _ ?_ ?_) (hom 1 _ ?_ ?_)
  · exact Submodule.smul_mem _ _ (add_mem hx hσ)
  · rw [IsHomog, map_smul, map_add, parity_parity, zSign_zero, one_smul, add_comm]
  · exact Submodule.smul_mem _ _ (sub_mem hx hσ)
  · rw [IsHomog, map_smul, map_sub, parity_parity, zSign_one, neg_one_smul, ← smul_neg, neg_sub]

omit [FiniteDimensional K H] in
variable (P p) in
/-- `[R, G̃] ⊆ R`. -/
lemma superBracket_mem_maxIdeal_left {r y : P.SuperEnveloping p} (hr : r ∈ maxIdeal P p)
    (hy : y ∈ gTilde P p) : superBracket P p r y ∈ maxIdeal P p := by
  refine induction_parity P p (N := maxIdeal P p) (fun _ ↦ parity_mem_maxIdeal P p)
    (q := fun r ↦ superBracket P p r y ∈ maxIdeal P p) (fun a r hr hra ↦ ?_)
    (fun r₁ r₂ h₁ h₂ ↦ by rw [superBracket_add_left]; exact add_mem h₁ h₂) hr
  refine induction_parity P p (N := gTilde P p) (fun _ ↦ parity_mem_gTilde P p)
    (q := fun y ↦ superBracket P p r y ∈ maxIdeal P p) (fun b y hy hyb ↦ ?_)
    (fun y₁ y₂ h₁ h₂ ↦ by rw [superBracket_add_right]; exact add_mem h₁ h₂) hy
  rw [superBracket_swap hyb hra]
  exact neg_mem (Submodule.smul_mem _ _
    ((isIdeal_maxIdeal P p).superBracket_mem y hy r hr))

lemma h_toDual_symm_ne_zero {μ : Dual K H} (hμ : μ ≠ 0) : h P p ((P.toDual S).symm μ) ≠ 0 :=
  fun h0 ↦ hμ ((P.toDual S).symm.map_eq_zero_iff.1
    ((injective_iff_map_eq_zero _).1 (h_injective P p) _ h0))

variable (P p S) in
/-- The maximal ideal `R` lies in the radical of the form: `(R | G̃) = 0` and `(G̃ | R) = 0`. -/
theorem invForm_eq_zero_of_mem_maxIdeal {r y : P.SuperEnveloping p} (hr : r ∈ maxIdeal P p)
    (hy : y ∈ gTilde P p) : invForm P p S r y = 0 ∧ invForm P p S y r = 0 := by
  have hR := isIdeal_maxIdeal P p
  have hle := le_iSup_inf_weightSpace P p (maxIdeal P p) fun a x hx ↦
    hR.superBracket_mem _ (h_mem_gTilde P p a) x hx
  refine Submodule.iSup_induction _
    (motive := fun r ↦ invForm P p S r y = 0 ∧ invForm P p S y r = 0) (hle hr) ?_ (by simp)
    fun r₁ r₂ h₁ h₂ ↦ ⟨by rw [map_add, LinearMap.add_apply, h₁.1, h₂.1, add_zero],
      by rw [map_add, h₁.2, h₂.2, add_zero]⟩
  rintro μ r ⟨hrR, hrμ⟩
  have hrG := hR.le_gTilde hrR
  by_cases hμ : μ = 0
  · subst hμ
    have : r ∈ maxIdeal P p ⊓ LinearMap.range (h P p) := ⟨hrR, by
      rw [← gTilde_inf_weightSpace_zero P p]; exact ⟨hrG, hrμ⟩⟩
    rw [maxIdeal_inf_range_h, Submodule.mem_bot] at this
    simp [this]
  refine induction_on_gTilde P p
    (q := fun y ↦ invForm P p S r y = 0 ∧ invForm P p S y r = 0) hy (fun ν y hy hyν ↦ ?_)
    fun y₁ y₂ h₁ h₂ ↦ ⟨by rw [map_add, h₁.1, h₂.1, add_zero],
      by rw [map_add, LinearMap.add_apply, h₁.2, h₂.2, add_zero]⟩
  by_cases hμν : μ + ν = 0
  · obtain rfl : ν = -μ := eq_neg_of_add_eq_zero_right hμν
    have hC := lieEqForm P p S μ r hrG hrμ y hy hyν
    have hC' := lieEqForm P p S (-μ) y hy hyν r hrG (by rwa [neg_neg])
    have hm : superBracket P p r y ∈ maxIdeal P p ⊓ LinearMap.range (h P p) :=
      ⟨superBracket_mem_maxIdeal_left P p hrR hy, by
        rw [hC, ← map_smul]; exact LinearMap.mem_range_self _ _⟩
    have hm' : superBracket P p y r ∈ maxIdeal P p ⊓ LinearMap.range (h P p) :=
      ⟨hR.superBracket_mem y hy r hrR, by
        rw [hC', ← map_smul]; exact LinearMap.mem_range_self _ _⟩
    rw [maxIdeal_inf_range_h, Submodule.mem_bot, hC, smul_eq_zero] at hm
    rw [maxIdeal_inf_range_h, Submodule.mem_bot, hC', smul_eq_zero] at hm'
    exact ⟨hm.resolve_right (h_toDual_symm_ne_zero hμ),
      hm'.resolve_right (h_toDual_symm_ne_zero (neg_ne_zero.2 hμ))⟩
  · exact ⟨invForm_eq_zero P p S hrμ hyν hμν,
      invForm_eq_zero P p S hyν hrμ (by rwa [add_comm])⟩

variable (P p S) in
/-- The radical of the form on `G̃(A, τ)` is the maximal ideal `R` ([Kac78] Prop. 1.5;
cf. [Kac] Thm. 2.2 for `𝔤̃(A)`). -/
theorem mem_maxIdeal_iff {r : P.SuperEnveloping p} (hr : r ∈ gTilde P p) :
    r ∈ maxIdeal P p ↔ ∀ y ∈ gTilde P p, invForm P p S y r = 0 := by
  refine ⟨fun hr y hy ↦ (invForm_eq_zero_of_mem_maxIdeal P p S hr hy).2, fun h0 ↦ ?_⟩
  let I : Submodule K (P.SuperEnveloping p) :=
    { carrier := {r | r ∈ gTilde P p ∧ ∀ y ∈ gTilde P p, invForm P p S y r = 0}
      add_mem' := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ ↦ ⟨add_mem h₁ h₂, fun y hy ↦ by
        rw [map_add, h₁' y hy, h₂' y hy, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun y _ ↦ map_zero _⟩
      smul_mem' := fun c r ⟨h, h'⟩ ↦ ⟨Submodule.smul_mem _ c h, fun y hy ↦ by
        rw [map_smul, h' y hy, smul_zero]⟩ }
  have hI : IsIdeal P p I :=
    ⟨fun _ hr ↦ hr.1, fun x hx r ⟨hrG, hr0⟩ ↦ ⟨superBracket_mem_gTilde P p hx hrG, fun y hy ↦ by
      rw [← invForm_superBracket P p S hy hx hrG]
      exact hr0 _ (superBracket_mem_gTilde P p hy hx)⟩⟩
  have hI0 : I ⊓ LinearMap.range (h P p) = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨⟨-, hx⟩, ⟨t, rfl⟩⟩
    rw [Submodule.mem_bot, ← map_zero (h P p)]
    congr 1
    refine (P.nondegenerate_bilinForm S).2 t fun b ↦ ?_
    have := hx (h P p b) (h_mem_gTilde P p b)
    rwa [invForm_h_h] at this
  exact le_maxIdeal P p hI hI0 ⟨hr, h0⟩

end Invariance

end SuperEnveloping

end Matrix.Realization
