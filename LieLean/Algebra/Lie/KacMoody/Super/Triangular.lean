/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.Grading
import LieLean.Algebra.Lie.KacMoody.Super.Verma

/-!
# The triangular decomposition of `G̃(A, τ)`

Let `U = U(G̃(A, τ))` be the enveloping algebra of the auxiliary contragredient Lie superalgebra
([Kac78] §1.1). We realize the positive and negative parts of `G̃(A, τ)` inside `U`:
`ñ₊ ⊆ U` is the span of the iterated super commutators `[e_{j₁}, [e_{j₂}, ⋯ [e_{jₖ}, eᵢ] ⋯ ]]`
(`SuperEnveloping.nPlus`), and `ñ₋` is its image under the Chevalley involution `ω`
(`SuperEnveloping.omega`: `eᵢ ↦ fᵢ`, `fᵢ ↦ (-1)^{p i} eᵢ`, `h ↦ -h`; `ω² = σ`).

We prove the super Jacobi identity for homogeneous elements of `U`, that `ñ₊` is stable under
`[eⱼ, -]` and `[h, -]`, that `[fₖ, ñ₊] ⊆ ñ₊ + 𝔥` (and the images of these statements under `ω`),
and that the sum `ñ₋ + 𝔥 + ñ₊` is direct ([Kac78] §1.1, cf. [Kac] Thm. 1.2 (a), (b)): the
elements of `ñ₋` are `fAlg x` with `x` in the augmentation ideal of `T(V)`, and acting on `1` in
the tensor-algebra representation separates the three summands.

## Main definitions

* `Matrix.Realization.zSign`: the sign `(-1)^a` of `a ∈ ℤ/2`.
* `Matrix.Realization.SuperEnveloping.IsHomog`: homogeneous elements of a given parity.
* `Matrix.Realization.SuperEnveloping.eLie`: the iterated super commutators of the `eⱼ`.
* `Matrix.Realization.SuperEnveloping.nPlus`, `.nMinus`: `ñ₊` and `ñ₋`.
* `Matrix.Realization.SuperEnveloping.omega`: the Chevalley involution.

## Main results

* `Matrix.Realization.SuperEnveloping.superBracket_of_isHomog`:
  `[x, y] = x y - (-1)^{|x||y|} y x`.
* `Matrix.Realization.SuperEnveloping.superBracket_jacobi`: the super Jacobi identity.
* `Matrix.Realization.SuperEnveloping.superBracket_f_mem_nPlus_sup`: `[fₖ, ñ₊] ⊆ ñ₊ + 𝔥`.
* `Matrix.Realization.SuperEnveloping.eq_zero_of_add_add_eq_zero`: `ñ₋ + 𝔥 + ñ₊` is direct.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.1.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.2.
-/

open Module

noncomputable section

namespace Matrix.Realization

section zSign

variable (K : Type*) [Field K]

/-- The sign `(-1)^a` of `a ∈ ℤ/2`. -/
def zSign (a : ZMod 2) : K := if a = 1 then -1 else 1

@[simp] lemma zSign_zero : zSign K 0 = 1 := by simp [zSign]

@[simp] lemma zSign_one : zSign K 1 = -1 := by simp [zSign]

lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  exacts [Or.inl rfl, Or.inr rfl]

lemma zSign_add (a b : ZMod 2) : zSign K (a + b) = zSign K a * zSign K b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 from rfl]

lemma zSign_mul_self (a : ZMod 2) : zSign K a * zSign K a = 1 := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

lemma superSign_eq_zSign {ι : Type*} (p : ι → ZMod 2) (i j : ι) :
    superSign K p i j = zSign K (p i * p j) := by
  rcases zmod_two_cases (p i) with hi | hi <;> rcases zmod_two_cases (p j) with hj | hj <;>
    simp [superSign, hi, hj]

lemma paritySign_eq_zSign {ι : Type*} (p : ι → ZMod 2) (i : ι) :
    paritySign K p i = zSign K (p i) := rfl

end zSign

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

namespace SuperEnveloping

/-! ### Homogeneous elements and the super Jacobi identity -/

/-- `u` is homogeneous of parity `a`: `σ u = (-1)^a u`. -/
def IsHomog (a : ZMod 2) (u : P.SuperEnveloping p) : Prop := parity P p u = zSign K a • u

variable {P p}

lemma IsHomog.mul {a b : ZMod 2} {x y : P.SuperEnveloping p} (hx : IsHomog P p a x)
    (hy : IsHomog P p b y) : IsHomog P p (a + b) (x * y) := by
  rw [IsHomog, map_mul, hx, hy, smul_mul_smul_comm, zSign_add]

lemma IsHomog.smul {a : ZMod 2} {x : P.SuperEnveloping p} (hx : IsHomog P p a x) (c : K) :
    IsHomog P p a (c • x) := by
  rw [IsHomog, map_smul, hx, smul_comm]

lemma IsHomog.neg {a : ZMod 2} {x : P.SuperEnveloping p} (hx : IsHomog P p a x) :
    IsHomog P p a (-x) := by
  rw [IsHomog, map_neg, hx, smul_neg]

lemma IsHomog.add {a : ZMod 2} {x y : P.SuperEnveloping p} (hx : IsHomog P p a x)
    (hy : IsHomog P p a y) : IsHomog P p a (x + y) := by
  rw [IsHomog, map_add, hx, hy, smul_add]

lemma isHomog_zero (a : ZMod 2) : IsHomog P p a 0 := by simp [IsHomog]

variable (P p)

lemma isHomog_e (i : ι) : IsHomog P p (p i) (e P p i) := parity_e P p i

lemma isHomog_f (i : ι) : IsHomog P p (p i) (f P p i) := parity_f P p i

lemma isHomog_h (a : H) : IsHomog P p 0 (h P p a) := by simp [IsHomog]

variable {P p} [CharZero K]

/-- On homogeneous elements, `[x, y] = x y - (-1)^{|x||y|} y x`. -/
lemma superBracket_of_isHomog {a b : ZMod 2} {x y : P.SuperEnveloping p}
    (hx : IsHomog P p a x) (hy : IsHomog P p b y) :
    superBracket P p x y = x * y - zSign K (a * b) • (y * x) := by
  rcases zmod_two_cases b with rfl | rfl
  · rw [superBracket_of_even_right P p x (by rw [IsEven, hy, zSign_zero, one_smul]), mul_zero,
      zSign_zero, one_smul]
  · have hy' : parity P p y = -y := by rw [hy, zSign_one, neg_one_smul]
    rw [superBracket, hx, hy', add_neg_cancel, zero_mul, zero_add, sub_neg_eq_add,
      ← two_smul K y, smul_mul_assoc, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul,
      mul_smul_comm, mul_one]

lemma IsHomog.superBracket {a b : ZMod 2} {x y : P.SuperEnveloping p} (hx : IsHomog P p a x)
    (hy : IsHomog P p b y) : IsHomog P p (a + b) (superBracket P p x y) := by
  rw [superBracket_of_isHomog hx hy, IsHomog, map_sub, map_smul, map_mul, map_mul, hx, hy,
    smul_mul_smul_comm, smul_mul_smul_comm, zSign_add, smul_sub, smul_smul, smul_smul,
    mul_comm (zSign K b) (zSign K a), mul_comm (zSign K (a * b))]

/-- The super Jacobi identity
`[x, [y, z]] = [[x, y], z] + (-1)^{|x||y|} [y, [x, z]]` for homogeneous `x, y, z`. -/
theorem superBracket_jacobi {a b c : ZMod 2} {x y z : P.SuperEnveloping p}
    (hx : IsHomog P p a x) (hy : IsHomog P p b y) (hz : IsHomog P p c z) :
    superBracket P p x (superBracket P p y z) =
      superBracket P p (superBracket P p x y) z +
        zSign K (a * b) • superBracket P p y (superBracket P p x z) := by
  rw [superBracket_of_isHomog hx (hy.superBracket hz),
    superBracket_of_isHomog (hx.superBracket hy) hz,
    superBracket_of_isHomog hy (hx.superBracket hz), superBracket_of_isHomog hy hz,
    superBracket_of_isHomog hx hy, superBracket_of_isHomog hx hz]
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    rcases zmod_two_cases c with rfl | rfl <;>
    simp only [mul_zero, mul_one, zero_add, add_zero, zSign_zero, zSign_one,
      one_smul, neg_smul, show (1 : ZMod 2) + 1 = 0 from rfl] <;> noncomm_ring

omit [CharZero K] in
lemma superBracket_mem_weightSpace {μ ν : Dual K H} {x y : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) (hy : y ∈ weightSpace P p ν) :
    superBracket P p x y ∈ weightSpace P p (μ + ν) := by
  have hyx : ∀ {y'} {x'}, y' ∈ weightSpace P p ν → x' ∈ weightSpace P p μ →
      y' * x' ∈ weightSpace P p (μ + ν) := fun hy' hx' ↦ by
    rw [add_comm]; exact mul_mem_weightSpace P p hy' hx'
  refine sub_mem (mul_mem_weightSpace P p hx hy) (Submodule.smul_mem _ _ (add_mem ?_ ?_))
  · exact hyx (add_mem hy (parity_mem_weightSpace P p hy)) hx
  · exact hyx (sub_mem hy (parity_mem_weightSpace P p hy)) (parity_mem_weightSpace P p hx)

omit [CharZero K] in
variable (P p) in
/-- The super commutator `[x, -]` as a linear map. -/
def superBracketRight (x : P.SuperEnveloping p) : P.SuperEnveloping p →ₗ[K] P.SuperEnveloping p :=
  LinearMap.mulLeft K x - (2 : K)⁻¹ •
    ((LinearMap.mulRight K x) ∘ₗ (LinearMap.id + (parity P p).toLinearMap) +
      (LinearMap.mulRight K (parity P p x)) ∘ₗ (LinearMap.id - (parity P p).toLinearMap))

omit [CharZero K] in
@[simp] lemma superBracketRight_apply (x y : P.SuperEnveloping p) :
    superBracketRight P p x y = superBracket P p x y := rfl

omit [CharZero K] in
lemma superBracket_smul_left (c : K) (x y : P.SuperEnveloping p) :
    superBracket P p (c • x) y = c • superBracket P p x y := by
  simp only [superBracket, map_smul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add,
    smul_comm c]

omit [CharZero K] in
lemma superBracket_zero_left (y : P.SuperEnveloping p) : superBracket P p 0 y = 0 := by
  simpa using superBracket_smul_left (P := P) (p := p) 0 0 y

omit [CharZero K] in
lemma superBracket_neg_left (x y : P.SuperEnveloping p) :
    superBracket P p (-x) y = -superBracket P p x y := by
  simpa using superBracket_smul_left (P := P) (p := p) (-1) x y

/-! ### The positive part `ñ₊` -/

variable (P p)

/-- The iterated super commutator `[e_{j₁}, [e_{j₂}, ⋯ [e_{jₖ}, eᵢ] ⋯ ]]` for `w = [j₁, …, jₖ]`. -/
def eLie (i : ι) : List ι → P.SuperEnveloping p
  | [] => e P p i
  | j :: w => superBracket P p (e P p j) (eLie i w)

omit [CharZero K] in
@[simp] lemma eLie_nil (i : ι) : eLie P p i [] = e P p i := rfl

omit [CharZero K] in
@[simp] lemma eLie_cons (i j : ι) (w : List ι) :
    eLie P p i (j :: w) = superBracket P p (e P p j) (eLie P p i w) := rfl

lemma isHomog_eLie (i : ι) (w : List ι) :
    IsHomog P p ((w.map p).sum + p i) (eLie P p i w) := by
  induction w with
  | nil => simpa using isHomog_e P p i
  | cons j w ih =>
    rw [List.map_cons, List.sum_cons, add_assoc]
    exact (isHomog_e P p j).superBracket ih

omit [CharZero K] in
lemma eLie_mem_weightSpace (i : ι) (w : List ι) :
    eLie P p i w ∈ weightSpace P p ((w.map P.root).sum + P.root i) := by
  induction w with
  | nil => simpa using e_mem_weightSpace P p i
  | cons j w ih =>
    rw [List.map_cons, List.sum_cons, add_assoc]
    exact superBracket_mem_weightSpace (e_mem_weightSpace P p j) ih

/-- The positive part `ñ₊` of `G̃(A, τ)`, spanned by the iterated super commutators of the `eⱼ`. -/
def nPlus : Submodule K (P.SuperEnveloping p) :=
  Submodule.span K (Set.range fun x : ι × List ι ↦ eLie P p x.1 x.2)

omit [CharZero K] in
lemma eLie_mem_nPlus (i : ι) (w : List ι) : eLie P p i w ∈ nPlus P p :=
  Submodule.subset_span ⟨(i, w), rfl⟩

omit [CharZero K] in
lemma e_mem_nPlus (i : ι) : e P p i ∈ nPlus P p := eLie_mem_nPlus P p i []

omit [CharZero K] in
/-- An inclusion `ñ₊ ≤ N` may be checked on the iterated super commutators. -/
lemma nPlus_le_iff {N : Submodule K (P.SuperEnveloping p)} :
    nPlus P p ≤ N ↔ ∀ i w, eLie P p i w ∈ N := by
  rw [nPlus, Submodule.span_le, Set.range_subset_iff]
  exact Prod.forall

omit [CharZero K] in
/-- `[eⱼ, ñ₊] ⊆ ñ₊`. -/
lemma superBracket_e_mem_nPlus (j : ι) {x : P.SuperEnveloping p} (hx : x ∈ nPlus P p) :
    superBracket P p (e P p j) x ∈ nPlus P p := by
  have : nPlus P p ≤ (nPlus P p).comap (superBracketRight P p (e P p j)) :=
    (nPlus_le_iff P p).2 fun i w ↦ eLie_mem_nPlus P p i (j :: w)
  exact this hx

/-- `[h, x] = μ(h) x` for `x ∈ U_μ`. -/
lemma superBracket_h_of_mem_weightSpace (a : H) {μ : Dual K H} {x : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) : superBracket P p (h P p a) x = μ a • x := by
  rw [superBracket_of_even_left P p (isEven_h P p a), hx a, add_sub_cancel_left]

/-- `[𝔥, ñ₊] ⊆ ñ₊`. -/
lemma superBracket_h_mem_nPlus (a : H) {x : P.SuperEnveloping p} (hx : x ∈ nPlus P p) :
    superBracket P p (h P p a) x ∈ nPlus P p := by
  have : nPlus P p ≤ (nPlus P p).comap (superBracketRight P p (h P p a)) :=
    (nPlus_le_iff P p).2 fun i w ↦ by
      rw [Submodule.mem_comap, superBracketRight_apply,
        superBracket_h_of_mem_weightSpace P p a (eLie_mem_weightSpace P p i w)]
      exact Submodule.smul_mem _ _ (eLie_mem_nPlus P p i w)
  exact this hx

/-- `[e_j, h] = -αⱼ(h) eⱼ`. -/
lemma superBracket_e_h (j : ι) (a : H) :
    superBracket P p (e P p j) (h P p a) = -(P.root j a • e P p j) := by
  rw [superBracket_of_even_right P p _ (isEven_h P p a), h_mul_e]
  abel

omit [CharZero K] in
lemma f_mul_e (i j : ι) : f P p i * e P p j = superSign K p i j • (e P p j * f P p i) -
    superSign K p i j • if i = j then h P p (P.coroot i) else 0 := by
  rw [e_mul_f, superSign_comm K p j i, smul_add, smul_smul, superSign_mul_self, one_smul]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/-- `[fₖ, eⱼ] = -δₖⱼ (-1)^{p j} hⱼ`. -/
lemma superBracket_f_e (k j : ι) :
    superBracket P p (f P p k) (e P p j) =
      -(superSign K p k j • if k = j then h P p (P.coroot k) else 0) := by
  rw [superBracket_of_isHomog (isHomog_f P p k) (isHomog_e P p j), f_mul_e,
    superSign_eq_zSign]
  abel

/-- `[eⱼ, ñ₊ + 𝔥] ⊆ ñ₊`. -/
lemma superBracket_e_mem_nPlus_of_mem_sup (j : ι) {x : P.SuperEnveloping p}
    (hx : x ∈ nPlus P p ⊔ LinearMap.range (h P p)) :
    superBracket P p (e P p j) x ∈ nPlus P p := by
  obtain ⟨y, hy, _, ⟨a, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
  rw [← superBracketRight_apply, map_add, superBracketRight_apply, superBracketRight_apply,
    superBracket_e_h]
  exact add_mem (superBracket_e_mem_nPlus P p j hy)
    (neg_mem (Submodule.smul_mem _ _ (e_mem_nPlus P p j)))

/-- `[fₖ, eLie i w] ∈ ñ₊ + 𝔥`. -/
lemma superBracket_f_eLie_mem (k i : ι) (w : List ι) :
    superBracket P p (f P p k) (eLie P p i w) ∈ nPlus P p ⊔ LinearMap.range (h P p) := by
  induction w with
  | nil =>
    rw [eLie_nil, superBracket_f_e]
    refine neg_mem (Submodule.smul_mem _ _ ?_)
    split_ifs
    · exact Submodule.mem_sup_right ⟨_, rfl⟩
    · exact zero_mem _
  | cons j w ih =>
    rw [eLie_cons, superBracket_jacobi (isHomog_f P p k) (isHomog_e P p j)
      (isHomog_eLie P p i w), superBracket_f_e, superBracket_neg_left, superBracket_smul_left]
    refine Submodule.mem_sup_left (add_mem (neg_mem (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ (superBracket_e_mem_nPlus_of_mem_sup P p j ih)))
    split_ifs
    · exact superBracket_h_mem_nPlus P p _ (eLie_mem_nPlus P p i w)
    · rw [superBracket_zero_left]; exact zero_mem _

/-- `[fₖ, ñ₊] ⊆ ñ₊ + 𝔥`. -/
lemma superBracket_f_mem_nPlus_sup (k : ι) {x : P.SuperEnveloping p} (hx : x ∈ nPlus P p) :
    superBracket P p (f P p k) x ∈ nPlus P p ⊔ LinearMap.range (h P p) := by
  have : nPlus P p ≤ (nPlus P p ⊔ LinearMap.range (h P p)).comap
      (superBracketRight P p (f P p k)) :=
    (nPlus_le_iff P p).2 fun i w ↦ superBracket_f_eLie_mem P p k i w
  exact this hx

/-! ### The Chevalley involution and `ñ₋` -/

omit [CharZero K]

/-- The data of the Chevalley involution. -/
def omegaData : LiftData P p (P.SuperEnveloping p) where
  h := -h P p
  e := f P p
  f i := paritySign K p i • e P p i
  h_mul_h a b := by simp [h_mul_h]
  e_mul_f i j := by
    rw [mul_smul_comm, smul_mul_assoc, f_mul_e, smul_sub, smul_smul, smul_smul,
      mul_comm (paritySign K p j)]
    by_cases hij : i = j
    · subst hij
      rcases zmod_two_cases (p i) with hi | hi <;> simp [superSign, paritySign, hi, sub_eq_add_neg]
    · simp [hij, smul_smul]
  h_mul_e a i := by
    simp only [LinearMap.neg_apply, neg_mul, mul_neg, h_mul_f]
    abel
  h_mul_f a i := by
    simp only [LinearMap.neg_apply, neg_mul, mul_neg, mul_smul_comm, smul_mul_assoc, h_mul_e]
    module

/-- The Chevalley involution `ω` of `U(G̃(A, τ))`: `eᵢ ↦ fᵢ`, `fᵢ ↦ (-1)^{p i} eᵢ`, `h ↦ -h`.
Its square is the parity involution `σ`. -/
def omega : P.SuperEnveloping p →ₐ[K] P.SuperEnveloping p := lift (omegaData P p)

@[simp] lemma omega_e (i : ι) : omega P p (e P p i) = f P p i := lift_e _ i

@[simp] lemma omega_f (i : ι) : omega P p (f P p i) = paritySign K p i • e P p i := lift_f _ i

@[simp] lemma omega_h (a : H) : omega P p (h P p a) = -h P p a := lift_h _ a

lemma omega_comp_omega : (omega P p).comp (omega P p) = parity P p := by
  refine hom_ext (fun i ↦ ?_) (fun i ↦ ?_) (fun a ↦ ?_) <;> simp

lemma omega_comp_parity : (omega P p).comp (parity P p) = (parity P p).comp (omega P p) := by
  refine hom_ext (fun i ↦ ?_) (fun i ↦ ?_) (fun a ↦ ?_) <;> simp

lemma omega_parity (u : P.SuperEnveloping p) :
    omega P p (parity P p u) = parity P p (omega P p u) :=
  congrArg (fun φ : P.SuperEnveloping p →ₐ[K] _ ↦ φ u) (omega_comp_parity P p)

lemma omega_superBracket (x y : P.SuperEnveloping p) :
    omega P p (superBracket P p x y) = superBracket P p (omega P p x) (omega P p y) := by
  simp only [superBracket, map_sub, map_mul, map_smul, map_add, omega_parity]

/-- The negative part `ñ₋ = ω(ñ₊)` of `G̃(A, τ)`. -/
def nMinus : Submodule K (P.SuperEnveloping p) := (nPlus P p).map (omega P p).toLinearMap

lemma omega_mem_nMinus {x : P.SuperEnveloping p} (hx : x ∈ nPlus P p) :
    omega P p x ∈ nMinus P p :=
  Submodule.mem_map_of_mem hx

lemma f_mem_nMinus (i : ι) : f P p i ∈ nMinus P p := by
  simpa using omega_mem_nMinus P p (e_mem_nPlus P p i)

lemma omega_sup_range_h :
    (nPlus P p ⊔ LinearMap.range (h P p)).map (omega P p).toLinearMap ≤
      nMinus P p ⊔ LinearMap.range (h P p) := by
  rw [Submodule.map_sup]
  refine sup_le_sup le_rfl ?_
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨-a, by simp⟩

/-- `[fⱼ, ñ₋] ⊆ ñ₋`. -/
lemma superBracket_f_mem_nMinus (j : ι) {x : P.SuperEnveloping p} (hx : x ∈ nMinus P p) :
    superBracket P p (f P p j) x ∈ nMinus P p := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [AlgHom.toLinearMap_apply, ← omega_e, ← omega_superBracket]
  exact omega_mem_nMinus P p (superBracket_e_mem_nPlus P p j hy)

variable [CharZero K] in
/-- `[eₖ, ñ₋] ⊆ ñ₋ + 𝔥`. -/
lemma superBracket_e_mem_nMinus_sup (k : ι) {x : P.SuperEnveloping p} (hx : x ∈ nMinus P p) :
    superBracket P p (e P p k) x ∈ nMinus P p ⊔ LinearMap.range (h P p) := by
  obtain ⟨y, hy, rfl⟩ := hx
  have he : e P p k = paritySign K p k • omega P p (f P p k) := by
    rw [omega_f, smul_smul, paritySign_mul_self, one_smul]
  rw [AlgHom.toLinearMap_apply, he, superBracket_smul_left, ← omega_superBracket]
  exact Submodule.smul_mem _ _
    (omega_sup_range_h P p (Submodule.mem_map_of_mem (superBracket_f_mem_nPlus_sup P p k hy)))

variable [CharZero K] in
/-- `[𝔥, ñ₋] ⊆ ñ₋`. -/
lemma superBracket_h_mem_nMinus (a : H) {x : P.SuperEnveloping p} (hx : x ∈ nMinus P p) :
    superBracket P p (h P p a) x ∈ nMinus P p := by
  obtain ⟨y, hy, rfl⟩ := hx
  have : h P p a = omega P p (h P p (-a)) := by simp
  rw [AlgHom.toLinearMap_apply, this, ← omega_superBracket]
  exact omega_mem_nMinus P p (superBracket_h_mem_nPlus P p _ hy)

/-! ### The sum `ñ₋ + 𝔥 + ñ₊` is direct -/

/-- The parity involution of `T(V)`, `vᵢ ↦ (-1)^{p i} vᵢ`. -/
def parityT : FreeAlgebra K ι →ₐ[K] FreeAlgebra K ι :=
  FreeAlgebra.lift K fun i ↦ paritySign K p i • FreeAlgebra.ι K i

lemma parity_fAlg (x : FreeAlgebra K ι) : parity P p (fAlg P p x) = fAlg P p (parityT p x) := by
  have : (parity P p).comp (fAlg P p) = (fAlg P p).comp (parityT (K := K) p) :=
    FreeAlgebra.hom_ext (funext fun i ↦ by simp [parityT])
  exact congrArg (fun φ : FreeAlgebra K ι →ₐ[K] _ ↦ φ x) this

/-- The image under `fAlg` of the augmentation ideal of `T(V)`. -/
def fAug : Submodule K (P.SuperEnveloping p) :=
  (LinearMap.ker (FreeAlgebra.algebraMapInv (R := K) (X := ι)).toLinearMap).map
    (fAlg P p).toLinearMap

lemma superBracket_f_mem_fAug (j : ι) {x : P.SuperEnveloping p} (hx : x ∈ fAug P p) :
    superBracket P p (f P p j) x ∈ fAug P p := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨FreeAlgebra.ι K j * t - (2 : K)⁻¹ • ((t + parityT p t) * FreeAlgebra.ι K j +
    (t - parityT p t) * (paritySign K p j • FreeAlgebra.ι K j)), ?_, ?_⟩
  · simp [FreeAlgebra.algebraMapInv]
  · simp [superBracket, parity_fAlg]

lemma nMinus_le_fAug : nMinus P p ≤ fAug P p := by
  rintro _ ⟨y, hy, rfl⟩
  have : nPlus P p ≤ (fAug P p).comap (omega P p).toLinearMap :=
    (nPlus_le_iff P p).2 fun i w ↦ by
      induction w with
      | nil =>
        exact ⟨FreeAlgebra.ι K i, by simp [FreeAlgebra.algebraMapInv], by simp⟩
      | cons j w ih =>
        rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, eLie_cons, omega_superBracket,
          omega_e]
        exact superBracket_f_mem_fAug P p j ih
  exact this hy

lemma nPlus_le_vermaIdeal (Λ : Dual K H) : nPlus P p ≤ (vermaIdeal P p Λ).restrictScalars K := by
  refine (nPlus_le_iff P p).2 fun i w ↦ ?_
  induction w with
  | nil => exact e_mem_vermaIdeal P p Λ i
  | cons j w ih =>
    rw [Submodule.restrictScalars_mem] at ih ⊢
    rw [eLie_cons, superBracket, parity_e, mul_smul_comm]
    exact sub_mem (mul_mem_vermaIdeal P p Λ _ ih) (Submodule.smul_of_tower_mem _ _ (add_mem
      (mul_mem_vermaIdeal P p Λ _ (e_mem_vermaIdeal P p Λ j))
      (Submodule.smul_of_tower_mem _ _ (mul_mem_vermaIdeal P p Λ _ (e_mem_vermaIdeal P p Λ j)))))

/-- The sum `ñ₋ + 𝔥 + ñ₊` is direct ([Kac78] §1.1, cf. [Kac] Thm. 1.2 (a), (b)). -/
theorem eq_zero_of_add_add_eq_zero {x y : P.SuperEnveloping p} (hx : x ∈ nMinus P p) (a : H)
    (hy : y ∈ nPlus P p) (hsum : x + h P p a + y = 0) : x = 0 ∧ a = 0 ∧ y = 0 := by
  obtain ⟨t, ht, rfl⟩ := nMinus_le_fAug P p hx
  have ht : FreeAlgebra.algebraMapInv t = 0 := ht
  have key : ∀ Λ : Dual K H, t + Λ a • 1 = 0 := fun Λ ↦ by
    have h1 := congrArg (fun u ↦ tensorRep P p Λ u 1) hsum
    have h2 := Verma.vermaIdeal_le_ker_toTensorAux P p Λ (nPlus_le_vermaIdeal P p Λ hy)
    simp only [LinearMap.mem_ker, Verma.toTensorAux_apply] at h2
    simpa [map_add, LinearMap.add_apply, tensorRep_fAlg_one, tensorRep_h_one, h2] using h1
  have ha : a = 0 := (forall_dual_apply_eq_zero_iff K a).mp fun Λ ↦ by
    have := congrArg FreeAlgebra.algebraMapInv (key Λ)
    rwa [map_add, map_smul, map_one, ht, zero_add, smul_eq_mul, mul_one, map_zero] at this
  have htz : t = 0 := by simpa [ha] using key 0
  subst ha htz
  refine ⟨by simp, rfl, ?_⟩
  simpa using hsum

end SuperEnveloping

end Matrix.Realization
