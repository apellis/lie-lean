/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.RootSpace
import LieLean.Algebra.Lie.KacMoody.Super.Triangular

/-!
# The auxiliary Lie superalgebra `G̃(A, τ)` inside its enveloping algebra

We realize the auxiliary contragredient Lie superalgebra `G̃(A, τ)` of [Kac78] §1.1 as the
subspace `G̃ = ñ₋ + 𝔥 + ñ₊` of `U = U(G̃(A, τ))` (`SuperEnveloping.gTilde`), and prove that it is
closed under the super commutator (`superBracket_mem_gTilde`). The positive part `ñ₊` lies in the
sum of the weight spaces `U_α`, `α ∈ Q₊ \ {0}`, and `ñ₋` in the sum of the `U_{-α}`; hence
`G̃ ∩ U_0 = 𝔥` (`gTilde_inf_weightSpace_zero`) and `[ñ₊ ∩ U_α, ñ₋ ∩ U_{-α}] ⊆ 𝔥`
(`superBracket_mem_range_h`), which is the starting point of the invariant form ([Kac78] §1.4,
cf. [Kac] §2.2).

## Main definitions

* `Matrix.Realization.SuperEnveloping.gTilde`: the subspace `ñ₋ + 𝔥 + ñ₊` of `U`.
* `Matrix.Realization.SuperEnveloping.wordVec`: the root-lattice coordinates of a word.

## Main results

* `Matrix.Realization.SuperEnveloping.superBracket_mem_gTilde`: `[G̃, G̃] ⊆ G̃`.
* `Matrix.Realization.SuperEnveloping.nPlus_le_iSup_weightSpace`,
  `Matrix.Realization.SuperEnveloping.nMinus_le_iSup_weightSpace`: weights of `ñ₊` and `ñ₋`.
* `Matrix.Realization.SuperEnveloping.gTilde_inf_weightSpace_zero`: `G̃ ∩ U_0 = 𝔥`.
* `Matrix.Realization.SuperEnveloping.superBracket_mem_range_h`: `[ñ₊ ∩ U_α, ñ₋ ∩ U_{-α}] ⊆ 𝔥`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.1.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.2–1.3.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

namespace SuperEnveloping

/-! ### Linearity of the super commutator -/

lemma superBracket_add_left (x y z : P.SuperEnveloping p) :
    superBracket P p (x + y) z = superBracket P p x z + superBracket P p y z := by
  simp only [superBracket, map_add, add_mul, mul_add, smul_add]
  abel

/-- The super commutator `[-, y]` as a linear map. -/
def superBracketLeft (y : P.SuperEnveloping p) : P.SuperEnveloping p →ₗ[K] P.SuperEnveloping p where
  toFun x := superBracket P p x y
  map_add' x x' := superBracket_add_left P p x x' y
  map_smul' c x := superBracket_smul_left c x y

@[simp] lemma superBracketLeft_apply (x y : P.SuperEnveloping p) :
    superBracketLeft P p y x = superBracket P p x y := rfl

/-! ### The subspace `G̃` -/

/-- The auxiliary Lie superalgebra `G̃(A, τ) = ñ₋ + 𝔥 + ñ₊`, as a subspace of `U(G̃(A, τ))`. -/
def gTilde : Submodule K (P.SuperEnveloping p) :=
  nMinus P p ⊔ LinearMap.range (h P p) ⊔ nPlus P p

lemma mem_gTilde_iff {x : P.SuperEnveloping p} :
    x ∈ gTilde P p ↔ ∃ n ∈ nMinus P p, ∃ a, ∃ m ∈ nPlus P p, n + h P p a + m = x := by
  simp only [gTilde, Submodule.mem_sup, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨n, hn, _, ⟨a, rfl⟩, rfl⟩, m, hm, rfl⟩
    exact ⟨n, hn, a, m, hm, rfl⟩
  · rintro ⟨n, hn, a, m, hm, rfl⟩
    exact ⟨_, ⟨n, hn, _, ⟨a, rfl⟩, rfl⟩, m, hm, rfl⟩

lemma nMinus_le_gTilde : nMinus P p ≤ gTilde P p := le_sup_left.trans le_sup_left

lemma range_h_le_gTilde : LinearMap.range (h P p) ≤ gTilde P p := le_sup_right.trans le_sup_left

lemma nPlus_le_gTilde : nPlus P p ≤ gTilde P p := le_sup_right

lemma h_mem_gTilde (a : H) : h P p a ∈ gTilde P p := range_h_le_gTilde P p ⟨a, rfl⟩

lemma nMinus_sup_le_gTilde : nMinus P p ⊔ LinearMap.range (h P p) ≤ gTilde P p := le_sup_left

lemma nPlus_sup_le_gTilde : nPlus P p ⊔ LinearMap.range (h P p) ≤ gTilde P p :=
  sup_le (nPlus_le_gTilde P p) (range_h_le_gTilde P p)

variable [CharZero K]

/-- `[eⱼ, G̃] ⊆ G̃`. -/
lemma superBracket_e_mem_gTilde (j : ι) {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) :
    superBracket P p (e P p j) x ∈ gTilde P p := by
  obtain ⟨n, hn, a, m, hm, rfl⟩ := (mem_gTilde_iff P p).1 hx
  simp only [← superBracketRight_apply, map_add]
  refine add_mem (add_mem (nMinus_sup_le_gTilde P p (superBracket_e_mem_nMinus_sup P p j hn)) ?_)
    (nPlus_le_gTilde P p (superBracket_e_mem_nPlus P p j hm))
  rw [superBracketRight_apply, superBracket_e_h]
  exact neg_mem (Submodule.smul_mem _ _ (nPlus_le_gTilde P p (e_mem_nPlus P p j)))

/-- `[fⱼ, G̃] ⊆ G̃`. -/
lemma superBracket_f_mem_gTilde (j : ι) {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) :
    superBracket P p (f P p j) x ∈ gTilde P p := by
  obtain ⟨n, hn, a, m, hm, rfl⟩ := (mem_gTilde_iff P p).1 hx
  simp only [← superBracketRight_apply, map_add]
  refine add_mem (add_mem (nMinus_le_gTilde P p (superBracket_f_mem_nMinus P p j hn)) ?_)
    (nPlus_sup_le_gTilde P p (superBracket_f_mem_nPlus_sup P p j hm))
  rw [superBracketRight_apply, superBracket_of_even_right P p _ (isEven_h P p a), h_mul_f]
  rw [sub_sub_cancel]
  exact Submodule.smul_mem _ _ (nMinus_le_gTilde P p (f_mem_nMinus P p j))

/-- `[𝔥, G̃] ⊆ G̃`. -/
lemma superBracket_h_mem_gTilde (b : H) {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) :
    superBracket P p (h P p b) x ∈ gTilde P p := by
  obtain ⟨n, hn, a, m, hm, rfl⟩ := (mem_gTilde_iff P p).1 hx
  simp only [← superBracketRight_apply, map_add]
  refine add_mem (add_mem (nMinus_le_gTilde P p (superBracket_h_mem_nMinus P p b hn)) ?_)
    (nPlus_le_gTilde P p (superBracket_h_mem_nPlus P p b hm))
  rw [superBracketRight_apply, superBracket_of_even_left P p (isEven_h P p b), h_mul_h, sub_self]
  exact zero_mem _

/-- The elements `y` with `[y, G̃] ⊆ G̃`. -/
def bracketStable : Submodule K (P.SuperEnveloping p) where
  carrier := {y | ∀ x ∈ gTilde P p, superBracket P p y x ∈ gTilde P p}
  add_mem' hy hy' x hx := by
    rw [superBracket_add_left]; exact add_mem (hy x hx) (hy' x hx)
  zero_mem' x _ := by rw [superBracket_zero_left]; exact zero_mem _
  smul_mem' c y hy x hx := by
    rw [superBracket_smul_left]; exact Submodule.smul_mem _ _ (hy x hx)

omit [CharZero K] in
lemma IsHomog.omega {c : ZMod 2} {x : P.SuperEnveloping p} (hx : IsHomog P p c x) :
    IsHomog P p c (omega P p x) := by
  rw [IsHomog, ← omega_parity, hx, map_smul]

/-- `G̃` is spanned by homogeneous elements. -/
lemma gTilde_le_span_homog :
    gTilde P p ≤ Submodule.span K {x | x ∈ gTilde P p ∧ ∃ c, IsHomog P p c x} := by
  have hP : nPlus P p ≤ Submodule.span K {x | x ∈ gTilde P p ∧ ∃ c, IsHomog P p c x} :=
    (nPlus_le_iff P p).2 fun i w ↦ Submodule.subset_span
      ⟨nPlus_le_gTilde P p (eLie_mem_nPlus P p i w), _, isHomog_eLie P p i w⟩
  refine sup_le (sup_le ?_ ?_) hP
  · rintro _ ⟨y, hy, rfl⟩
    have : nPlus P p ≤ (Submodule.span K {x | x ∈ gTilde P p ∧ ∃ c, IsHomog P p c x}).comap
        (omega P p).toLinearMap :=
      (nPlus_le_iff P p).2 fun i w ↦ Submodule.subset_span
        ⟨nMinus_le_gTilde P p (omega_mem_nMinus P p (eLie_mem_nPlus P p i w)), _,
          (isHomog_eLie P p i w).omega⟩
    exact this hy
  · rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨h_mem_gTilde P p a, 0, isHomog_h P p a⟩

/-- If `[y, G̃] ⊆ G̃` and `g` is a homogeneous element with `[g, G̃] ⊆ G̃`, then
`[[g, y], G̃] ⊆ G̃`, by the super Jacobi identity. -/
lemma superBracket_mem_bracketStable {a b : ZMod 2} {g y : P.SuperEnveloping p}
    (hg : IsHomog P p a g) (hy : IsHomog P p b y) (hg' : g ∈ bracketStable P p)
    (hy' : y ∈ bracketStable P p) : superBracket P p g y ∈ bracketStable P p := by
  intro x hx
  have key : Submodule.span K {x | x ∈ gTilde P p ∧ ∃ c, IsHomog P p c x} ≤
      (gTilde P p).comap (superBracketRight P p (superBracket P p g y)) := by
    refine Submodule.span_le.2 fun z ⟨hz, c, hc⟩ ↦ ?_
    have hj := superBracket_jacobi hg hy hc
    simp only [SetLike.mem_coe, Submodule.mem_comap, superBracketRight_apply]
    rw [eq_sub_of_add_eq hj.symm]
    exact sub_mem (hg' _ (hy' _ hz)) (Submodule.smul_mem _ _ (hy' _ (hg' _ hz)))
  exact key (gTilde_le_span_homog P p hx)


lemma e_mem_bracketStable (j : ι) : e P p j ∈ bracketStable P p :=
  fun _ hx ↦ superBracket_e_mem_gTilde P p j hx

lemma f_mem_bracketStable (j : ι) : f P p j ∈ bracketStable P p :=
  fun _ hx ↦ superBracket_f_mem_gTilde P p j hx

lemma h_mem_bracketStable (a : H) : h P p a ∈ bracketStable P p :=
  fun _ hx ↦ superBracket_h_mem_gTilde P p a hx

lemma nPlus_le_bracketStable : nPlus P p ≤ bracketStable P p := by
  refine (nPlus_le_iff P p).2 fun i w ↦ ?_
  induction w with
  | nil => simpa using e_mem_bracketStable P p i
  | cons j w ih =>
    rw [eLie_cons]
    exact superBracket_mem_bracketStable P p (isHomog_e P p j) (isHomog_eLie P p i w)
      (e_mem_bracketStable P p j) ih

omit [CharZero K] in
lemma omega_eLie_cons (i j : ι) (w : List ι) :
    omega P p (eLie P p i (j :: w)) = superBracket P p (f P p j) (omega P p (eLie P p i w)) := by
  rw [eLie_cons, omega_superBracket, omega_e]

lemma nMinus_le_bracketStable : nMinus P p ≤ bracketStable P p := by
  refine Submodule.map_le_iff_le_comap.2 ((nPlus_le_iff P p).2 fun i w ↦ ?_)
  simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply]
  induction w with
  | nil => simpa using f_mem_bracketStable P p i
  | cons j w ih =>
    rw [omega_eLie_cons]
    exact superBracket_mem_bracketStable P p (isHomog_f P p j) (isHomog_eLie P p i w).omega
      (f_mem_bracketStable P p j) ih

lemma gTilde_le_bracketStable : gTilde P p ≤ bracketStable P p :=
  sup_le (sup_le (nMinus_le_bracketStable P p) (by
    rintro _ ⟨a, rfl⟩; exact h_mem_bracketStable P p a)) (nPlus_le_bracketStable P p)

/-- `G̃` is closed under the super commutator: `[G̃, G̃] ⊆ G̃` ([Kac78] §1.1). -/
theorem superBracket_mem_gTilde {x y : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hy : y ∈ gTilde P p) : superBracket P p x y ∈ gTilde P p :=
  gTilde_le_bracketStable P p hx y hy

/-! ### Weights of `ñ₊` and `ñ₋` -/

omit [CharZero K]

/-- The root-lattice coordinates `∑ₖ e_{wₖ}` of a word `w`. -/
def wordVec (w : List ι) : ι → ℤ := (w.map fun j ↦ Pi.single j 1).sum

omit [Fintype ι] in
@[simp] lemma wordVec_nil : wordVec ([] : List ι) = 0 := rfl

omit [Fintype ι] in
@[simp] lemma wordVec_cons (j : ι) (w : List ι) :
    wordVec (j :: w) = Pi.single j 1 + wordVec w := by
  simp [wordVec]

omit [Fintype ι] in
lemma wordVec_nonneg (w : List ι) : 0 ≤ wordVec w := by
  induction w with
  | nil => exact le_rfl
  | cons j w ih =>
    rw [wordVec_cons]
    exact add_nonneg (fun k ↦ by by_cases hk : k = j <;> simp [hk]) ih

omit [Fintype ι] in
lemma wordVec_cons_mem_posCone (i : ι) (w : List ι) : wordVec (i :: w) ∈ posCone ι := by
  refine ⟨wordVec_nonneg _, fun h0 ↦ ?_⟩
  have := congrFun h0 i
  have hw := wordVec_nonneg w i
  simp only [wordVec_cons, Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this hw
  omega

lemma rootOf_wordVec (w : List ι) : P.rootOf (wordVec w) = (w.map P.root).sum := by
  induction w with
  | nil => simp
  | cons j w ih => simp [ih]

/-- `ñ₊ ⊆ ⨁_{α ∈ Q₊ \ {0}} U_α`. -/
lemma nPlus_le_iSup_weightSpace :
    nPlus P p ≤ ⨆ k ∈ posCone ι, weightSpace P p (P.rootOf k) := by
  refine (nPlus_le_iff P p).2 fun i w ↦ ?_
  have hw : eLie P p i w ∈ weightSpace P p (P.rootOf (wordVec (i :: w))) := by
    rw [rootOf_wordVec, List.map_cons, List.sum_cons, add_comm]
    exact eLie_mem_weightSpace P p i w
  exact (le_biSup (fun k ↦ weightSpace P p (P.rootOf k)) (wordVec_cons_mem_posCone i w)) hw

lemma omega_mem_weightSpace {μ : Dual K H} {x : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p μ) : omega P p x ∈ weightSpace P p (-μ) := fun a ↦ by
  have := congrArg (omega P p) (hx a)
  simp only [map_mul, map_add, map_smul, omega_h, neg_mul, mul_neg] at this
  rw [LinearMap.neg_apply, neg_smul, ← neg_inj, this]
  abel

/-- `ñ₋ ⊆ ⨁_{α ∈ Q₊ \ {0}} U_{-α}`. -/
lemma nMinus_le_iSup_weightSpace :
    nMinus P p ≤ ⨆ k ∈ posCone ι, weightSpace P p (-P.rootOf k) := by
  refine Submodule.map_le_iff_le_comap.2 ((nPlus_le_iSup_weightSpace P p).trans ?_)
  refine iSup₂_le fun k hk x hx ↦ ?_
  exact (le_biSup (fun k ↦ weightSpace P p (-P.rootOf k)) hk) (omega_mem_weightSpace P p hx)

variable [CharZero K]

lemma nPlus_le_iSup_ne_zero : nPlus P p ≤ ⨆ μ ∈ {μ : Dual K H | μ ≠ 0}, weightSpace P p μ :=
  (nPlus_le_iSup_weightSpace P p).trans <| iSup₂_le fun k hk ↦
    le_biSup (fun μ ↦ weightSpace P p μ) (show P.rootOf k ≠ 0 from P.rootOf_ne_zero hk.2)

lemma nMinus_le_iSup_ne_zero : nMinus P p ≤ ⨆ μ ∈ {μ : Dual K H | μ ≠ 0}, weightSpace P p μ :=
  (nMinus_le_iSup_weightSpace P p).trans <| iSup₂_le fun k hk ↦
    le_biSup (fun μ ↦ weightSpace P p μ)
      (show -P.rootOf k ≠ 0 from neg_ne_zero.2 (P.rootOf_ne_zero hk.2))

/-- `G̃ ∩ U_0 = 𝔥`. -/
theorem gTilde_inf_weightSpace_zero :
    gTilde P p ⊓ weightSpace P p 0 = LinearMap.range (h P p) := by
  refine le_antisymm ?_ (le_inf (range_h_le_gTilde P p) ?_)
  · rintro x ⟨hx, hx0⟩
    obtain ⟨n, hn, a, m, hm, rfl⟩ := (mem_gTilde_iff P p).1 hx
    have hS : n + m ∈ ⨆ μ ∈ {μ : Dual K H | μ ≠ 0}, weightSpace P p μ :=
      add_mem (nMinus_le_iSup_ne_zero P p hn) (nPlus_le_iSup_ne_zero P p hm)
    have h0 : n + m ∈ weightSpace P p 0 := by
      have := sub_mem hx0 (h_mem_weightSpace P p a)
      rwa [add_right_comm, add_sub_cancel_right] at this
    have hnm : n + m = 0 := by
      have := (iSupIndep_weightSpace P p).disjoint_biSup (y := {μ : Dual K H | μ ≠ 0})
        (x := 0) (by simp)
      exact (Submodule.disjoint_def.1 this) _ h0 hS
    have := eq_zero_of_add_add_eq_zero P p hn 0 hm (by rw [map_zero, add_zero, hnm])
    rw [this.1, this.2.2, zero_add, add_zero]
    exact ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩; exact h_mem_weightSpace P p a

/-- `[ñ₊ ∩ U_α, ñ₋ ∩ U_{-α}] ⊆ 𝔥`. -/
theorem superBracket_mem_range_h {μ : Dual K H} {x y : P.SuperEnveloping p}
    (hx : x ∈ nPlus P p) (hxμ : x ∈ weightSpace P p μ) (hy : y ∈ nMinus P p)
    (hyμ : y ∈ weightSpace P p (-μ)) : superBracket P p x y ∈ LinearMap.range (h P p) := by
  rw [← gTilde_inf_weightSpace_zero]
  refine ⟨superBracket_mem_gTilde P p (nPlus_le_gTilde P p hx) (nMinus_le_gTilde P p hy), ?_⟩
  simpa using superBracket_mem_weightSpace hxμ hyμ

end SuperEnveloping

end Matrix.Realization
