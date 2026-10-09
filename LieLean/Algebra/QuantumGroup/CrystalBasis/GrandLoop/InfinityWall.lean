/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityStar

/-!
# The forms `G_z` at a wall

The Shapovalov form of `M_q(λ)` pulled back to `'f` is the member `z = (vⱼ^{-2⟨j,λ⟩})ⱼ` of the
family `G_z` (`VermaModule.shapZ`, `G_z(θⱼ x, y) = G_z(x, (Lⱼ - zⱼ Rⱼ) y)`). If `⟨i, λ⟩ = 0` and
`⟨j, λ⟩ ≫ 0` for `j ≠ i`, then `z` is close to `zᵂ = (δᵢⱼ)ⱼ` (`VermaModule.zWall`). We show:

* `G_z(x, y θᵢ) = 0` whenever `zᵢ = 1` (`VermaModule.shapZ_mul_θ_eq_zero`), the counterpart of
  `Fᵢ v_λ = 0` for `⟨i, λ⟩ = 0`;
* `G_{zᵂ}(x, y) = (x, y)` when `rᵢ y ∈ J` (`VermaModule.shapZ_zWall_eq_form`);
* `G_z` kills `J` in the second variable (`VermaModule.shapZ_eq_zero_of_mem`);
* on words of bounded length, `G_z ≡ G_{z'}` modulo `ϖᵐ` up to a fixed power of `ϖ` when
  `z ≡ z'` modulo `ϖᵐ` and `z'` is `A`-valued (`VermaModule.exists_shapZ_sub_shapZ_mem`, extending
  `VermaModule.exists_shapZ_sub_mem`).

Hence `G_{zᵂ}(x, y) = (x, y⁰)`, where `y⁰` is the component in `ker e''ᵢ` (`e''ᵢ = * e'ᵢ *`) of
`y = Σₙ yₙ fᵢ^{(n)}` (`GrandLoop.comp0`, `GrandLoop.shapZ_zWall_eq_formU`), and for `⟨i, λ⟩ = 0`,
`⟨j, λ⟩ ≫ 0` (`j ≠ i`):

* `(π_λ x, π_λ y)_λ ≡ (x, y⁰)` modulo `ϖ` on `L(∞) ∩ U⁻_{-ν}`
  (`GrandLoop.exists_form_evq_sub_formU`);
* if `A/ϖA` is formally real, `P ∈ L(∞) ∖ ϖ L(∞)` and `e''ᵢ P = 0`, then `π_λ(P) ∉ ϖ L(λ)`
  (`GrandLoop.evq_notMem_smul_lat`).

The last statement is used in [Kas93a] Prop. 2.1.2 (`P u_λ ∈ B(λ)` there), where it rests on the
global bases of [Kas91] (Thm. 7); the argument here uses only the forms.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516.
* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858.
-/

open Finset Pointwise LusztigF FreeAlgebra

noncomputable section

namespace LieLean.QuantumGroup

namespace VermaModule

variable {k I : Type*} [Field k] [DecidableEq I] {D : LusztigCartanDatum I} {v : k} [NeZero v]

/-! ### The operators `T_z(x)` -/

section Ops

variable {z : I → k}

omit [NeZero v] in
lemma unop_opZ_algebraMap (c : k) (y : LusztigF k I) :
    (opZ D v z (algebraMap k _ c)).unop y = c • y := by
  simp [opZ, Algebra.algebraMap_eq_smul_one]

omit [NeZero v] in
lemma unop_opZ_θ (j : I) (y : LusztigF k I) :
    (opZ D v z (θ k j)).unop y = Lop D v j y - z j • Rop D v j y := by
  simp [opZ, θ]

omit [NeZero v] in
lemma unop_opZ_mul (a b y : LusztigF k I) :
    (opZ D v z (a * b)).unop y = (opZ D v z b).unop ((opZ D v z a).unop y) := by
  simp [map_mul, MulOpposite.unop_mul]

omit [NeZero v] in
lemma unop_opZ_add (a b y : LusztigF k I) :
    (opZ D v z (a + b)).unop y = (opZ D v z a).unop y + (opZ D v z b).unop y := by
  simp [map_add]

/-- `Tⱼ(y θᵢ) ∈ 'f θᵢ` when `zᵢ = 1`. -/
lemma exists_unop_opZ_mul_θ {i : I} (hz : z i = 1) (a : LusztigF k I) :
    ∀ y, ∃ y', (opZ D v z a).unop (y * θ k i) = y' * θ k i := by
  induction a using FreeAlgebra.induction with
  | grade0 c => exact fun y ↦ ⟨c • y, by rw [unop_opZ_algebraMap, smul_mul_assoc]⟩
  | grade1 j =>
    intro y
    refine ⟨thetaNorm D v j • lDeriv D v j y - z j • ((v ^ D.d j * (qDenom D v j)⁻¹) •
      (v ^ D.dot j i • v ^ D.dot j i • twist D v j (rDeriv D v j y))), ?_⟩
    have hθ : ι k j = θ k j := rfl
    rw [hθ, unop_opZ_θ, Lop, Rop, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, AlgHom.toLinearMap_apply, lDeriv_mul, rDeriv_mul_θ, lDeriv_θ,
      map_add, map_smul, map_mul, twist_θ]
    by_cases h : j = i
    · subst h
      simp only [↓reduceIte]
      rw [hz, thetaNorm_eq]
      simp only [mul_one, one_smul, smul_add, sub_mul, smul_mul_assoc, mul_smul_comm]
      abel
    · simp only [h, ↓reduceIte, mul_zero, add_zero, map_zero, zero_add, sub_mul, smul_mul_assoc,
        mul_smul_comm]
  | mul a b ha hb =>
    intro y
    obtain ⟨y₁, h₁⟩ := ha y
    obtain ⟨y₂, h₂⟩ := hb y₁
    exact ⟨y₂, by rw [unop_opZ_mul, h₁, h₂]⟩
  | add a b ha hb =>
    intro y
    obtain ⟨y₁, h₁⟩ := ha y
    obtain ⟨y₂, h₂⟩ := hb y
    exact ⟨y₁ + y₂, by rw [unop_opZ_add, h₁, h₂, add_mul]⟩

/-- `G_z(x, y θᵢ) = 0` when `zᵢ = 1`. -/
theorem shapZ_mul_θ_eq_zero {i : I} (hz : z i = 1) (x y : LusztigF k I) :
    shapZ D v z x (y * θ k i) = 0 := by
  obtain ⟨y', h⟩ := exists_unop_opZ_mul_θ (D := D) (v := v) hz x y
  rw [shapZ, h, map_mul]
  simp [θ]

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

/-- The operators `T_z(a)` preserve `J`. -/
lemma unop_opZ_mem_serreIdeal (a : LusztigF k I) :
    ∀ y ∈ serreIdeal D v, (opZ D v z a).unop y ∈ serreIdeal D v := by
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro y hy
    rw [unop_opZ_algebraMap]; exact smul_mem_serreIdeal c hy
  | grade1 j =>
    intro y hy
    rw [show ι k j = θ k j from rfl, unop_opZ_θ, Lop, Rop]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    refine TwoSidedIdeal.sub_mem _ (smul_mem_serreIdeal _ ?_) (smul_mem_serreIdeal _
      (smul_mem_serreIdeal _ ?_))
    · exact lDeriv_mem_serreIdeal (NeZero.ne v) hv' j hy
    · exact twist_mem_serreIdeal j (rDeriv_mem_serreIdeal (NeZero.ne v) hv' j hy)
  | mul a b ha hb => intro y hy; rw [unop_opZ_mul]; exact hb _ (ha y hy)
  | add a b ha hb =>
    intro y hy; rw [unop_opZ_add]; exact TwoSidedIdeal.add_mem _ (ha y hy) (hb y hy)

/-- `G_z` kills `J` in the second variable. -/
theorem shapZ_eq_zero_of_mem (x : LusztigF k I) {y : LusztigF k I} (hy : y ∈ serreIdeal D v) :
    shapZ D v z x y = 0 :=
  counit_eq_zero_of_mem_serreIdeal (unop_opZ_mem_serreIdeal hv' x y hy)

end Ops

/-! ### The wall parameter -/

variable (i : I) in
/-- `zᵂ = (δᵢⱼ)ⱼ`: the limit of `(vⱼ^{-2⟨j,λ⟩})ⱼ` for `⟨i,λ⟩ = 0` and `⟨j,λ⟩ → ∞`, `j ≠ i`. -/
def zWall : I → k := fun j ↦ if j = i then 1 else 0

omit [NeZero v] in
@[simp] lemma zWall_self (i : I) : zWall (k := k) i i = 1 := by simp [zWall]

section WallForm

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

lemma unop_opZ_zWall (i : I) (a : LusztigF k I) :
    ∀ y, rDeriv D v i y ∈ serreIdeal D v →
      (opZ D v (zWall i) a).unop y - (opZ D v 0 a).unop y ∈ serreIdeal D v ∧
        rDeriv D v i ((opZ D v 0 a).unop y) ∈ serreIdeal D v := by
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro y hy
    rw [unop_opZ_algebraMap, unop_opZ_algebraMap, sub_self, map_smul]
    exact ⟨TwoSidedIdeal.zero_mem _, smul_mem_serreIdeal c hy⟩
  | grade1 j =>
    intro y hy
    rw [show ι k j = θ k j from rfl, unop_opZ_θ, unop_opZ_θ, Pi.zero_apply, zero_smul, sub_zero,
      sub_sub_cancel_left]
    refine ⟨TwoSidedIdeal.neg_mem _ ?_, ?_⟩
    · by_cases h : j = i
      · subst h
        rw [zWall_self, one_smul, Rop]
        simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
        exact smul_mem_serreIdeal _ (twist_mem_serreIdeal j hy)
      · simp only [zWall, h, ↓reduceIte, zero_smul]
        exact TwoSidedIdeal.zero_mem _
    · rw [Lop, LinearMap.smul_apply, map_smul, ← lDeriv_rDeriv]
      exact smul_mem_serreIdeal _ (lDeriv_mem_serreIdeal (NeZero.ne v) hv' j hy)
  | mul a b ha hb =>
    intro y hy
    obtain ⟨h₁, h₂⟩ := ha y hy
    obtain ⟨h₃, h₄⟩ := hb _ h₂
    refine ⟨?_, by rw [unop_opZ_mul]; exact h₄⟩
    rw [unop_opZ_mul, unop_opZ_mul]
    have : (opZ D v (zWall i) b).unop ((opZ D v (zWall i) a).unop y) -
        (opZ D v 0 b).unop ((opZ D v 0 a).unop y) =
        (opZ D v (zWall i) b).unop ((opZ D v (zWall i) a).unop y - (opZ D v 0 a).unop y) +
          ((opZ D v (zWall i) b).unop ((opZ D v 0 a).unop y) -
            (opZ D v 0 b).unop ((opZ D v 0 a).unop y)) := by
      rw [map_sub]; abel
    rw [this]
    exact TwoSidedIdeal.add_mem _ (unop_opZ_mem_serreIdeal hv' b _ h₁) h₃
  | add a b ha hb =>
    intro y hy
    obtain ⟨h₁, h₂⟩ := ha y hy
    obtain ⟨h₃, h₄⟩ := hb y hy
    rw [unop_opZ_add, unop_opZ_add, map_add]
    refine ⟨?_, TwoSidedIdeal.add_mem _ h₂ h₄⟩
    have : (opZ D v (zWall i) a).unop y + (opZ D v (zWall i) b).unop y -
        ((opZ D v 0 a).unop y + (opZ D v 0 b).unop y) =
        ((opZ D v (zWall i) a).unop y - (opZ D v 0 a).unop y) +
          ((opZ D v (zWall i) b).unop y - (opZ D v 0 b).unop y) := by abel
    rw [this]
    exact TwoSidedIdeal.add_mem _ h₁ h₃

/-- `G_{zᵂ}(x, y) = (x, y)` when `rᵢ y ∈ J`. -/
theorem shapZ_zWall_eq_form (i : I) (x : LusztigF k I) {y : LusztigF k I}
    (hy : rDeriv D v i y ∈ serreIdeal D v) :
    shapZ D v (zWall i) x y = LusztigF.form D v x y := by
  rw [form_eq_shapZ_zero, ← sub_eq_zero, shapZ, shapZ, ← map_sub]
  exact counit_eq_zero_of_mem_serreIdeal (unop_opZ_zWall hv' i x y hy).1

end WallForm

/-! ### Comparison of `G_z` and `G_{z'}` -/

section Estimate

variable (A : Type*) [CommRing A] [Algebra A k]

/-- **`G_z ≡ G_{z'}` modulo `ϖᵐ`** on the lattice of words of length `≤ N`, for `z'` with values
in `A` and `z ≡ z'` modulo `ϖᵐ`, up to a fixed power `ϖ^C`. -/
theorem exists_shapZ_sub_shapZ_mem [Finite I] {ϖ : A}
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a) (N : ℕ)
    (z' : I → A) :
    ∃ C : ℕ, ∀ (z : I → k) (m : ℕ),
      (∀ i, ∃ a : A, z i - algebraMap A k (z' i) = algebraMap A k (ϖ ^ m * a)) →
      ∀ x ∈ latN k I A N, ∀ y ∈ latN k I A N, ∃ a : A,
        algebraMap A k (ϖ ^ C) *
          (shapZ D v z x y - shapZ D v (fun i ↦ algebraMap A k (z' i)) x y) =
          algebraMap A k (ϖ ^ m * a) := by
  classical
  have := Fintype.ofFinite I
  have hbd : ∀ T : Module.End k (LusztigF k I), (∀ y, y ∈ fLe k I N → T y ∈ fLe k I N) →
      ∃ c : ℕ, ∀ y ∈ latN k I A N, ϖ ^ c • T y ∈ latN k I A N := by
    intro T hT
    obtain ⟨c, hc⟩ := DualLattice.exists_pow_smul_le hk (Λ := latN k I A N)
      (N := (latN k I A N).map (T.restrictScalars A)) ((latN_fg A N).map _)
      (fun x hx ↦ by
        obtain ⟨y, hy, rfl⟩ := hx
        rw [span_latN]
        exact hT y (by rw [← span_latN A]; exact Submodule.subset_span hy))
    exact ⟨c, fun y hy ↦ hc _ ⟨y, hy, rfl⟩⟩
  choose cL hcL using fun i ↦ hbd (Lop D v i) fun y hy ↦ Lop_mem_fLe i hy
  choose cR hcR using fun i ↦ hbd (Rop D v i) fun y hy ↦ Rop_mem_fLe i hy
  set C₀ := Finset.univ.sup cL ⊔ Finset.univ.sup cR
  have hmono : ∀ (c : ℕ) (T : Module.End k (LusztigF k I)), c ≤ C₀ →
      (∀ y ∈ latN k I A N, ϖ ^ c • T y ∈ latN k I A N) →
      ∀ y ∈ latN k I A N, ϖ ^ C₀ • T y ∈ latN k I A N := by
    intro c T hc hT y hy
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hc
    rw [hd, pow_add, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hT y hy)
  have hL : ∀ i, ∀ y ∈ latN k I A N, ϖ ^ C₀ • Lop D v i y ∈ latN k I A N := fun i ↦
    hmono _ _ ((Finset.le_sup (f := cL) (Finset.mem_univ i)).trans le_sup_left) (hcL i)
  have hR : ∀ i, ∀ y ∈ latN k I A N, ϖ ^ C₀ • Rop D v i y ∈ latN k I A N := fun i ↦
    hmono _ _ ((Finset.le_sup (f := cR) (Finset.mem_univ i)).trans le_sup_right) (hcR i)
  refine ⟨N * C₀, fun z m hz ↦ ?_⟩
  choose b hb using hz
  set z'' : I → k := fun i ↦ algebraMap A k (z' i)
  have hzA : ∀ i, z i = algebraMap A k (z' i) + algebraMap A k (ϖ ^ m * b i) := fun i ↦ by
    rw [← hb i]; ring
  -- the statement on words
  have key : ∀ w : List I, w.length ≤ N → ∀ y ∈ latN k I A N,
      (∃ a : A, (algebraMap A k) (ϖ ^ (w.length * C₀)) * shapZ D v z (wordBasis k I w) y =
        (algebraMap A k) a) ∧
      (∃ a : A, (algebraMap A k) (ϖ ^ (w.length * C₀)) * shapZ D v z'' (wordBasis k I w) y =
        (algebraMap A k) a) ∧
      (∃ a : A, (algebraMap A k) (ϖ ^ (w.length * C₀)) *
        (shapZ D v z (wordBasis k I w) y - shapZ D v z'' (wordBasis k I w) y) =
          (algebraMap A k) (ϖ ^ m * a)) := by
    intro w
    induction w with
    | nil =>
      intro _ y hy
      obtain ⟨a, ha⟩ := counit_mem_range A hy
      refine ⟨⟨a, ?_⟩, ⟨a, ?_⟩, ⟨0, ?_⟩⟩ <;> simp [shapZ_one, ha]
    | cons j w ih =>
      intro hw y hy
      simp only [List.length_cons] at hw
      have hy₁ := hL j y hy
      have hy₂ := hR j y hy
      obtain ⟨⟨a₁, ha₁⟩, ⟨a₁', ha₁'⟩, ⟨d₁, hd₁⟩⟩ := ih (by omega) _ hy₁
      obtain ⟨⟨a₂, ha₂⟩, ⟨a₂', ha₂'⟩, ⟨d₂, hd₂⟩⟩ := ih (by omega) _ hy₂
      simp only [shapZ_smul_right_A] at ha₁ ha₁' ha₂ ha₂' hd₁ hd₂
      have e : ((w.length + 1) * C₀) = w.length * C₀ + C₀ := by ring
      have hlin : ∀ (z₀ : I → k) (c : k) (x : LusztigF k I),
          shapZ D v z₀ x (Lop D v j y - c • Rop D v j y) =
            shapZ D v z₀ x (Lop D v j y) - c * shapZ D v z₀ x (Rop D v j y) := by
        intro z₀ c x; simp [shapZ, map_sub, map_smul]
      rw [← ι_mul_wordBasis, ← θ, shapZ_θ_mul, shapZ_θ_mul, hlin, hlin,
        List.length_cons, e, pow_add, map_mul, hzA j]
      refine ⟨⟨a₁ - (z' j + ϖ ^ m * b j) * a₂, ?_⟩, ⟨a₁' - z' j * a₂', ?_⟩,
        ⟨d₁ - z' j * d₂ - b j * a₂, ?_⟩⟩
      · simp only [map_sub, map_mul, map_add] at ha₁ ha₂ ⊢
        linear_combination ha₁ -
          ((algebraMap A k) (z' j) + (algebraMap A k) (ϖ ^ m) * (algebraMap A k) (b j)) * ha₂
      · simp only [map_sub, map_mul, z''] at ha₁' ha₂' ⊢
        linear_combination ha₁' - (algebraMap A k) (z' j) * ha₂'
      · simp only [map_sub, map_mul, z''] at hd₁ hd₂ ha₂ ⊢
        linear_combination hd₁ - (algebraMap A k) (z' j) * hd₂ -
          (algebraMap A k) (ϖ ^ m) * (algebraMap A k) (b j) * ha₂
  -- extend to the lattice
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨-, -, ⟨a, ha⟩⟩ := key w hw y hy
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.mul_le_mul_right C₀ (show w.length ≤ N from hw))
    refine ⟨ϖ ^ d * a, ?_⟩
    rw [hd, pow_add]
    simp only [map_mul] at ha ⊢
    linear_combination (algebraMap A k (ϖ ^ d)) * ha
  | zero => exact ⟨0, by simp [shapZ]⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hx'
    refine ⟨a + a', ?_⟩
    rw [shapZ_add_left, shapZ_add_left]
    simp only [map_add, map_mul] at ha ha' ⊢
    linear_combination ha + ha'
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨c * a, ?_⟩
    rw [shapZ_smul_left_A, shapZ_smul_left_A]
    simp only [map_mul] at ha ⊢
    linear_combination (algebraMap A k) c * ha

end Estimate

omit [NeZero v] in
lemma shapZ_zero_right (z : I → k) (x : LusztigF k I) : shapZ D v z x 0 = 0 := by
  simpa using shapZ_smul_right (D := D) (v := v) z 0 x 0

omit [NeZero v] in
lemma shapZ_sum_right {ι : Type*} (z : I → k) (x : LusztigF k I) (s : Finset ι)
    (f : ι → LusztigF k I) : shapZ D v z x (∑ n ∈ s, f n) = ∑ n ∈ s, shapZ D v z x (f n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [shapZ_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, shapZ_add_right, ih]

end VermaModule

namespace GrandLoop

open VermaModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### The component `y⁰` of `y` in `ker e''ᵢ` -/

variable (hvt) in
/-- `y⁰ = ((y*)₀)*`, the component in `ker e''ᵢ` (`e''ᵢ = * e'ᵢ *`) of the decomposition
`y = Σₙ yₙ fᵢ^{(n)}`, `e''ᵢ yₙ = 0`. -/
def comp0 (i : I) : Module.End k (Um D v) := starU D v ∘ₗ comp hvt i 0 ∘ₗ starU D v

lemma comp0_apply (i : I) (y : Um D v) :
    comp0 hvt i y = starU D v (comp hvt i 0 (starU D v y)) := rfl

/-- `P⁰ = P` if `e''ᵢ P = 0`. -/
lemma comp0_of_e_starU (i : I) {P : Um D v}
    (hP : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0) :
    comp0 hvt i P = P := by
  have := BosonModule.component_df (NegativePart.pow_d_ne_zero (D := D) (NeZero.ne v) i)
    (NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i) hP 0 0
  simp only [BosonModule.df_zero, ↓reduceIte] at this
  rw [comp0_apply, this, starU_starU]

omit [CharZero k] [DecidableEq I] [NeZero v] in
lemma f_pow_mk (i : I) (n : ℕ) (c : LusztigF k I) :
    (NegativePart.f D v i ^ n) (Submodule.Quotient.mk c : Um D v) =
      Submodule.Quotient.mk (θ k i ^ n * c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, NegativePart.f_mk, pow_succ', mul_assoc]

/-- **`G_{zᵂ}(x, y) = (x, y⁰)`** for all `x, y ∈ 'f`. -/
theorem shapZ_zWall_eq_formU (i : I) (x y : LusztigF k I) :
    shapZ D v (zWall i) x y = formU (pow_ne_one_of_transcendental' hvt)
      (Submodule.Quotient.mk x : Um D v) (comp0 hvt i (Submodule.Quotient.mk y)) := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  set u : Um D v := starU D v (Submodule.Quotient.mk y)
  obtain ⟨N, hN, -⟩ := exists_sum_comp (hvt := hvt) i u
  have hu := eq_sum_comp (hvt := hvt) i u (N := N + 1) (fun n hn ↦ hN n (by omega))
  choose c hc using fun n ↦ Submodule.Quotient.mk_surjective (serreSubmodule D v) (comp hvt i n u)
  set y' : LusztigF k I := ∑ n ∈ range (N + 1),
    (qFactorial (v ^ D.d i)⁻¹ n)⁻¹ • (rev k I (c n) * θ k i ^ n)
  have hy' : (Submodule.Quotient.mk y' : Um D v) = Submodule.Quotient.mk y := by
    have h2 := congrArg (starU D v) hu
    rw [starU_starU] at h2
    rw [h2, map_sum, show (Submodule.Quotient.mk y' : Um D v) = Submodule.mkQ _ y' from rfl,
      map_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [map_smul, Submodule.mkQ_apply]
    rw [BosonModule.df_apply, map_smul, ← hc n]
    change _ = (qFactorial (v ^ D.d i)⁻¹ n)⁻¹ •
      starU D v ((NegativePart.f D v i ^ n) (Submodule.Quotient.mk (c n)))
    have hpow : ∀ m : ℕ, rev k I (θ k i ^ m) = θ k i ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, rev_mul, ih, rev_θ, ← pow_succ', pow_succ]
    rw [f_pow_mk, starU_mk, rev_mul, hpow]
  have hJ : y - y' ∈ serreIdeal D v := by
    rw [← mem_serreSubmodule, ← Submodule.Quotient.eq, hy']
  have e1 : shapZ D v (zWall i) x y = shapZ D v (zWall i) x y' := by
    have h := shapZ_eq_zero_of_mem (z := zWall i) hv' x hJ
    rw [show y = y' + (y - y') by abel, shapZ_add_right, h, add_zero]
  rw [e1, shapZ_sum_right, Finset.sum_eq_single 0]
  · simp only [qFactorial, pow_zero, mul_one, inv_one, one_smul]
    rw [shapZ_zWall_eq_form hv' i]
    · rw [comp0_apply, ← hc 0, starU_mk]
      rfl
    · rw [rDeriv_rev]
      refine rev_mem_serreIdeal D v ?_
      have h := e_comp (hvt := hvt) i 0 u
      rw [← hc 0] at h
      have h' : (Submodule.Quotient.mk (lDeriv D v i (c 0)) : Um D v) = 0 := h
      exact mem_serreSubmodule.1 ((Submodule.Quotient.mk_eq_zero _).1 h')
  · intro n _ hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [shapZ_smul_right, pow_succ, ← mul_assoc, shapZ_mul_θ_eq_zero (zWall_self i), mul_zero]
  · intro h; simp at h

/-! ### The forms of `V(λ)` at a wall -/

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
lemma comp0_mem_latInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) {y : Um D v}
    (hy : y ∈ latInf hvt A) : comp0 hvt i y ∈ latInf hvt A :=
  starU_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund (comp_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund
    i 0 (starU_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund hy))

omit hinj hϖ hϖv hfund [IsDomain A] [IsDiscreteValuationRing A] in
/-- `ϖ^c (L(∞) ∩ U⁻_{-ν})` lifts to the words of length `≤ |ν|`. -/
lemma exists_pow_smul_eq_mk (ν : I →₀ ℕ) :
    ∃ c : ℕ, ∀ x ∈ latInf hvt A, x ∈ Uw D v ν →
      ∃ P ∈ latN k I A ν.degree, ϖ ^ c • x = Submodule.Quotient.mk P := by
  classical
  set Λm : Submodule A (Um D v) := (mon D v A ν).map ((Uw D v ν).subtype.restrictScalars A)
  set N : Submodule A (Um D v) := Submodule.span A (fWi (D := D) hvt '' {w | wordWeight w = ν})
  have hNfg : N.FG := Submodule.fg_span ((finite_words ν).image _)
  have hsp : ∀ u : Uw D v ν, (u : Um D v) ∈ Submodule.span k (Λm : Set (Um D v)) := by
    intro u
    have hu : u ∈ Submodule.span k (mon D v A ν : Set (Uw D v ν)) := by rw [span_mon]; trivial
    have h := Submodule.mem_map_of_mem (f := (Uw D v ν).subtype) hu
    rw [← Submodule.span_image] at h
    convert h using 3 <;> rfl
  have hNs : ∀ x ∈ N, x ∈ Submodule.span k (Λm : Set (Um D v)) := by
    intro x hx
    refine (Submodule.span_le (p := (Submodule.span k (Λm : Set (Um D v))).restrictScalars A)).2
      ?_ hx
    rintro _ ⟨w, hw, rfl⟩
    exact hsp ⟨_, hw ▸ fWi_mem_Uw (hvt := hvt) w⟩
  obtain ⟨c, hc⟩ := DualLattice.exists_pow_smul_le hk hNfg hNs
  refine ⟨c, fun x hx hxw ↦ ?_⟩
  obtain ⟨m, hm, e⟩ := hc x (mem_span_fWi_of_mem hx hxw)
  obtain ⟨P, hP, e'⟩ := exists_latN_of_mem_mon (le_refl ν.degree) hm
  exact ⟨P, hP, by rw [← e, ← e']; rfl⟩

omit hinj hϖ hfund [IsDomain A] [IsDiscreteValuationRing A] in
include hR in
/-- **The forms of `V(λ)` at a wall**: if `⟨i, λ⟩ = 0` and `⟨j, λ⟩ ≫ 0` for `j ≠ i`, then
`(π_λ x, π_λ y)_λ ≡ (x, y⁰)` modulo `ϖ` for `x, y ∈ L(∞) ∩ U⁻_{-ν}`. -/
theorem exists_form_evq_sub_formU (i : I) (ν : I →₀ ℕ) :
    ∃ m₀ : ℕ, ∀ Λ : Dom R, Λ.1 (R.coroot i) = 0 → (∀ j, j ≠ i → (m₀ : ℤ) ≤ Λ.1 (R.coroot j)) →
      ∀ x ∈ latInf hvt A, x ∈ Uw D v ν → ∀ y ∈ latInf hvt A, y ∈ Uw D v ν →
        ∃ a : A, IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt)
          (evq hvt Λ x) (evq hvt Λ y) -
            formU (pow_ne_one_of_transcendental' hvt) x (comp0 hvt i y) =
              algebraMap A k (ϖ * a) := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨c, hc⟩ := exists_pow_smul_eq_mk (hvt := hvt) hk ν
  obtain ⟨C, hC⟩ := exists_shapZ_sub_shapZ_mem (D := D) (v := v) A hk ν.degree
    (fun j ↦ if j = i then 1 else 0)
  refine ⟨C + 2 * c + 1, fun Λ hΛi hΛ x hx hxw y hy hyw ↦ ?_⟩
  set m₀ := C + 2 * c + 1
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨P, hP, eP⟩ := hc x hx hxw
  obtain ⟨Q, hQ, eQ⟩ := hc y hy hyw
  have hz : ∀ j, ∃ a : A, zcoef R v Λ.1 j -
      algebraMap A k (if j = i then 1 else 0) = algebraMap A k (ϖ ^ m₀ * a) := by
    intro j
    by_cases h : j = i
    · subst h
      refine ⟨0, ?_⟩
      simp [zcoef, hΛi]
    · rw [zcoef_eq hϖv Λ.1 j (Λ.2 j)]
      simp only [h, ↓reduceIte, map_zero, sub_zero]
      have h1 := hΛ j h
      have h2 := D.d_pos j
      obtain ⟨d, hd⟩ : ∃ d, 2 * D.d j * (Λ.1 (R.coroot j)).toNat = m₀ + d := by
        refine ⟨2 * D.d j * (Λ.1 (R.coroot j)).toNat - m₀, ?_⟩
        have : (m₀ : ℤ) ≤ ((Λ.1 (R.coroot j)).toNat : ℤ) := by
          rw [Int.toNat_of_nonneg (Λ.2 j)]; exact h1
        have h3 : m₀ ≤ (Λ.1 (R.coroot j)).toNat := by exact_mod_cast this
        have h4 : (Λ.1 (R.coroot j)).toNat ≤ 2 * D.d j * (Λ.1 (R.coroot j)).toNat := by
          nlinarith
        omega
      exact ⟨ϖ ^ d, by rw [hd, pow_add]⟩
  obtain ⟨a, ha⟩ := hC (zcoef R v Λ.1) m₀ hz P hP Q hQ
  have hzW : (fun j ↦ algebraMap A k (if j = i then (1 : A) else 0)) = zWall (k := k) i := by
    funext j; by_cases h : j = i <;> simp [zWall, h]
  rw [hzW, ← shapF_eq_shapZ R hv', shapF_apply, shapZ_zWall_eq_formU (hvt := hvt)] at ha
  have e1 : IrreducibleModule.form Λ.1 hR hv' (Submodule.Quotient.mk (toVerma R v Λ.1 P))
      (Submodule.Quotient.mk (toVerma R v Λ.1 Q)) =
      algebraMap A k (ϖ ^ c) * algebraMap A k (ϖ ^ c) *
        IrreducibleModule.form Λ.1 hR hv' (evq hvt Λ x) (evq hvt Λ y) := by
    have hx' : (Submodule.Quotient.mk (toVerma R v Λ.1 P) : IrreducibleModule R v Λ.1) =
        algebraMap A k (ϖ ^ c) • evq hvt Λ x := by
      rw [← map_smul, algebraMap_smul, eP]; rfl
    have hy' : (Submodule.Quotient.mk (toVerma R v Λ.1 Q) : IrreducibleModule R v Λ.1) =
        algebraMap A k (ϖ ^ c) • evq hvt Λ y := by
      rw [← map_smul, algebraMap_smul, eQ]; rfl
    rw [hx', hy']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  have e2 : formU hv' (Submodule.Quotient.mk P : Um D v)
      (comp0 hvt i (Submodule.Quotient.mk Q)) =
      algebraMap A k (ϖ ^ c) * algebraMap A k (ϖ ^ c) * formU hv' x (comp0 hvt i y) := by
    rw [← eP, ← eQ, ← algebraMap_smul k, ← algebraMap_smul k (ϖ ^ c) y, map_smul, map_smul,
      LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]; ring
  rw [← IrreducibleModule.form_mk hR, e1, e2] at ha
  refine ⟨a, ?_⟩
  have hne : algebraMap A k (ϖ ^ (C + 2 * c)) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hϖ0
  apply mul_left_cancel₀ hne
  have em : m₀ = C + 2 * c + 1 := rfl
  rw [em, pow_succ, show C + 2 * c = C + c + c by ring] at ha
  rw [show C + 2 * c = C + c + c by ring]
  simp only [pow_add, map_mul] at ha ⊢
  linear_combination ha

include hR in
/-- **Nonvanishing at a wall**: if `⟨i, λ⟩ = 0` and `⟨j, λ⟩ ≫ 0` for `j ≠ i`, then for
`P ∈ L(∞) ∩ U⁻_{-ν}` with `e''ᵢ P = 0` and `P ∉ ϖ L(∞)`, `π_λ(P) ∉ ϖ L(λ)`. This replaces the
use of global bases ([Kas91] Thm. 7) in [Kas93a] Prop. 2.1.2. -/
theorem evq_notMem_smul_lat [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (i : I) (ν : I →₀ ℕ) :
    ∃ m₀ : ℕ, ∀ Λ : Dom R, Λ.1 (R.coroot i) = 0 → (∀ j, j ≠ i → (m₀ : ℤ) ≤ Λ.1 (R.coroot j)) →
      ∀ P ∈ latInf hvt A, P ∈ Uw D v ν →
        (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0 →
        P ∉ ϖ • latInf hvt A → evq hvt Λ P ∉ ϖ • lat hvt hR A Λ := by
  obtain ⟨m₀, hm₀⟩ := exists_form_evq_sub_formU (hR := hR) hϖv hk i ν
  refine ⟨m₀, fun Λ hΛi hΛ P hP hPw he hPS hS ↦ hPS ?_⟩
  set hv' := pow_ne_one_of_transcendental' hvt
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨z, hz, ez⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hS
  have hzw : z ∈ wsp Λ ν := by
    have h := evq_mem_wsp (hvt := hvt) hR hPw Λ
    rw [← ez, ← algebraMap_smul k] at h
    have := Submodule.smul_mem _ (algebraMap A k ϖ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hϖ0, one_smul] at this
  obtain ⟨R', hR'L, hR'w, eR'⟩ := exists_evq_eq (hR := hR) hinj hϖ hϖv hk hfund hz hzw
  obtain ⟨a₁, ha₁⟩ := hm₀ Λ hΛi hΛ P hP hPw P hP hPw
  obtain ⟨a₂, ha₂⟩ := hm₀ Λ hΛi hΛ R' hR'L hR'w R' hR'L hR'w
  obtain ⟨b, hb⟩ := formU_mem (hR := hR) hinj hϖ hϖv hk hfund hR'L
    (comp0_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund i hR'L)
  rw [comp0_of_e_starU i he] at ha₁
  have hPe : evq hvt Λ P = algebraMap A k ϖ • evq hvt Λ R' := by
    rw [eR', ← ez, algebraMap_smul]
  rw [hPe] at ha₁
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at ha₁
  refine mem_smul_latInf_of_formU_mem (hR := hR) hinj hϖ hϖv hk hfund hP
    (b₀ := ϖ * (ϖ * a₂ + b) - a₁) ?_
  have h2 : IrreducibleModule.form Λ.1 hR hv' (evq hvt Λ R') (evq hvt Λ R') =
      algebraMap A k (ϖ * a₂) + algebraMap A k b := by rw [← hb, ← ha₂]; ring
  rw [h2] at ha₁
  simp only [map_mul, map_sub, map_add] at ha₁ ⊢
  linear_combination -ha₁

end Base

end GrandLoop

end LieLean.QuantumGroup
