/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ContravariantForm
import LieLean.Algebra.QuantumGroup.GabberKac.Quantum
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Verma
import LieLean.Algebra.QuantumGroup.CrystalBasis.DualLattice

/-!
# The Shapovalov forms on `'f` and their limit

For `Λ : Y →+ ℤ` let `G_Λ(x, y) = (x⁻ v_Λ, y⁻ v_Λ)` be the Shapovalov form of `M_q(Λ)` pulled back
to `'f` (`QuantumGroup.VermaModule.shapF`). With the operators `Lᵢ = (θᵢ, θᵢ) ᵢr` and
`Rᵢ = vᵢ (vᵢ - vᵢ⁻¹)⁻¹ σᵢ ∘ rᵢ` on `'f` we show

`G_Λ(θᵢ x, y) = G_Λ(x, Lᵢ y - zᵢ Rᵢ y)`, `zᵢ = vᵢ^{-2⟨i, Λ⟩}`
(`QuantumGroup.VermaModule.shapF_θ_mul`),

so `G_Λ` is the member `z = (vᵢ^{-2⟨i,Λ⟩})ᵢ` of the family of forms `G_z(x, y) = ε(T_z(x) y)`,
`T_z(θᵢ) = Lᵢ - zᵢ Rᵢ` (`QuantumGroup.VermaModule.shapF_eq_shapZ`), and the member `z = 0` is
Lusztig's form `( , )` on `'f` (`QuantumGroup.VermaModule.form_eq_shapZ_zero`; [Lus] 1.2.13 (a)).
Hence `G_Λ → ( , )` as `⟨i, Λ⟩ → ∞` (in the `v⁻¹`-adic sense), which is how the Shapovalov forms
of `L_q(Λ)` for large `Λ` are compared in Kashiwara's grand loop. The computation is ours.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.13, 3.1.6.
-/

open LieLean LusztigF FreeAlgebra

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]

omit [DecidableEq I] [NeZero v] in
lemma rootSum_ktilde (ν : I →₀ ℕ) (i : I) :
    R.rootSum ν (ktilde R i) = D.weightDot (Finsupp.single i 1) ν := by
  rw [LusztigCartanDatum.weightDot, Finsupp.sum_single_index (by simp)]
  simp only [LusztigCartanDatum.RootDatum.rootSum, Finsupp.sum, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.nsmul_apply, root_ktilde_eq_dot, nsmul_eq_mul, Nat.cast_one, one_mul]

namespace VermaModule

variable (R) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (Λ : Y →+ ℤ)

/-- The Shapovalov form of `M_q(Λ)` pulled back to `'f`. -/
def shapF : LinearMap.BilinForm k (LusztigF k I) :=
  (shapForm Λ hv').compl₁₂ (toVerma R v Λ) (toVerma R v Λ)

lemma shapF_apply (x y : LusztigF k I) :
    shapF R hv' Λ x y = shapForm Λ hv' (toVerma R v Λ x) (toVerma R v Λ y) := rfl

lemma shapF_one_left (y : LusztigF k I) : shapF R hv' Λ 1 y = LusztigF.counit y := by
  rw [shapF_apply, toVerma_one, ← one_smul (QuantumGroup R v) (hwv R v Λ), shapForm_smul_hwv,
    rho_one, one_smul, hwCoord_toVerma]

/-- `K_{-k̃ᵢ} (y⁻ v_Λ) = vᵢ^{-⟨i,Λ⟩} (σᵢ y)⁻ v_Λ`. -/
lemma K_neg_ktilde_smul_toVerma (i : I) (z : LusztigF k I) :
    K R v (-ktilde R i) • toVerma R v Λ z =
      (v ^ D.d i) ^ (-Λ (R.coroot i)) • toVerma R v Λ (twist D v i z) := by
  induction z using induction_wordBasis with
  | zero => simp
  | add a b ha hb => rw [map_add, smul_add, ha, hb, map_add, map_add, smul_add]
  | smul c a ha => rw [map_smul, smul_comm, ha, map_smul, map_smul, smul_comm]
  | word w =>
    have hw : wordBasis k I w ∈ LusztigF.weightSpace k (wordWeight w) :=
      wordBasis_mem_wordSpan w
    have h1 := (toVerma_mem_weightSpace (R := R) (v := v) (Λ := Λ) hw) (-ktilde R i)
    rw [h1, twist_of_mem (NeZero.ne v) i hw, map_smul, smul_smul, ← rootSum_ktilde (R := R)]
    congr 1
    rw [AddMonoidHom.sub_apply, map_neg, map_neg, ktilde, map_nsmul, nsmul_eq_mul, ← zpow_natCast,
      ← zpow_mul, ← zpow_add₀ (NeZero.ne v)]
    congr 1
    ring

variable (D v) in
/-- `Lᵢ = (θᵢ, θᵢ) ᵢr`. -/
def Lop (i : I) : Module.End k (LusztigF k I) := thetaNorm D v i • lDeriv D v i

variable (D v) in
/-- `Rᵢ = vᵢ (vᵢ - vᵢ⁻¹)⁻¹ σᵢ ∘ rᵢ`. -/
def Rop (i : I) : Module.End k (LusztigF k I) :=
  (v ^ D.d i * (LusztigF.qDenom D v i)⁻¹) • ((twist D v i).toLinearMap ∘ₗ rDeriv D v i)

variable (v) in
/-- `zᵢ = vᵢ^{-2⟨i,Λ⟩}`. -/
def zcoef (i : I) : k := (v ^ D.d i) ^ (-2 * Λ (R.coroot i))

omit [DecidableEq I] in
lemma twist_twist_inv (i : I) (z : LusztigF k I) : twist D v i (twist D v⁻¹ i z) = z := by
  have : (twist D v i).comp (twist D v⁻¹ i) = AlgHom.id k (LusztigF k I) := by
    refine FreeAlgebra.hom_ext (funext fun j ↦ ?_)
    simp only [AlgHom.comp_apply, Function.comp_apply, AlgHom.id_apply]
    rw [twist_θ, map_smul, twist_θ, smul_smul, inv_zpow', ← zpow_add₀ (NeZero.ne v),
      neg_add_cancel, zpow_zero, one_smul]
  exact congrArg (fun f ↦ f z) this

omit [DecidableEq I] in
lemma thetaNorm_eq (i : I) :
    thetaNorm D v i = v ^ D.d i * (LusztigF.qDenom D v i)⁻¹ := by
  have h0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  unfold thetaNorm LusztigF.qDenom
  rw [← inv_inv (v ^ D.d i * _), mul_inv, inv_inv]
  congr 1
  field_simp

/-- **The recursion for the Shapovalov form** on `'f`:
`G_Λ(θᵢ x, y) = G_Λ(x, Lᵢ y - zᵢ Rᵢ y)`. -/
theorem shapF_θ_mul [CharZero k] (i : I) (x y : LusztigF k I) :
    shapF R hv' Λ (θ k i * x) y =
      shapF R hv' Λ x (Lop D v i y - zcoef R v Λ i • Rop D v i y) := by
  have hq : LusztigF.qDenom D v i ≠ 0 := LieLean.QuantumGroup.qDenom_ne_zero (NeZero.ne v) hv' i
  have h0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  rw [shapF_apply, shapF_apply, toVerma_ι_mul, isContravariant_shapForm hv', rho_F, rhoF,
    smul_assoc, mul_smul, E_smul_toVerma hv']
  have hE : vermaOp i (qCoeff R v Λ i) = vermaOpQ D v (fun j ↦ Λ (R.coroot j)) i :=
    (vermaOpQ_eq_vermaOp D (NeZero.ne v) _ hq).symm
  rw [hE, K_neg_ktilde_smul_toVerma, smul_smul, ← map_smul]
  congr 2
  rw [vermaOpQ_apply, map_smul, map_sub, map_smul, map_smul, twist_twist_inv, Lop, Rop, zcoef,
    thetaNorm_eq]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, smul_sub,
    smul_smul]
  have hn : (v ^ D.d i) ^ Λ (R.coroot i) ≠ 0 := zpow_ne_zero _ h0
  congr 1
  · congr 1
    rw [zpow_neg]; field_simp
  · congr 1
    rw [show -2 * Λ (R.coroot i) = -Λ (R.coroot i) + -Λ (R.coroot i) by ring, zpow_add₀ h0,
      zpow_neg]
    field_simp

/-! ### The family `G_z` -/

variable (D v) in
/-- `θᵢ ↦ Lᵢ - zᵢ Rᵢ`, as an algebra map into `End('f)ᵐᵒᵖ`. -/
def opZ (z : I → k) : LusztigF k I →ₐ[k] (Module.End k (LusztigF k I))ᵐᵒᵖ :=
  FreeAlgebra.lift k fun i ↦ MulOpposite.op (Lop D v i - z i • Rop D v i)

variable (D v) in
/-- `G_z(x, y) = ε(T_z(x) y)`. -/
def shapZ (z : I → k) (x y : LusztigF k I) : k := LusztigF.counit ((opZ D v z x).unop y)

omit [NeZero v] in
lemma shapZ_one (z : I → k) (y : LusztigF k I) : shapZ D v z 1 y = LusztigF.counit y := by
  simp [shapZ]

omit [NeZero v] in
lemma shapZ_θ_mul (z : I → k) (i : I) (x y : LusztigF k I) :
    shapZ D v z (θ k i * x) y = shapZ D v z x (Lop D v i y - z i • Rop D v i y) := by
  simp [shapZ, opZ, θ, map_mul, MulOpposite.unop_mul]

omit [NeZero v] in
lemma shapZ_add_left (z : I → k) (x x' y : LusztigF k I) :
    shapZ D v z (x + x') y = shapZ D v z x y + shapZ D v z x' y := by
  simp [shapZ, map_add]

omit [NeZero v] in
lemma shapZ_smul_left (z : I → k) (c : k) (x y : LusztigF k I) :
    shapZ D v z (c • x) y = c * shapZ D v z x y := by
  simp [shapZ, map_smul]

omit [NeZero v] in
lemma shapZ_add_right (z : I → k) (x y y' : LusztigF k I) :
    shapZ D v z x (y + y') = shapZ D v z x y + shapZ D v z x y' := by
  simp [shapZ, map_add]

omit [NeZero v] in
lemma shapZ_smul_right (z : I → k) (c : k) (x y : LusztigF k I) :
    shapZ D v z x (c • y) = c * shapZ D v z x y := by
  simp [shapZ, map_smul]

/-- `G_Λ = G_z` for `zᵢ = vᵢ^{-2⟨i,Λ⟩}`. -/
theorem shapF_eq_shapZ [CharZero k] (x y : LusztigF k I) :
    shapF R hv' Λ x y = shapZ D v (zcoef R v Λ) x y := by
  induction x using induction_wordBasis generalizing y with
  | zero => simp [shapZ]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, shapZ_add_left]
  | smul c a ha => rw [map_smul, LinearMap.smul_apply, ha, shapZ_smul_left, smul_eq_mul]
  | word w =>
    induction w generalizing y with
    | nil => rw [wordBasis_nil, shapF_one_left, shapZ_one]
    | cons j w ih => rw [← ι_mul_wordBasis, ← θ, shapF_θ_mul, ih, shapZ_θ_mul]

omit [NeZero v] in
/-- Lusztig's form is `G_0` ([Lus] 1.2.13 (a)). -/
theorem form_eq_shapZ_zero (x y : LusztigF k I) : LusztigF.form D v x y = shapZ D v 0 x y := by
  induction x using induction_wordBasis generalizing y with
  | zero => simp [shapZ]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, shapZ_add_left]
  | smul c a ha => rw [map_smul, LinearMap.smul_apply, ha, shapZ_smul_left, smul_eq_mul]
  | word w =>
    induction w generalizing y with
    | nil => rw [wordBasis_nil, form_one_left, shapZ_one]
    | cons j w ih =>
      rw [← ι_mul_wordBasis, ← θ, form_θ_mul, shapZ_θ_mul, Pi.zero_apply, zero_smul, sub_zero,
        Lop, LinearMap.smul_apply, ← ih, map_smul, smul_eq_mul]

/-! ### Degree bounds -/

variable (k I) in
/-- `'f_{≤N}`: the span of the words of length `≤ N`. -/
def fLe (N : ℕ) : Submodule k (LusztigF k I) :=
  Submodule.span k (wordBasis k I '' {w | w.length ≤ N})

omit [DecidableEq I] [NeZero v] in
lemma wordBasis_mem_fLe {N : ℕ} {w : List I} (hw : w.length ≤ N) : wordBasis k I w ∈ fLe k I N :=
  Submodule.subset_span ⟨w, hw, rfl⟩

omit [DecidableEq I] [NeZero v] in
lemma fLe_mono {N N' : ℕ} (h : N ≤ N') : fLe k I N ≤ fLe k I N' :=
  Submodule.span_mono (Set.image_mono fun _ hw ↦ le_trans hw h)

omit [DecidableEq I] [NeZero v] in
lemma twist_wordBasis_mem (i : I) (hv : v ≠ 0) {N : ℕ} {w : List I} (hw : w.length ≤ N) :
    twist D v i (wordBasis k I w) ∈ fLe k I N := by
  rw [twist_of_mem hv i (wordBasis_mem_wordSpan w)]
  exact Submodule.smul_mem _ _ (wordBasis_mem_fLe hw)

omit [DecidableEq I] [NeZero v] in
lemma θ_mul_mem_fLe (j : I) {N : ℕ} {z : LusztigF k I} (hz : z ∈ fLe k I N) :
    θ k j * z ∈ fLe k I (N + 1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, rfl⟩ := hz
    rw [θ, ι_mul_wordBasis]
    exact wordBasis_mem_fLe (by simp at hu ⊢; omega)
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha

omit [NeZero v] in
lemma lDeriv_wordBasis_mem (i : I) (w : List I) {N : ℕ} (hw : w.length ≤ N) :
    lDeriv D v i (wordBasis k I w) ∈ fLe k I N := by
  induction w generalizing N with
  | nil => simp
  | cons j w ih =>
    simp only [List.length_cons] at hw
    rw [← ι_mul_wordBasis, ← θ, lDeriv_θ_mul]
    refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
    · split_ifs
      · exact wordBasis_mem_fLe (by omega)
      · exact zero_mem _
    · have h := θ_mul_mem_fLe j (ih (N := N - 1) (by omega))
      rwa [Nat.sub_add_cancel (by omega)] at h

omit [NeZero v] in
lemma rDeriv_wordBasis_mem (i : I) (hv : v ≠ 0) (w : List I) {N : ℕ} (hw : w.length ≤ N) :
    rDeriv D v i (wordBasis k I w) ∈ fLe k I N := by
  induction w generalizing N with
  | nil => simp
  | cons j w ih =>
    simp only [List.length_cons] at hw
    rw [← ι_mul_wordBasis, ← θ, rDeriv_θ_mul]
    refine add_mem ?_ ?_
    · have h := θ_mul_mem_fLe j (ih (N := N - 1) (by omega))
      rwa [Nat.sub_add_cancel (by omega)] at h
    · split_ifs
      · exact twist_wordBasis_mem i hv (by omega)
      · exact zero_mem _

omit [DecidableEq I] [NeZero v] in
lemma map_fLe {T : Module.End k (LusztigF k I)} (hT : ∀ (w : List I) (N : ℕ), w.length ≤ N →
      T (wordBasis k I w) ∈ fLe k I N) {N : ℕ} {y : LusztigF k I} (hy : y ∈ fLe k I N) :
    T y ∈ fLe k I N := by
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨u, hu, rfl⟩ := hz; exact hT u N hu
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

omit [NeZero v] in
lemma Lop_mem_fLe (i : I) {N : ℕ} {y : LusztigF k I} (hy : y ∈ fLe k I N) :
    Lop D v i y ∈ fLe k I N :=
  map_fLe (fun w _ hw ↦ Submodule.smul_mem _ _ (lDeriv_wordBasis_mem i w hw)) hy

lemma Rop_mem_fLe (i : I) {N : ℕ} {y : LusztigF k I} (hy : y ∈ fLe k I N) :
    Rop D v i y ∈ fLe k I N := by
  refine map_fLe (fun w _ hw ↦ Submodule.smul_mem _ _ ?_) hy
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  exact map_fLe (T := (twist D v i).toLinearMap)
    (fun u _ hu ↦ twist_wordBasis_mem i (NeZero.ne v) hu)
    (rDeriv_wordBasis_mem i (NeZero.ne v) w hw)

/-! ### The estimate `G_z ≡ G_0 (mod zᵢ)` -/

section Estimate

variable (A : Type*) [CommRing A] [Algebra A k]

variable (k I) in
/-- The `A`-span of the words of length `≤ N`. -/
def latN (N : ℕ) : Submodule A (LusztigF k I) :=
  Submodule.span A (wordBasis k I '' {w | w.length ≤ N})

omit [DecidableEq I] [NeZero v] in
lemma span_latN (N : ℕ) : Submodule.span k (latN k I A N : Set (LusztigF k I)) = fLe k I N := by
  rw [latN, Submodule.span_span_of_tower]
  rfl

omit [DecidableEq I] [NeZero v] in
lemma latN_fg [Finite I] (N : ℕ) : (latN k I A N).FG := by
  refine ⟨((List.finite_length_le I N).image (wordBasis k I)).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  rfl

omit [DecidableEq I] [NeZero v] in
lemma counit_mem_range {N : ℕ} {y : LusztigF k I} (hy : y ∈ latN k I A N) :
    LusztigF.counit y ∈ (algebraMap A k).range := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, -, rfl⟩ := hy
    rcases w with _ | ⟨j, w⟩
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩
  | smul c a _ ha =>
    obtain ⟨x, hx⟩ := ha
    exact ⟨c * x, by rw [← algebraMap_smul k c a, map_smul, ← hx, smul_eq_mul, map_mul]⟩

omit [NeZero v] in
lemma shapZ_smul_left_A (z : I → k) (c : A) (x y : LusztigF k I) :
    shapZ D v z (c • x) y = algebraMap A k c * shapZ D v z x y := by
  rw [← algebraMap_smul k c x, shapZ_smul_left]

omit [NeZero v] in
lemma shapZ_smul_right_A (z : I → k) (c : A) (x y : LusztigF k I) :
    shapZ D v z x (c • y) = algebraMap A k c * shapZ D v z x y := by
  rw [← algebraMap_smul k c y, shapZ_smul_right]

/-- **`G_z ≡ G_0` modulo `zᵢ`**: on the lattice of words of length `≤ N` there is a constant `C`
with `ϖ^C (G_z - G_0) ∈ ϖ^m A` whenever all `zᵢ ∈ ϖ^m A` (`k = A[ϖ⁻¹]`). -/
theorem exists_shapZ_sub_mem [Finite I] {ϖ : A}
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a) (N : ℕ) :
    ∃ C : ℕ, ∀ (z : I → k) (m : ℕ), (∀ i, ∃ a : A, z i = algebraMap A k (ϖ ^ m * a)) →
      ∀ x ∈ latN k I A N, ∀ y ∈ latN k I A N, ∃ a : A,
        algebraMap A k (ϖ ^ C) * (shapZ D v z x y - shapZ D v 0 x y) =
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
  have hzA : ∀ i, z i = algebraMap A k (ϖ ^ m * b i) := hb
  -- the statement on words
  have key : ∀ w : List I, w.length ≤ N → ∀ y ∈ latN k I A N,
      (∃ a : A, (algebraMap A k) (ϖ ^ (w.length * C₀)) * shapZ D v z (wordBasis k I w) y =
        (algebraMap A k) a) ∧
      (∃ a : A, (algebraMap A k) (ϖ ^ (w.length * C₀)) * shapZ D v 0 (wordBasis k I w) y =
        (algebraMap A k) a) ∧
      (∃ a : A, (algebraMap A k) (ϖ ^ (w.length * C₀)) *
        (shapZ D v z (wordBasis k I w) y - shapZ D v 0 (wordBasis k I w) y) =
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
      simp only [shapZ_smul_right_A] at ha₁ ha₁' ha₂ ha₂' hd₁
      have e : ((w.length + 1) * C₀) = w.length * C₀ + C₀ := by ring
      have hlin : ∀ (z' : I → k) (c : k) (x : LusztigF k I),
          shapZ D v z' x (Lop D v j y - c • Rop D v j y) =
            shapZ D v z' x (Lop D v j y) - c * shapZ D v z' x (Rop D v j y) := by
        intro z' c x; simp [shapZ, map_sub, map_smul]
      rw [← ι_mul_wordBasis, ← θ, shapZ_θ_mul, shapZ_θ_mul, hlin, hlin, Pi.zero_apply,
        List.length_cons, e, pow_add, map_mul, hzA j]
      simp only [map_mul, zero_mul, sub_zero]
      refine ⟨⟨a₁ - ϖ ^ m * b j * a₂, ?_⟩, ⟨a₁', ?_⟩, ⟨d₁ - b j * a₂, ?_⟩⟩
      · simp only [map_sub, map_mul]
        linear_combination ha₁ - (algebraMap A k) (ϖ ^ m) * (algebraMap A k) (b j) * ha₂
      · linear_combination ha₁'
      · simp only [map_sub, map_mul] at hd₁ ⊢
        linear_combination hd₁ - (algebraMap A k) (ϖ ^ m) * (algebraMap A k) (b j) * ha₂
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

end VermaModule

end LieLean.QuantumGroup

end
