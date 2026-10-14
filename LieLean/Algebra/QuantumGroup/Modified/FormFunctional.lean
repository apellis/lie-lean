/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.LeftModule
import LieLean.Algebra.QuantumGroup.RhoBar
import LieLean.Algebra.QuantumGroup.LusztigF.Reverse
import LieLean.Algebra.QuantumGroup.GabberKac.VermaOperator
import LieLean.Algebra.QuantumGroup.TriangularDecomposition
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreNegative

/-!
# The functionals `z ↦ (1_ζ, z 1_ζ)` on `U`

The form `(,)` on `U̇` of [Lus] 26.1.2 is determined by the values `(1_ζ, z 1_ζ)`, `z ∈ U`,
`ζ ∈ X`, and properties (b), (c) of 26.1.2 force
`(1_ζ, ρ̄(x⁻) y⁻ K_μ 1_ζ) = v^{⟨μ,ζ⟩} (x, y)` for `x, y ∈ 'f`. We construct, for each `ζ`, the
linear functional `P_ζ : U → k` with these values, using the triangular decomposition
`U ≅ 'f/J ⊗ k[Y] ⊗ 'f/J` (`triangularEquiv`) and the Chevalley involution to write `U` as
`U⁺ U⁰ U⁻`. In this ordering
`P_ζ(x⁺ K_μ y⁻) = v^{(ν·ν)/2 - ⟨μ,ν⟩ + ⟨μ,ζ⟩ - ⟨K̃_ν,ζ⟩} (σ(x), y)` for `x, y` of weight `ν`, where
`σ` is the reversal of words and `K̃_ν = Σ νᵢ K̃ᵢ`; this is the computation behind
`ρ̄(F_w) = v^{(ν·ν)/2} E_{σ(w)} K̃_ν` (`rhoBar_minusHom_monomial`).

## Main definitions and results

* `QuantumGroup.rhoBar_minusHom_monomial`: `ρ̄(θ_w⁻) = v^{(ν·ν)/2} θ_{σ(w)}⁺ K̃_ν`, `ν = |w|`.
* `QuantumGroup.formFunctional`: the functional `P_ζ`.
* `QuantumGroup.formFunctional_mul_K`: `P_ζ(u K_μ) = v^{⟨μ,ζ⟩} P_ζ(u)`.
* `QuantumGroup.formFunctional_rhoBar_minusHom`: `P_ζ(ρ̄(x⁻) y⁻ K_μ) = v^{⟨μ,ζ⟩} (x, y)`.
* `QuantumGroup.induction_rhoBar_minusHom`: `U` is spanned by the `ρ̄(θ_w⁻) θ_{w'}⁻ K_μ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 26.1.2. The functional
  `P_ζ` is implicit in the proof there; its construction from the triangular decomposition is
  our own.
-/

open LieLean LusztigF TensorProduct

noncomputable section

namespace LusztigF

variable {k I : Type*} [Field k]

omit [Field k] in
lemma wordBasis_eq_monomial {k : Type*} [Field k] (w : List I) :
    FreeAlgebra.wordBasis k I w = monomial k w := by
  rw [FreeAlgebra.wordBasis_apply]; rfl

lemma weightScale_monomial (c : (I →₀ ℕ) → k) (w : List I) :
    weightScale c (monomial k w) = c (wordWeight w) • monomial k w := by
  rw [← wordBasis_eq_monomial, weightScale_wordBasis]

variable [DecidableEq I] (D : LusztigCartanDatum I) (v : k)

/-- Weight scalings are self-adjoint for Lusztig's form, which is orthogonal for the weight
grading ([Lus] 1.2.3). -/
lemma form_weightScale (c : (I →₀ ℕ) → k) (x y : LusztigF k I) :
    form D v x (weightScale c y) = form D v (weightScale c x) y := by
  have h : (form D v).compl₁₂ LinearMap.id (weightScale c) =
      (form D v).compl₁₂ (weightScale c) LinearMap.id :=
    LinearMap.ext_basis (FreeAlgebra.wordBasis k I) (FreeAlgebra.wordBasis k I) fun w w' ↦ by
      rw [LinearMap.compl₁₂_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
        LinearMap.id_apply, weightScale_wordBasis, weightScale_wordBasis, map_smul,
        LinearMap.map_smul₂, wordBasis_eq_monomial, wordBasis_eq_monomial]
      by_cases hw : wordWeight w = wordWeight w'
      · rw [hw]
      · rw [form_eq_zero_of_ne D v hw (monomial_mem_weightSpace w)
          (monomial_mem_weightSpace w'), smul_zero, smul_zero]
  exact LinearMap.congr_fun₂ h x y

end LusztigF

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-! ### Weight arithmetic -/

section Weights

variable (R) in
/-- `K̃_ν = Σᵢ νᵢ K̃ᵢ ∈ Y` for `ν ∈ ℕ[I]`. -/
def ktildeSum (ν : I →₀ ℕ) : Y := ν.sum fun i n ↦ n • ktilde R i

omit [DecidableEq I] in
@[simp] lemma ktildeSum_zero : ktildeSum R (0 : I →₀ ℕ) = 0 := Finsupp.sum_zero_index

omit [DecidableEq I] in
lemma ktildeSum_add (ν ν' : I →₀ ℕ) :
    ktildeSum R (ν + ν') = ktildeSum R ν + ktildeSum R ν' :=
  Finsupp.sum_add_index' (fun _ ↦ zero_smul _ _) fun _ _ _ ↦ add_smul _ _ _

omit [DecidableEq I] in
@[simp] lemma ktildeSum_single (i : I) (n : ℕ) :
    ktildeSum R (Finsupp.single i n) = n • ktilde R i :=
  Finsupp.sum_single_index (zero_smul _ _)

omit [DecidableEq I] in
lemma rootSum_ktilde_eq_root_ktildeSum (ν : I →₀ ℕ) (i : I) :
    R.rootSum ν (ktilde R i) = R.root i (ktildeSum R ν) := by
  induction ν using Finsupp.induction_linear with
  | zero => simp [LusztigCartanDatum.RootDatum.rootSum]
  | add ν ν' h h' =>
    rw [LusztigCartanDatum.RootDatum.rootSum_add, AddMonoidHom.add_apply, h, h', ktildeSum_add,
      map_add]
  | single j n =>
    rw [LusztigCartanDatum.RootDatum.rootSum_single, ktildeSum_single, AddMonoidHom.nsmul_apply,
      map_nsmul, root_ktilde_comm]

variable (R) in
/-- The norm `ν·ν = Σᵢⱼ νᵢ νⱼ (i·j)` of `ν ∈ ℕ[I]`, as `⟨K̃_ν, ν⟩`. -/
def normSq (ν : I →₀ ℕ) : ℤ := R.rootSum ν (ktildeSum R ν)

omit [DecidableEq I] in
@[simp] lemma normSq_zero : normSq R (0 : I →₀ ℕ) = 0 := by
  simp [normSq, LusztigCartanDatum.RootDatum.rootSum]

omit [DecidableEq I] in
lemma normSq_single_add (i : I) (ν : I →₀ ℕ) :
    normSq R (Finsupp.single i 1 + ν) =
      normSq R ν + 2 * R.root i (ktildeSum R ν) + 2 * D.d i := by
  simp only [normSq, LusztigCartanDatum.RootDatum.rootSum_add, ktildeSum_add,
    LusztigCartanDatum.RootDatum.rootSum_single, ktildeSum_single, one_smul,
    AddMonoidHom.add_apply, map_add, rootSum_ktilde_eq_root_ktildeSum, root_ktilde_eq_dot,
    ← D.two_mul_d]
  ring

omit [DecidableEq I] in
lemma normSq_wordWeight_emod_two (w : List I) : normSq R (wordWeight w) % 2 = 0 := by
  induction w with
  | nil => simp
  | cons i w ih => rw [wordWeight_cons, normSq_single_add]; omega

omit [DecidableEq I] in
lemma wordChar_eq_rootSum (w : List I) : wordChar R w = R.rootSum (wordWeight w) := by
  induction w with
  | nil => simp [LusztigCartanDatum.RootDatum.rootSum]
  | cons i w ih =>
    rw [wordChar_cons, wordWeight_cons, LusztigCartanDatum.RootDatum.rootSum_add,
      LusztigCartanDatum.RootDatum.rootSum_single, one_smul, ih]

end Weights

/-! ### `ρ̄` on `U⁻` and the Chevalley involution on `U^±` -/

section RhoBar

variable [NeZero v]

lemma minusHom_monomial_mul_K (w : List I) (μ : Y) :
    minusHom R v (monomial k w) * K R v μ =
      v ^ R.rootSum (wordWeight w) μ • (K R v μ * minusHom R v (monomial k w)) := by
  rw [mul_K_of_mem_adWeightSpace (minusHom_monomial_mem_adWeightSpace w), AddMonoidHom.neg_apply,
    neg_neg, wordChar_eq_rootSum]

/-- `ρ̄(θ_w⁻) = v^{(ν·ν)/2} θ_{σ(w)}⁺ K̃_ν` for a word `w` of weight `ν` ([Lus] 26.1.1; our
computation). -/
theorem rhoBar_minusHom_monomial (w : List I) :
    rhoBar R v (minusHom R v (monomial k w)) =
      v ^ (normSq R (wordWeight w) / 2) •
        (plusHom R v (monomial k w.reverse) * K R v (ktildeSum R (wordWeight w))) := by
  have hv := NeZero.ne v
  induction w with
  | nil => simp
  | cons i w ih =>
    have he := normSq_wordWeight_emod_two (R := R) w
    have h1 : K R v (ktildeSum R (wordWeight w)) * (Kt R v i * E R v i) =
        v ^ R.root i (ktildeSum R (wordWeight w) + ktilde R i) •
          (E R v i * K R v (ktildeSum R (wordWeight w) + ktilde R i)) := by
      rw [← mul_assoc, Kt, K_add, K_mul_E]
    rw [monomial_cons, map_mul, minusHom_θ, rhoBar_mul, ih, rhoBar_F, rhoBarF, List.reverse_cons,
      monomial_append, map_mul, monomial_cons, monomial_nil, mul_one, plusHom_θ, wordWeight_cons,
      ktildeSum_add, ktildeSum_single, one_smul, add_comm (ktilde R i), smul_mul_assoc,
      mul_smul_comm, mul_assoc, h1, mul_smul_comm, smul_smul, smul_smul, ← mul_assoc]
    congr 1
    have hd : (2 : ℤ) * D.d i = D.dot i i := D.two_mul_d i
    rw [normSq_single_add, map_add, root_ktilde_eq_dot, ← zpow_natCast, ← zpow_neg,
      ← zpow_add₀ hv, ← zpow_add₀ hv]
    congr 1
    omega

end RhoBar

section Chevalley

lemma chevalley_plusHom (x : LusztigF k I) : chevalley R v (plusHom R v x) = minusHom R v x := by
  have : (chevalley R v).comp (plusHom R v) = minusHom R v :=
    FreeAlgebra.hom_ext (funext fun i ↦ by simp [plusHom, minusHom])
  exact AlgHom.congr_fun this x

lemma chevalley_minusHom (x : LusztigF k I) : chevalley R v (minusHom R v x) = plusHom R v x := by
  have : (chevalley R v).comp (minusHom R v) = plusHom R v :=
    FreeAlgebra.hom_ext (funext fun i ↦ by simp [plusHom, minusHom])
  exact AlgHom.congr_fun this x

/-- `U` is spanned by the `θ_w⁺ K_μ θ_{w'}⁻` (the image of `span_triangular` under the Chevalley
involution). -/
theorem induction_plusHom_K_minusHom (hv : v ≠ 0) {P : QuantumGroup R v → Prop}
    (u : QuantumGroup R v) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : k) x, P x → P (c • x))
    (hmon : ∀ w μ w', P (plusHom R v (monomial k w) * K R v μ * minusHom R v (monomial k w'))) :
    P u := by
  have hu : chevalley R v u ∈ triangularSpan R v := by
    rw [span_triangular hv]; trivial
  suffices key : ∀ x ∈ triangularSpan R v, P (chevalley R v x) by
    simpa only [chevalley_chevalley] using key _ hu
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, μ, w', rfl⟩ := hx
    simpa only [map_mul, chevalley_minusHom, chevalley_K, chevalley_plusHom] using hmon w (-μ) w'
  | zero => simpa using h0
  | add x y _ _ hx hy => simpa only [map_add] using hadd _ _ hx hy
  | smul c x _ hx => simpa only [map_smul] using hsmul c _ hx

end Chevalley

/-! ### The functional `P_ζ` -/

section Functional

variable (R v)

/-- The scalar `v^{(ν·ν)/2 - ⟨μ,ν⟩ + ⟨μ,ζ⟩ - ⟨K̃_ν,ζ⟩}`. -/
def formScale (ζ : Y →+ ℤ) (μ : Y) (ν : I →₀ ℕ) : k :=
  v ^ (normSq R ν / 2 - R.rootSum ν μ + ζ μ - ζ (ktildeSum R ν))

/-- The pairing `(x, y) ↦ (σ(x), c(|y|) y)` giving `P_ζ(x⁺ K_μ y⁻)`. -/
def formPair (ζ : Y →+ ℤ) (μ : Y) : LusztigF k I →ₗ[k] LusztigF k I →ₗ[k] k :=
  (form D v).compl₁₂ (rev k I) (weightScale (formScale R v ζ μ))

/-- The pairings `formPair ζ (-μ)` assembled over `e^μ ∈ k[Y]`. -/
def formTri (ζ : Y →+ ℤ) :
    AddMonoidAlgebra k Y →ₗ[k] LusztigF k I →ₗ[k] LusztigF k I →ₗ[k] k :=
  (AddMonoidAlgebra.basis Y k).constr k fun μ ↦ formPair R v ζ (-μ)

/-- The functional `y ⊗ e^μ ⊗ x ↦ formPair ζ (-μ) y x` on `'f ⊗ k[Y] ⊗ 'f`. -/
def formTriLin (ζ : Y →+ ℤ) : TriSpace k I Y →ₗ[k] k :=
  TensorProduct.lift (TensorProduct.uncurry (RingHom.id k) _ _ _ ∘ₗ (formTri R v ζ).flip)

variable {R v}

lemma formPair_apply (ζ : Y →+ ℤ) (μ : Y) (x y : LusztigF k I) :
    formPair R v ζ μ x y = form D v (rev k I x) (weightScale (formScale R v ζ μ) y) := rfl

lemma formTri_single (ζ : Y →+ ℤ) (μ : Y) :
    formTri R v ζ (AddMonoidAlgebra.single μ 1) = formPair R v ζ (-μ) := by
  rw [formTri, ← AddMonoidAlgebra.basis_apply, Module.Basis.constr_basis]

lemma formTriLin_tmul (ζ : Y →+ ℤ) (y : LusztigF k I) (g : AddMonoidAlgebra k Y)
    (x : LusztigF k I) : formTriLin R v ζ (y ⊗ₜ (g ⊗ₜ x)) = formTri R v ζ g y x := by
  simp [formTriLin]

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv

lemma formPair_eq_zero_left (ζ : Y →+ ℤ) (μ : Y) {x : LusztigF k I} (hx : x ∈ serreIdeal D v)
    (y : LusztigF k I) : formPair R v ζ μ x y = 0 :=
  (mem_radical_iff D v).1 (serreIdeal_le_radical (NeZero.ne v) hv
    (rev_mem_serreIdeal D v hx)) _

lemma formPair_eq_zero_right (ζ : Y →+ ℤ) (μ : Y) (x : LusztigF k I) {y : LusztigF k I}
    (hy : y ∈ serreIdeal D v) : formPair R v ζ μ x y = 0 := by
  rw [formPair_apply, form_weightScale, form_comm]
  exact (mem_radical_iff D v).1 (serreIdeal_le_radical (NeZero.ne v) hv hy) _

lemma serreTriSubmodule_le_ker_formTriLin (ζ : Y →+ ℤ) :
    serreTriSubmodule Y D v ≤ LinearMap.ker (formTriLin R v ζ) := by
  rw [serreTriSubmodule, Submodule.span_le]
  rintro _ ⟨y, g, x, rfl, hy | hx⟩
  · have h : (formTri R v ζ).flip y = 0 :=
      (AddMonoidAlgebra.basis Y k).ext fun μ ↦ LinearMap.ext fun x ↦ by
        rw [LinearMap.flip_apply, AddMonoidAlgebra.basis_apply, formTri_single,
          formPair_eq_zero_left hv _ _ hy, LinearMap.zero_apply, LinearMap.zero_apply]
    rw [SetLike.mem_coe, LinearMap.mem_ker, formTriLin_tmul,
      ← LinearMap.flip_apply (formTri R v ζ) g y, h]
    rfl
  · have h : ((formTri R v ζ).flip y).flip x = 0 :=
      (AddMonoidAlgebra.basis Y k).ext fun μ ↦ by
        rw [LinearMap.flip_apply, LinearMap.flip_apply, AddMonoidAlgebra.basis_apply,
          formTri_single, formPair_eq_zero_right hv _ _ _ hx, LinearMap.zero_apply]
    have h' := LinearMap.congr_fun h g
    simp only [LinearMap.flip_apply, LinearMap.zero_apply] at h'
    simp [formTriLin_tmul, h']

variable (R v) in
/-- **The functional `P_ζ`** with `P_ζ(z) = (1_ζ, z 1_ζ)` for Lusztig's form on `U̇` ([Lus]
26.1.2): `P_ζ(x⁺ K_μ y⁻) = v^{(ν·ν)/2 - ⟨μ,ν⟩ + ⟨μ,ζ⟩ - ⟨K̃_ν,ζ⟩} (σ(x), y)` for `y` of weight `ν`
(`formFunctional_plusHom_K_minusHom`). -/
def formFunctional (ζ : Y →+ ℤ) : QuantumGroup R v →ₗ[k] k :=
  (serreTriSubmodule Y D v).liftQ (formTriLin R v ζ) (serreTriSubmodule_le_ker_formTriLin hv ζ) ∘ₗ
    (triangularEquiv R v hv).symm.toLinearMap ∘ₗ (chevalley R v).toLinearMap

theorem formFunctional_plusHom_K_minusHom (ζ : Y →+ ℤ) (x : LusztigF k I) (μ : Y)
    (y : LusztigF k I) :
    formFunctional R v hv ζ (plusHom R v x * K R v μ * minusHom R v y) =
      form D v (rev k I x) (weightScale (formScale R v ζ μ) y) := by
  have h : chevalley R v (plusHom R v x * K R v μ * minusHom R v y) =
      triangularEquiv R v hv (Submodule.Quotient.mk
        (x ⊗ₜ (AddMonoidAlgebra.single (-μ) 1 ⊗ₜ y))) := by
    rw [triangularEquiv_mk, zeroHom_single, map_mul, map_mul, chevalley_plusHom, chevalley_K,
      chevalley_minusHom]
  rw [formFunctional, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply, formTriLin_tmul,
    formTri_single, neg_neg, formPair_apply]

theorem formFunctional_plusHom_K_minusHom_monomial (ζ : Y →+ ℤ) (x : LusztigF k I) (μ : Y)
    (w : List I) :
    formFunctional R v hv ζ (plusHom R v x * K R v μ * minusHom R v (monomial k w)) =
      formScale R v ζ μ (wordWeight w) * form D v (rev k I x) (monomial k w) := by
  rw [formFunctional_plusHom_K_minusHom, weightScale_monomial, map_smul, smul_eq_mul]

/-- `P_ζ(u K_μ) = v^{⟨μ,ζ⟩} P_ζ(u)`. -/
theorem formFunctional_mul_K (ζ : Y →+ ℤ) (u : QuantumGroup R v) (μ : Y) :
    formFunctional R v hv ζ (u * K R v μ) = v ^ ζ μ * formFunctional R v hv ζ u := by
  have hv0 := NeZero.ne v
  induction u using induction_plusHom_K_minusHom hv0 with
  | h0 => simp
  | hadd x y hx hy => rw [add_mul, map_add, map_add, hx, hy, mul_add]
  | hsmul c x hx => rw [smul_mul_assoc, map_smul, map_smul, hx, smul_eq_mul, smul_eq_mul,
      mul_left_comm]
  | hmon w ν w' =>
    rw [mul_assoc, minusHom_monomial_mul_K, mul_smul_comm, ← mul_assoc, mul_assoc _ (K R v ν),
      K_add, map_smul, formFunctional_plusHom_K_minusHom_monomial,
      formFunctional_plusHom_K_minusHom_monomial, smul_eq_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    simp only [formScale, map_add, ← zpow_add₀ hv0]
    congr 1
    ring

/-- `P_ζ(K_μ z) = v^{⟨μ,ζ⟩} P_ζ(z)` for `z` of weight `0`. -/
theorem formFunctional_K_mul (ζ : Y →+ ℤ) {z : QuantumGroup R v}
    (hz : z ∈ adWeightSpace R v 0) (μ : Y) :
    formFunctional R v hv ζ (K R v μ * z) = v ^ ζ μ * formFunctional R v hv ζ z := by
  rw [hz μ, AddMonoidHom.zero_apply, zpow_zero, one_smul, formFunctional_mul_K]

/-- `P_ζ(ρ̄(θ_w⁻) θ_{w'}⁻) = (θ_w, θ_{w'})`. -/
lemma formFunctional_rhoBar_minusHom_monomial (ζ : Y →+ ℤ) (w w' : List I) :
    formFunctional R v hv ζ
        (rhoBar R v (minusHom R v (monomial k w)) * minusHom R v (monomial k w')) =
      form D v (monomial k w) (monomial k w') := by
  have hv0 := NeZero.ne v
  rw [rhoBar_minusHom_monomial, smul_mul_assoc, map_smul,
    formFunctional_plusHom_K_minusHom_monomial, rev_monomial, List.reverse_reverse, smul_eq_mul,
    ← mul_assoc]
  by_cases hw : wordWeight w = wordWeight w'
  · have he := normSq_wordWeight_emod_two (R := R) w
    rw [← hw, formScale, ← zpow_add₀ hv0]
    have h0 : normSq R (wordWeight w) / 2 + (normSq R (wordWeight w) / 2 -
        R.rootSum (wordWeight w) (ktildeSum R (wordWeight w)) + ζ (ktildeSum R (wordWeight w)) -
        ζ (ktildeSum R (wordWeight w))) = 0 := by
      change _ + (_ - normSq R (wordWeight w) + _ - _) = _
      omega
    rw [h0, zpow_zero, one_mul]
  · rw [form_eq_zero_of_ne D v hw (monomial_mem_weightSpace w) (monomial_mem_weightSpace w'),
      mul_zero]

/-- **`P_ζ(ρ̄(x⁻) y⁻ K_μ) = v^{⟨μ,ζ⟩} (x, y)`** for `x, y ∈ 'f`: the values forced on
`(1_ζ, z 1_ζ)` by [Lus] 26.1.2 (b), (c). -/
theorem formFunctional_rhoBar_minusHom (ζ : Y →+ ℤ) (x y : LusztigF k I) (μ : Y) :
    formFunctional R v hv ζ (rhoBar R v (minusHom R v x) * minusHom R v y * K R v μ) =
      v ^ ζ μ * form D v x y := by
  rw [formFunctional_mul_K]
  congr 1
  have h : ((LinearMap.mul k (QuantumGroup R v)).compr₂ (formFunctional R v hv ζ)).compl₁₂
      (rhoBar R v ∘ₗ (minusHom R v).toLinearMap) (minusHom R v).toLinearMap = form D v :=
    LinearMap.ext_basis (FreeAlgebra.wordBasis k I) (FreeAlgebra.wordBasis k I) fun w w' ↦ by
      simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearMap.mul_apply',
        LinearMap.comp_apply, AlgHom.toLinearMap_apply, wordBasis_eq_monomial]
      exact formFunctional_rhoBar_minusHom_monomial hv ζ w w'
  exact LinearMap.congr_fun₂ h x y

end Functional

/-- `U` is spanned by the `ρ̄(θ_w⁻) θ_{w'}⁻ K_μ` ([Lus] 26.1.2, proof). -/
theorem induction_rhoBar_minusHom [NeZero v] {P : QuantumGroup R v → Prop}
    (u : QuantumGroup R v) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : k) x, P x → P (c • x))
    (hmon : ∀ w w' μ, P (rhoBar R v (minusHom R v (monomial k w)) *
      minusHom R v (monomial k w') * K R v μ)) : P u := by
  have hv0 := NeZero.ne v
  induction u using induction_plusHom_K_minusHom hv0 with
  | h0 => exact h0
  | hadd x y hx hy => exact hadd x y hx hy
  | hsmul c x hx => exact hsmul c x hx
  | hmon w μ w' =>
    have hkey := rhoBar_minusHom_monomial (R := R) (v := v) w.reverse
    rw [List.reverse_reverse] at hkey
    set e := normSq R (wordWeight w.reverse) / 2
    set κ := ktildeSum R (wordWeight w.reverse)
    have hE : plusHom R v (monomial k w) =
        (v ^ e)⁻¹ • (rhoBar R v (minusHom R v (monomial k w.reverse)) * K R v (-κ)) := by
      rw [hkey, smul_mul_assoc, mul_assoc, K_add, add_neg_cancel, K_zero, mul_one, smul_smul,
        inv_mul_cancel₀ (zpow_ne_zero _ hv0), one_smul]
    rw [hE, smul_mul_assoc, smul_mul_assoc, mul_assoc _ (K R v (-κ)), K_add, mul_assoc,
      K_mul_minusHom_monomial, mul_smul_comm, ← mul_assoc]
    exact hsmul _ _ (hsmul _ _ (hmon _ _ _))

/-- `ρ̄` maps `U_χ` to `U_{-χ}`. -/
lemma rhoBar_mem_adWeightSpace [NeZero v] {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) : rhoBar R v x ∈ adWeightSpace R v (-χ) := fun μ ↦ by
  have h := congrArg (rhoBar R v) (hx μ)
  rw [rhoBar_mul, map_smul, rhoBar_mul, rhoBar_K] at h
  rw [AddMonoidHom.neg_apply, h, smul_smul, ← zpow_add₀ (NeZero.ne v), neg_add_cancel, zpow_zero,
    one_smul]

end LieLean.QuantumGroup
