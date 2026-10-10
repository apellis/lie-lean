/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.Triangular
import LieLean.Algebra.QuantumGroup.PBW.TriangularBasis
import LieLean.Algebra.QuantumGroup.PBW.RootVectorsNotRoot

/-!
# Integrality of the root vectors ([Lus] 41.1.3)

We construct, for `ζ ∈ X`, the linear map `Θ_ζ : U̇ → U` with `Θ_ζ(y⁻ x⁺ 1_ζ) = ε(y) x⁺` for
`y⁻ ∈ U⁻`, `x⁺ ∈ U⁺`, which vanishes on the components `ₗU_λ''` with `λ'' ≠ ζ`
(`Modified.Theta`, from the triangular decomposition of `U`). Since `𝒜U̇` is the `𝒜`-span of the
`F_w E_{w'} 1_λ` ([Lus] 23.2.2), `Θ_ζ` maps `𝒜U̇` into `𝒜U⁺` (the `𝒜`-span of the monomials `E_w`
in divided powers, i.e. the image of `𝒜f`); hence **if `x⁺ 1_ζ ∈ 𝒜U̇` then `x⁺ ∈ 𝒜U⁺`**
(`Modified.mem_aPlus_of_elt_mem_aForm`), the statement deduced from 23.2.2 in the proof of
[Lus] 41.1.3. Combined with 41.1.2 (`Modified.braid_mem_aForm`) and 40.1.3 this gives
**[Lus] 41.1.3**.

## Main results

* `Modified.aPlus R`: `𝒜U⁺`, the `𝒜`-combinations of the `E_w`.
* `Modified.mem_aPlus_of_elt_mem_aForm`: `x ∈ U⁺`, `x 1_ζ ∈ 𝒜U̇` ⇒ `x ∈ 𝒜U⁺`.
* `Modified.list_braid_qDivPow_E_mem_aPlus`: **[Lus] 41.1.3 (a)** for `e = 1`:
  `T''_{i₁,1} ⋯ T''_{iₙ₋₁,1}(E_{iₙ}^{(t)}) ∈ 𝒜U⁺` when `s_{i₁} ⋯ s_{iₙ}` is reduced.
* `Modified.list_braid_symm_qDivPow_E_mem_aPlus`: **[Lus] 41.1.3 (b)** for `e = -1`:
  `T'_{i₁,-1} ⋯ T'_{iₙ₋₁,-1}(E_{iₙ}^{(t)}) ∈ 𝒜U⁺` (`T'_{i,-1} = Tᵢ⁻¹`), from (a) by Lusztig's
  anti-automorphism `σ` (`σ T''_{i,1} σ = T'_{i,-1}`, [Lus] 37.2.4).

Both use that the root vectors lie in `U⁺` ([Lus] 40.1.3), which the library proves when
`aᵢⱼ aⱼᵢ ≤ 3` for all `i ≠ j` (`rootVector_mem_adjoin_of_not_root`; all finite types); this
hypothesis is inherited. The symmetries `T''_{i,-1}`, `T'_{i,1}` are not defined in the library.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.2.2, 37.2.4, 40.1.3,
  41.1.2, 41.1.3.
-/

open LieLean Finset TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-! ### The map `θ_ζ : U → U` -/

section Theta

variable (R v) in
/-- Conjugation `x ↦ K_μ x K_{-μ}`. -/
def adK (μ : Y) : Module.End k (QuantumGroup R v) :=
  LinearMap.mulLeft k (K R v μ) ∘ₗ LinearMap.mulRight k (K R v (-μ))

lemma adK_apply (μ : Y) (x : QuantumGroup R v) : adK R v μ x = K R v μ * x * K R v (-μ) := by
  simp [adK, mul_assoc]

lemma adK_zero (x : QuantumGroup R v) : adK R v 0 x = x := by
  rw [adK_apply, neg_zero, K_zero, one_mul, mul_one]

lemma adK_add (μ ν : Y) (x : QuantumGroup R v) :
    adK R v (μ + ν) x = adK R v μ (adK R v ν x) := by
  simp only [adK_apply]
  have h : K R v (-ν) * K R v (-μ) = K R v (-(μ + ν)) := by rw [K_add]; congr 1; abel
  rw [← K_add, ← h]; simp only [mul_assoc]

variable [NeZero v]

variable (R v) in
/-- The algebra map `k[Y] → End(U)`, `e^μ ↦ v^{⟨μ,ζ⟩} Ad(K_μ)`. -/
def twistAd (ζ : Y →+ ℤ) : AddMonoidAlgebra k Y →ₐ[k] Module.End k (QuantumGroup R v) :=
  AddMonoidAlgebra.lift k (Module.End k (QuantumGroup R v)) Y
    { toFun := fun μ ↦ v ^ ζ μ.toAdd • adK R v μ.toAdd
      map_one' := by
        ext x
        simp [adK_zero]
      map_mul' := fun μ ν ↦ by
        ext x
        simp only [toAdd_mul, map_add, zpow_add₀ (NeZero.ne v), Module.End.mul_apply,
          LinearMap.smul_apply, map_smul, smul_smul]
        rw [adK_add, mul_comm] }

lemma twistAd_single (ζ : Y →+ ℤ) (μ : Y) (c : k) (x : QuantumGroup R v) :
    twistAd R v ζ (AddMonoidAlgebra.single μ c) x = (c * v ^ ζ μ) • adK R v μ x := by
  simp [twistAd, AddMonoidAlgebra.lift_single, mul_smul]

omit [NeZero v] in
lemma adK_mem_plus (μ : Y) {x : QuantumGroup R v}
    (hx : x ∈ Algebra.adjoin k (Set.range (E R v))) :
    adK R v μ x ∈ Algebra.adjoin k (Set.range (E R v)) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [adK_apply, conj_eq_of_mem_adWeightSpace (E_mem_adWeightSpace i)]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _
  | algebraMap c =>
    rw [adK_apply, ← Algebra.commutes, mul_assoc, K_add, add_neg_cancel, K_zero, mul_one]
    exact Subalgebra.algebraMap_mem _ c
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    have : adK R v μ (x * y) = adK R v μ x * adK R v μ y := by
      simp only [adK_apply, mul_assoc]
      rw [← mul_assoc (K R v (-μ)) (K R v μ), K_add, neg_add_cancel, K_zero, one_mul]
    rw [this]; exact mul_mem hx hy

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

variable (R) in
/-- `g ⊗ x ↦ (e^μ ↦ v^{⟨μ,ζ⟩} Ad(K_μ))(g)(x)` on `k[Y] ⊗ U⁺`. -/
def phiTheta (ζ : Y →+ ℤ) :
    AddMonoidAlgebra k Y ⊗[k] Algebra.adjoin k (Set.range (E R v)) →ₗ[k] QuantumGroup R v :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun (g : AddMonoidAlgebra k Y) (x : Algebra.adjoin k (Set.range (E R v))) ↦
      twistAd R v ζ g (x : QuantumGroup R v))
    (fun g g' x ↦ by simp) (fun c g x ↦ by simp)
    (fun g x x' ↦ by simp) (fun c g x ↦ by simp)

variable (R) in
/-- `y ⊗ z ↦ ε(y) φ(z)` on `U⁻ ⊗ k[Y] ⊗ U⁺`. -/
def psiTheta (ζ : Y →+ ℤ) :
    Algebra.adjoin k (Set.range (F R v)) ⊗[k]
      (AddMonoidAlgebra k Y ⊗[k] Algebra.adjoin k (Set.range (E R v))) →ₗ[k] QuantumGroup R v :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun (y : Algebra.adjoin k (Set.range (F R v)))
      (z : AddMonoidAlgebra k Y ⊗[k] Algebra.adjoin k (Set.range (E R v))) ↦
      counit R v (y : QuantumGroup R v) • phiTheta R ζ z)
    (fun y y' z ↦ by simp [add_smul]) (fun c y z ↦ by simp [smul_smul])
    (fun y z z' ↦ by simp) (fun c y z ↦ by simp [smul_comm c])

include hv in
variable (R) in
/-- **The map `θ_ζ : U → U`**, `y⁻ K_μ x⁺ ↦ ε(y) v^{⟨μ,ζ⟩} K_μ x⁺ K_{-μ}` (through the triangular
decomposition). -/
def theta (ζ : Y →+ ℤ) : QuantumGroup R v →ₗ[k] QuantumGroup R v :=
  psiTheta R ζ ∘ₗ (triangularMultiplicationEquiv R v hv).symm.toLinearMap

lemma theta_apply (ζ : Y →+ ℤ) (y : Algebra.adjoin k (Set.range (F R v)))
    (g : AddMonoidAlgebra k Y) (x : Algebra.adjoin k (Set.range (E R v))) :
    theta R hv ζ ((y : QuantumGroup R v) * zeroHom R v g * x) =
      counit R v (y : QuantumGroup R v) • twistAd R v ζ g x := by
  rw [← triangularMultiplicationEquiv_tmul R v hv, theta, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  simp [psiTheta, phiTheta]

lemma theta_mul_plus (ζ : Y →+ ℤ) (y : Algebra.adjoin k (Set.range (F R v)))
    (x : Algebra.adjoin k (Set.range (E R v))) :
    theta R hv ζ ((y : QuantumGroup R v) * x) = counit R v (y : QuantumGroup R v) • x := by
  have h := theta_apply hv ζ y 1 x
  rwa [map_one, mul_one, map_one, Module.End.one_apply] at h

lemma theta_plus (ζ : Y →+ ℤ) {x : QuantumGroup R v}
    (hx : x ∈ Algebra.adjoin k (Set.range (E R v))) : theta R hv ζ x = x := by
  have h := theta_mul_plus hv ζ 1 ⟨x, hx⟩
  simpa using h

lemma theta_mul_K (ζ : Y →+ ℤ) (u : QuantumGroup R v) (ν : Y) :
    theta R hv ζ (u * K R v ν) = v ^ ζ ν • theta R hv ζ u := by
  obtain ⟨t, rfl⟩ := (triangularMultiplicationEquiv R v hv).surjective u
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, add_mul, map_add, ha, hb, map_add, smul_add]
  | tmul y z =>
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [tmul_add, map_add, add_mul, map_add, ha, hb, map_add, smul_add]
    | tmul g x =>
      induction g using AddMonoidAlgebra.induction_on with
      | of μ =>
        rw [triangularMultiplicationEquiv_tmul]
        have hx' := adK_mem_plus (R := R) (-ν) x.2
        have e : (y : QuantumGroup R v) * zeroHom R v (AddMonoidAlgebra.of k Y (.ofAdd μ)) * x *
            K R v ν = y * zeroHom R v (AddMonoidAlgebra.single (μ + ν) 1) *
              (⟨_, hx'⟩ : Algebra.adjoin k (Set.range (E R v))) := by
          simp only [AddMonoidAlgebra.of_apply, toAdd_ofAdd, zeroHom_single]
          rw [adK_apply, neg_neg, ← K_add]
          simp only [mul_assoc]
          rw [← mul_assoc (K R v ν) (K R v (-ν)), K_add, add_neg_cancel, K_zero, one_mul]
        rw [e, theta_apply, theta_apply, AddMonoidAlgebra.of_apply, twistAd_single,
          twistAd_single, adK_add, ← adK_add ν (-ν), add_neg_cancel, adK_zero]
        simp only [smul_smul, one_mul, map_add, zpow_add₀ (NeZero.ne v), toAdd_ofAdd]
        congr 1
        ring
      | add a b ha hb =>
        rw [add_tmul, tmul_add, map_add, add_mul, map_add, ha, hb, map_add, smul_add]
      | smul c a ha =>
        rw [← smul_tmul', tmul_smul, map_smul, smul_mul_assoc, map_smul, ha, map_smul, smul_comm]

lemma theta_K_mul (ζ χ : Y →+ ℤ) {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v χ) (μ : Y) :
    theta R hv ζ (K R v μ * u) = v ^ (χ + ζ) μ • theta R hv ζ u := by
  rw [hu μ, map_smul, theta_mul_K, smul_smul, AddMonoidHom.add_apply, zpow_add₀ (NeZero.ne v)]

lemma theta_modRel {L ζ : Y →+ ℤ} {x : QuantumGroup R v} (hx : x ∈ modRel R v L ζ) :
    theta R hv ζ x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · rw [sub_mul, map_sub, theta_K_mul hv ζ _ hu, sub_add_cancel, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, map_smul, sub_self]
    · rw [mul_sub, map_sub, theta_mul_K, ← Algebra.commutes, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, map_smul, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

end Theta

/-! ### The map `Θ_ζ : U̇ → U` -/

namespace Modified

attribute [local instance] decEqIdx

section ThetaDot

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

open scoped Classical in
include hv in
variable (R) in
/-- `Θ_ζ` on the component `ₗU_λ''`: induced by `θ_ζ` if `λ'' = ζ`, zero otherwise. -/
def thetaComp (ζ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) : Comp R v p →ₗ[k] QuantumGroup R v :=
  if h : p.2 = ζ then
    Submodule.liftQ _ (theta R hv ζ ∘ₗ (adWeightSpace R v (p.1 - p.2)).subtype) fun x hx ↦
      LinearMap.mem_ker.2 (by
        have hx' : x.1 ∈ modRel R v p.1 p.2 := hx
        subst h
        exact theta_modRel hv hx')
  else 0

include hv in
variable (R) in
/-- **The map `Θ_ζ : U̇ → U`**: `Θ_ζ(π_{λ',ζ}(y⁻ x⁺)) = ε(y) x⁺`, and `Θ_ζ` vanishes on the
components `ₗU_λ''` with `λ'' ≠ ζ`. -/
def Theta (ζ : Y →+ ℤ) : Modified R v →ₗ[k] QuantumGroup R v :=
  DirectSum.toModule k _ _ (thetaComp R hv ζ)

open scoped Classical in
lemma Theta_elt (ζ L l : Y →+ ℤ) {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v (L - l)) :
    Theta R hv ζ (elt L l u hu) = if l = ζ then theta R hv ζ u else 0 := by
  rw [Theta, elt, DirectSum.toModule_lof]
  by_cases h : l = ζ
  · subst h
    simp only [thetaComp, Comp.mk, ↓reduceDIte, ↓reduceIte]
    rfl
  · simp [thetaComp, h]

end ThetaDot

/-! ### `𝒜U⁺` and the integrality statement -/

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X

variable (R) in
/-- `𝒜U⁺`: the `𝒜`-combinations of the monomials `E_w` in divided powers, i.e. the image of `𝒜f`
under `x ↦ x⁺` ([Lus] 3.1.13). -/
def aPlus : AddSubgroup (QuantumGroup R 𝕧) :=
  AddSubgroup.closure {x | ∃ (c : 𝕂) (w : List (I × ℕ)), IsLaurent c ∧ x = c • ePow R w}

lemma ePow_mem_aPlus (w : List (I × ℕ)) : ePow R w ∈ aPlus R :=
  AddSubgroup.subset_closure ⟨1, w, isLaurent_one, (one_smul _ _).symm⟩

lemma smul_mem_aPlus {c : 𝕂} (hc : IsLaurent c) {x : QuantumGroup R 𝕧} (hx : x ∈ aPlus R) :
    c • x ∈ aPlus R := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c', w, hc', rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c * c', w, hc.mul hc', by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma qDivPow_F_mem_minus (i : I) (n : ℕ) :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) ∈ Algebra.adjoin 𝕂 (Set.range (F R 𝕧)) :=
  Subalgebra.smul_mem _ (pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) n) _

lemma fPow_mem_minus (w : List (I × ℕ)) :
    fPow R w ∈ Algebra.adjoin 𝕂 (Set.range (F R 𝕧)) := by
  induction w with
  | nil => exact one_mem _
  | cons p w ih => rw [fPow_cons]; exact mul_mem (qDivPow_F_mem_minus p.1 p.2) ih

lemma qDivPow_E_mem_plus (i : I) (n : ℕ) :
    qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i) ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) :=
  Subalgebra.smul_mem _ (pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) n) _

lemma ePow_mem_plus (w : List (I × ℕ)) :
    ePow R w ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) := by
  induction w with
  | nil => exact one_mem _
  | cons p w ih => rw [ePow_cons]; exact mul_mem (qDivPow_E_mem_plus p.1 p.2) ih

lemma isLaurent_counit_fPow (w : List (I × ℕ)) : IsLaurent (counit R 𝕧 (fPow R w)) := by
  induction w with
  | nil => simpa using isLaurent_one
  | cons p w ih =>
    rw [fPow_cons, _root_.map_mul]
    refine IsLaurent.mul ?_ ih
    rcases Nat.eq_zero_or_pos p.2 with h | h
    · rw [h, qDivPow_zero', _root_.map_one]; exact isLaurent_one
    · rw [qDivPow, map_smul, map_pow, counit_F, zero_pow h.ne', smul_zero]; exact isLaurent_zero

lemma Theta_mem_aPlus (ζ : Y →+ ℤ) {x : Modified R 𝕧} (hx : x ∈ aFormFE R) :
    Theta R ratFunc_X_not_root ζ x ∈ aPlus R := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, w', L, l, h, rfl⟩ := hx
    rw [Theta_elt]
    split_ifs
    · have e := theta_mul_plus ratFunc_X_not_root ζ ⟨fPow R w, fPow_mem_minus w⟩
        ⟨ePow R w', ePow_mem_plus w'⟩
      simp only at e
      rw [e]
      exact smul_mem_aPlus (isLaurent_counit_fPow w) (ePow_mem_aPlus w')
    · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [laurent_smul, map_smul]; exact smul_mem_aPlus ⟨a, rfl⟩ hx

/-- **If `x⁺ 1_ζ ∈ 𝒜U̇` then `x⁺ ∈ 𝒜U⁺`** (the consequence of [Lus] 23.2.2 used in the proof of
[Lus] 41.1.3). Here `x⁺ 1_ζ = π_{ζ+|x|,ζ}(x⁺)`. -/
theorem mem_aPlus_of_elt_mem_aForm {x : QuantumGroup R 𝕧}
    (hx : x ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧))) {L ζ : Y →+ ℤ}
    (hxw : x ∈ adWeightSpace R 𝕧 (L - ζ)) (h : elt L ζ x hxw ∈ aForm R) : x ∈ aPlus R := by
  have h' : elt L ζ x hxw ∈ aFormFE R := by
    rw [← aForm_eq_aFormFE]; exact h
  have := Theta_mem_aPlus ζ h'
  simp only [Theta_elt, ↓reduceIte] at this
  rwa [theta_plus ratFunc_X_not_root ζ hx] at this

/-! ### [Lus] 41.1.3 -/

omit [DecidableEq I] in
lemma wordWeightAction_sub (ω : List I) (L l : Y →+ ℤ) :
    wordWeightAction R ω (L - l) = wordWeightAction R ω L - wordWeightAction R ω l := by
  induction ω with
  | nil => rfl
  | cons i ω ih => simp only [wordWeightAction, ih, AddMonoidHom.sub_comp]

lemma word_braid_mem {ω : List I} {L l : Y →+ ℤ} {u : QuantumGroup R 𝕧}
    (hu : u ∈ adWeightSpace R 𝕧 (L - l)) :
    (ω.map (braidEquivOfNotRoot R ratFunc_X_not_root)).prod u ∈
      adWeightSpace R 𝕧 (wordWeightAction R ω L - wordWeightAction R ω l) := by
  rw [← wordWeightAction_sub]
  exact word_braid_mem_adWeightSpace
    (fun i ↦ braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i) ω hu

/-- `T_{i₁} ⋯ T_{iₖ}(π_{λ',λ''}(u)) = π(T_{i₁} ⋯ T_{iₖ}(u))` on `U̇`. -/
lemma list_braid_elt (ω : List I) {L l : Y →+ ℤ} {u : QuantumGroup R 𝕧}
    (hu : u ∈ adWeightSpace R 𝕧 (L - l)) :
    (ω.map (braid (R := R) ratFunc_X_not_root)).prod (elt L l u hu) =
      elt (wordWeightAction R ω L) (wordWeightAction R ω l)
        ((ω.map (braidEquivOfNotRoot R ratFunc_X_not_root)).prod u) (word_braid_mem hu) := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih,
      braid_elt ratFunc_X_not_root i _ _ _ (by
        rw [← AddMonoidHom.sub_comp]
        exact (braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i).map_mem_adWeightSpace
          (word_braid_mem hu))]
    exact elt_index rfl rfl (by rw [List.map_cons, List.prod_cons, AlgEquiv.mul_apply]) _ _

lemma list_braid_mem_aForm (ω : List I) {x : Modified R 𝕧} (hx : x ∈ aForm R) :
    (ω.map (braid (R := R) ratFunc_X_not_root)).prod x ∈ aForm R := by
  induction ω with
  | nil => exact hx
  | cons i ω ih =>
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply]
    exact braid_mem_aForm i ih

/-- **[Lus] 41.1.3 (a)** (`e = 1`): if `s_{i₁} ⋯ s_{iₙ₋₁} s_i` is a reduced expression, then
`T''_{i₁,1} ⋯ T''_{iₙ₋₁,1}(E_i^{(t)}) ∈ 𝒜U⁺`. The hypothesis `aᵢⱼ aⱼᵢ ≤ 3` (all finite types)
is that of the library's [Lus] 40.1.3 (`rootVector_mem_adjoin_of_not_root`). -/
theorem list_braid_qDivPow_E_mem_aPlus
    (hfin : ∀ i j, i ≠ j → D.cartanMatrix i j * D.cartanMatrix j i ≤ 3)
    {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
    {ω : List I} {i : I} (hω : cs.IsReduced (ω ++ [i])) (t : ℕ) :
    (ω.map (braidEquivOfNotRoot R ratFunc_X_not_root)).prod (qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i)) ∈
      aPlus R := by
  set T := braidEquivOfNotRoot R ratFunc_X_not_root
  have hE : (ω.map T).prod (E R 𝕧 i) ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) := by
    have := rootVector_mem_adjoin_of_not_root (R := R) hfin ratFunc_X_not_root hω ω.length
      (by simp)
    simpa [CoxeterSystem.rootVector, T] using this
  have hx : (ω.map T).prod (qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i)) ∈
      Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) := by
    have e := map_qDivPow' ((ω.map T).prod : QuantumGroup R 𝕧 ≃ₐ[𝕂] _).toAlgHom (𝕧 ^ D.d i) t
      (E R 𝕧 i)
    simp only [AlgEquiv.coe_toAlgHom] at e
    rw [e]
    exact Subalgebra.smul_mem _ (pow_mem hE t) _
  have hd := list_braid_mem_aForm ω (divE_mem (R := R) i t 0)
  rw [divE, list_braid_elt] at hd
  exact mem_aPlus_of_elt_mem_aForm hx _ hd

lemma braidReversal_one : braidReversal (1 : QuantumGroup R 𝕧) = 1 := by
  simp [braidReversal]

lemma ePow_append (w w' : List (I × ℕ)) : ePow R (w ++ w') = ePow R w * ePow R w' := by
  simp [ePow]

lemma braidReversal_ePow (w : List (I × ℕ)) : braidReversal (ePow R w) = ePow R w.reverse := by
  induction w with
  | nil => simpa using braidReversal_one
  | cons p w ih =>
    rw [ePow_cons, braidReversal_mul, ih, braidReversal_qDivPow, braidReversal_E,
      List.reverse_cons, ePow_append]
    simp [ePow]

lemma braidReversal_mem_aPlus {x : QuantumGroup R 𝕧} (hx : x ∈ aPlus R) :
    braidReversal x ∈ aPlus R := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, hc, rfl⟩ := hx
    rw [map_smul, braidReversal_ePow]
    exact smul_mem_aPlus hc (ePow_mem_aPlus _)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/-- `T'_{i,-1} = σ T''_{i,1} σ` ([Lus] 37.2.4), `σ = braidReversal`. -/
lemma braidEquivOfNotRoot_symm_apply' (i : I) (y : QuantumGroup R 𝕧) :
    (braidEquivOfNotRoot R ratFunc_X_not_root i).symm y =
      braidReversal (braidEquivOfNotRoot R ratFunc_X_not_root i (braidReversal y)) :=
  rfl

lemma list_braid_symm_apply (ω : List I) (y : QuantumGroup R 𝕧) :
    (ω.map fun j ↦ (braidEquivOfNotRoot R ratFunc_X_not_root j).symm).prod y =
      braidReversal ((ω.map (braidEquivOfNotRoot R ratFunc_X_not_root)).prod
        (braidReversal y)) := by
  induction ω generalizing y with
  | nil => simp [braidReversal_involutive y]
  | cons i ω ih =>
    simp only [List.map_cons, List.prod_cons, AlgEquiv.mul_apply]
    rw [ih, braidEquivOfNotRoot_symm_apply', braidReversal_involutive]

/-- **[Lus] 41.1.3 (b)** (`e = -1`): if `s_{i₁} ⋯ s_{iₙ₋₁} s_i` is a reduced expression, then
`T'_{i₁,-1} ⋯ T'_{iₙ₋₁,-1}(E_i^{(t)}) ∈ 𝒜U⁺`, where `T'_{j,-1} = T''_{j,1}⁻¹`. -/
theorem list_braid_symm_qDivPow_E_mem_aPlus
    (hfin : ∀ i j, i ≠ j → D.cartanMatrix i j * D.cartanMatrix j i ≤ 3)
    {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
    {ω : List I} {i : I} (hω : cs.IsReduced (ω ++ [i])) (t : ℕ) :
    (ω.map fun j ↦ (braidEquivOfNotRoot R ratFunc_X_not_root j).symm).prod
      (qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i)) ∈ aPlus R := by
  rw [list_braid_symm_apply, braidReversal_qDivPow, braidReversal_E]
  exact braidReversal_mem_aPlus (list_braid_qDivPow_E_mem_aPlus hfin hω t)

end Modified

end LieLean.QuantumGroup
