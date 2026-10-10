/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.RootVectors

/-!
# The triangular basis of `U̇`

**[Lus] 23.2.1 (b)**: if `(bᵢ)` is a basis of `U⁻` and `(b'ⱼ)` a basis of `U⁺`, both consisting
of weight vectors, then the elements `bᵢ 1_λ b'ⱼ` (`λ ∈ X`) form a basis of `U̇`
(`Modified.triangularBasis`). Lusztig takes `bᵢ = b⁻`, `b'ⱼ = b'⁺` for `b, b'` in a basis `B` of
`f`; here the two bases are arbitrary. `bᵢ 1_λ b'ⱼ = π_{λ-|bᵢ|, λ-|b'ⱼ|}(bᵢ b'ⱼ)`.

The proof of linear independence uses the maps `Φ_ζ : U̇ → U⁻ ⊗ U⁺`, `π_{λ',ζ}(y⁻ x⁺) ↦ y⁻ ⊗ x⁺`,
obtained from the triangular decomposition of `U` (`Modified.Phi`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.2.1.
-/

open LieLean Finset TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-! ### The map `Φ_ζ : U → U⁻ ⊗ U⁺` -/

section Phi

lemma twistAd_mem_plus (ζ : Y →+ ℤ) (g : AddMonoidAlgebra k Y) {x : QuantumGroup R v}
    (hx : x ∈ Algebra.adjoin k (Set.range (E R v))) :
    twistAd R v ζ g x ∈ Algebra.adjoin k (Set.range (E R v)) := by
  induction g using AddMonoidAlgebra.induction_on with
  | of μ =>
    rw [AddMonoidAlgebra.of_apply, twistAd_single]
    exact Subalgebra.smul_mem _ (adK_mem_plus _ hx) _
  | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | smul c a ha => rw [map_smul, LinearMap.smul_apply]; exact Subalgebra.smul_mem _ ha c

variable (R) in
/-- `g ⊗ x ↦ (e^μ ↦ v^{⟨μ,ζ⟩} Ad(K_μ))(g)(x)`, `k[Y] ⊗ U⁺ → U⁺`. -/
def phiPlus (ζ : Y →+ ℤ) :
    AddMonoidAlgebra k Y ⊗[k] Algebra.adjoin k (Set.range (E R v)) →ₗ[k]
      Algebra.adjoin k (Set.range (E R v)) :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun (g : AddMonoidAlgebra k Y) (x : Algebra.adjoin k (Set.range (E R v))) ↦
      (⟨twistAd R v ζ g x, twistAd_mem_plus ζ g x.2⟩ : Algebra.adjoin k (Set.range (E R v))))
    (fun g g' x ↦ by ext; simp) (fun c g x ↦ by ext; simp)
    (fun g x x' ↦ by ext; simp) (fun c g x ↦ by ext; simp)

include hv in
variable (R) in
/-- **The map `Φ_ζ : U → U⁻ ⊗ U⁺`**, `y⁻ K_μ x⁺ ↦ y⁻ ⊗ v^{⟨μ,ζ⟩} K_μ x⁺ K_{-μ}`. -/
def PhiU (ζ : Y →+ ℤ) :
    QuantumGroup R v →ₗ[k]
      Algebra.adjoin k (Set.range (F R v)) ⊗[k] Algebra.adjoin k (Set.range (E R v)) :=
  TensorProduct.map LinearMap.id (phiPlus R ζ) ∘ₗ
    (triangularMultiplicationEquiv R v hv).symm.toLinearMap

lemma PhiU_apply (ζ : Y →+ ℤ) (y : Algebra.adjoin k (Set.range (F R v)))
    (g : AddMonoidAlgebra k Y) (x : Algebra.adjoin k (Set.range (E R v))) :
    PhiU R hv ζ ((y : QuantumGroup R v) * zeroHom R v g * x) =
      y ⊗ₜ (⟨twistAd R v ζ g x, twistAd_mem_plus ζ g x.2⟩ :
        Algebra.adjoin k (Set.range (E R v))) := by
  rw [← triangularMultiplicationEquiv_tmul R v hv, PhiU, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  simp [phiPlus]

lemma PhiU_mul_plus (ζ : Y →+ ℤ) (y : Algebra.adjoin k (Set.range (F R v)))
    (x : Algebra.adjoin k (Set.range (E R v))) :
    PhiU R hv ζ ((y : QuantumGroup R v) * x) = y ⊗ₜ x := by
  have h := PhiU_apply hv ζ y 1 x
  rw [map_one, mul_one] at h
  rw [h]
  congr 1
  ext
  simp

lemma PhiU_mul_K (ζ : Y →+ ℤ) (u : QuantumGroup R v) (ν : Y) :
    PhiU R hv ζ (u * K R v ν) = v ^ ζ ν • PhiU R hv ζ u := by
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
        rw [e, PhiU_apply, PhiU_apply, ← tmul_smul]
        congr 1
        ext
        simp only [AddMonoidAlgebra.of_apply, toAdd_ofAdd, twistAd_single, Subalgebra.coe_smul]
        rw [adK_add, ← adK_add ν (-ν), add_neg_cancel, adK_zero]
        simp only [smul_smul, one_mul, map_add, zpow_add₀ (NeZero.ne v)]
        congr 1
        ring
      | add a b ha hb =>
        rw [add_tmul, tmul_add, map_add, add_mul, map_add, ha, hb, map_add, smul_add]
      | smul c a ha =>
        rw [← smul_tmul', tmul_smul, map_smul, smul_mul_assoc, map_smul, ha, map_smul, smul_comm]

lemma PhiU_modRel {L ζ : Y →+ ℤ} {x : QuantumGroup R v} (hx : x ∈ modRel R v L ζ) :
    PhiU R hv ζ x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · rw [sub_mul, map_sub, hu μ, map_smul, PhiU_mul_K, smul_smul, ← zpow_add₀ (NeZero.ne v),
        AddMonoidHom.sub_apply, sub_add_cancel, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, map_smul, sub_self]
    · rw [mul_sub, map_sub, PhiU_mul_K, ← Algebra.commutes, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, map_smul, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

end Phi

namespace Modified

attribute [local instance] decEqIdx

open scoped Classical in
include hv in
variable (R) in
/-- `Φ_ζ` on the component `ₗU_λ''`: induced by `Φ_ζ` if `λ'' = ζ`, zero otherwise. -/
def phiComp (ζ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Comp R v p →ₗ[k]
      Algebra.adjoin k (Set.range (F R v)) ⊗[k] Algebra.adjoin k (Set.range (E R v)) :=
  if h : p.2 = ζ then
    Submodule.liftQ _ (PhiU R hv ζ ∘ₗ (adWeightSpace R v (p.1 - p.2)).subtype) fun x hx ↦
      LinearMap.mem_ker.2 (by
        have hx' : x.1 ∈ modRel R v p.1 p.2 := hx
        subst h
        exact PhiU_modRel hv hx')
  else 0

include hv in
variable (R) in
/-- **The map `Φ_ζ : U̇ → U⁻ ⊗ U⁺`**, `π_{λ',ζ}(y⁻ x⁺) ↦ y⁻ ⊗ x⁺`, zero on the components
`ₗU_λ''` with `λ'' ≠ ζ`. -/
def Phi (ζ : Y →+ ℤ) :
    Modified R v →ₗ[k]
      Algebra.adjoin k (Set.range (F R v)) ⊗[k] Algebra.adjoin k (Set.range (E R v)) :=
  DirectSum.toModule k _ _ (phiComp R hv ζ)

open scoped Classical in
lemma Phi_elt (ζ L l : Y →+ ℤ) {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v (L - l)) :
    Phi R hv ζ (elt L l u hu) = if l = ζ then PhiU R hv ζ u else 0 := by
  rw [Phi, elt, DirectSum.toModule_lof]
  by_cases h : l = ζ
  · subst h
    simp only [phiComp, Comp.mk, ↓reduceDIte, ↓reduceIte]
    rfl
  · simp [phiComp, h]

/-! ### The triangular basis of `U̇` ([Lus] 23.2.1) -/

section Basis

variable {ι κ : Type*} (bm : Module.Basis ι k (Algebra.adjoin k (Set.range (F R v))))
  (bp : Module.Basis κ k (Algebra.adjoin k (Set.range (E R v)))) (wm : ι → Y →+ ℤ)
  (wp : κ → Y →+ ℤ) (hm : ∀ i, (bm i : QuantumGroup R v) ∈ adWeightSpace R v (-wm i))
  (hp : ∀ j, (bp j : QuantumGroup R v) ∈ adWeightSpace R v (wp j))

include hm hp in
lemma bm_mul_bp_mem (i : ι) (l : Y →+ ℤ) (j : κ) :
    (bm i : QuantumGroup R v) * bp j ∈ adWeightSpace R v ((l - wm i) - (l - wp j)) := by
  have := mul_mem_adWeightSpace (hm i) (hp j)
  convert this using 2
  abel

/-- The elements `bᵢ 1_λ b'ⱼ = π_{λ-|bᵢ|, λ-|b'ⱼ|}(bᵢ b'ⱼ)` of `U̇`. -/
def triFun (t : ι × (Y →+ ℤ) × κ) : Modified R v :=
  elt (t.2.1 - wm t.1) (t.2.1 - wp t.2.2) _ (bm_mul_bp_mem bm bp wm wp hm hp t.1 t.2.1 t.2.2)

include hv in
theorem linearIndependent_triFun : LinearIndependent k (triFun bm bp wm wp hm hp) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg t0 ht0
  obtain ⟨i0, l0, j0⟩ := t0
  let ℓ : Modified R v →ₗ[k] k :=
    Finsupp.lapply (i0, j0) ∘ₗ (bm.tensorProduct bp).repr.toLinearMap ∘ₗ
      Phi R hv (l0 - wp j0)
  have hℓ : ∀ t, ℓ (triFun bm bp wm wp hm hp t) = if t = (i0, l0, j0) then 1 else 0 := by
    rintro ⟨i, l, j⟩
    simp only [ℓ, LinearMap.comp_apply, triFun, Phi_elt, LinearEquiv.coe_coe]
    by_cases h : l - wp j = l0 - wp j0
    · simp only [h, ↓reduceIte]
      rw [PhiU_mul_plus]
      have e : (bm.tensorProduct bp).repr (bm i ⊗ₜ bp j) = Finsupp.single (i, j) 1 := by
        rw [← Module.Basis.tensorProduct_apply, Module.Basis.repr_self]
      rw [e, Finsupp.lapply_apply, Finsupp.single_apply]
      by_cases hij : (i, j) = (i0, j0)
      · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hij
        have : l = l0 := by simpa using h
        subst this
        simp
      · have hne : (i, l, j) ≠ (i0, l0, j0) := by
          rintro ⟨⟩
          exact hij rfl
        simp [hij, hne]
    · have hne : (i, l, j) ≠ (i0, l0, j0) := by
        rintro ⟨⟩
        exact h rfl
      simp [h, hne]
  have := congrArg ℓ hg
  rw [map_sum, map_zero] at this
  simp only [map_smul, hℓ, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  simpa [ht0] using this

include hm hp in
lemma fullBasis_mem (t : ι × Y × κ) :
    ((bm.tensorProduct ((AddMonoidAlgebra.basis Y k).tensorProduct bp)).map
      (triangularMultiplicationEquiv R v hv) t) ∈ adWeightSpace R v (wp t.2.2 - wm t.1) := by
  have e : ((bm.tensorProduct ((AddMonoidAlgebra.basis Y k).tensorProduct bp)).map
      (triangularMultiplicationEquiv R v hv) t) = bm t.1 * K R v t.2.1 * bp t.2.2 := by
    obtain ⟨i, μ, j⟩ := t
    rw [Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
      Module.Basis.tensorProduct_apply, triangularMultiplicationEquiv_tmul,
      AddMonoidAlgebra.basis_apply, zeroHom_single]
  rw [e, sub_eq_neg_add]
  simpa using mul_mem_adWeightSpace (mul_mem_adWeightSpace (hm t.1) (K_mem_adWeightSpace t.2.1))
    (hp t.2.2)

include hv in
theorem span_triFun : Submodule.span k (Set.range (triFun bm bp wm wp hm hp)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  induction x using Modified.induction_on with
  | h0 => exact zero_mem _
  | hadd x y hx hy => exact add_mem hx hy
  | helt L l u hu =>
    set FB := (bm.tensorProduct ((AddMonoidAlgebra.basis Y k).tensorProduct bp)).map
      (triangularMultiplicationEquiv R v hv)
    have hFB : ∀ t, FB t = bm t.1 * K R v t.2.1 * bp t.2.2 := fun t ↦ by
      obtain ⟨i, μ, j⟩ := t
      rw [Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
        Module.Basis.tensorProduct_apply, triangularMultiplicationEquiv_tmul,
        AddMonoidAlgebra.basis_apply, zeroHom_single]
    set S := (FB.repr u).support
    let f : ι × Y × κ → QuantumGroup R v := fun t ↦
      if wp t.2.2 - wm t.1 = L - l then FB.repr u t • FB t else 0
    have hf : ∀ t, f t ∈ adWeightSpace R v (L - l) := fun t ↦ by
      simp only [f]
      split_ifs with h
      · exact Submodule.smul_mem _ _ (h ▸ fullBasis_mem hv bm bp wm wp hm hp t)
      · exact zero_mem _
    have hu' : u = ∑ t ∈ S, f t := by
      have hsum : u = ∑ t ∈ S, FB.repr u t • FB t := by
        conv_lhs => rw [← FB.linearCombination_repr u]
        rfl
      have hrest : u - ∑ t ∈ S, f t ∈ otherWeights R v (L - l) := by
        have e : u - ∑ t ∈ S, f t = ∑ t ∈ S, (FB.repr u t • FB t - f t) := by
          rw [sum_sub_distrib, ← hsum]
        rw [e]
        refine Submodule.sum_mem _ fun t _ ↦ ?_
        simp only [f]
        split_ifs with h
        · rw [sub_self]; exact zero_mem _
        · rw [sub_zero]
          exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem h
            (fullBasis_mem hv bm bp wm wp hm hp t)))
      have hin : u - ∑ t ∈ S, f t ∈ adWeightSpace R v (L - l) :=
        sub_mem hu (Submodule.sum_mem _ fun t _ ↦ hf t)
      have h0 : u - ∑ t ∈ S, f t = 0 := by
        have hmem : u - ∑ t ∈ S, f t ∈ adWeightSpace R v (L - l) ⊓ otherWeights R v (L - l) :=
          ⟨hin, hrest⟩
        rw [inf_otherWeights hv (L - l)] at hmem
        exact (Submodule.mem_bot k).1 hmem
      exact (sub_eq_zero.1 h0)
    rw [elt_congr hu' hu (Submodule.sum_mem _ fun t _ ↦ hf t), elt_sum S f hf]
    refine Submodule.sum_mem _ fun t _ ↦ ?_
    by_cases h : wp t.2.2 - wm t.1 = L - l
    · have e : elt L l (f t) (hf t) = (FB.repr u t * v ^ (wp t.2.2) t.2.1 *
          v ^ (l t.2.1)) • triFun bm bp wm wp hm hp (t.1, l + wp t.2.2, t.2.2) := by
        have hK : (bm t.1 : QuantumGroup R v) * K R v t.2.1 * bp t.2.2 =
            v ^ (wp t.2.2) t.2.1 • ((bm t.1 : QuantumGroup R v) * bp t.2.2 * K R v t.2.1) := by
          rw [mul_assoc, hp t.2.2 t.2.1, mul_smul_comm, mul_assoc]
        have hmem := bm_mul_bp_mem bm bp wm wp hm hp t.1 (l + wp t.2.2) t.2.2
        have hmem' : (bm t.1 : QuantumGroup R v) * bp t.2.2 ∈ adWeightSpace R v (L - l) := by
          convert hmem using 2; rw [← h]; abel
        have hmemK : (bm t.1 : QuantumGroup R v) * bp t.2.2 * K R v t.2.1 ∈
            adWeightSpace R v (L - l) := by
          simpa using mul_mem_adWeightSpace hmem' (K_mem_adWeightSpace t.2.1)
        have e1 : f t = (FB.repr u t * v ^ (wp t.2.2) t.2.1) •
            ((bm t.1 : QuantumGroup R v) * bp t.2.2 * K R v t.2.1) := by
          simp only [f, h, ↓reduceIte, hFB, hK, smul_smul]
        rw [elt_congr e1 (hf t) (Submodule.smul_mem _ _ hmemK), elt_smul _ _ _ hmemK,
          elt_mul_K _ _ _ hmem', smul_smul, triFun]
        congr 1
        refine elt_index ?_ ?_ rfl _ _
        · change L = l + wp t.2.2 - wm t.1
          rw [add_sub_assoc, h]; abel
        · change l = l + wp t.2.2 - wp t.2.2
          abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · simp only [f, h, ↓reduceIte]
      rw [elt_eq_zero _ (zero_mem _)]
      exact zero_mem _

include hv in
/-- **The triangular basis of `U̇`** ([Lus] 23.2.1 (b)): for bases `(bᵢ)` of `U⁻` and `(b'ⱼ)` of
`U⁺` consisting of weight vectors (`bᵢ ∈ U_{-|bᵢ|}`, `b'ⱼ ∈ U_{|b'ⱼ|}`), the elements
`bᵢ 1_λ b'ⱼ = π_{λ-|bᵢ|, λ-|b'ⱼ|}(bᵢ b'ⱼ)`, `λ ∈ X`, form a basis of `U̇` (`v ≠ 0` not a root of
unity; Lusztig: over `ℚ(v)`). -/
def triangularBasis : Module.Basis (ι × (Y →+ ℤ) × κ) k (Modified R v) :=
  Module.Basis.mk (linearIndependent_triFun hv bm bp wm wp hm hp)
    (span_triFun hv bm bp wm wp hm hp).ge

lemma triangularBasis_apply (t : ι × (Y →+ ℤ) × κ) :
    triangularBasis hv bm bp wm wp hm hp t = triFun bm bp wm wp hm hp t :=
  Module.Basis.mk_apply _ _ _

end Basis

end Modified

end LieLean.QuantumGroup
