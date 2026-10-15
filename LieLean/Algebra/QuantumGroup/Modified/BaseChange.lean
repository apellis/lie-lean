/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BaseChange
import LieLean.Algebra.QuantumGroup.Modified.Form
import LieLean.Algebra.QuantumGroup.Modified.TriangularBasis
import LieLean.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Base change of the modified quantum group and of its bilinear form

For a field extension `L / K` and `v ∈ K` with `v ≠ 0` not a root of unity, the maps
`π_{λ',λ''}(u) ↦ π_{λ',λ''}(u)` induce an isomorphism of `L`-vector spaces
`L ⊗_K U̇_K(v) ≅ U̇_L(v)` (`Modified.baseChangeEquiv`), compatible with the product, the
idempotents `1_λ` and the left action of `U`. Under this isomorphism Lusztig's form on `U̇_L`
([Lus] 26.1.2) is the base change of the form on `U̇_K` (`Modified.form_baseChangeEquiv`); hence
nondegeneracy of the form over `K` implies nondegeneracy over `L`
(`Modified.form_nondegenerate_of_baseChange`). In particular, nondegeneracy over `ℚ(v)` implies
nondegeneracy over every field of characteristic zero at every parameter transcendental over `ℚ`
(`Modified.form_nondegenerate_of_transcendental`), e.g. at `X⁻¹` and `(tX)⁻¹`, `t² = -1`, in an
algebraic closure of `ℚ(X)`.

The isomorphism is proved with the triangular bases of [Lus] 23.2.1 (b): bases of `U^±_K`
consisting of weight vectors map to bases of `U^±_L`. The comparison of the forms uses the
uniqueness in [Lus] 26.1.2 (`Modified.eq_form`).

## Main definitions

* `QuantumGroup.Modified.toBaseChange`: the semilinear map `U̇_K → U̇_L`.
* `QuantumGroup.Modified.baseChangeEquiv`: the `L`-linear isomorphism `L ⊗[K] U̇_K ≃ U̇_L`.

## Main results

* `QuantumGroup.Modified.toBaseChange_mul`, `toBaseChange_one`, `toBaseChange_leftAct`.
* `QuantumGroup.Modified.form_toBaseChange`: `(x, y)_L = (x, y)_K` for `x, y ∈ U̇_K`.
* `QuantumGroup.Modified.form_baseChangeEquiv`: the form on `U̇_L` is the base change of the
  form on `U̇_K`.
* `QuantumGroup.Modified.form_nondegenerate_of_baseChange`: nondegeneracy over `K` implies
  nondegeneracy over `L`, at any `w ∈ L` equal to the image of `v`.
* `QuantumGroup.Modified.formFunctional_toBaseChange`: compatibility of `P_ζ` with base change.
* `QuantumGroup.Modified.form_nondegenerate_of_transcendental`: transfer from `ℚ(v)` to any
  transcendental parameter; `QuantumGroup.transcendental_inv_X`,
  `QuantumGroup.transcendental_inv_mul_X`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1, 23.2.1, 26.1.2.
-/

noncomputable section

open TensorProduct

namespace LieLean.QuantumGroup

variable {k L I Y : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

theorem toBaseChange_mem_modRel [NeZero v] {l₁ l₂ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ modRel R v l₁ l₂) :
    toBaseChange (L := L) R v x ∈ modRel R (algebraMap k L v) l₁ l₂ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    refine Submodule.subset_span ?_
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · exact Or.inl ⟨μ, _, toBaseChange_mem_adWeightSpace hu, by simp⟩
    · exact Or.inr ⟨μ, _, toBaseChange_mem_adWeightSpace hu, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [toBaseChange_smul]; exact Submodule.smul_mem _ _ hx

theorem not_root_algebraMap (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    ∀ n : ℕ, 0 < n → algebraMap k L v ^ n ≠ 1 := fun n hn h ↦
  hv n hn ((algebraMap k L).injective (by rw [map_pow, h, map_one]))

/-! ### Bases of `U^±` consisting of weight vectors -/

section WeightBasis

variable [NeZero v]

omit [Algebra k L] in
theorem list_prod_mem_adWeightSpace {G : I → QuantumGroup R v} {c : I → Y →+ ℤ}
    (hG : ∀ i, G i ∈ adWeightSpace R v (c i)) (w : List I) :
    (w.map G).prod ∈ adWeightSpace R v (w.map c).sum := by
  induction w with
  | nil => simpa using one_mem_adWeightSpace
  | cons i w ih => simpa using mul_mem_adWeightSpace (hG i) ih

omit [Algebra k L] [NeZero v] in
theorem span_list_prod_eq_adjoin (G : I → QuantumGroup R v) :
    Submodule.span k (Set.range fun w : List I ↦ (w.map G).prod) =
      (Algebra.adjoin k (Set.range G)).toSubmodule := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨w, rfl⟩
    exact Subalgebra.list_prod_mem _ fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact Algebra.subset_adjoin ⟨i, rfl⟩
  · rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have key : ∀ l : List (QuantumGroup R v), (∀ y ∈ l, y ∈ Set.range G) →
        ∃ w : List I, w.map G = l := by
      intro l hl
      induction l with
      | nil => exact ⟨[], rfl⟩
      | cons a l ih =>
        obtain ⟨i, rfl⟩ := hl a List.mem_cons_self
        obtain ⟨w, hw⟩ := ih fun b hb ↦ hl b (List.mem_cons_of_mem _ hb)
        exact ⟨i :: w, by simp [hw]⟩
    obtain ⟨w, rfl⟩ := key l hl
    exact Submodule.subset_span ⟨w, rfl⟩

omit [Algebra k L] in
/-- The subalgebra generated by elements `Gᵢ` of weights `cᵢ` has a basis of weight vectors. -/
theorem exists_basis_adjoin_adWeightSpace {G : I → QuantumGroup R v} {c : I → Y →+ ℤ}
    (hG : ∀ i, G i ∈ adWeightSpace R v (c i)) :
    ∃ (t : Set (QuantumGroup R v)) (b : Module.Basis t k (Algebra.adjoin k (Set.range G)))
      (w : t → Y →+ ℤ), ∀ i, (b i : QuantumGroup R v) ∈ adWeightSpace R v (w i) := by
  obtain ⟨t, hts, hspan, hli⟩ :=
    exists_linearIndependent k (Set.range fun w : List I ↦ (w.map G).prod)
  have h : Submodule.span k (Set.range ((↑) : t → QuantumGroup R v)) =
      (Algebra.adjoin k (Set.range G)).toSubmodule := by
    rw [Subtype.range_coe, hspan, span_list_prod_eq_adjoin]
  refine ⟨t, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ h),
    fun x ↦ ((hts x.2).choose.map c).sum, fun x ↦ ?_⟩
  have hb : ((Module.Basis.span hli).map (LinearEquiv.ofEq _ _ h) x : QuantumGroup R v) = x := by
    simp
  rw [hb, ← (hts x.2).choose_spec]
  exact list_prod_mem_adWeightSpace hG _

end WeightBasis

/-- A basis of a subalgebra `S ⊆ U_K` maps to a basis of a subalgebra `S' ⊆ U_L` spanned by the
image of `S`. -/
def basisToBaseChange {ι : Type*} {S : Subalgebra k (QuantumGroup R v)}
    {S' : Subalgebra L (QuantumGroup R (algebraMap k L v))} (b : Module.Basis ι k S)
    (hmem : ∀ x ∈ S, toBaseChange R v x ∈ S')
    (hspan : S'.toSubmodule ≤ Submodule.span L (toBaseChange R v '' S)) :
    Module.Basis ι L S' :=
  Module.Basis.mk (v := fun i ↦ ⟨toBaseChange R v (b i), hmem _ (b i).2⟩)
    (by
      refine LinearIndependent.of_comp S'.val.toLinearMap ?_
      have h1 : LinearIndependent k fun i ↦ (b i : QuantumGroup R v) :=
        b.linearIndependent.map' S.val.toLinearMap
          (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
      have h2 := (Module.Flat.linearIndependent_one_tmul (S := L) h1).map'
        (baseChangeEquiv (L := L) R v).toLinearMap
        (LinearMap.ker_eq_bot.mpr (baseChangeEquiv (L := L) R v).injective)
      convert h2 using 1
      ext i
      simp)
    (by
      rintro ⟨x, hx⟩ -
      have hx' := hspan hx
      have key : toBaseChange (L := L) R v '' S ⊆
          (Submodule.span L (Set.range fun i ↦ toBaseChange (L := L) R v (b i)) : Set _) := by
        rintro _ ⟨y, hy, rfl⟩
        suffices ∀ z : S, toBaseChange (L := L) R v z ∈
            Submodule.span L (Set.range fun i ↦ toBaseChange (L := L) R v (b i)) from this ⟨y, hy⟩
        intro z
        induction b.mem_span z using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨i, rfl⟩ := hz
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add z z' _ _ hz hz' => simpa using add_mem hz hz'
        | smul c z _ hz =>
          simpa [toBaseChange_smul] using Submodule.smul_mem _ (algebraMap k L c) hz
      have hx'' : x ∈ (Submodule.span L (Set.range fun i ↦
          (⟨toBaseChange R v (b i), hmem _ (b i).2⟩ : S'))).map S'.val.toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact Submodule.span_le.mpr key hx'
      obtain ⟨y, hy, hyx⟩ := hx''
      have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
      rw [← hyx']
      exact hy)

theorem toBaseChange_mem_adjoin {G : I → QuantumGroup R v}
    {G' : I → QuantumGroup R (algebraMap k L v)} (hG : ∀ i, toBaseChange R v (G i) = G' i)
    {x : QuantumGroup R v} (hx : x ∈ Algebra.adjoin k (Set.range G)) :
    toBaseChange (L := L) R v x ∈ Algebra.adjoin L (Set.range G') := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hG]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap c => rw [toBaseChange_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem adjoin_le_span_toBaseChange {G : I → QuantumGroup R v}
    {G' : I → QuantumGroup R (algebraMap k L v)} (hG : ∀ i, toBaseChange R v (G i) = G' i) :
    (Algebra.adjoin L (Set.range G')).toSubmodule ≤
      Submodule.span L (toBaseChange R v '' Algebra.adjoin k (Set.range G)) := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨G i, Algebra.subset_adjoin ⟨i, rfl⟩, hG i⟩
  | algebraMap c =>
    have h : algebraMap L (QuantumGroup R (algebraMap k L v)) c = c • toBaseChange R v 1 := by
      rw [map_one, Algebra.algebraMap_eq_smul_one c]
    rw [h]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨1, one_mem _, rfl⟩)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a * b, mul_mem ha hb, map_mul _ _ _⟩

namespace Modified

attribute [local instance] decEqIdx

variable [NeZero v]

omit [NeZero v] in
theorem span_range_quantumGroup_toBaseChange :
    Submodule.span L (Set.range (QuantumGroup.toBaseChange (L := L) R v)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro x -
  obtain ⟨t, rfl⟩ := (QuantumGroup.baseChangeEquiv (L := L) R v).surjective x
  induction t using TensorProduct.inductionOn with
  | tmul c y =>
    rw [QuantumGroup.baseChangeEquiv_tmul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨y, rfl⟩)
  | add a b ha hb => rw [_root_.map_add]; exact add_mem ha hb

variable (L R v) in
/-- `U_{χ,K} → U_{χ,L}`. -/
def adBaseChange (χ : Y →+ ℤ) :
    adWeightSpace R v χ →ₛₗ[algebraMap k L] adWeightSpace R (algebraMap k L v) χ where
  toFun x := ⟨QuantumGroup.toBaseChange R v x, toBaseChange_mem_adWeightSpace x.2⟩
  map_add' _ _ := Subtype.ext (_root_.map_add _ _ _)
  map_smul' c x := Subtype.ext (toBaseChange_smul (L := L) c x.1)

variable (L R v) in
/-- `ₗU_λ''` over `K` to `ₗU_λ''` over `L`. -/
def compBaseChange (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Comp R v p →ₛₗ[algebraMap k L] Comp R (algebraMap k L v) p :=
  Submodule.mapQ _ _ (adBaseChange L R v (p.1 - p.2)) fun _ hx ↦ toBaseChange_mem_modRel hx

variable (L R v) in
/-- The semilinear map `U̇_K → U̇_L`, `π_{λ',λ''}(u) ↦ π_{λ',λ''}(u)`. -/
def toBaseChange : Modified R v →ₛₗ[algebraMap k L] Modified R (algebraMap k L v) where
  toFun := DirectSum.toAddMonoid fun p ↦
    (DirectSum.of (Comp R (algebraMap k L v)) p).comp (compBaseChange L R v p).toAddMonoidHom
  map_add' := _root_.map_add _
  map_smul' c x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      rw [← DirectSum.of_smul, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
      simp [DirectSum.of_smul]
    | add _ _ hx hy => simp only [smul_add, _root_.map_add, hx, hy]

theorem toBaseChange_elt (l₁ l₂ : Y →+ ℤ) {a : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) :
    toBaseChange L R v (elt l₁ l₂ a ha) =
      elt l₁ l₂ (QuantumGroup.toBaseChange R v a) (toBaseChange_mem_adWeightSpace ha) := by
  simp only [toBaseChange, elt, LinearMap.coe_mk, AddHom.coe_mk, DirectSum.lof_eq_of,
    DirectSum.toAddMonoid_of]
  rfl

theorem toBaseChange_one (l : Y →+ ℤ) : toBaseChange L R v (one l) = one l := by
  rw [one, toBaseChange_elt]
  exact elt_index rfl rfl (_root_.map_one _) _ _

theorem toBaseChange_mul (x y : Modified R v) :
    toBaseChange L R v (x * y) = toBaseChange L R v x * toBaseChange L R v y := by
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => rw [add_mul, _root_.map_add, _root_.map_add, add_mul, hx, hx']
  | helt l₁ l₂ a ha =>
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => rw [mul_add, _root_.map_add, _root_.map_add, mul_add, hy, hy']
  | helt l₃ l₄ b hb =>
    by_cases h : l₂ = l₃
    · subst h
      rw [elt_mul_elt, toBaseChange_elt, toBaseChange_elt, toBaseChange_elt, elt_mul_elt]
      exact elt_index rfl rfl (_root_.map_mul _ _ _) _ _
    · rw [elt_mul_elt_of_ne h, toBaseChange_elt, toBaseChange_elt, elt_mul_elt_of_ne h,
        _root_.map_zero]

theorem toBaseChange_leftAct (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (u : QuantumGroup R v)
    (x : Modified R v) :
    toBaseChange L R v (leftAct R v hv u x) =
      leftAct R (algebraMap k L v) (not_root_algebraMap hv) (QuantumGroup.toBaseChange R v u)
        (toBaseChange L R v x) := by
  induction u using induction_adWeightSpace with
  | h0 => simp
  | hadd u u' hu hu' => simp only [_root_.map_add, LinearMap.add_apply, hu, hu']
  | hhom χ u hu =>
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => simp only [_root_.map_add, hx, hx']
  | helt l₁ l₂ a ha =>
    rw [leftAct_elt hv hu, toBaseChange_elt, toBaseChange_elt,
      leftAct_elt _ (toBaseChange_mem_adWeightSpace hu)]
    exact elt_index rfl rfl (_root_.map_mul _ _ _) _ _

/-! ### The isomorphism `L ⊗_K U̇_K ≅ U̇_L` -/

section Equiv

variable (L R v) in
/-- The `K`-module structure on `U̇_L` through `K → L` (used locally). -/
abbrev baseChangeModule : Module k (Modified R (algebraMap k L v)) :=
  Module.compHom _ (algebraMap k L)

attribute [local instance] baseChangeModule

omit [NeZero v] in
theorem baseChange_isScalarTower : IsScalarTower k L (Modified R (algebraMap k L v)) :=
  ⟨fun c l x ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

attribute [local instance] baseChange_isScalarTower

variable (L R v) in
/-- The `L`-linear map `L ⊗[K] U̇_K → U̇_L`, `c ⊗ x ↦ c x`. -/
def baseChangeLinearMap : L ⊗[k] Modified R v →ₗ[L] Modified R (algebraMap k L v) :=
  LinearMap.liftBaseChange L
    { toFun := toBaseChange L R v
      map_add' := _root_.map_add _
      map_smul' := (toBaseChange L R v).map_smulₛₗ }

theorem baseChangeLinearMap_tmul (c : L) (x : Modified R v) :
    baseChangeLinearMap L R v (c ⊗ₜ x) = c • toBaseChange L R v x := rfl

theorem bijective_baseChangeLinearMap (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    Function.Bijective (baseChangeLinearMap L R v) := by
  obtain ⟨tm, bm, wm, hm⟩ :=
    exists_basis_adjoin_adWeightSpace (F_mem_adWeightSpace (R := R) (v := v))
  obtain ⟨tp, bp, wp, hp⟩ :=
    exists_basis_adjoin_adWeightSpace (E_mem_adWeightSpace (R := R) (v := v))
  have hm' : ∀ i, (bm i : QuantumGroup R v) ∈ adWeightSpace R v (-(-wm i)) := by simpa using hm
  let bm' := basisToBaseChange (L := L) bm
    (fun x hx ↦ toBaseChange_mem_adjoin (fun i ↦ toBaseChange_F i) hx)
    (adjoin_le_span_toBaseChange fun i ↦ toBaseChange_F i)
  let bp' := basisToBaseChange (L := L) bp
    (fun x hx ↦ toBaseChange_mem_adjoin (fun i ↦ toBaseChange_E i) hx)
    (adjoin_le_span_toBaseChange fun i ↦ toBaseChange_E i)
  have hbm' : ∀ i, (bm' i : QuantumGroup R (algebraMap k L v)) =
      QuantumGroup.toBaseChange R v (bm i) := fun i ↦ by
    simp [bm', basisToBaseChange]
  have hbp' : ∀ i, (bp' i : QuantumGroup R (algebraMap k L v)) =
      QuantumGroup.toBaseChange R v (bp i) := fun i ↦ by
    simp [bp', basisToBaseChange]
  let Bk := triangularBasis hv bm bp (fun i ↦ -wm i) wp hm' hp
  let BL := triangularBasis (not_root_algebraMap hv) bm' bp' (fun i ↦ -wm i) wp
    (fun i ↦ by rw [hbm']; exact toBaseChange_mem_adWeightSpace (hm' i))
    (fun i ↦ by rw [hbp']; exact toBaseChange_mem_adWeightSpace (hp i))
  have key : ∀ t, baseChangeLinearMap L R v (Algebra.TensorProduct.basis L Bk t) = BL t := by
    intro t
    rw [Algebra.TensorProduct.basis_apply, baseChangeLinearMap_tmul, one_smul,
      triangularBasis_apply, triangularBasis_apply, triFun, triFun, toBaseChange_elt]
    exact elt_index rfl rfl (by rw [_root_.map_mul, hbm', hbp']) _ _
  have he : baseChangeLinearMap L R v =
      ((Algebra.TensorProduct.basis L Bk).equiv BL (Equiv.refl _)).toLinearMap :=
    (Algebra.TensorProduct.basis L Bk).ext fun t ↦ by
      rw [key, LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      rfl
  rw [he]
  exact LinearEquiv.bijective _

variable (L R v) in
/-- **Base change of `U̇`**: `L ⊗_K U̇_K(v) ≅ U̇_L(v)` as `L`-vector spaces,
`c ⊗ π_{λ',λ''}(u) ↦ c π_{λ',λ''}(u)` ([Lus] 23.1.1, 23.2.1 (b)). -/
def baseChangeEquiv (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    L ⊗[k] Modified R v ≃ₗ[L] Modified R (algebraMap k L v) :=
  LinearEquiv.ofBijective _ (bijective_baseChangeLinearMap hv)

theorem baseChangeEquiv_tmul (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (c : L) (x : Modified R v) :
    baseChangeEquiv L R v hv (c ⊗ₜ x) = c • toBaseChange L R v x := rfl

theorem baseChangeEquiv_one_tmul (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (x : Modified R v) :
    baseChangeEquiv L R v hv (1 ⊗ₜ x) = toBaseChange L R v x := by
  rw [baseChangeEquiv_tmul, one_smul]

theorem span_range_toBaseChange (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    Submodule.span L (Set.range (toBaseChange L R v)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro x -
  obtain ⟨t, rfl⟩ := (baseChangeEquiv L R v hv).surjective x
  induction t using TensorProduct.inductionOn with
  | tmul c y =>
    rw [baseChangeEquiv_tmul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨y, rfl⟩)
  | add a b ha hb => rw [_root_.map_add]; exact add_mem ha hb

end Equiv

/-! ### The bilinear form -/

section Form

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

omit [Algebra k L] [DecidableEq I] [NeZero v] in
theorem bilin_eq_of_span {M : Type*} [AddCommGroup M] [Module L M] {s : Set M}
    (hs : Submodule.span L s = ⊤) {f g : M →ₗ[L] M →ₗ[L] L}
    (h : ∀ x ∈ s, ∀ y ∈ s, f x y = g x y) : f = g :=
  LinearMap.ext_on hs fun x hx ↦ LinearMap.ext_on hs fun y hy ↦ h x hx y hy

variable (L R v) in
/-- The base change of the form on `U̇_K`, transported to `U̇_L`. -/
def baseChangeForm : Modified R (algebraMap k L v) →ₗ[L] Modified R (algebraMap k L v) →ₗ[L] L :=
  (LinearMap.BilinForm.baseChange L (form R v hv)).compl₁₂
    (baseChangeEquiv L R v hv).symm.toLinearMap
    (baseChangeEquiv L R v hv).symm.toLinearMap

theorem baseChangeForm_toBaseChange (x y : Modified R v) :
    baseChangeForm L R v hv (toBaseChange L R v x) (toBaseChange L R v y) =
      algebraMap k L (form R v hv x y) := by
  rw [baseChangeForm, LinearMap.compl₁₂_apply, ← baseChangeEquiv_one_tmul hv,
    ← baseChangeEquiv_one_tmul hv]
  simp [LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]

theorem baseChangeForm_eq_form :
    baseChangeForm L R v hv = form R (algebraMap k L v) (not_root_algebraMap hv) := by
  have hs := span_range_toBaseChange (L := L) (R := R) hv
  have hsU := span_range_quantumGroup_toBaseChange (L := L) (R := R) (v := v)
  refine eq_form _ ?_ ?_ ?_
  · intro l₁ l₂ m₁ m₂ h
    have := bilin_eq_of_span hs (f := (baseChangeForm L R v hv).compl₁₂
      ((LinearMap.mulRight L (one l₂)).comp (LinearMap.mulLeft L (one l₁)))
      ((LinearMap.mulRight L (one m₂)).comp (LinearMap.mulLeft L (one m₁)))) (g := 0) ?_
    · exact fun x y ↦ by simpa using congr($this x y)
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, LinearMap.zero_apply]
    rw [← toBaseChange_one, ← toBaseChange_one, ← toBaseChange_one, ← toBaseChange_one,
      ← toBaseChange_mul, ← toBaseChange_mul, ← toBaseChange_mul, ← toBaseChange_mul,
      baseChangeForm_toBaseChange, form_one_mul_mul_one_eq_zero hv h, _root_.map_zero]
  · intro u
    have hu : u ∈ Submodule.span L (Set.range (QuantumGroup.toBaseChange (L := L) R v)) := by
      rw [hsU]; trivial
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨u, rfl⟩ := hu
      have := bilin_eq_of_span hs (f := (baseChangeForm L R v hv).compl₁₂
        (leftAct R _ (not_root_algebraMap hv) (QuantumGroup.toBaseChange R v u)) LinearMap.id)
        (g := (baseChangeForm L R v hv).compl₁₂ LinearMap.id
          (leftAct R _ (not_root_algebraMap hv) (rho R _ (QuantumGroup.toBaseChange R v u)))) ?_
      · exact fun x y ↦ congr($this x y)
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply]
      rw [← toBaseChange_rho, ← toBaseChange_leftAct hv, ← toBaseChange_leftAct hv,
        baseChangeForm_toBaseChange, baseChangeForm_toBaseChange, form_leftAct_left]
    | zero => intro x y; simp
    | add u u' _ _ hu hu' => intro x y; simp [hu, hu']
    | smul c u _ hu => intro x y; simp [hu]
  · intro l
    have hw : Submodule.span L (Set.range (FreeAlgebra.mapCoeffs (algebraMap k L) :
        LusztigF k I → LusztigF L I)) = ⊤ := by
      refine eq_top_iff.mpr (le_trans (FreeAlgebra.wordBasis L I).span_eq.ge ?_)
      refine Submodule.span_mono ?_
      rintro _ ⟨w, rfl⟩
      exact ⟨FreeAlgebra.wordBasis k I w, FreeAlgebra.mapCoeffs_wordBasis _ w⟩
    have := bilin_eq_of_span hw (f := (baseChangeForm L R v hv).compl₁₂
      ((leftAct R _ (not_root_algebraMap hv)).flip (one l) ∘ₗ
        (minusHom R (algebraMap k L v)).toLinearMap)
      ((leftAct R _ (not_root_algebraMap hv)).flip (one l) ∘ₗ
        (minusHom R (algebraMap k L v)).toLinearMap)) (g := LusztigF.form D (algebraMap k L v)) ?_
    · exact fun x y ↦ congr($this x y)
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      AlgHom.toLinearMap_apply]
    rw [← toBaseChange_minusHom, ← toBaseChange_minusHom, ← toBaseChange_one,
      ← toBaseChange_leftAct hv, ← toBaseChange_leftAct hv, baseChangeForm_toBaseChange,
      form_minusHom_leftAct_one, LusztigF.form_mapCoeffs]

/-- **The form on `U̇` commutes with base change**: for `x, y ∈ U̇_K`,
`(x, y)_L = (x, y)_K` ([Lus] 26.1.2). -/
theorem form_toBaseChange (x y : Modified R v) :
    form R (algebraMap k L v) (not_root_algebraMap hv) (toBaseChange L R v x)
      (toBaseChange L R v y) = algebraMap k L (form R v hv x y) := by
  rw [← baseChangeForm_eq_form hv, baseChangeForm_toBaseChange]

/-- The form on `U̇_L` is the base change of the form on `U̇_K` along `L ⊗_K U̇_K ≅ U̇_L`. -/
theorem form_baseChangeEquiv (x y : L ⊗[k] Modified R v) :
    form R (algebraMap k L v) (not_root_algebraMap hv) (baseChangeEquiv L R v hv x)
      (baseChangeEquiv L R v hv y) = LinearMap.BilinForm.baseChange L (form R v hv) x y := by
  rw [← baseChangeForm_eq_form hv, baseChangeForm, LinearMap.compl₁₂_apply]
  simp

/-- The functionals `P_ζ` of [Lus] 26.1.2 commute with base change. -/
theorem formFunctional_toBaseChange (ζ : Y →+ ℤ) (z : QuantumGroup R v) :
    formFunctional R (algebraMap k L v) (not_root_algebraMap hv) ζ
      (QuantumGroup.toBaseChange R v z) = algebraMap k L (formFunctional R v hv ζ z) := by
  rw [← one_leftAct_one_eq_formFunctional _ (form_leftAct_left _) (form_minusHom_leftAct_one _),
    ← one_leftAct_one_eq_formFunctional hv (form_leftAct_left hv) (form_minusHom_leftAct_one hv),
    ← toBaseChange_one, ← toBaseChange_leftAct hv, form_toBaseChange]

/-- **Transfer of nondegeneracy**: if Lusztig's form on `U̇_K(v)` is nondegenerate, so is the form
on `U̇_L(w)` for every field extension `L / K` and `w ∈ L` the image of `v`. -/
theorem form_nondegenerate_of_baseChange
    (hK : ∀ x : Modified R v, (∀ y, form R v hv x y = 0) → x = 0) {w : L}
    (hw : algebraMap k L v = w) [NeZero w] (hw' : ∀ n : ℕ, 0 < n → w ^ n ≠ 1)
    (x : Modified R w) (hx : ∀ y, form R w hw' x y = 0) : x = 0 := by
  subst hw
  exact LinearMap.BilinForm.eq_zero_of_baseChange_equiv (form R v hv) hK _
    (baseChangeEquiv L R v hv) (fun x y ↦ form_baseChangeEquiv hv x _) hx

end Form

end Modified

/-! ### Specialization of `ℚ(v)` at a transcendental element -/

section RatFunc

theorem nonZeroDivisors_le_comap_aeval {L : Type*} [Field L] [CharZero L] {w : L}
    (hw : Transcendental ℚ w) :
    nonZeroDivisors (Polynomial ℚ) ≤
      (nonZeroDivisors L).comap (Polynomial.aeval w).toRingHom := fun p hp ↦
  mem_nonZeroDivisors_of_ne_zero fun h ↦ hw ⟨p, nonZeroDivisors.ne_zero hp, h⟩

/-- The field embedding `ℚ(v) → L`, `v ↦ w`, for `w` transcendental over `ℚ`. -/
def ratFuncEmbedding {L : Type*} [Field L] [CharZero L] (w : L) (hw : Transcendental ℚ w) :
    RatFunc ℚ →+* L :=
  RatFunc.liftRingHom (Polynomial.aeval w).toRingHom (nonZeroDivisors_le_comap_aeval hw)

theorem ratFuncEmbedding_X {L : Type*} [Field L] [CharZero L] (w : L) (hw : Transcendental ℚ w) :
    ratFuncEmbedding w hw RatFunc.X = w := by
  rw [ratFuncEmbedding, ← RatFunc.algebraMap_X, ← div_one (algebraMap _ (RatFunc ℚ) _),
    ← map_one (algebraMap (Polynomial ℚ) (RatFunc ℚ)), RatFunc.liftRingHom_apply_div]
  simp

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

/-- **Transfer of nondegeneracy from `ℚ(v)`**: if Lusztig's form on `U̇` over `ℚ(v)` is
nondegenerate, so is the form on `U̇` over any field `L` of characteristic zero at any `w ∈ L`
transcendental over `ℚ` (through the embedding `ℚ(v) → L`, `v ↦ w`). -/
theorem Modified.form_nondegenerate_of_transcendental
    (hQ : ∀ x : Modified R (RatFunc.X : RatFunc ℚ),
      (∀ y, Modified.form R _ ratFunc_X_not_root x y = 0) → x = 0)
    {L : Type*} [Field L] [CharZero L] {w : L} (hw : Transcendental ℚ w) [NeZero w]
    (x : Modified R w)
    (hx : ∀ y, Modified.form R w (fun _ hn ↦ LusztigF.pow_ne_one_of_transcendental hw hn) x y = 0) :
    x = 0 := by
  let _ := (ratFuncEmbedding w hw).toAlgebra
  exact Modified.form_nondegenerate_of_baseChange ratFunc_X_not_root hQ
    (ratFuncEmbedding_X w hw) (fun _ hn ↦ LusztigF.pow_ne_one_of_transcendental hw hn) x hx

/-- `X⁻¹` is transcendental over `ℚ` in an algebraic closure of `ℚ(X)`. -/
theorem transcendental_inv_X :
    Transcendental ℚ (algebraMap (RatFunc ℚ) (AlgebraicClosure (RatFunc ℚ)) RatFunc.X)⁻¹ := by
  rw [Transcendental, IsAlgebraic.inv_iff (R := ℚ), ← Transcendental,
    transcendental_algebraMap_iff (algebraMap (RatFunc ℚ) _).injective]
  convert RatFunc.transcendental_X (K := ℚ)
  exact Subsingleton.elim _ _

/-- `(tX)⁻¹` is transcendental over `ℚ` in an algebraic closure of `ℚ(X)`, for `t² = -1`. -/
theorem transcendental_inv_mul_X {t : AlgebraicClosure (RatFunc ℚ)} (ht : t ^ 2 = -1) :
    Transcendental ℚ (t * algebraMap (RatFunc ℚ) (AlgebraicClosure (RatFunc ℚ)) RatFunc.X)⁻¹ := by
  have ht0 : t ≠ 0 := by rintro rfl; norm_num at ht
  have hta : IsAlgebraic ℚ t := ⟨Polynomial.X ^ 2 + 1, fun h ↦ by
    simpa using congr(Polynomial.natDegree $h), by simp [ht]⟩
  intro h
  rw [IsAlgebraic.inv_iff (R := ℚ)] at h
  have := (Subalgebra.algebraicClosure ℚ (AlgebraicClosure (RatFunc ℚ))).mul_mem
    (hta.inv : t⁻¹ ∈ Subalgebra.algebraicClosure ℚ _) (h : _ ∈ Subalgebra.algebraicClosure ℚ _)
  rw [← mul_assoc, inv_mul_cancel₀ ht0, one_mul] at this
  exact transcendental_inv_X (IsAlgebraic.inv_iff (R := ℚ).mpr this)

end RatFunc

end LieLean.QuantumGroup
