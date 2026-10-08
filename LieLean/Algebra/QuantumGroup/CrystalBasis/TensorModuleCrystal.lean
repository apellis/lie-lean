/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorProductRule
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorIntegrable
import LieLean.Algebra.QuantumGroup.CrystalBasis.Transfer

/-!
# The tensor product rule for crystal bases of integrable `U_q(𝔤)`-modules

Let `(L₁, B₁)`, `(L₂, B₂)` be crystal bases (`QuantumGroup.IsCrystalBase`) of finite-dimensional
integrable `U`-modules `M₁`, `M₂` over a local ring `A` with fraction field `k`, at a non-unit `c`,
and let `ϖ ∈ cA` be an element of the maximal ideal with image `v⁻¹` in `k` (with the library's
coproduct, the natural lattices live at `v = ∞`). Then `L₁ ⊗ L₂` with
`B₁ ⊗ B₂ = {b₁ ⊗ b₂}` is a crystal base of `M₁ ⊗ M₂`
(`QuantumGroup.TensorModule.isCrystalBase_tensor`; [HK] Thm. 4.4.1, there for Kashiwara's
coproduct). At each node the Kashiwara operators act by the tensor product rule of
`QuantumGroup.IntegrableSl2.isCrystalBase_tensor`, after the flip `x ⊗ y ↦ y ⊗ x`
(`QuantumGroup.TensorModule.flip_kashiwaraE`).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
-/

open TensorProduct Pointwise

namespace LieLean.QuantumGroup

/-! ### Classes of pure tensors at one colour -/

namespace IntegrableSl2

namespace IsCrystalBase

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] {V₁ : IntegrableSl2 q M₁} {V₂ : IntegrableSl2 q M₂}
  {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂]
  {L₁ : Submodule A M₁} {L₂ : Submodule A M₂} {c : A}
  {B₁ : Set (L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂))}
  (hB₁ : V₁.IsCrystalBase hq0 hq L₁ c B₁) (hB₂ : V₂.IsCrystalBase hq0 hq L₂ c B₂)
  (hc : ¬IsUnit c)
  [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁] [FiniteDimensional k M₂]

lemma tmul_mem_tensorLattice (x : L₁) (y : L₂) :
    (x : M₁) ⊗ₜ[k] (y : M₂) ∈
      tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A := by
  rw [hB₁.tensorLattice_eq hB₂ hc]
  exact Submodule.subset_span ⟨x, x.2, y, y.2, rfl⟩

omit [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁]
  [FiniteDimensional k M₂] in
/-- `x - x' ∈ cL₁`, `y - y' ∈ cL₂` imply `x ⊗ y - x' ⊗ y' ∈ cN` for any `A`-submodule `N` of
`M₁ ⊗ M₂` containing `L₁ ⊗ L₂`. -/
lemma tmul_sub_tmul_mem_smul {N : Submodule A (M₁ ⊗[k] M₂)}
    (hN : ∀ x ∈ L₁, ∀ y ∈ L₂, x ⊗ₜ[k] y ∈ N) {x x' : M₁} {y y' : M₂} (hx : x ∈ L₁) (hy' : y' ∈ L₂)
    (hxx : x - x' ∈ c • L₁) (hyy : y - y' ∈ c • L₂) :
    x ⊗ₜ[k] y - x' ⊗ₜ[k] y' ∈ c • N := by
  have e : x ⊗ₜ[k] y - x' ⊗ₜ[k] y' = x ⊗ₜ[k] (y - y') + (x - x') ⊗ₜ[k] y' := by
    rw [tmul_sub, sub_tmul]; abel
  rw [e]
  obtain ⟨z, hz, hz'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxx
  obtain ⟨w, hw, hw'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hyy
  rw [← hz', ← hw', ← smul_tmul', ← algebraMap_smul k c w, tmul_smul, algebraMap_smul]
  exact add_mem (Submodule.smul_mem_pointwise_smul _ _ _ (hN x hx w hw))
    (Submodule.smul_mem_pointwise_smul _ _ _ (hN z hz y' hy'))

/-- The crystal base of the tensor product consists of the classes of the `x ⊗ y` with
`[x] ∈ B₁`, `[y] ∈ B₂`. -/
theorem mem_range_tensorVec_iff (β : tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc)
      (hB₁.hvec hc) (hB₂.hvec hc) A ⧸ (Ideal.span {c} • ⊤ : Submodule A
        (tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A))) :
    (β ∈ Set.range fun x ↦ Submodule.Quotient.mk
        (⟨tensorVec V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) x,
          tensorVec_mem V₁ V₂ _ _ _ _ x⟩ :
          tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A)) ↔
      ∃ (x : L₁) (y : L₂), Submodule.Quotient.mk x ∈ B₁ ∧ Submodule.Quotient.mk y ∈ B₂ ∧
        β = Submodule.Quotient.mk ⟨_, hB₁.tmul_mem_tensorLattice hB₂ hc x y⟩ := by
  have hN : ∀ x ∈ L₁, ∀ y ∈ L₂, x ⊗ₜ[k] y ∈
      tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A :=
    fun x hx y hy ↦ hB₁.tmul_mem_tensorLattice hB₂ hc ⟨x, hx⟩ ⟨y, hy⟩
  constructor
  · rintro ⟨⟨s, t⟩, rfl⟩
    refine ⟨⟨_, hB₁.strVec_mem hc s⟩, ⟨_, hB₂.strVec_mem hc t⟩, ?_, ?_, rfl⟩
    · have := hB₁.strCls_mem hc s
      rwa [hB₁.strCls_eq hc s] at this
    · have := hB₂.strCls_mem hc t
      rwa [hB₂.strCls_eq hc t] at this
  · rintro ⟨x, y, hx, hy, rfl⟩
    obtain ⟨s, hs⟩ := hB₁.exists_strCls_eq hc _ hx
    obtain ⟨t, ht⟩ := hB₂.exists_strCls_eq hc _ hy
    rw [hB₁.strCls_eq hc s, mk_eq_mk_iff] at hs
    rw [hB₂.strCls_eq hc t, mk_eq_mk_iff] at ht
    refine ⟨(s, t), ?_⟩
    rw [mk_eq_mk_iff]
    exact tmul_sub_tmul_mem_smul hN (hB₁.strVec_mem hc s) y.2 hs ht

end IsCrystalBase

/-! ### Changing `q` to `q⁻¹` -/

section Inv

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M} {c : A} {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}

lemma quotEquiv_refl (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :
    quotEquiv (LinearEquiv.refl k M) (L := L) (L' := L) (fun _ ↦ Iff.rfl) c b = b := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rfl

/-- A crystal base for `q` is a crystal base for `q⁻¹`. -/
theorem IsCrystalBase.inv (hB : V.IsCrystalBase hq0 hq L c B) :
    V.inv.IsCrystalBase (inv_ne_zero hq0) (inv_pow_ne_one hq) L c B :=
  IsCrystalBase.of_equiv (V := V.inv) (LinearEquiv.refl k M) (fun _ ↦ Iff.rfl) hB
    (fun _ _ ↦ Iff.rfl)
    (fun m ↦ by rw [inv_eTilde]; rfl) (fun m ↦ by rw [inv_fTilde]; rfl)
    (fun b ↦ by rw [quotEquiv_refl])

/-- A crystal base for `q⁻¹` is a crystal base for `q`. -/
theorem IsCrystalBase.of_inv
    (hB : V.inv.IsCrystalBase (inv_ne_zero hq0) (inv_pow_ne_one hq) L c B) :
    V.IsCrystalBase hq0 hq L c B :=
  IsCrystalBase.of_equiv (V := V) (hq0 := hq0) (hq := hq) (LinearEquiv.refl k M)
    (fun _ ↦ Iff.rfl) hB (fun _ _ ↦ Iff.rfl)
    (fun m ↦ by rw [inv_eTilde]; rfl) (fun m ↦ by rw [inv_fTilde]; rfl)
    (fun b ↦ by rw [quotEquiv_refl])

end Inv

end IntegrableSl2

/-! ### Weight components -/

section WeightComponents

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] (hM : IsIntegrable R v M)

/-- Every vector of an integrable module is the finite sum of its weight components. -/
lemma exists_sum_weightSetProj (m : M) :
    ∃ s : Finset (Y →+ ℤ), ∑ Λ ∈ s, weightSetProj hv hM {Λ} m = m ∧
      ∀ Λ, weightSetProj hv hM {Λ} m ∈ weightSpace R v M Λ := by
  classical
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ m).1
    (hM.iSup_weightSpace_eq_top ▸ Submodule.mem_top)
  have hproj : ∀ Λ, weightSetProj hv hM {Λ} m = if Λ ∈ f.support then f Λ else 0 := by
    intro Λ
    rw [← hsum, Finsupp.sum, map_sum]
    simp only [weightSetProj_of_mem hv hM _ (hf _), Set.mem_singleton_iff]
    exact Finset.sum_ite_eq' _ _ _
  refine ⟨f.support, ?_, fun Λ ↦ ?_⟩
  · conv_rhs => rw [← hsum]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun Λ hΛ ↦ by simp [hproj, hΛ]
  · rw [hproj]
    split_ifs
    · exact hf Λ
    · exact zero_mem _

end WeightComponents

/-! ### The crystal base of a tensor product -/

namespace TensorModule

section ModuleA

variable {k : Type*} [Field k] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂]

/-- A commutative ring `A` acts on `M₁ ⊗ M₂` through the first factor (low priority, so that for
`A = k` the original instance is found first). -/
instance (priority := 100) instModuleLeft {A : Type*} [CommSemiring A] [Module A M₁]
    [SMulCommClass k A M₁] :
    Module A (TensorModule k M₁ M₂) :=
  inferInstanceAs (Module A (M₁ ⊗[k] M₂))

instance {A : Type*} [CommSemiring A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁] :
    IsScalarTower A k (TensorModule k M₁ M₂) :=
  inferInstanceAs (IsScalarTower A k (M₁ ⊗[k] M₂))

end ModuleA

variable {k : Type*} [Field k] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂]
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂]

variable (k A) in
/-- The lattice `L₁ ⊗ L₂`: the `A`-span of the `x ⊗ y`, `x ∈ L₁`, `y ∈ L₂`. -/
def lattice (L₁ : Submodule A M₁) (L₂ : Submodule A M₂) : Submodule A (TensorModule k M₁ M₂) :=
  Submodule.span A (Set.image2 (fun x y ↦ mk M₁ M₂ (x ⊗ₜ[k] y)) L₁ L₂)

variable {L₁ : Submodule A M₁} {L₂ : Submodule A M₂}

omit [IsScalarTower A k M₂] in
lemma tmul_mem_lattice {x : M₁} {y : M₂} (hx : x ∈ L₁) (hy : y ∈ L₂) :
    mk M₁ M₂ (x ⊗ₜ[k] y) ∈ lattice k A L₁ L₂ :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

variable (k) {c : A} in
/-- The set `B₁ ⊗ B₂` of the classes of the `x ⊗ y` with `[x] ∈ B₁`, `[y] ∈ B₂`. -/
def base (B₁ : Set (L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)))
    (B₂ : Set (L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂))) :
    Set (lattice k A L₁ L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A (lattice k A L₁ L₂))) :=
  {b | ∃ (x : L₁) (y : L₂), Submodule.Quotient.mk x ∈ B₁ ∧ Submodule.Quotient.mk y ∈ B₂ ∧
    b = Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k) x.2 y.2⟩}

/-- Under the flip, `L₁ ⊗ L₂` is the span of the `y ⊗ x`. -/
lemma mem_lattice_iff (m : TensorModule k M₁ M₂) :
    m ∈ lattice k A L₁ L₂ ↔
      flip M₁ M₂ m ∈ Submodule.span A (Set.image2 (fun y x ↦ y ⊗ₜ[k] x) L₂ L₁) := by
  let φ : TensorModule k M₁ M₂ ≃ₗ[A] M₂ ⊗[k] M₁ := (flip M₁ M₂).restrictScalars A
  have h : (lattice k A L₁ L₂).map φ.toLinearMap =
      Submodule.span A (Set.image2 (fun y x ↦ y ⊗ₜ[k] x) L₂ L₁) := by
    rw [lattice, Submodule.map_span, Set.image_image2, Set.image2_swap]
    rfl
  rw [← h, Submodule.mem_map_equiv]
  simp [φ]

/-- `[x ⊗ y]` only depends on the classes `[x]`, `[y]`. -/
lemma mk_tmul_eq {c : A} {x x' : L₁} {y y' : L₂}
    (hx : (Submodule.Quotient.mk x : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)) =
      Submodule.Quotient.mk x')
    (hy : (Submodule.Quotient.mk y : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) =
      Submodule.Quotient.mk y') :
    (Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k) x.2 y.2⟩ :
      lattice k A L₁ L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A (lattice k A L₁ L₂))) =
      Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k) x'.2 y'.2⟩ := by
  rw [IntegrableSl2.mk_eq_mk_iff] at hx hy ⊢
  exact IntegrableSl2.IsCrystalBase.tmul_sub_tmul_mem_smul
    (N := (lattice k A L₁ L₂ : Submodule A (M₁ ⊗[k] M₂)))
    (fun x hx y hy ↦ tmul_mem_lattice hx hy) x.2 y'.2 hx hy

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1}
  [Module (QuantumGroup R v) M₁] [IsScalarTower k (QuantumGroup R v) M₁]
  [Module (QuantumGroup R v) M₂] [IsScalarTower k (QuantumGroup R v) M₂]
  {h₁ : IsIntegrable R v M₁} {h₂ : IsIntegrable R v M₂}

omit [IsScalarTower A k M₂] in
/-- `L₁ ⊗ L₂` is the sum of its intersections with the weight spaces. -/
lemma weightSetProj_mem (hL₁ : ∀ S, ∀ m ∈ L₁, weightSetProj hv h₁ S m ∈ L₁)
    (hL₂ : ∀ S, ∀ m ∈ L₂, weightSetProj hv h₂ S m ∈ L₂) (S : Set (Y →+ ℤ))
    {z : TensorModule k M₁ M₂} (hz : z ∈ lattice k A L₁ L₂) :
    weightSetProj hv (isIntegrable h₁ h₂) S z ∈ lattice k A L₁ L₂ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    beta_reduce
    obtain ⟨s, hs, hsw⟩ := exists_sum_weightSetProj hv h₁ x
    obtain ⟨s', hs', hsw'⟩ := exists_sum_weightSetProj hv h₂ y
    have e : mk M₁ M₂ (x ⊗ₜ[k] y) = ∑ Λ ∈ s, ∑ Λ' ∈ s',
        mk M₁ M₂ (weightSetProj hv h₁ {Λ} x ⊗ₜ[k] weightSetProj hv h₂ {Λ'} y) := by
      conv_lhs => rw [← hs, ← hs']
      simp only [sum_tmul, tmul_sum, map_sum]
      exact Finset.sum_comm
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun Λ _ ↦ ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun Λ' _ ↦ ?_
    rw [weightSetProj_of_mem hv (isIntegrable h₁ h₂) S (tmul_mem_weightSpace (hsw Λ) (hsw' Λ'))]
    split_ifs
    · exact tmul_mem_lattice (hL₁ _ _ hx) (hL₂ _ _ hy)
    · exact zero_mem _
  | zero => simp
  | add z z' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul a z _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a h

section CrystalBase

variable [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁] [FiniteDimensional k M₂]
  {hL₁ : IsCrystalLattice hv h₁ L₁} {hL₂ : IsCrystalLattice hv h₂ L₂} {c : A}
  {B₁ : Set (L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂))}
  (hB₁ : IsCrystalBase hL₁ c B₁) (hB₂ : IsCrystalBase hL₂ c B₂) (hc : ¬IsUnit c)
  {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
  (hϖc : ϖ ∈ Ideal.span {c})
include hB₁ hB₂ hc hϖ hϖv hϖc

/-- At every node, `(L₁ ⊗ L₂, B₁ ⊗ B₂)` is a crystal base of `M₁ ⊗ M₂` as a
`U_{vᵢ}(𝔰𝔩₂)`-module. -/
theorem isCrystalBase_nodeSl2 (i : I) :
    (nodeSl2 R v (TensorModule k M₁ M₂) hv (isIntegrable h₁ h₂) i).IsCrystalBase
      (pow_d_ne_zero i) (pow_d_ne_one hv i) (lattice k A L₁ L₂) c (base k B₁ B₂) := by
  have hB₁i := (hB₁.isCrystalBase_nodeSl2 i).inv
  have hB₂i := (hB₂.isCrystalBase_nodeSl2 i).inv
  have hϖi : ϖ ^ D.d i ∈ IsLocalRing.maximalIdeal A := Ideal.pow_mem_of_mem _ hϖ _ (D.d_pos i)
  have hϖiv : algebraMap A k (ϖ ^ D.d i) = (v ^ D.d i)⁻¹ := by rw [map_pow, hϖv, inv_pow]
  have hϖic : ϖ ^ D.d i ∈ Ideal.span {c} := Ideal.pow_mem_of_mem _ hϖc _ (D.d_pos i)
  have hW := IntegrableSl2.IsCrystalBase.isCrystalBase_tensor hB₂i hB₁i hc hϖi hϖiv hϖic
  have hLflip : ∀ m, m ∈ lattice k A L₁ L₂ ↔ flip M₁ M₂ m ∈
      IntegrableSl2.tensorLattice (nodeSl2 R v M₂ hv h₂ i).inv (nodeSl2 R v M₁ hv h₁ i).inv
        (hB₂i.hwt hc) (hB₁i.hwt hc) (hB₂i.hvec hc) (hB₁i.hvec hc) A := by
    intro m
    rw [hB₂i.tensorLattice_eq hB₁i hc, mem_lattice_iff]
  refine IntegrableSl2.IsCrystalBase.of_inv ?_
  refine IntegrableSl2.IsCrystalBase.of_equiv (flip M₁ M₂) hLflip hW ?_ ?_ ?_ ?_
  · exact IntegrableSl2.mem_wt_iff_of_equiv _ fun n m hm ↦ flip_mem_wt hv h₁ h₂ i hm
  · intro m
    rw [IntegrableSl2.inv_eTilde]
    exact flip_kashiwaraE hv h₁ h₂ i m
  · intro m
    rw [IntegrableSl2.inv_fTilde]
    exact flip_kashiwaraF hv h₁ h₂ i m
  · intro b
    rw [IntegrableSl2.IsCrystalBase.mem_range_tensorVec_iff]
    constructor
    · rintro ⟨x, y, hx, hy, rfl⟩
      exact ⟨y, x, hy, hx, rfl⟩
    · rintro ⟨y, x, hy, hx, h⟩
      refine ⟨x, y, hx, hy, (IntegrableSl2.quotEquiv _ hLflip c).injective ?_⟩
      rw [h]
      rfl

/-- **Tensor product rule** ([HK] Thm. 4.4.1): if `(L₁, B₁)`, `(L₂, B₂)` are crystal bases of
finite-dimensional integrable `U`-modules over a local ring `A` with fraction field `k`, at a
non-unit `c`, and `ϖ ∈ cA` lies in the maximal ideal and maps to `v⁻¹`, then
`(L₁ ⊗ L₂, B₁ ⊗ B₂)` is a crystal base of `M₁ ⊗ M₂` (`I` nonempty). At each node `i` the
Kashiwara operators act on `B₁ ⊗ B₂` by the tensor product rule for `B₂ ⊗ B₁` at `vᵢ⁻¹`
(`TensorModule.flip_kashiwaraE`, `IntegrableSl2.fTilde_tensorVec_sub`). [HK] use Kashiwara's
coproduct and lattices at `q = 0`; with the library's coproduct the factors are exchanged and
the lattices are at `v = ∞`. -/
theorem isCrystalBase_tensor [Nonempty I] :
    ∃ hL : IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂),
      IsCrystalBase hL c (base k B₁ B₂) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hN := fun i ↦ isCrystalBase_nodeSl2 hB₁ hB₂ hc hϖ hϖv hϖc i
  let hL : IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂) :=
    { span_eq_top := (hN i₀).span_eq_top
      free := (hN i₀).free
      weightSetProj_mem := fun S m hm ↦
        weightSetProj_mem hL₁.weightSetProj_mem hL₂.weightSetProj_mem S hm
      kashiwaraE_mem := fun i m hm ↦ (hN i).isKashiwaraStable.eTilde_mem m hm
      kashiwaraF_mem := fun i m hm ↦ (hN i).isKashiwaraStable.fTilde_mem m hm }
  refine ⟨hL,
    { linearIndependent := (hN i₀).linearIndependent
      span_eq_top := (hN i₀).span_quot_eq_top
      exists_weight := ?_
      eQ_mem := fun i ↦ (hN i).eQ_mem
      fQ_mem := fun i ↦ (hN i).fQ_mem
      fQ_eq_iff := fun i ↦ (hN i).fQ_eq_iff }⟩
  rintro b ⟨x, y, hx, hy, rfl⟩
  obtain ⟨Λ, x', hx', hxx⟩ := hB₁.exists_weight _ hx
  obtain ⟨Λ', y', hy', hyy⟩ := hB₂.exists_weight _ hy
  exact ⟨Λ + Λ', ⟨_, tmul_mem_lattice x'.2 y'.2⟩, tmul_mem_weightSpace hx' hy',
    mk_tmul_eq hxx hyy⟩

end CrystalBase

end TensorModule

end LieLean.QuantumGroup
