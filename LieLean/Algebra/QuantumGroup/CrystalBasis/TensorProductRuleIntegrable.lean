/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorIndependence
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorCrystalEquiv
import LieLean.Algebra.QuantumGroup.CrystalBasis.LocalTensorRule

/-!
# The tensor product rule for crystal bases of arbitrary integrable modules

Let `A ⊆ k` be a local ring with `k = A[ϖ⁻¹]`, where `ϖ` lies in the maximal ideal and maps to
`v⁻¹` (with the library's coproduct, the natural lattices live at `v = ∞`). For crystal bases
`(L₁, B₁)`, `(L₂, B₂)` at `ϖ` of integrable `U`-modules `M₁`, `M₂`, the pair
`(L₁ ⊗ L₂, B₁ ⊗ B₂)` (`TensorModule.lattice`, `TensorModule.base`) is a crystal base of
`M₁ ⊗ M₂` (`TensorModule.isCrystalBase_tensor_integrable`; [HK] Thm. 4.4.1, stated there for
modules in `𝒪_int`), and the Kashiwara operators act on `B₁ ⊗ B₂` by the tensor product rule
(`TensorModule.fQ_tmulL_integrable`, `TensorModule.eQ_tmulL_integrable`). No
finite-dimensionality is assumed (compare `TensorModule.isCrystalBase_tensor`).

## Main results

* `TensorModule.isCrystalLattice_tensor`: `L₁ ⊗ L₂` is a crystal lattice of `M₁ ⊗ M₂`.
* `TensorModule.linearIndependent_base`, `TensorModule.span_base_eq_top`: the classes of the
  `x ⊗ y` (`[x] ∈ B₁`, `[y] ∈ B₂`) form an `A/ϖA`-basis of `(L₁ ⊗ L₂)/ϖ(L₁ ⊗ L₂)`.
* `IsCrystalBase.exists_string`: every `b ∈ B` is the class of `Fᵢ^{(k)} u` with `u ∈ L` an
  `Eᵢ`-primitive weight vector whose class lies in `B` ([HK] Prop. 4.2.11 (3), by weights).
* `TensorModule.fQ_tmulL_integrable`, `TensorModule.eQ_tmulL_integrable`: the tensor product
  rule on `B₁ ⊗ B₂`.
* `TensorModule.isCrystalBase_tensor_integrable`: [HK] Thm. 4.4.1.
* `TensorModule.nonempty_crystalEquiv_integrable`: the crystal of `B₁ ⊗ B₂` is the tensor
  product of the crystals of `B₂` and `B₁` (the factors are exchanged by Lusztig's coproduct).

## Proof

As in [HK]: by [HK] Prop. 4.2.11 every element of `B₁` (`B₂`) at a node `i` is the class of a
vector `Fᵢ^{(k₁)} u` (`Fᵢ^{(k₂)} u'`) with `u`, `u'` primitive, and the local tensor product rule
(`TensorModule.kashiwaraF_tmul_sub_mem`, `TensorModule.kashiwaraE_tmul_sub_mem`) computes
`f̃ᵢ`, `ẽᵢ` on the class of `x ⊗ y` from these strings. [HK] Thm. 4.4.3 is replaced by these
local statements, which hold without finite-dimensionality. Freeness of `L₁ ⊗ L₂` comes from
`A`-bases of `L₁`, `L₂`, which are `k`-bases of `M₁`, `M₂`; linear independence of `B₁ ⊗ B₂`
from the coordinate functionals of `TensorModule.mul_eq_of_tmul_sub_mem`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2,
  §4.4.
-/

open TensorProduct Pointwise Finset

noncomputable section

namespace LieLean.QuantumGroup

/-! ### Freeness and spanning of `L₁ ⊗ L₂` -/

namespace TensorModule

section Free

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra A k]
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module A M₁] [IsScalarTower A k M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A M₂] [IsScalarTower A k M₂]
  {L₁ : Submodule A M₁} {L₂ : Submodule A M₂}

omit [Algebra A k] [IsScalarTower A k M₁] [Module k M₁] in
lemma mem_span_basis {M : Type*} [AddCommGroup M] [Module A M] {L : Submodule A M}
    {κ : Type*} (e : Module.Basis κ A L) {x : M} (hx : x ∈ L) :
    x ∈ Submodule.span A (Set.range fun a ↦ (e a : M)) := by
  have := Submodule.mem_map_of_mem (f := L.subtype) (e.mem_span ⟨x, hx⟩)
  rwa [Submodule.map_span, ← Set.range_comp] at this

/-- `L₁ ⊗ L₂` is spanned over `A` by the `e₁ a ⊗ e₂ b` for `A`-bases `e₁`, `e₂` of `L₁`, `L₂`. -/
lemma lattice_eq_span {κ₁ κ₂ : Type*} (e₁ : Module.Basis κ₁ A L₁)
    (e₂ : Module.Basis κ₂ A L₂) :
    lattice k A L₁ L₂ = Submodule.span A
      (Set.range fun p : κ₁ × κ₂ ↦ mk M₁ M₂ ((e₁ p.1 : M₁) ⊗ₜ[k] (e₂ p.2 : M₂))) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hmk : ∀ (c : A) (z : M₁ ⊗[k] M₂), mk M₁ M₂ (c • z) = c • mk M₁ M₂ z := fun _ _ ↦ rfl
    set S := Submodule.span A
      (Set.range fun p : κ₁ × κ₂ ↦ mk M₁ M₂ ((e₁ p.1 : M₁) ⊗ₜ[k] (e₂ p.2 : M₂)))
    have key : ∀ x ∈ Submodule.span A (Set.range fun a ↦ (e₁ a : M₁)),
        ∀ y ∈ Submodule.span A (Set.range fun a ↦ (e₂ a : M₂)), mk M₁ M₂ (x ⊗ₜ[k] y) ∈ S := by
      intro x hx y hy
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨b, rfl⟩ := hy
          exact Submodule.subset_span ⟨(a, b), rfl⟩
        | zero => simp
        | add y y' _ _ h h' => rw [tmul_add, map_add]; exact add_mem h h'
        | smul c y _ h => rw [tmul_smul, hmk]; exact Submodule.smul_mem _ c h
      | zero => simp
      | add x x' _ _ h h' => rw [add_tmul, map_add]; exact add_mem h h'
      | smul c x _ h => rw [← smul_tmul', hmk]; exact Submodule.smul_mem _ c h
    exact key x (mem_span_basis e₁ hx) y (mem_span_basis e₂ hy)
  · rintro _ ⟨p, rfl⟩
    exact tmul_mem_lattice (e₁ p.1).2 (e₂ p.2).2

variable {ϖ : A} (hϖ0 : algebraMap A k ϖ ≠ 0)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)

include hϖ0 hk in
omit [IsScalarTower A k M₂] in
/-- An `A`-basis of a lattice spanning `M` over `k = A[ϖ⁻¹]` is a `k`-basis of `M`. -/
lemma exists_basis_coe {M : Type*} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower A k M] {L : Submodule A M} (hL : Submodule.span k (L : Set M) = ⊤)
    {κ : Type*} (e : Module.Basis κ A L) :
    ∃ b : Module.Basis κ k M, ∀ a, b a = e a := by
  have hli := linearIndependent_coe_of_basis hϖ0 hk e
  have hsp : ⊤ ≤ Submodule.span k (Set.range fun a ↦ (e a : M)) := by
    rw [← hL, Submodule.span_le]
    intro x hx
    exact Submodule.span_le_restrictScalars A k _ (mem_span_basis e hx)
  exact ⟨Module.Basis.mk hli hsp, fun a ↦ Module.Basis.mk_apply _ _ _⟩

include hϖ0 hk in
/-- `L₁ ⊗ L₂` is a free `A`-module. -/
theorem free_lattice (hinj : Function.Injective (algebraMap A k)) [Module.Free A L₁]
    [Module.Free A L₂] (hL₁ : Submodule.span k (L₁ : Set M₁) = ⊤)
    (hL₂ : Submodule.span k (L₂ : Set M₂) = ⊤) : Module.Free A (lattice k A L₁ L₂) := by
  let e₁ := Module.Free.chooseBasis A L₁
  let e₂ := Module.Free.chooseBasis A L₂
  obtain ⟨b₁, hb₁⟩ := exists_basis_coe hϖ0 hk hL₁ e₁
  obtain ⟨b₂, hb₂⟩ := exists_basis_coe hϖ0 hk hL₂ e₂
  have hli : LinearIndependent k
      (fun p : _ × _ ↦ mk M₁ M₂ ((e₁ p.1 : M₁) ⊗ₜ[k] (e₂ p.2 : M₂))) := by
    have := (b₁.tensorProduct b₂).linearIndependent.map' (mk M₁ M₂).toLinearMap
      (mk M₁ M₂).ker
    have e : (fun p : _ × _ ↦ mk M₁ M₂ ((e₁ p.1 : M₁) ⊗ₜ[k] (e₂ p.2 : M₂))) =
        (mk M₁ M₂).toLinearMap ∘ (b₁.tensorProduct b₂) := by
      funext ⟨a, b⟩
      change _ = mk M₁ M₂ ((b₁.tensorProduct b₂) (a, b))
      rw [Module.Basis.tensorProduct_apply, hb₁, hb₂]
    rw [e]
    exact this
  have hliA := hli.restrict_scalars (R := A) (by
    intro a a' h
    simp only [Algebra.smul_def, mul_one] at h
    exact hinj h)
  have := Module.Free.of_basis (Module.Basis.span hliA)
  exact Module.Free.of_equiv (LinearEquiv.ofEq _ _ (lattice_eq_span e₁ e₂).symm)

omit [IsScalarTower A k M₂] in
/-- `L₁ ⊗ L₂` spans `M₁ ⊗ M₂` over `k`. -/
theorem span_lattice_eq_top (hL₁ : Submodule.span k (L₁ : Set M₁) = ⊤)
    (hL₂ : Submodule.span k (L₂ : Set M₂) = ⊤) :
    Submodule.span k (lattice k A L₁ L₂ : Set (TensorModule k M₁ M₂)) = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  have h : Submodule.span k (Set.image2 (fun x y ↦ x ⊗ₜ[k] y) (L₁ : Set M₁) (L₂ : Set M₂)) =
      (⊤ : Submodule k (M₁ ⊗[k] M₂)) := by
    change Submodule.span k (Set.image2 (fun x y ↦ TensorProduct.mk k M₁ M₂ x y) _ _) = ⊤
    rw [← Submodule.map₂_span_span, hL₁, hL₂, TensorProduct.map₂_mk_top_top_eq_top]
  have hz : (mk M₁ M₂).symm z ∈ Submodule.span k
      (Set.image2 (fun x y ↦ x ⊗ₜ[k] y) (L₁ : Set M₁) (L₂ : Set M₂)) := by
    rw [h]; exact Submodule.mem_top
  refine Submodule.span_mono (R := k) ?_ hz
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact tmul_mem_lattice (k := k) hx hy

section Base

variable {B₁ : Set (L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₂))}

include hϖ0 hk in
/-- The classes `[x ⊗ y]` (`[x] ∈ B₁`, `[y] ∈ B₂`) are linearly independent over `A/ϖA` when `B₁`,
`B₂` are bases of `L₁/ϖL₁`, `L₂/ϖL₂` (our argument, via coordinate functionals). -/
theorem linearIndependent_base (hinj : Function.Injective (algebraMap A k)) [Module.Free A L₁]
    [Module.Free A L₂] (hL₁ : Submodule.span k (L₁ : Set M₁) = ⊤)
    (hL₂ : Submodule.span k (L₂ : Set M₂) = ⊤)
    (hB₁ : LinearIndependent (A ⧸ Ideal.span {ϖ}) (Subtype.val : B₁ → _))
    (hB₁' : Submodule.span (A ⧸ Ideal.span {ϖ}) B₁ = ⊤)
    (hB₂ : LinearIndependent (A ⧸ Ideal.span {ϖ}) (Subtype.val : B₂ → _))
    (hB₂' : Submodule.span (A ⧸ Ideal.span {ϖ}) B₂ = ⊤) :
    LinearIndependent (A ⧸ Ideal.span {ϖ}) (Subtype.val : base k B₁ B₂ → _) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg β₀ hβ₀
  have hrep : ∀ β : base k B₁ B₂, ∃ (x : L₁) (y : L₂), Submodule.Quotient.mk x ∈ B₁ ∧
      Submodule.Quotient.mk y ∈ B₂ ∧
      β.1 = Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k) x.2 y.2⟩ := fun β ↦ β.2
  choose X Y hX hY hXY using hrep
  obtain ⟨p₁, hp₁⟩ := exists_coord hB₁ hB₁' ⟨_, hX β₀⟩
  obtain ⟨p₂, hp₂⟩ := exists_coord hB₂ hB₂' ⟨_, hY β₀⟩
  obtain ⟨f₁, hf₁⟩ := Module.projective_lifting_property (Ideal.span {ϖ}).mkQ p₁
    (Submodule.mkQ_surjective _)
  obtain ⟨f₂, hf₂⟩ := Module.projective_lifting_property (Ideal.span {ϖ}).mkQ p₂
    (Submodule.mkQ_surjective _)
  obtain ⟨F₁, hF₁⟩ := exists_extend hϖ0 hk hL₁ f₁
  obtain ⟨F₂, hF₂⟩ := exists_extend hϖ0 hk hL₂ f₂
  choose g' hg' using fun β ↦ Ideal.Quotient.mk_surjective (g β)
  have hzL : ∑ β ∈ s, g' β • mk M₁ M₂ ((X β : M₁) ⊗ₜ[k] (Y β : M₂)) ∈ lattice k A L₁ L₂ :=
    Submodule.sum_mem _ fun β _ ↦ Submodule.smul_mem _ _ (tmul_mem_lattice (X β).2 (Y β).2)
  have hz : ∑ β ∈ s, g' β • mk M₁ M₂ ((X β : M₁) ⊗ₜ[k] (Y β : M₂)) ∈
      ϖ • lattice k A L₁ L₂ := by
    refine (IntegrableSl2.mk_eq_zero_iff ϖ ⟨_, hzL⟩).1 ?_
    rw [← hg]
    have e : (⟨_, hzL⟩ : lattice k A L₁ L₂) =
        ∑ β ∈ s, g' β • (⟨_, tmul_mem_lattice (k := k) (X β).2 (Y β).2⟩ : lattice k A L₁ L₂) :=
      Subtype.ext (by simp)
    rw [e, ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [hXY β, ← hg' β]
    rfl
  obtain ⟨a, ha, he⟩ := exists_eq_algebraMap_of_mem_smul F₁ F₂
    (fun x hx ↦ ⟨f₁ ⟨x, hx⟩, hF₁ ⟨x, hx⟩⟩) (fun y hy ↦ ⟨f₂ ⟨y, hy⟩, hF₂ ⟨y, hy⟩⟩) hz
  have e : ∀ (x : M₁) (y : M₂), TensorProduct.lift ((LinearMap.mul k k).compl₁₂ F₁ F₂)
      ((mk M₁ M₂).symm (mk M₁ M₂ (x ⊗ₜ[k] y))) = F₁ x * F₂ y := fun x y ↦ by simp
  have hsum : algebraMap A k (∑ β ∈ s, g' β * f₁ (X β) * f₂ (Y β)) = algebraMap A k a := by
    rw [← he, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [← algebraMap_smul k (g' β), map_smul, map_smul, e, smul_eq_mul, hF₁, hF₂, map_mul,
      map_mul, mul_assoc]
  have hs0 : ∑ β ∈ s, g β * p₁ (X β) * p₂ (Y β) = 0 := by
    have h1 := congrArg (Ideal.Quotient.mk (Ideal.span {ϖ})) (hinj hsum)
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [map_mul, map_mul, hg', ← hf₁, ← hf₂]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Ideal.Quotient.mk_eq_mk]
  rw [Finset.sum_eq_single β₀] at hs0
  · rwa [(hp₁ _ (hX β₀)).1 rfl, (hp₂ _ (hY β₀)).1 rfl, mul_one, mul_one] at hs0
  · intro β _ hne
    by_cases h1 : (⟨_, hX β⟩ : B₁) = ⟨_, hX β₀⟩
    · by_cases h2 : (⟨_, hY β⟩ : B₂) = ⟨_, hY β₀⟩
      · exfalso
        apply hne
        apply Subtype.ext
        rw [hXY β, hXY β₀, ← tmulL_mk, ← tmulL_mk, Subtype.mk.inj h1, Subtype.mk.inj h2]
      · rw [(hp₂ _ (hY β)).2 h2, mul_zero]
    · rw [(hp₁ _ (hX β)).2 h1, mul_zero, zero_mul]
  · intro h
    exact absurd hβ₀ h

omit [Algebra A k] [IsScalarTower A k M₁] [IsScalarTower A k M₂] [Module k M₁] in
/-- An `A`-linear map `N → P/ϖP` killing `ϖN` takes values in an `A/ϖA`-submodule `S` as soon as
it does on lifts of a spanning set of `N/ϖN`. -/
lemma mem_of_mk_mem_of_span_eq_top {N P : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] {B : Set (N ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A N))}
    (hB : Submodule.span (A ⧸ Ideal.span {ϖ}) B = ⊤)
    (f : N →ₗ[A] P ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A P)) (hf : ∀ n, f (ϖ • n) = 0)
    (S : Submodule (A ⧸ Ideal.span {ϖ}) (P ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A P)))
    (hS : ∀ n, Submodule.Quotient.mk n ∈ B → f n ∈ S) (n : N) : f n ∈ S := by
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule A N) ≤ LinearMap.ker f := by
    refine Submodule.smul_le.2 fun r hr n _ ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, mul_smul, map_smul, hf, smul_zero]
  let g := (Ideal.span {ϖ} • ⊤ : Submodule A N).liftQ f hle
  have key : ∀ q, g q ∈ S := by
    intro q
    have hq : q ∈ Submodule.span (A ⧸ Ideal.span {ϖ}) B := hB ▸ Submodule.mem_top
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact hS n hq
    | zero => rw [map_zero]; exact S.zero_mem
    | add q q' _ _ h h' => rw [map_add]; exact S.add_mem h h'
    | smul c q _ h =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk n))
      rw [Module.Quotient.mk_smul_mk, Submodule.Quotient.mk_smul, map_smul, ← hp,
        ← Submodule.Quotient.mk_smul, ← Module.Quotient.mk_smul_mk]
      rw [← hp] at h
      exact S.smul_mem _ h
  exact key (Submodule.Quotient.mk n)

/-- The classes `[x ⊗ y]` (`[x] ∈ B₁`, `[y] ∈ B₂`) span `(L₁ ⊗ L₂)/ϖ(L₁ ⊗ L₂)` when `B₁`, `B₂`
span `L₁/ϖL₁`, `L₂/ϖL₂`. -/
theorem span_base_eq_top (hB₁ : Submodule.span (A ⧸ Ideal.span {ϖ}) B₁ = ⊤)
    (hB₂ : Submodule.span (A ⧸ Ideal.span {ϖ}) B₂ = ⊤) :
    Submodule.span (A ⧸ Ideal.span {ϖ}) (base k B₁ B₂) = ⊤ := by
  set S := Submodule.span (A ⧸ Ideal.span {ϖ}) (base k B₁ B₂)
  have hmk : ∀ (c : A) (z : M₁ ⊗[k] M₂), mk M₁ M₂ (c • z) = c • mk M₁ M₂ z := fun _ _ ↦ rfl
  have h0 : ∀ z : lattice k A L₁ L₂,
      (Submodule.Quotient.mk (ϖ • z) : lattice k A L₁ L₂ ⧸
        (Ideal.span {ϖ} • ⊤ : Submodule A (lattice k A L₁ L₂))) = 0 := fun z ↦
    (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top)
  let fR : L₁ → L₂ →ₗ[A] lattice k A L₁ L₂ ⧸
      (Ideal.span {ϖ} • ⊤ : Submodule A (lattice k A L₁ L₂)) := fun x ↦
    { toFun := fun y ↦ Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k) x.2 y.2⟩
      map_add' := fun y y' ↦ by
        rw [← Submodule.Quotient.mk_add]
        congr 1
        exact Subtype.ext (by simp [tmul_add])
      map_smul' := fun a y ↦ by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        refine Subtype.ext ?_
        change mk M₁ M₂ ((x : M₁) ⊗ₜ[k] (a • (y : M₂))) = a • mk M₁ M₂ ((x : M₁) ⊗ₜ[k] (y : M₂))
        rw [tmul_smul, hmk] }
  let fL : L₂ → L₁ →ₗ[A] lattice k A L₁ L₂ ⧸
      (Ideal.span {ϖ} • ⊤ : Submodule A (lattice k A L₁ L₂)) := fun y ↦
    { toFun := fun x ↦ Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k) x.2 y.2⟩
      map_add' := fun x x' ↦ by
        rw [← Submodule.Quotient.mk_add]
        congr 1
        exact Subtype.ext (by simp [add_tmul])
      map_smul' := fun a x ↦ by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1 }
  have hR : ∀ (x : L₁) (y : L₂), fR x (ϖ • y) = 0 := fun x y ↦ by
    rw [LinearMap.map_smul]
    exact h0 _
  have hL : ∀ (y : L₂) (x : L₁), fL y (ϖ • x) = 0 := fun y x ↦ by
    rw [LinearMap.map_smul]
    exact h0 _
  have h1 : ∀ x : L₁, Submodule.Quotient.mk x ∈ B₁ → ∀ y : L₂, fR x y ∈ S := fun x hx ↦
    mem_of_mk_mem_of_span_eq_top hB₂ (fR x) (hR x) S
      (fun y hy ↦ Submodule.subset_span ⟨x, y, hx, hy, rfl⟩)
  have h2 : ∀ (x : L₁) (y : L₂), fR x y ∈ S := fun x y ↦
    mem_of_mk_mem_of_span_eq_top hB₁ (fL y) (hL y) S (fun x hx ↦ h1 x hx y) x
  rw [eq_top_iff]
  rintro q -
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    exact h2 ⟨x, hx⟩ ⟨y, hy⟩
  | zero => exact S.zero_mem
  | add z z' _ _ h h' => exact S.add_mem h h'
  | smul a z _ h => exact S.smul_mem (Ideal.Quotient.mk _ a) h

end Base

end Free

/-! ### `L₁ ⊗ L₂` is a crystal lattice -/

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1}
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]
  {h₁ : IsIntegrable R v M₁} {h₂ : IsIntegrable R v M₂}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂] {L₁ : Submodule A M₁} {L₂ : Submodule A M₂}

omit [IsScalarTower A k M₂] in
/-- An endomorphism mapping every `x ⊗ y` (`x ∈ L₁ ∩ M₁^Λ`, `y ∈ L₂ ∩ M₂^{Λ'}`) into
`L₁ ⊗ L₂` preserves `L₁ ⊗ L₂`, for `L₁`, `L₂` graded. -/
lemma mem_lattice_of_tmul (hL₁ : ∀ S, ∀ m ∈ L₁, weightSetProj hv h₁ S m ∈ L₁)
    (hL₂ : ∀ S, ∀ m ∈ L₂, weightSetProj hv h₂ S m ∈ L₂) (T : Module.End k (TensorModule k M₁ M₂))
    (hT : ∀ (Λ Λ' : Y →+ ℤ) (x : M₁) (y : M₂), x ∈ L₁ → x ∈ weightSpace R v M₁ Λ → y ∈ L₂ →
      y ∈ weightSpace R v M₂ Λ' → T (mk M₁ M₂ (x ⊗ₜ[k] y)) ∈ lattice k A L₁ L₂)
    {z : TensorModule k M₁ M₂} (hz : z ∈ lattice k A L₁ L₂) : T z ∈ lattice k A L₁ L₂ := by
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
    exact Submodule.sum_mem _ fun Λ' _ ↦ hT Λ Λ' _ _ (hL₁ _ _ hx) (hsw Λ) (hL₂ _ _ hy) (hsw' Λ')
  | zero => simp
  | add z z' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul a z _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a h

variable [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hinj : Function.Injective (algebraMap A k))

include hϖ hϖv hk hinj in
/-- `L₁ ⊗ L₂` is a crystal lattice of `M₁ ⊗ M₂` (part of [HK] Thm. 4.4.1). -/
theorem isCrystalLattice_tensor (hL₁ : IsCrystalLattice hv h₁ L₁)
    (hL₂ : IsCrystalLattice hv h₂ L₂) :
    IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂) where
  span_eq_top := span_lattice_eq_top hL₁.span_eq_top hL₂.span_eq_top
  free := by
    have := hL₁.free
    have := hL₂.free
    have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
    exact free_lattice hϖ0 hk hinj hL₁.span_eq_top hL₂.span_eq_top
  weightSetProj_mem S m hm := weightSetProj_mem hL₁.weightSetProj_mem hL₂.weightSetProj_mem S hm
  kashiwaraE_mem i m hm := mem_lattice_of_tmul hL₁.weightSetProj_mem hL₂.weightSetProj_mem _
    (fun _ _ _ _ hx hxw hy hyw ↦ kashiwaraE_tmul_mem hv h₁ h₂ i (hL₁.kashiwaraF_mem i)
      (hL₂.kashiwaraF_mem i) (fun _ y hy _ ↦ hL₁.kashiwaraE_mem i y hy)
      (fun _ y hy _ ↦ hL₂.kashiwaraE_mem i y hy) hϖ hϖv hx hxw hy hyw) hm
  kashiwaraF_mem i m hm := mem_lattice_of_tmul hL₁.weightSetProj_mem hL₂.weightSetProj_mem _
    (fun _ _ _ _ hx hxw hy hyw ↦ kashiwaraF_tmul_mem hv h₁ h₂ i (hL₁.kashiwaraF_mem i)
      (hL₂.kashiwaraF_mem i) (fun _ y hy _ ↦ hL₁.kashiwaraE_mem i y hy)
      (fun _ y hy _ ↦ hL₂.kashiwaraE_mem i y hy) hϖ hϖv hx hxw hy hyw) hm

end TensorModule

/-! ### Strings through the elements of a crystal base -/

section Strings

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] {hM : IsIntegrable R v M}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M} {i : I}

omit [Algebra A k] [IsScalarTower A k M] in
/-- A lattice stable under `ẽᵢ` is stable under its powers. -/
lemma kashiwaraE_pow_mem_of (hE : ∀ y ∈ L, kashiwaraE R v M hv hM i y ∈ L) (m : ℕ) {y : M}
    (hy : y ∈ L) : (kashiwaraE R v M hv hM i ^ m) y ∈ L := by
  induction m with
  | zero => simpa using hy
  | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hE _ ih

/-- `f̃ᵢ^m Fᵢ^{(j)} u = Fᵢ^{(j+m)} u` for `u` primitive. -/
lemma kashiwaraF_pow_dF {p : ℤ} {u : M} (hE : E R v i • u = 0) (hp : u ∈ nodeWt R v M i p)
    (m j : ℕ) :
    (kashiwaraF R v M hv hM i ^ m) ((nodeSl2 R v M hv hM i).dF j u) =
      (nodeSl2 R v M hv hM i).dF (j + m) u := by
  rw [← kashiwaraF_pow_of_primitive hv hM i hE hp j, ← Module.End.mul_apply, ← pow_add,
    add_comm, kashiwaraF_pow_of_primitive hv hM i hE hp]

/-- `ẽᵢ^m Fᵢ^{(j)} u = Fᵢ^{(j-m)} u` for `u` primitive of `⟨i, ·⟩`-weight `a ≥ j ≥ m`. -/
lemma kashiwaraE_pow_dF {a : ℕ} {u : M} (hE : E R v i • u = 0)
    (hp : u ∈ nodeWt R v M i a) {m j : ℕ} (hmj : m ≤ j) (hj : j ≤ a) :
    (kashiwaraE R v M hv hM i ^ m) ((nodeSl2 R v M hv hM i).dF j u) =
      (nodeSl2 R v M hv hM i).dF (j - m) u := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih (by omega)]
    obtain ⟨l, hl⟩ : ∃ l, j - m = l + 1 := ⟨j - m - 1, by omega⟩
    rw [hl, show j - (m + 1) = l by omega]
    exact IntegrableSl2.eTilde_dF_succ (V := nodeSl2 R v M hv hM i) (pow_d_ne_zero i)
      (pow_d_ne_one hv i) hE hp (by omega)

/-- `ẽᵢ^m Fᵢ^{(j)} u = 0` for `u` primitive and `m > j`. -/
lemma kashiwaraE_pow_dF_eq_zero {a : ℕ} {u : M} (hE : E R v i • u = 0)
    (hp : u ∈ nodeWt R v M i a) {m j : ℕ} (hjm : j < m) :
    (kashiwaraE R v M hv hM i ^ m) ((nodeSl2 R v M hv hM i).dF j u) = 0 := by
  by_cases hj : j ≤ a
  · obtain ⟨l, rfl⟩ : ∃ l, m = (l + 1) + j := ⟨m - j - 1, by omega⟩
    rw [pow_add, Module.End.mul_apply, kashiwaraE_pow_dF hE hp le_rfl hj, Nat.sub_self,
      IntegrableSl2.dF_zero, pow_succ, Module.End.mul_apply]
    rw [show kashiwaraE R v M hv hM i u = 0 from
      IntegrableSl2.eTilde_of_primitive (V := nodeSl2 R v M hv hM i) (pow_d_ne_zero i)
        (pow_d_ne_one hv i) hE hp, map_zero]
  · rw [IntegrableSl2.dF_eq_zero_of_primitive (V := nodeSl2 R v M hv hM i) (pow_d_ne_zero i)
      (pow_d_ne_one hv i) hp hE (by omega), map_zero]

/-- `Fᵢ^{(j)} u ∉ c L` for `u ∉ c L` primitive of `⟨i, ·⟩`-weight `a ≥ j`. -/
lemma IsCrystalLattice.dF_notMem_smul (hL : IsCrystalLattice hv hM L) (c : A) {a : ℕ} {u : M}
    (hE : E R v i • u = 0) (hp : u ∈ nodeWt R v M i a) (hu : u ∉ c • L) {j : ℕ} (hj : j ≤ a) :
    (nodeSl2 R v M hv hM i).dF j u ∉ c • L := by
  intro h
  apply hu
  have := kashiwaraE_pow_mem_of ((hL.isKashiwaraStable i).smul c).eTilde_mem j h
  rwa [kashiwaraE_pow_dF hE hp le_rfl hj, Nat.sub_self, IntegrableSl2.dF_zero] at this

variable (hv hM) in
/-- A string representative of `x ∈ L ∩ M^μ` at the node `i`: `x ≡ Fᵢ^{(s)} u` modulo `c L`,
where `u ∈ L ∩ M^{μ + s αᵢ}` is `Eᵢ`-primitive of `⟨i, ·⟩`-weight `a ≥ s` and `u ∉ c L`. -/
structure IsStringRep (L : Submodule A M) (c : A) (i : I) (μ : Y →+ ℤ) (x : M) (s a : ℕ)
    (u : M) : Prop where
  mem : u ∈ L
  mem_weightSpace : u ∈ weightSpace R v M (μ + s • R.root i)
  E_smul : E R v i • u = 0
  coroot : (a : ℤ) = μ (R.coroot i) + 2 * s
  notMem : u ∉ c • L
  le : s ≤ a
  sub_mem : x - (nodeSl2 R v M hv hM i).dF s u ∈ c • L

namespace IsStringRep

variable {c : A} {μ : Y →+ ℤ} {x : M} {s a : ℕ} {u : M}

omit [Algebra A k] [IsScalarTower A k M] in
lemma mem_nodeWt (h : IsStringRep hv hM L c i μ x s a u) : u ∈ nodeWt R v M i a := by
  rw [h.coroot]; exact mem_nodeWt_of_mem_add_nsmul i h.mem_weightSpace

omit [Algebra A k] [IsScalarTower A k M] in
lemma dF_mem (hL : IsCrystalLattice hv hM L) (h : IsStringRep hv hM L c i μ x s a u) (j : ℕ) :
    (nodeSl2 R v M hv hM i).dF j u ∈ L := by
  rw [← kashiwaraF_pow_of_primitive hv hM i h.E_smul h.mem_nodeWt]
  exact kashiwaraF_pow_mem hv hM i (hL.kashiwaraF_mem i) _ h.mem

omit [Algebra A k] [IsScalarTower A k M] in
lemma ne_zero (h : IsStringRep hv hM L c i μ x s a u) : u ≠ 0 := fun h0 ↦
  h.notMem (h0 ▸ zero_mem _)

end IsStringRep

namespace IsCrystalBase

variable {hL : IsCrystalLattice hv hM L} {c : A}
  {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}

/-- Every element of a crystal base is the class of a string vector `Fᵢ^{(s)} u` with `[u] ∈ B`
([HK] Prop. 4.2.11 (3), for a weight vector and string decompositions by weights). -/
theorem exists_string (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) {μ : Y →+ ℤ}
    (x : L) (hxw : (x : M) ∈ weightSpace R v M μ) (hxB : Submodule.Quotient.mk x ∈ B) :
    ∃ (s a : ℕ) (u : M), IsStringRep hv hM L c i μ x s a u ∧
      ∃ hu : u ∈ L, Submodule.Quotient.mk ⟨u, hu⟩ ∈ B := by
  obtain ⟨N, η, hηw, hηE, hη2, -, hx⟩ := exists_sum_dF_weight hv hM i hxw
  have hu : ∑ j ∈ range N, (nodeSl2 R v M hv hM i).dF j (η j) ∈ L := hx ▸ x.2
  have hxe : (⟨_, hu⟩ : L) = x := Subtype.ext hx.symm
  obtain ⟨s, hsN, hs, hsB, -, hsmod⟩ := (hL.isKashiwaraStable i).exists_of_mk_mem c B
    (hB.zero_notMem hc) (hB.eQ_mem i) (hB.fQ_eq_iff i) N (μ (R.coroot i)) η
    (fun j ↦ ⟨mem_nodeWt_of_mem_add_nsmul i (hηw j), hηE j⟩) hη2 hu (by rw [hxe]; exact hxB)
  have hne : η s ∉ c • L := fun h ↦ hB.zero_notMem hc
    (by rwa [(IntegrableSl2.mk_eq_zero_iff c ⟨η s, hs⟩).2 h] at hsB)
  have h2 := hη2 s fun h0 ↦ hne (h0 ▸ zero_mem _)
  refine ⟨s, (μ (R.coroot i) + 2 * s).toNat, η s, ⟨hs, hηw s, hηE s, by omega, hne, by omega,
    by rw [hx]; exact hsmod⟩, hs, hsB⟩

end IsCrystalBase

namespace IsStringRep

variable {hL : IsCrystalLattice hv hM L} {c : A} {μ : Y →+ ℤ} {x : M} {s a : ℕ} {u : M}

omit [Algebra A k] [IsScalarTower A k M] in
/-- The class of `x` is the class of `Fᵢ^{(s)} u`. -/
lemma mk_eq (h : IsStringRep hv hM L c i μ x s a u) (hx : x ∈ L) :
    (Submodule.Quotient.mk ⟨x, hx⟩ : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
      Submodule.Quotient.mk ⟨_, h.dF_mem hL s⟩ :=
  (IntegrableSl2.mk_eq_mk_iff c _ _).2 h.sub_mem

/-- `f̃ᵢ [Fᵢ^{(j)} u] = [Fᵢ^{(j+1)} u]`. -/
lemma fQ_mk_dF (h : IsStringRep hv hM L c i μ x s a u) (j : ℕ) :
    hL.fQ c i (Submodule.Quotient.mk ⟨_, h.dF_mem hL j⟩) =
      Submodule.Quotient.mk ⟨_, h.dF_mem hL (j + 1)⟩ := by
  have e := kashiwaraF_pow_dF (hv := hv) (hM := hM) h.E_smul h.mem_nodeWt 1 j
  rw [pow_one] at e
  exact congrArg Submodule.Quotient.mk (Subtype.ext e)

/-- `ẽᵢ [Fᵢ^{(j+1)} u] = [Fᵢ^{(j)} u]` for `j < a`. -/
lemma eQ_mk_dF_succ (h : IsStringRep hv hM L c i μ x s a u) {j : ℕ} (hj : j < a) :
    hL.eQ c i (Submodule.Quotient.mk ⟨_, h.dF_mem hL (j + 1)⟩) =
      Submodule.Quotient.mk ⟨_, h.dF_mem hL j⟩ := by
  have e := kashiwaraE_pow_dF (hv := hv) (hM := hM) h.E_smul h.mem_nodeWt
    (show 1 ≤ j + 1 by omega) (show j + 1 ≤ a by omega)
  rw [pow_one, Nat.add_sub_cancel] at e
  exact congrArg Submodule.Quotient.mk (Subtype.ext e)

/-- `ẽᵢ [u] = 0`. -/
lemma eQ_mk_dF_zero (h : IsStringRep hv hM L c i μ x s a u) :
    hL.eQ c i (Submodule.Quotient.mk ⟨_, h.dF_mem hL 0⟩) = 0 := by
  have e := kashiwaraE_pow_dF_eq_zero (hv := hv) (hM := hM) h.E_smul h.mem_nodeWt
    (show 0 < 1 by omega)
  rw [pow_one] at e
  change (Submodule.Quotient.mk (⟨_, hL.kashiwaraE_mem i _ (h.dF_mem hL 0)⟩ : L) :
    L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) = 0
  rw [IntegrableSl2.mk_eq_zero_iff]
  change kashiwaraE R v M hv hM i ((nodeSl2 R v M hv hM i).dF 0 u) ∈ c • L
  rw [e]
  exact zero_mem _

/-- `ẽᵢ^m [x] = 0` iff `m > s`. -/
lemma eQ_pow_eq_zero_iff (h : IsStringRep hv hM L c i μ x s a u) (hx : x ∈ L) (m : ℕ) :
    (hL.eQ c i ^ m) (Submodule.Quotient.mk ⟨x, hx⟩) = 0 ↔ s < m := by
  rw [h.mk_eq (hL := hL) hx]
  have hpow : ∀ z : L, (hL.eQ c i ^ m) (Submodule.Quotient.mk z) = Submodule.Quotient.mk
      ⟨_, kashiwaraE_pow_mem_of (hL.kashiwaraE_mem i) m z.2⟩ := by
    intro z
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        simp only [pow_succ', Module.End.mul_apply]; rfl))
  rw [hpow, IntegrableSl2.mk_eq_zero_iff]
  change (kashiwaraE R v M hv hM i ^ m) ((nodeSl2 R v M hv hM i).dF s u) ∈ c • L ↔ _
  constructor
  · intro h0
    by_contra hkm
    rw [kashiwaraE_pow_dF h.E_smul h.mem_nodeWt (by omega) h.le] at h0
    exact hL.dF_notMem_smul c h.E_smul h.mem_nodeWt h.notMem (by have := h.le; omega) h0
  · intro hkm
    rw [kashiwaraE_pow_dF_eq_zero h.E_smul h.mem_nodeWt hkm]
    exact zero_mem _

/-- `f̃ᵢ^m [x] = 0` iff `s + m > a`. -/
lemma fQ_pow_eq_zero_iff (h : IsStringRep hv hM L c i μ x s a u) (hx : x ∈ L) (m : ℕ) :
    (hL.fQ c i ^ m) (Submodule.Quotient.mk ⟨x, hx⟩) = 0 ↔ a < s + m := by
  rw [h.mk_eq (hL := hL) hx]
  have hpow : ∀ z : L, (hL.fQ c i ^ m) (Submodule.Quotient.mk z) = Submodule.Quotient.mk
      ⟨_, kashiwaraF_pow_mem hv hM i (hL.kashiwaraF_mem i) m z.2⟩ := by
    intro z
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        simp only [pow_succ', Module.End.mul_apply]; rfl))
  rw [hpow, IntegrableSl2.mk_eq_zero_iff]
  change (kashiwaraF R v M hv hM i ^ m) ((nodeSl2 R v M hv hM i).dF s u) ∈ c • L ↔ _
  rw [kashiwaraF_pow_dF h.E_smul h.mem_nodeWt]
  constructor
  · intro h0
    by_contra ham
    exact hL.dF_notMem_smul c h.E_smul h.mem_nodeWt h.notMem (by omega) h0
  · intro ham
    rw [IntegrableSl2.dF_eq_zero_of_primitive (V := nodeSl2 R v M hv hM i) (pow_d_ne_zero i)
      (pow_d_ne_one hv i) h.mem_nodeWt h.E_smul (by push_cast; omega)]
    exact zero_mem _

end IsStringRep

namespace IsCrystalBase

variable {hL : IsCrystalLattice hv hM L} {c : A}
  {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}

/-- The lengths `εᵢ(b)`, `φᵢ(b)` of the `i`-string through `b ∈ B`. -/
lemma exists_eQ_fQ_counts (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) {b}
    (hb : b ∈ B) : ∃ e φ : ℕ, (∀ a, (hL.eQ c i ^ a) b = 0 ↔ e < a) ∧
      (∀ a, (hL.fQ c i ^ a) b = 0 ↔ φ < a) := by
  obtain ⟨e, p, -, hep, he, hf⟩ := hB.exists_counts hc i ⟨b, hb⟩
  exact ⟨e, p - e, he, fun a ↦ (hf a).trans (by omega)⟩

/-- If `f̃ᵢ b = b'` in `B`, then `εᵢ(b') = εᵢ(b) + 1` and `φᵢ(b) = φᵢ(b') + 1`. -/
lemma counts_of_fQ_eq (hB : IsCrystalBase hL c B) (i : I) {b b'} (hb : b ∈ B) (hb' : b' ∈ B)
    (h : hL.fQ c i b = b') {e φ e' φ' : ℕ} (he : ∀ a, (hL.eQ c i ^ a) b = 0 ↔ e < a)
    (hφ : ∀ a, (hL.fQ c i ^ a) b = 0 ↔ φ < a) (he' : ∀ a, (hL.eQ c i ^ a) b' = 0 ↔ e' < a)
    (hφ' : ∀ a, (hL.fQ c i ^ a) b' = 0 ↔ φ' < a) : e' = e + 1 ∧ φ = φ' + 1 := by
  have h' := (hB.fQ_eq_iff i b hb b' hb').1 h
  have hE : ∀ m, e' < m + 1 ↔ e < m := fun m ↦ by
    rw [← he' (m + 1), ← he m, pow_succ, Module.End.mul_apply, h']
  have hF : ∀ m, φ < m + 1 ↔ φ' < m := fun m ↦ by
    rw [← hφ (m + 1), ← hφ' m, pow_succ, Module.End.mul_apply, h]
  have h1 := hE e
  have h2 := (hE (e + 1)).2 (by omega)
  have h3 := hF φ'
  have h4 := (hF (φ' + 1)).2 (by omega)
  simp only [lt_self_iff_false, iff_false, not_lt] at h1 h3
  omega

end IsCrystalBase

end Strings

/-! ### The tensor product rule on `B₁ ⊗ B₂` -/

namespace TensorModule

section Rule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1}
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]
  {h₁ : IsIntegrable R v M₁} {h₂ : IsIntegrable R v M₂}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂] {L₁ : Submodule A M₁} {L₂ : Submodule A M₂}
  [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
  {hL₁ : IsCrystalLattice hv h₁ L₁} {hL₂ : IsCrystalLattice hv h₂ L₂}
  (hL : IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂)) (i : I)

include hϖ hϖv in
/-- The tensor product rule for `f̃ᵢ` on classes of string representatives
`x ≡ Fᵢ^{(s₁)} u`, `y ≡ Fᵢ^{(s₂)} u'` (`⟨i, ·⟩`-weights `a`, `b` of `u`, `u'`). -/
theorem fQ_tmulL_of_isStringRep {μ₁ μ₂ : Y →+ ℤ} {x : M₁} {y : M₂} (hx : x ∈ L₁)
    (hy : y ∈ L₂) (hxw : x ∈ weightSpace R v M₁ μ₁) (hyw : y ∈ weightSpace R v M₂ μ₂)
    {s₁ a s₂ b : ℕ} {u : M₁} {u' : M₂} (sx : IsStringRep hv h₁ L₁ ϖ i μ₁ x s₁ a u)
    (sy : IsStringRep hv h₂ L₂ ϖ i μ₂ y s₂ b u') :
    hL.fQ ϖ i (tmulL k (Submodule.Quotient.mk ⟨x, hx⟩ :
        L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁)) (Submodule.Quotient.mk ⟨y, hy⟩)) =
      if s₁ < b - s₂ then
        tmulL k (Submodule.Quotient.mk ⟨x, hx⟩) (hL₂.fQ ϖ i (Submodule.Quotient.mk ⟨y, hy⟩))
      else
        tmulL k (hL₁.fQ ϖ i (Submodule.Quotient.mk ⟨x, hx⟩)) (Submodule.Quotient.mk ⟨y, hy⟩) := by
  have hmain := kashiwaraF_tmul_sub_mem hv h₁ h₂ i (hL₁.kashiwaraF_mem i) (hL₂.kashiwaraF_mem i)
    (fun _ z hz _ ↦ hL₁.kashiwaraE_mem i z hz) (fun _ z hz _ ↦ hL₂.kashiwaraE_mem i z hz) hϖ hϖv
    hxw hy hyw sx.mem sx.mem_weightSpace sx.E_smul sx.coroot sx.ne_zero sx.le sy.mem
    sy.mem_weightSpace sy.E_smul sy.coroot sy.ne_zero sy.le sx.sub_mem sy.sub_mem
  rw [tmulL_mk, sx.mk_eq (hL := hL₁) hx, sy.mk_eq (hL := hL₂) hy]
  split_ifs with h
  · rw [sy.fQ_mk_dF, tmulL_mk]
    simp only [h, ↓reduceIte] at hmain
    exact (IntegrableSl2.mk_eq_mk_iff ϖ _ _).2 hmain
  · rw [sx.fQ_mk_dF, tmulL_mk]
    simp only [h, ↓reduceIte] at hmain
    exact (IntegrableSl2.mk_eq_mk_iff ϖ _ _).2 hmain

include hϖ hϖv in
/-- The tensor product rule for `ẽᵢ` on classes of string representatives
`x ≡ Fᵢ^{(s₁)} u`, `y ≡ Fᵢ^{(s₂)} u'` (`⟨i, ·⟩`-weights `a`, `b` of `u`, `u'`). -/
theorem eQ_tmulL_of_isStringRep {μ₁ μ₂ : Y →+ ℤ} {x : M₁} {y : M₂} (hx : x ∈ L₁)
    (hy : y ∈ L₂) (hxw : x ∈ weightSpace R v M₁ μ₁) (hyw : y ∈ weightSpace R v M₂ μ₂)
    {s₁ a s₂ b : ℕ} {u : M₁} {u' : M₂} (sx : IsStringRep hv h₁ L₁ ϖ i μ₁ x s₁ a u)
    (sy : IsStringRep hv h₂ L₂ ϖ i μ₂ y s₂ b u') :
    hL.eQ ϖ i (tmulL k (Submodule.Quotient.mk ⟨x, hx⟩ :
        L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁)) (Submodule.Quotient.mk ⟨y, hy⟩)) =
      if s₁ ≤ b - s₂ then
        tmulL k (Submodule.Quotient.mk ⟨x, hx⟩) (hL₂.eQ ϖ i (Submodule.Quotient.mk ⟨y, hy⟩))
      else
        tmulL k (hL₁.eQ ϖ i (Submodule.Quotient.mk ⟨x, hx⟩)) (Submodule.Quotient.mk ⟨y, hy⟩) := by
  have hmain := kashiwaraE_tmul_sub_mem hv h₁ h₂ i (hL₁.kashiwaraF_mem i) (hL₂.kashiwaraF_mem i)
    (fun _ z hz _ ↦ hL₁.kashiwaraE_mem i z hz) (fun _ z hz _ ↦ hL₂.kashiwaraE_mem i z hz) hϖ hϖv
    hxw hy hyw sx.mem sx.mem_weightSpace sx.E_smul sx.coroot sx.ne_zero sx.le sy.mem
    sy.mem_weightSpace sy.E_smul sy.coroot sy.ne_zero sy.le sx.sub_mem sy.sub_mem
  rw [tmulL_mk, sx.mk_eq (hL := hL₁) hx, sy.mk_eq (hL := hL₂) hy]
  split_ifs with h
  · simp only [h, ↓reduceIte] at hmain
    obtain _ | t := s₂
    · simp only [↓reduceIte, sub_zero] at hmain
      rw [sy.eQ_mk_dF_zero, tmulL_zero_right]
      exact (IntegrableSl2.mk_eq_zero_iff ϖ _).2 hmain
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hmain
      rw [sy.eQ_mk_dF_succ (by have := sy.le; omega), tmulL_mk]
      exact (IntegrableSl2.mk_eq_mk_iff ϖ _ _).2 hmain
  · simp only [h, ↓reduceIte] at hmain
    obtain _ | t := s₁
    · omega
    · rw [Nat.add_sub_cancel] at hmain
      rw [sx.eQ_mk_dF_succ (by have := sx.le; omega), tmulL_mk]
      exact (IntegrableSl2.mk_eq_mk_iff ϖ _ _).2 hmain

variable {B₁ : Set (L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₂))}
  (hB₁ : IsCrystalBase hL₁ ϖ B₁) (hB₂ : IsCrystalBase hL₂ ϖ B₂)

include hϖ hB₁ hB₂ in
/-- Elements `b₁ ∈ B₁`, `b₂ ∈ B₂` are classes of weight vectors with string representatives. -/
lemma exists_isStringRep_pair {b₁ b₂} (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂) :
    ∃ (μ₁ μ₂ : Y →+ ℤ) (x : M₁) (y : M₂) (hx : x ∈ L₁) (hy : y ∈ L₂),
      x ∈ weightSpace R v M₁ μ₁ ∧ y ∈ weightSpace R v M₂ μ₂ ∧
      Submodule.Quotient.mk ⟨x, hx⟩ = b₁ ∧ Submodule.Quotient.mk ⟨y, hy⟩ = b₂ ∧
      ∃ (s₁ a s₂ b : ℕ) (u : M₁) (u' : M₂), IsStringRep hv h₁ L₁ ϖ i μ₁ x s₁ a u ∧
        IsStringRep hv h₂ L₂ ϖ i μ₂ y s₂ b u' := by
  have hc : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  obtain ⟨⟨x, hx⟩, hxw, hxb⟩ := hB₁.exists_mk_eq ⟨b₁, hb₁⟩
  obtain ⟨⟨y, hy⟩, hyw, hyb⟩ := hB₂.exists_mk_eq ⟨b₂, hb₂⟩
  obtain ⟨s₁, a, u, sx, -⟩ := hB₁.exists_string hc i ⟨x, hx⟩ hxw (by rw [hxb]; exact hb₁)
  obtain ⟨s₂, b, u', sy, -⟩ := hB₂.exists_string hc i ⟨y, hy⟩ hyw (by rw [hyb]; exact hb₂)
  exact ⟨_, _, x, y, hx, hy, hxw, hyw, hxb, hyb, s₁, a, s₂, b, u, u', sx, sy⟩

include hϖ hϖv hB₁ hB₂ in
/-- **Tensor product rule for `f̃ᵢ`** on `B₁ ⊗ B₂`, for integrable modules: with the library's
coproduct, `f̃ᵢ (b₁ ⊗ b₂) = b₁ ⊗ f̃ᵢ b₂` if `φᵢ(b₂) > εᵢ(b₁)`, and `f̃ᵢ b₁ ⊗ b₂` otherwise
([HK] Thm. 4.4.1, stated there for modules in `𝒪_int`; compare `TensorModule.fQ_tmulL`). -/
theorem fQ_tmulL_integrable {b₁ b₂} (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂) {e₁ φ₂ : ℕ}
    (he : ∀ a, (hL₁.eQ ϖ i ^ a) b₁ = 0 ↔ e₁ < a) (hφ : ∀ a, (hL₂.fQ ϖ i ^ a) b₂ = 0 ↔ φ₂ < a) :
    hL.fQ ϖ i (tmulL k b₁ b₂) =
      if e₁ < φ₂ then tmulL k b₁ (hL₂.fQ ϖ i b₂) else tmulL k (hL₁.fQ ϖ i b₁) b₂ := by
  obtain ⟨μ₁, μ₂, x, y, hx, hy, hxw, hyw, rfl, rfl, s₁, a, s₂, b, u, u', sx, sy⟩ :=
    exists_isStringRep_pair hϖ i hB₁ hB₂ hb₁ hb₂
  have h1 : e₁ = s₁ := eq_of_forall_gt_iff fun m ↦
    (he m).symm.trans (sx.eQ_pow_eq_zero_iff (hL := hL₁) hx m)
  have h2 : φ₂ = b - s₂ := eq_of_forall_gt_iff fun m ↦
    (hφ m).symm.trans ((sy.fQ_pow_eq_zero_iff (hL := hL₂) hy m).trans (by have := sy.le; omega))
  subst h1 h2
  exact fQ_tmulL_of_isStringRep hϖ hϖv hL i hx hy hxw hyw sx sy

include hϖ hϖv hB₁ hB₂ in
/-- **Tensor product rule for `ẽᵢ`** on `B₁ ⊗ B₂`, for integrable modules: with the library's
coproduct, `ẽᵢ (b₁ ⊗ b₂) = b₁ ⊗ ẽᵢ b₂` if `φᵢ(b₂) ≥ εᵢ(b₁)`, and `ẽᵢ b₁ ⊗ b₂` otherwise
([HK] Thm. 4.4.1, stated there for modules in `𝒪_int`; compare `TensorModule.eQ_tmulL`). -/
theorem eQ_tmulL_integrable {b₁ b₂} (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂) {e₁ φ₂ : ℕ}
    (he : ∀ a, (hL₁.eQ ϖ i ^ a) b₁ = 0 ↔ e₁ < a) (hφ : ∀ a, (hL₂.fQ ϖ i ^ a) b₂ = 0 ↔ φ₂ < a) :
    hL.eQ ϖ i (tmulL k b₁ b₂) =
      if e₁ ≤ φ₂ then tmulL k b₁ (hL₂.eQ ϖ i b₂) else tmulL k (hL₁.eQ ϖ i b₁) b₂ := by
  obtain ⟨μ₁, μ₂, x, y, hx, hy, hxw, hyw, rfl, rfl, s₁, a, s₂, b, u, u', sx, sy⟩ :=
    exists_isStringRep_pair hϖ i hB₁ hB₂ hb₁ hb₂
  have h1 : e₁ = s₁ := eq_of_forall_gt_iff fun m ↦
    (he m).symm.trans (sx.eQ_pow_eq_zero_iff (hL := hL₁) hx m)
  have h2 : φ₂ = b - s₂ := eq_of_forall_gt_iff fun m ↦
    (hφ m).symm.trans ((sy.fQ_pow_eq_zero_iff (hL := hL₂) hy m).trans (by have := sy.le; omega))
  subst h1 h2
  exact eQ_tmulL_of_isStringRep hϖ hϖv hL i hx hy hxw hyw sx sy

omit [IsLocalRing A] in
/-- The elements of `B₁ ⊗ B₂` are the `b₁ ⊗ b₂`. -/
lemma exists_tmulL_eq_of_mem_base {β} (hβ : β ∈ base k B₁ B₂) :
    ∃ b₁ ∈ B₁, ∃ b₂ ∈ B₂, tmulL k b₁ b₂ = β := by
  obtain ⟨x, y, hx, hy, rfl⟩ := hβ
  exact ⟨_, hx, _, hy, tmulL_mk x y⟩

include hϖ hϖv hB₁ hB₂ in
/-- `ẽᵢ f̃ᵢ β = β` for `β ∈ B₁ ⊗ B₂` with `f̃ᵢ β ≠ 0`. -/
lemma eQ_fQ_of_mem_base {β} (hβ : β ∈ base k B₁ B₂) (h : hL.fQ ϖ i β ≠ 0) :
    hL.eQ ϖ i (hL.fQ ϖ i β) = β := by
  have hc : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_tmulL_eq_of_mem_base hβ
  obtain ⟨e₁, φ₁, he₁, hφ₁⟩ := hB₁.exists_eQ_fQ_counts hc i hb₁
  obtain ⟨e₂, φ₂, he₂, hφ₂⟩ := hB₂.exists_eQ_fQ_counts hc i hb₂
  rw [fQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hb₁ hb₂ he₁ hφ₂] at h ⊢
  split_ifs at h ⊢ with hlt
  · have hf : hL₂.fQ ϖ i b₂ ≠ 0 := fun h0 ↦ h (by rw [h0, tmulL_zero_right])
    have hc₂ := (hB₂.fQ_mem i b₂ hb₂).resolve_right hf
    obtain ⟨e₂', φ₂', he₂', hφ₂'⟩ := hB₂.exists_eQ_fQ_counts hc i hc₂
    obtain ⟨-, h2⟩ := hB₂.counts_of_fQ_eq i hb₂ hc₂ rfl he₂ hφ₂ he₂' hφ₂'
    rw [eQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hb₁ hc₂ he₁ hφ₂']
    simp only [show e₁ ≤ φ₂' by omega, ↓reduceIte]
    rw [(hB₂.fQ_eq_iff i b₂ hb₂ _ hc₂).1 rfl]
  · have hf : hL₁.fQ ϖ i b₁ ≠ 0 := fun h0 ↦ h (by rw [h0, tmulL_zero_left])
    have hc₁ := (hB₁.fQ_mem i b₁ hb₁).resolve_right hf
    obtain ⟨e₁', φ₁', he₁', hφ₁'⟩ := hB₁.exists_eQ_fQ_counts hc i hc₁
    obtain ⟨h1, -⟩ := hB₁.counts_of_fQ_eq i hb₁ hc₁ rfl he₁ hφ₁ he₁' hφ₁'
    rw [eQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hc₁ hb₂ he₁' hφ₂]
    simp only [show ¬e₁' ≤ φ₂ by omega, ↓reduceIte]
    rw [(hB₁.fQ_eq_iff i b₁ hb₁ _ hc₁).1 rfl]

include hϖ hϖv hB₁ hB₂ in
/-- `f̃ᵢ ẽᵢ β = β` for `β ∈ B₁ ⊗ B₂` with `ẽᵢ β ≠ 0`. -/
lemma fQ_eQ_of_mem_base {β} (hβ : β ∈ base k B₁ B₂) (h : hL.eQ ϖ i β ≠ 0) :
    hL.fQ ϖ i (hL.eQ ϖ i β) = β := by
  have hc : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_tmulL_eq_of_mem_base hβ
  obtain ⟨e₁, φ₁, he₁, hφ₁⟩ := hB₁.exists_eQ_fQ_counts hc i hb₁
  obtain ⟨e₂, φ₂, he₂, hφ₂⟩ := hB₂.exists_eQ_fQ_counts hc i hb₂
  rw [eQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hb₁ hb₂ he₁ hφ₂] at h ⊢
  split_ifs at h ⊢ with hle
  · have he : hL₂.eQ ϖ i b₂ ≠ 0 := fun h0 ↦ h (by rw [h0, tmulL_zero_right])
    have hc₂ := (hB₂.eQ_mem i b₂ hb₂).resolve_right he
    obtain ⟨e₂', φ₂', he₂', hφ₂'⟩ := hB₂.exists_eQ_fQ_counts hc i hc₂
    have hf := (hB₂.fQ_eq_iff i _ hc₂ b₂ hb₂).2 rfl
    obtain ⟨-, h2⟩ := hB₂.counts_of_fQ_eq i hc₂ hb₂ hf he₂' hφ₂' he₂ hφ₂
    rw [fQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hb₁ hc₂ he₁ hφ₂']
    simp only [show e₁ < φ₂' by omega, ↓reduceIte]
    rw [hf]
  · have he : hL₁.eQ ϖ i b₁ ≠ 0 := fun h0 ↦ h (by rw [h0, tmulL_zero_left])
    have hc₁ := (hB₁.eQ_mem i b₁ hb₁).resolve_right he
    obtain ⟨e₁', φ₁', he₁', hφ₁'⟩ := hB₁.exists_eQ_fQ_counts hc i hc₁
    have hf := (hB₁.fQ_eq_iff i _ hc₁ b₁ hb₁).2 rfl
    obtain ⟨h1, -⟩ := hB₁.counts_of_fQ_eq i hc₁ hb₁ hf he₁' hφ₁' he₁ hφ₁
    rw [fQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hc₁ hb₂ he₁' hφ₂]
    simp only [show ¬e₁' < φ₂ by omega, ↓reduceIte]
    rw [hf]

variable (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hinj : Function.Injective (algebraMap A k))

include hϖ hϖv hk hinj hB₁ hB₂ in
/-- **The tensor product of crystal bases** ([HK] Thm. 4.4.1, stated there for modules in
`𝒪_int`): for crystal bases `(L₁, B₁)`, `(L₂, B₂)` at `ϖ` of integrable `U`-modules,
`(L₁ ⊗ L₂, B₁ ⊗ B₂)` is a crystal base of `M₁ ⊗ M₂`, on which `ẽᵢ`, `f̃ᵢ` act by the tensor
product rule (`TensorModule.eQ_tmulL_integrable`, `TensorModule.fQ_tmulL_integrable`). No
finite-dimensionality is assumed (compare `TensorModule.isCrystalBase_tensor`). -/
theorem isCrystalBase_tensor_integrable :
    IsCrystalBase (isCrystalLattice_tensor hϖ hϖv hk hinj hL₁ hL₂) ϖ (base k B₁ B₂) := by
  have hc : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have := hL₁.free
  have := hL₂.free
  have hli := linearIndependent_base hϖ0 hk hinj hL₁.span_eq_top hL₂.span_eq_top
    hB₁.linearIndependent hB₁.span_eq_top hB₂.linearIndependent hB₂.span_eq_top
  have h0 : (0 : _) ∉ base k B₁ B₂ := by
    have : Nontrivial (A ⧸ Ideal.span {ϖ}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact fun h ↦ hli.ne_zero ⟨0, h⟩ rfl
  set hL := isCrystalLattice_tensor hϖ hϖv hk hinj hL₁ hL₂
  refine
    { linearIndependent := hli
      span_eq_top := span_base_eq_top hB₁.span_eq_top hB₂.span_eq_top
      exists_weight := ?_
      eQ_mem := fun i β hβ ↦ ?_
      fQ_mem := fun i β hβ ↦ ?_
      fQ_eq_iff := fun i β hβ β' hβ' ↦ ⟨?_, ?_⟩ }
  · rintro b ⟨x, y, hx, hy, rfl⟩
    obtain ⟨Λ, x', hx', hxx⟩ := hB₁.exists_weight _ hx
    obtain ⟨Λ', y', hy', hyy⟩ := hB₂.exists_weight _ hy
    exact ⟨Λ + Λ', ⟨_, tmul_mem_lattice x'.2 y'.2⟩, tmul_mem_weightSpace hx' hy',
      mk_tmul_eq hxx hyy⟩
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_tmulL_eq_of_mem_base hβ
    obtain ⟨e₁, -, he₁, -⟩ := hB₁.exists_eQ_fQ_counts hc i hb₁
    obtain ⟨-, φ₂, -, hφ₂⟩ := hB₂.exists_eQ_fQ_counts hc i hb₂
    rw [eQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hb₁ hb₂ he₁ hφ₂]
    split_ifs
    · rcases hB₂.eQ_mem i b₂ hb₂ with h | h
      · exact Or.inl (tmulL_mem_base hb₁ h)
      · exact Or.inr (by rw [h, tmulL_zero_right])
    · rcases hB₁.eQ_mem i b₁ hb₁ with h | h
      · exact Or.inl (tmulL_mem_base h hb₂)
      · exact Or.inr (by rw [h, tmulL_zero_left])
  · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_tmulL_eq_of_mem_base hβ
    obtain ⟨e₁, -, he₁, -⟩ := hB₁.exists_eQ_fQ_counts hc i hb₁
    obtain ⟨-, φ₂, -, hφ₂⟩ := hB₂.exists_eQ_fQ_counts hc i hb₂
    rw [fQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ hb₁ hb₂ he₁ hφ₂]
    split_ifs
    · rcases hB₂.fQ_mem i b₂ hb₂ with h | h
      · exact Or.inl (tmulL_mem_base hb₁ h)
      · exact Or.inr (by rw [h, tmulL_zero_right])
    · rcases hB₁.fQ_mem i b₁ hb₁ with h | h
      · exact Or.inl (tmulL_mem_base h hb₂)
      · exact Or.inr (by rw [h, tmulL_zero_left])
  · rintro rfl
    exact eQ_fQ_of_mem_base hϖ hϖv hL i hB₁ hB₂ hβ fun h ↦ h0 (h ▸ hβ')
  · rintro rfl
    exact fQ_eQ_of_mem_base hϖ hϖv hL i hB₁ hB₂ hβ' fun h ↦ h0 (h ▸ hβ)

include hϖ hϖv hk hinj in
/-- **The crystal of a tensor product** of crystal bases of integrable modules ([HK] Thm. 4.4.1,
stated there for modules in `𝒪_int`): the crystal of `(L₁ ⊗ L₂, B₁ ⊗ B₂)` is isomorphic to the
tensor product (Kashiwara's convention, `Crystal.tensor`) of the crystals of `B₂` and `B₁`, by
`b₂ ⊗ b₁ ↦ [b₁ ⊗ b₂]`; the factors are exchanged because the library's coproduct is Lusztig's.
No finite-dimensionality is assumed (compare `TensorModule.nonempty_crystalEquiv`). -/
theorem nonempty_crystalEquiv_integrable :
    Nonempty (Crystal.Equiv
      ((hB₂.crystal ((IsLocalRing.mem_maximalIdeal ϖ).1 hϖ)).tensor
        (hB₁.crystal ((IsLocalRing.mem_maximalIdeal ϖ).1 hϖ)))
      ((isCrystalBase_tensor_integrable hϖ hϖv hB₁ hB₂ hk hinj).crystal
        ((IsLocalRing.mem_maximalIdeal ϖ).1 hϖ))) := by
  have hc : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have := hL₁.free
  have := hL₂.free
  set hB := isCrystalBase_tensor_integrable hϖ hϖv hB₁ hB₂ hk hinj
  set hL := isCrystalLattice_tensor hϖ hϖv hk hinj hL₁ hL₂
  let Φ : B₂ × B₁ → base k B₁ B₂ := fun p ↦ ⟨tmulL k p.2.1 p.1.1, tmulL_mem_base p.2.2 p.1.2⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨b₂, b₁⟩ ⟨b₂', b₁'⟩ h
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ b₁.1
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ b₂.1
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ b₁'.1
    obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ b₂'.1
    have h' : tmulL k b₁.1 b₂.1 = tmulL k b₁'.1 b₂'.1 := congrArg Subtype.val h
    rw [← hx, ← hy, ← hx', ← hy', tmulL_mk, tmulL_mk] at h'
    obtain ⟨e1, e2⟩ := mk_eq_of_tmul_sub_mem hinj hϖ0 hk hL₁.span_eq_top hL₂.span_eq_top
      hB₁.linearIndependent hB₁.span_eq_top hB₂.linearIndependent hB₂.span_eq_top
      (by rw [hx]; exact b₁.2) (by rw [hx']; exact b₁'.2) (by rw [hy]; exact b₂.2)
      (by rw [hy']; exact b₂'.2) ((IntegrableSl2.mk_eq_mk_iff ϖ _ _).1 h')
    exact Prod.ext (Subtype.ext (hy.symm.trans (e2.trans hy')))
      (Subtype.ext (hx.symm.trans (e1.trans hx')))
  have hsurj : Function.Surjective Φ := by
    rintro ⟨b, x, y, hx, hy, rfl⟩
    exact ⟨(⟨_, hy⟩, ⟨_, hx⟩), Subtype.ext (tmulL_mk x y)⟩
  refine ⟨Crystal.equivOfE ((hB₂.isSeminormal_crystal hc).tensor (hB₁.isSeminormal_crystal hc))
    (hB.isSeminormal_crystal hc) (Equiv.ofBijective Φ ⟨hΦ, hsurj⟩) ?_ ?_⟩
  · rintro ⟨b₂, b₁⟩
    change hB.wt (Φ (b₂, b₁)) = hB₂.wt b₂ + hB₁.wt b₁
    rw [wt_tmulL hB₁ hB₂ hc hB, add_comm]
  · rintro i ⟨b₂, b₁⟩
    obtain ⟨φ₂, hφ₂⟩ : ∃ n : ℕ, (hB₂.eps hc i b₂ : ℤ) + hB₂.wt b₂ (R.coroot i) = n := by
      have h0 := (hB₂.isSeminormal_crystal hc).φ_nonneg i b₂
      change ((0 : ℤ) : WithBot ℤ) ≤ (((hB₂.eps hc i b₂ : ℤ) + hB₂.wt b₂ (R.coroot i) : ℤ) :
        WithBot ℤ) at h0
      rw [WithBot.coe_le_coe] at h0
      exact ⟨_, (Int.toNat_of_nonneg h0).symm⟩
    have hφ : ∀ a, (hL₂.fQ ϖ i ^ a) b₂.1 = 0 ↔ φ₂ < a := fun a ↦ by
      rw [hB₂.fQ_pow_eq_zero_iff hc i b₂ a, hφ₂]
      norm_cast
    have key := eQ_tmulL_integrable hϖ hϖv hL i hB₁ hB₂ b₁.2 b₂.2
      (hB₁.eQ_pow_eq_zero_iff hc i b₁) hφ
    have hcond : ((hB₁.crystal hc).ε i b₁ ≤ (hB₂.crystal hc).φ i b₂) ↔
        hB₁.eps hc i b₁ ≤ φ₂ := by
      change (((hB₁.eps hc i b₁ : ℤ)) : WithBot ℤ) ≤
        (((hB₂.eps hc i b₂ : ℤ) + hB₂.wt b₂ (R.coroot i) : ℤ) : WithBot ℤ) ↔ _
      rw [hφ₂, WithBot.coe_le_coe]
      norm_cast
    change hB.e i (Φ (b₂, b₁)) = ((hB₂.crystal hc).tensor (hB₁.crystal hc) |>.e i (b₂, b₁)).map Φ
    by_cases h : hB₁.eps hc i b₁ ≤ φ₂
    · simp only [h, ↓reduceIte] at key
      have ht : ((hB₂.crystal hc).tensor (hB₁.crystal hc)).e i (b₂, b₁) =
          ((hB₂.crystal hc).e i b₂).map (·, b₁) := by
        simp only [Crystal.tensor, hcond.2 h, ↓reduceIte]
      rw [ht, IsCrystalBase.crystal_e]
      by_cases h0 : hL₂.eQ ϖ i b₂.1 = 0
      · rw [(hB₂.e_eq_none_iff i b₂).2 h0, Option.map_none, Option.map_none,
          hB.e_eq_none_iff i]
        change hL.eQ ϖ i (tmulL k b₁.1 b₂.1) = 0
        rw [key, h0, tmulL_zero_right]
      · rw [(hB₂.e_eq_some_iff hc i b₂ ⟨_, hB₂.eQ_mem_of_ne i b₂ h0⟩).2 rfl, Option.map_some,
          Option.map_some, hB.e_eq_some_iff hc]
        exact key
    · simp only [h, ↓reduceIte] at key
      have ht : ((hB₂.crystal hc).tensor (hB₁.crystal hc)).e i (b₂, b₁) =
          ((hB₁.crystal hc).e i b₁).map (b₂, ·) := by
        simp only [Crystal.tensor, mt hcond.1 h, ↓reduceIte]
      rw [ht, IsCrystalBase.crystal_e]
      by_cases h0 : hL₁.eQ ϖ i b₁.1 = 0
      · rw [(hB₁.e_eq_none_iff i b₁).2 h0, Option.map_none, Option.map_none,
          hB.e_eq_none_iff i]
        change hL.eQ ϖ i (tmulL k b₁.1 b₂.1) = 0
        rw [key, h0, tmulL_zero_left]
      · rw [(hB₁.e_eq_some_iff hc i b₁ ⟨_, hB₁.eQ_mem_of_ne i b₁ h0⟩).2 rfl, Option.map_some,
          Option.map_some, hB.e_eq_some_iff hc]
        exact key

end Rule

end TensorModule

end LieLean.QuantumGroup
