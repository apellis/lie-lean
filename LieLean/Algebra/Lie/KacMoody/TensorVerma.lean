/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.VermaHomology
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor identities and negative-nilradical tensor-Verma pieces

## Main definitions / Main results

* `UniversalEnvelopingAlgebra.TensorIdentity.equiv`: the actual equivalence
  `U(L)_reg ⊗ Z_trivial ≃ U(L)_reg ⊗ Z_diagonal`, over a commutative ring.
* `VermaModule.tensorEquivLeftRegular`: its PBW specialization to `M(Λ) ⊗ Z`,
  equivariant for the negative nilradical.
* `VermaModule.tensorSubspaceMap_injective`: the concrete piece morphism attached to
  any coefficient subspace is injective.
* `VermaModule.tensorSubspace_mono` and `tensorSubspace_top`: coefficient subspaces give
  increasing negative-nilradical submodules, exhausting the tensor-Verma module.

The concrete map `u ⊗ z ↦ u • (1 ⊗ z)` has an inverse constructed by the enveloping
representation on a Hom module. No bijectivity or filtration is assumed.
These are negative-nilradical pieces, not yet full Lie-algebra submodules or a standard
filtration. A Borel flag, full Lie-algebra stability and the Verma quotient identifications
remain to be constructed.

## References

The argument is reconstructed from the enveloping universal property and existing PBW APIs.
No external primary source was consulted: this is not a certification of Humphreys
Theorem 3.6 or 7.6, and no Casimir/full-central-character block identification is made.
-/

open TensorProduct LieModule

noncomputable section

namespace UniversalEnvelopingAlgebra
namespace TensorIdentity

variable {R L Z : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup Z] [Module R Z] [LieRingModule L Z] [LieModule R L Z]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "Reg" => LeftRegular R L
local notation "Z₀" => TrivialLieModule R L Z
local notation "Free" => Reg ⊗[R] Z₀
local notation "Diag" => Reg ⊗[R] Z

/-- The enveloping action attached to an actual Lie representation. -/
def act (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] : U →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (toEnd R L M)

@[simp] theorem act_ι (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] (x : L) (m : M) : act M (ι R x) m = ⁅x, m⁆ := by
  rw [act, lift_ι_apply, toEnd_apply_apply]

/-- Induction using multiplication by one Lie generator on the left. -/
theorem induction_left {C : U → Prop} (hone : C 1)
    (hadd : ∀ a b, C a → C b → C (a + b))
    (hsmul : ∀ (r : R) a, C a → C (r • a))
    (hι : ∀ (x : L) a, C a → C (ι R x * a)) (u : U) : C u := by
  have h (a : U) : ∀ b, C b → C (a * b) := by
    induction a using UniversalEnvelopingAlgebra.induction with
    | algebraMap r => intro b hb; rw [← Algebra.smul_def]; exact hsmul r b hb
    | ι x => exact hι x
    | mul a b ha hb => intro c hc; rw [mul_assoc]; exact ha _ (hb _ hc)
    | add a b ha hb => intro c hc; rw [add_mul]; exact hadd _ _ (ha _ hc) (hb _ hc)
  simpa using h u 1 hone

/-- Insert a vector into degree zero of the diagonal tensor module. -/
def seed : Z →ₗ[R] Diag := TensorProduct.mk R Reg Z ((LeftRegular.equiv R L).symm 1)

/-- Insert a vector into degree zero of the free tensor module. -/
def freeSeed : Z →ₗ[R] Free :=
  (TensorProduct.mk R Reg Z₀ ((LeftRegular.equiv R L).symm 1)).comp
    (TrivialLieModule.equiv R L Z).symm.toLinearMap

/-- The tensor identity map, extending the degree-zero inclusion by the diagonal action. -/
def forward : Free →ₗ[R] Diag := TensorProduct.lift
  { toFun := fun u => (act Diag (LeftRegular.equiv R L u)).comp
      (seed.comp (TrivialLieModule.equiv R L Z).toLinearMap)
    map_add' := by intros; ext z; simp
    map_smul' := by intros; ext z; simp }

/-- The inverse candidate, from the action on `Hom(Z, Free)`. -/
def backward : Diag →ₗ[R] Free := TensorProduct.lift
  { toFun := fun u => act (Z →ₗ[R] Free) (LeftRegular.equiv R L u) freeSeed
    map_add' := by intros; simp
    map_smul' := by intros; simp }

@[simp] theorem forward_tmul (u : Reg) (z : Z₀) :
    forward (u ⊗ₜ[R] z) =
      act Diag (LeftRegular.equiv R L u) (seed (TrivialLieModule.equiv R L Z z)) := rfl

@[simp] theorem backward_tmul (u : Reg) (z : Z) :
    backward (u ⊗ₜ[R] z) = act (Z →ₗ[R] Free) (LeftRegular.equiv R L u) freeSeed z := rfl

/-- The forward map commutes with the Lie action. -/
theorem forward_lie (x : L) (t : Free) : forward ⁅x, t⁆ = ⁅x, forward t⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul u z =>
    simp only [TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero, tmul_zero,
      add_zero, forward_tmul, LeftRegular.equiv_lie, map_mul, Module.End.mul_apply, act_ι]
  | add t s ht hs => simp only [lie_add, map_add, ht, hs]

/-- On a left generator the Hom-module action gives the subtraction recurrence. -/
theorem backward_lie_tmul (x : L) (u : Reg) (z : Z) :
    backward (⁅x, u⁆ ⊗ₜ[R] z) =
      ⁅x, backward (u ⊗ₜ[R] z)⁆ - backward (u ⊗ₜ[R] ⁅x, z⁆) := by
  simp only [backward_tmul, LeftRegular.equiv_lie, map_mul, Module.End.mul_apply, act_ι,
    LieHom.lie_apply]

/-- The inverse candidate also commutes with the Lie action. -/
theorem backward_lie (x : L) (t : Diag) : backward ⁅x, t⁆ = ⁅x, backward t⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul u z =>
    rw [TensorProduct.LieModule.lie_tmul_right, map_add, backward_lie_tmul,
      sub_add_cancel]
  | add t s ht hs => simp only [lie_add, map_add, ht, hs]

/-- Both maps fix their degree-zero generators. -/
@[simp] theorem forward_freeSeed (z : Z) :
    forward (freeSeed (R := R) (L := L) z) = seed z := by
  simp [freeSeed, forward_tmul]

@[simp] theorem backward_seed (z : Z) :
    backward (seed (R := R) (L := L) z) = freeSeed z := by
  simp [seed, backward_tmul]

/-- The Hom-action inverse is a left inverse, on every tensor, not only generators. -/
theorem backward_forward (t : Free) : backward (forward t) = t := by
  suffices h : ∀ (u : U) (z : Z₀),
      backward (forward ((LeftRegular.equiv R L).symm u ⊗ₜ[R] z)) =
        (LeftRegular.equiv R L).symm u ⊗ₜ[R] z by
    induction t using TensorProduct.inductionOn with
    | tmul u z => simpa using h (LeftRegular.equiv R L u) z
    | add t s ht hs => simp only [map_add, ht, hs]
  intro u
  induction u using induction_left with
  | hone =>
    intro z
    change backward (forward (freeSeed (R := R) (L := L)
      (TrivialLieModule.equiv R L Z z))) = _
    rw [forward_freeSeed, backward_seed]
    rfl
  | hadd a b ha hb => intro z; simp only [map_add, add_tmul, ha, hb]
  | hsmul r a ha => intro z; simp only [map_smul, ← smul_tmul', ha]
  | hι x a ha =>
    intro z
    have e : (LeftRegular.equiv R L).symm (ι R x * a) ⊗ₜ[R] z =
        ⁅x, (LeftRegular.equiv R L).symm a ⊗ₜ[R] z⁆ := by
      simp only [TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero, tmul_zero,
        add_zero]
      rfl
    rw [e, forward_lie, backward_lie, ha]

/-- The Hom-action inverse is also a right inverse. -/
theorem forward_backward (t : Diag) : forward (backward t) = t := by
  suffices h : ∀ (u : U) (z : Z),
      forward (backward ((LeftRegular.equiv R L).symm u ⊗ₜ[R] z)) =
        (LeftRegular.equiv R L).symm u ⊗ₜ[R] z by
    induction t using TensorProduct.inductionOn with
    | tmul u z => simpa using h (LeftRegular.equiv R L u) z
    | add t s ht hs => simp only [map_add, ht, hs]
  intro u
  induction u using induction_left with
  | hone =>
    intro z
    change forward (backward (seed (R := R) (L := L) z)) = _
    rw [backward_seed, forward_freeSeed]
    rfl
  | hadd a b ha hb => intro z; simp only [map_add, add_tmul, ha, hb]
  | hsmul r a ha => intro z; simp only [map_smul, ← smul_tmul', ha]
  | hι x a ha =>
    intro z
    change forward (backward (⁅x, (LeftRegular.equiv R L).symm a⁆ ⊗ₜ[R] z)) = _
    rw [backward_lie_tmul, map_sub, forward_lie, ha, ha,
      TensorProduct.LieModule.lie_tmul_right, add_sub_cancel_right]
    rfl

/-- The tensor identity: the diagonal tensor with the regular module is free.
Reconstructed directly from the enveloping universal property; valid over any commutative ring.
The left side has trivial action on the coefficient factor, the right side its given action. -/
def equiv : Free ≃ₗ⁅R,L⁆ Diag :=
  { forward with
    invFun := backward
    left_inv := backward_forward
    right_inv := forward_backward
    map_lie' := forward_lie _ _ }

end TensorIdentity
end UniversalEnvelopingAlgebra

namespace LieModuleEquiv

variable {R L M N M' N' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']
  [AddCommGroup N'] [Module R N'] [LieRingModule L N'] [LieModule R L N']

/-- Tensor two Lie-module equivalences, with the diagonal actions. -/
def tensorCongr (f : M ≃ₗ⁅R,L⁆ M') (g : N ≃ₗ⁅R,L⁆ N') :
    M ⊗[R] N ≃ₗ⁅R,L⁆ M' ⊗[R] N' :=
  { TensorProduct.congr f.toLinearEquiv g.toLinearEquiv with
    map_lie' := (TensorProduct.LieModule.map f.toLieModuleHom g.toLieModuleHom).map_lie _ _ }

@[simp] theorem tensorCongr_tmul (f : M ≃ₗ⁅R,L⁆ M') (g : N ≃ₗ⁅R,L⁆ N') (m : M) (n : N) :
    tensorCongr f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n :=
  TensorProduct.congr_tmul _ _ _ _

end LieModuleEquiv

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

open UniversalEnvelopingAlgebra

variable {ι K H Z : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (Λ : Module.Dual K H) [AddCommGroup Z] [Module K Z]
  [LieRingModule P.KacMoodyAlgebra Z] [LieModule K P.KacMoodyAlgebra Z]

/-- The actual tensor-Verma negative-nilradical identity. The coefficient factor on the
left is trivial; the right carries the diagonal action inherited from the full Lie algebra.
Reconstructed from the Hom-module tensor identity and the existing PBW equivalence.
No finiteness, dominance, integrality, or symmetrizability is needed for this step. -/
def tensorEquivLeftRegular :
    LeftRegular K (nNeg P) ⊗[K] TrivialLieModule K (nNeg P) Z ≃ₗ⁅K,nNeg P⁆
      VermaModule P Λ ⊗[K] Z :=
  (TensorIdentity.equiv (R := K) (L := nNeg P) (Z := Z)).trans
    ((equivLeftRegular P Λ).tensorCongr LieModuleEquiv.refl)

/-- The tensor identity sends `1 ⊗ z` to the highest-weight tensor `v_Λ ⊗ z`. -/
@[simp] theorem tensorEquivLeftRegular_one (z : Z) :
    tensorEquivLeftRegular P Λ
      ((LeftRegular.equiv K (nNeg P)).symm 1 ⊗ₜ[K]
        (TrivialLieModule.equiv K (nNeg P) Z).symm z) = hwv P Λ ⊗ₜ[K] z := by
  change (equivLeftRegular P Λ).tensorCongr LieModuleEquiv.refl
    (TensorIdentity.forward (TensorIdentity.freeSeed z)) = _
  rw [TensorIdentity.forward_freeSeed]
  rw [TensorIdentity.seed, TensorProduct.mk_apply, LieModuleEquiv.tensorCongr_tmul]
  change equivEnvNNeg P Λ 1 ⊗ₜ[K] z = _
  simp

/-- The tensor-Verma module is genuinely generated over the negative enveloping algebra
by its highest-weight tensors. This is an equality of Lie submodules, not of characters. -/
theorem eq_top_of_hwv_tmul_mem
    (N : LieSubmodule K (nNeg P) (VermaModule P Λ ⊗[K] Z))
    (hN : ∀ z : Z, hwv P Λ ⊗ₜ[K] z ∈ N) : N = ⊤ := by
  apply eq_top_iff.mpr
  intro t ht
  clear ht
  obtain ⟨s, rfl⟩ := (tensorEquivLeftRegular P Λ).surjective t
  suffices h : ∀ (u : UniversalEnvelopingAlgebra K (nNeg P))
      (z : TrivialLieModule K (nNeg P) Z),
      tensorEquivLeftRegular P Λ ((LeftRegular.equiv K (nNeg P)).symm u ⊗ₜ[K] z) ∈ N by
    induction s using TensorProduct.inductionOn with
    | tmul u z => simpa using h (LeftRegular.equiv K (nNeg P) u) z
    | add s t hs ht => rw [map_add]; exact N.add_mem hs ht
  intro u
  induction u using TensorIdentity.induction_left with
  | hone =>
    intro z
    rw [← (TrivialLieModule.equiv K (nNeg P) Z).symm_apply_apply z,
      tensorEquivLeftRegular_one]
    exact hN _
  | hadd a b ha hb => intro z; simp only [map_add, add_tmul]; exact N.add_mem (ha z) (hb z)
  | hsmul r a ha =>
    intro z
    simp only [map_smul, ← smul_tmul']
    exact N.smul_mem r (ha z)
  | hι x a ha =>
    intro z
    have e : (LeftRegular.equiv K (nNeg P)).symm (UniversalEnvelopingAlgebra.ι K x * a)
        ⊗ₜ[K] z = ⁅x, (LeftRegular.equiv K (nNeg P)).symm a ⊗ₜ[K] z⁆ := by
      simp only [TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero, tmul_zero,
        add_zero]
      rfl
    rw [e]
    change (tensorEquivLeftRegular P Λ).toLieModuleHom ⁅x, _⁆ ∈ N
    rw [LieModuleHom.map_lie]
    exact N.lie_mem (ha z)

/-- The inclusion of a coefficient subspace, with trivial negative-nilradical actions. -/
def trivialSubspaceIncl (F : Submodule K Z) :
    TrivialLieModule K (nNeg P) F →ₗ⁅K,nNeg P⁆ TrivialLieModule K (nNeg P) Z :=
  { (TrivialLieModule.equiv K (nNeg P) Z).symm.toLinearMap.comp
      (F.subtype.comp (TrivialLieModule.equiv K (nNeg P) F).toLinearMap) with
    map_lie' := by intros; rfl }

/-- The concrete filtration-piece morphism: extend `F ↪ Z` freely over the negative
nilradical, then apply the tensor-Verma identity. This construction does not require F
to be a submodule for the full Lie algebra. -/
def tensorSubspaceMap (F : Submodule K Z) :
    LeftRegular K (nNeg P) ⊗[K] TrivialLieModule K (nNeg P) F →ₗ⁅K,nNeg P⁆
      VermaModule P Λ ⊗[K] Z :=
  (tensorEquivLeftRegular P Λ).toLieModuleHom.comp
    (TensorProduct.LieModule.map LieModuleHom.id (trivialSubspaceIncl P F))

/-- These concrete piece morphisms are injective. In particular the coefficient
subspaces do not acquire extra relations on passage to the tensor-Verma module. -/
theorem tensorSubspaceMap_injective (F : Submodule K Z) :
    Function.Injective (tensorSubspaceMap P Λ F) := by
  apply (tensorEquivLeftRegular P Λ).injective.comp
  apply TensorProduct.map_injective_of_flat_flat
  · exact Function.injective_id
  · exact (TrivialLieModule.equiv K (nNeg P) Z).symm.injective.comp
      (F.subtype_injective.comp (TrivialLieModule.equiv K (nNeg P) F).injective)

/-- The negative-nilradical submodule attached to a coefficient subspace.
Full Lie-algebra stability for a Borel-stable F is a separate remaining step. -/
def tensorSubspace (F : Submodule K Z) :
    LieSubmodule K (nNeg P) (VermaModule P Λ ⊗[K] Z) :=
  (tensorSubspaceMap P Λ F).range

/-- Increasing coefficient spaces give increasing actual negative-nilradical submodules. -/
theorem tensorSubspace_mono : Monotone (tensorSubspace (Z := Z) P Λ) := by
  intro F G h t ht
  obtain ⟨s, rfl⟩ := ht
  induction s using TensorProduct.inductionOn with
  | tmul u z =>
    refine ⟨u ⊗ₜ[K] (TrivialLieModule.equiv K (nNeg P) G).symm
      ⟨(TrivialLieModule.equiv K (nNeg P) F z).val,
        h (TrivialLieModule.equiv K (nNeg P) F z).property⟩, ?_⟩
    simp only [tensorSubspaceMap, LieModuleHom.comp_apply, TensorProduct.LieModule.map_tmul]
    rfl
  | add s t hs ht =>
    rw [map_add]
    exact (tensorSubspace P Λ G).add_mem hs ht

/-- The last coefficient space gives the whole tensor-Verma module. -/
@[simp] theorem tensorSubspace_top : tensorSubspace (Z := Z) P Λ ⊤ = ⊤ := by
  apply eq_top_of_hwv_tmul_mem
  intro z
  refine ⟨(LeftRegular.equiv K (nNeg P)).symm 1 ⊗ₜ[K]
    (TrivialLieModule.equiv K (nNeg P) (⊤ : Submodule K Z)).symm ⟨z, trivial⟩, ?_⟩
  simp only [tensorSubspaceMap, LieModuleHom.comp_apply, TensorProduct.LieModule.map_tmul]
  exact tensorEquivLeftRegular_one P Λ z

end Matrix.Realization.KacMoodyAlgebra.VermaModule
