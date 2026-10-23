/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.LeftRegular
import LieLean.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.NoncommRing

/-!
# Natural transformations between tensoring functors

Let `I` be a two-sided ideal of `U = U(L)` and `A = U / I`. On the modules killed by `I`
consider the functors `F_V : M ↦ M ⊗ V` and `F_W : M ↦ M ⊗ W` for `L`-modules `V`, `W`.
Natural transformations `F_V → F_W` correspond to morphisms of `L`-modules
`V → A^{ad} ⊗ W`, where `A^{ad}` is `A` with the adjoint action `x · a = x a - a x`:

* a morphism `g : V → A^{ad} ⊗ W` gives `φ_M (m ⊗ v) = Σ aᵢ m ⊗ wᵢ` for `g v = Σ aᵢ ⊗ wᵢ`
  (`tensorNatMap`), natural in `M` (`tensorNatMap_naturality`);
* conversely `φ` is recovered from `g v = φ_A (1 ⊗ v)` (`evalNat`), using naturality of `φ`
  along the maps `A → A`, `a ↦ a u` (`evalNat`, requires them) and `A → M`, `a ↦ a m`
  (`tensorNatMap_evalNat`); and `evalNat (tensorNatMap g) = g` (`evalNat_tensorNatMap`).

This is the bimodule description of natural transformations between projective functors used
by Bernstein–Gelfand, and in the proof of Theorem 10.7 in Humphreys, *Representations of
semisimple Lie algebras in the BGG category `𝒪`*, GSM 94.

## Main definitions

* `UniversalEnvelopingAlgebra.AdRegular`: `U(L)` with the adjoint action.
* `UniversalEnvelopingAlgebra.IsKilledBy`: `I` acts by zero on `M`.
* `UniversalEnvelopingAlgebra.LeftQuotient`, `UniversalEnvelopingAlgebra.AdQuotient`: `U / I`
  with the left-multiplication action, resp. the adjoint action.
* `UniversalEnvelopingAlgebra.tensorNatMap`: `φ_M : M ⊗ V → M ⊗ W` for `g : V → A^{ad} ⊗ W`.
* `UniversalEnvelopingAlgebra.evalNat`: `g v = φ_A (1 ⊗ v)`.
-/

noncomputable section

open TensorProduct LieModule

namespace UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "𝓤" => UniversalEnvelopingAlgebra R L

/-! ### The adjoint module -/

/-- The enveloping algebra regarded as a Lie module by the adjoint action
`x · u = ι(x) u - u ι(x)`. -/
def AdRegular := UniversalEnvelopingAlgebra R L

namespace AdRegular

attribute [local instance] LieRing.ofAssociativeRing

instance : AddCommGroup (AdRegular R L) := inferInstanceAs (AddCommGroup 𝓤)

instance : Module R (AdRegular R L) := inferInstanceAs (Module R 𝓤)

instance : LieRingModule 𝓤 (AdRegular R L) := inferInstanceAs (LieRingModule 𝓤 𝓤)

instance : LieModule R 𝓤 (AdRegular R L) := inferInstanceAs (LieModule R 𝓤 𝓤)

instance : LieRingModule L (AdRegular R L) := LieRingModule.compLieHom _ (ι R)

instance : LieModule R L (AdRegular R L) := LieModule.compLieHom _ (ι R)

/-- The underlying linear identification forgets only the type tag. -/
def equiv : AdRegular R L ≃ₗ[R] 𝓤 := LinearEquiv.refl R _

@[simp] theorem equiv_lie (x : L) (u : AdRegular R L) :
    equiv R L ⁅x, u⁆ = ι R x * equiv R L u - equiv R L u * ι R x := rfl

end AdRegular

/-! ### Modules killed by an ideal -/

variable {R L} (I : TwoSidedIdeal (UniversalEnvelopingAlgebra R L))

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The action of `U(L)` on an `L`-module. -/
abbrev actionHom : 𝓤 →ₐ[R] Module.End R M := lift R (toEnd R L M)

theorem actionHom_ι (x : L) : actionHom (R := R) (L := L) M (ι R x) = toEnd R L M x :=
  lift_ι_apply R _ x

/-- `I` acts by zero on `M`. -/
def IsKilledBy : Prop := ∀ a ∈ I, actionHom (R := R) (L := L) M a = 0

variable {M} {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- Morphisms of `L`-modules commute with the action of `U(L)`. -/
theorem _root_.LieModuleHom.map_actionHom (f : M →ₗ⁅R,L⁆ N) (u : 𝓤) (m : M) :
    f (actionHom M u m) = actionHom N u (f m) := by
  obtain ⟨t, rfl⟩ : ∃ t, mkAlgHom R L t = u := by
    induction u using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  induction t using TensorAlgebra.induction generalizing m with
  | algebraMap r => simp
  | ι x => simp
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      map_add, ha, hb]

variable (R L)

/-- `I` as a Lie submodule of the left-regular module. -/
def leftIdeal : LieSubmodule R L (LeftRegular R L) where
  carrier := {u | LeftRegular.equiv R L u ∈ I}
  add_mem' ha hb := I.add_mem ha hb
  zero_mem' := I.zero_mem
  smul_mem' c u hu := by
    change LeftRegular.equiv R L (c • u) ∈ I
    rw [map_smul, Algebra.smul_def]
    exact I.mul_mem_left _ _ hu
  lie_mem {x u} hu := I.mul_mem_left (ι R x) _ hu

/-- `I` as a Lie submodule of the adjoint module. -/
def adIdeal : LieSubmodule R L (AdRegular R L) where
  carrier := {u | AdRegular.equiv R L u ∈ I}
  add_mem' ha hb := I.add_mem ha hb
  zero_mem' := I.zero_mem
  smul_mem' c u hu := by
    change AdRegular.equiv R L (c • u) ∈ I
    rw [map_smul, Algebra.smul_def]
    exact I.mul_mem_left _ _ hu
  lie_mem {x u} hu := I.sub_mem (I.mul_mem_left (ι R x) _ hu) (I.mul_mem_right _ (ι R x) hu)

/-- `U / I` with the left-multiplication action. -/
abbrev LeftQuotient := LeftRegular R L ⧸ leftIdeal R L I

/-- `U / I` with the adjoint action. -/
abbrev AdQuotient := AdRegular R L ⧸ adIdeal R L I

/-- The two quotients have the same underlying module. -/
def quotientEquiv : AdQuotient R L I ≃ₗ[R] LeftQuotient R L I :=
  Submodule.Quotient.equiv _ _ ((AdRegular.equiv R L).trans (LeftRegular.equiv R L).symm)
    (Submodule.ext fun u ↦ by
      constructor
      · rintro ⟨v, hv, rfl⟩; exact hv
      · intro hu; exact ⟨u, hu, rfl⟩)

@[simp] theorem quotientEquiv_mk (u : AdRegular R L) :
    quotientEquiv R L I (LieSubmodule.Quotient.mk u) =
      LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm (AdRegular.equiv R L u)) := rfl

/-! ### The action of `U / I` -/

variable {R L I}

/-- On a module killed by `I`, the action of `U` factors through `U / I`. -/
def quotientAction (hM : IsKilledBy I M) : AdQuotient R L I →ₗ[R] Module.End R M :=
  (adIdeal R L I).toSubmodule.liftQ
    ((actionHom M).toLinearMap ∘ₗ (AdRegular.equiv R L).toLinearMap)
    fun _ hu ↦ LinearMap.mem_ker.mpr (hM _ hu)

@[simp] theorem quotientAction_mk (hM : IsKilledBy I M) (u : AdRegular R L) :
    quotientAction hM (LieSubmodule.Quotient.mk u) = actionHom M (AdRegular.equiv R L u) := rfl

theorem quotientAction_lie (hM : IsKilledBy I M) (x : L) (q : AdQuotient R L I) (m : M) :
    quotientAction hM ⁅x, q⁆ m =
      ⁅x, quotientAction hM q m⁆ - quotientAction hM q ⁅x, m⁆ := by
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    change actionHom M (AdRegular.equiv R L ⁅x, u⁆) m = _
    rw [AdRegular.equiv_lie, map_sub, map_mul, map_mul, actionHom_ι]
    rfl

/-- The `U(L)`-orbit map `a ↦ a m` of `m ∈ M`, a morphism `U / I → M` of `L`-modules. -/
def orbitMap (hM : IsKilledBy I M) (m : M) : LeftQuotient R L I →ₗ⁅R,L⁆ M :=
  LieSubmodule.Quotient.lift _
    { toFun u := actionHom M (LeftRegular.equiv R L u) m
      map_add' u v := by simp
      map_smul' c u := by simp
      map_lie' {x u} := by
        change actionHom M (ι R x * LeftRegular.equiv R L u) m = _
        rw [map_mul, actionHom_ι]
        rfl }
    fun u hu ↦ LieModuleHom.mem_ker.mpr (by
      change actionHom M (LeftRegular.equiv R L u) m = 0
      rw [show actionHom M (LeftRegular.equiv R L u) = 0 from hM _ hu, LinearMap.zero_apply])

@[simp] theorem orbitMap_mk (hM : IsKilledBy I M) (m : M) (u : LeftRegular R L) :
    orbitMap hM m (LieSubmodule.Quotient.mk u) = actionHom M (LeftRegular.equiv R L u) m := rfl

theorem quotientAction_flip_eq (hM : IsKilledBy I M) (m : M) :
    (quotientAction hM).flip m =
      (orbitMap hM m : LeftQuotient R L I →ₗ[R] M) ∘ₗ (quotientEquiv R L I).toLinearMap := by
  ext m'
  induction m' using Submodule.Quotient.induction_on with
  | H u => rfl

/-- The action of `U` on `U / I` is left multiplication. -/
theorem actionHom_leftQuotient_mk (a : 𝓤) (u : LeftRegular R L) :
    actionHom (LeftQuotient R L I) a (LieSubmodule.Quotient.mk u) =
      LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm (a * LeftRegular.equiv R L u)) := by
  obtain ⟨t, rfl⟩ : ∃ t, mkAlgHom R L t = a := by
    induction a using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  induction t using TensorAlgebra.induction generalizing u with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, ← Algebra.smul_def]
    rfl
  | ι x =>
    change actionHom _ (ι R x) _ = _
    rw [actionHom_ι]
    rfl
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, hb, ha, mul_assoc]
    rfl
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_mul]
    rfl

variable (I) in
theorem isKilledBy_leftQuotient : IsKilledBy I (LeftQuotient R L I) := fun a ha ↦ by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    rw [LinearMap.zero_apply, actionHom_leftQuotient_mk]
    exact (LieSubmodule.Quotient.mk_eq_zero' (N := leftIdeal R L I)).mpr
      (I.mul_mem_right _ _ ha)

variable (I) in
/-- Right multiplication `a ↦ a u` on `U / I`, a morphism of `L`-modules. -/
def quotientMulRight (u : 𝓤) : LeftQuotient R L I →ₗ⁅R,L⁆ LeftQuotient R L I :=
  LieSubmodule.Quotient.lift _ ((LieSubmodule.Quotient.mk' _).comp (LeftRegular.mulRight u))
    fun _ hv ↦ LieModuleHom.mem_ker.mpr
      ((LieSubmodule.Quotient.mk_eq_zero' (N := leftIdeal R L I)).mpr (I.mul_mem_right _ _ hv))

@[simp] theorem quotientMulRight_mk (u : 𝓤) (v : LeftRegular R L) :
    quotientMulRight I u (LieSubmodule.Quotient.mk v) =
      LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm (LeftRegular.equiv R L v * u)) :=
  rfl

/-! ### From `g : V → A^{ad} ⊗ W` to natural transformations -/

variable {V W : Type*} [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

theorem lie_rTensor_quotientAction (hM : IsKilledBy I M) (x : L) (m : M)
    (t : AdQuotient R L I ⊗[R] W) :
    ⁅x, ((quotientAction hM).flip m).rTensor W t⁆ =
      ((quotientAction hM).flip ⁅x, m⁆).rTensor W t +
        ((quotientAction hM).flip m).rTensor W ⁅x, t⁆ := by
  induction t with
  | add s t hs ht => rw [map_add, lie_add, hs, ht, lie_add, map_add, map_add]; abel
  | tmul q w =>
    simp only [LinearMap.rTensor_tmul, LinearMap.flip_apply, LieModule.lie_tmul_right,
      map_add, quotientAction_lie]
    rw [sub_tmul]
    abel

/-- The natural transformation `φ_M : M ⊗ V → M ⊗ W`, `m ⊗ v ↦ Σ aᵢ m ⊗ wᵢ` for
`g v = Σ aᵢ ⊗ wᵢ`, on a module `M` killed by `I`. -/
def tensorNatMap (g : V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W) (hM : IsKilledBy I M) :
    M ⊗[R] V →ₗ⁅R,L⁆ M ⊗[R] W where
  toLinearMap := TensorProduct.lift
    ((LinearMap.lcomp R (M ⊗[R] W) g.toLinearMap) ∘ₗ (LinearMap.rTensorHom W) ∘ₗ
      (quotientAction hM).flip)
  map_lie' {x t} := by
    induction t with
    | add s t hs ht =>
      simp only [LinearMap.toFun_eq_coe] at hs ht ⊢
      rw [lie_add, map_add, hs, ht, map_add, lie_add]
    | tmul m v =>
      simp only [LinearMap.toFun_eq_coe, LieModule.lie_tmul_right, map_add,
        TensorProduct.lift.tmul]
      change ((quotientAction hM).flip ⁅x, m⁆).rTensor W (g v) +
          ((quotientAction hM).flip m).rTensor W (g ⁅x, v⁆) =
        ⁅x, ((quotientAction hM).flip m).rTensor W (g v)⁆
      rw [LieModuleHom.map_lie, lie_rTensor_quotientAction]

@[simp] theorem tensorNatMap_tmul (g : V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W)
    (hM : IsKilledBy I M) (m : M) (v : V) :
    tensorNatMap g hM (m ⊗ₜ v) = ((quotientAction hM).flip m).rTensor W (g v) := rfl

/-- **Naturality** of `φ` along morphisms between modules killed by `I`. -/
theorem tensorNatMap_naturality (g : V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W)
    (hM : IsKilledBy I M) (hN : IsKilledBy I N) (f : M →ₗ⁅R,L⁆ N) (t : M ⊗[R] V) :
    (f : M →ₗ[R] N).rTensor W (tensorNatMap g hM t) =
      tensorNatMap g hN ((f : M →ₗ[R] N).rTensor V t) := by
  induction t with
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul m v =>
    rw [tensorNatMap_tmul, LinearMap.rTensor_tmul, tensorNatMap_tmul,
      ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    congr 2
    ext q
    induction q using Submodule.Quotient.induction_on with
    | H u => exact f.map_actionHom _ m

/-! ### From natural transformations to `g` -/

variable (I) in
/-- The class of `1` in `U / I`. -/
abbrev quotientOne : LeftQuotient R L I :=
  LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm 1)

theorem rTensor_quotientEquiv_symm_lie (x : L) (t : LeftQuotient R L I ⊗[R] W) :
    ((quotientEquiv R L I).symm.toLinearMap.rTensor W) ⁅x, t⁆ -
        ((quotientEquiv R L I).symm.toLinearMap.rTensor W)
          ((quotientMulRight I (ι R x) : LeftQuotient R L I →ₗ[R] _).rTensor W t) =
      ⁅x, (quotientEquiv R L I).symm.toLinearMap.rTensor W t⁆ := by
  induction t with
  | add s t hs ht =>
    simp only [lie_add, map_add]
    rw [← hs, ← ht]
    abel
  | tmul q w =>
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      simp only [LieModule.lie_tmul_right, map_add, LinearMap.rTensor_tmul,
        LieModuleHom.coe_toLinearMap, quotientMulRight_mk]
      rw [add_sub_right_comm, ← sub_tmul]
      rfl

/-- **The bimodule element of a natural transformation**: `g v = φ_A (1 ⊗ v)` for
`φ_A : A ⊗ V → A ⊗ W` commuting with the right multiplications of `A = U / I`. -/
def evalNat (ψ : LeftQuotient R L I ⊗[R] V →ₗ⁅R,L⁆ LeftQuotient R L I ⊗[R] W)
    (hψ : ∀ (u : 𝓤) (t : LeftQuotient R L I ⊗[R] V),
      (quotientMulRight I u : LeftQuotient R L I →ₗ[R] _).rTensor W (ψ t) =
        ψ ((quotientMulRight I u : LeftQuotient R L I →ₗ[R] _).rTensor V t)) :
    V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W where
  toLinearMap := ((quotientEquiv R L I).symm.toLinearMap.rTensor W) ∘ₗ ψ.toLinearMap ∘ₗ
    (TensorProduct.mk R _ V (quotientOne I))
  map_lie' {x v} := by
    have h1 : quotientOne I ⊗ₜ[R] ⁅x, v⁆ =
        ⁅x, quotientOne I ⊗ₜ[R] v⁆ -
          (quotientMulRight I (ι R x) : LeftQuotient R L I →ₗ[R] _).rTensor V
            (quotientOne I ⊗ₜ[R] v) := by
      rw [LieModule.lie_tmul_right, LinearMap.rTensor_tmul]
      have : ⁅x, quotientOne I⁆ =
          quotientMulRight I (ι R x) (quotientOne I) := by
        rw [quotientMulRight_mk]
        change (LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm (ι R x * 1)) :
          LeftQuotient R L I) = LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm (1 * ι R x))
        rw [mul_one, one_mul]
      rw [LieModuleHom.coe_toLinearMap, ← this]
      abel
    change (quotientEquiv R L I).symm.toLinearMap.rTensor W (ψ (quotientOne I ⊗ₜ ⁅x, v⁆)) =
      ⁅x, (quotientEquiv R L I).symm.toLinearMap.rTensor W (ψ (quotientOne I ⊗ₜ v))⁆
    rw [h1, map_sub, LieModuleHom.map_lie, ← hψ, map_sub, rTensor_quotientEquiv_symm_lie]

@[simp] theorem evalNat_apply
    (ψ : LeftQuotient R L I ⊗[R] V →ₗ⁅R,L⁆ LeftQuotient R L I ⊗[R] W) (hψ) (v : V) :
    evalNat ψ hψ v = (quotientEquiv R L I).symm.toLinearMap.rTensor W
      (ψ (quotientOne I ⊗ₜ v)) := rfl

/-- `g` is recovered from its natural transformation: `evalNat (tensorNatMap g) = g`. -/
theorem evalNat_tensorNatMap (g : V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W) :
    evalNat (tensorNatMap g (isKilledBy_leftQuotient I)) (fun u t ↦
      tensorNatMap_naturality g _ _ (quotientMulRight I u) t) = g := by
  ext v
  rw [evalNat_apply, tensorNatMap_tmul, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  convert LinearMap.rTensor_id_apply (x := g v)
  ext q
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    change (quotientEquiv R L I).symm (actionHom (LeftQuotient R L I) (AdRegular.equiv R L u)
      (quotientOne I)) = LieSubmodule.Quotient.mk u
    rw [actionHom_leftQuotient_mk]
    change (LieSubmodule.Quotient.mk ((AdRegular.equiv R L).symm (AdRegular.equiv R L u * 1)) :
      AdQuotient R L I) = _
    rw [mul_one]
    rfl

/-- A natural transformation is determined by `evalNat`: if `ψ_M` is natural along the orbit
maps `A → M`, then `ψ_M = tensorNatMap (evalNat ψ_A)`. -/
theorem tensorNatMap_evalNat
    (ψ : LeftQuotient R L I ⊗[R] V →ₗ⁅R,L⁆ LeftQuotient R L I ⊗[R] W) (hψ)
    (hM : IsKilledBy I M) (ψM : M ⊗[R] V →ₗ⁅R,L⁆ M ⊗[R] W)
    (hnat : ∀ (m : M) (t : LeftQuotient R L I ⊗[R] V),
      (orbitMap hM m : LeftQuotient R L I →ₗ[R] M).rTensor W (ψ t) =
        ψM ((orbitMap hM m : LeftQuotient R L I →ₗ[R] M).rTensor V t)) :
    tensorNatMap (evalNat ψ hψ) hM = ψM := by
  ext t
  induction t with
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul m v =>
    have hm : orbitMap hM m (quotientOne I) = m := by
      rw [orbitMap_mk]
      change actionHom M 1 m = m
      rw [map_one, Module.End.one_apply]
    rw [tensorNatMap_tmul, evalNat_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      quotientAction_flip_eq, LinearMap.comp_assoc]
    rw [show (quotientEquiv R L I).toLinearMap ∘ₗ (quotientEquiv R L I).symm.toLinearMap =
        LinearMap.id from by ext; simp, LinearMap.comp_id, hnat, LinearMap.rTensor_tmul,
      LieModuleHom.coe_toLinearMap, hm]

end UniversalEnvelopingAlgebra
