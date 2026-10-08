/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.DirectSum.Module
import LieLean.Algebra.Lie.Weights.OfMap

/-!
# Extensions of weight modules and `Ext¹`

Let `L` be a Lie algebra over a field `K` and `φ : H →ₗ[K] L` a linear map (the inclusion of a
Cartan subalgebra `𝔥`). For `L`-modules `M`, `N` we define the `K`-vector space
`ExtOne φ M N = Z¹ / B¹` of relative `1`-cocycles modulo coboundaries:

* `Z¹` consists of the linear maps `c : L → Hom_K(M, N)` with `c(φ a) = 0` for all `a ∈ H` and
  `c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆` (the action of `L` on `Hom_K(M, N)` is
  `⁅x, f⁆ = x ∘ f - f ∘ x`);
* `B¹` consists of the `x ↦ ⁅x, f⁆` with `f : M → N` commuting with `φ(H)`.

A cocycle `c` defines an extension `0 → N → E_c → M → 0`, with `E_c = N × M` and
`x (n, m) = (x n + c(x) m, x m)` (`ExtOne.Extension`); its class vanishes iff the extension splits
(`ExtOne.mk_eq_zero_iff`). Conversely, every short exact sequence `0 → A → B → C → 0` with a
`φ(H)`-equivariant linear section of `B → C` has a class in `ExtOne φ C A` (the class of the cocycle
`x ↦ r ∘ ⁅x, s⁆`, `ExtOne.SplitData.cocycle`), which vanishes iff the sequence splits
(`ExtOne.SplitData.connecting_id_eq_zero_iff`); for weight modules such sections always exist
(`ExtOne.exists_splitData`). Hence for modules that are sums of their weight spaces, `ExtOne φ M N`
classifies the extensions of `M` by `N` in which `φ(H)` still acts diagonally: it is the Yoneda
`Ext¹` of the category of weight modules, and of any subcategory closed under extensions among
weight modules, such as the category `𝒪` (Humphreys, GSM 94, §3.1, and the `Ext_𝒪` of §7.14).
The comparison of the vector-space structure with the Baer sum is not formalized.

For a short exact sequence `0 → A → B → C → 0` as above and a module `N`, the connecting map
`δ : Hom(A, N) → ExtOne φ C N` fits in the exact sequence
`Hom(B, N) → Hom(A, N) → ExtOne φ C N → ExtOne φ B N`
(`ExtOne.SplitData.connecting_eq_zero_iff`, `ExtOne.SplitData.exists_connecting_eq`). In
particular `δ` is an isomorphism when `Hom(B, N) = 0` and `ExtOne φ B N = 0`
(`ExtOne.SplitData.connectingEquiv`).

## Main definitions

* `LieModule.relHom`: the `φ(H)`-equivariant linear maps.
* `LieModule.extCocycles`, `LieModule.extCoboundary`, `LieModule.ExtOne`.
* `LieModule.ExtOne.Extension`: the extension module of a cocycle.
* `LieModule.ExtOne.comap`: functoriality in the first variable.
* `LieModule.ExtOne.SplitData`: a short exact sequence with an equivariant splitting as vector
  spaces; `SplitData.connecting`: the connecting map.
-/

noncomputable section

open Module

namespace LieModule

variable {K H L : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  (φ : H →ₗ[K] L)

section Defs

variable (M N : Type*) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- The linear maps `M → N` commuting with the action of `φ(H)`. -/
def relHom : Submodule K (M →ₗ[K] N) where
  carrier := {f | ∀ a m, f ⁅φ a, m⁆ = ⁅φ a, f m⁆}
  add_mem' hf hg a m := by simp [hf a m, hg a m, lie_add]
  zero_mem' a m := by simp
  smul_mem' c f hf a m := by simp [hf a m, lie_smul]

/-- Relative `1`-cocycles: linear maps `c : L → Hom_K(M, N)` vanishing on `φ(H)` with
`c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆`. (Linearity of `c` is part of the condition: the ambient space
is the space of all functions `L → Hom_K(M, N)`.) -/
def extCocycles : Submodule K (L → M →ₗ[K] N) where
  carrier := {c | (∀ x y, c (x + y) = c x + c y) ∧ (∀ (t : K) x, c (t • x) = t • c x) ∧
    (∀ a, c (φ a) = 0) ∧ ∀ x y, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆}
  add_mem' {c d} hc hd := ⟨fun x y ↦ by simp only [Pi.add_apply, hc.1, hd.1]; abel,
    fun t x ↦ by simp only [Pi.add_apply, hc.2.1, hd.2.1, smul_add],
    fun a ↦ by simp [hc.2.2.1 a, hd.2.2.1 a], fun x y ↦ by
    simp only [Pi.add_apply, hc.2.2.2 x y, hd.2.2.2 x y, lie_add]; abel⟩
  zero_mem' := ⟨fun x y ↦ by simp, fun t x ↦ by simp, fun a ↦ rfl, fun x y ↦ by simp⟩
  smul_mem' t c hc := ⟨fun x y ↦ by simp only [Pi.smul_apply, hc.1, smul_add],
    fun t' x ↦ by simp only [Pi.smul_apply, hc.2.1, smul_comm t t'],
    fun a ↦ by simp [hc.2.2.1 a], fun x y ↦ by
    simp only [Pi.smul_apply, hc.2.2.2 x y, lie_smul, smul_sub]⟩

/-- The coboundary `x ↦ ⁅x, f⁆` of an equivariant map `f`. -/
def extCoboundary : relHom φ M N →ₗ[K] extCocycles φ M N where
  toFun f := ⟨fun x ↦ ⁅x, (f : M →ₗ[K] N)⁆,
    ⟨fun x y ↦ add_lie x y _, fun t x ↦ smul_lie t x _,
      fun a ↦ by ext m; simp [LieHom.lie_apply, f.2 a m], fun x y ↦ lie_lie x y _⟩⟩
  map_add' f g := by ext x m; simp [lie_add]
  map_smul' t f := by ext x m; simp [lie_smul]

/-- `Ext¹` relative to `φ`: relative `1`-cocycles modulo coboundaries. For weight modules it is
the Yoneda `Ext¹` in the category of weight modules (see the module docstring). -/
abbrev ExtOne : Type _ := extCocycles φ M N ⧸ LinearMap.range (extCoboundary φ M N)

end Defs

variable {M N A B C : Type*}
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup A] [Module K A] [LieRingModule L A] [LieModule K L A]
  [AddCommGroup B] [Module K B] [LieRingModule L B] [LieModule K L B]
  [AddCommGroup C] [Module K C] [LieRingModule L C] [LieModule K L C]

namespace extCocycles

variable {φ}

theorem map_add' (c : extCocycles φ M N) (x y : L) : c.1 (x + y) = c.1 x + c.1 y := c.2.1 x y

theorem map_smul' (c : extCocycles φ M N) (t : K) (x : L) : c.1 (t • x) = t • c.1 x := c.2.2.1 t x

theorem map_apply_eq_zero (c : extCocycles φ M N) (a : H) : c.1 (φ a) = 0 := c.2.2.2.1 a

theorem map_zero' (c : extCocycles φ M N) : c.1 0 = 0 := by
  simpa using extCocycles.map_smul' c 0 0

/-- The cocycle identity, evaluated at a vector. -/
theorem apply_lie_apply (c : extCocycles φ M N) (x y : L) (m : M) :
    c.1 ⁅x, y⁆ m = ⁅x, c.1 y m⁆ - c.1 y ⁅x, m⁆ - (⁅y, c.1 x m⁆ - c.1 x ⁅y, m⁆) := by
  rw [c.2.2.2.2 x y, LinearMap.sub_apply, LieHom.lie_apply, LieHom.lie_apply]

end extCocycles

namespace ExtOne

variable {φ}

/-- The class of a cocycle. -/
abbrev mk (c : extCocycles φ M N) : ExtOne φ M N := Submodule.Quotient.mk c

theorem mk_surjective : Function.Surjective (mk : extCocycles φ M N → ExtOne φ M N) :=
  Submodule.Quotient.mk_surjective _

/-- The class of `c` vanishes iff `c = ⁅·, f⁆` for an equivariant `f`. -/
theorem mk_eq_zero_iff_exists (c : extCocycles φ M N) :
    mk c = 0 ↔ ∃ f : M →ₗ[K] N, f ∈ relHom φ M N ∧ ∀ x m, c.1 x m = ⁅x, f m⁆ - f ⁅x, m⁆ := by
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, f.2, fun x m ↦ LieHom.lie_apply _ _ _⟩
  · rintro ⟨f, hf, h⟩
    refine ⟨⟨f, hf⟩, Subtype.ext (funext fun x ↦ LinearMap.ext fun m ↦ ?_)⟩
    exact (LieHom.lie_apply _ _ _).trans (h x m).symm

/-! ### The extension module of a cocycle -/

/-- The extension `E_c = N × M` of `M` by `N` defined by a cocycle `c`, with
`x (n, m) = (x n + c(x) m, x m)`. -/
@[nolint unusedArguments]
def Extension (_c : extCocycles φ M N) : Type _ := N × M

namespace Extension

variable (c : extCocycles φ M N)

instance : AddCommGroup (Extension c) := inferInstanceAs (AddCommGroup (N × M))
instance : Module K (Extension c) := inferInstanceAs (Module K (N × M))

/-- The identification of `E_c` with `N × M` as vector spaces. -/
def equiv : Extension c ≃ₗ[K] N × M := LinearEquiv.refl K (N × M)

instance : Bracket L (Extension c) where
  bracket x v := (equiv c).symm
    (⁅x, (equiv c v).1⁆ + c.1 x (equiv c v).2, ⁅x, (equiv c v).2⁆)

theorem equiv_lie (x : L) (v : Extension c) :
    equiv c ⁅x, v⁆ = (⁅x, (equiv c v).1⁆ + c.1 x (equiv c v).2, ⁅x, (equiv c v).2⁆) :=
  rfl

theorem ext_iff' {v w : Extension c} :
    v = w ↔ (equiv c v).1 = (equiv c w).1 ∧ (equiv c v).2 = (equiv c w).2 := by
  rw [← Prod.ext_iff, (equiv c).injective.eq_iff]

theorem fst_lie (x : L) (v : Extension c) :
    (equiv c ⁅x, v⁆).1 = ⁅x, (equiv c v).1⁆ + c.1 x (equiv c v).2 := rfl

theorem snd_lie' (x : L) (v : Extension c) : (equiv c ⁅x, v⁆).2 = ⁅x, (equiv c v).2⁆ := rfl

instance : LieRingModule L (Extension c) where
  add_lie x y v := by
    rw [ext_iff']
    refine ⟨?_, ?_⟩
    · simp only [map_add, Prod.fst_add, fst_lie, add_lie, extCocycles.map_add' c,
        LinearMap.add_apply]
      abel
    · simp only [map_add, Prod.snd_add, snd_lie', add_lie]
  lie_add x v w := by
    rw [ext_iff']
    refine ⟨?_, ?_⟩
    · simp only [map_add, Prod.fst_add, Prod.snd_add, fst_lie, lie_add]
      abel
    · simp only [map_add, Prod.snd_add, snd_lie', lie_add]
  leibniz_lie x y v := by
    rw [ext_iff']
    refine ⟨?_, ?_⟩
    · change ⁅x, ⁅y, (equiv c v).1⁆ + c.1 y (equiv c v).2⁆ + c.1 x ⁅y, (equiv c v).2⁆ =
        ⁅⁅x, y⁆, (equiv c v).1⁆ + c.1 ⁅x, y⁆ (equiv c v).2 +
          (⁅y, ⁅x, (equiv c v).1⁆ + c.1 x (equiv c v).2⁆ + c.1 y ⁅x, (equiv c v).2⁆)
      rw [lie_add, lie_add, leibniz_lie x y (equiv c v).1, extCocycles.apply_lie_apply c]
      abel
    · exact leibniz_lie x y (equiv c v).2

instance : LieModule K L (Extension c) where
  smul_lie t x v := by
    rw [ext_iff']
    refine ⟨?_, ?_⟩
    · change ⁅t • x, (equiv c v).1⁆ + c.1 (t • x) (equiv c v).2 =
        t • (⁅x, (equiv c v).1⁆ + c.1 x (equiv c v).2)
      rw [smul_lie, extCocycles.map_smul' c, LinearMap.smul_apply, smul_add]
    · exact smul_lie t x (equiv c v).2
  lie_smul t x v := by
    rw [ext_iff']
    refine ⟨?_, ?_⟩
    · change ⁅x, t • (equiv c v).1⁆ + c.1 x (t • (equiv c v).2) =
        t • (⁅x, (equiv c v).1⁆ + c.1 x (equiv c v).2)
      rw [lie_smul, map_smul, smul_add]
    · exact lie_smul t x (equiv c v).2

/-- The inclusion `N → E_c`. -/
def inl : N →ₗ⁅K,L⁆ Extension c where
  toLinearMap := (equiv c).symm.toLinearMap ∘ₗ LinearMap.inl K N M
  map_lie' {x n} := by
    rw [ext_iff']
    refine ⟨?_, ?_⟩
    · change ⁅x, n⁆ = ⁅x, n⁆ + c.1 x 0
      rw [map_zero, add_zero]
    · change (0 : M) = ⁅x, (0 : M)⁆
      rw [lie_zero]

/-- The projection `E_c → M`. -/
def snd : Extension c →ₗ⁅K,L⁆ M where
  toLinearMap := LinearMap.snd K N M ∘ₗ (equiv c).toLinearMap
  map_lie' {_ _} := rfl

@[simp] theorem equiv_inl (n : N) : equiv c (inl c n) = (n, 0) := rfl

@[simp] theorem snd_apply (v : Extension c) : snd c v = (equiv c v).2 := rfl

theorem injective_inl : Function.Injective (inl c) := fun n n' h ↦ by
  simpa using congrArg (fun v ↦ (equiv c v).1) h

theorem surjective_snd : Function.Surjective (snd c) := fun m ↦
  ⟨(equiv c).symm (0, m), rfl⟩

theorem exists_inl_eq_of_snd_eq_zero {v : Extension c} (hv : snd c v = 0) :
    ∃ n, inl c n = v :=
  ⟨(equiv c v).1, (ext_iff' c).mpr ⟨rfl, by rw [equiv_inl]; exact hv.symm⟩⟩

/-- `E_μ = N_μ × M_μ`: the weight spaces of `E_c`. -/
theorem mem_weightSpaceOfMap_iff (μ : Dual K H) (v : Extension c) :
    v ∈ weightSpaceOfMap (Extension c) φ μ ↔
      (equiv c v).1 ∈ weightSpaceOfMap N φ μ ∧ (equiv c v).2 ∈ weightSpaceOfMap M φ μ := by
  simp only [mem_weightSpaceOfMap, ext_iff', fst_lie, snd_lie', extCocycles.map_apply_eq_zero c,
    LinearMap.zero_apply, add_zero, map_smul, Prod.smul_fst, Prod.smul_snd]
  exact ⟨fun h ↦ ⟨fun a ↦ (h a).1, fun a ↦ (h a).2⟩, fun h a ↦ ⟨h.1 a, h.2 a⟩⟩

theorem symm_zero_mem_weightSpaceOfMap {μ : Dual K H} {m : M}
    (hm : m ∈ weightSpaceOfMap M φ μ) :
    (equiv c).symm (0, m) ∈ weightSpaceOfMap (Extension c) φ μ :=
  (mem_weightSpaceOfMap_iff c μ _).mpr ⟨Submodule.zero_mem _, hm⟩

/-- `E_c` is a sum of weight spaces if `N` and `M` are. -/
theorem iSup_weightSpaceOfMap_eq_top (hN : ⨆ μ, weightSpaceOfMap N φ μ = ⊤)
    (hM : ⨆ μ, weightSpaceOfMap M φ μ = ⊤) :
    ⨆ μ, weightSpaceOfMap (Extension c) φ μ = ⊤ := by
  have hinl : ∀ n : N, inl c n ∈ ⨆ μ, weightSpaceOfMap (Extension c) φ μ := by
    intro n
    have hn : n ∈ ⨆ μ, weightSpaceOfMap N φ μ := hN ▸ Submodule.mem_top
    induction hn using Submodule.iSup_induction' with
    | mem μ n hn =>
      exact Submodule.mem_iSup_of_mem μ ((mem_weightSpaceOfMap_iff c μ _).mpr
        ⟨hn, Submodule.zero_mem _⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add n n' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
  have hsnd : ∀ m : M, (equiv c).symm (0, m) ∈ ⨆ μ, weightSpaceOfMap (Extension c) φ μ := by
    intro m
    have hm : m ∈ ⨆ μ, weightSpaceOfMap M φ μ := hM ▸ Submodule.mem_top
    induction hm using Submodule.iSup_induction' with
    | mem μ m hm => exact Submodule.mem_iSup_of_mem μ (symm_zero_mem_weightSpaceOfMap c hm)
    | zero =>
      rw [show ((0 : N), (0 : M)) = 0 from rfl, map_zero]; exact Submodule.zero_mem _
    | add m m' _ _ h h' =>
      have : ((equiv c).symm (0, m + m') : Extension c) =
          (equiv c).symm (0, m) + (equiv c).symm (0, m') := by
        rw [← map_add, Prod.mk_add_mk, add_zero]
      rw [this]; exact Submodule.add_mem _ h h'
  rw [eq_top_iff]
  rintro v -
  have hv : v = inl c (equiv c v).1 + (equiv c).symm (0, (equiv c v).2) := by
    rw [ext_iff']
    exact ⟨(add_zero _).symm, (zero_add _).symm⟩
  rw [hv]
  exact Submodule.add_mem _ (hinl _) (hsnd _)

/-- The linear map `E_μ → N_μ × M_μ`, injective. -/
def weightSpaceMap (μ : Dual K H) :
    weightSpaceOfMap (Extension c) φ μ →ₗ[K] weightSpaceOfMap N φ μ × weightSpaceOfMap M φ μ :=
  LinearMap.prod
    (((LinearMap.fst K N M ∘ₗ (equiv c).toLinearMap ∘ₗ
      (weightSpaceOfMap (Extension c) φ μ).subtype).codRestrict _ fun v ↦
        ((mem_weightSpaceOfMap_iff c μ v).mp v.2).1))
    (((LinearMap.snd K N M ∘ₗ (equiv c).toLinearMap ∘ₗ
      (weightSpaceOfMap (Extension c) φ μ).subtype).codRestrict _ fun v ↦
        ((mem_weightSpaceOfMap_iff c μ v).mp v.2).2))

theorem injective_weightSpaceMap (μ : Dual K H) : Function.Injective (weightSpaceMap c μ) := by
  intro v w h
  have h1 := congrArg (fun p ↦ (p.1 : N)) h
  have h2 := congrArg (fun p ↦ (p.2 : M)) h
  exact Subtype.ext ((ext_iff' c).mpr ⟨h1, h2⟩)

end Extension

/-- **Splitting criterion.** The class of a cocycle `c` vanishes iff the extension
`0 → N → E_c → M → 0` splits. -/
theorem mk_eq_zero_iff (c : extCocycles φ M N) :
    mk c = 0 ↔ ∃ σ : M →ₗ⁅K,L⁆ Extension c, ∀ m, Extension.snd c (σ m) = m := by
  rw [mk_eq_zero_iff_exists]
  constructor
  · rintro ⟨f, -, hf⟩
    refine ⟨{ toLinearMap := (Extension.equiv c).symm.toLinearMap ∘ₗ LinearMap.prod (-f)
                LinearMap.id
              map_lie' := fun {x m} ↦ ?_ }, fun m ↦ rfl⟩
    rw [Extension.ext_iff']
    refine ⟨?_, rfl⟩
    change -f ⁅x, m⁆ = ⁅x, -f m⁆ + c.1 x m
    rw [hf, lie_neg]
    abel
  · rintro ⟨σ, hσ⟩
    let f : M →ₗ[K] N := -(LinearMap.fst K N M ∘ₗ (Extension.equiv c).toLinearMap ∘ₗ
      (σ : M →ₗ[K] Extension c))
    have hf : ∀ m, f m = -(Extension.equiv c (σ m)).1 := fun m ↦ rfl
    have hσ2 : ∀ m, (Extension.equiv c (σ m)).2 = m := hσ
    have key : ∀ x m, (Extension.equiv c (σ ⁅x, m⁆)).1 =
        ⁅x, (Extension.equiv c (σ m)).1⁆ + c.1 x m := by
      intro x m
      rw [LieModuleHom.map_lie, Extension.fst_lie, hσ2]
    refine ⟨f, fun a m ↦ ?_, fun x m ↦ ?_⟩
    · rw [hf, hf, key, extCocycles.map_apply_eq_zero c, LinearMap.zero_apply, add_zero, lie_neg]
    · rw [hf, hf, key, lie_neg]
      abel

/-! ### Functoriality in the first variable -/

variable (φ) in
/-- Pulling back cocycles along a module map `g : A → M`. -/
def cocycleComap (g : A →ₗ⁅K,L⁆ M) : extCocycles φ M N →ₗ[K] extCocycles φ A N where
  toFun c := ⟨fun x ↦ c.1 x ∘ₗ (g : A →ₗ[K] M),
    ⟨fun x y ↦ by dsimp only; rw [extCocycles.map_add' c, LinearMap.add_comp],
     fun t x ↦ by dsimp only; rw [extCocycles.map_smul' c, LinearMap.smul_comp],
     fun a ↦ by dsimp only; rw [extCocycles.map_apply_eq_zero c, LinearMap.zero_comp],
     fun x y ↦ by
      ext m
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply, LieHom.lie_apply,
        extCocycles.apply_lie_apply c, LieModuleHom.coe_toLinearMap, LieModuleHom.map_lie]⟩⟩
  map_add' c d := rfl
  map_smul' t c := rfl

/-- `ExtOne φ M N → ExtOne φ A N` induced by `g : A → M`. -/
def comap (g : A →ₗ⁅K,L⁆ M) : ExtOne φ M N →ₗ[K] ExtOne φ A N :=
  Submodule.mapQ _ _ (cocycleComap φ g) (by
    rintro _ ⟨f, rfl⟩
    refine ⟨⟨(f : M →ₗ[K] N) ∘ₗ (g : A →ₗ[K] M), fun a m ↦ ?_⟩, ?_⟩
    · simp [f.2 a]
    · apply Subtype.ext
      funext x
      ext m
      change ⁅x, (f : M →ₗ[K] N) ∘ₗ (g : A →ₗ[K] M)⁆ m = ⁅x, (f : M →ₗ[K] N)⁆ (g m)
      rw [LieHom.lie_apply, LieHom.lie_apply]
      simp)

@[simp] theorem comap_mk (g : A →ₗ⁅K,L⁆ M) (c : extCocycles φ M N) :
    comap g (mk c) = mk (cocycleComap φ g c) := rfl

/-! ### Short exact sequences and the connecting map -/

variable (φ) in
/-- A short exact sequence `0 → A → B → C → 0` of `L`-modules together with a splitting as
vector spaces compatible with `φ(H)`: `p ∘ s = 1`, `r ∘ i = 1`, `i ∘ r + s ∘ p = 1`, with `s` and
`r` commuting with `φ(H)`. -/
@[nolint unusedArguments]
structure SplitData (i : A →ₗ⁅K,L⁆ B) (p : B →ₗ⁅K,L⁆ C) where
  /-- The section of `p`. -/
  s : C →ₗ[K] B
  /-- The retraction of `i`. -/
  r : B →ₗ[K] A
  p_s : ∀ c, p (s c) = c
  r_i : ∀ a, r (i a) = a
  i_r_add_s_p : ∀ b, i (r b) + s (p b) = b
  s_mem : s ∈ relHom φ C B
  r_mem : r ∈ relHom φ B A

namespace SplitData

variable {i : A →ₗ⁅K,L⁆ B} {p : B →ₗ⁅K,L⁆ C} (S : SplitData φ i p)

omit [LieModule K L C] in
include S in
theorem p_i (a : A) : p (i a) = 0 := by
  have h := S.i_r_add_s_p (i a)
  rw [S.r_i, add_eq_left] at h
  simpa [S.p_s] using congrArg p h

omit [LieModule K L C] in
theorem r_s (c : C) : S.r (S.s c) = 0 := by
  have h := S.i_r_add_s_p (S.s c)
  rw [S.p_s, add_eq_right] at h
  have := congrArg S.r h
  rwa [S.r_i, map_zero] at this

omit [LieModule K L C] in
theorem i_r_of_p_eq_zero {b : B} (hb : p b = 0) : i (S.r b) = b := by
  simpa [hb] using S.i_r_add_s_p b

omit [LieModule K L C] in
/-- The defect `x (s c) - s (x c)` lies in the kernel of `p`. -/
theorem p_lie_s_sub (x : L) (c : C) : p (⁅x, S.s c⁆ - S.s ⁅x, c⁆) = 0 := by
  simp [S.p_s]

omit [LieModule K L C] in
/-- Moving `x ∈ L` past `r` on the kernel of `p`. -/
theorem lie_r_of_p_eq_zero (z : L) {b : B} (hb : p b = 0) : ⁅z, S.r b⁆ = S.r ⁅z, b⁆ := by
  have h1 : i ⁅z, S.r b⁆ = ⁅z, b⁆ := by rw [LieModuleHom.map_lie, S.i_r_of_p_eq_zero hb]
  rw [← h1, S.r_i]

/-- The cocycle of the extension: `c(x) = r ∘ ⁅x, s⁆`. -/
def cocycle : extCocycles φ C A :=
  ⟨fun x ↦ S.r ∘ₗ ⁅x, S.s⁆,
    ⟨fun x y ↦ by dsimp only; rw [add_lie, LinearMap.comp_add],
     fun t x ↦ by dsimp only; rw [smul_lie, LinearMap.comp_smul],
     fun a ↦ by ext c; simp [LieHom.lie_apply, S.s_mem a c], fun x y ↦ by
      ext c
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply, LieHom.lie_apply]
      rw [S.lie_r_of_p_eq_zero x (S.p_lie_s_sub y c), S.lie_r_of_p_eq_zero y (S.p_lie_s_sub x c)]
      simp only [← map_sub]
      congr 1
      rw [lie_lie, lie_lie, map_sub]
      simp only [lie_sub]
      abel⟩⟩

theorem cocycle_apply (x : L) (c : C) :
    S.cocycle.1 x c = S.r (⁅x, S.s c⁆ - S.s ⁅x, c⁆) := by
  rfl

theorem i_cocycle_apply (x : L) (c : C) :
    i (S.cocycle.1 x c) = ⁅x, S.s c⁆ - S.s ⁅x, c⁆ := by
  rw [cocycle_apply, S.i_r_of_p_eq_zero (S.p_lie_s_sub x c)]

/-- Pushing the cocycle forward along `f : A → N`. -/
def pushCocycle (f : A →ₗ⁅K,L⁆ N) : extCocycles φ C N :=
  ⟨fun x ↦ (f : A →ₗ[K] N) ∘ₗ S.cocycle.1 x,
    ⟨fun x y ↦ by dsimp only; rw [extCocycles.map_add' S.cocycle, LinearMap.comp_add],
     fun t x ↦ by dsimp only; rw [extCocycles.map_smul' S.cocycle, LinearMap.comp_smul],
     fun a ↦ by dsimp only; rw [extCocycles.map_apply_eq_zero S.cocycle, LinearMap.comp_zero],
     fun x y ↦ by
      ext c
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply, LieHom.lie_apply,
        extCocycles.apply_lie_apply S.cocycle, map_sub, LieModuleHom.coe_toLinearMap,
        LieModuleHom.map_lie]⟩⟩

theorem pushCocycle_apply (f : A →ₗ⁅K,L⁆ N) (x : L) (c : C) :
    (S.pushCocycle f).1 x c = f (S.cocycle.1 x c) := rfl

/-- The connecting map `δ : Hom(A, N) → ExtOne φ C N`. -/
def connecting : (A →ₗ⁅K,L⁆ N) →ₗ[K] ExtOne φ C N where
  toFun f := ExtOne.mk (S.pushCocycle f)
  map_add' f g := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
  map_smul' t f := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1

theorem connecting_apply (f : A →ₗ⁅K,L⁆ N) :
    S.connecting f = ExtOne.mk (S.pushCocycle f) := rfl

/-- **Exactness at `Hom(A, N)`.** `δ f = 0` iff `f` extends along `i : A → B`. -/
theorem connecting_eq_zero_iff (f : A →ₗ⁅K,L⁆ N) :
    S.connecting f = 0 ↔ ∃ g : B →ₗ⁅K,L⁆ N, g.comp i = f := by
  rw [connecting_apply, mk_eq_zero_iff_exists]
  constructor
  · rintro ⟨e, -, hfe⟩
    -- `g = f ∘ r + e ∘ p`
    let g₀ : B →ₗ[K] N := (f : A →ₗ[K] N) ∘ₗ S.r + e ∘ₗ (p : B →ₗ[K] C)
    have hg₀i : ∀ a, g₀ (i a) = f a := fun a ↦ by
      simp [g₀, S.r_i, S.p_i]
    have hg₀s : ∀ c, g₀ (S.s c) = e c := fun c ↦ by
      simp [g₀, S.r_s, S.p_s]
    have hlie : ∀ (x : L) b, g₀ ⁅x, b⁆ = ⁅x, g₀ b⁆ := by
      intro x b
      rw [← S.i_r_add_s_p b, lie_add, map_add, map_add, lie_add, ← LieModuleHom.map_lie, hg₀i,
        hg₀i, LieModuleHom.map_lie]
      congr 1
      have h2 : ⁅x, S.s (p b)⁆ = i (S.cocycle.1 x (p b)) + S.s ⁅x, p b⁆ := by
        rw [S.i_cocycle_apply]; abel
      rw [h2, map_add, hg₀i, hg₀s, hg₀s, ← pushCocycle_apply, hfe]
      abel
    refine ⟨{ toLinearMap := g₀, map_lie' := fun {x b} ↦ hlie x b }, ?_⟩
    ext a
    exact hg₀i a
  · rintro ⟨g, rfl⟩
    refine ⟨(g : B →ₗ[K] N) ∘ₗ S.s, fun a c ↦ ?_, fun x c ↦ ?_⟩
    · simp [S.s_mem a c]
    · rw [pushCocycle_apply]
      simp only [LieModuleHom.coe_comp, Function.comp_apply, S.i_cocycle_apply, map_sub,
        LieModuleHom.map_lie, LinearMap.coe_comp, LieModuleHom.coe_toLinearMap]

/-- The connecting map of `id_A` is the class of the sequence; it vanishes iff the sequence
splits. -/
theorem connecting_id_eq_zero_iff :
    S.connecting (LieModuleHom.id : A →ₗ⁅K,L⁆ A) = 0 ↔
      ∃ g : B →ₗ⁅K,L⁆ A, ∀ a, g (i a) = a := by
  rw [connecting_eq_zero_iff]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, fun a ↦ LieModuleHom.congr_fun hg a⟩,
    fun ⟨g, hg⟩ ↦ ⟨g, LieModuleHom.ext hg⟩⟩

/-- **Exactness at `ExtOne φ C N`** (one inclusion): a class whose pullback along `p` vanishes
is in the image of the connecting map. -/
theorem exists_connecting_eq {y : ExtOne φ C N} (hy : comap p y = 0) :
    ∃ f : A →ₗ⁅K,L⁆ N, S.connecting f = y := by
  obtain ⟨c, rfl⟩ := mk_surjective y
  rw [comap_mk, mk_eq_zero_iff_exists] at hy
  obtain ⟨g, hg, hgc⟩ := hy
  have hgc' : ∀ x b, c.1 x (p b) = ⁅x, g b⁆ - g ⁅x, b⁆ := hgc
  -- `g ∘ i` is a module map
  have hgi : ∀ (x : L) a, g (i ⁅x, a⁆) = ⁅x, g (i a)⁆ := by
    intro x a
    have := hgc' x (i a)
    rw [S.p_i, map_zero, eq_comm, sub_eq_zero, ← LieModuleHom.map_lie] at this
    exact this.symm
  let f : A →ₗ⁅K,L⁆ N :=
    { toLinearMap := -(g ∘ₗ (i : A →ₗ[K] B))
      map_lie' := fun {x a} ↦ by
        change -(g (i ⁅x, a⁆)) = ⁅x, -(g (i a))⁆
        rw [hgi, lie_neg] }
  refine ⟨f, ?_⟩
  rw [connecting_apply, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_iff_exists]
  refine ⟨-(g ∘ₗ S.s), fun a c' ↦ ?_, fun x c' ↦ ?_⟩
  · simp [hg a, S.s_mem a c']
  · change (S.pushCocycle f).1 x c' - c.1 x c' = _
    have h1 : c.1 x c' = ⁅x, g (S.s c')⁆ - g ⁅x, S.s c'⁆ := by
      rw [← hgc', S.p_s]
    have h2 : (S.pushCocycle f).1 x c' = -(g (⁅x, S.s c'⁆ - S.s ⁅x, c'⁆)) := by
      change -(g (i _)) = _
      rw [S.i_cocycle_apply]
    rw [h1, h2, map_sub]
    simp only [LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply, lie_neg]
    abel

/-- **The connecting isomorphism.** If `Hom(B, N) = 0` and `ExtOne φ B N = 0`, then
`δ : Hom(A, N) ≅ ExtOne φ C N`. -/
def connectingEquiv (hHom : ∀ g : B →ₗ⁅K,L⁆ N, g = 0)
    (hExt : ∀ y : ExtOne φ B N, y = 0) : (A →ₗ⁅K,L⁆ N) ≃ₗ[K] ExtOne φ C N :=
  LinearEquiv.ofBijective S.connecting
    ⟨(injective_iff_map_eq_zero _).mpr fun f hf ↦ by
      obtain ⟨g, rfl⟩ := (S.connecting_eq_zero_iff f).mp hf
      rw [hHom g]
      rfl,
     fun y ↦ S.exists_connecting_eq (hExt _)⟩

theorem connectingEquiv_apply (hHom : ∀ g : B →ₗ⁅K,L⁆ N, g = 0)
    (hExt : ∀ y : ExtOne φ B N, y = 0) (f : A →ₗ⁅K,L⁆ N) :
    S.connectingEquiv hHom hExt f = S.connecting f := rfl

end SplitData

/-! ### Existence of equivariant splittings for weight modules -/

variable (φ)

omit [LieModule K L C] in
/-- Given an exact sequence `0 → A → B → C → 0` and an equivariant section of `p`, there is
`SplitData`. -/
theorem exists_splitData_of_section {i : A →ₗ⁅K,L⁆ B} {p : B →ₗ⁅K,L⁆ C}
    (hi : Function.Injective i) (hexact : ∀ b, p b = 0 ↔ ∃ a, i a = b) (s : C →ₗ[K] B)
    (hps : ∀ c, p (s c) = c) (hs : s ∈ relHom φ C B) : Nonempty (SplitData φ i p) := by
  classical
  have hpi : ∀ a, p (i a) = 0 := fun a ↦ (hexact (i a)).mpr ⟨a, rfl⟩
  have hmem : ∀ b, b - s (p b) ∈ LinearMap.range (i : A →ₗ[K] B) := fun b ↦ by
    obtain ⟨a, ha⟩ := (hexact (b - s (p b))).mp (by simp [hps])
    exact ⟨a, ha⟩
  let e := LinearEquiv.ofInjective (i : A →ₗ[K] B) hi
  let r : B →ₗ[K] A := e.symm.toLinearMap ∘ₗ
    ((LinearMap.id - s ∘ₗ (p : B →ₗ[K] C)).codRestrict _ hmem)
  have hir : ∀ b, i (r b) = b - s (p b) := fun b ↦ by
    have := LinearEquiv.ofInjective_symm_apply (f := (i : A →ₗ[K] B)) (h := hi)
      ⟨b - s (p b), hmem b⟩
    exact this
  have hri : ∀ a, r (i a) = a := fun a ↦ hi (by rw [hir, hpi, map_zero, sub_zero])
  exact ⟨{
    s := s
    r := r
    p_s := hps
    r_i := hri
    i_r_add_s_p := fun b ↦ by rw [hir]; abel
    s_mem := hs
    r_mem := fun a b ↦ hi (by
      rw [hir, LieModuleHom.map_lie i, hir, LieModuleHom.map_lie p, hs a, lie_sub]) }⟩

/-- A module map sends weight vectors to weight vectors of the same weight. -/
theorem map_mem_weightSpaceOfMap (g : B →ₗ⁅K,L⁆ C) {μ : Dual K H} {b : B}
    (hb : b ∈ weightSpaceOfMap B φ μ) : g b ∈ weightSpaceOfMap C φ μ := fun a ↦ by
  rw [← LieModuleHom.map_lie, hb a, map_smul]

/-- A surjective module map out of a sum of weight spaces is surjective on each weight space. -/
theorem exists_mem_weightSpaceOfMap_of_surjective (hB : ⨆ μ, weightSpaceOfMap B φ μ = ⊤)
    {g : B →ₗ⁅K,L⁆ C} (hg : Function.Surjective g) {μ : Dual K H} {c : C}
    (hc : c ∈ weightSpaceOfMap C φ μ) : ∃ b ∈ weightSpaceOfMap B φ μ, g b = c := by
  have hle : ∀ ν, (weightSpaceOfMap B φ ν).map (g : B →ₗ[K] C) ≤ weightSpaceOfMap C φ ν :=
    fun ν ↦ by
      rintro _ ⟨v, hv, rfl⟩
      exact map_mem_weightSpaceOfMap φ g hv
  obtain ⟨b, hb, hbc⟩ := mem_of_mem_iSup_of_le φ _ hle hc (by
    rw [← Submodule.map_iSup, hB, Submodule.map_top, LinearMap.range_eq_top.mpr hg]
    trivial)
  exact ⟨b, hb, hbc⟩

/-- **Equivariant sections.** A surjective module map `p : B → C` between sums of weight spaces
has a linear section commuting with `φ(H)`. -/
theorem exists_relHom_section (hB : ⨆ μ, weightSpaceOfMap B φ μ = ⊤)
    (hC : ⨆ μ, weightSpaceOfMap C φ μ = ⊤) {p : B →ₗ⁅K,L⁆ C} (hp : Function.Surjective p) :
    ∃ s : C →ₗ[K] B, (∀ c, p (s c) = c) ∧ s ∈ relHom φ C B := by
  classical
  have hint : DirectSum.IsInternal (fun μ ↦ weightSpaceOfMap C φ μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_weightSpaceOfMap φ) hC
  let bC := hint.collectedBasis fun μ ↦ Basis.ofVectorSpace K (weightSpaceOfMap C φ μ)
  have hbC : ∀ j, bC j ∈ weightSpaceOfMap C φ j.1 := fun j ↦ hint.collectedBasis_mem _ j
  have hpre : ∀ j, ∃ b ∈ weightSpaceOfMap B φ j.1, p b = bC j := fun j ↦
    exists_mem_weightSpaceOfMap_of_surjective φ hB hp (hbC j)
  choose pre hpreW hpreP using hpre
  let s : C →ₗ[K] B := bC.constr K pre
  have hs : ∀ j, s (bC j) = pre j := fun j ↦ bC.constr_basis K pre j
  refine ⟨s, fun c ↦ ?_, fun a c ↦ ?_⟩
  · have := bC.ext (f₁ := (p : B →ₗ[K] C) ∘ₗ s) (f₂ := LinearMap.id) fun j ↦ by
      simp [hs, hpreP]
    exact LinearMap.congr_fun this c
  · have := bC.ext (f₁ := s ∘ₗ (toEnd K L C (φ a) : C →ₗ[K] C))
      (f₂ := (toEnd K L B (φ a) : B →ₗ[K] B) ∘ₗ s) fun j ↦ by
        simp only [LinearMap.coe_comp, Function.comp_apply, toEnd_apply_apply, hbC j a,
          map_smul, hs, hpreW j a]
    exact LinearMap.congr_fun this c

/-- For an exact sequence `0 → A → B → C → 0` of sums of weight spaces there is `SplitData`. -/
theorem exists_splitData (hB : ⨆ μ, weightSpaceOfMap B φ μ = ⊤)
    (hC : ⨆ μ, weightSpaceOfMap C φ μ = ⊤) {i : A →ₗ⁅K,L⁆ B} {p : B →ₗ⁅K,L⁆ C}
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : ∀ b, p b = 0 ↔ ∃ a, i a = b) : Nonempty (SplitData φ i p) := by
  obtain ⟨s, hps, hs⟩ := exists_relHom_section φ hB hC hp
  exact exists_splitData_of_section φ hi hexact s hps hs

end ExtOne

end LieModule
