/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HighestWeight
import LieLean.Algebra.Lie.UniversalEnveloping.Domain
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroup

/-!
# Homomorphisms between Verma modules

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a realization of a matrix `A` over a field `K` of
characteristic zero, and let `M(λ)` be the Verma module of highest weight `λ ∈ 𝔥*`.

* Morphisms of `𝔤`-modules `M(μ) → V` correspond to the *primitive vectors* of weight `μ` of `V`,
  i.e. the vectors of weight `μ` killed by all the `eᵢ` (`VermaModule.homEquiv`). In particular
  there is a nonzero morphism `M(μ) → M(λ)` if and only if `M(λ)` has a nonzero primitive vector
  of weight `μ`.
* Every nonzero morphism `M(μ) → M(λ)` is injective ([HumO] Thm. 4.2 (a) (check)): `M(λ)` is a
  free `U(𝔫₋)`-module of rank one and `U(𝔫₋)` is a domain.
* If `⟨λ + ρ, αᵢ^∨⟩ = n` is a positive integer, then `fᵢⁿ v_λ` is a primitive vector of weight
  `rᵢ · λ = rᵢ(λ + ρ) - ρ = λ - n αᵢ`, which gives an embedding `M(rᵢ · λ) ↪ M(λ)`, and
  `Hom(M(rᵢ · λ), M(λ))` is one-dimensional ([HumO] Prop. 1.4 and §4.2 (check);
  [Kac] §9 (check)).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.primitiveVectors`: the space of vectors of weight `μ`
  killed by all the `eᵢ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.homEquiv`: the linear isomorphism
  `Hom_𝔤(M(μ), V) ≃ {primitive vectors of weight μ in V}`, `φ ↦ φ(v_μ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.injective_of_ne_zero`: nonzero morphisms
  of Verma modules are injective.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_ne_zero_iff`: there is a nonzero
  morphism `M(μ) → M(λ)` iff `M(λ)` has a nonzero primitive vector of weight `μ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_injective_reflection`: the embedding
  `M(rᵢ · λ) ↪ M(λ)` when `⟨λ + ρ, αᵢ^∨⟩ ∈ ℤ_{>0}`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_hom_reflection`:
  `dim Hom(M(rᵢ · λ), M(λ)) = 1` in that case.

## Remark

[HumO] Thm. 4.2 (b) also states `dim Hom(M(μ), M(λ)) ≤ 1` for all `μ, λ` for a
finite-dimensional semisimple Lie algebra. The proof given there uses that `U(𝔫₋)` is a
(left Noetherian, hence) left Ore domain, so that any two nonzero submodules of `M(λ)` meet
nontrivially. For a general Kac–Moody algebra `U(𝔫₋)` need not be Noetherian nor Ore (`𝔫₋` can
contain free Lie algebras on two generators), so this argument does not carry over, and the
general statement is not proved here; we only prove the case `μ = rᵢ · λ`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §1.4, §4.1–4.2 (check).
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.2–9.3 (check).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))

/-! ### Primitive vectors -/

section Primitive

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- The space of *primitive vectors* of weight `μ` of a `𝔤(A)`-module `V`: the vectors of weight
`μ` killed by all the `eᵢ` (hence by `𝔫₊`, `lie_eq_zero_of_mem_nPos`). These are called maximal
vectors in [HumO] §1.2 (check). -/
def primitiveVectors (μ : Dual K H) : Submodule K V :=
  weightSpace P V μ ⊓ ⨅ i, LinearMap.ker (toEnd K P.KacMoodyAlgebra V (e P i))

variable {P V}

lemma mem_primitiveVectors {μ : Dual K H} {v : V} :
    v ∈ primitiveVectors P V μ ↔ v ∈ weightSpace P V μ ∧ ∀ i, ⁅e P i, v⁆ = 0 := by
  simp [primitiveVectors, Submodule.mem_iInf]

end Primitive

namespace VermaModule

variable {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

lemma hwv_mem_primitiveVectors (Λ : Dual K H) :
    hwv P Λ ∈ primitiveVectors P (VermaModule P Λ) Λ :=
  mem_primitiveVectors.mpr ⟨hwv_mem_weightSpace P Λ, lie_e_hwv P Λ⟩

lemma map_hwv_mem_primitiveVectors {μ : Dual K H}
    (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) :
    φ (hwv P μ) ∈ primitiveVectors P V μ :=
  mem_primitiveVectors.mpr ⟨map_mem_weightSpaceOfMap P φ (hwv_mem_weightSpace P μ),
    fun i ↦ by rw [← LieModuleHom.map_lie, lie_e_hwv, map_zero]⟩

variable (V) in
/-- **Universal property of Verma modules, linear form** ([Kac] §9.2 (check)): morphisms of
`𝔤(A)`-modules `M(μ) → V` correspond to the primitive vectors of weight `μ` of `V`, via
`φ ↦ φ(v_μ)`. -/
def homEquiv (μ : Dual K H) :
    (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) ≃ₗ[K] primitiveVectors P V μ where
  toFun φ := ⟨φ (hwv P μ), map_hwv_mem_primitiveVectors P φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := lift P v.1
    (fun _ hx ↦ lie_eq_zero_of_mem_nPos (mem_primitiveVectors.mp v.2).2 hx)
    (fun a ↦ (mem_primitiveVectors.mp v.2).1 a)
  left_inv _ := hom_ext P μ (lift_hwv P _ _ _)
  right_inv _ := Subtype.ext (lift_hwv P _ _ _)

@[simp] lemma homEquiv_apply (μ : Dual K H) (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) :
    (homEquiv P V μ φ : V) = φ (hwv P μ) := rfl

/-- A morphism out of `M(μ)` is zero iff it kills `v_μ`. -/
lemma eq_zero_iff {μ : Dual K H} (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) :
    φ = 0 ↔ φ (hwv P μ) = 0 := by
  rw [← homEquiv_apply, ← ZeroMemClass.coe_zero (primitiveVectors P V μ), Subtype.coe_inj,
    LinearEquiv.map_eq_zero_iff]

/-- There is a nonzero morphism `M(μ) → V` iff `V` has a nonzero primitive vector of weight `μ`
([Kac] §9.2–9.3 (check); [HumO] §1.3 (check)). -/
theorem exists_ne_zero_iff (μ : Dual K H) :
    (∃ φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ V, φ ≠ 0) ↔
      ∃ v ∈ weightSpaceOfMap V (h P) μ, v ≠ 0 ∧ ∀ i, ⁅e P i, v⁆ = 0 := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ (hwv P μ), (mem_primitiveVectors.mp (map_hwv_mem_primitiveVectors P φ)).1,
      fun h ↦ hφ ((eq_zero_iff P φ).mpr h),
      (mem_primitiveVectors.mp (map_hwv_mem_primitiveVectors P φ)).2⟩
  · rintro ⟨v, hv, hv0, he⟩
    refine ⟨(homEquiv P V μ).symm ⟨v, mem_primitiveVectors.mpr ⟨hv, he⟩⟩, fun h ↦ hv0 ?_⟩
    have := congrArg (fun φ ↦ (homEquiv P V μ φ : V)) h
    simpa using this

/-- `dim Hom(M(μ), V)` is the dimension of the space of primitive vectors of weight `μ`. -/
theorem finrank_hom (μ : Dual K H) :
    finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) =
      finrank K (primitiveVectors P V μ) :=
  (homEquiv P V μ).finrank_eq

/-! ### Morphisms between Verma modules are injective -/

variable [CharZero K]

omit [CharZero K] in
/-- The action of `U(𝔤)` on `M(Λ)` through `VermaModule.rep` is the module structure. -/
lemma rep_apply (Λ : Dual K H) (u : 𝓤) (m : VermaModule P Λ) :
    rep P (VermaModule P Λ) u m = u • m := by
  induction u using UniversalEnvelopingAlgebra.induction generalizing m with
  | algebraMap r => rw [AlgHom.commutes, Module.algebraMap_end_apply, algebraMap_smul]
  | ι x => rw [rep_ι, lie_eq_smul]
  | mul a b ha hb => rw [map_mul, Module.End.mul_apply, hb, ha, mul_smul]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_smul]

omit [CharZero K] in
/-- A morphism of `𝔤(A)`-modules between Verma modules is `U(𝔤)`-linear. -/
lemma map_smul_eq_smul {Λ μ : Dual K H}
    (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ)
    (u : 𝓤) (m : VermaModule P μ) : φ (u • m) = u • φ m := by
  rw [map_smul_eq_rep, rep_apply]

/-- **Morphisms of Verma modules are injective** ([HumO] Thm. 4.2 (a) (check); [Kac] §9
(check)): every nonzero morphism of `𝔤(A)`-modules `M(μ) → M(λ)` is injective. Indeed
`M(λ) ≅ U(𝔫₋)` as a `U(𝔫₋)`-module (`VermaModule.equivEnvNNeg`) and `U(𝔫₋)` is a domain
(`UniversalEnvelopingAlgebra.instIsDomain`). -/
theorem injective_of_ne_zero {Λ μ : Dual K H}
    {φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ} (hφ : φ ≠ 0) :
    Function.Injective φ := by
  have hw : φ (hwv P μ) ≠ 0 := fun h ↦ hφ ((eq_zero_iff P φ).mpr h)
  obtain ⟨u₀, hu₀⟩ := (equivEnvNNeg P Λ).surjective (φ (hwv P μ))
  have hu₀0 : u₀ ≠ 0 := by rintro rfl; rw [map_zero] at hu₀; exact hw hu₀.symm
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨u, rfl⟩ := (equivEnvNNeg P μ).surjective m
  rw [equivEnvNNeg_apply, map_smul_eq_smul, ← hu₀, ← equivEnvNNeg_mul,
    LinearEquiv.map_eq_zero_iff] at hm
  rw [(mul_eq_zero.mp hm).resolve_right hu₀0, map_zero]

/-- A nonzero morphism `M(μ) → M(λ)` exists iff `M(λ)` has a nonzero primitive vector of weight
`μ`, and then every nonzero such morphism is injective ([HumO] Thm. 4.2 (check)). -/
theorem exists_injective_iff (Λ μ : Dual K H) :
    (∃ φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ, Function.Injective φ) ↔
      ∃ v ∈ weightSpace P Λ μ, v ≠ 0 ∧ ∀ i, ⁅e P i, v⁆ = 0 := by
  refine Iff.trans ?_ (exists_ne_zero_iff P μ)
  refine ⟨fun ⟨φ, hφ⟩ ↦ ⟨φ, fun h ↦ ?_⟩, fun ⟨φ, hφ⟩ ↦ ⟨φ, injective_of_ne_zero P hφ⟩⟩
  exact hwv_ne_zero P μ (hφ (by rw [h, _root_.zero_apply, map_zero]))

/-! ### The embeddings `M(rᵢ · λ) ↪ M(λ)` -/

omit [CharZero K] in
lemma toEnd_pow_apply {Λ : Dual K H} (x : P.KacMoodyAlgebra) (n : ℕ) (m : VermaModule P Λ) :
    (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) x ^ n) m = (ιᵤ x) ^ n • m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, toEnd_apply_apply, lie_eq_smul, pow_succ',
      mul_smul]

/-- `fᵢⁿ v_λ ≠ 0` in `M(λ)`, since `U(𝔫₋)` is a domain. -/
theorem toEnd_f_pow_hwv_ne_zero (Λ : Dual K H) (i : ι) (n : ℕ) :
    (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) (hwv P Λ) ≠ 0 := by
  have hf : UniversalEnvelopingAlgebra.ι K (⟨f P i, f_mem_nNeg P i⟩ : nNeg P) ≠ 0 := fun h0 ↦
    f_ne_zero P i (congrArg Subtype.val
      (UniversalEnvelopingAlgebra.ι_injective (R := K) (L := nNeg P)
        (h0.trans (map_zero _).symm)))
  have : (ιᵤ (f P i)) ^ n =
      mapN ((UniversalEnvelopingAlgebra.ι K (⟨f P i, f_mem_nNeg P i⟩ : nNeg P)) ^ n) := by
    rw [map_pow, UniversalEnvelopingAlgebra.map_ι]
    rfl
  rw [toEnd_pow_apply, this, ← equivEnvNNeg_apply, ne_eq, LinearEquiv.map_eq_zero_iff]
  exact pow_ne_zero _ hf

omit [CharZero K] in
/-- `fᵢⁿ = f_{i} ⋯ f_{i}` as a word. -/
lemma fWord_replicate (i : ι) (n : ℕ) : fWord P (List.replicate n i) = (ιᵤ (f P i)) ^ n := by
  simp [fWord]

/-- `M(λ)_{λ - n αᵢ} = K fᵢⁿ v_λ`: the only way to write `n αᵢ` as a sum of simple roots is
`αᵢ + ⋯ + αᵢ`. -/
theorem weightSpace_sub_nsmul_root (Λ : Dual K H) (i : ι) (n : ℕ) :
    weightSpace P Λ (Λ - n • P.root i) =
      K ∙ (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) (hwv P Λ) := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr
    (toEnd_f_pow_mem_weightSpace i (hwv_mem_weightSpace P Λ) n))
  rw [weightSpace_eq_wordSpan, wordSpan, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  have hc : AuxLieAlgebra.counts w = n • Pi.single i 1 := by
    refine P.rootOf_injective ?_
    rw [← AuxLieAlgebra.wordWt_eq_rootOf, map_nsmul, rootOf_single]
    exact sub_right_injective hw
  have hw' : w = List.replicate n i := by
    cases w with
    | nil =>
      have := congrFun hc i
      simp only [AuxLieAlgebra.counts_nil, Pi.zero_apply, Pi.smul_apply, Pi.single_eq_same,
        nsmul_eq_mul, mul_one] at this
      rw [show n = 0 by exact_mod_cast this.symm, List.replicate_zero]
    | cons j l =>
      obtain ⟨rfl, rfl⟩ := AuxLieAlgebra.eq_replicate_of_counts_eq hc
      have := congrFun hc j
      simp only [AuxLieAlgebra.counts, List.count_cons_self, List.count_replicate_self,
        Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one] at this
      rw [← List.replicate_succ]
      congr 1
      omega
  rw [SetLike.mem_coe, hw']
  dsimp only
  rw [fWord_replicate, ← toEnd_pow_apply]
  exact Submodule.mem_span_singleton_self _

omit [DecidableEq ι] [CharZero K] in
/-- For the dot action `rᵢ · λ = rᵢ(λ + ρ) - ρ`: if `⟨λ + ρ, αᵢ^∨⟩ = n`, then
`rᵢ · λ = λ - n αᵢ`. (This does not depend on the choice of `ρ`, which only enters through
`⟨ρ, αᵢ^∨⟩ = 1`.) -/
lemma _root_.Matrix.Realization.reflection_add_rho_sub_rho (hA : A.IsGeneralizedCartan)
    {Λ : Dual K H} {i : ι} {n : ℕ}
    (hn : (Λ + P.rho) (P.coroot i) = n) :
    P.reflection hA i (Λ + P.rho) - P.rho = Λ - n • P.root i := by
  rw [reflection_apply, hn, Nat.cast_smul_eq_nsmul]
  abel

variable (hA : A.IsGeneralizedCartan)
include hA

/-- **Singular vectors for simple reflections** ([HumO] Prop. 1.4 (check), [Kac] §9 (check)): if
`⟨λ + ρ, αᵢ^∨⟩ = n` is a positive integer, then `fᵢⁿ v_λ` is a nonzero primitive vector of
`M(λ)` of weight `rᵢ · λ = λ - n αᵢ`. -/
theorem toEnd_f_pow_hwv_mem_primitiveVectors {Λ : Dual K H} {i : ι} {n : ℕ} (hn0 : 0 < n)
    (hn : (Λ + P.rho) (P.coroot i) = n) :
    (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) (hwv P Λ) ∈
      primitiveVectors P (VermaModule P Λ) (P.reflection hA i (Λ + P.rho) - P.rho) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : Λ (P.coroot i) = m := by
    rw [LinearMap.add_apply, rho_coroot, Nat.cast_succ] at hn
    exact add_right_cancel hn
  rw [P.reflection_add_rho_sub_rho hA hn]
  exact mem_primitiveVectors.mpr ⟨toEnd_f_pow_mem_weightSpace i (hwv_mem_weightSpace P Λ) _,
    lie_e_fPowHwv P Λ hA hm⟩

/-- **The embedding `M(rᵢ · λ) ↪ M(λ)`** ([HumO] Prop. 1.4, §4.2 (check); [Kac] §9 (check)):
if `⟨λ + ρ, αᵢ^∨⟩ = n` is a positive integer, there is an injective morphism of `𝔤(A)`-modules
`M(rᵢ · λ) → M(λ)`, where `rᵢ · λ = rᵢ(λ + ρ) - ρ = λ - n αᵢ`, sending `v_{rᵢ · λ}` to
`fᵢⁿ v_λ`. -/
theorem exists_injective_reflection {Λ : Dual K H} {i : ι} {n : ℕ} (hn0 : 0 < n)
    (hn : (Λ + P.rho) (P.coroot i) = n) :
    ∃ φ : VermaModule P (P.reflection hA i (Λ + P.rho) - P.rho) →ₗ⁅K,P.KacMoodyAlgebra⁆
        VermaModule P Λ, Function.Injective φ ∧
      φ (hwv P _) = (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) (hwv P Λ) := by
  set φ := (homEquiv P (VermaModule P Λ) _).symm
    ⟨_, toEnd_f_pow_hwv_mem_primitiveVectors P hA hn0 hn⟩
  have hφ : φ (hwv P _) = (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n)
      (hwv P Λ) := by
    rw [← homEquiv_apply, LinearEquiv.apply_symm_apply]
  refine ⟨φ, injective_of_ne_zero P fun h ↦ toEnd_f_pow_hwv_ne_zero P Λ i n ?_, hφ⟩
  rw [← hφ, h, _root_.zero_apply]

/-- If `⟨λ + ρ, αᵢ^∨⟩ = n` is a positive integer, then `dim Hom(M(rᵢ · λ), M(λ)) = 1`
([HumO] Thm. 4.2 (b) in this case (check)). -/
theorem finrank_hom_reflection {Λ : Dual K H} {i : ι} {n : ℕ} (hn0 : 0 < n)
    (hn : (Λ + P.rho) (P.coroot i) = n) :
    finrank K (VermaModule P (P.reflection hA i (Λ + P.rho) - P.rho) →ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule P Λ) = 1 := by
  rw [finrank_hom]
  have hmem := toEnd_f_pow_hwv_mem_primitiveVectors P hA hn0 hn
  have heq : primitiveVectors P (VermaModule P Λ) (P.reflection hA i (Λ + P.rho) - P.rho) =
      K ∙ (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) (hwv P Λ) := by
    refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)
    rw [← weightSpace_sub_nsmul_root, ← P.reflection_add_rho_sub_rho hA hn]
    exact inf_le_left
  rw [heq, finrank_span_singleton (toEnd_f_pow_hwv_ne_zero P Λ i n)]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
