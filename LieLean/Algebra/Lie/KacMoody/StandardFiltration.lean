/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Character
import LieLean.Algebra.Lie.KacMoody.CategoryOSubmodule
import LieLean.Algebra.Lie.KacMoody.TensorRep
import LieLean.Algebra.Lie.KacMoody.Integrable
import LieLean.Algebra.Lie.KacMoody.CentralBlocks
import LieLean.Algebra.Lie.KacMoody.TensorVermaFiltration

/-!
# Standard filtrations

A *standard filtration* (Verma flag) of a Lie submodule `N` of a `𝔤(A)`-module `X` is a chain
`0 = N₀ ⊆ N₁ ⊆ ⋯ ⊆ N_r = N` with `N_j / N_{j-1} ≅ M(μ_j)` (Humphreys, GSM 94, §3.7). The
multiset `{μ_j}` of its highest weights is encoded in the predicate `IsStdFiltered P N s`.

The multiplicity `(N : M(μ))` of `M(μ)` in a standard filtration is independent of the filtration:
it is the dimension of the weight-`μ` space of the `𝔫₋`-coinvariants `N / 𝔫₋N`
(`IsStdFiltered.count_eq_coinvDim`). This is the coinvariant form of Humphreys' Theorem 3.7
(`(M : M(λ)) = dim Hom(M, M(λ)^∨)`); the comparison with `Hom(M, M(λ)^∨)` is made in
`KacMoody/DualVerma.lean`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered`: `N` has a standard filtration with highest
  weights `s`.
* `Matrix.Realization.KacMoodyAlgebra.negSpan`: `𝔫₋ N = Σᵢ fᵢ N`.
* `Matrix.Realization.KacMoodyAlgebra.coinvDim`: `dim (N / 𝔫₋N)_ν`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.coinvDim_top`: `dim (M(μ) / 𝔫₋M(μ))_ν = δ_{μν}`.
* `Matrix.Realization.KacMoodyAlgebra.coinvDim_step`: if `N ⊆ N'` and `N'/N ≅ M(μ)`, then
  `dim (N'/𝔫₋N')_ν = dim (N/𝔫₋N)_ν + δ_{μν}`.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.count_eq_coinvDim`: the multiplicity of `μ` in
  a standard filtration of `N` is `dim (N / 𝔫₋N)_μ` (cf. Humphreys, GSM 94, Theorem 3.7).
* `Matrix.Realization.KacMoodyAlgebra.isStdFiltered_of_fin`: filtrations indexed by `Fin (n + 1)`.
* `Matrix.Realization.KacMoodyAlgebra.exists_isStdFiltered_tensorVerma`: `M(Λ) ⊗ Z` has a
  standard filtration with factors `M(Λ + μ)`, `μ` occurring `dim Z_μ` times (Humphreys, GSM 94,
  Theorem 3.6).

## Proof notes

Since `M(μ)` is free over `U(𝔫₋)` on `v_μ` (`VermaModule.equivEnvNNeg`), a step `N'/N ≅ M(μ)`
has a `U(𝔫₋)`-linear section `σ : M(μ) → N'`, `σ(u v_μ) = u x` for a lift `x` of weight `μ` of the
generator (`exists_section`). Then `N ∩ 𝔫₋N' = 𝔫₋N` (`negSpan_inf_le`), so the coinvariants are
additive along the step. This replaces Humphreys' use of `Ext¹_𝒪(M(μ), M(λ)^∨) = 0`
(reconstructed).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.7.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X Y : Type*}
  [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup Y] [Module K Y] [LieRingModule P.KacMoodyAlgebra Y]
  [LieModule K P.KacMoodyAlgebra Y]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))
local notation "wt" => AuxLieAlgebra.wordWt P

section Generic

/-- `IsStdFiltered P N s`: the Lie submodule `N` has a **standard filtration**
`0 = N₀ ⊆ ⋯ ⊆ N_r = N` with `N_j / N_{j-1} ≅ M(μ_j)` and `s = {μ₁, …, μ_r}` (Humphreys, GSM 94,
§3.7). The successive quotients are the images `N_j.map (N_{j-1} → X/N_{j-1})`. -/
inductive IsStdFiltered : LieSubmodule K 𝔤 X → Multiset (Dual K H) → Prop
  | bot : IsStdFiltered ⊥ 0
  | step {N N' : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)} {μ : Dual K H} :
      IsStdFiltered N s → N ≤ N' →
      Nonempty (VermaModule P μ ≃ₗ⁅K,𝔤⁆ N'.map (LieSubmodule.Quotient.mk' N)) →
      IsStdFiltered N' (μ ::ₘ s)

/-- `𝔫₋ N = Σᵢ fᵢ N` for a subspace `N`. -/
def negSpan (N : Submodule K X) : Submodule K X :=
  ⨆ i, N.map (toEnd K 𝔤 X (f P i))

/-- The dimension of the weight-`ν` space of the `𝔫₋`-coinvariants `N / 𝔫₋N` of a Lie submodule
`N`. -/
def coinvDim (N : LieSubmodule K 𝔤 X) (ν : Dual K H) : ℕ :=
  finrank K ↥(N.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) -
    finrank K ↥(negSpan P N.toSubmodule ⊓ weightSpaceOfMap X (h P) ν)

omit [CharZero K] in
lemma negSpan_le (N : LieSubmodule K 𝔤 X) : negSpan P N.toSubmodule ≤ N.toSubmodule :=
  iSup_le fun i ↦ by
    rintro _ ⟨n, hn, rfl⟩
    exact N.lie_mem hn

omit [CharZero K] in
lemma negSpan_mono {N N' : Submodule K X} (h : N ≤ N') : negSpan P N ≤ negSpan P N' :=
  iSup_mono fun _ ↦ Submodule.map_mono h

omit [CharZero K] in
lemma toEnd_f_mem_negSpan {N : Submodule K X} (i : ι) {n : X} (hn : n ∈ N) :
    ⁅f P i, n⁆ ∈ negSpan P N :=
  Submodule.mem_iSup_of_mem i ⟨n, hn, rfl⟩

omit [CharZero K] in
/-- Induction principle for `𝔫₋ N`. -/
lemma negSpan_induction {N : Submodule K X} {p : X → Prop} (mem : ∀ i, ∀ n ∈ N, p ⁅f P i, n⁆)
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) {x : X} (hx : x ∈ negSpan P N) : p x := by
  induction hx using Submodule.iSup_induction' with
  | mem i x hx =>
    obtain ⟨n, hn, rfl⟩ := hx
    exact mem i n hn
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy

omit [CharZero K] in
/-- Rank–nullity for the restriction of a linear map to a subspace. -/
lemma finrank_map_add_finrank_inf_ker {Z : Type*} [AddCommGroup Z] [Module K Z]
    (g : X →ₗ[K] Z) (S : Submodule K X) [FiniteDimensional K S] :
    finrank K (S.map g) + finrank K ↥(S ⊓ LinearMap.ker g) = finrank K S := by
  have := LinearMap.finrank_range_add_finrank_ker (g.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at this
  rw [← this, ← Submodule.finrank_map_subtype_eq S ((LinearMap.ker g).comap S.subtype),
    Submodule.map_comap_subtype]

omit [CharZero K] in
/-- An injective morphism reflects weight vectors. -/
lemma mem_weightSpaceOfMap_of_injective (g : X →ₗ⁅K,𝔤⁆ Y) (hg : Function.Injective g) {ν : Dual K H}
    {x : X} (hx : g x ∈ weightSpaceOfMap Y (h P) ν) : x ∈ weightSpaceOfMap X (h P) ν := by
  intro a
  apply hg
  rw [LieModuleHom.map_lie, map_smul]
  exact hx a

omit [CharZero K] in
/-- `U(𝔤)` preserves Lie submodules. -/
lemma rep_mem (N : LieSubmodule K 𝔤 X) (u : 𝓤) {x : X} (hx : x ∈ N) : rep P X u x ∈ N := by
  induction u using UniversalEnvelopingAlgebra.induction generalizing x with
  | algebraMap r => rw [AlgHom.commutes, Module.algebraMap_end_apply]; exact N.smul_mem r hx
  | ι y => rw [rep_ι]; exact N.lie_mem hx
  | mul a b ha hb => rw [map_mul, Module.End.mul_apply]; exact ha (hb hx)
  | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact N.add_mem (ha hx) (hb hx)

omit [CharZero K] in
/-- `f_{j₁} ⋯ f_{jₖ} x` has weight `μ - (α_{j₁} + ⋯ + α_{jₖ})` for `x` of weight `μ`. -/
lemma rep_fWord_mem_weightSpace_wordWt {μ : Dual K H} {x : X} (hx : x ∈ weightSpaceOfMap X (h P) μ)
    (w : List ι) : rep P X (fWord P w) x ∈ weightSpaceOfMap X (h P) (μ - wt w) := by
  induction w with
  | nil => simpa using hx
  | cons j w ih =>
    rw [fWord_cons, map_mul, Module.End.mul_apply, rep_ι, AuxLieAlgebra.wordWt_cons,
      show μ - (P.root j + wt w) = μ - wt w - P.root j by abel]
    exact toEnd_f_mem_weightSpace j ih

end Generic

section Step

variable {N N' : LieSubmodule K P.KacMoodyAlgebra X} {μ : Dual K H}

/-- **A `U(𝔫₋)`-linear section of a Verma step.** If `N ⊆ N'` and `N'/N ≅ M(μ)`, there is a
linear map `σ : M(μ) → N'` lifting the isomorphism, commuting with the `fᵢ` and preserving
weights: `σ(u v_μ) = u x` for a lift `x` of weight `μ` of the generator. -/
theorem exists_section (hX : ⨆ ν, weightSpaceOfMap X (h P) ν = ⊤) (hNN' : N ≤ N')
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N'.map (LieSubmodule.Quotient.mk' N)) :
    ∃ σ : VermaModule P μ →ₗ[K] X,
      (∀ m, LieSubmodule.Quotient.mk' N (σ m) = (e m : X ⧸ N)) ∧ (∀ m, σ m ∈ N') ∧
      (∀ i m, σ ⁅f P i, m⁆ = ⁅f P i, σ m⁆) ∧
      (∀ ν m, m ∈ weightSpaceOfMap (VermaModule P μ) (h P) ν →
        σ m ∈ weightSpaceOfMap X (h P) ν) := by
  set ι' : VermaModule P μ →ₗ⁅K,𝔤⁆ X ⧸ N := (N'.map (LieSubmodule.Quotient.mk' N)).incl.comp
    e.toLieModuleHom
  set y : X ⧸ N := ι' (hwv P μ)
  have hyw : y ∈ weightSpaceOfMap (X ⧸ N) (h P) μ :=
    map_mem_weightSpaceOfMap P ι' (hwv_mem_weightSpace P μ)
  obtain ⟨x, hxw, hxy⟩ := (map_weightSpaceOfMap_quotient P N hX μ).ge hyw
  change LieSubmodule.Quotient.mk' N x = y at hxy
  have hxN' : x ∈ N' := by
    obtain ⟨x', hx', hx'y⟩ := (LieSubmodule.mem_map _).mp (e (hwv P μ)).2
    have : x - x' ∈ N := by
      rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub]
      change LieSubmodule.Quotient.mk' N x - LieSubmodule.Quotient.mk' N x' = 0
      rw [hxy, hx'y]
      exact sub_eq_zero.mpr rfl
    simpa using N'.add_mem (hNN' this) hx'
  set E := equivEnvNNeg P μ
  set σ : VermaModule P μ →ₗ[K] X :=
    (LinearMap.applyₗ x ∘ₗ (rep P X).toLinearMap ∘ₗ (mapN).toLinearMap) ∘ₗ E.symm.toLinearMap
  have hσ (m : VermaModule P μ) : σ m = rep P X (mapN (E.symm m)) x := rfl
  have hE (u : UniversalEnvelopingAlgebra K (nNeg P)) : E u = mapN u • hwv P μ :=
    equivEnvNNeg_apply P μ u
  refine ⟨σ, fun m ↦ ?_, fun m ↦ ?_, fun i m ↦ ?_, fun ν m hm ↦ ?_⟩
  · obtain ⟨u, rfl⟩ := E.surjective m
    rw [hσ, LinearEquiv.symm_apply_apply, map_rep, hxy, hE]
    change _ = ι' (mapN u • hwv P μ)
    rw [map_smul_eq_rep]
  · exact rep_mem P N' _ hxN'
  · obtain ⟨u, rfl⟩ := E.surjective m
    have h1 : ⁅f P i, E u⁆ = E (fWordNeg P [i] * u) := by
      rw [equivEnvNNeg_mul, map_fWordNeg, hE, fWord_cons, fWord_nil, mul_one,
        VermaModule.lie_eq_smul P μ]
    rw [h1, hσ, hσ, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, map_mul,
      map_mul, Module.End.mul_apply, map_fWordNeg, fWord_cons, fWord_nil, mul_one, rep_ι]
  · have hm' := weightSpace_le_wordSpan P μ ν hm
    rw [wordSpan] at hm'
    refine Submodule.span_induction (p := fun m _ ↦ σ m ∈ weightSpaceOfMap X (h P) ν) ?_
      (by simp) (fun _ _ _ _ h1 h2 ↦ by rw [map_add]; exact add_mem h1 h2)
      (fun c _ _ h1 ↦ by rw [map_smul]; exact Submodule.smul_mem _ c h1) hm'
    rintro _ ⟨w, hw, rfl⟩
    rw [hσ]
    dsimp only
    rw [← equivEnvNNeg_fWordNeg, LinearEquiv.symm_apply_apply, map_fWordNeg, ← hw]
    exact rep_fWord_mem_weightSpace_wordWt P hxw w

/-- **`N ∩ 𝔫₋N' = 𝔫₋N`** for a Verma step `N'/N ≅ M(μ)`: the key point is the `U(𝔫₋)`-linear
section of `exists_section`. -/
theorem negSpan_inf_le (hX : ⨆ ν, weightSpaceOfMap X (h P) ν = ⊤) (hNN' : N ≤ N')
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N'.map (LieSubmodule.Quotient.mk' N)) :
    negSpan P N'.toSubmodule ⊓ N.toSubmodule ≤ negSpan P N.toSubmodule := by
  obtain ⟨σ, hσmk, -, hσf, -⟩ := exists_section P hX hNN' e
  have key : ∀ y ∈ negSpan P N'.toSubmodule, ∃ m, y - σ m ∈ negSpan P N.toSubmodule ∧
      LieSubmodule.Quotient.mk' N y = (e m : X ⧸ N) := by
    intro y hy
    refine negSpan_induction P (p := fun y ↦ ∃ m, y - σ m ∈ negSpan P N.toSubmodule ∧
      LieSubmodule.Quotient.mk' N y = (e m : X ⧸ N)) (fun i n hn ↦ ?_) ⟨0, by simp, by simp⟩
      (fun y z ⟨m, hm, hmy⟩ ⟨m', hm', hmz⟩ ↦ ⟨m + m', ?_, ?_⟩) hy
    · have hmem : LieSubmodule.Quotient.mk' N n ∈ N'.map (LieSubmodule.Quotient.mk' N) :=
        LieSubmodule.mem_map_of_mem hn
      set m₀ := e.symm ⟨_, hmem⟩
      have hm₀ : (e m₀ : X ⧸ N) = LieSubmodule.Quotient.mk' N n := by simp [m₀]
      refine ⟨⁅f P i, m₀⁆, ?_, ?_⟩
      · rw [hσf, ← lie_sub]
        refine toEnd_f_mem_negSpan P i ?_
        rw [LieSubmodule.mem_toSubmodule, ← LieSubmodule.Quotient.mk_eq_zero']
        change LieSubmodule.Quotient.mk' N (n - σ m₀) = 0
        rw [map_sub, hσmk, hm₀, sub_self]
      · have := e.toLieModuleHom.map_lie (f P i) m₀
        simp only [LieModuleEquiv.coe_toLieModuleHom] at this
        rw [LieModuleHom.map_lie, ← hm₀, this, LieSubmodule.coe_bracket]
    · rw [map_add, add_sub_add_comm]; exact add_mem hm hm'
    · rw [map_add, map_add, hmy, hmz, LieSubmodule.coe_add]
  rintro y ⟨hy, hyN⟩
  obtain ⟨m, hm, hmy⟩ := key y hy
  have hem : e m = 0 := Subtype.ext (by
    rw [← hmy, LieSubmodule.coe_zero, LieSubmodule.Quotient.mk_eq_zero]; exact hyN)
  have hm0 : m = 0 := (e.toLinearEquiv.map_eq_zero_iff).mp hem
  simpa [hm0] using hm

/-- **Coinvariants along a Verma step.** If `N ⊆ N'` and `N'/N ≅ M(μ)`, then
`dim (N'/𝔫₋N')_ν = dim (N/𝔫₋N)_ν + dim (M(μ)/𝔫₋M(μ))_ν`. -/
theorem coinvDim_step (hX : IsCategoryO P X) (hNN' : N ≤ N')
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N'.map (LieSubmodule.Quotient.mk' N)) (ν : Dual K H) :
    coinvDim P N' ν = coinvDim P N ν + coinvDim P (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)) ν := by
  have hXd := hX.iSup_weightSpaceOfMap_eq_top
  obtain ⟨σ, hσmk, hσN', hσf, hσw⟩ := exists_section P hXd hNN' e
  set ι' : VermaModule P μ →ₗ⁅K,𝔤⁆ X ⧸ N := (N'.map (LieSubmodule.Quotient.mk' N)).incl.comp
    e.toLieModuleHom
  have hι' : Function.Injective ι' := fun a b hab ↦ e.injective (Subtype.ext hab)
  have hι'σ (m : VermaModule P μ) : LieSubmodule.Quotient.mk' N (σ m) = ι' m := hσmk m
  set q : X →ₗ[K] X ⧸ N := (LieSubmodule.Quotient.mk' N).toLinearMap
  have hker : LinearMap.ker q = N.toSubmodule := by
    ext x
    simp [q]
  have hrange (y : X ⧸ N) (hy : y ∈ N'.map (LieSubmodule.Quotient.mk' N)) :
      ∃ m, ι' m = y := ⟨e.symm ⟨y, hy⟩, by simp [ι']⟩
  have := hX.finiteDimensional_weightSpaceOfMap ν
  have hfin (S : Submodule K X) : FiniteDimensional K ↥(S ⊓ weightSpaceOfMap X (h P) ν) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have := VermaModule.finiteDimensional_weightSpace P μ ν
  have hfinM (S : Submodule K (VermaModule P μ)) :
      FiniteDimensional K ↥(S ⊓ weightSpaceOfMap (VermaModule P μ) (h P) ν) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hmapfin (T : Submodule K (VermaModule P μ)) :
      finrank K (T.map (ι' : VermaModule P μ →ₗ[K] X ⧸ N)) = finrank K T :=
    (Submodule.equivMapOfInjective _ hι' T).finrank_eq.symm
  -- the step for `N'` itself
  have h1 : finrank K ↥(N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) =
      finrank K ↥(N.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) +
        finrank K ↥((⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
          weightSpaceOfMap (VermaModule P μ) (h P) ν) := by
    have hrn := finrank_map_add_finrank_inf_ker q (N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν)
    have hmap : (N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν).map q =
        ((⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
          weightSpaceOfMap (VermaModule P μ) (h P) ν).map (ι' : VermaModule P μ →ₗ[K] X ⧸ N) := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxN', hxw⟩, rfl⟩
        obtain ⟨m, hm⟩ := hrange (q x) (LieSubmodule.mem_map_of_mem hxN')
        refine ⟨m, ⟨trivial, mem_weightSpaceOfMap_of_injective P ι' hι' ?_⟩, hm⟩
        rw [hm]; exact map_mem_weightSpaceOfMap P (LieSubmodule.Quotient.mk' N) hxw
      · rintro ⟨m, ⟨-, hmw⟩, rfl⟩
        exact ⟨σ m, ⟨hσN' m, hσw ν m hmw⟩, hι'σ m⟩
    have hinf : (N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) ⊓ LinearMap.ker q =
        N.toSubmodule ⊓ weightSpaceOfMap X (h P) ν := by
      rw [hker, inf_right_comm, inf_eq_right.mpr (show N.toSubmodule ≤ N'.toSubmodule from hNN')]
    rw [hmap, hmapfin, hinf] at hrn
    omega
  -- the step for `𝔫₋N'`
  have h2 : finrank K ↥(negSpan P N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) =
      finrank K ↥(negSpan P N.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) +
        finrank K ↥(negSpan P (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
          weightSpaceOfMap (VermaModule P μ) (h P) ν) := by
    have hrn := finrank_map_add_finrank_inf_ker q
      (negSpan P N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν)
    have hneg : ∀ x ∈ negSpan P N'.toSubmodule, ∃ m ∈ negSpan P
        (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule, ι' m = q x := by
      intro x hx
      refine negSpan_induction P (p := fun x ↦ ∃ m ∈ negSpan P
        (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule, ι' m = q x)
        (fun i n hn ↦ ?_) ⟨0, zero_mem _, by simp⟩
        (fun x y ⟨m, hm, hmx⟩ ⟨m', hm', hmy⟩ ↦ ⟨m + m', add_mem hm hm', by
          rw [map_add, map_add, hmx, hmy]⟩) hx
      obtain ⟨m, hm⟩ := hrange (q n) (LieSubmodule.mem_map_of_mem hn)
      refine ⟨⁅f P i, m⁆, toEnd_f_mem_negSpan P i trivial, ?_⟩
      rw [LieModuleHom.map_lie, hm]
      exact (LieModuleHom.map_lie (LieSubmodule.Quotient.mk' N) (f P i) n).symm
    have hσneg : ∀ m ∈ negSpan P (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule,
        σ m ∈ negSpan P N'.toSubmodule := by
      intro m hm
      refine negSpan_induction P (p := fun m ↦ σ m ∈ negSpan P N'.toSubmodule)
        (fun i n _ ↦ ?_) (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy) hm
      rw [hσf]
      exact toEnd_f_mem_negSpan P i (hσN' n)
    have hmap : (negSpan P N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν).map q =
        (negSpan P (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
          weightSpaceOfMap (VermaModule P μ) (h P) ν).map (ι' : VermaModule P μ →ₗ[K] X ⧸ N) := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxn, hxw⟩, rfl⟩
        obtain ⟨m, hm, hmx⟩ := hneg x hxn
        refine ⟨m, ⟨hm, mem_weightSpaceOfMap_of_injective P ι' hι' ?_⟩, hmx⟩
        change ι' m ∈ _
        rw [hmx]; exact map_mem_weightSpaceOfMap P (LieSubmodule.Quotient.mk' N) hxw
      · rintro ⟨m, ⟨hmn, hmw⟩, rfl⟩
        exact ⟨σ m, ⟨hσneg m hmn, hσw ν m hmw⟩, hι'σ m⟩
    have hinf : (negSpan P N'.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) ⊓ LinearMap.ker q =
        negSpan P N.toSubmodule ⊓ weightSpaceOfMap X (h P) ν := by
      rw [hker, inf_right_comm]
      refine le_antisymm (inf_le_inf_right _ (negSpan_inf_le P hXd hNN' e)) ?_
      exact inf_le_inf_right _ (le_inf (negSpan_mono P hNN') (negSpan_le P N))
    rw [hmap, hmapfin, hinf] at hrn
    omega
  have hle (N₀ : LieSubmodule K 𝔤 X) :
      finrank K ↥(negSpan P N₀.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) ≤
        finrank K ↥(N₀.toSubmodule ⊓ weightSpaceOfMap X (h P) ν) :=
    Submodule.finrank_mono (inf_le_inf_right _ (negSpan_le P N₀))
  have hleM : finrank K ↥(negSpan P (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
        weightSpaceOfMap (VermaModule P μ) (h P) ν) ≤
      finrank K ↥((⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
        weightSpaceOfMap (VermaModule P μ) (h P) ν) :=
    Submodule.finrank_mono (inf_le_inf_right _ (negSpan_le P _))
  have := hle N
  unfold coinvDim
  omega

end Step

section Verma

variable (μ : Dual K H)

/-- `𝔫₋M(μ)` contains no vector of weight `μ`. -/
theorem VermaModule.negSpan_le_lowerPart :
    negSpan P (⊤ : Submodule K (VermaModule P μ)) ≤ lowerPart P μ := by
  intro x hx
  refine negSpan_induction P (p := fun x ↦ x ∈ lowerPart P μ) (fun i n hn0 ↦ ?_) (zero_mem _)
    (fun x y hx hy ↦ add_mem hx hy) hx
  clear hn0 hx
  have hn : n ∈ ⨆ (k : ι → ℤ) (_ : 0 ≤ k), VermaModule.weightSpace P μ (μ - P.rootOf k) := by
    rw [iSup_weightSpace_eq_top]; trivial
  induction hn using Submodule.iSup_induction' with
  | mem k n hn =>
    induction hn using Submodule.iSup_induction' with
    | mem hk n hn =>
      have hne : μ - P.rootOf k - P.root i ≠ μ := by
        intro h0
        have h1 : P.rootOf (k + Pi.single i 1) = P.rootOf 0 := by
          rw [map_add, rootOf_single, map_zero]
          rw [sub_sub, sub_eq_self] at h0
          exact h0
        have h2 := congrFun (P.rootOf_injective h1) i
        have h3 : (0 : ℤ) ≤ k i := hk i
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at h2
        omega
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne
        (toEnd_f_mem_weightSpace i hn))
    | zero => simp
    | add x y _ _ hx hy => rw [lie_add]; exact add_mem hx hy
  | zero => simp
  | add x y _ _ hx hy => rw [lie_add]; exact add_mem hx hy

/-- **The `𝔫₋`-coinvariants of `M(μ)`**: `dim (M(μ)/𝔫₋M(μ))_ν = δ_{μν}`. -/
theorem VermaModule.coinvDim_top [DecidableEq (Dual K H)] (ν : Dual K H) :
    coinvDim P (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)) ν = if ν = μ then 1 else 0 := by
  have := VermaModule.finiteDimensional_weightSpace P μ ν
  have htop : finrank K ↥((⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
      weightSpaceOfMap (VermaModule P μ) (h P) ν) =
      finrank K (weightSpaceOfMap (VermaModule P μ) (h P) ν) :=
    (LinearEquiv.ofEq _ _ (by simp)).finrank_eq
  unfold coinvDim
  rw [htop]
  split_ifs with hν
  · subst hν
    have hbot : negSpan P (⊤ : LieSubmodule K 𝔤 (VermaModule P ν)).toSubmodule ⊓
        weightSpaceOfMap (VermaModule P ν) (h P) ν = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxn, hxw⟩
      have hx : x ∈ K ∙ hwv P ν := by rw [← weightSpace_self]; exact hxw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply hwv_notMem_lowerPart P ν
        have := Submodule.smul_mem (lowerPart P ν) c⁻¹
          (negSpan_le_lowerPart P ν (by simpa using hxn))
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [(LinearEquiv.ofEq _ _ hbot).finrank_eq, finrank_bot,
      VermaModule.finrank_weightSpace_self]
  · have hle : weightSpaceOfMap (VermaModule P μ) (h P) ν ≤
        negSpan P (⊤ : Submodule K (VermaModule P μ)) := by
      intro m hm
      have hm' := weightSpace_le_wordSpan P μ ν hm
      rw [wordSpan] at hm'
      refine Submodule.span_induction
        (p := fun m _ ↦ m ∈ negSpan P (⊤ : Submodule K (VermaModule P μ))) ?_ (zero_mem _)
        (fun _ _ _ _ h1 h2 ↦ add_mem h1 h2) (fun c _ _ h1 ↦ Submodule.smul_mem _ c h1) hm'
      rintro _ ⟨w, hw, rfl⟩
      cases w with
      | nil => exact (hν (by simpa using hw.symm)).elim
      | cons j w =>
        dsimp only
        rw [fWord_smul_cons]
        exact toEnd_f_mem_negSpan P j trivial
    have heq : negSpan P (⊤ : LieSubmodule K 𝔤 (VermaModule P μ)).toSubmodule ⊓
        weightSpaceOfMap (VermaModule P μ) (h P) ν = weightSpaceOfMap (VermaModule P μ) (h P) ν :=
      inf_eq_right.mpr (by simpa using hle)
    rw [(LinearEquiv.ofEq _ _ heq).finrank_eq, Nat.sub_self]

end Verma

/-- **Multiplicities in standard filtrations** (coinvariant form of Humphreys, GSM 94,
Theorem 3.7): if `N` has a standard filtration with highest weights `s`, then the number of
factors `M(ν)` is `dim (N / 𝔫₋N)_ν`. In particular it does not depend on the filtration. -/
theorem IsStdFiltered.count_eq_coinvDim [DecidableEq (Dual K H)] (hX : IsCategoryO P X)
    {N : LieSubmodule K 𝔤 X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) (ν : Dual K H) :
    s.count ν = coinvDim P N ν := by
  induction hN with
  | bot =>
    have h0 : finrank K ↥((⊥ : LieSubmodule K 𝔤 X).toSubmodule ⊓ weightSpaceOfMap X (h P) ν) = 0 :=
      Nat.le_zero.mp ((Submodule.finrank_mono (inf_le_left.trans (by simp))).trans
        (finrank_bot K X).le)
    unfold coinvDim
    rw [h0, Nat.zero_sub, Multiset.count_zero]
  | step _ hNN' he ih =>
    obtain ⟨e⟩ := he
    rw [coinvDim_step P hX hNN' e, ← ih, VermaModule.coinvDim_top, Multiset.count_cons]

section Fin

omit [CharZero K] in
/-- A standard filtration indexed by `Fin (n + 1)` (as produced by
`exists_tensorVermaStandardFiltration`) gives `IsStdFiltered`. -/
theorem isStdFiltered_of_fin {n : ℕ} (F : Fin (n + 1) → LieSubmodule K 𝔤 X)
    (wt' : Fin n → Dual K H) (hF : Monotone F) (h0 : F 0 = ⊥)
    (hstep : ∀ j, Nonempty (VermaModule P (wt' j) ≃ₗ⁅K,𝔤⁆
      (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)))) :
    IsStdFiltered P (F (Fin.last n)) (Finset.univ.val.map wt') := by
  classical
  have key : ∀ k (hk : k ≤ n), IsStdFiltered P (F ⟨k, Nat.lt_succ_of_le hk⟩)
      ((Finset.univ.filter fun j : Fin n ↦ j.val < k).val.map wt') := by
    intro k
    induction k with
    | zero =>
      intro _
      have : (Finset.univ.filter fun j : Fin n ↦ j.val < 0) = ∅ := by
        ext j; simp
      rw [this]
      simpa [h0] using IsStdFiltered.bot (P := P) (X := X)
    | succ k ih =>
      intro hk
      set j : Fin n := ⟨k, hk⟩
      have hfilt : (Finset.univ.filter fun i : Fin n ↦ i.val < k + 1) =
          Finset.cons j (Finset.univ.filter fun i : Fin n ↦ i.val < k) (by simp [j]) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons, j]
        constructor
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (rfl | h)
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt h
      rw [hfilt, Finset.cons_val, Multiset.map_cons]
      have h1 := ih (Nat.le_of_succ_le hk)
      exact IsStdFiltered.step h1 (hF (Fin.mk_le_mk.mpr (Nat.le_succ k))) (hstep j)
  have := key n le_rfl
  have hfull : (Finset.univ.filter fun j : Fin n ↦ j.val < n) = Finset.univ := by
    ext j; simp
  rwa [hfull] at this

/-- **Standard filtration of `M(Λ) ⊗ Z`** (Humphreys, GSM 94, Theorem 3.6): for `Z`
finite-dimensional and `𝔥`-diagonalizable, `M(Λ) ⊗ Z` has a standard filtration with factors
`M(Λ + μ)`, each `μ` occurring `dim Z_μ` times. -/
theorem exists_isStdFiltered_tensorVerma {Z : Type*} [AddCommGroup Z] [Module K Z]
    [LieRingModule P.KacMoodyAlgebra Z] [LieModule K P.KacMoodyAlgebra Z] [FiniteDimensional K Z]
    [DecidableEq (Dual K H)] (hZ : IsHDiagonalizable P Z) (Λ : Dual K H) :
    ∃ s : Multiset (Dual K H),
      IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (VermaModule P Λ ⊗[K] Z)) (s.map (Λ + ·)) ∧
      ∀ μ : Dual K H, s.count μ = finrank K (weightSpaceOfMap Z (h P) μ) := by
  obtain ⟨N, wt', hmono, hN0, hNlast, hstep, hcount⟩ :=
    exists_tensorVermaStandardFiltration P hZ Λ
  refine ⟨Finset.univ.val.map wt', ?_, fun μ ↦ ?_⟩
  · have := isStdFiltered_of_fin P N (fun j ↦ Λ + wt' j) hmono.monotone hN0 hstep
    rw [hNlast] at this
    rwa [Multiset.map_map]
  · classical
    rw [← hcount μ, Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext j
    simp [eq_comm]

end Fin

end Matrix.Realization.KacMoodyAlgebra
