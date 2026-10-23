/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorWeylInduction
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorComposition
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralWall

/-!
# Shifting the block of a projective functor

Lemmas for Bernstein–Gelfand's reduction of Theorem 3.4 (iv) to the case §3.9 (d): a projective
functor on the block of a dominant `λ` is composed with a translation `pr_{χ_λ}(− ⊗ L(nρ)^*)`
from the block of `φ = λ + nρ`, for `n` large.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsInBlock.sub_mem_rootLattice`: the weights of a module in
  the block of `λ` lie in `λ + Q`.
* `Matrix.Realization.KacMoodyAlgebra.isInBlock_of_centralBlock_eq_top`: a finitely generated
  module in `𝒪` with central character `χ_λ` and weights in `λ + Q` lies in the block of `λ`.
* `BlockProjectiveFunctor.mapsTo_tensorBlock`: `pr_{χ_λ}(− ⊗ V)` maps the block of `φ` to the
  block of `λ` if the weights of `V` lie in `λ - φ + Q`.
* `Matrix.Realization.KacMoodyAlgebra.finrank_weightSpace_sub_weylDot`: for `λ` dominant and the
  lowest weight `-δ` of `V` of multiplicity one, the only factor of `M(w·(λ + δ)) ⊗ V` with
  central character `χ_λ` is `M(w·λ)`, once.
* `Matrix.Realization.KacMoodyAlgebra.IsDominant.add_nsmul_rho`,
  `integralWeylGroup_add_nsmul_rho`, `exists_isDominantIntegral_add_nsmul_rho_sub`: the shift
  `λ ↦ λ + nρ` keeps `λ` dominant and `W_[λ]` fixed, and makes finitely many `λ + nρ - ξ`
  dominant integral.
* `BlockProjectiveFunctor.nonempty_idem_range_equiv`: `F(M) ≅ F(N)` for `M ≅ N` in the block.
* `BlockProjectiveFunctor.nonempty_tensorBlock_verma_equiv`:
  `pr_{χ_λ}(M(w·(λ + δ)) ⊗ V) ≅ M(w·λ)`.
* `BlockProjectiveFunctor.vermaMult_verma_le`, `finite_setOf_vermaMult_ne_zero`: `M(ν)` occurs in
  `F(M(Λ))` at most `dim V_{ν - Λ}` times, so only finitely many `M(ν)` occur.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285, §3.9 (e).
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 3.6, §10.8.
-/

noncomputable section

open Module LieModule UniversalEnvelopingAlgebra TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Weights

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

/-- A weight `ξ` of `V ⊗ W` is `a + b` for weights `a` of `V` and `b` of `W`. -/
theorem exists_weightSpace_ne_bot_of_tensorProduct (hV : IsHDiagonalizable P V)
    (hW : IsHDiagonalizable P W) {ξ : Dual K H} (h : weightSpace P (V ⊗[K] W) ξ ≠ ⊥) :
    ∃ a, weightSpace P V a ≠ ⊥ ∧ weightSpace P W (ξ - a) ≠ ⊥ := by
  by_contra hne
  push Not at hne
  refine h ?_
  rw [weightSpace_tensorProduct hV hW ξ]
  refine iSup_eq_bot.mpr fun a ↦ LinearMap.range_eq_bot.mpr ?_
  by_cases ha : weightSpace P V a = ⊥
  · have : (weightSpace P V a).subtype = 0 := by
      ext x
      have hx : (x : V) ∈ (⊥ : Submodule K V) := ha ▸ x.property
      exact (Submodule.mem_bot K).mp hx
    rw [this, TensorProduct.map_zero_left]
  · have hb := hne a ha
    have : (weightSpace P W (ξ - a)).subtype = 0 := by
      ext x
      have hx : (x : W) ∈ (⊥ : Submodule K W) := hb ▸ x.property
      exact (Submodule.mem_bot K).mp hx
    rw [this, TensorProduct.map_zero_right]

end Weights

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H] [IsAlgClosed K] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- The weights of a module in the block of `λ` lie in `λ + Q`. -/
theorem IsInBlock.sub_mem_rootLattice {lam : Dual K H} {M : Type (max u₁ u₂)} [AddCommGroup M]
    [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsInBlock P hA lam M)
    {a : Dual K H} (ha : weightSpace P M a ≠ ⊥) : a - lam ∈ P.rootLattice := by
  have : FiniteDimensional K (weightSpace P M a) :=
    hM.isCategoryO.finiteDimensional_weightSpaceOfMap a
  have hfr : finrank K (weightSpace P M a) ≠ 0 := fun h0 ↦ ha (Submodule.finrank_eq_zero.mp h0)
  rw [hM.isCategoryO.finrank_weightSpace_eq_finsum a] at hfr
  obtain ⟨μ, hμ⟩ : ∃ μ, hM.isCategoryO.multiplicity μ *
      finrank K (weightSpace P (IrreducibleModule P μ) a) ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hfr (finsum_eq_zero_of_forall_eq_zero h0)
  obtain ⟨w, hw, rfl⟩ := hM.multiplicity_ne_zero μ (left_ne_zero_of_mul hμ)
  obtain ⟨k, -, hk⟩ := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero
    (right_ne_zero_of_mul hμ)
  rw [mem_integralWeylGroup_iff_dot] at hw
  have e : a - lam = (P.weylDot hA.isGeneralizedCartan w lam - lam) - P.rootOf k := by
    rw [hk]
    abel
  rw [e]
  exact sub_mem hw (P.rootOf_mem_rootLattice k)

omit [IsAlgClosed K] in
/-- A finitely generated module in `𝒪` with central character `χ_λ` and weights in `λ + Q`
lies in the block of `λ`. -/
theorem isInBlock_of_centralBlock_eq_top {lam : Dual K H} {X : Type (max u₁ u₂)}
    [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X] (hX : IsCategoryO P X)
    (hfg : ∃ s : Finset X, LieSubmodule.lieSpan K 𝔤 (s : Set X) = ⊤)
    (hχ : centralBlock P X (centralCharacter P lam) = ⊤)
    (hwt : ∀ a, weightSpace P X a ≠ ⊥ → a - lam ∈ P.rootLattice) : IsInBlock P hA lam X where
  isCategoryO := hX
  exists_finset := hfg
  multiplicity_ne_zero μ hμ := by
    have hc := hX.centralCharacter_eq_of_multiplicity_ne_zero P hχ hμ
    obtain ⟨w, hw, hwμ⟩ := (VermaModule.centralCharacter_eq_iff P hA lam μ).mp hc.symm
    refine ⟨⟨w, hw⟩, ?_, ?_⟩
    · rw [mem_integralWeylGroup_iff_dot]
      change w (lam + P.rho) - P.rho - lam ∈ P.rootLattice
      rw [hwμ, add_sub_cancel_right]
      exact hwt μ (hX.weightSpace_ne_bot_of_multiplicity_ne_zero hμ)
    · change μ = w (lam + P.rho) - P.rho
      rw [hwμ, add_sub_cancel_right]

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
/-- A Verma flag with a single factor `M(μ)` is a copy of `M(μ)`. -/
theorem IsStdFiltered.nonempty_equiv_of_singleton {X : Type*} [AddCommGroup X] [Module K X]
    [LieRingModule 𝔤 X] [LieModule K 𝔤 X] {N : LieSubmodule K 𝔤 X} {μ : Dual K H}
    (h : IsStdFiltered P N {μ}) : Nonempty (VermaModule P μ ≃ₗ⁅K,𝔤⁆ N) := by
  generalize hs : ({μ} : Multiset (Dual K H)) = s at h
  cases h with
  | bot => exact absurd hs (Multiset.singleton_ne_zero μ)
  | step h₀ hle e =>
    obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff _).mp hs
    have hb := IsStdFiltered.eq_bot_of_zero P h₀
    subst hb
    have hinj : Function.Injective (LieSubmodule.Quotient.mk' (⊥ : LieSubmodule K 𝔤 X)) :=
      (LieModuleHom.ker_eq_bot _).mp (LieSubmodule.Quotient.mk'_ker ⊥)
    exact ⟨e.some.trans (LieSubmodule.equivMapOfInjective _ hinj).symm⟩

omit [IsAlgClosed K] in
open Classical in
/-- **Linked weights of a shifted tensor product** (Bernstein–Gelfand, §3.9 (e)): let `λ` be
dominant and `V` finite-dimensional with weights `b` satisfying `-b ≤ δ`, and with
`dim V_{-δ} = 1`. Then for every `w ∈ W`, the only weight `ξ` with `χ_ξ = χ_λ` and
`V_{ξ - w·(λ + δ)} ≠ 0` is `ξ = w·λ`, with multiplicity one. -/
theorem finrank_weightSpace_sub_weylDot {V : Type*} [AddCommGroup V] [Module K V]
    [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [FiniteDimensional K V] {lam δ : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    (hVc : ∀ b, weightSpace P V b ≠ ⊥ → -b ∈ cone P δ)
    (hδ : finrank K (weightSpace P V (-δ)) = 1) (w : P.weylGroup hA.isGeneralizedCartan)
    (ξ : Dual K H) :
    (if centralCharacter P ξ = centralCharacter P lam then
        finrank K (weightSpace P V (ξ - P.weylDot hA.isGeneralizedCartan w (lam + δ)))
      else 0) = if ξ = P.weylDot hA.isGeneralizedCartan w lam then 1 else 0 := by
  have hVI := isIntegrable_of_finiteDimensional (P := P) (V := V) hA
  have hinv : ∀ (u : P.weylGroup hA.isGeneralizedCartan) μ,
      finrank K (weightSpace P V ((u : Dual K H ≃ₗ[K] Dual K H) μ)) =
        finrank K (weightSpace P V μ) := fun u μ ↦
    congrArg Cardinal.toNat (rank_weightSpace_weylGroup hA.isGeneralizedCartan hVI u.property μ)
  by_cases hξ : ξ = P.weylDot hA.isGeneralizedCartan w lam
  · subst hξ
    have h1 : centralCharacter P (P.weylDot hA.isGeneralizedCartan w lam) =
        centralCharacter P lam := centralCharacter_weyl P hA.isGeneralizedCartan w.property lam
    simp only [h1, ↓reduceIte]
    have e : P.weylDot hA.isGeneralizedCartan w lam -
        P.weylDot hA.isGeneralizedCartan w (lam + δ) = (w : Dual K H ≃ₗ[K] Dual K H) (-δ) := by
      simp only [weylDot, map_add, map_neg]
      abel
    rw [e, hinv, hδ]
  simp only [hξ, ↓reduceIte]
  rw [ite_eq_right_iff]
  intro hc
  by_contra h0
  obtain ⟨u, hu, huξ⟩ := (VermaModule.centralCharacter_eq_iff P hA lam ξ).mp hc.symm
  set c := ((w⁻¹ : P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H)
    (ξ - P.weylDot hA.isGeneralizedCartan w (lam + δ)) with hcdef
  have hb : weightSpace P V c ≠ ⊥ := fun hbot ↦ h0 (by rw [← hinv w⁻¹, ← hcdef, hbot,
    finrank_bot])
  obtain ⟨k, hk0, hk⟩ := hVc c hb
  set v : P.weylGroup hA.isGeneralizedCartan := w⁻¹ * ⟨u, hu⟩
  have e1 : ξ - P.weylDot hA.isGeneralizedCartan w (lam + δ) =
      u (lam + P.rho) - (w : Dual K H ≃ₗ[K] Dual K H) (lam + δ + P.rho) := by
    rw [huξ, weylDot, add_right_comm]
    abel
  have hc' : c = (v : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - (lam + δ + P.rho) := by
    rw [hcdef, e1, map_sub, inv_apply_apply]
    rfl
  rw [hc'] at hk
  have hv : (v : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) = lam + P.rho + P.rootOf k := by
    calc (v : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho)
        = -(-((v : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - (lam + δ + P.rho))) +
          (lam + δ + P.rho) := by abel
      _ = -(δ - P.rootOf k) + (lam + δ + P.rho) := by rw [hk]
      _ = lam + P.rho + P.rootOf k := by abel
  have hvmem : v ∈ P.integralWeylGroup hA.isGeneralizedCartan lam := by
    rw [mem_integralWeylGroup_iff_dot, hv,
      show lam + P.rho + P.rootOf k - P.rho - lam = P.rootOf k by abel]
    exact P.rootOf_mem_rootLattice k
  obtain ⟨k', hk'0, hk'⟩ := IsDominant.exists_sub_weylDot_eq_rootOf P hA hlam hvmem
  have hvd : P.weylDot hA.isGeneralizedCartan v lam = lam + P.rootOf k := by
    rw [weylDot, hv]
    abel
  have heq : P.weylDot hA.isGeneralizedCartan v lam = lam :=
    eq_of_mem_cone_of_mem_cone ⟨k', hk'0, by rw [← hk']; abel⟩
      ⟨k, hk0, by rw [hvd]; abel⟩
  have hvl : (v : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) = lam + P.rho := by
    rw [← weylDot_add_rho, heq]
  apply hξ
  rw [weylDot, ← hvl]
  change ξ = (w : Dual K H ≃ₗ[K] Dual K H)
    (((w⁻¹ : P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) (u (lam + P.rho))) -
      P.rho
  rw [apply_inv_apply, huξ, add_sub_cancel_right]

omit [IsAlgClosed K] in
/-- Dominance is preserved by adding multiples of `ρ`. -/
theorem IsDominant.add_nsmul_rho {lam : Dual K H} (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    (n : ℕ) : P.IsDominant hA.isGeneralizedCartan (lam + (n : K) • P.rho) := by
  intro v i hv m hm
  obtain ⟨r, hr⟩ := exists_int_corootPairing_of_forall_int (hA := hA.isGeneralizedCartan)
    (c := P.rho) (fun t ↦ ⟨1, by rw [rho_coroot, Int.cast_one]⟩) v i
  have hr1 := one_le_of_corootPairing_rho_eq hA hv hr
  have hsplit : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i =
      ((m - n * r : ℤ) : K) := by
    rw [add_right_comm, corootPairing_add, corootPairing_smul, hr] at hm
    push_cast
    rw [← hm]
    ring
  have h0 := hlam v i hv _ hsplit
  have hnr : (0 : ℤ) ≤ n * r := mul_nonneg (Nat.cast_nonneg n) (by omega)
  omega

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
/-- `W_[λ + nρ] = W_[λ]`. -/
theorem integralWeylGroup_add_nsmul_rho (lam : Dual K H) (n : ℕ) :
    P.integralWeylGroup hA.isGeneralizedCartan (lam + (n : K) • P.rho) =
      P.integralWeylGroup hA.isGeneralizedCartan lam :=
  P.integralWeylGroup_eq_of_integral hA.isGeneralizedCartan fun j ↦
    ⟨n, by simp [rho_coroot]⟩

omit [DecidableEq ι] [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
/-- For finitely many `ξ` with `λ - ξ` integral, `λ + nρ - ξ` is dominant integral for every
large `n`. -/
theorem exists_isDominantIntegral_add_nsmul_rho_sub (lam : Dual K H) (T : Finset (Dual K H))
    (hT : ∀ ξ ∈ T, ∀ i, ∃ z : ℤ, (lam - ξ) (P.coroot i) = z) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ξ ∈ T, P.IsDominantIntegral (lam + (n : K) • P.rho - ξ) := by
  choose! z hz using hT
  refine ⟨T.sup fun ξ ↦ ∑ i, (z ξ i).natAbs, fun n hn ξ hξ i ↦ ⟨(z ξ i + n).toNat, ?_⟩⟩
  have hle : (z ξ i).natAbs ≤ n :=
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun ξ ↦ ∑ i, (z ξ i).natAbs) hξ)).trans hn
  have hpos : 0 ≤ z ξ i + n := by omega
  have e : (lam + (n : K) • P.rho - ξ) (P.coroot i) = (lam - ξ) (P.coroot i) + n := by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, rho_coroot,
      smul_eq_mul, mul_one]
    ring
  rw [e, hz ξ hξ i]
  have : ((z ξ i + n).toNat : K) = ((z ξ i + n : ℤ) : K) := by
    exact_mod_cast congrArg (Int.cast (R := K)) (Int.toNat_of_nonneg hpos)
  rw [this]
  push_cast
  ring

namespace BlockProjectiveFunctor

local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- **`pr_{χ_λ}(− ⊗ V)` maps the block of `φ` to the block of `λ`** if every weight `b` of `V`
has `φ + b - λ ∈ Q`. -/
theorem mapsTo_tensorBlock {φ lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V]
    [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [FiniteDimensional K V]
    (hV : ∀ b, weightSpace P V b ≠ ⊥ → φ + b - lam ∈ P.rootLattice) :
    (tensorBlock P hA φ V (centralCharacter P lam)).MapsTo lam := by
  intro M _ _ _ _ hM
  have hVO := isCategoryO_of_finiteDimensional (P := P) (hA := hA) V
  have hMV := hM.isCategoryO.tensorProduct hVO
  refine isInBlock_of_centralBlock_eq_top (hMV.lieSubmodule _) ?_ ?_ ?_
  · obtain ⟨s, hs⟩ := hM.exists_finset
    obtain ⟨T, hT⟩ := exists_finset_lieSpan_tensor_eq_top (W := V) hs
    classical
    refine ⟨T.image (rangeRetr ((tensorBlock P hA φ V (centralCharacter P lam)).idem M)), ?_⟩
    rw [Finset.coe_image]
    exact lieSpan_image_eq_top_of_surjective _
      (surjective_rangeRetr ((tensorBlock P hA φ V (centralCharacter P lam)).idem_mul_idem hM)) hT
  · rw [eq_top_iff]
    rintro v -
    have hv : (v : M ⊗[K] V) ∈ centralBlock P (M ⊗[K] V) (centralCharacter P lam) := by
      rw [← range_tensorBlock_idem _ hM.isCategoryO]
      exact v.property
    exact mem_centralBlock_of_injective P (LieSubmodule.incl _) Subtype.val_injective _ hv
  · intro a ha
    have ha' : weightSpace P (M ⊗[K] V) a ≠ ⊥ := fun h ↦ ha (weightSpace_lieSubmodule_eq_bot _ h)
    obtain ⟨c, hc, hb⟩ := exists_weightSpace_ne_bot_of_tensorProduct
      hM.isCategoryO.iSup_weightSpaceOfMap_eq_top hVO.iSup_weightSpaceOfMap_eq_top ha'
    have := add_mem (hM.sub_mem_rootLattice hc) (hV _ hb)
    convert this using 1
    abel

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- **Projective functors respect isomorphisms**: `F(M) ≅ F(N)` for `M ≅ N` in the block. -/
theorem nonempty_idem_range_equiv {M N : Type (max u₁ u₂)} [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N]
    [LieModule K 𝔤 N] (hM : IsInBlock P hA lam M) (hN : IsInBlock P hA lam N)
    (e : M ≃ₗ⁅K,𝔤⁆ N) : Nonempty ((F.idem M).range ≃ₗ⁅K,𝔤⁆ (F.idem N).range) := by
  set E := LieModuleEquiv.tensorCongr e (LieModuleEquiv.refl (M := V))
  have hE : ∀ x, E x = (e.toLieModuleHom : M →ₗ[K] N).rTensor V x := fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul m v =>
      rw [LieModuleEquiv.tensorCongr_tmul, LinearMap.rTensor_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hc : ∀ x, E (F.idem M x) = F.idem N (E x) := fun x ↦ by
    rw [hE, hE, F.naturality hM hN]
  have hmap : (F.idem M).range.map E.toLieModuleHom = (F.idem N).range := by
    ext y
    simp only [LieSubmodule.mem_map, LieModuleHom.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨E x, (hc x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨F.idem M (E.symm x), ⟨_, rfl⟩, ?_⟩
      change E (F.idem M (E.symm x)) = _
      rw [hc, E.apply_symm_apply]
  rw [← hmap]
  exact ⟨LieSubmodule.equivMapOfInjective _ E.injective⟩

/-- **Shifted Verma images** (Bernstein–Gelfand, §3.9 (e)): under the hypotheses of
`finrank_weightSpace_sub_weylDot`, `pr_{χ_λ}(M(w·(λ + δ)) ⊗ V) ≅ M(w·λ)` for every `w ∈ W`. -/
theorem nonempty_tensorBlock_verma_equiv [FiniteDimensional K V] {μ₀ δ : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    (hVc : ∀ b, weightSpace P V b ≠ ⊥ → -b ∈ cone P δ)
    (hδ : finrank K (weightSpace P V (-δ)) = 1) (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) ≃ₗ⁅K,𝔤⁆
      ((tensorBlock P hA μ₀ V (centralCharacter P lam)).idem
        (VermaModule P (P.weylDot hA.isGeneralizedCartan w (lam + δ)))).range) := by
  classical
  obtain ⟨s, hs, hcount⟩ := exists_isStdFiltered_tensorBlock_verma (P := P) (hA := hA)
    (lam := μ₀) (V := V) (centralCharacter P lam) (P.weylDot hA.isGeneralizedCartan w (lam + δ))
  have hs1 : s = {P.weylDot hA.isGeneralizedCartan w lam} := by
    ext ξ
    rw [hcount ξ, Multiset.count_singleton]
    convert finrank_weightSpace_sub_weylDot (hA := hA) hlam hVc hδ w ξ
  subst hs1
  exact hs.nonempty_equiv_of_singleton

omit [IsAlgClosed K] in
/-- **Bound on Verma multiplicities**: the multiplicity of `M(ν)` in `F(M(Λ))` is at most
`dim V_{ν - Λ}`, the multiplicity of `M(ν)` in `M(Λ) ⊗ V` (Humphreys, GSM 94, Thm. 3.6). -/
theorem vermaMult_verma_le [FiniteDimensional K V] {Λ : Dual K H}
    (hΛ : IsInBlock P hA lam (VermaModule P Λ)) (ν : Dual K H) :
    F.vermaMult (VermaModule P Λ) ν ≤ finrank K (weightSpace P V (ν - Λ)) := by
  classical
  obtain ⟨s, hs, hcount⟩ := exists_isStdFiltered_tensorVerma P
    (isHDiagonalizable_of_finiteDimensional (P := P) (V := V) hA) Λ
  have hY : IsCategoryO P (VermaModule P Λ ⊗[K] V) :=
    (VermaModule.isCategoryO P Λ).tensorProduct (isCategoryO_of_finiteDimensional (P := P)
      (hA := hA) V)
  have h := finrank_hom_range_eq_add P hY hs (e := LieModuleHom.id)
    (e₁ := F.idem (VermaModule P Λ)) (by ext; rfl) (F.idem_mul_idem hΛ)
    (by ext; rfl) (by ext; rfl) ν
  have hcnt := hs.count_eq_finrank_hom hY ν
  have hmap := Multiset.count_map_eq_count' (Λ + ·) s (add_right_injective Λ) (ν - Λ)
  simp only [add_sub_cancel] at hmap
  rw [hmap, hcount] at hcnt
  have hE : (LieModuleHom.id : VermaModule P Λ ⊗[K] V →ₗ⁅K,𝔤⁆ _).range ≃ₗ⁅K,𝔤⁆
      VermaModule P Λ ⊗[K] V :=
    LieModuleEquiv.ofBijective (LieSubmodule.incl _)
      ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, y, rfl⟩, rfl⟩⟩
  rw [finrank_hom_congr_left P hE] at h
  have hle : F.vermaMult (VermaModule P Λ) ν ≤
      finrank K (VermaModule P Λ ⊗[K] V →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) := by
    rw [h]
    exact Nat.le_add_right _ _
  exact hle.trans_eq hcnt.symm

omit [IsAlgClosed K] in
/-- Only finitely many Verma modules occur in `F(M(Λ))`. -/
theorem finite_setOf_vermaMult_ne_zero [FiniteDimensional K V] {Λ : Dual K H}
    (hΛ : IsInBlock P hA lam (VermaModule P Λ)) :
    {ν | F.vermaMult (VermaModule P Λ) ν ≠ 0}.Finite := by
  classical
  have hind := iSupIndep_weightSpaceOfMap (M := V) (h P)
  have := hind.fintypeNeBotOfFiniteDimensional
  have hfin : {μ | weightSpace P V μ ≠ ⊥}.Finite :=
    Set.finite_coe_iff.mp (inferInstance : Finite {μ // weightSpaceOfMap V (h P) μ ≠ ⊥})
  refine (hfin.image (Λ + ·)).subset fun ν hν ↦ ⟨ν - Λ, ?_, add_sub_cancel Λ ν⟩
  intro h0
  have := F.vermaMult_verma_le hΛ ν
  rw [h0, finrank_bot] at this
  exact hν (Nat.le_zero.mp this)

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
