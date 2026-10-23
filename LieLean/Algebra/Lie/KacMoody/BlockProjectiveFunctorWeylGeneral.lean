/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorShift

/-!
# Projective functors commute with the Weyl group

Bernstein–Gelfand's Theorem 3.4 (iv) on the block of a dominant weight `λ`, for every projective
functor `F = e(− ⊗ V)`: the multiplicity of `M(w·ν)` in `F(M(w·λ))` equals the multiplicity of
`M(ν)` in `F(M(λ))` for `w ∈ W_[λ]`. The case of an indecomposable functor whose linkage class is
dominated by `λ` is `commutesWithWeyl_of_equiv_projectiveCover` (§3.9 (d)); the general case
(§3.9 (e)) composes `F` with the translation `G = pr_{χ_λ}(− ⊗ L(nρ)^*)` from the block of
`φ = λ + nρ`, `n` large. Then `GF` lies on the block of `φ`, `(GF)(M(w·φ)) ≅ F(M(w·λ))`, and
`φ` dominates the linkage classes of all summands of `GF`.

## Main results

* `BlockProjectiveFunctor.commutesWithWeyl`: **Bernstein–Gelfand, Thm. 3.4 (iv)** on the block of
  a dominant `λ`, assuming Kostant's multiplicity formula for `(U(𝔤) / Ann M(μ))^{ad}` for
  dominant `μ`.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285,
  Thm. 3.4 (iv), §3.9 (e).
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8.
-/

noncomputable section

open Module LieModule UniversalEnvelopingAlgebra TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H] [IsAlgClosed K] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

namespace BlockProjectiveFunctor

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

/-- **Projective functors commute with the Weyl group** (Bernstein–Gelfand, Thm. 3.4 (iv),
§3.9 (e)): let `λ` be dominant and `F` a projective functor on the block of `λ`. Assume
Kostant's multiplicity formula for `(U(𝔤) / I_μ)^{ad}`, `I_μ` the annihilator of `M(μ)`, for
every dominant `μ`. Then the multiplicity of `M(w·ν)` in `F(M(w·λ))` is the multiplicity of
`M(ν)` in `F(M(λ))`, for every `w ∈ W_[λ]` and every `ν`. -/
theorem commutesWithWeyl [FiniteDimensional K V] (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    (hK : ∀ μ, P.IsDominant hA.isGeneralizedCartan μ → KostantMultiplicity P
      (AdQuotient K 𝔤 (TwoSidedIdeal.ker (actionHom (R := K) (L := 𝔤) (VermaModule P μ))))) :
    F.CommutesWithWeyl := by
  classical
  have hF₀ := isInBlock_verma P hA lam
  -- The weights `ψ` with `M(ψ)` in `F(M(λ))`, and their linkage classes.
  set S := {ν | F.vermaMult (VermaModule P lam) ν ≠ 0} with hS_def
  have hS : S.Finite := F.finite_setOf_vermaMult_ne_zero hF₀
  have hSint : ∀ ψ ∈ S, ∀ i, ∃ z : ℤ, (ψ - lam) (P.coroot i) = z := fun ψ hψ i ↦ by
    refine exists_int_of_weightSpace_ne_bot hA.isGeneralizedCartan
      (isIntegrable_of_finiteDimensional (P := P) (V := V) hA) (fun h0 ↦ hψ ?_) i
    have := F.vermaMult_verma_le hF₀ ψ
    rw [h0, finrank_bot] at this
    exact Nat.le_zero.mp this
  set T := {ξ | ∃ ψ ∈ S, centralCharacter P ξ = centralCharacter P ψ ∧
    ξ - ψ ∈ P.rootLattice} with hT_def
  have hT : T.Finite := by
    have := P.finite_weylGroup hA
    refine (hS.biUnion fun ψ _ ↦ Set.finite_range fun w : P.weylGroup hA.isGeneralizedCartan ↦
      P.weylDot hA.isGeneralizedCartan w ψ).subset fun ξ hξT ↦ ?_
    obtain ⟨ψ, hψ, hξ, -⟩ := hξT
    obtain ⟨w, hw, hwξ⟩ := (VermaModule.centralCharacter_eq_iff P hA ψ ξ).mp hξ.symm
    refine Set.mem_biUnion hψ ⟨⟨w, hw⟩, ?_⟩
    change w (ψ + P.rho) - P.rho = ξ
    rw [hwξ, add_sub_cancel_right]
  have hTint : ∀ ξ ∈ hT.toFinset, ∀ i, ∃ z : ℤ, (lam - ξ) (P.coroot i) = z := by
    intro ξ hξ i
    obtain ⟨ψ, hψ, -, hξψ⟩ := hT.mem_toFinset.mp hξ
    obtain ⟨a, ha⟩ := hSint ψ hψ i
    obtain ⟨b, hb⟩ := P.exists_int_of_mem_rootLattice hξψ i
    refine ⟨-a - b, ?_⟩
    have e : lam - ξ = -(ψ - lam) - (ξ - ψ) := by abel
    rw [e, LinearMap.sub_apply, LinearMap.neg_apply, ha, hb]
    push_cast
    ring
  obtain ⟨N, hN⟩ := exists_isDominantIntegral_add_nsmul_rho_sub lam hT.toFinset hTint
  -- The translation `G = pr_{χ_λ}(− ⊗ L(Nρ)^*)` from the block of `φ = λ + Nρ`.
  set φ := lam + (N : K) • P.rho with hφ_def
  have hφ : P.IsDominant hA.isGeneralizedCartan φ := IsDominant.add_nsmul_rho (hA := hA) hlam N
  have hWφ : P.integralWeylGroup hA.isGeneralizedCartan φ =
      P.integralWeylGroup hA.isGeneralizedCartan lam :=
    integralWeylGroup_add_nsmul_rho (hA := hA) lam N
  have := IrreducibleModule.finiteDimensional (P := P) hA (isDominantIntegral_nsmul_rho P N)
  have hLO := isCategoryO_of_finiteDimensional (P := P) (hA := hA)
    (IrreducibleModule P ((N : K) • P.rho))
  -- Fix the instances on `L(Nρ)^*` once, so that they are found inside nested tensor products.
  let D := Module.Dual K (IrreducibleModule P ((N : K) • P.rho))
  let _ : AddCommGroup D := inferInstance
  let _ : Module K D := inferInstance
  let _ : LieRingModule 𝔤 D := inferInstance
  let _ : LieModule K 𝔤 D := inferInstance
  have hLO' := isCategoryO_of_finiteDimensional (P := P) (hA := hA) D
  have hVc : ∀ b, weightSpace P D b ≠ ⊥ → -b ∈ cone P ((N : K) • P.rho) := by
    intro b hb
    refine IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero ?_
    rw [weightSpace, ← finrank_weightSpaceOfMap_dual P hLO.1 hLO'.1]
    exact fun h0 ↦ hb (Submodule.finrank_eq_zero.mp h0)
  have hδ : finrank K (weightSpace P D (-((N : K) • P.rho))) = 1 := by
    rw [weightSpace, finrank_weightSpaceOfMap_dual P hLO.1 hLO'.1, neg_neg]
    exact IrreducibleModule.finrank_weightSpace_self P _
  set G := tensorBlock P hA φ D (centralCharacter P lam)
  have hG : G.MapsTo lam := mapsTo_tensorBlock fun b hb ↦ by
    obtain ⟨k, -, hk⟩ := hVc b hb
    have e : φ + b - lam = P.rootOf k := by
      rw [hφ_def, show b = -(-b) by abel, hk]
      abel
    rw [e]
    exact P.rootOf_mem_rootLattice k
  set Hf := G.comp F hG
  -- `(GF)(M(w·φ)) ≅ F(M(w·λ))`.
  have hkey : ∀ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam, ∀ ν,
      Hf.vermaMult (VermaModule P (P.weylDot hA.isGeneralizedCartan w φ)) ν =
        F.vermaMult (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)) ν := by
    intro w hw ν
    have hw' : w ∈ P.integralWeylGroup hA.isGeneralizedCartan φ := hWφ ▸ hw
    have hMφ := isInBlock_verma_weylDot (hA := hA) (lam := φ) hw'
    obtain ⟨e₁⟩ := G.nonempty_comp_equiv F hG _ hMφ
    obtain ⟨e₂⟩ := nonempty_tensorBlock_verma_equiv (μ₀ := φ) hlam hVc hδ w
    obtain ⟨e₃⟩ := F.nonempty_idem_range_equiv (hG _ hMφ)
      (isInBlock_verma_weylDot (hA := hA) hw) e₂.symm
    exact finrank_hom_congr_left P (e₁.trans e₃)
  -- Decompose `GF` on the block of `φ`; each summand commutes with `W_[φ]`.
  set I := TwoSidedIdeal.ker (actionHom (R := K) (L := 𝔤) (VermaModule P φ))
  have hM₀ : IsKilledBy I (VermaModule P φ) := fun a ha ↦ (TwoSidedIdeal.mem_ker _).mp ha
  have hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P φ) a = 0 → a ∈ I :=
    fun a ha ↦ (TwoSidedIdeal.mem_ker _).mpr ha
  obtain ⟨l, hl, hp, hsum⟩ := Hf.exists_decomposition hφ hM₀ hI
  have hone : ∀ ν, Hf.vermaMult (VermaModule P φ) ν = F.vermaMult (VermaModule P lam) ν :=
    fun ν ↦ by
      have h := hkey 1 (one_mem _) ν
      rwa [weylDot_one, weylDot_one] at h
  have hcomm : ∀ G' ∈ l, G'.CommutesWithWeyl := by
    intro G' hG'
    obtain ⟨ψ, ⟨E⟩⟩ :=
      G'.exists_nonempty_equiv_projectiveCover hφ hM₀ hI (hK φ hφ) (hl G' hG').1
    refine G'.commutesWithWeyl_of_equiv_projectiveCover hφ hM₀ hI (hK φ hφ)
      (fun ξ hξ hξ' ↦ ?_) E
    have h1 : G'.vermaMult (VermaModule P φ) ψ = 1 := by
      rw [G'.vermaMult_verma_eq_multiplicity E ψ, VermaModule.multiplicity_self]
    have h2 : 1 ≤ Hf.vermaMult (VermaModule P φ) ψ := by
      rw [Hf.vermaMult_eq_sum l hp hsum (isInBlock_verma P hA φ) ψ, ← h1]
      exact List.le_sum_of_mem (List.mem_map_of_mem hG')
    have hψ : ψ ∈ S := by
      change F.vermaMult _ ψ ≠ 0
      rw [← hone]
      omega
    exact hN N le_rfl ξ (hT.mem_toFinset.mpr ⟨ψ, hψ, hξ, hξ'⟩)
  -- Hence `F` commutes with `W_[λ] = W_[φ]`.
  intro w hw ν
  have hw' : w ∈ P.integralWeylGroup hA.isGeneralizedCartan φ := hWφ ▸ hw
  rw [← hkey w hw, ← hone, Hf.vermaMult_eq_sum l hp hsum (isInBlock_verma_weylDot (hA := hA) hw'),
    Hf.vermaMult_eq_sum l hp hsum (isInBlock_verma P hA φ)]
  exact congrArg List.sum (List.map_congr_left fun G' hG' ↦ hcomm G' hG' w hw' ν)

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
