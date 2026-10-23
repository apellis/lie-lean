/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.RelativeDuality
import LieLean.Algebra.Lie.Homology.RelativeTensor
import LieLean.Algebra.Lie.KacMoody.DualVermaCohomology
import LieLean.Algebra.Lie.KacMoody.VermaCoordinates

/-!
# Relative cohomology with coefficients in `Hom(M(λ), M(μ)^∨)`

Let `𝔤 = 𝔤(A)` with Cartan subalgebra `𝔥`, and suppose `𝔫₋` is finite-dimensional (finite type).
We prove that every relative cocycle of positive degree in `C^•(𝔤, 𝔥; Hom_K(M(λ), M(μ)^∨))` is
the coboundary of a relative cochain, for all weights `λ`, `μ`. This is the base case of the
comparison `Extⁿ_𝒪(M, N) ≅ Hⁿ(𝔤, 𝔥; Hom_K(M, N))` of Humphreys, GSM 94, Thm. 6.15 (a), matching
`Extⁿ_𝒪(M(λ), M(μ)^∨) = 0` for `n > 0` (Humphreys Thm. 6.12).

The proof applies `LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_relExact` to the
invariant pairing of `Hom_K(M(λ), M(μ)^∨)` with `X = M(λ) ⊗ M(μ)^ω` (`M(μ)^ω` is `M(μ)` with
the action twisted by the Chevalley involution), and checks the exactness hypothesis with
`LieModule.ChevalleyEilenberg.RelativeKoszul.relExact`. The relative coordinates are the root
vectors `f_j`, `ω(f_j)` on `𝔫₋ ⊕ 𝔫₊` and the PBW coordinates of `M(λ)` and `M(μ)^ω`, in which
`f_j` acts on `M(λ)` and `ω(f_j)` acts on `M(μ)^ω` by multiplication by a variable up to lower
order terms, while the other root vectors do not raise the degree.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.exists_δ_eq_relVerma`: relative cocycles of positive
  degree with values in `Hom_K(M(λ), M(μ)^∨)` are coboundaries.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 6.15 (a), Thm. 6.12. The argument is our own.
-/

open Module LieModule LieModule.ChevalleyEilenberg MvPolynomial TensorProduct

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => P.KacMoodyAlgebra

/-! ### The complement `𝔫₋ ⊕ 𝔫₊` of `𝔥` and its root vector basis -/

/-- The complement `𝔫₋ ⊕ 𝔫₊` of `𝔥`. -/
abbrev nSum : Submodule K 𝔤 := (nNeg P).toSubmodule ⊔ (nPos P).toSubmodule

lemma isCompl_nSum_range_h : IsCompl (nSum P) (LinearMap.range (h P)) :=
  (isCompl_range_h_nNeg_sup_nPos P).symm

/-- The projection `𝔤 → 𝔫₋ ⊕ 𝔫₊` along `𝔥`. -/
def nSumProj : 𝔤 →ₗ[K] nSum P :=
  Submodule.projectionOnto _ _ (isCompl_nSum_range_h P)

lemma nSumProj_apply_coe (x : nSum P) : nSumProj P x = x :=
  Submodule.projectionOnto_apply_left _ x

lemma nSumProj_of_mem {x : 𝔤} (hx : x ∈ nSum P) : (nSumProj P x : 𝔤) = x := by
  rw [nSumProj, Submodule.projectionOnto_apply_of_mem_left _ hx]

omit [CharZero K] in
lemma lie_h_mem_nSum (a : H) {x : 𝔤} (hx : x ∈ nSum P) : ⁅h P a, x⁆ ∈ nSum P := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [lie_add]
  exact Submodule.add_mem_sup (lie_h_mem_nNeg P a hy) (lie_h_mem_nPos P a hz)

/-- The root vectors `f_j` and `ω(f_j)`. -/
def nSumVec : NegRootIndex P ⊕ NegRootIndex P → 𝔤 :=
  Sum.elim (fun i ↦ (nNegBasis P i : 𝔤)) (fun i ↦ chevalleyInvolution P (nNegBasis P i))

lemma nSumVec_inl (i : NegRootIndex P) : nSumVec P (Sum.inl i) = nNegBasis P i := rfl

lemma nSumVec_inr (i : NegRootIndex P) :
    nSumVec P (Sum.inr i) = chevalleyInvolution P (nNegBasis P i) := rfl

lemma span_nNegBasis :
    Submodule.span K (Set.range fun i ↦ (nNegBasis P i : 𝔤)) = (nNeg P).toSubmodule := by
  have h := congrArg (Submodule.map (nNeg P).toSubmodule.subtype) (nNegBasis P).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at h
  exact h

lemma linearIndependent_nSumVec : LinearIndependent K (nSumVec P) := by
  have hNeg : LinearIndependent K fun i ↦ (nNegBasis P i : 𝔤) :=
    (nNegBasis P).linearIndependent.map' (nNeg P).toSubmodule.subtype
      (Submodule.ker_subtype _)
  have hPos : LinearIndependent K fun i ↦ chevalleyInvolution P (nNegBasis P i) :=
    hNeg.map' (chevalleyInvolution P).toLinearMap (LinearMap.ker_eq_bot.mpr
      (Function.LeftInverse.injective (chevalleyInvolution_chevalleyInvolution P)))
  refine LinearIndependent.sum_type hNeg hPos ?_
  refine ((isCompl_nNeg_borel P).disjoint.mono_right fun x hx ↦ nPos_le_borel P hx).mono ?_ ?_
  · exact (span_nNegBasis P).le
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦
      chevalleyInvolution_mem_nPos P (nNegBasis P i).2)

lemma span_nSumVec : Submodule.span K (Set.range (nSumVec P)) = nSum P := by
  refine le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ ?_))
    (sup_le ?_ fun x hx ↦ ?_)
  · rcases j with i | i
    · exact Submodule.mem_sup_left (nNegBasis P i).2
    · exact Submodule.mem_sup_right (chevalleyInvolution_mem_nPos P (nNegBasis P i).2)
  · rw [← span_nNegBasis]
    exact Submodule.span_mono (Set.range_subset_iff.mpr fun i ↦ ⟨Sum.inl i, rfl⟩)
  · have hω : chevalleyInvolution P x ∈ Submodule.span K (Set.range fun i ↦ (nNegBasis P i : 𝔤)) :=
      (span_nNegBasis P).ge (chevalleyInvolution_mem_nNeg P hx)
    have hx' : x ∈ Submodule.span K
        (Set.range fun i ↦ chevalleyInvolution P (nNegBasis P i : 𝔤)) := by
      have := Submodule.mem_map_of_mem (f := (chevalleyInvolution P).toLinearMap) hω
      rw [Submodule.map_span, ← Set.range_comp] at this
      simpa [Function.comp_def, chevalleyInvolution_chevalleyInvolution] using this
    refine Submodule.span_mono ?_ hx'
    exact Set.range_subset_iff.mpr fun i ↦ ⟨Sum.inr i, rfl⟩

/-- The basis `f_j`, `ω(f_j)` of `𝔫₋ ⊕ 𝔫₊`. -/
def nSumBasis : Basis (NegRootIndex P ⊕ NegRootIndex P) K (nSum P) :=
  (Basis.span (linearIndependent_nSumVec P)).map (LinearEquiv.ofEq _ _ (span_nSumVec P))

@[simp] lemma coe_nSumBasis (j : NegRootIndex P ⊕ NegRootIndex P) :
    (nSumBasis P j : 𝔤) = nSumVec P j := by
  simp [nSumBasis, Basis.span_apply]

/-- The weights `-α_j`, `α_j` of `f_j`, `ω(f_j)`. -/
def nSumWt : NegRootIndex P ⊕ NegRootIndex P → Dual K H :=
  Sum.elim (fun i ↦ -i.root) (fun i ↦ i.root)

lemma lie_h_nSumVec (a : H) (j : NegRootIndex P ⊕ NegRootIndex P) :
    ⁅h P a, nSumVec P j⁆ = nSumWt P j a • nSumVec P j := by
  rcases j with i | i
  · simpa [nSumVec_inl, nSumWt] using nNegBasis_mem P i a
  · have h1 : ⁅h P a, (nNegBasis P i : 𝔤)⁆ = (-i.root) a • (nNegBasis P i : 𝔤) :=
      nNegBasis_mem P i a
    rw [nSumVec_inr, ← chevalleyInvolution_chevalleyInvolution P (h P a), ← LieHom.map_lie,
      chevalleyInvolution_h, neg_lie, h1, map_neg, map_smul]
    simp [nSumWt]

/-! ### Relative data -/

variable (Λ μ : Dual K H)

/-- The module `X = M(λ) ⊗ M(μ)^ω`. -/
abbrev RelX : Type _ := VermaModule P Λ ⊗[K] OmegaTwist P (VermaModule P μ)

/-- The action of `𝔥` on `M(λ) ⊗ M(μ)^ω`. -/
abbrev relAction : DerivAction K H 𝔤 (RelX P Λ μ) := DerivAction.ofMap (RelX P Λ μ) (h P)

lemma isRelData_relAction : RelativeKoszul.IsRelData (h P) (relAction P Λ μ) (nSumProj P) where
  D_eq _ := rfl
  φ_eq _ _ := rfl
  lie_eta := lie_h_h P
  map_eta a :=
    Submodule.projectionOnto_apply_right (isCompl_nSum_range_h P)
      ⟨h P a, LinearMap.mem_range_self _ a⟩
  sub_mem y := by
    have : y - (nSumProj P y : 𝔤) ∈ LinearMap.range (h P) := by
      rw [← Submodule.projectionOnto_apply_eq_zero_iff (isCompl_nSum_range_h P)]
      change nSumProj P (y - (nSumProj P y : 𝔤)) = 0
      rw [map_sub, nSumProj_apply_coe, sub_self]
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha.symm⟩
  map_ad a y := by
    obtain ⟨a', ha'⟩ : ∃ a', y - (nSumProj P y : 𝔤) = h P a' := by
      have : y - (nSumProj P y : 𝔤) ∈ LinearMap.range (h P) := by
        rw [← Submodule.projectionOnto_apply_eq_zero_iff (isCompl_nSum_range_h P)]
        change nSumProj P (y - (nSumProj P y : 𝔤)) = 0
        rw [map_sub, nSumProj_apply_coe, sub_self]
      obtain ⟨a', h'⟩ := this
      exact ⟨a', h'.symm⟩
    have hy : y = (nSumProj P y : 𝔤) + h P a' := by rw [← ha', add_sub_cancel]
    have hmem := lie_h_mem_nSum P a (nSumProj P y).2
    conv_lhs => rw [hy, lie_add, lie_h_h, add_zero]
    exact nSumProj_of_mem P hmem

/-! ### Coordinates -/

/-- The PBW coordinates of `M(μ)^ω`. -/
def omegaCoord : OmegaTwist P (VermaModule P μ) ≃ₗ[K] MvPolynomial (NegRootIndex P) K :=
  (OmegaTwist.of P _).symm ≪≫ₗ VermaModule.vermaCoord P μ

/-- The coordinates of `M(λ) ⊗ M(μ)^ω`. -/
def relCoord : RelX P Λ μ ≃ₗ[K] MvPolynomial (NegRootIndex P ⊕ NegRootIndex P) K :=
  RelativeKoszul.tensorCoord (VermaModule.vermaCoord P Λ) (omegaCoord P μ)

lemma omegaCoord_lie (x : 𝔤) (q : MvPolynomial (NegRootIndex P) K) :
    omegaCoord P μ ⁅x, (omegaCoord P μ).symm q⁆ =
      VermaModule.vermaCoord P μ ⁅chevalleyInvolution P x, (VermaModule.vermaCoord P μ).symm q⁆ :=
  rfl

lemma isLeading_relCoord : RelativeKoszul.IsLeading (relCoord P Λ μ) (nSumBasis P) := by
  refine RelativeKoszul.isLeading_tensorCoord _ _ _ (fun j n q hq ↦ ?_) (fun j n q hq ↦ ?_)
    (fun j n q hq ↦ ?_) (fun j n q hq ↦ ?_)
  · rw [coe_nSumBasis, nSumVec_inl]
    exact VermaModule.vermaCoord_lie_nNegBasis_sub_mem P Λ j n hq
  · rw [coe_nSumBasis, nSumVec_inl, omegaCoord_lie]
    exact VermaModule.vermaCoord_lie_mem_of_mem_borel P μ
      (nPos_le_borel P (chevalleyInvolution_mem_nPos P (nNegBasis P j).2)) hq
  · rw [coe_nSumBasis, nSumVec_inr]
    exact VermaModule.vermaCoord_lie_mem_of_mem_borel P Λ
      (nPos_le_borel P (chevalleyInvolution_mem_nPos P (nNegBasis P j).2)) hq
  · rw [coe_nSumBasis, nSumVec_inr, omegaCoord_lie, chevalleyInvolution_chevalleyInvolution]
    exact VermaModule.vermaCoord_lie_nNegBasis_sub_mem P μ j n hq

omit [CharZero K] in
lemma monoWt_nSumWt_inl (m : NegRootIndex P →₀ ℕ) :
    RelativeKoszul.monoWt (nSumWt P ∘ Sum.inl) m = -negRootWt P m := by
  simp [RelativeKoszul.monoWt, negRootWt, nSumWt, Finsupp.sum]

omit [CharZero K] in
lemma monoWt_nSumWt_inr (m : NegRootIndex P →₀ ℕ) :
    RelativeKoszul.monoWt (nSumWt P ∘ Sum.inr) m = negRootWt P m := rfl

lemma isWeightCoord_relCoord :
    RelativeKoszul.IsWeightCoord (nSumBasis P) (nSumWt P) (relAction P Λ μ) (relCoord P Λ μ)
      (Λ + -μ) := by
  refine RelativeKoszul.isWeightCoord_tensorCoord _ _ _ (fun a j ↦ ?_) (fun a m ↦ ?_)
    (fun a m ↦ ?_)
  · rw [coe_nSumBasis]
    exact lie_h_nSumVec P a j
  · rw [monoWt_nSumWt_inl, ← sub_eq_add_neg]
    exact VermaModule.vermaCoord_symm_monomial_mem_weightSpace P Λ m a
  · rw [monoWt_nSumWt_inr]
    change OmegaTwist.of P _ ⁅chevalleyInvolution P (h P a),
      (VermaModule.vermaCoord P μ).symm (monomial m 1)⁆ = _
    rw [chevalleyInvolution_h, neg_lie,
      VermaModule.vermaCoord_symm_monomial_mem_weightSpace P μ m a, map_neg, map_smul]
    change -(((μ - negRootWt P m) a) • _) = ((-μ + negRootWt P m) a) • _
    rw [← neg_smul]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply]
    ring

/-! ### The pairing -/

/-- The coefficient module `Hom_K(M(λ), M(μ)^∨)`. -/
abbrev RelN : Type _ := VermaModule P Λ →ₗ[K] restrictedDual P (VermaModule P μ)

/-- The invariant pairing `Hom_K(M(λ), M(μ)^∨) × (M(λ) ⊗ M(μ)^ω) → K`,
`(n, m ⊗ y) ↦ ⟨n(m), y⟩`. -/
def relPairing : RelN P Λ μ →ₗ[K] RelX P Λ μ →ₗ[K] K :=
  (TensorProduct.lift.equiv (RingHom.id K) _ _ K).toLinearMap ∘ₗ
    LinearMap.llcomp K _ _ _ (dualPairing P (VermaModule P μ))

@[simp] lemma relPairing_tmul (n : RelN P Λ μ) (m : VermaModule P Λ)
    (y : OmegaTwist P (VermaModule P μ)) :
    relPairing P Λ μ n (m ⊗ₜ y) = dualPairing P _ (n m) y := by
  simp [relPairing]

lemma relPairing_lie (x : 𝔤) (n : RelN P Λ μ) (z : RelX P Λ μ) :
    relPairing P Λ μ ⁅x, n⁆ z = -relPairing P Λ μ n ⁅x, z⁆ := by
  induction z using TensorProduct.inductionOn with
  | tmul m y =>
    rw [relPairing_tmul, LieHom.lie_apply, map_sub, LinearMap.sub_apply, dualPairing_lie,
      TensorProduct.LieModule.lie_tmul_right, map_add, relPairing_tmul, relPairing_tmul]
    ring
  | add z z' h h' => rw [map_add, h, h', lie_add, map_add, neg_add]

lemma relPairing_injective : Function.Injective (relPairing P Λ μ) := fun n n' hnn' ↦
  LinearMap.ext fun m ↦ dualPairing_injective P (LinearMap.ext fun y ↦ by
    simpa using LinearMap.congr_fun hnn' (m ⊗ₜ y))

lemma mem_range_relPairing {γ : Dual K H} {ψ : RelX P Λ μ →ₗ[K] K}
    (hψ : ∀ a z, ψ ((relAction P Λ μ).φ a z) = γ a * ψ z) :
    ψ ∈ LinearMap.range (relPairing P Λ μ) := by
  have hs : ∀ s, ∃ d, dualPairing P (VermaModule P μ) d =
      ψ ∘ₗ TensorProduct.mk K _ _ (VermaModule.pbwBasisVerma P Λ s) := fun s ↦ by
    refine mem_range_dualPairing P (γ := γ - (Λ - negRootWt P s)) fun a y ↦ ?_
    have h1 := hψ a (VermaModule.pbwBasisVerma P Λ s ⊗ₜ y)
    rw [DerivAction.ofMap_φ, TensorProduct.LieModule.lie_tmul_right,
      VermaModule.pbwBasisVerma_mem_weightSpace P Λ s a, ← TensorProduct.smul_tmul', map_add,
      map_smul, smul_eq_mul, LinearMap.sub_apply] at h1
    simp only [nPosDerivAction_φ_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
      LinearMap.sub_apply]
    linear_combination h1
  choose d hd using hs
  refine ⟨(VermaModule.pbwBasisVerma P Λ).constr K d,
    TensorProduct.ext ((VermaModule.pbwBasisVerma P Λ).ext fun s ↦ LinearMap.ext fun y ↦ ?_)⟩
  simpa [Basis.constr_basis] using LinearMap.congr_fun (hd s) y

/-! ### The vanishing theorem -/

/-- **Relative cocycles with values in `Hom_K(M(λ), M(μ)^∨)` are coboundaries**: for `𝔫₋`
finite-dimensional, every relative cocycle of degree `k + 1` in
`C^•(𝔤, 𝔥; Hom_K(M(λ), M(μ)^∨))` is the coboundary of a relative cochain. This is the base
case of Humphreys GSM 94, Thm. 6.15 (a), matching `Extⁿ_𝒪(M(λ), M(μ)^∨) = 0` for `n > 0`
(Thm. 6.12). -/
theorem exists_δ_eq_relVerma [Finite (NegRootIndex P)] {k : ℕ}
    {f : Cochains K 𝔤 (RelN P Λ μ) (k + 1)}
    (hf : f ∈ relCochains K 𝔤 (RelN P Λ μ) (Set.range (h P)) (k + 1))
    (hδ : δ K 𝔤 (RelN P Λ μ) (k + 1) f = 0) :
    ∃ g ∈ relCochains K 𝔤 (RelN P Λ μ) (Set.range (h P)) k, δ K 𝔤 (RelN P Λ μ) k g = f := by
  have hr := isRelData_relAction P Λ μ
  have hw := isWeightCoord_relCoord P Λ μ
  have hL := RelativeKoszul.iSup_weightSpaceOf_D hr hw
  have hX := RelativeKoszul.iSup_weightSpaceOf_φ hw
  have hT := (relAction P Λ μ).iSup_chainWeightSpace hL hX
  exact DerivAction.exists_δ_eq_of_relExact (ρ := relAction P Λ μ)
    (ρN := DerivAction.ofMap (RelN P Λ μ) (h P)) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (lie_h_h P) (relPairing_lie P Λ μ) (fun a n z ↦ relPairing_lie P Λ μ (h P a) n z)
    (relPairing_injective P Λ μ) (fun _ _ hψ ↦ mem_range_relPairing P Λ μ hψ) hL hX
    (fun t ht hdt ↦ RelativeKoszul.relExact (hp := nSumProj_apply_coe P) (hT := hT)
      (isLeading_relCoord P Λ μ) hr hw t ht hdt) hf hδ

end Matrix.Realization.KacMoodyAlgebra
