/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorExact

/-!
# Adjoint projective functors and Verma multiplicities

Let `F = e(− ⊗ V)` be a projective functor on the block of `λ` and `G = e'(− ⊗ W)` one on the
block of `μ` that maps the block of `μ` to the block of `λ`, and suppose `G` is right adjoint to
`F` on these blocks: `Hom(F(M), N) ≅ Hom(M, G(N))` for `M` in the block of `λ` and `N` in the
block of `μ`. Then the matrices of Verma multiplicities of `F` and `G` are transposes of each
other (Bernstein–Gelfand, Thm. 3.4 (iii)):

`(F(M(χ)) : M(ν)) = (G(M(ν)) : M(χ))` for `χ = w·λ`, `ν = w'·μ`, `w ∈ W_[λ]`, `w' ∈ W_[μ]`.

The proof is the standard one. For `ψ` in the block of `λ`, BGG reciprocity, exactness of `F`
along a standard filtration of `P(ψ)` and adjunction give
`[G(M(ν)) : L(ψ)] = dim Hom(P(ψ), G(M(ν))) = dim Hom(F(P(ψ)), M(ν)) = (F(P(ψ)) : M(ν))
  = Σ_χ [M(χ) : L(ψ)] (F(M(χ)) : M(ν))`,
and both sides vanish for `ψ` outside the block. Since `G(M(ν))` has a standard filtration,
`[G(M(ν)) : L(ψ)] = Σ_χ (G(M(ν)) : M(χ)) [M(χ) : L(ψ)]`, and unitriangularity of the matrix
`[M(χ) : L(ψ)]` identifies the two families of coefficients.

## Main results

* `IsFGProjectiveO.finrank_hom_restrictedDual`: `dim Hom(Q, Y^∨) = dim Hom(Q, Y)` for a finitely
  generated projective `Q` in `𝒪`.
* `eq_of_forall_sum_multiplicity_eq`: a multiset of weights `s` is determined by the sums
  `Σ_{Λ ∈ s} [M(Λ) : L(κ)]`.
* `blockWeights`, `finite_blockWeights`: the weights `w·λ`, `w ∈ W_[λ]`, of the block of `λ`.
* `isInBlock_projectiveCover`: `P(ψ)` lies in the block of `λ` for `ψ` in it.
* `BlockProjectiveFunctor.vermaMult_projectiveCover`: `(F(P(ψ)) : M(ν))` is the sum of the
  `(F(M(Λ)) : M(ν))` over a standard filtration of `P(ψ)`.
* `BlockProjectiveFunctor.vermaMult_eq_vermaMult_of_adjoint`: Bernstein–Gelfand, Thm. 3.4 (iii).

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285, §1.12,
  Thm. 3.4 (iii).
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  §10.8.
-/

noncomputable section

open Module LieModule TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule WeightOrd

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H] [IsAlgClosed K] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Generic facts -/

include hA in
/-- For a finitely generated projective `Q` and `Y` in `𝒪`, `dim Hom(Q, Y^∨) = dim Hom(Q, Y)`:
both are `Σ [Y : L(Λ)]` over the indecomposable summands `P(Λ)` of `Q`. -/
theorem IsFGProjectiveO.finrank_hom_restrictedDual {Q : Type (max u₁ u₂)} [AddCommGroup Q]
    [Module K Q] [LieRingModule P.KacMoodyAlgebra Q] [LieModule K P.KacMoodyAlgebra Q]
    (hQ : IsFGProjectiveO P Q) {Y : Type (max u₁ u₂)} [AddCommGroup Y] [Module K Y]
    [LieRingModule P.KacMoodyAlgebra Y] [LieModule K P.KacMoodyAlgebra Y]
    (hY : IsCategoryO P Y) :
    finrank K (Q →ₗ⁅K,𝔤⁆ restrictedDual P Y) = finrank K (Q →ₗ⁅K,𝔤⁆ Y) := by
  obtain ⟨f, hf⟩ := hQ.isCategoryO.exists_strictMono_lieSubmodule P hA hQ.fg.choose_spec
  suffices key : ∀ n : ℕ, ∀ (Q : Type (max u₁ u₂)) [AddCommGroup Q] [Module K Q]
      [LieRingModule P.KacMoodyAlgebra Q] [LieModule K P.KacMoodyAlgebra Q],
      IsFGProjectiveO P Q → ∀ f : LieSubmodule K 𝔤 Q → ℕ, StrictMono f → f ⊤ < n →
      finrank K (Q →ₗ⁅K,𝔤⁆ restrictedDual P Y) = finrank K (Q →ₗ⁅K,𝔤⁆ Y) from
    key _ Q hQ f hf (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
  intro Q _ _ _ _ hQ f hf hn
  by_cases hQt : Nontrivial Q
  · obtain ⟨Λ, φ, hφ⟩ := hQ.isCategoryO.exists_surjective_irreducibleModule P hA
      hQ.fg.choose_spec
    obtain ⟨s, r, hrs⟩ := hQ.exists_retract hA φ hφ
    have hlt : f ((⊤ : LieSubmodule K 𝔤 r.ker).map r.ker.incl) < n := by
      rw [LieSubmodule.map_incl_top]
      have := hf (lt_top_iff_ne_top.mpr (IsFGProjectiveO.ker_ne_top hA hrs))
      omega
    have h1 := hQ.finrank_hom_eq_add hA hrs (isCategoryO_restrictedDual hY)
    have h2 := hQ.finrank_hom_eq_add hA hrs hY
    have h3 := ProjectiveCover.finrank_hom_eq_multiplicity (P := P) (hA := hA) (Λ := Λ)
      (isCategoryO_restrictedDual hY)
    have h4 := ProjectiveCover.finrank_hom_eq_multiplicity (P := P) (hA := hA) (Λ := Λ) hY
    have h5 := multiplicity_restrictedDual hY Λ
    have h6 := ih r.ker (hQ.ker hrs) _ (r.ker.strictMono_map_incl hf) hlt
    omega
  · rw [not_nontrivial_iff_subsingleton] at hQt
    have hzero {Z : Type (max u₁ u₂)} [AddCommGroup Z] [Module K Z]
        [LieRingModule P.KacMoodyAlgebra Z] [LieModule K P.KacMoodyAlgebra Z] :
        finrank K (Q →ₗ⁅K,𝔤⁆ Z) = 0 := by
      have : Subsingleton (Q →ₗ⁅K,𝔤⁆ Z) :=
        ⟨fun a b ↦ LieModuleHom.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      exact Module.finrank_zero_of_subsingleton
    rw [hzero, hzero]

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- **Unitriangularity of `[M(Λ) : L(κ)]`**: a multiset of weights `s` is determined by the
sums `Σ_{Λ ∈ s} [M(Λ) : L(κ)]`, `κ ∈ 𝔥^*`. -/
theorem eq_of_forall_sum_multiplicity_eq {s s' : Multiset (Dual K H)}
    (h : ∀ κ, (s.map fun Λ ↦ (VermaModule.isCategoryO P Λ).multiplicity κ).sum =
      (s'.map fun Λ ↦ (VermaModule.isCategoryO P Λ).multiplicity κ).sum) : s = s' :=
  Multiset.eq_of_forall_sum_map_eq (o := fun μ ↦ OrderDual.toDual (toWeightOrd P μ))
    (fun _ _ hab ↦ (toWeightOrd P).injective (OrderDual.toDual.injective hab))
    (w := fun Λ κ ↦ (VermaModule.isCategoryO P Λ).multiplicity κ)
    (fun Λ ↦ VermaModule.multiplicity_self Λ)
    (fun _ _ hne ↦ OrderDual.toDual_le_toDual.mpr
      ((toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
        (VermaModule.mem_cone_of_multiplicity_ne_zero hne))) s s' h

/-- `⊤ ≅ X`. -/
private def topEquiv (X : Type*) [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X]
    [LieModule K 𝔤 X] : (⊤ : LieSubmodule K 𝔤 X) ≃ₗ⁅K,𝔤⁆ X :=
  LieModuleEquiv.ofBijective (⊤ : LieSubmodule K 𝔤 X).incl
    ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, trivial⟩, rfl⟩⟩

/-! ### Weights of a block -/

/-- The weights `w·λ`, `w ∈ W_[λ]`, of the block of `λ`. -/
def blockWeights (lam : Dual K H) : Set (Dual K H) :=
  {χ | ∃ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
    χ = P.weylDot hA.isGeneralizedCartan w lam}

omit [IsAlgClosed K] [FiniteDimensional K H] in
theorem finite_blockWeights (lam : Dual K H) : (blockWeights P hA lam).Finite := by
  have := P.finite_weylGroup hA
  exact (Set.finite_range fun w ↦ P.weylDot hA.isGeneralizedCartan w lam).subset
    fun _ ⟨w, _, hχ⟩ ↦ ⟨w, hχ.symm⟩

variable {P hA}

/-- `M(Λ)` lies in the block of `λ` for `Λ` a weight of the block. -/
theorem isInBlock_verma_of_mem {lam Λ : Dual K H} (hΛ : Λ ∈ blockWeights P hA lam) :
    IsInBlock P hA lam (VermaModule P Λ) := by
  obtain ⟨w, hw, rfl⟩ := hΛ
  exact BlockProjectiveFunctor.isInBlock_verma_weylDot hw

/-- The composition factors `L(χ)` of `M(Λ)`, `Λ` in the block of `λ`, are in the block. -/
theorem mem_blockWeights_of_multiplicity_ne_zero {lam Λ χ : Dual K H}
    (hΛ : Λ ∈ blockWeights P hA lam) (h : (VermaModule.isCategoryO P Λ).multiplicity χ ≠ 0) :
    χ ∈ blockWeights P hA lam :=
  (isInBlock_verma_of_mem hΛ).multiplicity_ne_zero χ h

/-- If `L(ψ)`, `ψ` in the block of `λ`, is a composition factor of `M(Λ)`, then `Λ` is in the
block of `λ`. -/
theorem mem_blockWeights_of_multiplicity_ne_zero' {lam Λ ψ : Dual K H}
    (hψ : ψ ∈ blockWeights P hA lam) (h : (VermaModule.isCategoryO P Λ).multiplicity ψ ≠ 0) :
    Λ ∈ blockWeights P hA lam := by
  obtain ⟨w, hw, rfl⟩ := hψ
  obtain ⟨x, hx, hxΛ⟩ := (isInBlock_verma P hA Λ).multiplicity_ne_zero _ h
  refine ⟨x⁻¹ * w, ?_, ?_⟩
  · rw [mem_integralWeylGroup_iff_dot] at hw hx ⊢
    change P.weylDot hA.isGeneralizedCartan w lam - lam ∈ P.rootLattice at hw
    change P.weylDot hA.isGeneralizedCartan x Λ - Λ ∈ P.rootLattice at hx
    change P.weylDot hA.isGeneralizedCartan (x⁻¹ * w) lam - lam ∈ P.rootLattice
    have h1 : P.weylDot hA.isGeneralizedCartan (x⁻¹ * w) lam = Λ := by
      rw [weylDot_mul, hxΛ, ← weylDot_mul, inv_mul_cancel, weylDot_one]
    have h2 : Λ - lam = -(P.weylDot hA.isGeneralizedCartan x Λ - Λ) +
        (P.weylDot hA.isGeneralizedCartan w lam - lam) := by
      rw [← hxΛ]
      abel
    rw [h1, h2]
    exact add_mem (neg_mem hx) hw
  · rw [weylDot_mul, hxΛ, ← weylDot_mul, inv_mul_cancel, weylDot_one]

/-- `P(ψ)` lies in the block of `λ` for `ψ` a weight of the block. -/
theorem isInBlock_projectiveCover {lam ψ : Dual K H} (hψ : ψ ∈ blockWeights P hA lam) :
    IsInBlock P hA lam (ProjectiveCover P hA ψ) where
  isCategoryO := ProjectiveCover.isCategoryO P hA ψ
  exists_finset := (ProjectiveCover.isFGProjectiveO P hA ψ).fg
  multiplicity_ne_zero κ hκ := by
    classical
    obtain ⟨t, ht, -, -⟩ := ProjectiveCover.exists_isStdFiltered P ψ hA
    have hX := ProjectiveCover.isCategoryO P hA ψ
    have hsum := IsStdFiltered.multiplicity_eq_sum hX ht κ
    have htop := IsCategoryO.multiplicity_congr (hX.lieSubmodule ⊤) hX (topEquiv P _) κ
    obtain ⟨Λ, hΛt, hΛ⟩ : ∃ Λ ∈ t, (VermaModule.isCategoryO P Λ).multiplicity κ ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      refine hκ ?_
      change hX.multiplicity κ = 0
      rw [← htop, hsum]
      exact Multiset.sum_eq_zero fun x hx ↦ by
        obtain ⟨Λ, hΛ, rfl⟩ := Multiset.mem_map.mp hx
        exact hcon Λ hΛ
    have hΛψ : (VermaModule.isCategoryO P Λ).multiplicity ψ ≠ 0 := by
      rw [← ProjectiveCover.count_eq_multiplicity P ψ hA ht Λ]
      exact Multiset.count_ne_zero.mpr hΛt
    exact mem_blockWeights_of_multiplicity_ne_zero
      (mem_blockWeights_of_multiplicity_ne_zero' hψ hΛψ) hΛ

/-! ### Projective functors on projective covers -/

namespace BlockProjectiveFunctor

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] [FiniteDimensional K V]
  (F : BlockProjectiveFunctor P hA lam V)

omit [IsAlgClosed K] in
/-- `F(M(Λ))` has a standard filtration. -/
theorem exists_isStdFiltered_verma {Λ : Dual K H} (hΛ : IsInBlock P hA lam (VermaModule P Λ)) :
    ∃ s, IsStdFiltered P (F.idem (VermaModule P Λ)).range s := by
  classical
  obtain ⟨s, hs, -⟩ := exists_isStdFiltered_tensorVerma P
    (isHDiagonalizable_of_finiteDimensional (V := V) hA) Λ
  have hY := (VermaModule.isCategoryO P Λ).tensorProduct
    (isCategoryO_of_finiteDimensional (P := P) (hA := hA) V)
  exact exists_isStdFiltered_range P _ hY _ rfl hs _ (F.idem_mul_idem hΛ)

omit [IsAlgClosed K] in
/-- `F(Q)` is finitely generated projective in `𝒪` for `Q` finitely generated projective in the
block. -/
theorem isFGProjectiveO_range {Q : Type (max u₁ u₂)} [AddCommGroup Q] [Module K Q]
    [LieRingModule 𝔤 Q] [LieModule K 𝔤 Q] (hQb : IsInBlock P hA lam Q)
    (hQ : IsFGProjectiveO P Q) : IsFGProjectiveO P (F.idem Q).range := by
  have he : (F.idem Q).comp (F.idem Q) = F.idem Q := F.idem_mul_idem hQb
  refine ⟨?_, F.isCategoryO_range hQ.isCategoryO, ?_⟩
  · exact (hQ.isProjectiveO.tensorProduct P
      (isCategoryO_of_finiteDimensional (P := P) (hA := hA) (Module.Dual K V))).of_retract
      (F.idem Q).range.incl (rangeRetr _) (rangeRetr_comp_incl he)
  · obtain ⟨T, hT⟩ := exists_finset_lieSpan_tensor_eq_top (W := V) hQ.fg.choose_spec
    classical
    refine ⟨T.image (rangeRetr (F.idem Q)), ?_⟩
    rw [Finset.coe_image]
    exact lieSpan_image_eq_top_of_surjective _ (surjective_rangeRetr he) hT

/-- **Verma multiplicities of `F(P(ψ))`**: if `P(ψ)` has a standard filtration with factors
`M(Λ)`, `Λ ∈ t`, all in the block, then `(F(P(ψ)) : M(ν)) = Σ_{Λ ∈ t} (F(M(Λ)) : M(ν))`. -/
theorem vermaMult_projectiveCover {ψ : Dual K H}
    (hψ : IsInBlock P hA lam (ProjectiveCover P hA ψ)) {t : Multiset (Dual K H)}
    (ht : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (ProjectiveCover P hA ψ)) t)
    (htb : ∀ Λ ∈ t, IsInBlock P hA lam (VermaModule P Λ)) (ν : Dual K H) :
    F.vermaMult (ProjectiveCover P hA ψ) ν =
      (t.map fun Λ ↦ F.vermaMult (VermaModule P Λ) ν).sum := by
  classical
  have hQ := ProjectiveCover.isFGProjectiveO P hA ψ
  have hFQ := F.isFGProjectiveO_range hψ hQ
  obtain ⟨u, hu⟩ := hFQ.isProjectiveO.exists_isStdFiltered P hA hFQ.isCategoryO
    hFQ.fg.choose_spec
  let sF : Dual K H → Multiset (Dual K H) := fun Λ ↦
    if h : ∃ s, IsStdFiltered P (F.idem (VermaModule P Λ)).range s then h.choose else 0
  have hsF : ∀ Λ ∈ t, IsStdFiltered P (F.idem (VermaModule P Λ)).range (sF Λ) := fun Λ hΛ ↦ by
    have h := F.exists_isStdFiltered_verma (htb Λ hΛ)
    simp only [sF, h, ↓reduceDIte]
    exact h.choose_spec
  have hY : ∀ Λ, IsCategoryO P (VermaModule P Λ ⊗[K] V) := fun Λ ↦
    (VermaModule.isCategoryO P Λ).tensorProduct
      (isCategoryO_of_finiteDimensional (P := P) (hA := hA) V)
  have hTop := hψ.lieSubmodule ⊤
  have huF : u = t.bind sF := by
    refine eq_of_forall_sum_multiplicity_eq P fun κ ↦ ?_
    rw [← IsStdFiltered.multiplicity_eq_sum hFQ.isCategoryO hu κ,
      IsCategoryO.multiplicity_congr _ hFQ.isCategoryO (topEquiv P _) κ,
      ← IsCategoryO.multiplicity_congr (F.isCategoryO_range hTop.isCategoryO) hFQ.isCategoryO
        (LieModuleEquiv.ofBijective (F.map hTop hψ (⊤ : LieSubmodule K 𝔤 _).incl)
          ⟨F.map_injective hTop hψ Subtype.val_injective,
            F.map_surjective hTop hψ fun x ↦ ⟨⟨x, trivial⟩, rfl⟩⟩) κ,
      F.multiplicity_eq_sum_of_isStdFiltered hψ ht κ, Multiset.map_bind, Multiset.sum_bind]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun Λ hΛ ↦ ?_)
    exact IsStdFiltered.multiplicity_eq_sum (hY Λ) (hsF Λ hΛ) κ
  rw [vermaMult, ← hu.count_eq_finrank_hom hFQ.isCategoryO ν, huF, Multiset.count_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun Λ hΛ ↦ ?_)
  exact F.count_eq_vermaMult (htb Λ hΛ) (F.isCategoryO_range (VermaModule.isCategoryO P Λ))
    (hsF Λ hΛ) ν

/-- **Adjoint projective functors have transposed Verma multiplicities** (Bernstein–Gelfand,
Thm. 3.4 (iii); Humphreys, GSM 94, §10.8). Let `F = e(− ⊗ V)` be a projective functor on the block
of `λ` and `G = e'(− ⊗ W)` one on the block of `μ` mapping it to the block of `λ`, and suppose
`Hom(F(M), N) ≅ Hom(M, G(N))` for `M` in the block of `λ` and `N` in the block of `μ`. Then
`(F(M(χ)) : M(ν)) = (G(M(ν)) : M(χ))` for `χ` a weight of the block of `λ` and `ν` one of the
block of `μ`. -/
theorem vermaMult_eq_vermaMult_of_adjoint {μ : Dual K H} {W : Type (max u₁ u₂)}
    [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
    [LieModule K P.KacMoodyAlgebra W] [FiniteDimensional K W]
    (G : BlockProjectiveFunctor P hA μ W) (hG : G.MapsTo lam)
    (hadj : ∀ (M N : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
      [LieModule K 𝔤 M] [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N] [LieModule K 𝔤 N],
      IsInBlock P hA lam M → IsInBlock P hA μ N →
      Nonempty (((F.idem M).range →ₗ⁅K,𝔤⁆ N) ≃ₗ[K] (M →ₗ⁅K,𝔤⁆ (G.idem N).range)))
    {χ ν : Dual K H} (hχ : χ ∈ blockWeights P hA lam) (hν : ν ∈ blockWeights P hA μ) :
    F.vermaMult (VermaModule P χ) ν = G.vermaMult (VermaModule P ν) χ := by
  classical
  have hνb := isInBlock_verma_of_mem hν
  have hGM := hG _ hνb
  obtain ⟨sG, hsG⟩ := G.exists_isStdFiltered_verma hνb
  have hY : IsCategoryO P (VermaModule P ν ⊗[K] W) :=
    (VermaModule.isCategoryO P ν).tensorProduct
      (isCategoryO_of_finiteDimensional (P := P) (hA := hA) W)
  set B := (finite_blockWeights P hA lam).toFinset
  set a : Dual K H → ℕ := fun Λ ↦ F.vermaMult (VermaModule P Λ) ν
  have key : sG = B.val.bind fun Λ ↦ Multiset.replicate (a Λ) Λ := by
    refine eq_of_forall_sum_multiplicity_eq P fun ψ ↦ ?_
    rw [← IsStdFiltered.multiplicity_eq_sum hY hsG ψ, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul]
    rw [← Finset.sum_eq_multiset_sum]
    by_cases hψ : ψ ∈ blockWeights P hA lam
    · obtain ⟨t, ht, -, -⟩ := ProjectiveCover.exists_isStdFiltered P ψ hA
      have hcount := ProjectiveCover.count_eq_multiplicity P ψ hA ht
      have htb : ∀ Λ ∈ t, Λ ∈ blockWeights P hA lam := fun Λ hΛ ↦
        mem_blockWeights_of_multiplicity_ne_zero' hψ (by
          rw [← hcount Λ]
          exact Multiset.count_ne_zero.mpr hΛ)
      have hPb := isInBlock_projectiveCover hψ
      have hFQ := F.isFGProjectiveO_range hPb (ProjectiveCover.isFGProjectiveO P hA ψ)
      obtain ⟨e⟩ := hadj _ _ hPb hνb
      have h1 := ProjectiveCover.finrank_hom_eq_multiplicity (P := P) (hA := hA) (Λ := ψ)
        (G.isCategoryO_range (VermaModule.isCategoryO P ν))
      have h2 := hFQ.finrank_hom_restrictedDual P hA (VermaModule.isCategoryO P ν)
      have h3 := F.vermaMult_projectiveCover hPb ht (fun Λ hΛ ↦ isInBlock_verma_of_mem (htb Λ hΛ)) ν
      rw [vermaMult] at h3
      change (G.isCategoryO_range (VermaModule.isCategoryO P ν)).multiplicity ψ = _
      rw [← h1, ← e.finrank_eq, ← h2, h3, Finset.sum_multiset_map_count]
      rw [Finset.sum_subset (s₂ := B) (fun Λ hΛ ↦ (finite_blockWeights P hA lam).mem_toFinset.mpr
        (htb Λ (Multiset.mem_toFinset.mp hΛ))) (fun Λ _ hΛ ↦ by
          rw [Multiset.count_eq_zero.mpr fun h ↦ hΛ (Multiset.mem_toFinset.mpr h), zero_smul])]
      refine Finset.sum_congr rfl fun Λ _ ↦ ?_
      rw [hcount Λ, smul_eq_mul, mul_comm]
    · have h0 : (G.isCategoryO_range (VermaModule.isCategoryO P ν)).multiplicity ψ = 0 := by
        by_contra h
        exact hψ (hGM.multiplicity_ne_zero ψ h)
      change (G.isCategoryO_range (VermaModule.isCategoryO P ν)).multiplicity ψ = _
      rw [h0]
      refine (Finset.sum_eq_zero fun Λ hΛ ↦ ?_).symm
      have hΛ' := (finite_blockWeights P hA lam).mem_toFinset.mp hΛ
      by_cases hm : (VermaModule.isCategoryO P Λ).multiplicity ψ = 0
      · rw [hm, mul_zero]
      · exact absurd (mem_blockWeights_of_multiplicity_ne_zero hΛ' hm) hψ
  have hχB : χ ∈ B := (finite_blockWeights P hA lam).mem_toFinset.mpr hχ
  rw [← G.count_eq_vermaMult hνb (G.isCategoryO_range (VermaModule.isCategoryO P ν)) hsG χ, key,
    Multiset.count_bind, ← Finset.sum_eq_multiset_sum]
  simp only [Multiset.count_replicate]
  rw [Finset.sum_ite_eq' B χ a]
  simp only [hχB, ↓reduceIte, a]

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
