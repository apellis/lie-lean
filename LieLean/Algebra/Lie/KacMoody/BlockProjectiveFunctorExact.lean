/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorWeylGeneral
import LieLean.Algebra.Lie.KacMoody.TranslationMultiplicity

/-!
# Projective functors are exact

A projective functor `F = e(− ⊗ V)` on the block of `λ` is exact: tensoring with `V` is exact
over a field, and `F` is cut out of it by natural idempotents (Bernstein–Gelfand, §3.1). This
file records the consequences on composition multiplicities used for Bernstein–Gelfand's
Theorem 3.4 (iii): multiplicities of `F(B)` are additive on short exact sequences
`0 → A → B → C → 0` of the block, and if `X` has a standard filtration with factors `M(Λ)`,
`Λ ∈ s`, then `[F(X) : L(χ)] = Σ_{Λ ∈ s} [F(M(Λ)) : L(χ)]`.

## Main results

* `IsCategoryO.multiplicity_lieSubmodule_eq_add`: `[N' : L(χ)] = [N : L(χ)] + [M : L(χ)]` for
  `N ≤ N'` with `N' / N ≅ M`.
* `IsStdFiltered.multiplicity_eq_sum`: the multiplicities of a module with a standard filtration
  are the sums of the multiplicities of its Verma factors.
* `IsInBlock.lieSubmodule`: submodules of modules of the block lie in the block.
* `BlockProjectiveFunctor.multiplicity_eq_add_of_exact`: `F` is exact on multiplicities.
* `BlockProjectiveFunctor.multiplicity_eq_sum_of_isStdFiltered`: `F` is additive along standard
  filtrations.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285, §3.1,
  Thm. 3.4.
-/

noncomputable section

open Module LieModule TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {X M : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X] [AddCommGroup M] [Module K M]
  [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M]

/-- The surjection `N' → N' / N` onto the image of `N'` in `X / N`. -/
def lieSubmoduleQuotientMap (N N' : LieSubmodule K P.KacMoodyAlgebra X) :
    N' →ₗ⁅K,P.KacMoodyAlgebra⁆ N'.map (LieSubmodule.Quotient.mk' N) :=
  LieModuleHom.codRestrict _ ((LieSubmodule.Quotient.mk' N).comp N'.incl)
    fun x ↦ LieSubmodule.mem_map_of_mem x.2

omit [CharZero K] in
theorem lieSubmoduleQuotientMap_surjective (N N' : LieSubmodule K P.KacMoodyAlgebra X) :
    Function.Surjective (lieSubmoduleQuotientMap N N') := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := (LieSubmodule.mem_map _).mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

omit [CharZero K] in
theorem ker_lieSubmoduleQuotientMap {N N' : LieSubmodule K P.KacMoodyAlgebra X} (hle : N ≤ N') :
    (lieSubmoduleQuotientMap N N').ker = (LieSubmodule.inclusion hle).range := by
  ext x
  rw [LieModuleHom.mem_ker, LieModuleHom.mem_range]
  constructor
  · intro hx
    have hx' : LieSubmodule.Quotient.mk' N (x : X) = 0 := congrArg Subtype.val hx
    rw [LieSubmodule.Quotient.mk_eq_zero] at hx'
    exact ⟨⟨x, hx'⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    refine Subtype.ext ?_
    change LieSubmodule.Quotient.mk' N (y : X) = 0
    exact (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr y.2

namespace IsCategoryO

/-- `[N' : L(χ)] = [N : L(χ)] + [M : L(χ)]` for submodules `N ≤ N'` of a module in `𝒪` with
`N' / N ≅ M`. -/
theorem multiplicity_lieSubmodule_eq_add (hX : IsCategoryO P X) (hM : IsCategoryO P M)
    {N N' : LieSubmodule K P.KacMoodyAlgebra X} (hle : N ≤ N')
    (e : M ≃ₗ⁅K,P.KacMoodyAlgebra⁆ N'.map (LieSubmodule.Quotient.mk' N)) (χ : Dual K H) :
    (hX.lieSubmodule N').multiplicity χ =
      (hX.lieSubmodule N).multiplicity χ + hM.multiplicity χ :=
  multiplicity_eq_add_of_exact (hX.lieSubmodule N) (hX.lieSubmodule N') hM
    (LieSubmodule.inclusion hle) (e.symm.toLieModuleHom.comp (lieSubmoduleQuotientMap N N'))
    (LieSubmodule.inclusion_injective hle)
    (by
      rw [← ker_lieSubmoduleQuotientMap hle]
      ext x
      simp only [LieModuleHom.mem_ker, LieModuleHom.coe_comp, Function.comp_apply]
      exact e.symm.toLinearEquiv.map_eq_zero_iff)
    (e.symm.surjective.comp (lieSubmoduleQuotientMap_surjective N N')) χ

/-- A module in `𝒪` with no nonzero vectors has no composition factors. -/
theorem multiplicity_eq_zero_of_subsingleton [Subsingleton M] (hM : IsCategoryO P M)
    (χ : Dual K H) : hM.multiplicity χ = 0 :=
  hM.multiplicity_eq_zero_of_weightSpace_eq_bot (Subsingleton.elim _ _)

end IsCategoryO

/-- **Multiplicities of a module with a standard filtration**: if `N ⊆ X` has a standard
filtration with factors `M(ν)`, `ν ∈ s`, then `[N : L(χ)] = Σ_{ν ∈ s} [M(ν) : L(χ)]`. -/
theorem IsStdFiltered.multiplicity_eq_sum (hX : IsCategoryO P X)
    {N : LieSubmodule K P.KacMoodyAlgebra X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) (χ : Dual K H) :
    (hX.lieSubmodule N).multiplicity χ =
      (s.map fun ν ↦ (VermaModule.isCategoryO P ν).multiplicity χ).sum := by
  induction hN with
  | bot =>
    rw [Multiset.map_zero, Multiset.sum_zero]
    exact (hX.lieSubmodule ⊥).multiplicity_eq_zero_of_subsingleton χ
  | @step N N' s μ _ hle he ih =>
    obtain ⟨e⟩ := he
    rw [hX.multiplicity_lieSubmodule_eq_add (VermaModule.isCategoryO P μ) hle e, ih,
      Multiset.map_cons, Multiset.sum_cons, add_comm]

end Generic

section Block

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H] [IsAlgClosed K] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Modules of the block -/

namespace IsInBlock

variable {lam : Dual K H} {X M : Type (max u₁ u₂)} [AddCommGroup X] [Module K X]
  [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X] [AddCommGroup M]
  [Module K M] [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M]

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- A finitely generated module in `𝒪` whose multiplicities are bounded by those of a module of
the block lies in the block. -/
theorem of_multiplicity_le (hX : IsInBlock P hA lam X) (hM : IsCategoryO P M)
    (hfg : ∃ s : Finset M, LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤)
    (h : ∀ χ, hM.multiplicity χ ≤ hX.isCategoryO.multiplicity χ) : IsInBlock P hA lam M where
  isCategoryO := hM
  exists_finset := hfg
  multiplicity_ne_zero χ hχ := hX.multiplicity_ne_zero χ fun h0 ↦ hχ (by
    have := h χ
    omega)

/-- Submodules of modules of the block lie in the block. -/
theorem lieSubmodule (hX : IsInBlock P hA lam X) (N : LieSubmodule K 𝔤 X) :
    IsInBlock P hA lam N := by
  have := hX.isCategoryO.wellFoundedGT_lieSubmodule P hA hX.exists_finset.choose_spec
  have : WellFoundedGT (LieSubmodule K 𝔤 N) :=
    (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.val_injective).strictMono.wellFoundedGT
  have hfg : ∃ T : Finset N, LieSubmodule.lieSpan K 𝔤 (T : Set N) = ⊤ :=
    LieSubmodule.exists_finset_lieSpan_eq_top
  refine of_multiplicity_le (M := N) hX (hX.isCategoryO.lieSubmodule N) hfg ?_
  intro χ
  have := hX.isCategoryO.multiplicity_eq_add N χ
  omega

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- A module with a finite generating set isomorphic to a subquotient `N' / N` of a module of the
block lies in the block. -/
theorem of_equiv_map (hX : IsInBlock P hA lam X) (hM : IsCategoryO P M)
    (hfg : ∃ s : Finset M, LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤)
    {N N' : LieSubmodule K 𝔤 X} (hle : N ≤ N')
    (e : M ≃ₗ⁅K,𝔤⁆ N'.map (LieSubmodule.Quotient.mk' N)) : IsInBlock P hA lam M :=
  hX.of_multiplicity_le hM hfg fun χ ↦ by
    have h₁ := hX.isCategoryO.multiplicity_lieSubmodule_eq_add hM hle e χ
    have h₂ := hX.isCategoryO.multiplicity_eq_add N' χ
    omega

end IsInBlock

/-! ### Exactness -/

namespace BlockProjectiveFunctor

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

variable {A' B C : Type (max u₁ u₂)} [AddCommGroup A'] [Module K A']
  [LieRingModule P.KacMoodyAlgebra A'] [LieModule K P.KacMoodyAlgebra A'] [AddCommGroup B]
  [Module K B] [LieRingModule P.KacMoodyAlgebra B] [LieModule K P.KacMoodyAlgebra B]
  [AddCommGroup C] [Module K C] [LieRingModule P.KacMoodyAlgebra C]
  [LieModule K P.KacMoodyAlgebra C]

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- `f ⊗ 1` maps `F(A)` into `F(B)`. -/
theorem rTensor_mem_range (hA' : IsInBlock P hA lam A') (hB : IsInBlock P hA lam B)
    (f : A' →ₗ⁅K,𝔤⁆ B) (x : A' ⊗[K] V) (hx : x ∈ (F.idem A').range) :
    (f : A' →ₗ[K] B).rTensor V x ∈ (F.idem B).range := by
  obtain ⟨y, rfl⟩ := (LieModuleHom.mem_range _ _).mp hx
  rw [F.naturality hA' hB f y]
  exact (LieModuleHom.mem_range _ _).mpr ⟨_, rfl⟩

/-- The map `F(f) : F(A) → F(B)`, the restriction of `f ⊗ 1`. -/
def map (hA' : IsInBlock P hA lam A') (hB : IsInBlock P hA lam B) (f : A' →ₗ⁅K,𝔤⁆ B) :
    (F.idem A').range →ₗ⁅K,𝔤⁆ (F.idem B).range :=
  LieModuleHom.codRestrict _
    ((TensorProduct.LieModule.map f (LieModuleHom.id : V →ₗ⁅K,𝔤⁆ V)).comp
      (F.idem A').range.incl)
    fun x ↦ F.rTensor_mem_range hA' hB f x x.2

omit [IsAlgClosed K] [FiniteDimensional K H] in
theorem coe_map_apply (hA' : IsInBlock P hA lam A') (hB : IsInBlock P hA lam B)
    (f : A' →ₗ⁅K,𝔤⁆ B) (x : (F.idem A').range) :
    (F.map hA' hB f x : B ⊗[K] V) = (f : A' →ₗ[K] B).rTensor V x := rfl

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- `F` preserves injections. -/
theorem map_injective (hA' : IsInBlock P hA lam A') (hB : IsInBlock P hA lam B)
    {f : A' →ₗ⁅K,𝔤⁆ B} (hf : Function.Injective f) : Function.Injective (F.map hA' hB f) :=
  fun _ _ hxy ↦ Subtype.ext (Module.Flat.rTensor_preserves_injective_linearMap
    (M := V) (f : A' →ₗ[K] B) hf (congrArg Subtype.val hxy))

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- `F` preserves surjections. -/
theorem map_surjective (hB : IsInBlock P hA lam B) (hC : IsInBlock P hA lam C)
    {g : B →ₗ⁅K,𝔤⁆ C} (hg : Function.Surjective g) : Function.Surjective (F.map hB hC g) := by
  rintro ⟨y, hy⟩
  obtain ⟨z, rfl⟩ := (LieModuleHom.mem_range _ _).mp hy
  obtain ⟨x, rfl⟩ := LinearMap.rTensor_surjective V (g := (g : B →ₗ[K] C)) hg z
  refine ⟨⟨F.idem B x, (LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩⟩, Subtype.ext ?_⟩
  rw [coe_map_apply, F.naturality hB hC g x]

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- `F` is exact in the middle. -/
theorem ker_map_eq_range (hA' : IsInBlock P hA lam A') (hB : IsInBlock P hA lam B)
    (hC : IsInBlock P hA lam C) {f : A' →ₗ⁅K,𝔤⁆ B} {g : B →ₗ⁅K,𝔤⁆ C} (hex : g.ker = f.range)
    (hg : Function.Surjective g) : (F.map hB hC g).ker = (F.map hA' hB f).range := by
  have hexact : Function.Exact (f : A' →ₗ[K] B) (g : B →ₗ[K] C) := fun y ↦ by
    have := congrArg (y ∈ ·) hex
    simp only [LieModuleHom.mem_ker, LieModuleHom.mem_range] at this
    simpa [Set.mem_range] using this
  have hT := rTensor_exact V hexact hg
  ext ⟨y, hy⟩
  rw [LieModuleHom.mem_ker, LieModuleHom.mem_range]
  constructor
  · intro h0
    have h0' : (g : B →ₗ[K] C).rTensor V y = 0 := congrArg Subtype.val h0
    obtain ⟨x, hx⟩ := (hT y).mp h0'
    obtain ⟨z, rfl⟩ := (LieModuleHom.mem_range _ _).mp hy
    refine ⟨⟨F.idem A' x, (LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩⟩, Subtype.ext ?_⟩
    rw [coe_map_apply, F.naturality hA' hB f x, hx, F.idem_idem B hB z]
  · rintro ⟨x, hx⟩
    rw [← hx]
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero, coe_map_apply, coe_map_apply]
    exact (hT _).mpr ⟨x, rfl⟩

variable [FiniteDimensional K V]

omit [IsAlgClosed K] in
include hA in
/-- `F(M)` lies in `𝒪` for `M` in `𝒪`. -/
theorem isCategoryO_range {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M) :
    IsCategoryO P (F.idem M).range :=
  (hM.tensorProduct (isCategoryO_of_finiteDimensional (P := P) (hA := hA) V)).lieSubmodule _

omit [IsAlgClosed K] in
/-- **Projective functors are exact** (Bernstein–Gelfand, §3.1): for a short exact sequence
`0 → A → B → C → 0` of the block, `[F(B) : L(χ)] = [F(A) : L(χ)] + [F(C) : L(χ)]`. -/
theorem multiplicity_eq_add_of_exact (hA' : IsInBlock P hA lam A') (hB : IsInBlock P hA lam B)
    (hC : IsInBlock P hA lam C) {f : A' →ₗ⁅K,𝔤⁆ B} {g : B →ₗ⁅K,𝔤⁆ C}
    (hf : Function.Injective f) (hex : g.ker = f.range) (hg : Function.Surjective g)
    (χ : Dual K H) :
    (F.isCategoryO_range hB.isCategoryO).multiplicity χ =
      (F.isCategoryO_range hA'.isCategoryO).multiplicity χ +
        (F.isCategoryO_range hC.isCategoryO).multiplicity χ :=
  IsCategoryO.multiplicity_eq_add_of_exact _ _ _ (F.map hA' hB f) (F.map hB hC g)
    (F.map_injective hA' hB hf) (F.ker_map_eq_range hA' hB hC hex hg)
    (F.map_surjective hB hC hg) χ

/-- **Projective functors are additive along standard filtrations**: if `N ⊆ X` (`X` in the
block) has a standard filtration with factors `M(Λ)`, `Λ ∈ s`, then
`[F(N) : L(χ)] = Σ_{Λ ∈ s} [F(M(Λ)) : L(χ)]`. -/
theorem multiplicity_eq_sum_of_isStdFiltered {X : Type (max u₁ u₂)} [AddCommGroup X]
    [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X] (hX : IsInBlock P hA lam X)
    {N : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s)
    (χ : Dual K H) :
    (F.isCategoryO_range (hX.isCategoryO.lieSubmodule N)).multiplicity χ =
      (s.map fun Λ ↦ (F.isCategoryO_range (VermaModule.isCategoryO P Λ)).multiplicity χ).sum := by
  induction hN with
  | bot =>
    rw [Multiset.map_zero, Multiset.sum_zero]
    have : Subsingleton (⊥ : LieSubmodule K 𝔤 X) :=
      ⟨fun a b ↦ Subtype.ext ((a.2.trans b.2.symm : (a : X) = b))⟩
    have : Subsingleton ((⊥ : LieSubmodule K 𝔤 X) ⊗[K] V) := by
      refine ⟨fun a b ↦ ?_⟩
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    have : Subsingleton (F.idem (⊥ : LieSubmodule K 𝔤 X)).range :=
      ⟨fun a b ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    exact IsCategoryO.multiplicity_eq_zero_of_subsingleton _ χ
  | @step N N' s Λ _ hle he ih =>
    obtain ⟨e⟩ := he
    have hN := hX.lieSubmodule N
    have hN' := hX.lieSubmodule N'
    have hΛ := hX.of_equiv_map (VermaModule.isCategoryO P Λ)
      (isInBlock_verma P hA Λ).exists_finset hle e
    rw [F.multiplicity_eq_add_of_exact hN hN' hΛ (f := LieSubmodule.inclusion hle)
      (g := (e.symm : N'.map (LieSubmodule.Quotient.mk' N) →ₗ⁅K,𝔤⁆ VermaModule P Λ).comp
        (lieSubmoduleQuotientMap N N')) (LieSubmodule.inclusion_injective hle)
      (by
        rw [← ker_lieSubmoduleQuotientMap hle]
        ext x
        rw [LieModuleHom.mem_ker, LieModuleHom.mem_ker, LieModuleHom.comp_apply]
        exact e.symm.toLinearEquiv.map_eq_zero_iff)
      (e.symm.surjective.comp (lieSubmoduleQuotientMap_surjective N N')) χ,
      ih, Multiset.map_cons, Multiset.sum_cons, add_comm]

end BlockProjectiveFunctor

end Block

end Matrix.Realization.KacMoodyAlgebra
