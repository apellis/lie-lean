/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorWeyl
import LieLean.Algebra.Lie.KacMoody.TranslationAdjunction
import LieLean.Algebra.Lie.KacMoody.DominantVermaTensor

/-!
# Projective functors commute with the Weyl group: the dominant case

Bernstein–Gelfand's proof of Theorem 3.4 (iv), the case of §3.9 (d). Let `λ` be dominant and
`F` a projective functor on the block of `λ` with `F(M(λ)) ≅ P(ψ)`, where `λ` dominates the
linkage class of `ψ`: `λ - ξ` is dominant integral for every `ξ` linked to `ψ` with `ξ - ψ` in
the root lattice. Then `F` commutes with `W_[λ]` on Verma multiplicities.

The proof is BG's induction on the weights above `ψ` in its linkage class (`linkedAbove`; BG use
the height `(λ - ψ)(h)`, which decreases along the same steps). With `L = L(λ - ψ)`, the
functor `G = pr_{χ_ψ}(− ⊗ L^*)` commutes with `W`, and decomposes into indecomposable summands
`Gᵢ` with `Gᵢ(M(λ)) ≅ P(μᵢ)`. By BGG reciprocity one of them has `μᵢ = ψ`, and all others have
`μᵢ > ψ` linked to `ψ`, so they commute with `W` by induction. Verma multiplicities are additive
over the decomposition, so the summand with `μᵢ = ψ` commutes with `W`, and it is isomorphic to
`F` on the block (Cor. 3.8). The Kostant hypothesis enters through the classification of
indecomposable projective functors.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.finrank_hom_range_eq_add`,
  `finrank_hom_range_list_sum`: for orthogonal idempotents on a module with a standard
  filtration, `dim Hom(e(Y), M(ν)^∨)` is additive.
* `linkedAbove`, `finite_linkedAbove`, `ncard_linkedAbove_lt`: the induction measure.
* `BlockProjectiveFunctor.vermaMult_eq_sum`: additivity over a decomposition of `F`.
* `BlockProjectiveFunctor.vermaMult_eq_of_bijOn`,
  `BlockProjectiveFunctor.CommutesWithWeyl.of_bijOn`.
* `BlockProjectiveFunctor.vermaMult_verma_eq_multiplicity`: if `F(M(λ)) ≅ P(μ)`, then
  `(F(M(λ)) : M(ν)) = [M(ν) : L(μ)]`.
* `BlockProjectiveFunctor.commutesWithWeyl_of_equiv_projectiveCover`: BG Thm. 3.4 (iv), case
  §3.9 (d).

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285, §3.9 (d).
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 3.7, Prop. 3.7 (b), Thm. 3.11, §10.8.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Additivity

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] in
/-- `dim Hom(M, D)` only depends on `M` up to isomorphism. -/
theorem finrank_hom_congr_left {M M' D : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] [AddCommGroup M'] [Module K M'] [LieRingModule 𝔤 M']
    [LieModule K 𝔤 M'] [AddCommGroup D] [Module K D] [LieRingModule 𝔤 D] [LieModule K 𝔤 D]
    (E : M ≃ₗ⁅K,𝔤⁆ M') : finrank K (M →ₗ⁅K,𝔤⁆ D) = finrank K (M' →ₗ⁅K,𝔤⁆ D) :=
  (lieModuleHomCongr P E LieModuleEquiv.refl).finrank_eq

/-- **Additivity of Verma multiplicities over a direct sum decomposition** (Humphreys, GSM 94,
Prop. 3.7 (b) and Thm. 3.7): let `Y ∈ 𝒪` have a standard filtration, and let `e₁` and `e - e₁` be
orthogonal idempotents. Then `dim Hom(e(Y), M(ν)^∨) = dim Hom(e₁(Y), M(ν)^∨) +
dim Hom((e - e₁)(Y), M(ν)^∨)`. -/
theorem finrank_hom_range_eq_add {Y : Type*} [AddCommGroup Y] [Module K Y]
    [LieRingModule 𝔤 Y] [LieModule K 𝔤 Y] (hY : IsCategoryO P Y)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 Y) s)
    {e e₁ : Y →ₗ⁅K,𝔤⁆ Y} (he : e.comp e = e) (he₁ : e₁.comp e₁ = e₁) (hee₁ : e.comp e₁ = e₁)
    (he₁e : e₁.comp e = e₁) (ν : Dual K H) :
    finrank K (e.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) =
      finrank K (e₁.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) +
        finrank K ((e - e₁).range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) := by
  classical
  have hee (y : Y) : e (e y) = e y := LieModuleHom.congr_fun he y
  have hee₁' (y : Y) : e (e₁ y) = e₁ y := LieModuleHom.congr_fun hee₁ y
  have he₁e' (y : Y) : e₁ (e y) = e₁ y := LieModuleHom.congr_fun he₁e y
  have he₁e₁ (y : Y) : e₁ (e₁ y) = e₁ y := LieModuleHom.congr_fun he₁ y
  obtain ⟨t, ht⟩ := exists_isStdFiltered_range P _ hY s rfl hs e he
  have hX : IsCategoryO P e.range := hY.lieSubmodule _
  have htX := isStdFiltered_top_range P he ht
  have hmem (y : e.range) : e₁ y ∈ e.range :=
    (LieModuleHom.mem_range _ _).mpr ⟨e₁ y, hee₁' y⟩
  set p : e.range →ₗ⁅K,𝔤⁆ e.range := LieModuleHom.codRestrict _ (e₁.comp e.range.incl) hmem
  have hp (y : e.range) : (p y : Y) = e₁ y := rfl
  have hpp : p.comp p = p := LieModuleHom.ext fun y ↦ Subtype.ext <| by
    change e₁ (e₁ y) = e₁ y
    exact he₁e₁ y
  obtain ⟨a, b, ha, hb, hab⟩ := exists_isStdFiltered_range_add P hX htX p hpp
  set q : e.range →ₗ⁅K,𝔤⁆ e.range := LieModuleHom.id - p
  have hq (y : e.range) : (q y : Y) = y - e₁ y := rfl
  have hqq : q.comp q = q := LieModuleHom.ext fun y ↦ Subtype.ext <| by
    change (q y : Y) - e₁ (q y) = q y
    rw [hq, map_sub, he₁e₁, sub_self, sub_zero]
  have hqk : q.range = p.ker := by
    ext x
    rw [LieModuleHom.mem_range, LieModuleHom.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      change e₁ (q y : Y) = 0
      rw [hq, map_sub, he₁e₁, sub_self]
    · intro h
      refine ⟨x, Subtype.ext ?_⟩
      rw [hq, ← hp, h]
      exact sub_zero _
  rw [← hqk] at hb
  have hinj : Function.Injective e.range.incl := Subtype.val_injective
  have hmap₁ : p.range.map e.range.incl = e₁.range := by
    ext y
    rw [LieSubmodule.mem_map, LieModuleHom.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨z, rfl⟩
      refine ⟨p ⟨e z, (LieModuleHom.mem_range _ _).mpr ⟨z, rfl⟩⟩,
        (LieModuleHom.mem_range _ _).mpr ⟨_, rfl⟩, ?_⟩
      change e₁ (e z) = e₁ z
      exact he₁e' z
  have hmap₂ : q.range.map e.range.incl = (e - e₁).range := by
    ext y
    rw [LieSubmodule.mem_map, LieModuleHom.mem_range]
    constructor
    · rintro ⟨_, ⟨⟨_, ⟨z, rfl⟩⟩, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      change e z - e₁ z = e z - e₁ (e z)
      rw [he₁e']
    · rintro ⟨z, rfl⟩
      refine ⟨q ⟨e z, (LieModuleHom.mem_range _ _).mpr ⟨z, rfl⟩⟩,
        (LieModuleHom.mem_range _ _).mpr ⟨_, rfl⟩, ?_⟩
      change e z - e₁ (e z) = e z - e₁ z
      rw [he₁e']
  have h0 := htX.count_eq_finrank_hom hX ν
  have h1 := ha.count_range_eq_finrank_hom P hpp (hX.lieSubmodule _) ν
  have h2 := hb.count_range_eq_finrank_hom P hqq (hX.lieSubmodule _) ν
  rw [finrank_hom_congr_left P (p.range.equivMapOfInjective hinj), hmap₁] at h1
  rw [finrank_hom_congr_left P (q.range.equivMapOfInjective hinj), hmap₂] at h2
  rw [← h0, ← h1, ← h2, hab, Multiset.count_add]

omit [CharZero K] in
/-- An element orthogonal to every member of a list is orthogonal to its sum. -/
theorem mul_list_sum_eq_zero {Y : Type*} [AddCommGroup Y] [Module K Y] [LieRingModule 𝔤 Y]
    [LieModule K 𝔤 Y] (a : Y →ₗ⁅K,𝔤⁆ Y) (l : List (Y →ₗ⁅K,𝔤⁆ Y))
    (hl : ∀ e ∈ l, a * e = 0 ∧ e * a = 0) : a * l.sum = 0 ∧ l.sum * a = 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    obtain ⟨h₁, h₂⟩ := ih fun e he ↦ hl e (List.mem_cons_of_mem b he)
    rw [List.sum_cons, mul_add, add_mul, (hl b List.mem_cons_self).1,
      (hl b List.mem_cons_self).2, h₁, h₂, add_zero]
    exact ⟨rfl, rfl⟩

omit [CharZero K] in
/-- A sum of pairwise orthogonal idempotents is idempotent. -/
theorem list_sum_mul_self {Y : Type*} [AddCommGroup Y] [Module K Y] [LieRingModule 𝔤 Y]
    [LieModule K 𝔤 Y] (l : List (Y →ₗ⁅K,𝔤⁆ Y)) (hl : ∀ e ∈ l, e * e = e)
    (hp : l.Pairwise fun e e' ↦ e * e' = 0 ∧ e' * e = 0) : l.sum * l.sum = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hp
    obtain ⟨h₁, h₂⟩ := mul_list_sum_eq_zero P a t hp.1
    rw [List.sum_cons, add_mul, mul_add, mul_add, h₁, h₂, hl a List.mem_cons_self,
      ih (fun e he ↦ hl e (List.mem_cons_of_mem a he)) hp.2, add_zero, zero_add]

/-- **Additivity of Verma multiplicities over a decomposition into pairwise orthogonal
idempotents**: if `Y ∈ 𝒪` has a standard filtration and `e₁, …, eₙ` are pairwise orthogonal
idempotents of `Y`, then `dim Hom((Σ eᵢ)(Y), M(ν)^∨) = Σ dim Hom(eᵢ(Y), M(ν)^∨)`. -/
theorem finrank_hom_range_list_sum {Y : Type*} [AddCommGroup Y] [Module K Y]
    [LieRingModule 𝔤 Y] [LieModule K 𝔤 Y] (hY : IsCategoryO P Y)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 Y) s) (ν : Dual K H)
    (l : List (Y →ₗ⁅K,𝔤⁆ Y)) (hl : ∀ e ∈ l, e * e = e)
    (hp : l.Pairwise fun e e' ↦ e * e' = 0 ∧ e' * e = 0) :
    finrank K (l.sum.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) =
      (l.map fun e ↦ finrank K (e.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν))).sum := by
  classical
  induction l with
  | nil =>
    rw [List.sum_nil, List.map_nil, List.sum_nil]
    have : Subsingleton ((0 : Y →ₗ⁅K,𝔤⁆ Y).range →ₗ⁅K,𝔤⁆
        restrictedDual P (VermaModule P ν)) := ⟨fun f g ↦ LieModuleHom.ext fun x ↦ by
      obtain ⟨_, ⟨y, rfl⟩⟩ := x
      have : (⟨(0 : Y →ₗ⁅K,𝔤⁆ Y) y, ⟨y, rfl⟩⟩ : (0 : Y →ₗ⁅K,𝔤⁆ Y).range) = 0 := rfl
      rw [this, map_zero, map_zero]⟩
    exact Module.finrank_zero_of_subsingleton
  | cons a t ih =>
    have hp' := hp
    rw [List.pairwise_cons] at hp'
    have hl' : ∀ e ∈ t, e * e = e := fun e he ↦ hl e (List.mem_cons_of_mem a he)
    obtain ⟨h₂, h₁⟩ := mul_list_sum_eq_zero P a t hp'.1
    have ha : a * a = a := hl a List.mem_cons_self
    have h := finrank_hom_range_eq_add P hY hs (list_sum_mul_self P (a :: t) hl hp) ha
      (show (a + t.sum) * a = a by rw [add_mul, ha, h₁, add_zero])
      (show a * (a + t.sum) = a by rw [mul_add, ha, h₂, add_zero]) ν
    rw [List.sum_cons, add_sub_cancel_left] at h
    rw [List.sum_cons, h, ih hl' hp'.2, List.map_cons, List.sum_cons]

end Additivity

section LinkedAbove

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The weights `ξ ≠ ψ` above `ψ` (`ψ ≤ ξ`) with the central character of `ψ`. -/
def linkedAbove (ψ : Dual K H) : Set (Dual K H) :=
  {ξ | centralCharacter P ξ = centralCharacter P ψ ∧ ψ ∈ cone P ξ ∧ ξ ≠ ψ}

/-- Finitely many weights lie above `ψ` in its linkage class (Harish-Chandra). -/
theorem finite_linkedAbove (hA : A.IsFiniteCartan) (ψ : Dual K H) :
    (linkedAbove P ψ).Finite := by
  have := P.finite_weylGroup hA
  refine (Set.finite_range fun w : P.weylGroup hA.isGeneralizedCartan ↦
    P.weylDot hA.isGeneralizedCartan w ψ).subset fun ξ hξ ↦ ?_
  obtain ⟨w, hw, hwξ⟩ := (VermaModule.centralCharacter_eq_iff P hA ψ ξ).mp hξ.1.symm
  refine ⟨⟨w, hw⟩, ?_⟩
  change w (ψ + P.rho) - P.rho = ξ
  rw [hwξ, add_sub_cancel_right]

/-- Passing to a weight above `ψ` in its linkage class decreases the number of weights above. -/
theorem ncard_linkedAbove_lt (hA : A.IsFiniteCartan) {ψ μ : Dual K H}
    (hμ : μ ∈ linkedAbove P ψ) : (linkedAbove P μ).ncard < (linkedAbove P ψ).ncard := by
  refine Set.ncard_lt_ncard ⟨fun ξ hξ ↦ ⟨hξ.1.trans hμ.1, mem_cone_trans hμ.2.1 hξ.2.1,
    fun h ↦ hμ.2.2 ?_⟩, fun h ↦ (h hμ).2.2 rfl⟩ (finite_linkedAbove P hA ψ)
  subst h
  exact eq_of_mem_cone_of_mem_cone hξ.2.1 hμ.2.1

end LinkedAbove

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ}

namespace BlockProjectiveFunctor

variable {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

/-- Verma multiplicities only depend on `F(M)` up to isomorphism. -/
theorem vermaMult_eq_of_equiv {W : Type (max u₁ u₂)} [AddCommGroup W] [Module K W]
    [LieRingModule 𝔤 W] [LieModule K 𝔤 W] (G : BlockProjectiveFunctor P hA lam W)
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (E : (F.idem M).range ≃ₗ⁅K,𝔤⁆ (G.idem M).range) (ν : Dual K H) :
    F.vermaMult M ν = G.vermaMult M ν :=
  finrank_hom_congr_left P E

/-- A natural transformation mapping `F(M)` bijectively onto `G(M)` (as in Cor. 3.8) preserves
Verma multiplicities. -/
theorem vermaMult_eq_of_bijOn {W : Type (max u₁ u₂)} [AddCommGroup W] [Module K W]
    [LieRingModule 𝔤 W] [LieModule K 𝔤 W] (G : BlockProjectiveFunctor P hA lam W)
    (φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W)
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hb : Set.BijOn (fun x ↦ G.idem M (φ.app M x)) (Set.range (F.idem M))
      (Set.range (G.idem M))) (ν : Dual K H) :
    F.vermaMult M ν = G.vermaMult M ν := by
  have hmem (x : (F.idem M).range) : ((G.idem M).comp (φ.app M)) x ∈ (G.idem M).range :=
    (LieModuleHom.mem_range _ _).mpr ⟨_, rfl⟩
  set f : (F.idem M).range →ₗ⁅K,𝔤⁆ (G.idem M).range :=
    LieModuleHom.codRestrict _ (((G.idem M).comp (φ.app M)).comp (F.idem M).range.incl) hmem
  have hf (x : (F.idem M).range) : (f x : M ⊗[K] W) = G.idem M (φ.app M x) := rfl
  have hrange (x : (F.idem M).range) : (x : M ⊗[K] V) ∈ Set.range (F.idem M) := by
    obtain ⟨_, y, rfl⟩ := x
    exact ⟨y, rfl⟩
  refine F.vermaMult_eq_of_equiv G (LieModuleEquiv.ofBijective f ⟨fun x y hxy ↦ ?_, ?_⟩) ν
  · exact Subtype.ext (hb.injOn (hrange x) (hrange y) (by
      have := congrArg Subtype.val hxy
      rwa [hf, hf] at this))
  · rintro ⟨_, z, rfl⟩
    obtain ⟨x, hx, hxz⟩ := hb.surjOn ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨F.idem M y, y, rfl⟩, Subtype.ext hxz⟩

variable [IsAlgClosed K] [FiniteDimensional K H]

include hA in
/-- `M(w·λ)` lies in the block of `λ` for `w ∈ W_[λ]`. -/
theorem isInBlock_verma_weylDot {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    IsInBlock P hA lam (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)) where
  isCategoryO := VermaModule.isCategoryO P _
  exists_finset := (isInBlock_verma P hA _).exists_finset
  multiplicity_ne_zero μ hμ := by
    obtain ⟨x, -, hx⟩ := (isInBlock_verma P hA _).multiplicity_ne_zero μ hμ
    obtain ⟨k, -, hk⟩ := VermaModule.mem_cone_of_multiplicity_ne_zero hμ
    refine ⟨x * w, ?_, by rw [weylDot_mul, hx]⟩
    rw [mem_integralWeylGroup_iff_dot] at hw ⊢
    have h : P.weylDot hA.isGeneralizedCartan (x * w) lam - lam =
        -P.rootOf k + (P.weylDot hA.isGeneralizedCartan w lam - lam) := by
      rw [weylDot_mul, ← hx, hk]
      abel
    change P.weylDot hA.isGeneralizedCartan (x * w) lam - lam ∈ P.rootLattice
    rw [h]
    exact add_mem (neg_mem (P.rootOf_mem_rootLattice k)) hw

/-- **Projective functors isomorphic on the block commute with `W` together**. -/
theorem CommutesWithWeyl.of_bijOn {W : Type (max u₁ u₂)} [AddCommGroup W] [Module K W]
    [LieRingModule 𝔤 W] [LieModule K 𝔤 W] {G : BlockProjectiveFunctor P hA lam W}
    (hG : G.CommutesWithWeyl) (φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W)
    (hb : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
      [LieModule K 𝔤 M], IsInBlock P hA lam M →
      Set.BijOn (fun x ↦ G.idem M (φ.app M x)) (Set.range (F.idem M))
        (Set.range (G.idem M))) :
    F.CommutesWithWeyl := fun w hw ν ↦ by
  rw [F.vermaMult_eq_of_bijOn G φ (hb _ (isInBlock_verma_weylDot hw)),
    F.vermaMult_eq_of_bijOn G φ (hb _ (isInBlock_verma P hA lam)), hG w hw ν]

omit [IsAlgClosed K] in
include hA in
/-- **Additivity of Verma multiplicities over a decomposition of `F`**: if `F` is the sum on the
block of pairwise orthogonal summands `G₁, …, Gₙ`, then `(F(M(Λ)) : M(ν)) = Σ (Gᵢ(M(Λ)) : M(ν))`
for every Verma module `M(Λ)` of the block. -/
theorem vermaMult_eq_sum [FiniteDimensional K V] (l : List (BlockProjectiveFunctor P hA lam V))
    (hp : l.Pairwise (fun G G' ↦ ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M]
      [LieRingModule 𝔤 M] [LieModule K 𝔤 M], IsInBlock P hA lam M →
        G.idem M * G'.idem M = 0 ∧ G'.idem M * G.idem M = 0))
    (hsum : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
      [LieModule K 𝔤 M], IsInBlock P hA lam M → (l.map fun G ↦ G.idem M).sum = F.idem M)
    {Λ : Dual K H} (hΛ : IsInBlock P hA lam (VermaModule P Λ)) (ν : Dual K H) :
    F.vermaMult (VermaModule P Λ) ν = (l.map fun G ↦ G.vermaMult (VermaModule P Λ) ν).sum := by
  classical
  obtain ⟨s, hs, -⟩ := exists_isStdFiltered_tensorVerma P
    (isHDiagonalizable_of_finiteDimensional (V := V) hA) Λ
  have hY := (VermaModule.isCategoryO P Λ).tensorProduct
    (isCategoryO_of_finiteDimensional (P := P) (hA := hA) V)
  have h := finrank_hom_range_list_sum P hY hs ν (l.map fun G ↦ G.idem (VermaModule P Λ))
    (fun e he ↦ by
      obtain ⟨G, -, rfl⟩ := List.mem_map.mp he
      exact G.idem_mul_idem hΛ)
    (List.pairwise_map.mpr (hp.imp fun h ↦ h _ hΛ))
  rw [hsum _ hΛ, List.map_map] at h
  exact h

include hA in
/-- **Verma multiplicities of a projective cover** (BGG reciprocity, Humphreys, GSM 94,
Thm. 3.11): if `F(M(λ)) ≅ P(μ)`, then `(F(M(λ)) : M(ν)) = [M(ν) : L(μ)]`. -/
theorem vermaMult_verma_eq_multiplicity {μ : Dual K H}
    (E : ProjectiveCover P hA μ ≃ₗ⁅K,𝔤⁆ F.vermaValue) (ν : Dual K H) :
    F.vermaMult (VermaModule P lam) ν = (VermaModule.isCategoryO P ν).multiplicity μ := by
  rw [vermaMult, ← finrank_hom_congr_left P E,
    ProjectiveCover.finrank_hom_eq_multiplicity (P := P) (hA := hA) (Λ := μ)
      (isCategoryO_restrictedDual (VermaModule.isCategoryO P ν)),
    multiplicity_restrictedDual]

include hA in
/-- The induction of Bernstein–Gelfand §3.9 (d), on the number of weights above `ψ` in its
linkage class. -/
private theorem commutesWithWeyl_of_ncard (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) :
    ∀ (n : ℕ) (ψ : Dual K H), (linkedAbove P ψ).ncard = n →
      (∀ ξ, centralCharacter P ξ = centralCharacter P ψ → ξ - ψ ∈ P.rootLattice →
        P.IsDominantIntegral (lam - ξ)) →
      ∀ (V₁ : Type (max u₁ u₂)) [AddCommGroup V₁] [Module K V₁] [LieRingModule 𝔤 V₁]
        [LieModule K 𝔤 V₁] [FiniteDimensional K V₁] (F₁ : BlockProjectiveFunctor P hA lam V₁),
        Nonempty (ProjectiveCover P hA ψ ≃ₗ⁅K,𝔤⁆ F₁.vermaValue) → F₁.CommutesWithWeyl := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ψ hn hD V₁ _ _ _ _ _ F₁ ⟨E₁⟩
  have hν : P.IsDominantIntegral (lam - ψ) := hD ψ rfl (by rw [sub_self]; exact zero_mem _)
  have := IrreducibleModule.finiteDimensional hA hν
  set L := IrreducibleModule P (lam - ψ)
  have hLO := isCategoryO_of_finiteDimensional (P := P) (hA := hA) L
  have hLO' := isCategoryO_of_finiteDimensional (P := P) (hA := hA) (Module.Dual K L)
  set G := tensorBlock P hA lam (Module.Dual K L) (centralCharacter P ψ)
  have hGv (ξ : Dual K H) : G.vermaMult (VermaModule P lam) ξ =
      if centralCharacter P ξ = centralCharacter P ψ then
        finrank K (weightSpace P L (lam - ξ)) else 0 := by
    rw [vermaMult_tensorBlock]
    split_ifs
    · rw [weightSpace, finrank_weightSpaceOfMap_dual P hLO.1 hLO'.1, neg_sub]
    · rfl
  obtain ⟨l, hl, hp, hsum⟩ := G.exists_decomposition hlam hM₀ hI
  have hμ : ∀ G' ∈ l, ∃ μ, Nonempty (ProjectiveCover P hA μ ≃ₗ⁅K,𝔤⁆ G'.vermaValue) :=
    fun G' hG' ↦ G'.exists_nonempty_equiv_projectiveCover hlam hM₀ hI hK (hl G' hG').1
  have hdec (ξ : Dual K H) : G.vermaMult (VermaModule P lam) ξ =
      (l.map fun G' ↦ G'.vermaMult (VermaModule P lam) ξ).sum :=
    G.vermaMult_eq_sum l hp hsum (isInBlock_verma P hA lam) ξ
  -- The summands are projective covers `P(μ)` with `μ ≥ ψ` linked to `ψ`.
  have hcone : ∀ G' ∈ l, ∀ μ, Nonempty (ProjectiveCover P hA μ ≃ₗ⁅K,𝔤⁆ G'.vermaValue) →
      centralCharacter P μ = centralCharacter P ψ ∧ ψ ∈ cone P μ := by
    rintro G' hG' μ ⟨E⟩
    have h1 : G'.vermaMult (VermaModule P lam) μ = 1 := by
      rw [G'.vermaMult_verma_eq_multiplicity E μ, VermaModule.multiplicity_self]
    have h2 : 1 ≤ G.vermaMult (VermaModule P lam) μ := by
      rw [hdec, ← h1]
      exact List.le_sum_of_mem (List.mem_map_of_mem hG')
    rw [hGv] at h2
    split_ifs at h2 with hc
    · refine ⟨hc, ?_⟩
      have hne : weightSpace P L (lam - μ) ≠ ⊥ := fun h ↦ by
        rw [h, finrank_bot] at h2
        omega
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨k, hk, h⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P (lam - ψ)
        (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P (lam - ψ)))
        (LieSubmodule.Quotient.surjective_mk' _) hx hx0
      refine ⟨k, hk, ?_⟩
      calc ψ = lam - (lam - ψ - P.rootOf k) - P.rootOf k := by abel
        _ = lam - (lam - μ) - P.rootOf k := by rw [h]
        _ = μ - P.rootOf k := by abel
    · omega
  have hval : ∀ G' ∈ l, ∀ μ, Nonempty (ProjectiveCover P hA μ ≃ₗ⁅K,𝔤⁆ G'.vermaValue) →
      G'.vermaMult (VermaModule P lam) ψ = if μ = ψ then 1 else 0 := by
    rintro G' hG' μ ⟨E⟩
    rw [G'.vermaMult_verma_eq_multiplicity E ψ]
    split_ifs with h
    · subst h
      exact VermaModule.multiplicity_self _
    · by_contra hne
      exact h (eq_of_mem_cone_of_mem_cone (VermaModule.mem_cone_of_multiplicity_ne_zero hne)
        (hcone G' hG' μ ⟨E⟩).2)
  have hsumψ := hdec ψ
  rw [hGv, ite_eq_left rfl, IrreducibleModule.finrank_weightSpace_self P (lam - ψ)] at hsumψ
  obtain ⟨x, hx, hx0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero (by
    rw [← hsumψ]; exact one_ne_zero)
  obtain ⟨Gk, hGk, rfl⟩ := List.mem_map.mp hx
  obtain ⟨μk, ⟨Ek⟩⟩ := hμ Gk hGk
  have hμk : μk = ψ := by
    rw [hval Gk hGk μk ⟨Ek⟩] at hx0
    by_contra h
    exact hx0 (ite_eq_right h)
  rw [hμk] at Ek
  have hGkψ : Gk.vermaMult (VermaModule P lam) ψ = 1 := by
    rw [hval Gk hGk ψ ⟨Ek⟩, ite_eq_left rfl]
  obtain ⟨s, t, hst⟩ := List.append_of_mem hGk
  -- The other summands are covers `P(μ)` with `μ` strictly above `ψ`: induction.
  have hrest : ∀ G' ∈ s ++ t, G'.CommutesWithWeyl := by
    intro G' hG'
    have hG'l : G' ∈ l := by
      rw [hst]
      rcases List.mem_append.mp hG' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨μ', ⟨E'⟩⟩ := hμ G' hG'l
    have h0 : G'.vermaMult (VermaModule P lam) ψ = 0 := by
      have h := hsumψ
      rw [hst, List.map_append, List.map_cons, List.sum_append, List.sum_cons, hGkψ] at h
      rcases List.mem_append.mp hG' with h' | h'
      · have := List.le_sum_of_mem (List.mem_map_of_mem
          (f := fun G' ↦ G'.vermaMult (VermaModule P lam) ψ) h')
        omega
      · have := List.le_sum_of_mem (List.mem_map_of_mem
          (f := fun G' ↦ G'.vermaMult (VermaModule P lam) ψ) h')
        omega
    have hne : μ' ≠ ψ := fun h ↦ by
      rw [hval G' hG'l μ' ⟨E'⟩, ite_eq_left h] at h0
      exact one_ne_zero h0
    obtain ⟨hc, hc'⟩ := hcone G' hG'l μ' ⟨E'⟩
    have hmem : μ' ∈ linkedAbove P ψ := ⟨hc, hc', hne⟩
    refine ih _ (hn ▸ ncard_linkedAbove_lt P hA hmem) μ' rfl (fun ξ hξ hξ' ↦ hD ξ (hξ.trans hc)
      ?_) (Module.Dual K L) G' ⟨E'⟩
    obtain ⟨k, -, hk⟩ := hc'
    rw [show ξ - ψ = (ξ - μ') + (μ' - ψ) by abel, hk, sub_sub_cancel]
    exact add_mem hξ' (P.rootOf_mem_rootLattice k)
  -- Hence `Gk`, the summand with `Gk(M(λ)) ≅ P(ψ)`, commutes with `W` as `G` does.
  have hGkc : Gk.CommutesWithWeyl := by
    intro w hw ξ
    have hG := commutesWithWeyl_tensorBlock (P := P) (hA := hA) (lam := lam)
      (V := Module.Dual K L) (centralCharacter P ψ) w hw ξ
    have h1 := G.vermaMult_eq_sum l hp hsum (isInBlock_verma_weylDot hw)
      (P.weylDot hA.isGeneralizedCartan w ξ)
    have h2 := hdec ξ
    rw [hst, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at h1 h2
    have hs : (s.map fun G' ↦ G'.vermaMult (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
        (P.weylDot hA.isGeneralizedCartan w ξ)).sum =
        (s.map fun G' ↦ G'.vermaMult (VermaModule P lam) ξ).sum :=
      congrArg List.sum (List.map_congr_left fun G' hG' ↦
        hrest G' (List.mem_append_left _ hG') w hw ξ)
    have ht : (t.map fun G' ↦ G'.vermaMult (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
        (P.weylDot hA.isGeneralizedCartan w ξ)).sum =
        (t.map fun G' ↦ G'.vermaMult (VermaModule P lam) ξ).sum :=
      congrArg List.sum (List.map_congr_left fun G' hG' ↦
        hrest G' (List.mem_append_right _ hG') w hw ξ)
    change G.vermaMult _ _ = G.vermaMult _ _ at hG
    omega
  obtain ⟨φ, hb⟩ := F₁.exists_bijOn_of_equiv_verma Gk hlam hM₀ hI hK (E₁.symm.trans Ek)
  exact CommutesWithWeyl.of_bijOn F₁ hGkc φ hb

/-- **Projective functors commute with the Weyl group** (Bernstein–Gelfand, Thm. 3.4 (iv), the
case of §3.9 (d)): let `λ` be dominant, `I` the annihilator of `M(λ)` (with Kostant's
multiplicity statement), and `F` a projective functor on the block of `λ` with
`F(M(λ)) ≅ P(ψ)`. If `λ` dominates the linkage class of `ψ` (`λ - ξ` is dominant integral for
every `ξ` linked to `ψ` with `ξ - ψ` in the root lattice), then `F` commutes with `W_[λ]` on
Verma multiplicities. -/
theorem commutesWithWeyl_of_equiv_projectiveCover [FiniteDimensional K V]
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) {ψ : Dual K H}
    (hD : ∀ ξ, centralCharacter P ξ = centralCharacter P ψ → ξ - ψ ∈ P.rootLattice →
      P.IsDominantIntegral (lam - ξ))
    (E : ProjectiveCover P hA ψ ≃ₗ⁅K,𝔤⁆ F.vermaValue) : F.CommutesWithWeyl :=
  commutesWithWeyl_of_ncard hlam hM₀ hI hK _ ψ rfl hD V F ⟨E⟩

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
