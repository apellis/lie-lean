/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorWeyl
import LieLean.Algebra.Lie.KacMoody.TranslationAdjunction

/-!
# Projective functors and the Weyl group: additivity of Verma multiplicities

Ingredients of the induction in Bernstein–Gelfand's proof of Theorem 3.4 (iv) (§3.9 (d)): the
Verma multiplicities `(F(M) : M(ν))` of projective functors on the block of `λ` are additive over
decompositions of `F` into summands, and they only depend on `F` up to isomorphism; the Verma
multiplicities of a projective cover are given by BGG reciprocity.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.finrank_hom_range_eq_add`: for orthogonal idempotents
  `e₁`, `e - e₁` on a module with a standard filtration, `dim Hom(e(Y), M(ν)^∨)` is additive.
* `BlockProjectiveFunctor.vermaMult_eq_add`, `BlockProjectiveFunctor.vermaMult_eq_sum`.
* `BlockProjectiveFunctor.vermaMult_eq_of_bijOn`, `BlockProjectiveFunctor.CommutesWithWeyl.of_bijOn`.
* `BlockProjectiveFunctor.vermaMult_verma_eq_multiplicity`: if `F(M(λ)) ≅ P(μ)`, then
  `(F(M(λ)) : M(ν)) = [M(ν) : L(μ)]`.

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
theorem finrank_hom_range_eq_add [DecidableEq (Dual K H)] {Y : Type*} [AddCommGroup Y]
    [Module K Y] [LieRingModule 𝔤 Y] [LieModule K 𝔤 Y] (hY : IsCategoryO P Y)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 Y) s)
    {e e₁ : Y →ₗ⁅K,𝔤⁆ Y} (he : e.comp e = e) (he₁ : e₁.comp e₁ = e₁) (hee₁ : e.comp e₁ = e₁)
    (he₁e : e₁.comp e = e₁) (ν : Dual K H) :
    finrank K (e.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) =
      finrank K (e₁.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) +
        finrank K ((e - e₁).range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) := by
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
theorem finrank_hom_range_list_sum [DecidableEq (Dual K H)] {Y : Type*} [AddCommGroup Y]
    [Module K Y] [LieRingModule 𝔤 Y] [LieModule K 𝔤 Y] (hY : IsCategoryO P Y)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 Y) s) (ν : Dual K H)
    (l : List (Y →ₗ⁅K,𝔤⁆ Y)) (hl : ∀ e ∈ l, e * e = e)
    (hp : l.Pairwise fun e e' ↦ e * e' = 0 ∧ e' * e = 0) :
    finrank K (l.sum.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) =
      (l.map fun e ↦ finrank K (e.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν))).sum := by
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

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
