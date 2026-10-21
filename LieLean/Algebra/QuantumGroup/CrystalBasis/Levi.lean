/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase
import LieLean.Algebra.QuantumGroup.Levi

/-!
# Restriction of crystal bases to Levi subalgebras

Let `e : J ↪ I` and let `M` be an integrable `U(R)`-module. The Kashiwara operators of the
restriction `LeviRestrict R v e M` to `U(R.comap e)` at `j ∈ J` are those of `M` at `e j`
(`QuantumGroup.kashiwaraE_leviRestrict`, `QuantumGroup.kashiwaraF_leviRestrict`). Hence a crystal
base `(L, B)` of `M` is a crystal base of the restriction ([Kas] §4.6:
`QuantumGroup.IsCrystalLattice.leviRestrict`, `QuantumGroup.IsCrystalBase.leviRestrict`), with
`ẽⱼ`, `f̃ⱼ` on `L / cL` equal to `ẽ_{e j}`, `f̃_{e j}`
(`QuantumGroup.IsCrystalLattice.eQ_leviRestrict`, `QuantumGroup.IsCrystalLattice.fQ_leviRestrict`).

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §4.6.
-/

noncomputable section

open LieLean

namespace LieLean.QuantumGroup

section Congr

variable {k : Type*} [Field k] {q : k} {N : Type*} [AddCommGroup N] [Module k N]
  {V W : IntegrableSl2 q N} (h : V = W) (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {A : Type*} [CommRing A] [Algebra A k] [Module A N] [IsScalarTower A k N] {L : Submodule A N}

include h

lemma IntegrableSl2.eTildeQ_congr (hV : ∀ m ∈ L, V.eTilde hq0 hq m ∈ L)
    (hW : ∀ m ∈ L, W.eTilde hq0 hq m ∈ L) (c : A) :
    V.eTildeQ hq0 hq hV c = W.eTildeQ hq0 hq hW c := by
  subst h
  rfl

lemma IntegrableSl2.fTildeQ_congr (hV : ∀ m ∈ L, V.fTilde hq0 hq m ∈ L)
    (hW : ∀ m ∈ L, W.fTilde hq0 hq m ∈ L) (c : A) :
    V.fTildeQ hq0 hq hV c = W.fTildeQ hq0 hq hW c := by
  subst h
  rfl

end Congr

variable {k I J Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] [DecidableEq J]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {e : J ↪ I}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]
  [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M)

/-- The projections onto sums of weight spaces of the restriction are those of `M`. -/
theorem weightSetProj_leviRestrict (S : Set (Y →+ ℤ)) (m : LeviRestrict R v e M) :
    weightSetProj hv hM.leviRestrict S m = (weightSetProj hv hM S (m : M) : M) := by
  have h := ext_weightSpace hM (f := (weightSetProj hv hM.leviRestrict S :
      Module.End k (LeviRestrict R v e M)) ∘ₗ (LeviRestrict.of R v e M).toLinearMap)
    (g := (LeviRestrict.of R v e M).toLinearMap ∘ₗ weightSetProj hv hM S) fun Λ x hx ↦ by
      have hx' : LeviRestrict.of R v e M x ∈
          weightSpace (R.comap e) v (LeviRestrict R v e M) Λ := by
        rw [weightSpace_leviRestrict]
        exact hx
      classical
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [weightSetProj_of_mem hv _ S hx', weightSetProj_of_mem hv hM S hx]
      split_ifs <;> rfl
  exact LinearMap.congr_fun h m

/-- `ẽⱼ` on the restriction is `ẽ_{e j}` on `M`. -/
theorem kashiwaraE_leviRestrict (j : J) (m : LeviRestrict R v e M) :
    kashiwaraE (R.comap e) v (LeviRestrict R v e M) hv hM.leviRestrict j m =
      (kashiwaraE R v M hv hM (e j) (m : M) : M) :=
  LinearMap.congr_fun (congrArg (fun V : IntegrableSl2 (v ^ D.d (e j)) M ↦
    V.eTilde (pow_d_ne_zero (e j)) (pow_d_ne_one hv (e j)))
      (nodeSl2_leviRestrict hv hM j)) m

/-- `f̃ⱼ` on the restriction is `f̃_{e j}` on `M`. -/
theorem kashiwaraF_leviRestrict (j : J) (m : LeviRestrict R v e M) :
    kashiwaraF (R.comap e) v (LeviRestrict R v e M) hv hM.leviRestrict j m =
      (kashiwaraF R v M hv hM (e j) (m : M) : M) :=
  LinearMap.congr_fun (congrArg (fun V : IntegrableSl2 (v ^ D.d (e j)) M ↦
    V.fTilde (pow_d_ne_zero (e j)) (pow_d_ne_one hv (e j)))
      (nodeSl2_leviRestrict hv hM j)) m

variable {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M} {hv hM}

instance instIsScalarTowerLeviRestrict : IsScalarTower A k (LeviRestrict R v e M) :=
  inferInstanceAs (IsScalarTower A k M)

omit [Algebra A k] [IsScalarTower A k M] in
/-- A crystal lattice of `M` is a crystal lattice of its restriction ([Kas] §4.6). -/
theorem IsCrystalLattice.leviRestrict (hL : IsCrystalLattice hv hM L) :
    IsCrystalLattice (M := LeviRestrict R v e M) hv hM.leviRestrict
      (L : Submodule A (LeviRestrict R v e M)) where
  span_eq_top := hL.span_eq_top
  free := hL.free
  weightSetProj_mem S m hm := by
    rw [weightSetProj_leviRestrict]
    exact hL.weightSetProj_mem S m hm
  kashiwaraE_mem j m hm := by
    rw [kashiwaraE_leviRestrict]
    exact hL.kashiwaraE_mem (e j) m hm
  kashiwaraF_mem j m hm := by
    rw [kashiwaraF_leviRestrict]
    exact hL.kashiwaraF_mem (e j) m hm

/-- `ẽⱼ` on `L / cL` for the restriction is `ẽ_{e j}`. -/
lemma IsCrystalLattice.eQ_leviRestrict (hL : IsCrystalLattice hv hM L) (c : A) (j : J) :
    (hL.leviRestrict (e := e)).eQ c j = hL.eQ c (e j) :=
  IntegrableSl2.eTildeQ_congr (nodeSl2_leviRestrict hv hM j) _ _ _ _ c

/-- `f̃ⱼ` on `L / cL` for the restriction is `f̃_{e j}`. -/
lemma IsCrystalLattice.fQ_leviRestrict (hL : IsCrystalLattice hv hM L) (c : A) (j : J) :
    (hL.leviRestrict (e := e)).fQ c j = hL.fQ c (e j) :=
  IntegrableSl2.fTildeQ_congr (nodeSl2_leviRestrict hv hM j) _ _ _ _ c

/-- **[Kas] §4.6**: a crystal base of an integrable `U(R)`-module is a crystal base of its
restriction to the Levi subalgebra `U(R.comap e)`. -/
theorem IsCrystalBase.leviRestrict {hL : IsCrystalLattice hv hM L} {c : A}
    {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))} (hB : IsCrystalBase hL c B) :
    IsCrystalBase (hL.leviRestrict (e := e)) c B where
  linearIndependent := hB.linearIndependent
  span_eq_top := hB.span_eq_top
  exists_weight b hb := by
    obtain ⟨Λ, x, hx, hxb⟩ := hB.exists_weight b hb
    exact ⟨Λ, x, by rw [weightSpace_leviRestrict]; exact hx, hxb⟩
  eQ_mem j b hb := by
    rw [hL.eQ_leviRestrict]
    exact hB.eQ_mem (e j) b hb
  fQ_mem j b hb := by
    rw [hL.fQ_leviRestrict]
    exact hB.fQ_mem (e j) b hb
  fQ_eq_iff j b hb b' hb' := by
    rw [hL.eQ_leviRestrict, hL.fQ_leviRestrict]
    exact hB.fQ_eq_iff (e j) b hb b' hb'

end LieLean.QuantumGroup
