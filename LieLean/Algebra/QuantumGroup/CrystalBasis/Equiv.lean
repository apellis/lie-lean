/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase
import LieLean.Algebra.QuantumGroup.CrystalBasis.Transfer

/-!
# Transport of crystal bases along isomorphisms of `U`-modules

Let `ψ : M ≃ M'` be an isomorphism of integrable `U = U_q(𝔤)`-modules. Since `ψ` commutes with the
projections onto weight spaces and with the Kashiwara operators, it carries a crystal base
`(L, B)` of `M` to the crystal base `(ψ(L), ψ̄(B))` of `M'`, where `ψ̄ : L / cL ≃ ψ(L) / cψ(L)` is
the isomorphism induced by `ψ` ([HK] Prop. 4.2.8).

## Main results

* `QuantumGroup.IsCrystalLattice.of_equiv`: `ψ(L)` is a crystal lattice of `M'`.
* `QuantumGroup.IsCrystalBase.of_equiv`: `(ψ(L), ψ̄(B))` is a crystal base of `M'`
  ([HK] Prop. 4.2.8).

Here `ψ(L)` and `ψ̄(B)` are described by membership: `L'` is any `A`-submodule of `M'` with
`m ∈ L ↔ ψ m ∈ L'`, and `B'` any subset of `L' / cL'` with `b ∈ B ↔ ψ̄ b ∈ B'`.

Hong–Kang state this for `A = A₀` the rational functions regular at `q = 0` and `c = q`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2.
-/

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]
  {M' : Type*} [AddCommGroup M'] [Module k M'] [Module (QuantumGroup R v) M']
  [IsScalarTower k (QuantumGroup R v) M']
  [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1} {hM : IsIntegrable R v M}
  (hM' : IsIntegrable R v M')
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  [Module A M'] [IsScalarTower A k M']
  (ψ : M ≃ₗ[QuantumGroup R v] M')

/-- The image of a crystal lattice under an isomorphism of integrable `U`-modules is a crystal
lattice ([HK] Prop. 4.2.8). -/
theorem IsCrystalLattice.of_equiv {L : Submodule A M} (hL : IsCrystalLattice hv hM L)
    {L' : Submodule A M'} (hLL' : ∀ m, m ∈ L ↔ ψ m ∈ L') :
    IsCrystalLattice hv hM' L' := by
  have hL' : ∀ m', m' ∈ L' ↔ ψ.symm m' ∈ L := fun m' ↦ by rw [hLL', ψ.apply_symm_apply]
  have := hL.free
  refine
    { span_eq_top := ?_
      free := Module.Free.of_equiv (IntegrableSl2.latticeEquiv (ψ.restrictScalars k) hLL')
      weightSetProj_mem := fun S m hm ↦ ?_
      kashiwaraE_mem := fun i m hm ↦ ?_
      kashiwaraF_mem := fun i m hm ↦ ?_ }
  · have h := congrArg (Submodule.map (ψ.restrictScalars k).toLinearMap) hL.span_eq_top
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    rw [← h]
    congr 1
    ext m'
    simp only [Set.mem_image, SetLike.mem_coe, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply]
    exact ⟨fun hm ↦ ⟨ψ.symm m', (hL' m').1 hm, ψ.apply_symm_apply m'⟩,
      fun ⟨m, hm, he⟩ ↦ he ▸ (hLL' m).1 hm⟩
  · rw [hL', ← LinearEquiv.coe_toLinearMap, map_weightSetProj hv hM' hM]
    exact hL.weightSetProj_mem S _ ((hL' m).1 hm)
  · rw [hL', ← LinearEquiv.coe_toLinearMap, map_kashiwaraE hv hM' i hM]
    exact hL.kashiwaraE_mem i _ ((hL' m).1 hm)
  · rw [hL', ← LinearEquiv.coe_toLinearMap, map_kashiwaraF hv hM' i hM]
    exact hL.kashiwaraF_mem i _ ((hL' m).1 hm)

/-- **Hong–Kang, Prop. 4.2.8.** An isomorphism `ψ : M ≃ M'` of integrable `U`-modules carries a
crystal base `(L, B)` of `M` to the crystal base `(ψ(L), ψ̄(B))` of `M'`, where
`ψ̄ : L / cL ≃ ψ(L) / cψ(L)` is induced by `ψ`. Here `L'` is `ψ(L)` and `B'` is `ψ̄(B)`, described
by membership. -/
theorem IsCrystalBase.of_equiv {L : Submodule A M} {hL : IsCrystalLattice hv hM L} {c : A}
    {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))} (hB : IsCrystalBase hL c B)
    {L' : Submodule A M'} (hLL' : ∀ m, m ∈ L ↔ ψ m ∈ L')
    {B' : Set (L' ⧸ (Ideal.span {c} • ⊤ : Submodule A L'))}
    (hBB' : ∀ b, b ∈ B ↔ IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b ∈ B') :
    IsCrystalBase (hL.of_equiv hM' ψ hLL') c B' := by
  set Q := IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c
  have hB' : ∀ b', b' ∈ B' ↔ Q.symm b' ∈ B := fun b' ↦ by rw [hBB', Q.apply_symm_apply]
  have hQe : ∀ i b, Q (hL.eQ c i b) = (hL.of_equiv hM' ψ hLL').eQ c i (Q b) := fun i b ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact map_kashiwaraE hv hM i hM' ψ.toLinearMap x
  have hQf : ∀ i b, Q (hL.fQ c i b) = (hL.of_equiv hM' ψ hLL').fQ c i (Q b) := fun i b ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact map_kashiwaraF hv hM i hM' ψ.toLinearMap x
  have hQB : IntegrableSl2.quotEquiv' (ψ.restrictScalars k) hLL' c '' B = B' := by
    ext b'
    rw [hB', LinearEquiv.image_eq_preimage_symm, Set.mem_preimage]
    rfl
  refine
    { linearIndependent := ?_
      span_eq_top := ?_
      exists_weight := ?_
      eQ_mem := ?_
      fQ_mem := ?_
      fQ_eq_iff := ?_ }
  · rw [← hQB]
    have := hB.linearIndependent.map'
      (IntegrableSl2.quotEquiv' (ψ.restrictScalars k) hLL' c).toLinearMap (LinearEquiv.ker _)
    refine (linearIndependent_equiv'
      ((IntegrableSl2.quotEquiv' (ψ.restrictScalars k) hLL' c).toEquiv.image B) ?_).1 this
    ext b
    rfl
  · rw [← hQB]
    have h := Submodule.span_image (R := A ⧸ Ideal.span {c})
      (IntegrableSl2.quotEquiv' (ψ.restrictScalars k) hLL' c).toLinearMap (s := B)
    rw [LinearEquiv.coe_coe] at h
    rw [h, hB.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · intro b' hb'
    obtain ⟨Λ, x, hx, hxb⟩ := hB.exists_weight _ ((hB' b').1 hb')
    refine ⟨Λ, ⟨ψ x, (hLL' x).1 x.2⟩, map_mem_weightSpace ψ.toLinearMap hx, ?_⟩
    rw [← Q.apply_symm_apply b', ← hxb]
    rfl
  · intro i b' hb'
    rcases hB.eQ_mem i _ ((hB' b').1 hb') with h | h
    · refine Or.inl ((hB' _).2 ?_)
      rwa [← Q.apply_symm_apply b', ← hQe, Q.symm_apply_apply]
    · refine Or.inr ?_
      rw [← Q.apply_symm_apply b', ← hQe, h, map_zero]
  · intro i b' hb'
    rcases hB.fQ_mem i _ ((hB' b').1 hb') with h | h
    · refine Or.inl ((hB' _).2 ?_)
      rwa [← Q.apply_symm_apply b', ← hQf, Q.symm_apply_apply]
    · refine Or.inr ?_
      rw [← Q.apply_symm_apply b', ← hQf, h, map_zero]
  · intro i b₁ hb₁ b₂ hb₂
    rw [← Q.apply_symm_apply b₁, ← Q.apply_symm_apply b₂, ← hQf, ← hQe, Q.injective.eq_iff,
      Q.injective.eq_iff]
    exact hB.fQ_eq_iff i _ ((hB' b₁).1 hb₁) _ ((hB' b₂).1 hb₂)

end LieLean.QuantumGroup
