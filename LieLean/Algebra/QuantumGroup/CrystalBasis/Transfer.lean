/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Sl2

/-!
# Transport of crystal bases of `U_q(𝔰𝔩₂)`-modules

Crystal bases (`QuantumGroup.IntegrableSl2.IsCrystalBase`) only depend on the gradings and the
Kashiwara operators. If a linear equivalence `φ : M ≃ M'` matches the gradings and the Kashiwara
operators of `V : IntegrableSl2 q M` and `V' : IntegrableSl2 q' M'` (the parameters may differ,
e.g. `q' = q⁻¹`), then `φ` carries crystal bases of `M'` to crystal bases of `M`
(`QuantumGroup.IntegrableSl2.IsCrystalBase.of_equiv`).
-/

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q q' : k} {M M' : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup M'] [Module k M']
  {V : IntegrableSl2 q M} {V' : IntegrableSl2 q' M'}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  [Module A M'] [IsScalarTower A k M']
  (φ : M ≃ₗ[k] M')

omit [Algebra A k] [Module A M] [IsScalarTower A k M] [Module A M'] [IsScalarTower A k M'] in
/-- A linear map preserving the gradings commutes with the projections onto graded pieces. -/
lemma map_wtProj (hwt : ∀ n m, m ∈ V.wt n → φ m ∈ V'.wt n) (n : ℤ) (m : M) :
    φ (V.wtProj n m) = V'.wtProj n (φ m) := by
  have := V.ext_wt (f := φ.toLinearMap ∘ₗ V.wtProj n) (g := V'.wtProj n ∘ₗ φ.toLinearMap)
    fun n' m hm ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wtProj_of_mem hm,
        wtProj_of_mem (hwt n' m hm)]
      split_ifs <;> simp
  exact LinearMap.congr_fun this m

omit [Algebra A k] [Module A M] [IsScalarTower A k M] [Module A M'] [IsScalarTower A k M'] in
lemma wtProj_mem_wt (n : ℤ) (m : M) : V.wtProj n m ∈ V.wt n := by
  simp only [wtProj, LinearMap.comp_apply]
  exact Submodule.coe_mem _

omit [Algebra A k] [Module A M] [IsScalarTower A k M] [Module A M'] [IsScalarTower A k M'] in
/-- A linear equivalence mapping graded pieces into graded pieces matches the gradings. -/
lemma mem_wt_iff_of_equiv (hwt : ∀ n m, m ∈ V.wt n → φ m ∈ V'.wt n) (n : ℤ) (m : M) :
    m ∈ V.wt n ↔ φ m ∈ V'.wt n := by
  refine ⟨hwt n m, fun h ↦ ?_⟩
  have h1 : V'.wtProj n (φ m) = φ m := by simp [wtProj_of_mem h]
  rw [← map_wtProj φ hwt] at h1
  rw [← φ.injective h1]
  exact wtProj_mem_wt n m

variable {L : Submodule A M} {L' : Submodule A M'} (hL : ∀ m, m ∈ L ↔ φ m ∈ L')

/-- The restriction `L ≃ L'` of `φ`. -/
noncomputable def latticeEquiv : L ≃ₗ[A] L' where
  toFun x := ⟨φ x, (hL x).1 x.2⟩
  invFun y := ⟨φ.symm y, (hL _).2 (by simp)⟩
  map_add' x y := Subtype.ext (map_add φ _ _)
  map_smul' a x := Subtype.ext (by
    simp only [SetLike.val_smul, RingHom.id_apply]
    rw [← algebraMap_smul k a (x : M), map_smul, algebraMap_smul])
  left_inv x := Subtype.ext (φ.symm_apply_apply x)
  right_inv y := Subtype.ext (φ.apply_symm_apply y)

/-- The induced isomorphism `L / cL ≃ L' / cL'`. -/
noncomputable def quotEquiv (c : A) :
    (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) ≃ₗ[A] (L' ⧸ (Ideal.span {c} • ⊤ : Submodule A L')) :=
  Submodule.Quotient.equiv _ _ (latticeEquiv φ hL) (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])

lemma quotEquiv_mk (c : A) (x : L) :
    quotEquiv φ hL c (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨φ x, (hL x).1 x.2⟩ := rfl

/-- `quotEquiv` is linear over `A / cA`. -/
noncomputable def quotEquiv' (c : A) :
    (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) ≃ₗ[A ⧸ Ideal.span {c}]
      (L' ⧸ (Ideal.span {c} • ⊤ : Submodule A L')) where
  __ := quotEquiv φ hL c
  map_smul' r x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change quotEquiv φ hL c (_ • _) = _ • quotEquiv φ hL c _
    rw [Module.Quotient.mk_smul_mk, RingHom.id_apply, quotEquiv_mk, quotEquiv_mk,
      Module.Quotient.mk_smul_mk]
    congr 1
    exact Subtype.ext (by
      simp only [SetLike.val_smul]
      rw [← algebraMap_smul k a (x : M), map_smul, algebraMap_smul])

/-- `quotEquiv` intertwines `ẽ` on `L / cL` and `L' / cL'`. -/
lemma quotEquiv_eTildeQ {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
    {hq0' : q' ≠ 0} {hq' : ∀ n : ℕ, 0 < n → q' ^ n ≠ 1}
    (he : ∀ m, φ (V.eTilde hq0 hq m) = V'.eTilde hq0' hq' (φ m))
    (hLe : ∀ m ∈ L, V.eTilde hq0 hq m ∈ L) (hLe' : ∀ m ∈ L', V'.eTilde hq0' hq' m ∈ L') (c : A)
    (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :
    quotEquiv φ hL c (V.eTildeQ hq0 hq hLe c b) =
      V'.eTildeQ hq0' hq' hLe' c (quotEquiv φ hL c b) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [eTildeQ_mk, quotEquiv_mk, quotEquiv_mk, eTildeQ_mk]
  congr 1
  exact Subtype.ext (he x)

/-- `quotEquiv` intertwines `f̃` on `L / cL` and `L' / cL'`. -/
lemma quotEquiv_fTildeQ {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
    {hq0' : q' ≠ 0} {hq' : ∀ n : ℕ, 0 < n → q' ^ n ≠ 1}
    (hf : ∀ m, φ (V.fTilde hq0 hq m) = V'.fTilde hq0' hq' (φ m))
    (hLf : ∀ m ∈ L, V.fTilde hq0 hq m ∈ L) (hLf' : ∀ m ∈ L', V'.fTilde hq0' hq' m ∈ L') (c : A)
    (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :
    quotEquiv φ hL c (V.fTildeQ hq0 hq hLf c b) =
      V'.fTildeQ hq0' hq' hLf' c (quotEquiv φ hL c b) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [fTildeQ_mk, quotEquiv_mk, quotEquiv_mk, fTildeQ_mk]
  congr 1
  exact Subtype.ext (hf x)

variable {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {hq0' : q' ≠ 0} {hq' : ∀ n : ℕ, 0 < n → q' ^ n ≠ 1}

/-- Crystal bases are transported along linear equivalences matching the gradings and the
Kashiwara operators. -/
theorem IsCrystalBase.of_equiv {c : A} {B' : Set (L' ⧸ (Ideal.span {c} • ⊤ : Submodule A L'))}
    (hB' : V'.IsCrystalBase hq0' hq' L' c B') (hwt : ∀ n m, m ∈ V.wt n ↔ φ m ∈ V'.wt n)
    (he : ∀ m, φ (V.eTilde hq0 hq m) = V'.eTilde hq0' hq' (φ m))
    (hf : ∀ m, φ (V.fTilde hq0 hq m) = V'.fTilde hq0' hq' (φ m))
    {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}
    (hB : ∀ b, b ∈ B ↔ quotEquiv φ hL c b ∈ B') :
    V.IsCrystalBase hq0 hq L c B := by
  have hL' : ∀ m', m' ∈ L' ↔ φ.symm m' ∈ L := fun m' ↦ by rw [hL, φ.apply_symm_apply]
  have hst : V.IsKashiwaraStable hq0 hq L :=
    { wtProj_mem := fun m hm n ↦ by
        rw [hL, map_wtProj φ (fun n m ↦ (hwt n m).1)]
        exact hB'.isKashiwaraStable.wtProj_mem _ ((hL m).1 hm) n
      eTilde_mem := fun m hm ↦ by
        rw [hL, he]; exact hB'.isKashiwaraStable.eTilde_mem _ ((hL m).1 hm)
      fTilde_mem := fun m hm ↦ by
        rw [hL, hf]; exact hB'.isKashiwaraStable.fTilde_mem _ ((hL m).1 hm) }
  have hQe : ∀ b, quotEquiv φ hL c (V.eTildeQ hq0 hq hst.eTilde_mem c b) =
      V'.eTildeQ hq0' hq' hB'.isKashiwaraStable.eTilde_mem c (quotEquiv φ hL c b) := fun b ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [eTildeQ_mk, quotEquiv_mk, quotEquiv_mk, eTildeQ_mk]
    congr 1
    exact Subtype.ext (he x)
  have hQf : ∀ b, quotEquiv φ hL c (V.fTildeQ hq0 hq hst.fTilde_mem c b) =
      V'.fTildeQ hq0' hq' hB'.isKashiwaraStable.fTilde_mem c (quotEquiv φ hL c b) := fun b ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [fTildeQ_mk, quotEquiv_mk, quotEquiv_mk, fTildeQ_mk]
    congr 1
    exact Subtype.ext (hf x)
  have hBB' : (quotEquiv' φ hL c).symm '' B' = B := by
    ext b
    rw [hB, LinearEquiv.image_symm_eq_preimage, Set.mem_preimage]
    rfl
  have := hB'.free
  refine
    { isKashiwaraStable := hst
      span_eq_top := ?_
      free := Module.Free.of_equiv (latticeEquiv φ hL).symm
      linearIndependent := ?_
      span_quot_eq_top := ?_
      exists_wt := ?_
      eQ_mem := ?_
      fQ_mem := ?_
      fQ_eq_iff := ?_ }
  · have h := congrArg (Submodule.map φ.symm.toLinearMap) hB'.span_eq_top
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    rw [← h]
    congr 1
    ext m
    simp only [Set.mem_image, SetLike.mem_coe, LinearEquiv.coe_coe]
    exact ⟨fun hm ↦ ⟨φ m, (hL m).1 hm, φ.symm_apply_apply m⟩,
      fun ⟨m', hm', he⟩ ↦ he ▸ (hL' m').1 hm'⟩
  · rw [← hBB']
    have := hB'.linearIndependent.map' (quotEquiv' φ hL c).symm.toLinearMap
      (LinearEquiv.ker _)
    refine (linearIndependent_equiv' ((quotEquiv' φ hL c).symm.toEquiv.image B') ?_).1 this
    ext b
    rfl
  · rw [← hBB']
    have h := Submodule.span_image (R := A ⧸ Ideal.span {c})
      (quotEquiv' φ hL c).symm.toLinearMap (s := B')
    rw [LinearEquiv.coe_coe] at h
    rw [h, hB'.span_quot_eq_top, Submodule.map_top, LinearEquiv.range]
  · intro b hb
    obtain ⟨n, x', hx', hxb⟩ := hB'.exists_wt _ ((hB b).1 hb)
    refine ⟨n, (latticeEquiv φ hL).symm x', (hwt n _).2 (by simpa [latticeEquiv] using hx'), ?_⟩
    apply (quotEquiv φ hL c).injective
    rw [← hxb, quotEquiv_mk]
    congr 1
    exact Subtype.ext (φ.apply_symm_apply _)
  · intro b hb
    rcases hB'.eQ_mem _ ((hB b).1 hb) with h | h
    · exact Or.inl ((hB _).2 (by rwa [hQe]))
    · exact Or.inr ((quotEquiv φ hL c).injective (by rw [hQe, h, map_zero]))
  · intro b hb
    rcases hB'.fQ_mem _ ((hB b).1 hb) with h | h
    · exact Or.inl ((hB _).2 (by rwa [hQf]))
    · exact Or.inr ((quotEquiv φ hL c).injective (by rw [hQf, h, map_zero]))
  · intro b hb b' hb'
    rw [← (quotEquiv φ hL c).injective.eq_iff, hQf, ← (quotEquiv φ hL c).injective.eq_iff, hQe]
    exact hB'.fQ_eq_iff _ ((hB b).1 hb) _ ((hB b').1 hb')

end IntegrableSl2

end LieLean.QuantumGroup
