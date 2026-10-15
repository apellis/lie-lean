/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase

/-!
# Crystal bases of direct sums

Let `(Mᵢ)_{i ∈ ι}` be a family of integrable `U = U_q(𝔤)`-modules and `M = ⊕ᵢ Mᵢ` (modelled as
`Π₀ i, Mᵢ`). For `A`-submodules `Lᵢ ⊆ Mᵢ`, let `L = ⊕ᵢ Lᵢ = {m | ∀ i, mᵢ ∈ Lᵢ}`
(`QuantumGroup.dfinsuppLattice`); the inclusions `Lᵢ → L` induce injections
`Lᵢ / cLᵢ → L / cL` (`QuantumGroup.dfinsuppQuotIncl`), and for subsets `Bᵢ ⊆ Lᵢ / cLᵢ` we let
`B = ⊔ᵢ Bᵢ ⊆ L / cL` be the union of their images (`QuantumGroup.dfinsuppBase`).

## Main results

* `QuantumGroup.isIntegrable_dfinsupp`: direct sums of integrable modules are integrable.
* `QuantumGroup.IsCrystalBase.dfinsupp`: if each `(Lᵢ, Bᵢ)` is a crystal base of `Mᵢ`, then
  `(L, B)` is a crystal base of `M` ([HK] Thm. 4.2.10 (1)).
* `QuantumGroup.IsCrystalBase.of_dfinsupp`: conversely, if `(L, B)` is a crystal base of `M` and
  each `Lᵢ` is free, then each `(Lᵢ, Bᵢ)` is a crystal base of `Mᵢ` ([HK] Thm. 4.2.10 (2)).

Hong–Kang state (1) for two summands and for countable direct sums, and (2) for two summands; here
both are proved for families indexed by an arbitrary type. Their setting is `A = A₀` and `c = q`;
here `A` is any commutative ring and `c ∈ A`, not a unit in (1).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2.
-/

open Pointwise

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
  [∀ i, Module (QuantumGroup R v) (M i)] [∀ i, IsScalarTower k (QuantumGroup R v) (M i)]

/-! ### Integrability -/

/-- A direct sum of integrable `U`-modules is integrable. -/
theorem isIntegrable_dfinsupp (hM : ∀ i, IsIntegrable R v (M i)) :
    IsIntegrable R v (Π₀ i, M i) := by
  classical
  have nil : ∀ (X : QuantumGroup R v), (∀ i (m : M i), ∃ n : ℕ, X ^ n • m = 0) →
      ∀ m : Π₀ i, M i, ∃ n : ℕ, X ^ n • m = 0 := fun X hX m ↦ by
    induction m using DFinsupp.induction with
    | h0 => exact ⟨0, smul_zero _⟩
    | ha i b f _ _ ih =>
      obtain ⟨n₁, hn₁⟩ := hX i b
      obtain ⟨n₂, hn₂⟩ := ih
      refine ⟨n₁ + n₂, ?_⟩
      have h1 : X ^ n₁ • DFinsupp.single i b = 0 := by
        rw [← DFinsupp.lsingle_apply (R := QuantumGroup R v), ← map_smul, hn₁, map_zero]
      have e1 : X ^ (n₁ + n₂) • DFinsupp.single i b = 0 := by
        rw [add_comm, pow_add, mul_smul, h1, smul_zero]
      have e2 : X ^ (n₁ + n₂) • f = 0 := by rw [pow_add, mul_smul, hn₂, smul_zero]
      rw [smul_add, e1, e2, add_zero]
  refine ⟨eq_top_iff.2 fun m _ ↦ ?_, fun i ↦ nil _ fun j ↦ (hM j).exists_E_pow_smul_eq_zero i,
    fun i ↦ nil _ fun j ↦ (hM j).exists_F_pow_smul_eq_zero i⟩
  induction m using DFinsupp.induction with
  | h0 => exact zero_mem _
  | ha i b f _ _ ih =>
    refine add_mem ?_ (ih trivial)
    have hb : b ∈ ⨆ Λ, weightSpace R v (M i) Λ := (hM i).iSup_weightSpace_eq_top ▸ trivial
    have := Submodule.mem_map_of_mem
      (f := ((DFinsupp.lsingle (R := QuantumGroup R v) (M := M) i).restrictScalars k)) hb
    rw [Submodule.map_iSup] at this
    refine SetLike.le_def.1 (iSup_mono fun Λ ↦ ?_) this
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_weightSpace _ hx

/-! ### Lattices and their quotients -/

section Lattice

variable {A : Type*} [CommRing A] [∀ j, Module A (M j)] (L : ∀ j, Submodule A (M j))

/-- The direct sum `⊕ⱼ Lⱼ = {m | ∀ j, mⱼ ∈ Lⱼ}` of `A`-submodules `Lⱼ ⊆ Mⱼ`. -/
def dfinsuppLattice : Submodule A (Π₀ j, M j) :=
  ⨅ j, (L j).comap (DFinsupp.lapply j)

omit [DecidableEq ι] in
variable {L} in
lemma mem_dfinsuppLattice {m : Π₀ j, M j} : m ∈ dfinsuppLattice L ↔ ∀ j, m j ∈ L j := by
  simp [dfinsuppLattice]

variable {L} in
lemma single_mem_dfinsuppLattice {j : ι} {x : M j} (hx : x ∈ L j) :
    DFinsupp.single j x ∈ dfinsuppLattice L := mem_dfinsuppLattice.2 fun l ↦ by
  rw [DFinsupp.single_apply]
  split_ifs with h
  · subst h; exact hx
  · exact zero_mem _

/-- The inclusion `Lⱼ → ⊕ₗ Lₗ`. -/
def dfinsuppLatticeIncl (j : ι) : L j →ₗ[A] dfinsuppLattice L :=
  (DFinsupp.lsingle j).restrict fun _ hx ↦ single_mem_dfinsuppLattice hx

/-- The projection `⊕ₗ Lₗ → Lⱼ`. -/
def dfinsuppLatticeProj (j : ι) : dfinsuppLattice L →ₗ[A] L j :=
  (DFinsupp.lapply j).restrict fun _ hx ↦ mem_dfinsuppLattice.1 hx j

@[simp] lemma coe_dfinsuppLatticeIncl (j : ι) (x : L j) :
    (dfinsuppLatticeIncl L j x : Π₀ j, M j) = DFinsupp.single j (x : M j) := rfl

omit [DecidableEq ι] in
@[simp] lemma coe_dfinsuppLatticeProj (j : ι) (x : dfinsuppLattice L) :
    (dfinsuppLatticeProj L j x : M j) = (x : Π₀ j, M j) j := rfl

lemma dfinsuppLatticeProj_incl_self (j : ι) (x : L j) :
    dfinsuppLatticeProj L j (dfinsuppLatticeIncl L j x) = x :=
  Subtype.ext (by simp)

lemma dfinsuppLatticeProj_incl_of_ne {j l : ι} (h : j ≠ l) (x : L j) :
    dfinsuppLatticeProj L l (dfinsuppLatticeIncl L j x) = 0 :=
  Subtype.ext (by simp [DFinsupp.single_apply, h])

lemma exists_eq_sum_dfinsuppLatticeIncl (x : dfinsuppLattice L) :
    ∃ s : Finset ι, x = ∑ j ∈ s, dfinsuppLatticeIncl L j (dfinsuppLatticeProj L j x) := by
  classical
  refine ⟨(x : Π₀ j, M j).support, Subtype.ext ?_⟩
  rw [Submodule.coe_sum]
  simp only [coe_dfinsuppLatticeIncl, coe_dfinsuppLatticeProj]
  exact (x : Π₀ j, M j).sum_single.symm

lemma dfinsuppLatticeProj_lsum (l : ι) (y : Π₀ j, L j) :
    dfinsuppLatticeProj L l (DFinsupp.lsum ℕ (dfinsuppLatticeIncl L) y) = y l := by
  induction y using DFinsupp.induction with
  | h0 => simp
  | ha j b f _ _ ih =>
    rw [map_add, map_add, ih, DFinsupp.lsum_single, DFinsupp.add_apply]
    congr 1
    by_cases h : j = l
    · subst h; rw [dfinsuppLatticeProj_incl_self, DFinsupp.single_eq_same]
    · rw [dfinsuppLatticeProj_incl_of_ne L h]
      simp [DFinsupp.single_apply, h]

/-- `⊕ⱼ Lⱼ` is isomorphic to the external direct sum of the `Lⱼ`. -/
noncomputable def dfinsuppLatticeEquiv : (Π₀ j, L j) ≃ₗ[A] dfinsuppLattice L :=
  LinearEquiv.ofBijective (DFinsupp.lsum ℕ (dfinsuppLatticeIncl L)) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun y hy ↦ DFinsupp.ext fun l ↦ ?_
    rw [← dfinsuppLatticeProj_lsum, hy, map_zero, DFinsupp.zero_apply], fun x ↦ by
    obtain ⟨s, hs⟩ := exists_eq_sum_dfinsuppLatticeIncl L x
    refine ⟨∑ j ∈ s, DFinsupp.single j (dfinsuppLatticeProj L j x), ?_⟩
    rw [map_sum]
    simp only [DFinsupp.lsum_single]
    exact hs.symm⟩

variable (c : A)

lemma smul_top_le_comap {P P' : Type*} [AddCommGroup P] [Module A P] [AddCommGroup P']
    [Module A P'] (f : P →ₗ[A] P') :
    (Ideal.span {c} • ⊤ : Submodule A P) ≤ (Ideal.span {c} • ⊤ : Submodule A P').comap f := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

/-- The inclusion `Lⱼ / cLⱼ → L / cL`. -/
noncomputable def dfinsuppQuotIncl (j : ι) :
    (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j))) →ₗ[A]
      (dfinsuppLattice L ⧸ (Ideal.span {c} • ⊤ : Submodule A (dfinsuppLattice L))) :=
  Submodule.mapQ _ _ (dfinsuppLatticeIncl L j) (smul_top_le_comap c _)

/-- The projection `L / cL → Lⱼ / cLⱼ`. -/
noncomputable def dfinsuppQuotProj (j : ι) :
    (dfinsuppLattice L ⧸ (Ideal.span {c} • ⊤ : Submodule A (dfinsuppLattice L))) →ₗ[A]
      (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j))) :=
  Submodule.mapQ _ _ (dfinsuppLatticeProj L j) (smul_top_le_comap c _)

lemma dfinsuppQuotProj_incl_self (j : ι) (b) :
    dfinsuppQuotProj L c j (dfinsuppQuotIncl L c j b) = b := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  simp [dfinsuppQuotProj, dfinsuppQuotIncl, dfinsuppLatticeProj_incl_self]

lemma dfinsuppQuotProj_incl_of_ne {j l : ι} (h : j ≠ l) (b) :
    dfinsuppQuotProj L c l (dfinsuppQuotIncl L c j b) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  simp [dfinsuppQuotProj, dfinsuppQuotIncl, dfinsuppLatticeProj_incl_of_ne L h]

lemma dfinsuppQuotIncl_injective (j : ι) : Function.Injective (dfinsuppQuotIncl L c j) :=
  Function.LeftInverse.injective (dfinsuppQuotProj_incl_self L c j)

lemma mk_eq_sum_dfinsuppQuotIncl (x : dfinsuppLattice L) : ∃ s : Finset ι,
    (Submodule.Quotient.mk x : dfinsuppLattice L ⧸ (Ideal.span {c} • ⊤ : Submodule A _)) =
      ∑ j ∈ s, dfinsuppQuotIncl L c j (Submodule.Quotient.mk (dfinsuppLatticeProj L j x)) := by
  obtain ⟨s, hs⟩ := exists_eq_sum_dfinsuppLatticeIncl L x
  refine ⟨s, ?_⟩
  conv_lhs => rw [hs]
  simp only [← Submodule.mkQ_apply, map_sum]
  rfl

/-- `Lⱼ / cLⱼ → L / cL` as a map of `A / cA`-modules. -/
noncomputable def dfinsuppQuotIncl' (j : ι) :
    (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j))) →ₗ[A ⧸ Ideal.span {c}]
      (dfinsuppLattice L ⧸ (Ideal.span {c} • ⊤ : Submodule A (dfinsuppLattice L))) :=
  (dfinsuppQuotIncl L c j).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- `L / cL → Lⱼ / cLⱼ` as a map of `A / cA`-modules. -/
noncomputable def dfinsuppQuotProj' (j : ι) :
    (dfinsuppLattice L ⧸ (Ideal.span {c} • ⊤ : Submodule A (dfinsuppLattice L))) →ₗ[A ⧸ Ideal.span {c}]
      (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j))) :=
  (dfinsuppQuotProj L c j).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

@[simp] lemma dfinsuppQuotIncl'_apply (j : ι) (b) :
    dfinsuppQuotIncl' L c j b = dfinsuppQuotIncl L c j b := rfl

omit [DecidableEq ι] in
@[simp] lemma dfinsuppQuotProj'_apply (j : ι) (b) :
    dfinsuppQuotProj' L c j b = dfinsuppQuotProj L c j b := rfl

lemma linearIndependent_dfinsuppQuotIncl
    {B : ∀ j, Set (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j)))}
    (hB : ∀ j, LinearIndependent (A ⧸ Ideal.span {c}) (Subtype.val : B j → _)) :
    LinearIndependent (A ⧸ Ideal.span {c}) fun x : Σ j, B j ↦ dfinsuppQuotIncl L c x.1 x.2 := by
  classical
  rw [linearIndependent_iff']
  rintro s g hs ⟨l, b⟩ hx
  have h := congrArg (dfinsuppQuotProj' L c l) hs
  rw [map_sum, map_zero] at h
  have hG : ∀ x ∈ s, x ∉ Set.range (Sigma.mk (β := fun j ↦ B j) l) →
      dfinsuppQuotProj' L c l (g x • dfinsuppQuotIncl L c x.1 x.2) = 0 := by
    rintro ⟨j, b'⟩ - hj
    have hjl : j ≠ l := by
      rintro rfl
      exact hj ⟨b', rfl⟩
    rw [map_smul, dfinsuppQuotProj'_apply, dfinsuppQuotProj_incl_of_ne L c hjl, smul_zero]
  rw [← Finset.sum_preimage (Sigma.mk (β := fun j ↦ B j) l) s sigma_mk_injective.injOn _ hG] at h
  simp only [map_smul, dfinsuppQuotProj'_apply, dfinsuppQuotProj_incl_self] at h
  exact linearIndependent_iff'.1 (hB l) _ _ h b (Finset.mem_preimage.2 hx)

/-- The subset `⊔ⱼ Bⱼ ⊆ L / cL` for subsets `Bⱼ ⊆ Lⱼ / cLⱼ`. -/
def dfinsuppBase (B : ∀ j, Set (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j)))) :
    Set (dfinsuppLattice L ⧸ (Ideal.span {c} • ⊤ : Submodule A (dfinsuppLattice L))) :=
  ⋃ j, dfinsuppQuotIncl L c j '' B j

end Lattice

/-! ### Crystal bases -/

section Crystal

variable [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1} {hM : ∀ j, IsIntegrable R v (M j)}
  {A : Type*} [CommRing A] [Algebra A k] [∀ j, Module A (M j)] [∀ j, IsScalarTower A k (M j)]
  {L : ∀ j, Submodule A (M j)}

lemma weightSetProj_dfinsupp_apply (S : Set (Y →+ ℤ)) (m : Π₀ j, M j) (j : ι) :
    weightSetProj hv (isIntegrable_dfinsupp hM) S m j = weightSetProj hv (hM j) S (m j) :=
  map_weightSetProj hv (isIntegrable_dfinsupp hM) (hM j) (DFinsupp.lapply j) S m

lemma kashiwaraE_dfinsupp_apply (i : I) (m : Π₀ j, M j) (j : ι) :
    kashiwaraE R v (Π₀ j, M j) hv (isIntegrable_dfinsupp hM) i m j =
      kashiwaraE R v (M j) hv (hM j) i (m j) :=
  map_kashiwaraE hv (isIntegrable_dfinsupp hM) i (hM j) (DFinsupp.lapply j) m

lemma kashiwaraF_dfinsupp_apply (i : I) (m : Π₀ j, M j) (j : ι) :
    kashiwaraF R v (Π₀ j, M j) hv (isIntegrable_dfinsupp hM) i m j =
      kashiwaraF R v (M j) hv (hM j) i (m j) :=
  map_kashiwaraF hv (isIntegrable_dfinsupp hM) i (hM j) (DFinsupp.lapply j) m

omit [Algebra A k] [∀ j, IsScalarTower A k (M j)] in
/-- The direct sum of crystal lattices is a crystal lattice ([HK] Thm. 4.2.10 (1)). -/
theorem IsCrystalLattice.dfinsupp (hL : ∀ j, IsCrystalLattice hv (hM j) (L j)) :
    IsCrystalLattice hv (isIntegrable_dfinsupp hM) (dfinsuppLattice L) := by
  have := fun j ↦ (hL j).free
  refine
    { span_eq_top := eq_top_iff.2 fun m _ ↦ ?_
      free := Module.Free.of_equiv (dfinsuppLatticeEquiv L)
      weightSetProj_mem := fun S m hm ↦ mem_dfinsuppLattice.2 fun j ↦ ?_
      kashiwaraE_mem := fun i m hm ↦ mem_dfinsuppLattice.2 fun j ↦ ?_
      kashiwaraF_mem := fun i m hm ↦ mem_dfinsuppLattice.2 fun j ↦ ?_ }
  · classical
    induction m using DFinsupp.induction with
    | h0 => exact zero_mem _
    | ha j b f _ _ ih =>
      refine add_mem ?_ (ih trivial)
      have hb : b ∈ Submodule.span k (L j : Set (M j)) := (hL j).span_eq_top ▸ trivial
      have h := Submodule.mem_map_of_mem (f := DFinsupp.lsingle (R := k) (M := M) j) hb
      rw [Submodule.map_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨x, hx, rfl⟩
      exact single_mem_dfinsuppLattice hx
  · rw [weightSetProj_dfinsupp_apply]
    exact (hL j).weightSetProj_mem S _ (mem_dfinsuppLattice.1 hm j)
  · rw [kashiwaraE_dfinsupp_apply]
    exact (hL j).kashiwaraE_mem i _ (mem_dfinsuppLattice.1 hm j)
  · rw [kashiwaraF_dfinsupp_apply]
    exact (hL j).kashiwaraF_mem i _ (mem_dfinsuppLattice.1 hm j)

omit [Algebra A k] [∀ j, IsScalarTower A k (M j)] in
variable (hM) in
/-- A summand of a crystal lattice of a direct sum is a crystal lattice, if it is free
([HK] Thm. 4.2.10 (2)). -/
theorem IsCrystalLattice.of_dfinsupp
    (hLs : IsCrystalLattice hv (isIntegrable_dfinsupp hM) (dfinsuppLattice L))
    (hfree : ∀ j, Module.Free A (L j)) (j : ι) : IsCrystalLattice hv (hM j) (L j) where
  span_eq_top := by
    have h := congrArg (Submodule.map (DFinsupp.lapply (R := k) (M := M) j)) hLs.span_eq_top
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.2 fun m ↦ ⟨DFinsupp.single j m, by simp⟩] at h
    refine eq_top_iff.2 (h ▸ Submodule.span_mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact mem_dfinsuppLattice.1 hx j
  free := hfree j
  weightSetProj_mem S m hm := by
    have h := mem_dfinsuppLattice.1 (hLs.weightSetProj_mem S _ (single_mem_dfinsuppLattice hm)) j
    rwa [weightSetProj_dfinsupp_apply, DFinsupp.single_eq_same] at h
  kashiwaraE_mem i m hm := by
    have h := mem_dfinsuppLattice.1 (hLs.kashiwaraE_mem i _ (single_mem_dfinsuppLattice hm)) j
    rwa [kashiwaraE_dfinsupp_apply, DFinsupp.single_eq_same] at h
  kashiwaraF_mem i m hm := by
    have h := mem_dfinsuppLattice.1 (hLs.kashiwaraF_mem i _ (single_mem_dfinsuppLattice hm)) j
    rwa [kashiwaraF_dfinsupp_apply, DFinsupp.single_eq_same] at h

lemma IsCrystalLattice.eQ_dfinsuppQuotIncl
    (hLs : IsCrystalLattice hv (isIntegrable_dfinsupp hM) (dfinsuppLattice L))
    (hL : ∀ j, IsCrystalLattice hv (hM j) (L j)) (c : A) (i : I) (j : ι) (b) :
    hLs.eQ c i (dfinsuppQuotIncl L c j b) = dfinsuppQuotIncl L c j ((hL j).eQ c i b) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (map_kashiwaraE hv (hM j) i (isIntegrable_dfinsupp hM) (DFinsupp.lsingle j) x).symm)

lemma IsCrystalLattice.fQ_dfinsuppQuotIncl
    (hLs : IsCrystalLattice hv (isIntegrable_dfinsupp hM) (dfinsuppLattice L))
    (hL : ∀ j, IsCrystalLattice hv (hM j) (L j)) (c : A) (i : I) (j : ι) (b) :
    hLs.fQ c i (dfinsuppQuotIncl L c j b) = dfinsuppQuotIncl L c j ((hL j).fQ c i b) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (map_kashiwaraF hv (hM j) i (isIntegrable_dfinsupp hM) (DFinsupp.lsingle j) x).symm)

variable {c : A}

/-- **Hong–Kang, Thm. 4.2.10 (1).** If `(Lⱼ, Bⱼ)` is a crystal base of `Mⱼ` for every `j`, then
`(⊕ⱼ Lⱼ, ⊔ⱼ Bⱼ)` is a crystal base of `⊕ⱼ Mⱼ`. Hong–Kang state this for two and for countably
many summands, with `c = q`. -/
theorem IsCrystalBase.dfinsupp {hL : ∀ j, IsCrystalLattice hv (hM j) (L j)} (hc : ¬IsUnit c)
    {B : ∀ j, Set (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j)))}
    (hB : ∀ j, IsCrystalBase (hL j) c (B j)) :
    IsCrystalBase (IsCrystalLattice.dfinsupp hL) c (dfinsuppBase L c B) := by
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hQe := (IsCrystalLattice.dfinsupp hL).eQ_dfinsuppQuotIncl hL c
  have hQf := (IsCrystalLattice.dfinsupp hL).fQ_dfinsuppQuotIncl hL c
  have hinj := dfinsuppQuotIncl_injective L c
  -- the family `(j, b) ↦ ιⱼ b`
  have hFi := linearIndependent_dfinsuppQuotIncl L c fun j ↦ (hB j).linearIndependent
  have hrange : Set.range (fun x : Σ j, B j ↦ dfinsuppQuotIncl L c x.1 x.2) =
      dfinsuppBase L c B := by
    refine Set.ext fun b ↦ ⟨?_, fun hb ↦ ?_⟩
    · rintro ⟨⟨j, b', hb'⟩, rfl⟩
      exact Set.mem_iUnion.2 ⟨j, b', hb', rfl⟩
    · obtain ⟨j, b', hb', rfl⟩ := Set.mem_iUnion.1 hb
      exact ⟨⟨j, b', hb'⟩, rfl⟩
  refine
    { linearIndependent := ?_
      span_eq_top := eq_top_iff.2 fun b _ ↦ ?_
      exists_weight := ?_
      eQ_mem := ?_
      fQ_mem := ?_
      fQ_eq_iff := ?_ }
  · rw [← hrange]
    exact (linearIndepOn_id_range_iff hFi.injective).2 hFi
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    obtain ⟨s, hs⟩ := mk_eq_sum_dfinsuppQuotIncl L c x
    rw [hs]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have hb : Submodule.Quotient.mk (dfinsuppLatticeProj L j x) ∈
        Submodule.span (A ⧸ Ideal.span {c}) (B j) := (hB j).span_eq_top ▸ trivial
    have h := Submodule.mem_map_of_mem (f := dfinsuppQuotIncl' L c j) hb
    rw [Submodule.map_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨y, hy, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, y, hy, rfl⟩
  · intro b hb
    obtain ⟨j, b₀, hb₀, rfl⟩ := Set.mem_iUnion.1 hb
    obtain ⟨Λ, x, hx, hxb⟩ := (hB j).exists_weight b₀ hb₀
    refine ⟨Λ, dfinsuppLatticeIncl L j x, map_mem_weightSpace (DFinsupp.lsingle j) hx, ?_⟩
    rw [← hxb]
    rfl
  · intro i b hb
    obtain ⟨j, b₀, hb₀, rfl⟩ := Set.mem_iUnion.1 hb
    rw [hQe]
    rcases (hB j).eQ_mem i b₀ hb₀ with h | h
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, _, h, rfl⟩)
    · exact Or.inr (by rw [h, map_zero])
  · intro i b hb
    obtain ⟨j, b₀, hb₀, rfl⟩ := Set.mem_iUnion.1 hb
    rw [hQf]
    rcases (hB j).fQ_mem i b₀ hb₀ with h | h
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, _, h, rfl⟩)
    · exact Or.inr (by rw [h, map_zero])
  · intro i b hb b' hb'
    obtain ⟨j, b₀, hb₀, rfl⟩ := Set.mem_iUnion.1 hb
    obtain ⟨l, b₁, hb₁, rfl⟩ := Set.mem_iUnion.1 hb'
    rw [hQf, hQe]
    by_cases h : j = l
    · subst h
      rw [(hinj j).eq_iff, (hinj j).eq_iff]
      exact (hB j).fQ_eq_iff i b₀ hb₀ b₁ hb₁
    · refine iff_of_false (fun H ↦ ?_) (fun H ↦ ?_)
      · have := congrArg (dfinsuppQuotProj L c l) H
        rw [dfinsuppQuotProj_incl_of_ne L c h, dfinsuppQuotProj_incl_self] at this
        exact (hB l).zero_notMem hc (this ▸ hb₁)
      · have := congrArg (dfinsuppQuotProj L c j) H
        rw [dfinsuppQuotProj_incl_of_ne L c (Ne.symm h), dfinsuppQuotProj_incl_self] at this
        exact (hB j).zero_notMem hc (this ▸ hb₀)

variable (hM) in
/-- **Hong–Kang, Thm. 4.2.10 (2).** If `(⊕ⱼ Lⱼ, ⊔ⱼ Bⱼ)` is a crystal base of `⊕ⱼ Mⱼ` and every
`Lⱼ` is free, then each `(Lⱼ, Bⱼ)` is a crystal base of `Mⱼ`. Hong–Kang state this for two
summands, with `A = A₀` and `c = q`; over a principal ideal domain such as `A₀` the freeness of
the summands `Lⱼ` of the free module `⊕ⱼ Lⱼ` is automatic, and for general `A` it is kept as a
hypothesis. -/
theorem IsCrystalBase.of_dfinsupp
    {hLs : IsCrystalLattice hv (isIntegrable_dfinsupp hM) (dfinsuppLattice L)}
    {B : ∀ j, Set (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j)))}
    (hB : IsCrystalBase hLs c (dfinsuppBase L c B)) (hfree : ∀ j, Module.Free A (L j)) (j : ι) :
    IsCrystalBase (hLs.of_dfinsupp hM hfree j) c (B j) := by
  have hQe := hLs.eQ_dfinsuppQuotIncl (hLs.of_dfinsupp hM hfree) c
  have hQf := hLs.fQ_dfinsuppQuotIncl (hLs.of_dfinsupp hM hfree) c
  have hinj := dfinsuppQuotIncl_injective L c j
  have hmem : ∀ b ∈ B j, dfinsuppQuotIncl L c j b ∈ dfinsuppBase L c B :=
    fun b hb ↦ Set.mem_iUnion.2 ⟨j, b, hb, rfl⟩
  have hback : ∀ y, dfinsuppQuotIncl L c j y ∈ dfinsuppBase L c B → y ∈ B j ∨ y = 0 := by
    intro y hy
    obtain ⟨l, b, hb, he⟩ := Set.mem_iUnion.1 hy
    by_cases h : l = j
    · subst h
      exact Or.inl (hinj he ▸ hb)
    · have := congrArg (dfinsuppQuotProj L c j) he
      rw [dfinsuppQuotProj_incl_of_ne L c h, dfinsuppQuotProj_incl_self] at this
      exact Or.inr this.symm
  refine
    { linearIndependent := ?_
      span_eq_top := eq_top_iff.2 fun b _ ↦ ?_
      exists_weight := fun b hb ↦ ?_
      eQ_mem := fun i b hb ↦ ?_
      fQ_mem := fun i b hb ↦ ?_
      fQ_eq_iff := fun i b hb b' hb' ↦ ?_ }
  · have := hB.linearIndependent.comp (fun b : B j ↦ ⟨_, hmem b b.2⟩)
      fun b₁ b₂ h ↦ Subtype.ext (hinj (congrArg Subtype.val h))
    exact this.of_comp (dfinsuppQuotIncl' L c j)
  · have h1 : dfinsuppQuotIncl L c j b ∈ Submodule.span (A ⧸ Ideal.span {c})
        (dfinsuppBase L c B) := hB.span_eq_top ▸ trivial
    have h2 := Submodule.mem_map_of_mem (f := dfinsuppQuotProj' L c j) h1
    rw [Submodule.map_span, dfinsuppQuotProj'_apply,
      dfinsuppQuotProj_incl_self] at h2
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨l, b', hb', rfl⟩ := Set.mem_iUnion.1 hy
    rw [dfinsuppQuotProj'_apply]
    by_cases h : l = j
    · subst h
      rw [dfinsuppQuotProj_incl_self]
      exact Submodule.subset_span hb'
    · rw [dfinsuppQuotProj_incl_of_ne L c h]
      exact zero_mem _
  · obtain ⟨Λ, x, hx, hxb⟩ := hB.exists_weight _ (hmem b hb)
    refine ⟨Λ, dfinsuppLatticeProj L j x, map_mem_weightSpace (DFinsupp.lapply j) hx, ?_⟩
    have := congrArg (dfinsuppQuotProj L c j) hxb
    rwa [dfinsuppQuotProj_incl_self] at this
  · rcases hB.eQ_mem i _ (hmem b hb) with h | h
    · rw [hQe] at h
      exact hback _ h
    · rw [hQe] at h
      exact Or.inr (hinj (by rw [h, map_zero]))
  · rcases hB.fQ_mem i _ (hmem b hb) with h | h
    · rw [hQf] at h
      exact hback _ h
    · rw [hQf] at h
      exact Or.inr (hinj (by rw [h, map_zero]))
  · rw [← hinj.eq_iff, ← hQf, ← hinj.eq_iff, ← hQe]
    exact hB.fQ_eq_iff i _ (hmem b hb) _ (hmem b' hb')

end Crystal

end LieLean.QuantumGroup
