/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.ChevalleyEilenberg
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The Chevalley–Eilenberg chain complex and Lie algebra homology

Let `L` be a Lie algebra over a commutative ring `R` and `M` a Lie module. The differential `d`
on `⋀L ⊗ M` (`LieModule.ChevalleyEilenberg.diff`) lowers degrees by one, so it restricts to
differentials `d_k : C_{k+1}(L, M) → C_k(L, M)` on the chains `C_k(L, M) = ⋀ᵏ L ⊗ M`, with
`d_k ∘ d_{k+1} = 0`. The Lie algebra homology is `H_k(L, M) = ker d_{k-1} / im d_k` (with
`d_{-1} = 0`).

To identify `C_k(L, M)` with a direct summand of `⋀L ⊗ M` we use the projection `⋀L → ⋀ᵏL`
onto the degree `k` part (`LieModule.ChevalleyEilenberg.degProj`). Mathlib provides it through
`ExteriorAlgebra.gradedAlgebra`; we construct it directly by a fold over the exterior algebra,
which keeps the imports light.

## Main definitions

* `LieModule.ChevalleyEilenberg.degProj`: the projection `⋀L → ⋀ᵏL`.
* `LieModule.ChevalleyEilenberg.d`: the differential `d_k : ⋀^{k+1}L ⊗ M → ⋀ᵏL ⊗ M`.
* `LieModule.ChevalleyEilenberg.cycles`, `boundaries`, `homology`: `Z_k`, `B_k` and
  `H_k(L, M) = Z_k / B_k`.
* `LieModule.ChevalleyEilenberg.mapChains`, `homologyMap`: functoriality in `M`.

## Main results

* `LieModule.ChevalleyEilenberg.d_comp_d`: `d_k ∘ d_{k+1} = 0`.
* `LieModule.ChevalleyEilenberg.incl_d`: `d_k` is the restriction of `d`.
* `LieModule.ChevalleyEilenberg.mapChains_d`: naturality of `d_k` in `M`.

## References

* C. A. Weibel, *An introduction to homological algebra*, CUP 1994, §7.7 (check).
-/

open TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

/-! ### The degree projections of the exterior algebra -/

section DegProj

variable (R L : Type*) [CommRing R] [AddCommGroup L] [Module R L]

/-- The recursion step for `gradeFun`: `(y, ω, g) ↦ (k ↦ y ∧ g (k - 1))` (and `0` for `k = 0`). -/
def gradeStep :
    L →ₗ[R] ExteriorAlgebra R L × (ℕ → ExteriorAlgebra R L) →ₗ[R] (ℕ → ExteriorAlgebra R L) :=
  LinearMap.mk₂ R (fun y p k ↦ if k = 0 then 0 else ι R y * p.2 (k - 1))
    (fun y y' p ↦ by funext k; by_cases hk : k = 0 <;> simp [hk, add_mul])
    (fun r y p ↦ by funext k; by_cases hk : k = 0 <;> simp [hk])
    (fun y p p' ↦ by funext k; by_cases hk : k = 0 <;> simp [hk, mul_add])
    (fun r y p ↦ by funext k; by_cases hk : k = 0 <;> simp [hk])

variable {R L} in
lemma gradeStep_apply (y : L) (p : ExteriorAlgebra R L × (ℕ → ExteriorAlgebra R L)) (k : ℕ) :
    gradeStep R L y p k = if k = 0 then 0 else ι R y * p.2 (k - 1) := rfl

variable {R L} in
lemma gradeStep_step (y : L) (ω : ExteriorAlgebra R L) (g : ℕ → ExteriorAlgebra R L) :
    gradeStep R L y (ι R y * ω, gradeStep R L y (ω, g)) = (0 : QuadraticForm R L) y • g := by
  ext k
  simp only [gradeStep_apply]
  split_ifs <;> simp [← mul_assoc]

/-- The family `(ω_k)_k` of homogeneous components of `ω ∈ ⋀L`. -/
def gradeFun : ExteriorAlgebra R L →ₗ[R] (ℕ → ExteriorAlgebra R L) :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (gradeStep R L)
    (fun y ω g ↦ by exact gradeStep_step y ω g) (fun k ↦ if k = 0 then 1 else 0)

variable {R L}

lemma gradeFun_algebraMap (r : R) (k : ℕ) :
    gradeFun R L (algebraMap R _ r) k = if k = 0 then algebraMap R _ r else 0 := by
  rw [gradeFun, CliffordAlgebra.foldr'_algebraMap]
  split_ifs with hk <;> simp [hk, Algebra.algebraMap_eq_smul_one]

lemma gradeFun_ι_mul (y : L) (ω : ExteriorAlgebra R L) (k : ℕ) :
    gradeFun R L (ι R y * ω) k = if k = 0 then 0 else ι R y * gradeFun R L ω (k - 1) :=
  congrFun (CliffordAlgebra.foldr'_ι_mul _ _ _ _ _ _) k

lemma gradeFun_mem (ω : ExteriorAlgebra R L) (k : ℕ) : gradeFun R L ω k ∈ ⋀[R]^k L := by
  induction ω using CliffordAlgebra.left_induction generalizing k with
  | algebraMap r =>
    rw [gradeFun_algebraMap]
    split_ifs with hk
    · subst hk; rw [exteriorPower, pow_zero]; exact Submodule.algebraMap_mem r
    · exact zero_mem _
  | add ω ω' hω hω' => rw [map_add, Pi.add_apply]; exact add_mem (hω k) (hω' k)
  | ι_mul ω y hω =>
    rw [gradeFun_ι_mul]
    split_ifs with hk
    · exact zero_mem _
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [exteriorPower, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ y) (hω k)

lemma gradeFun_of_mem {k : ℕ} {ω : ExteriorAlgebra R L} (hω : ω ∈ ⋀[R]^k L) (j : ℕ) :
    gradeFun R L ω j = if j = k then ω else 0 := by
  induction k generalizing ω j with
  | zero =>
    rw [exteriorPower, pow_zero, Submodule.mem_one] at hω
    obtain ⟨r, rfl⟩ := hω
    exact gradeFun_algebraMap r j
  | succ k ih =>
    rw [exteriorPower, pow_succ'] at hω
    induction hω using Submodule.mul_induction_on' generalizing j with
    | mem_mul_mem a ha b hb =>
      obtain ⟨y, rfl⟩ := ha
      rw [gradeFun_ι_mul]
      rcases j with _ | j
      · simp
      · simp [ih hb j]
    | add a _ b _ ha hb => simp [ha, hb, ite_add_ite]

variable (R L) in
/-- The projection `⋀L → ⋀ᵏL` onto the homogeneous component of degree `k`. -/
def degProj (k : ℕ) : ExteriorAlgebra R L →ₗ[R] ⋀[R]^k L :=
  LinearMap.codRestrict _ (LinearMap.proj k ∘ₗ gradeFun R L) fun ω ↦ gradeFun_mem ω k

@[simp] lemma degProj_subtype (k : ℕ) (ω : ⋀[R]^k L) : degProj R L k ω = ω := by
  exact Subtype.ext ((gradeFun_of_mem ω.2 k).trans (ite_eq_left_iff.mpr fun h ↦ absurd rfl h))

lemma degProj_comp_subtype (k : ℕ) : degProj R L k ∘ₗ (⋀[R]^k L).subtype = LinearMap.id :=
  LinearMap.ext fun ω ↦ degProj_subtype k ω

end DegProj

/-! ### The chains `⋀ᵏL ⊗ M` inside `⋀L ⊗ M` -/

section Module

variable (R L M : Type*) [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R L ⊗[R] M

/-- The inclusion `⋀ᵏL ⊗ M → ⋀L ⊗ M`. -/
def incl (k : ℕ) : ⋀[R]^k L ⊗[R] M →ₗ[R] E := (⋀[R]^k L).subtype.rTensor M

/-- The projection `⋀L ⊗ M → ⋀ᵏL ⊗ M`. -/
def proj (k : ℕ) : E →ₗ[R] ⋀[R]^k L ⊗[R] M := (degProj R L k).rTensor M

/-- The image `F_k` of `⋀ᵏL ⊗ M` in `⋀L ⊗ M`. -/
def chainsIn (k : ℕ) : Submodule R E := LinearMap.range (incl R L M k)

variable {R L M}

@[simp] lemma proj_incl (k : ℕ) (t : ⋀[R]^k L ⊗[R] M) : proj R L M k (incl R L M k t) = t := by
  rw [proj, incl, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, degProj_comp_subtype,
    LinearMap.rTensor_id, LinearMap.id_apply]

lemma incl_injective (k : ℕ) : Function.Injective (incl R L M k) :=
  Function.LeftInverse.injective (g := proj R L M k) (proj_incl k)

lemma incl_proj_of_mem {k : ℕ} {c : E} (hc : c ∈ chainsIn R L M k) :
    incl R L M k (proj R L M k c) = c := by
  obtain ⟨t, rfl⟩ := hc
  rw [proj_incl]

lemma incl_tmul (k : ℕ) (ω : ⋀[R]^k L) (m : M) :
    incl R L M k (ω ⊗ₜ m) = (ω : ExteriorAlgebra R L) ⊗ₜ m := rfl

lemma tmul_mem_chainsIn {k : ℕ} {ω : ExteriorAlgebra R L} (hω : ω ∈ ⋀[R]^k L) (m : M) :
    ω ⊗ₜ m ∈ chainsIn R L M k :=
  ⟨⟨ω, hω⟩ ⊗ₜ m, rfl⟩

lemma one_tmul_mem_chainsIn (m : M) : (1 : ExteriorAlgebra R L) ⊗ₜ m ∈ chainsIn R L M 0 :=
  tmul_mem_chainsIn (by rw [exteriorPower, pow_zero]; exact Submodule.one_le.mp le_rfl) m

lemma wedge_mem_chainsIn (y : L) {k : ℕ} {c : E} (hc : c ∈ chainsIn R L M k) :
    wedge R L M y c ∈ chainsIn R L M (k + 1) := by
  obtain ⟨t, rfl⟩ := hc
  induction t with
  | tmul ω m =>
    rw [incl_tmul, wedge_tmul]
    refine tmul_mem_chainsIn ?_ m
    rw [exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ y) ω.2
  | add t t' ht ht' => rw [map_add, map_add]; exact add_mem ht ht'

/-- `F_0` is spanned by the elements `1 ⊗ m`. -/
lemma chainsIn_zero_le {S : Submodule R E} (h : ∀ m : M, (1 : ExteriorAlgebra R L) ⊗ₜ m ∈ S) :
    chainsIn R L M 0 ≤ S := by
  rintro _ ⟨t, rfl⟩
  induction t with
  | tmul ω m =>
    obtain ⟨ω, hω⟩ := ω
    change ω ⊗ₜ m ∈ S
    rw [exteriorPower, pow_zero, Submodule.mem_one] at hω
    obtain ⟨r, rfl⟩ := hω
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
    exact h _
  | add t t' ht ht' => rw [map_add]; exact add_mem ht ht'

/-- `F_{k+1}` is spanned by the elements `y ∧ c` with `c ∈ F_k`. -/
lemma chainsIn_succ_le {k : ℕ} {S : Submodule R E}
    (h : ∀ (y : L) (c : E), c ∈ chainsIn R L M k → wedge R L M y c ∈ S) :
    chainsIn R L M (k + 1) ≤ S := by
  rintro _ ⟨t, rfl⟩
  induction t with
  | tmul ω m =>
    obtain ⟨ω, hω⟩ := ω
    change ω ⊗ₜ m ∈ S
    rw [exteriorPower, pow_succ'] at hω
    induction hω using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      obtain ⟨y, rfl⟩ := ha
      exact h y _ (tmul_mem_chainsIn hb m)
    | add a _ b _ ha hb => rw [add_tmul]; exact add_mem ha hb
  | add t t' ht ht' => rw [map_add]; exact add_mem ht ht'

lemma derivExt_mem_chainsIn (D : L →ₗ[R] L) (φ : M →ₗ[R] M) {k : ℕ} {c : E}
    (hc : c ∈ chainsIn R L M k) : derivExt D φ c ∈ chainsIn R L M k := by
  induction k generalizing c with
  | zero =>
    refine chainsIn_zero_le (S := (chainsIn R L M 0).comap (derivExt D φ)) (fun m ↦ ?_) hc
    rw [Submodule.mem_comap, derivExt_one_tmul]
    exact one_tmul_mem_chainsIn _
  | succ k ih =>
    refine chainsIn_succ_le (S := (chainsIn R L M (k + 1)).comap (derivExt D φ))
      (fun y c hc ↦ ?_) hc
    rw [Submodule.mem_comap, derivExt_wedge]
    exact add_mem (wedge_mem_chainsIn _ hc) (wedge_mem_chainsIn _ (ih hc))

end Module

/-! ### The differentials `d_k` -/

section Lie

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "E" => ExteriorAlgebra R L ⊗[R] M

variable {R L M} in
lemma diff_eq_zero_of_mem_chainsIn_zero {c : E} (hc : c ∈ chainsIn R L M 0) : diff R L M c = 0 :=
  chainsIn_zero_le (S := LinearMap.ker (diff R L M)) (fun m ↦ diff_one_tmul m) hc

variable {R L M} in
lemma diff_mem_chainsIn {k : ℕ} {c : E} (hc : c ∈ chainsIn R L M (k + 1)) :
    diff R L M c ∈ chainsIn R L M k := by
  induction k generalizing c with
  | zero =>
    refine chainsIn_succ_le (S := (chainsIn R L M 0).comap (diff R L M)) (fun y c hc ↦ ?_) hc
    rw [Submodule.mem_comap, diff_wedge, diff_eq_zero_of_mem_chainsIn_zero hc, map_zero,
      sub_zero]
    exact neg_mem (derivExt_mem_chainsIn _ _ hc)
  | succ k ih =>
    refine chainsIn_succ_le (S := (chainsIn R L M (k + 1)).comap (diff R L M))
      (fun y c hc ↦ ?_) hc
    rw [Submodule.mem_comap, diff_wedge]
    exact sub_mem (neg_mem (derivExt_mem_chainsIn _ _ hc)) (wedge_mem_chainsIn _ (ih hc))

/-- The Chevalley–Eilenberg differential `d_k : ⋀^{k+1}L ⊗ M → ⋀ᵏL ⊗ M`. -/
def d (k : ℕ) : ⋀[R]^(k + 1) L ⊗[R] M →ₗ[R] ⋀[R]^k L ⊗[R] M :=
  proj R L M k ∘ₗ diff R L M ∘ₗ incl R L M (k + 1)

variable {R L M}

/-- `d_k` is the restriction of the differential `d` of `⋀L ⊗ M`. -/
lemma incl_d (k : ℕ) (t : ⋀[R]^(k + 1) L ⊗[R] M) :
    incl R L M k (d R L M k t) = diff R L M (incl R L M (k + 1) t) :=
  incl_proj_of_mem (diff_mem_chainsIn ⟨t, rfl⟩)

/-- `d_k ∘ d_{k+1} = 0`. -/
theorem d_comp_d (k : ℕ) : d R L M k ∘ₗ d R L M (k + 1) = 0 := by
  ext t
  refine incl_injective k ?_
  simp [incl_d]

@[simp] lemma d_d (k : ℕ) (t : ⋀[R]^(k + 2) L ⊗[R] M) : d R L M k (d R L M (k + 1) t) = 0 :=
  LinearMap.congr_fun (d_comp_d k) t

/-- `d_0 (x ⊗ m) = -(1 ⊗ x m)`. -/
lemma incl_d_zero_tmul (x : L) (m : M) :
    incl R L M 0 (d R L M 0 (⟨ι R x, by simp⟩ ⊗ₜ m)) =
      -((1 : ExteriorAlgebra R L) ⊗ₜ ⁅x, m⁆) := by
  rw [incl_d, incl_tmul, diff_ι_tmul]

/-! ### Homology

We realize cycles and boundaries inside `⋀L ⊗ M`, i.e. with `F_k ≅ ⋀ᵏL ⊗ M` in place of
`⋀ᵏL ⊗ M`, and the homology `Z_k / B_k` as the image of `Z_k` in `(⋀L ⊗ M) / B_k`. (Quotients of
submodules of `⋀ᵏL ⊗ M` or of `⋀L ⊗ M` run into instance problems with the additive group
structure of the exterior algebra.) -/

variable (R L M) in
/-- The `k`-cycles `Z_k = F_k ∩ ker d ⊆ ⋀L ⊗ M` (for `k = 0` this is all of `F_0`). -/
def cycles (k : ℕ) : Submodule R E := chainsIn R L M k ⊓ LinearMap.ker (diff R L M)

variable (R L M) in
/-- The `k`-boundaries `B_k = d(F_{k+1}) ⊆ ⋀L ⊗ M`. -/
def boundaries (k : ℕ) : Submodule R E := (chainsIn R L M (k + 1)).map (diff R L M)

lemma mem_cycles_iff {k : ℕ} {c : E} :
    c ∈ cycles R L M k ↔ c ∈ chainsIn R L M k ∧ diff R L M c = 0 := Iff.rfl

lemma incl_mem_cycles_succ_iff {k : ℕ} {t : ⋀[R]^(k + 1) L ⊗[R] M} :
    incl R L M (k + 1) t ∈ cycles R L M (k + 1) ↔ d R L M k t = 0 := by
  rw [mem_cycles_iff, ← incl_d, map_eq_zero_iff _ (incl_injective k)]
  exact and_iff_right ⟨t, rfl⟩

lemma cycles_zero : cycles R L M 0 = chainsIn R L M 0 :=
  inf_eq_left.mpr fun _ hc ↦ diff_eq_zero_of_mem_chainsIn_zero hc

lemma boundaries_le_cycles (k : ℕ) : boundaries R L M k ≤ cycles R L M k := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨diff_mem_chainsIn hc, diff_diff c⟩

lemma boundaries_eq_map_d (k : ℕ) :
    boundaries R L M k = (LinearMap.range (d R L M k)).map (incl R L M k) := by
  rw [boundaries, chainsIn, LinearMap.range_eq_map, LinearMap.range_eq_map, ← Submodule.map_comp,
    ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun t ↦ (incl_d k t).symm

variable (R L M) in
/-- The **Lie algebra homology** `H_k(L, M) = Z_k / B_k` ([Weibel, §7.7] (check)), realized as
the image of `Z_k` in `(⋀L ⊗ M) / B_k`. -/
abbrev homology (k : ℕ) : Submodule R (E ⧸ boundaries R L M k) :=
  (cycles R L M k).map (boundaries R L M k).mkQ

/-- `H_k(L, M) ≅ Z_k / B_k`. -/
theorem ker_mkQ_cycles (k : ℕ) :
    LinearMap.ker ((boundaries R L M k).mkQ.domRestrict (cycles R L M k)) =
      (boundaries R L M k).comap (cycles R L M k).subtype := by
  ext c
  simp

/-! ### Functoriality in the coefficients -/

variable {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (R L) in
/-- The map `⋀ᵏL ⊗ M → ⋀ᵏL ⊗ N` induced by a morphism `f : M → N` of Lie modules. -/
abbrev mapChains (k : ℕ) (f : M →ₗ⁅R,L⁆ N) : ⋀[R]^k L ⊗[R] M →ₗ[R] ⋀[R]^k L ⊗[R] N :=
  (f : M →ₗ[R] N).lTensor _

omit [LieModule R L M] [LieModule R L N] in
lemma incl_mapChains (k : ℕ) (f : M →ₗ⁅R,L⁆ N) (t : ⋀[R]^k L ⊗[R] M) :
    incl R L N k (mapChains R L k f t) = (f : M →ₗ[R] N).lTensor _ (incl R L M k t) := by
  rw [incl, incl, mapChains, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- **Naturality** of `d_k` in the coefficient module. -/
theorem mapChains_d (k : ℕ) (f : M →ₗ⁅R,L⁆ N) (t : ⋀[R]^(k + 1) L ⊗[R] M) :
    mapChains R L k f (d R L M k t) = d R L N k (mapChains R L (k + 1) f t) := by
  refine incl_injective k ?_
  rw [incl_mapChains, incl_d, incl_d, incl_mapChains, lTensor_diff]

omit [LieModule R L M] [LieModule R L N] in
lemma lTensor_mem_chainsIn {k : ℕ} (f : M →ₗ⁅R,L⁆ N) {c : E} (hc : c ∈ chainsIn R L M k) :
    (f : M →ₗ[R] N).lTensor _ c ∈ chainsIn R L N k := by
  obtain ⟨t, rfl⟩ := hc
  exact ⟨_, incl_mapChains k f t⟩

lemma lTensor_mem_cycles {k : ℕ} (f : M →ₗ⁅R,L⁆ N) {c : E} (hc : c ∈ cycles R L M k) :
    (f : M →ₗ[R] N).lTensor _ c ∈ cycles R L N k :=
  ⟨lTensor_mem_chainsIn f hc.1, LinearMap.mem_ker.mpr (by
    rw [← lTensor_diff, LinearMap.mem_ker.mp hc.2, map_zero])⟩

lemma lTensor_mem_boundaries {k : ℕ} (f : M →ₗ⁅R,L⁆ N) {c : E} (hc : c ∈ boundaries R L M k) :
    (f : M →ₗ[R] N).lTensor _ c ∈ boundaries R L N k := by
  obtain ⟨c, hc, rfl⟩ := hc
  exact ⟨_, lTensor_mem_chainsIn f hc, (lTensor_diff f c).symm⟩

variable (R L) in
/-- The map `(⋀L ⊗ M) / B_k → (⋀L ⊗ N) / B_k` induced by a morphism `f : M → N`. -/
def quotMap (k : ℕ) (f : M →ₗ⁅R,L⁆ N) : (E ⧸ boundaries R L M k) →ₗ[R]
    (ExteriorAlgebra R L ⊗[R] N ⧸ boundaries R L N k) :=
  Submodule.mapQ _ _ ((f : M →ₗ[R] N).lTensor _) fun _ hc ↦ lTensor_mem_boundaries f hc

lemma quotMap_mk (k : ℕ) (f : M →ₗ⁅R,L⁆ N) (c : E) :
    quotMap R L k f (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk ((f : M →ₗ[R] N).lTensor _ c) := rfl

lemma quotMap_mem_homology {k : ℕ} (f : M →ₗ⁅R,L⁆ N) {x : E ⧸ boundaries R L M k}
    (hx : x ∈ homology R L M k) : quotMap R L k f x ∈ homology R L N k := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨_, lTensor_mem_cycles f hc, rfl⟩

variable (R L) in
/-- The map `H_k(L, M) → H_k(L, N)` induced by a morphism `f : M → N` of Lie modules. -/
def homologyMap (k : ℕ) (f : M →ₗ⁅R,L⁆ N) : homology R L M k →ₗ[R] homology R L N k :=
  (quotMap R L k f).restrict fun _ hx ↦ quotMap_mem_homology f hx

@[simp] lemma coe_homologyMap (k : ℕ) (f : M →ₗ⁅R,L⁆ N) (x : homology R L M k) :
    (homologyMap R L k f x : ExteriorAlgebra R L ⊗[R] N ⧸ boundaries R L N k) =
      quotMap R L k f x := rfl

@[simp] lemma homologyMap_id (k : ℕ) :
    homologyMap R L k (LieModuleHom.id : M →ₗ⁅R,L⁆ M) = LinearMap.id := by
  ext ⟨x, hx⟩
  obtain ⟨c, -, rfl⟩ := hx
  simp only [LinearMap.id_coe, id_eq, coe_homologyMap, Submodule.mkQ_apply, quotMap_mk]
  rw [show ((LieModuleHom.id : M →ₗ⁅R,L⁆ M) : M →ₗ[R] M) = LinearMap.id from rfl,
    LinearMap.lTensor_id, LinearMap.id_apply]

lemma homologyMap_comp {P : Type*} [AddCommGroup P] [Module R P] [LieRingModule L P]
    [LieModule R L P] (k : ℕ) (g : N →ₗ⁅R,L⁆ P) (f : M →ₗ⁅R,L⁆ N) :
    homologyMap R L k (g.comp f) = homologyMap R L k g ∘ₗ homologyMap R L k f := by
  ext ⟨x, hx⟩
  obtain ⟨c, -, rfl⟩ := hx
  simp only [LinearMap.comp_apply, coe_homologyMap, Submodule.mkQ_apply, quotMap_mk,
    LieModuleHom.toLinearMap_comp, LinearMap.lTensor_comp]

end Lie

end LieModule.ChevalleyEilenberg
