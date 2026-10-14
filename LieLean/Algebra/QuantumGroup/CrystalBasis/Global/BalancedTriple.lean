/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.ScalarResidue

/-!
# Balanced triples (Kashiwara, Lemmas 7.1.1 and 7.1.2)

Let `V` be a vector space over `𝕂 = ℚ(v)`, `L₀` a lattice over `A = ℚ[[v⁻¹]] ∩ ℚ(v)` (the local
ring at `v = ∞`, uniformizer `v⁻¹`) and `L_∞` a lattice over `Ā = ℚ[v]_{(v)}` (the local ring at
`v = 0`, uniformizer `v`). Kashiwara's Lemma 7.1.1 (ii) ([Kas91], stated there with lattices at
`q = 0` and `q = ∞`; `q` corresponds to `v⁻¹`) says: if `M` is spanned over `𝒜 = ℤ[v, v⁻¹]` by
elements `g_b ∈ L₀ ∩ L_∞` whose images in `L₀/v⁻¹L₀` and in `L_∞/vL_∞` are linearly independent,
then `M ∩ L₀ ∩ L_∞ = ⊕ ℤ g_b` and `M ∩ v⁻¹L₀ ∩ L_∞ = 0`. We prove it in this basis form:

* `ResidueIndependent L ϖ g`: the `g_b ∈ L` are independent modulo `ϖ L`;
* `ResidueIndependent.exists_eq_of_sum_mem`, `ResidueIndependent.exists_eq_of_sum_mem_smul`:
  if `Σ c_b g_b ∈ L` (resp. `∈ ϖ L`) with `c_b` in the fraction field, then all `c_b ∈ A`
  (resp. `∈ ϖ A`), for any discrete valuation ring `A`;
* `ResidueIndependent.linearIndependent`: the `g_b` are linearly independent over the field;
* `exists_int_of_laurent_regular`, `eq_zero_of_laurent_regular_uniformizer`:
  `𝒜 ∩ A ∩ Ā = ℤ` and `𝒜 ∩ v⁻¹A ∩ Ā = 0` inside `ℚ(v)`;
* `balanced_coeff_int`, `balanced_coeff_zero`: **Kashiwara Lemma 7.1.1 (ii)**,
  in the form: if `Σ c_b g_b` with `c_b ∈ 𝒜` lies in `L₀ ∩ L_∞`, then every `c_b` is an integer;
  if it lies in `v⁻¹L₀ ∩ L_∞`, then every `c_b` is zero;
* `balanced_eq_zero_of_mem_span`: Lemma 7.1.1 (i) in the form `M ∩ v⁻¹L₀ ∩ L_∞ = 0`;
* `exists_split_of_mem_span`: `M = M ∩ L₀ + M ∩ L_∞` when the `g_b` lie in `L₀ ∩ L_∞`;
* `exists_residueIndependent_extension`: **Kashiwara Lemma 7.1.2** in basis form: vectors of
  `(L₀ + M) ∩ (L_∞ + M)` with residues independent modulo `M` can be corrected by elements of
  `M` so that, together with the `g_b`, they lie in `L₀ ∩ L_∞` with independent residues;
* `balanced_eq_of_sub_eq_smul`: the scalar step of [Kas91] Lemma 7.3.4: if `x, x' ∈ L₀ ∩ L_∞` and
  `x - x' ∈ (v - v⁻¹) M`, then `x = x'`.

Lemmas 7.1.1 and 7.1.2 follow Kashiwara's statements and the structure of his proofs (the
splitting `M = M ∩ L₀ + M ∩ L_∞` in 7.1.2); the valuation arguments for the scalar
intersections `𝒜 ∩ A ∩ Ā = ℤ`, `𝒜 ∩ v⁻¹A ∩ Ā = 0` and the basis-form formulation are our own.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.1 and Lemma 7.3.4.
-/

open Finset Pointwise

noncomputable section

namespace LieLean.QuantumGroup

/-! ### Coordinates with respect to residue-independent families -/

section DVR

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {A : Type*} [CommRing A] [Algebra A K] [Module A V] [IsScalarTower A K V]
  {ι : Type*}

variable (A) in
/-- The family `g` (with values in `L`) is linearly independent modulo `ϖ L`: if a finite
combination `Σ aᵢ gᵢ` with coefficients in `A` lies in `ϖ L`, then `ϖ` divides every `aᵢ`. -/
def ResidueIndependent (L : Submodule A V) (ϖ : A) (g : ι → V) : Prop :=
  (∀ i, g i ∈ L) ∧ ∀ (s : Finset ι) (a : ι → A), ∑ i ∈ s, a i • g i ∈ ϖ • L → ∀ i ∈ s, ϖ ∣ a i

variable {L : Submodule A V} {ϖ : A} {g : ι → V}

omit [Module K V] [Module A V] [IsScalarTower A K V] in
lemma algebraMap_ne_zero_of_ne (hinj : Function.Injective (algebraMap A K)) (hϖ : ϖ ≠ 0) :
    algebraMap A K ϖ ≠ 0 := by
  rw [← map_zero (algebraMap A K)]; exact fun h ↦ hϖ (hinj h)

/-- `ϖ⁻¹ • (ϖ • y) = y`. -/
lemma inv_smul_smul_uniformizer (hϖ : algebraMap A K ϖ ≠ 0) (y : V) :
    (algebraMap A K ϖ)⁻¹ • ϖ • y = y := by
  rw [← algebraMap_smul K ϖ y, smul_smul, inv_mul_cancel₀ hϖ, one_smul]

/-- Descent step: coefficients with `ϖ^m cᵢ ∈ A` and `Σ cᵢ gᵢ ∈ L` lie in `A`. -/
lemma ResidueIndependent.mem_of_pow (hinj : Function.Injective (algebraMap A K)) (hϖ : ϖ ≠ 0)
    (hg : ResidueIndependent A L ϖ g) (s : Finset ι) :
    ∀ (m : ℕ) (c : ι → K), (∀ i ∈ s, ∃ a : A, algebraMap A K (ϖ ^ m) * c i = algebraMap A K a) →
      ∑ i ∈ s, c i • g i ∈ L → ∀ i ∈ s, ∃ a : A, c i = algebraMap A K a := by
  intro m
  induction m with
  | zero =>
    intro c hc _ i hi
    obtain ⟨a, ha⟩ := hc i hi
    exact ⟨a, by simpa using ha⟩
  | succ m ih =>
    intro c hc hsum
    choose! a ha using hc
    have hmem : ∑ i ∈ s, a i • g i ∈ ϖ • L := by
      have : ∑ i ∈ s, a i • g i = ϖ • ((ϖ ^ m) • ∑ i ∈ s, c i • g i) := by
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [← algebraMap_smul K (a i), ← ha i hi, ← algebraMap_smul K ϖ,
          ← algebraMap_smul K (ϖ ^ m), smul_smul, smul_smul, ← map_mul, ← pow_succ']
      rw [this]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (L.smul_mem _ hsum)
    have hdiv := hg.2 s a hmem
    refine ih c (fun i hi ↦ ?_) hsum
    obtain ⟨b, hb⟩ := hdiv i hi
    refine ⟨b, ?_⟩
    apply mul_left_cancel₀ (algebraMap_ne_zero_of_ne hinj hϖ)
    rw [← mul_assoc, ← map_mul, ← pow_succ', ha i hi, hb, map_mul]

/-- If `Σ cᵢ gᵢ ∈ L` with `cᵢ ∈ K`, then all `cᵢ ∈ A`. -/
theorem ResidueIndependent.exists_eq_of_sum_mem (hinj : Function.Injective (algebraMap A K))
    (hϖ : ϖ ≠ 0) (hk : ∀ c : K, ∃ (m : ℕ) (a : A), algebraMap A K (ϖ ^ m) * c = algebraMap A K a)
    (hg : ResidueIndependent A L ϖ g)
    (s : Finset ι) (c : ι → K) (hsum : ∑ i ∈ s, c i • g i ∈ L) :
    ∀ i ∈ s, ∃ a : A, c i = algebraMap A K a := by
  choose m a ha using fun i ↦ hk (c i)
  refine hg.mem_of_pow hinj hϖ s (∑ i ∈ s, m i) c (fun i hi ↦ ?_) hsum
  refine ⟨ϖ ^ (∑ j ∈ s, m j - m i) * a i, ?_⟩
  rw [map_mul, ← ha i, ← mul_assoc, ← map_mul, ← pow_add,
    Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi)]

/-- If `Σ cᵢ gᵢ ∈ ϖ L` with `cᵢ ∈ K`, then all `cᵢ ∈ ϖ A`. -/
theorem ResidueIndependent.exists_eq_of_sum_mem_smul
    (hinj : Function.Injective (algebraMap A K)) (hϖ : ϖ ≠ 0)
    (hk : ∀ c : K, ∃ (m : ℕ) (a : A), algebraMap A K (ϖ ^ m) * c = algebraMap A K a)
    (hg : ResidueIndependent A L ϖ g)
    (s : Finset ι) (c : ι → K) (hsum : ∑ i ∈ s, c i • g i ∈ ϖ • L) :
    ∀ i ∈ s, ∃ a : A, c i = algebraMap A K (ϖ * a) := by
  obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hsum
  have hϖ' := algebraMap_ne_zero_of_ne (K := K) hinj hϖ
  have h : ∑ i ∈ s, ((algebraMap A K ϖ)⁻¹ * c i) • g i ∈ L := by
    have : ∑ i ∈ s, ((algebraMap A K ϖ)⁻¹ * c i) • g i = y := by
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, ← hxy, inv_smul_smul_uniformizer hϖ']
    rw [this]; exact hy
  intro i hi
  obtain ⟨a, ha⟩ := hg.exists_eq_of_sum_mem hinj hϖ hk s _ h i hi
  refine ⟨a, ?_⟩
  rw [map_mul, ← ha, ← mul_assoc, mul_inv_cancel₀ hϖ', one_mul]

/-- If `Σ cᵢ gᵢ ∈ ϖⁿ L`, then all `cᵢ ∈ ϖⁿ A`. -/
theorem ResidueIndependent.exists_eq_of_sum_mem_pow
    (hinj : Function.Injective (algebraMap A K)) (hϖ : ϖ ≠ 0)
    (hk : ∀ c : K, ∃ (m : ℕ) (a : A), algebraMap A K (ϖ ^ m) * c = algebraMap A K a)
    (hg : ResidueIndependent A L ϖ g) (s : Finset ι) (n : ℕ) (c : ι → K)
    (hsum : ∑ i ∈ s, c i • g i ∈ ϖ ^ n • L) :
    ∀ i ∈ s, ∃ a : A, c i = algebraMap A K (ϖ ^ n * a) := by
  induction n generalizing c with
  | zero =>
    simp only [pow_zero, one_smul, one_mul] at hsum ⊢
    exact hg.exists_eq_of_sum_mem hinj hϖ hk s c hsum
  | succ n ih =>
    have hϖ' := algebraMap_ne_zero_of_ne (K := K) hinj hϖ
    obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hsum
    have h : ∑ i ∈ s, ((algebraMap A K ϖ)⁻¹ * c i) • g i ∈ ϖ ^ n • L := by
      have : ∑ i ∈ s, ((algebraMap A K ϖ)⁻¹ * c i) • g i = ϖ ^ n • y := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, ← hxy, pow_succ', mul_smul, inv_smul_smul_uniformizer hϖ']
      rw [this]; exact Submodule.smul_mem_pointwise_smul _ _ _ hy
    intro i hi
    obtain ⟨a, ha⟩ := ih _ h i hi
    refine ⟨a, ?_⟩
    rw [pow_succ', mul_assoc, map_mul, ← ha, ← mul_assoc, mul_inv_cancel₀ hϖ', one_mul]

/-- A residue-independent family is linearly independent over the field (`ϖ` a uniformizer). -/
theorem ResidueIndependent.linearIndependent [IsDomain A] [IsDiscreteValuationRing A]
    (hinj : Function.Injective (algebraMap A K)) (hϖ : ϖ ≠ 0)
    (hk : ∀ c : K, ∃ (m : ℕ) (a : A), algebraMap A K (ϖ ^ m) * c = algebraMap A K a)
    (hg : ResidueIndependent A L ϖ g) (hirr : Irreducible ϖ) : LinearIndependent K g := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hall : ∀ n : ℕ, ∃ a : A, c i = algebraMap A K (ϖ ^ n * a) := fun n ↦
    hg.exists_eq_of_sum_mem_pow hinj hϖ hk s n c (by rw [hc]; exact zero_mem _) i hi
  obtain ⟨a, ha⟩ := hall 0
  rw [pow_zero, one_mul] at ha
  by_contra hne
  have ha0 : a ≠ 0 := by rintro rfl; exact hne (by simp [ha])
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hirr
  obtain ⟨b, hb⟩ := hall (n + 1)
  have : a = ϖ ^ (n + 1) * b := hinj (by rw [← ha, hb])
  -- `a u = ϖⁿ` and `a = ϖ^{n+1} b` give `ϖ (b u) = 1`
  have h2 : ϖ ^ n * (ϖ * (b * u)) = ϖ ^ n * 1 :=
    calc ϖ ^ n * (ϖ * (b * u)) = ϖ ^ (n + 1) * b * u := by ring
      _ = a * u := by rw [this]
      _ = ϖ ^ n * 1 := by rw [hu, mul_one]
  have h3 : ϖ * (b * u) = 1 := mul_left_cancel₀ (pow_ne_zero _ hϖ) h2
  exact hirr.not_isUnit (isUnit_iff_exists_inv.2 ⟨_, h3⟩)

omit [Module K V] [Algebra A K] [IsScalarTower A K V] in
/-- Adjoining to a residue-independent family `g` a family `y ⊆ L` that is residue-independent
modulo a submodule `W` containing every `g i` gives a residue-independent family. -/
theorem ResidueIndependent.sumElim {κ : Type*} (hg : ResidueIndependent A L ϖ g) {y : κ → V}
    (W : Submodule A V) (hgW : ∀ i, g i ∈ W) (hy : ∀ s, y s ∈ L)
    (hyW : ∀ (t : Finset κ) (a : κ → A), ∑ s ∈ t, a s • y s ∈ ϖ • L ⊔ W → ∀ s ∈ t, ϖ ∣ a s) :
    ResidueIndependent A L ϖ (Sum.elim g y) := by
  refine ⟨fun x ↦ ?_, fun t a ht ↦ ?_⟩
  · cases x with
    | inl i => exact hg.1 i
    | inr s => exact hy s
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight] at ht
  simp only [Sum.elim_inl, Sum.elim_inr] at ht
  have hW : ∑ i ∈ t.toLeft, a (Sum.inl i) • g i ∈ W :=
    Submodule.sum_mem _ fun i _ ↦ W.smul_mem _ (hgW i)
  have hright : ∀ s ∈ t.toRight, ϖ ∣ a (Sum.inr s) := by
    refine hyW t.toRight (fun s ↦ a (Sum.inr s)) ?_
    have : ∑ s ∈ t.toRight, a (Sum.inr s) • y s =
        (∑ i ∈ t.toLeft, a (Sum.inl i) • g i + ∑ s ∈ t.toRight, a (Sum.inr s) • y s) -
          ∑ i ∈ t.toLeft, a (Sum.inl i) • g i := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ht) (Submodule.mem_sup_right hW)
  have hR : ∑ s ∈ t.toRight, a (Sum.inr s) • y s ∈ ϖ • L := by
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    obtain ⟨b, hb⟩ := hright s hs
    rw [hb, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (L.smul_mem _ (hy s))
  have hleft : ∀ i ∈ t.toLeft, ϖ ∣ a (Sum.inl i) := by
    refine hg.2 t.toLeft (fun i ↦ a (Sum.inl i)) ?_
    have : ∑ i ∈ t.toLeft, a (Sum.inl i) • g i =
        (∑ i ∈ t.toLeft, a (Sum.inl i) • g i + ∑ s ∈ t.toRight, a (Sum.inr s) • y s) -
          ∑ s ∈ t.toRight, a (Sum.inr s) • y s := by abel
    rw [this]
    exact Submodule.sub_mem _ ht hR
  intro x hx
  cases x with
  | inl i => exact hleft i (Finset.mem_toLeft.2 hx)
  | inr s => exact hright s (Finset.mem_toRight.2 hx)

omit [Module K V] [Algebra A K] [IsScalarTower A K V] in
/-- Residue independence modulo `W` is unchanged by perturbing each vector inside `W`. -/
theorem residueIndependent_mod_of_sub_mem {κ : Type*} (W : Submodule A V) {f y : κ → V}
    (hfy : ∀ s, y s - f s ∈ W)
    (hf : ∀ (t : Finset κ) (a : κ → A), ∑ s ∈ t, a s • f s ∈ ϖ • L ⊔ W → ∀ s ∈ t, ϖ ∣ a s)
    (t : Finset κ) (a : κ → A) (ht : ∑ s ∈ t, a s • y s ∈ ϖ • L ⊔ W) : ∀ s ∈ t, ϖ ∣ a s := by
  refine hf t a ?_
  have : ∑ s ∈ t, a s • f s = ∑ s ∈ t, a s • y s - ∑ s ∈ t, a s • (y s - f s) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [smul_sub]; abel
  rw [this]
  exact Submodule.sub_mem _ ht
    (Submodule.mem_sup_right (Submodule.sum_mem _ fun s _ ↦ W.smul_mem _ (hfy s)))

end DVR

/-! ### Scalar intersections in `ℚ(v)` -/

section Scalar

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ

/-- Integer Laurent polynomials evaluate into the rational Laurent functions. -/
lemma integralLaurentEval_mem_range_laurentToCoeff (f : LaurentPolynomial ℤ) :
    integralLaurentEval f ∈ Set.range laurentToCoeff := by
  refine LaurentPolynomial.induction_on' f ?_ ?_
  · rintro p q ⟨p', hp⟩ ⟨q', hq⟩
    exact ⟨p' + q', by rw [map_add, map_add, hp, hq]⟩
  · intro n a
    refine ⟨LaurentPolynomial.C (a : ℚ) * LaurentPolynomial.T n, ?_⟩
    simp [laurentToCoeff, integralLaurentEval]

/-- `𝒜 ∩ A ∩ Ā = ℤ`: a Laurent integer that is regular at `v = ∞` (an element of
`InfinityLocalRing`) and at `v = 0` (an element of `LocalRing`) is an integer. -/
theorem exists_int_of_laurent_regular (f : LaurentPolynomial ℤ) (a : InfinityLocalRing)
    (ha : algebraMap InfinityLocalRing 𝕂 a = integralLaurentEval f) (b : LocalRing)
    (hb : algebraMap LocalRing 𝕂 b = integralLaurentEval f) :
    ∃ z : ℤ, integralLaurentEval f = z := by
  have hzero : integralLaurentEval f ∈ LocalRing := hb ▸ b.2
  have hinf : RatFunc.bar (integralLaurentEval f) ∈ LocalRing := by
    rw [← ha]
    change RatFunc.bar (RatFunc.bar (algebraMap LocalRing 𝕂 a)) ∈ LocalRing
    rw [RatFunc.bar_bar]
    exact (show LocalRing from a).2
  obtain ⟨c, hc⟩ := scalar_laurent_intersection _
    (integralLaurentEval_mem_range_laurentToCoeff f) hzero hinf
  obtain ⟨z, hz⟩ := residue_integer_of_laurent_at_zero b f hb
  have hbc : b = algebraMap ℚ LocalRing c :=
    injective_algebraMap_localRing (by rw [hb, hc]; exact (local_rat_coe c).symm)
  rw [hbc, residue_rat] at hz
  exact ⟨z, by rw [hc, hz, map_intCast]⟩

/-- `𝒜 ∩ v⁻¹A ∩ Ā = 0`: a Laurent integer in `v⁻¹ InfinityLocalRing` and in `LocalRing`
is zero. -/
theorem eq_zero_of_laurent_regular_uniformizer (f : LaurentPolynomial ℤ) (a : InfinityLocalRing)
    (ha : algebraMap InfinityLocalRing 𝕂 (InfinityLocalRing.uniformizer * a) =
      integralLaurentEval f) (b : LocalRing)
    (hb : algebraMap LocalRing 𝕂 b = integralLaurentEval f) :
    integralLaurentEval f = 0 := by
  obtain ⟨z, hz⟩ := exists_int_of_laurent_regular f _ ha b hb
  let a' : LocalRing := a
  have h1 : algebraMap LocalRing 𝕂 (localX * a') =
      algebraMap LocalRing 𝕂 (z : LocalRing) := by
    have h := congrArg RatFunc.bar (ha.trans hz)
    change RatFunc.bar (RatFunc.bar (algebraMap LocalRing 𝕂 (localX * a'))) =
      RatFunc.bar (z : 𝕂) at h
    rw [RatFunc.bar_bar, map_intCast] at h
    rw [h, map_intCast]
  have h2 := congrArg residue (injective_algebraMap_localRing h1)
  rw [map_mul, residue_localX, zero_mul, map_intCast] at h2
  rw [hz]
  exact_mod_cast h2.symm

/-- `(v - v⁻¹)⁻¹ ∈ v Ā`: it is regular at `v = 0` and vanishes there. -/
lemma exists_inv_X_sub_eq_localX_mul :
    ∃ u : LocalRing, algebraMap LocalRing 𝕂 (localX * u) = (RatFunc.X - RatFunc.X⁻¹)⁻¹ := by
  have hw : IsUnit (localX ^ 2 - 1 : LocalRing) := by
    rw [← IsLocalRing.notMem_maximalIdeal, maximalIdeal_localRing, ← ker_residue,
      RingHom.mem_ker]
    simp
  refine ⟨↑hw.unit⁻¹, ?_⟩
  have h1 : algebraMap LocalRing 𝕂 (localX ^ 2 - 1) * algebraMap LocalRing 𝕂 ↑hw.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_sub, map_pow, map_one, algebraMap_localX, inv_inv] at h1
  rw [map_mul, algebraMap_localX, inv_inv, eq_inv_of_mul_eq_one_right h1]
  have hX : (RatFunc.X : 𝕂) ≠ 0 := RatFunc.X_ne_zero
  have h2 : (RatFunc.X ^ 2 - 1 : 𝕂) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have h3 : (RatFunc.X - RatFunc.X⁻¹ : 𝕂) = (RatFunc.X ^ 2 - 1) * RatFunc.X⁻¹ := by
    field_simp
  rw [h3, mul_inv, inv_inv, mul_comm]

/-- `(v - v⁻¹)⁻¹ ∈ v⁻¹ A`: it is regular at `v = ∞` and vanishes there. -/
lemma exists_inv_X_sub_eq_uniformizer_mul :
    ∃ u : InfinityLocalRing, algebraMap InfinityLocalRing 𝕂 (InfinityLocalRing.uniformizer * u) =
      (RatFunc.X - RatFunc.X⁻¹)⁻¹ := by
  obtain ⟨u, hu⟩ := exists_inv_X_sub_eq_localX_mul
  refine ⟨-u, ?_⟩
  change RatFunc.bar (algebraMap LocalRing 𝕂 (localX * -u)) = _
  rw [mul_neg, map_neg, hu, map_neg, map_inv₀, map_sub, RatFunc.bar_X, map_inv₀, RatFunc.bar_X,
    inv_inv, ← inv_neg, neg_sub]

/-- Every Laurent integer is the sum of one regular at `v = ∞` and one regular at `v = 0`. -/
lemma exists_laurent_split (c : LaurentPolynomial ℤ) :
    ∃ (c₀ c₁ : LaurentPolynomial ℤ) (a : InfinityLocalRing) (b : LocalRing), c = c₀ + c₁ ∧
      algebraMap InfinityLocalRing 𝕂 a = integralLaurentEval c₀ ∧
      algebraMap LocalRing 𝕂 b = integralLaurentEval c₁ := by
  refine LaurentPolynomial.induction_on' c ?_ ?_
  · rintro p q ⟨p₀, p₁, a, b, rfl, ha, hb⟩ ⟨q₀, q₁, a', b', rfl, ha', hb'⟩
    exact ⟨p₀ + q₀, p₁ + q₁, a + a', b + b', by ring, by rw [map_add, map_add, ha, ha'],
      by rw [map_add, map_add, hb, hb']⟩
  · intro n z
    rcases le_or_gt n 0 with hn | hn
    · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn
      refine ⟨LaurentPolynomial.C z * LaurentPolynomial.T (-(m : ℤ)), 0,
        (z : InfinityLocalRing) * InfinityLocalRing.uniformizer ^ m, 0, by ring, ?_, by simp⟩
      rw [map_mul, map_pow, InfinityLocalRing.algebraMap_uniformizer, map_mul,
        integralLaurentEval_T, map_intCast, zpow_neg, zpow_natCast, inv_pow]
      simp [integralLaurentEval]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
      refine ⟨0, LaurentPolynomial.C z * LaurentPolynomial.T (m : ℤ), 0,
        (z : LocalRing) * localX ^ m, by ring, by simp, ?_⟩
      rw [map_mul, map_pow, algebraMap_localX, inv_inv, map_mul, integralLaurentEval_T,
        map_intCast, zpow_natCast]
      simp [integralLaurentEval]


end Scalar

/-! ### Laurent spans -/

section LaurentSpan

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ

variable {V : Type*} [AddCommGroup V] [Module 𝕂 V] [Module (LaurentPolynomial ℤ) V] {ι : Type*}
  {g : ι → V}

/-- The `𝒜`-span of `g` lies in its `ℚ(v)`-span. -/
lemma mem_span_field_of_mem_span_laurent
    (hsmul : ∀ (c : LaurentPolynomial ℤ) (x : V), c • x = integralLaurentEval c • x) {x : V}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g)) :
    x ∈ Submodule.span 𝕂 (Set.range g) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy => rw [hsmul]; exact Submodule.smul_mem _ _ hy

end LaurentSpan

/-! ### Balanced coefficients -/

section Balanced

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ

variable {V : Type*} [AddCommGroup V] [Module 𝕂 V]
  [Module InfinityLocalRing V] [IsScalarTower InfinityLocalRing 𝕂 V]
  [Module LocalRing V] [IsScalarTower LocalRing 𝕂 V] {ι : Type*}
  {L₀ : Submodule InfinityLocalRing V} {L₁ : Submodule LocalRing V} {g : ι → V}

/-- **Kashiwara, Lemma 7.1.1 (ii)**, coefficient form, first half. Let the `g_b` lie in
`L₀ ∩ L₁` with independent residues in `L₀ / v⁻¹L₀` and in `L₁ / vL₁`. If a combination
`Σ c_b g_b` with Laurent integer coefficients lies in `L₀ ∩ L₁`, then every `c_b ∈ ℤ`. -/
theorem balanced_coeff_int
    (h₀ : ResidueIndependent InfinityLocalRing L₀ InfinityLocalRing.uniformizer g)
    (h₁ : ResidueIndependent LocalRing L₁ localX g) (s : Finset ι)
    (c : ι → LaurentPolynomial ℤ) (hs₀ : ∑ i ∈ s, integralLaurentEval (c i) • g i ∈ L₀)
    (hs₁ : ∑ i ∈ s, integralLaurentEval (c i) • g i ∈ L₁) :
    ∀ i ∈ s, ∃ z : ℤ, integralLaurentEval (c i) = z := by
  intro i hi
  obtain ⟨a, ha⟩ := h₀.exists_eq_of_sum_mem InfinityLocalRing.injective_algebraMap
    (show InfinityLocalRing.uniformizer ≠ 0 from irreducible_localX.ne_zero)
    InfinityLocalRing.exists_pow_mul s _ hs₀ i hi
  obtain ⟨b, hb⟩ := h₁.exists_eq_of_sum_mem injective_algebraMap_localRing
    irreducible_localX.ne_zero exists_pow_localX_mul s _ hs₁ i hi
  exact exists_int_of_laurent_regular _ a ha.symm b hb.symm

/-- **Kashiwara, Lemma 7.1.1 (ii)**, coefficient form, second half: if the combination lies in
`v⁻¹L₀ ∩ L₁`, then every coefficient vanishes. -/
theorem balanced_coeff_zero
    (h₀ : ResidueIndependent InfinityLocalRing L₀ InfinityLocalRing.uniformizer g)
    (h₁ : ResidueIndependent LocalRing L₁ localX g) (s : Finset ι)
    (c : ι → LaurentPolynomial ℤ)
    (hs₀ : ∑ i ∈ s, integralLaurentEval (c i) • g i ∈ InfinityLocalRing.uniformizer • L₀)
    (hs₁ : ∑ i ∈ s, integralLaurentEval (c i) • g i ∈ L₁) :
    ∀ i ∈ s, integralLaurentEval (c i) = 0 := by
  intro i hi
  obtain ⟨a, ha⟩ := h₀.exists_eq_of_sum_mem_smul InfinityLocalRing.injective_algebraMap
    (show InfinityLocalRing.uniformizer ≠ 0 from irreducible_localX.ne_zero)
    InfinityLocalRing.exists_pow_mul s _ hs₀ i hi
  obtain ⟨b, hb⟩ := h₁.exists_eq_of_sum_mem injective_algebraMap_localRing
    irreducible_localX.ne_zero exists_pow_localX_mul s _ hs₁ i hi
  exact eq_zero_of_laurent_regular_uniformizer _ a ha.symm b hb.symm

variable [Module (LaurentPolynomial ℤ) V]
  (hsmul : ∀ (c : LaurentPolynomial ℤ) (x : V), c • x = integralLaurentEval c • x)
include hsmul

/-- If the `g_b` lie in `L₀ ∩ L₁`, their `𝒜`-span is `N ∩ L₀ + N ∩ L₁` (the decomposition used
in the proof of Kashiwara's Lemma 7.1.2). -/
lemma exists_split_of_mem_span (hg₀ : ∀ i, g i ∈ L₀) (hg₁ : ∀ i, g i ∈ L₁) {x : V}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g)) :
    ∃ x₀ x₁ : V, x = x₀ + x₁ ∧ x₀ ∈ L₀ ∧ x₁ ∈ L₁ ∧
      x₀ ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g) ∧
      x₁ ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g) := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
  choose c₀ c₁ a b hc ha hb using exists_laurent_split
  refine ⟨c.sum fun i e ↦ c₀ e • g i, c.sum fun i e ↦ c₁ e • g i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Finsupp.sum_add]
    exact Finsupp.sum_congr fun i _ ↦ by rw [← add_smul, ← hc (c i)]
  · refine Submodule.sum_mem _ fun i _ ↦ ?_
    dsimp only
    rw [hsmul, ← ha, algebraMap_smul]
    exact L₀.smul_mem _ (hg₀ i)
  · refine Submodule.sum_mem _ fun i _ ↦ ?_
    dsimp only
    rw [hsmul, ← hb, algebraMap_smul]
    exact L₁.smul_mem _ (hg₁ i)
  · exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Kashiwara, Lemma 7.1.2**, in basis form. Let `N` be the `𝒜`-span of a family `g` in
`L₀ ∩ L₁` with independent residues on both sides. Let `f_s ∈ (L₀ + N) ∩ (L₁ + N)` be vectors
whose residues are independent modulo `ℚ(v) N` on both sides. Then there are `y_s ≡ f_s mod N`
such that `g ⊔ y` lies in `L₀ ∩ L₁` with independent residues on both sides. -/
theorem exists_residueIndependent_extension {κ : Type*}
    (h₀ : ResidueIndependent InfinityLocalRing L₀ InfinityLocalRing.uniformizer g)
    (h₁ : ResidueIndependent LocalRing L₁ localX g) (f : κ → V)
    (hf₀ : ∀ s, ∃ l ∈ L₀, f s - l ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g))
    (hf₁ : ∀ s, ∃ l ∈ L₁, f s - l ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g))
    (hr₀ : ∀ (t : Finset κ) (a : κ → InfinityLocalRing), ∑ s ∈ t, a s • f s ∈
      InfinityLocalRing.uniformizer • L₀ ⊔
        (Submodule.span 𝕂 (Set.range g)).restrictScalars InfinityLocalRing →
      ∀ s ∈ t, InfinityLocalRing.uniformizer ∣ a s)
    (hr₁ : ∀ (t : Finset κ) (a : κ → LocalRing), ∑ s ∈ t, a s • f s ∈
      localX • L₁ ⊔ (Submodule.span 𝕂 (Set.range g)).restrictScalars LocalRing →
      ∀ s ∈ t, localX ∣ a s) :
    ∃ y : κ → V, (∀ s, y s - f s ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g)) ∧
      ResidueIndependent InfinityLocalRing L₀ InfinityLocalRing.uniformizer (Sum.elim g y) ∧
      ResidueIndependent LocalRing L₁ localX (Sum.elim g y) := by
  set N := Submodule.span (LaurentPolynomial ℤ) (Set.range g)
  have hy : ∀ s, ∃ y : V, y - f s ∈ N ∧ y ∈ L₀ ∧ y ∈ L₁ := by
    intro s
    obtain ⟨l₀, hl₀, hn₀⟩ := hf₀ s
    obtain ⟨l₁, hl₁, hn₁⟩ := hf₁ s
    -- `l₀ - l₁ ∈ N`; split it as `m₀ + m₁` with `m₀ ∈ N ∩ L₀`, `m₁ ∈ N ∩ L₁`
    have hd : l₀ - l₁ ∈ N := by
      have : l₀ - l₁ = (f s - l₁) - (f s - l₀) := by abel
      rw [this]; exact sub_mem hn₁ hn₀
    obtain ⟨m₀, m₁, hm, hm₀, hm₁, hm₀', hm₁'⟩ :=
      exists_split_of_mem_span hsmul h₀.1 h₁.1 hd
    refine ⟨l₀ - m₀, ?_, sub_mem hl₀ hm₀, ?_⟩
    · have : l₀ - m₀ - f s = -(f s - l₀) - m₀ := by abel
      rw [this]; exact sub_mem (neg_mem hn₀) hm₀'
    · have : l₀ - m₀ = l₁ + m₁ := by
        rw [show l₀ - m₀ = (l₀ - l₁) + l₁ - m₀ by abel, hm]; abel
      rw [this]; exact add_mem hl₁ hm₁
  choose y hyN hy₀ hy₁ using hy
  have hNK : ∀ s, y s - f s ∈ Submodule.span 𝕂 (Set.range g) := fun s ↦
    mem_span_field_of_mem_span_laurent hsmul (hyN s)
  refine ⟨y, hyN, ?_, ?_⟩
  · exact h₀.sumElim _ (fun i ↦ (Submodule.restrictScalars_mem _ _ _).2
      (Submodule.subset_span (Set.mem_range_self i))) hy₀
      (residueIndependent_mod_of_sub_mem _ hNK hr₀)
  · exact h₁.sumElim _ (fun i ↦ (Submodule.restrictScalars_mem _ _ _).2
      (Submodule.subset_span (Set.mem_range_self i))) hy₁
      (residueIndependent_mod_of_sub_mem _ hNK hr₁)

/-- A vector of the `𝒜`-span of a family with independent residues on both sides that lies in
`v⁻¹L₀ ∩ L₁` vanishes ([Kas91] Lemma 7.1.1 (i): `M ∩ qL₀ ∩ L_∞ = 0`). -/
theorem balanced_eq_zero_of_mem_span
    (h₀ : ResidueIndependent InfinityLocalRing L₀ InfinityLocalRing.uniformizer g)
    (h₁ : ResidueIndependent LocalRing L₁ localX g) {x : V}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g))
    (hx₀ : x ∈ InfinityLocalRing.uniformizer • L₀) (hx₁ : x ∈ L₁) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
  have hc : (c.sum fun i a ↦ a • g i) = ∑ i ∈ c.support, integralLaurentEval (c i) • g i :=
    Finset.sum_congr rfl fun i _ ↦ hsmul _ _
  rw [hc] at hx₀ hx₁ ⊢
  have h := balanced_coeff_zero h₀ h₁ c.support c hx₀ hx₁
  exact Finset.sum_eq_zero fun i hi ↦ by rw [h i hi, zero_smul]

/-- [Kas91] Lemma 7.3.4, abstract form. If `x, x' ∈ L₀ ∩ L₁` and `x - x' = (v - v⁻¹) y` with `y`
in the `𝒜`-span of a family with independent residues on both sides, then `x = x'`. -/
theorem balanced_eq_of_sub_eq_smul
    (h₀ : ResidueIndependent InfinityLocalRing L₀ InfinityLocalRing.uniformizer g)
    (h₁ : ResidueIndependent LocalRing L₁ localX g) {x x' y : V} (hx₀ : x ∈ L₀) (hx₁ : x ∈ L₁)
    (hx₀' : x' ∈ L₀) (hx₁' : x' ∈ L₁)
    (hy : y ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g))
    (hxy : x - x' = (RatFunc.X - RatFunc.X⁻¹ : 𝕂) • y) : x = x' := by
  have hne : (RatFunc.X - RatFunc.X⁻¹ : 𝕂) ≠ 0 := by
    intro h
    have h' : (RatFunc.X : 𝕂) ^ 2 = 1 := by
      rw [sq]; nth_rewrite 2 [sub_eq_zero.1 h]; exact mul_inv_cancel₀ RatFunc.X_ne_zero
    exact pow_ne_one_of_transcendental' transcendental_ratFunc_X 2 two_pos h'
  have hy' : y = (RatFunc.X - RatFunc.X⁻¹ : 𝕂)⁻¹ • (x - x') := by
    rw [hxy, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hy0 : y = 0 := by
    refine balanced_eq_zero_of_mem_span hsmul h₀ h₁ hy ?_ ?_
    · obtain ⟨u, hu⟩ := exists_inv_X_sub_eq_uniformizer_mul
      rw [hy', ← hu, algebraMap_smul, mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (L₀.smul_mem _ (sub_mem hx₀ hx₀'))
    · obtain ⟨u, hu⟩ := exists_inv_X_sub_eq_localX_mul
      rw [hy', ← hu, algebraMap_smul]
      exact L₁.smul_mem _ (sub_mem hx₁ hx₁')
  rw [hy0, smul_zero, sub_eq_zero] at hxy
  exact hxy

end Balanced

end LieLean.QuantumGroup
