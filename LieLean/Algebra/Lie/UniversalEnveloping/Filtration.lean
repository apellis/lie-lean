/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.PBW
import Mathlib.RingTheory.FilteredAlgebra.Basic

/-!
# The PBW filtration of the universal enveloping algebra

The universal enveloping algebra `U(L)` of a Lie algebra `L` over a commutative ring `R` carries
the (Poincaré–Birkhoff–Witt) filtration `F₀ ⊆ F₁ ⊆ ⋯`, where `Fₙ` is the `R`-span of the products
of at most `n` elements of `ι L`. We define it as `Fₙ = (R·1 + ι L) ^ n` (a power of a submodule
of the algebra `U(L)`).

## Main definitions

* `UniversalEnvelopingAlgebra.filtration R L n`: the submodule `Fₙ` of `U(L)`.
* `UniversalEnvelopingAlgebra.filtrationBasis b n`: for a basis `b` of `L` indexed by a linearly
  ordered type, the basis of `Fₙ` given by the ordered monomials of length at most `n`.

## Main results

* `UniversalEnvelopingAlgebra.filtration_mono`, `one_mem_filtration`, `mul_mem_filtration`,
  `iSup_filtration`: `F` is an exhaustive ring filtration (an instance of Mathlib's
  `IsRingFiltration`).
* `UniversalEnvelopingAlgebra.commutator_mem_filtration`: `[Fₘ, Fₙ] ⊆ F_{m+n-1}`.
* `UniversalEnvelopingAlgebra.map_pbwEquiv_filtration`: the PBW isomorphism
  `U(L) ≃ₗ[R] R[X_i : i ∈ σ]` maps `Fₙ` onto the polynomials of total degree at most `n`.
* `UniversalEnvelopingAlgebra.filtration_eq_span`, `filtrationBasis_apply`: the ordered
  monomials of length at most `n` form a basis of `Fₙ`.

## References

* J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §17.3 (check).
* N. Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.6–2.7 (check).
-/

open MvPolynomial Finsupp Module

noncomputable section

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The PBW filtration of the universal enveloping algebra: `filtration R L n` is the
`R`-span of the products of at most `n` elements of `ι R L`, defined as `(R·1 + ι L) ^ n`. -/
def filtration (n : ℕ) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  (1 ⊔ LinearMap.range (ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L).toLinearMap) ^ n

variable {R L}

theorem filtration_zero : filtration R L 0 = 1 := pow_zero _

theorem filtration_succ (n : ℕ) : filtration R L (n + 1) =
    (1 ⊔ LinearMap.range (ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L).toLinearMap) *
      filtration R L n := pow_succ' _ _

theorem filtration_add (m n : ℕ) :
    filtration R L (m + n) = filtration R L m * filtration R L n := pow_add _ _ _

theorem filtration_mono : Monotone (filtration R L) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [filtration_succ]
  calc filtration R L n = 1 * filtration R L n := (one_mul _).symm
    _ ≤ _ := mul_le_mul_left le_sup_left _

theorem one_mem_filtration (n : ℕ) : (1 : UniversalEnvelopingAlgebra R L) ∈ filtration R L n :=
  filtration_mono (Nat.zero_le n) (by rw [filtration_zero]; exact Submodule.one_le.mp le_rfl)

theorem algebraMap_mem_filtration (r : R) (n : ℕ) :
    algebraMap R (UniversalEnvelopingAlgebra R L) r ∈ filtration R L n := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (one_mem_filtration n)

theorem ι_mem_filtration_one (x : L) : ι R x ∈ filtration R L 1 := by
  rw [filtration, pow_one]
  exact Submodule.mem_sup_right ⟨x, rfl⟩

theorem mul_mem_filtration {m n : ℕ} {x y : UniversalEnvelopingAlgebra R L}
    (hx : x ∈ filtration R L m) (hy : y ∈ filtration R L n) : x * y ∈ filtration R L (m + n) := by
  rw [filtration_add]; exact Submodule.mul_mem_mul hx hy

/-- The PBW filtration is exhaustive. -/
theorem exists_mem_filtration (u : UniversalEnvelopingAlgebra R L) :
    ∃ n, u ∈ filtration R L n := by
  obtain ⟨a, rfl⟩ : ∃ a, mkAlgHom R L a = u := by
    induction u using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r => exact ⟨0, by rw [AlgHom.commutes]; exact algebraMap_mem_filtration r 0⟩
  | ι x => exact ⟨1, ι_mem_filtration_one x⟩
  | add a₁ a₂ h₁ h₂ =>
    obtain ⟨m, hm⟩ := h₁
    obtain ⟨n, hn⟩ := h₂
    rw [map_add]
    exact ⟨max m n, add_mem (filtration_mono (le_max_left m n) hm)
      (filtration_mono (le_max_right m n) hn)⟩
  | mul a₁ a₂ h₁ h₂ =>
    obtain ⟨m, hm⟩ := h₁
    obtain ⟨n, hn⟩ := h₂
    rw [map_mul]
    exact ⟨m + n, mul_mem_filtration hm hn⟩

theorem iSup_filtration : ⨆ n, filtration R L n = ⊤ := by
  refine eq_top_iff.mpr fun u _ ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration u
  exact Submodule.mem_iSup_of_mem n hn

theorem mem_filtration_zero {u : UniversalEnvelopingAlgebra R L} :
    u ∈ filtration R L 0 ↔ ∃ r : R, algebraMap R _ r = u := by
  rw [filtration_zero, Submodule.mem_one]

/-- Elements of `F₁` have commutators with `Fₙ` in `Fₙ`. -/
theorem commutator_mem_filtration_of_mem_one {g u : UniversalEnvelopingAlgebra R L}
    (hg : g ∈ filtration R L 1) {n : ℕ} (hu : u ∈ filtration R L n) :
    g * u - u * g ∈ filtration R L n := by
  rw [filtration, pow_one] at hg
  obtain ⟨y, hy, z, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hg
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hy
  have key : ∀ {i : ℕ} {v : UniversalEnvelopingAlgebra R L}, v ∈ filtration R L i →
      ι R x * v - v * ι R x ∈ filtration R L i := by
    intro i v hv
    induction hv using Submodule.pow_induction_on_left' with
    | algebraMap r' => rw [Algebra.commutes, sub_self]; exact zero_mem _
    | add v₁ v₂ i _ _ h₁ h₂ =>
      rw [mul_add, add_mul, add_sub_add_comm]; exact add_mem h₁ h₂
    | mem_mul g' hg' i v hv ih =>
      obtain ⟨y', hy', z', ⟨x', rfl⟩, rfl⟩ := Submodule.mem_sup.mp hg'
      obtain ⟨r', rfl⟩ := Submodule.mem_one.mp hy'
      have e : ι R x * ((algebraMap R _ r' + (ι R).toLinearMap x') * v) -
          (algebraMap R _ r' + (ι R).toLinearMap x') * v * ι R x =
          ι R ⁅x, x'⁆ * v + (algebraMap R _ r' + (ι R).toLinearMap x') *
            (ι R x * v - v * ι R x) := by
        rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, LieHom.coe_toLinearMap,
          Algebra.algebraMap_eq_smul_one]
        simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_assoc]
        abel
      rw [e, filtration_succ]
      refine add_mem (Submodule.mul_mem_mul (Submodule.mem_sup_right ⟨_, rfl⟩) hv)
        (Submodule.mul_mem_mul hg' ih)
  simpa [add_mul, mul_add, Algebra.commutes, add_sub_add_comm] using key hu

/-- **Commutators drop the filtration degree**: if `a ∈ Fₘ` and `u ∈ Fₙ` then
`a * u - u * a ∈ F_{m + n - 1}`. Consequently the associated graded algebra of `U(L)` is
commutative. See Humphreys, *Introduction to Lie algebras and representation theory*, §17.3
(check), and Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.6 (check). -/
theorem commutator_mem_filtration {m n : ℕ} {a u : UniversalEnvelopingAlgebra R L}
    (ha : a ∈ filtration R L m) (hu : u ∈ filtration R L n) :
    a * u - u * a ∈ filtration R L (m + n - 1) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [Algebra.commutes, sub_self]; exact zero_mem _
  | add a₁ a₂ i _ _ h₁ h₂ => rw [add_mul, mul_add, add_sub_add_comm]; exact add_mem h₁ h₂
  | mem_mul g hg i a ha ih =>
    have hg1 : g ∈ filtration R L 1 := by rwa [filtration, pow_one]
    have e : g * a * u - u * (g * a) = g * (a * u - u * a) + (g * u - u * g) * a := by
      noncomm_ring
    rw [e]
    refine add_mem ?_ (filtration_mono (by omega)
      (mul_mem_filtration (commutator_mem_filtration_of_mem_one hg1 hu) ha))
    rcases Nat.eq_zero_or_pos (i + n) with h | h
    · obtain ⟨r, rfl⟩ := mem_filtration_zero.mp (show a ∈ filtration R L 0 by
        rwa [show i = 0 by omega] at ha)
      rw [Algebra.commutes, sub_self, mul_zero]; exact zero_mem _
    · exact filtration_mono (by omega) (mul_mem_filtration hg1 ih)

/-- The PBW filtration is a ring filtration in the sense of Mathlib's `IsRingFiltration`. -/
instance : IsRingFiltration (filtration R L) (fun n ↦ ⨆ i < n, filtration R L i) where
  mono := filtration_mono
  is_le hij := le_iSup₂_of_le _ hij le_rfl
  is_sup _ _ h := iSup₂_le h
  one_mem := one_mem_filtration 0
  mul_mem _ _ _ _ := mul_mem_filtration

theorem iSup_lt_filtration (n : ℕ) : ⨆ i < n + 1, filtration R L i = filtration R L n :=
  le_antisymm (iSup₂_le fun _ hi ↦ filtration_mono (by omega)) (le_iSup₂_of_le n (by omega) le_rfl)

/-- A product of `k` elements of `ι L` lies in `Fₖ`. -/
theorem list_prod_mem_filtration (l : List L) :
    (l.map (ι R)).prod ∈ filtration R L l.length := by
  induction l with
  | nil => exact one_mem_filtration 0
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, filtration_succ]
    exact Submodule.mul_mem_mul (Submodule.mem_sup_right ⟨x, rfl⟩) ih

section PBW

variable {σ : Type*} [LinearOrder σ]

theorem pbwMonomial_mem_filtration (v : σ → L) (s : σ →₀ ℕ) :
    pbwMonomial R v s ∈ filtration R L s.degree := by
  have := list_prod_mem_filtration (R := R) (((toMultiset s).sort (· ≤ ·)).map v)
  rw [List.map_map, List.length_map, Multiset.length_sort, card_toMultiset] at this
  exact this

open PBW in
/-- **PBW, filtered version**: the PBW isomorphism `U(L) ≃ₗ[R] R[X_i : i ∈ σ]` attached to an
ordered basis of `L` maps `Fₙ` onto the polynomials of total degree at most `n`. See Humphreys,
*Introduction to Lie algebras and representation theory*, §17.4 (check); the statement is part of
the proof of Theorem C there (Lemma A (b)). -/
theorem map_pbwEquiv_filtration (b : Basis σ R L) (n : ℕ) :
    (filtration R L n).map (pbwEquiv b : _ →ₗ[R] MvPolynomial σ R) = restrictTotalDegree σ R n := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [Submodule.mem_comap, Algebra.algebraMap_eq_smul_one, map_smul]
      refine Submodule.smul_mem _ _ ?_
      rw [← pbwMonomial_zero (R := R) b, LinearEquiv.coe_coe, pbwEquiv_pbwMonomial]
      exact z_mem_restrictTotalDegree (by simp)
    | add x y i _ _ hx hy => exact add_mem hx hy
    | mem_mul g hg i x _ ih =>
      obtain ⟨y, hy, z, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hy
      rw [Submodule.mem_comap] at ih ⊢
      have hx : x = phi b (pbwEquiv b x) := ((pbwEquiv b).symm_apply_apply x).symm
      rw [add_mul, Algebra.algebraMap_eq_smul_one, smul_one_mul, map_add, map_smul, hx,
        ← phi_lift, LieHom.coe_toLinearMap, lift_ι_apply, rhoHom_apply]
      refine add_mem (Submodule.smul_mem _ _ (restrictTotalDegree_mono (Nat.le_succ i) ?_)) ?_
      · simpa [← hx] using ih
      · exact (pbwEquiv b).apply_symm_apply _ ▸ rho_mem b i w ih
  · rw [restrictTotalDegree, restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨pbwMonomial R b s, filtration_mono ?_ (pbwMonomial_mem_filtration b s), ?_⟩
    · exact hs
    · simp

theorem mem_filtration_iff_pbwEquiv (b : Basis σ R L) {n : ℕ}
    {u : UniversalEnvelopingAlgebra R L} :
    u ∈ filtration R L n ↔ pbwEquiv b u ∈ restrictTotalDegree σ R n := by
  rw [← map_pbwEquiv_filtration b n]
  refine ⟨fun h ↦ ⟨u, h, rfl⟩, fun ⟨v, hv, e⟩ ↦ ?_⟩
  rwa [← (pbwEquiv b).injective e]

/-- `Fₙ` is spanned by the ordered monomials of length at most `n`. -/
theorem filtration_eq_span (b : Basis σ R L) (n : ℕ) :
    filtration R L n = Submodule.span R (pbwMonomial R b '' {s | s.degree ≤ n}) := by
  apply Submodule.map_injective_of_injective (pbwEquiv b).injective
  rw [map_pbwEquiv_filtration, Submodule.map_span, Set.image_image, restrictTotalDegree,
    restrictSupport_eq_span]
  congr 1
  refine Set.image_congr fun s _ ↦ ?_
  simp

theorem linearIndependent_pbwMonomial_subtype (b : Basis σ R L) (n : ℕ) :
    LinearIndependent R fun s : {s : σ →₀ ℕ // s.degree ≤ n} ↦ pbwMonomial R b s := by
  convert (pbwBasis b).linearIndependent.comp _ Subtype.val_injective
  simp

/-- **PBW, filtered version**: the ordered monomials `pbwMonomial R b s` with `|s| ≤ n` form a
basis of the `n`-th filtered piece `Fₙ` of `U(L)`. See Humphreys, §17.4 (check), and Bourbaki,
Ch. I, §2.7, Theorem 1 (check). -/
def filtrationBasis (b : Basis σ R L) (n : ℕ) :
    Basis {s : σ →₀ ℕ // s.degree ≤ n} R (filtration R L n) :=
  (Basis.span (linearIndependent_pbwMonomial_subtype b n)).map
    (LinearEquiv.ofEq _ _ (by
      rw [filtration_eq_span b n]
      congr 1
      ext u
      simp))

@[simp] theorem filtrationBasis_apply (b : Basis σ R L) (n : ℕ)
    (s : {s : σ →₀ ℕ // s.degree ≤ n}) :
    (filtrationBasis b n s : UniversalEnvelopingAlgebra R L) = pbwMonomial R b s := by
  simp [filtrationBasis, Basis.span_apply]

end PBW

/-- If `L` is a free `R`-module, then so is each piece `Fₙ` of the PBW filtration. -/
instance [Module.Free R L] (n : ℕ) : Module.Free R (filtration R L n) :=
  let : LinearOrder (Module.Free.ChooseBasisIndex R L) := IsWellOrder.linearOrder WellOrderingRel
  .of_basis (filtrationBasis (Module.Free.chooseBasis R L) n)

end UniversalEnvelopingAlgebra
