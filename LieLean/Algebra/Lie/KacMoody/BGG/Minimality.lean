/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG
import LieLean.Algebra.Lie.KacMoody.Shapovalov
import LieLean.Algebra.Lie.Homology.Complex

/-!
# Nilradical coinvariants and minimality of the actual BGG differential

This file proves necessary ingredients for a homological proof of BGG
exactness; it does not assume or claim positive-degree exactness. All arguments are
reconstructed from the existing PBW, highest-weight and BGG APIs.

## Main results

* `boundaries_zero_eq_actionSpan` and `homologyZeroEquivCoinvariants`: the concrete CE
  `H₀(𝔫₋, V)` really is `V / 𝔫₋ V`, naturally in actual coefficient maps.
* `VermaModule.ker_hwCoord_eq_nNegActionSpan`: word generation identifies the kernel of
  highest-weight coordinate with `𝔫₋ M(μ)`.
* `VermaModule.homologyZeroEquiv`: `H₀(𝔫₋, M(μ)) ≃ₗ[K] K` for every weight `μ`.
* `bggDiff_mem_nNegActionSpan`: every actual BGG differential is minimal over `U(𝔫₋)`.
* `homologyZeroMap_bggDiff_eq_zero`: the induced map on actual degree-zero CE homology is zero.

The new minimality argument invokes no Hom dimension theorem: it uses distinct dot-orbit highest
weights and the highest-weight coordinate, so it holds for any GCM and dominant integral Λ.
The general CE/coinvariant bridge does not require characteristic zero.

## Relation to positive-degree exactness

`BGG/Exactness.lean` proves positive-degree exactness for symmetrizable GCM and
finite-dimensional Cartan space by the independent lowering-operator/Casimir route.
`BGG/Syzygy.lean` detects cycles by simple-ascent coordinates, `BGG/Integrable.lean` proves
local lowering-operator nilpotence modulo actual boundaries, and `BGG/Casimir.lean`
annihilates the resulting actual homology. This file does not import or use that result.

The alternative Garland–Lepowsky/dimension-shifting/Nakayama route was not needed.
Its supporting ingredients remain useful: Verma and BGG-term CE acyclicity, coefficient
long exact sequences and weight-space connecting maps, and bounded-weight Nakayama.
Minimality alone does not detect a prescribed generator modulo the action on the syzygy:
membership in `𝔫₋ Cₖ` is different from membership in `𝔫₋ ker(dₖ₋₁)`.
Neither Euler characteristics nor matching Betti numbers are used to infer exactness.
Positive-degree CE acyclicity does not imply the degree-zero vanishing assumption in
the general dimension-shifting equivalence.

## References

Arguments reconstructed from the definitions and existing repository proofs. Context:
Garland-Lepowsky, Invent. Math. 34 (1976), 37-76, and Kumar, Kac-Moody groups,
Ch. 3 / §9.1.
-/

open Module LieModule CoxeterSystem DirectSum
noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra
namespace BGGMinimality

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The linear span of the negative-nilradical action, whose quotient is coinvariants. -/
def nNegActionSpan (V : Type*) [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] : Submodule K V :=
  Submodule.span K {v | ∃ x ∈ nNeg P, ∃ m : V, ⁅x, m⁆ = v}

omit [CharZero K] in
/-- Every negative-nilradical action lies in the coinvariant relation space. -/
lemma lie_mem_nNegActionSpan {V : Type*} [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    {x : P.KacMoodyAlgebra} (hx : x ∈ nNeg P) (m : V) :
    ⁅x, m⁆ ∈ nNegActionSpan P V :=
  Submodule.subset_span ⟨x, hx, m, rfl⟩

omit [CharZero K] in
/-- The action span is functorial under actual Lie-module maps. -/
lemma map_mem_nNegActionSpan {V U : Type*} [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
    [LieModule K P.KacMoodyAlgebra U] (φ : V →ₗ⁅K,P.KacMoodyAlgebra⁆ U)
    {v : V} (hv : v ∈ nNegActionSpan P V) : φ v ∈ nNegActionSpan P U := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, m, rfl⟩ := hv
    rw [LieModuleHom.map_lie]
    exact lie_mem_nNegActionSpan P hx _
  | zero => rw [map_zero]; exact zero_mem _
  | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
  | smul c v _ hv => rw [map_smul]; exact Submodule.smul_mem _ c hv

section HomologyZero

open LieModule.ChevalleyEilenberg TensorProduct ExteriorAlgebra

variable (V : Type*) [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]

/-- The canonical identification of a vector with its degree-zero CE chain. -/
abbrev oneTmul : V →ₗ[K] ExteriorAlgebra K (nNeg P) ⊗[K] V :=
  TensorProduct.mk K (ExteriorAlgebra K (nNeg P)) V 1

omit [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] in
lemma oneTmul_injective : Function.Injective (oneTmul P V) := by
  refine Function.LeftInverse.injective
    (g := (TensorProduct.lid K V).toLinearMap ∘ₗ LinearMap.rTensor V
      (algebraMapInv : ExteriorAlgebra K (nNeg P) →ₐ[K] K).toLinearMap) fun v ↦ ?_
  simp [oneTmul]

omit [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] in
lemma chainsIn_zero_le_range_oneTmul :
    chainsIn K (nNeg P) V 0 ≤ LinearMap.range (oneTmul P V) :=
  chainsIn_zero_le fun v ↦ ⟨v, rfl⟩

omit [CharZero K] in
/-- Degree-zero CE boundaries are exactly the nilradical action span.
This identifies the concrete CE homology API with coinvariants, without a resolution. -/
theorem boundaries_zero_eq_actionSpan :
    boundaries K (nNeg P) V 0 = (nNegActionSpan P V).map (oneTmul P V) := by
  apply le_antisymm
  · rw [boundaries, Submodule.map_le_iff_le_comap]
    apply chainsIn_succ_le
    intro y c hc
    obtain ⟨m, rfl⟩ := chainsIn_zero_le_range_oneTmul P V hc
    change diff K (nNeg P) V (wedge K (nNeg P) V y (1 ⊗ₜ m)) ∈
      (nNegActionSpan P V).map (oneTmul P V)
    rw [wedge_tmul, mul_one, diff_ι_tmul, LieSubalgebra.coe_bracket_of_module]
    exact neg_mem (Submodule.mem_map.mpr ⟨⁅(y : P.KacMoodyAlgebra), m⁆,
      lie_mem_nNegActionSpan P y.2 m, rfl⟩)
  · rintro _ ⟨m, hm, rfl⟩
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨x, hx, v, rfl⟩ := hm
      let y : nNeg P := ⟨x, hx⟩
      refine ⟨-(ExteriorAlgebra.ι K y ⊗ₜ v), neg_mem (tmul_mem_chainsIn ?_ v), ?_⟩
      · rw [exteriorPower, pow_one]
        exact LinearMap.mem_range_self _ y
      · rw [map_neg, diff_ι_tmul, neg_neg, LieSubalgebra.coe_bracket_of_module]
        rfl
    | zero => rw [map_zero]; exact zero_mem _
    | add m n _ _ hm hn => rw [map_add]; exact add_mem hm hn
    | smul c m _ hm => rw [map_smul]; exact Submodule.smul_mem _ c hm

/-- The class of a vector in the actual zeroth CE homology of `𝔫₋`. -/
def toHomologyZero : V →ₗ[K] homology K (nNeg P) V 0 :=
  (((boundaries K (nNeg P) V 0).mkQ).comp (oneTmul P V)).codRestrict _ fun m ↦
    ⟨oneTmul P V m, ⟨one_tmul_mem_chainsIn m, diff_one_tmul m⟩, rfl⟩

set_option maxHeartbeats 800000 in
-- Unfolding the nested range/submodule representation of degree-zero homology exceeds default fuel.
omit [CharZero K] in
lemma toHomologyZero_surjective : Function.Surjective (toHomologyZero P V) := by
  rintro ⟨c, t, ht, rfl⟩
  obtain ⟨m, rfl⟩ := chainsIn_zero_le_range_oneTmul P V ht.1
  exact ⟨m, rfl⟩

omit [CharZero K] in
/-- The kernel of the canonical map to CE homology is exactly `𝔫₋ V`. -/
theorem ker_toHomologyZero : (toHomologyZero P V).ker = nNegActionSpan P V := by
  ext m
  change (⟨_, _⟩ : homology K (nNeg P) V 0) = 0 ↔ _
  rw [Subtype.ext_iff]
  change Submodule.Quotient.mk (oneTmul P V m) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, boundaries_zero_eq_actionSpan]
  constructor
  · rintro ⟨v, hv, hvm⟩
    exact oneTmul_injective P V hvm ▸ hv
  · intro hm
    exact ⟨m, hm, rfl⟩

/-- `H₀(𝔫₋, V)` is canonically the quotient by the nilradical action span. -/
def homologyZeroEquivCoinvariants :
    homology K (nNeg P) V 0 ≃ₗ[K] (V ⧸ nNegActionSpan P V) := by
  rw [← ker_toHomologyZero]
  exact (LinearMap.quotKerEquivOfSurjective (toHomologyZero P V)
    (toHomologyZero_surjective P V)).symm

variable {V} {U : Type*} [AddCommGroup U] [Module K U]
  [LieRingModule P.KacMoodyAlgebra U] [LieModule K P.KacMoodyAlgebra U]

/-- Restriction of a coefficient map to the negative nilradical. -/
def restrictNNeg (φ : V →ₗ⁅K,P.KacMoodyAlgebra⁆ U) : V →ₗ⁅K,nNeg P⁆ U :=
  { φ.toLinearMap with
    map_lie' := fun {x m} ↦ φ.map_lie (x : P.KacMoodyAlgebra) m }

omit [CharZero K] in
/-- Naturality of the canonical map from vectors to actual degree-zero CE classes. -/
lemma homologyMap_toHomologyZero (φ : V →ₗ⁅K,P.KacMoodyAlgebra⁆ U) (v : V) :
    homologyMap K (nNeg P) 0 (restrictNNeg P φ) (toHomologyZero P V v) =
      toHomologyZero P U (φ v) := by
  apply Subtype.ext
  change Submodule.Quotient.mk
    ((φ.toLinearMap).lTensor (ExteriorAlgebra K (nNeg P)) (1 ⊗ₜ v)) = _
  rw [LinearMap.lTensor_tmul]
  rfl

set_option maxHeartbeats 2000000 in
-- Definitional equality through the coefficient restriction and CE quotient exceeds default fuel.
omit [CharZero K] in
lemma homologyZeroMap_eq_zero_of_range_le (φ : V →ₗ⁅K,P.KacMoodyAlgebra⁆ U)
    (hφ : ∀ v, φ v ∈ nNegActionSpan P U) :
    homologyMap K (nNeg P) 0 (restrictNNeg P φ) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, hv⟩ := toHomologyZero_surjective P V x
  have hz : toHomologyZero P U (φ v) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [ker_toHomologyZero]
    exact hφ v
  exact (congrArg (homologyMap K (nNeg P) 0 (restrictNNeg P φ)) hv).symm.trans
    ((homologyMap_toHomologyZero P φ v).trans hz)

end HomologyZero

namespace VermaModule

variable (μ : Dual K H)

/-- The kernel of highest-weight coordinate is exactly `𝔫₋ M(μ)`.
The reverse inclusion is proved by word generation, not by an exactness assumption. -/
theorem ker_hwCoord_eq_nNegActionSpan :
    (VermaModule.hwCoord P μ).ker = nNegActionSpan P (VermaModule P μ) := by
  apply le_antisymm
  · have hdecomp : ∀ m : VermaModule P μ,
        m - VermaModule.hwCoord P μ m • VermaModule.hwv P μ ∈
          nNegActionSpan P (VermaModule P μ) := by
      intro m
      have hm : m ∈ VermaModule.fWordSpan P μ := by
        rw [VermaModule.span_fWord_smul_eq_top]; trivial
      induction hm using Submodule.span_induction with
      | mem m hm =>
        obtain ⟨w, rfl⟩ := hm
        cases w with
        | nil => simp
        | cons i w =>
          dsimp only
          rw [VermaModule.fWord_smul_cons,
            VermaModule.hwCoord_lie_of_mem_nNeg P μ (f_mem_nNeg P i), zero_smul, sub_zero]
          exact lie_mem_nNegActionSpan P (f_mem_nNeg P i) _
      | zero => simp
      | add m n _ _ hm hn =>
        simpa only [map_add, add_smul, add_sub_add_comm] using add_mem hm hn
      | smul c m _ hm =>
        simpa only [map_smul, smul_sub, smul_smul, smul_eq_mul] using
          (Submodule.smul_mem (nNegActionSpan P (VermaModule P μ)) c hm)
    intro m hm
    simpa only [LinearMap.mem_ker.mp hm, zero_smul, sub_zero] using hdecomp m
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, m, rfl⟩
    exact VermaModule.hwCoord_lie_of_mem_nNeg P μ hx m

/-- Every Verma module has one-dimensional negative-nilradical coinvariants,
canonically identified with the highest-weight coordinate. -/
def coinvariantsEquiv :
    ((VermaModule P μ) ⧸ nNegActionSpan P (VermaModule P μ)) ≃ₗ[K] K := by
  rw [← ker_hwCoord_eq_nNegActionSpan]
  exact LinearMap.quotKerEquivOfSurjective (VermaModule.hwCoord P μ) (fun c ↦
    ⟨c • VermaModule.hwv P μ, by simp⟩)

/-- **Actual CE homology in degree zero**: `H₀(𝔫₋, M(μ)) ≃ K` for every weight.
Unlike the irreducible-module theorem, this needs no character or GL argument. -/
def homologyZeroEquiv :
    LieModule.ChevalleyEilenberg.homology K (nNeg P) (VermaModule P μ) 0 ≃ₗ[K] K :=
  homologyZeroEquivCoinvariants P (VermaModule P μ) ≪≫ₗ coinvariantsEquiv P μ

/-- `dim H₀(𝔫₋, M(μ)) = 1`. -/
theorem finrank_homologyZero :
    finrank K (LieModule.ChevalleyEilenberg.homology K (nNeg P) (VermaModule P μ) 0) = 1 := by
  rw [(homologyZeroEquiv P μ).finrank_eq, Module.finrank_self]

/-- A map between distinct highest weights has zero map on nilradical coinvariants.
This holds for arbitrary highest weights and does not use a Hom dimension bound. -/
theorem hom_mem_nNegActionSpan {ν : Dual K H} (hνμ : ν ≠ μ)
    (φ : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ)
    (m : VermaModule P ν) : φ m ∈ nNegActionSpan P (VermaModule P μ) := by
  rw [← ker_hwCoord_eq_nNegActionSpan, LinearMap.mem_ker]
  have heq := VermaModule.eq_smul_hwCoord P ν
    ((VermaModule.hwCoord P μ).comp φ.toLinearMap) (fun i m ↦ by
      change VermaModule.hwCoord P μ (φ ⁅f P i, m⁆) = 0
      rw [LieModuleHom.map_lie]
      exact VermaModule.hwCoord_lie_of_mem_nNeg P μ (f_mem_nNeg P i) _)
  have hz : VermaModule.hwCoord P μ (φ (VermaModule.hwv P ν)) = 0 := by
    exact VermaModule.hwCoord_eq_zero_of_ne P μ
      (mem_primitiveVectors.mp (VermaModule.map_hwv_mem_primitiveVectors P φ)).1 hνμ
  have := LinearMap.congr_fun heq m
  change VermaModule.hwCoord P μ (φ m) =
    VermaModule.hwCoord P μ (φ (VermaModule.hwv P ν)) * VermaModule.hwCoord P ν m at this
  simpa only [hz, zero_mul] using this

end VermaModule

variable (hA : A.IsGeneralizedCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

/-- **Minimality of the actual BGG differential**: its image is contained in
`𝔫₋ C_k`. This is a theorem about the constructed `bggDiff`, not an assumed resolution. -/
theorem bggDiff_mem_nNegActionSpan (k : ℕ) (x : BGGTerm P hA Λ (k + 1)) :
    bggDiff P hA hΛ k x ∈ nNegActionSpan P (BGGTerm P hA Λ k) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | of w' x =>
    rw [bggDiff_of]
    apply Submodule.sum_mem
    intro w hw
    apply Submodule.smul_mem
    apply map_mem_nNegActionSpan P (DirectSum.lieModuleOf K _ P.KacMoodyAlgebra _ w)
    apply VermaModule.hom_mem_nNegActionSpan P _ _ (bggMap P hA hΛ w' w)
    intro heq
    have hww := weylDot_injective P hA hΛ heq
    have hlen := congrArg (P.coxeterSystem hA).length hww
    rw [w'.2, w.2] at hlen
    omega

/-- **The BGG differential induces zero on actual nilradical CE homology in degree zero**.
This is the minimality condition required by a GL/dimension-shifting proof. -/
theorem homologyZeroMap_bggDiff_eq_zero (k : ℕ) :
    LieModule.ChevalleyEilenberg.homologyMap K (nNeg P) 0
      (restrictNNeg P (bggDiff P hA hΛ k)) = 0 := by
  exact homologyZeroMap_eq_zero_of_range_le P (bggDiff P hA hΛ k)
    (bggDiff_mem_nNegActionSpan P hA hΛ k)


end BGGMinimality
end Matrix.Realization.KacMoodyAlgebra
