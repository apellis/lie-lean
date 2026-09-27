/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Projectivity
import LieLean.Algebra.Lie.KacMoody.BGG.Verma

/-!
# Uniqueness of homomorphisms between the Verma modules `M(w · Λ)`

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a generalized Cartan matrix over a field `K` of
characteristic zero and `Λ` a dominant integral weight. We prove that
`dim Hom(M(w' · Λ), M(w · Λ)) ≤ 1` for all `w, w' ∈ W`, with equality if `w ≤ w'` in the Bruhat
order (by Verma's theorem, `VermaModule.exists_injective_of_bruhatLE`). This is the uniqueness
statement used to define the maps of the BGG resolution ([HumO] Thm. 4.2 (b) (check), for
finite-dimensional semisimple `𝔤`; [Kum] §9.1 (check) in Kac–Moody generality). Humphreys' proof
uses that `U(𝔫₋)` is an Ore domain, which fails for general Kac–Moody algebras; we give a different
argument, reconstructed by us, based on the `𝔰𝔩₂`-projectivity of Verma modules
(`LieLean.Algebra.Lie.KacMoody.BGG.Projectivity`).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_hom_reflection_reflection`:
  **Verma's lemma, bijective form**: if `⟨λ, αᵢ^∨⟩ ∈ ℕ` and `⟨μ + ρ, αᵢ^∨⟩ ∈ ℤ_{>0}`, then
  `dim Hom(M(rᵢ · μ), M(rᵢ · λ)) = dim Hom(M(μ), M(λ))`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_hom_weylDot_self`:
  `dim Hom(M(w · Λ), M(Λ)) = 1`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_hom_weylDot_le_one`:
  `dim Hom(M(w' · Λ), M(w · Λ)) ≤ 1`; `finrank_hom_weylDot_eq_one`: `= 1` if `w ≤ w'`.

## Proof

For `⟨λ, αᵢ^∨⟩ ∈ ℕ` and `⟨μ + ρ, αᵢ^∨⟩ = n > 0`: `Hom(M(rᵢ · μ), M(rᵢ · λ)) ≅ Hom(M(rᵢ · μ), M(λ))`
since the primitive vectors of `M(λ)` of weight `rᵢ · μ` lie in `M(rᵢ · λ)`
(`VermaModule.bijective_reflectionHom_comp`), and `x ↦ fᵢⁿ x` is a bijection from the primitive
vectors of weight `μ` of `M(λ)` onto those of weight `rᵢ · μ = μ - n αᵢ`: it is injective since
`U(𝔫₋)` is a domain, and surjective by the `𝔰𝔩₂`-projectivity of `M(λ)`
(`VermaModule.exists_mem_primitiveVectors_of_mem`). Then `dim Hom(M(w · Λ), M(Λ))` is computed by
induction on `ℓ(w)`: for a left descent `s` of `w`,
`Hom(M(w · Λ), M(Λ)) ≅ Hom(M(w · Λ), M(s · Λ)) ≅ Hom(M(sw · Λ), M(Λ))`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.2 (check).
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §9.1 (check).
-/

open Module LieModule CoxeterSystem

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

namespace VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsGeneralizedCartan)

instance finiteDimensional_primitiveVectors (Λ μ : Dual K H) :
    FiniteDimensional K (primitiveVectors P (VermaModule P Λ) μ) :=
  have := finiteDimensional_weightSpace P Λ μ
  Submodule.finiteDimensional_of_le inf_le_left

instance finiteDimensional_hom (Λ μ : Dual K H) :
    FiniteDimensional K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) :=
  LinearEquiv.finiteDimensional (homEquiv P (VermaModule P Λ) μ).symm

include hA in
/-- **Verma's lemma, bijective form** (reconstructed by us; cf. [HumO] Lemma 4.6 (check)): if
`⟨λ, αᵢ^∨⟩ ∈ ℕ` and `⟨μ + ρ, αᵢ^∨⟩ = n` is a positive integer, then
`dim Hom(M(rᵢ · μ), M(rᵢ · λ)) = dim Hom(M(μ), M(λ))`. -/
theorem finrank_hom_reflection_reflection {Λ μ : Dual K H} {i : ι} {d n : ℕ}
    (hd : Λ (P.coroot i) = d) (hn0 : 0 < n) (hn : (μ + P.rho) (P.coroot i) = n) :
    finrank K (VermaModule P (P.reflection hA i (μ + P.rho) - P.rho) →ₗ⁅K,P.KacMoodyAlgebra⁆
        VermaModule P (P.reflection hA i (Λ + P.rho) - P.rho)) =
      finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) := by
  have hΛn : (Λ + P.rho) (P.coroot i) = ((d + 1 : ℕ) : K) := by
    rw [LinearMap.add_apply, hd, rho_coroot]; push_cast; ring
  have hμn : μ (P.coroot i) = (n : K) - 1 := by
    rw [LinearMap.add_apply, rho_coroot] at hn; linear_combination hn
  have hν : (P.reflection hA i (μ + P.rho) - P.rho) (P.coroot i) = -((n : K) + 1) := by
    rw [P.reflection_add_rho_sub_rho hA hn, LinearMap.sub_apply, LinearMap.smul_apply,
      root_coroot_self P hA, hμn, nsmul_eq_mul]
    ring
  rw [finrank_hom_reflection_eq (hA := hA) (hn0 := Nat.succ_pos d) (hn := hΛn) (fun m hm ↦ by
    rw [hν] at hm
    have : ((m + n + 1 : ℕ) : K) = 0 := by push_cast; linear_combination -hm
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)), finrank_hom, finrank_hom]
  -- the bijection `x ↦ fᵢⁿ x` between primitive vectors
  rw [P.reflection_add_rho_sub_rho hA hn]
  let T : primitiveVectors P (VermaModule P Λ) μ →ₗ[K]
      primitiveVectors P (VermaModule P Λ) (μ - n • P.root i) :=
    ((toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n).restrict fun x hx ↦
      toEnd_f_pow_mem_primitiveVectors_of_mem i Λ (by rw [hμn]; ring) hx hA)
  have hT : Function.Bijective T := by
    refine ⟨fun x y hxy ↦ Subtype.ext (toEnd_f_pow_injective i Λ n
      (congrArg Subtype.val hxy)), fun y ↦ ?_⟩
    have hν' : (μ - n • P.root i) (P.coroot i) = -((n : K) + 1) := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, root_coroot_self P hA, hμn, nsmul_eq_mul]
      ring
    obtain ⟨x, hx, hxy⟩ := exists_mem_primitiveVectors_of_mem i Λ hA hd hn0 hν' y.2
    rw [sub_add_cancel] at hx
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (LinearEquiv.ofBijective T hT).finrank_eq.symm

variable {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hA hΛ

/-- `dim Hom(M(w · Λ), M(Λ)) = 1` for `Λ` dominant integral and `w ∈ W` (reconstructed by us). -/
theorem finrank_hom_weylDot_self (w : P.weylGroup hA) :
    finrank K (VermaModule P (P.weylDot hA w Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) = 1 := by
  set cs := P.coxeterSystem hA
  induction hl : cs.length w using Nat.strong_induction_on generalizing w with
  | _ l ih =>
  subst hl
  by_cases hw1 : w = 1
  · subst hw1
    rw [weylDot_one, finrank_hom]
    have : primitiveVectors P (VermaModule P Λ) Λ = K ∙ hwv P Λ := by
      refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (hwv_mem_primitiveVectors P Λ))
      rw [← weightSpace_self]
      exact inf_le_left
    rw [this, finrank_span_singleton (hwv_ne_zero P Λ)]
  obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
  have hsl := (cs.isLeftDescent_iff).mp hs
  set w' := cs.simple s * w
  have hww' : w = cs.simple s * w' := (cs.simple_mul_simple_cancel_left s).symm
  have hw' : ¬cs.IsLeftDescent w' s := by
    rwa [← cs.isLeftDescent_iff_not_isLeftDescent_mul]
  obtain ⟨n, hn0, hn⟩ := P.exists_weylDot_add_rho_coroot_eq hA hΛ hw'
  obtain ⟨d, hd⟩ := hΛ s
  have hΛn : (Λ + P.rho) (P.coroot s) = ((d + 1 : ℕ) : K) := by
    rw [LinearMap.add_apply, hd, rho_coroot]; push_cast; ring
  -- `Hom(M(w · Λ), M(Λ)) ≅ Hom(M(w · Λ), M(s · Λ))`
  have hν : ∀ m : ℕ, (P.weylDot hA w Λ) (P.coroot s) ≠ m := by
    intro m hm
    rw [hww', weylDot_simple_mul, LinearMap.sub_apply, reflection_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, hn, root_coroot_self P hA, rho_coroot] at hm
    have : ((m + n + 1 : ℕ) : K) = 0 := by push_cast; linear_combination -hm
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)
  rw [← finrank_hom_reflection_eq (hA := hA) (hn0 := Nat.succ_pos d) (hn := hΛn) hν, hww',
    weylDot_simple_mul, finrank_hom_reflection_reflection hA hd hn0 hn]
  exact ih _ (by omega) w' rfl

/-- **Uniqueness of homomorphisms between Verma modules in the BGG resolution**
([HumO] Thm. 4.2 (b) (check), for finite-dimensional semisimple Lie algebras; here for any
Kac–Moody algebra, by a different argument reconstructed by us): for `Λ` dominant integral and
`w, w' ∈ W`, `dim Hom(M(w' · Λ), M(w · Λ)) ≤ 1`. -/
theorem finrank_hom_weylDot_le_one (w w' : P.weylGroup hA) :
    finrank K (VermaModule P (P.weylDot hA w' Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule P (P.weylDot hA w Λ)) ≤ 1 := by
  have := exists_injective_of_bruhatLE hA hΛ ((P.coxeterSystem hA).one_bruhatLE w)
  rw [weylDot_one] at this
  obtain ⟨φ, hφ⟩ := this
  let Φ : (VermaModule P (P.weylDot hA w' Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule P (P.weylDot hA w Λ)) →ₗ[K]
      (VermaModule P (P.weylDot hA w' Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) :=
    { toFun := fun ψ ↦ φ.comp ψ
      map_add' := fun _ _ ↦ LieModuleHom.ext fun _ ↦ map_add φ _ _
      map_smul' := fun _ _ ↦ LieModuleHom.ext fun _ ↦ map_smul φ _ _ }
  have hΦ : Function.Injective Φ := fun ψ ψ' h ↦
    LieModuleHom.ext fun m ↦ hφ (LieModuleHom.congr_fun h m)
  have hle := LinearMap.finrank_le_finrank_of_injective hΦ
  exact hle.trans (finrank_hom_weylDot_self hA hΛ w').le

/-- For `Λ` dominant integral and `w ≤ w'` in the Bruhat order,
`dim Hom(M(w' · Λ), M(w · Λ)) = 1`. -/
theorem finrank_hom_weylDot_eq_one {w w' : P.weylGroup hA}
    (h : (P.coxeterSystem hA).BruhatLE w w') :
    finrank K (VermaModule P (P.weylDot hA w' Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule P (P.weylDot hA w Λ)) = 1 := by
  refine le_antisymm (finrank_hom_weylDot_le_one hA hΛ w w') ?_
  obtain ⟨φ, hφ⟩ := exists_injective_of_bruhatLE hA hΛ h
  refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨φ, fun h0 ↦ hwv_ne_zero P _ (hφ ?_)⟩
  rw [h0, map_zero, _root_.zero_apply]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
