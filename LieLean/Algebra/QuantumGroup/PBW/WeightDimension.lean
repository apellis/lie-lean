/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.GabberKac
import LieLean.Algebra.QuantumGroup.TriangularDecomposition

/-!
# The dimensions of the weight spaces of `U⁺`

Let `U⁺_ν ⊆ U = U_v(𝔤)` be the image of the weight space `'f_ν` (words of weight `ν ∈ ℕ[I]`)
under `x ↦ x⁺` (`θᵢ ↦ Eᵢ`, `QuantumGroup.plusHom`). For `k` of characteristic zero, `I` finite and
`v` transcendental over `ℚ`, the quantum Gabber–Kac theorem (with its dimension count,
`LusztigF.mem_serreSpan_of_mem_radical_and_finrank_serreSpan`) and `U⁺ ≅ 'f ⧸ J`
(`QuantumGroup.plusHom_eq_zero_iff`) give

`dim U⁺_ν = #{words of weight ν} - dim Z_ν`,

where `Z_ν ⊆ ℚ⟨θ⟩` is the span of the products `a sᵢⱼ b` of weight `ν` with the *classical*
Serre elements `sᵢⱼ = Σ (-1)^r (m choose r) θᵢ^{m-r} θⱼ θᵢ^r` (`m = 1 - aᵢⱼ`). The right-hand
side is `dim U(𝔫)_ν` for the classical Kac–Moody algebra (Gabber–Kac, [Kac] Thm. 9.11); in
particular `dim U⁺_ν` does not depend on `v` (transcendental) or on `k`
(`QuantumGroup.finrank_plusWeightSpace`, `QuantumGroup.finrank_plusWeightSpace_eq`).

This is the dimension input for the PBW theorem ([Jan] 8.24, [Lus] 40.2.1–40.2.2):
ordered monomials in the root vectors of weight `ν` span `U⁺_ν` iff they are linearly independent
as soon as their number is `dim U⁺_ν`.

## Main definitions / results

* `QuantumGroup.plusWeightSpace`: `U⁺_ν`.
* `QuantumGroup.ker_plusHom_inf_weightSpace`: `ker(x ↦ x⁺) ∩ 'f_ν` is the span of the quantum
  Serre products of weight `ν`.
* `QuantumGroup.finrank_plusWeightSpace`: the dimension formula above.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, 33.1.3, 40.2.1–40.2.2.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 4.21, 8.24.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Thm. 9.11.
-/

noncomputable section

namespace QuantumGroup

open LusztigF Module

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- The weight space `U⁺_ν`: the image of the words of weight `ν` under `θᵢ ↦ Eᵢ`. -/
def plusWeightSpace (ν : I →₀ ℕ) : Submodule k (QuantumGroup R v) :=
  (weightSpace k ν).map (plusHom R v).toLinearMap

theorem plusHom_mem_plusWeightSpace {ν : I →₀ ℕ} {x : LusztigF k I}
    (hx : x ∈ weightSpace k ν) : plusHom R v x ∈ plusWeightSpace R v ν :=
  Submodule.mem_map_of_mem hx

variable {R v} [CharZero k] [NeZero v]

/-- The kernel of `x ↦ x⁺` on the words of weight `ν` is the span of the quantum Serre products
of weight `ν`, for `v` transcendental. -/
theorem ker_plusHom_inf_weightSpace [Finite I] (hv : Transcendental ℚ v) (ν : I →₀ ℕ)
    {x : LusztigF k I} (hx : x ∈ weightSpace k ν) :
    plusHom R v x = 0 ↔ x ∈ serreSpan D (fun i ↦ v ^ D.d i) ν := by
  have hv0 := ne_zero_of_transcendental hv
  have hvn : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 := fun _ hn ↦ pow_ne_one_of_transcendental hv hn
  rw [plusHom_eq_zero_iff R v hvn]
  exact ⟨fun h ↦ (mem_serreSpan_of_mem_radical_and_finrank_serreSpan D hv ν).1 x
    (serreIdeal_le_radical hv0 hvn h) hx, serreSpan_le_serreIdeal D hv0 hvn⟩

/-- **The dimension of `U⁺_ν`** ([Lus] 33.1.3): for `v` transcendental over
`ℚ`, `dim U⁺_ν + dim Z_ν = #{words of weight ν}`, where `Z_ν ⊆ ℚ⟨θ⟩` is the span of the classical
Serre products of weight `ν`. -/
theorem finrank_plusWeightSpace [Finite I] (hv : Transcendental ℚ v) (ν : I →₀ ℕ) :
    finrank k (plusWeightSpace R v ν) + finrank ℚ (serreSpan D (fun _ ↦ (1 : ℚ)) ν) =
      Fintype.card (Words ν) := by
  set V := weightSpace k ν
  set f := (plusHom R v).toLinearMap.domRestrict V
  have hrange : LinearMap.range f = plusWeightSpace R v ν := by
    rw [LinearMap.range_domRestrict]; rfl
  have hker : LinearMap.ker f = (serreSpan D (fun i ↦ v ^ D.d i) ν).comap V.subtype := by
    ext y
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    exact ker_plusHom_inf_weightSpace hv ν y.2
  have hSer : finrank k ((serreSpan D (fun i ↦ v ^ D.d i) ν).comap V.subtype) =
      finrank k (serreSpan D (fun i ↦ v ^ D.d i) ν) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      inf_eq_right.2 (serreSpan_le_weightSpace D _ ν)]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, hSer, finrank_weightSpace,
    (mem_serreSpan_of_mem_radical_and_finrank_serreSpan D hv ν).2] at hrn
  exact hrn

/-- **`dim U⁺_ν` does not depend on the parameter**: for two fields of characteristic zero and
parameters transcendental over `ℚ`, the weight spaces `U⁺_ν` have the same dimension. -/
theorem finrank_plusWeightSpace_eq [Finite I] (hv : Transcendental ℚ v) {k' Y' : Type*}
    [Field k'] [CharZero k'] [AddCommGroup Y'] (R' : D.RootDatum Y') {v' : k'} [NeZero v']
    (hv' : Transcendental ℚ v') (ν : I →₀ ℕ) :
    finrank k (plusWeightSpace R v ν) = finrank k' (plusWeightSpace R' v' ν) := by
  have h := finrank_plusWeightSpace (R := R) hv ν
  have h' := finrank_plusWeightSpace (R := R') hv' ν
  omega

end QuantumGroup
