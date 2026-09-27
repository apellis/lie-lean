/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Parabolic
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Properties
import LieLean.GroupTheory.Coxeter.Longest

/-!
# Parabolic and ordinary Kazhdan–Lusztig polynomials

We relate Deodhar's parabolic Kazhdan–Lusztig polynomials `P^J_{d',d}`
(`IwahoriHeckeAlgebra.parabolicKLPoly`, for the modules `𝓗 ⊗_{𝓗_J} sgn` and `𝓗 ⊗_{𝓗_J} ind`)
to the ordinary Kazhdan–Lusztig polynomials `P_{y,w}` (`IwahoriHeckeAlgebra.klPoly`), following
[Deo] Prop. 3.4 (check):

* **The sign module, any `J`** (`parabolicKLPoly_sgn`): for `d', d ∈ W^J`,
  ```
    P^{J,-1}_{d',d} = Σ_{z ∈ W_J, d'z ≤ d} (-1)^{ℓ(z)} P_{d'z, d}.
  ```
  Proof: the projection `𝓗 → 𝓗 ⊗_{𝓗_J} sgn`, `h ↦ h ⊗ 1`, commutes with the bar involutions,
  so the image of `C'_d` is bar invariant; since `T_{d'z} ⊗ 1 = (-1)^{ℓ(z)} m_{d'}`, its
  coefficients are the alternating sums above, and the degree bounds for the `P_{y,d}` show that
  it has the normalization of `C^J_d`.
* **The index module, `W_J` finite** (`parabolicKLPoly_ind`): with `w_J` the longest element of
  `W_J`,
  ```
    P^{J,q}_{d',d} = P_{d' w_J, d w_J}.
  ```
  Proof: `T_s C'_{w_J} = q C'_{w_J}` for `s ∈ J`, so `h ⊗ 1 ↦ h C'_{w_J}` is a well defined map
  `𝓗 ⊗_{𝓗_J} ind → 𝓗` commuting with the bar involutions (`parabolicLift`). Since
  `C'_{w_J} = v^{-ℓ(w_J)} Σ_{z ∈ W_J} T_z` (`klPoly_parabolicLongestElement_of_mem`), the image of
  `C^J_d` has the normalization of `C'_{d w_J}`, so it is `C'_{d w_J}`
  (`parabolicLift_parabolicKLBasis`), and comparing coefficients gives the formula.
* **`J = ∅`** (`parabolicKLPoly_sgn_empty`, `parabolicKLPoly_ind_empty`): the parabolic
  polynomials are the ordinary ones.

We did not consult [Deo]; the arguments above are reconstructions of the standard ones.

## Main results

* `IwahoriHeckeAlgebra.mk_klBasis_eq_parabolicKLBasis_sgn`, `parabolicKLPoly_sgn`.
* `IwahoriHeckeAlgebra.parabolicLift_parabolicKLBasis`, `parabolicKLPoly_ind`.
* `IwahoriHeckeAlgebra.parabolicKLPoly_sgn_empty`, `parabolicKLPoly_ind_empty`.
* `IwahoriHeckeAlgebra.klPoly_parabolicLongestElement_of_mem`: `P_{z, w_J} = 1` for `z ∈ W_J`.

## References

* [Deo] V. Deodhar, *On some geometric aspects of Bruhat orderings II. The parabolic analogue of
  Kazhdan–Lusztig polynomials*, J. Algebra **111** (1987), 483–506.
* [Soe] W. Soergel, *Kazhdan–Lusztig-Polynome und eine Kombinatorik für Kipp-Moduln*,
  Represent. Theory **1** (1997), 37–68, Prop. 3.4 (check).
* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184.
-/

open Finsupp LaurentPolynomial Polynomial Module

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

variable {cs} {J : Set B}

/-- The minimal coset representative of an element of `W^J` is itself. -/
theorem minCosetRep_of_mem {d : W} (hd : d ∈ cs.minCosetReps J) : cs.minCosetRep J d = d :=
  minCosetRep_eq_iff.mpr ⟨hd, by simp⟩

theorem parabolicComponent_of_mem {d : W} (hd : d ∈ cs.minCosetReps J) :
    cs.parabolicComponent J d = 1 := by
  rw [parabolicComponent, minCosetRep_of_mem hd, inv_mul_cancel]

/-- `(d z)^J = d` for `d ∈ W^J`, `z ∈ W_J`. -/
theorem minCosetRep_mul {d z : W} (hd : d ∈ cs.minCosetReps J) (hz : z ∈ cs.parabolicSubgroup J) :
    cs.minCosetRep J (d * z) = d :=
  minCosetRep_eq_iff.mpr ⟨hd, by simpa using hz⟩

/-- An element below an element of `W_J` in the Bruhat order lies in `W_J`. -/
theorem mem_parabolicSubgroup_of_bruhatLE {y w : W} (hw : w ∈ cs.parabolicSubgroup J)
    (h : cs.BruhatLE y w) : y ∈ cs.parabolicSubgroup J := by
  obtain ⟨ω, hω, hJ, rfl⟩ := exists_isReduced_of_mem_parabolicSubgroup hw
  obtain ⟨σ, hσ, rfl⟩ := hω.bruhatLE_iff.mp h
  exact wordProd_mem_parabolicSubgroup fun i hi ↦ hJ i (hσ.subset hi)

theorem minCosetReps_empty : cs.minCosetReps ∅ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ h ↦ h.elim

theorem minCosetRep_empty (y : W) : cs.minCosetRep ∅ y = y :=
  minCosetRep_eq_iff.mpr ⟨by simp [minCosetReps_empty], by simp⟩

section Finite

variable (cs J) [Finite (cs.parabolicSubgroup J)]

/-- The longest element `w_J` of a finite standard parabolic subgroup `W_J`. -/
noncomputable def parabolicLongestElement : W := ((cs.parabolicCoxeterSystem J).longestElement : W)

variable {cs J}

theorem parabolicLongestElement_mem :
    cs.parabolicLongestElement J ∈ cs.parabolicSubgroup J :=
  ((cs.parabolicCoxeterSystem J).longestElement).2

/-- Every element of `W_J` has length at most `ℓ(w_J)`. -/
theorem length_le_length_parabolicLongestElement {z : W} (hz : z ∈ cs.parabolicSubgroup J) :
    ℓ z ≤ ℓ (cs.parabolicLongestElement J) := by
  have := (cs.parabolicCoxeterSystem J).length_le_length_longestElement ⟨z, hz⟩
  rwa [length_parabolicCoxeterSystem, length_parabolicCoxeterSystem] at this

/-- `w_J` is the only element of `W_J` of length `ℓ(w_J)`. -/
theorem eq_parabolicLongestElement {z : W} (hz : z ∈ cs.parabolicSubgroup J)
    (h : ℓ (cs.parabolicLongestElement J) ≤ ℓ z) : z = cs.parabolicLongestElement J := by
  have := (cs.parabolicCoxeterSystem J).eq_longestElement_of_forall_length_le
    (w := ⟨z, hz⟩) fun u ↦ by
      rw [length_parabolicCoxeterSystem, length_parabolicCoxeterSystem]
      exact (length_le_length_parabolicLongestElement u.2).trans h
  exact congrArg Subtype.val this

/-- Every `s ∈ J` is a left descent of `w_J`. -/
theorem length_simple_mul_parabolicLongestElement_lt {j : B} (hj : j ∈ J) :
    ℓ (s j * cs.parabolicLongestElement J) < ℓ (cs.parabolicLongestElement J) := by
  have := (cs.parabolicCoxeterSystem J).isLeftDescent_longestElement ⟨j, hj⟩
  rw [IsLeftDescent, length_parabolicCoxeterSystem, length_parabolicCoxeterSystem,
    Subgroup.coe_mul, coe_parabolicCoxeterSystem_simple] at this
  exact this

end Finite

end CoxeterSystem

namespace IwahoriHeckeAlgebra

open CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

local notation "𝓗" => IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])

variable {cs} {J : Set B}

/-- `[T_y] C'_w ≠ 0` implies `y ≤ w`. -/
theorem support_toFinsupp_klBasis_subset (w : W) :
    (toFinsupp cs _ (klBasis cs w)).support ⊆ (cs.finite_setOf_bruhatLE w).toFinset := by
  intro y hy
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine bruhatLE_of_klPoly_ne_zero cs fun h ↦ Finsupp.mem_support_iff.mp hy ?_
  rw [toFinsupp_klBasis_apply, h, map_zero, mul_zero]

/-! ### The sign module -/

section Sign

variable (J) in
/-- The projection of `C'_d` to `𝓗 ⊗_{𝓗_J} sgn`: `[m_{d'}] (C'_d ⊗ 1)` is
`v^{-ℓ(d)} Σ_{d'z ≤ d} (-1)^{ℓ(z)} P_{d'z,d}(q)`. -/
theorem repr_mk_klBasis_sgn [DecidableEq W] (d' : cs.minCosetReps J) (d : W) :
    (inducedBasis (sgn (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]))).repr
        (Submodule.Quotient.mk (klBasis cs d)) d' =
      LaurentPolynomial.T (-(ℓ d : ℤ)) * aeval (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])
        (∑ y ∈ (cs.finite_setOf_bruhatLE d).toFinset with cs.minCosetRep J y = d',
          (-1) ^ ℓ (cs.parabolicComponent J y) * klPoly cs y d) := by
  rw [repr_mk_apply, Finsupp.sum_of_support_subset _ (support_toFinsupp_klBasis_subset d) _
    (fun _ _ ↦ by rw [zero_mul]), Finset.sum_filter, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [inducedCoeff_T_apply, toFinsupp_klBasis_apply]
  split_ifs
  · rw [sgn_T, length_parabolicCoxeterSystem, map_mul, map_pow, map_neg, map_one]
    ring
  · rw [mul_zero, map_zero, mul_zero]

variable (J) in
/-- **Deodhar's formula for the sign module** ([Deo] Prop. 3.4 (check)): the image `C'_d ⊗ 1` of
the Kazhdan–Lusztig basis element `C'_d`, `d ∈ W^J`, in `𝓗 ⊗_{𝓗_J} sgn` is the parabolic
Kazhdan–Lusztig basis element `C^J_d`. -/
theorem mk_klBasis_eq_parabolicKLBasis_sgn (d : cs.minCosetReps J) :
    (Submodule.Quotient.mk (klBasis cs d) :
        InducedModule (sgn (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]))) =
      parabolicKLBasis (isBarCompatible_sgn (cs.parabolicCoxeterSystem J)) d := by
  classical
  refine eq_parabolicKLBasis _ (by rw [parabolicBar_mk, barL_klBasis]) ?_ fun d' hd' ↦ ?_
  · rw [repr_mk_klBasis_sgn, Finset.sum_eq_single_of_mem (d : W), parabolicComponent_of_mem d.2,
      cs.length_one, pow_zero, one_mul, klPoly_self, map_one, mul_one]
    · simp [minCosetRep_of_mem d.2, cs.bruhatLE_refl]
    · intro y hy hyd
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hy
      exfalso
      have hl := length_eq_length_minCosetRep_add (cs := cs) (J := J) y
      rw [hy.2] at hl
      exact hyd (hy.1.eq_of_length_le (by omega))
  · intro n hn
    rw [repr_mk_klBasis_sgn, ← mul_assoc, ← T_add]
    refine coeff_T_mul_aeval_T_two_eq_zero fun k hk ↦ ?_
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun y hy ↦ ?_
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hy
    have hyd : y ≠ d := by
      rintro rfl
      exact hd' (Subtype.ext (by rw [← hy.2, minCosetRep_of_mem d.2]))
    have hl := length_eq_length_minCosetRep_add (cs := cs) (J := J) y
    rw [hy.2] at hl
    rw [show ((-1 : ℤ[X]) ^ ℓ (cs.parabolicComponent J y)) =
      Polynomial.C ((-1) ^ ℓ (cs.parabolicComponent J y)) by simp, coeff_C_mul,
      coeff_klPoly_eq_zero cs hyd (by omega), mul_zero]

variable (J) in
/-- **Deodhar's formula for the sign module** ([Deo] Prop. 3.4 (check), [Soe] Prop. 3.4
(check)): for `d', d ∈ W^J`,
`P^{J,-1}_{d',d} = Σ_{z ∈ W_J, d'z ≤ d} (-1)^{ℓ(z)} P_{d'z,d}`, where the sum runs over the
`y = d'z ≤ d` with `y^J = d'` and `z = y_J`. -/
theorem parabolicKLPoly_sgn [DecidableEq W] (d' d : cs.minCosetReps J) :
    parabolicKLPoly (isBarCompatible_sgn (cs.parabolicCoxeterSystem J)) d' d =
      ∑ y ∈ (cs.finite_setOf_bruhatLE d).toFinset with cs.minCosetRep J y = d',
        (-1) ^ ℓ (cs.parabolicComponent J y) * klPoly cs y d := by
  refine T_mul_aeval_T_two_injective (-(ℓ d : ℤ)) ?_
  simp only
  rw [← repr_parabolicKLBasis, ← mk_klBasis_eq_parabolicKLBasis_sgn, repr_mk_klBasis_sgn]

/-- For `J = ∅` the parabolic Kazhdan–Lusztig polynomials of the sign module are the ordinary
Kazhdan–Lusztig polynomials. -/
theorem parabolicKLPoly_sgn_empty (d' d : cs.minCosetReps ∅) :
    parabolicKLPoly (isBarCompatible_sgn (cs.parabolicCoxeterSystem ∅)) d' d =
      klPoly cs d' d := by
  classical
  rw [parabolicKLPoly_sgn]
  simp only [minCosetRep_empty, parabolicComponent, inv_mul_cancel, cs.length_one, pow_zero,
    one_mul, Finset.sum_filter, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  split_ifs with h
  · rfl
  · exact (klPoly_eq_zero_of_not_bruhatLE cs h).symm

end Sign

/-! ### The index module -/

section Index

/-- The parabolic Kazhdan–Lusztig polynomials only depend on the representation `χ`. -/
theorem parabolicKLPoly_congr {χ₁ χ₂ : IwahoriHeckeAlgebra (cs.parabolicCoxeterSystem J)
      (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) →ₐ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹]} (e : χ₁ = χ₂)
    (h₁ : IsBarCompatible (cs.parabolicCoxeterSystem J) χ₁)
    (h₂ : IsBarCompatible (cs.parabolicCoxeterSystem J) χ₂) (d' d : cs.minCosetReps J) :
    parabolicKLPoly h₁ d' d = parabolicKLPoly h₂ d' d := by
  subst e
  rfl

/-- For `J = ∅`, `ind = sgn` on the (trivial) Iwahori–Hecke algebra of `W_∅ = 1`. -/
theorem ind_eq_sgn_empty (q : ℤ[T;T⁻¹]) :
    ind (cs.parabolicCoxeterSystem ∅) q = sgn (cs.parabolicCoxeterSystem ∅) q :=
  algHom_ext _ _ fun i ↦ i.2.elim

/-- For `J = ∅` the parabolic Kazhdan–Lusztig polynomials of the index module are the ordinary
Kazhdan–Lusztig polynomials. -/
theorem parabolicKLPoly_ind_empty (d' d : cs.minCosetReps ∅) :
    parabolicKLPoly (isBarCompatible_ind (cs.parabolicCoxeterSystem ∅)) d' d =
      klPoly cs d' d := by
  rw [parabolicKLPoly_congr (ind_eq_sgn_empty _) _ (isBarCompatible_sgn _),
    parabolicKLPoly_sgn_empty]

variable [Finite (cs.parabolicSubgroup J)]

local notation "w_J" => cs.parabolicLongestElement J

/-- `P_{z, w_J} = 1` for `z ∈ W_J` ([KL] (2.3.g) (check)). -/
theorem klPoly_parabolicLongestElement_of_mem {z : W} (hz : z ∈ cs.parabolicSubgroup J) :
    klPoly cs z (w_J) = 1 := by
  have key : ∀ ω : List B, (∀ i ∈ ω, i ∈ J) → klPoly cs (cs.wordProd ω) (w_J) =
      klPoly cs 1 (w_J) := by
    intro ω hω
    induction ω with
    | nil => rw [wordProd_nil]
    | cons i ω ih =>
      rw [wordProd_cons, klPoly_simple_mul_left cs
        (length_simple_mul_parabolicLongestElement_lt (hω i List.mem_cons_self))]
      exact ih fun j hj ↦ hω j (List.mem_cons_of_mem _ hj)
  obtain ⟨ω, hω, rfl⟩ := mem_parabolicSubgroup_iff.mp hz
  obtain ⟨ω', hω', he⟩ := mem_parabolicSubgroup_iff.mp (parabolicLongestElement_mem (cs := cs)
    (J := J))
  rw [key ω hω, ← key ω' hω', he, klPoly_self]

theorem klPoly_parabolicLongestElement_of_not_mem {y : W} (hy : y ∉ cs.parabolicSubgroup J) :
    klPoly cs y (w_J) = 0 :=
  klPoly_eq_zero_of_not_bruhatLE cs fun h ↦
    hy (mem_parabolicSubgroup_of_bruhatLE parabolicLongestElement_mem h)

/-- `h C'_{w_J} = ind(h) C'_{w_J}` for `h ∈ 𝓗_J`. -/
theorem parabolicHom_mul_klBasis_parabolicLongestElement
    (h : IwahoriHeckeAlgebra (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])) :
    parabolicHom cs _ J h * klBasis cs (w_J) =
      ind (cs.parabolicCoxeterSystem J) _ h • klBasis cs (w_J) := by
  induction h using induction_on _ _ with
  | T v =>
    induction v using (cs.parabolicCoxeterSystem J).induction_simple_mul with
    | one => rw [T_one, map_one, map_one, one_mul, one_smul]
    | simple_mul v j hlt ih =>
      rw [← T_simple_mul_T_of_lt _ _ hlt, map_mul, map_mul, mul_assoc, ih, mul_smul_comm,
        parabolicHom_T, coe_parabolicCoxeterSystem_simple,
        T_simple_mul_klBasis cs (length_simple_mul_parabolicLongestElement_lt j.2), smul_smul,
        ind_T_simple, mul_comm]
  | add x y hx hy => rw [map_add, add_mul, hx, hy, map_add, add_smul]
  | smul a x hx => rw [_root_.map_smul, smul_mul_assoc, hx, _root_.map_smul, smul_eq_mul,
      mul_smul]

variable (cs J) in
/-- The `𝓗`-linear map `𝓗 ⊗_{𝓗_J} ind → 𝓗`, `h ⊗ 1 ↦ h C'_{w_J}`, for `W_J` finite. -/
noncomputable def parabolicLift :
    InducedModule (ind (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])) →ₗ[𝓗]
      𝓗 :=
  Submodule.liftQ _ (LinearMap.toSpanSingleton 𝓗 𝓗 (klBasis cs (w_J))) <| by
    rw [inducedIdeal, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul,
      sub_mul, parabolicHom_mul_klBasis_parabolicLongestElement, ← Algebra.smul_def, sub_self]

theorem parabolicLift_mk (x : 𝓗) :
    parabolicLift cs J (Submodule.Quotient.mk x) = x * klBasis cs (w_J) :=
  rfl

/-- `h ↦ h C'_{w_J}` commutes with the bar involutions. -/
theorem barL_parabolicLift (m : InducedModule (ind (cs.parabolicCoxeterSystem J)
      (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]))) :
    barL cs (parabolicLift cs J m) =
      parabolicLift cs J (parabolicBar (isBarCompatible_ind (cs.parabolicCoxeterSystem J)) m) := by
  induction m using Submodule.Quotient.induction_on with
  | H x => rw [parabolicLift_mk, parabolicBar_mk, parabolicLift_mk, map_mul, barL_klBasis]

/-- `[T_y](T_{d'} C'_{w_J}) = v^{-ℓ(w_J)}` if `y^J = d'`, and `0` otherwise. -/
theorem toFinsupp_T_mul_klBasis_parabolicLongestElement [DecidableEq W]
    (d' : cs.minCosetReps J) (y : W) :
    toFinsupp cs _ (T cs _ (d' : W) * klBasis cs (w_J)) y =
      if cs.minCosetRep J y = d' then LaurentPolynomial.T (-(ℓ (w_J) : ℤ)) else 0 := by
  have hsupp : ∀ z ∈ (toFinsupp cs _ (klBasis cs (w_J))).support, z ∈ cs.parabolicSubgroup J :=
    fun z hz ↦ mem_parabolicSubgroup_of_bruhatLE parabolicLongestElement_mem (by
      simpa using support_toFinsupp_klBasis_subset (cs.parabolicLongestElement J) hz)
  conv_lhs => rw [eq_sum_toFinsupp cs (klBasis cs (w_J)), Finsupp.sum, Finset.mul_sum]
  simp only [mul_smul_comm, map_sum, _root_.map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_congr rfl fun z hz ↦ by
    rw [T_mul_T_of_mem_minCosetReps cs _ d'.2 (hsupp z hz), toFinsupp_T, Finsupp.single_apply]]
  split_ifs with h
  · have hy : (d' : W)⁻¹ * y ∈ cs.parabolicSubgroup J := by
      rw [← h]; exact parabolicComponent_mem y
    rw [Finset.sum_eq_single ((d' : W)⁻¹ * y)]
    · rw [mul_inv_cancel_left, ite_eq_left rfl, mul_one, toFinsupp_klBasis_apply,
        klPoly_parabolicLongestElement_of_mem hy, map_one, mul_one]
    · intro z _ hz
      rw [ite_eq_right fun h' ↦ hz (by rw [← h']; group), mul_zero]
    · intro hz
      rw [Finsupp.notMem_support_iff.mp hz, zero_mul]
  · refine Finset.sum_eq_zero fun z hz ↦ ?_
    rw [ite_eq_right fun h' ↦ h (by rw [← h']; exact minCosetRep_mul d'.2 (hsupp z hz)),
      mul_zero]

/-- The coefficients of the image of `m ∈ 𝓗 ⊗_{𝓗_J} ind` under `h ⊗ 1 ↦ h C'_{w_J}`:
`[T_y] = v^{-ℓ(w_J)} [m_{y^J}] m`. -/
theorem toFinsupp_parabolicLift_apply (m : InducedModule (ind (cs.parabolicCoxeterSystem J)
      (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]))) (y : W) :
    toFinsupp cs _ (parabolicLift cs J m) y = LaurentPolynomial.T (-(ℓ (w_J) : ℤ)) *
      (inducedBasis _).repr m ⟨cs.minCosetRep J y, minCosetRep_mem y⟩ := by
  classical
  conv_lhs => rw [← (inducedBasis _).linearCombination_repr m]
  rw [Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum, Finsupp.sum_apply,
    Finsupp.sum, Finset.sum_eq_single ⟨cs.minCosetRep J y, minCosetRep_mem y⟩]
  · rw [LinearMap.map_smul_of_tower, _root_.map_smul, Finsupp.smul_apply, inducedBasis_apply,
      parabolicLift_mk, toFinsupp_T_mul_klBasis_parabolicLongestElement, ite_eq_left rfl,
      smul_eq_mul, mul_comm]
  · intro d' _ hd'
    rw [LinearMap.map_smul_of_tower, _root_.map_smul, Finsupp.smul_apply, inducedBasis_apply,
      parabolicLift_mk, toFinsupp_T_mul_klBasis_parabolicLongestElement,
      ite_eq_right fun h ↦ hd' (Subtype.ext h.symm), smul_zero]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_smul, map_zero, map_zero, Finsupp.zero_apply]

/-- **Deodhar's comparison for the index module** ([Deo] Prop. 3.4 (check)): for `W_J` finite,
the image of the parabolic Kazhdan–Lusztig basis element `C^J_d` of `𝓗 ⊗_{𝓗_J} ind` under
`h ⊗ 1 ↦ h C'_{w_J}` is `C'_{d w_J}`. -/
theorem parabolicLift_parabolicKLBasis (d : cs.minCosetReps J) :
    parabolicLift cs J (parabolicKLBasis (isBarCompatible_ind (cs.parabolicCoxeterSystem J)) d) =
      klBasis cs (d * w_J) := by
  set hχ := isBarCompatible_ind (cs.parabolicCoxeterSystem J)
  have hdw : ℓ ((d : W) * w_J) = ℓ d + ℓ (w_J) :=
    length_mul_of_mem_minCosetReps d.2 parabolicLongestElement_mem
  rw [← sub_eq_zero]
  refine eq_zero_of_barL_eq_self cs ?_ fun y n hn ↦ ?_
  · rw [map_sub, barL_parabolicLift, parabolicBar_parabolicKLBasis, barL_klBasis]
  have hl := length_eq_length_minCosetRep_add (cs := cs) (J := J) y
  have hlJ := length_le_length_parabolicLongestElement (cs := cs)
    (parabolicComponent_mem (J := J) y)
  rw [map_sub, Finsupp.sub_apply, toFinsupp_parabolicLift_apply, repr_parabolicKLBasis,
    toFinsupp_klBasis_apply, ← mul_assoc, ← T_add, hdw,
    show -(ℓ (w_J) : ℤ) + -(ℓ d : ℤ) = -((ℓ d + ℓ (w_J) : ℕ) : ℤ) by push_cast; ring, ← mul_sub,
    ← map_sub]
  refine coeff_T_mul_aeval_T_two_eq_zero fun k hk ↦ ?_
  rw [coeff_sub]
  by_cases hy : y = d * w_J
  · have hd' : (⟨cs.minCosetRep J y, minCosetRep_mem y⟩ : cs.minCosetReps J) = d :=
      Subtype.ext (by simp only [hy, minCosetRep_mul d.2 parabolicLongestElement_mem])
    rw [hd', parabolicKLPoly_self, ← hy, klPoly_self, sub_self]
  rw [coeff_klPoly_eq_zero cs hy (by rw [hdw]; push_cast at hk; omega), sub_zero]
  by_cases hd' : (⟨cs.minCosetRep J y, minCosetRep_mem y⟩ : cs.minCosetReps J) = d
  · rw [hd', parabolicKLPoly_self, coeff_one]
    refine ite_eq_right fun hk0 ↦ ?_
    subst hk0
    apply hy
    have h1 : cs.minCosetRep J y = d := congrArg Subtype.val hd'
    have h2 : cs.parabolicComponent J y = w_J :=
      eq_parabolicLongestElement (parabolicComponent_mem y)
        (by rw [h1] at hl; push_cast at hk; omega)
    rw [← minCosetRep_mul_parabolicComponent (cs := cs) (J := J) y, h1, h2]
  · exact coeff_parabolicKLPoly_eq_zero hχ hd' (by
      change ℓ d ≤ 2 * k + ℓ (cs.minCosetRep J y)
      push_cast at hk
      omega)

/-- **Deodhar's formula for the index module** ([Deo] Prop. 3.4 (check), [Soe] Prop. 3.4
(check)): if `W_J` is finite with longest element `w_J`, then for `d', d ∈ W^J`,
`P^{J,q}_{d',d} = P_{d' w_J, d w_J}`. -/
theorem parabolicKLPoly_ind (d' d : cs.minCosetReps J) :
    parabolicKLPoly (isBarCompatible_ind (cs.parabolicCoxeterSystem J)) d' d =
      klPoly cs (d' * w_J) (d * w_J) := by
  have h := congrArg (fun x ↦ toFinsupp cs _ x ((d' : W) * w_J)) (parabolicLift_parabolicKLBasis d)
  have hd' : (⟨cs.minCosetRep J ((d' : W) * w_J), minCosetRep_mem _⟩ : cs.minCosetReps J) = d' :=
    Subtype.ext (minCosetRep_mul d'.2 parabolicLongestElement_mem)
  have hdw : ℓ ((d : W) * w_J) = ℓ d + ℓ (w_J) :=
    length_mul_of_mem_minCosetReps d.2 parabolicLongestElement_mem
  rw [toFinsupp_parabolicLift_apply, hd', repr_parabolicKLBasis, toFinsupp_klBasis_apply,
    ← mul_assoc, ← T_add, hdw,
    show -(ℓ (w_J) : ℤ) + -(ℓ d : ℤ) = -((ℓ d + ℓ (w_J) : ℕ) : ℤ) by push_cast; ring] at h
  exact T_mul_aeval_T_two_injective _ h

end Index

end IwahoriHeckeAlgebra
