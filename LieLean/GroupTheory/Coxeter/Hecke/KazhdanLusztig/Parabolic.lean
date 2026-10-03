/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Canonical
import LieLean.GroupTheory.Coxeter.Hecke.Parabolic

/-!
# Parabolic Kazhdan–Lusztig polynomials

Let `(W, S)` be a Coxeter system, `J ⊆ S`, `W_J` the standard parabolic subgroup and `W^J` the set
of minimal left coset representatives. Let `𝓗 = 𝓗_{v²}(W)` be the generic Iwahori–Hecke algebra
over `ℤ[v, v⁻¹]` (normalization `(T_s - q)(T_s + 1) = 0`, `q = v²`) with its bar involution
`h ↦ h̄` (`IwahoriHeckeAlgebra.barL`), and `𝓗_J = 𝓗_{v²}(W_J)`.

For a one-dimensional representation `χ : 𝓗_J → ℤ[v, v⁻¹]` compatible with the bar involution
(`IwahoriHeckeAlgebra.IsBarCompatible`: `χ(h̄) = \overline{χ(h)}`, plus a grading condition), the
induced module `𝓜 = 𝓗 ⊗_{𝓗_J} χ` (`IwahoriHeckeAlgebra.InducedModule χ`), with `ℤ[v, v⁻¹]`-basis
`m_d = T_d ⊗ 1`, `d ∈ W^J`, carries a bar involution (`IwahoriHeckeAlgebra.parabolicBar`)
```
  \overline{h ⊗ 1} = h̄ ⊗ 1,   so that   \overline{h m} = h̄ m̄,   m̄_1 = m_1.
```
The two cases of interest are Deodhar's modules ([Deo] §2): `χ = ind` (`T_s ↦ q`, `u = q`
in Deodhar's notation) and `χ = sgn` (`T_s ↦ -1`, `u = -1`); both are bar compatible
(`isBarCompatible_ind`, `isBarCompatible_sgn`).

The bar involution is unitriangular in the basis `(m_d)` for the Bruhat order restricted to `W^J`:
`m̄_d ∈ q^{-ℓ(d)} m_d + Σ_{d' < d} ℤ[v, v⁻¹] m_{d'}` (`repr_parabolicBar_basis_self`,
`bruhatLE_of_repr_parabolicBar_basis_ne_zero`). This follows from the triangularity of the bar
involution of `𝓗` and from `T_y ⊗ 1 = χ(T_{y_J}) m_{y^J}` for `y = y^J y_J`, `y^J ≤ y`.
By Lusztig's lemma (`Module.Basis.IsBarTriangular.existsUnique_canonical`) there is, for every
`d ∈ W^J`, a unique bar-invariant element (the **parabolic Kazhdan–Lusztig basis**)
```
  C^J_d ∈ m̃_d + Σ_{d' < d} v⁻¹ ℤ[v⁻¹] m̃_{d'},     m̃_d = v^{-ℓ(d)} m_d
```
(`existsUnique_parabolicKLBasis`). The grading of the matrix of the bar involution shows that
the coefficients have the Kazhdan–Lusztig shape
```
  C^J_d = v^{-ℓ(d)} Σ_{d' ≤ d} P^J_{d',d}(q) m_{d'},    P^J_{d,d} = 1,
  deg P^J_{d',d} ≤ (ℓ(d) - ℓ(d') - 1)/2  (d' < d)
```
with **parabolic Kazhdan–Lusztig polynomials** `P^J_{d',d} ∈ ℤ[q]` (`parabolicKLPoly`). For
`χ = ind` these are Soergel's `m_{d',d}` and for `χ = sgn` Soergel's `n_{d',d}`, up to
normalization. Deodhar's invariant elements ([Deo] Prop. 3.2) have the shape of
Kazhdan–Lusztig's `C_w`, not `C'_w`, which exchanges the two cases: our polynomials for `χ = ind`
are Deodhar's for `u = -1`, those for `χ = sgn` are Deodhar's for `u = q` ([Deo] Prop. 3.4,
Rem. 3.8; [Soe] Def. 3.3, Rem. 3.5(1)). The relations with ordinary Kazhdan–Lusztig
polynomials are in
`LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.ParabolicRelations`.

The normalization is the Kazhdan–Lusztig one (coefficients in `v⁻¹ ℤ[v⁻¹]`); Soergel's `v ℤ[v]`
normalization [Soe] differs by `v ↦ v⁻¹`. We did not consult [Deo]; the construction via
Lusztig's lemma and the grading argument are our own write-up of the standard argument.

## Main definitions

* `IwahoriHeckeAlgebra.IsBarCompatible χ`: `χ` commutes with the bar involutions and is graded.
* `IwahoriHeckeAlgebra.parabolicBar χ`: the bar involution of the induced module.
* `IwahoriHeckeAlgebra.parabolicKLBasis hχ d`: the parabolic Kazhdan–Lusztig basis element
  `C^J_d`.
* `IwahoriHeckeAlgebra.parabolicKLPoly hχ d' d`: the parabolic Kazhdan–Lusztig polynomial
  `P^J_{d',d}`.

## Main results

* `IwahoriHeckeAlgebra.parabolicHom_barL`: `𝓗_J → 𝓗` commutes with the bar involutions.
* `IwahoriHeckeAlgebra.isBarCompatible_ind`, `isBarCompatible_sgn`.
* `IwahoriHeckeAlgebra.parabolicBar_smul`, `parabolicBar_parabolicBar`,
  `parabolicBar_mk_one`: the bar involution of the induced module.
* `IwahoriHeckeAlgebra.repr_parabolicBar_basis_self`,
  `bruhatLE_of_repr_parabolicBar_basis_ne_zero`: triangularity.
* `IwahoriHeckeAlgebra.existsUnique_parabolicKLBasis`: existence and uniqueness of `C^J_d`.
* `IwahoriHeckeAlgebra.repr_parabolicKLBasis`, `parabolicKLPoly_self`,
  `parabolicKLPoly_eq_zero_of_not_bruhatLE`, `two_mul_natDegree_parabolicKLPoly_add_length_lt`:
  basic properties of the parabolic Kazhdan–Lusztig polynomials.

## References

* [Deo] V. Deodhar, *On some geometric aspects of Bruhat orderings II. The parabolic analogue of
  Kazhdan–Lusztig polynomials*, J. Algebra **111** (1987), 483–506.
* [Soe] W. Soergel, *Kazhdan–Lusztig-Polynome und eine Kombinatorik für Kipp-Moduln*,
  Represent. Theory **1** (1997), 37–68, §3.
* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184.
-/

open Finsupp LaurentPolynomial Polynomial Module

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

variable {cs} in
/-- If `ℓ(uv) = ℓ(u) + ℓ(v)`, then `u ≤ uv` in the Bruhat order. -/
theorem bruhatLE_mul_of_length_mul {u v : W} (h : ℓ (u * v) = ℓ u + ℓ v) :
    cs.BruhatLE u (u * v) := by
  induction v using cs.induction_mul_simple with
  | one => simpa using cs.bruhatLE_refl u
  | mul_simple v i hlt ih =>
    have h1 := cs.length_mul_le u v
    have h2 := cs.length_mul_le (u * v) (s i)
    have h3 := cs.length_mul_simple v i
    rw [cs.length_simple, ← mul_assoc] at *
    have huv : ℓ (u * v) = ℓ u + ℓ v := by omega
    refine (ih huv).trans (cs.bruhatLE_mul_simple ?_)
    rw [IsRightDescent]
    omega

/-- The minimal coset representative `w^J` of `w` satisfies `w^J ≤ w`. -/
theorem minCosetRep_bruhatLE (J : Set B) (w : W) : cs.BruhatLE (cs.minCosetRep J w) w := by
  have h := bruhatLE_mul_of_length_mul (cs := cs) (u := cs.minCosetRep J w)
    (v := cs.parabolicComponent J w)
  rw [minCosetRep_mul_parabolicComponent] at h
  exact h (length_eq_length_minCosetRep_add w)

/-- The Bruhat order on the set `W^J` of minimal coset representatives, as a partial order (used
as a local instance). -/
abbrev minCosetRepsPartialOrder (J : Set B) : PartialOrder (cs.minCosetReps J) where
  le d d' := cs.BruhatLE d d'
  le_refl d := cs.bruhatLE_refl d
  le_trans _ _ _ := BruhatLE.trans
  le_antisymm _ _ h h' := Subtype.ext (h.antisymm h')

end CoxeterSystem

namespace IwahoriHeckeAlgebra

open CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

local notation "𝓗" => IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])

/-! ### Compatibility of one-dimensional representations with the bar involution -/

section Compat

/-- Two ring homomorphisms out of `𝓗` that are semilinear for `v ↦ v⁻¹` and agree on the `T_s`
are equal. -/
theorem ringHom_ext_of_map_smul {A : Type*} [Ring A] [Algebra ℤ[T;T⁻¹] A] {f g : 𝓗 →+* A}
    (hf : ∀ (a : ℤ[T;T⁻¹]) x, f (a • x) = invert a • f x)
    (hg : ∀ (a : ℤ[T;T⁻¹]) x, g (a • x) = invert a • g x)
    (hT : ∀ i, f (T cs _ (s i)) = g (T cs _ (s i))) : f = g := by
  ext x
  induction x using induction_on cs _ with
  | T w =>
    induction w using cs.induction_simple_mul with
    | one => rw [T_one, map_one, map_one]
    | simple_mul w i hlt ih => rw [← T_simple_mul_T_of_lt cs _ hlt, map_mul, map_mul, ih, hT]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul a x hx => rw [hf, hg, hx]

theorem barL_algebraMap (a : ℤ[T;T⁻¹]) :
    barL cs (algebraMap ℤ[T;T⁻¹] 𝓗 a) = algebraMap ℤ[T;T⁻¹] 𝓗 (invert a) := by
  rw [Algebra.algebraMap_eq_smul_one, barL_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

/-- A one-dimensional representation of `𝓗` commutes with the bar involutions as soon as it does
on the generators `T_s`. -/
theorem map_barL_of_forall_simple (χ : 𝓗 →ₐ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹])
    (h : ∀ i, χ (barL cs (T cs _ (s i))) = invert (χ (T cs _ (s i)))) (x : 𝓗) :
    χ (barL cs x) = invert (χ x) := by
  have := ringHom_ext_of_map_smul cs (f := χ.toRingHom.comp (barL cs))
    (g := invertHom.comp χ.toRingHom)
    (fun a x ↦ by simp [barL_smul, smul_eq_mul])
    (fun a x ↦ by simp [smul_eq_mul]) h
  exact congrArg (fun φ : 𝓗 →+* ℤ[T;T⁻¹] ↦ φ x) this

theorem T_neg_two_mul_T_two :
    (LaurentPolynomial.T (-2) * LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) = 1 := by
  rw [← T_add]; simp

/-- `ind` commutes with the bar involutions. -/
theorem ind_barL (x : 𝓗) : ind cs _ (barL cs x) = invert (ind cs _ x) := by
  refine map_barL_of_forall_simple cs _ (fun i ↦ ?_) x
  rw [barL_T_simple, map_sub, _root_.map_smul, _root_.map_smul, ind_T_simple, map_one, invert_T,
    smul_eq_mul, smul_eq_mul, T_neg_two_mul_T_two]
  ring

/-- `sgn` commutes with the bar involutions. -/
theorem sgn_barL (x : 𝓗) : sgn cs _ (barL cs x) = invert (sgn cs _ x) := by
  refine map_barL_of_forall_simple cs _ (fun i ↦ ?_) x
  rw [barL_T_simple, map_sub, _root_.map_smul, _root_.map_smul, sgn_T_simple, map_one, map_neg,
    map_one, smul_eq_mul, smul_eq_mul]
  ring

/-- A one-dimensional representation `χ` of `𝓗` is *bar compatible* if `χ(h̄) = \overline{χ(h)}`
and each `v^{-ℓ(w)} χ(T_w)` is supported in degrees `n` with `|n| ≤ ℓ(w)`,
`n ≡ ℓ(w) (mod 2)`. Examples: `ind` and `sgn`. -/
structure IsBarCompatible (χ : 𝓗 →ₐ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹]) : Prop where
  /-- `χ` commutes with the bar involutions. -/
  map_barL (x : 𝓗) : χ (barL cs x) = invert (χ x)
  /-- The grading condition. -/
  isBounded_T (w : W) : (LaurentPolynomial.T (-(ℓ w : ℤ)) * χ (T cs _ w)).IsBounded (ℓ w)

/-- The index representation `T_s ↦ q` is bar compatible. -/
theorem isBarCompatible_ind : IsBarCompatible cs (ind cs _) where
  map_barL := ind_barL cs
  isBounded_T w := by
    rw [ind_T, T_pow, ← T_add]
    exact isBounded_T (by omega) (by omega) ⟨ℓ w, by ring⟩

/-- The sign representation `T_s ↦ -1` is bar compatible. -/
theorem isBarCompatible_sgn : IsBarCompatible cs (sgn cs _) where
  map_barL := sgn_barL cs
  isBounded_T w := by
    rw [sgn_T, show ((-1 : ℤ[T;T⁻¹]) ^ ℓ w) = LaurentPolynomial.C ((-1) ^ ℓ w) by simp,
      mul_comm]
    exact isBounded_C_mul_T _ (by omega) (by omega) ⟨0, by ring⟩

end Compat

/-! ### The parabolic subalgebra and the bar involution -/

section ParabolicHom

variable (J : Set B)

/-- The inclusion `𝓗(W_J) → 𝓗(W)` commutes with the bar involutions. -/
theorem parabolicHom_barL (x : IwahoriHeckeAlgebra (cs.parabolicCoxeterSystem J)
      (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])) :
    parabolicHom cs _ J (barL _ x) = barL cs (parabolicHom cs _ J x) := by
  have := ringHom_ext_of_map_smul (cs.parabolicCoxeterSystem J)
    (f := (parabolicHom cs _ J).toRingHom.comp (barL _))
    (g := (barL cs).comp (parabolicHom cs _ J).toRingHom)
    (fun a x ↦ by simp [barL_smul]) (fun a x ↦ by simp [barL_smul]) (fun j ↦ by
      simp only [RingHom.coe_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply,
        barL_T_simple, map_sub, _root_.map_smul, map_one, parabolicHom_T,
        coe_parabolicCoxeterSystem_simple])
  exact congrArg (fun φ ↦ φ x) this

end ParabolicHom

/-- The normalized `R`-polynomials: `v^{ℓ(y) + ℓ(w)} [T_y] T̄_w` is supported in degrees `n` with
`|n| ≤ ℓ(w) - ℓ(y)`, `n ≡ ℓ(w) - ℓ(y) (mod 2)`. -/
theorem isBounded_toFinsupp_barL_T (y w : W) :
    (LaurentPolynomial.T ((ℓ y : ℤ) + ℓ w) *
      toFinsupp cs _ (barL cs (T cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) w)) y).IsBounded
      ((ℓ w : ℤ) - ℓ y) := by
  obtain ⟨p, hp, hpd, hp0⟩ := exists_rPoly_eq_aeval_natDegree_le cs (isUnit_T_two (A := ℤ)) y w
  rw [toFinsupp_barL_T_apply, hp]
  by_cases hyw : ℓ w < ℓ y
  · rw [hp0 hyw, map_zero, mul_zero, mul_zero]
    exact isBounded_zero _
  have key := (isBounded_C_mul_T ((-1) ^ (ℓ y + ℓ w)) (N := 0) le_rfl le_rfl ⟨0, by ring⟩).mul
    (isBounded_T_mul_aeval (N := (ℓ w : ℤ) - ℓ y) (a := (ℓ y : ℤ) - ℓ w) p (by omega) (by omega)
      ⟨0, by ring⟩)
  rw [zero_add] at key
  convert key using 1
  rw [show (LaurentPolynomial.C ((-1) ^ (ℓ y + ℓ w)) : ℤ[T;T⁻¹]) = (-1) ^ (ℓ y + ℓ w) by simp,
    neg_zero, T_zero, mul_one, show (LaurentPolynomial.T ((ℓ y : ℤ) - ℓ w) : ℤ[T;T⁻¹]) =
      LaurentPolynomial.T ((ℓ y : ℤ) + ℓ w) * LaurentPolynomial.T (-(2 * ℓ w : ℤ)) by
      rw [← T_add]; congr 1; ring]
  ring_nf
  rfl

/-! ### The bar involution of an induced module -/

section Induced

variable {J : Set B}

/-- The bar involution of `𝓗`, as a semilinear map of `𝓗`-modules over the ring homomorphism
`barL`. -/
noncomputable def barLSemilinear : 𝓗 →ₛₗ[barL (A := ℤ) cs] 𝓗 where
  toFun := barL cs
  map_add' x y := map_add (barL cs) x y
  map_smul' x y := map_mul (barL cs) x y

@[simp]
theorem barLSemilinear_apply (x : 𝓗) : barLSemilinear cs x = barL cs x := rfl

variable {cs}
variable (χ : IwahoriHeckeAlgebra (cs.parabolicCoxeterSystem J)
  (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) →ₐ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹])

theorem inducedIdeal_le_comap_barL (hχ : ∀ x, χ (barL _ x) = invert (χ x)) :
    inducedIdeal χ ≤ (inducedIdeal χ).comap (barLSemilinear cs) := by
  rw [inducedIdeal, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, barLSemilinear_apply]
  rw [map_sub, ← parabolicHom_barL, barL_algebraMap, ← hχ]
  exact Submodule.subset_span ⟨_, rfl⟩

variable {χ}

/-- The **bar involution of the induced module** `𝓗 ⊗_{𝓗_J} χ` ([Deo] §2):
`\overline{h ⊗ 1} = h̄ ⊗ 1`. It is semilinear over the bar involution of `𝓗`
(`parabolicBar_smul_hecke`). -/
noncomputable def parabolicBar (hχ : IsBarCompatible (cs.parabolicCoxeterSystem J) χ) :
    InducedModule χ →ₛₗ[barL (A := ℤ) cs] InducedModule χ :=
  Submodule.mapQ _ _ (barLSemilinear cs) (inducedIdeal_le_comap_barL χ hχ.map_barL)

variable (hχ : IsBarCompatible (cs.parabolicCoxeterSystem J) χ)

@[simp]
theorem parabolicBar_mk (x : 𝓗) :
    parabolicBar hχ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (barL cs x) := rfl

/-- `\overline{h m} = h̄ m̄`. -/
theorem parabolicBar_smul_hecke (h : 𝓗) (m : InducedModule χ) :
    parabolicBar hχ (h • m) = barL cs h • parabolicBar hχ m :=
  LinearMap.map_smulₛₗ _ h m

/-- The bar involution of the induced module is semilinear for `v ↦ v⁻¹`. -/
theorem parabolicBar_smul (a : ℤ[T;T⁻¹]) (m : InducedModule χ) :
    parabolicBar hχ (a • m) = invert a • parabolicBar hχ m := by
  induction m using Submodule.Quotient.induction_on with
  | H x => rw [← Submodule.Quotient.mk_smul, parabolicBar_mk, parabolicBar_mk, barL_smul,
    Submodule.Quotient.mk_smul]

/-- The bar involution of the induced module is an involution. -/
theorem parabolicBar_parabolicBar (m : InducedModule χ) :
    parabolicBar hχ (parabolicBar hχ m) = m := by
  induction m using Submodule.Quotient.induction_on with
  | H x => rw [parabolicBar_mk, parabolicBar_mk, barL_barL]

/-- `m̄_1 = m_1`. -/
theorem parabolicBar_mk_one :
    parabolicBar hχ (Submodule.Quotient.mk (1 : 𝓗) : InducedModule χ) =
      Submodule.Quotient.mk 1 := by
  rw [parabolicBar_mk, map_one]

/-! ### Coefficients in the standard basis -/

omit hχ in
/-- `T_y ⊗ 1 = χ(T_{y_J}) m_{y^J}`. -/
theorem inducedCoeff_T_apply [DecidableEq W] (y : W) (d : cs.minCosetReps J) :
    inducedCoeff χ (T cs _ y) d = if cs.minCosetRep J y = d then
      χ (T _ _ ⟨cs.parabolicComponent J y, parabolicComponent_mem y⟩) else 0 := by
  have e : T cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) y = T cs _ (cs.minCosetRep J y) *
      parabolicHom cs _ J (T _ _ ⟨cs.parabolicComponent J y, parabolicComponent_mem y⟩) := by
    rw [parabolicHom_T, T_mul_T_of_mem_minCosetReps cs _ (minCosetRep_mem y)
      (parabolicComponent_mem y), minCosetRep_mul_parabolicComponent]
  rw [e, inducedCoeff_mul_parabolicHom,
    show T cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) (cs.minCosetRep J y) =
      T cs _ ((⟨_, minCosetRep_mem y⟩ : cs.minCosetReps J) : W) from rfl, inducedCoeff_T,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  classical
  by_cases h : cs.minCosetRep J y = d
  · rw [ite_eq_left (Subtype.ext h), ite_eq_left h, mul_one]
  · rw [ite_eq_right (fun h' ↦ h (congrArg Subtype.val h')), ite_eq_right h, mul_zero]

omit hχ in
/-- The coefficients of `h ⊗ 1` in the basis `(m_d)`. -/
theorem repr_mk_apply (x : 𝓗) (d : cs.minCosetReps J) :
    (inducedBasis χ).repr (Submodule.Quotient.mk x) d =
      (toFinsupp cs _ x).sum fun y a ↦ a * inducedCoeff χ (T cs _ y) d := by
  rw [show (inducedBasis χ).repr = inducedModuleEquiv χ from rfl, inducedModuleEquiv_mk]
  conv_lhs => rw [eq_sum_toFinsupp cs x]
  rw [map_finsuppSum, Finsupp.sum_apply]
  simp only [_root_.map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- **Triangularity of the bar involution of the induced module**, diagonal part:
the coefficient of `m_d` in `m̄_d` is `q^{-ℓ(d)}`. -/
theorem repr_parabolicBar_basis_self (d : cs.minCosetReps J) :
    (inducedBasis χ).repr (parabolicBar hχ (inducedBasis χ d)) d =
      LaurentPolynomial.T (-(2 * ℓ d : ℤ)) := by
  classical
  have hd1 : cs.minCosetRep J (d : W) = d := (minCosetRep_eq_iff).mpr ⟨d.2, by simp⟩
  rw [inducedBasis_apply, parabolicBar_mk, repr_mk_apply, Finsupp.sum]
  have hd : (d : W) ∈
      (toFinsupp cs _ (barL cs (T cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) (d : W)))).support := by
    rw [Finsupp.mem_support_iff, toFinsupp_barL_T_self]
    exact (LaurentPolynomial.isUnit_T _).ne_zero
  rw [Finset.sum_eq_single_of_mem _ hd, toFinsupp_barL_T_self, inducedCoeff_T_apply,
    ite_eq_left hd1]
  · have : (⟨cs.parabolicComponent J d, parabolicComponent_mem (d : W)⟩ :
        cs.parabolicSubgroup J) = 1 := by
      apply Subtype.ext
      have h := minCosetRep_mul_parabolicComponent (cs := cs) (J := J) (d : W)
      rw [hd1] at h
      simpa using h
    rw [this, T_one, map_one, mul_one]
  · intro y hy hyd
    rw [inducedCoeff_T_apply]
    split_ifs with h
    · exfalso
      have hle := bruhatLE_of_toFinsupp_barL_T_ne_zero cs (Finsupp.mem_support_iff.mp hy)
      have hl := length_eq_length_minCosetRep_add (cs := cs) (J := J) y
      rw [h] at hl
      exact hyd (hle.eq_of_length_le (by omega))
    · rw [mul_zero]

/-- **Triangularity of the bar involution of the induced module** ([Deo] §2): if `m_{d'}`
occurs in `m̄_d`, then `d' ≤ d`. -/
theorem bruhatLE_of_repr_parabolicBar_basis_ne_zero {d d' : cs.minCosetReps J}
    (h : (inducedBasis χ).repr (parabolicBar hχ (inducedBasis χ d)) d' ≠ 0) :
    cs.BruhatLE d' d := by
  classical
  rw [inducedBasis_apply, parabolicBar_mk, repr_mk_apply, Finsupp.sum] at h
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [inducedCoeff_T_apply] at hne
  split_ifs at hne with hyd
  · rw [← hyd]
    exact (minCosetRep_bruhatLE cs J y).trans
      (bruhatLE_of_toFinsupp_barL_T_ne_zero cs (Finsupp.mem_support_iff.mp hy))
  · exact absurd (mul_zero _) hne

/-- The grading of the bar involution of the induced module:
`v^{ℓ(d') + ℓ(d)} [m_{d'}] m̄_d` is supported in degrees `n` with `|n| ≤ ℓ(d) - ℓ(d')`,
`n ≡ ℓ(d) - ℓ(d') (mod 2)`. -/
theorem isBounded_repr_parabolicBar_basis (d d' : cs.minCosetReps J) :
    (LaurentPolynomial.T ((ℓ d' : ℤ) + ℓ d) *
      (inducedBasis χ).repr (parabolicBar hχ (inducedBasis χ d)) d').IsBounded
      ((ℓ d : ℤ) - ℓ d') := by
  classical
  rw [inducedBasis_apply, parabolicBar_mk, repr_mk_apply, Finsupp.sum, Finset.mul_sum]
  refine isBounded_sum _ fun y _ ↦ ?_
  rw [inducedCoeff_T_apply]
  split_ifs with hyd
  · set z : cs.parabolicSubgroup J := ⟨cs.parabolicComponent J y, parabolicComponent_mem y⟩
    have hl : ℓ y = ℓ d' + (cs.parabolicCoxeterSystem J).length z := by
      rw [length_parabolicCoxeterSystem, ← hyd]
      exact length_eq_length_minCosetRep_add (J := J) y
    have key := (isBounded_toFinsupp_barL_T cs y d).mul (hχ.isBounded_T z)
    convert key.of_eq (show ((ℓ d : ℤ) - ℓ y) + (cs.parabolicCoxeterSystem J).length z =
      (ℓ d : ℤ) - ℓ d' by rw [hl]; push_cast; ring) using 1
    rw [show (LaurentPolynomial.T ((ℓ d' : ℤ) + ℓ d) : ℤ[T;T⁻¹]) =
      LaurentPolynomial.T ((ℓ y : ℤ) + ℓ d) *
        LaurentPolynomial.T (-((cs.parabolicCoxeterSystem J).length z : ℤ)) by
          rw [← T_add, hl]; congr 1; push_cast; ring]
    ring
  · rw [mul_zero, mul_zero]
    exact isBounded_zero _

end Induced

/-! ### The parabolic Kazhdan–Lusztig basis -/

section Canonical

variable {J : Set B} {χ : IwahoriHeckeAlgebra (cs.parabolicCoxeterSystem J)
  (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) →ₐ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹]}

variable (χ) in
/-- The normalized basis `m̃_d = v^{-ℓ(d)} m_d` of the induced module. -/
noncomputable def normalizedBasis : Basis (cs.minCosetReps J) ℤ[T;T⁻¹] (InducedModule χ) :=
  (inducedBasis χ).unitsSMul fun d ↦ (LaurentPolynomial.isUnit_T (-(ℓ d : ℤ))).unit

theorem normalizedBasis_apply (d : cs.minCosetReps J) :
    normalizedBasis cs χ d = (LaurentPolynomial.T (-(ℓ d : ℤ)) : ℤ[T;T⁻¹]) • inducedBasis χ d :=
  Basis.unitsSMul_apply d

theorem normalizedBasis_repr_apply (m : InducedModule χ) (d : cs.minCosetReps J) :
    (normalizedBasis cs χ).repr m d =
      LaurentPolynomial.T (ℓ d : ℤ) * (inducedBasis χ).repr m d := by
  rw [normalizedBasis, Basis.repr_unitsSMul, Units.smul_def, smul_eq_mul]
  congr 1
  exact Units.inv_eq_of_mul_eq_one_right (by rw [IsUnit.unit_spec, ← T_add]; simp)

variable {cs}
variable (hχ : IsBarCompatible (cs.parabolicCoxeterSystem J) χ)

attribute [local instance] CoxeterSystem.minCosetRepsPartialOrder

/-- The bar involution of the induced module satisfies the hypotheses of Lusztig's lemma in the
normalized basis `m̃_d = v^{-ℓ(d)} m_d`, graded by the length. -/
theorem isBarTriangular :
    (normalizedBasis cs χ).IsBarTriangular (parabolicBar hχ).toAddMonoidHom
      (fun d ↦ (ℓ d : ℤ)) where
  map_smul a x := parabolicBar_smul hχ a x
  involutive x := parabolicBar_parabolicBar hχ x
  repr_self d := by
    rw [LinearMap.toAddMonoidHom_coe, normalizedBasis_repr_apply, normalizedBasis_apply,
      parabolicBar_smul, _root_.map_smul, Finsupp.smul_apply, smul_eq_mul,
      repr_parabolicBar_basis_self, invert_T, ← T_add, ← T_add, neg_neg]
    convert T_zero using 2
    ring
  le_of_repr_ne_zero {d d'} h := by
    rw [LinearMap.toAddMonoidHom_coe, normalizedBasis_repr_apply, normalizedBasis_apply,
      parabolicBar_smul, _root_.map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    exact bruhatLE_of_repr_parabolicBar_basis_ne_zero hχ fun h' ↦ h (by rw [h', mul_zero, mul_zero])
  isBounded d d' := by
    rw [LinearMap.toAddMonoidHom_coe, normalizedBasis_repr_apply, normalizedBasis_apply,
      parabolicBar_smul, _root_.map_smul, Finsupp.smul_apply, smul_eq_mul, invert_T, neg_neg,
      ← mul_assoc, ← T_add]
    exact isBounded_repr_parabolicBar_basis hχ d d'
  finite_Iio d := ((cs.finite_setOf_bruhatLE d).preimage Subtype.val_injective.injOn).subset
    fun _ h ↦ (Set.mem_Iio.mp h).le

/-- The **parabolic Kazhdan–Lusztig basis** element `C^J_d` of the induced module
`𝓗 ⊗_{𝓗_J} χ` ([Soe] Thm. 3.1; cf. [Deo] Prop. 3.2): the unique bar-invariant
element of `m̃_d + Σ_{d' < d} v⁻¹ ℤ[v⁻¹] m̃_{d'}`, `m̃_d = v^{-ℓ(d)} m_d`
(`existsUnique_parabolicKLBasis`). -/
noncomputable def parabolicKLBasis (d : cs.minCosetReps J) : InducedModule χ :=
  (isBarTriangular hχ).canonical d

/-- `C^J_d` is bar invariant. -/
theorem parabolicBar_parabolicKLBasis (d : cs.minCosetReps J) :
    parabolicBar hχ (parabolicKLBasis hχ d) = parabolicKLBasis hχ d :=
  (isBarTriangular hχ).apply_canonical d

/-- The coefficient of `m_d` in `C^J_d` is `v^{-ℓ(d)}`. -/
theorem repr_parabolicKLBasis_self (d : cs.minCosetReps J) :
    (inducedBasis χ).repr (parabolicKLBasis hχ d) d = LaurentPolynomial.T (-(ℓ d : ℤ)) := by
  have h := (isBarTriangular hχ).repr_canonical_self d
  rw [normalizedBasis_repr_apply] at h
  rw [parabolicKLBasis, ← one_mul ((inducedBasis χ).repr _ d), ← T_zero,
    show (0 : ℤ) = -(ℓ d : ℤ) + ℓ d by ring, T_add, mul_assoc, h, mul_one]

/-- For `d' ≠ d`, the coefficient of `m̃_{d'}` in `C^J_d` lies in `v⁻¹ ℤ[v⁻¹]`. -/
theorem isNeg_repr_parabolicKLBasis {d d' : cs.minCosetReps J} (h : d' ≠ d) :
    (LaurentPolynomial.T (ℓ d' : ℤ) * (inducedBasis χ).repr (parabolicKLBasis hχ d) d').IsNeg := by
  rw [← normalizedBasis_repr_apply]
  exact (isBarTriangular hχ).isNeg_repr_canonical h

/-- If `m_{d'}` occurs in `C^J_d`, then `d' ≤ d` in the Bruhat order. -/
theorem bruhatLE_of_repr_parabolicKLBasis_ne_zero {d d' : cs.minCosetReps J}
    (h : (inducedBasis χ).repr (parabolicKLBasis hχ d) d' ≠ 0) : cs.BruhatLE d' d := by
  refine (isBarTriangular hχ).le_of_repr_canonical_ne_zero (j := d') ?_
  intro h'
  rw [normalizedBasis_repr_apply] at h'
  exact h ((mul_eq_zero.mp h').resolve_left (LaurentPolynomial.isUnit_T _).ne_zero)

theorem isBounded_repr_parabolicKLBasis (d d' : cs.minCosetReps J) :
    (LaurentPolynomial.T (ℓ d' : ℤ) * (inducedBasis χ).repr (parabolicKLBasis hχ d) d').IsBounded
      ((ℓ d : ℤ) - ℓ d') := by
  rw [← normalizedBasis_repr_apply]
  exact (isBarTriangular hχ).isBounded_repr_canonical d d'

/-- Characterization of `C^J_d`. -/
theorem eq_parabolicKLBasis {d : cs.minCosetReps J} {C : InducedModule χ}
    (hC : parabolicBar hχ C = C)
    (hd : (inducedBasis χ).repr C d = LaurentPolynomial.T (-(ℓ d : ℤ)))
    (hneg : ∀ d', d' ≠ d → (LaurentPolynomial.T (ℓ d' : ℤ) * (inducedBasis χ).repr C d').IsNeg) :
    C = parabolicKLBasis hχ d := by
  refine (isBarTriangular hχ).eq_canonical hC ?_ fun d' h ↦ ?_
  · rw [normalizedBasis_repr_apply, hd, ← T_add, add_neg_cancel, T_zero]
  · rw [normalizedBasis_repr_apply]
    exact hneg d' h

/-- **Existence and uniqueness of the parabolic Kazhdan–Lusztig basis** ([Soe] Thm. 3.1,
in the normalization of [KL]; cf. [Deo] Prop. 3.2): for `d ∈ W^J` there is a unique
bar-invariant `C ∈ 𝓗 ⊗_{𝓗_J} χ` with `C ∈ m̃_d + Σ_{d' ≠ d} v⁻¹ ℤ[v⁻¹] m̃_{d'}`, where
`m̃_d = v^{-ℓ(d)} m_d`. It is `C^J_d`; its coefficients vanish outside `{d' ≤ d}`
(`bruhatLE_of_repr_parabolicKLBasis_ne_zero`). -/
theorem existsUnique_parabolicKLBasis (d : cs.minCosetReps J) :
    ∃! C : InducedModule χ, parabolicBar hχ C = C ∧
      (inducedBasis χ).repr C d = LaurentPolynomial.T (-(ℓ d : ℤ)) ∧
      ∀ d', d' ≠ d → (LaurentPolynomial.T (ℓ d' : ℤ) * (inducedBasis χ).repr C d').IsNeg :=
  ⟨parabolicKLBasis hχ d, ⟨parabolicBar_parabolicKLBasis hχ d, repr_parabolicKLBasis_self hχ d,
    fun _ h ↦ isNeg_repr_parabolicKLBasis hχ h⟩,
    fun _ ⟨hC, hd, hneg⟩ ↦ eq_parabolicKLBasis hχ hC hd hneg⟩

/-! ### Parabolic Kazhdan–Lusztig polynomials -/

theorem exists_parabolicKLPoly (d' d : cs.minCosetReps J) :
    ∃ P : ℤ[X], (inducedBasis χ).repr (parabolicKLBasis hχ d) d' =
        LaurentPolynomial.T (-(ℓ d : ℤ)) * aeval (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) P ∧
      ∀ k : ℕ, P.coeff k =
        ((inducedBasis χ).repr (parabolicKLBasis hχ d) d').coeff (-(ℓ d : ℤ) + 2 * k) := by
  refine exists_eq_T_mul_aeval fun n hn ↦ ?_
  have hb := isBounded_repr_parabolicKLBasis hχ d d' (n + ℓ d')
    (by rwa [coeff_T_mul, add_sub_cancel_right])
  obtain ⟨h1, -, h3⟩ := hb
  refine ⟨by omega, ?_⟩
  convert h3 using 1
  ring

/-- The **parabolic Kazhdan–Lusztig polynomial** `P^J_{d',d} ∈ ℤ[q]` ([Deo] §3):
`C^J_d = v^{-ℓ(d)} Σ_{d' ≤ d} P^J_{d',d}(q) m_{d'}` (`repr_parabolicKLBasis`). For `χ = ind`
these are Deodhar's `P^J` for `u = -1`, for `χ = sgn` those for `u = q` (see the module
docstring). -/
noncomputable def parabolicKLPoly (d' d : cs.minCosetReps J) : ℤ[X] :=
  (exists_parabolicKLPoly hχ d' d).choose

/-- `C^J_d = v^{-ℓ(d)} Σ_{d'} P^J_{d',d}(q) m_{d'}`. -/
theorem repr_parabolicKLBasis (d' d : cs.minCosetReps J) :
    (inducedBasis χ).repr (parabolicKLBasis hχ d) d' =
      LaurentPolynomial.T (-(ℓ d : ℤ)) *
        aeval (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) (parabolicKLPoly hχ d' d) :=
  (exists_parabolicKLPoly hχ d' d).choose_spec.1

theorem coeff_parabolicKLPoly (d' d : cs.minCosetReps J) (k : ℕ) :
    (parabolicKLPoly hχ d' d).coeff k =
      ((inducedBasis χ).repr (parabolicKLBasis hχ d) d').coeff (-(ℓ d : ℤ) + 2 * k) :=
  (exists_parabolicKLPoly hχ d' d).choose_spec.2 k

/-- `P^J_{d,d} = 1` ([Deo] §3). -/
@[simp]
theorem parabolicKLPoly_self (d : cs.minCosetReps J) : parabolicKLPoly hχ d d = 1 := by
  refine T_mul_aeval_T_two_injective (-(ℓ d : ℤ)) ?_
  simp only
  rw [← repr_parabolicKLBasis, repr_parabolicKLBasis_self, map_one, mul_one]

/-- `P^J_{d',d} = 0` unless `d' ≤ d` in the Bruhat order ([Deo] §3). -/
theorem parabolicKLPoly_eq_zero_of_not_bruhatLE {d' d : cs.minCosetReps J}
    (h : ¬cs.BruhatLE d' d) : parabolicKLPoly hχ d' d = 0 := by
  refine T_mul_aeval_T_two_injective (-(ℓ d : ℤ)) ?_
  simp only
  rw [← repr_parabolicKLBasis, map_zero, mul_zero]
  by_contra hne
  exact h (bruhatLE_of_repr_parabolicKLBasis_ne_zero hχ hne)

theorem bruhatLE_of_parabolicKLPoly_ne_zero {d' d : cs.minCosetReps J}
    (h : parabolicKLPoly hχ d' d ≠ 0) : cs.BruhatLE d' d :=
  not_not.mp fun h' ↦ h (parabolicKLPoly_eq_zero_of_not_bruhatLE hχ h')

/-- For `d' ≠ d`, the coefficient of `q^k` in `P^J_{d',d}` vanishes if `2k + ℓ(d') ≥ ℓ(d)`. -/
theorem coeff_parabolicKLPoly_eq_zero {d' d : cs.minCosetReps J} (h : d' ≠ d) {k : ℕ}
    (hk : ℓ d ≤ 2 * k + ℓ d') : (parabolicKLPoly hχ d' d).coeff k = 0 := by
  rw [coeff_parabolicKLPoly]
  have := isNeg_repr_parabolicKLBasis hχ h (-(ℓ d : ℤ) + 2 * k + ℓ d') (by omega)
  rwa [coeff_T_mul, add_sub_cancel_right] at this

/-- **The degree bound for parabolic Kazhdan–Lusztig polynomials** ([Deo] §3): for
`d' < d`, `deg P^J_{d',d} ≤ (ℓ(d) - ℓ(d') - 1)/2`, i.e. `2 deg P^J_{d',d} + ℓ(d') < ℓ(d)`. -/
theorem two_mul_natDegree_parabolicKLPoly_add_length_lt {d' d : cs.minCosetReps J}
    (hle : cs.BruhatLE d' d) (hne : d' ≠ d) :
    2 * (parabolicKLPoly hχ d' d).natDegree + ℓ d' < ℓ d := by
  have hl := hle.eq_or_length_lt.resolve_left fun h ↦ hne (Subtype.ext h)
  have : (parabolicKLPoly hχ d' d).natDegree ≤ (ℓ d - ℓ d' - 1) / 2 :=
    natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦
      coeff_parabolicKLPoly_eq_zero hχ hne (by
        have : (ℓ d - ℓ d' - 1) / 2 < N := by exact_mod_cast hN
        omega)
  omega

end Canonical

end IwahoriHeckeAlgebra
