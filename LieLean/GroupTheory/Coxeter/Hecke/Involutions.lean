/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.Bar
import LieLean.GroupTheory.Coxeter.Hecke.Presentation

/-!
# Involutions and one-dimensional representations of the Iwahori–Hecke algebra

Let `𝓗 = 𝓗_q(W)` be the Iwahori–Hecke algebra of a Coxeter system over a commutative ring `R`
(normalization `(T_s - q)(T_s + 1) = 0`). Using the presentation of `𝓗`
(`IwahoriHeckeAlgebra.lift`) we construct:

* the one-dimensional representations `ind : T_w ↦ q^{ℓ(w)}` ("index") and
  `sgn : T_w ↦ (-1)^{ℓ(w)}` ("sign") ([GP] Rem. 8.1.3);
* the `R`-linear anti-automorphism `T_w ↦ T_{w⁻¹}` (`antiInvolution`, an algebra isomorphism
  `𝓗 ≃ₐ[R] 𝓗ᵐᵒᵖ`), an involution;
* for `q` a unit, the "sign twist" automorphism `T_s ↦ -q T_s⁻¹ = (q - 1) - T_s` (`signTwist`),
  an involution with `T_w ↦ (-q)^{ℓ(w)} T_{w⁻¹}⁻¹`, which interchanges `ind` and `sgn`;
* its composite with the bar involution, `barSignTwist`, the `σ`-semilinear ring involution
  `Σ a_w T_w ↦ Σ σ(a_w) (-q⁻¹)^{ℓ(w)} T_w` used by Kazhdan–Lusztig ([KL] §1, the
  map `j`).

## Main definitions

* `IwahoriHeckeAlgebra.ind`, `IwahoriHeckeAlgebra.sgn`: `𝓗 →ₐ[R] R`.
* `IwahoriHeckeAlgebra.antiInvolution : 𝓗 ≃ₐ[R] 𝓗ᵐᵒᵖ`, and `antiInvolutionSelf : 𝓗 ≃ₗ[R] 𝓗`, the
  same map viewed as a linear self-equivalence of `𝓗`.
* `IwahoriHeckeAlgebra.signTwist : 𝓗 ≃ₐ[R] 𝓗` (for `q` a unit).
* `IwahoriHeckeAlgebra.barSignTwist : 𝓗 →+* 𝓗` (for `σ : R →+* R` with `σ(q) q = 1`).

## Main results

* `IwahoriHeckeAlgebra.ind_T`, `sgn_T`: `ind T_w = q^{ℓ(w)}`, `sgn T_w = (-1)^{ℓ(w)}`.
* `IwahoriHeckeAlgebra.antiInvolution_T`: `T_w ↦ T_{w⁻¹}`; `antiInvolutionSelf_mul`,
  `antiInvolutionSelf_antiInvolution`.
* `IwahoriHeckeAlgebra.signTwist_T`: `T_w ↦ (-q)^{ℓ(w)} T_{w⁻¹}⁻¹`;
  `signTwist_symm`, `sgn_comp_signTwist`, `ind_comp_signTwist`.
* `IwahoriHeckeAlgebra.barSignTwist_T`, `barSignTwist_smul`, `barSignTwist_barSignTwist`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184.
* [GP] M. Geck, G. Pfeiffer, *Characters of finite Coxeter groups and Iwahori–Hecke algebras*,
  LMS Monographs 21, OUP 2000, Ch. 8.
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, Ch. 7.
-/

open MulOpposite

namespace CoxeterMatrix

open CoxeterSystem

variable {B : Type*} (M : CoxeterMatrix B)

/-- A constant family satisfies the braid relations. -/
theorem isBraidLiftable_const {G : Type*} [Monoid G] (c : G) :
    M.IsBraidLiftable (fun _ : B ↦ c) := by
  intro i j _ _
  simp only [List.map_const', length_alternatingWord, M.symmetric i j]

variable {M}

/-- The braid relations for reversed braid words. -/
theorem IsBraidLiftable.reverse {G : Type*} [Monoid G] {g : B → G} (hg : M.IsBraidLiftable g)
    {i j : B} (hij : i ≠ j) (hm : M i j ≠ 0) :
    (((braidWord M i j).reverse).map g).prod = (((braidWord M j i).reverse).map g).prod := by
  have h := hg i j hij hm
  simp only [braidWord, M.symmetric j i] at h ⊢
  rw [reverse_alternatingWord, reverse_alternatingWord]
  split_ifs
  · exact h.symm
  · exact h

/-- If the `g i` satisfy the braid relations in `G`, so do the `op (g i)` in `Gᵐᵒᵖ`. -/
theorem IsBraidLiftable.op {G : Type*} [Monoid G] {g : B → G} (hg : M.IsBraidLiftable g) :
    M.IsBraidLiftable (MulOpposite.op ∘ g) := by
  have key : ∀ ω : List B,
      (ω.map (MulOpposite.op ∘ g)).prod = MulOpposite.op ((ω.reverse.map g).prod) := by
    intro ω
    rw [op_list_prod, List.map_reverse, List.map_reverse, List.reverse_reverse, List.map_map]
  intro i j hij hm
  rw [key, key, hg.reverse hij hm]

/-- If the `g i` satisfy the braid relations in a group, so do their inverses. -/
theorem IsBraidLiftable.inv {G : Type*} [Group G] {g : B → G} (hg : M.IsBraidLiftable g) :
    M.IsBraidLiftable (fun i ↦ (g i)⁻¹) := by
  have key : ∀ ω : List B, (ω.map (fun i ↦ (g i)⁻¹)).prod = ((ω.reverse.map g).prod)⁻¹ := by
    intro ω
    rw [List.prod_inv_reverse, List.map_reverse, List.map_reverse, List.reverse_reverse,
      List.map_map]
    rfl
  intro i j hij hm
  rw [key, key, hg.reverse hij hm]

/-- If the `g i` satisfy the braid relations in an `R`-algebra, so do the `c • g i`. -/
theorem IsBraidLiftable.smul {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {g : B → A}
    (hg : M.IsBraidLiftable g) (c : R) : M.IsBraidLiftable (fun i ↦ c • g i) := by
  have key : ∀ ω : List B, (ω.map (fun i ↦ c • g i)).prod = c ^ ω.length • (ω.map g).prod := by
    intro ω
    induction ω with
    | nil => simp
    | cons a ω ih =>
      rw [List.map_cons, List.prod_cons, ih, smul_mul_smul_comm, List.map_cons, List.prod_cons,
        List.length_cons, pow_succ']
  intro i j hij hm
  rw [key, key, hg i j hij hm]
  simp only [braidWord, length_alternatingWord, M.symmetric i j]

variable {R : Type*} [CommRing R] {q : R}

/-- If the `t i` satisfy the Hecke relations in `A`, so do the `op (t i)` in `Aᵐᵒᵖ`. -/
theorem IsHeckeFamily.op {A : Type*} [Ring A] [Algebra R A] {t : B → A}
    (ht : M.IsHeckeFamily q t) : M.IsHeckeFamily q (MulOpposite.op ∘ t) where
  quadratic i := by
    have hc : Commute (t i - algebraMap R A q) (t i + 1) :=
      ((Commute.refl (t i)).sub_left (Algebra.commute_algebraMap_left q (t i))).add_right
        (Commute.one_right _)
    simp only [Function.comp_apply]
    rw [MulOpposite.algebraMap_apply, ← op_sub, ← op_one, ← op_add, ← op_mul, ← hc.eq,
      ht.quadratic i, op_zero]
  braid := ht.braid.op

end CoxeterMatrix

namespace IwahoriHeckeAlgebra

open CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {R : Type*} [CommRing R] (q : R)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

/-! ### One-dimensional representations -/

/-- The "index" representation `ind : 𝓗 → R`, `T_s ↦ q`, so `T_w ↦ q^{ℓ(w)}` (`ind_T`)
([GP] Rem. 8.1.3; at `q = 1` it is the trivial representation of `W`). -/
noncomputable def ind : IwahoriHeckeAlgebra cs q →ₐ[R] R :=
  lift cs q R ⟨fun _ ↦ q, by simp, M.isBraidLiftable_const q⟩

/-- The "sign" representation `sgn : 𝓗 → R`, `T_s ↦ -1`, so `T_w ↦ (-1)^{ℓ(w)}` (`sgn_T`)
([GP] Rem. 8.1.3; at `q = 1` it is the sign representation of `W`). -/
noncomputable def sgn : IwahoriHeckeAlgebra cs q →ₐ[R] R :=
  lift cs q R ⟨fun _ ↦ -1, by simp, M.isBraidLiftable_const (-1)⟩

@[simp]
theorem ind_T_simple (i : B) : ind cs q (T cs q (s i)) = q := by
  simp [ind]

@[simp]
theorem sgn_T_simple (i : B) : sgn cs q (T cs q (s i)) = -1 := by
  simp [sgn]

/-- `ind T_w = q^{ℓ(w)}`. -/
theorem ind_T (w : W) : ind cs q (T cs q w) = q ^ ℓ w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [ind, lift_apply_T _ hω, List.map_const', List.prod_replicate, hω.eq]

/-- `sgn T_w = (-1)^{ℓ(w)}`. -/
theorem sgn_T (w : W) : sgn cs q (T cs q w) = (-1) ^ ℓ w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [sgn, lift_apply_T _ hω, List.map_const', List.prod_replicate, hω.eq]

/-! ### The anti-involution `T_w ↦ T_{w⁻¹}` -/

/-- The algebra homomorphism `𝓗 → 𝓗ᵐᵒᵖ`, `T_s ↦ op T_s`. -/
noncomputable def antiInvolutionHom :
    IwahoriHeckeAlgebra cs q →ₐ[R] (IwahoriHeckeAlgebra cs q)ᵐᵒᵖ :=
  lift cs q _ ⟨_, (isHeckeFamily_T cs q).op⟩

theorem antiInvolutionHom_T (w : W) : antiInvolutionHom cs q (T cs q w) = op (T cs q w⁻¹) := by
  induction w using cs.induction_simple_mul with
  | one => simp
  | simple_mul w i hlt ih =>
    have e : (s i * w)⁻¹ = w⁻¹ * s i := by rw [mul_inv_rev, inv_simple]
    have hlt' : ℓ w⁻¹ < ℓ (w⁻¹ * s i) := by rwa [← e, length_inv, length_inv]
    rw [← T_simple_mul_T_of_lt cs q hlt, map_mul, ih, antiInvolutionHom, lift_apply_T_simple,
      e, ← T_mul_T_simple_of_lt cs q hlt']
    rfl

/-- The linear equivalence `𝓗 ≃ 𝓗ᵐᵒᵖ`, `T_w ↦ op T_{w⁻¹}`. -/
noncomputable def antiInvolutionLinearEquiv :
    IwahoriHeckeAlgebra cs q ≃ₗ[R] (IwahoriHeckeAlgebra cs q)ᵐᵒᵖ :=
  ((basis cs q).equiv (basis cs q) (Equiv.inv W)).trans (MulOpposite.opLinearEquiv R)

theorem antiInvolutionLinearEquiv_apply (x : IwahoriHeckeAlgebra cs q) :
    antiInvolutionLinearEquiv cs q x = antiInvolutionHom cs q x := by
  induction x using induction_on cs q with
  | T w =>
    rw [antiInvolutionHom_T, antiInvolutionLinearEquiv, LinearEquiv.trans_apply, ← basis_apply,
      Module.Basis.equiv_apply, basis_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul a x hx => rw [map_smul, map_smul, hx]

/-- The anti-involution of `𝓗`: the `R`-algebra isomorphism `𝓗 ≃ₐ[R] 𝓗ᵐᵒᵖ` with
`T_w ↦ T_{w⁻¹}` (`antiInvolution_T`), i.e. the `R`-linear anti-automorphism `T_w ↦ T_{w⁻¹}` of
`𝓗`; it is an involution (`unop_antiInvolution_unop`). -/
noncomputable def antiInvolution :
    IwahoriHeckeAlgebra cs q ≃ₐ[R] (IwahoriHeckeAlgebra cs q)ᵐᵒᵖ :=
  AlgEquiv.ofLinearEquiv (antiInvolutionLinearEquiv cs q)
    (by rw [antiInvolutionLinearEquiv_apply, map_one])
    (fun x y ↦ by simp only [antiInvolutionLinearEquiv_apply, map_mul])

@[simp]
theorem antiInvolution_T (w : W) : antiInvolution cs q (T cs q w) = op (T cs q w⁻¹) := by
  rw [← antiInvolutionHom_T]
  exact antiInvolutionLinearEquiv_apply cs q _

/-- `T_w ↦ T_{w⁻¹}` is an involution. -/
theorem unop_antiInvolution_unop (x : IwahoriHeckeAlgebra cs q) :
    (antiInvolution cs q (antiInvolution cs q x).unop).unop = x := by
  induction x using induction_on cs q with
  | T w => simp
  | add x y hx hy => simp only [map_add, unop_add, hx, hy]
  | smul a x hx => simp only [map_smul, unop_smul, hx]

/-- The anti-involution `T_w ↦ T_{w⁻¹}` as an `R`-linear self-equivalence of `𝓗`: the composite
of `antiInvolution : 𝓗 ≃ₐ[R] 𝓗ᵐᵒᵖ` with `unop` (`antiInvolutionSelf_apply`). It reverses
products (`antiInvolutionSelf_mul`). -/
noncomputable def antiInvolutionSelf : IwahoriHeckeAlgebra cs q ≃ₗ[R] IwahoriHeckeAlgebra cs q :=
  (antiInvolution cs q).toLinearEquiv.trans (MulOpposite.opLinearEquiv R).symm

theorem antiInvolutionSelf_apply (x : IwahoriHeckeAlgebra cs q) :
    antiInvolutionSelf cs q x = (antiInvolution cs q x).unop := rfl

@[simp]
theorem antiInvolutionSelf_T (w : W) : antiInvolutionSelf cs q (T cs q w) = T cs q w⁻¹ := by
  simp [antiInvolutionSelf_apply]

theorem toFinsupp_antiInvolution_apply (h : IwahoriHeckeAlgebra cs q) (y : W) :
    toFinsupp cs q (antiInvolutionSelf cs q h) y = toFinsupp cs q h y⁻¹ := by
  induction h using induction_on cs q with
  | T w =>
    classical
    rw [antiInvolutionSelf_T, toFinsupp_T, toFinsupp_T, Finsupp.single_apply,
      Finsupp.single_apply]
    exact if_congr inv_eq_iff_eq_inv rfl rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | smul a x hx => simp only [map_smul, Finsupp.smul_apply, hx]

theorem antiInvolutionSelf_one : antiInvolutionSelf cs q 1 = 1 := by
  simp [antiInvolutionSelf_apply]

/-- `T_w ↦ T_{w⁻¹}` is an involution. -/
theorem antiInvolutionSelf_antiInvolution (h : IwahoriHeckeAlgebra cs q) :
    antiInvolutionSelf cs q (antiInvolutionSelf cs q h) = h :=
  unop_antiInvolution_unop cs q h

/-- The map `T_w ↦ T_{w⁻¹}` reverses products. -/
theorem antiInvolutionSelf_mul (x y : IwahoriHeckeAlgebra cs q) :
    antiInvolutionSelf cs q (x * y) = antiInvolutionSelf cs q y * antiInvolutionSelf cs q x := by
  simp [antiInvolutionSelf_apply]

theorem antiInvolutionSelf_mul_T_simple (h : IwahoriHeckeAlgebra cs q) (i : B) :
    antiInvolutionSelf cs q (h * T cs q (s i)) = T cs q (s i) * antiInvolutionSelf cs q h := by
  rw [antiInvolutionSelf_mul, antiInvolutionSelf_T, CoxeterSystem.inv_simple]

/-! ### The sign twist `T_s ↦ -q T_s⁻¹` -/

section SignTwist

variable {q} (hq : IsUnit q)

/-- The `T_s⁻¹` satisfy the braid relations. -/
theorem isBraidLiftable_TInv : M.IsBraidLiftable (fun i ↦ TInv cs hq (s i)) := by
  have hU : M.IsBraidLiftable (fun i ↦ TUnit cs hq (s i)) := by
    intro i j hij hm
    apply Units.ext
    have := (isHeckeFamily_T cs q).braid i j hij hm
    change Units.coeHom _ _ = Units.coeHom _ _
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
    exact this
  intro i j hij hm
  have := congrArg (Units.coeHom _) (hU.inv i j hij hm)
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map] at this
  exact this

/-- `-q T_s⁻¹ = (q - 1) - T_s`. -/
theorem neg_smul_TInv_simple (i : B) :
    (-q) • TInv cs hq (s i) = algebraMap R _ (q - 1) - T cs q (s i) := by
  have e : q * hq.unit⁻¹.1 = 1 := hq.mul_val_inv
  rw [TInv_simple, smul_sub, smul_smul, smul_smul, Algebra.algebraMap_eq_smul_one]
  match_scalars <;> linear_combination (-1 : R) * e

include hq in
/-- The elements `(q - 1) - T_s = -q T_s⁻¹` satisfy the Hecke relations. -/
theorem isHeckeFamily_signTwist :
    M.IsHeckeFamily q (fun i ↦ algebraMap R _ (q - 1) - T cs q (s i)) where
  quadratic i := by
    have hc : Commute (T cs q (s i) - algebraMap R _ q) (T cs q (s i) + 1) :=
      ((Commute.refl _).sub_left (Algebra.commute_algebraMap_left q _)).add_right
        (Commute.one_right _)
    have e1 : algebraMap R (IwahoriHeckeAlgebra cs q) (q - 1) - T cs q (s i) - algebraMap R _ q =
        -(T cs q (s i) + 1) := by
      rw [map_sub, map_one]; abel
    have e2 : algebraMap R (IwahoriHeckeAlgebra cs q) (q - 1) - T cs q (s i) + 1 =
        -(T cs q (s i) - algebraMap R _ q) := by
      rw [map_sub, map_one]; abel
    rw [e1, e2, neg_mul_neg, ← hc.eq, T_simple_sub_mul_T_simple_add]
  braid := by
    have := (isBraidLiftable_TInv cs hq).smul (-q)
    simp_rw [neg_smul_TInv_simple] at this
    exact this

/-- The algebra endomorphism of `𝓗` with `T_s ↦ -q T_s⁻¹ = (q - 1) - T_s`. -/
noncomputable def signTwistHom : IwahoriHeckeAlgebra cs q →ₐ[R] IwahoriHeckeAlgebra cs q :=
  lift cs q _ ⟨_, isHeckeFamily_signTwist cs hq⟩

theorem signTwistHom_T_simple (i : B) :
    signTwistHom cs hq (T cs q (s i)) = algebraMap R _ (q - 1) - T cs q (s i) := by
  simp [signTwistHom]

theorem signTwistHom_signTwistHom :
    (signTwistHom cs hq).comp (signTwistHom cs hq) = AlgHom.id R _ :=
  algHom_ext cs q fun i ↦ by simp [signTwistHom_T_simple]

/-- The *sign twist* of `𝓗` (for `q` a unit): the `R`-algebra involution with
`T_s ↦ -q T_s⁻¹ = (q - 1) - T_s`, hence `T_w ↦ (-q)^{ℓ(w)} T_{w⁻¹}⁻¹` (`signTwist_T`)
([GP] Exercise 8.2). It exchanges `ind` and `sgn` (`sgn_comp_signTwist`). -/
noncomputable def signTwist : IwahoriHeckeAlgebra cs q ≃ₐ[R] IwahoriHeckeAlgebra cs q :=
  AlgEquiv.ofAlgHom (signTwistHom cs hq) (signTwistHom cs hq) (signTwistHom_signTwistHom cs hq)
    (signTwistHom_signTwistHom cs hq)

theorem signTwist_apply (x : IwahoriHeckeAlgebra cs q) :
    signTwist cs hq x = signTwistHom cs hq x := rfl

@[simp]
theorem signTwist_T_simple (i : B) :
    signTwist cs hq (T cs q (s i)) = algebraMap R _ (q - 1) - T cs q (s i) :=
  signTwistHom_T_simple cs hq i

/-- The sign twist is an involution. -/
@[simp]
theorem signTwist_symm : (signTwist cs hq).symm = signTwist cs hq := rfl

theorem signTwist_signTwist (x : IwahoriHeckeAlgebra cs q) :
    signTwist cs hq (signTwist cs hq x) = x :=
  (signTwist cs hq).apply_symm_apply x

/-- `T_w ↦ (-q)^{ℓ(w)} T_{w⁻¹}⁻¹` under the sign twist. -/
theorem signTwist_T (w : W) :
    signTwist cs hq (T cs q w) = (-q) ^ ℓ w • TInv cs hq w⁻¹ := by
  induction w using cs.induction_simple_mul with
  | one => simp
  | simple_mul w i hlt ih =>
    have e : (s i * w)⁻¹ = w⁻¹ * s i := by rw [mul_inv_rev, inv_simple]
    have hl : ℓ (s i * w) = ℓ w + 1 := by
      rcases cs.length_simple_mul w i with h | h <;> omega
    have hl' : ℓ (w⁻¹ * s i) = ℓ w⁻¹ + ℓ (s i) := by
      rw [← e, length_inv, length_inv, hl, length_simple]
    rw [← T_simple_mul_T_of_lt cs q hlt, map_mul, ih, signTwist_T_simple,
      ← neg_smul_TInv_simple, smul_mul_smul_comm, e, TInv_mul cs hq hl', hl, pow_succ']

theorem sgn_comp_signTwist : (sgn cs q).comp (signTwist cs hq).toAlgHom = ind cs q :=
  algHom_ext cs q fun i ↦ by
    change sgn cs q (signTwist cs hq (T cs q (s i))) = ind cs q (T cs q (s i))
    rw [signTwist_T_simple, map_sub, AlgHom.commutes, sgn_T_simple, ind_T_simple,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring

theorem ind_comp_signTwist : (ind cs q).comp (signTwist cs hq).toAlgHom = sgn cs q :=
  algHom_ext cs q fun i ↦ by
    change ind cs q (signTwist cs hq (T cs q (s i))) = sgn cs q (T cs q (s i))
    rw [signTwist_T_simple, map_sub, AlgHom.commutes, sgn_T_simple, ind_T_simple,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring

end SignTwist

/-! ### The composite of the bar involution and the sign twist -/

section Bar

variable {q} (σ : R →+* R) (hσ : σ q * q = 1)

/-- The composite `j = signTwist ∘ bar` of the bar involution and the sign twist: the
`σ`-semilinear ring endomorphism of `𝓗` with `T_w ↦ (-σ(q))^{ℓ(w)} T_w` (`barSignTwist_T`),
i.e. `Σ a_w T_w ↦ Σ σ(a_w) (-q⁻¹)^{ℓ(w)} T_w`. This is the involution `j` of [KL] §1,
used to relate the bases `C_w` and `C'_w`. -/
noncomputable def barSignTwist : IwahoriHeckeAlgebra cs q →+* IwahoriHeckeAlgebra cs q :=
  (signTwist cs (isUnit_of_mul_eq_one' σ hσ)).toRingEquiv.toRingHom.comp (bar cs σ hσ)

theorem barSignTwist_apply (x : IwahoriHeckeAlgebra cs q) :
    barSignTwist cs σ hσ x = signTwist cs (isUnit_of_mul_eq_one' σ hσ) (bar cs σ hσ x) := rfl

theorem barSignTwist_smul (a : R) (x : IwahoriHeckeAlgebra cs q) :
    barSignTwist cs σ hσ (a • x) = σ a • barSignTwist cs σ hσ x := by
  rw [barSignTwist_apply, bar_smul, map_smul, barSignTwist_apply]

/-- `j(T_w) = (-σ(q))^{ℓ(w)} T_w`. -/
theorem barSignTwist_T (w : W) :
    barSignTwist cs σ hσ (T cs q w) = (-σ q) ^ ℓ w • T cs q w := by
  set hq := isUnit_of_mul_eq_one' σ hσ
  set x := barSignTwist cs σ hσ (T cs q w)
  set y := (-q) ^ ℓ w • TInv cs hq w
  set z := (-σ q) ^ ℓ w • T cs q w
  have hx : x * y = 1 := by
    have h := congrArg (signTwist cs hq) (TInv_mul_T cs hq w⁻¹)
    rwa [map_mul, map_one, signTwist_T, inv_inv, length_inv, ← bar_T cs σ hσ] at h
  have hyz : y * z = 1 := by
    rw [smul_mul_smul_comm, TInv_mul_T, ← mul_pow, neg_mul_neg, mul_comm, hσ, one_pow, one_smul]
  calc x = x * (y * z) := by rw [hyz, mul_one]
    _ = z := by rw [← mul_assoc, hx, one_mul]

/-- `j` is an involution if `σ` is. -/
theorem barSignTwist_barSignTwist (hσσ : ∀ a, σ (σ a) = a) (x : IwahoriHeckeAlgebra cs q) :
    barSignTwist cs σ hσ (barSignTwist cs σ hσ x) = x := by
  induction x using induction_on cs q with
  | T w =>
    rw [barSignTwist_T, barSignTwist_smul, barSignTwist_T, smul_smul, map_pow, map_neg, hσσ,
      ← mul_pow, neg_mul_neg, mul_comm, hσ, one_pow, one_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul a x hx => rw [barSignTwist_smul, barSignTwist_smul, hσσ, hx]

end Bar

end IwahoriHeckeAlgebra
