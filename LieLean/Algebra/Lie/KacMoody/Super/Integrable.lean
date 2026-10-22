/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.Casimir
import LieLean.Algebra.Lie.KacMoody.IntegrableWeyl

/-!
# Integrable modules over contragredient Lie superalgebras

Let `A` be a generalized Cartan matrix, `p : ι → ZMod 2` a parity and `U = U(G̃(A, τ))`. For each
`i` we construct an `𝔰𝔩₂`-triple `(Hᵢ, Eᵢ, Fᵢ)` in `U`, regarded as a Lie algebra under the
commutator ([Kac78] §1.4, proof of Lemma 1.2):

* for `eᵢ` even, `(αᵢ^∨, eᵢ, fᵢ)`;
* for `eᵢ` odd, `(αᵢ^∨ / 2, eᵢ² / 2, -fᵢ² / 2)`; here `eᵢ² = [eᵢ, eᵢ] / 2` and `fᵢ²` are even.

A `U`-module `V` is *integrable* if all `eᵢ` and `fᵢ` act locally nilpotently. Applying the
`𝔰𝔩₂`-theory of `KacMoody/IntegrableWeyl.lean` to these triples we obtain, for the weight spaces
`V_λ = {v | h v = λ(h) v}` of an integrable `V`:

* `⟨λ, αᵢ^∨⟩ ∈ ℤ` if `V_λ ≠ 0`, and `⟨λ, αᵢ^∨⟩ ∈ 2ℤ` if moreover `eᵢ` is odd ([Kac78] Lemma 1.2;
  this is where the condition that `aᵢⱼ` is even for odd `i` comes from);
* `dim V_λ = dim V_{rᵢ λ}`, `rᵢ λ = λ - ⟨λ, αᵢ^∨⟩ αᵢ`, hence `dim V_{w λ} = dim V_λ` for all `w`
  in the Weyl group `W` of `A` ([Kac78] Prop. 1.4 (b) for the adjoint module, cf. [Kac] Prop. 3.7).

For odd `eᵢ`, the reflection `rᵢ` is the reflection of the even root `2αᵢ`: `⟨λ, (2αᵢ)^∨⟩ =
⟨λ, αᵢ^∨⟩ / 2` is the eigenvalue of `Hᵢ`, and `Fᵢⁿ` moves weights by `-2n αᵢ`.

## Main definitions

* `Matrix.Realization.SuperEnveloping.sl2H`, `sl2E`, `sl2F`: the triple.
* `Matrix.Realization.SuperEnveloping.IsIntegrable`: `eᵢ`, `fᵢ` act locally nilpotently;
  `IsIntegrableAt` is the same condition at a single node `i`.

## Main results

* `Matrix.Realization.SuperEnveloping.isSl2Triple`: `(Hᵢ, Eᵢ, Fᵢ)` is an `𝔰𝔩₂`-triple.
* `Matrix.Realization.SuperEnveloping.exists_int_of_modWeightSpace_ne_bot`,
  `exists_int_mul_two_of_modWeightSpace_ne_bot`: integrality of weights.
* `Matrix.Realization.SuperEnveloping.rank_modWeightSpace_reflection`,
  `rank_modWeightSpace_weylGroup`: `W`-invariance of weight multiplicities.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2–1.4.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.6–3.7.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

attribute [local instance] LieRing.ofAssociativeRing LieRingModule.ofAssociativeModule
  LieModule.ofAssociativeModule

/-! ### The `𝔰𝔩₂`-triples -/

/-- The degree `dᵢ` of the triple at `i`: `2` if `eᵢ` is odd, `1` otherwise. -/
def sl2Deg (i : ι) : ℕ := if p i = 1 then 2 else 1

/-- The coroot `αᵢ^∨ / dᵢ` of the triple at `i`. -/
def sl2Coroot (i : ι) : H := ((sl2Deg p i : ℕ) : K)⁻¹ • P.coroot i

/-- `Hᵢ = h(αᵢ^∨ / dᵢ)`. -/
def sl2H (i : ι) : 𝒰 := h P p (sl2Coroot P p i)

/-- `Eᵢ = eᵢ` for `eᵢ` even, `eᵢ² / 2` for `eᵢ` odd. -/
def sl2E (i : ι) : 𝒰 := if p i = 1 then (2 : K)⁻¹ • e P p i ^ 2 else e P p i

/-- `Fᵢ = fᵢ` for `eᵢ` even, `-fᵢ² / 2` for `eᵢ` odd. -/
def sl2F (i : ι) : 𝒰 := if p i = 1 then -((2 : K)⁻¹ • f P p i ^ 2) else f P p i

omit [Fintype ι] [DecidableEq ι] in
lemma sl2Deg_pos (i : ι) : 0 < sl2Deg p i := by unfold sl2Deg; split_ifs <;> norm_num

section Relations

variable (hA : A.IsGeneralizedCartan)
include hA

lemma h_coroot_mul_e (i : ι) :
    h P p (P.coroot i) * e P p i = e P p i * h P p (P.coroot i) + (2 : K) • e P p i := by
  rw [h_mul_e, P.root_coroot_self hA]

lemma h_coroot_mul_f (i : ι) :
    h P p (P.coroot i) * f P p i = f P p i * h P p (P.coroot i) - (2 : K) • f P p i := by
  rw [h_mul_f, P.root_coroot_self hA]

/-- For odd `eᵢ`: `[αᵢ^∨, eᵢ²] = 4 eᵢ²`. -/
lemma h_coroot_mul_e_sq (i : ι) :
    h P p (P.coroot i) * e P p i ^ 2 =
      e P p i ^ 2 * h P p (P.coroot i) + (4 : K) • e P p i ^ 2 := by
  have h₁ := h_coroot_mul_e P p hA i
  calc h P p (P.coroot i) * e P p i ^ 2
      = (h P p (P.coroot i) * e P p i) * e P p i := by rw [sq, mul_assoc]
    _ = e P p i * (h P p (P.coroot i) * e P p i) + (2 : K) • (e P p i * e P p i) := by
        rw [h₁, add_mul, mul_assoc, smul_mul_assoc, h₁]
    _ = _ := by
        rw [h₁, mul_add, ← mul_assoc, mul_smul_comm, ← sq, add_assoc, ← add_smul]
        norm_num

/-- For odd `eᵢ`: `[αᵢ^∨, fᵢ²] = -4 fᵢ²`. -/
lemma h_coroot_mul_f_sq (i : ι) :
    h P p (P.coroot i) * f P p i ^ 2 =
      f P p i ^ 2 * h P p (P.coroot i) - (4 : K) • f P p i ^ 2 := by
  have h₁ := h_coroot_mul_f P p hA i
  calc h P p (P.coroot i) * f P p i ^ 2
      = (h P p (P.coroot i) * f P p i) * f P p i := by rw [sq, mul_assoc]
    _ = f P p i * (h P p (P.coroot i) * f P p i) - (2 : K) • (f P p i * f P p i) := by
        rw [h₁, sub_mul, mul_assoc, smul_mul_assoc, h₁]
    _ = _ := by
        rw [h₁, mul_sub, ← mul_assoc, mul_smul_comm, ← sq, sub_sub, ← add_smul]
        norm_num

omit hA in
/-- For odd `eᵢ`: `eᵢ fᵢ = -fᵢ eᵢ + αᵢ^∨`. -/
lemma e_mul_f_self_of_odd {i : ι} (hi : p i = 1) :
    e P p i * f P p i = h P p (P.coroot i) - f P p i * e P p i := by
  rw [e_mul_f, superSign_self, ite_eq_left hi, ite_eq_left rfl, neg_one_smul]
  abel

/-- For odd `eᵢ`: `eᵢ² fᵢ = fᵢ eᵢ² - 2 eᵢ`. -/
lemma e_sq_mul_f_of_odd {i : ι} (hi : p i = 1) :
    e P p i ^ 2 * f P p i = f P p i * e P p i ^ 2 - (2 : K) • e P p i := by
  have h₀ := e_mul_f_self_of_odd P p hi
  calc e P p i ^ 2 * f P p i = e P p i * (e P p i * f P p i) := by rw [sq, mul_assoc]
    _ = e P p i * h P p (P.coroot i) - (e P p i * f P p i) * e P p i := by
        conv_lhs => rw [h₀]
        rw [mul_sub, ← mul_assoc]
    _ = e P p i * h P p (P.coroot i) - h P p (P.coroot i) * e P p i +
          f P p i * e P p i ^ 2 := by
        conv_lhs => rw [h₀]
        rw [sub_mul, sq, mul_assoc]
        abel
    _ = _ := by
        rw [h_coroot_mul_e P p hA]
        abel

/-- For odd `eᵢ`: `eᵢ² fᵢ² = fᵢ² eᵢ² - 2 αᵢ^∨`. -/
lemma e_sq_mul_f_sq_of_odd {i : ι} (hi : p i = 1) :
    e P p i ^ 2 * f P p i ^ 2 = f P p i ^ 2 * e P p i ^ 2 - (2 : K) • h P p (P.coroot i) := by
  have h₀ := e_mul_f_self_of_odd P p hi
  have h₁ := e_sq_mul_f_of_odd P p hA hi
  calc e P p i ^ 2 * f P p i ^ 2 = (e P p i ^ 2 * f P p i) * f P p i := by
        rw [sq (f P p i), mul_assoc]
    _ = f P p i * (e P p i ^ 2 * f P p i) - (2 : K) • (e P p i * f P p i) := by
        rw [h₁, sub_mul, mul_assoc, smul_mul_assoc, h₁]
    _ = _ := by
        rw [h₁, h₀, mul_sub, ← mul_assoc, ← sq, mul_smul_comm, smul_sub]
        abel

end Relations

variable [CharZero K]

/-- `(Hᵢ, Eᵢ, Fᵢ)` is an `𝔰𝔩₂`-triple in `U(G̃(A, τ))` ([Kac78] §1.4). -/
theorem isSl2Triple {hA : A.IsGeneralizedCartan} (i : ι) :
    IsSl2Triple (sl2H P p i) (sl2E P p i) (sl2F P p i) := by
  have hd : ((sl2Deg p i : ℕ) : K) ≠ 0 := by exact_mod_cast (sl2Deg_pos p i).ne'
  have hH : sl2H P p i ≠ 0 := by
    rw [sl2H, Ne, ← map_zero (h P p), (h_injective P p).eq_iff, sl2Coroot, smul_eq_zero, not_or]
    exact ⟨inv_ne_zero hd, P.linearIndependent_coroot.ne_zero i⟩
  by_cases hi : p i = 1
  · have hH' : sl2H P p i = (2 : K)⁻¹ • h P p (P.coroot i) := by
      rw [sl2H, sl2Coroot, sl2Deg, ite_eq_left hi, map_smul]; norm_num
    have hE : sl2E P p i = (2 : K)⁻¹ • e P p i ^ 2 := ite_eq_left hi
    have hF : sl2F P p i = -((2 : K)⁻¹ • f P p i ^ 2) := ite_eq_left hi
    refine ⟨hH, ?_, ?_, ?_⟩
    · rw [hH', hE, hF, LieRing.of_associative_ring_bracket]
      simp only [mul_neg, neg_mul, smul_mul_smul_comm, e_sq_mul_f_sq_of_odd P p hA hi]
      module
    · rw [hH', hE, LieRing.of_associative_ring_bracket]
      simp only [smul_mul_smul_comm, h_coroot_mul_e_sq P p hA]
      module
    · rw [hH', hF, LieRing.of_associative_ring_bracket]
      simp only [mul_neg, neg_mul, smul_mul_smul_comm, h_coroot_mul_f_sq P p hA]
      module
  · have hH' : sl2H P p i = h P p (P.coroot i) := by
      rw [sl2H, sl2Coroot, sl2Deg, ite_eq_right hi]; simp
    have hE : sl2E P p i = e P p i := ite_eq_right hi
    have hF : sl2F P p i = f P p i := ite_eq_right hi
    refine ⟨hH, ?_, ?_, ?_⟩
    · rw [hH', hE, hF, LieRing.of_associative_ring_bracket, e_mul_f, superSign_self,
        ite_eq_right hi, ite_eq_left rfl, one_smul, add_sub_cancel_left]
    · rw [hH', hE, LieRing.of_associative_ring_bracket, h_coroot_mul_e P p hA, add_sub_cancel_left,
        two_smul, two_smul]
    · rw [hH', hF, LieRing.of_associative_ring_bracket, h_coroot_mul_f P p hA, sub_sub_cancel_left,
        two_smul, two_smul]

/-! ### Weight spaces -/

variable {P p} {V : Type*} [AddCommGroup V] [Module K V] [Module (P.SuperEnveloping p) V]
  [IsScalarTower K (P.SuperEnveloping p) V]

omit [CharZero K] in
lemma toEnd_pow_apply (u : 𝒰) (n : ℕ) (v : V) : (toEnd K 𝒰 V u ^ n) v = u ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, pow_succ', mul_smul]; rfl

omit [CharZero K] in
lemma e_smul_mem_modWeightSpace {μ : Dual K H} {v : V} (hv : v ∈ modWeightSpace P p V μ)
    (i : ι) : e P p i • v ∈ modWeightSpace P p V (μ + P.root i) := fun a ↦ by
  rw [← mul_smul, h_mul_e, add_smul, mul_smul, hv a, smul_assoc, smul_comm, LinearMap.add_apply,
    add_smul, add_comm]

omit [CharZero K] in
lemma f_smul_mem_modWeightSpace {μ : Dual K H} {v : V} (hv : v ∈ modWeightSpace P p V μ)
    (i : ι) : f P p i • v ∈ modWeightSpace P p V (μ - P.root i) := fun a ↦ by
  rw [← mul_smul, h_mul_f, sub_smul, mul_smul, hv a, smul_assoc, smul_comm, LinearMap.sub_apply,
    sub_smul]

omit [CharZero K] in
lemma e_pow_smul_mem_modWeightSpace {μ : Dual K H} {v : V} (hv : v ∈ modWeightSpace P p V μ)
    (i : ι) (n : ℕ) : e P p i ^ n • v ∈ modWeightSpace P p V (μ + n • P.root i) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', mul_smul, succ_nsmul, ← add_assoc]
    exact e_smul_mem_modWeightSpace ih i

omit [CharZero K] in
lemma f_pow_smul_mem_modWeightSpace {μ : Dual K H} {v : V} (hv : v ∈ modWeightSpace P p V μ)
    (i : ι) (n : ℕ) : f P p i ^ n • v ∈ modWeightSpace P p V (μ - n • P.root i) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', mul_smul, succ_nsmul, ← sub_sub]
    exact f_smul_mem_modWeightSpace ih i

omit [CharZero K] in
lemma sl2E_pow_smul_mem {μ : Dual K H} {v : V} (hv : v ∈ modWeightSpace P p V μ) (i : ι)
    (n : ℕ) : sl2E P p i ^ n • v ∈ modWeightSpace P p V (μ + (sl2Deg p i * n) • P.root i) := by
  unfold sl2E sl2Deg
  split_ifs
  · rw [smul_pow, smul_assoc, ← pow_mul]
    exact Submodule.smul_mem _ _ (e_pow_smul_mem_modWeightSpace hv i _)
  · simpa using e_pow_smul_mem_modWeightSpace hv i n

omit [CharZero K] in
lemma sl2F_pow_smul_mem {μ : Dual K H} {v : V} (hv : v ∈ modWeightSpace P p V μ) (i : ι)
    (n : ℕ) : sl2F P p i ^ n • v ∈ modWeightSpace P p V (μ - (sl2Deg p i * n) • P.root i) := by
  unfold sl2F sl2Deg
  split_ifs
  · rw [← neg_smul, smul_pow, smul_assoc, ← pow_mul]
    exact Submodule.smul_mem _ _ (f_pow_smul_mem_modWeightSpace hv i _)
  · simpa using f_pow_smul_mem_modWeightSpace hv i n

omit [CharZero K] in
lemma sl2H_smul {μ : Dual K H} {v : V} (hv : v ∈ modWeightSpace P p V μ) (i : ι) :
    ⁅sl2H P p i, v⁆ = μ (sl2Coroot P p i) • v := hv _

/-! ### Integrable modules -/

variable (P p V) in
/-- A `U(G̃(A, τ))`-module is *integrable at `i`* if `eᵢ` and `fᵢ` act locally nilpotently. -/
def IsIntegrableAt (i : ι) : Prop :=
  ∀ v : V, (∃ n, e P p i ^ n • v = 0) ∧ ∃ n, f P p i ^ n • v = 0

variable (P p V) in
/-- A `U(G̃(A, τ))`-module is *integrable* if all `eᵢ` and `fᵢ` act locally nilpotently. -/
def IsIntegrable : Prop :=
  ∀ i, IsIntegrableAt P p V i

omit [CharZero K] in
lemma IsIntegrableAt.exists_sl2E {i : ι} (hV : IsIntegrableAt P p V i) (v : V) :
    ∃ n, (toEnd K 𝒰 V (sl2E P p i) ^ n) v = 0 := by
  obtain ⟨n, hn⟩ := (hV v).1
  refine ⟨n, ?_⟩
  rw [toEnd_pow_apply]
  unfold sl2E
  split_ifs
  · rw [smul_pow, smul_assoc, ← pow_mul, mul_comm, pow_mul, sq, mul_smul, hn, smul_zero,
      smul_zero]
  · exact hn

omit [CharZero K] in
lemma IsIntegrableAt.exists_sl2F {i : ι} (hV : IsIntegrableAt P p V i) (v : V) :
    ∃ n, (toEnd K 𝒰 V (sl2F P p i) ^ n) v = 0 := by
  obtain ⟨n, hn⟩ := (hV v).2
  refine ⟨n, ?_⟩
  rw [toEnd_pow_apply]
  unfold sl2F
  split_ifs
  · rw [← neg_smul, smul_pow, smul_assoc, ← pow_mul, mul_comm, pow_mul, sq, mul_smul, hn,
      smul_zero, smul_zero]
  · exact hn

omit [CharZero K] in
lemma IsIntegrable.exists_sl2E (hV : IsIntegrable P p V) (i : ι) (v : V) :
    ∃ n, (toEnd K 𝒰 V (sl2E P p i) ^ n) v = 0 :=
  (hV i).exists_sl2E v

omit [CharZero K] in
lemma IsIntegrable.exists_sl2F (hV : IsIntegrable P p V) (i : ι) (v : V) :
    ∃ n, (toEnd K 𝒰 V (sl2F P p i) ^ n) v = 0 :=
  (hV i).exists_sl2F v

variable (hA : A.IsGeneralizedCartan)
include hA

/-- The weights of a module integrable at `i` are integral on the `𝔰𝔩₂`-coroot `αᵢ^∨ / dᵢ`. -/
theorem exists_int_of_modWeightSpace_ne_bot_of_isIntegrableAt {i : ι}
    (hV : IsIntegrableAt P p V i) {μ : Dual K H} (hμ : modWeightSpace P p V μ ≠ ⊥) :
    ∃ z : ℤ, μ (sl2Coroot P p i) = z := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  obtain ⟨k, hk⟩ := hV.exists_sl2E v
  exact (isSl2Triple P p (hA := hA) i).exists_int_of_lie_h_eq_smul hV.exists_sl2F hk
    (sl2H_smul hv i) hv0

/-- The weights of an integrable module are integral on the `𝔰𝔩₂`-coroots: if `V_λ ≠ 0` then
`⟨λ, αᵢ^∨ / dᵢ⟩ ∈ ℤ` ([Kac78] Lemma 1.2). -/
theorem exists_int_of_modWeightSpace_ne_bot' (hV : IsIntegrable P p V) {μ : Dual K H}
    (hμ : modWeightSpace P p V μ ≠ ⊥) (i : ι) : ∃ z : ℤ, μ (sl2Coroot P p i) = z :=
  exists_int_of_modWeightSpace_ne_bot_of_isIntegrableAt hA (hV i) hμ

omit hA [DecidableEq ι] in
lemma apply_coroot_eq (μ : Dual K H) (i : ι) :
    μ (P.coroot i) = (sl2Deg p i : K) * μ (sl2Coroot P p i) := by
  have hd : ((sl2Deg p i : ℕ) : K) ≠ 0 := by exact_mod_cast (sl2Deg_pos p i).ne'
  rw [sl2Coroot, map_smul, smul_eq_mul, mul_inv_cancel_left₀ hd]

/-- The weights of an integrable module are integral: if `V_λ ≠ 0` then `⟨λ, αᵢ^∨⟩ ∈ ℤ`. -/
theorem exists_int_of_modWeightSpace_ne_bot (hV : IsIntegrable P p V) {μ : Dual K H}
    (hμ : modWeightSpace P p V μ ≠ ⊥) (i : ι) : ∃ z : ℤ, μ (P.coroot i) = z := by
  obtain ⟨z, hz⟩ := exists_int_of_modWeightSpace_ne_bot' hA hV hμ i
  exact ⟨sl2Deg p i * z, by rw [apply_coroot_eq, hz]; push_cast; ring⟩

/-- For odd `eᵢ`, the weights of an integrable module satisfy `⟨λ, αᵢ^∨⟩ ∈ 2ℤ`
([Kac78] Lemma 1.2). -/
theorem exists_int_mul_two_of_modWeightSpace_ne_bot (hV : IsIntegrable P p V) {μ : Dual K H}
    (hμ : modWeightSpace P p V μ ≠ ⊥) {i : ι} (hi : p i = 1) :
    ∃ z : ℤ, μ (P.coroot i) = 2 * z := by
  obtain ⟨z, hz⟩ := exists_int_of_modWeightSpace_ne_bot' hA hV hμ i
  refine ⟨z, ?_⟩
  rw [apply_coroot_eq, hz, sl2Deg, ite_eq_left hi]
  norm_num

/-- For an integrable module, `dim V_λ ≤ dim V_{rᵢ λ}`: the map `Fᵢⁿ` (if `n = ⟨λ, αᵢ^∨ / dᵢ⟩ ≥ 0`)
or `Eᵢ⁻ⁿ` (if `n ≤ 0`) embeds `V_λ` into `V_{rᵢ λ}`. -/
theorem rank_modWeightSpace_le_reflection_of_isIntegrableAt {i : ι}
    (hV : IsIntegrableAt P p V i) (μ : Dual K H) :
    Module.rank K (modWeightSpace P p V μ) ≤
      Module.rank K (modWeightSpace P p V (P.reflection hA i μ)) := by
  by_cases hμ : modWeightSpace P p V μ = ⊥
  · rw [hμ, rank_bot]; exact zero_le
  obtain ⟨z, hz⟩ := exists_int_of_modWeightSpace_ne_bot_of_isIntegrableAt hA hV hμ
  have t := isSl2Triple P p (hA := hA) i
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · -- `⟨λ, αᵢ^∨ / dᵢ⟩ = n ≥ 0`: `Fᵢⁿ : V_λ → V_{λ - dᵢ n αᵢ}` is injective
    have hr : P.reflection hA i μ = μ - (sl2Deg p i * n) • P.root i := by
      rw [reflection_apply, apply_coroot_eq, hz, ← Nat.cast_smul_eq_nsmul K]
      push_cast; rfl
    let φ : modWeightSpace P p V μ →ₗ[K] modWeightSpace P p V (P.reflection hA i μ) :=
      (toEnd K 𝒰 V (sl2F P p i) ^ n).restrict fun v hv ↦ by
        rw [hr, toEnd_pow_apply]; exact sl2F_pow_smul_mem hv i n
    refine LinearMap.rank_le_of_injective φ (LinearMap.ker_eq_bot.mp ?_)
    refine LinearMap.ker_eq_bot'.mpr fun v hv ↦ Subtype.ext ?_
    obtain ⟨k, hk⟩ := hV.exists_sl2E v
    refine t.eq_zero_of_pow_toEnd_f_eq_zero hk ?_ (congr_arg Subtype.val hv)
    rw [sl2H_smul v.2 i, hz, Int.cast_natCast]
  · -- `⟨λ, αᵢ^∨ / dᵢ⟩ = -n ≤ 0`: `Eᵢⁿ : V_λ → V_{λ + dᵢ n αᵢ}` is injective
    have hr : P.reflection hA i μ = μ + (sl2Deg p i * n) • P.root i := by
      rw [reflection_apply, apply_coroot_eq, hz, ← Nat.cast_smul_eq_nsmul K]
      push_cast
      module
    let φ : modWeightSpace P p V μ →ₗ[K] modWeightSpace P p V (P.reflection hA i μ) :=
      (toEnd K 𝒰 V (sl2E P p i) ^ n).restrict fun v hv ↦ by
        rw [hr, toEnd_pow_apply]; exact sl2E_pow_smul_mem hv i n
    refine LinearMap.rank_le_of_injective φ (LinearMap.ker_eq_bot.mp ?_)
    refine LinearMap.ker_eq_bot'.mpr fun v hv ↦ Subtype.ext ?_
    obtain ⟨k, hk⟩ := hV.exists_sl2F v
    refine t.symm.eq_zero_of_pow_toEnd_f_eq_zero hk ?_ (congr_arg Subtype.val hv)
    rw [neg_lie, sl2H_smul v.2 i, hz, Int.cast_neg, Int.cast_natCast, neg_smul, neg_neg]

/-- For an integrable module, `dim V_λ ≤ dim V_{rᵢ λ}`. -/
theorem rank_modWeightSpace_le_reflection (hV : IsIntegrable P p V) (i : ι) (μ : Dual K H) :
    Module.rank K (modWeightSpace P p V μ) ≤
      Module.rank K (modWeightSpace P p V (P.reflection hA i μ)) :=
  rank_modWeightSpace_le_reflection_of_isIntegrableAt hA (hV i) μ

/-- For a module integrable at `i`, `dim V_{rᵢ λ} = dim V_λ`. -/
theorem rank_modWeightSpace_reflection_of_isIntegrableAt {i : ι}
    (hV : IsIntegrableAt P p V i) (μ : Dual K H) :
    Module.rank K (modWeightSpace P p V (P.reflection hA i μ)) =
      Module.rank K (modWeightSpace P p V μ) := by
  refine le_antisymm ?_ (rank_modWeightSpace_le_reflection_of_isIntegrableAt hA hV μ)
  have := rank_modWeightSpace_le_reflection_of_isIntegrableAt hA hV (P.reflection hA i μ)
  rwa [reflection_reflection] at this

/-- For an integrable module, `dim V_{rᵢ λ} = dim V_λ`. -/
theorem rank_modWeightSpace_reflection (hV : IsIntegrable P p V) (i : ι) (μ : Dual K H) :
    Module.rank K (modWeightSpace P p V (P.reflection hA i μ)) =
      Module.rank K (modWeightSpace P p V μ) :=
  rank_modWeightSpace_reflection_of_isIntegrableAt hA (hV i) μ

/-- For an integrable module `V`, the weight multiplicities are `W`-invariant:
`dim V_{w λ} = dim V_λ` for all `w ∈ W` ([Kac78] Prop. 1.4 (b), cf. [Kac] Prop. 3.7 (a)). -/
theorem rank_modWeightSpace_weylGroup (hV : IsIntegrable P p V) {w : Dual K H ≃ₗ[K] Dual K H}
    (hw : w ∈ P.weylGroup hA) (μ : Dual K H) :
    Module.rank K (modWeightSpace P p V (w μ)) = Module.rank K (modWeightSpace P p V μ) := by
  refine P.weylGroup_induction hA
    (p := fun w ↦ ∀ μ, Module.rank K (modWeightSpace P p V (w μ)) =
      Module.rank K (modWeightSpace P p V μ))
    (fun μ ↦ rfl) (fun i w ih μ ↦ ?_) hw μ
  rw [LinearEquiv.mul_apply, rank_modWeightSpace_reflection hA hV, ih]

/-- The set of weights of an integrable module is `W`-invariant. -/
theorem modWeightSpace_weylGroup_eq_bot_iff (hV : IsIntegrable P p V)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA) (μ : Dual K H) :
    modWeightSpace P p V (w μ) = ⊥ ↔ modWeightSpace P p V μ = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← Submodule.rank_eq_zero, rank_modWeightSpace_weylGroup hA hV hw]

end Matrix.Realization.SuperEnveloping
