/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.DividedPowers

/-!
# The symmetries `T'_{i,1}` and `T''_{i,-1}` of `U`

Lusztig ([Lus] 37.1) defines four families of automorphisms `T'_{i,e}`, `T''_{i,e}` (`e = ±1`)
of `U`, with `T''_{i,-e} = (T'_{i,e})⁻¹`. The library's `Tᵢ = braidEquivOfNotRoot` is `T''_{i,1}`
and its inverse is `T'_{i,-1}`. Here we define the other two, through [Lus] 37.2.4
(`ω T'_{i,e} ω = T''_{i,e}`, `ω` the Chevalley involution):

* `braidPrimeEquiv R hv i = ω Tᵢ ω`, Lusztig's `T'_{i,1}`, and its inverse
  `(braidPrimeEquiv R hv i).symm = ω Tᵢ⁻¹ ω`, Lusztig's `T''_{i,-1}`;
* their values on the divided powers of the generators and on `K_μ`, as listed in [Lus] 37.1.3
  (`braidPrimeEquiv_qDivPow_E_self`, ..., `braidPrimeEquiv_symm_K`);
* the last formula of [Lus] 37.2.4, in the form `T''_{i,1} = T'_{i,1} ∘ D_{cᵢ}` for the diagonal
  automorphism `D_{cᵢ}` (`Eⱼ ↦ cᵢⱼ Eⱼ`, `Fⱼ ↦ cᵢⱼ⁻¹ Fⱼ`, `cᵢⱼ = (-vᵢ)^{⟨i,j'⟩}`): on an element
  `u` of `U` of degree `ν` in the root lattice, `D_{cᵢ} u = (-vᵢ)^{⟨i,ν'⟩} u`, and
  `K̃ᵢ u K̃_{-i} = vᵢ^{⟨i,ν'⟩} u` (`braidEquivOfNotRoot_eq_braidPrimeEquiv_diagHom`);
* the commutation `D_c Tⱼ = Tⱼ D_{sⱼ c}` of diagonal automorphisms with the `Tⱼ`
  (`diagHom_comp_of_hasImages`), and its consequences for words: `T'_{i₁,1} ⋯ T'_{iₙ,1}` and
  `T''_{i₁,-1} ⋯ T''_{iₙ,-1}` are `T''_{i₁,1} ⋯ T''_{iₙ,1}` and `T'_{i₁,-1} ⋯ T'_{iₙ,-1}`
  composed with diagonal automorphisms whose scalars are of the form `± v^m`
  (`exists_list_braidPrime_eq`, `exists_list_braidPrime_symm_eq`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 37.1.2, 37.1.3, 37.2.4.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-! ### Diagonal automorphisms and the `Tⱼ` -/

section Diagonal

variable (D) in
/-- The twist `(sⱼ c)ₗ = cₗ cⱼ^{-aⱼₗ}` of the scalars of a diagonal automorphism by `sⱼ`. -/
def reflChar (j : I) (c : I → kˣ) : I → kˣ := fun l ↦ c l * c j ^ (-D.cartanMatrix j l)

omit [DecidableEq I] in
lemma reflChar_self (j : I) (c : I → kˣ) : reflChar D j c j = (c j)⁻¹ := by
  change c j * c j ^ (-D.cartanMatrix j j) = (c j)⁻¹
  rw [D.cartanMatrix_self]
  group

omit [DecidableEq I] in
lemma reflChar_reflChar (j : I) (c : I → kˣ) : reflChar D j (reflChar D j c) = c := by
  funext l
  change reflChar D j c l * reflChar D j c j ^ (-D.cartanMatrix j l) = c l
  rw [reflChar_self]
  change c l * c j ^ (-D.cartanMatrix j l) * (c j)⁻¹ ^ (-D.cartanMatrix j l) = c l
  group

lemma diagHom_serreAux (c : I → kˣ) (q x : k) (m : ℕ) (a b : I) :
    diagHom R v c (serreAux q x m (E R v a) (E R v b)) =
      ((c a : k) ^ m * c b) • serreAux q x m (E R v a) (E R v b) := by
  rw [show diagHom R v c (serreAux q x m (E R v a) (E R v b)) =
      serreAux q x m ((c a : k) • E R v a) ((c b : k) • E R v b) by
    simp [serreAux, map_sum, map_smul, map_mul, map_pow], serreAux_smul_smul']

lemma diagHom_serreAux_F (c : I → kˣ) (q x : k) (m : ℕ) (a b : I) :
    diagHom R v c (serreAux q x m (F R v a) (F R v b)) =
      (((c a : k) ^ m)⁻¹ * (c b : k)⁻¹) • serreAux q x m (F R v a) (F R v b) := by
  rw [show diagHom R v c (serreAux q x m (F R v a) (F R v b)) =
      serreAux q x m ((c a : k)⁻¹ • F R v a) ((c b : k)⁻¹ • F R v b) by
    simp [serreAux, map_sum, map_smul, map_mul, map_pow], serreAux_smul_smul', inv_pow]

omit [DecidableEq I] in
lemma units_zpow_negA (c : kˣ) {j l : I} (hjl : j ≠ l) :
    ((c ^ (-D.cartanMatrix j l) : kˣ) : k) = (c : k) ^ negA D j l := by
  rw [cartanMatrix_eq_neg_negA hjl, neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]

/-- **Diagonal automorphisms and Lusztig's `Tⱼ`**: `D_c ∘ Tⱼ = Tⱼ ∘ D_{sⱼ c}` for any algebra
endomorphism `Tⱼ` with Lusztig's generator formulas (`Tⱼ` maps the root lattice degree `ν` to
`sⱼ ν`). -/
theorem diagHom_comp_of_hasImages {j : I} {T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
    (H : HasBraidGeneratorImages j T) (c : I → kˣ) :
    (diagHom R v c).comp T = T.comp (diagHom R v (reflChar D j c)) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · simp only [AlgHom.comp_apply, diagHom_E, map_smul, H.map_E]
    by_cases hl : l = j
    · subst hl
      simp only [↓reduceIte, braidEi, map_neg, map_mul, diagHom_F, Kt, diagHom_K, smul_neg,
        smul_mul_assoc, reflChar_self, Units.val_inv_eq_inv_val]
    · simp only [hl, ↓reduceIte, braidEj, map_smul, diagHom_serreAux, smul_smul, reflChar,
        Units.val_mul, units_zpow_negA _ (Ne.symm hl)]
      congr 1
      ring
  · simp only [AlgHom.comp_apply, diagHom_F, map_smul, H.map_F]
    by_cases hl : l = j
    · subst hl
      simp only [↓reduceIte, braidFi, map_neg, map_mul, diagHom_E, diagHom_K, smul_neg,
        mul_smul_comm, reflChar_self, Units.val_inv_eq_inv_val, inv_inv]
    · simp only [hl, ↓reduceIte, braidFj, map_smul, diagHom_serreAux_F, smul_smul, reflChar,
        Units.val_mul, units_zpow_negA _ (Ne.symm hl)]
      congr 1
      rw [mul_inv]
      ring
  · simp [H.map_K]

/-- The inverse form: `D_c ∘ Tⱼ⁻¹ = Tⱼ⁻¹ ∘ D_{sⱼ c}`. -/
theorem diagHom_symm_apply_of_hasImages {j : I} {T : QuantumGroup R v ≃ₐ[k] QuantumGroup R v}
    (H : HasBraidGeneratorImages j T.toAlgHom) (c : I → kˣ) (x : QuantumGroup R v) :
    diagHom R v c (T.symm x) = T.symm (diagHom R v (reflChar D j c) x) := by
  apply T.injective
  have h := DFunLike.congr_fun (diagHom_comp_of_hasImages H (reflChar D j c)) (T.symm x)
  simp only [AlgHom.comp_apply, reflChar_reflChar] at h
  have h2 : T (T.symm x) = x := T.apply_symm_apply x
  rw [AlgEquiv.apply_symm_apply]
  calc T (diagHom R v c (T.symm x)) = diagHom R v (reflChar D j c) (T (T.symm x)) := h.symm
    _ = _ := by rw [h2]

variable (v) in
/-- Scalars of the form `± v^m`. -/
def IsSignPow (c : I → kˣ) : Prop := ∀ l, ∃ e m : ℤ, (c l : k) = (-1) ^ e * v ^ m

omit [DecidableEq I] in
lemma IsSignPow.one : IsSignPow v (1 : I → kˣ) := fun _ ↦ ⟨0, 0, by simp⟩

omit [DecidableEq I] in
lemma IsSignPow.mul [NeZero v] {c c' : I → kˣ} (h : IsSignPow v c) (h' : IsSignPow v c') :
    IsSignPow v (c * c') := fun l ↦ by
  obtain ⟨e, m, he⟩ := h l
  obtain ⟨e', m', he'⟩ := h' l
  refine ⟨e + e', m + m', ?_⟩
  rw [Pi.mul_apply, Units.val_mul, he, he', zpow_add₀ (neg_ne_zero.2 one_ne_zero),
    zpow_add₀ (NeZero.ne v)]
  ring

omit [DecidableEq I] in
lemma IsSignPow.zpow_apply {c : I → kˣ} (h : IsSignPow v c) (l : I) (z : ℤ) :
    ∃ e m : ℤ, ((c l ^ z : kˣ) : k) = (-1) ^ e * v ^ m := by
  obtain ⟨e, m, he⟩ := h l
  exact ⟨e * z, m * z, by rw [Units.val_zpow_eq_zpow_val, he, mul_zpow, zpow_mul, zpow_mul]⟩

omit [DecidableEq I] in
lemma IsSignPow.reflChar [NeZero v] {c : I → kˣ} (h : IsSignPow v c) (j : I) :
    IsSignPow v (reflChar D j c) := fun l ↦ by
  obtain ⟨e, m, he⟩ := h l
  obtain ⟨e', m', he'⟩ := h.zpow_apply j (-D.cartanMatrix j l)
  refine ⟨e + e', m + m', ?_⟩
  rw [QuantumGroup.reflChar, Units.val_mul, he, he', zpow_add₀ (neg_ne_zero.2 one_ne_zero),
    zpow_add₀ (NeZero.ne v)]
  ring

omit [DecidableEq I] in
lemma IsSignPow.inv {c : I → kˣ} (h : IsSignPow v c) : IsSignPow v c⁻¹ :=
  fun l ↦ by
    obtain ⟨e, m, he⟩ := h.zpow_apply l (-1)
    exact ⟨e, m, by rw [Pi.inv_apply, ← zpow_neg_one, he]⟩

/-- `D_c(Eᵢ^{(n)}) = cᵢⁿ Eᵢ^{(n)}`. -/
lemma diagHom_qDivPow_E' (c : I → kˣ) (q : k) (n : ℕ) (i : I) :
    diagHom R v c (qDivPow q n (E R v i)) = ((c i : k) ^ n) • qDivPow q n (E R v i) := by
  simp [qDivPow, map_smul, map_pow, smul_pow, smul_smul, mul_comm]

end Diagonal

/-! ### `T'_{i,1}` and `T''_{i,-1}` -/

section Symmetries

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

variable (R) in
/-- **Lusztig's `T'_{i,1}`** ([Lus] 37.1.2 (c), via [Lus] 37.2.4: `ω T'_{i,1} ω = T''_{i,1}`):
`ω Tᵢ ω`, `ω` the Chevalley involution. Its inverse `(braidPrimeEquiv R hv i).symm` is Lusztig's
`T''_{i,-1}` ([Lus] 37.1.2 (d)). -/
def braidPrimeEquiv (i : I) : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  (chevalleyEquiv R v).trans ((braidEquivOfNotRoot R hv i).trans (chevalleyEquiv R v))

lemma braidPrimeEquiv_apply (i : I) (x : QuantumGroup R v) :
    braidPrimeEquiv R hv i x = chevalley R v (braidEquivOfNotRoot R hv i (chevalley R v x)) :=
  rfl

/-- `T''_{i,-1} = ω Tᵢ⁻¹ ω`. -/
lemma braidPrimeEquiv_symm_apply (i : I) (x : QuantumGroup R v) :
    (braidPrimeEquiv R hv i).symm x =
      chevalley R v ((braidEquivOfNotRoot R hv i).symm (chevalley R v x)) :=
  rfl

omit [DecidableEq I] [NeZero v] in
lemma reflY_neg' (i : I) (μ : Y) : reflY R i (-μ) = -reflY R i μ := map_neg _ μ

lemma braidPrimeEquiv_K (i : I) (μ : Y) :
    braidPrimeEquiv R hv i (K R v μ) = K R v (reflY R i μ) := by
  have hK := (braidEquivOfNotRoot_hasImages hv R i).map_K (-μ)
  rw [AlgEquiv.coe_toAlgHom] at hK
  rw [braidPrimeEquiv_apply, chevalley_K, hK, chevalley_K, reflY_neg', neg_neg]

lemma braidPrimeEquiv_symm_K (i : I) (μ : Y) :
    (braidPrimeEquiv R hv i).symm (K R v μ) = K R v (reflY R i μ) := by
  rw [AlgEquiv.symm_apply_eq, braidPrimeEquiv_K, reflY_reflY]

/-- [Lus] 37.1.3: `T'_{i,1}(Eᵢ^{(n)}) = (-1)ⁿ vᵢ^{n(n-1)} K̃_{ni} Fᵢ^{(n)}`. -/
theorem braidPrimeEquiv_qDivPow_E_self (i : I) (n : ℕ) :
    braidPrimeEquiv R hv i (qDivPow (v ^ D.d i) n (E R v i)) =
      ((-1) ^ n * (v ^ D.d i) ^ (n * (n - 1))) •
        (K R v (n • ktilde R i) * qDivPow (v ^ D.d i) n (F R v i)) := by
  rw [braidPrimeEquiv_apply, chevalley_qDivPow_E, braidEquivOfNotRoot_qDivPow_F_self hv R,
    map_smul, map_mul, chevalley_K, chevalley_qDivPow_E, smul_neg, neg_neg]

/-- [Lus] 37.1.3: `T'_{i,1}(Fᵢ^{(n)}) = (-1)ⁿ vᵢ^{-n(n-1)} Eᵢ^{(n)} K̃_{-ni}`. -/
theorem braidPrimeEquiv_qDivPow_F_self (i : I) (n : ℕ) :
    braidPrimeEquiv R hv i (qDivPow (v ^ D.d i) n (F R v i)) =
      ((-1) ^ n * (v ^ D.d i)⁻¹ ^ (n * (n - 1))) •
        (qDivPow (v ^ D.d i) n (E R v i) * K R v (-(n • ktilde R i))) := by
  rw [braidPrimeEquiv_apply, chevalley_qDivPow_F, braidEquivOfNotRoot_qDivPow_E_self hv R,
    map_smul, map_mul, chevalley_K, chevalley_qDivPow_F]

/-- [Lus] 37.1.3: `T'_{i,1}(Eⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^r Eᵢ^{(r)} Eⱼ^{(n)} Eᵢ^{(s)}` for
`j ≠ i`, `a = -⟨i, j'⟩`. -/
theorem braidPrimeEquiv_qDivPow_E_ne {i j : I} (hji : j ≠ i) (n : ℕ) :
    braidPrimeEquiv R hv i (qDivPow (v ^ D.d j) n (E R v j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i) ^ r) •
        (qDivPow (v ^ D.d i) r (E R v i) * qDivPow (v ^ D.d j) n (E R v j) *
          qDivPow (v ^ D.d i) (negA D i j * n - r) (E R v i)) := by
  rw [braidPrimeEquiv_apply, chevalley_qDivPow_E, braidEquivOfNotRoot_qDivPow_F_ne hv R hji,
    braidFjDiv, map_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  simp only [map_smul, map_mul, chevalley_qDivPow_F]

/-- [Lus] 37.1.3: `T'_{i,1}(Fⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{-r} Fᵢ^{(s)} Fⱼ^{(n)} Fᵢ^{(r)}` for
`j ≠ i`. -/
theorem braidPrimeEquiv_qDivPow_F_ne {i j : I} (hji : j ≠ i) (n : ℕ) :
    braidPrimeEquiv R hv i (qDivPow (v ^ D.d j) n (F R v j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i)⁻¹ ^ r) •
        (qDivPow (v ^ D.d i) (negA D i j * n - r) (F R v i) * qDivPow (v ^ D.d j) n (F R v j) *
          qDivPow (v ^ D.d i) r (F R v i)) := by
  rw [braidPrimeEquiv_apply, chevalley_qDivPow_F, braidEquivOfNotRoot_qDivPow_E_ne hv R hji,
    braidEjDiv, map_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  simp only [map_smul, map_mul, chevalley_qDivPow_E]

/-- [Lus] 37.1.3: `T''_{i,-1}(Eᵢ^{(n)}) = (-1)ⁿ vᵢ^{n(n-1)} Fᵢ^{(n)} K̃_{-ni}`. -/
theorem braidPrimeEquiv_symm_qDivPow_E_self (i : I) (n : ℕ) :
    (braidPrimeEquiv R hv i).symm (qDivPow (v ^ D.d i) n (E R v i)) =
      ((-1) ^ n * (v ^ D.d i) ^ (n * (n - 1))) •
        (qDivPow (v ^ D.d i) n (F R v i) * K R v (-(n • ktilde R i))) := by
  rw [braidPrimeEquiv_symm_apply, chevalley_qDivPow_E,
    braidEquivOfNotRoot_symm_qDivPow_F_self hv R, map_smul, map_mul, chevalley_K,
    chevalley_qDivPow_E]

/-- [Lus] 37.1.3: `T''_{i,-1}(Fᵢ^{(n)}) = (-1)ⁿ vᵢ^{-n(n-1)} K̃_{ni} Eᵢ^{(n)}`. -/
theorem braidPrimeEquiv_symm_qDivPow_F_self (i : I) (n : ℕ) :
    (braidPrimeEquiv R hv i).symm (qDivPow (v ^ D.d i) n (F R v i)) =
      ((-1) ^ n * (v ^ D.d i)⁻¹ ^ (n * (n - 1))) •
        (K R v (n • ktilde R i) * qDivPow (v ^ D.d i) n (E R v i)) := by
  rw [braidPrimeEquiv_symm_apply, chevalley_qDivPow_F,
    braidEquivOfNotRoot_symm_qDivPow_E_self hv R, map_smul, map_mul, chevalley_K,
    chevalley_qDivPow_F, neg_neg]

/-- [Lus] 37.1.3: `T''_{i,-1}(Eⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^r Eᵢ^{(s)} Eⱼ^{(n)} Eᵢ^{(r)}` for
`j ≠ i`. -/
theorem braidPrimeEquiv_symm_qDivPow_E_ne {i j : I} (hji : j ≠ i) (n : ℕ) :
    (braidPrimeEquiv R hv i).symm (qDivPow (v ^ D.d j) n (E R v j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i) ^ r) •
        (qDivPow (v ^ D.d i) (negA D i j * n - r) (E R v i) * qDivPow (v ^ D.d j) n (E R v j) *
          qDivPow (v ^ D.d i) r (E R v i)) := by
  rw [braidPrimeEquiv_symm_apply, chevalley_qDivPow_E,
    braidEquivOfNotRoot_symm_qDivPow_F_ne hv R hji, map_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  simp only [map_smul, map_mul, chevalley_qDivPow_F]

/-- [Lus] 37.1.3: `T''_{i,-1}(Fⱼ^{(n)}) = Σ_{r+s=an} (-1)^r vᵢ^{-r} Fᵢ^{(r)} Fⱼ^{(n)} Fᵢ^{(s)}`
for `j ≠ i`. -/
theorem braidPrimeEquiv_symm_qDivPow_F_ne {i j : I} (hji : j ≠ i) (n : ℕ) :
    (braidPrimeEquiv R hv i).symm (qDivPow (v ^ D.d j) n (F R v j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : k) ^ r * (v ^ D.d i)⁻¹ ^ r) •
        (qDivPow (v ^ D.d i) r (F R v i) * qDivPow (v ^ D.d j) n (F R v j) *
          qDivPow (v ^ D.d i) (negA D i j * n - r) (F R v i)) := by
  rw [braidPrimeEquiv_symm_apply, chevalley_qDivPow_F,
    braidEquivOfNotRoot_symm_qDivPow_E_ne hv R hji, map_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  simp only [map_smul, map_mul, chevalley_qDivPow_E]

variable (D v) in
/-- The scalars `cᵢⱼ = (-vᵢ)^{⟨i,j'⟩}` of [Lus] 37.2.4. -/
def braidSign (i : I) : I → kˣ := fun j ↦ chevalleyScalar D v i ^ D.cartanMatrix i j

omit [DecidableEq I] in
lemma isSignPow_chevalleyScalar_zpow (i : I) (c : I → ℤ) :
    IsSignPow v (fun j ↦ chevalleyScalar D v i ^ c j) := fun j ↦
  ⟨c j, D.d i * c j, by
    rw [Units.val_zpow_eq_zpow_val, chevalleyScalar, Units.val_mk0, neg_eq_neg_one_mul, mul_zpow,
      ← zpow_natCast, ← zpow_mul]⟩

include hv in
/-- **[Lus] 37.2.4**, last formula, for `e = 1`: `T''_{i,1} = T'_{i,1} ∘ D_{cᵢ}`, where `D_{cᵢ}` is
the diagonal automorphism `Eⱼ ↦ (-vᵢ)^{⟨i,j'⟩} Eⱼ`, `Fⱼ ↦ (-vᵢ)^{-⟨i,j'⟩} Fⱼ`; on an element `u` of
root lattice degree `ν` this reads `T''_{i,1}(u) = (-1)ⁿ vᵢⁿ T'_{i,1}(u)`, `n = ⟨i, ν'⟩`. -/
theorem braidEquivOfNotRoot_eq_braidPrimeEquiv_diagHom (i : I) (x : QuantumGroup R v) :
    braidEquivOfNotRoot R hv i x = braidPrimeEquiv R hv i (diagHom R v (braidSign D v i) x) := by
  have H := braidEquivOfNotRoot_hasImages hv R i
  have h3 : reflChar D i (chevalleyScalar D v) * (chevalleyScalar D v)⁻¹ =
      (braidSign D v i)⁻¹ := by
    funext l
    simp only [reflChar, braidSign, Pi.mul_apply, Pi.inv_apply, zpow_neg]
    rw [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hD : ∀ (c c' : I → kˣ) (z : QuantumGroup R v),
      diagHom R v c (diagHom R v c' z) = diagHom R v (c * c') z := fun c c' z ↦ by
    rw [← AlgHom.comp_apply, diagHom_comp_diagHom]
  -- `T'_{i,1} z = Tᵢ (D_{c⁻¹} z)`, from `ω Tᵢ ω D_ζ = D_ζ Tᵢ` and `D_ζ Tᵢ = Tᵢ D_{sᵢ ζ}`
  have key : ∀ z, braidPrimeEquiv R hv i z =
      braidEquivOfNotRoot R hv i (diagHom R v (braidSign D v i)⁻¹ z) := by
    intro z
    have h1 := DFunLike.congr_fun (chevalley_comp_comp_diagHom H)
      (diagHom R v (chevalleyScalar D v)⁻¹ z)
    have h2 := DFunLike.congr_fun (diagHom_comp_of_hasImages H (chevalleyScalar D v))
      (diagHom R v (chevalleyScalar D v)⁻¹ z)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h1 h2
    rw [hD, mul_inv_cancel, diagHom_one, AlgHom.id_apply] at h1
    rw [braidPrimeEquiv_apply, h1, h2, hD, h3]
  rw [key, hD, inv_mul_cancel, diagHom_one, AlgHom.id_apply]

/-- `T'_{i,1} = Tᵢ ∘ D_{cᵢ}⁻¹`. -/
theorem braidPrimeEquiv_eq_braidEquivOfNotRoot_diagHom (i : I) (x : QuantumGroup R v) :
    braidPrimeEquiv R hv i x =
      braidEquivOfNotRoot R hv i (diagHom R v (braidSign D v i)⁻¹ x) := by
  rw [braidEquivOfNotRoot_eq_braidPrimeEquiv_diagHom hv, ← AlgHom.comp_apply,
    diagHom_comp_diagHom, mul_inv_cancel, diagHom_one, AlgHom.id_apply]

/-- `T''_{i,-1} = D_{cᵢ} ∘ Tᵢ⁻¹`. -/
theorem braidPrimeEquiv_symm_eq_diagHom_symm (i : I) (x : QuantumGroup R v) :
    (braidPrimeEquiv R hv i).symm x =
      diagHom R v (braidSign D v i) ((braidEquivOfNotRoot R hv i).symm x) := by
  rw [AlgEquiv.symm_apply_eq, braidPrimeEquiv_eq_braidEquivOfNotRoot_diagHom hv,
    ← AlgHom.comp_apply, diagHom_comp_diagHom, inv_mul_cancel, diagHom_one, AlgHom.id_apply,
    AlgEquiv.apply_symm_apply]

/-- Diagonal automorphisms move across products of the `Tᵢ`. -/
theorem exists_diagHom_list_braid (ω : List I) {c : I → kˣ} (hc : IsSignPow v c) :
    ∃ c' : I → kˣ, IsSignPow v c' ∧ ∀ x, diagHom R v c ((ω.map (braidEquivOfNotRoot R hv)).prod x)
      = (ω.map (braidEquivOfNotRoot R hv)).prod (diagHom R v c' x) := by
  induction ω generalizing c with
  | nil => exact ⟨c, hc, fun x ↦ rfl⟩
  | cons i ω ih =>
    obtain ⟨c', hc', h⟩ := ih (hc.reflChar i)
    refine ⟨c', hc', fun x ↦ ?_⟩
    have H := diagHom_comp_of_hasImages (braidEquivOfNotRoot_hasImages hv R i) c
    simp only [List.map_cons, List.prod_cons, AlgEquiv.mul_apply]
    rw [← h]
    exact (DFunLike.congr_fun H _ :)

/-- Diagonal automorphisms move across products of the `Tᵢ⁻¹`. -/
theorem exists_diagHom_list_braid_symm (ω : List I) {c : I → kˣ} (hc : IsSignPow v c) :
    ∃ c' : I → kˣ, IsSignPow v c' ∧
      ∀ x, diagHom R v c ((ω.map fun j ↦ (braidEquivOfNotRoot R hv j).symm).prod x) =
        (ω.map fun j ↦ (braidEquivOfNotRoot R hv j).symm).prod (diagHom R v c' x) := by
  induction ω generalizing c with
  | nil => exact ⟨c, hc, fun x ↦ rfl⟩
  | cons i ω ih =>
    obtain ⟨c', hc', h⟩ := ih (hc.reflChar i)
    refine ⟨c', hc', fun x ↦ ?_⟩
    simp only [List.map_cons, List.prod_cons, AlgEquiv.mul_apply]
    rw [diagHom_symm_apply_of_hasImages (braidEquivOfNotRoot_hasImages hv R i), h]

/-- **Words in `T'_{i,1}`**: `T'_{i₁,1} ⋯ T'_{iₙ,1} = T''_{i₁,1} ⋯ T''_{iₙ,1} ∘ D_c` for a
diagonal automorphism `D_c` with scalars `± v^m` (from [Lus] 37.2.4). -/
theorem exists_list_braidPrime_eq (ω : List I) :
    ∃ c : I → kˣ, IsSignPow v c ∧ ∀ x, (ω.map (braidPrimeEquiv R hv)).prod x =
      (ω.map (braidEquivOfNotRoot R hv)).prod (diagHom R v c x) := by
  induction ω with
  | nil => exact ⟨1, IsSignPow.one, fun x ↦ by simp [diagHom_one]⟩
  | cons i ω ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := exists_diagHom_list_braid (R := R) hv ω
      (isSignPow_chevalleyScalar_zpow (D := D) i (D.cartanMatrix i)).inv
    refine ⟨c' * c, hc'.mul hc, fun x ↦ ?_⟩
    simp only [List.map_cons, List.prod_cons, AlgEquiv.mul_apply]
    rw [h, braidPrimeEquiv_eq_braidEquivOfNotRoot_diagHom hv,
      show braidSign D v i = fun j ↦ chevalleyScalar D v i ^ D.cartanMatrix i j from rfl, h',
      ← AlgHom.comp_apply (diagHom R v c'), diagHom_comp_diagHom]

/-- **Words in `T''_{i,-1}`**: `T''_{i₁,-1} ⋯ T''_{iₙ,-1} = T'_{i₁,-1} ⋯ T'_{iₙ,-1} ∘ D_c` for a
diagonal automorphism `D_c` with scalars `± v^m` (from [Lus] 37.2.4). -/
theorem exists_list_braidPrime_symm_eq (ω : List I) :
    ∃ c : I → kˣ, IsSignPow v c ∧ ∀ x, (ω.map fun j ↦ (braidPrimeEquiv R hv j).symm).prod x =
      (ω.map fun j ↦ (braidEquivOfNotRoot R hv j).symm).prod (diagHom R v c x) := by
  induction ω with
  | nil => exact ⟨1, IsSignPow.one, fun x ↦ by simp [diagHom_one]⟩
  | cons i ω ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := exists_diagHom_list_braid_symm (R := R) hv (i :: ω)
      (isSignPow_chevalleyScalar_zpow (D := D) i (D.cartanMatrix i))
    refine ⟨c' * c, hc'.mul hc, fun x ↦ ?_⟩
    have h'' := h' (diagHom R v c x)
    simp only [List.map_cons, List.prod_cons, AlgEquiv.mul_apply] at h'' ⊢
    rw [h, braidPrimeEquiv_symm_eq_diagHom_symm hv,
      show braidSign D v i = fun j ↦ chevalleyScalar D v i ^ D.cartanMatrix i j from rfl, h'',
      ← AlgHom.comp_apply (diagHom R v c'), diagHom_comp_diagHom]

/-- On divided powers:
`T'_{i₁,1} ⋯ T'_{iₙ,1}(Eᵢ^{(t)}) = (±v^m)^t T''_{i₁,1} ⋯ T''_{iₙ,1}(Eᵢ^{(t)})`. -/
theorem exists_list_braidPrime_qDivPow_E (ω : List I) (i : I) :
    ∃ e m : ℤ, ∀ t : ℕ, (ω.map (braidPrimeEquiv R hv)).prod (qDivPow (v ^ D.d i) t (E R v i)) =
      (((-1) ^ e * v ^ m) ^ t) •
        (ω.map (braidEquivOfNotRoot R hv)).prod (qDivPow (v ^ D.d i) t (E R v i)) := by
  obtain ⟨c, hc, h⟩ := exists_list_braidPrime_eq (R := R) hv ω
  obtain ⟨e, m, he⟩ := hc i
  exact ⟨e, m, fun t ↦ by rw [h, diagHom_qDivPow_E', map_smul, he]⟩

/-- On divided powers:
`T''_{i₁,-1} ⋯ T''_{iₙ,-1}(Eᵢ^{(t)}) = (±v^m)^t T'_{i₁,-1} ⋯ T'_{iₙ,-1}(Eᵢ^{(t)})`. -/
theorem exists_list_braidPrime_symm_qDivPow_E (ω : List I) (i : I) :
    ∃ e m : ℤ, ∀ t : ℕ,
      (ω.map fun j ↦ (braidPrimeEquiv R hv j).symm).prod (qDivPow (v ^ D.d i) t (E R v i)) =
        (((-1) ^ e * v ^ m) ^ t) • (ω.map fun j ↦ (braidEquivOfNotRoot R hv j).symm).prod
          (qDivPow (v ^ D.d i) t (E R v i)) := by
  obtain ⟨c, hc, h⟩ := exists_list_braidPrime_symm_eq (R := R) hv ω
  obtain ⟨e, m, he⟩ := hc i
  exact ⟨e, m, fun t ↦ by rw [h, diagHom_qDivPow_E', map_smul, he]⟩

end Symmetries

end LieLean.QuantumGroup
