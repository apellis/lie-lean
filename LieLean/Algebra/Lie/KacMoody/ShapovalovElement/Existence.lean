/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ShapovalovElement.Uniqueness
import LieLean.Algebra.Lie.KacMoody.ShapovalovElement.Roots
import LieLean.Algebra.Lie.KacMoody.TranslationWall
import LieLean.Algebra.Lie.KacMoody.Integrable
import LieLean.Algebra.Lie.UniversalEnveloping.Commutator

/-!
# Existence of Shapovalov elements

**Shapovalov's theorem** ([HumO] Thm. 4.12): for `𝔤` of finite type over an algebraically closed
field of characteristic zero, every positive root `γ = ∑ⱼ aⱼ αⱼ` and every `r > 0` admit a
Shapovalov element (`VermaModule.exists_isShapovalovElement`), unique modulo
`U(𝔟⁻)(h_γ + ρ(h_γ) - r)` (`VermaModule.IsShapovalovElement.exists_sub_eq_smul`).

The proof follows [HumO] §4.13, by induction on the height of `γ`. For `γ = αⱼ` simple, `yⱼ^r`
works (`VermaModule.isShapovalovElement_simple`). Otherwise pick `αⱼ` with `p = ⟨γ, αⱼ^∨⟩ > 0`
and `β = sⱼ γ = γ - p αⱼ` positive (`Matrix.Realization.exists_simple_descent`), and let `θ_β` be
a Shapovalov element for `(β, r)`. For `λ` on the hyperplane `⟨λ + ρ, γ^∨⟩ = r` with
`q = -⟨λ + ρ, αⱼ^∨⟩ ∈ ℕ` large, put `μ = sⱼ · λ = λ + q αⱼ` and `n = q + r p`. Then
`yⁿ θ_β(μ) v_μ` is a maximal vector of `M(μ)` of weight `λ - rγ`; by Verma's theorem
([HumO] Thm. 4.6) and `dim Hom(M(λ - rγ), M(μ)) ≤ 1` it lies in `M(λ) = U(𝔫⁻) y^q v_μ`, so
`yⁿ θ_β(μ) = X y^q` for a unique `X` with `X v_λ` maximal (`VermaModule.exists_mul_fEnv_pow_eq`).
Expanding `yⁿ θ_β(μ)` with the binomial formula (`LinearMap.pow_mul_eq_sum_mul_pow`) writes `X` as
a polynomial family in `λ`, and Zariski density of these `λ` in the hyperplane
(`VermaModule.mem_of_forall_nat`) gives (a) and (b) on the hyperplane. Finally the family is
extended off the hyperplane by projecting along `γ`
(`VermaModule.IsShapovalovElement.of_hyperplane`).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.6, §4.12, §4.13.
-/

open Module Module.Dual LieModule UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

/-- `⟨x, (sⱼ v αᵢ)^∨⟩ = ⟨sⱼ x, (v αᵢ)^∨⟩`. -/
lemma corootPairing_simple_mul (hA : A.IsGeneralizedCartan) (x : Dual K H) (j : ι)
    (v : P.weylGroup hA) (i : ι) :
    P.corootPairing hA x ((P.coxeterSystem hA).simple j * v) i =
      P.corootPairing hA (P.reflection hA j x) v i := by
  rw [← coxeterSystem_simple, corootPairing_apply, CoxeterSystem.inv_simple]

omit [DecidableEq ι] [CharZero K] in
/-- `⟨v αᵢ, (v αᵢ)^∨⟩ = 2`. -/
lemma corootPairing_apply_root (hA : A.IsGeneralizedCartan) (v : P.weylGroup hA) (i : ι) :
    P.corootPairing hA ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) v i = 2 := by
  rw [corootPairing_apply, inv_mul_cancel, corootPairing_one, P.root_coroot_self hA]

end Matrix.Realization

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

local notation "𝒰⁻" => UniversalEnvelopingAlgebra K (nNeg P)

/-! ### Auxiliary facts -/

omit [CharZero K] in
lemma coe_ad_pow_nNeg (x y : nNeg P) (n : ℕ) :
    (((LieAlgebra.ad K (nNeg P) x ^ n) y : nNeg P) : P.KacMoodyAlgebra) =
      (LieAlgebra.ad K P.KacMoodyAlgebra x ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieSubalgebra.coe_bracket, ih,
      pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]

/-- `ad yⱼ` is locally nilpotent on `U(𝔫⁻)`. -/
lemma exists_commutator_fEnv_pow_eq_zero (hA : A.IsGeneralizedCartan) (j : ι) (u : 𝒰⁻) :
    ∃ n, (LinearMap.commutator K (fEnv P j) ^ n) u = 0 := by
  refine exists_commutator_pow_eq_zero (fun y ↦ ?_) u
  obtain ⟨n, hn⟩ := exists_ad_f_pow_eq_zero P hA j (y : P.KacMoodyAlgebra)
  exact ⟨n, Subtype.ext (by rw [coe_ad_pow_nNeg]; exact hn)⟩

omit [CharZero K] in
/-- A locally nilpotent commutator kills all values of a polynomial family after a fixed number of
steps. -/
lemma exists_commutator_pow_eq_zero_of_mem_polyFam {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P)
    {a : 𝒰⁻} (ha : ∀ u : 𝒰⁻, ∃ n, (LinearMap.commutator K a ^ n) u = 0) :
    ∃ N, ∀ Λ, (LinearMap.commutator K a ^ N) (F Λ) = 0 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, u, rfl⟩ := hF
    obtain ⟨n, hn⟩ := ha u
    refine ⟨n, fun Λ ↦ ?_⟩
    change (LinearMap.commutator K a ^ n) (evalPoly K H p Λ • u) = 0
    rw [map_smul, hn, smul_zero]
  | zero => exact ⟨0, fun Λ ↦ by simp⟩
  | add F G _ _ hF hG =>
    obtain ⟨m, hm⟩ := hF
    obtain ⟨n, hn⟩ := hG
    refine ⟨max m n, fun Λ ↦ ?_⟩
    rw [Pi.add_apply, map_add,
      LinearMap.commutator_pow_eq_zero_of_le (le_max_left m n) (hm Λ),
      LinearMap.commutator_pow_eq_zero_of_le (le_max_right m n) (hn Λ), add_zero]
  | smul b F _ hF =>
    obtain ⟨n, hn⟩ := hF
    exact ⟨n, fun Λ ↦ by rw [Pi.smul_apply, map_smul, hn Λ, smul_zero]⟩

lemma fEnv_pow_ne_zero (j : ι) (n : ℕ) : fEnv P j ^ n ≠ 0 :=
  pow_ne_zero n ((hasSymbol_fEnv j).ne_zero (fSym_ne_zero j))

/-- A morphism `M(λ) → M(μ)` sending `v_λ` to `w v_μ` sends `u v_λ` to `u w v_μ`. -/
lemma map_equivEnvNNeg {Λ μ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ) {w : 𝒰⁻}
    (hw : φ (hwv P Λ) = equivEnvNNeg P μ w) (u : 𝒰⁻) :
    φ (equivEnvNNeg P Λ u) = equivEnvNNeg P μ (u * w) := by
  rw [equivEnvNNeg_apply, map_smul_eq_smul P φ, hw, ← equivEnvNNeg_mul]

omit [CharZero K] in
lemma map_toEnd_pow {Λ μ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ) (x : P.KacMoodyAlgebra)
    (n : ℕ) (m : VermaModule P Λ) :
    φ ((toEnd K P.KacMoodyAlgebra (VermaModule P Λ) x ^ n) m) =
      (toEnd K P.KacMoodyAlgebra (VermaModule P μ) x ^ n) (φ m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, LieModuleHom.map_lie, ih, pow_succ',
      Module.End.mul_apply, toEnd_apply_apply]

omit [CharZero K] in
/-- Morphisms of `𝔤(A)`-modules preserve primitive vectors. -/
lemma map_mem_primitiveVectors {Λ μ ν : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ) {m : VermaModule P Λ}
    (hm : m ∈ primitiveVectors P (VermaModule P Λ) ν) :
    φ m ∈ primitiveVectors P (VermaModule P μ) ν :=
  mem_primitiveVectors.mpr ⟨map_mem_weightSpaceOfMap P φ (mem_primitiveVectors.mp hm).1,
    fun i ↦ by rw [← LieModuleHom.map_lie, (mem_primitiveVectors.mp hm).2 i, map_zero]⟩

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
lemma exists_smul_eq_of_finrank_le_one {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : finrank K V ≤ 1) {x : V} (hx : x ≠ 0) (z : V) :
    ∃ c : K, c • x = z :=
  (finrank_eq_one_iff_of_nonzero' x hx).mp
    (le_antisymm h (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩)) z

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
lemma exists_apply_eq_zero_apply_eq_one {V : Type*} [AddCommGroup V] [Module K V]
    {φ ψ : V →ₗ[K] K} {x₀ : V} (hx₀ : φ x₀ = 1) (h : ¬ ∀ x, ψ x = ψ x₀ * φ x) :
    ∃ δ, φ δ = 0 ∧ ψ δ = 1 := by
  push Not at h
  obtain ⟨x, hx⟩ := h
  have hy : φ (x - φ x • x₀) = 0 := by
    rw [map_sub, map_smul, hx₀, smul_eq_mul, mul_one, sub_self]
  have hy' : ψ (x - φ x • x₀) ≠ 0 := by
    rw [map_sub, map_smul, smul_eq_mul]
    intro h0
    exact hx (by linear_combination h0)
  refine ⟨(ψ (x - φ x • x₀))⁻¹ • (x - φ x • x₀), ?_, ?_⟩
  · rw [map_smul, hy, smul_zero]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']

/-! ### The Verma module step -/

/-- **The key step of [HumO] §4.13.** Let `γ = v αᵢ` be a positive root, `⟨λ + ρ, γ^∨⟩ = r`, and
`λ = μ - Q αⱼ` with `⟨μ + ρ, αⱼ^∨⟩ = Q > 0`, so that `M(λ) ↪ M(μ)`, `v_λ ↦ y_j^Q v_μ`. Every
maximal vector `w ∈ M(μ)` of weight `λ - rγ` is `X y_j^Q v_μ` with `X v_λ ∈ M(λ)` maximal. -/
theorem exists_mul_fEnv_pow_eq [IsAlgClosed K] [FiniteDimensional K H]
    {hA : A.IsGeneralizedCartan} (hfin : A.IsFiniteCartan) {v : P.weylGroup hA} {i : ι}
    (hv : P.IsPosRoot hA v i) {r : ℕ} {Λ μ : Dual K H}
    (hΛ : P.corootPairing hA (Λ + P.rho) v i = r) {j : ι} {Q : ℕ} (hQ : 0 < Q)
    (hμ : (μ + P.rho) (P.coroot j) = Q) (hΛμ : Λ = μ - (Q : K) • P.root j)
    {w : VermaModule P μ}
    (hw : w ∈ primitiveVectors P (VermaModule P μ)
      (Λ - r • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i))) :
    ∃ X : 𝒰⁻, equivEnvNNeg P μ (X * fEnv P j ^ Q) = w ∧
      equivEnvNNeg P Λ X ∈ primitiveVectors P (VermaModule P Λ)
        (Λ - r • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) := by
  obtain ⟨S⟩ := isSymmetrizable_iff_nonempty_symmetrization.mp hfin.isSymmetrizable
  have hprim : equivEnvNNeg P μ (fEnv P j ^ Q) ∈ primitiveVectors P (VermaModule P μ) Λ := by
    rw [equivEnvNNeg_fEnv_pow]
    have h := toEnd_f_pow_hwv_mem_primitiveVectors P hA hQ hμ
    have hw' : P.reflection hA j (μ + P.rho) - P.rho = Λ := by
      rw [reflection_apply, hμ, hΛμ]
      abel
    rwa [hw'] at h
  let ι' := (homEquiv P (VermaModule P μ) Λ).symm ⟨_, hprim⟩
  have hιv : ι' (hwv P Λ) = equivEnvNNeg P μ (fEnv P j ^ Q) :=
    congrArg Subtype.val ((homEquiv P (VermaModule P μ) Λ).apply_symm_apply ⟨_, hprim⟩)
  have hι0 : ι' ≠ 0 := by
    intro h0
    have h1 := hιv
    rw [h0, _root_.zero_apply, eq_comm, LinearEquiv.map_eq_zero_iff] at h1
    exact fEnv_pow_ne_zero j Q h1
  have hιinj := injective_of_ne_zero P hι0
  set ν := Λ - r • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)
  obtain ⟨φ₁, hφ₁⟩ := exists_injective_reflectionOf hfin (P := P) (Λ := Λ) (v := v) hv hΛ
  have hψ0 : ι' (φ₁ (hwv P ν)) ≠ 0 := by
    intro h0
    apply hwv_ne_zero P ν
    apply hφ₁
    rw [map_zero]
    apply hιinj
    rw [map_zero]
    exact h0
  set W := primitiveVectors P (VermaModule P μ) ν
  have : FiniteDimensional K W := by
    have := finiteDimensional_weightSpace P μ ν
    exact Submodule.finiteDimensional_of_le inf_le_left
  have h1 : finrank K W ≤ 1 := by
    rw [← finrank_hom (P := P) (V := VermaModule P μ)]
    exact finrank_hom_le_one_of_finite_type P hfin S μ ν
  have hmemψ : ι' (φ₁ (hwv P ν)) ∈ W :=
    map_mem_primitiveVectors ι' (map_hwv_mem_primitiveVectors P φ₁)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_le_one h1 (x := ⟨_, hmemψ⟩)
    (fun h0 ↦ hψ0 (by rw [Subtype.ext_iff] at h0; exact h0)) ⟨w, hw⟩
  have hc' := congrArg Subtype.val hc
  rw [Submodule.coe_smul] at hc'
  obtain ⟨X₀, hX₀⟩ := (equivEnvNNeg P Λ).surjective (φ₁ (hwv P ν))
  refine ⟨c • X₀, ?_, ?_⟩
  · rw [← map_equivEnvNNeg ι' hιv, map_smul (equivEnvNNeg P Λ) c X₀, hX₀, map_smul]
    exact hc'
  · rw [map_smul (equivEnvNNeg P Λ) c X₀, hX₀]
    exact Submodule.smul_mem _ c (map_hwv_mem_primitiveVectors P φ₁)

/-! ### Extension off the hyperplane -/

/-- A polynomial family satisfying (a) and (b) of [HumO] Thm. 4.12 on the hyperplane
`⟨λ + ρ, γ^∨⟩ = r` can be modified off the hyperplane (by projecting along `γ`) to a Shapovalov
element. -/
theorem IsShapovalovElement.of_hyperplane [FiniteDimensional K H] {hA : A.IsGeneralizedCartan}
    {v : P.weylGroup hA} {i : ι} {r : ℕ} {a : ι → ℕ} {θ : Dual K H → 𝒰⁻}
    (hθ : θ ∈ polyFam P) (hw : ∀ Λ, θ Λ ∈ negWeightSpace P (r • P.rootOf fun j ↦ (a j : ℤ)))
    (ha : ∀ Λ, P.corootPairing hA (Λ + P.rho) v i = r →
      ∀ x ∈ nPos P, actEnv P Λ x (θ Λ) = 0)
    (hb : ∀ Λ, P.corootPairing hA (Λ + P.rho) v i = r →
      θ Λ - shapovalovLead P r a ∈ filtration K (nNeg P) (r * ∑ j, a j - 1)) :
    ∃ θ', IsShapovalovElement P hA v i r a θ' := by
  obtain ⟨b, hb'⟩ : ∃ b : H, ∀ Λ : Dual K H, Λ b = P.corootPairing hA Λ v i :=
    ⟨(Module.evalEquiv K H).symm ((Dual.eval K H (P.coroot i)).comp
      ((v⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H).toLinearMap),
      fun Λ ↦ Module.apply_evalEquiv_symm_apply K H Λ _⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) := ⟨_, rfl⟩
  have h2 : P.corootPairing hA γ v i = 2 := hγ ▸ corootPairing_apply_root hA v i
  let c : Dual K H → K := fun Λ ↦ -(P.corootPairing hA (Λ + P.rho) v i - r) / 2
  have hc : c ∈ polyFun K H := by
    have h3 : c = fun Λ ↦ Λ b * (-1 / 2) + (-(P.corootPairing hA P.rho v i - r) / 2) := by
      funext Λ
      simp only [c]
      rw [corootPairing_add, ← hb' Λ]
      ring
    rw [h3]
    exact add_mem (mul_mem (apply_mem_polyFun b) (const_mem_polyFun _)) (const_mem_polyFun _)
  have hcp : ∀ Λ, P.corootPairing hA ((Λ + c Λ • γ + 0) + P.rho) v i = r := by
    intro Λ
    simp only [c, add_zero, corootPairing_add, corootPairing_smul, h2]
    ring
  refine ⟨fun Λ ↦ θ (Λ + c Λ • γ + 0), ⟨comp_add_smul_mem_polyFam hθ hc γ 0, fun Λ ↦ hw _,
    fun Λ hΛ ↦ ?_, fun Λ ↦ hb _ (hcp Λ)⟩⟩
  have hc0 : c Λ = 0 := by
    simp only [c]
    rw [hΛ, sub_self, neg_zero, zero_div]
  simp only [hc0, zero_smul, add_zero]
  exact ha Λ hΛ

/-! ### The induction step -/

/-- **The induction step of [HumO] §4.13.** Let `γ = v αᵢ = ∑ kₗ αₗ` be a positive root, `j` with
`p = ⟨γ, αⱼ^∨⟩ > 0` and `β = sⱼ γ = γ - p αⱼ` positive. A Shapovalov element for `(β, r)` gives one
for `(γ, r)`. -/
theorem exists_isShapovalovElement_step [IsAlgClosed K] [FiniteDimensional K H]
    {hA : A.IsGeneralizedCartan} (hfin : A.IsFiniteCartan) {v : P.weylGroup hA} {i : ι}
    {k : ι → ℤ} (hk : 0 ≤ k) (hvk : (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf k)
    {j : ι} (hp : 0 < (A *ᵥ k) j)
    (hsv : P.IsPosRoot hA ((P.coxeterSystem hA).simple j * v) i) {r : ℕ} (hr : 0 < r)
    {θβ : Dual K H → 𝒰⁻}
    (hθβ : IsShapovalovElement P hA ((P.coxeterSystem hA).simple j * v) i r
      (fun l ↦ ((k - (A *ᵥ k) j • Pi.single j 1 : ι → ℤ) l).toNat) θβ) :
    ∃ θ, IsShapovalovElement P hA v i r (fun l ↦ (k l).toNat) θ := by
  classical
  /- The roots `γ = ∑ kₗ αₗ` and `β = ∑ k'ₗ αₗ`. -/
  obtain ⟨p, hpz⟩ : ∃ p : ℕ, ((p : ℕ) : ℤ) = (A *ᵥ k) j := ⟨_, Int.toNat_of_nonneg hp.le⟩
  obtain ⟨k', hk'def⟩ : ∃ k', k' = k - (A *ᵥ k) j • Pi.single j 1 := ⟨_, rfl⟩
  rw [← hk'def] at hθβ
  have hβ : (((P.coxeterSystem hA).simple j * v : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H)
      (P.root i) = P.rootOf k' := by
    rw [simple_mul_apply_root, hvk, reflection_rootOf, hk'def]
  have hk' : 0 ≤ k' := by
    obtain ⟨k'', hk'', h''⟩ := hsv
    rw [hβ] at h''
    rw [P.rootOf_injective h'']
    exact hk''
  have hk'l : ∀ l, k' l = k l - if l = j then (p : ℤ) else 0 := by
    intro l
    rw [hk'def, hpz]
    by_cases hl : l = j
    · subst hl
      simp
    · simp [hl]
  set aγ : ι → ℕ := fun l ↦ (k l).toNat with haγdef
  set aβ : ι → ℕ := fun l ↦ (k' l).toNat with haβdef
  have haγ : ∀ l, aγ l = aβ l + if l = j then p else 0 := by
    intro l
    have h1 : (0 : ℤ) ≤ k l := hk l
    have h2 : (0 : ℤ) ≤ k' l := hk' l
    have h3 := hk'l l
    simp only [haγdef, haβdef]
    split_ifs with hl
    · subst hl
      simp only [↓reduceIte] at h3
      omega
    · simp only [hl, ↓reduceIte] at h3
      omega
  have hcastγ : (fun l ↦ ((aγ l : ℕ) : ℤ)) = k := funext fun l ↦ Int.toNat_of_nonneg (hk l)
  have hsum : ∑ l, aγ l = ∑ l, aβ l + p := by
    simp only [haγ, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hβ0 : k' ≠ 0 := by
    intro h0
    rw [h0, map_zero, LinearEquiv.map_eq_zero_iff] at hβ
    exact P.linearIndependent_root.ne_zero i hβ
  obtain ⟨l₀, hl₀⟩ : ∃ l, k' l ≠ 0 := by
    by_contra! h
    exact hβ0 (funext h)
  have hsumβ : 0 < ∑ l, aβ l := by
    refine lt_of_lt_of_le ?_
      (Finset.single_le_sum (fun l _ ↦ Nat.zero_le (aβ l)) (Finset.mem_univ l₀))
    have h0 : (0 : ℤ) ≤ k' l₀ := hk' l₀
    simp only [haβdef]
    omega
  have hposβ : 0 < r * ∑ l, aβ l := Nat.mul_pos hr hsumβ
  have hposγ : 0 < r * ∑ l, aγ l := Nat.mul_pos hr (by rw [hsum]; omega)
  have hv : P.IsPosRoot hA v i := ⟨k, hk, hvk⟩
  have hγj : (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) (P.coroot j) = (p : K) := by
    rw [hvk, rootOf_apply_coroot, ← hpz, Int.cast_natCast]
  have hβval : P.rootOf k' = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) - (p : K) • P.root j := by
    rw [← hβ, simple_mul_apply_root, reflection_apply, hγj]
  have hk'j : P.rootOf k' (P.coroot j) = -(p : K) := by
    rw [hβval, LinearMap.sub_apply, LinearMap.smul_apply, hγj, P.root_coroot_self hA,
      smul_eq_mul]
    ring
  obtain ⟨b, hb⟩ : ∃ b : H, ∀ Λ : Dual K H, Λ b = P.corootPairing hA Λ v i :=
    ⟨(Module.evalEquiv K H).symm ((Dual.eval K H (P.coroot i)).comp
      ((v⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H).toLinearMap),
      fun Λ ↦ Module.apply_evalEquiv_symm_apply K H Λ _⟩
  /- The construction of [HumO] §4.13, as a polynomial family. -/
  obtain ⟨J₀, hJ₀⟩ := exists_commutator_pow_eq_zero_of_mem_polyFam hθβ.mem_polyFam
    (exists_commutator_fEnv_pow_eq_zero hA j)
  set J := J₀ + r * p with hJdef
  have hJ : ∀ Λ, (LinearMap.commutator K (fEnv P j) ^ (J + 1)) (θβ Λ) = 0 := fun Λ ↦
    LinearMap.commutator_pow_eq_zero_of_le (by omega) (hJ₀ Λ)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.mulRight K (fEnv P j ^ (J - r * p)))
    (LinearMap.ker_eq_bot.mpr fun a b hab ↦
      mul_right_cancel₀ (fEnv_pow_ne_zero j _) (by simpa using hab))
  have hLy : ∀ X, L (X * fEnv P j ^ (J - r * p)) = X := fun X ↦ by
    simpa using congrArg (fun g ↦ g X) hL
  let Wν := negWeightSpace P (r • P.rootOf fun l ↦ ((aγ l : ℕ) : ℤ))
  obtain ⟨Wc, hWc⟩ := Submodule.exists_isCompl Wν
  let π := Wν.projection Wc hWc
  let qf : Dual K H → K := fun Λ ↦ -Λ (P.coroot j) - 1
  let nf : Dual K H → K := fun Λ ↦ qf Λ + ((r * p : ℕ) : K)
  let E : Dual K H → 𝒰⁻ := fun Λ ↦ ∑ l ∈ Finset.range (J + 1),
    ((descPochhammer K l).eval (nf Λ) * ((l.factorial : ℕ) : K)⁻¹) •
      ((LinearMap.commutator K (fEnv P j) ^ l) (θβ (Λ + qf Λ • P.root j)) * fEnv P j ^ (J - l))
  let θ₀ : Dual K H → 𝒰⁻ := fun Λ ↦ π (L (E Λ))
  have hq : qf ∈ polyFun K H := by
    have h3 : qf = fun Λ ↦ Λ (P.coroot j) * (-1) + (-1) := by
      funext Λ
      simp only [qf]
      ring
    rw [h3]
    exact add_mem (mul_mem (apply_mem_polyFun _) (const_mem_polyFun _)) (const_mem_polyFun _)
  have hn : nf ∈ polyFun K H := add_mem hq (const_mem_polyFun _)
  have hθμ : (fun Λ ↦ θβ (Λ + qf Λ • P.root j)) ∈ polyFam P := by
    simpa using comp_add_smul_mem_polyFam hθβ.mem_polyFam hq (P.root j) 0
  have hE : E ∈ polyFam P := by
    have h3 : E = ∑ l ∈ Finset.range (J + 1), fun Λ ↦
        ((descPochhammer K l).eval (nf Λ) * ((l.factorial : ℕ) : K)⁻¹) •
          ((LinearMap.mulRight K (fEnv P j ^ (J - l)) ∘ₗ
            (LinearMap.commutator K (fEnv P j) ^ l)) (θβ (Λ + qf Λ • P.root j))) := by
      funext Λ
      simp only [E, Finset.sum_apply]
      rfl
    rw [h3]
    exact Submodule.sum_mem _ fun l _ ↦ smul_mem_polyFam_of_mem_polyFun
      (mul_mem (descPochhammer_mem_polyFun hn l) (const_mem_polyFun _)) (map_mem_polyFam _ hθμ)
  have hθ₀ : θ₀ ∈ polyFam P := map_mem_polyFam (π ∘ₗ L) hE
  /- At the points `λ` of the hyperplane with `q = -⟨λ + ρ, αⱼ^∨⟩ ∈ ℕ` large, `θ₀(λ)` is the
  element `X` with `yⁿ θ_β(μ) = X y^q`, which satisfies (a) and (b). -/
  have key : ∀ Λ : Dual K H, P.corootPairing hA (Λ + P.rho) v i = r → ∀ m : ℕ, J + 2 ≤ m →
      Λ (P.coroot j) = -(m : K) →
      (∀ x ∈ nPos P, actEnv P Λ x (θ₀ Λ) = 0) ∧
        θ₀ Λ - shapovalovLead P r aγ ∈ filtration K (nNeg P) (r * ∑ l, aγ l - 1) := by
    intro Λ hΛ m hm hΛm
    obtain ⟨Q, rfl⟩ : ∃ Q, m = Q + 1 := ⟨m - 1, by omega⟩
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = Λ + (Q : K) • P.root j := ⟨_, rfl⟩
    have hqf : qf Λ = Q := by
      simp only [qf, hΛm]
      push_cast
      ring
    have hμρ : (μ + P.rho) (P.coroot j) = Q := by
      rw [hμdef, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, hΛm,
        P.root_coroot_self hA, rho_coroot, smul_eq_mul]
      push_cast
      ring
    have hΛμ : Λ = μ - (Q : K) • P.root j := by rw [hμdef, add_sub_cancel_right]
    have hμβ : P.corootPairing hA (μ + P.rho) ((P.coxeterSystem hA).simple j * v) i = r := by
      rw [corootPairing_simple_mul, reflection_apply, hμρ,
        show μ + P.rho - (Q : K) • P.root j = Λ + P.rho by rw [hμdef]; abel]
      exact hΛ
    set nN := Q + r * p with hnN
    have hθβprim := hθβ.equivEnvNNeg_mem_primitiveVectors hμβ
    have hcastβ : (fun l ↦ ((aβ l : ℕ) : ℤ)) = k' := funext fun l ↦ Int.toNat_of_nonneg (hk' l)
    rw [hcastβ] at hθβprim
    have hν'j : (μ - r • P.rootOf k' + P.rho) (P.coroot j) = (nN : K) := by
      rw [← Nat.cast_smul_eq_nsmul K,
        show μ - (r : K) • P.rootOf k' + P.rho = (μ + P.rho) - (r : K) • P.rootOf k' by abel,
        LinearMap.sub_apply, LinearMap.smul_apply, hμρ, hk'j, smul_eq_mul, hnN]
      push_cast
      ring
    let ψβ := (homEquiv P (VermaModule P μ) (μ - r • P.rootOf k')).symm ⟨_, hθβprim⟩
    have hψβv : ψβ (hwv P _) = equivEnvNNeg P μ (θβ μ) :=
      congrArg Subtype.val ((homEquiv P (VermaModule P μ) _).apply_symm_apply ⟨_, hθβprim⟩)
    have hnN0 : 0 < nN := by omega
    have hfprim := toEnd_f_pow_hwv_mem_primitiveVectors P hA hnN0 hν'j
    have hwt : P.reflection hA j (μ - r • P.rootOf k' + P.rho) - P.rho =
        Λ - r • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) := by
      rw [reflection_apply, hν'j, hβval, hΛμ, hnN]
      simp only [← Nat.cast_smul_eq_nsmul K]
      push_cast
      module
    rw [hwt] at hfprim
    have hwprim : equivEnvNNeg P μ (fEnv P j ^ nN * θβ μ) ∈ primitiveVectors P
        (VermaModule P μ) (Λ - r • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) := by
      rw [equivEnvNNeg_fEnv_pow_mul, ← hψβv, ← map_toEnd_pow]
      exact map_mem_primitiveVectors ψβ hfprim
    obtain ⟨X, hX, hXprim⟩ :=
      exists_mul_fEnv_pow_eq hfin hv hΛ (by omega : 0 < Q) hμρ hΛμ hwprim
    have hXeq : X * fEnv P j ^ Q = fEnv P j ^ nN * θβ μ := (equivEnvNNeg P μ).injective hX
    have hXW : X ∈ Wν := by
      have h3 := (mem_primitiveVectors.mp hXprim).1
      rw [hvk, ← hcastγ] at h3
      exact (equivEnvNNeg_mem_weightSpace_iff P Λ _ X).mp h3
    have hnf : nf Λ = (nN : K) := by
      simp only [nf, hqf, hnN]
      push_cast
      ring
    have hEΛ : E Λ = ∑ l ∈ Finset.range (J + 1), nN.choose l •
        ((LinearMap.commutator K (fEnv P j) ^ l) (θβ μ) * fEnv P j ^ (J - l)) := by
      simp only [E, hnf, hqf, ← hμdef]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [← Nat.cast_smul_eq_nsmul K, choose_eq_descPochhammer, div_eq_mul_inv]
    have hXE : X * fEnv P j ^ (J - r * p) = E Λ := by
      apply mul_right_cancel₀ (fEnv_pow_ne_zero j (nN - J))
      rw [mul_assoc, ← pow_add, show J - r * p + (nN - J) = Q by omega, hXeq, hEΛ]
      exact LinearMap.pow_mul_eq_sum_mul_pow (by omega) (hJ μ)
    have hθΛ : θ₀ Λ = X := by
      change π (L (E Λ)) = X
      rw [← hXE, hLy]
      exact Submodule.projection_apply_of_mem_left hWc hXW
    refine ⟨fun x hx ↦ ?_, ?_⟩
    · rw [hθΛ, actEnv_apply, lie_eq_zero_of_mem_nPos (mem_primitiveVectors.mp hXprim).2 hx,
        map_zero]
    · rw [hθΛ]
      have hs1 := (hasSymbol_shapovalovLead (P := P) r aγ).mul ((hasSymbol_fEnv (P := P) j).pow Q)
      have hs2 := ((hasSymbol_fEnv (P := P) j).pow nN).mul (hθβ.hasSymbol hposβ μ)
      rw [one_mul] at hs1 hs2
      rw [← hXeq] at hs2
      have hsym : fSym P j ^ nN * ∏ l, fSym P l ^ (r * aβ l) =
          (∏ l, fSym P l ^ (r * aγ l)) * fSym P j ^ Q := by
        have hprod : ∏ l, fSym P l ^ (r * aγ l) =
            (∏ l, fSym P l ^ (r * aβ l)) * fSym P j ^ (r * p) := by
          simp only [haγ, mul_add, pow_add, Finset.prod_mul_distrib]
          congr 1
          rw [Finset.prod_eq_single j (fun l _ hl ↦ by simp [hl]) (by simp)]
          simp
        rw [hprod, hnN, pow_add]
        ring
      rw [hsym] at hs2
      have hdeg : nN + r * ∑ l, aβ l = r * ∑ l, aγ l + Q := by
        rw [hsum, hnN]
        ring
      rw [hdeg] at hs2
      have hD : r * ∑ l, aγ l + Q = (r * ∑ l, aγ l - 1 + Q) + 1 := by omega
      rw [hD] at hs1 hs2
      have hsub := hs2.sub_mem hs1
      rw [← sub_mul] at hsub
      exact mem_filtration_of_mul_pow_mem (hasSymbol_fEnv j) (fSym_ne_zero j) hsub
  /- Density: the two linear forms `⟨-, γ^∨⟩` and `⟨-, αⱼ^∨⟩` are not proportional. -/
  have hcoef : ∀ Λ, P.corootPairing hA (Λ + P.rho) v i = r ↔
      Dual.eval K H b Λ = r - P.corootPairing hA P.rho v i := by
    intro Λ
    rw [Dual.eval_apply, hb, corootPairing_add, eq_sub_iff_add_eq]
  obtain ⟨δ, hδa, hδb⟩ : ∃ δ, Dual.eval K H b δ = 0 ∧ Dual.eval K H (P.coroot j) δ = 1 := by
    refine exists_apply_eq_zero_apply_eq_one
      (x₀ := (1 / 2 : K) • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) ?_ fun h ↦ ?_
    · rw [Dual.eval_apply, hb, corootPairing_smul, corootPairing_apply_root]
      norm_num
    · refine not_isPosRoot_of_forall_coroot_eq hfin hv (Dual.eval K H (P.coroot j)
        ((1 / 2 : K) • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i))) (fun x ↦ ?_) hsv
      rw [← hb x]
      exact h x
  refine IsShapovalovElement.of_hyperplane (θ := θ₀) hθ₀
    (fun Λ ↦ Submodule.projection_apply_mem hWc _) (fun Λ hΛ x hx ↦ ?_) (fun Λ hΛ ↦ ?_)
  · have h3 := mem_of_forall_nat (actEnv_mem_polyFam x hθ₀) ⊥ hδa hδb (J + 2)
      (fun Λ' hΛ' m hm hψ ↦ by
        rw [Submodule.mem_bot]
        exact (key Λ' ((hcoef Λ').mpr hΛ') m hm hψ).1 x hx) ((hcoef Λ).mp hΛ)
    exact (Submodule.mem_bot K).mp h3
  · exact mem_of_forall_nat (sub_mem_polyFam hθ₀ (const_mem_polyFam _)) _ hδa hδb (J + 2)
      (fun Λ' hΛ' m hm hψ ↦ (key Λ' ((hcoef Λ').mpr hΛ') m hm hψ).2) ((hcoef Λ).mp hΛ)

/-! ### Shapovalov's theorem -/

theorem exists_isShapovalovElement_aux [IsAlgClosed K] [FiniteDimensional K H]
    {hA : A.IsGeneralizedCartan} (hfin : A.IsFiniteCartan) (n : ℕ) :
    ∀ (v : P.weylGroup hA) (i : ι) (k : ι → ℤ), 0 ≤ k →
      (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf k → ∑ l, k l = n →
      ∀ r : ℕ, 0 < r → ∃ θ, IsShapovalovElement P hA v i r (fun l ↦ (k l).toNat) θ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v i k hk hvk hn r hr
  by_cases h1 : 1 < n
  · obtain ⟨j, -, hp, hsv⟩ := exists_simple_descent hfin hk hvk (by rw [hn]; exact_mod_cast h1)
    have hβ : (((P.coxeterSystem hA).simple j * v : P.weylGroup hA) :
        Dual K H ≃ₗ[K] Dual K H) (P.root i) =
          P.rootOf (k - (A *ᵥ k) j • Pi.single j 1 : ι → ℤ) := by
      rw [simple_mul_apply_root, hvk, reflection_rootOf]
    have hk' : 0 ≤ k - (A *ᵥ k) j • Pi.single j 1 := by
      obtain ⟨k'', hk'', h''⟩ := hsv
      rw [hβ] at h''
      rw [P.rootOf_injective h'']
      exact hk''
    have hsum' : ∑ l, (k - (A *ᵥ k) j • Pi.single j 1 : ι → ℤ) l = (n : ℤ) - (A *ᵥ k) j := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_sub_distrib, hn, ← Finset.mul_sum]
      simp
    have hnn : (0 : ℤ) ≤ (n : ℤ) - (A *ᵥ k) j := by
      rw [← hsum']
      exact Finset.sum_nonneg fun l _ ↦ hk' l
    obtain ⟨θβ, hθβ⟩ := ih ((n : ℤ) - (A *ᵥ k) j).toNat (by omega) _ i _ hk' hβ
      (by rw [hsum', Int.toNat_of_nonneg hnn]) r hr
    exact exists_isShapovalovElement_step hfin hk hvk hp hsv hr hθβ
  · have hk0 : k ≠ 0 := by
      rintro rfl
      rw [map_zero, LinearEquiv.map_eq_zero_iff] at hvk
      exact P.linearIndependent_root.ne_zero i hvk
    obtain ⟨j, hj⟩ : ∃ j, 0 < k j := by
      by_contra! h
      exact hk0 (funext fun l ↦ le_antisymm (h l) (hk l))
    have hsplit := Finset.add_sum_erase Finset.univ k (Finset.mem_univ j)
    have hnonneg := Finset.sum_nonneg (s := Finset.univ.erase j) fun l _ ↦ hk l
    have hrest : ∑ l ∈ Finset.univ.erase j, k l = 0 := by omega
    have hkj : k j = 1 := by omega
    have hkl : ∀ l, l ≠ j → k l = 0 := fun l hl ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun l _ ↦ hk l).mp hrest l
        (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)
    have hk1 : k = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl
        simp [hkj]
      · simp [hl, hkl l hl]
    have ha : (fun l ↦ (k l).toNat) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl
        simp [hk1]
      · simp [hk1, hl]
    rw [ha]
    refine ⟨_, (isShapovalovElement_simple hA j hr).of_corootPairing_eq fun x ↦ ?_⟩
    exact corootPairing_eq_of_apply_root_eq hfin (v := 1) (v' := v) (i := j) (i' := i)
      (by rw [hvk, hk1, rootOf_single]; rfl) x

/-- **Shapovalov's theorem, existence** ([HumO] Thm. 4.12): for `𝔤` of finite type over an
algebraically closed field of characteristic zero, a positive root `γ = v αᵢ = ∑ⱼ aⱼ αⱼ` and
`r > 0`, there is a Shapovalov element for `(γ, r)`. -/
theorem exists_isShapovalovElement [IsAlgClosed K] [FiniteDimensional K H]
    {hA : A.IsGeneralizedCartan} (hfin : A.IsFiniteCartan) {v : P.weylGroup hA} {i : ι}
    {a : ι → ℕ} (hva : (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf fun l ↦ (a l : ℤ))
    {r : ℕ} (hr : 0 < r) : ∃ θ, IsShapovalovElement P hA v i r a θ := by
  obtain ⟨θ, hθ⟩ := exists_isShapovalovElement_aux hfin (∑ l, a l) v i (fun l ↦ (a l : ℤ))
    (fun l ↦ by simp) hva (Nat.cast_sum _ _).symm r hr
  simp only [Int.toNat_natCast] at hθ
  exact ⟨θ, hθ⟩

/-- **Shapovalov's theorem** ([HumO] Thm. 4.12): for `𝔤` of finite type over an algebraically
closed field of characteristic zero, a positive root `γ = v αᵢ = ∑ⱼ aⱼ αⱼ` and `r > 0`, there is
a Shapovalov element `θ` for `(γ, r)`, and every Shapovalov element for `(γ, r)` is congruent to
`θ` modulo `U(𝔟⁻)(h_γ + ρ(h_γ) - r)`. -/
theorem shapovalov [IsAlgClosed K] [FiniteDimensional K H] {hA : A.IsGeneralizedCartan}
    (hfin : A.IsFiniteCartan) {v : P.weylGroup hA} {i : ι} {a : ι → ℕ}
    (hva : (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf fun l ↦ (a l : ℤ))
    {r : ℕ} (hr : 0 < r) :
    ∃ θ, IsShapovalovElement P hA v i r a θ ∧ ∀ θ', IsShapovalovElement P hA v i r a θ' →
      ∃ G ∈ polyFam P, ∀ Λ, θ' Λ - θ Λ = (P.corootPairing hA (Λ + P.rho) v i - r) • G Λ := by
  obtain ⟨θ, hθ⟩ := exists_isShapovalovElement hfin hva hr
  have ha0 : 0 < ∑ l, a l := by
    by_contra h0
    have hzero : (fun l ↦ ((a l : ℕ) : ℤ)) = 0 := funext fun l ↦ by
      have := Finset.single_le_sum (fun l _ ↦ Nat.zero_le (a l)) (Finset.mem_univ l)
      simp only [Pi.zero_apply, Nat.cast_eq_zero]
      omega
    rw [hzero, map_zero, LinearEquiv.map_eq_zero_iff] at hva
    exact P.linearIndependent_root.ne_zero i hva
  exact ⟨θ, hθ, fun θ' hθ' ↦ hθ'.exists_sub_eq_smul hfin hθ (Nat.mul_pos hr ha0)⟩

end Matrix.Realization.KacMoodyAlgebra.VermaModule
