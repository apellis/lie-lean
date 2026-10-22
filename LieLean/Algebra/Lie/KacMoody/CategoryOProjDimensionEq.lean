import LieLean.Algebra.Lie.KacMoody.CategoryOProjDimension
import LieLean.Algebra.Lie.KacMoody.CategoryOTranslation
import LieLean.Algebra.Lie.KacMoody.TranslationWallCrossing
import LieLean.Algebra.Lie.KacMoody.TranslationWallHead
import LieLean.Algebra.Lie.KacMoody.TranslationUpperClosureNonintegral
import LieLean.Algebra.Lie.KacMoody.DualIrreducible
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralWeylGroupAntidominant

noncomputable section

universe w u

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hF : A.IsFiniteCartan)

include hF in
/-- The `W`-invariant form of a finite-type Cartan matrix, through its normalization
`(x | v αᵢ) = dᵢ ⟨x, (v αᵢ)^∨⟩`: for `v αᵢ = ∑ kⱼ αⱼ`,
`dᵢ ⟨x, (v αᵢ)^∨⟩ = ∑ kⱼ dⱼ ⟨x, αⱼ^∨⟩`. -/
lemma exists_corootPairing_mul_eq_sum :
    ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ ∀ (x : Dual K H) (v : P.weylGroup hF.isGeneralizedCartan)
      (i : ι) (k : ι → ℤ), (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf k →
        (d i : K) * P.corootPairing hF.isGeneralizedCartan x v i =
          ∑ l, ((k l * d l : ℤ) : K) * x (P.coroot l) := by
  have hA := hF.isGeneralizedCartan
  obtain ⟨d, hdpos, hpos⟩ := hF.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  refine ⟨d, hdpos, fun x v i k hvk ↦ ?_⟩
  have hi : (d i : K) ≠ 0 := by exact_mod_cast (hdpos i).ne'
  have h : P.dualBilinForm S x ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) =
      d i * P.corootPairing hA x v i := by
    rw [← P.dualBilinForm_weylGroup hA S (v⁻¹).2 x, P.inv_apply_apply v,
      dualBilinForm_root_right]
    simp only [S, Symmetrization.ofDiagonal, corootPairing]
    push_cast
    field_simp
  rw [← h, hvk, (P.isSymm_dualBilinForm S).eq, P.dualBilinForm_ofDiagonal_rootOf d hdpos hsymm]

include hF in
/-- In finite type, the pairing with the coroot of a positive real root is a nonzero
nonnegative integral combination of the pairings with the simple coroots. -/
lemma exists_corootPairing_eq_sum {v : P.weylGroup hF.isGeneralizedCartan} {i : ι}
    (hv : P.IsPosRoot hF.isGeneralizedCartan v i) :
    ∃ k : ι → ℕ, k ≠ 0 ∧ ∀ x : Dual K H,
      P.corootPairing hF.isGeneralizedCartan x v i = ∑ j, (k j : K) * x (P.coroot j) := by
  have hA := hF.isGeneralizedCartan
  obtain ⟨d, hdpos, hd⟩ := exists_corootPairing_mul_eq_sum (P := P) hF
  obtain ⟨k, hk, hvk⟩ := hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearEquiv.map_eq_zero_iff] at hvk
    exact P.linearIndependent_root.ne_zero i hvk
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk0
  have hkj : 0 < k j := lt_of_le_of_ne (hk j) (Ne.symm hj)
  have hN : (0 : ℤ) < ∑ l, k l * d l :=
    Finset.sum_pos' (fun l _ ↦ mul_nonneg (hk l) (hdpos l).le)
      ⟨j, Finset.mem_univ _, mul_pos hkj (hdpos j)⟩
  have hρ : (d i : K) * P.corootPairing hA P.rho v i = ((∑ l, k l * d l : ℤ) : K) := by
    rw [hd P.rho v i k hvk]
    simp
  obtain ⟨k', hk', ε, hε, h⟩ := P.exists_apply_coroot_eq_sum hA (v⁻¹).2 i
  have hcp : ∀ x : Dual K H, P.corootPairing hA x v i = ε * ∑ l, (k' l : K) * x (P.coroot l) :=
    fun x ↦ h x
  have hM : 0 ≤ ∑ l, k' l := Finset.sum_nonneg fun l _ ↦ hk' l
  have hint : d i * (ε * ∑ l, k' l) = ∑ l, k l * d l := by
    have := hcp P.rho
    simp only [rho_coroot, mul_one] at this
    rw [this] at hρ
    exact_mod_cast hρ
  have hε1 : ε = 1 := by
    rcases hε with rfl | rfl
    · rfl
    · nlinarith [hdpos i]
  subst hε1
  refine ⟨fun l ↦ (k' l).toNat, ?_, fun x ↦ ?_⟩
  · intro h0
    have : ∑ l, k' l = (0 : ℤ) := Finset.sum_eq_zero fun l _ ↦ by
      have := congrFun h0 l
      simp only [Pi.zero_apply, Int.toNat_eq_zero] at this
      exact le_antisymm this (hk' l)
    rw [this] at hint
    omega
  · rw [hcp x, Int.cast_one, one_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (hk' l)).symm

include hF in
/-- A dominant integral weight pairs with the coroot of a positive root in `ℕ`. -/
lemma exists_nat_corootPairing {x : Dual K H} (hx : ∀ j, ∃ n : ℕ, x (P.coroot j) = n)
    {v : P.weylGroup hF.isGeneralizedCartan} {i : ι}
    (hv : P.IsPosRoot hF.isGeneralizedCartan v i) :
    ∃ n : ℕ, P.corootPairing hF.isGeneralizedCartan x v i = n := by
  choose n hn using hx
  obtain ⟨k, -, hk⟩ := exists_corootPairing_eq_sum hF hv
  exact ⟨∑ j, k j * n j, by rw [hk x]; push_cast; simp [hn]⟩

include hF in
/-- For `x` dominant integral, `x + ρ` pairs with the coroot of a positive root in `ℕ_{>0}`. -/
lemma exists_nat_corootPairing_add_rho {x : Dual K H} (hx : ∀ j, ∃ n : ℕ, x (P.coroot j) = n)
    {v : P.weylGroup hF.isGeneralizedCartan} {i : ι}
    (hv : P.IsPosRoot hF.isGeneralizedCartan v i) :
    ∃ n : ℕ, P.corootPairing hF.isGeneralizedCartan (x + P.rho) v i = n + 1 := by
  choose n hn using hx
  obtain ⟨k, hk0, hk⟩ := exists_corootPairing_eq_sum hF hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk0
  have hs : 1 ≤ ∑ l, k l := le_trans (Nat.one_le_iff_ne_zero.mpr hj)
    (Finset.single_le_sum (fun l _ ↦ Nat.zero_le (k l)) (Finset.mem_univ j))
  refine ⟨∑ l, k l * n l + (∑ l, k l - 1), ?_⟩
  rw [hk]
  simp only [LinearMap.add_apply, rho_coroot, hn]
  push_cast [Nat.cast_sub hs]
  simp only [mul_add, mul_one, Finset.sum_add_distrib]
  ring

/-- The weight `b` with `⟨b, αⱼ^∨⟩ = 1` for `j ≠ i` and `⟨b, αᵢ^∨⟩ = 0`: `ρ` minus the
fundamental weight `ϖᵢ`. -/
def wallWeight (P : Realization A K H) (i : ι) : Dual K H :=
  P.rho - LinearMap.proj i ∘ₗ P.corootCoord

omit [CharZero K] [FiniteDimensional K H] in
lemma wallWeight_coroot (i j : ι) :
    P.wallWeight i (P.coroot j) = if j = i then 0 else 1 := by
  by_cases h : j = i
  · subst h; simp [wallWeight]
  · simp [wallWeight, h, Ne.symm h]

include hF in
/-- The only positive root `β` with `⟨b, β^∨⟩ = 0` for `b` the wall weight of `i` is `αᵢ`. -/
lemma apply_root_eq_of_corootPairing_wallWeight {u : P.weylGroup hF.isGeneralizedCartan}
    {i j : ι} (hu : P.IsPosRoot hF.isGeneralizedCartan u j)
    (h0 : P.corootPairing hF.isGeneralizedCartan (P.wallWeight i) u j = 0) :
    (u : Dual K H ≃ₗ[K] Dual K H) (P.root j) = P.root i := by
  have hA := hF.isGeneralizedCartan
  obtain ⟨k, -, hk⟩ := exists_corootPairing_eq_sum hF hu
  -- `k l = 0` for `l ≠ i`
  have hkl : ∀ l, l ≠ i → k l = 0 := by
    have hsum : ((∑ l, if l = i then 0 else k l : ℕ) : K) = 0 := by
      rw [← h0, hk]
      push_cast
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [wallWeight_coroot]
      split_ifs <;> simp
    have hsum' : (∑ l, if l = i then 0 else k l) = 0 := by exact_mod_cast hsum
    intro l hl
    have := (Finset.sum_eq_zero_iff.mp hsum') l (Finset.mem_univ l)
    simpa [hl] using this
  have hki : ∀ x : Dual K H, P.corootPairing hA x u j = (k i : K) * x (P.coroot i) := by
    intro x
    rw [hk, Finset.sum_eq_single i (fun l _ hl ↦ by simp [hkl l hl]) (by simp)]
  obtain ⟨k'', hk''0, hk''⟩ := hu
  obtain ⟨d, hdpos, hd⟩ := exists_corootPairing_mul_eq_sum (P := P) hF
  have hk''l : ∀ l, l ≠ i → k'' l = 0 := by
    intro l hl
    have h := hd (LinearMap.proj l ∘ₗ P.corootCoord) u j k'' hk''
    rw [hki] at h
    simp only [LinearMap.coe_comp, Function.comp_apply, corootCoord_coroot, LinearMap.coe_proj,
      Function.eval, Pi.single_apply, hl, ite_false, mul_zero, mul_ite, mul_one] at h
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    have : k'' l * d l = 0 := by exact_mod_cast h.symm
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' (hdpos l).ne'
  have hβ : P.rootOf k'' = (k'' i : K) • P.root i := by
    rw [rootOf_apply, Finset.sum_eq_single i (fun l _ hl ↦ by simp [hk''l l hl]) (by simp)]
  -- `⟨β, β^∨⟩ = 2`
  have h2 : P.corootPairing hA ((u : Dual K H ≃ₗ[K] Dual K H) (P.root j)) u j = 2 := by
    rw [corootPairing, P.inv_apply_apply u]
    exact P.root_coroot_self hA j
  rw [hk'', hβ, hki] at h2
  simp only [LinearMap.smul_apply, P.root_coroot_self hA, smul_eq_mul] at h2
  have h1 : (k i : ℤ) * k'' i = 1 := by
    have : ((k i : ℤ) * k'' i : K) * 2 = 1 * 2 := by
      push_cast; linear_combination h2
    exact_mod_cast mul_right_cancel₀ (two_ne_zero) this
  have hk''1 : k'' i = 1 := by
    have h0i : 0 ≤ k'' i := hk''0 i
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · omega
  rw [hk'', hβ, hk''1, Int.cast_one, one_smul]

include hF in
/-- There is `y ∈ W` sending every positive root to a negative root (the longest element). -/
lemma exists_forall_not_isPosRoot_mul :
    ∃ y : P.weylGroup hF.isGeneralizedCartan, ∀ v i,
      P.IsPosRoot hF.isGeneralizedCartan v i → ¬P.IsPosRoot hF.isGeneralizedCartan (y * v) i := by
  obtain ⟨y, -, hy⟩ := P.exists_isAntidominant_weylDot hF 0
  refine ⟨y⁻¹, fun v i hv hyv ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_corootPairing_add_rho (P := P) hF (x := 0)
    (fun j ↦ ⟨0, by simp⟩) hyv
  have h := hy v i hv (n + 1)
  rw [zero_add, sub_add_cancel, corootPairing_apply, ← zero_add P.rho, hn] at h
  exact absurd (h (by push_cast; ring)) (by omega)

omit [FiniteDimensional K H] in
/-- If `y` sends positive roots to negative roots, it sends negative roots to positive roots. -/
lemma isPosRoot_mul_of_not {hA : A.IsGeneralizedCartan} {y : P.weylGroup hA}
    (hy : ∀ v i, P.IsPosRoot hA v i → ¬P.IsPosRoot hA (y * v) i) {v : P.weylGroup hA} {i : ι}
    (hv : ¬P.IsPosRoot hA v i) : P.IsPosRoot hA (y * v) i := by
  have hvs := (P.isPosRoot_or v i).resolve_left hv
  refine (P.isPosRoot_or (y * v) i).resolve_right fun h ↦ hy _ _ hvs ?_
  rwa [← mul_assoc]

/-! ### The wall setup -/

section Wall

variable {y : P.weylGroup hF.isGeneralizedCartan}
  (hy : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i →
    ¬P.IsPosRoot hF.isGeneralizedCartan (y * v) i)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hF hy hΛ

/-- `λ = y·Λ` is antidominant and regular: `⟨λ + ρ, β^∨⟩ ∈ ℤ_{<0}` for every positive root `β`. -/
lemma exists_corootPairing_weylDot_eq_neg {v : P.weylGroup hF.isGeneralizedCartan} {j : ι}
    (hv : P.IsPosRoot hF.isGeneralizedCartan v j) :
    ∃ n : ℕ, P.corootPairing hF.isGeneralizedCartan
      (P.weylDot hF.isGeneralizedCartan y Λ + P.rho) v j = -(n + 1 : K) := by
  have hA := hF.isGeneralizedCartan
  have hn : ¬P.IsPosRoot hA (y⁻¹ * v) j := fun h ↦ hy _ _ h (by rwa [← mul_assoc,
    mul_inv_cancel, one_mul])
  obtain ⟨n, hn⟩ := exists_nat_corootPairing_add_rho hF hΛ ((P.isPosRoot_or _ j).resolve_left hn)
  refine ⟨n, ?_⟩
  rw [weylDot_add_rho, corootPairing_apply, ← neg_neg (P.corootPairing hA _ _ j),
    ← corootPairing_mul_simple, hn]

lemma isAntidominant_weylDot : P.IsAntidominant hF.isGeneralizedCartan
    (P.weylDot hF.isGeneralizedCartan y Λ) := by
  intro v j hv m hm
  obtain ⟨n, hn⟩ := exists_corootPairing_weylDot_eq_neg hF hy hΛ hv
  rw [hn] at hm
  have : (m : K) = ((-(n + 1 : ℤ)) : ℤ) := by rw [← hm]; push_cast; ring
  have := Int.cast_injective this
  omega

omit hΛ [CharZero K] [FiniteDimensional K H] in
lemma not_isPosRoot_inv_mul {v : P.weylGroup hF.isGeneralizedCartan} {j : ι}
    (hv : P.IsPosRoot hF.isGeneralizedCartan v j) :
    ¬P.IsPosRoot hF.isGeneralizedCartan (y⁻¹ * v) j := fun h ↦
  hy _ _ h (by rwa [← mul_assoc, mul_inv_cancel, one_mul])

omit hF hy hΛ [CharZero K] [FiniteDimensional K H] in
lemma isPosRoot_one (hA : A.IsGeneralizedCartan) (i : ι) : P.IsPosRoot hA 1 i :=
  ⟨Pi.single i 1, Pi.single_nonneg.mpr zero_le_one, by simp⟩

omit hy hΛ [FiniteDimensional K H] in
lemma not_isPosRoot_simple (i : ι) : ¬P.IsPosRoot hF.isGeneralizedCartan
    ((P.coxeterSystem hF.isGeneralizedCartan).simple i) i := fun h ↦
  P.not_isPosRoot_and (isPosRoot_one hF.isGeneralizedCartan i) (by rwa [one_mul])

omit hΛ [FiniteDimensional K H] in
/-- `y sᵢ αᵢ = -y αᵢ` is a positive root. -/
lemma isPosRoot_mul_simple (i : ι) : P.IsPosRoot hF.isGeneralizedCartan
    (y * (P.coxeterSystem hF.isGeneralizedCartan).simple i) i :=
  isPosRoot_mul_of_not hy (not_isPosRoot_simple hF i)

omit hΛ in
/-- The wall weight `μ = y b - ρ` is antidominant. -/
lemma isAntidominant_wall (i : ι) : P.IsAntidominant hF.isGeneralizedCartan
    ((y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho) := by
  have hA := hF.isGeneralizedCartan
  intro v j hv m hm
  have hb : ∀ l, ∃ n : ℕ, P.wallWeight i (P.coroot l) = n := fun l ↦ by
    rw [wallWeight_coroot]; split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  obtain ⟨n, hn⟩ := exists_nat_corootPairing hF hb
    ((P.isPosRoot_or _ j).resolve_left (not_isPosRoot_inv_mul hF hy hv))
  rw [sub_add_cancel, corootPairing_apply, ← neg_neg (P.corootPairing hA _ _ j),
    ← corootPairing_mul_simple, hn] at hm
  have : (m : K) = ((-(n : ℤ)) : ℤ) := by rw [← hm]; push_cast; ring
  have := Int.cast_injective this
  omega

omit hy hΛ [FiniteDimensional K H] in
lemma corootPairing_wall_mul_simple (i : ι) : P.corootPairing hF.isGeneralizedCartan
    ((y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho + P.rho)
      (y * (P.coxeterSystem hF.isGeneralizedCartan).simple i) i = 0 := by
  rw [sub_add_cancel, corootPairing_apply, show y⁻¹ * (y *
    (P.coxeterSystem hF.isGeneralizedCartan).simple i) =
      1 * (P.coxeterSystem hF.isGeneralizedCartan).simple i by group,
    corootPairing_mul_simple, corootPairing_one, wallWeight_coroot, ite_eq_left_iff.mpr (fun h => absurd rfl h), neg_zero]

omit hy hΛ [FiniteDimensional K H] in
lemma corootPairing_weylDot_mul_simple (i : ι) : P.corootPairing hF.isGeneralizedCartan
    (P.weylDot hF.isGeneralizedCartan y Λ + P.rho)
      (y * (P.coxeterSystem hF.isGeneralizedCartan).simple i) i = -(Λ (P.coroot i) + 1) := by
  rw [weylDot_add_rho, corootPairing_apply, show y⁻¹ * (y *
    (P.coxeterSystem hF.isGeneralizedCartan).simple i) =
      1 * (P.coxeterSystem hF.isGeneralizedCartan).simple i by group,
    corootPairing_mul_simple, corootPairing_one]
  simp

omit hy hΛ in
/-- The only roots `β` with `⟨μ + ρ, β^∨⟩ = 0` are `±y αᵢ`. -/
lemma apply_root_eq_or_of_corootPairing_wall (i : ι) {v : P.weylGroup hF.isGeneralizedCartan}
    {j : ι} (h0 : P.corootPairing hF.isGeneralizedCartan
      ((y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho + P.rho) v j = 0) :
    (v : Dual K H ≃ₗ[K] Dual K H) (P.root j) =
        ((y * (P.coxeterSystem hF.isGeneralizedCartan).simple i :
          P.weylGroup hF.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
      (v : Dual K H ≃ₗ[K] Dual K H) (P.root j) =
        -((y * (P.coxeterSystem hF.isGeneralizedCartan).simple i :
          P.weylGroup hF.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) (P.root i) := by
  have hA := hF.isGeneralizedCartan
  rw [sub_add_cancel, corootPairing_apply] at h0
  rw [mul_simple_apply_root, neg_neg]
  have hv : v = y * (y⁻¹ * v) := by group
  rcases P.isPosRoot_or (y⁻¹ * v) j with hu | hu
  · right
    rw [hv, Subgroup.coe_mul, LinearEquiv.mul_apply,
      apply_root_eq_of_corootPairing_wallWeight hF hu h0]
  · left
    have h0' : P.corootPairing hA (P.wallWeight i) (y⁻¹ * v *
        (P.coxeterSystem hA).simple j) j = 0 := by
      rw [corootPairing_mul_simple, h0, neg_zero]
    have h := apply_root_eq_of_corootPairing_wallWeight hF hu h0'
    rw [mul_simple_apply_root, neg_eq_iff_eq_neg] at h
    rw [hv, Subgroup.coe_mul, LinearEquiv.mul_apply, h, map_neg]

omit hF hy [CharZero K] [FiniteDimensional K H] in
/-- `ν = Λ + ρ - b` is dominant integral. -/
lemma isDominantIntegral_sub_wallWeight (i : ι) :
    P.IsDominantIntegral (Λ + P.rho - P.wallWeight i) := by
  intro j
  obtain ⟨n, hn⟩ := hΛ j
  refine ⟨n + if j = i then 1 else 0, ?_⟩
  rw [LinearMap.sub_apply, LinearMap.add_apply, hn, rho_coroot, wallWeight_coroot]
  split_ifs <;> simp

omit hy hΛ [CharZero K] [FiniteDimensional K H] in
lemma inv_apply_weylDot_sub_wall (i : ι) :
    ((y⁻¹ : P.weylGroup hF.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H)
      (P.weylDot hF.isGeneralizedCartan y Λ -
        ((y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho)) =
      Λ + P.rho - P.wallWeight i := by
  rw [weylDot, show ∀ a b c : Dual K H, a - c - (b - c) = a - b from fun a b c ↦ by abel,
    ← map_sub, P.inv_apply_apply]

/-- `μ - λ = -y ν` is dominant integral. -/
lemma isDominantIntegral_wall_sub_weylDot (i : ι) :
    P.IsDominantIntegral ((y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho -
      P.weylDot hF.isGeneralizedCartan y Λ) := by
  have hA := hF.isGeneralizedCartan
  intro j
  have hn : ¬P.IsPosRoot hA y⁻¹ j := fun h ↦ hy _ _ h (by
    rw [mul_inv_cancel]; exact isPosRoot_one hA j)
  obtain ⟨n, hn⟩ := exists_nat_corootPairing hF (isDominantIntegral_sub_wallWeight hΛ i)
    ((P.isPosRoot_or _ j).resolve_left hn)
  refine ⟨n, ?_⟩
  rw [show (y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho -
      P.weylDot hA y Λ = -(y : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho - P.wallWeight i) by
    rw [weylDot, map_sub, map_add]; abel,
    LinearMap.neg_apply, apply_coroot_eq_corootPairing, ← neg_neg (P.corootPairing hA _ _ j),
    ← corootPairing_mul_simple, hn, neg_neg]

end Wall

end Matrix.Realization

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with `Extⁿ(X₂, Y) = 0`, the connecting map
`Extⁿ(X₁, Y) → Extⁿ⁺¹(X₃, Y)` is injective. -/
theorem extClass_comp_ne_zero {S : ShortComplex C} (hS : S.ShortExact) {Y : C} {n : ℕ}
    (h₂ : ∀ x : Ext.{w} S.X₂ Y n, x = 0) {x₁ : Ext.{w} S.X₁ Y n} (hx₁ : x₁ ≠ 0) :
    hS.extClass.comp x₁ (add_comm 1 n) ≠ 0 := fun h ↦ by
  obtain ⟨x₂, hx₂⟩ := contravariant_sequence_exact₁ hS Y x₁ (add_comm 1 n) h
  rw [h₂ x₂, comp_zero] at hx₂
  exact hx₁ hx₂.symm

end CategoryTheory.Abelian.Ext

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

open CategoryTheory VermaModule

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- An object of `𝒪` whose underlying module is trivial is zero. -/
theorem isZero_of_subsingleton (X : CategoryO.{u} P) [Subsingleton X.obj] : Limits.IsZero X := by
  have : Subsingleton ((IsObj.{u} P).ι.obj X) := inferInstanceAs (Subsingleton X.obj)
  exact Limits.IsZero.of_full_of_faithful_of_isZero (IsObj.{u} P).ι _
    (ModuleCat.isZero_of_subsingleton _)

variable (hA : A.IsFiniteCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

include hΛ in
/-- The step of [HumO] §6.9: for `ℓ(u sᵢ) < ℓ(u)`, a nonzero class in `Extⁿ(M(u sᵢ·Λ), L(Λ))`
gives a nonzero class in `Extⁿ⁺¹(M(u·Λ), L(Λ))`. The connecting map of the wall-crossing sequence
`0 → M(u sᵢ·Λ) → Θ M(u·Λ) → M(u·Λ) → 0` (for a regular antidominant `λ = y·Λ` and the wall of
`y αᵢ`) is injective, since `Extⁿ(Θ M(u·Λ), L(Λ)) ≅ Extⁿ(T M(u·Λ), T' L(Λ))` and `L(Λ)` is
killed by translation onto the wall. -/
theorem exists_ext_verma_simple_ne_zero_succ (i : ι) {u : P.weylGroup hA.isGeneralizedCartan}
    (hu : P.IsPosRoot hA.isGeneralizedCartan (u * (P.coxeterSystem hA.isGeneralizedCartan).simple i) i)
    {n : ℕ} (h : ∃ x : Abelian.Ext.{u} (verma P (P.weylDot hA.isGeneralizedCartan
      (u * (P.coxeterSystem hA.isGeneralizedCartan).simple i) Λ)) (simple P Λ) n, x ≠ 0) :
    ∃ x : Abelian.Ext.{u} (verma P (P.weylDot hA.isGeneralizedCartan u Λ)) (simple P Λ) (n + 1),
      x ≠ 0 := by
  have hA' := hA.isGeneralizedCartan
  obtain ⟨y, hy⟩ := exists_forall_not_isPosRoot_mul (P := P) hA
  set s := (P.coxeterSystem hA').simple i
  set lam := P.weylDot hA' y Λ
  set μ := (y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho
  set ν := Λ + P.rho - P.wallWeight i
  set ν' := μ - lam
  set v₀ := y * s
  set w := u * y⁻¹
  have hlam := isAntidominant_weylDot hA hy hΛ
  have hμ := isAntidominant_wall hA hy i
  have hfacet : ∀ v j, P.IsPosRoot hA' v j → P.corootPairing hA' (lam + P.rho) v j = 0 →
      P.corootPairing hA' (μ + P.rho) v j = 0 := fun v j hv h0 ↦ by
    obtain ⟨m, hm⟩ := exists_corootPairing_weylDot_eq_neg hA hy hΛ hv
    rw [hm] at h0
    exact (Nat.cast_add_one_ne_zero m (neg_eq_zero.mp h0)).elim
  have hν := isDominantIntegral_sub_wallWeight hΛ i
  have hν' := isDominantIntegral_wall_sub_weylDot hA hy hΛ i
  have hzν : ((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (lam - μ) = ν :=
    inv_apply_weylDot_sub_wall (hF := hA) (y := y) i
  have hv₀ : P.IsPosRoot hA' v₀ i := isPosRoot_mul_simple hA hy i
  have hμα := corootPairing_wall_mul_simple (hF := hA) (y := y) i
  have hwall := fun v' i' (h0 : P.corootPairing hA' (μ + P.rho) v' i' = 0) ↦
    apply_root_eq_or_of_corootPairing_wall hA i h0
  obtain ⟨m, hm⟩ := hΛ i
  have hlamα : P.corootPairing hA' (lam + P.rho) v₀ i ≠ 0 := by
    rw [corootPairing_weylDot_mul_simple (hF := hA) (y := y) (Λ := Λ) i, hm]
    intro h0
    exact Nat.cast_add_one_ne_zero m (neg_eq_zero.mp h0)
  have hw : P.IsPosRoot hA' (w * v₀) i := by
    rwa [show w * v₀ = u * s by simp only [w, v₀]; group]
  set chiL := centralCharacter P lam
  set chiM := centralCharacter P μ
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν'
  let Xo := (translationFunctor (IrreducibleModule P ν') chiL chiM).obj
    (verma P (P.weylDot hA' w lam))
  let eX : Xo.obj ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν') chiL chiM
      (VermaModule P (P.weylDot hA' w lam)) :=
    (ofLieEquiv (P := P) (centralTranslation P (IrreducibleModule P ν') chiL chiM
      (verma P (P.weylDot hA' w lam)).obj)).symm.trans
      (centralTranslationEquiv P (IrreducibleModule P ν') chiL chiM
        (ofLieEquiv (P := P) (VermaModule P (P.weylDot hA' w lam))).symm)
  obtain ⟨f, g, hf, hg, hfg⟩ := wallCrossing_verma_shortExact P hA hlam hμ hfacet hν
    (y⁻¹).2 hzν hν' (1 : P.weylGroup hA').2 rfl hv₀ hμα hwall hlamα hw eX
  let Θo := (translationFunctor (IrreducibleModule P ν) chiM chiL).obj Xo
  let F : verma P (P.weylDot hA' (w * P.reflectionOf hA' v₀ i) lam) ⟶ Θo :=
    (IsObj.{u} P).homMk (ofLieModuleHom ((ofLieEquiv (P := P) _).toLieModuleHom.comp
      (f.comp (ofLieEquiv (P := P) (VermaModule P _)).symm.toLieModuleHom)))
  let G : Θo ⟶ verma P (P.weylDot hA' w lam) :=
    (IsObj.{u} P).homMk (ofLieModuleHom ((ofLieEquiv (P := P) _).toLieModuleHom.comp
      (g.comp (ofLieEquiv (P := P) _).symm.toLieModuleHom)))
  have hFG : F ≫ G = 0 := by
    ext x
    exact (hfg _).mpr ⟨_, rfl⟩
  let S := ShortComplex.mk F G hFG
  have hS : S.ShortExact := shortExact_of_lie (fun a b hab ↦ hf hab) (fun b ↦ hg b)
    (fun b hb ↦ (hfg b).mp hb)
  have h₂ : ∀ x : Abelian.Ext.{u} S.X₂ (simple P Λ) n, x = 0 := by
    obtain ⟨z'', hz'', hdom, ⟨eD⟩⟩ := IrreducibleModule.exists_equiv_dual (P := P) hA hν
    have hint : ∀ j, ∃ z : ℤ, lam (P.coroot j) = z := fun j ↦ by
      obtain ⟨k, hk⟩ := exists_corootPairing_weylDot_eq_neg hA hy hΛ (isPosRoot_one hA' j)
      rw [corootPairing_one, LinearMap.add_apply, rho_coroot] at hk
      exact ⟨-(k + 2 : ℤ), by push_cast; linear_combination hk⟩
    have hsimp : (⟨P.reflection hA' i, P.reflection_mem_weylGroup hA' i⟩ :
        P.weylGroup hA') = s := Subtype.ext (coxeterSystem_simple P hA' i).symm
    have hC : ¬P.UpperClosureCondition hA'
        (((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho))
        (((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho)) := by
      have key := not_upperClosureCondition_of_wall (P := P) hA (a := lam + P.rho) (b := μ + P.rho)
        (v := v₀) (w := s * y⁻¹) (i := i) hμα (n := -((m : ℤ) + 1)) (by omega) (by
          rw [corootPairing_weylDot_mul_simple (hF := hA) (y := y) (Λ := Λ) i, hm]; push_cast; ring)
        (by
          rw [show s * y⁻¹ * v₀ = 1 by simp [v₀, s, mul_assoc]]
          exact isPosRoot_one hA' i)
      rwa [show s * y⁻¹ * P.reflectionOf hA' v₀ i = y⁻¹ by
        simp [reflectionOf, hsimp, v₀, s, mul_assoc]] at key
    have hsub := translation_irreducible_of_not_upperClosureCondition_of_isAntidominant P hA
      hlam hμ hfacet hdom (z := z'' * ((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H))
      (mul_mem hz'' (y⁻¹).2) (by
        rw [LinearEquiv.mul_apply, show μ - lam = -(lam - μ) by abel, map_neg, hzν])
      y⁻¹ (by rw [P.integralWeylGroup_eq_top hA' hint]; trivial) hC
    have hΛ' : P.weylDot hA' y⁻¹ lam = Λ := by
      rw [← weylDot_mul, inv_mul_cancel, weylDot_one]
    rw [hΛ'] at hsub
    let T' := (translationFunctor (Module.Dual K (IrreducibleModule P ν)) chiL chiM).obj (simple P Λ)
    have : Subsingleton T'.obj := (((ofLieEquiv (P := P) _).symm.trans
      ((centralTranslationEquiv P _ chiL chiM (ofLieEquiv (P := P) (IrreducibleModule P Λ)).symm).trans
        (centralTranslationCoeffEquiv P (IrreducibleModule P Λ) chiL chiM eD))).toEquiv).subsingleton
    intro x
    have hz := Abelian.Ext.eq_zero_of_isZero_right (isZero_of_subsingleton T')
      (extTranslationEquiv (IrreducibleModule P ν) chiM chiL Xo (simple P Λ) n x)
    exact (LinearEquiv.map_eq_zero_iff _).mp hz
  have h1 : P.weylDot hA' (w * P.reflectionOf hA' v₀ i) lam = P.weylDot hA' (u * s) Λ := by
    have hsimp : (⟨P.reflection hA' i, P.reflection_mem_weylGroup hA' i⟩ :
        P.weylGroup hA') = s := Subtype.ext (coxeterSystem_simple P hA' i).symm
    rw [← weylDot_mul]
    congr 1
    simp [reflectionOf, hsimp, w, v₀, s, mul_assoc]
  have h3 : P.weylDot hA' w lam = P.weylDot hA' u Λ := by
    rw [← weylDot_mul]
    simp [w]
  obtain ⟨x, hx⟩ := h
  have hx' : ∃ x : Abelian.Ext.{u} (verma P (P.weylDot hA' (w * P.reflectionOf hA' v₀ i) lam))
      (simple P Λ) n, x ≠ 0 := by rw [h1]; exact ⟨x, hx⟩
  obtain ⟨x₁, hx₁⟩ := hx'
  rw [← h3]
  exact ⟨_, Abelian.Ext.extClass_comp_ne_zero hS h₂ (x₁ := x₁) hx₁⟩

include hΛ in
/-- **[HumO] Proposition 6.9 (a), lower bound**: `Ext^{ℓ(w)}(M(w·Λ), L(Λ)) ≠ 0` for `Λ` dominant
integral and `w ∈ W`. -/
theorem exists_ext_verma_weylDot_simple_ne_zero :
    ∀ (l : ℕ) (w : P.weylGroup hA.isGeneralizedCartan),
    (P.coxeterSystem hA.isGeneralizedCartan).length w = l →
    ∃ x : Abelian.Ext.{u} (verma P (P.weylDot hA.isGeneralizedCartan w Λ)) (simple P Λ) l,
      x ≠ 0 := by
  have hA' := hA.isGeneralizedCartan
  intro l
  induction l with
  | zero =>
    intro w hw
    rw [(P.coxeterSystem hA').length_eq_zero_iff.mp hw, weylDot_one]
    have := IrreducibleModule.isIrreducible P Λ
    have : Nontrivial (simple.{u} P Λ).obj :=
      (ofLieEquiv (P := P) (IrreducibleModule P Λ)).toEquiv.symm.nontrivial
    refine ⟨Abelian.Ext.mk₀ ((IsObj.{u} P).homMk (ofLieModuleHom
      (toSimple P Λ (simple P Λ) (ofLieEquiv (P := P) (IrreducibleModule P Λ)).symm))), ?_⟩
    rw [Ne, Abelian.Ext.mk₀_eq_zero_iff]
    intro h0
    obtain ⟨a, ha⟩ := exists_ne (0 : (simple.{u} P Λ).obj)
    obtain ⟨b, rfl⟩ := surjective_toSimple Λ (simple P Λ)
      (ofLieEquiv (P := P) (IrreducibleModule P Λ)).symm a
    exact ha (congrArg (fun φ ↦ φ.hom.hom b) h0)
  | succ l ih =>
    intro w hw
    have hw1 : w ≠ 1 := fun h ↦ by simp [h] at hw
    obtain ⟨i, hi⟩ := (P.coxeterSystem hA').exists_rightDescent_of_ne_one hw1
    have hl := (P.coxeterSystem hA').isRightDescent_iff.mp hi
    have hpos : P.IsPosRoot hA' (w * (P.coxeterSystem hA').simple i) i := by
      rw [isPosRoot_iff_not_isRightDescent]
      exact (P.coxeterSystem hA').isRightDescent_iff_not_isRightDescent_mul.mp hi
    exact exists_ext_verma_simple_ne_zero_succ hA hΛ i hpos (ih _ (by omega))

include hΛ in
/-- **[HumO] Proposition 6.9 (a)**: `pd M(w·Λ) = ℓ(w)` for `Λ` dominant integral and `w ∈ W`.
Finite type, algebraically closed field of characteristic zero (Humphreys works over `ℂ` with
`Λ = 0`). -/
theorem projectiveDimension_verma_weylDot (w : P.weylGroup hA.isGeneralizedCartan) :
    projectiveDimension (verma.{u} P (P.weylDot hA.isGeneralizedCartan w Λ)) =
      ((P.coxeterSystem hA.isGeneralizedCartan).length w : ℕ) := by
  refine le_antisymm ?_ ?_
  · exact (projectiveDimension_le_iff _ _).mpr (hasProjectiveDimensionLT_verma_weylDot hA hΛ w)
  · rw [projectiveDimension_ge_iff]
    intro h
    obtain ⟨x, hx⟩ := exists_ext_verma_weylDot_simple_ne_zero hA hΛ _ w rfl
    exact hx (x.eq_zero_of_hasProjectiveDimensionLT _ le_rfl)

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
