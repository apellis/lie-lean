/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Determinant
import LieLean.Algebra.Lie.KacMoody.TensorRep

/-!
# Verma modules as a polynomial family

Via the PBW isomorphism `U(𝔫₋) ≃ M(λ)`, `u ↦ u v_λ`, all Verma modules `M(λ)` have the same
underlying space `U(𝔫₋)`. We show that the action of `𝔤` depends polynomially on `λ`: for
`x ∈ 𝔤` and a polynomial family `λ ↦ F(λ) ∈ U(𝔫₋)` (a finite sum `∑ pₖ(λ) uₖ` with polynomial
functions `pₖ` on `𝔥*`), the family `λ ↦ x · F(λ)` (computed in `M(λ)`) is again polynomial
(`Matrix.Realization.KacMoodyAlgebra.VermaModule.actEnv_mem_polyFam`). Similarly the Shapovalov
pairing `λ ↦ B_λ(F(λ) v_λ, G(λ) v_λ)` of two polynomial families is a polynomial function
(`Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_mem_polyFun`). This is the
"universal Verma module" `U(𝔤) ⊗_{U(𝔟)} S(𝔥)` in disguise; it is the input for the Jantzen
filtration.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.polyFam`: polynomial families in `U(𝔫₋)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.actEnv`: the action of `𝔤` on `M(λ)`,
  transported to `U(𝔫₋)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.actEnv_mem_polyFam`: the action is polynomial.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_mem_polyFun`: the Shapovalov
  pairing of polynomial families is polynomial.
-/

open Module LieModule Module.Dual MvPolynomial UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K
local notation "𝒰⁻" => UniversalEnvelopingAlgebra K (nNeg P)
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))

omit [CharZero K] in
/-- `[eᵢ, 𝔫₋] ⊆ 𝔫₋ + 𝔥`. -/
lemma exists_lie_e_eq_add_h {y : P.KacMoodyAlgebra} (hy : y ∈ nNeg P) (i : ι) :
    ∃ y' ∈ nNeg P, ∃ b : H, ⁅e P i, y⁆ = y' + h P b := by
  obtain ⟨w, rfl⟩ := hy
  obtain ⟨w', b, hw⟩ := AuxLieAlgebra.lie_e_fHom P i w
  refine ⟨fHom P w', ⟨w', rfl⟩, b, ?_⟩
  change ⁅π P (AuxLieAlgebra.e P i), π P (AuxLieAlgebra.fHom P w)⁆ = _
  rw [← LieHom.map_lie, hw, map_add]
  rfl

namespace VermaModule

/-- Polynomial families `λ ↦ ∑ₖ pₖ(λ) uₖ` of elements of `U(𝔫₋)`, `pₖ` polynomial functions on
`𝔥*`. -/
def polyFam : Submodule K (Dual K H → 𝒰⁻) :=
  Submodule.span K {F | ∃ (p : MvPolynomial (PolyIdx K H) K) (u : 𝒰⁻),
    F = fun Λ ↦ evalPoly K H p Λ • u}

variable {P}

omit [CharZero K] in
lemma zero_mem_polyFam : (fun _ : Dual K H ↦ (0 : 𝒰⁻)) ∈ polyFam P := (polyFam P).zero_mem

omit [CharZero K] in
lemma add_mem_polyFam {F G : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) (hG : G ∈ polyFam P) :
    (fun Λ ↦ F Λ + G Λ) ∈ polyFam P := (polyFam P).add_mem hF hG

omit [CharZero K] in
lemma sub_mem_polyFam {F G : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) (hG : G ∈ polyFam P) :
    (fun Λ ↦ F Λ - G Λ) ∈ polyFam P := (polyFam P).sub_mem hF hG

omit [CharZero K] in
lemma const_smul_mem_polyFam (a : K) {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) :
    (fun Λ ↦ a • F Λ) ∈ polyFam P := (polyFam P).smul_mem a hF

omit [CharZero K] in
lemma smul_const_mem_polyFam {c : Dual K H → K} {d : ℕ} (hc : c ∈ polyLE K H d) (u : 𝒰⁻) :
    (fun Λ ↦ c Λ • u) ∈ polyFam P := by
  obtain ⟨p, -, rfl⟩ := mem_polyLE.mp hc
  exact Submodule.subset_span ⟨p, u, rfl⟩

omit [CharZero K] in
lemma const_mem_polyFam (u : 𝒰⁻) : (fun _ : Dual K H ↦ u) ∈ polyFam P := by
  simpa using smul_const_mem_polyFam (one_mem_polyLE (K := K) (H := H) 0) u

omit [CharZero K] in
/-- Multiplying a polynomial family by a polynomial function gives a polynomial family. -/
lemma smul_mem_polyFam {c : Dual K H → K} {d : ℕ} (hc : c ∈ polyLE K H d) {F : Dual K H → 𝒰⁻}
    (hF : F ∈ polyFam P) : (fun Λ ↦ c Λ • F Λ) ∈ polyFam P := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, u, rfl⟩ := hF
    simp only [smul_smul]
    obtain ⟨q, -, rfl⟩ := mem_polyLE.mp hc
    exact Submodule.subset_span ⟨q * p, u, by ext Λ; simp⟩
  | zero => simpa using zero_mem_polyFam
  | add F G _ _ hF hG => simpa [smul_add] using add_mem_polyFam hF hG
  | smul a F _ hF => simpa [smul_comm (c _) a] using const_smul_mem_polyFam a hF

omit [CharZero K] in
/-- Applying a fixed linear map to a polynomial family gives a polynomial family. -/
lemma map_mem_polyFam (L : 𝒰⁻ →ₗ[K] 𝒰⁻) {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) :
    (fun Λ ↦ L (F Λ)) ∈ polyFam P := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, u, rfl⟩ := hF
    exact Submodule.subset_span ⟨p, L u, by ext Λ; simp⟩
  | zero => simpa using zero_mem_polyFam
  | add F G _ _ hF hG => simpa using add_mem_polyFam hF hG
  | smul a F _ hF => simpa using const_smul_mem_polyFam a hF

variable (P) in
/-- The action of `x ∈ 𝔤` on `M(Λ)`, transported to `U(𝔫₋)` via `U(𝔫₋) ≃ M(Λ)`. -/
def actEnv (Λ : Dual K H) (x : P.KacMoodyAlgebra) : 𝒰⁻ →ₗ[K] 𝒰⁻ :=
  (equivEnvNNeg P Λ).symm.toLinearMap ∘ₗ (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) x) ∘ₗ
    (equivEnvNNeg P Λ).toLinearMap

lemma actEnv_apply (Λ : Dual K H) (x : P.KacMoodyAlgebra) (u : 𝒰⁻) :
    actEnv P Λ x u = (equivEnvNNeg P Λ).symm ⁅x, equivEnvNNeg P Λ u⁆ := rfl

lemma equivEnvNNeg_actEnv (Λ : Dual K H) (x : P.KacMoodyAlgebra) (u : 𝒰⁻) :
    equivEnvNNeg P Λ (actEnv P Λ x u) = ⁅x, equivEnvNNeg P Λ u⁆ := by
  rw [actEnv_apply, LinearEquiv.apply_symm_apply]

lemma actEnv_add (Λ : Dual K H) (x y : P.KacMoodyAlgebra) (u : 𝒰⁻) :
    actEnv P Λ (x + y) u = actEnv P Λ x u + actEnv P Λ y u := by
  simp [actEnv_apply, add_lie]

lemma actEnv_smul (Λ : Dual K H) (c : K) (x : P.KacMoodyAlgebra) (u : 𝒰⁻) :
    actEnv P Λ (c • x) u = c • actEnv P Λ x u := by
  simp [actEnv_apply, smul_lie]

lemma actEnv_lie (Λ : Dual K H) (x y : P.KacMoodyAlgebra) (u : 𝒰⁻) :
    actEnv P Λ ⁅x, y⁆ u = actEnv P Λ x (actEnv P Λ y u) - actEnv P Λ y (actEnv P Λ x u) := by
  simp [actEnv_apply, lie_lie]

lemma actEnv_of_mem_nNeg (Λ : Dual K H) {y : P.KacMoodyAlgebra} (hy : y ∈ nNeg P) (u : 𝒰⁻) :
    actEnv P Λ y u = UniversalEnvelopingAlgebra.ι K ⟨y, hy⟩ * u := by
  rw [actEnv_apply, LinearEquiv.symm_apply_eq, equivEnvNNeg_mul, map_ι, lie_eq_smul]
  rfl

/-- `x` acts polynomially on polynomial families. -/
def ActsPoly (x : P.KacMoodyAlgebra) : Prop :=
  ∀ F ∈ polyFam P, (fun Λ ↦ actEnv P Λ x (F Λ)) ∈ polyFam P

lemma ActsPoly.of_const {x : P.KacMoodyAlgebra}
    (h : ∀ u : 𝒰⁻, (fun Λ ↦ actEnv P Λ x u) ∈ polyFam P) : ActsPoly x := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, u, rfl⟩ := hF
    simpa [map_smul] using smul_mem_polyFam (mem_polyLE.mpr ⟨p, le_rfl, rfl⟩) (h u)
  | zero => simpa using zero_mem_polyFam
  | add F G _ _ hF hG => simpa using add_mem_polyFam hF hG
  | smul a F _ hF => simpa using const_smul_mem_polyFam a hF

lemma ActsPoly.add {x y : P.KacMoodyAlgebra} (hx : ActsPoly x) (hy : ActsPoly y) :
    ActsPoly (x + y) := fun F hF ↦ by
  simpa [actEnv_add] using add_mem_polyFam (hx F hF) (hy F hF)

lemma ActsPoly.smul {x : P.KacMoodyAlgebra} (c : K) (hx : ActsPoly x) : ActsPoly (c • x) :=
  fun F hF ↦ by simpa [actEnv_smul] using const_smul_mem_polyFam c (hx F hF)

lemma ActsPoly.lie {x y : P.KacMoodyAlgebra} (hx : ActsPoly x) (hy : ActsPoly y) :
    ActsPoly ⁅x, y⁆ := fun F hF ↦ by
  simpa [actEnv_lie] using sub_mem_polyFam (hx _ (hy F hF)) (hy _ (hx F hF))

lemma actsPoly_of_mem_nNeg {y : P.KacMoodyAlgebra} (hy : y ∈ nNeg P) : ActsPoly y :=
  fun F hF ↦ by
    simpa [actEnv_of_mem_nNeg _ hy] using
      map_mem_polyFam (LinearMap.mulLeft K (UniversalEnvelopingAlgebra.ι K ⟨y, hy⟩)) hF

lemma actEnv_h_pbw (Λ : Dual K H) (a : H) (s : NegRootIndex P →₀ ℕ) :
    actEnv P Λ (h P a) (pbwBasis (nNegBasis P) s) =
      (Λ a - negRootWt P s a) • pbwBasis (nNegBasis P) s := by
  rw [actEnv_apply, LinearEquiv.symm_apply_eq, map_smul]
  have := pbwBasisVerma_mem_weightSpace P Λ s a
  rw [pbwBasisVerma, Basis.map_apply] at this
  rw [this, LinearMap.sub_apply]

lemma actsPoly_h (a : H) : ActsPoly (h P a) := by
  refine ActsPoly.of_const fun u ↦ ?_
  set S : Submodule K 𝒰⁻ :=
    { carrier := {u | (fun Λ ↦ actEnv P Λ (h P a) u) ∈ polyFam P}
      add_mem' := fun hu hv ↦ by simpa using add_mem_polyFam hu hv
      zero_mem' := by simpa using zero_mem_polyFam
      smul_mem' := fun c u hu ↦ by simpa using const_smul_mem_polyFam c hu }
  have : ∀ s, pbwBasis (nNegBasis P) s ∈ S := fun s ↦ by
    change (fun Λ ↦ actEnv P Λ (h P a) (pbwBasis (nNegBasis P) s)) ∈ polyFam P
    simp_rw [actEnv_h_pbw, sub_smul]
    exact sub_mem_polyFam (smul_const_mem_polyFam (apply_mem_polyLE a) _)
      (const_mem_polyFam _)
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← (pbwBasis (nNegBasis P)).span_eq, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact this s
  have hu : u ∈ S := hS ▸ Submodule.mem_top
  exact hu

lemma actsPoly_e (i : ι) : ActsPoly (e P i) := by
  refine ActsPoly.of_const fun u ↦ ?_
  -- the set of `u` for which the claim holds contains `1` and is stable under left
  -- multiplication by `𝔫₋`
  set S : Submodule K 𝒰⁻ :=
    { carrier := {u | (fun Λ ↦ actEnv P Λ (e P i) u) ∈ polyFam P}
      add_mem' := fun hu hv ↦ by simpa using add_mem_polyFam hu hv
      zero_mem' := by simpa using zero_mem_polyFam
      smul_mem' := fun c u hu ↦ by simpa using const_smul_mem_polyFam c hu }
  have h1 : (1 : 𝒰⁻) ∈ S := by
    change (fun Λ ↦ actEnv P Λ (e P i) 1) ∈ polyFam P
    have : ∀ Λ, actEnv P Λ (e P i) 1 = 0 := fun Λ ↦ by
      rw [actEnv_apply, LinearEquiv.symm_apply_eq, map_zero, equivEnvNNeg_apply, map_one,
        one_smul, lie_e_hwv]
    simp_rw [this]
    exact zero_mem_polyFam
  have hmul : ∀ y : nNeg P, ∀ u ∈ S, UniversalEnvelopingAlgebra.ι K y * u ∈ S := by
    intro y u hu
    change (fun Λ ↦ actEnv P Λ (e P i) (UniversalEnvelopingAlgebra.ι K y * u)) ∈ polyFam P
    obtain ⟨y', hy', b, hb⟩ := exists_lie_e_eq_add_h P y.2 i
    have : ∀ Λ, actEnv P Λ (e P i) (UniversalEnvelopingAlgebra.ι K y * u) =
        UniversalEnvelopingAlgebra.ι K ⟨y', hy'⟩ * u + actEnv P Λ (h P b) u +
          UniversalEnvelopingAlgebra.ι K y * actEnv P Λ (e P i) u := fun Λ ↦ by
      have hyu : UniversalEnvelopingAlgebra.ι K y * u = actEnv P Λ (y : P.KacMoodyAlgebra) u :=
        (actEnv_of_mem_nNeg Λ y.2 u).symm
      rw [hyu, ← actEnv_of_mem_nNeg Λ y.2, ← actEnv_of_mem_nNeg Λ hy', ← actEnv_add,
        ← hb]
      simp only [actEnv_apply, LinearEquiv.apply_symm_apply, ← map_add, lie_lie]
      congr 1
      abel
    simp_rw [this]
    refine add_mem_polyFam (add_mem_polyFam (const_mem_polyFam _) ?_) ?_
    · exact actsPoly_h b _ (const_mem_polyFam u)
    · exact map_mem_polyFam (LinearMap.mulLeft K (UniversalEnvelopingAlgebra.ι K y)) hu
  have hall : ∀ a : 𝒰⁻, ∀ u ∈ S, a * u ∈ S := by
    intro a
    induction a using UniversalEnvelopingAlgebra.induction with
    | algebraMap r => intro u hu; rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
                      exact S.smul_mem r hu
    | ι y => exact hmul y
    | mul a b ha hb => intro u hu; rw [mul_assoc]; exact ha _ (hb u hu)
    | add a b ha hb => intro u hu; rw [add_mul]; exact S.add_mem (ha u hu) (hb u hu)
  have hu : u ∈ S := by simpa using hall u 1 h1
  exact hu

/-- **The action of `𝔤` on `M(λ) ≅ U(𝔫₋)` is polynomial in `λ`.** -/
theorem actsPoly (x : P.KacMoodyAlgebra) : ActsPoly x := by
  obtain ⟨y, a, z, rfl⟩ := exists_triangular P x
  refine ((actsPoly_of_mem_nNeg ⟨y, rfl⟩).add (actsPoly_h a)).add ?_
  induction z using FreeLieAlgebra.induction_on with
  | of j => simpa using actsPoly_e j
  | zero => simpa using actsPoly_of_mem_nNeg (P := P) (nNeg P).zero_mem
  | add y z hy hz => simpa using hy.add hz
  | smul c y hy => simpa using hy.smul c
  | lie y z hy hz => simpa using hy.lie hz

theorem actEnv_mem_polyFam (x : P.KacMoodyAlgebra) {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) :
    (fun Λ ↦ actEnv P Λ x (F Λ)) ∈ polyFam P :=
  actsPoly x F hF

/-! ### The Shapovalov pairing of polynomial families -/

section Pairing

variable (P) [FiniteDimensional K H] (S : A.Symmetrization)

variable (K H) in
/-- The polynomial functions on `𝔥*`. -/
abbrev polyFun : Subalgebra K (Dual K H → K) := (evalPoly K H).range

omit [CharZero K] [FiniteDimensional K H] in
lemma mem_polyFun_of_mem_polyLE {F : Dual K H → K} {d : ℕ} (hF : F ∈ polyLE K H d) :
    F ∈ polyFun K H := by
  obtain ⟨p, -, rfl⟩ := mem_polyLE.mp hF
  exact ⟨p, rfl⟩

omit [CharZero K] [FiniteDimensional K H] in
/-- A submodule containing a basis is everything. -/
lemma _root_.Module.Basis.mem_of_forall_mem {κ M : Type*} [AddCommGroup M] [Module K M]
    (b : Basis κ K M) {T : Submodule K M} (h : ∀ i, b i ∈ T) (x : M) : x ∈ T := by
  have : ⊤ ≤ T := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact this trivial

/-- The Shapovalov pairing `(F, G) ↦ (λ ↦ B_λ(F(λ) v_λ, G(λ) v_λ))` of two families in
`U(𝔫₋)`, as a bilinear map. -/
def pairBil : (Dual K H → 𝒰⁻) →ₗ[K] (Dual K H → 𝒰⁻) →ₗ[K] (Dual K H → K) :=
  LinearMap.mk₂ K
    (fun F G Λ ↦ contravariantForm P Λ (equivEnvNNeg P Λ (F Λ)) (equivEnvNNeg P Λ (G Λ)))
    (fun _ _ _ ↦ by ext; simp only [Pi.add_apply, map_add, LinearMap.add_apply])
    (fun _ _ _ ↦ by ext; simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul])
    (fun _ _ _ ↦ by ext; simp only [Pi.add_apply, map_add])
    (fun _ _ _ ↦ by ext; simp only [Pi.smul_apply, map_smul, smul_eq_mul])

omit [FiniteDimensional K H] in
lemma pairBil_apply (F G : Dual K H → 𝒰⁻) (Λ : Dual K H) :
    pairBil P F G Λ =
      contravariantForm P Λ (equivEnvNNeg P Λ (F Λ)) (equivEnvNNeg P Λ (G Λ)) := rfl

omit [FiniteDimensional K H] in
lemma pairBil_smul_fun_left (c : Dual K H → K) (F G : Dual K H → 𝒰⁻) :
    pairBil P (fun Λ ↦ c Λ • F Λ) G = c * pairBil P F G := by
  ext Λ; simp [pairBil_apply]

omit [FiniteDimensional K H] in
lemma pairBil_smul_fun_right (c : Dual K H → K) (F G : Dual K H → 𝒰⁻) :
    pairBil P F (fun Λ ↦ c Λ • G Λ) = c * pairBil P F G := by
  ext Λ; simp [pairBil_apply]

variable {P} in
/-- Constant families. -/
abbrev constFam : 𝒰⁻ →ₗ[K] (Dual K H → 𝒰⁻) := LinearMap.pi fun _ ↦ LinearMap.id

include S in
/-- The Shapovalov pairing of two fixed elements of `U(𝔫₋)` is a polynomial function of `λ`. -/
theorem pairBil_const_mem_polyFun (u w : 𝒰⁻) :
    pairBil P (constFam u) (constFam w) ∈ polyFun K H := by
  set Φ := (pairBil P).compl₁₂ (constFam (K := K) (H := H) (P := P))
    (constFam (K := K) (H := H) (P := P)) with hΦ
  have hs : ∀ s w, Φ (pbwBasis (nNegBasis P) s) w ∈ Subalgebra.toSubmodule (polyFun K H) := by
    intro s w
    refine (pbwBasis (nNegDualBasis P S)).mem_of_forall_mem
      (T := (Subalgebra.toSubmodule (polyFun K H)).comap (Φ (pbwBasis (nNegBasis P) s)))
      (fun t ↦ ?_) w
    exact mem_polyFun_of_mem_polyLE (contravariantForm_pbw_mem_polyLE P S s t)
  exact (pbwBasis (nNegBasis P)).mem_of_forall_mem
    (T := (Subalgebra.toSubmodule (polyFun K H)).comap (Φ.flip w)) (fun s ↦ hs s w) u

include S in
/-- **The Shapovalov pairing of polynomial families is polynomial**: for polynomial families
`F, G` in `U(𝔫₋)`, `λ ↦ B_λ(F(λ) v_λ, G(λ) v_λ)` is a polynomial function. -/
theorem pairBil_mem_polyFun {F G : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P)
    (hG : G ∈ polyFam P) : pairBil P F G ∈ polyFun K H := by
  have key : ∀ F ∈ polyFam P, ∀ w : 𝒰⁻, pairBil P F (constFam w) ∈ polyFun K H := by
    intro F hF w
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨p, u, rfl⟩ := hF
      have : (fun Λ ↦ evalPoly K H p Λ • u) = fun Λ ↦ evalPoly K H p Λ • constFam u Λ := rfl
      rw [this, pairBil_smul_fun_left]
      exact (polyFun K H).mul_mem ⟨p, rfl⟩ (pairBil_const_mem_polyFun P S u w)
    | zero => simp
    | add F F' _ _ hF hF' => simpa using (polyFun K H).add_mem hF hF'
    | smul a F _ hF => simpa using (polyFun K H).smul_mem hF a
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨q, w, rfl⟩ := hG
    have : (fun Λ ↦ evalPoly K H q Λ • w) = fun Λ ↦ evalPoly K H q Λ • constFam w Λ := rfl
    rw [this, pairBil_smul_fun_right]
    exact (polyFun K H).mul_mem ⟨q, rfl⟩ (key F hF w)
  | zero => simp
  | add G G' _ _ hG hG' => simpa using (polyFun K H).add_mem hG hG'
  | smul a G _ hG => simpa using (polyFun K H).smul_mem hG a

end Pairing

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
