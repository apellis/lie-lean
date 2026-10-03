/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Families
import LieLean.Algebra.Lie.KacMoody.Jantzen.OrderFormula

/-!
# The Jantzen filtration of a Verma module

Let `A` be symmetrizable and `𝔤 = 𝔤(A)` over a field `K` of characteristic zero. Fix `λ₀, δ ∈ 𝔥*`
and consider the line `λ(t) = λ₀ + t δ`. All Verma modules `M(λ(t))` have the same underlying
space `U(𝔫₋)` (`u ↦ u v_{λ(t)}`), and the action of `𝔤` and the Shapovalov forms `B_{λ(t)}` depend
polynomially on `t` (`KacMoody/KacKazhdan/Families.lean`). The **Jantzen filtration**
([HumO] §5.3, §5.7, citing Jantzen, *Moduln mit einem höchsten Gewicht*, 5.3) is
`M(λ₀)^i = {f(0) v_{λ₀} | f a polynomial family in U(𝔫₋) with B_{λ(t)}(f(t) v_{λ(t)}, w v_{λ(t)})
divisible by tⁱ for all w ∈ U(𝔫₋)}`.
It is a decreasing filtration of `M(λ₀)` by submodules with `M(λ₀)^0 = M(λ₀)` and
`M(λ₀)^1 = M'(λ₀)`, the maximal proper submodule. (The usual definition works over the local ring
`K[t]_{(t)}`; with polynomial families one gets the same spaces, and the order formula of
`KacMoody/Jantzen/Weight.lean` relates them to the Shapovalov determinant.) The Jantzen sum
formula is proved in `KacMoody/Jantzen/SumFormula.lean`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.lineFam`: polynomial families `t ↦ ∑ tⁿ uₙ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.DvdXPow`: a function `K → K` of the form
  `t ↦ tⁱ q(t)` with `q` a polynomial.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.jantzenEnv`: the `i`-th Jantzen space, in
  `U(𝔫₋)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.jantzen`: the Jantzen filtration `M(λ₀)^i`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.jantzen_antitone`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.jantzen_zero`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.jantzen_one`: `M(λ₀)^{i+1} ⊆ M(λ₀)^i`,
  `M(λ₀)^0 = M(λ₀)` and `M(λ₀)^1 = M'(λ₀)`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.3, §5.7.
-/

open Module LieModule Module.Dual Polynomial UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace VermaModule

section DvdXPow

variable (K : Type*) [Field K]

/-- A function `K → K` of the form `t ↦ tⁱ q(t)` with `q` a polynomial. -/
def DvdXPow (i : ℕ) (f : K → K) : Prop := ∃ q : K[X], ∀ t, f t = t ^ i * q.eval t

namespace DvdXPow

variable {K} {i : ℕ} {f g : K → K}

lemma zero (i : ℕ) : DvdXPow K i (fun _ ↦ 0) := ⟨0, fun t ↦ by simp⟩

lemma add (hf : DvdXPow K i f) (hg : DvdXPow K i g) : DvdXPow K i (fun t ↦ f t + g t) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun t ↦ by simp [hp, hq, mul_add]⟩

lemma const_mul (c : K) (hf : DvdXPow K i f) : DvdXPow K i (fun t ↦ c * f t) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨C c * p, fun t ↦ by simp [hp]; ring⟩

lemma pow_mul (n : ℕ) (hf : DvdXPow K i f) : DvdXPow K i (fun t ↦ t ^ n * f t) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨X ^ n * p, fun t ↦ by simp [hp]; ring⟩

lemma of_succ (hf : DvdXPow K (i + 1) f) : DvdXPow K i f := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨X * p, fun t ↦ by simp [hp]; ring⟩

lemma eval_zero (hf : DvdXPow K (i + 1) f) : f 0 = 0 := by
  obtain ⟨p, hp⟩ := hf
  simp [hp]

lemma sum {κ : Type*} (s : Finset κ) {f : κ → K → K} (hf : ∀ k ∈ s, DvdXPow K i (f k)) :
    DvdXPow K i (fun t ↦ ∑ k ∈ s, f k t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (K := K) i
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))

end DvdXPow

end DvdXPow

end VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝒰⁻" => UniversalEnvelopingAlgebra K (nNeg P)

namespace VermaModule

/-! ### Polynomial families along a line -/


omit [CharZero K] in
/-- A polynomial function on `𝔥*`, restricted to a line, is a polynomial function of `t`. -/
lemma exists_eval_eq_evalPoly (Λ₀ δ : Dual K H) (p : MvPolynomial (PolyIdx K H) K) :
    ∃ q : K[X], ∀ t : K, q.eval t = evalPoly K H p (Λ₀ + t • δ) := by
  refine ⟨MvPolynomial.aeval (fun j ↦ C (Λ₀ (Module.Free.chooseBasis K H j)) +
    C (δ (Module.Free.chooseBasis K H j)) * X) p, fun t ↦ ?_⟩
  have := congrArg (fun φ ↦ φ p) (MvPolynomial.comp_aeval (R := K)
    (f := fun j ↦ C (Λ₀ (Module.Free.chooseBasis K H j)) +
      C (δ (Module.Free.chooseBasis K H j)) * X) (Polynomial.aeval t))
  simp only [AlgHom.comp_apply] at this
  rw [← coe_aeval_eq_eval, this, evalPoly_apply]
  refine congrArg (fun g ↦ MvPolynomial.aeval g p) (funext fun j ↦ ?_)
  simp only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

omit [CharZero K] in
lemma exists_eval_eq_of_mem_polyFun (Λ₀ δ : Dual K H) {F : Dual K H → K}
    (hF : F ∈ polyFun K H) : ∃ q : K[X], ∀ t : K, q.eval t = F (Λ₀ + t • δ) := by
  obtain ⟨p, rfl⟩ := hF
  exact exists_eval_eq_evalPoly Λ₀ δ p

/-- Polynomial families `t ↦ ∑ₙ tⁿ uₙ` in `U(𝔫₋)`. -/
def lineFam : Submodule K (K → 𝒰⁻) :=
  Submodule.span K {f | ∃ (n : ℕ) (u : 𝒰⁻), f = fun t ↦ t ^ n • u}

variable {P}

omit [CharZero K] in
lemma zero_mem_lineFam : (fun _ : K ↦ (0 : 𝒰⁻)) ∈ lineFam P := (lineFam P).zero_mem

omit [CharZero K] in
lemma add_mem_lineFam {f g : K → 𝒰⁻} (hf : f ∈ lineFam P) (hg : g ∈ lineFam P) :
    (fun t ↦ f t + g t) ∈ lineFam P := (lineFam P).add_mem hf hg

omit [CharZero K] in
lemma const_smul_mem_lineFam (a : K) {f : K → 𝒰⁻} (hf : f ∈ lineFam P) :
    (fun t ↦ a • f t) ∈ lineFam P := (lineFam P).smul_mem a hf

omit [CharZero K] in
lemma pow_smul_mem_lineFam (n : ℕ) (u : 𝒰⁻) : (fun t : K ↦ t ^ n • u) ∈ lineFam P :=
  Submodule.subset_span ⟨n, u, rfl⟩

omit [CharZero K] in
lemma const_mem_lineFam (u : 𝒰⁻) : (fun _ : K ↦ u) ∈ lineFam P := by
  simpa using pow_smul_mem_lineFam (P := P) 0 u

omit [CharZero K] in
lemma polyEval_smul_mem_lineFam (q : K[X]) (u : 𝒰⁻) :
    (fun t : K ↦ q.eval t • u) ∈ lineFam P := by
  have : (fun t : K ↦ q.eval t • u) =
      ∑ n ∈ Finset.range (q.natDegree + 1), q.coeff n • fun t : K ↦ t ^ n • u := by
    ext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_smul]
    rw [eval_eq_sum_range, Finset.sum_smul]
  rw [this]
  exact Submodule.sum_mem _ fun n _ ↦ Submodule.smul_mem _ _ (pow_smul_mem_lineFam n u)

omit [CharZero K] in
/-- A polynomial family on `𝔥*`, restricted to a line, is a polynomial family in `t`. -/
lemma lineFam_of_mem_polyFam (Λ₀ δ : Dual K H) {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) :
    (fun t : K ↦ F (Λ₀ + t • δ)) ∈ lineFam P := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, u, rfl⟩ := hF
    obtain ⟨q, hq⟩ := exists_eval_eq_evalPoly Λ₀ δ p
    simp_rw [← hq]
    exact polyEval_smul_mem_lineFam q u
  | zero => exact (lineFam P).zero_mem
  | add F G _ _ hF hG => exact (lineFam P).add_mem hF hG
  | smul a F _ hF => exact (lineFam P).smul_mem a hF

omit [CharZero K] in
lemma pow_smul_mem_lineFam' (n : ℕ) {f : K → 𝒰⁻} (hf : f ∈ lineFam P) :
    (fun t ↦ t ^ n • f t) ∈ lineFam P := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, u, rfl⟩ := hf
    simpa [smul_smul, ← pow_add] using pow_smul_mem_lineFam (P := P) (n + k) u
  | zero => simpa using zero_mem_lineFam
  | add f g _ _ hf hg => simpa [smul_add] using add_mem_lineFam hf hg
  | smul a f _ hf => simpa [smul_comm (_ ^ n) a] using const_smul_mem_lineFam a hf

/-- The action of `x ∈ 𝔤` on a polynomial family along a line is a polynomial family. -/
lemma actEnv_mem_lineFam (Λ₀ δ : Dual K H) (x : P.KacMoodyAlgebra) {f : K → 𝒰⁻}
    (hf : f ∈ lineFam P) : (fun t ↦ actEnv P (Λ₀ + t • δ) x (f t)) ∈ lineFam P := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, u, rfl⟩ := hf
    simp only [map_smul]
    exact pow_smul_mem_lineFam' n
      (lineFam_of_mem_polyFam Λ₀ δ (actEnv_mem_polyFam x (const_mem_polyFam u)))
  | zero => simpa using zero_mem_lineFam
  | add f g _ _ hf hg => simpa using add_mem_lineFam hf hg
  | smul a f _ hf => simpa using const_smul_mem_lineFam a hf

/-! ### The Shapovalov pairing along a line -/

variable (P) in
/-- The Shapovalov pairing `B_Λ(u v_Λ, w v_Λ)` of `u, w ∈ U(𝔫₋)`. -/
def pairAt (Λ : Dual K H) (u w : 𝒰⁻) : K :=
  contravariantForm P Λ (equivEnvNNeg P Λ u) (equivEnvNNeg P Λ w)

lemma pairAt_add_left (Λ : Dual K H) (u u' w : 𝒰⁻) :
    pairAt P Λ (u + u') w = pairAt P Λ u w + pairAt P Λ u' w := by
  simp [pairAt, add_smul]

lemma pairAt_smul_left (Λ : Dual K H) (c : K) (u w : 𝒰⁻) :
    pairAt P Λ (c • u) w = c * pairAt P Λ u w := by
  simp [pairAt]

lemma pairAt_add_right (Λ : Dual K H) (u w w' : 𝒰⁻) :
    pairAt P Λ u (w + w') = pairAt P Λ u w + pairAt P Λ u w' := by
  simp [pairAt, add_smul]

lemma pairAt_smul_right (Λ : Dual K H) (c : K) (u w : 𝒰⁻) :
    pairAt P Λ u (c • w) = c * pairAt P Λ u w := by
  simp [pairAt]

/-- Contravariance of the Shapovalov pairing on `U(𝔫₋)`. -/
lemma pairAt_actEnv (Λ : Dual K H) (x : P.KacMoodyAlgebra) (u w : 𝒰⁻) :
    pairAt P Λ (actEnv P Λ x u) w = pairAt P Λ u (actEnv P Λ (transpose P x) w) := by
  simp only [pairAt, equivEnvNNeg_actEnv, contravariantForm_lie_left]

variable [FiniteDimensional K H] (S : A.Symmetrization)

include S in
lemma exists_eval_eq_pairAt (Λ₀ δ : Dual K H) (u w : 𝒰⁻) :
    ∃ q : K[X], ∀ t : K, q.eval t = pairAt P (Λ₀ + t • δ) u w :=
  exists_eval_eq_of_mem_polyFun Λ₀ δ (pairBil_const_mem_polyFun P S u w)

include S in
/-- The Shapovalov pairing of a polynomial family along a line with a fixed vector is a polynomial
function of `t`. -/
lemma dvdXPow_zero_pairAt (Λ₀ δ : Dual K H) {f : K → 𝒰⁻} (hf : f ∈ lineFam P) (w : 𝒰⁻) :
    DvdXPow K 0 (fun t ↦ pairAt P (Λ₀ + t • δ) (f t) w) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, u, rfl⟩ := hf
    obtain ⟨q, hq⟩ := exists_eval_eq_pairAt S Λ₀ δ u w
    exact ⟨X ^ n * q, fun t ↦ by simp [pairAt_smul_left, hq]⟩
  | zero => simpa [pairAt] using DvdXPow.zero (K := K) 0
  | add f g _ _ hf hg =>
    simpa [pairAt_add_left] using hf.add hg
  | smul a f _ hf =>
    simpa [pairAt_smul_left] using hf.const_mul a

/-! ### The Jantzen filtration -/

variable (P) (Λ₀ δ : Dual K H)

/-- The `i`-th Jantzen space in `U(𝔫₋)`: the values `f(0)` of polynomial families `f` along the
line `λ(t) = λ₀ + t δ` such that `B_{λ(t)}(f(t) v_{λ(t)}, w v_{λ(t)})` is divisible by `tⁱ` for all
`w ∈ U(𝔫₋)`. -/
def jantzenEnv (i : ℕ) : Submodule K 𝒰⁻ where
  carrier := {u | ∃ f ∈ lineFam P, f 0 = u ∧
    ∀ w, DvdXPow K i (fun t ↦ pairAt P (Λ₀ + t • δ) (f t) w)}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl, hfw⟩ ⟨g, hg, rfl, hgw⟩
    refine ⟨f + g, (lineFam P).add_mem hf hg, rfl, fun w ↦ ?_⟩
    simpa [pairAt_add_left] using (hfw w).add (hgw w)
  zero_mem' := ⟨0, (lineFam P).zero_mem, rfl, fun w ↦ by
    simpa [pairAt] using DvdXPow.zero (K := K) i⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl, hfw⟩
    refine ⟨c • f, (lineFam P).smul_mem c hf, rfl, fun w ↦ ?_⟩
    simpa [pairAt_smul_left] using (hfw w).const_mul c

variable {P Λ₀ δ}

omit [FiniteDimensional K H] in
lemma pairAt_zero_smul (u w : 𝒰⁻) : pairAt P (Λ₀ + (0 : K) • δ) u w = pairAt P Λ₀ u w := by
  rw [zero_smul, add_zero]

omit [FiniteDimensional K H] in
lemma actEnv_zero_smul (x : P.KacMoodyAlgebra) :
    actEnv P (Λ₀ + (0 : K) • δ) x = actEnv P Λ₀ x := by
  rw [zero_smul, add_zero]

omit [FiniteDimensional K H] in
/-- The Jantzen spaces are stable under the action of `𝔤`. -/
lemma actEnv_mem_jantzenEnv {i : ℕ} (x : P.KacMoodyAlgebra) {u : 𝒰⁻}
    (hu : u ∈ jantzenEnv P Λ₀ δ i) : actEnv P Λ₀ x u ∈ jantzenEnv P Λ₀ δ i := by
  obtain ⟨f, hf, rfl, hfw⟩ := hu
  refine ⟨fun t ↦ actEnv P (Λ₀ + t • δ) x (f t), actEnv_mem_lineFam Λ₀ δ x hf,
    by simp only [actEnv_zero_smul], fun w ↦ ?_⟩
  simp_rw [pairAt_actEnv]
  -- the family `t ↦ σ(x) w` in `M(λ(t))` is a polynomial family
  have hg := actEnv_mem_lineFam Λ₀ δ (transpose P x) (const_mem_lineFam (P := P) w)
  -- divisibility against polynomial families
  suffices ∀ g ∈ lineFam P, DvdXPow K i (fun t ↦ pairAt P (Λ₀ + t • δ) (f t) (g t)) from
    this _ hg
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, w', rfl⟩ := hg
    simpa [pairAt_smul_right] using (hfw w').pow_mul n
  | zero => simpa [pairAt] using DvdXPow.zero (K := K) i
  | add g g' _ _ hg hg' => simpa [pairAt_add_right] using hg.add hg'
  | smul a g _ hg => simpa [pairAt_smul_right] using hg.const_mul a

variable (P Λ₀ δ)

/-- **The Jantzen filtration** `M(λ₀)^i` of the Verma module `M(λ₀)` along the line
`λ(t) = λ₀ + t δ` ([HumO] §5.3, §5.7, there with `δ = ρ`). -/
def jantzen (i : ℕ) : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ₀) where
  toSubmodule := (jantzenEnv P Λ₀ δ i).map (equivEnvNNeg P Λ₀).toLinearMap
  lie_mem := by
    rintro x _ ⟨u, hu, rfl⟩
    refine ⟨actEnv P Λ₀ x u, actEnv_mem_jantzenEnv x hu, ?_⟩
    change equivEnvNNeg P Λ₀ (actEnv P Λ₀ x u) = ⁅x, equivEnvNNeg P Λ₀ u⁆
    exact equivEnvNNeg_actEnv Λ₀ x u

omit [FiniteDimensional K H] in
lemma mem_jantzen {i : ℕ} {m : VermaModule P Λ₀} :
    m ∈ jantzen P Λ₀ δ i ↔ (equivEnvNNeg P Λ₀).symm m ∈ jantzenEnv P Λ₀ δ i := by
  change m ∈ (jantzenEnv P Λ₀ δ i).map (equivEnvNNeg P Λ₀).toLinearMap ↔ _
  rw [Submodule.mem_map_equiv]

omit [FiniteDimensional K H] in
/-- The Jantzen filtration is decreasing. -/
theorem jantzen_antitone (i : ℕ) : jantzen P Λ₀ δ (i + 1) ≤ jantzen P Λ₀ δ i := by
  intro m hm
  rw [mem_jantzen] at hm ⊢
  obtain ⟨f, hf, hf0, hfw⟩ := hm
  exact ⟨f, hf, hf0, fun w ↦ (hfw w).of_succ⟩

include S in
/-- `M(λ₀)^0 = M(λ₀)`. -/
theorem jantzen_zero : jantzen P Λ₀ δ 0 = ⊤ := by
  refine eq_top_iff.mpr fun m _ ↦ (mem_jantzen P Λ₀ δ).mpr ?_
  exact ⟨_, const_mem_lineFam _, rfl, fun w ↦ dvdXPow_zero_pairAt S Λ₀ δ (const_mem_lineFam _) w⟩

include S in
/-- **`M(λ₀)^1` is the maximal proper submodule `M'(λ₀)`** ([HumO] §5.3). -/
theorem jantzen_one : jantzen P Λ₀ δ 1 = maxSubmodule P Λ₀ := by
  ext m
  rw [mem_jantzen]
  constructor
  · rintro ⟨f, -, hf0, hfw⟩
    rw [mem_maxSubmodule_iff]
    intro w
    obtain ⟨w, rfl⟩ := (equivEnvNNeg P Λ₀).surjective w
    have h0 := (hfw w).eval_zero
    have : pairAt P Λ₀ (f 0) w = 0 := by
      have e : pairAt P (Λ₀ + (0 : K) • δ) (f 0) w = pairAt P Λ₀ (f 0) w := pairAt_zero_smul _ _
      exact e ▸ h0
    rw [hf0, pairAt, LinearEquiv.apply_symm_apply] at this
    exact this
  · intro hm
    refine ⟨_, const_mem_lineFam ((equivEnvNNeg P Λ₀).symm m), rfl, fun w ↦ ?_⟩
    obtain ⟨q, hq⟩ := exists_eval_eq_pairAt S Λ₀ δ ((equivEnvNNeg P Λ₀).symm m) w
    have hq0 : q.eval 0 = 0 := by
      rw [hq, pairAt_zero_smul, pairAt, LinearEquiv.apply_symm_apply]
      exact (mem_maxSubmodule_iff P Λ₀ m).mp hm _
    obtain ⟨q', hq'⟩ : X ∣ q := by rwa [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact ⟨q', fun t ↦ by beta_reduce; rw [← hq, hq']; simp⟩

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
