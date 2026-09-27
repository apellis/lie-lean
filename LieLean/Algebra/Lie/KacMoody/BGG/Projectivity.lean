/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.VermaDecomposition
import LieLean.Algebra.Lie.KacMoody.BGG.Sl2
import LieLean.Algebra.Lie.KacMoody.VermaHom
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Criterion

/-!
# Verma modules are projective in the direction of a simple root

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a generalized Cartan matrix over a field `K` of
characteristic zero, `i` a simple index, and `λ` a weight with `⟨λ, αᵢ^∨⟩ = d ∈ ℕ`. As a module
over the `𝔰𝔩₂`-subalgebra `⟨eᵢ, fᵢ, αᵢ^∨⟩`, the Verma module `M(λ)` is `U(𝔲ᵢ⁻) ⊗ M_{𝔰𝔩₂}(d)` with
`U(𝔲ᵢ⁻)` locally finite, a projective object of the `𝔰𝔩₂`-category `𝒪`. We prove the consequence
that is needed for the BGG resolution:

**If `y ∈ M(λ)` is killed by `eᵢ` and has `αᵢ^∨`-weight `-(k + 1)`, `k ≥ 1`, then `y ∈ fᵢᵏ M(λ)`**
(`Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_eq_toEnd_f_pow`).

## Proof

Write `y = ∑ₐ fᵢᵃ uₐ v_λ` with `uₐ ∈ U(𝔲ᵢ⁻)` (`VermaModule.nilradDecomp`). As `eᵢ v_λ = 0` and
`U(𝔲ᵢ⁻)` is stable under `ad eᵢ`, `ad αᵢ^∨`, the conditions `eᵢ y = 0` and `αᵢ^∨ y = -(k+1) y`
become `(ad αᵢ^∨) uₐ = (2a - k - 1 - d) uₐ` and `(ad eᵢ) uₐ = -(a + 1)(a + 1 - k) u_{a+1}`, so
`(ad eᵢ)ᵏ u₀ = 0` while `u₀` has `ad αᵢ^∨`-weight `-(k + 1 + d)`. Since `ad eᵢ` and `ad fᵢ` are
locally nilpotent on `U(𝔤)`, the `𝔰𝔩₂`-lemma `IsSl2Triple.eq_zero_of_toEnd_e_pow_eq_zero` gives
`u₀ = 0`, i.e. `y ∈ fᵢ M(λ)`. If `y = fᵢʲ x` with `1 ≤ j < k`, then `eᵢ y = 0` forces
`fᵢ eᵢ x = j (k - j) x`, so `x ∈ fᵢ M(λ)`; by induction `y ∈ fᵢᵏ M(λ)`. The argument was
reconstructed by us; it is the Kac–Moody version of the `𝔰𝔩₂`-projectivity of Verma modules used
in [HumO] §4 (check) and [Kum] §2.? (check).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.mem_range_toEnd_f`: `y ∈ fᵢ M(λ)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_eq_toEnd_f_pow`: `y ∈ fᵢᵏ M(λ)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_mem_primitiveVectors_of_eq`: if moreover
  `y` is primitive of weight `ν`, then `y = fᵢᵏ x` with `x` primitive of weight `ν + k αᵢ`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.4 (check).
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002 (check).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (i : ι)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K
local notation "𝓤ᵢ" => UniversalEnvelopingAlgebra K (nilradNegSub P i)

/-! ### Commutators on `U(𝔲ᵢ⁻)` -/

/-- The commutator `u ↦ [x, u]` on `U(𝔲ᵢ⁻)`, for `x ∈ 𝔤` normalizing `𝔲ᵢ⁻`. -/
def adNilrad (x : P.KacMoodyAlgebra) (hx : ∀ y ∈ nilradNeg P i, ⁅x, y⁆ ∈ nilradNeg P i) :
    𝓤ᵢ →ₗ[K] 𝓤ᵢ :=
  (LinearEquiv.ofInjective (envNilrad P i).toLinearMap
    (envNilrad_injective P i)).symm.toLinearMap ∘ₗ LinearMap.codRestrict _
      ((LinearMap.mulLeft K (ιᵤ x) - LinearMap.mulRight K (ιᵤ x)) ∘ₗ
      (envNilrad P i).toLinearMap) (fun u ↦ by
        obtain ⟨v, hv⟩ := commutator_mem_range_envNilrad P i hx u
        exact ⟨v, hv⟩)

lemma envNilrad_adNilrad (x : P.KacMoodyAlgebra)
    (hx : ∀ y ∈ nilradNeg P i, ⁅x, y⁆ ∈ nilradNeg P i) (u : 𝓤ᵢ) :
    envNilrad P i (adNilrad P i x hx u) = ιᵤ x * envNilrad P i u - envNilrad P i u * ιᵤ x := by
  have := LinearEquiv.ofInjective_apply (envNilrad P i).toLinearMap (h := envNilrad_injective P i)
    ((LinearEquiv.ofInjective (envNilrad P i).toLinearMap (envNilrad_injective P i)).symm
      (LinearMap.codRestrict _ ((LinearMap.mulLeft K (ιᵤ x) - LinearMap.mulRight K (ιᵤ x)) ∘ₗ
      (envNilrad P i).toLinearMap) (fun u ↦ by
        obtain ⟨v, hv⟩ := commutator_mem_range_envNilrad P i hx u
        exact ⟨v, hv⟩) u))
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

/-- `ad eᵢ` on `U(𝔲ᵢ⁻)`. -/
abbrev adE : 𝓤ᵢ →ₗ[K] 𝓤ᵢ := adNilrad P i (e P i) fun _ hy ↦ lie_e_mem_nilradNeg i hy

/-- `ad αᵢ^∨` on `U(𝔲ᵢ⁻)`. -/
abbrev adH : 𝓤ᵢ →ₗ[K] 𝓤ᵢ :=
  adNilrad P i (h P (P.coroot i)) fun _ hy ↦ lie_h_mem_nilradNeg i _ hy

namespace VermaModule

variable {P} (Λ : Dual K H)

/-- `x (u v_λ) = [x, u] v_λ + u (x v_λ)`. -/
lemma lie_envNilrad_smul_hwv (x : P.KacMoodyAlgebra)
    (hx : ∀ y ∈ nilradNeg P i, ⁅x, y⁆ ∈ nilradNeg P i) (u : 𝓤ᵢ) :
    ⁅x, envNilrad P i u • hwv P Λ⁆ =
      envNilrad P i (adNilrad P i x hx u) • hwv P Λ + envNilrad P i u • ⁅x, hwv P Λ⁆ := by
  rw [envNilrad_adNilrad, lie_eq_smul, lie_eq_smul, ← mul_smul, ← mul_smul, sub_smul,
    sub_add_cancel]

lemma lie_e_envNilrad_smul_hwv (u : 𝓤ᵢ) :
    ⁅e P i, envNilrad P i u • hwv P Λ⁆ = envNilrad P i (adE P i u) • hwv P Λ := by
  rw [lie_envNilrad_smul_hwv, lie_e_hwv, smul_zero, add_zero]

lemma lie_h_envNilrad_smul_hwv (u : 𝓤ᵢ) :
    ⁅h P (P.coroot i), envNilrad P i u • hwv P Λ⁆ =
      envNilrad P i (adH P i u) • hwv P Λ + Λ (P.coroot i) • (envNilrad P i u • hwv P Λ) := by
  rw [lie_envNilrad_smul_hwv, lie_h_hwv, smul_comm]

/-! ### The action of `eᵢ`, `fᵢ`, `αᵢ^∨` in the decomposition `M(λ) = ⊕ₐ fᵢᵃ U(𝔲ᵢ⁻) v_λ` -/

lemma nilradDecomp_single' (n : ℕ) (u : 𝓤ᵢ) :
    nilradDecomp P i Λ (Finsupp.single n u) =
      (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) (envNilrad P i u • hwv P Λ) := by
  rw [nilradDecomp_single, toEnd_pow_apply]

/-- The operator on coefficient sequences corresponding to `fᵢ`: the shift. -/
def shiftF : (ℕ →₀ 𝓤ᵢ) →ₗ[K] (ℕ →₀ 𝓤ᵢ) := Finsupp.lmapDomain 𝓤ᵢ K (· + 1)

theorem lie_f_nilradDecomp (g : ℕ →₀ 𝓤ᵢ) :
    ⁅f P i, nilradDecomp P i Λ g⁆ = nilradDecomp P i Λ (shiftF i g) := by
  have : (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i)) ∘ₗ
      (nilradDecomp P i Λ).toLinearMap = (nilradDecomp P i Λ).toLinearMap ∘ₗ shiftF i := by
    refine Finsupp.lhom_ext fun n u ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, shiftF,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, nilradDecomp_single']
    rw [pow_succ', Module.End.mul_apply]
  exact LinearMap.congr_fun this g

variable (hA : A.IsGeneralizedCartan)

/-- The operator on coefficient sequences corresponding to `αᵢ^∨`. -/
def opH : (ℕ →₀ 𝓤ᵢ) →ₗ[K] (ℕ →₀ 𝓤ᵢ) :=
  Finsupp.lsum K fun n ↦ Finsupp.lsingle n ∘ₗ
    (adH P i + (Λ (P.coroot i) - 2 * n) • LinearMap.id)

/-- The operator on coefficient sequences corresponding to `eᵢ`. -/
def opE : (ℕ →₀ 𝓤ᵢ) →ₗ[K] (ℕ →₀ 𝓤ᵢ) :=
  Finsupp.lsum K fun n ↦ Finsupp.lsingle n ∘ₗ adE P i +
    (n : K) • (Finsupp.lsingle (n - 1) ∘ₗ
      (adH P i + (Λ (P.coroot i) - ((n - 1 : ℕ) : K)) • LinearMap.id))

include hA in
theorem lie_h_nilradDecomp (g : ℕ →₀ 𝓤ᵢ) :
    ⁅h P (P.coroot i), nilradDecomp P i Λ g⁆ = nilradDecomp P i Λ (opH i Λ g) := by
  have t := isSl2Triple P hA i
  have : (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (h P (P.coroot i))) ∘ₗ
      (nilradDecomp P i Λ).toLinearMap = (nilradDecomp P i Λ).toLinearMap ∘ₗ opH i Λ := by
    refine Finsupp.lhom_ext fun n u ↦ ?_
    have hR : opH i Λ (Finsupp.single n u) =
        Finsupp.single n (adH P i u + (Λ (P.coroot i) - 2 * n) • u) := by
      simp [opH]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hR,
      nilradDecomp_single', nilradDecomp_single', ← Module.End.mul_apply, t.toEnd_h_mul_f_pow,
      LinearMap.sub_apply, Module.End.mul_apply, toEnd_apply_apply, lie_h_envNilrad_smul_hwv,
      LinearMap.smul_apply, map_add (envNilrad P i), map_smul (envNilrad P i), add_smul,
      smul_assoc, map_add, map_add,
      map_smul (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) (Λ (P.coroot i)),
      map_smul (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n)
        (Λ (P.coroot i) - 2 * n)]
    module
  exact LinearMap.congr_fun this g

include hA in
theorem lie_e_nilradDecomp (g : ℕ →₀ 𝓤ᵢ) :
    ⁅e P i, nilradDecomp P i Λ g⁆ = nilradDecomp P i Λ (opE i Λ g) := by
  have t := isSl2Triple P hA i
  have : (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (e P i)) ∘ₗ
      (nilradDecomp P i Λ).toLinearMap = (nilradDecomp P i Λ).toLinearMap ∘ₗ opE i Λ := by
    refine Finsupp.lhom_ext fun n u ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, nilradDecomp_single',
      toEnd_apply_apply]
    rcases n with _ | m
    · have hR : opE i Λ (Finsupp.single 0 u) = Finsupp.single 0 (adE P i u) := by
        simp [opE]
      rw [hR, nilradDecomp_single', pow_zero, Module.End.one_apply, Module.End.one_apply,
        lie_e_envNilrad_smul_hwv]
    · have hR : opE i Λ (Finsupp.single (m + 1) u) = Finsupp.single (m + 1) (adE P i u) +
          ((m + 1 : ℕ) : K) • Finsupp.single m (adH P i u + (Λ (P.coroot i) - m) • u) := by
        simp [opE]
      have e1 : envNilrad P i (adH P i u + (Λ (P.coroot i) - m) • u) • hwv P Λ =
          envNilrad P i (adH P i u) • hwv P Λ +
            (Λ (P.coroot i) - m) • (envNilrad P i u • hwv P Λ) := by
        rw [map_add, map_smul, add_smul, smul_assoc]
      rw [hR, map_add, map_smul (nilradDecomp P i Λ) ((m + 1 : ℕ) : K), nilradDecomp_single',
        nilradDecomp_single', t.lie_e_pow_succ_toEnd_f, lie_e_envNilrad_smul_hwv,
        lie_h_envNilrad_smul_hwv, e1]
      generalize envNilrad P i (adH P i u) • hwv P Λ = a
      generalize envNilrad P i u • hwv P Λ = b
      generalize envNilrad P i (adE P i u) • hwv P Λ = c
      rw [map_sub, map_add, map_add, map_smul, map_smul, map_smul]
      push_cast
      module
  exact LinearMap.congr_fun this g

lemma opH_apply (g : ℕ →₀ 𝓤ᵢ) (n : ℕ) :
    opH i Λ g n = adH P i (g n) + (Λ (P.coroot i) - 2 * n) • g n := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp only [map_add, Finsupp.add_apply, hg, hg', smul_add]; abel
  | single a u =>
    simp only [opH, Finsupp.lsum_single, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.lsingle_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; rfl
    · simp

lemma opE_apply (g : ℕ →₀ 𝓤ᵢ) (n : ℕ) :
    opE i Λ g n = adE P i (g n) +
      ((n + 1 : ℕ) : K) • (adH P i (g (n + 1)) + (Λ (P.coroot i) - n) • g (n + 1)) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' =>
    simp only [map_add, Finsupp.add_apply, hg, hg', smul_add]
    abel
  | single a u =>
    simp only [opE, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h1 : a = n
    · subst h1
      simp only [ite_true, show ¬(a = a + 1) from by omega, ite_false, map_zero,
        smul_zero, add_zero]
      by_cases ha : a - 1 = a
      · have : a = 0 := by omega
        subst this; simp
      · simp [ha]
    · by_cases h2 : a = n + 1
      · subst h2
        simp only [h1, ite_false, map_zero, zero_add, show n + 1 - 1 = n from by omega, ite_true]
      · simp only [h1, h2, ite_false, map_zero, add_zero, smul_zero, zero_add]
        split_ifs with h3
        · omega
        · simp

end VermaModule

/-! ### The adjoint action on `U(𝔤)` -/

section AdModule

omit [DecidableEq ι] [CharZero K] in
/-- If a linear operator `D` on a ring satisfies the Leibniz rule, `Dᵖ a = 0` and `D^q b = 0`
imply `D^{p+q} (a b) = 0`. -/
lemma pow_apply_mul_eq_zero_of_leibniz {R : Type*} [Ring R] [Module K R] (D : Module.End K R)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) :
    ∀ (p q : ℕ) (a b : R), (D ^ p) a = 0 → (D ^ q) b = 0 → (D ^ (p + q)) (a * b) = 0 := by
  intro p q
  induction hn : p + q using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
  intro a b ha hb
  rcases p with _ | p
  · rw [pow_zero, Module.End.one_apply] at ha; rw [ha, zero_mul, map_zero]
  rcases q with _ | q
  · rw [pow_zero, Module.End.one_apply] at hb; rw [hb, mul_zero, map_zero]
  subst hn
  rw [show p + 1 + (q + 1) = (p + (q + 1)) + 1 by omega, pow_succ, Module.End.mul_apply, hD,
    map_add, ih (p + (q + 1)) (by omega) p (q + 1) rfl (D a) b
      (by rwa [← Module.End.mul_apply, ← pow_succ]) hb,
    show p + (q + 1) = (p + 1) + q by omega,
    ih (p + 1 + q) (by omega) (p + 1) q rfl a (D b) ha
      (by rwa [← Module.End.mul_apply, ← pow_succ]), add_zero]

/-- `U(𝔤)` as a `𝔤`-module under the adjoint action `x · u = [x, u] = x u - u x`. -/
abbrev adLieRingModule : LieRingModule P.KacMoodyAlgebra 𝓤 :=
  LieRingModule.compLieHom 𝓤 (UniversalEnvelopingAlgebra.ι K)

attribute [local instance] adLieRingModule

omit [CharZero K] in
lemma adLieModule : LieModule K P.KacMoodyAlgebra 𝓤 :=
  LieModule.compLieHom 𝓤 (UniversalEnvelopingAlgebra.ι K)

attribute [local instance] adLieModule

omit [CharZero K] in
lemma ad_lie_eq (x : P.KacMoodyAlgebra) (u : 𝓤) : ⁅x, u⁆ = ιᵤ x * u - u * ιᵤ x := rfl

omit [CharZero K] in
/-- If `ad x` is locally nilpotent on `𝔤`, it is locally nilpotent on `U(𝔤)`. -/
lemma exists_toEnd_pow_eq_zero_of_ad {x : P.KacMoodyAlgebra}
    (hx : ∀ y : P.KacMoodyAlgebra, ∃ n, (LieAlgebra.ad K _ x ^ n) y = 0) (u : 𝓤) :
    ∃ n, (toEnd K P.KacMoodyAlgebra 𝓤 x ^ n) u = 0 := by
  set D := toEnd K P.KacMoodyAlgebra 𝓤 x
  have hD : ∀ a b : 𝓤, D (a * b) = D a * b + a * D b := fun a b ↦ by
    simp only [D, toEnd_apply_apply, ad_lie_eq]; noncomm_ring
  induction u using UniversalEnvelopingAlgebra.induction with
  | algebraMap r =>
    exact ⟨1, by rw [pow_one, toEnd_apply_apply, ad_lie_eq, Algebra.commutes, sub_self]⟩
  | ι y =>
    obtain ⟨n, hn⟩ := hx y
    refine ⟨n, ?_⟩
    have : ∀ m (z : P.KacMoodyAlgebra), (D ^ m) (ιᵤ z) = ιᵤ ((LieAlgebra.ad K _ x ^ m) z) := by
      intro m
      induction m with
      | zero => intro z; rfl
      | succ m ih =>
        intro z
        rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply,
          LieAlgebra.ad_apply]
        simp only [D, toEnd_apply_apply, ad_lie_eq, ← Ring.lie_def, ← LieHom.map_lie]
    rw [this, hn, map_zero]
  | mul a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, pow_apply_mul_eq_zero_of_leibniz D hD p q a b hp hq⟩
  | add a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    refine ⟨p + q, ?_⟩
    have h1 : (D ^ (p + q)) a = 0 := by
      rw [add_comm, pow_add, Module.End.mul_apply, hp, map_zero]
    have h2 : (D ^ (p + q)) b = 0 := by
      rw [pow_add, Module.End.mul_apply, hq, map_zero]
    rw [map_add, h1, h2, add_zero]

lemma toEnd_envNilrad (x : P.KacMoodyAlgebra) (hx : ∀ y ∈ nilradNeg P i, ⁅x, y⁆ ∈ nilradNeg P i)
    (w : 𝓤ᵢ) (n : ℕ) :
    (toEnd K P.KacMoodyAlgebra 𝓤 x ^ n) (envNilrad P i w) =
      envNilrad P i ((adNilrad P i x hx ^ n) w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, toEnd_apply_apply, ad_lie_eq, ← envNilrad_adNilrad,
      ← Module.End.mul_apply, ← pow_succ']

end AdModule

namespace VermaModule

variable {P} (Λ : Dual K H) (hA : A.IsGeneralizedCartan)

include hA in
/-- **The key lemma**: let `⟨λ, αᵢ^∨⟩ = d ∈ ℕ` and let `y ∈ M(λ)` be killed by `eᵢ`, of
`αᵢ^∨`-weight `-(k + 1)` with `k ≥ 1`. Then `y ∈ fᵢ M(λ)`. -/
theorem mem_range_toEnd_f {d : ℕ} (hd : Λ (P.coroot i) = d) {y : VermaModule P Λ}
    (he : ⁅e P i, y⁆ = 0) {k : ℕ} (hk : 1 ≤ k) (hy : ⁅h P (P.coroot i), y⁆ = -((k : K) + 1) • y) :
    ∃ z, ⁅f P i, z⁆ = y := by
  set D := nilradDecomp P i Λ
  set g := D.symm y
  have hyg : D g = y := D.apply_symm_apply y
  have hH : opH i Λ g = (-((k : K) + 1)) • g := D.injective (by
    rw [← lie_h_nilradDecomp i Λ hA, hyg, hy, map_smul, hyg])
  have hE : opE i Λ g = 0 := D.injective (by rw [← lie_e_nilradDecomp i Λ hA, hyg, he, map_zero])
  have hHn : ∀ n : ℕ, adH P i (g n) = (-((k : K) + 1) - d + 2 * n) • g n := fun n ↦ by
    have := congrArg (· n) hH
    simp only [opH_apply, Finsupp.smul_apply, hd] at this
    rw [eq_sub_of_add_eq this]
    module
  have hEn : ∀ n : ℕ, adE P i (g n) = (-(((n : K) + 1) * ((n : K) + 1 - k))) • g (n + 1) := by
    intro n
    have := congrArg (· n) hE
    simp only [opE_apply, Finsupp.zero_apply, hd, hHn (n + 1)] at this
    rw [← sub_eq_zero, ← this]
    push_cast
    module
  -- `(ad eᵢ)ᵏ u₀ = 0`
  have hpow : ∀ j : ℕ, (adE P i ^ j) (g 0) =
      (∏ n ∈ Finset.range j, (-(((n : K) + 1) * ((n : K) + 1 - k)))) • g j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hEn, smul_smul, Finset.prod_range_succ]
  have hk0 : (adE P i ^ k) (g 0) = 0 := by
    rw [hpow, Finset.prod_eq_zero (i := k - 1) (Finset.mem_range.mpr (by omega)) (by
      push_cast [Nat.cast_sub hk]; ring), zero_smul]
  -- the `𝔰𝔩₂`-lemma in `U(𝔤)` gives `u₀ = 0`
  have hg0 : g 0 = 0 := by
    let _ := adLieRingModule P
    have _ := adLieModule P
    have hx := (isSl2Triple P hA i).eq_zero_of_toEnd_e_pow_eq_zero (M := 𝓤)
      (exists_toEnd_pow_eq_zero_of_ad P (exists_ad_e_pow_eq_zero P hA i))
      (exists_toEnd_pow_eq_zero_of_ad P (exists_ad_f_pow_eq_zero P hA i))
      (x := envNilrad P i (g 0)) (m := k + 1 + d) (k := k)
      (by
        have := toEnd_envNilrad P i (h P (P.coroot i))
          (fun _ hy ↦ lie_h_mem_nilradNeg i _ hy) (g 0) 1
        rw [pow_one, pow_one, toEnd_apply_apply] at this
        rw [this, hHn 0]
        simp only [map_smul]
        push_cast
        ring_nf)
      (by omega)
      (by rw [toEnd_envNilrad P i (e P i) (fun _ hy ↦ lie_e_mem_nilradNeg i hy), hk0, map_zero])
    exact envNilrad_injective P i (by rw [hx, map_zero])
  -- hence `y = fᵢ z`
  refine ⟨D (Finsupp.comapDomain (· + 1) g (Set.injOn_of_injective (add_left_injective 1))), ?_⟩
  rw [lie_f_nilradDecomp, ← hyg]
  congr 1
  ext n
  rcases n with _ | n
  · rw [hg0, shiftF, Finsupp.lmapDomain_apply, Finsupp.mapDomain_of_notMem_range]
    simp
  · rw [shiftF, Finsupp.lmapDomain_apply]
    exact (Finsupp.mapDomain_apply_of_injective (f := (· + 1)) (add_left_injective 1) _ n).trans
      (Finsupp.comapDomain_apply _ _ _ n)

omit [CharZero K] in
/-- `[h, fⁿ x] = fⁿ [h, x] - n αᵢ(h) fⁿ x`. -/
lemma lie_h_toEnd_f_pow (a : H) (n : ℕ) (x : VermaModule P Λ) :
    ⁅h P a, (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) x⁆ =
      (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) ⁅h P a, x⁆ -
        ((n : K) * P.root i a) • (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, toEnd_apply_apply,
      toEnd_apply_apply, leibniz_lie, ih, lie_h_f, neg_lie, smul_lie, lie_sub, lie_smul]
    push_cast
    module

lemma toEnd_f_pow_injective (n : ℕ) :
    Function.Injective (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) := by
  rw [Module.End.coe_pow]
  exact (toEnd_f_injective P Λ i).iterate n

include hA in
/-- **`M(λ)` is projective in the direction of `αᵢ`**: let `⟨λ, αᵢ^∨⟩ = d ∈ ℕ` and let `y ∈ M(λ)` be
killed by `eᵢ`, of `αᵢ^∨`-weight `-(k + 1)` with `k ≥ 1`. Then `y ∈ fᵢᵏ M(λ)`. (Reconstructed by
us, see the module docstring.) -/
theorem exists_eq_toEnd_f_pow {d : ℕ} (hd : Λ (P.coroot i) = d) {y : VermaModule P Λ}
    (he : ⁅e P i, y⁆ = 0) {k : ℕ} (hk : 1 ≤ k) (hy : ⁅h P (P.coroot i), y⁆ = -((k : K) + 1) • y) :
    ∃ x, (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ k) x = y := by
  have t := isSl2Triple P hA i
  set F := toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i)
  suffices ∀ j, 1 ≤ j → j ≤ k → ∃ x, (F ^ j) x = y from this k hk le_rfl
  intro j hj1 hjk
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · obtain ⟨z, hz⟩ := mem_range_toEnd_f i Λ hA hd he hk hy
      exact ⟨z, by rw [pow_one]; exact hz⟩
    obtain ⟨x, rfl⟩ := ih hj0 (by omega)
    -- the weight of `x`
    have hxh : ⁅h P (P.coroot i), x⁆ = (2 * (j : K) - k - 1) • x := by
      apply toEnd_f_pow_injective i Λ j
      have := lie_h_toEnd_f_pow i Λ (P.coroot i) j x
      rw [hy, root_coroot_self P hA, eq_sub_iff_add_eq] at this
      rw [map_smul, ← this]
      module
    -- `f e x = j (k - j) x`
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hfe : ⁅f P i, ⁅e P i, x⁆⁆ = (((j' : K) + 1) * (k - j' - 1)) • x := by
      apply toEnd_f_pow_injective i Λ j'
      have := t.lie_e_pow_succ_toEnd_f (K := K) j' x
      rw [he, hxh, pow_succ, Module.End.mul_apply, toEnd_apply_apply, ← sub_smul, map_smul,
        eq_comm, add_eq_zero_iff_eq_neg] at this
      rw [map_smul, this]
      push_cast
      module
    have hc : ((j' : K) + 1) * (k - j' - 1) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero j') ?_
      have : ((k : ℕ) : K) - j' - 1 = ((k - j' - 1 : ℕ) : K) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this, Nat.cast_ne_zero]
      omega
    refine ⟨(((j' : K) + 1) * (k - j' - 1))⁻¹ • ⁅e P i, x⁆, ?_⟩
    rw [pow_succ, Module.End.mul_apply, map_smul, toEnd_apply_apply, hfe, smul_smul,
      inv_mul_cancel₀ hc, one_smul]

include hA in
/-- If `y ∈ M(λ)` is a primitive vector of weight `ν` with `⟨ν, αᵢ^∨⟩ = -(k + 1)`, `k ≥ 1`, and
`⟨λ, αᵢ^∨⟩ ∈ ℕ`, then `y = fᵢᵏ x` for a primitive vector `x` of weight `ν + k αᵢ`. -/
theorem exists_mem_primitiveVectors_of_mem {d : ℕ} (hd : Λ (P.coroot i) = d) {ν : Dual K H}
    {k : ℕ} (hk : 1 ≤ k) (hν : ν (P.coroot i) = -((k : K) + 1)) {y : VermaModule P Λ}
    (hy : y ∈ primitiveVectors P (VermaModule P Λ) ν) :
    ∃ x ∈ primitiveVectors P (VermaModule P Λ) (ν + k • P.root i),
      (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ k) x = y := by
  have t := isSl2Triple P hA i
  rw [mem_primitiveVectors] at hy
  obtain ⟨x, rfl⟩ := exists_eq_toEnd_f_pow i Λ hA hd (hy.2 i) hk (by rw [hy.1, hν])
  have hxw : ∀ a, ⁅h P a, x⁆ = (ν + k • P.root i) a • x := fun a ↦ by
    apply toEnd_f_pow_injective i Λ k
    have := lie_h_toEnd_f_pow i Λ a k x
    rw [hy.1 a] at this
    rw [map_smul, LinearMap.add_apply, LinearMap.smul_apply, add_smul]
    rw [eq_sub_iff_add_eq] at this
    rw [← this, nsmul_eq_mul]
  refine ⟨x, mem_primitiveVectors.mpr ⟨hxw, fun l ↦ ?_⟩, rfl⟩
  apply toEnd_f_pow_injective i Λ k
  rw [map_zero]
  by_cases hl : l = i
  · subst hl
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have := t.lie_e_pow_succ_toEnd_f (K := K) k' x
    rw [hy.2 l, hxw, ← sub_smul, map_smul] at this
    have hz : ν (P.coroot l) + ((k' + 1) • P.root l) (P.coroot l) - k' = 0 := by
      rw [LinearMap.smul_apply, hν, root_coroot_self P hA, nsmul_eq_mul]
      push_cast
      ring
    rw [LinearMap.add_apply, hz, zero_smul, smul_zero, add_zero] at this
    exact this.symm
  · rw [← lie_toEnd_pow_of_lie_eq_zero (lie_e_f_of_ne P hl) k x, hy.2 l]

lemma toEnd_f_pow_mem_primitiveVectors_of_mem {ν : Dual K H} {n : ℕ}
    (hn : ν (P.coroot i) + 1 = n) {x : VermaModule P Λ}
    (hx : x ∈ primitiveVectors P (VermaModule P Λ) ν) (hA : A.IsGeneralizedCartan) :
    (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n) x ∈
      primitiveVectors P (VermaModule P Λ) (ν - n • P.root i) := by
  have t := isSl2Triple P hA i
  rw [mem_primitiveVectors] at hx ⊢
  refine ⟨fun a ↦ ?_, fun l ↦ ?_⟩
  · rw [lie_h_toEnd_f_pow, hx.1 a, map_smul, ← sub_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, nsmul_eq_mul]
  · by_cases hl : l = i
    · subst hl
      rcases n with _ | n
      · simp [hx.2 l]
      · rw [t.lie_e_pow_succ_toEnd_f, hx.2 l, map_zero, zero_add, hx.1, ← sub_smul, map_smul]
        have : ν (P.coroot l) - n = 0 := by push_cast at hn; linear_combination hn
        rw [this, zero_smul, smul_zero]
    · rw [lie_toEnd_pow_of_lie_eq_zero (lie_e_f_of_ne P hl), hx.2 l, map_zero]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
