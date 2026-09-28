/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaHomSingularReduction

/-!
# Singular-wall projectivity and finite-type Verma Hom uniqueness

Reconstructed extension of `BGG/Sl2`, `BGG/Projectivity`, and `BGG/Uniqueness`.
The key endpoint is injectivity of `e^k` on weight `-m` for `k ≤ m`, not just `k < m`.
This permits the target highest-weight pairing `-1` in rank-one projectivity.
Classical context: Humphreys, *Representations of semisimple Lie algebras in the BGG
category O*, Chapter 4. The printed proof has not been inspected for this extension.
-/

open LieModule Module Polynomial

namespace IsSl2Triple

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] {h e f : L} (t : IsSl2Triple h e f)
include t
variable [CharZero K]

omit t in
/-- `n (n + 2) ≠ c (c + 2)` in `K` if `c = 2j - m` with `j < k ≤ m ≤ n`. -/
lemma wall_cast_mul_ne {n m j k : ℕ} (hj : j < k) (hkm : k ≤ m) (hmn : m ≤ n) :
    (-(m : K) + 2 * j) * (-(m : K) + 2 * j + 2) - n * (n + 2) ≠ 0 := by
  have : ((-(m : ℤ) + 2 * j) * (-(m : ℤ) + 2 * j + 2) - n * (n + 2) : ℤ) ≠ 0 := by
    have h1 : (-(m : ℤ) + 2 * j + 1) - (n + 1) < 0 := by omega
    have h2 : 0 < (-(m : ℤ) + 2 * j + 1) + (n + 1) := by omega
    nlinarith
  exact_mod_cast this

/-- **`eᵏ` is injective on the weight space `-m` for `k ≤ m`** (finite-dimensional case). -/
theorem wall_eq_zero_of_toEnd_e_pow_eq_zero_of_finiteDimensional [FiniteDimensional K M] {x : M}
    {m k : ℕ} (hx : ⁅h, x⁆ = -(m : K) • x) (hkm : k ≤ m) (hk : (toEnd K L M e ^ k) x = 0) :
    x = 0 := by
  classical
  set Ω := casimir K M h e f
  obtain ⟨d, hd⟩ := t.isNilpotent_toEnd_e (K := K) (M := M)
  obtain ⟨N, hN'⟩ := t.isNilpotent_toEnd_f (K := K) (M := M)
  have hN : toEnd K L M f ^ (N + 1) = 0 := by rw [pow_succ, hN', zero_mul]
  -- `x` is killed by `P₁(Ω)`
  set c : ℕ → K := fun j ↦ -(m : K) + 2 * j
  set P₁ := ∏ j ∈ Finset.range k, (X - C (c j * (c j + 2)))
  have h₁ : aeval Ω P₁ x = 0 := by
    rw [← t.four_pow_smul_pow_f_pow_e hx k, hk, map_zero, smul_zero]
  -- `x` is killed by `Q(Ω)ᵈ`
  set g : ℕ → K[X] := fun n ↦ (X - C ((n : K) * (n + 2))) ^ d
  set s := Finset.range (N + 1)
  have h₂ : aeval Ω (∏ n ∈ s, g n) x = 0 := by
    have := t.aeval_casimir_pow_apply_eq_zero hN d (v := x) (by rw [hd, LinearMap.zero_apply])
    rwa [← map_pow, ← Finset.prod_pow] at this
  -- split off the factors with `n ≥ m`
  set A := ∏ n ∈ s.filter (· < m), g n
  set B := ∏ n ∈ s.filter (fun n ↦ ¬ n < m), g n
  have hAB : ∏ n ∈ s, g n = A * B := (Finset.prod_filter_mul_prod_filter_not s (· < m) g).symm
  have hcop : IsCoprime P₁ B := by
    refine IsCoprime.prod_right fun n hn ↦ IsCoprime.pow_right (IsCoprime.prod_left fun j hj ↦ ?_)
    rw [Finset.mem_filter, not_lt] at hn
    refine isCoprime_X_sub_C_of_isUnit_sub (Ne.isUnit ?_)
    exact wall_cast_mul_ne (Finset.mem_range.mp hj) hkm hn.2
  have hAx : aeval Ω A x = 0 := by
    have hker := Polynomial.disjoint_ker_aeval_of_isCoprime Ω hcop
    refine Submodule.disjoint_def.mp hker _ ?_ ?_
    · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
        Module.End.mul_apply, h₁, map_zero]
    · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← map_mul, mul_comm, ← hAB, h₂]
  -- hence `x` lies in the sum of the eigenspaces of `h` for weights `> -m`
  set S := ⨆ (c : K) (_ : c ≠ -(m : K)), (toEnd K L M h).eigenspace c
  have hS : ∀ n < m, LinearMap.ker (aeval Ω (g n)) ≤ S := by
    intro n hn v hv
    have hvp := t.mem_primitiveSpan hN n d d (v := v) (by rw [hd, LinearMap.zero_apply]) hv
    refine (iSup_le fun j ↦ Submodule.map_le_iff_le_comap.mpr ?_ :
      primitiveSpan K M h e f (n : K) ≤ S) hvp
    rintro w ⟨hwe, hwh⟩
    replace hwe : ⁅e, w⁆ = 0 := hwe
    replace hwh : ⁅h, w⁆ = (n : K) • w := Module.End.mem_eigenspace_iff.mp hwh
    rw [Submodule.mem_comap]
    by_cases hj : j ≤ n
    · refine Submodule.mem_iSup_of_mem ((n : K) - 2 * j) (Submodule.mem_iSup_of_mem ?_ ?_)
      · intro heq
        have : ((m + n : ℕ) : K) = ((2 * j : ℕ) : K) := by push_cast; linear_combination heq
        have := Nat.cast_injective this
        omega
      · rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply]
        exact t.lie_h_pow_toEnd_f_of_eq hwh j
    · rw [show j = (j - (n + 1)) + (n + 1) by omega, pow_add, Module.End.mul_apply,
        t.pow_f_succ_eq_zero hwe hwh ⟨N + 1, by rw [hN, LinearMap.zero_apply]⟩, map_zero]
      exact zero_mem _
  have hxS : x ∈ S := by
    have hcopg : ∀ i ∈ s.filter (· < m), ∀ j ∈ s.filter (· < m), i ≠ j →
        IsCoprime (g i) (g j) := by
      intro i _ j _ hij
      refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub (Ne.isUnit fun hc ↦ hij ?_))
      have : ((i * (i + 2) : ℕ) : K) = ((j * (j + 2) : ℕ) : K) := by
        push_cast; linear_combination hc
      have h' := Nat.cast_injective this
      rcases lt_trichotomy i j with h | h | h
      · exact absurd h' (Nat.mul_lt_mul'' h (by omega)).ne
      · exact h
      · exact absurd h' (Nat.mul_lt_mul'' h (by omega)).ne'
    have := Module.End.ker_aeval_prod_le_iSup Ω (s.filter (· < m)) g hcopg
      (LinearMap.mem_ker.mpr hAx)
    have hle : (⨆ n ∈ s.filter (· < m), LinearMap.ker (aeval Ω (g n))) ≤ S :=
      iSup₂_le fun n hn ↦ hS n (Finset.mem_filter.mp hn).2
    exact hle this
  have hxm : x ∈ (toEnd K L M h).eigenspace (-(m : K)) := by
    rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply, hx]
  exact Submodule.disjoint_def.mp
    ((Module.End.eigenspaces_iSupIndep (toEnd K L M h)).disjoint_biSup
      (x := -(m : K)) (y := {c | c ≠ -(m : K)}) fun hc ↦ hc rfl) x hxm hxS

/-- **`eᵏ` is injective on the weight space `-m` for `k ≤ m`**: let `e` and `f` act locally
nilpotently on `M`, and let `x ∈ M` have `h`-weight `-m`, `m ∈ ℕ`. If `eᵏ x = 0` with `k ≤ m`, then
`x = 0`. -/
theorem wall_eq_zero_of_toEnd_e_pow_eq_zero
    (he : ∀ v : M, ∃ n, (toEnd K L M e ^ n) v = 0) (hf : ∀ v : M, ∃ n, (toEnd K L M f ^ n) v = 0)
    {x : M} {m k : ℕ} (hx : ⁅h, x⁆ = -(m : K) • x) (hkm : k ≤ m)
    (hk : (toEnd K L M e ^ k) x = 0) : x = 0 := by
  classical
  obtain ⟨B, hB⟩ := he x
  rcases Nat.eq_zero_or_pos B with rfl | hB0
  · simpa using hB
  choose A hA using fun b : ℕ ↦ hf ((toEnd K L M e ^ b) x)
  set A' := ∑ b ∈ Finset.range B, A b
  set E := toEnd K L M e
  set F := toEnd K L M f
  have hFA : ∀ b < B, ∀ a, A' ≤ a → (F ^ a) ((E ^ b) x) = 0 := by
    intro b hb a ha
    have : A b ≤ a := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr hb)).trans ha
    rw [show a = (a - A b) + A b by omega, pow_add, Module.End.mul_apply, hA b, map_zero]
  have hEB : ∀ b, B ≤ b → (E ^ b) x = 0 := fun b hb ↦ by
    rw [show b = (b - B) + B by omega, pow_add, Module.End.mul_apply, hB, map_zero]
  set S : Finset M := ((Finset.range A') ×ˢ (Finset.range B)).image fun p ↦ (F ^ p.1) ((E ^ p.2) x)
  set W := Submodule.span K (S : Set M)
  have hmem : ∀ a b, (F ^ a) ((E ^ b) x) ∈ W := by
    intro a b
    by_cases hb : b < B
    · by_cases ha : a < A'
      · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩,
            rfl⟩))
      · rw [hFA b hb a (by omega)]; exact zero_mem _
    · rw [hEB b (by omega), map_zero]; exact zero_mem _
  have hwt : ∀ b : ℕ, ⁅h, (E ^ b) x⁆ = (-(m : K) + 2 * b) • (E ^ b) x := fun b ↦ by
    rw [← toEnd_apply_apply (R := K), ← Module.End.mul_apply, t.toEnd_h_mul_e_pow,
      LinearMap.add_apply, Module.End.mul_apply, toEnd_apply_apply, hx, map_smul,
      LinearMap.smul_apply, ← add_smul, add_comm]
  have hstab : ∀ T : Module.End K M, (∀ a b, T ((F ^ a) ((E ^ b) x)) ∈ W) → ∀ v ∈ W, T v ∈ W := by
    intro T hT v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      exact hT a b
    | zero => rw [map_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul c v _ hv => rw [map_smul]; exact W.smul_mem c hv
  have hfW : ∀ v ∈ W, ⁅f, v⁆ ∈ W := hstab F fun a b ↦ by
    rw [← Module.End.mul_apply, ← pow_succ']; exact hmem _ _
  have hhW : ∀ v ∈ W, ⁅h, v⁆ ∈ W := hstab (toEnd K L M h) fun a b ↦ by
    rw [toEnd_apply_apply, t.lie_h_pow_toEnd_f_of_eq (hwt b)]; exact W.smul_mem _ (hmem _ _)
  have heW : ∀ v ∈ W, ⁅e, v⁆ ∈ W := hstab E fun a b ↦ by
    rcases a with _ | a
    · rw [pow_zero, Module.End.one_apply, ← Module.End.mul_apply, ← pow_succ']
      simpa using hmem 0 (b + 1)
    · rw [toEnd_apply_apply, t.lie_e_pow_succ_toEnd_f, hwt b, ← sub_smul, map_smul]
      refine add_mem ?_ (W.smul_mem _ (W.smul_mem _ (hmem _ _)))
      have : ⁅e, (E ^ b) x⁆ = (E ^ (b + 1)) x := by rw [pow_succ', Module.End.mul_apply]; rfl
      rw [this]
      exact hmem _ _
  -- the finite-dimensional submodule `W` over the subalgebra spanned by the triple
  set L' := LieSubalgebra.lieSpan K L {h, e, f}
  have hL' : ∀ z ∈ L', ∀ v ∈ W, ⁅z, v⁆ ∈ W := by
    intro z hz
    induction hz using LieSubalgebra.lieSpan_induction with
    | mem z hz =>
      rcases hz with rfl | rfl | rfl
      · exact hhW
      · exact heW
      · exact hfW
    | zero => intro v _; rw [zero_lie]; exact zero_mem _
    | add z z' _ _ hz hz' => intro v hv; rw [add_lie]; exact add_mem (hz v hv) (hz' v hv)
    | smul c z _ hz => intro v hv; rw [smul_lie]; exact W.smul_mem c (hz v hv)
    | lie z z' _ _ hz hz' =>
      intro v hv
      rw [lie_lie]
      exact sub_mem (hz _ (hz' v hv)) (hz' _ (hz v hv))
  let Y : LieSubmodule K L' M :=
    { W with lie_mem := fun {z v} hv ↦ hL' z z.2 v hv }
  have : FiniteDimensional K Y := FiniteDimensional.span_finset K S
  let h' : L' := ⟨h, LieSubalgebra.subset_lieSpan (by simp)⟩
  let e' : L' := ⟨e, LieSubalgebra.subset_lieSpan (by simp)⟩
  let f' : L' := ⟨f, LieSubalgebra.subset_lieSpan (by simp)⟩
  have t' : IsSl2Triple h' e' f' :=
    { h_ne_zero := fun h0 ↦ t.h_ne_zero (congrArg Subtype.val h0)
      lie_e_f := Subtype.ext t.lie_e_f
      lie_h_e_nsmul := Subtype.ext t.lie_h_e_nsmul
      lie_h_f_nsmul := Subtype.ext t.lie_h_f_nsmul }
  have hxY : x ∈ Y := by
    change x ∈ W
    simpa using hmem 0 0
  have hpow : ∀ n (y : Y), ((toEnd K L' Y e' ^ n) y : M) = (E ^ n) (y : M) := by
    intro n y
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have := t'.wall_eq_zero_of_toEnd_e_pow_eq_zero_of_finiteDimensional (M := Y) (x := ⟨x, hxY⟩)
    (Subtype.ext hx) hkm (Subtype.ext (by rw [hpow]; exact hk))
  exact congrArg Subtype.val this

end IsSl2Triple

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (i : ι)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)

namespace VermaModule

variable (Λ : Dual K H) (hA : A.IsGeneralizedCartan)

include hA in
/-- **The key lemma**: let `⟨λ + ρ, αᵢ^∨⟩ = d ∈ ℕ` and let `y ∈ M(λ)` be killed by `eᵢ`, of
`αᵢ^∨`-weight `-(k + 1)` with `k ≥ 1`. Then `y ∈ fᵢ M(λ)`. -/
theorem wall_mem_range_toEnd_f {d : ℕ} (hd : Λ (P.coroot i) = (d : K) - 1) {y : VermaModule P Λ}
    (he : ⁅e P i, y⁆ = 0) {k : ℕ} (hk : 1 ≤ k) (hy : ⁅h P (P.coroot i), y⁆ = -((k : K) + 1) • y) :
    ∃ z, ⁅f P i, z⁆ = y := by
  set D := nilradDecomp P i Λ
  set g := D.symm y
  have hyg : D g = y := D.apply_symm_apply y
  have hH : opH i Λ g = (-((k : K) + 1)) • g := D.injective (by
    rw [← lie_h_nilradDecomp i Λ hA, hyg, hy, map_smul, hyg])
  have hE : opE i Λ g = 0 := D.injective (by rw [← lie_e_nilradDecomp i Λ hA, hyg, he, map_zero])
  have hHn : ∀ n : ℕ, adH P i (g n) = (-((k : K) + 1) - ((d : K) - 1) + 2 * n) • g n := fun n ↦ by
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
    have hx := (isSl2Triple P hA i).wall_eq_zero_of_toEnd_e_pow_eq_zero (M := 𝓤)
      (exists_toEnd_pow_eq_zero_of_ad P (exists_ad_e_pow_eq_zero P hA i))
      (exists_toEnd_pow_eq_zero_of_ad P (exists_ad_f_pow_eq_zero P hA i))
      (x := envNilrad P i (g 0)) (m := k + d) (k := k)
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

include hA in
/-- **`M(λ)` is projective in the direction of `αᵢ`**: let `⟨λ + ρ, αᵢ^∨⟩ = d ∈ ℕ`.
Let `y ∈ M(λ)` be killed by `eᵢ`, of `αᵢ^∨`-weight `-(k + 1)` with `k ≥ 1`.
Then `y ∈ fᵢᵏ M(λ)`. Reconstructed; see the module docstring. -/
theorem wall_exists_eq_toEnd_f_pow {d : ℕ} (hd : Λ (P.coroot i) = (d : K) - 1) {y : VermaModule P Λ}
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
    · obtain ⟨z, hz⟩ := wall_mem_range_toEnd_f i Λ hA hd he hk hy
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
`⟨λ + ρ, αᵢ^∨⟩ ∈ ℕ`, then `y = fᵢᵏ x` for a primitive vector `x` of weight `ν + k αᵢ`. -/
theorem wall_exists_mem_primitiveVectors_of_mem {d : ℕ}
    (hd : Λ (P.coroot i) = (d : K) - 1) {ν : Dual K H}
    {k : ℕ} (hk : 1 ≤ k) (hν : ν (P.coroot i) = -((k : K) + 1)) {y : VermaModule P Λ}
    (hy : y ∈ primitiveVectors P (VermaModule P Λ) ν) :
    ∃ x ∈ primitiveVectors P (VermaModule P Λ) (ν + k • P.root i),
      (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ k) x = y := by
  have t := isSl2Triple P hA i
  rw [mem_primitiveVectors] at hy
  obtain ⟨x, rfl⟩ := wall_exists_eq_toEnd_f_pow i Λ hA hd (hy.2 i) hk (by rw [hy.1, hν])
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


variable {Λ}

include hA in
/-- Source reflection preserves Hom dimension into a dot-dominant rank-one target,
including the singular wall `Λ(αᵢ∨) = -1`. Reconstructed primitive-vector bijection. -/
theorem wall_finrank_hom_reflection_source {μ : Dual K H} {d n : ℕ}
    (hd : Λ (P.coroot i) = (d : K) - 1) (hn0 : 0 < n)
    (hn : (μ + P.rho) (P.coroot i) = n) :
    finrank K (VermaModule P (P.reflection hA i (μ + P.rho) - P.rho) →ₗ⁅K,P.KacMoodyAlgebra⁆
        VermaModule P Λ) =
      finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) := by
  have hμn : μ (P.coroot i) = (n : K) - 1 := by
    rw [LinearMap.add_apply, rho_coroot] at hn
    linear_combination hn
  rw [finrank_hom, finrank_hom, P.reflection_add_rho_sub_rho hA hn]
  let T : primitiveVectors P (VermaModule P Λ) μ →ₗ[K]
      primitiveVectors P (VermaModule P Λ) (μ - n • P.root i) :=
    ((toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P i) ^ n).restrict fun x hx ↦
      toEnd_f_pow_mem_primitiveVectors_of_mem i Λ (by rw [hμn]; ring) hx hA)
  have hT : Function.Bijective T := by
    refine ⟨fun x y hxy ↦ Subtype.ext (toEnd_f_pow_injective i Λ n
      (congrArg Subtype.val hxy)), fun y ↦ ?_⟩
    have hν : (μ - n • P.root i) (P.coroot i) = -((n : K) + 1) := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, root_coroot_self P hA, hμn, nsmul_eq_mul]
      ring
    obtain ⟨x, hx, hxy⟩ := wall_exists_mem_primitiveVectors_of_mem i Λ hA hd hn0 hν y.2
    rw [sub_add_cancel] at hx
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (LinearEquiv.ofBijective T hT).finrank_eq.symm

omit i in
/-- Hom from any dot-orbit translate into a weakly dot-dominant integral Verma module
has dimension one. The zero shifted source pairing is handled by the identity, not lifting.
Reconstructed extension of the induction in `BGG/Uniqueness`. -/
theorem wall_finrank_hom_weylDot_self (hΛ : P.IsDominantIntegral (Λ + P.rho))
    (w : P.weylGroup hA) :
    finrank K (VermaModule P (P.weylDot hA w Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) = 1 := by
  set cs := P.coxeterSystem hA
  induction hl : cs.length w using Nat.strong_induction_on generalizing w with
  | _ l ih =>
    subst hl
    by_cases hw1 : w = 1
    · subst hw1
      rw [weylDot_one, finrank_hom]
      have : primitiveVectors P (VermaModule P Λ) Λ = K ∙ hwv P Λ := by
        refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr
          (hwv_mem_primitiveVectors P Λ))
        rw [← weightSpace_self]
        exact inf_le_left
      rw [this, finrank_span_singleton (hwv_ne_zero P Λ)]
    obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
    have hsl := (cs.isLeftDescent_iff).mp hs
    set w' := cs.simple s * w
    have hww' : w = cs.simple s * w' := (cs.simple_mul_simple_cancel_left s).symm
    have hw' : ¬cs.IsLeftDescent w' s := by
      rwa [← cs.isLeftDescent_iff_not_isLeftDescent_mul]
    have hind := ih _ (by omega) w' rfl
    obtain ⟨n, hn⟩ := P.exists_apply_coroot_nat_of_not_isLeftDescent hA hΛ hw'
    have hn' : (P.weylDot hA w' Λ + P.rho) (P.coroot s) = n := by
      rwa [weylDot_add_rho]
    rw [hww', weylDot_simple_mul]
    by_cases hn0 : n = 0
    · rw [P.reflection_add_rho_sub_rho hA hn', hn0, zero_nsmul, sub_zero]
      exact hind
    · obtain ⟨d, hd⟩ := hΛ s
      have hd' : Λ (P.coroot s) = (d : K) - 1 := by
        rw [LinearMap.add_apply, rho_coroot] at hd
        linear_combination hd
      rw [wall_finrank_hom_reflection_source s hA hd' (Nat.pos_of_ne_zero hn0) hn']
      exact hind

omit i in
/-- Uniqueness on the dot orbit of any weakly dot-dominant integral weight, with no
regularity hypothesis. This is an orbit theorem, not unrestricted Kac–Moody uniqueness.
Reconstructed from wall lifting and the existing actual weak-dominant embeddings. -/
theorem wall_finrank_hom_weylDot_le_one (hΛ : P.IsDominantIntegral (Λ + P.rho))
    (w w' : P.weylGroup hA) :
    finrank K (VermaModule P (P.weylDot hA w' Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆
      VermaModule P (P.weylDot hA w Λ)) ≤ 1 := by
  obtain ⟨φ, hφ⟩ := exists_injective_weylDot_of_dotDominant P hA hΛ w
  exact (finrank_hom_le_of_injective P _ φ hφ).trans
    (wall_finrank_hom_weylDot_self hA hΛ w').le

variable [FiniteDimensional K H] [IsAlgClosed K]

omit i hA in
/-- Finite-type Hom uniqueness with weakly dot-dominant integral target and arbitrary
source. The source orbit is forced by the existing Kac–Kazhdan theorem, not assumed.
Reconstructed; classical context is Humphreys, category O, Chapter 4. -/
theorem finrank_hom_le_one_of_dotDominant (hfin : A.IsFiniteCartan)
    (S : A.Symmetrization) (hΛ : P.IsDominantIntegral (Λ + P.rho)) (μ : Dual K H) :
    finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) ≤ 1 := by
  classical
  by_cases hzero : ∀ φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ, φ = 0
  · have : Subsingleton (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) :=
      ⟨fun φ ψ ↦ (hzero φ).trans (hzero ψ).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  push Not at hzero
  obtain ⟨φ, hφ⟩ := hzero
  obtain ⟨w, rfl⟩ := exists_weylDot_of_hom_ne_zero P hfin S hφ
  exact (wall_finrank_hom_weylDot_self hfin.isGeneralizedCartan hΛ w).le

omit i hA in
/-- **Finite-type Verma Hom uniqueness for every integral target, including singular
walls, and every source weight**. No source integrality or orbit hypothesis is assumed.
Over an algebraically closed characteristic-zero field, finite-dimensional Cartan,
finite Cartan matrix, and an explicit symmetrization. Reconstructed proof of this part
of the classical theorem (Humphreys, category O, Chapter 4); no printed proof consulted. -/
theorem finrank_hom_le_one_of_finite_type_integral (hfin : A.IsFiniteCartan)
    (S : A.Symmetrization) (Λ μ : Dual K H)
    (hΛ : ∀ i, ∃ z : ℤ, (Λ + P.rho) (P.coroot i) = z) :
    finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) ≤ 1 := by
  obtain ⟨Λ', hΛ', -, hbound⟩ :=
    exists_dotDominant_hom_bound_of_finite_type_integral P hfin Λ hΛ
  exact (hbound μ).trans (finrank_hom_le_one_of_dotDominant hfin S hΛ' μ)

end VermaModule
end Matrix.Realization.KacMoodyAlgebra
