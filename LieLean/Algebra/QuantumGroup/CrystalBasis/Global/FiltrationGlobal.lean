/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.StringFiltration

/-!
# Global bases of the string filtrations: [Kas91] Prop. 7.4.1

Let `λ` be dominant, `i ∈ I` and `n ≥ 1`. [Kas91] Prop. 7.4.1 states that, at the weight `λ - ν`,

`(fᵢⁿV(λ))^ℤ ∩ L(λ) ∩ L(λ)⁻ → (fᵢⁿV(λ))^ℤ ∩ L(λ) / (fᵢⁿV(λ))^ℤ ∩ v⁻¹L(λ)`

is an isomorphism, under the induction hypothesis of [Kas91] §7 at the weights below `ν`. We
prove it in basis form (`HwFiltGlobalAt`): `(fᵢⁿV(λ))^ℤ_{λ-ν}` is the `𝒜`-span of vectors
`g_k ∈ (fᵢⁿV(λ))^ℤ_{λ-ν}` with independent residues in `L(λ)/v⁻¹L(λ)` and in `L(λ)⁻/vL(λ)⁻`, and
the residue of each `g_k` is an element `f̃ᵢⁿ f̃_{u_k} u_λ` of `f̃ᵢⁿB(λ)`. The two halves of the
isomorphism then follow from Lemma 7.1.1 (`hwFilt_eq_zero_of_mem`, `exists_hwFilt_sub_mem`).

The induction hypothesis (`GlobalBelow`) is the part of Kashiwara's `(G_{l-1})` used in the proof:
at every weight `μ < ν`, `(G.1)` holds (`NegGlobalAt`), `G(b)u_λ = 0` whenever `π̄_λ(b) = 0`
(Lemma 7.5.2, which with `(G.1)` gives `(G.2)`, `hwGlobalAt_of_vanishing`), and `G(b) ∈ (fᵢU⁻)^ℤ`
whenever `ẽᵢb ≠ 0` (`(G.3)` for `n = 1`).

The proof is Kashiwara's: descending induction on `n`; the reduction to `n + ⟨hᵢ, λ - ν⟩ ≥ 0`
(`hwFilt_le_succ`); then `(fᵢⁿV(λ))^ℤ = Σ_{b ∈ S} 𝒜 fᵢ^{(n)}G(b)u_λ + (fᵢ^{n+1}V(λ))^ℤ`, with
`S` the elements `b` of `B(∞)` of weight `-ν + nαᵢ` with `ẽᵢb = 0`, the congruences
`fᵢ^{(n)}G(b) ≡ fᵢ^{(n)}PᵢG(b)` (6.1.2) and `fᵢ^{(n)}PᵢG(b) ≡ f̃ᵢⁿb`, and Lemma 7.1.2. In basis
form, Lemma 7.1.2 is `exists_residueIndependent_extension`. Kashiwara identifies `S` with
`B(λ) ∩ f̃ᵢⁿB(λ) \ f̃ᵢ^{n+1}B(λ)` using (7.4.3); we only need the independence of the residues
`f̃ᵢⁿπ̄_λ(b)` modulo `(fᵢ^{n+1}V(λ))^ℤ`, which we check directly in `B(λ)` by applying `ẽᵢⁿ`
(`dvd_of_sum_mem_sup`; our own argument for this step). The statement that these residues exhaust
`B(λ) ∩ f̃ᵢⁿB(λ)` is not needed later and is not formalized.

## Main definitions

* `GlobalBelow hR ν`: the induction hypothesis at the weights below `ν`.
* `HwFiltGlobalAt hR Λ i n ν`: [Kas91] Prop. 7.4.1 at `(i, n, ν)`, in basis form.

## Main results

* `hwFiltGlobalAt`: **[Kas91] Prop. 7.4.1**.
* `hwFilt_eq_zero_of_mem`, `exists_hwFilt_sub_mem`: the injectivity and surjectivity in (7.4.1).

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.4.
-/

open Pointwise

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} {Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I}

/-! ### Bar and divided powers on the filtrations -/

section Negative

variable (D)

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

omit [Finite I] [DecidableEq I] in
lemma negBar_f_pow (i : I) (k : ℕ) (y : Um D 𝕧) :
    negBar D ((NegativePart.f D 𝕧 i ^ k) y) = (NegativePart.f D 𝕧 i ^ k) (negBar D y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    obtain ⟨Y, hY⟩ := Submodule.Quotient.mk_surjective _ ((NegativePart.f D 𝕧 i ^ k) y)
    rw [← hY]
    change negBar D (NegativePart.f D 𝕧 i (NegativePart.mk Y)) =
      NegativePart.f D 𝕧 i (negBar D (NegativePart.mk Y))
    rw [NegativePart.f_mk]
    erw [negBar_mk, negBar_mk]
    rw [NegativePart.f_mk, map_mul, LusztigF.bar_θ]

omit [Finite I] in
/-- The divided powers `fᵢ^{(k)}` commute with the bar involution of `U⁻`. -/
lemma negBar_df (i : I) (k : ℕ) (y : Um D 𝕧) :
    negBar D ((bosv i).df k y) = (bosv i).df k (negBar D y) := by
  rw [BosonModule.df_apply, BosonModule.df_apply, negBar_smul, NegativePart.boson_f,
    negBar_f_pow, qFactorial_inv, map_inv₀, QuantumGroup.bar_qFactorial]

omit [Finite I] [DecidableEq I] in
lemma negBar_laurent_smul (c : LaurentPolynomial ℤ) (x : Um D 𝕧) :
    negBar D (c • x) = LaurentPolynomial.invert c • negBar D x := by
  rw [laurent_smul_eq, negBar_smul, bar_integralLaurentEval, laurent_smul_eq]

/-- `(fᵢⁿU⁻)^ℤ_ν` is bar-stable. -/
lemma negBar_mem_negFilt {i : I} {n : ℕ} {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ negFilt D i n ν) :
    negBar D x ∈ negFilt D i n ν := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, y, hnk, hk, hy, hyw, rfl⟩ := hx
    rw [negBar_df]
    exact df_mem_negFilt D i hnk hk (negBar_mem_negIntegral D hy) (negBar_mem_Uw D hyw)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [negBar_laurent_smul]; exact Submodule.smul_mem _ _ hx

/-- `fᵢ^{(n)}(fᵢU⁻)^ℤ_{ν-nαᵢ} ⊆ (fᵢ^{n+1}U⁻)^ℤ_ν`. -/
lemma df_mem_negFilt_succ (i : I) {n : ℕ} {ν : I →₀ ℕ} (hn : n ≤ ν i) {x : Um D 𝕧}
    (hx : x ∈ negFilt D i 1 (ν - Finsupp.single i n)) :
    (bosv i).df n x ∈ negFilt D i (n + 1) ν := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, y, hk1, hk, hy, hyw, rfl⟩ := hx
    have hkν : k ≤ ν i - n := by simpa using hk
    have hw : ν - Finsupp.single i n - Finsupp.single i k = ν - Finsupp.single i (n + k) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp; omega
      · simp [Ne.symm hl]
    rw [hw] at hyw
    rw [BosonModule.df_df _ (NegativePart.pow_d_ne_zero (NeZero.ne 𝕧) i)
      (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i), qBinomial_inv]
    obtain ⟨a, ha⟩ := isLaurent_qBinomial (D.d i) (n + k) n
    rw [← ha, ← laurent_smul_eq]
    exact Submodule.smul_mem _ _ (df_mem_negFilt D i (by omega) (by omega) hy hyw)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [laurent_smul_eq, map_smul, ← laurent_smul_eq]
    exact Submodule.smul_mem _ _ hx

omit [Finite I] in
/-- `f̃ᵢⁿ f̃_w 1 = f̃_{iⁿw} 1`. -/
lemma kF_pow_fWi (i : I) (n : ℕ) (w : List I) :
    (kF hvt i ^ n) (fWi (D := D) hvt w) = fWi hvt (List.replicate n i ++ w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp [fWi, List.replicate_succ, NegativePart.fWord_cons]

omit [Finite I] in
lemma kF_pow_mem_smul_latInf (i : I) (n : ℕ) {x : Um D 𝕧}
    (hx : x ∈ ϖ • latInf (D := D) hvt A) : (kF hvt i ^ n) x ∈ ϖ • latInf (D := D) hvt A := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact kF_mem_smul_latInf i ih

end Negative

section HighestWeight

variable {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)

/-- `(fᵢⁿV(λ))^ℤ_{λ-ν}` is bar-stable. -/
lemma hwBar_mem_hwFilt {i : I} {n : ℕ} {ν : I →₀ ℕ} {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwFilt Λ i n ν) : hwBar hR Λ m ∈ hwFilt Λ i n ν := by
  obtain ⟨x, hx, rfl⟩ := hm
  rw [hwBar_evq]
  exact evq_mem_hwFilt Λ (negBar_mem_negFilt D hx)

/-- `(fᵢⁿV(λ))^ℤ_{λ-ν} = 0` for `n > νᵢ`. -/
lemma hwFilt_eq_bot {i : I} {n : ℕ} {ν : I →₀ ℕ} (hn : ν i < n) {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwFilt Λ i n ν) : m = 0 := by
  obtain ⟨x, hx, rfl⟩ := hm
  have : negFilt D i n ν = ⊥ := by
    rw [negFilt, Submodule.span_eq_bot]
    rintro _ ⟨k, y, hnk, hk, -⟩
    omega
  rw [this, SetLike.mem_coe, Submodule.mem_bot] at hx
  rw [hx, map_zero]

end HighestWeight

/-! ### `i`-strings in `B(λ)` -/

section Strings

variable {R : D.RootDatum Y} {hR : R.IsXRegular}
variable (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

omit [Finite I] in
lemma fW_replicate_append (Λ : Dom R) (i : I) (m : ℕ) (w : List I) :
    fW hvt hR Λ (List.replicate m i ++ w) = (fK hvt hR Λ i ^ m) (fW hvt hR Λ w) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ← ih]
    rfl

omit [Finite I] in
lemma fW_replicate_append_mem {Λ : Dom R} (i : I) (m : ℕ) {w : List I}
    (hw : fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ) :
    fW hvt hR Λ (List.replicate m i ++ w) ∈ ϖ • lat hvt hR A Λ := by
  induction m with
  | zero => simpa using hw
  | succ m ih => exact kashiwaraF_mem_smul_lat Λ i ih

include hfund in
lemma eK_pow_mem_smul_lat {Λ : Dom R} (i : I) (m : ℕ) {x : IrreducibleModule R 𝕧 Λ.1}
    (hx : x ∈ ϖ • lat hvt hR A Λ) : (eK hvt hR Λ i ^ m) x ∈ ϖ • lat hvt hR A Λ := by
  have hL : IsCrystalLattice _ (isInt hvt hR Λ) (lat hvt hR A Λ) :=
    isCrystalLattice_lat (hR := hR) InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund Λ
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact LinearMap.map_mem_smul_of_mem ϖ (fun m hm ↦ hL.kashiwaraE_mem i m hm) ih

include hfund in
/-- `ẽᵢᵐ f̃ᵢᵐ b = b` in `B(λ)` when `f̃ᵢᵐ b ≠ 0`. -/
lemma eK_pow_fW_replicate_sub_mem (Λ : Dom R) (i : I) (w : List I) :
    ∀ m : ℕ, fW hvt hR Λ (List.replicate m i ++ w) ∉ ϖ • lat hvt hR A Λ →
      (eK hvt hR Λ i ^ m) (fW hvt hR Λ (List.replicate m i ++ w)) - fW hvt hR Λ w ∈
        ϖ • lat hvt hR A Λ := by
  have hall : ∀ r, AllProp hvt hR A ϖ r := allProp (hR := hR)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul hfund
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    set w₀ := List.replicate m i ++ w
    have hcons : List.replicate (m + 1) i ++ w = i :: w₀ := rfl
    have hw₀ : fW hvt hR Λ w₀ ∉ ϖ • lat hvt hR A Λ := fun h ↦ hm (by
      rw [hcons, fW_cons]; exact kashiwaraF_mem_smul_lat Λ i h)
    rw [hcons] at hm ⊢
    have hC := (hall (w₀.length + 1)).2.2.1 Λ i w₀ (i :: w₀) rfl rfl hw₀ hm
    have h1 : fW hvt hR Λ w₀ - eK hvt hR Λ i (fW hvt hR Λ (i :: w₀)) ∈ ϖ • lat hvt hR A Λ :=
      hC.1 (by rw [fW_cons, sub_self]; exact zero_mem _)
    have h2 := eK_pow_mem_smul_lat hfund i m (neg_mem h1)
    rw [neg_sub, map_sub] at h2
    rw [pow_succ, Module.End.mul_apply]
    have := add_mem h2 (ih hw₀)
    rwa [sub_add_sub_cancel] at this

include hfund in
/-- If `ẽᵢb = 0` and `n ≤ ⟨hᵢ, wt b⟩` for `b ∈ B(λ)`, then `f̃ᵢⁿb ≠ 0` (the string through `b` has
length `⟨hᵢ, wt b⟩`). -/
lemma fW_replicate_append_notMem (Λ : Dom R) (i : I) {w : List I}
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (he : eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ) {n : ℕ}
    (hn : (n : ℤ) ≤ (Λ.1 - R.rootSum (wordWeight w)) (R.coroot i)) :
    fW hvt hR Λ (List.replicate n i ++ w) ∉ ϖ • lat hvt hR A Λ := by
  have hall : ∀ r, AllProp hvt hR A ϖ r := allProp (hR := hR)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul hfund
  have hϖ0 : algebraMap A 𝕂 ϖ ≠ 0 := by
    rw [InfinityLocalRing.algebraMap_uniformizer]; exact inv_ne_zero RatFunc.X_ne_zero
  have hA : ∀ d, ∀ s ≤ d, PropA hvt hR A s := fun _ s _ ↦ (hall s).1
  obtain ⟨kk, a, u, hs⟩ := exists_isStr hϖ0 (hA _) (fun s _ ↦ (hall s).2.1)
    (fun s _ ↦ (hall s).2.2.1) Λ i rfl (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w)
    (fW_mem_wsp hvt hR Λ w) (w := w) (by rw [sub_self]; exact zero_mem _) hw
  have hk0 : kk = 0 := by
    by_contra hk
    have h1 := hs.eK_sub (hA _) rfl hϖ0
    simp only [hk, ↓reduceIte] at h1
    exact hs.dFV_notMem (hA _) rfl hϖ0 (kk - 1) (by omega)
      (by simpa using sub_mem he h1)
  subst hk0
  have hna : n ≤ a := by have := hs.node; omega
  have key : ∀ j ≤ a, IsStr hvt hR ϖ Λ i (wordWeight w + Finsupp.single i j)
      (fW hvt hR Λ (List.replicate j i ++ w)) j a u := by
    intro j
    induction j with
    | zero => intro _; simpa using hs
    | succ j ih =>
      intro hj
      have := (ih (by omega)).kashiwaraF (by omega)
      rwa [add_assoc, ← Finsupp.single_add] at this
  exact (key n hna).notMem_x (hA _) rfl hϖ0

include hfund in
/-- The residues `f̃ᵢⁿb`, for distinct `b ∈ B(λ)` with `ẽᵢb = 0` and `f̃ᵢⁿb ≠ 0`, are independent
modulo `v⁻¹L(λ) + ℚ(v)N`, where `N` is spanned by vectors with independent residues in
`f̃ᵢ^{n+1}B(λ)`. -/
lemma dvd_of_sum_mem_sup {Λ : Dom R} (i : I) (n : ℕ) {T ι : Type*} (w : T → List I)
    (u : ι → List I) (f : T → IrreducibleModule R 𝕧 Λ.1) (g : ι → IrreducibleModule R 𝕧 Λ.1)
    (hw : ∀ c, fW hvt hR Λ (w c) ∉ ϖ • lat hvt hR A Λ)
    (he : ∀ c, eK hvt hR Λ i (fW hvt hR Λ (w c)) ∈ ϖ • lat hvt hR A Λ)
    (hwinj : ∀ c c', fW hvt hR Λ (w c) - fW hvt hR Λ (w c') ∈ ϖ • lat hvt hR A Λ → c = c')
    (hfn : ∀ c, fW hvt hR Λ (List.replicate n i ++ w c) ∉ ϖ • lat hvt hR A Λ)
    (hf : ∀ c, f c - fW hvt hR Λ (List.replicate n i ++ w c) ∈ ϖ • lat hvt hR A Λ)
    (hg : ResidueIndependent A (lat hvt hR A Λ) ϖ g)
    (hgu : ∀ k, g k - fW hvt hR Λ (List.replicate (n + 1) i ++ u k) ∈ ϖ • lat hvt hR A Λ)
    (t : Finset T) (a : T → A)
    (ht : ∑ c ∈ t, a c • f c ∈
      ϖ • lat hvt hR A Λ ⊔ (Submodule.span 𝕂 (Set.range g)).restrictScalars A) :
    ∀ c ∈ t, ϖ ∣ a c := by
  classical
  have hall : ∀ r, AllProp hvt hR A ϖ r := allProp (hR := hR)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul hfund
  have hD : ∀ r, PropD hvt hR A ϖ r := fun r ↦ (hall r).2.2.2.1
  have hϖu : ¬ ϖ ∣ (1 : A) := fun h ↦ irreducible_localX.not_isUnit (isUnit_of_dvd_one h)
  have hsl : ∀ {x : IrreducibleModule R 𝕧 Λ.1}, x ∈ ϖ • lat hvt hR A Λ → x ∈ lat hvt hR A Λ :=
    fun hx ↦ Submodule.smul_le_self_of_tower ϖ _ hx
  have hrep : ∀ k, List.replicate (n + 1) i ++ u k = List.replicate n i ++ i :: u k := fun k ↦ by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]
  have hg0 : ∀ k, fW hvt hR Λ (List.replicate (n + 1) i ++ u k) ∉ ϖ • lat hvt hR A Λ := by
    intro k hk
    refine hϖu (hg.2 {k} (fun _ ↦ 1) ?_ k (Finset.mem_singleton_self k))
    rw [Finset.sum_singleton, one_smul, ← sub_add_cancel (g k) (fW hvt hR Λ _)]
    exact add_mem (hgu k) hk
  have hgd : ∀ k k', k ≠ k' → fW hvt hR Λ (List.replicate (n + 1) i ++ u k) -
      fW hvt hR Λ (List.replicate (n + 1) i ++ u k') ∉ ϖ • lat hvt hR A Λ := by
    intro k k' hne hk
    have h1 := hg.2 {k, k'} (fun j ↦ if j = k then 1 else -1) (by
      simp only [Finset.sum_pair hne, ↓reduceIte, Ne.symm hne, one_smul,
        neg_smul]
      have e : g k + -g k' = (g k - fW hvt hR Λ (List.replicate (n + 1) i ++ u k)) -
          (g k' - fW hvt hR Λ (List.replicate (n + 1) i ++ u k')) +
          (fW hvt hR Λ (List.replicate (n + 1) i ++ u k) -
            fW hvt hR Λ (List.replicate (n + 1) i ++ u k')) := by abel
      rw [e]
      exact add_mem (sub_mem (hgu k) (hgu k')) hk) k (Finset.mem_insert_self _ _)
    simp only [↓reduceIte] at h1
    exact hϖu h1
  have heK : ∀ m {x : IrreducibleModule R 𝕧 Λ.1}, x ∈ ϖ • lat hvt hR A Λ →
      (eK hvt hR Λ i ^ m) x ∈ ϖ • lat hvt hR A Λ := fun m _ hx ↦ eK_pow_mem_smul_lat hfund i m hx
  -- the three kinds of distinctness
  have H1 : ∀ c c', c ≠ c' → fW hvt hR Λ (List.replicate n i ++ w c) -
      fW hvt hR Λ (List.replicate n i ++ w c') ∉ ϖ • lat hvt hR A Λ := by
    intro c c' hne hc
    refine hne (hwinj c c' ?_)
    have e : fW hvt hR Λ (w c) - fW hvt hR Λ (w c') =
        -((eK hvt hR Λ i ^ n) (fW hvt hR Λ (List.replicate n i ++ w c)) - fW hvt hR Λ (w c)) +
        ((eK hvt hR Λ i ^ n) (fW hvt hR Λ (List.replicate n i ++ w c')) - fW hvt hR Λ (w c')) +
        (eK hvt hR Λ i ^ n) (fW hvt hR Λ (List.replicate n i ++ w c) -
          fW hvt hR Λ (List.replicate n i ++ w c')) := by rw [map_sub]; abel
    rw [e]
    exact add_mem (add_mem (neg_mem (eK_pow_fW_replicate_sub_mem hfund Λ i (w c) n (hfn c)))
      (eK_pow_fW_replicate_sub_mem hfund Λ i (w c') n (hfn c'))) (heK n hc)
  have H3 : ∀ c k, fW hvt hR Λ (List.replicate n i ++ w c) -
      fW hvt hR Λ (List.replicate (n + 1) i ++ u k) ∉ ϖ • lat hvt hR A Λ := by
    intro c k hc
    rw [hrep k] at hc
    have h1 : fW hvt hR Λ (w c) - fW hvt hR Λ (i :: u k) ∈ ϖ • lat hvt hR A Λ := by
      have e : fW hvt hR Λ (w c) - fW hvt hR Λ (i :: u k) =
          -((eK hvt hR Λ i ^ n) (fW hvt hR Λ (List.replicate n i ++ w c)) - fW hvt hR Λ (w c)) +
          ((eK hvt hR Λ i ^ n) (fW hvt hR Λ (List.replicate n i ++ i :: u k)) -
            fW hvt hR Λ (i :: u k)) +
          (eK hvt hR Λ i ^ n) (fW hvt hR Λ (List.replicate n i ++ w c) -
            fW hvt hR Λ (List.replicate n i ++ i :: u k)) := by rw [map_sub]; abel
      rw [e]
      refine add_mem (add_mem (neg_mem (eK_pow_fW_replicate_sub_mem hfund Λ i (w c) n (hfn c)))
        (eK_pow_fW_replicate_sub_mem hfund Λ i (i :: u k) n ?_)) (heK n hc)
      rw [← hrep k]; exact hg0 k
    by_cases hX : fW hvt hR Λ (i :: u k) ∈ ϖ • lat hvt hR A Λ
    · refine hw c ?_
      rw [← sub_add_cancel (fW hvt hR Λ (w c)) (fW hvt hR Λ (i :: u k))]
      exact add_mem h1 hX
    · have h2 := eK_pow_fW_replicate_sub_mem hfund Λ i (u k) 1 hX
      rw [pow_one] at h2
      change eK hvt hR Λ i (fW hvt hR Λ (i :: u k)) - fW hvt hR Λ (u k) ∈ _ at h2
      have h1' := heK 1 h1
      rw [pow_one, map_sub] at h1'
      have h3 : eK hvt hR Λ i (fW hvt hR Λ (i :: u k)) ∈ ϖ • lat hvt hR A Λ := by
        have := sub_mem (he c) h1'
        rwa [sub_sub_cancel] at this
      have h4 : fW hvt hR Λ (u k) ∈ ϖ • lat hvt hR A Λ := by
        have := sub_mem h3 h2
        rwa [sub_sub_cancel] at this
      exact hX (kashiwaraF_mem_smul_lat Λ i h4)
  -- reduce to the independence of `B(λ)`
  intro c₀ hc₀
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ht
  have hfL : ∀ c, f c ∈ lat hvt hR A Λ := fun c ↦ by
    rw [← sub_add_cancel (f c) (fW hvt hR Λ _)]
    exact add_mem (hsl (hf c)) (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A _)
  have hzL : z ∈ lat hvt hR A Λ := by
    have : z = ∑ c ∈ t, a c • f c - y := by rw [← hyz]; abel
    rw [this]
    exact sub_mem (Submodule.sum_mem _ fun c _ ↦ Submodule.smul_mem _ _ (hfL c)) (hsl hy)
  obtain ⟨d, hd⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1
    ((Submodule.restrictScalars_mem _ _ _).1 hz)
  have hd' : ∑ k ∈ d.support, d k • g k ∈ lat hvt hR A Λ := by rw [← hd] at hzL; exact hzL
  have hb := hg.exists_eq_of_sum_mem InfinityLocalRing.injective_algebraMap
    (show ϖ ≠ 0 from irreducible_localX.ne_zero) InfinityLocalRing.exists_pow_mul d.support d hd'
  choose! b hb using hb
  have hzb : z = ∑ k ∈ d.support, b k • g k := by
    rw [← hd]
    exact Finset.sum_congr rfl fun k hk ↦ by simp only [hb k hk, algebraMap_smul]
  let wd : T ⊕ ι → List I :=
    Sum.elim (fun c ↦ List.replicate n i ++ w c) (fun k ↦ List.replicate (n + 1) i ++ u k)
  have hdist : ∀ x₁ ∈ t.disjSum d.support, ∀ x₂ ∈ t.disjSum d.support, x₁ ≠ x₂ →
      fW hvt hR Λ (wd x₁) - fW hvt hR Λ (wd x₂) ∉ ϖ • lat hvt hR A Λ := by
    rintro (c | k) - (c' | k') - hne
    · exact H1 c c' fun h ↦ hne (by rw [h])
    · exact H3 c k'
    · intro h
      exact H3 c' k (by rw [← neg_sub]; exact neg_mem h)
    · exact hgd k k' fun h ↦ hne (by rw [h])
  have hsum : ∑ x ∈ t.disjSum d.support, Sum.elim a (fun k ↦ -b k) x • fW hvt hR Λ (wd x) ∈
      ϖ • lat hvt hR A Λ := by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr, wd, neg_smul, Finset.sum_neg_distrib]
    have e : ∑ c ∈ t, a c • fW hvt hR Λ (List.replicate n i ++ w c) -
        ∑ k ∈ d.support, b k • fW hvt hR Λ (List.replicate (n + 1) i ++ u k) =
        (∑ c ∈ t, a c • f c - z) - ∑ c ∈ t, a c • (f c - fW hvt hR Λ (List.replicate n i ++ w c))
          + ∑ k ∈ d.support, b k • (g k - fW hvt hR Λ (List.replicate (n + 1) i ++ u k)) := by
      simp only [smul_sub, Finset.sum_sub_distrib, hzb]
      abel
    rw [← sub_eq_add_neg, e, ← hyz, add_sub_cancel_right]
    exact add_mem (sub_mem hy (Submodule.sum_mem _ fun c _ ↦ Submodule.smul_mem _ _ (hf c)))
      (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hgu k))
  have := coeff_mem_of_sum_mem hD Λ (t.disjSum d.support) wd
    (fun x₁ h₁ x₂ h₂ he ↦ by
      by_contra hne
      exact hdist x₁ h₁ x₂ h₂ hne (by rw [he, sub_self]; exact zero_mem _))
    (by
      rintro (c | k) -
      · exact hfn c
      · exact hg0 k)
    hdist _ hsum (Sum.inl c₀) (Finset.inl_mem_disjSum.2 hc₀)
  exact Ideal.mem_span_singleton.1 this

/-- The bar version of `dvd_of_sum_mem_sup`: residue independence modulo `vL(λ)⁻ + ℚ(v)N`
follows from residue independence modulo `v⁻¹L(λ) + ℚ(v)N` when `f` is bar-invariant modulo
`ℚ(v)N` and `ℚ(v)N` is bar-stable. -/
lemma dvd_of_sum_mem_sup_bar {Λ : Dom R} {T ι : Type*} (f : T → IrreducibleModule R 𝕧 Λ.1)
    (g : ι → IrreducibleModule R 𝕧 Λ.1)
    (hfb : ∀ c, hwBar hR Λ (f c) - f c ∈ Submodule.span 𝕂 (Set.range g))
    (hgb : ∀ k, hwBar hR Λ (g k) ∈ Submodule.span 𝕂 (Set.range g))
    (h₀ : ∀ (t : Finset T) (a : T → A), ∑ c ∈ t, a c • f c ∈
      ϖ • lat hvt hR A Λ ⊔ (Submodule.span 𝕂 (Set.range g)).restrictScalars A →
      ∀ c ∈ t, ϖ ∣ a c)
    (t : Finset T) (a : T → LocalRing) (ht : ∑ c ∈ t, a c • f c ∈
      localX • latBar hR Λ ⊔ (Submodule.span 𝕂 (Set.range g)).restrictScalars LocalRing) :
    ∀ c ∈ t, localX ∣ a c := by
  have hW : ∀ x ∈ Submodule.span 𝕂 (Set.range g),
      hwBar hR Λ x ∈ Submodule.span 𝕂 (Set.range g) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hgb k
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [hwBar_smul]; exact Submodule.smul_mem _ _ hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ht
  refine h₀ t (fun c ↦ show A from a c) ?_
  have e : ∑ c ∈ t, (show A from a c) • f c = hwBar hR Λ y + hwBar hR Λ z -
      ∑ c ∈ t, (show A from a c) • (hwBar hR Λ (f c) - f c) := by
    rw [← map_add, hyz, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [hwBar_local_smul, smul_sub, sub_sub_cancel]
  rw [e]
  refine sub_mem (add_mem (Submodule.mem_sup_left ((mem_localX_smul_latBar_iff hR Λ y).1 hy))
    (Submodule.mem_sup_right ((Submodule.restrictScalars_mem _ _ _).2
      (hW z ((Submodule.restrictScalars_mem _ _ _).1 hz)))))
    (Submodule.sum_mem _ fun c _ ↦ Submodule.mem_sup_right ?_)
  exact (Submodule.restrictScalars_mem _ _ _).2 (Submodule.smul_of_tower_mem _ _ (hfb c))

end Strings

/-- `ẽᵢG(b) ∈ v⁻¹L(∞)` when `ẽᵢb = 0`. -/
lemma kE_negLift_mem {μ : I →₀ ℕ} (h : NegGlobalAt D μ) (i : I)
    (w : {w : List I // wordWeight w = μ})
    (hw : kE hvt i (fWi (D := D) hvt w.1) ∈ ϖ • latInf (D := D) hvt A) :
    kE hvt i (negLift h w) ∈ ϖ • latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  rw [← sub_add_cancel (negLift h w) (fWi hvt w.1), map_add]
  exact add_mem (kashiwaraE_mem_smul_latInf (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum i (negLift_sub_mem h w)) hw

/-! ### [Kas91] Prop. 7.4.1 -/

section Statement

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

variable {R : D.RootDatum Y} (hR : R.IsXRegular)

/-- The induction hypothesis of [Kas91] §7 used in the proof of Prop. 7.4.1, at the weights
`μ < ν`: `(G.1)` at `μ`; the vanishing `G(b)u_λ = 0` for `π̄_λ(b) = 0` of Lemma 7.5.2 at `μ`, for
every dominant `λ`; and `(G.3)` for `n = 1` at `μ`: `G(b) ∈ (fᵢU⁻)^ℤ` whenever `ẽᵢb ≠ 0`. -/
def GlobalBelow (ν : I →₀ ℕ) : Prop :=
  ∀ μ, μ ≤ ν → μ ≠ ν → ∃ h : NegGlobalAt D μ,
    (∀ (Λ : Dom R) (w : {w : List I // wordWeight w = μ}),
      fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ → evq hvt Λ (negLift h w) = 0) ∧
    ∀ (i : I) (w : {w : List I // wordWeight w = μ}),
      kE hvt i (fWi (D := D) hvt w.1) ∉ ϖ • latInf (D := D) hvt A →
        negLift h w ∈ negFilt D i 1 μ

/-- **[Kas91] Prop. 7.4.1** at `(λ, i, n, ν)`, in basis form: `(fᵢⁿV(λ))^ℤ_{λ-ν}` is the `𝒜`-span
of vectors `g_k ∈ (fᵢⁿV(λ))^ℤ_{λ-ν}` with independent residues in `L(λ)/v⁻¹L(λ)` and in
`L(λ)⁻/vL(λ)⁻`, whose residues are the elements `f̃ᵢⁿ f̃_{u_k} u_λ` of `f̃ᵢⁿB(λ)`, with words
`iⁿu_k` of weight `ν`. -/
def HwFiltGlobalAt (Λ : Dom R) (i : I) (n : ℕ) (ν : I →₀ ℕ) : Prop :=
  ∃ (ι : Type u) (g : ι → IrreducibleModule R 𝕧 Λ.1) (u : ι → List I),
    (∀ k, g k ∈ hwFilt Λ i n ν) ∧
    ResidueIndependent A (lat hvt hR A Λ) ϖ g ∧
    ResidueIndependent LocalRing (latBar hR Λ) localX g ∧
    (∀ x ∈ hwFilt Λ i n ν, x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g)) ∧
    (∀ k, g k - fW hvt hR Λ (List.replicate n i ++ u k) ∈ ϖ • lat hvt hR A Λ) ∧
    ∀ k, wordWeight (List.replicate n i ++ u k) = ν

/-- `(fᵢⁿV(λ))^ℤ_{λ-ν} = 0` for `n > νᵢ`: the empty family. -/
lemma hwFiltGlobalAt_of_lt (Λ : Dom R) (i : I) {n : ℕ} {ν : I →₀ ℕ} (hn : ν i < n) :
    HwFiltGlobalAt hR Λ i n ν := by
  refine ⟨PEmpty.{u + 1}, PEmpty.elim, PEmpty.elim, fun k ↦ k.elim,
    ⟨fun k ↦ k.elim, fun _ _ _ k ↦ k.elim⟩, ⟨fun k ↦ k.elim, fun _ _ _ k ↦ k.elim⟩,
    fun x hx ↦ ?_, fun k ↦ k.elim, fun k ↦ k.elim⟩
  rw [hwFilt_eq_bot Λ hn hx]
  exact zero_mem _

/-- The reduction step of [Kas91] Prop. 7.4.1: if `n + ⟨hᵢ, λ - ν⟩ < 0`, the statement for
`n + 1` gives the statement for `n`. -/
lemma hwFiltGlobalAt_of_neg {Λ : Dom R} {i : I} {n : ℕ} {ν : I →₀ ℕ}
    (hneg : (Λ.1 - R.rootSum ν) (R.coroot i) + n < 0) (h : HwFiltGlobalAt hR Λ i (n + 1) ν) :
    HwFiltGlobalAt hR Λ i n ν := by
  obtain ⟨ι, g, u, hgF, hg₀, hg₁, hspan, hgu, hgw⟩ := h
  have e : ∀ k, List.replicate n i ++ i :: u k = List.replicate (n + 1) i ++ u k := fun k ↦ by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]
  refine ⟨ι, g, fun k ↦ i :: u k, fun k ↦ hwFilt_antitone Λ i (Nat.le_succ n) ν (hgF k), hg₀,
    hg₁, fun x hx ↦ hspan x (hwFilt_le_succ hR Λ i hneg hx), fun k ↦ ?_, fun k ↦ ?_⟩
  · rw [e]; exact hgu k
  · rw [e]; exact hgw k

variable (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

include hfund in
/-- The main step of [Kas91] Prop. 7.4.1, for `1 ≤ n ≤ νᵢ` and `n + ⟨hᵢ, λ - ν⟩ ≥ 0`: the
statement for `n + 1` and the induction hypothesis at `μ = ν - nαᵢ` give the statement for `n`. -/
theorem hwFiltGlobalAt_step {Λ : Dom R} {i : I} {n : ℕ} {ν : I →₀ ℕ} (hn : n ≤ ν i)
    (hpos : 0 ≤ (Λ.1 - R.rootSum ν) (R.coroot i) + n)
    (h : NegGlobalAt D (ν - Finsupp.single i n))
    (hvan : ∀ w : {w : List I // wordWeight w = ν - Finsupp.single i n},
      fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ → evq hvt Λ (negLift h w) = 0)
    (hG3 : ∀ w : {w : List I // wordWeight w = ν - Finsupp.single i n},
      kE hvt i (fWi (D := D) hvt w.1) ∉ ϖ • latInf (D := D) hvt A →
        negLift h w ∈ negFilt D i 1 (ν - Finsupp.single i n))
    (hP : HwFiltGlobalAt hR Λ i (n + 1) ν) : HwFiltGlobalAt hR Λ i n ν := by
  classical
  set μ := ν - Finsupp.single i n with hμ
  obtain ⟨ι, g, u, hgF, hg₀, hg₁, hspan, hgu, hgw⟩ := hP
  set N := Submodule.span (LaurentPolynomial ℤ) (Set.range g) with hN
  have hNF : ∀ x ∈ hwFilt Λ i (n + 1) ν, x ∈ N := hspan
  have hFN : ∀ x ∈ N, x ∈ hwFilt Λ i (n + 1) ν := fun x hx ↦
    (Submodule.span_le.2 (Set.range_subset_iff.2 hgF)) hx
  have hNK : ∀ x ∈ N, x ∈ Submodule.span 𝕂 (Set.range g) := fun x hx ↦
    mem_span_field_of_mem_span_laurent (hw_laurent_smul_eq Λ) hx
  have hsl : ∀ {x : IrreducibleModule R 𝕧 Λ.1}, x ∈ ϖ • lat hvt hR A Λ → x ∈ lat hvt hR A Λ :=
    fun hx ↦ Submodule.smul_le_self_of_tower ϖ _ hx
  -- the elements `b` of `B(λ)_{λ-μ}` with `ẽᵢb = 0` in `B(∞)`
  let T := {c : hwCrystal hR Λ μ //
    kE hvt i (fWi (D := D) hvt (Quotient.out c).1) ∈ ϖ • latInf (D := D) hvt A}
  let w : T → {w : List I // wordWeight w = μ} := fun c ↦
    ⟨(Quotient.out c.1).1, (Quotient.out c.1).2.1⟩
  let G : T → Um D 𝕧 := fun c ↦ negLift h (w c)
  let fc : T → IrreducibleModule R 𝕧 Λ.1 := fun c ↦ evq hvt Λ ((bosv i).df n (G c))
  let f' : T → IrreducibleModule R 𝕧 Λ.1 := fun c ↦
    evq hvt Λ ((bosv i).df n (comp hvt i 0 (G c)))
  have hGZ : ∀ c, G c ∈ negIntegral D := fun c ↦ (negLift_mem h (w c)).1
  have hGw : ∀ c, G c ∈ Uw D 𝕧 μ := fun c ↦ (negLift_mem h (w c)).2.1
  have hcZ : ∀ c, comp hvt i 0 (G c) ∈ negIntegral D := fun c ↦
    negative_component_mem_integral D i (hGZ c) 0
  have hcw : ∀ c, comp hvt i 0 (G c) ∈ Uw D 𝕧 μ := fun c ↦ by
    simpa using @component_mem_Uw _ _ _ _ D _ _ _ transcendental_ratFunc_X i _ (G c) (hGw c) 0
  have hf'F : ∀ c, f' c ∈ hwFilt Λ i n ν := fun c ↦
    evq_mem_hwFilt Λ (df_mem_negFilt D i le_rfl hn (hcZ c) (hcw c))
  -- (6.1.2)
  have hfcF : ∀ c, fc c - f' c ∈ hwFilt Λ i (n + 1) ν := fun c ↦ by
    rw [← map_sub]
    exact evq_mem_hwFilt Λ (df_sub_df_comp_mem_negFilt D i hn (hGZ c) (hGw c))
  -- `fᵢ^{(n)} PᵢG(b) u_λ ≡ f̃ᵢⁿ π̄_λ(b)`
  have hf'sub : ∀ c, f' c - fW hvt hR Λ (List.replicate n i ++ (w c).1) ∈
      ϖ • lat hvt hR A Λ := by
    intro c
    have h1 := df_comp_sub_kF_pow_mem D i n (kE_negLift_mem h i (w c) c.2)
    have h2 := kF_pow_mem_smul_latInf D i n (negLift_sub_mem h (w c))
    rw [map_sub, kF_pow_fWi] at h2
    have h3 : evq hvt Λ (fWi hvt (List.replicate n i ++ (w c).1)) -
        fW hvt hR Λ (List.replicate n i ++ (w c).1) ∈ ϖ • lat hvt hR A Λ :=
      evq_fWord_sub_fW_mem InfinityLocalRing.injective_algebraMap
        InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
        InfinityLocalRing.exists_pow_mul hfund _ Λ
    have e : f' c - fW hvt hR Λ (List.replicate n i ++ (w c).1) =
        evq hvt Λ ((bosv i).df n (comp hvt i 0 (G c)) - (kF hvt i ^ n) (G c)) +
        evq hvt Λ ((kF hvt i ^ n) (G c) - fWi hvt (List.replicate n i ++ (w c).1)) +
        (evq hvt Λ (fWi hvt (List.replicate n i ++ (w c).1)) -
          fW hvt hR Λ (List.replicate n i ++ (w c).1)) := by
      simp only [map_sub, f']; abel
    rw [e]
    exact add_mem (add_mem (evq_mem_smul_lat' hfund h1 Λ) (evq_mem_smul_lat' hfund h2 Λ)) h3
  have hf'L : ∀ c, f' c ∈ lat hvt hR A Λ := fun c ↦ by
    rw [← sub_add_cancel (f' c) (fW hvt hR Λ _)]
    exact add_mem (hsl (hf'sub c)) (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A _)
  -- bar-invariance
  have hfcbar : ∀ c, hwBar hR Λ (fc c) = fc c := fun c ↦ by
    change hwBar hR Λ (evq hvt Λ ((bosv i).df n (negLift h (w c)))) = _
    rw [hwBar_evq, negBar_df, negBar_eq_of_mem h (negLift_mem h (w c))]
  have hf'bar : ∀ c, hwBar hR Λ (f' c) - f' c ∈ hwFilt Λ i (n + 1) ν := fun c ↦ by
    have e : hwBar hR Λ (f' c) - f' c = (fc c - f' c) - hwBar hR Λ (fc c - f' c) := by
      rw [map_sub, hfcbar]; abel
    rw [e]
    exact sub_mem (hfcF c) (hwBar_mem_hwFilt hR Λ (hfcF c))
  -- residues: `f̃ᵢⁿb ≠ 0`, and distinct `b` give distinct `f̃ᵢⁿb`
  have hwc0 : ∀ c, fW hvt hR Λ (w c).1 ∉ ϖ • lat hvt hR A Λ := fun c ↦ (Quotient.out c.1).2.2
  have hwce : ∀ c, eK hvt hR Λ i (fW hvt hR Λ (w c).1) ∈ ϖ • lat hvt hR A Λ := fun c ↦ by
    have h1 := evq_kE_fWi_sub_mem InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
      InfinityLocalRing.exists_pow_mul hfund i (hwc0 c)
    have h2 : evq hvt Λ (kE hvt i (fWi (D := D) hvt (w c).1)) ∈ ϖ • lat hvt hR A Λ :=
      evq_mem_smul_lat' hfund c.2 Λ
    have := sub_mem h2 h1
    rwa [sub_sub_cancel] at this
  have hμν : μ + Finsupp.single i n = ν := sub_single_add_single hn
  have hbound : (n : ℤ) ≤ (Λ.1 - R.rootSum μ) (R.coroot i) := by
    have e : (Λ.1 - R.rootSum ν) (R.coroot i) =
        (Λ.1 - R.rootSum μ) (R.coroot i) - 2 * n := by
      rw [← hμν, R.rootSum_add, R.rootSum_single]
      simp [R.root_coroot, D.cartanMatrix_self]
      ring
    omega
  have hwcn : ∀ c, fW hvt hR Λ (List.replicate n i ++ (w c).1) ∉ ϖ • lat hvt hR A Λ :=
    fun c ↦ fW_replicate_append_notMem hfund Λ i (hwc0 c) (hwce c) (by rw [(w c).2]; exact hbound)
  have hwinj : ∀ c c', fW hvt hR Λ (w c).1 - fW hvt hR Λ (w c').1 ∈ ϖ • lat hvt hR A Λ →
      c = c' := by
    intro c c' hcc
    refine Subtype.ext ?_
    rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]
    exact Quotient.sound hcc
  have hr₀ := dvd_of_sum_mem_sup hfund i n (fun c ↦ (w c).1) u f' g hwc0 hwce hwinj hwcn hf'sub
    hg₀ hgu
  have hr₁ := dvd_of_sum_mem_sup_bar f' g (fun c ↦ hNK _ (hNF _ (hf'bar c)))
    (fun k ↦ hNK _ (hNF _ (hwBar_mem_hwFilt hR Λ (hgF k)))) hr₀
  -- [Kas91] Lemma 7.1.2
  have hf₀ : ∀ c, ∃ l ∈ lat hvt hR A Λ, f' c - l ∈ N := fun c ↦
    ⟨f' c, hf'L c, by rw [sub_self]; exact zero_mem _⟩
  have hf₁ : ∀ c, ∃ l ∈ latBar hR Λ, f' c - l ∈ N := fun c ↦
    ⟨hwBar hR Λ (f' c), (mem_latBar_iff hR Λ _).2 (by rw [hwBar_hwBar]; exact hf'L c),
      by rw [← neg_sub]; exact neg_mem (hNF _ (hf'bar c))⟩
  obtain ⟨y, hyN, hy₀, hy₁⟩ := exists_residueIndependent_extension (hw_laurent_smul_eq Λ) hg₀ hg₁
    f' hf₀ hf₁ hr₀ hr₁
  -- correct the lifts by `ℤ`-combinations of the `g_k` so that their residues are `f̃ᵢⁿb`
  have hz : ∀ c, ∃ z ∈ Submodule.span ℤ (Set.range g), (y c - f' c) - z ∈ ϖ • lat hvt hR A Λ :=
    fun c ↦ exists_int_sub_mem_of_mem_span (hw_laurent_smul_eq Λ) hg₀ (hyN c)
      (sub_mem (hy₀.1 (Sum.inr c)) (hf'L c))
  choose z hzZ hzsub using hz
  have hZ : ∀ x ∈ Submodule.span ℤ (Set.range g),
      x ∈ lat hvt hR A Λ ∧ x ∈ latBar hR Λ ∧ x ∈ N := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact ⟨hg₀.1 k, hg₁.1 k, Submodule.subset_span ⟨k, rfl⟩⟩
    | zero => exact ⟨zero_mem _, zero_mem _, zero_mem _⟩
    | add x x' _ _ hx hx' =>
      exact ⟨add_mem hx.1 hx'.1, add_mem hx.2.1 hx'.2.1, add_mem hx.2.2 hx'.2.2⟩
    | smul m x _ hx => exact ⟨zsmul_mem hx.1 m, zsmul_mem hx.2.1 m, zsmul_mem hx.2.2 m⟩
  let y' : T → IrreducibleModule R 𝕧 Λ.1 := fun c ↦ y c - z c
  have hy'f : ∀ c, y' c - f' c ∈ N := fun c ↦ by
    have e : y' c - f' c = (y c - f' c) - z c := by simp only [y']; abel
    rw [e]
    exact sub_mem (hyN c) (hZ _ (hzZ c)).2.2
  have hr₀' : ResidueIndependent A (lat hvt hR A Λ) ϖ (Sum.elim g y') :=
    hg₀.sumElim ((Submodule.span 𝕂 (Set.range g)).restrictScalars A)
      (fun k ↦ (Submodule.restrictScalars_mem _ _ _).2
        (Submodule.subset_span (Set.mem_range_self k)))
      (fun c ↦ sub_mem (hy₀.1 (Sum.inr c)) (hZ _ (hzZ c)).1)
      (residueIndependent_mod_of_sub_mem _
        (fun c ↦ (Submodule.restrictScalars_mem _ _ _).2 (hNK _ (hy'f c))) hr₀)
  have hr₁' : ResidueIndependent LocalRing (latBar hR Λ) localX (Sum.elim g y') :=
    hg₁.sumElim ((Submodule.span 𝕂 (Set.range g)).restrictScalars LocalRing)
      (fun k ↦ (Submodule.restrictScalars_mem _ _ _).2
        (Submodule.subset_span (Set.mem_range_self k)))
      (fun c ↦ sub_mem (hy₁.1 (Sum.inr c)) (hZ _ (hzZ c)).2.1)
      (residueIndependent_mod_of_sub_mem _
        (fun c ↦ (Submodule.restrictScalars_mem _ _ _).2 (hNK _ (hy'f c))) hr₁)
  refine ⟨ι ⊕ T, Sum.elim g y', Sum.elim (fun k ↦ i :: u k) (fun c ↦ (w c).1), ?_, hr₀', hr₁',
    ?_, ?_, ?_⟩
  · rintro (k | c)
    · exact hwFilt_antitone Λ i (Nat.le_succ n) ν (hgF k)
    · change y' c ∈ _
      rw [← sub_add_cancel (y' c) (f' c)]
      exact add_mem (hwFilt_antitone Λ i (Nat.le_succ n) ν (hFN _ (hy'f c))) (hf'F c)
  · -- spanning: `(fᵢⁿV(λ))^ℤ = Σ_{b ∈ S} 𝒜 fᵢ^{(n)}G(b)u_λ + (fᵢ^{n+1}V(λ))^ℤ`
    set S' := Submodule.span (LaurentPolynomial ℤ) (Set.range (Sum.elim g y'))
    have hgS : ∀ x ∈ N, x ∈ S' := fun x hx ↦ Submodule.span_mono (by
      rintro _ ⟨k, rfl⟩; exact ⟨Sum.inl k, rfl⟩) hx
    have hfcS : ∀ c, fc c ∈ S' := fun c ↦ by
      have e : fc c = (fc c - f' c) - (y' c - f' c) + y' c := by abel
      rw [e]
      exact add_mem (sub_mem (hgS _ (hNF _ (hfcF c))) (hgS _ (hy'f c)))
        (Submodule.subset_span ⟨Sum.inr c, rfl⟩)
    have hGS : ∀ w' : {w : List I // wordWeight w = μ},
        evq hvt Λ ((bosv i).df n (negLift h w')) ∈ S' := by
      intro w'
      by_cases hw0 : fW hvt hR Λ w'.1 ∈ ϖ • lat hvt hR A Λ
      · rw [evq_df (hR := hR), hvan w' hw0, map_zero]
        exact zero_mem _
      let b : hwCrystal hR Λ μ := ⟦⟨w'.1, w'.2, hw0⟩⟧
      have hrel : fW hvt hR Λ (Quotient.out b).1 - fW hvt hR Λ w'.1 ∈ ϖ • lat hvt hR A Λ :=
        Quotient.mk_out (s := hwCrystalSetoid hR Λ μ) ⟨w'.1, w'.2, hw0⟩
      have hi := fWi_sub_mem_of_fW_sub_mem InfinityLocalRing.injective_algebraMap
        InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
        InfinityLocalRing.exists_pow_mul hfund _ w'.1 (Quotient.out b).1 rfl hw0
        (by rw [← neg_sub]; exact neg_mem hrel)
      rw [negLift_eq_of_sub_mem h (w' := ⟨(Quotient.out b).1, (Quotient.out b).2.1⟩) hi]
      by_cases hb : kE hvt i (fWi (D := D) hvt (Quotient.out b).1) ∈ ϖ • latInf (D := D) hvt A
      · exact hfcS ⟨b, hb⟩
      · exact hgS _ (hNF _ (evq_mem_hwFilt Λ (df_mem_negFilt_succ D i hn (hG3 _ hb))))
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, y₀, hnk, hk, hy₀Z, hy₀w, rfl⟩ := hx
      rcases Nat.lt_or_ge n k with hlt | hle
      · exact hgS _ (hNF _ (evq_mem_hwFilt Λ (df_mem_negFilt D i hlt hk hy₀Z hy₀w)))
      have hkn : k = n := le_antisymm hle hnk
      rw [hkn] at hy₀w ⊢
      have hsp := mem_span_negLift h hy₀Z hy₀w
      clear hy₀Z hy₀w
      induction hsp using Submodule.span_induction with
      | mem z hz => obtain ⟨w', rfl⟩ := hz; exact hGS w'
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add a a' _ _ ha ha' => rw [map_add, map_add]; exact add_mem ha ha'
      | smul c a _ ha =>
        rw [laurent_smul_eq, map_smul, map_smul, ← hw_laurent_smul_eq]
        exact Submodule.smul_mem _ c ha
    | zero => rw [map_zero]; exact zero_mem _
    | add a a' _ _ ha ha' => rw [map_add]; exact add_mem ha ha'
    | smul c a _ ha =>
      rw [laurent_smul_eq, map_smul, ← hw_laurent_smul_eq]
      exact Submodule.smul_mem _ c ha
  · rintro (k | c)
    · change g k - fW hvt hR Λ (List.replicate n i ++ i :: u k) ∈ _
      have e : List.replicate n i ++ i :: u k = List.replicate (n + 1) i ++ u k := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [e]
      exact hgu k
    · change y c - z c - fW hvt hR Λ (List.replicate n i ++ (w c).1) ∈ _
      have e : y c - z c - fW hvt hR Λ (List.replicate n i ++ (w c).1) =
          ((y c - f' c) - z c) + (f' c - fW hvt hR Λ (List.replicate n i ++ (w c).1)) := by abel
      rw [e]
      exact add_mem (hzsub c) (hf'sub c)
  · rintro (k | c)
    · change wordWeight (List.replicate n i ++ i :: u k) = ν
      rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ']
      exact hgw k
    · change wordWeight (List.replicate n i ++ (w c).1) = ν
      rw [LusztigF.wordWeight_append, GrandLoop.wordWeight_replicate, (w c).2, ← hμν, add_comm]
      simp

include hfund in
/-- **[Kas91] Prop. 7.4.1.** Under the induction hypothesis of [Kas91] §7 at the weights below
`ν`, for every dominant `λ`, `i ∈ I` and `n ≥ 1`, `(fᵢⁿV(λ))^ℤ_{λ-ν}` is the `𝒜`-span of a
family with independent residues on both sides, whose residues lie in `f̃ᵢⁿB(λ)`
(`HwFiltGlobalAt`). Kashiwara's proof, by descending induction on `n`. -/
theorem hwFiltGlobalAt {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (Λ : Dom R) (i : I) {n : ℕ}
    (hn : 1 ≤ n) : HwFiltGlobalAt hR Λ i n ν := by
  suffices H : ∀ t n, 1 ≤ n → ν i < n + t → HwFiltGlobalAt hR Λ i n ν from
    H (ν i + 1) n hn (by omega)
  intro t
  induction t with
  | zero => intro n _ h; exact hwFiltGlobalAt_of_lt hR Λ i (by simpa using h)
  | succ t ih =>
    intro n hn ht
    by_cases hlt : ν i < n
    · exact hwFiltGlobalAt_of_lt hR Λ i hlt
    have hP := ih (n + 1) (by omega) (by omega)
    by_cases hneg : (Λ.1 - R.rootSum ν) (R.coroot i) + n < 0
    · exact hwFiltGlobalAt_of_neg hR hneg hP
    obtain ⟨h, hvan, hG3⟩ := hIH (ν - Finsupp.single i n) tsub_le_self (by
      intro e
      have := congrArg (fun μ : I →₀ ℕ ↦ μ i) e
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at this
      omega)
    exact hwFiltGlobalAt_step hR hfund (by omega) (by omega) h (hvan Λ) (hG3 i) hP

include hfund in
/-- Injectivity in [Kas91] Prop. 7.4.1: an element of `(fᵢⁿV(λ))^ℤ_{λ-ν} ∩ v⁻¹L(λ) ∩ L(λ)⁻`
vanishes. -/
theorem hwFilt_eq_zero_of_mem {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (Λ : Dom R) (i : I) {n : ℕ}
    (hn : 1 ≤ n) {x : IrreducibleModule R 𝕧 Λ.1} (hx : x ∈ hwFilt Λ i n ν)
    (hxϖ : x ∈ ϖ • lat hvt hR A Λ) (hx₁ : x ∈ latBar hR Λ) : x = 0 := by
  obtain ⟨ι, g, u, -, hg₀, hg₁, hspan, -, -⟩ := hwFiltGlobalAt hR hfund hIH Λ i hn
  exact balanced_eq_zero_of_mem_span (hw_laurent_smul_eq Λ) hg₀ hg₁ (hspan x hx) hxϖ hx₁

include hfund in
/-- Surjectivity in [Kas91] Prop. 7.4.1: every element of `(fᵢⁿV(λ))^ℤ_{λ-ν} ∩ L(λ)` is congruent
modulo `v⁻¹L(λ)` to an element of `(fᵢⁿV(λ))^ℤ_{λ-ν} ∩ L(λ) ∩ L(λ)⁻`. -/
theorem exists_hwFilt_sub_mem {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (Λ : Dom R) (i : I)
    {n : ℕ} (hn : 1 ≤ n) {x : IrreducibleModule R 𝕧 Λ.1} (hx : x ∈ hwFilt Λ i n ν)
    (hx₀ : x ∈ lat hvt hR A Λ) :
    ∃ y ∈ hwFilt Λ i n ν, y ∈ lat hvt hR A Λ ∧ y ∈ latBar hR Λ ∧
      x - y ∈ ϖ • lat hvt hR A Λ := by
  obtain ⟨ι, g, u, hgF, hg₀, hg₁, hspan, -, -⟩ := hwFiltGlobalAt hR hfund hIH Λ i hn
  obtain ⟨y, hy, hxy⟩ := exists_int_sub_mem_of_mem_span (hw_laurent_smul_eq Λ) hg₀
    (hspan x hx) hx₀
  have key : ∀ y ∈ Submodule.span ℤ (Set.range g),
      y ∈ hwFilt Λ i n ν ∧ y ∈ lat hvt hR A Λ ∧ y ∈ latBar hR Λ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact ⟨hgF k, hg₀.1 k, hg₁.1 k⟩
    | zero => exact ⟨zero_mem _, zero_mem _, zero_mem _⟩
    | add y y' _ _ hy hy' => exact ⟨add_mem hy.1 hy'.1, add_mem hy.2.1 hy'.2.1,
        add_mem hy.2.2 hy'.2.2⟩
    | smul m y _ hy => exact ⟨zsmul_mem hy.1 m, zsmul_mem hy.2.1 m, zsmul_mem hy.2.2 m⟩
  exact ⟨y, (key y hy).1, (key y hy).2.1, (key y hy).2.2, hxy⟩

end Statement

end LieLean.QuantumGroup
