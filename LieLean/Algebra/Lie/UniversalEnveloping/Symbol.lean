/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.Domain
import LieLean.Algebra.Lie.UniversalEnveloping.PBW

/-!
# Symbols in the universal enveloping algebra

`UniversalEnvelopingAlgebra.HasSymbol k s u` says that `u ∈ Fₖ U(L)` (the PBW filtration) and that
the class of `u` in `Fₖ / Fₖ₋₁ ⊆ gr U(L)` is `s`. Symbols are multiplicative
(`HasSymbol.mul`, `HasSymbol.pow`), two elements with the same symbol in degree `k + 1` differ by
an element of `Fₖ` (`HasSymbol.sub_mem`), and for `L` free over a domain, right multiplication by
an element with a nonzero symbol of degree one lowers no filtration degree
(`mem_filtration_of_mul_pow_mem`).

These are the degree arguments in the proof of Shapovalov's theorem ([HumO] §4.13): there
"degree" is the degree of a PBW monomial, i.e. the PBW filtration.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.12–4.13.
-/

noncomputable section

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- `u ∈ Fₖ U(L)` and the class of `u` in `Fₖ / Fₖ₋₁ ⊆ gr U(L)` is `s`. -/
def HasSymbol (k : ℕ) (s : AssociatedGraded R L) (u : UniversalEnvelopingAlgebra R L) : Prop :=
  ∃ h : u ∈ filtration R L k, toGr R L k ⟨u, h⟩ = s

namespace HasSymbol

variable {k m n : ℕ} {s t : AssociatedGraded R L} {u w : UniversalEnvelopingAlgebra R L}

lemma mem (h : HasSymbol k s u) : u ∈ filtration R L k := h.1

lemma of_mem (h : u ∈ filtration R L k) : HasSymbol k (toGr R L k ⟨u, h⟩) u := ⟨h, rfl⟩

lemma mul (hu : HasSymbol m s u) (hw : HasSymbol n t w) : HasSymbol (m + n) (s * t) (u * w) := by
  obtain ⟨hu, rfl⟩ := hu
  obtain ⟨hw, rfl⟩ := hw
  exact ⟨mul_mem_filtration hu hw, (toGr_mul _ _).symm⟩

lemma one : HasSymbol 0 1 (1 : UniversalEnvelopingAlgebra R L) :=
  ⟨one_mem_filtration 0, toGr_zero_one⟩

lemma pow (hu : HasSymbol m s u) (q : ℕ) : HasSymbol (m * q) (s ^ q) (u ^ q) := by
  induction q with
  | zero => simpa using (one : HasSymbol 0 1 (1 : UniversalEnvelopingAlgebra R L))
  | succ q ih => simpa [pow_succ, Nat.mul_succ] using ih.mul hu

lemma congr_deg (h : HasSymbol k s u) (hk : k = m) : HasSymbol m s u := hk ▸ h

lemma smul (h : HasSymbol k s u) (c : R) : HasSymbol k (c • s) (c • u) := by
  obtain ⟨hu, rfl⟩ := h
  exact ⟨Submodule.smul_mem _ c hu, by rw [← map_smul]; rfl⟩

lemma sub (hu : HasSymbol k s u) (hw : HasSymbol k t w) : HasSymbol k (s - t) (u - w) := by
  obtain ⟨hu, rfl⟩ := hu
  obtain ⟨hw, rfl⟩ := hw
  exact ⟨sub_mem hu hw, by rw [← map_sub]; rfl⟩

lemma add (hu : HasSymbol k s u) (hw : HasSymbol k t w) : HasSymbol k (s + t) (u + w) := by
  obtain ⟨hu, rfl⟩ := hu
  obtain ⟨hw, rfl⟩ := hw
  exact ⟨add_mem hu hw, by rw [← map_add]; rfl⟩

/-- An element of `Fₖ` has symbol `0` in degree `k + 1`. -/
lemma zero_of_mem (h : u ∈ filtration R L k) : HasSymbol (k + 1) 0 u :=
  ⟨filtration_mono (Nat.le_succ k) h, (toGr_succ_eq_zero_iff _).mpr h⟩

/-- Two elements with the same symbol in degree `k + 1` differ by an element of `Fₖ`. -/
lemma sub_mem (hu : HasSymbol (k + 1) s u) (hw : HasSymbol (k + 1) s w) :
    u - w ∈ filtration R L k := by
  obtain ⟨h, h0⟩ := hu.sub hw
  rw [sub_self] at h0
  exact (toGr_succ_eq_zero_iff ⟨u - w, h⟩).mp h0

/-- Adding an element of `Fₖ` does not change the symbol in degree `k + 1`. -/
lemma of_sub_mem (hw : HasSymbol (k + 1) s w) (h : u - w ∈ filtration R L k) :
    HasSymbol (k + 1) s u := by
  simpa using (zero_of_mem h).add hw

lemma ne_zero (h : HasSymbol k s u) (hs : s ≠ 0) : u ≠ 0 := by
  rintro rfl
  obtain ⟨h0, rfl⟩ := h
  exact hs (by rw [show (⟨0, h0⟩ : filtration R L k) = 0 from rfl, map_zero])

/-- An element with a nonzero symbol in degree `k + 1` does not lie in `Fₖ`. -/
lemma not_mem (h : HasSymbol (k + 1) s u) (hs : s ≠ 0) : u ∉ filtration R L k := fun hu ↦
  hs (by obtain ⟨h', rfl⟩ := h; exact (toGr_succ_eq_zero_iff _).mpr hu)

end HasSymbol

/-- The symbol of `ι x` in degree one. -/
lemma hasSymbol_ι (x : L) : HasSymbol 1 (toGr R L 1 ⟨ι R x, ι_mem_filtration_one x⟩) (ι R x) :=
  HasSymbol.of_mem _

/-- For `L` free and `x ≠ 0`, the symbol of `ι x` in degree one is nonzero. -/
lemma toGr_ι_ne_zero [Nontrivial R] [Module.Free R L] {x : L} (hx : x ≠ 0) :
    toGr R L 1 ⟨ι R x, ι_mem_filtration_one x⟩ ≠ 0 := by
  rw [ne_eq, toGr_succ_eq_zero_iff, mem_filtration_zero]
  rintro ⟨r, hr⟩
  have h := congrArg (lift R (0 : L →ₗ⁅R⁆ R)) hr
  rw [AlgHom.commutes, lift_ι_apply, Algebra.algebraMap_self, RingHom.id_apply,
    LieHom.zero_apply] at h
  rw [h, map_zero] at hr
  exact hx (ι_injective R L (by rw [← hr, LieHom.map_zero]))

instance instNoZeroDivisorsAssociatedGraded [NoZeroDivisors R] [Module.Free R L] :
    NoZeroDivisors (AssociatedGraded R L) :=
  (symmetricAlgebraEquivAssociatedGraded R L).symm.toMulEquiv.noZeroDivisors

/-- If `y` has a nonzero symbol in degree one and `u yᵠ ∈ Fₘ₊ᵩ`, then `u ∈ Fₘ`. -/
theorem mem_filtration_of_mul_pow_mem [NoZeroDivisors R] [Module.Free R L]
    {y : UniversalEnvelopingAlgebra R L} {t : AssociatedGraded R L} (hy : HasSymbol 1 t y)
    (ht : t ≠ 0) {u : UniversalEnvelopingAlgebra R L} {m q : ℕ}
    (h : u * y ^ q ∈ filtration R L (m + q)) : u ∈ filtration R L m := by
  by_contra hum
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hum (Submodule.zero_mem _)
  obtain ⟨e, he, hne⟩ := exists_toGr_ne_zero hu0
  have hme : m < e := by
    by_contra hle
    exact hum (filtration_mono (not_lt.mp hle) he)
  have hsym := (HasSymbol.of_mem he).mul (hy.pow q)
  rw [one_mul] at hsym
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hsym' : HasSymbol (e' + q + 1) _ (u * y ^ q) := hsym.congr_deg (by omega)
  exact hsym'.not_mem (mul_ne_zero hne (pow_ne_zero q ht))
    (filtration_mono (by omega) h)

end UniversalEnvelopingAlgebra
