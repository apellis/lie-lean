/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.Sl2

/-!
# Locally nilpotent adjoint actions

An element `x` of a Lie algebra `L` acts locally nilpotently on `L` (i.e. `ad x` is locally
nilpotent) if every `y ∈ L` is killed by some power of `ad x`, i.e. if the Engel subalgebra
`LieSubalgebra.engel R x` is everything. Since the Engel subalgebra is a Lie subalgebra (by the
Leibniz rule `LieAlgebra.ad_pow_lie`), it suffices to check this on a generating set.

We also record the `𝔰𝔩₂` fact that the eigenvalue of a primitive vector on which the lowering
operator acts nilpotently is a natural number (a variant of
`IsSl2Triple.HasPrimitiveVectorWith.exists_nat`, which assumes finite-dimensionality instead).

## Main results

* `LieSubalgebra.engel_eq_top_of_lieSpan_eq_top`: if `ad x` is locally nilpotent on a generating
  set of `L`, it is locally nilpotent on `L`.
* `LieSubalgebra.engel_eq_top_of_surjective`: local nilpotency passes to quotients.
* `IsSl2Triple.HasPrimitiveVectorWith.exists_nat_of_exists_pow_eq_zero`: if `m` is a primitive
  vector of weight `μ` for an `𝔰𝔩₂`-triple `(h, e, f)` and `f^n m = 0` for some `n`, then `μ` is a
  natural number.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.2, §3.4.
-/

open LieAlgebra LieModule

namespace LieSubalgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L']

/-- If `ad x` is locally nilpotent on a set generating `L` as a Lie algebra, then `ad x` is locally
nilpotent on `L`. -/
theorem engel_eq_top_of_lieSpan_eq_top {s : Set L} (hs : lieSpan R L s = ⊤) (x : L)
    (hx : ∀ y ∈ s, ∃ n : ℕ, (ad R L x ^ n) y = 0) : engel R x = ⊤ := by
  rw [eq_top_iff, ← hs, lieSpan_le]
  intro y hy
  exact (mem_engel_iff R x y).mpr (hx y hy)

/-- If `ad x` is locally nilpotent on a set generating `L` as a Lie algebra, then every `y ∈ L` is
killed by a power of `ad x`. -/
theorem exists_ad_pow_eq_zero_of_lieSpan_eq_top {s : Set L} (hs : lieSpan R L s = ⊤) (x : L)
    (hx : ∀ y ∈ s, ∃ n : ℕ, (ad R L x ^ n) y = 0) (y : L) : ∃ n : ℕ, (ad R L x ^ n) y = 0 :=
  (mem_engel_iff R x y).mp (engel_eq_top_of_lieSpan_eq_top hs x hx ▸ mem_top y)

/-- A morphism of Lie algebras maps the Engel subalgebra of `x` into that of `f x`. -/
lemma map_engel_le (f : L →ₗ⁅R⁆ L') (x : L) : (engel R x).map f ≤ engel R (f x) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨n, hn⟩ := (mem_engel_iff R x y).mp hy
  refine (mem_engel_iff R (f x) (f y)).mpr ⟨n, ?_⟩
  have key : ∀ (k : ℕ) (z : L), f ((ad R L x ^ k) z) = (ad R L' (f x) ^ k) (f z) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro z
      rw [pow_succ', Module.End.mul_apply, ad_apply, LieHom.map_lie, ih, pow_succ',
        Module.End.mul_apply, ad_apply]
  rw [← key, hn, map_zero]

/-- If `ad x` is locally nilpotent on `L` and `f : L → L'` is surjective, then `ad (f x)` is
locally nilpotent on `L'`. -/
lemma engel_eq_top_of_surjective {f : L →ₗ⁅R⁆ L'} (hf : Function.Surjective f) {x : L}
    (hx : engel R x = ⊤) : engel R (f x) = ⊤ := by
  rw [eq_top_iff]
  rintro _ -
  obtain ⟨y, rfl⟩ := hf ‹L'›
  exact map_engel_le f x ⟨y, hx ▸ mem_top y, rfl⟩

end LieSubalgebra

namespace IsSl2Triple.HasPrimitiveVectorWith

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {h e f : L} {t : IsSl2Triple h e f} {m : M} {μ : R}

/-- If `m` is a primitive vector of weight `μ` for an `𝔰𝔩₂`-triple `(h, e, f)` and some power of
`f` kills `m`, then `μ` is a natural number. This is the standard `𝔰𝔩₂` computation, e.g.
[Kac] (3.2.4) and the proof of Lemma 3.2 (b). -/
theorem exists_nat_of_exists_pow_eq_zero [IsDomain R] [CharZero R] [Module.IsTorsionFree R M]
    (P : t.HasPrimitiveVectorWith m μ) (hm : ∃ n : ℕ, ((toEnd R L M f) ^ n) m = 0) :
    ∃ n : ℕ, μ = n := by
  obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists (by simpa using P.ne_zero)
    hm
  refine ⟨n, ?_⟩
  have := P.lie_e_pow_succ_toEnd_f n
  rw [hn₂, lie_zero, eq_comm, smul_eq_zero_iff_left hn₁, mul_eq_zero, sub_eq_zero] at this
  exact this.resolve_left <| Nat.cast_add_one_ne_zero n

end IsSl2Triple.HasPrimitiveVectorWith
