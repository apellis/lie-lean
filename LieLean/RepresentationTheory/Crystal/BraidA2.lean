/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.WeylGroupAction

/-!
# The braid relation of length three for Kashiwara's reflections

For a seminormal crystal and a colour `i`, `Crystal.top C i b = ẽᵢ^{εᵢ(b)} b` is the top of the
`i`-string of `b`. Along the reduced word `(i, j, i)` every element `b` has *string coordinates*
`a₁ = εᵢ(b)`, `a₂ = εⱼ(topᵢ b)`, `a₃ = εᵢ(topⱼ topᵢ b)` and a top `topᵢ topⱼ topᵢ b`, which
determine `b`; Kashiwara's reflection `Sᵢ` acts on them by the affine map
`a₁ ↦ ⟨wt top, αᵢ^∨⟩ + a₂ - 2a₃ - a₁`.

`Crystal.IsSeminormal.reflection_braid_three` proves `SᵢSⱼSᵢ = SⱼSᵢSⱼ` on a stable set of
elements when `⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = -1` and, on that set, the two string tops agree and the
coordinates along `(j, i, j)` are related to those along `(i, j, i)` by the `A₂` transition map
`c₁ = max(a₃, a₂ - a₁)` (and symmetrically); the braid relation then reduces to an identity
of piecewise-linear maps on `ℤ³`. For path crystals these hypotheses are the Pitman-transform
identities of `LieLean.RepresentationTheory.Crystal.Path.Pitman`.

## References

* [Lit98] P. Littelmann, *Cones, crystals, and patterns*, Transform. Groups **3** (1998),
  145–179, §1–2 (string parametrizations and the `A₂` transition map) (check).
* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413, §7 (check).

The argument is reconstructed.
-/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B : Type*} (C : Crystal D B)

lemma eIter_add (i : ι) (m n : ℕ) (b : B) :
    C.eIter i (m + n) b = (C.eIter i m b).bind (C.eIter i n) := by
  induction m generalizing b with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, eIter_succ, eIter_succ, Option.bind_assoc]
    congr 1
    funext c
    exact ih c

/-- `εᵢ(b)` as a natural number (`0` if `εᵢ(b) = -∞`). -/
def εN (i : ι) (b : B) : ℕ := (WithBot.unbotD 0 (C.ε i b)).toNat

/-- The top `ẽᵢ^{εᵢ(b)} b` of the `i`-string of `b`. -/
def top (i : ι) (b : B) : B := (C.eIter i (C.εN i b) b).getD b

variable {C}

lemma IsStable.eIter_mem {S : Set B} (hS : C.IsStable S) {i : ι} {n : ℕ} {b b' : B}
    (hb : b ∈ S) (h : C.eIter i n b = some b') : b' ∈ S := by
  induction n generalizing b with
  | zero => cases h; exact hb
  | succ n ih =>
    obtain ⟨c, hc, hcb⟩ := Option.bind_eq_some_iff.mp h
    exact ih (hS.e_mem i b c hb hc) hcb

lemma IsStable.fIter_mem {S : Set B} (hS : C.IsStable S) {i : ι} {n : ℕ} {b b' : B}
    (hb : b ∈ S) (h : C.fIter i n b = some b') : b' ∈ S := by
  induction n generalizing b with
  | zero => cases h; exact hb
  | succ n ih =>
    obtain ⟨c, hc, hcb⟩ := Option.bind_eq_some_iff.mp h
    exact ih (hS.f_mem i b c hb hc) hcb

lemma IsStable.reflection_mem {S : Set B} (hS : C.IsStable S) {i : ι} {b : B} (hb : b ∈ S) :
    C.reflection i b ∈ S := by
  unfold reflection
  split_ifs
  · cases h : C.fIter i _ b with
    | none => exact hb
    | some b' => exact hS.fIter_mem hb h
  · cases h : C.eIter i _ b with
    | none => exact hb
    | some b' => exact hS.eIter_mem hb h

lemma IsStable.top_mem {S : Set B} (hS : C.IsStable S) {i : ι} {b : B} (hb : b ∈ S) :
    C.top i b ∈ S := by
  unfold top
  cases h : C.eIter i (C.εN i b) b with
  | none => exact hb
  | some b' => exact hS.eIter_mem hb h

/-- The piecewise-linear identity behind the `A₂` braid relation: the string coordinates of
`SᵢSⱼSᵢ b` and of `SⱼSᵢSⱼ b`, computed through the transition map
`(a₁, a₂, a₃) ↦ (max(a₃, a₂ - a₁), a₁ + a₃, a₂ - max(a₃, a₂ - a₁))` and its inverse, agree. -/
theorem a2_braid_coordinates {mi mj a1 a2 a3 c1 c2 c3 p1 p2 p3 q1 q2 q3 r1 r2 r3 s1 s2 s3
    u1 u2 u3 v1 v2 v3 w1 w2 w3 x1 x2 x3 y1 y2 y3 z1 z2 z3 t1 t2 t3 : ℤ}
    (T1 : c1 = max a3 (a2 - a1)) (T2 : c2 = a1 + a3) (T3 : c3 = a2 - c1)
    (hp1 : p1 = mi + a2 - 2 * a3 - a1) (hp2 : p2 = a2) (hp3 : p3 = a3)
    (U1 : q1 = max p3 (p2 - p1)) (U2 : q2 = p1 + p3) (U3 : q3 = p2 - q1)
    (hr1 : r1 = mj + q2 - 2 * q3 - q1) (hr2 : r2 = q2) (hr3 : r3 = q3)
    (V2 : r2 = s1 + s3) (V3 : r3 = s2 - r1) (R1 : s1 = max r3 (r2 - r1))
    (hu1 : u1 = mi + s2 - 2 * s3 - s1) (hu2 : u2 = s2) (hu3 : u3 = s3)
    (hv1 : v1 = mj + c2 - 2 * c3 - c1) (hv2 : v2 = c2) (hv3 : v3 = c3)
    (W2 : v2 = w1 + w3) (W3 : v3 = w2 - v1) (R2 : w1 = max v3 (v2 - v1))
    (hx1 : x1 = mi + w2 - 2 * w3 - w1) (hx2 : x2 = w2) (hx3 : x3 = w3)
    (Y1 : y1 = max x3 (x2 - x1)) (Y2 : y2 = x1 + x3) (Y3 : y3 = x2 - y1)
    (hz1 : z1 = mj + y2 - 2 * y3 - y1) (hz2 : z2 = y2) (hz3 : z3 = y3)
    (Z2 : z2 = t1 + t3) (Z3 : z3 = t2 - z1) (R3 : t1 = max z3 (z2 - z1)) :
    u1 = t1 ∧ u2 = t2 ∧ u3 = t3 := by
  have hs2 : s2 = r1 + r3 := by omega
  have hs3 : s3 = r2 - s1 := by omega
  have hw2 : w2 = v1 + v3 := by omega
  have hw3 : w3 = v2 - w1 := by omega
  have ht2 : t2 = z1 + z3 := by omega
  have ht3 : t3 = z2 - t1 := by omega
  clear V2 V3 W2 W3 Z2 Z3
  subst_vars
  refine ⟨?_, ?_, ?_⟩ <;> omega

namespace IsSeminormal

variable (hC : C.IsSeminormal) {i j : ι} {b : B}
include hC

lemma ε_eq_εN : C.ε i b = (C.εN i b : WithBot ℤ) := by
  obtain ⟨n, hn⟩ := hC.exists_ε_eq i b
  rw [εN, hn]
  rfl

lemma eIter_top : C.eIter i (C.εN i b) b = some (C.top i b) := by
  have hs : (C.eIter i (C.εN i b) b).isSome := (hC.isSome_eIter_iff _).mpr (hC.ε_eq_εN).ge
  rw [top, ← Option.some_get hs, Option.getD_some]

lemma e_top : C.e i (C.top i b) = none := by
  have hn : C.eIter i (C.εN i b + 1) b = none := by
    rw [← Option.not_isSome_iff_eq_none, hC.isSome_eIter_iff, hC.ε_eq_εN]
    intro h
    have : ((C.εN i b + 1 : ℕ) : ℤ) ≤ C.εN i b := by exact_mod_cast h
    omega
  rwa [eIter_succ', hC.eIter_top, Option.bind_some] at hn

lemma εN_top : C.εN i (C.top i b) = 0 := by
  rw [εN, hC.ε_eq_zero hC.e_top]
  rfl

lemma wt_top : C.wt (C.top i b) = C.wt b + C.εN i b • D.root i :=
  C.wt_eIter hC.eIter_top

lemma fIter_top : C.fIter i (C.εN i b) (C.top i b) = some b :=
  (C.fIter_eq_some_iff _ _ _).mpr hC.eIter_top

lemma top_eq_of_eIter {k : ℕ} {y : B} (h : C.eIter i k b = some y) (hy : C.e i y = none) :
    C.top i b = y := by
  have h1 := C.ε_eIter h
  rw [hC.ε_eq_zero hy, zero_add, hC.ε_eq_εN] at h1
  have hk : C.εN i b = k := by exact_mod_cast h1
  have h2 := hC.eIter_top (i := i) (b := b)
  rw [hk, h] at h2
  exact (Option.some_injective _ h2).symm

lemma eq_of_top_eq {b' : B} (h : C.top i b = C.top i b') (hε : C.εN i b = C.εN i b') :
    b = b' := by
  have h1 := hC.fIter_top (i := i) (b := b)
  rw [h, hε, hC.fIter_top] at h1
  exact (Option.some_injective _ h1).symm

/-- `Sᵢ` stays in the `i`-string: `topᵢ (Sᵢ b) = topᵢ b`. -/
lemma top_reflection : C.top i (C.reflection i b) = C.top i b := by
  have hs := hC.stringMap_reflection i b
  unfold stringMap at hs
  split_ifs at hs with hn
  · have he := (C.fIter_eq_some_iff _ _ _).mp hs
    refine hC.top_eq_of_eIter (k := (D.coroot i (C.wt b)).toNat + C.εN i b) ?_ hC.e_top
    rw [eIter_add, he, Option.bind_some, hC.eIter_top]
  · set m := (-D.coroot i (C.wt b)).toNat
    have hm : m ≤ C.εN i b := by
      have := (hC.isSome_eIter_iff (b := b) m).mp (by rw [hs]; rfl)
      rw [hC.ε_eq_εN] at this
      exact_mod_cast this
    refine hC.top_eq_of_eIter (k := C.εN i b - m) ?_ hC.e_top
    have := hC.eIter_top (i := i) (b := b)
    rwa [← Nat.add_sub_cancel' hm, eIter_add, hs, Option.bind_some] at this

/-- `εᵢ(Sᵢ b) = ⟨wt (topᵢ b), αᵢ^∨⟩ - εᵢ(b)`. -/
lemma εN_reflection :
    (C.εN i (C.reflection i b) : ℤ) = D.coroot i (C.wt (C.top i b)) - C.εN i b := by
  have h := hC.ε_reflection i b
  rw [C.φ_eq, hC.ε_eq_εN, hC.ε_eq_εN] at h
  have h' : (C.εN i (C.reflection i b) : ℤ) = C.εN i b + D.coroot i (C.wt b) := by
    exact_mod_cast h
  rw [hC.wt_top, map_add, map_nsmul, D.coroot_root_self, h', nsmul_eq_mul]
  ring

/-- The weight of the string top along `(i, j, i)`. -/
lemma wt_top_three :
    C.wt (C.top i (C.top j (C.top i b))) = C.wt b +
      ((C.εN i b + C.εN i (C.top j (C.top i b))) • D.root i + C.εN j (C.top i b) • D.root j) := by
  rw [hC.wt_top, hC.wt_top, hC.wt_top, add_nsmul]
  abel

lemma coroot_wt_top (hij : D.coroot i (D.root j) = -1) :
    D.coroot i (C.wt (C.top i b)) = D.coroot i (C.wt (C.top i (C.top j (C.top i b)))) +
      C.εN j (C.top i b) - 2 * C.εN i (C.top j (C.top i b)) := by
  rw [hC.wt_top (i := i) (b := C.top j (C.top i b)), hC.wt_top (i := j) (b := C.top i b),
    map_add, map_add, map_nsmul, map_nsmul, hij, D.coroot_root_self]
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  ring

/-- **The braid relation of length three** ([Kas94] §7 (check), reconstructed): if
`⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = -1` and, on a stable set `S`, the string tops along `(i, j, i)` and
`(j, i, j)` agree and the string coordinates satisfy the `A₂` transition rule
`c₁ = max(a₃, a₂ - a₁)` in both directions, then `SᵢSⱼSᵢ = SⱼSᵢSⱼ` on `S`. -/
theorem reflection_braid_three (hij : D.coroot i (D.root j) = -1)
    (hji : D.coroot j (D.root i) = -1) {S : Set B} (hS : C.IsStable S)
    (htop : ∀ b ∈ S, C.top i (C.top j (C.top i b)) = C.top j (C.top i (C.top j b)))
    (hε : ∀ b ∈ S, (C.εN j b : ℤ) =
      max (C.εN i (C.top j (C.top i b)) : ℤ) ((C.εN j (C.top i b) : ℤ) - C.εN i b))
    (hε' : ∀ b ∈ S, (C.εN i b : ℤ) =
      max (C.εN j (C.top i (C.top j b)) : ℤ) ((C.εN i (C.top j b) : ℤ) - C.εN j b))
    (hb : b ∈ S) :
    C.reflection i (C.reflection j (C.reflection i b)) =
      C.reflection j (C.reflection i (C.reflection j b)) := by
  -- string coordinates and tops
  set τ : B → B := fun x => C.top i (C.top j (C.top i x)) with hτ
  set a₁ : B → ℤ := fun x => C.εN i x
  set a₂ : B → ℤ := fun x => C.εN j (C.top i x)
  set a₃ : B → ℤ := fun x => C.εN i (C.top j (C.top i x))
  set c₁ : B → ℤ := fun x => C.εN j x
  set c₂ : B → ℤ := fun x => C.εN i (C.top j x)
  set c₃ : B → ℤ := fun x => C.εN j (C.top i (C.top j x))
  -- injectivity of the coordinates
  have inj : ∀ x y, a₁ x = a₁ y → a₂ x = a₂ y → a₃ x = a₃ y → τ x = τ y → x = y := by
    intro x y h1 h2 h3 h4
    simp only [a₁, a₂, a₃, τ, Nat.cast_inj] at h1 h2 h3 h4
    have e3 : C.top j (C.top i x) = C.top j (C.top i y) := hC.eq_of_top_eq h4 h3
    have e2 : C.top i x = C.top i y := hC.eq_of_top_eq e3 h2
    exact hC.eq_of_top_eq e2 h1
  -- the transition map
  have hT : ∀ x ∈ S, c₁ x = max (a₃ x) (a₂ x - a₁ x) ∧ c₂ x = a₁ x + a₃ x ∧
      c₃ x = a₂ x - c₁ x := by
    intro x hx
    have hw := hC.wt_top_three (i := i) (j := j) (b := x)
    have hw' := hC.wt_top_three (i := j) (j := i) (b := x)
    rw [← htop x hx] at hw'
    rw [hw] at hw'
    have hzero : ((C.εN i x + C.εN i (C.top j (C.top i x)) : ℕ) : ℤ) • D.root i +
        (C.εN j (C.top i x) : ℤ) • D.root j = ((C.εN i (C.top j x) : ℕ) : ℤ) • D.root i +
        ((C.εN j x + C.εN j (C.top i (C.top j x)) : ℕ) : ℤ) • D.root j := by
      simp only [natCast_zsmul]
      have := add_left_cancel hw'
      rw [this]
      abel
    have hi := congrArg (D.coroot i) hzero
    have hj := congrArg (D.coroot j) hzero
    simp only [map_add, map_zsmul, D.coroot_root_self, hij, hji, smul_eq_mul] at hi hj
    push_cast at hi hj
    have := hε x hx
    refine ⟨this, ?_, ?_⟩ <;> simp only [a₁, a₂, a₃, c₁, c₂, c₃] <;> omega
  have hT' : ∀ x ∈ S, a₁ x = max (c₃ x) (c₂ x - c₁ x) := fun x hx => hε' x hx
  -- the action of the reflections
  have hSi : ∀ x, a₁ (C.reflection i x) =
      D.coroot i (C.wt (τ x)) + a₂ x - 2 * a₃ x - a₁ x ∧ a₂ (C.reflection i x) = a₂ x ∧
      a₃ (C.reflection i x) = a₃ x ∧ τ (C.reflection i x) = τ x := by
    intro x
    have ht := hC.top_reflection (i := i) (b := x)
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (C.εN i (C.reflection i x) : ℤ) = _
      rw [hC.εN_reflection, hC.coroot_wt_top hij]
    · change (C.εN j (C.top i (C.reflection i x)) : ℤ) = _
      rw [ht]
    · change (C.εN i (C.top j (C.top i (C.reflection i x))) : ℤ) = _
      rw [ht]
    · change C.top i (C.top j (C.top i (C.reflection i x))) = _
      rw [ht]
  have hSj : ∀ x ∈ S, c₁ (C.reflection j x) =
      D.coroot j (C.wt (τ x)) + c₂ x - 2 * c₃ x - c₁ x ∧ c₂ (C.reflection j x) = c₂ x ∧
      c₃ (C.reflection j x) = c₃ x ∧ τ (C.reflection j x) = τ x := by
    intro x hx
    have ht := hC.top_reflection (i := j) (b := x)
    have hτx : τ x = C.top j (C.top i (C.top j x)) := htop x hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (C.εN j (C.reflection j x) : ℤ) = _
      rw [hC.εN_reflection, hC.coroot_wt_top hji, hτx]
    · change (C.εN i (C.top j (C.reflection j x)) : ℤ) = _
      rw [ht]
    · change (C.εN j (C.top i (C.top j (C.reflection j x))) : ℤ) = _
      rw [ht]
    · change C.top i (C.top j (C.top i (C.reflection j x))) = C.top i (C.top j (C.top i x))
      rw [htop _ (hS.reflection_mem hx), htop x hx, ht]
  -- run both sides
  clear_value τ a₁ a₂ a₃ c₁ c₂ c₃
  have hx₁ : C.reflection i b ∈ S := hS.reflection_mem hb
  have hx₂ : C.reflection j (C.reflection i b) ∈ S := hS.reflection_mem hx₁
  have hy₁ : C.reflection j b ∈ S := hS.reflection_mem hb
  have hy₂ : C.reflection i (C.reflection j b) ∈ S := hS.reflection_mem hy₁
  have hy₃ : C.reflection j (C.reflection i (C.reflection j b)) ∈ S := hS.reflection_mem hy₂
  obtain ⟨a1, a2, a3, t1⟩ := hSi b
  obtain ⟨b1, b2, b3, t2⟩ := hSj _ hx₁
  obtain ⟨d1, d2, d3, t3⟩ := hSi (C.reflection j (C.reflection i b))
  obtain ⟨e1, e2, e3, t4⟩ := hSj b hb
  obtain ⟨g1, g2, g3, t5⟩ := hSi (C.reflection j b)
  obtain ⟨k1, k2, k3, t6⟩ := hSj _ hy₂
  obtain ⟨T1, T2, T3⟩ := hT b hb
  obtain ⟨U1, U2, U3⟩ := hT _ hx₁
  obtain ⟨V1, V2, V3⟩ := hT _ hx₂
  obtain ⟨W1, W2, W3⟩ := hT _ hy₁
  obtain ⟨Y1, Y2, Y3⟩ := hT _ hy₂
  obtain ⟨Z1, Z2, Z3⟩ := hT _ hy₃
  have R0 := hT' b hb
  have R1 := hT' _ hx₂
  have R2 := hT' _ hy₁
  have R3 := hT' _ hy₃
  set μi := D.coroot i (C.wt (τ b))
  set μj := D.coroot j (C.wt (τ b))
  rw [t1] at b1
  rw [t2, t1] at d1
  rw [t4] at g1
  rw [t5, t4] at k1
  obtain ⟨h1, h2, h3⟩ := a2_braid_coordinates T1 T2 T3 a1 a2 a3 U1 U2 U3 b1 b2 b3 V2 V3 R1
    d1 d2 d3 e1 e2 e3 W2 W3 R2 g1 g2 g3 Y1 Y2 Y3 k1 k2 k3 Z2 Z3 R3
  exact inj _ _ h1 h2 h3 (by rw [t3, t2, t1, t6, t5, t4])

end IsSeminormal

end Crystal
