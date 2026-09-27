/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import LieLean.Algebra.QuantumGroup.CartanDatum
import LieLean.Algebra.QuantumGroup.QBinomial

/-!
# The quantized enveloping algebra `U_q(𝔤)`

Let `(I, ·)` be a Cartan datum with Cartan matrix `aᵢⱼ = 2 (i·j)/(i·i)` and `dᵢ = (i·i)/2`, and
let `(Y, …)` be a root datum of type `(I, ·)` ([Lus] 2.2.1 (check)): an abelian group `Y` (the
coweight lattice) with elements `i ∈ Y` (the simple coroots, `CartanDatum.RootDatum.coroot`) and
homomorphisms `⟨·, j'⟩ : Y → ℤ` (the simple roots, `CartanDatum.RootDatum.root`) such that
`⟨i, j'⟩ = aᵢⱼ`. Let `k` be a field and `v ∈ k`, `vᵢ = v^{dᵢ}`, `K̃ᵢ = K_{dᵢ i}`.

Following [Lus] 3.1.1 (check), `U = U_q(𝔤)` is the associative `k`-algebra with generators `Eᵢ`,
`Fᵢ` (`i ∈ I`) and `K_μ` (`μ ∈ Y`) and relations
* (a) `K_0 = 1`, `K_μ K_ν = K_{μ+ν}`;
* (b) `K_μ Eᵢ = v^{⟨μ, i'⟩} Eᵢ K_μ`;
* (c) `K_μ Fᵢ = v^{-⟨μ, i'⟩} Fᵢ K_μ`;
* (d) `Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ (K̃ᵢ - K̃₋ᵢ)/(vᵢ - vᵢ⁻¹)`;
* (e) the quantum Serre relations `Σ_{r=0}^{1-aᵢⱼ} (-1)^r [1-aᵢⱼ, r]ᵢ Eᵢ^{1-aᵢⱼ-r} Eⱼ Eᵢ^r = 0`
  and likewise for `F`, for `i ≠ j`.

We state the Serre relations in the binomial form of [Jan] 4.3 (R6) (check), which makes sense for
every `v`; when `[1 - aᵢⱼ]ᵢ! ≠ 0` (e.g. `v` not a root of unity) it is equivalent to Lusztig's
divided-power form `Σ_{r+s=1-aᵢⱼ} (-1)^r Eᵢ^{(s)} Eⱼ Eᵢ^{(r)} = 0`
(`QuantumGroup.qSerreDiv_eq`). The algebra is constructed as a quotient (`RingQuot`) of the free
algebra on the generators.

## Main definitions

* `CartanDatum.RootDatum`: a root datum of type `(I, ·)`.
* `QuantumGroup R v`: the algebra `U`; generators `QuantumGroup.E`, `QuantumGroup.F`,
  `QuantumGroup.K`, and `QuantumGroup.Kt i = K̃ᵢ`.
* `QuantumGroup.Relations`: the relations (b)–(e) for elements of an arbitrary `k`-algebra.
* `QuantumGroup.lift`: the universal property.

## Main results

* `QuantumGroup.K_zero`, `K_add`, `K_mul_E`, `K_mul_F`, `E_mul_F_sub`, `serre_E`, `serre_F`.
* `QuantumGroup.lift_E`, `lift_F`, `lift_K`, `QuantumGroup.hom_ext`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §2.2, §3.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 4.
-/

noncomputable section

variable {I : Type*}

/-- A root datum of type `(I, ·)` in the sense of [Lus] 2.2.1 (check), recorded through the
coweight lattice `Y`: elements `coroot i ∈ Y` and homomorphisms `root j : Y →+ ℤ` with
`⟨i, j'⟩ = root j (coroot i) = aᵢⱼ`. (Lusztig's `X` is the dual lattice, which we do not
need.) -/
structure CartanDatum.RootDatum (D : CartanDatum I) (Y : Type*) [AddCommGroup Y] where
  /-- The simple coroots `i ∈ Y`. -/
  coroot : I → Y
  /-- The simple roots `j' ∈ X = Hom(Y, ℤ)`. -/
  root : I → Y →+ ℤ
  root_coroot : ∀ i j, root j (coroot i) = D.cartanMatrix i j

namespace QuantumGroup

variable (I) in
/-- The generators `Eᵢ`, `Fᵢ`, `K_μ` of the free algebra of which `U` is a quotient. -/
inductive Generator (Y : Type*)
  | E : I → Generator Y
  | F : I → Generator Y
  | K : Y → Generator Y

variable {k Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : CartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-- `K̃ᵢ = K_{dᵢ i}`: the element `dᵢ • coroot i ∈ Y`. -/
def ktilde (i : I) : Y := D.d i • R.coroot i

section Relations

variable {A : Type*} [Ring A] [Algebra k A]

/-- The defining relations (b)–(e) of `U` ([Lus] 3.1.1 (check), Serre relations in the binomial
form of [Jan] 4.3 (check)) for elements `eᵢ, fᵢ` and a family `κ : Y → A` with `κ(μ + ν) =
κ(μ) κ(ν)`, `κ(0) = 1` (encoded as a monoid homomorphism `Multiplicative Y →* A`). -/
structure Relations (e f : I → A) (κ : Multiplicative Y →* A) : Prop where
  K_mul_E : ∀ μ i, κ (.ofAdd μ) * e i = v ^ R.root i μ • (e i * κ (.ofAdd μ))
  K_mul_F : ∀ μ i, κ (.ofAdd μ) * f i = v ^ (-R.root i μ) • (f i * κ (.ofAdd μ))
  E_mul_F : ∀ i j, e i * f j - f j * e i = if i = j then
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (κ (.ofAdd (ktilde R i)) - κ (.ofAdd (-ktilde R i))) else 0
  serre_E : ∀ i j, i ≠ j → qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (e i) (e j) = 0
  serre_F : ∀ i j, i ≠ j → qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (f i) (f j) = 0

end Relations

variable (k) in
/-- The generator `Eᵢ` of the free algebra. -/
abbrev genE (i : I) : FreeAlgebra k (Generator I Y) := FreeAlgebra.ι k (.E i)

variable (k) in
/-- The generator `Fᵢ` of the free algebra. -/
abbrev genF (i : I) : FreeAlgebra k (Generator I Y) := FreeAlgebra.ι k (.F i)

variable (k) in
/-- The generator `K_μ` of the free algebra. -/
abbrev genK (μ : Y) : FreeAlgebra k (Generator I Y) := FreeAlgebra.ι k (.K μ)

/-- The defining relations of `U` in the free algebra on the generators. -/
inductive Rel : FreeAlgebra k (Generator I Y) → FreeAlgebra k (Generator I Y) → Prop
  | K_zero : Rel (genK k 0) 1
  | K_add (μ ν : Y) : Rel (genK k μ * genK k ν) (genK k (μ + ν))
  | K_E (μ : Y) (i : I) : Rel (genK k μ * genE k i) (v ^ R.root i μ • (genE k i * genK k μ))
  | K_F (μ : Y) (i : I) : Rel (genK k μ * genF k i) (v ^ (-R.root i μ) • (genF k i * genK k μ))
  | E_F (i j : I) : Rel (genE k i * genF k j - genF k j * genE k i) (if i = j then
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (genK k (ktilde R i) - genK k (-ktilde R i)) else 0)
  | serre_E (i j : I) (h : i ≠ j) :
      Rel (qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (genE k i) (genE k j)) 0
  | serre_F (i j : I) (h : i ≠ j) :
      Rel (qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (genF k i) (genF k j)) 0

end QuantumGroup

open QuantumGroup in
/-- The quantized enveloping algebra `U = U_q(𝔤)` of a root datum `R` of type `(I, ·)` over a
field `k`, at the parameter `v ∈ k` ([Lus] 3.1.1 (check)). -/
def QuantumGroup {k Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : CartanDatum I}
    (R : D.RootDatum Y) (v : k) : Type _ :=
  RingQuot (Rel R v)

namespace QuantumGroup

variable {k Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : CartanDatum I}
  (R : D.RootDatum Y) (v : k)

instance : Ring (QuantumGroup R v) := inferInstanceAs (Ring (RingQuot _))

instance : Algebra k (QuantumGroup R v) := inferInstanceAs (Algebra k (RingQuot _))

/-- The quotient map from the free algebra. -/
def mkAlgHom : FreeAlgebra k (Generator I Y) →ₐ[k] QuantumGroup R v := RingQuot.mkAlgHom k _

/-- The generator `Eᵢ` of `U`. -/
def E (i : I) : QuantumGroup R v := mkAlgHom R v (genE k i)

/-- The generator `Fᵢ` of `U`. -/
def F (i : I) : QuantumGroup R v := mkAlgHom R v (genF k i)

/-- The generators `K_μ` of `U`, as a monoid homomorphism `Multiplicative Y →* U`. -/
def KHom : Multiplicative Y →* QuantumGroup R v where
  toFun μ := mkAlgHom R v (genK k μ.toAdd)
  map_one' := RingQuot.mkAlgHom_rel k Rel.K_zero |>.trans (map_one _)
  map_mul' μ ν := by
    rw [← map_mul]
    exact (RingQuot.mkAlgHom_rel k (Rel.K_add μ.toAdd ν.toAdd)).symm

/-- The generator `K_μ` of `U`. -/
def K (μ : Y) : QuantumGroup R v := KHom R v (.ofAdd μ)

/-- `K̃ᵢ = K_{dᵢ i}`. -/
abbrev Kt (i : I) : QuantumGroup R v := K R v (ktilde R i)

@[simp] lemma KHom_apply (μ : Multiplicative Y) : KHom R v μ = K R v μ.toAdd := rfl

lemma KHom_apply' (μ : Multiplicative Y) : KHom R v μ = mkAlgHom R v (genK k μ.toAdd) := rfl

/-- `K_0 = 1`. -/
@[simp] theorem K_zero : K R v 0 = 1 := map_one (KHom R v)

/-- `K_μ K_ν = K_{μ+ν}`. -/
theorem K_add (μ ν : Y) : K R v μ * K R v ν = K R v (μ + ν) :=
  (map_mul (KHom R v) (.ofAdd μ) (.ofAdd ν)).symm

theorem K_mul_K_neg (μ : Y) : K R v μ * K R v (-μ) = 1 := by rw [K_add, add_neg_cancel, K_zero]

theorem K_neg_mul_K (μ : Y) : K R v (-μ) * K R v μ = 1 := by rw [K_add, neg_add_cancel, K_zero]

theorem K_comm (μ ν : Y) : K R v μ * K R v ν = K R v ν * K R v μ := by
  rw [K_add, K_add, add_comm]

/-- `K_μ Eᵢ = v^{⟨μ, i'⟩} Eᵢ K_μ`. -/
theorem K_mul_E (μ : Y) (i : I) : K R v μ * E R v i = v ^ R.root i μ • (E R v i * K R v μ) := by
  change mkAlgHom R v (genK k μ) * mkAlgHom R v (genE k i) =
    v ^ R.root i μ • (mkAlgHom R v (genE k i) * mkAlgHom R v (genK k μ))
  rw [← map_mul, ← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k (Rel.K_E μ i)

/-- `K_μ Fᵢ = v^{-⟨μ, i'⟩} Fᵢ K_μ`. -/
theorem K_mul_F (μ : Y) (i : I) :
    K R v μ * F R v i = v ^ (-R.root i μ) • (F R v i * K R v μ) := by
  change mkAlgHom R v (genK k μ) * mkAlgHom R v (genF k i) =
    v ^ (-R.root i μ) • (mkAlgHom R v (genF k i) * mkAlgHom R v (genK k μ))
  rw [← map_mul, ← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k (Rel.K_F μ i)

/-- `Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ (K̃ᵢ - K̃₋ᵢ)/(vᵢ - vᵢ⁻¹)`. -/
theorem E_mul_F_sub (i j : I) : E R v i * F R v j - F R v j * E R v i = if i = j then
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (Kt R v i - K R v (-ktilde R i)) else 0 := by
  have := RingQuot.mkAlgHom_rel k (Rel.E_F (R := R) (v := v) i j)
  change mkAlgHom R v (genE k i) * mkAlgHom R v (genF k j) -
    mkAlgHom R v (genF k j) * mkAlgHom R v (genE k i) = if i = j then
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ •
      (mkAlgHom R v (genK k (ktilde R i)) - mkAlgHom R v (genK k (-ktilde R i))) else 0
  rw [← map_mul, ← map_mul, ← map_sub]
  split_ifs at this ⊢
  · rw [← map_sub, ← map_smul]; exact this
  · rw [← map_zero (mkAlgHom R v)]; exact this

/-- The quantum Serre relations for the `Eᵢ`. -/
theorem serre_E {i j : I} (h : i ≠ j) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (E R v i) (E R v j) = 0 := by
  change qSerre _ _ (mkAlgHom R v (genE k i)) (mkAlgHom R v (genE k j)) = 0
  rw [← map_qSerre, ← map_zero (mkAlgHom R v)]
  exact RingQuot.mkAlgHom_rel k (Rel.serre_E i j h)

/-- The quantum Serre relations for the `Fᵢ`. -/
theorem serre_F {i j : I} (h : i ≠ j) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (F R v i) (F R v j) = 0 := by
  change qSerre _ _ (mkAlgHom R v (genF k i)) (mkAlgHom R v (genF k j)) = 0
  rw [← map_qSerre, ← map_zero (mkAlgHom R v)]
  exact RingQuot.mkAlgHom_rel k (Rel.serre_F i j h)

/-- The generators of `U` satisfy the defining relations. -/
theorem relations : Relations R v (E R v) (F R v) (KHom R v) where
  K_mul_E μ i := K_mul_E R v μ i
  K_mul_F μ i := K_mul_F R v μ i
  E_mul_F i j := E_mul_F_sub R v i j
  serre_E _ _ h := serre_E R v h
  serre_F _ _ h := serre_F R v h

/-- Induction on `U`: a property of elements of `U` that holds for scalars and the generators
and is closed under sums and products holds everywhere. -/
theorem induction_on {P : QuantumGroup R v → Prop} (x : QuantumGroup R v)
    (algebraMap : ∀ c, P (algebraMap k _ c)) (E : ∀ i, P (E R v i)) (F : ∀ i, P (F R v i))
    (K : ∀ μ, P (K R v μ)) (add : ∀ x y, P x → P y → P (x + y))
    (mul : ∀ x y, P x → P y → P (x * y)) : P x := by
  obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective k (Rel R v) x
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact algebraMap c
  | grade1 g =>
    cases g with
    | E i => exact E i
    | F i => exact F i
    | K μ => exact K μ
  | mul a b ha hb => rw [map_mul]; exact mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact add _ _ ha hb

section lift

variable {R v} {A : Type*} [Ring A] [Algebra k A]

/-- The map on the free algebra defined by `eᵢ, fᵢ, κ`. -/
def freeLift (e f : I → A) (κ : Multiplicative Y →* A) : FreeAlgebra k (Generator I Y) →ₐ[k] A :=
  FreeAlgebra.lift k fun
    | .E i => e i
    | .F i => f i
    | .K μ => κ (.ofAdd μ)

/-- The universal property of `U`: elements `eᵢ, fᵢ` and `κ : Y → A` of a `k`-algebra `A`
satisfying the defining relations determine an algebra homomorphism `U → A`. -/
def lift {e f : I → A} {κ : Multiplicative Y →* A} (h : Relations R v e f κ) :
    QuantumGroup R v →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨freeLift e f κ, fun x y hxy ↦ by
    induction hxy with
    | K_zero => simp [freeLift]
    | K_add μ ν => simp [freeLift, map_mul]
    | K_E μ i => simpa [freeLift] using h.K_mul_E μ i
    | K_F μ i => simpa [freeLift] using h.K_mul_F μ i
    | E_F i j =>
      have := h.E_mul_F i j
      split_ifs at this ⊢ <;> simpa [freeLift] using this
    | serre_E i j hij => simpa [freeLift, map_qSerre] using h.serre_E i j hij
    | serre_F i j hij => simpa [freeLift, map_qSerre] using h.serre_F i j hij⟩

variable {e f : I → A} {κ : Multiplicative Y →* A} (h : Relations R v e f κ)

lemma lift_mkAlgHom (x : FreeAlgebra k (Generator I Y)) :
    lift h (mkAlgHom R v x) = freeLift e f κ x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

@[simp] theorem lift_E (i : I) : lift h (E R v i) = e i := by
  rw [E, lift_mkAlgHom]; simp [freeLift]

@[simp] theorem lift_F (i : I) : lift h (F R v i) = f i := by
  rw [F, lift_mkAlgHom]; simp [freeLift]

@[simp] theorem lift_K (μ : Y) : lift h (K R v μ) = κ (.ofAdd μ) := by
  rw [K, KHom_apply']; rw [lift_mkAlgHom]; simp [freeLift]

/-- Algebra homomorphisms out of `U` are determined by their values on the generators. -/
@[ext]
theorem hom_ext {φ ψ : QuantumGroup R v →ₐ[k] A} (hE : ∀ i, φ (E R v i) = ψ (E R v i))
    (hF : ∀ i, φ (F R v i) = ψ (F R v i)) (hK : ∀ μ, φ (K R v μ) = ψ (K R v μ)) : φ = ψ := by
  refine RingQuot.ringQuot_ext' k φ ψ (FreeAlgebra.hom_ext (funext fun g ↦ ?_))
  cases g with
  | E i => exact hE i
  | F i => exact hF i
  | K μ => exact hK μ

end lift

end QuantumGroup
