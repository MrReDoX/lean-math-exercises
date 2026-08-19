import Mathlib.Tactic

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Exercises — RingTheory / Rings

A commutative ring `R` has an abelian group structure under addition and a commutative,
associative multiplication with identity `1`, related by the distributive laws. The integers,
residue rings, polynomial rings, and products of rings are examples. A ring homomorphism
preserves `0`, `1`, addition, and multiplication.

An element `u` is a unit if there is `v` with `u * v = 1`. A zero divisor is a nonzero element
`a` for which `a * b = 0` for some nonzero `b`; thus multiplication by `a` need not be injective.
A domain has no zero divisors, so `a * b = a * c` and `a ≠ 0` imply `b = c`. A field is a domain
in which every nonzero element is a unit. The characteristic of `R` is the least positive `n`
with `n • 1 = 0`, if one exists, and is `0` otherwise.

Prove each statement yourself; the canonical proofs will live in
`Solutions/RingTheory/01Rings.lean`. Do **not** commit your proofs into this file.
-/


namespace Exercises.RingTheory.Rings

variable {R : Type*} [CommRing R]

/-- The real Hamilton quaternions written as coordinate tuples `a + bi + cj + dk`.

This small model exposes the multiplication and inverse formula used below, rather than hiding
them behind a pre-existing division-ring instance. -/
@[ext]
structure Hamilton where
  re : ℝ
  i : ℝ
  j : ℝ
  k : ℝ

namespace Hamilton

/-- The additive and multiplicative identities in the coordinate model. -/
def zero : Hamilton := ⟨0, 0, 0, 0⟩
def one : Hamilton := ⟨1, 0, 0, 0⟩

/-- Hamilton's multiplication rule, determined by `i² = j² = k² = ijk = -1`. -/
def mul (q r : Hamilton) : Hamilton :=
  ⟨q.re * r.re - q.i * r.i - q.j * r.j - q.k * r.k,
    q.re * r.i + q.i * r.re + q.j * r.k - q.k * r.j,
    q.re * r.j - q.i * r.k + q.j * r.re + q.k * r.i,
    q.re * r.k + q.i * r.j - q.j * r.i + q.k * r.re⟩

/-- Quaternion conjugation sends `a + bi + cj + dk` to `a - bi - cj - dk`. -/
def conj (q : Hamilton) : Hamilton := ⟨q.re, -q.i, -q.j, -q.k⟩

/-- The squared norm `a² + b² + c² + d²`. -/
def normSq (q : Hamilton) : ℝ := q.re ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2

/-- Multiply every coordinate of a quaternion by a real scalar. -/
def scale (t : ℝ) (q : Hamilton) : Hamilton := ⟨t * q.re, t * q.i, t * q.j, t * q.k⟩

/-- The candidate inverse `q̄ / ‖q‖²` for a nonzero quaternion. -/
noncomputable def inv (q : Hamilton) : Hamilton := scale (normSq q)⁻¹ (conj q)

/-- Additive negation in the coordinate model. -/
def neg (q : Hamilton) : Hamilton := ⟨-q.re, -q.i, -q.j, -q.k⟩

/-- The basic quaternion unit `i`. -/
def qi : Hamilton := ⟨0, 1, 0, 0⟩

/-- The basic quaternion unit `j`. -/
def qj : Hamilton := ⟨0, 0, 1, 0⟩

end Hamilton

/-- A candidate integer scalar action on an abelian group.  Additivity in the integer variable,
together with the values at `0` and `1`, expresses repeated addition without using a module
instance. -/
def IsIntScalarAction {A : Type*} [AddCommGroup A] (act : ℤ → A → A) : Prop :=
  (∀ a, act 0 a = 0) ∧ (∀ a, act 1 a = a) ∧
    ∀ m n a, act (m + n) a = act m a + act n a

/-! ## Potentially helpful results -/
section

-- Basic ring identities and cancellation.
#check @neg_mul
#check @IsUnit
#check @CharP.cast_eq_zero_iff
#check @isUnit_iff_exists

-- Residues, divisibility, and finite maps.
#check @Nat.Prime.dvd_mul
#check @ZMod.natCast_eq_zero_iff
#check @ZMod.natCast_zmod_surjective
#check @ZMod.isUnit_iff_coprime
#check @Finite.surjective_of_injective

-- Norm arguments for Gaussian integers.
#check @Zsqrtd.norm_mul
#check @Zsqrtd.norm_def
#check @Zsqrtd.norm_nonneg
#check @GaussianInt.norm_eq_zero
#check @Int.eq_one_of_dvd_one

-- Induction over positive and negative integers.
#check @Int.induction_on

end


/-- **Question 1.**

Negation distributes across multiplication on the left, and zero annihilates
multiplication. -/
theorem q1_neg_mul (a b : R) : (-a) * b = -(a * b) ∧ 0 * a = 0 := by
  constructor
  · simp only [neg_mul]
  · simp only [zero_mul]


/-- **Question 2.**

A unit cannot be a zero divisor: if `a` is a unit and `a*b = 0`, then `b = 0`. -/
theorem q2_unit_not_zero_divisor {a b : R} (ha : IsUnit a) (hab : a * b = 0) : b = 0 := by
  rw [isUnit_iff_exists] at ha
  obtain ⟨w, h⟩ := ha
  obtain ⟨left, right⟩ := h
  apply_fun (w * ·) at hab
  ring_nf at hab
  rw [right] at hab
  simp at hab
  trivial

/-- **Question 3.**

In an integral domain of characteristic `p`, the characteristic is either prime or zero.

Prove without using `CharP.char_is_prime_or_zero`. -/
theorem q3_char_prime_or_zero (p : ℕ) [IsDomain R] [CharP R p] : p.Prime ∨ p = 0 := by
  sorry


/-- **Question 4.**

The residue class of `5` is a unit modulo `12`. -/
theorem q4_zmod12_unit : IsUnit (5 : ZMod 12) := by
  sorry


/-- **Question 5.**

The determinant of a two-by-two real matrix is not additive. -/
theorem q5_determinant_not_additive :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, (A + B).det ≠ A.det + B.det := by
  sorry


/-- **Question 6.**

A multiplicative-and-additive map from `ℤ` to itself is either zero or the identity. -/
theorem q6_nonunital_ring_hom_int (f : ℤ →ₙ+* ℤ) :
    f = 0 ∨ f = NonUnitalRingHom.id ℤ := by
  sorry


/-- **Question 7.**

Any two unital ring homomorphisms from `ℤ` to a fixed ring are equal.

Prove without using `RingHom.ext_int`. -/
theorem q7_unique_int_ring_hom (f g : ℤ →+* R) : f = g := by
  sorry


/-- **Question 8.**

A homomorphism from a field is either zero or injective. -/
theorem q8_field_hom_zero_or_injective {K L : Type*} [Field K] [Ring L]
    (f : K →ₙ+* L) : f = 0 ∨ Function.Injective f := by
  sorry


/-- **Question 9.**

A unital ring homomorphism maps units to units.

Prove without using `IsUnit.map`. -/
theorem q9_ring_hom_maps_units {S : Type*} [Ring S] (f : R →+* S)
    {a : R} (ha : IsUnit a) : IsUnit (f a) := by
  sorry


/-- **Question 10.**

If `x² = 0`, then `1 + x` is a unit.

Prove without using `IsNilpotent.isUnit_one_add` or `IsNilpotent.isUnit_add_one`. -/
theorem q10_one_add_square_zero_is_unit (x : R) (hx : x ^ 2 = 0) : IsUnit (1 + x) := by
  sorry


/-- **Question 11.**

If `u` is a unit and `x² = 0`, then `u + x` is a unit.

Prove without using `IsNilpotent.isUnit_add_left_of_commute`. -/
theorem q11_unit_add_square_zero_is_unit (u x : R) (hu : IsUnit u)
    (hx : x ^ 2 = 0) : IsUnit (u + x) := by
  sorry


/-- **Question 12.**

Multiplication by `a` is injective exactly when `a` is nonzero and has no nonzero element that it
sends to zero. -/
theorem q12_left_mul_injective_iff [Nontrivial R] (a : R) :
    Function.Injective (fun b : R => a * b) ↔
      a ≠ 0 ∧ ∀ b : R, a * b = 0 → b = 0 := by
  sorry


/-- **Question 13.**

Multiplication by `a` is surjective exactly when `a` is a unit. -/
theorem q13_left_mul_surjective_iff (a : R) :
    Function.Surjective (fun b : R => a * b) ↔ IsUnit a := by
  sorry


/-- **Question 14.**

In a finite commutative domain, multiplication by a nonzero element is surjective.

Prove without using `IsLeftRegular.isUnit_of_finite`. -/
theorem q14_finite_domain_mul_surjective [Fintype R] [IsDomain R] (a : R) (ha : a ≠ 0) :
    Function.Surjective (fun b : R => a * b) := by
  sorry


/-- **Question 15.**

In a domain, an idempotent is either zero or one.

Prove without using `IsIdempotentElem.iff_eq_zero_or_one`. -/
theorem q15_domain_idempotent [IsDomain R] (e : R) (he : e * e = e) : e = 0 ∨ e = 1 := by
  sorry


/-- **Question 16.**

In a Boolean ring (one satisfying `x² = x` for every `x`), every element has
additive order dividing two, and multiplication is commutative. -/
theorem q16_boolean_two_torsion_and_comm {S : Type*} [Ring S]
    (h : ∀ x : S, x * x = x) (a b : S) : a + a = 0 ∧ a * b = b * a := by
  sorry


/-- **Question 17.**

The units of `ℤ/12ℤ` are exactly the residue classes of `1`, `5`, `7`, and `11`. -/
theorem q17_units_zmod12 (a : ZMod 12) :
    IsUnit a ↔ a = 1 ∨ a = 5 ∨ a = 7 ∨ a = 11 := by
  sorry


/-- **Question 18.**

If a nontrivial commutative ring has zero divisors, cross-multiplication is not a transitive
relation on numerator-denominator pairs. -/
theorem q18_cross_multiplication_not_transitive [Nontrivial R] (hR : ¬ IsDomain R) :
    ¬ IsTrans (R × R) (fun x y : R × R => x.1 * y.2 = x.2 * y.1) := by
  sorry


/-- **Question 19.**

For `n ≥ 2`, the residue ring `ℤ/nℤ` has no zero divisors exactly when
`n` is prime. -/
theorem q19_zmod_no_zero_divisors_iff_prime (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a b : ZMod n, a * b = 0 → a = 0 ∨ b = 0 := by
  sorry


/-- **Question 20.**

The Gaussian integers `ℤ[i]` have no zero divisors: if `zw = 0`, then
`z = 0` or `w = 0`.

Prove without using `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero`. -/
theorem q20_gaussian_no_zero_divisors (z w : GaussianInt) (hzw : z * w = 0) : z = 0 ∨ w = 0 := by
  sorry


/-- **Question 21.**

The only units of the Gaussian integers are `1`, `-1`, `i`, and `-i`.
Here `i` and `-i` are represented by the coordinate pairs `⟨0, 1⟩` and `⟨0, -1⟩`.

Prove without using `Zsqrtd.norm_eq_one_iff'`. -/
theorem q21_gaussian_units_exactly_four (z : GaussianInt) :
    IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ := by
  sorry


/-- **Question 22.**

In the coordinate model of the real quaternions, every nonzero quaternion
has a displayed two-sided inverse.  The basic units `i` and `j` also anticommute, so quaternion
multiplication is not commutative. -/
theorem q22_hamilton_inverse_and_noncommutative (q : Hamilton) (hq : q ≠ Hamilton.zero) :
    (∃ r, Hamilton.mul q r = Hamilton.one ∧ Hamilton.mul r q = Hamilton.one) ∧
      Hamilton.mul Hamilton.qi Hamilton.qj = Hamilton.neg (Hamilton.mul Hamilton.qj Hamilton.qi) := by
  sorry


end Exercises.RingTheory.Rings
