import Mathlib.Tactic

import Mathlib.Algebra.Polynomial.Eval.Defs

import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exercises — RingTheory / Prime and Maximal Ideals

A proper ideal `P` is prime when `a * b ∈ P` implies `a ∈ P` or `b ∈ P`; this is equivalent to
`R ⧸ P` being an integral domain. A proper ideal `m` is maximal when no ideal lies strictly between
`m` and `R`; this is equivalent to `R ⧸ m` being a field. Every maximal ideal is prime.

For a ring homomorphism `f : R →+* S`, the inverse image of a prime ideal is prime. If `f` is
surjective, the inverse image of a maximal ideal is maximal. The prime ideals of `R` form
`Spec R`, which is the underlying set of the prime spectrum.

Prove each statement yourself; the canonical proofs will live in
`Solutions/RingTheory/03PrimeAndMaximalIdeals.lean`. Do **not** commit your proofs into this file.
-/


namespace Exercises.RingTheory.PrimeAndMaximalIdeals

variable {R : Type*} [CommRing R]

/-! ## Potentially helpful results -/
section

-- Quotient criteria and maximal ideals.
#check @Ideal.Quotient.eq_zero_iff_mem
#check @Ideal.Quotient.mk_surjective
#check @Ideal.mem_span_singleton_sup
#check @eq_zero_or_eq_zero_of_mul_eq_zero

-- Arithmetic in `ℤ`.
#check @Int.gcd_dvd_left
#check @Int.gcd_dvd_right
#check @Int.gcd_eq_gcd_ab

-- Principal ideals, powers, and maximality.
#check @Ideal.IsPrime.mem_or_mem
#check @Ideal.isMaximal_iff
#check @Ideal.mem_span_singleton
#check @Ideal.span_le
#check @Ideal.subset_span
#check @Ideal.pow_mem_of_mem
#check @IsPrincipalIdealRing.principal

-- Polynomial and product-ring examples.
#check @Polynomial.X_dvd_iff
#check @Ideal.span_singleton_prime
#check @Int.ideal_span_isMaximal_of_prime
#check @Ideal.isPrime_ideal_prod_top'
#check @Ideal.comap_isMaximal_of_surjective

-- Finite families of ideals.
#check @Finset.exists_le_maximal
#check @Finset.prod_erase_mul
#check @Finset.sum_erase_add

-- Prime ideals and ideal products.
#check @Ideal.IsPrime.mul_le
#check @Ideal.mul_le_left
#check @Ideal.mul_le_right

end


/-- **Question 1.**

Show that `R ⧸ I` is an integral domain if and only if `I` is prime.

Prove without using `Ideal.Quotient.isDomain_iff_prime` or `Ideal.Quotient.isDomain`. -/
theorem q1_quotient_domain_iff_prime (I : Ideal R) : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  sorry


/-- **Question 2.**

The inverse image of a prime ideal along a ring homomorphism is prime.

Prove without using `Ideal.IsPrime.comap`. -/
theorem q2_comap_prime {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (J : Ideal S) (hJ : J.IsPrime) : (Ideal.comap f J).IsPrime := by
  sorry


/-- **Question 3.**

The quotient by an ideal is a field exactly when that ideal is maximal. For the forward direction,
adjoin a representative `x ∉ I` to `I`; maximality forces `1 = yx + z` with `z ∈ I`, and this
identity supplies the inverse of the class of `x`.

Prove without using `Ideal.Quotient.maximal_ideal_iff_isField_quotient`,
`Ideal.Quotient.field`, `Ideal.Quotient.maximal_of_isField`, or `Ideal.Quotient.exists_inv`. -/
theorem q3_quotient_field_iff_maximal (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I) := by
  sorry


/-- **Question 4.**

Every maximal ideal in a commutative ring is prime.

Prove without using `Ideal.IsMaximal.isPrime`. -/
theorem q4_maximal_prime (I : Ideal R) (hI : I.IsMaximal) : I.IsPrime := by
  sorry


/-- **Question 5.**

A prime integer generates a maximal ideal of `ℤ`: the ideal `(p)` is proper and every strictly
larger ideal is the whole ring. -/
theorem q5_int_prime_maximal (p : ℕ) [Fact p.Prime] :
    Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊤ ∧
    ∀ J : Ideal ℤ, Ideal.span ({(p : ℤ)} : Set ℤ) < J → J = ⊤ := by
  sorry


/-- **Question 6.**

The zero ideal of `ℤ` is prime but not maximal. Thus a prime ideal need not be maximal.

Prove without using `Ideal.isPrime_bot`. -/
theorem q6_zero_prime_not_maximal : (⊥ : Ideal ℤ).IsPrime ∧ ¬ (⊥ : Ideal ℤ).IsMaximal := by
  sorry


/-- **Question 7.**

In the polynomial ring `ℤ[X]`, the ideal `(X)` is prime but not maximal. -/
theorem q7_x_ideal_prime_not_maximal :
    (Ideal.span ({Polynomial.X} : Set (Polynomial ℤ))).IsPrime ∧
      ¬ (Ideal.span ({Polynomial.X} : Set (Polynomial ℤ))).IsMaximal := by
  sorry


/-- **Question 8.**

In a principal ideal domain, every nonzero prime ideal is maximal.

Prove without using `PrincipalIdealRing.isMaximal_of_irreducible`. -/
theorem q8_nonzero_prime_in_pid_is_maximal {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (P : Ideal R) (hP : P.IsPrime) (hP0 : P ≠ ⊥) : P.IsMaximal := by
  sorry


/-- **Question 9.**

If every element `x` satisfies `x ^ n = x` for some `n > 1`, then every prime ideal is maximal. -/
theorem q9_prime_ideals_maximal {R : Type*} [CommRing R]
    (hpower : ∀ x : R, ∃ n : ℕ, 1 < n ∧ x ^ n = x) (P : Ideal R) (hP : P.IsPrime) :
    P.IsMaximal := by
  sorry


/-- **Question 10.**

In the product ring `ℤ × ℤ`, the whole ideal `ℤ × ℤ` is not prime. -/
theorem q10_top_product_ideal_not_prime :
    ¬ (Ideal.prod (⊤ : Ideal ℤ) (⊤ : Ideal ℤ)).IsPrime := by
  sorry


/-- **Question 11.**

In the product ring `ℤ × ℤ`, the zero ideal `(0) × (0)` is not prime.

Prove without using `Ideal.ideal_prod_prime_aux`. -/
theorem q11_zero_product_ideal_not_prime :
    ¬ (Ideal.prod (⊥ : Ideal ℤ) (⊥ : Ideal ℤ)).IsPrime := by
  sorry


/-- **Question 12.**

In the product ring `ℤ × ℤ`, the ideal `(2) × (3)` is not prime.

Prove without using `Ideal.ideal_prod_prime_aux`. -/
theorem q12_product_ideal_not_prime :
    ¬ (Ideal.prod (Ideal.span ({2} : Set ℤ)) (Ideal.span ({3} : Set ℤ))).IsPrime := by
  sorry


/-- **Question 13.**

In the product ring `ℤ × ℤ`, the ideal `ℤ × (3)` is both prime and maximal. -/
theorem q13_top_times_three_prime_maximal :
    (Ideal.prod (⊤ : Ideal ℤ) (Ideal.span ({3} : Set ℤ))).IsPrime ∧
      (Ideal.prod (⊤ : Ideal ℤ) (Ideal.span ({3} : Set ℤ))).IsMaximal := by
  sorry


/-- **Question 14.**

Two ideals are incomparable if neither is contained in the other. Every finite family of ideals
contains a pairwise incomparable subfamily such that every ideal in the original family is
contained in a member of that subfamily. -/
theorem q14_exists_pairwise_incomparable_subfamily_covering {R : Type*} [CommRing R] {n : ℕ}
    (P : Fin n → Ideal R) :
    ∃ S : Finset (Fin n),
      (∀ i, ∃ j ∈ S, P i ≤ P j) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ P i ≤ P j) := by
  sorry


/-- **Question 15.**

Let `P` be a pairwise incomparable family of prime ideals. If `I` is not contained in any
member of the family, then for each `P i` there is an element of `I` outside `P i` and inside
every other member of the family. -/
theorem q15_exists_separating_element {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal R) (P : Fin n → Ideal R) (hP : ∀ i, (P i).IsPrime)
    (hI : ∀ i, ¬ I ≤ P i)
    (hincomparable : ∀ i j, i ≠ j → ¬ P i ≤ P j) :
    ∀ i, ∃ x : R, x ∈ I ∧ x ∉ P i ∧ ∀ j, j ≠ i → x ∈ P j := by
  sorry


/-- **Question 16.**

Given one separating element as in Question 15 for each member of a finite family, their sum
belongs to `I` and belongs to none of the ideals in the family. -/
theorem q16_sum_of_separating_elements_avoids_all {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal R) (P : Fin n → Ideal R) (c : Fin n → R)
    (hcI : ∀ i, c i ∈ I)
    (hc : ∀ i, c i ∉ P i ∧ ∀ j, j ≠ i → c i ∈ P j) :
    ∃ x : R, x ∈ I ∧ ∀ i, x ∉ P i := by
  sorry


/-- **Question 17.**

An ideal covered by a finite pairwise incomparable family of prime ideals is contained in one
of those ideals. -/
theorem q17_prime_avoidance_of_pairwise_incomparable {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal R) (P : Fin n → Ideal R) (hP : ∀ i, (P i).IsPrime)
    (hincomparable : ∀ i j, i ≠ j → ¬ P i ≤ P j)
    (hcover : ∀ x : R, x ∈ I → ∃ i : Fin n, x ∈ P i) :
    ∃ i : Fin n, I ≤ P i := by
  sorry


/-- **Question 18.**

By Question 14, a finite family of ideals can be reduced to a pairwise incomparable subfamily
that still covers `I`. Consequently, if every element of `I` belongs to one of finitely many
prime ideals, then `I` is contained in one of those ideals.

Prove without using `Ideal.subset_union_prime`, `Ideal.subset_union_prime_finite`, or
`Ideal.subset_union_prime'`. -/
theorem q18_prime_avoidance {R : Type*} [CommRing R] (n : ℕ) (I : Ideal R)
    (P : Fin n → Ideal R) (hP : ∀ i : Fin n, (P i).IsPrime)
    (hcover : ∀ x : R, x ∈ I → ∃ i : Fin n, x ∈ P i) : ∃ i : Fin n, I ≤ P i := by
  sorry


end Exercises.RingTheory.PrimeAndMaximalIdeals
