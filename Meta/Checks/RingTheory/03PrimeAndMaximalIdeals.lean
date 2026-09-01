import Exercises.RingTheory.«03PrimeAndMaximalIdeals»
import Solutions.RingTheory.«03PrimeAndMaximalIdeals»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q1_quotient_domain_iff_prime
  [Ideal.Quotient.isDomain_iff_prime, Ideal.Quotient.isDomain]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q2_comap_prime [Ideal.IsPrime.comap]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q3_quotient_field_iff_maximal
  [Ideal.Quotient.maximal_ideal_iff_isField_quotient, Ideal.Quotient.field,
    Ideal.Quotient.maximal_of_isField, Ideal.Quotient.exists_inv]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q4_maximal_prime [Ideal.IsMaximal.isPrime]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q6_zero_prime_not_maximal
  [Ideal.isPrime_bot]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q8_nonzero_prime_in_pid_is_maximal
  [PrincipalIdealRing.isMaximal_of_irreducible]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q11_zero_product_ideal_not_prime
  [Ideal.ideal_prod_prime_aux]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q12_product_ideal_not_prime
  [Ideal.ideal_prod_prime_aux]
assert_not_uses Exercises.RingTheory.PrimeAndMaximalIdeals.q18_prime_avoidance
  [Ideal.subset_union_prime, Ideal.subset_union_prime_finite, Ideal.subset_union_prime']

assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q1_quotient_domain_iff_prime
  [Ideal.Quotient.isDomain_iff_prime, Ideal.Quotient.isDomain]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q2_comap_prime [Ideal.IsPrime.comap]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q3_quotient_field_iff_maximal
  [Ideal.Quotient.maximal_ideal_iff_isField_quotient, Ideal.Quotient.field,
    Ideal.Quotient.maximal_of_isField, Ideal.Quotient.exists_inv]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q4_maximal_prime [Ideal.IsMaximal.isPrime]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q6_zero_prime_not_maximal
  [Ideal.isPrime_bot]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q8_nonzero_prime_in_pid_is_maximal
  [PrincipalIdealRing.isMaximal_of_irreducible]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q11_zero_product_ideal_not_prime
  [Ideal.ideal_prod_prime_aux]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q12_product_ideal_not_prime
  [Ideal.ideal_prod_prime_aux]
assert_not_uses Solutions.RingTheory.PrimeAndMaximalIdeals.q18_prime_avoidance
  [Ideal.subset_union_prime, Ideal.subset_union_prime_finite, Ideal.subset_union_prime']
