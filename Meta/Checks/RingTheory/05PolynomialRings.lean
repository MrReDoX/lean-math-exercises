import Exercises.RingTheory.«05PolynomialRings»
import Solutions.RingTheory.«05PolynomialRings»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.Polynomials.q1_factor_theorem
  [Polynomial.dvd_iff_isRoot, Polynomial.mul_divByMonic_eq_iff_isRoot]
assert_not_uses Exercises.RingTheory.Polynomials.q6_kernel_constant_coeff [Polynomial.ker_constantCoeff]

assert_not_uses Solutions.RingTheory.Polynomials.q1_factor_theorem
  [Polynomial.dvd_iff_isRoot, Polynomial.mul_divByMonic_eq_iff_isRoot]
assert_not_uses Solutions.RingTheory.Polynomials.q6_kernel_constant_coeff [Polynomial.ker_constantCoeff]
