import Exercises.RingTheory.«02Ideals»
import Solutions.RingTheory.«02Ideals»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.Ideals.q2_mem_span_singleton_iff
  [Ideal.mem_span_singleton, Ideal.mem_span_singleton']
assert_not_uses Exercises.RingTheory.Ideals.q3_span_singleton_le_iff
  [Ideal.span_singleton_le_iff_mem]
assert_not_uses Exercises.RingTheory.Ideals.q4_span_singleton_eq_iff_associated
  [Ideal.span_singleton_eq_span_singleton]
assert_not_uses Exercises.RingTheory.Ideals.q6_exists_ideal_comap [Ideal.comap]
assert_not_uses Exercises.RingTheory.Ideals.q7_quotient_comap_embeds_quotient
  [Ideal.quotientMap, Ideal.quotientMap_injective]
assert_not_uses Exercises.RingTheory.Ideals.q8_first_iso_ring
  [RingHom.quotientKerEquivRange, RingHom.quotientKerEquivOfSurjective,
    RingHom.quotientKerEquivOfRightInverse]
assert_not_uses Exercises.RingTheory.Ideals.q9_quotient_represents_maps_killing_ideal
  [Ideal.Quotient.lift]
assert_not_uses Exercises.RingTheory.Ideals.q11_coprime_inf_eq_mul
  [Ideal.mul_eq_inf_of_isCoprime, Ideal.mul_le_inf]
assert_not_uses Exercises.RingTheory.Ideals.q12_idempotent_gives_product_decomposition
  [AlgEquiv.prodQuotientOfIsIdempotentElem]

assert_not_uses Solutions.RingTheory.Ideals.q2_mem_span_singleton_iff
  [Ideal.mem_span_singleton, Ideal.mem_span_singleton']
assert_not_uses Solutions.RingTheory.Ideals.q3_span_singleton_le_iff
  [Ideal.span_singleton_le_iff_mem]
assert_not_uses Solutions.RingTheory.Ideals.q4_span_singleton_eq_iff_associated
  [Ideal.span_singleton_eq_span_singleton]
assert_not_uses Solutions.RingTheory.Ideals.q6_exists_ideal_comap [Ideal.comap]
assert_not_uses Solutions.RingTheory.Ideals.q7_quotient_comap_embeds_quotient
  [Ideal.quotientMap, Ideal.quotientMap_injective]
assert_not_uses Solutions.RingTheory.Ideals.q8_first_iso_ring
  [RingHom.quotientKerEquivRange, RingHom.quotientKerEquivOfSurjective,
    RingHom.quotientKerEquivOfRightInverse]
assert_not_uses Solutions.RingTheory.Ideals.q9_quotient_represents_maps_killing_ideal
  [Ideal.Quotient.lift]
assert_not_uses Solutions.RingTheory.Ideals.q11_coprime_inf_eq_mul
  [Ideal.mul_eq_inf_of_isCoprime, Ideal.mul_le_inf]
assert_not_uses Solutions.RingTheory.Ideals.q12_idempotent_gives_product_decomposition
  [AlgEquiv.prodQuotientOfIsIdempotentElem]
