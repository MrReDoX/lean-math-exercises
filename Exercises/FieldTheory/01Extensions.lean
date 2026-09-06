import Mathlib.Tactic

import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Exercises — FieldTheory / Extensions and Degree

An extension `L / K` is a vector space over `K`; its dimension is the degree `[L : K]`.
Minimal polynomials calculate the degree of simple algebraic extensions, while degrees multiply in
towers. These facts distinguish algebraic elements from transcendental ones.

Prove each statement yourself; the canonical proofs live in
`Solutions/FieldTheory/01Extensions.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.FieldTheory.Extensions

open scoped IntermediateField Polynomial

/-! ## Potentially helpful results -/
section

#check @Complex.ext
#check @Submodule.subset_span
#check @Submodule.smul_mem
#check @Polynomial.monic_X_pow_add_C
#check @Module.finrank_eq_card_basis
#check @Module.finrank_mul_finrank
#check @IntermediateField.finrank_eq_one_iff
#check @IntermediateField.finrank_eq_one_iff_eq_top
#check @Polynomial.eval₂_C_X

end


/-- **Question 1.**

Every complex number has unique real and imaginary coordinates: prove that
each `z : ℂ` can be written in exactly one way as `a + b * i` with `a, b : ℝ`. -/
theorem q1_complex_coordinates (z : ℂ) :
    ∃! ab : ℝ × ℝ, z = (ab.1 : ℂ) + ab.2 * Complex.I := by
  use ⟨z.re, z.im⟩
  constructor <;> simp
  · intro a b h
    rw [Complex.ext_iff] at h
    simp_all only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im, zero_add, and_self]


/-- **Question 2.**

If `a + bi = 0` with `a, b : ℝ`, then `a = b = 0`. -/
theorem q2_one_i_linear_independent (a b : ℝ) :
    (a : ℂ) + b * Complex.I = 0 → a = 0 ∧ b = 0 := by
  intro h
  rw [Complex.ext_iff] at h
  constructor <;> simp_all only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re, Complex.add_im, Complex.mul_im,
    zero_add, Complex.zero_im]


/-- **Question 3.**

The vectors `1` and `i` span `ℂ` as a real vector space.

Prove without using `Complex.basisOneI`. -/
theorem q3_one_i_spans_complex :
    Submodule.span ℝ ({(1 : ℂ), Complex.I} : Set ℂ) = ⊤ := by
  rw [@Submodule.eq_top_iff']
  intro z
  rw [@Submodule.mem_span_pair]
  use z.re, z.im
  simp only [Complex.real_smul, mul_one, Complex.re_add_im]


/-- **Question 4.**

The extension `ℂ / ℝ` has degree `2`.

Prove without using `Complex.finrank_real_complex` or `Complex.basisOneI`. -/
theorem q4_degree_complex_real : Module.finrank ℝ ℂ = 2 := by
  have e : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) := {
    toFun := fun z ↦ ![z.re, z.im]
    map_add' := by
      intro x y
      simp only [Complex.add_re, Complex.add_im, Matrix.add_cons, Matrix.head_cons,
        Matrix.tail_cons, Matrix.empty_add_empty]
    map_smul' := by
      intro m x
      simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.mul_im, add_zero, RingHom.id_apply, Matrix.smul_cons, smul_eq_mul,
        Matrix.smul_empty]
    invFun := fun v ↦ ⟨v 0, v 1⟩
    right_inv := by
      unfold Function.RightInverse
      unfold Function.LeftInverse
      intro x
      simp only [Fin.isValue]
      ext i
      fin_cases i <;> simp
  }

  rw [LinearEquiv.finrank_eq e]
  exact Module.finrank_fin_fun ℝ


example : Module.finrank ℝ ℂ = 2 := by
  have b : Module.Basis (Fin 2) ℝ ℂ :=
    Module.Basis.mk (v := ![1, Complex.I])
      (by
        rw [@linearIndependent_fin2]
        simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, ne_eq,
          Complex.I_ne_zero, not_false_eq_true, Complex.real_smul, Matrix.cons_val_zero, true_and]
        intro a h
        rw [Complex.ext_iff] at h
        simp_all only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
          mul_one, sub_self, Complex.one_re, zero_ne_one, Complex.mul_im, add_zero, Complex.one_im, false_and]
      )
      (by
        simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
          top_le_iff]
        rw [@Submodule.eq_top_iff']
        intro z
        rw [@Submodule.mem_span_pair]
        use z.im, z.re
        rw [Complex.ext_iff]
        simp only [Complex.real_smul, mul_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, zero_add,
          Complex.add_im, Complex.mul_im, add_zero, and_self]
      )

  rw [Module.finrank_eq_card_basis b]
  simp only [Fintype.card_fin]

/-- **Question 5.**

The polynomial `X² + 1` vanishes at `i`. -/
theorem q5_i_root :
    (Polynomial.X ^ 2 + Polynomial.C 1 : ℝ[X]).eval₂ (algebraMap ℝ ℂ) Complex.I = 0 := by
  simp only [map_one, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Complex.I_sq,
    Polynomial.eval₂_one, neg_add_cancel]


/-- **Question 6.**

The element `i` is integral over `ℝ`. -/
theorem q6_i_integral : IsIntegral ℝ Complex.I := by
  use Polynomial.X ^ 2 + Polynomial.C 1
  simp only [map_one, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Complex.I_sq,
    Polynomial.eval₂_one, neg_add_cancel, and_true]
  unfold Polynomial.Monic
  simp only [Order.lt_two_iff, zero_le, Polynomial.leadingCoeff_X_pow_add_one]


/-- **Question 7.**

Every `z ∈ ℂ` satisfies `z² - 2 Re(z) z + |z|² = 0`. -/
theorem q7_complex_quadratic_relation (z : ℂ) :
    z ^ 2 - ((2 * z.re : ℝ) : ℂ) * z + ((Complex.normSq z : ℝ) : ℂ) = 0 := by
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Complex.normSq_apply, Complex.ext_iff]
  simp_all only [Complex.ofReal_add, Complex.ofReal_mul, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im,
    zero_mul, add_zero, Complex.zero_re, Complex.add_im, Complex.sub_im, Complex.zero_im]
  apply And.intro <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring_nf


/-- **Question 8.**

Every complex number is integral over `ℝ`.

Prove directly from a quadratic relation, without using `IsAlgebraic.of_finite` or
`Algebra.IsAlgebraic.isAlgebraic`. -/
theorem q8_every_complex_integral (z : ℂ) : IsIntegral ℝ z := by
  use Polynomial.X ^ 2 - (2 * z.re) • Polynomial.X + Polynomial.C (z.re ^ 2 + z.im ^ 2)

  simp_all only [map_add, map_pow, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_smul, Complex.coe_algebraMap, Complex.ofReal_mul, Complex.ofReal_ofNat, Polynomial.eval₂_X,
    Polynomial.eval₂_pow', Polynomial.eval₂_C]
  apply And.intro
  · monicity!
    right
    simp_all only [Polynomial.coeff_X, OfNat.one_ne_ofNat, ↓reduceIte]
  · rw [Complex.ext_iff]
    simp_all only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
      Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, Complex.zero_re,
      Complex.add_im, Complex.sub_im, Complex.zero_im]
    apply And.intro
    · simp only [Complex.mul_re, pow_two, Complex.ofReal_re]
      ring_nf; norm_num
    · simp only [Complex.mul_im, pow_two, Complex.ofReal_im]
      ring_nf


/-- **Question 9.**

Inside `ℂ / ℝ`, the simple extension `ℝ(i)` is all of `ℂ`. -/
theorem q9_complex_is_generated_by_i :
    IntermediateField.adjoin ℝ ({Complex.I} : Set ℂ) = ⊤ := by
  sorry


/-- **Question 10.**

If `ℝ ⊆ F ⊆ ℂ`, then `F = ℝ` or `F = ℂ`.

Prove without using `IntermediateField.isSimpleOrder_of_finrank_prime`. -/
theorem q10_quadratic_extension_has_no_proper_intermediate_field (F : IntermediateField ℝ ℂ) :
    F = ⊥ ∨ F = ⊤ := by
  sorry


/-- **Question 11.**

A scalar `a` is a root of the linear polynomial `X - a`. -/
theorem q11_root_of_linear_polynomial (K : Type*) [Field K] (a : K) :
    (Polynomial.X - Polynomial.C a).eval a = 0 := by
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]


/-- **Question 12.**

The polynomial indeterminate `X ∈ K[X]` is transcendental over `K`.

Prove without using `Polynomial.transcendental_X`. -/
theorem q12_indeterminate_transcendental (K : Type*) [Field K] :
    Transcendental K (Polynomial.X : K[X]) := by
  unfold Transcendental
  intro h
  unfold IsAlgebraic at h
  simp_all only [ne_eq, Polynomial.aeval_X_left, AlgHom.coe_id, id_eq, not_and_self, exists_const]

end Exercises.FieldTheory.Extensions
