import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Basis

A **basis** of a vector space `V` is a family of vectors that is at once **linearly independent**
and **spanning**. These two properties combine into the single fact that makes a basis useful:
every vector of `V` is a *unique* finite linear combination of the basis vectors. Independence
gives the uniqueness of that expression, spanning gives its existence, and together they set up
the **coordinate isomorphism** `V ≅ Kⁿ` that lets us compute in an abstract space.

A basis also governs linear maps: a linear map is completely determined by its values on a
basis, and those values may be prescribed arbitrarily — so a basis of `V` and a choice of one
vector of `W` per basis vector are the same thing as a linear map `V → W`. Finally, dimension
constrains bases: in `Kⁿ` no more than `n` vectors can be independent and no fewer than `n` can
span.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/03Basis.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project (a proof using a banned lemma, directly or via `simp`/`exact?`, fails the
build).
-/

namespace Exercises.LinearAlgebra.Basis

open Module

variable {K : Type*} [Field K] {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {n : ℕ} (b : Basis (Fin n) K V)

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- A basis is linearly independent, and over a finite index this unfolds to: a vanishing
-- combination has all-zero coefficients.
#check @Basis.linearIndependent
#check @Fintype.linearIndependent_iff

-- Expand a vector in its coordinates, and push a linear map through a sum / a scalar.
#check @Basis.sum_repr
#check @map_sum
#check @map_smul

-- `b.constr K w` is the linear map obtained by extending the prescribed values `w` from the
-- basis to all of `V`; `constr_basis` says that this map has the prescribed value at each `b i`.
#check @Basis.constr
#check @Basis.constr_basis

-- An independent family of the right size *is* a basis; the dimension of `Kⁿ`; the size
-- bounds independence and spanning must obey.
#check @basisOfLinearIndependentOfCardEqFinrank
#check @Module.finrank_fin_fun
#check @LinearIndependent.fintype_card_le_finrank
#check @finrank_span_le_card

end


/-- **Question 1.**

For a basis `(bᵢ)`, coordinates are unique: if `∑ᵢ cᵢ bᵢ = ∑ᵢ dᵢ bᵢ`, then `cᵢ = dᵢ` for every
`i`.

Prove without using `Basis.ext_elem`. -/
theorem q1_coords_unique (c d : Fin n → K)
    (h : ∑ i, c i • b i = ∑ i, d i • b i) : c = d := by
  have := congrArg b.equivFun h
  simp only [map_sum, map_smul] at this
  funext j
  have hj := congrFun this j
  rw [Finset.sum_apply, Finset.sum_apply] at hj
  simp only [Pi.smul_apply, smul_eq_mul] at hj
  simp_all only [Basis.equivFun_apply, Basis.repr_self, Basis.equivFun_self, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]


/-- **Question 2.**

A linear map is determined by its values on a basis: if `f (bᵢ) = g (bᵢ)` for every `i`, then
`f = g`.

Prove without using `Basis.ext`. -/
theorem q2_map_determined (f g : V →ₗ[K] W) (h : ∀ i, f (b i) = g (b i)) : f = g := by
  ext v
  rw [← Basis.sum_repr b v]
  simp only [map_sum, map_smul]
  exact
    Fintype.sum_congr (fun a => (b.repr v) a • f (b a)) (fun a => (b.repr v) a • g (b a)) fun a =>
      congrArg (HSMul.hSMul ((b.repr v) a)) (h a)


/-- **Question 3.**

The basis values may be prescribed arbitrarily: given any target vectors `(wᵢ)` in `W`, there is
a linear map `f : V → W` with `f (bᵢ) = wᵢ` for every `i`. -/
theorem q3_prescribe_map (w : Fin n → W) : ∃ f : V →ₗ[K] W, ∀ i, f (b i) = w i := by
  let f : Fin n → W := fun i ↦ w i
  use Basis.constr b K (fun i ↦ w i)
  intro i
  simp only [Basis.constr_apply_fintype, Basis.equivFun_self, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]


/-- **Question 4.**

The vectors `(1,1)` and `(1,−1)` form a basis of `ℝ²`. -/
theorem q4_isBasis_concrete :
    ∃ B : Basis (Fin 2) ℝ (Fin 2 → ℝ), ⇑B = ![(![1, 1] : Fin 2 → ℝ), ![1, -1]] := by
  let v : Fin 2 → (Fin 2 → ℝ) := ![(![1, 1] : Fin 2 → ℝ), ![1, -1]]
  have v_li : LinearIndependent ℝ v := by
    simp [v]
    rw [@Fintype.linearIndependent_iff]
    intro g a i
    simp_all only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_one,
      Matrix.smul_empty, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_neg, Matrix.add_cons, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_add_empty, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true]
    obtain ⟨left, right⟩ := a
    fin_cases i <;> grind only
  let v_basis := basisOfLinearIndependentOfCardEqFinrank v_li (by simp only [Fintype.card_fin,
    finrank_fintype_fun_eq_card])
  use v_basis
  ext i j
  fin_cases i <;> fin_cases j <;> simp [v_basis, v]


/-- **Question 5.**

The nonzero vector `(1,2)` extends to a basis of `ℝ²`: there is a basis of `ℝ²` whose first
vector is `(1,2)`. -/
theorem q5_extend_concrete :
    ∃ B : Basis (Fin 2) ℝ (Fin 2 → ℝ), B 0 = ![1, 2] := by
  sorry


/-- **Question 6.**

Any three vectors in `ℝ²` are linearly dependent. -/
theorem q6_too_many_dependent (v : Fin 3 → (Fin 2 → ℝ)) : ¬ LinearIndependent ℝ v := by
  by_contra! h
  have := LinearIndependent.fintype_card_le_finrank h
  simp_all only [Fintype.card_fin, finrank_fintype_fun_eq_card, Nat.reduceLeDiff]


/-- **Question 7.**

No single vector spans `ℝ²`. -/
theorem q7_too_few_dont_span : ¬ ∃ v : Fin 2 → ℝ, Submodule.span ℝ {v} = ⊤ := by
  by_contra h
  obtain ⟨w, h⟩ := h
  -- #check finrank_span_le_card {w}
  have h_le := finrank_span_le_card (R := ℝ) ({w} : Set (Fin 2 → ℝ))
  simp_all only [Set.toFinset_singleton, Finset.card_singleton]
  rw [h] at h_le
  simp_all only [finrank_top, finrank_fintype_fun_eq_card, Fintype.card_fin, Nat.not_ofNat_le_one]


/-- **Question 8.**

A linear map that carries a basis to a linearly independent family is injective: if the images
`f (b₀), …, f (b_{n-1})` are linearly independent, then `f` is injective. -/
theorem q8_indep_image_injective (f : V →ₗ[K] W)
    (hf : LinearIndependent K fun i => f (b i)) : Function.Injective f := by
  unfold Function.Injective
  intro v w hvw
  have v_expand := (b.sum_repr v).symm
  have w_expand := (b.sum_repr w).symm
  have : f (v - w) = 0 := by sorry
  have this_expand : f (∑ i, (b.repr v) i • b i - ∑ i, (b.repr w) i • b i) = 0 := by sorry
  have h_sum : ∑ x, (b.repr (v - w)) x • f (b x) = 0 := by
    calc ∑ x, (b.repr (v - w)) x • f (b x)
      _ = f (∑ x, (b.repr (v - w)) x • b x) := by simp [map_sum, map_smul]
      _ = f (v - w)                         := by rw [b.sum_repr]
      _ = 0                                 := by trivial
  have h_repr_zero : b.repr (v - w) = 0 := by sorry
  have h_sub_zero : v - w = 0 := by sorry
  apply_fun fun t ↦ t + w at h_sub_zero
  simp at h_sub_zero
  trivial


end Exercises.LinearAlgebra.Basis
