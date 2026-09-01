import Mathlib.Tactic

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Determinant
namespace Solutions.RingTheory.Rings

variable {R : Type*} [CommRing R]

/-- The coordinate model of Hamilton quaternions used in Question 11. -/
@[ext]


structure Hamilton where
  re : ℝ
  i : ℝ
  j : ℝ
  k : ℝ

namespace Hamilton


def zero : Hamilton := ⟨0, 0, 0, 0⟩


def one : Hamilton := ⟨1, 0, 0, 0⟩


def mul (q r : Hamilton) : Hamilton :=
  ⟨q.re * r.re - q.i * r.i - q.j * r.j - q.k * r.k,
    q.re * r.i + q.i * r.re + q.j * r.k - q.k * r.j,
    q.re * r.j - q.i * r.k + q.j * r.re + q.k * r.i,
    q.re * r.k + q.i * r.j - q.j * r.i + q.k * r.re⟩


def conj (q : Hamilton) : Hamilton := ⟨q.re, -q.i, -q.j, -q.k⟩


def normSq (q : Hamilton) : ℝ := q.re ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2


def scale (t : ℝ) (q : Hamilton) : Hamilton := ⟨t * q.re, t * q.i, t * q.j, t * q.k⟩


noncomputable def inv (q : Hamilton) : Hamilton := scale (normSq q)⁻¹ (conj q)


def neg (q : Hamilton) : Hamilton := ⟨-q.re, -q.i, -q.j, -q.k⟩


def qi : Hamilton := ⟨0, 1, 0, 0⟩


def qj : Hamilton := ⟨0, 0, 1, 0⟩

end Hamilton

/-- An integer action characterized by zero, one, and additivity in the integer argument. -/


def IsIntScalarAction {A : Type*} [AddCommGroup A] (act : ℤ → A → A) : Prop :=
  (∀ a, act 0 a = 0) ∧ (∀ a, act 1 a = a) ∧
    ∀ m n a, act (m + n) a = act m a + act n a

open Hamilton


theorem q1_neg_mul (a b : R) : (-a) * b = -(a * b) ∧ 0 * a = 0 := by
  exact ⟨neg_mul a b, zero_mul a⟩


theorem q2_unit_not_zero_divisor {a b : R} (ha : IsUnit a) (hab : a * b = 0) : b = 0 := by
  rcases ha with ⟨u, rfl⟩
  -- Multiplying by the inverse of a unit cancels its nonzero factor.
  have h := congrArg (fun x : R => (↑(u⁻¹) : R) * x) hab
  simpa [mul_assoc] using h


theorem q3_char_prime_or_zero (p : ℕ) [IsDomain R] [CharP R p] : p.Prime ∨ p = 0 := by
  -- If `p = mk`, then the product of the casts of `m` and `k` is zero.  In a domain one factor
  -- must vanish, so the minimality encoded by the characteristic makes the factorization trivial.
  by_cases hp0 : p = 0
  · exact Or.inr hp0
  left
  rw [Nat.prime_def]
  refine ⟨?_, ?_⟩
  · have hp1 : p ≠ 1 := by
      intro hp1
      have hone : (1 : R) = 0 := by
        rw [← Nat.cast_one, ← hp1]
        exact CharP.cast_eq_zero R p
      exact one_ne_zero hone
    omega
  · intro m hmp
    rcases hmp with ⟨k, hk⟩
    have hmp : m ∣ p := ⟨k, hk⟩
    have hcast : (m : R) * (k : R) = 0 := by
      rw [← Nat.cast_mul, ← hk]
      exact CharP.cast_eq_zero R p
    rcases mul_eq_zero.mp hcast with hm0 | hk0
    · right
      exact Nat.dvd_antisymm hmp (CharP.cast_eq_zero_iff R p m |>.mp hm0)
    · left
      have hpdk : p ∣ k := CharP.cast_eq_zero_iff R p k |>.mp hk0
      have hkpos : 0 < k := by
        by_contra hkpos
        have hkzero : k = 0 := by omega
        exact hp0 (hk.trans (by simp [hkzero]))
      have hpkle : p ≤ k := Nat.le_of_dvd hkpos hpdk
      have hmkle : m * k ≤ k := by simpa [← hk] using hpkle
      have hmle : m ≤ 1 := Nat.le_of_mul_le_mul_right (by simpa using hmkle) hkpos
      have hmpos : 0 < m := by
        by_contra hmpos
        have hmzero : m = 0 := by omega
        exact hp0 (hk.trans (by simp [hmzero]))
      omega


theorem q4_coordinate_sum_not_nonunital_ring_hom :
    ¬ ∃ f : ℤ × ℤ →ₙ+* ℤ, ∀ x : ℤ × ℤ, f x = x.1 + x.2 := by
  rintro ⟨f, hf⟩
  have hmul := f.map_mul (1, 0) (0, 1)
  norm_num [hf] at hmul


theorem q5_determinant_not_additive :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, (A + B).det ≠ A.det + B.det := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := 1
  refine ⟨A, -A, ?_⟩
  simp [A]
  norm_num [Matrix.det_fin_two]


theorem q6_nonunital_ring_hom_int (f : ℤ →ₙ+* ℤ) :
    f = 0 ∨ f = NonUnitalRingHom.id ℤ := by
  set f1 := f 1 with hf1
  by_cases h : f1 = 0
  · left
    ext x
    calc
      f x = f (x * 1) := by simp
      _ = f x * f 1 := f.map_mul x 1
      _ = 0 := by rw [← hf1, h]; simp
  · right
    -- The image of `1` is idempotent; the only nonzero idempotent integer is `1`.
    have hf1_one : f1 = 1 := by
      by_contra hf1_ne_one
      have hidem : f1 * f1 = f1 := by
        simpa [hf1] using (f.map_mul 1 1).symm
      exact hf1_ne_one (IsIdempotentElem.iff_eq_zero_or_one.mp hidem |>.resolve_left h)
    ext n
    calc
      f n = f (n • (1 : ℤ)) := by simp
      _ = n • f 1 := f.toAddMonoidHom.map_zsmul n 1
      _ = n := by rw [← hf1, hf1_one]; simp


theorem q7_unique_int_ring_hom (f g : ℤ →+* R) : f = g := by
  -- A ring map must preserve both `1` and repeated addition, so its value on every integer is fixed.
  ext n
  simp


theorem q8_field_hom_zero_or_injective {K L : Type*} [Field K] [Ring L]
    (f : K →ₙ+* L) : f = 0 ∨ Function.Injective f := by
  set f1 := f 1 with hf1
  by_cases h : f1 = 0
  · left
    ext x
    calc
      f x = f (1 * x) := by simp
      _ = f 1 * f x := f.map_mul 1 x
      _ = 0 := by rw [← hf1, h]; simp
  · right
    -- A nonzero field element has an inverse, so a nonzero element in the kernel would force
    -- `f 1 = 0`.
    intro a b hab
    rw [← sub_eq_zero]
    set x := a - b with hx
    by_contra hne
    apply h
    rw [hf1]
    calc
      f 1 = f (x⁻¹ * x) := by rw [inv_mul_cancel₀ hne]
      _ = f x⁻¹ * f x := f.map_mul x⁻¹ x
      _ = 0 := by rw [show f x = 0 by simpa [hx] using sub_eq_zero.mpr hab, mul_zero]


theorem q9_ring_hom_maps_units {S : Type*} [Ring S] (f : R →+* S)
    {a : R} (ha : IsUnit a) : IsUnit (f a) := by
  rcases ha with ⟨u, rfl⟩
  exact ⟨u.map f, rfl⟩


theorem q10_one_add_square_zero_is_unit (x : R) (hx : x ^ 2 = 0) : IsUnit (1 + x) := by
  -- The square-zero hypothesis makes `1 - x` a two-sided inverse of `1 + x`.
  refine ⟨{ val := 1 + x, inv := 1 - x, val_inv := ?_, inv_val := ?_ }, rfl⟩ <;>
    calc
      _ = 1 - x ^ 2 := by ring
      _ = 1 := by rw [hx]; ring


theorem q11_unit_add_square_zero_is_unit (u x : R) (hu : IsUnit u)
    (hx : x ^ 2 = 0) : IsUnit (u + x) := by
  rcases hu with ⟨u, rfl⟩
  have hsq : ((↑(u⁻¹) : R) * x) ^ 2 = 0 := by
    rw [mul_pow]
    simp [hx]
  rw [show (↑u : R) + x = (↑u : R) * (1 + (↑(u⁻¹) : R) * x) by
    rw [mul_add, mul_one, ← mul_assoc]
    simp]
  exact u.isUnit.mul (q10_one_add_square_zero_is_unit _ hsq)


theorem q12_left_mul_injective_iff [Nontrivial R] (a : R) :
    Function.Injective (fun b : R => a * b) ↔
      a ≠ 0 ∧ ∀ b : R, a * b = 0 → b = 0 := by
  constructor
  · intro hinj
    constructor
    · intro ha
      have hzero_one : (0 : R) = 1 := hinj (by simp [ha])
      exact zero_ne_one hzero_one
    · intro b hab
      have hb : a * b = a * 0 := by simpa [hab]
      exact hinj hb
  · rintro ⟨ha, hkernel⟩ x y hxy
    change a * x = a * y at hxy
    apply sub_eq_zero.mp
    apply hkernel
    rw [mul_sub, hxy, sub_self]


theorem q13_left_mul_surjective_iff (a : R) :
    Function.Surjective (fun b : R => a * b) ↔ IsUnit a := by
  constructor
  · intro h
    -- A preimage of `1` supplies an inverse for `a`.
    obtain ⟨b, hb⟩ := h 1
    exact ⟨{ val := a, inv := b, val_inv := hb, inv_val := by simpa [mul_comm] using hb }, rfl⟩
  · rintro ⟨u, rfl⟩ b
    refine ⟨(↑(u⁻¹) : R) * b, ?_⟩
    change (↑u : R) * ((↑(u⁻¹) : R) * b) = b
    rw [← mul_assoc]
    simp


theorem q14_finite_domain_mul_surjective [Fintype R] [IsDomain R] (a : R) (ha : a ≠ 0) :
    Function.Surjective (fun b : R => a * b) := by
  -- Multiplication by `a` is injective: equal products differ by a product `a(x-y)` equal to zero.
  -- A self-map of a finite set is surjective once it is injective.
  have hinj : Function.Injective (fun x : R => a * x) := by
    intro x y hxy
    change a * x = a * y at hxy
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left ha
    rw [mul_sub, hxy, sub_self]
  exact Finite.surjective_of_injective hinj


theorem q15_domain_idempotent [IsDomain R] (e : R) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have hprod : e * (e - 1) = 0 := by
    rw [mul_sub, he, mul_one, sub_self]
  rcases mul_eq_zero.mp hprod with he0 | he1
  · exact Or.inl he0
  · exact Or.inr (sub_eq_zero.mp he1)


theorem q16_boolean_two_torsion_and_comm {S : Type*} [Ring S]
    (h : ∀ x : S, x * x = x) (a b : S) : a + a = 0 ∧ a * b = b * a := by
  -- First expand `(x+x)² = x+x`: it leaves `2x = 0` for every `x`.
  have htwo (x : S) : x + x = 0 := by
    have hfour : (x + x) + (x + x) = x + x := by
      calc
        (x + x) + (x + x) = (x + x) * (x + x) := by
          rw [mul_add, add_mul, h x]
        _ = x + x := h (x + x)
    apply add_left_cancel (a := x + x)
    simpa using hfour
  constructor
  · exact htwo a
  · -- Expanding `(a+b)² = a+b` gives `ab + ba = 0`; since `2ba = 0`, this forces `ab = ba`.
    have hab := h (a + b)
    have hcross : a * b + b * a = 0 := by
      have hexpand : (a * a + b * a) + (a * b + b * b) = a + b := by
        simpa only [mul_add, add_mul] using hab
      have hdiagonal : (a + b * a) + (a * b + b) = a + b := by
        simpa only [h a, h b] using hexpand
      apply add_left_cancel (a := a + b)
      calc
        (a + b) + (a * b + b * a) = (a + b * a) + (a * b + b) := by abel
        _ = a + b := hdiagonal
        _ = (a + b) + 0 := (add_zero _).symm
    calc
      a * b = a * b + 0 := (add_zero _).symm
      _ = a * b + (b * a + b * a) := by rw [htwo (b * a)]
      _ = (a * b + b * a) + b * a := by abel
      _ = b * a := by rw [hcross, zero_add]


theorem q17_units_zmod12 (a : ZMod 12) :
    IsUnit a ↔ a = 1 ∨ a = 5 ∨ a = 7 ∨ a = 11 := by
  have hval : (a.val : ZMod 12) = a := ZMod.natCast_zmod_val a
  rw [← hval, ZMod.isUnit_iff_coprime]
  have hlt : a.val < 12 := a.val_lt
  interval_cases h : a.val <;> norm_num [h] <;> decide


theorem q18_cross_multiplication_not_transitive [Nontrivial R] (hR : ¬ IsDomain R) :
    ¬ IsTrans (R × R) (fun x y : R × R => x.1 * y.2 = x.2 * y.1) := by
  intro h
  have hbad := h.trans (1, 0) (0, 0) (0, 1) (by simp) (by simp)
  simp at hbad


private theorem zmod_prime_iff_cast_no_zero_divisors (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a b : ℕ, (a : ZMod n) * b = 0 → (a : ZMod n) = 0 ∨ (b : ZMod n) = 0 := by
  constructor
  · intro hp a b hab
    rw [← Nat.cast_mul] at hab
    have hdivides : n ∣ a * b := (ZMod.natCast_eq_zero_iff (a * b) n).mp hab
    rcases hp.dvd_mul.mp hdivides with ha | hb
    · exact Or.inl ((ZMod.natCast_eq_zero_iff a n).mpr ha)
    · exact Or.inr ((ZMod.natCast_eq_zero_iff b n).mpr hb)
  · intro h
    have hnpos : 0 < n := by omega
    rw [Nat.prime_def_lt]
    refine ⟨hn, ?_⟩
    intro m hm hmn
    rcases hmn with ⟨k, hk⟩
    have hproduct : (m : ZMod n) * k = 0 := by
      rw [← Nat.cast_mul, ← hk]
      exact ZMod.natCast_self n
    rcases h m k hproduct with hmzero | hkzero
    · have hnm : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp hmzero
      have hmpos : 0 < m := by
        by_contra hmpos
        have hmzero : m = 0 := by omega
        simp [hmzero] at hk
        omega
      have hnle : n ≤ m := Nat.le_of_dvd hmpos hnm
      omega
    · have hnk : n ∣ k := (ZMod.natCast_eq_zero_iff k n).mp hkzero
      have hkpos : 0 < k := by
        by_contra hkpos
        have hkzero : k = 0 := by omega
        simp [hkzero] at hk
        omega
      have hnle : n ≤ k := Nat.le_of_dvd hkpos hnk
      have hmkle : m * k ≤ k := by simpa [← hk] using hnle
      have hmle : m ≤ 1 := Nat.le_of_mul_le_mul_right (by simpa using hmkle) hkpos
      have hmpos : 0 < m := by
        by_contra hmpos
        have hmzero : m = 0 := by omega
        simp [hmzero] at hk
        omega
      omega


theorem q19_zmod_no_zero_divisors_iff_prime (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a b : ZMod n, a * b = 0 → a = 0 ∨ b = 0 := by
  constructor
  · intro hp a b hab
    letI : NeZero n := ⟨Nat.ne_of_gt (by omega)⟩
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective b
    -- Every residue has a natural representative, so primality reduces the product to a
    -- divisibility statement in the natural numbers.
    exact zmod_prime_iff_cast_no_zero_divisors n hn |>.mp hp m k hab
  · intro h
    apply zmod_prime_iff_cast_no_zero_divisors n hn |>.mpr
    intro a b hab
    exact h a b hab


theorem q20_gaussian_no_zero_divisors (z w : GaussianInt) (hzw : z * w = 0) : z = 0 ∨ w = 0 := by
  -- Norms multiply.  Since an integer product is zero only when one factor is zero, one of the
  -- two Gaussian norms vanishes, and hence one of the two Gaussian integers vanishes.
  have hnorm : z.norm * w.norm = 0 := by
    rw [← Zsqrtd.norm_mul, hzw]
    rfl
  exact (Int.mul_eq_zero.mp hnorm).imp GaussianInt.norm_eq_zero.mp GaussianInt.norm_eq_zero.mp


theorem q21_gaussian_units_exactly_four (z : GaussianInt) :
    IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ := by
  constructor
  · intro hz
    rw [isUnit_iff_exists] at hz
    obtain ⟨w, hzw, _⟩ := hz
    -- A unit has an inverse, so its nonnegative norm divides one and must itself be one.
    have hnorm : z.norm = 1 := by
      apply Int.eq_one_of_dvd_one (Zsqrtd.norm_nonneg (by norm_num) z)
      refine ⟨w.norm, ?_⟩
      rw [← Zsqrtd.norm_mul, hzw, Zsqrtd.norm_one]
    have hsum : z.re * z.re + z.im * z.im = 1 := by
      simpa [Zsqrtd.norm_def] using hnorm
    -- Each coordinate has absolute value at most one.  The norm equation leaves exactly four
    -- lattice points on this circle.
    have hrelower : -1 ≤ z.re := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have hreupper : z.re ≤ 1 := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have himlower : -1 ≤ z.im := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have himupper : z.im ≤ 1 := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have hrecases : z.re = -1 ∨ z.re = 0 ∨ z.re = 1 := by omega
    have himcases : z.im = -1 ∨ z.im = 0 ∨ z.im = 1 := by omega
    rcases hrecases with hre | hre | hre <;> rcases himcases with him | him | him
    all_goals simp [hre, him, Zsqrtd.ext_iff] at hsum ⊢
  · rintro (rfl | rfl | rfl | rfl)
    -- The four displayed elements come in inverse pairs.
    all_goals rw [isUnit_iff_exists]
    · exact ⟨1, one_mul _, mul_one _⟩
    · exact ⟨-1, by ring, by ring⟩
    · exact ⟨⟨0, -1⟩, by ext <;> norm_num, by ext <;> norm_num⟩
    · exact ⟨⟨0, 1⟩, by ext <;> norm_num, by ext <;> norm_num⟩


private theorem hamilton_normSq_ne_zero (q : Hamilton) (hq : q ≠ zero) : normSq q ≠ 0 := by
  rintro h
  rcases q with ⟨a, b, c, d⟩
  dsimp [normSq] at h
  have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc2 : c ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd2 : d ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have ha : a = 0 := sq_eq_zero_iff.mp ha2
  have hb : b = 0 := sq_eq_zero_iff.mp hb2
  have hc : c = 0 := sq_eq_zero_iff.mp hc2
  have hd : d = 0 := sq_eq_zero_iff.mp hd2
  apply hq
  simp [zero, ha, hb, hc, hd]


private theorem hamilton_mul_inv (q : Hamilton) (hq : q ≠ zero) : mul q (inv q) = one := by
  rcases q with ⟨a, b, c, d⟩
  have hnorm : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≠ 0 := by
    simpa [normSq] using hamilton_normSq_ne_zero ⟨a, b, c, d⟩ hq
  ext <;> dsimp [mul, inv, scale, conj, normSq, one, zero] at *
  all_goals
    field_simp [hnorm]
    ring


private theorem hamilton_inv_mul (q : Hamilton) (hq : q ≠ zero) : mul (inv q) q = one := by
  rcases q with ⟨a, b, c, d⟩
  have hnorm : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≠ 0 := by
    simpa [normSq] using hamilton_normSq_ne_zero ⟨a, b, c, d⟩ hq
  ext <;> dsimp [mul, inv, scale, conj, normSq, one, zero] at *
  all_goals
    field_simp [hnorm]
    ring


theorem q22_hamilton_inverse_and_noncommutative (q : Hamilton) (hq : q ≠ zero) :
    (∃ r, mul q r = one ∧ mul r q = one) ∧ mul qi qj = neg (mul qj qi) := by
  -- Conjugation reverses the imaginary coordinates, and division by the positive squared norm
  -- makes it a two-sided inverse.  The coordinate multiplication also gives `ij = -ji`.
  refine ⟨⟨inv q, hamilton_mul_inv q hq, hamilton_inv_mul q hq⟩, ?_⟩
  simp [mul, qi, qj, neg]

end Solutions.RingTheory.Rings
