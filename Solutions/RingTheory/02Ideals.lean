import Mathlib.Tactic

import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Idempotents

namespace Solutions.RingTheory.Ideals

variable {R S : Type*} [CommRing R] [CommRing S]


theorem q1_span_six_fifteen :
    Ideal.span ({(6 : ℤ), 15} : Set ℤ) = Ideal.span ({3} : Set ℤ) := by
  apply le_antisymm
  · -- Both generators lie in `(3)`.
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases hx with (rfl | rfl)
    · exact Ideal.mem_span_singleton.mpr ⟨2, by norm_num⟩
    · exact Ideal.mem_span_singleton.mpr ⟨5, by norm_num⟩
  · -- Bézout's identity `3 = -2·6 + 15` puts the generator of `(3)` in the other ideal.
    rw [Ideal.span_le]
    rintro x rfl
    have h6 : (6 : ℤ) ∈ Ideal.span ({(6 : ℤ), 15} : Set ℤ) := Ideal.subset_span (by simp)
    have h15 : (15 : ℤ) ∈ Ideal.span ({(6 : ℤ), 15} : Set ℤ) := Ideal.subset_span (by simp)
    convert (Ideal.span ({(6 : ℤ), 15} : Set ℤ)).add_mem
      ((Ideal.span ({(6 : ℤ), 15} : Set ℤ)).mul_mem_left (-2) h6) h15 using 1
    all_goals norm_num


theorem q2_mem_span_singleton_iff {R : Type*} [CommRing R] (a x : R) :
    x ∈ Ideal.span ({a} : Set R) ↔ ∃ r : R, a * r = x := by
  -- View the singleton generator as a family indexed by `Fin 1`.
  let hspan := Ideal.mem_span_range_iff_exists_fun (x := x) (v := fun _ : Fin 1 => a)
  simp at hspan
  rw [hspan]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f 0, ?_⟩
    simpa [mul_comm] using hf
  · rintro ⟨r, hr⟩
    refine ⟨fun _ : Fin 1 => r, ?_⟩
    simpa [mul_comm] using hr


theorem q3_span_singleton_le_iff {R : Type*} [CommRing R] (a : R) (I : Ideal R) :
    Ideal.span ({a} : Set R) ≤ I ↔ a ∈ I := by
  rw [Ideal.span_le]
  simp


theorem q4_span_singleton_eq_iff_associated {R : Type*} [CommRing R] [IsDomain R]
    (a b : R) (hb0 : b ≠ 0) :
    Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R) ↔
      ∃ u : R, IsUnit u ∧ a = b * u := by
  constructor
  · intro h
    have ha : a ∈ Ideal.span ({b} : Set R) := by
      rw [← h]
      exact Ideal.subset_span (by simp)
    obtain ⟨r, hbr⟩ := (q2_mem_span_singleton_iff b a).mp ha
    have hb : b ∈ Ideal.span ({a} : Set R) := by
      rw [h]
      exact Ideal.subset_span (by simp)
    obtain ⟨s, has⟩ := (q2_mem_span_singleton_iff a b).mp hb
    -- The two divisibility relations make the coefficients inverse to one another.
    have hrs_one : r * s = 1 := by
      apply mul_left_cancel₀ hb0
      calc
        b * (r * s) = (b * r) * s := by rw [mul_assoc]
        _ = a * s := by rw [hbr]
        _ = b := has
        _ = b * 1 := by rw [mul_one]
    exact ⟨r, isUnit_iff_exists_inv.mpr ⟨s, hrs_one⟩, hbr.symm⟩
  · rintro ⟨u, hu, hau⟩
    rcases hu with ⟨u, rfl⟩
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      intro x hx
      have hxa : x = a := Set.mem_singleton_iff.mp hx
      rw [hxa, hau]
      have hbmem : b ∈ Ideal.span ({b} : Set R) := Ideal.subset_span (by simp)
      rw [mul_comm]
      exact (Ideal.span ({b} : Set R)).mul_mem_left (↑u) hbmem
    · refine Ideal.span_le.2 ?_
      intro x hx
      have hxb : x = b := Set.mem_singleton_iff.mp hx
      rw [hxb]
      have hbu : b = a * (↑(u⁻¹) : R) := by
        rw [hau, mul_assoc]
        simp
      rw [hbu]
      have hamem : a ∈ Ideal.span ({a} : Set R) := Ideal.subset_span (by simp)
      rw [mul_comm]
      exact (Ideal.span ({a} : Set R)).mul_mem_left (↑(u⁻¹)) hamem


theorem q5_image_of_ideal_need_not_be_ideal :
    ¬ ∃ I : Ideal (ℤ × ℤ), ∀ x : ℤ × ℤ,
      x ∈ I ↔ ∃ n : ℤ, Int.castRingHom (ℤ × ℤ) n = x := by
  rintro ⟨I, hI⟩
  have hdiag : (1, 1) ∈ I := (hI (1, 1)).mpr ⟨1, rfl⟩
  have haxis : (1, 0) ∈ I := by
    simpa using I.mul_mem_left (1, 0) hdiag
  obtain ⟨n, hn⟩ := (hI (1, 0)).mp haxis
  have hfst := congrArg Prod.fst hn
  have hsnd := congrArg Prod.snd hn
  norm_num at hfst hsnd
  omega


theorem q6_exists_ideal_comap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : Ideal S) :
    ∃ I : Ideal R, ∀ r : R, r ∈ I ↔ f r ∈ J := by
  -- The required ideal is the inverse image of `J`; its closure follows from preservation of
  -- addition and multiplication by `f`.
  let I : Ideal R :=
    { carrier := {r | f r ∈ J}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simpa using J.add_mem hx hy
      smul_mem' := by
        intro r x hx
        simpa using J.mul_mem_left (f r) hx }
  exact ⟨I, fun _ => Iff.rfl⟩


theorem q7_quotient_comap_embeds_quotient {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : Ideal S) :
    ∃ g : R ⧸ Ideal.comap f J →+* S ⧸ J, Function.Injective g := by
  -- Descend the composite map to the quotient; its kernel is precisely the pulled-back ideal.
  let g : R ⧸ Ideal.comap f J →+* S ⧸ J :=
    Ideal.Quotient.lift (Ideal.comap f J) ((Ideal.Quotient.mk J).comp f)
      (by
        intro x hx
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  refine ⟨g, ?_⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change g (Ideal.Quotient.mk (Ideal.comap f J) r) = 0 ↔
    Ideal.Quotient.mk (Ideal.comap f J) r = 0
  change Ideal.Quotient.mk J (f r) = 0 ↔ Ideal.Quotient.mk (Ideal.comap f J) r = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  rfl


theorem q8_first_iso_ring (f : R →+* S) : Nonempty (R ⧸ RingHom.ker f ≃+* f.range) := by
  -- First descend `f` to the quotient: elements of its kernel become zero there.
  let g : R ⧸ RingHom.ker f →+* f.range :=
    Ideal.Quotient.lift (RingHom.ker f) f.rangeRestrict (by
      intro x hx
      exact Subtype.ext hx)
  -- No further identifications remain after quotienting by the kernel, and every point in the
  -- range still has a preimage.
  have hg_injective : Function.Injective g := by
    dsimp [g]
    exact RingHom.lift_injective_of_ker_le_ideal (RingHom.ker f) (f := f.rangeRestrict)
      (fun x hx => Subtype.ext hx) (RingHom.ker_rangeRestrict f).le
  have hg_surjective : Function.Surjective g := by
    apply Ideal.Quotient.lift_surjective_of_surjective
    exact f.rangeRestrict_surjective
  exact ⟨RingEquiv.ofBijective g ⟨hg_injective, hg_surjective⟩⟩


theorem q9_quotient_represents_maps_killing_ideal {R S : Type*} [CommRing R]
    [CommRing S] (I : Ideal R) (f : R →+* S) (hf : ∀ x : R, x ∈ I → f x = 0) :
    ∃ g : R ⧸ I →+* S, ∀ x : R, g (Ideal.Quotient.mk I x) = f x := by
  let g : R ⧸ I → S := Quotient.lift f (by
    intro x y hxy
    change I.quotientRel x y at hxy
    rw [Submodule.quotientRel_def] at hxy
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hf _ hxy)
  have g_mk (x : R) : g (Ideal.Quotient.mk I x) = f x := rfl
  refine ⟨{ toFun := g
            map_one' := by
              change g (Ideal.Quotient.mk I 1) = 1
              rw [g_mk, f.map_one]
            map_mul' := by
              rintro ⟨x⟩ ⟨y⟩
              change g (Ideal.Quotient.mk I (x * y)) =
                g (Ideal.Quotient.mk I x) * g (Ideal.Quotient.mk I y)
              rw [g_mk, g_mk, g_mk, f.map_mul]
            map_zero' := by
              change g (Ideal.Quotient.mk I 0) = 0
              rw [g_mk, f.map_zero]
            map_add' := by
              rintro ⟨x⟩ ⟨y⟩
              change g (Ideal.Quotient.mk I (x + y)) =
                g (Ideal.Quotient.mk I x) + g (Ideal.Quotient.mk I y)
              rw [g_mk, g_mk, g_mk, f.map_add] }, ?_⟩
  intro x
  rfl


theorem q10_two_idempotents_generate_idempotent_ideal {R : Type*} [CommRing R]
    (a b : R) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    ∃ e : R, IsIdempotentElem e ∧ Ideal.span ({a, b} : Set R) = Ideal.span ({e} : Set R) := by
  have ha_sq : a ^ 2 = a := by simpa [pow_two] using ha.eq
  have hb_sq : b ^ 2 = b := by simpa [pow_two] using hb.eq
  -- The join of two idempotent principal ideals is generated by `a + b - ab`.
  let e : R := a + b - a * b
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    change (a + b - a * b) * (a + b - a * b) = a + b - a * b
    ring_nf
    repeat rw [ha_sq, hb_sq]
    ring
  · ext x
    rw [Ideal.mem_span_pair, q2_mem_span_singleton_iff]
    constructor
    · rintro ⟨p, q, hx⟩
      refine ⟨p * a + q * b, ?_⟩
      rw [← hx]
      dsimp [e]
      ring_nf
      repeat rw [ha_sq, hb_sq]
      ring
    · rintro ⟨r, hr⟩
      refine ⟨r * (a - b), r * b, ?_⟩
      dsimp [e] at hr
      rw [← hr]
      ring_nf
      repeat rw [ha_sq, hb_sq]
      ring


theorem q11_coprime_inf_eq_mul {R : Type*} [CommRing R] (I J : Ideal R) (h : I + J = ⊤) :
    I ⊓ J = I * J := by
  apply le_antisymm
  · intro x hx
    -- Write `1 = u + v` with `u ∈ I` and `v ∈ J`, then distribute `x` across this equality.
    rw [Ideal.mem_inf] at hx
    have htop : (1 : R) ∈ I + J := by rw [h]; exact Submodule.mem_top
    rw [Ideal.add_eq_sup] at htop
    rcases Submodule.mem_sup.mp htop with ⟨u, hu, v, hv, huv⟩
    rw [show x = x * (u + v) by rw [huv, mul_one], mul_add]
    exact (I * J).add_mem (by simpa [mul_comm] using Ideal.mul_mem_mul hu hx.2)
      (Ideal.mul_mem_mul hx.1 hv)
  · exact le_inf Ideal.mul_le_right Ideal.mul_le_left


def idempotent_product_quotient_map {R : Type*} [CommRing R] (e : R) :
    R →+* (R ⧸ Ideal.span ({e} : Set R)) × R ⧸ Ideal.span ({1 - e} : Set R) :=
  (Ideal.Quotient.mk _).prod (Ideal.Quotient.mk _)


theorem q12_idempotent_gives_product_decomposition {R : Type*} [CommRing R] (e : R)
    (he : IsIdempotentElem e) :
    Function.Injective (idempotent_product_quotient_map e) ∧
      Function.Surjective (idempotent_product_quotient_map e) := by
  constructor
  · intro x y hxy
    -- The difference lies in both complementary principal ideals, so multiplying it by either
    -- complementary idempotent gives zero.
    change (Ideal.Quotient.mk (Ideal.span ({e} : Set R)) x,
      Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) =
      (Ideal.Quotient.mk (Ideal.span ({e} : Set R)) y,
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) y) at hxy
    have hx_e : x - y ∈ Ideal.span ({e} : Set R) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrArg Prod.fst hxy)
    have hx_one_sub_e : x - y ∈ Ideal.span ({1 - e} : Set R) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrArg Prod.snd hxy)
    have hmul_e : (x - y) * e = 0 := by
      rcases Ideal.mem_span_singleton.mp hx_one_sub_e with ⟨a, ha⟩
      rw [ha]
      calc
        ((1 - e) * a) * e = a * ((1 - e) * e) := by ring
        _ = 0 := by rw [mul_comm (1 - e) e, mul_sub, mul_one, he.eq, sub_self, mul_zero]
    have hmul_one_sub_e : (x - y) * (1 - e) = 0 := by
      rcases Ideal.mem_span_singleton.mp hx_e with ⟨a, ha⟩
      rw [ha]
      calc
        (e * a) * (1 - e) = a * (e * (1 - e)) := by ring
        _ = 0 := by rw [mul_sub, mul_one, he.eq, sub_self, mul_zero]
    apply sub_eq_zero.mp
    calc
      x - y = (x - y) * (e + (1 - e)) := by ring
      _ = (x - y) * e + (x - y) * (1 - e) := by rw [mul_add]
      _ = 0 := by rw [hmul_e, hmul_one_sub_e, add_zero]
  · rintro ⟨a, b⟩
    -- The element `x(1-e) + ye` has the prescribed two residue classes.
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨x * (1 - e) + y * e, ?_⟩
    change (Ideal.Quotient.mk (Ideal.span ({e} : Set R)) (x * (1 - e) + y * e),
      Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) (x * (1 - e) + y * e)) =
      (Ideal.Quotient.mk (Ideal.span ({e} : Set R)) x,
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) y)
    apply Prod.ext
    · rw [show x * (1 - e) = x - x * e by ring]
      simp
    · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      rw [Ideal.mem_span_singleton]
      refine ⟨x - y, ?_⟩
      ring


end Solutions.RingTheory.Ideals
