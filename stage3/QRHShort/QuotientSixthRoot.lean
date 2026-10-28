import QRHShort.ArithmeticBasics

/-!
Reduction of the distinguished sixth root modulo an ideal avoiding 2 and 3.
The proof uses explicit powers, so it applies even before making the quotient
a finite field. No reciprocity or primary-generator existence is assumed.
-/

noncomputable section

namespace QRHShort

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  simpa only [omega, IsUnit.unit_spec] using
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem rootSix_sq : rootSix ^ 2 = omega := by
  calc
    rootSix ^ 2 = omega ^ 3 * omega := by unfold rootSix; ring
    _ = omega := by rw [omega_cube, one_mul]

theorem rootSix_cube : rootSix ^ 3 = -1 := by
  calc
    rootSix ^ 3 = -(omega ^ 3) ^ 2 := by unfold rootSix; ring
    _ = -1 := by rw [omega_cube, one_pow]

theorem quotient_omega_isPrimitiveRoot (P : Ideal O) (hthree : ¬ P ∣ principal 3) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let w : O ⧸ P := Ideal.Quotient.mk P omega
  have hthree' : (3 : O ⧸ P) ≠ 0 := by
    intro h
    apply hthree
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h)
  have hw3 : w ^ 3 = 1 := by
    simpa only [map_pow, map_one] using congrArg (Ideal.Quotient.mk P) omega_cube
  have hwpoly : w ^ 2 + w + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg (Ideal.Quotient.mk P) omega_sq_add_omega_add_one
  have hw1 : w ≠ 1 := by
    intro h
    apply hthree'
    calc
      (3 : O ⧸ P) = 1 ^ 2 + 1 + 1 := by ring
      _ = 0 := by simpa only [h] using hwpoly
  refine IsPrimitiveRoot.mk_of_lt w (by decide) hw3 ?_
  intro l hl hl3
  interval_cases l
  · simpa only [pow_one] using hw1
  · intro h
    apply hw1
    calc
      w = w ^ 2 * w := by rw [h, one_mul]
      _ = w ^ 3 := by ring
      _ = 1 := hw3

theorem quotient_rootSix_isPrimitiveRoot (P : Ideal O)
    (htwo : ¬ P ∣ principal 2) (hthree : ¬ P ∣ principal 3) :
    IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6 := by
  let r : O ⧸ P := Ideal.Quotient.mk P rootSix
  have htwo' : (2 : O ⧸ P) ≠ 0 := by
    intro h
    apply htwo
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h)
  have hneg : (-1 : O ⧸ P) ≠ 1 := by
    intro h
    apply htwo'
    calc
      (2 : O ⧸ P) = 1 + 1 := by ring
      _ = 1 + -1 := by rw [h]
      _ = 0 := by ring
  have hr6 : r ^ 6 = 1 := by
    simpa only [map_pow, map_one] using
      congrArg (Ideal.Quotient.mk P) rootSix_pow_six
  have hr3 : r ^ 3 = -1 := by
    simpa only [map_pow, map_neg, map_one] using
      congrArg (Ideal.Quotient.mk P) rootSix_cube
  have hr2 : r ^ 2 = Ideal.Quotient.mk P omega := by
    simpa only [map_pow] using congrArg (Ideal.Quotient.mk P) rootSix_sq
  have hw := quotient_omega_isPrimitiveRoot P hthree
  have hr1 : r ≠ 1 := by
    intro h
    apply hneg
    simpa only [h, one_pow] using hr3.symm
  refine IsPrimitiveRoot.mk_of_lt r (by decide) hr6 ?_
  intro l hl hl6
  interval_cases l
  · simpa only [pow_one] using hr1
  · rw [hr2]
    exact hw.ne_one (by decide)
  · rw [hr3]
    exact hneg
  · intro h
    apply hw.pow_ne_one_of_pos_of_lt (l := 2) (by decide) (by decide)
    calc
      (Ideal.Quotient.mk P omega) ^ 2 = (r ^ 2) ^ 2 := by rw [hr2]
      _ = r ^ 4 := by ring
      _ = 1 := h
  · intro h
    apply hr1
    calc
      r = 1 * r := by rw [one_mul]
      _ = r ^ 5 * r := by rw [h]
      _ = r ^ 6 := by ring
      _ = 1 := hr6

theorem outside_quotient_rootSix_isPrimitiveRoot (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (houtside : Outside c.S P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6 := by
  have hnot : P ∉ c.S := by
    intro hmem
    exact houtside.2 P hmem (dvd_refl P)
  exact quotient_rootSix_isPrimitiveRoot P
    (fun h => hnot (c.above_two P hP h))
    (fun h => hnot (c.above_three P hP h))

end QRHShort
