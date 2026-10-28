import QRHShort.QuotientSixthRoot
import Mathlib.Tactic.LinearCombination

/-!
Existence of a primary generator for each prime ideal away from 3. Two
successive reductions modulo omega - 1 determine a correcting sixth root of
unity; (omega - 1)^2 = -3 omega then gives congruence to one modulo 3.
This proves the existence required by the totalized `primaryGenerator` choice.
-/

noncomputable section
open Classical

namespace QRHShort

theorem omega_sub_one_sq : (omega - 1) ^ (2 : ℕ) = -3 * omega := by
  linear_combination omega_sq_add_omega_add_one

theorem omega_sub_one_prime : Prime (omega - 1) :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem omega_sub_one_dvd_three : omega - 1 ∣ (3 : O) :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_sub_one_dvd_prime'

theorem omega_sub_one_residues (a : O) :
    omega - 1 ∣ a ∨ omega - 1 ∣ a - 1 ∨ omega - 1 ∣ a + 1 :=
  IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one
    (IsCyclotomicExtension.zeta_spec 3 ℚ K) a

theorem isPrimary_iff_three_dvd (a : O) : IsPrimary a ↔ (3 : O) ∣ a - 1 :=
  Ideal.mem_span_singleton

private theorem exists_primary_unit_of_congr_one (a : O) (ha : omega - 1 ∣ a - 1) :
    ∃ u : Oˣ, IsPrimary ((u : O) * a) := by
  let η : Oˣ := ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
    (by decide)).unit
  have hη : (η : O) = omega := IsUnit.unit_spec _
  obtain ⟨t, ht⟩ := ha
  rcases omega_sub_one_residues t with h0 | h1 | hm1
  · obtain ⟨v, hv⟩ := h0
    refine ⟨1, (isPrimary_iff_three_dvd _).mpr ⟨-omega * v, ?_⟩⟩
    simp only [Units.val_one, one_mul]
    rw [ht, hv]
    calc
      (omega - 1) * ((omega - 1) * v) = (omega - 1) ^ (2 : ℕ) * v := by ring
      _ = 3 * (-omega * v) := by rw [omega_sub_one_sq]; ring
  · obtain ⟨v, hv⟩ := h1
    have haform : a = omega + (omega - 1) ^ (2 : ℕ) * v := by
      linear_combination ht + (omega - 1) * hv
    refine ⟨η ^ (2 : ℕ), (isPrimary_iff_three_dvd _).mpr ⟨-v, ?_⟩⟩
    simp only [Units.val_pow_eq_pow_val, hη]
    rw [haform, omega_sub_one_sq]
    calc
      omega ^ (2 : ℕ) * (omega + -3 * omega * v) - 1 =
          omega ^ (3 : ℕ) - 3 * omega ^ (3 : ℕ) * v - 1 := by ring
      _ = 3 * -v := by rw [omega_cube]; ring
  · obtain ⟨v, hv⟩ := hm1
    have haform : a = 2 - omega + (omega - 1) ^ (2 : ℕ) * v := by
      linear_combination ht + (omega - 1) * hv
    refine ⟨η, (isPrimary_iff_three_dvd _).mpr ⟨omega - omega ^ (2 : ℕ) * v, ?_⟩⟩
    rw [hη, haform, omega_sub_one_sq]
    calc
      omega * (2 - omega + -3 * omega * v) - 1 =
          -(omega ^ (2 : ℕ) + omega + 1) + 3 * omega - 3 * omega ^ (2 : ℕ) * v := by ring
      _ = 3 * (omega - omega ^ (2 : ℕ) * v) := by
        rw [omega_sq_add_omega_add_one]
        ring

/-- A sixth-root unit adjusts every element prime to omega - 1 to be primary. -/
theorem exists_primary_unit_of_not_dvd (a : O) (ha : ¬ omega - 1 ∣ a) :
    ∃ u : Oˣ, IsPrimary ((u : O) * a) := by
  rcases omega_sub_one_residues a with h0 | h1 | hm1
  · exact (ha h0).elim
  · exact exists_primary_unit_of_congr_one a h1
  · have hneg : omega - 1 ∣ -a - 1 := by
      convert dvd_neg.mpr hm1 using 1 <;> ring
    obtain ⟨u, hu⟩ := exists_primary_unit_of_congr_one (-a) hneg
    refine ⟨-u, ?_⟩
    simpa only [Units.val_neg, neg_mul, mul_neg] using hu

/-- Every prime ideal away from 3 has an actual primary generator. -/
theorem exists_primary_generator_of_prime {p : Ideal O} (hp : Prime p)
    (hthree : ¬ p ∣ principal 3) :
    ∃ a : O, principal a = p ∧ IsPrimary a := by
  let a := idealGenerator p
  have hgen : principal a = p := Ideal.span_singleton_generator p
  have ha0 : a ≠ 0 := by
    intro ha
    apply hp.ne_zero
    rw [← hgen, ha]
    simp [principal]
  have haprime : Prime a := by
    apply (Ideal.span_singleton_prime ha0).mp
    change (principal a).IsPrime
    rw [hgen]
    exact Ideal.isPrime_of_prime hp
  have hnot : ¬ omega - 1 ∣ a := by
    intro hdiv
    have ha3 : a ∣ (3 : O) :=
      (omega_sub_one_prime.associated_of_dvd haprime hdiv).symm.dvd.trans
        omega_sub_one_dvd_three
    apply hthree
    apply Ideal.dvd_span_singleton.mpr
    rw [← hgen]
    exact Ideal.mem_span_singleton.mpr ha3
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd a hnot
  refine ⟨(u : O) * a, ?_, hu⟩
  calc
    principal ((u : O) * a) = principal a := Ideal.span_singleton_mul_left_unit u.isUnit a
    _ = p := hgen

/-- The arithmetic exclusions include every prime above 3. -/
theorem exists_primary_generator_of_outside (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hout : Outside c.S p) :
    ∃ a : O, principal a = p ∧ IsPrimary a := by
  apply exists_primary_generator_of_prime hp
  intro hthree
  exact hout.2 p (c.above_three p hp hthree) (dvd_refl p)

end QRHShort
