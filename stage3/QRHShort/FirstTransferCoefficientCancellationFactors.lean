import QRHShort.FirstTransferReduction
import QRHShort.FirstTransferSymbolIdentities
import QRHShort.FirstTransferGeneratorNormalization
import QRHShort.FirstTransferRayFourierInput
import QRHShort.FirstTransferGaussCoefficient

/-!
Literal multiplicativity and norm filters for the first-transfer coefficient.
The arbitrary ray character cancels by its actual finite-group norm, without
using arithmetic reciprocity relations.
-/

noncomputable section
open Classical

namespace QRHShort

theorem first_transfer_rayValue_mul_outside (c : ArithmeticContext) (ξ : RayCharacter c)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) :
    rayValue ξ.val (a * b) = rayValue ξ.val a * rayValue ξ.val b := by
  simp only [rayValue, first_transfer_primaryGenerator_mul_outside c ha hb,
    HeckeCharacter.onElement, map_mul]

theorem first_transfer_rayValue_mul_star_outside (c : ArithmeticContext) (ξ : RayCharacter c)
    {n : Ideal O} (hn : Outside c.S n) :
    rayValue ξ.val n * star (rayValue ξ.val n) = 1 := by
  have hnorm : ‖rayValue ξ.val n‖ = 1 := by
    rw [FirstTransferRayFourier.rayValue_eq_rayClassCharacter c ξ hn]
    exact FirstTransferRayFourier.norm_rayClassCharacter c ξ _
  simpa only [starRingEnd_apply, hnorm, one_pow, Complex.ofReal_one] using
    Complex.mul_conj' (rayValue ξ.val n)

/-- Splitting off a squarefree relatively-prime factor gives the literal
coefficient at that factor times the coefficient with the new restriction. -/
theorem first_transfer_coefficient_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d : Ideal O) (z : O) {t n : Ideal O}
    (ht : SquarefreeOutside c.S t) (hn : SquarefreeOutside c.S n)
    (hnt : IsRelPrime n t) :
    firstTransferCoefficient c ξ C d 1 z (t * n) =
      firstTransferCoefficient c ξ C d 1 z t * firstTransferCoefficient c ξ C d t z n := by
  have htn : SquarefreeOutside c.S (t * n) :=
    ⟨(first_transfer_outside_mul_iff c t n).mpr ⟨ht.1, hn.1⟩,
      squarefree_mul_iff.mpr ⟨hnt.symm, ht.2, hn.2⟩⟩
  simp only [firstTransferCoefficient,
    ite_eq_left (show SquarefreeOutside c.S (t * n) ∧ IsRelPrime (t * n) 1 from
      ⟨htn, isRelPrime_one_right⟩),
    ite_eq_left (show SquarefreeOutside c.S t ∧ IsRelPrime t 1 from
      ⟨ht, isRelPrime_one_right⟩), ite_eq_left (show SquarefreeOutside c.S n ∧
      IsRelPrime n t from ⟨hn, hnt⟩),
    mobius, hnt.symm.moebius_mul, Int.cast_mul,
    first_transfer_rayValue_mul_outside c ξ ht.1 hn.1,
    first_transfer_sexticSymbol_mul, star_mul, mul_pow]
  ring

/-- The squared magnitude of the common factor is exactly its numerator
coprimality filter, since d divides C and C is relatively prime to t. -/
theorem first_transfer_coefficient_mul_star_filter (c : ArithmeticContext)
    (ξ : RayCharacter c) {C d t : Ideal O} (hC : Outside c.S C)
    (ht : SquarefreeOutside c.S t) (hCt : IsRelPrime C t) (hd : d ∣ C) (z : O) :
    firstTransferCoefficient c ξ C d 1 z t *
        star (firstTransferCoefficient c ξ C d 1 z t) =
      if IsRelPrime (principal z) t then 1 else 0 := by
  have hdout := first_transfer_outside_of_dvd c hC hd
  have hCunit : sexticSymbol t (primaryGenerator C) *
      star (sexticSymbol t (primaryGenerator C)) = 1 := by
    rw [first_transfer_sexticSymbol_mul_star c ht.1,
      (first_transfer_primaryGenerator_spec_and_primary_outside c hC).1,
      ite_eq_left hCt]
  have hdunit : sexticSymbol t (primaryGenerator d) *
      star (sexticSymbol t (primaryGenerator d)) = 1 := by
    rw [first_transfer_sexticSymbol_mul_star c ht.1,
      (first_transfer_primaryGenerator_spec_and_primary_outside c hdout).1,
      ite_eq_left (hCt.of_dvd_left hd)]
  simp only [firstTransferCoefficient,
    ite_eq_left (show SquarefreeOutside c.S t ∧ IsRelPrime t 1 from
      ⟨ht, isRelPrime_one_right⟩), star_mul, star_star, star_pow, star_intCast]
  calc
    _ = (mobius t : ℂ) ^ 2 *
        (rayValue ξ.val t * star (rayValue ξ.val t)) *
        (sexticSymbol t z * star (sexticSymbol t z)) *
        (sexticSymbol t (primaryGenerator C) *
          star (sexticSymbol t (primaryGenerator C))) ^ (4 : ℕ) *
        (sexticSymbol t (primaryGenerator d) *
          star (sexticSymbol t (primaryGenerator d))) := by ring
    _ = _ := by
      rw [first_transfer_mobius_sq ht.2, first_transfer_rayValue_mul_star_outside c ξ ht.1,
        hCunit, hdunit, first_transfer_sexticSymbol_mul_star c ht.1]
      simp only [one_mul, one_pow, mul_one]

end QRHShort
