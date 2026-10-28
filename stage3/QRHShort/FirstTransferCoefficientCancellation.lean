import QRHShort.FirstTransferCoefficientCancellationFactors

/-!
Cancelling the common ideal in the literal first-transfer coefficients.
The resulting conditions are exactly (f,C*t)=1 and ((h),t)=1; no relative
primality between the two remaining column ideals is assumed.
-/

noncomputable section
open Classical

namespace QRHShort

/-- Cancellation of the common squarefree factor leaves just its numerator
coprimality condition. The column ideals may share arbitrary prime factors. -/
theorem first_transfer_coefficient_cancel_common_factor (c : ArithmeticContext)
    (ξ : RayCharacter c) {C d t x y : Ideal O} (hC : Outside c.S C)
    (ht : SquarefreeOutside c.S t) (hx : SquarefreeOutside c.S x)
    (hy : SquarefreeOutside c.S y) (hCt : IsRelPrime C t)
    (hxt : IsRelPrime x t) (hyt : IsRelPrime y t) (hd : d ∣ C) (z : O) :
    firstTransferCoefficient c ξ C d 1 z (t * x) *
        star (firstTransferCoefficient c ξ C d 1 z (t * y)) =
      if IsRelPrime (principal z) t then
        firstTransferCoefficient c ξ C d t z x * star (firstTransferCoefficient c ξ C d t z y)
      else 0 := by
  rw [first_transfer_coefficient_mul c ξ C d z ht hx hxt,
    first_transfer_coefficient_mul c ξ C d z ht hy hyt, star_mul]
  calc
    _ = (firstTransferCoefficient c ξ C d 1 z t *
          star (firstTransferCoefficient c ξ C d 1 z t)) *
        (firstTransferCoefficient c ξ C d t z x *
          star (firstTransferCoefficient c ξ C d t z y)) := by ring
    _ = _ := by
      rw [first_transfer_coefficient_mul_star_filter c ξ hC ht hCt hd z]
      split_ifs <;> simp only [one_mul, zero_mul]

/-- The actual generator-square numerator has precisely the expected two
coprimality conditions, even when h is zero or the modulus is the unit ideal. -/
theorem first_transfer_coefficient_numerator_coprime_iff (c : ArithmeticContext)
    {f t : Ideal O} (hf : Outside c.S f) (h : O) :
    IsRelPrime (principal (h * primaryGenerator f ^ (2 : ℕ))) t ↔
      IsRelPrime (principal h) t ∧ IsRelPrime f t := by
  have hp : principal (h * primaryGenerator f ^ 2) = principal h * f ^ 2 := by
    calc
      principal (h * primaryGenerator f ^ 2) =
          principal h * principal (primaryGenerator f ^ 2) :=
        (Ideal.span_singleton_mul_span_singleton _ _).symm
      _ = principal h * principal (primaryGenerator f) ^ 2 := by
        simp only [principal, ← Ideal.span_singleton_pow]
      _ = principal h * f ^ 2 := by
        rw [(first_transfer_primaryGenerator_spec_and_primary_outside c hf).1]
  rw [hp, pow_two, IsRelPrime.mul_left_iff, IsRelPrime.mul_left_iff, and_self]

/-- The leading fourth-power symbol supplies the missing f,C filter. -/
theorem first_transfer_coefficient_leading_filter (c : ArithmeticContext)
    {C f : Ideal O} (hC : Outside c.S C) (hf : Outside c.S f) :
    sexticSymbol C (primaryGenerator f) ^ (4 : ℕ) *
        star (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ)) =
      if IsRelPrime f C then 1 else 0 := by
  rw [star_pow, ← mul_pow, first_transfer_sexticSymbol_mul_star c hC,
    (first_transfer_primaryGenerator_spec_and_primary_outside c hf).1]
  split_ifs <;> simp only [one_pow, zero_pow (by decide : (4 : ℕ) ≠ 0)]

/-- Exact common-ideal cancellation with the frozen numerator h*gen(f)^2.
Squarefreeness of C and f is unnecessary, and no x,y coprimality is imposed. -/
theorem first_transfer_coefficient_cancellation (c : ArithmeticContext)
    (ξ : RayCharacter c) {C d t x y f : Ideal O} (hC : Outside c.S C)
    (ht : SquarefreeOutside c.S t) (hx : SquarefreeOutside c.S x)
    (hy : SquarefreeOutside c.S y) (hf : Outside c.S f)
    (hCt : IsRelPrime C t) (hxt : IsRelPrime x t) (hyt : IsRelPrime y t)
    (hd : d ∣ C) (h : O) :
    (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ) *
        star (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ))) *
      firstTransferCoefficient c ξ C d 1 (h * primaryGenerator f ^ 2) (t * x) *
        star (firstTransferCoefficient c ξ C d 1 (h * primaryGenerator f ^ 2) (t * y)) =
      if IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t then
        firstTransferCoefficient c ξ C d t (h * primaryGenerator f ^ 2) x *
          star (firstTransferCoefficient c ξ C d t (h * primaryGenerator f ^ 2) y)
      else 0 := by
  rw [mul_assoc (sexticSymbol C (primaryGenerator f) ^ 4 *
    star (sexticSymbol C (primaryGenerator f) ^ 4))]
  rw [first_transfer_coefficient_leading_filter c hC hf,
    first_transfer_coefficient_cancel_common_factor c ξ hC ht hx hy hCt hxt hyt hd,
    first_transfer_coefficient_numerator_coprime_iff c hf,
    IsRelPrime.mul_right_iff]
  by_cases hfC : IsRelPrime f C <;> by_cases hft : IsRelPrime f t <;>
    by_cases hht : IsRelPrime (principal h) t <;>
    simp only [hfC, hft, hht, and_self, and_false, and_true, false_and, true_and,
      ite_true, ite_false, one_mul, zero_mul, mul_zero]

end QRHShort
