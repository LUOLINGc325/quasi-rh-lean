import QRHShort.FirstTransferPrimeCharacterPrimitivity
import QRHShort.PoissonStatements
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
The literal paired row character on the quotient by the product modulus.
The product quotient is identified by CRT, including when either factor is
the unit ideal and its quotient ring is trivial.
-/

noncomputable section
open Classical

namespace QRHShort

theorem first_transfer_ideal_isCoprime_of_isRelPrime {a b : Ideal O}
    (hab : IsRelPrime a b) : IsCoprime a b := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp (hab
    (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

theorem first_transfer_quotient_mul_isUnit_iff (a b : Ideal O) (hab : IsCoprime a b)
    (x : O ⧸ (a * b)) :
    IsUnit x ↔ IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x) ∧
      IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  rw [← isUnit_map_iff e x, Prod.isUnit_iff]
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

/-- A prescribed unit in one factor and 1 in the other lift to a unit of the
actual product quotient. No nontriviality of either quotient is required. -/
theorem first_transfer_crt_unit_lift (a b : Ideal O) (hab : IsCoprime a b)
    (u : O) (hu : IsUnit (Ideal.Quotient.mk a u)) :
    ∃ x : O, Ideal.Quotient.mk a x = Ideal.Quotient.mk a u ∧
      Ideal.Quotient.mk b x = 1 ∧ IsUnit (Ideal.Quotient.mk (a * b) x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (e.symm (Ideal.Quotient.mk a u, (1 : O ⧸ b)))
  have heq : e (Ideal.Quotient.mk (a * b) x) = (Ideal.Quotient.mk a u, (1 : O ⧸ b)) := by
    rw [hx, e.apply_symm_apply]
  have hxa : Ideal.Quotient.mk a x = Ideal.Quotient.mk a u := by
    simpa only [e, Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
      using congrArg Prod.fst heq
  have hxb : Ideal.Quotient.mk b x = 1 := by
    simpa only [e, Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
      using congrArg Prod.snd heq
  refine ⟨x, hxa, hxb, ?_⟩
  apply (first_transfer_quotient_mul_isUnit_iff a b hab _).mpr
  simpa only [Ideal.Quotient.factor_mk, hxa, hxb] using And.intro hu isUnit_one

/-- The quotient character has exactly the manuscript's sextic factor and
conjugate sextic factor, with zero extension on every nonunit. -/
def firstTransferPairedResidueCharacter (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b) :
    MulChar (O ⧸ (a * b)) ℂ where
  toFun x := firstTransferResidueCharacter c ha (Ideal.Quotient.factor Ideal.mul_le_left x) *
    star (firstTransferResidueCharacter c hb (Ideal.Quotient.factor Ideal.mul_le_right x))
  map_one' := by simp only [map_one, star_one, mul_one]
  map_mul' := by
    intro x y
    simp only [map_mul, star_mul]
    ring
  map_nonunit' := by
    intro x hx
    have hnot := mt (first_transfer_quotient_mul_isUnit_iff a b
      (first_transfer_ideal_isCoprime_of_isRelPrime hab) x).mpr hx
    by_cases hxa : IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x)
    · have hxb : ¬ IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) :=
        fun h => hnot ⟨hxa, h⟩
      rw [(firstTransferResidueCharacter c hb).map_nonunit hxb, star_zero, mul_zero]
    · rw [(firstTransferResidueCharacter c ha).map_nonunit hxa, zero_mul]

@[simp] theorem firstTransferPairedResidueCharacter_apply_mk (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (x : O) :
    firstTransferPairedResidueCharacter c ha hb hab (Ideal.Quotient.mk (a * b) x) =
      sexticSymbol a x * star (sexticSymbol b x) := by
  change firstTransferResidueCharacter c ha
      (Ideal.Quotient.factor Ideal.mul_le_left (Ideal.Quotient.mk (a * b) x)) *
    star (firstTransferResidueCharacter c hb
      (Ideal.Quotient.factor Ideal.mul_le_right (Ideal.Quotient.mk (a * b) x))) = _
  simp only [Ideal.Quotient.factor_mk, firstTransferResidueCharacter_apply_mk]

theorem first_transfer_sexticSymbol_eq_one_of_mk_eq_one (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) {x : O} (hx : Ideal.Quotient.mk a x = 1) :
    sexticSymbol a x = 1 := by
  rw [← firstTransferResidueCharacter_apply_mk c ha, hx, map_one]

end QRHShort
