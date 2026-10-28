import QRHShort.FirstTransferGaussCRTPhase
import QRHShort.FirstTransferPairedCharacterPrimitivity

/-!
CRT factorization of the actual normalized paired Gauss sum. The twist,
normalization, residue representatives, and chosen generators agree with
the frozen definitions, including the unit-ideal cases.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_gauss_sqrt_norm_inv_mul (a b : Ideal O) :
    (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ =
      (Real.sqrt (normIdeal a) : ℂ)⁻¹ * (Real.sqrt (normIdeal b) : ℂ)⁻¹ := by
  simp only [normIdeal, map_mul, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, mul_inv]

/-- The exact normalized CRT identity for the literal paired character.
No primitivity or nontriviality assumption on the quotient is needed. -/
theorem first_transfer_paired_gauss_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    [Fintype (O ⧸ (a * b))] :
    (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ *
      (∑ x : O ⧸ (a * b), firstTransferPairedResidueCharacter c ha hb hab x *
        additiveCharacter (embedding (residueLift (a * b) x) /
          embedding (chosenGenerator (a * b)))) =
      sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
        gauss 1 a * gauss (-1) b := by
  letI : Finite (O ⧸ a) := Ring.HasFiniteQuotients.finiteQuotient ha.1
  letI : Finite (O ⧸ b) := Ring.HasFiniteQuotients.finiteQuotient hb.1
  letI : Fintype (O ⧸ a) := Fintype.ofFinite _
  letI : Fintype (O ⧸ b) := Fintype.ofFinite _
  have hout := (first_transfer_outside_mul_iff c a b).mpr ⟨ha, hb⟩
  rw [first_transfer_chosenGenerator_eq_primaryGenerator c hout]
  change (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ *
    (∑ x : O ⧸ (a * b), firstTransferPairedResidueCharacter c ha hb hab x *
      firstTransferGaussPhase (a * b) x) = _
  rw [first_transfer_paired_gauss_crt_sum c ha hb hab,
    first_transfer_gauss_sqrt_norm_inv_mul]
  simp_rw [first_transfer_gauss_sextic_star_eq_neg_one c hb]
  simp only [gauss, dif_pos ha.1, dif_pos hb.1, zpow_one, firstTransferGaussPhase]
  ring

/-- The preceding finite-sum formula is precisely the Gauss sum attached
to the concrete primitive character for a squarefree coprime pair. -/
theorem first_transfer_primitive_paired_gauss_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    (firstTransferPrimitivePairedCharacter c ha hb hab).gauss =
      sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
        gauss 1 a * gauss (-1) b := by
  letI : Finite (O ⧸ (a * b)) :=
    Ring.HasFiniteQuotients.finiteQuotient (mul_ne_zero ha.1.1 hb.1.1)
  letI : Fintype (O ⧸ (a * b)) := Fintype.ofFinite _
  exact first_transfer_paired_gauss_crt c ha.1 hb.1 hab

end QRHShort
