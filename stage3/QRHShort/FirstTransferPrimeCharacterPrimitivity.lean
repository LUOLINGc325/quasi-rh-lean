import QRHShort.FirstTransferPrimeCharacter
import QRHShort.FirstTransferResidueCharacter
import QRHShort.SquarefreePrimeSymbol

/-!
Nontriviality and prime-modulus primitivity of the actual residue character.
Primitivity is stated as an explicit quotient-factorization property: a
character modulo an ideal J containing P that agrees on every unit modulo P
must already have J = P. Agreement is on units, as required for characters
extended by zero on nonunits.
-/

noncomputable section
open Classical

namespace QRHShort

theorem first_transfer_prime_character_hits_rootSix (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      firstTransferResidueCharacter c hout (Ideal.Quotient.mk P a) = embedding rootSix := by
  obtain ⟨a, ha, hv⟩ := first_transfer_sexticAtPrime_hits_rootSix c hP hout
  refine ⟨a, ha, ?_⟩
  rw [firstTransferResidueCharacter_apply_mk, SquarefreeReflection.sexticSymbol_prime hP]
  exact hv

/-- The bundled character is genuinely nontrivial on residue units. -/
theorem first_transfer_prime_character_ne_one (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    firstTransferResidueCharacter c hout ≠ 1 := by
  intro h
  obtain ⟨a, ha, hv⟩ := first_transfer_prime_character_hits_rootSix c hP hout
  rw [h, MulChar.one_apply ha] at hv
  exact first_transfer_embedding_rootSix_ne_one hv.symm

/-- Prime-modulus primitivity, expressed without introducing a new
conductor definition or a squarefree CRT assertion. -/
theorem first_transfer_prime_character_primitive (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P)
    (J : Ideal O) (hPJ : P ≤ J) (χ : MulChar (O ⧸ J) ℂ)
    (hagrees : ∀ a : O, IsUnit (Ideal.Quotient.mk P a) →
      firstTransferResidueCharacter c hout (Ideal.Quotient.mk P a) =
        χ (Ideal.Quotient.mk J a)) : J = P := by
  have hmax : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  by_cases hJ : J = ⊤
  · subst J
    obtain ⟨a, ha, hv⟩ := first_transfer_prime_character_hits_rootSix c hP hout
    have htop : Ideal.Quotient.mk (⊤ : Ideal O) a = 1 := Subsingleton.elim _ _
    have heq := hagrees a ha
    rw [htop, map_one, hv] at heq
    exact False.elim (first_transfer_embedding_rootSix_ne_one heq)
  · exact (hmax.eq_of_le hJ hPJ).symm

end QRHShort
