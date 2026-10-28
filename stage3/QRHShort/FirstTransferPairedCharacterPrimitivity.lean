import QRHShort.FirstTransferPairedCharacter
import QRHShort.FirstTransferGeneratorNormalization
import Mathlib.Algebra.Squarefree.Basic

/-!
Primitivity of the paired literal character.  If a prime factor of one
squarefree denominator were absent from an inducing modulus, CRT supplies a
unit which is 1 modulo that inducing modulus but has a nontrivial local
sextic value.  The proof uses precisely agreement on product-modulus units.
-/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem first_transfer_squarefree_dvd_of_prime_dvd {n J : Ideal O}
    (hn : n ≠ ⊥) (hJ : J ≠ ⊥) (hsq : Squarefree n)
    (hprime : ∀ P : Ideal O, Prime P → P ∣ n → P ∣ J) : n ∣ J := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hn hJ).mpr
  apply (Multiset.le_iff_subset ((squarefree_iff_nodup_normalizedFactors hn).mp hsq)).mpr
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact (mem_normalizedFactors_iff hJ).mpr ⟨hp, hprime P hp (dvd_of_mem_normalizedFactors hP)⟩

/-- Missing a prime factor of the left denominator produces a unit witness
whose paired literal value is nontrivial, while its residue modulo J is 1. -/
theorem first_transfer_paired_left_missing_prime_witness (c : ArithmeticContext)
    {a b J P : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hP : Prime P) (hPa : P ∣ a)
    (hmod : a * b ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
      Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
  obtain ⟨A, hA⟩ := hPa
  have hPa' : P ∣ a := ⟨A, hA⟩
  have hAa : A ∣ a := ⟨P, hA.trans (mul_comm _ _)⟩
  have hPout := first_transfer_outside_of_dvd c ha.1 hPa'
  have hAout := first_transfer_outside_of_dvd c ha.1 hAa
  have hsq : Squarefree (P * (A * b)) := by
    rw [← mul_assoc, ← hA]
    exact squarefree_mul_iff.mpr ⟨hab, ha.2, hb.2⟩
  have hcop : IsCoprime P (A * b) :=
    first_transfer_ideal_isCoprime_of_isRelPrime (IsRelPrime.of_squarefree_mul hsq)
  have hJdiv : J ∣ P * (A * b) := by
    rw [← mul_assoc, ← hA]
    exact Ideal.dvd_iff_le.mpr hmod
  have hJrest : J ∣ A * b :=
    ((hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot).symm).dvd_of_dvd_mul_left hJdiv
  obtain ⟨u, hu, hζ⟩ := first_transfer_prime_character_hits_rootSix c hP hPout
  obtain ⟨x, hxP, hxrest, hxunit⟩ := first_transfer_crt_unit_lift P (A * b) hcop u hu
  have hxJ : Ideal.Quotient.mk J x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (Ideal.le_of_dvd hJrest)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxA : Ideal.Quotient.mk A x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (show A * b ≤ A from Ideal.mul_le_left)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxb : Ideal.Quotient.mk b x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (show A * b ≤ b from Ideal.mul_le_right)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxPvalue : sexticSymbol P x = embedding rootSix := by
    apply (firstTransferSexticSymbol_congr hxP).trans
    simpa only [firstTransferResidueCharacter_apply_mk] using hζ
  have hxvalue : sexticSymbol a x * star (sexticSymbol b x) = embedding rootSix := by
    rw [hA, first_transfer_sexticSymbol_mul,
      first_transfer_sexticSymbol_eq_one_of_mk_eq_one c hAout hxA,
      first_transfer_sexticSymbol_eq_one_of_mk_eq_one c hb.1 hxb, hxPvalue]
    simp only [star_one, mul_one]
  refine ⟨x, ?_, hxJ, ?_⟩
  · rw [hA, mul_assoc]
    exact hxunit
  · rw [hxvalue]
    exact first_transfer_embedding_rootSix_ne_one

theorem first_transfer_paired_right_missing_prime_witness (c : ArithmeticContext)
    {a b J P : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hP : Prime P) (hPb : P ∣ b)
    (hmod : a * b ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
      Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
  obtain ⟨x, hxunit, hxJ, hxvalue⟩ := first_transfer_paired_left_missing_prime_witness c
    hb ha hab.symm hP hPb (by simpa only [mul_comm] using hmod) hnot
  refine ⟨x, ?_, hxJ, ?_⟩
  · rw [mul_comm a b]
    exact hxunit
  · intro h
    apply hxvalue
    have hh := congrArg star h
    simpa only [star_mul, star_star, star_one, mul_comm] using hh

/-- The exact unit-agreement condition required by PrimitiveResidueCharacter. -/
theorem firstTransferPairedResidueCharacter_primitive (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (J : Ideal O) (hJ : J ≠ ⊥) (hmod : a * b ≤ J)
    (ψ : MulChar (O ⧸ J) ℂ)
    (hagrees : ∀ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) →
      firstTransferPairedResidueCharacter c ha.1 hb.1 hab (Ideal.Quotient.mk (a * b) x) =
        ψ (Ideal.Quotient.mk J x)) : J = a * b := by
  have hab0 : a * b ≠ ⊥ := mul_ne_zero ha.1.1 hb.1.1
  have hsq : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨hab, ha.2, hb.2⟩
  have hdiv : a * b ∣ J := first_transfer_squarefree_dvd_of_prime_dvd hab0 hJ hsq (by
    intro P hP hPab
    by_contra hnot
    have hex : ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
        Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
      rcases hP.dvd_mul.mp hPab with hPa | hPb
      · exact first_transfer_paired_left_missing_prime_witness c ha hb hab hP hPa hmod hnot
      · exact first_transfer_paired_right_missing_prime_witness c ha hb hab hP hPb hmod hnot
    obtain ⟨x, hxunit, hxJ, hxvalue⟩ := hex
    apply hxvalue
    have h := hagrees x hxunit
    simpa only [firstTransferPairedResidueCharacter_apply_mk, hxJ, map_one] using h)
  exact le_antisymm (Ideal.le_of_dvd hdiv) hmod

/-- A primitive character for the literal paired sextic row, including the
principal character when both denominator ideals are the unit ideal. -/
def firstTransferPrimitivePairedCharacter (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b) :
    PrimitiveResidueCharacter where
  modulus := a * b
  modulus_ne_bot := mul_ne_zero ha.1.1 hb.1.1
  character := firstTransferPairedResidueCharacter c ha.1 hb.1 hab
  primitive := by
    intro J hJ hmod hfactor
    obtain ⟨ψ, hagrees⟩ := hfactor
    exact firstTransferPairedResidueCharacter_primitive c ha hb hab J hJ hmod ψ hagrees

@[simp] theorem firstTransferPrimitivePairedCharacter_modulus (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) : (firstTransferPrimitivePairedCharacter c ha hb hab).modulus = a * b := rfl

@[simp] theorem firstTransferPrimitivePairedCharacter_value (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (x : O) :
    (firstTransferPrimitivePairedCharacter c ha hb hab).value x =
      sexticSymbol a x * star (sexticSymbol b x) :=
  firstTransferPairedResidueCharacter_apply_mk c ha.1 hb.1 hab x

end QRHShort
