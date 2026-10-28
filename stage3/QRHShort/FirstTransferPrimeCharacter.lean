import QRHShort.QuotientSixthRoot
import QRHShort.SquarefreeRayDescent

/-!
Local nontriviality of the literal sixth-power residue symbol. The finite-field
power map is onto the roots of unity of the prescribed order, using a generator
of the cyclic unit group. Evaluation then uses the frozen defining residue test.
No reciprocity, Gauss-sum evaluation, or primitivity premise is assumed.
-/

noncomputable section
open Classical

namespace QRHShort

/-- In a finite field containing a primitive m-th root, the usual power
test reaches every m-th root on a nonzero field element. -/
theorem first_transfer_finiteField_power_test_surjective {F : Type*}
    [Field F] [Fintype F] {m : ℕ} (hm : m ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) {w : F} (hw : w ^ m = 1) :
    ∃ a : F, a ≠ 0 ∧ a ^ ((Fintype.card F - 1) / m) = w := by
  letI : NeZero m := ⟨hm⟩
  have hMpos : 0 < Fintype.card F - 1 := by
    have hcard : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hdiv : m ∣ Fintype.card F - 1 :=
    (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero hm))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hgen : IsPrimitiveRoot (g : F) (Fintype.card F - 1) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have htest : IsPrimitiveRoot ((g : F) ^ ((Fintype.card F - 1) / m)) m :=
    hgen.pow hMpos (Nat.div_mul_cancel hdiv).symm
  obtain ⟨j, _, hj⟩ := htest.eq_pow_of_pow_eq_one hw
  refine ⟨(g : F) ^ j, pow_ne_zero j g.ne_zero, ?_⟩
  simpa only [← pow_mul, Nat.mul_comm] using hj

/-- Each of the six literal complex root values occurs at a residue unit. -/
theorem first_transfer_sexticAtPrime_surjective (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) (j : ℕ) (hj : j < 6) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      sexticAtPrime P a = embedding (rootSix ^ j) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hP hout
  have hroot : (Ideal.Quotient.mk P rootSix ^ j) ^ (6 : ℕ) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨x, hx, htest⟩ := first_transfer_finiteField_power_test_surjective
    (by decide : (6 : ℕ) ≠ 0) hζ hroot
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨a, ?_, ?_⟩
  · rw [ha]
    exact isUnit_iff_ne_zero.mpr hx
  · have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    apply SquarefreeReflection.RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj
    simpa only [hcard, ha, map_pow] using htest

theorem first_transfer_sexticAtPrime_hits_rootSix (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      sexticAtPrime P a = embedding rootSix := by
  simpa only [pow_one] using first_transfer_sexticAtPrime_surjective c hP hout 1 (by decide)

theorem first_transfer_embedding_rootSix_ne_one : embedding rootSix ≠ 1 := by
  intro h
  have hc : embedding rootSix ^ 3 = (-1 : ℂ) := by
    rw [← embedding_pow, rootSix_cube, embedding_neg, embedding_one]
  rw [h] at hc
  norm_num at hc

/-- A unit witness proves genuine nontriviality, independently of how a
multiplicative character on the residue ring is bundled. -/
theorem first_transfer_sexticAtPrime_nontrivial (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧ sexticAtPrime P a ≠ 1 := by
  obtain ⟨a, ha, hvalue⟩ := first_transfer_sexticAtPrime_hits_rootSix c hP hout
  exact ⟨a, ha, hvalue ▸ first_transfer_embedding_rootSix_ne_one⟩

end QRHShort
