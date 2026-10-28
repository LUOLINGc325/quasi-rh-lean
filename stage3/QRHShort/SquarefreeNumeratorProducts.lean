import QRHShort.SquarefreeRayDescent

/-! Numerator multiplication and finite products for the frozen sextic symbol.
Only the verified local sixth-root prerequisites are imported. -/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.SquarefreeReflection
open RayValuePrerequisites

namespace NumeratorPrerequisites

@[simp] theorem embedding_mul (a b : O) :
    embedding (a * b) = embedding a * embedding b := by
  simpa only [embeddingHom_apply] using map_mul embeddingHom a b

theorem finiteField_sixth_power_test {F : Type*} [Field F] [Fintype F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (a : F) :
    (a ^ (6 : ℕ)) ^ ((Fintype.card F - 1) / 6) = if a = 0 then 0 else 1 := by
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  have hdvd : 6 ∣ Fintype.card F - 1 :=
    (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero (by decide)))
  have hpos : 0 < (Fintype.card F - 1) / 6 :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by decide)
  by_cases ha : a = 0
  · simp [ha, Nat.ne_of_gt hpos]
  · rw [if_neg ha, ← pow_mul, Nat.mul_div_cancel' hdvd]
    exact FiniteField.pow_card_sub_one_eq_one a ha

end NumeratorPrerequisites

open NumeratorPrerequisites

theorem sexticSymbol_one_of_outside (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : sexticSymbol n 1 = 1 := by
  simpa only [pow_zero, embedding_one, one_pow] using
    sexticSymbol_rootSix_pow_formula c hn 0

theorem sexticAtPrime_zero_of_mem {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a : O} (ha : a ∈ P) : sexticAtPrime P a = 0 := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have ht6 := finiteField_sixth_power_test hζ (Ideal.Quotient.mk P a)
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr ha)] at ht6
  have ht : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 6)
    simpa only [← pow_mul, Nat.mul_comm, hcard] using ht6
  unfold sexticAtPrime
  apply Finset.sum_eq_zero
  intro j _
  apply if_neg
  rw [ht, map_pow]
  exact (pow_ne_zero j (hζ.ne_zero (by decide))).symm

theorem sexticAtPrime_index {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a : O} (ha : a ∉ P) :
    ∃ j < 6, Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) =
      Ideal.Quotient.mk P (rootSix ^ j) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have ht6 := finiteField_sixth_power_test hζ (Ideal.Quotient.mk P a)
  rw [if_neg (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))] at ht6
  have ht : (Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6)) ^ 6 = 1 := by
    simpa only [← pow_mul, Nat.mul_comm, hcard] using ht6
  obtain ⟨j, hj, heq⟩ := hζ.eq_pow_of_pow_eq_one ht
  exact ⟨j, hj, by simpa only [map_pow] using heq.symm⟩

/-- Multiplicativity in the numerator, with no coprimality restriction. -/
theorem sexticAtPrime_mul {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a b : O) :
    sexticAtPrime P (a * b) = sexticAtPrime P a * sexticAtPrime P b := by
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hP hζ (P.mul_mem_right b ha),
      sexticAtPrime_zero_of_mem hP hζ ha, zero_mul]
  by_cases hb : b ∈ P
  · rw [sexticAtPrime_zero_of_mem hP hζ (P.mul_mem_left a hb),
      sexticAtPrime_zero_of_mem hP hζ hb, mul_zero]
  obtain ⟨i, hi, hit⟩ := sexticAtPrime_index hP hζ ha
  obtain ⟨j, hj, hjt⟩ := sexticAtPrime_index hP hζ hb
  have hij : Ideal.Quotient.mk P (a * b) ^ ((P.absNorm - 1) / 6) =
      Ideal.Quotient.mk P (rootSix ^ ((i + j) % 6)) := by
    rw [rootSix_pow_mod, map_mul, mul_pow, hit, hjt, ← map_mul, ← pow_add]
  rw [sexticAtPrime_eq_of_test hζ (Nat.mod_lt _ (by decide)) hij,
    sexticAtPrime_eq_of_test hζ hi hit, sexticAtPrime_eq_of_test hζ hj hjt,
    rootSix_pow_mod, pow_add, embedding_mul]

theorem sexticSymbol_mul_numerator (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (a b : O) :
    sexticSymbol n (a * b) = sexticSymbol n a * sexticSymbol n b := by
  simp only [sexticSymbol, if_neg hn.1]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  exact sexticAtPrime_mul (prime_of_normalized_factor P hP)
    (outside_quotient_rootSix_isPrimitiveRoot c (prime_of_normalized_factor P hP)
      (outside_of_mem_normalizedFactors hn hP)) a b

theorem sexticSymbol_prod_numerator (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) {ι : Type*} (s : Finset ι) (f : ι → O) :
    sexticSymbol n (∏ i ∈ s, f i) = ∏ i ∈ s, sexticSymbol n (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using sexticSymbol_one_of_outside c hn
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, sexticSymbol_mul_numerator c hn, ih,
      Finset.prod_insert hi]

end QRHShort.SquarefreeReflection

#print axioms QRHShort.SquarefreeReflection.sexticAtPrime_mul
#print axioms QRHShort.SquarefreeReflection.sexticSymbol_one_of_outside
#print axioms QRHShort.SquarefreeReflection.sexticSymbol_mul_numerator
#print axioms QRHShort.SquarefreeReflection.sexticSymbol_prod_numerator
