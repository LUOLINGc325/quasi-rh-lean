import QRHShort.QuotientSixthRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
The sixth-power test in the actual finite residue fields and the resulting
values of the concrete residue symbol. Primitivity of the image of `rootSix`
is an explicit local input here; the separate quotient-root argument supplies
it for primes away from 2 and 3. No reciprocity or primary-generator existence
is assumed by the finite-field calculation.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- Fermat's theorem evaluates the sixth-power residue test, including zero. -/
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

private theorem sexticAtPrime_eq_one_of_test_eq_one {P : Ideal O} {a : O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    (ha : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) = 1) :
    sexticAtPrime P a = 1 := by
  unfold sexticAtPrime
  simp_rw [ha]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    have hne : (1 : O ⧸ P) ≠ Ideal.Quotient.mk P (rootSix ^ j) := by
      intro heq
      apply hj0
      apply hζ.pow_inj (Finset.mem_range.mp hj) (by decide)
      simpa only [map_pow, pow_zero] using heq.symm
    simp only [if_neg hne]
  · simp

/-- The concrete local symbol takes the value one at one. -/
theorem sexticAtPrime_one {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) :
    sexticAtPrime P 1 = 1 := by
  exact sexticAtPrime_eq_one_of_test_eq_one hζ (by simp)

/-- For a prime denominator, a sixth power gives zero exactly on the prime. -/
theorem sexticAtPrime_sixth {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a : O) :
    sexticAtPrime P (a ^ (6 : ℕ)) = if a ∈ P then 0 else 1 := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have htest : Ideal.Quotient.mk P (a ^ (6 : ℕ)) ^ ((P.absNorm - 1) / 6) =
      if a ∈ P then 0 else 1 := by
    simpa only [map_pow, hcard, Ideal.Quotient.eq_zero_iff_mem] using
      finiteField_sixth_power_test hζ (Ideal.Quotient.mk P a)
  by_cases ha : a ∈ P
  · rw [if_pos ha]
    unfold sexticAtPrime
    apply Finset.sum_eq_zero
    intro j hj
    have hne : (0 : O ⧸ P) ≠ Ideal.Quotient.mk P (rootSix ^ j) := by
      simpa only [map_pow] using (pow_ne_zero j (hζ.ne_zero (by decide))).symm
    simp only [htest, if_pos ha, if_neg hne]
  · rw [if_neg ha]
    apply sexticAtPrime_eq_one_of_test_eq_one hζ
    simpa only [if_neg ha] using htest

/-- Extend the value at one over the actual multiset of ideal prime factors. -/
theorem sexticSymbol_one {n : Ideal O} (hn : n ≠ ⊥)
    (hζ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors n,
      IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) :
    sexticSymbol n 1 = 1 := by
  rw [sexticSymbol, if_neg hn]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  exact sexticAtPrime_one (hζ P hP)

/-- A sixth power of a generator of a prime ideal removes precisely its divisors. -/
theorem sexticSymbol_sixth_of_principal_prime {p n : Ideal O} {a : O}
    (hp : Prime p) (ha : principal a = p) (hn : n ≠ ⊥)
    (hζ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors n,
      IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) :
    sexticSymbol n (a ^ (6 : ℕ)) = if p ∣ n then 0 else 1 := by
  rw [sexticSymbol, if_neg hn]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    apply Multiset.prod_eq_zero
    have hmem : p ∈ UniqueFactorizationMonoid.normalizedFactors n :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mpr ⟨hp, hpn⟩
    refine Multiset.mem_map.mpr ⟨p, hmem, ?_⟩
    rw [sexticAtPrime_sixth hp (hζ p hmem)]
    apply if_pos
    apply (Ideal.span_singleton_le_iff_mem p).mp
    change principal a ≤ p
    exact ha.le
  · rw [if_neg hpn]
    apply Multiset.prod_eq_one
    intro z hz
    obtain ⟨P, hPmem, rfl⟩ := Multiset.mem_map.mp hz
    have hP : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hPmem
    rw [sexticAtPrime_sixth hP (hζ P hPmem)]
    apply if_neg
    intro haP
    have hPp : P ∣ p := Ideal.dvd_iff_le.mpr (by
      rw [← ha]
      exact (Ideal.span_singleton_le_iff_mem P).mpr haP)
    have heq : P = p := (prime_dvd_prime_iff_eq hP hp).mp hPp
    exact hpn (heq ▸ UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPmem)

/-- Every prime factor of an ideal outside `S` is itself outside `S`. -/
theorem outside_of_mem_normalizedFactors {S : Finset (Ideal O)} {n P : Ideal O}
    (hn : Outside S n) (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors n) :
    Outside S P := by
  refine ⟨(UniqueFactorizationMonoid.prime_of_normalized_factor P hP).ne_zero, ?_⟩
  intro q hq hqP
  exact hn.2 q hq (hqP.trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP))

/-- The actual symbol at one, with all local root conditions discharged. -/
theorem sexticSymbol_one_of_outside (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : sexticSymbol n 1 = 1 := by
  apply sexticSymbol_one hn.1
  intro P hP
  exact outside_quotient_rootSix_isPrimitiveRoot c
    (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    (outside_of_mem_normalizedFactors hn hP)

/-- The sixth-power sieve with only the actual principal-generator identity as input. -/
theorem sexticSymbol_sixth_of_outside (c : ArithmeticContext) {p n : Ideal O} {a : O}
    (hp : Prime p) (ha : principal a = p) (hn : Outside c.S n) :
    sexticSymbol n (a ^ (6 : ℕ)) = if p ∣ n then 0 else 1 := by
  apply sexticSymbol_sixth_of_principal_prime hp ha hn.1
  intro P hP
  exact outside_quotient_rootSix_isPrimitiveRoot c
    (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    (outside_of_mem_normalizedFactors hn hP)

end QRHShort
