import QRHShort.QuotientSixthRoot
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
Arithmetic assembly for the unchanged `QuadraticEstimate` in `Estimates.lean`.
The first bridge identifies the actual cubic power of the sextic symbol with
the quadratic character of the residue field.  No family or sieve hypothesis
is assumed in this bridge.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The ordinary quadratic residue character, with values in the same complex
field as the concrete sextic symbol. -/
def quadraticResidueChar (P : Ideal O) [P.IsMaximal] : MulChar (O ⧸ P) ℂ := by
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ)

/-- Cubing the actual sixth-root sum gives the quadratic residue character;
the equality includes the value zero on the prime ideal. -/
theorem sexticAtPrime_cube_eq_quadraticResidueChar (P : Ideal O) [P.IsMaximal]
    (htwo : ¬ P ∣ principal 2) (hthree : ¬ P ∣ principal 3) (a : O) :
    sexticAtPrime P a ^ (3 : ℕ) =
      quadraticResidueChar P (Ideal.Quotient.mk P a) := by
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  change sexticAtPrime P a ^ (3 : ℕ) =
    ((quadraticChar (O ⧸ P) (Ideal.Quotient.mk P a) : ℤ) : ℂ)
  have hζ := quotient_rootSix_isPrimitiveRoot P htwo hthree
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcardpos : 1 < P.absNorm := by
    rw [hcard]
    exact Fintype.one_lt_card
  have hdvd : 6 ∣ P.absNorm - 1 := by
    rw [hcard]
    exact (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one _ (hζ.ne_zero (by decide)))
  have hexp : 0 < (P.absNorm - 1) / 6 :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by decide)
  have hmul : (P.absNorm - 1) / 6 * 6 = P.absNorm - 1 :=
    Nat.div_mul_cancel hdvd
  have hhalf : Fintype.card (O ⧸ P) / 2 = (P.absNorm - 1) / 6 * 3 := by
    rw [← hcard]
    omega
  have htwo' : (2 : O ⧸ P) ≠ 0 := by
    intro h
    apply htwo
    exact Ideal.dvd_span_singleton.mpr
      (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h))
  have hchar : ringChar (O ⧸ P) ≠ 2 := by
    intro h
    exact htwo' ((ringChar.spec (O ⧸ P) 2).mpr (by rw [h]))
  have hminus : (-1 : O ⧸ P) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two hchar
  have hcube : Ideal.Quotient.mk P rootSix ^ (3 : ℕ) = -1 := by
    simpa only [map_pow, map_neg, map_one] using
      congrArg (Ideal.Quotient.mk P) rootSix_cube
  by_cases ha : Ideal.Quotient.mk P a = 0
  · have hsum : sexticAtPrime P a = 0 := by
      unfold sexticAtPrime
      apply Finset.sum_eq_zero
      intro j hj
      have hjne : (0 : O ⧸ P) ≠ Ideal.Quotient.mk P (rootSix ^ j) := by
        simpa only [map_pow] using (pow_ne_zero j (hζ.ne_zero (by decide))).symm
      simp only [ha, zero_pow (Nat.ne_of_gt hexp), if_neg hjne]
    simp only [hsum, ha, zero_pow (by decide : (3 : ℕ) ≠ 0),
      quadraticChar_zero, Int.cast_zero]
  · have htest : (Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6)) ^ (6 : ℕ) = 1 := by
      rw [← pow_mul, hmul, hcard]
      exact FiniteField.pow_card_sub_one_eq_one _ ha
    obtain ⟨j, hj, hjtest⟩ := hζ.eq_pow_of_pow_eq_one htest
    have hsum : sexticAtPrime P a = embedding (rootSix ^ j) := by
      unfold sexticAtPrime
      rw [Finset.sum_eq_single j]
      · apply if_pos
        simpa only [map_pow] using hjtest.symm
      · intro i hi hij
        apply if_neg
        intro hiTest
        apply hij
        apply hζ.pow_inj (Finset.mem_range.mp hi) hj
        have hiEq : Ideal.Quotient.mk P rootSix ^ i =
            Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) := by
          simpa only [map_pow] using hiTest.symm
        exact hiEq.trans hjtest.symm
      · exact fun h => (h (Finset.mem_range.mpr hj)).elim
    have heuler : Ideal.Quotient.mk P a ^ (Fintype.card (O ⧸ P) / 2) =
        (-1 : O ⧸ P) ^ j := by
      calc
        _ = (Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6)) ^ (3 : ℕ) := by
          rw [← pow_mul, hhalf]
        _ = (Ideal.Quotient.mk P rootSix ^ j) ^ (3 : ℕ) := by rw [hjtest]
        _ = (Ideal.Quotient.mk P rootSix ^ (3 : ℕ)) ^ j := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm j 3]
        _ = (-1 : O ⧸ P) ^ j := by rw [hcube]
    have hembed : embedding (rootSix ^ j) ^ (3 : ℕ) = (-1 : ℂ) ^ j := by
      rw [embedding_pow, ← pow_mul, Nat.mul_comm j 3, pow_mul,
        ← embedding_pow, rootSix_cube, embedding_neg, embedding_one]
    rw [hsum, hembed, quadraticChar_eq_pow_of_char_ne_two hchar ha, heuler]
    interval_cases j <;> norm_num [hminus]

end QRHShort

#print axioms QRHShort.sexticAtPrime_cube_eq_quadraticResidueChar
