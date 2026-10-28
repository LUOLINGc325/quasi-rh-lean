import QRHShort.CubeInversion
import QRHShort.SixthPowerResidue
import QRHShort.AnalyticObjects

/-! Uniform norm bounds for the actual cube-completion coefficients. -/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem norm_alpha_le_one (n : Ideal O) : ‖alpha n‖ ≤ 1 := by
  unfold alpha
  by_cases h : embedding (primaryGenerator n) = 0
  · simp only [h, norm_zero, Complex.ofReal_zero, div_zero, norm_zero, zero_le_one]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr h)]

theorem norm_sexticAtPrime_le_one {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (z : O) :
    ‖sexticAtPrime P z‖ ≤ 1 := by
  by_cases hex : ∃ j ∈ Finset.range 6,
      Ideal.Quotient.mk P z ^ ((P.absNorm - 1) / 6) =
        Ideal.Quotient.mk P (rootSix ^ j)
  · obtain ⟨j, hj, hjtest⟩ := hex
    have hsum : sexticAtPrime P z = embedding (rootSix ^ j) := by
      unfold sexticAtPrime
      rw [Finset.sum_eq_single j]
      · exact if_pos hjtest
      · intro i hi hij
        have hiTest : ¬ Ideal.Quotient.mk P z ^ ((P.absNorm - 1) / 6) =
            Ideal.Quotient.mk P (rootSix ^ i) := by
          intro hiTest
          apply hij
          apply hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
          simpa only [map_pow] using hiTest.symm.trans hjtest
        exact if_neg hiTest
      · exact fun h => (h hj).elim
    rw [hsum, norm_embedding_rootSix_pow]
  · have hzero : sexticAtPrime P z = 0 := by
      unfold sexticAtPrime
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (fun h => hex ⟨j, hj, h⟩)
    rw [hzero, norm_zero]
    exact zero_le_one

/-- At every ideal outside the excluded primes, the concrete symbol has norm at most one. -/
theorem norm_sexticSymbol_le_one (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (z : O) : ‖sexticSymbol n z‖ ≤ 1 := by
  have hprod : ∀ s : Multiset (Ideal O),
      (∀ P ∈ s, ‖sexticAtPrime P z‖ ≤ 1) →
        ‖(s.map (fun P => sexticAtPrime P z)).prod‖ ≤ 1 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | @cons P s ih =>
      intro hs
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      have hP := hs P (Multiset.mem_cons_self P s)
      have ht := ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ))
      simpa only [one_mul] using mul_le_mul hP ht (norm_nonneg _) zero_le_one
  rw [sexticSymbol, if_neg hn.1]
  apply hprod
  intro P hP
  exact norm_sexticAtPrime_le_one
    (outside_quotient_rootSix_isPrimitiveRoot c
      (prime_of_normalized_factor P hP) (outside_of_mem_normalizedFactors hn hP)) z

theorem norm_completedTwist_le_one (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f n : Ideal O) : ‖completedTwist c ξ k f n‖ ≤ 1 := by
  by_cases hn : Outside c.S n
  · rw [completedTwist, if_pos hn, norm_mul, norm_mul, norm_pow]
    have hξ : ‖rayValue ξ.val n‖ ≤ 1 := ξ.val.norm_onElement_le_one (primaryGenerator n)
    have hk := norm_sexticSymbol_le_one c hn k
    have hf := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sexticSymbol_le_one c hn (primaryGenerator f)) 4
    have hξk : ‖rayValue ξ.val n‖ * ‖sexticSymbol n k‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hξ hk (norm_nonneg _) zero_le_one
    simpa only [one_pow, one_mul] using
      mul_le_mul hξk hf (pow_nonneg (norm_nonneg _) _) zero_le_one
  · simp only [completedTwist, if_neg hn, norm_zero, zero_le_one]

/-- The reciprocal norm is a uniform majorant, also when the twist vanishes. -/
theorem norm_cubeWeight_le (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f b : Ideal O) : ‖cubeWeight c ξ k f b‖ ≤ (normIdeal b)⁻¹ := by
  by_cases hb : Outside c.S b
  · have hbpos := normIdeal_pos hb.1
    rw [cubeWeight, if_pos hb, norm_div, norm_mul, norm_pow, norm_star, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
    have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_alpha_le_one b) 3
    have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_completedTwist_le_one c ξ k f b) 3
    have hnum : ‖alpha b‖ ^ (3 : ℕ) * ‖completedTwist c ξ k f b‖ ^ (3 : ℕ) ≤ 1 := by
      simpa only [one_pow, one_mul] using
        mul_le_mul ha ht (pow_nonneg (norm_nonneg _) _) (by positivity : (0 : ℝ) ≤ 1 ^ (3 : ℕ))
    simpa only [one_div] using div_le_div_of_nonneg_right hnum hbpos.le
  · rw [cubeWeight, if_neg hb, norm_zero]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem norm_mobius_cubeWeight_le (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f h : Ideal O) :
    ‖(mobius h : ℂ) * cubeWeight c ξ k f h‖ ≤ (normIdeal h)⁻¹ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_mobius_le_one h) (norm_nonneg _)).trans
    (by simpa only [one_mul] using norm_cubeWeight_le c ξ k f h)

end QRHShort
