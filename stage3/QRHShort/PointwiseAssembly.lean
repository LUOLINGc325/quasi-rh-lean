import QRHShort.PrimeRowBridge
import QRHShort.IdealCounting
import QRHShort.DyadicPrimes
import QRHShort.APDyadicBridge
import QRHShort.SixthPowerResidue
import QRHShort.PrimaryGenerator
import QRHShort.Estimates
import QRHShort.MainStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The prime-row extraction for the actual arithmetic sums, including the bounded
range of D. Primary-generator existence, finite-field symbol identities, and ideal-counting
bounds are proved in the imported modules. The endpoint therefore requires only
the original arithmetic mean-square estimate.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- A common finite support gives a bound uniform for every positive D ≤ T. -/
theorem originalSum_norm_le_card_weightNorm (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) (J : ℕ)
    {D T : ℝ} (hD : 0 < D) (hDT : D ≤ T) :
    ‖originalSum c W D 1‖ ≤
      ((boundedDivisibleIdeals 1 (I.hi * T)).card : ℝ) * weightNorm J W := by
  have hsum : originalSum c W D 1 =
      ∑ n ∈ boundedDivisibleIdeals 1 (I.hi * T), if Outside c.S n then
        (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0 := by
    unfold originalSum
    calc
      _ = ∑' n : Ideal O, if Outside c.S n then
          (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0 := by
        apply tsum_congr
        intro n
        by_cases hn : Outside c.S n
        · simp only [if_pos hn, sexticSymbol_one_of_outside c hn, mul_one]
        · simp only [if_neg hn]
      _ = _ := by
        apply tsum_eq_sum
        intro n hn
        by_cases hout : Outside c.S n
        · rw [if_pos hout]
          have hzero : W (normIdeal n / D) = 0 := by
            by_contra hw
            have hnorm : normIdeal n ≤ I.hi * T :=
              ((div_le_iff₀ hD).mp (hW.2 hw).2).trans
                (mul_le_mul_of_nonneg_left hDT (I.lo_pos.trans_le I.ordered).le)
            exact hn (mem_boundedDivisibleIdeals.mpr ⟨hnorm, one_dvd n, hout.1⟩)
          simp only [hzero, mul_zero]
        · simp only [if_neg hout]
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ boundedDivisibleIdeals 1 (I.hi * T),
        ‖if Outside c.S n then
          (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ boundedDivisibleIdeals 1 (I.hi * T), weightNorm J W := by
      apply Finset.sum_le_sum
      intro n _
      split_ifs
      · have hcoeff : ‖(mobius n : ℂ) * c.nu.onIdeal n‖ ≤ 1 := by
          rw [norm_mul]
          simpa only [one_mul] using mul_le_mul (norm_mobius_le_one n)
            (c.nu.norm_onIdeal_le_one n) (norm_nonneg _) zero_le_one
        have hweight : ‖W (normIdeal n / D)‖ ≤ weightNorm J W := by
          simpa only [iteratedDeriv_zero] using
            norm_iteratedDeriv_le_weightNorm hW (Nat.zero_le J) (normIdeal n / D)
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hcoeff hweight (norm_nonneg _) zero_le_one
      · simpa only [norm_zero] using weightNorm_nonneg hW J
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Actual prime-ideal extraction of the 11/12 bound. Primary-generator existence
is stated explicitly and is not inferred from the totalized choice definition. -/
theorem pointwise_of_meanSquare_of_primary (hm : MeanSquareEstimate)
    (hprimary : ∀ (c : ArithmeticContext) (p : Ideal O), Prime p → Outside c.S p →
      ∃ z : O, principal z = p ∧ IsPrimary z) :
    PointwiseMobiusEstimate := by
  intro c I W ε hW hε
  obtain ⟨θ, η, hθ, hθupper, hη, hloss⟩ := arbitrarily_small_prime_losses hε
  obtain ⟨J, hJ, hmean⟩ := hm θ η hθ hθupper hη
  obtain ⟨K, hK, hmean⟩ := hmean c I
  obtain ⟨E, hE, herror⟩ := exists_sixth_row_error_weightNorm I
  obtain ⟨c₀, hc, Y₀, hY₀, hcount⟩ := dyadicPrimeFinset_eventually_many_from_ray c.S
  obtain ⟨D₀, hD₀⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (show 0 < (1 + θ) / 6 by positivity)) Y₀
  let T : ℝ := max 2 D₀
  let Csmall : ℝ := ((boundedDivisibleIdeals 1 (I.hi * T)).card : ℝ) * weightNorm J W
  let Cbig : ℝ := Real.sqrt
    (2 * (K * weightNorm J W ^ 2) * ((1 + θ) / (6 * η)) / c₀ +
      2 * (E * weightNorm J W) ^ 2)
  have hsmall : 0 ≤ Csmall := mul_nonneg (Nat.cast_nonneg _) (weightNorm_nonneg hW J)
  have hbig : 0 ≤ Cbig := Real.sqrt_nonneg _
  refine ⟨max Csmall Cbig, hbig.trans (le_max_right _ _), ?_⟩
  intro D hD
  have hD1 : 1 < D := lt_of_lt_of_le (by norm_num) hD
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hpow : 0 ≤ D ^ ((11 : ℝ) / 12 + ε) := Real.rpow_nonneg hD0.le _
  by_cases hlarge : D₀ ≤ D
  · let P := dyadicPrimeFinset c.S (D ^ ((1 + θ) / 6))
    obtain ⟨hcard, hP⟩ := hcount (D ^ ((1 + θ) / 6)) (hD₀ D hlarge)
    have hprime : ∀ p ∈ P, Prime p := fun p hp => (mem_dyadicPrimeFinset.mp hp).1
    have hgen : ∀ p ∈ P, ∃ z : O, principal z = p ∧ IsPrimary z := by
      intro p hp
      exact hprimary c p (hprime p hp) (dyadicPrimeFinset_outside c hp)
    have hsize : ∀ p ∈ P, 0 < normIdeal p ∧ normIdeal p ≤ D ^ ((1 + θ) / 6) := by
      intro p hp
      exact ⟨normIdeal_pos (hprime p hp).ne_zero, (mem_dyadicPrimeFinset.mp hp).2.2.1⟩
    have herr : ∀ p ∈ P,
        ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
          (E * weightNorm J W) * D / D ^ ((1 + θ) / 6) := by
      intro p hp
      apply herror c W hW J D (D ^ ((1 + θ) / 6)) hD0
        (Real.rpow_pos_of_pos hD0 _) p (hprime p hp).ne_zero
        (mem_dyadicPrimeFinset.mp hp).2.1.le
      · exact fun n hn => sexticSymbol_one_of_outside c hn
      · intro n hn
        exact sexticSymbol_sixth_of_outside c (hprime p hp)
          (primaryGenerator_spec (hgen p hp)).1 hn
    have hms : originalMeanSquare c W D (D ^ (1 + θ)) ≤
        (K * weightNorm J W ^ 2) * D ^ (2 + θ + η) :=
      hmean W D hW hD
    have hpoint : ‖originalSum c W D 1‖ ≤ Cbig * D ^ ((11 : ℝ) / 12 + ε) :=
      original_prime_rows_requested_loss P hP hprime hgen c W hD1 hc
        (mul_nonneg hE.le (weightNorm_nonneg hW J)) (mul_nonneg hK (sq_nonneg _))
        hθ.le hη hloss hsize herr hms hcard
    exact hpoint.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · have hDT : D ≤ T := (not_le.mp hlarge).le.trans (le_max_right _ _)
    have hbound : ‖originalSum c W D 1‖ ≤ Csmall :=
      originalSum_norm_le_card_weightNorm c I hW J hD0 hDT
    have hone : 1 ≤ D ^ ((11 : ℝ) / 12 + ε) :=
      Real.one_le_rpow hD1.le (by positivity)
    exact (hbound.trans (le_mul_of_one_le_right hsmall hone)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)

/-- The manuscript's actual pointwise estimate follows from its mean square. -/
theorem pointwise_of_meanSquare (hm : MeanSquareEstimate) : PointwiseMobiusEstimate :=
  pointwise_of_meanSquare_of_primary hm
    (fun c p hp hout => exists_primary_generator_of_outside c hp hout)

end QRHShort
