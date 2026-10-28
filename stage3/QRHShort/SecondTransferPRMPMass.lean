import QRHShort.SecondTransferPRMPRows

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def secondTransferPRMPMass (I : SupportInterval) (L : ℝ) : ℝ :=
  ∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
    ∑ d ∈ secondTransferPRMPBox I L,
      if d ∣ C then (normIdeal C ^ 2 * normIdeal t)⁻¹ else 0

theorem second_transfer_prmp_divisor_sum_const (I : SupportInterval) {L : ℝ}
    {C : Ideal O} (hC : C ∈ secondTransferPRMPBox I L) (a : ℝ) :
    (∑ d ∈ secondTransferPRMPBox I L, if d ∣ C then a else 0) =
      (divisorCount C : ℝ) * a := by
  have hC₀ := (mem_boundedDivisibleIdeals.mp hC).2.2
  have hfilter : (secondTransferPRMPBox I L).filter (fun d => d ∣ C) =
      SecondTransferPRMPHarmonic.idealDivisors C hC₀ := by
    ext d
    simp only [Finset.mem_filter, SecondTransferPRMPHarmonic.mem_idealDivisors]
    exact ⟨And.right, fun hd => ⟨second_transfer_prmp_divisor_mem I hC hd, hd⟩⟩
  have hcard : divisorCount C = (SecondTransferPRMPHarmonic.idealDivisors C hC₀).card :=
    Nat.subtype_card _ (SecondTransferPRMPHarmonic.mem_idealDivisors C hC₀)
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, ← hcard]

theorem second_transfer_prmp_mass_le_product (I : SupportInterval) (L : ℝ) :
    secondTransferPRMPMass I L ≤
      (∑ C ∈ secondTransferPRMPBox I L, (divisorCount C : ℝ) / normIdeal C) *
        (∑ t ∈ secondTransferPRMPBox I L, (normIdeal t)⁻¹) := by
  unfold secondTransferPRMPMass
  calc
    _ ≤ ∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
        ((divisorCount C : ℝ) / normIdeal C) * (normIdeal t)⁻¹ := by
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro t ht
      rw [second_transfer_prmp_divisor_sum_const I hC]
      have hC₀ := (mem_boundedDivisibleIdeals.mp hC).2.2
      have ht₀ := (mem_boundedDivisibleIdeals.mp ht).2.2
      have hC₁ := second_transfer_prmp_one_le_norm hC₀
      have hsq : normIdeal C ≤ normIdeal C ^ 2 := by nlinarith
      calc
        _ ≤ (divisorCount C : ℝ) * (normIdeal C * normIdeal t)⁻¹ :=
          mul_le_mul_of_nonneg_left
            (inv_anti₀ (mul_pos (normIdeal_pos hC₀) (normIdeal_pos ht₀))
              (mul_le_mul_of_nonneg_right hsq (normIdeal_pos ht₀).le)) (Nat.cast_nonneg _)
        _ = _ := by rw [mul_inv]; ring
    _ = _ := (Finset.sum_mul_sum _ _ _ _).symm

theorem second_transfer_prmp_mass_log_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (I : SupportInterval) (L : ℝ),
      secondTransferPRMPMass I L ≤ K * Real.log (2 * secondTransferPRMPRadius I L) ^ 3 := by
  obtain ⟨Kh, hKh, hh⟩ := SecondTransferPRMPHarmonic.exists_ideal_harmonic_constant
  obtain ⟨Kd, hKd, hd⟩ := SecondTransferPRMPHarmonic.exists_ideal_divisor_harmonic_constant
  refine ⟨Kd * Kh, mul_nonneg hKd.le hKh.le, ?_⟩
  intro I L
  have hR : 1 ≤ secondTransferPRMPRadius I L := le_max_left _ _
  have hlog : 0 ≤ Real.log (2 * secondTransferPRMPRadius I L) :=
    Real.log_nonneg (by linarith)
  calc
    _ ≤ (∑ C ∈ secondTransferPRMPBox I L, (divisorCount C : ℝ) / normIdeal C) *
        (∑ t ∈ secondTransferPRMPBox I L, (normIdeal t)⁻¹) :=
      second_transfer_prmp_mass_le_product I L
    _ ≤ (Kd * Real.log (2 * secondTransferPRMPRadius I L) ^ 2) *
        (Kh * Real.log (2 * secondTransferPRMPRadius I L)) :=
      mul_le_mul (hd _ hR) (hh _ hR)
        (Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
        (mul_nonneg hKd.le (sq_nonneg _))
    _ = _ := by ring

end QRHShort
