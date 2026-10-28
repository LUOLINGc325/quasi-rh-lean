import QRHShort.SecondTransferPRMPMass

noncomputable section
open Classical

namespace QRHShort

theorem second_transfer_prmp_log_cube_absorb (C ε : ℝ) (I : SupportInterval)
    (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D L : ℝ, 2 ≤ D → 1 ≤ L → L ≤ D ^ C →
      Real.log (2 * secondTransferPRMPRadius I L) ^ 3 ≤ K * D ^ ε := by
  let A : ℝ := max 1 (2 * I.hi)
  let η : ℝ := ε / 3
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hη : 0 < η := div_pos hε (by norm_num)
  have hlogA : 0 ≤ Real.log (2 * A) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ Real.log (2 * A) + C / η :=
    add_nonneg hlogA (div_nonneg (zero_le_one.trans hC) hη.le)
  refine ⟨(Real.log (2 * A) + C / η) ^ 3, pow_nonneg hcoef _, ?_⟩
  intro D L hD hL hLD
  have hD₁ : 1 ≤ D := le_trans (by norm_num) hD
  have hD₀ : 0 < D := zero_lt_one.trans_le hD₁
  have hpow : 1 ≤ D ^ C := Real.one_le_rpow hD₁ (zero_le_one.trans hC)
  have hpη : 1 ≤ D ^ η := Real.one_le_rpow hD₁ hη.le
  have hR : secondTransferPRMPRadius I L ≤ A * D ^ C := by
    apply max_le
    · exact hpow.trans (le_mul_of_one_le_left (Real.rpow_nonneg hD₀.le _) hA)
    · exact mul_le_mul (le_max_right _ _) hLD (zero_le_one.trans hL) hA₀.le
  have hsplit : Real.log (2 * secondTransferPRMPRadius I L) ≤
      Real.log (2 * A) + C * Real.log D := by
    have hR₀ : 0 < secondTransferPRMPRadius I L := zero_lt_one.trans_le (le_max_left _ _)
    calc
      _ ≤ Real.log ((2 * A) * D ^ C) := Real.log_le_log (by positivity)
        (by nlinarith only [hR])
      _ = _ := by rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hD₀ _).ne',
        Real.log_rpow hD₀]
  have hlog : 0 ≤ Real.log (2 * secondTransferPRMPRadius I L) :=
    Real.log_nonneg (by have := (le_max_left 1 (2 * I.hi * L)); dsimp [secondTransferPRMPRadius]; linarith)
  have hbase : Real.log (2 * secondTransferPRMPRadius I L) ≤
      (Real.log (2 * A) + C / η) * D ^ η := by
    calc
      _ ≤ Real.log (2 * A) + C * Real.log D := hsplit
      _ ≤ Real.log (2 * A) * D ^ η + C * (D ^ η / η) :=
        add_le_add (le_mul_of_one_le_right hlogA hpη)
          (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hD₀.le hη) (zero_le_one.trans hC))
      _ = _ := by ring
  calc
    _ ≤ ((Real.log (2 * A) + C / η) * D ^ η) ^ 3 := pow_le_pow_left₀ hlog hbase _
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hD₀.le]
      congr 1
      congr 1
      dsimp only [η]
      ring

theorem second_transfer_prmp_mass_absorb (C ε : ℝ) (I : SupportInterval)
    (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D L : ℝ, 2 ≤ D → 1 ≤ L → L ≤ D ^ C →
      secondTransferPRMPMass I L ≤ K * D ^ ε := by
  obtain ⟨Km, hKm, hm⟩ := second_transfer_prmp_mass_log_bound
  obtain ⟨Kl, hKl, hl⟩ := second_transfer_prmp_log_cube_absorb C ε I hC hε
  refine ⟨Km * Kl, mul_nonneg hKm hKl, ?_⟩
  intro D L hD hL hLD
  exact (hm I L).trans ((mul_le_mul_of_nonneg_left (hl D L hD hL hLD) hKm).trans_eq
    (mul_assoc _ _ _).symm)

end QRHShort
