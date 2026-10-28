import QRHShort.SecondTransferKernelDilation
import QRHShort.SecondTransferKernelProductBounds
import QRHShort.SecondTransferKernelSupport

/-! Uniform smoothness and derivative bounds for the literal second-transfer
kernel. The Fourier support reduces the unbounded parameter to a fixed compact
interval; the dilation is absorbed into a supported one-variable weight. -/

namespace QRHShort

theorem second_transfer_kernel_bound : SecondTransferKernelStatement := by
  classical
  intro I Φ q
  let J := secondTransferInterval I
  obtain ⟨B, hB, hbound⟩ := second_transfer_amplitude_uniform_bound J Φ q
    (Real.sqrt (Φ.fourierCap * J.hi ^ 2))
  let K : ℝ := ((2 : ℝ) ^ q) ^ 2 * B * ((4 : ℝ) ^ q) ^ 2
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  refine ⟨K, hK, ?_⟩
  intro U rho a hU hrho hrho4 ha
  refine ⟨second_transfer_kernel_smoothBox I Φ U rho a hU hrho hrho4 ha, ?_⟩
  by_cases hcap : a ≤ Φ.fourierCap * J.hi ^ 2
  · rw [second_transfer_kernel_eq_amplitude_dilated I Φ U rho a hU hrho hrho4 ha]
    have hV := second_transfer_dilatedWeight_smoothSupported I U rho hU hrho hrho4
    have hA := second_transfer_amplitude_contDiff J Φ (Real.sqrt a)
    have hAbound : ∀ j ≤ q,
        ∀ z ∈ Set.Icc (fun _ : Fin 2 => J.lo) (fun _ : Fin 2 => J.hi),
          ‖iteratedFDeriv ℝ j (secondTransferAmplitude J Φ (Real.sqrt a)) z‖ ≤ B := by
      intro j hj z hz
      exact hbound (Real.sqrt a) ⟨Real.sqrt_nonneg a, Real.sqrt_le_sqrt hcap⟩ z hz j hj
    have hmul := second_transfer_kernel_multiplier_bound J q
      (secondTransferAmplitude J Φ (Real.sqrt a)) B hB hA hAbound
      (secondTransferDilatedWeight U rho) hV
    have hN := weightNorm_nonneg hU q
    have hVnorm := second_transfer_dilatedWeight_weightNorm_le I U rho hU hrho hrho4 q
    have hsquare : weightNorm q (secondTransferDilatedWeight U rho) ^ 2 ≤
        ((4 : ℝ) ^ q * weightNorm q U) ^ 2 :=
      (sq_le_sq₀ (weightNorm_nonneg hV q) (mul_nonneg (by positivity) hN)).mpr hVnorm
    calc
      _ ≤ ((2 : ℝ) ^ q) ^ 2 * B * weightNorm q (secondTransferDilatedWeight U rho) ^ 2 := hmul
      _ ≤ ((2 : ℝ) ^ q) ^ 2 * B * ((4 : ℝ) ^ q * weightNorm q U) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (mul_nonneg (sq_nonneg _) hB)
      _ = K * weightNorm q U ^ 2 := by dsimp only [K]; ring
  · rw [second_transfer_kernel_eq_zero_of_parameter_gt I Φ U rho hU hrho hrho4 ha
      (lt_of_not_ge hcap)]
    have hzero : multiWeightNorm q (0 : BoxSpace 2 → ℂ) ≤ 0 := by
      apply QRHLean3.supZero_le le_rfl
      rintro r ⟨j, hj, x, rfl⟩
      simp
    exact hzero.trans (mul_nonneg hK (sq_nonneg _))

end QRHShort
