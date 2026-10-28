import QRHShort.FirstTransferKernelRegularityAmplitude
import QRHShort.FirstTransferKernelProductBounds

/-! Child K: regularity of the literal radial Fourier kernel and a uniform
derivative bound on the compact frequency-parameter interval. -/

namespace QRHShort

theorem first_transfer_kernel_bound :
    FirstTransferKernelStatement := by
  intro I Φ q
  obtain ⟨C, hC, hbound⟩ := first_transfer_amplitude_uniform_bound I Φ q
    (Real.sqrt (Φ.fourierCap * I.hi ^ 2))
  refine ⟨((2 : ℝ) ^ q) ^ 2 * C, mul_nonneg (sq_nonneg _) hC, ?_⟩
  intro W a hW ha hcap
  refine ⟨first_transfer_kernel_smoothBox I Φ W a hW ha, ?_⟩
  rw [first_transfer_kernel_eq_amplitude I Φ W a hW ha]
  apply first_transfer_kernel_multiplier_bound I q
    (firstTransferAmplitude I Φ (Real.sqrt a)) C hC
    (first_transfer_amplitude_contDiff I Φ (Real.sqrt a)) _ W hW
  intro j hj z hz
  exact hbound (Real.sqrt a) ⟨Real.sqrt_nonneg a, Real.sqrt_le_sqrt hcap⟩ z hz j hj

end QRHShort
