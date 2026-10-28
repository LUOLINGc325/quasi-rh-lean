import QRHShort.SecondTransferReduction

/-! The unbounded nonnegative Fourier parameter reduces to a fixed compact
interval: a nonzero literal kernel forces its parameter below the Fourier
support cap times the square of the fixed box's upper endpoint. -/

noncomputable section

namespace QRHShort

theorem second_transfer_kernel_parameter_le_of_ne_zero (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (rho : ℝ)
    (hU : SmoothSupported (halfEnlarged I) U) (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4)
    {a : ℝ} (ha : 0 ≤ a) {z : BoxSpace 2}
    (hz : secondTransferKernel Φ U rho a z ≠ 0) :
    a ≤ Φ.fourierCap * (secondTransferInterval I).hi ^ 2 := by
  have hbox := second_transfer_kernel_support I Φ U rho a hU hrho hrho4 hz
  have hz0 : 0 < z 0 := (secondTransferInterval I).lo_pos.trans_le (hbox 0).1
  have hz1 : 0 < z 1 := (secondTransferInterval I).lo_pos.trans_le (hbox 1).1
  have hhi : 0 < (secondTransferInterval I).hi :=
    (secondTransferInterval I).lo_pos.trans_le (secondTransferInterval I).ordered
  have hprod : 0 < z 0 * z 1 := mul_pos hz0 hz1
  have hfourier : radialFourier (fun x => (Φ.value x : ℂ)) (a / (z 0 * z 1)) ≠ 0 := by
    intro hzero
    exact hz (by simp only [secondTransferKernel, hzero, mul_zero])
  have hcap := (Φ.fourier_support ⟨hfourier, div_nonneg ha hprod.le⟩).2
  have hprod_le : z 0 * z 1 ≤ (secondTransferInterval I).hi ^ 2 := by
    calc
      z 0 * z 1 ≤ (secondTransferInterval I).hi * (secondTransferInterval I).hi :=
        mul_le_mul (hbox 0).2 (hbox 1).2 hz1.le hhi.le
      _ = (secondTransferInterval I).hi ^ 2 := (pow_two _).symm
  exact ((div_le_iff₀ hprod).mp hcap).trans
    (mul_le_mul_of_nonneg_left hprod_le Φ.cap_pos.le)

theorem second_transfer_kernel_eq_zero_of_parameter_gt (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (rho : ℝ)
    (hU : SmoothSupported (halfEnlarged I) U) (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4)
    {a : ℝ} (ha : 0 ≤ a) (hbound : Φ.fourierCap * (secondTransferInterval I).hi ^ 2 < a) :
    secondTransferKernel Φ U rho a = 0 := by
  funext z
  by_contra hz
  exact (not_le_of_gt hbound)
    (second_transfer_kernel_parameter_le_of_ne_zero I Φ U rho hU hrho hrho4 ha hz)

end QRHShort
