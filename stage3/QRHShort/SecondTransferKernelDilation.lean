import QRHShort.SecondTransferKernelAmplitude
import QRHShort.WeightNorm

/-!
The dilation is absorbed into the one-variable test weight. Its derivatives
cost at most 4^q on the prescribed dilation interval, while the square-root
normalization has norm at most one. The smooth amplitude is independent of
the dilation and agrees with the literal kernel on the weight support.
-/

noncomputable section
open scoped ContDiff

namespace QRHShort

def secondTransferDilatedWeight (U : ℝ → ℂ) (rho : ℝ) (x : ℝ) : ℂ :=
  (Real.sqrt rho : ℂ)⁻¹ * U (rho * x)

theorem second_transfer_dilated_support (I : SupportInterval) (U : ℝ → ℂ)
    (rho : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4) :
    SmoothSupported (secondTransferInterval I) (fun x => U (rho * x)) := by
  refine ⟨hU.1.comp (contDiff_const.mul contDiff_id), ?_⟩
  intro x hx
  obtain ⟨hlo, hhi⟩ := hU.2 hx
  change I.lo / 2 ≤ rho * x at hlo
  change rho * x ≤ 2 * I.hi at hhi
  have hxpos : 0 < x := by
    have hmul : 0 < rho * x := lt_of_lt_of_le (div_pos I.lo_pos (by norm_num)) hlo
    exact (mul_pos_iff_of_pos_left (zero_lt_one.trans_le hrho)).mp hmul
  change I.lo / 8 ≤ x ∧ x ≤ 2 * I.hi
  constructor <;> nlinarith

theorem second_transfer_dilatedWeight_smoothSupported (I : SupportInterval) (U : ℝ → ℂ)
    (rho : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4) :
    SmoothSupported (secondTransferInterval I) (secondTransferDilatedWeight U rho) :=
  (second_transfer_dilated_support I U rho hU hrho hrho4).const_mul (Real.sqrt rho : ℂ)⁻¹

theorem second_transfer_dilated_weightNorm_le (I : SupportInterval) (U : ℝ → ℂ)
    (rho : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4) (q : ℕ) :
    weightNorm q (fun x => U (rho * x)) ≤ (4 : ℝ) ^ q * weightNorm q U := by
  have hN := weightNorm_nonneg hU q
  apply QRHLean3.supZero_le (mul_nonneg (by positivity) hN)
  rintro r ⟨j, hj, x, rfl⟩
  rw [iteratedDeriv_comp_const_smul (n := j) (hU.1.of_le (by simp)) rho]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (zero_le_one.trans hrho) j)]
  exact mul_le_mul
    ((pow_le_pow_left₀ (zero_le_one.trans hrho) hrho4 j).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj))
    (norm_iteratedDeriv_le_weightNorm hU hj _) (norm_nonneg _) (by positivity)

theorem second_transfer_dilatedWeight_weightNorm_le (I : SupportInterval) (U : ℝ → ℂ)
    (rho : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4) (q : ℕ) :
    weightNorm q (secondTransferDilatedWeight U rho) ≤ (4 : ℝ) ^ q * weightNorm q U := by
  have hd := second_transfer_dilated_support I U rho hU hrho hrho4
  have hsqrt : 1 ≤ Real.sqrt rho := Real.one_le_sqrt.mpr hrho
  have hnorm : ‖(Real.sqrt rho : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg rho)]
    exact inv_le_one_of_one_le₀ hsqrt
  unfold secondTransferDilatedWeight
  rw [weightNorm_const_mul hd]
  exact (mul_le_of_le_one_left (weightNorm_nonneg hd q) hnorm).trans
    (second_transfer_dilated_weightNorm_le I U rho hU hrho hrho4 q)

theorem second_transfer_kernel_eq_amplitude_dilated (I : SupportInterval) (Φ : RowWeight)
    (U : ℝ → ℂ) (rho a : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4) (ha : 0 ≤ a) :
    secondTransferKernel Φ U rho a = fun z =>
      secondTransferAmplitude (secondTransferInterval I) Φ (Real.sqrt a) z *
        secondTransferDilatedWeight U rho (z 0) * star (secondTransferDilatedWeight U rho (z 1)) := by
  funext z
  by_cases h0 : U (rho * z 0) = 0
  · simp [secondTransferKernel, secondTransferDilatedWeight, h0]
  by_cases h1 : U (rho * z 1) = 0
  · simp [secondTransferKernel, secondTransferDilatedWeight, h1]
  have hd := second_transfer_dilated_support I U rho hU hrho hrho4
  have hz0 := (hd.2 h0).1
  have hz1 := (hd.2 h1).1
  have hx0 : 0 ≤ z 0 := ((secondTransferInterval I).lo_pos.trans_le hz0).le
  have hrho0 : 0 ≤ rho := zero_le_one.trans hrho
  have hstarinv (r : ℝ) : star ((r : ℂ)⁻¹) = (r : ℂ)⁻¹ := by simp
  simp only [secondTransferKernel, secondTransferDilatedWeight, secondTransferAmplitude,
    second_transfer_positiveCoordinate_eq (secondTransferInterval I) hz0,
    second_transfer_positiveCoordinate_eq (secondTransferInterval I) hz1,
    second_transfer_radialFourier_eq_profile, Real.sqrt_div ha,
    Real.sqrt_mul hrho0, Real.sqrt_mul hx0, Complex.ofReal_mul, mul_inv_rev,
    star_mul, hstarinv]
  ring

theorem second_transfer_kernel_smoothBox (I : SupportInterval) (Φ : RowWeight)
    (U : ℝ → ℂ) (rho a : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4) (ha : 0 ≤ a) :
    SmoothBox (fun _ : Fin 2 => secondTransferInterval I) (secondTransferKernel Φ U rho a) := by
  refine ⟨?_, second_transfer_kernel_support I Φ U rho a hU hrho hrho4⟩
  rw [second_transfer_kernel_eq_amplitude_dilated I Φ U rho a hU hrho hrho4 ha]
  have hV := second_transfer_dilatedWeight_smoothSupported I U rho hU hrho hrho4
  exact ((second_transfer_amplitude_contDiff (secondTransferInterval I) Φ (Real.sqrt a)).mul
    (hV.1.comp (contDiff_apply ℝ ℝ 0))).mul
    (Complex.conjCLE.contDiff.comp (hV.1.comp (contDiff_apply ℝ ℝ (1 : Fin 2))))

end QRHShort
