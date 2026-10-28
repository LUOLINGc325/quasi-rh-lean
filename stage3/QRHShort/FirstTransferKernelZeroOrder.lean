import QRHShort.FirstTransferReduction

/-!
The zero-order part of child K. The constant is the L¹ mass of the literal
radial weight, times the Fourier normalization and the inverse left endpoint.
It is chosen before W and the frequency parameter. Integrability is proved
from the RowWeight Schwartz witness, not inferred from a totalized integral.
This module does not assert the remaining smoothness or higher-derivative bounds.
-/

noncomputable section
open MeasureTheory

namespace QRHShort

theorem first_transfer_additiveCharacter_norm (z : ℂ) :
    ‖additiveCharacter z‖ = 1 := by
  simp [additiveCharacter, Complex.norm_exp]

theorem first_transfer_radial_integrable (Φ : RowWeight) :
    Integrable (fun z : ℂ => (Φ.value (Complex.normSq z) : ℂ)) := by
  obtain ⟨f, hf⟩ := Φ.schwartz
  have heq : (fun z : ℂ => (Φ.value (Complex.normSq z) : ℂ)) = f :=
    funext (fun z => (hf z).symm)
  rw [heq]
  exact f.integrable

theorem first_transfer_radialFourier_integrable (Φ : RowWeight) (x : ℝ) :
    Integrable (fun z : ℂ => (Φ.value (Complex.normSq z) : ℂ) *
      additiveCharacter (-z * (Real.sqrt x : ℂ))) := by
  obtain ⟨f, hf⟩ := Φ.schwartz
  have hcont : Continuous (fun z : ℂ => (Φ.value (Complex.normSq z) : ℂ)) := by
    have heq : (fun z : ℂ => (Φ.value (Complex.normSq z) : ℂ)) = f :=
      funext (fun z => (hf z).symm)
    rw [heq]
    exact f.continuous
  have hchar : Continuous (fun z : ℂ => additiveCharacter (-z * (Real.sqrt x : ℂ))) := by
    unfold additiveCharacter
    fun_prop
  apply (first_transfer_radial_integrable Φ).norm.mono'
    (hcont.mul hchar).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    change ‖(Φ.value (Complex.normSq z) : ℂ) *
      additiveCharacter (-z * (Real.sqrt x : ℂ))‖ ≤ ‖(Φ.value (Complex.normSq z) : ℂ)‖
    rw [norm_mul, first_transfer_additiveCharacter_norm, mul_one])

/-- Dominated convergence applies to the actual Fourier integral, including
at frequency zero. This is continuity, not a higher-derivative assertion. -/
theorem first_transfer_radialFourier_continuous (Φ : RowWeight) :
    Continuous (radialFourier (fun t => (Φ.value t : ℂ))) := by
  unfold radialFourier
  apply continuous_const.mul
  apply continuous_of_dominated
    (fun x => (first_transfer_radialFourier_integrable Φ x).aestronglyMeasurable)
    (bound := fun z : ℂ => ‖(Φ.value (Complex.normSq z) : ℂ)‖)
  · intro x
    exact Filter.Eventually.of_forall (fun z => by
      change ‖(Φ.value (Complex.normSq z) : ℂ) *
        additiveCharacter (-z * (Real.sqrt x : ℂ))‖ ≤ ‖(Φ.value (Complex.normSq z) : ℂ)‖
      rw [norm_mul, first_transfer_additiveCharacter_norm, mul_one])
  · exact (first_transfer_radial_integrable Φ).norm
  · exact Filter.Eventually.of_forall (fun z => by
      unfold additiveCharacter
      fun_prop)

/-- A constant depending only on the row weight, with the manuscript's
Fourier normalization. -/
def firstTransferFourierMass (Φ : RowWeight) : ℝ :=
  ‖(2 / Real.sqrt 3 : ℂ)‖ * ∫ z : ℂ, ‖(Φ.value (Complex.normSq z) : ℂ)‖

theorem firstTransferFourierMass_nonneg (Φ : RowWeight) :
    0 ≤ firstTransferFourierMass Φ := by
  exact mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _))

theorem first_transfer_radialFourier_norm_le (Φ : RowWeight) (x : ℝ) :
    ‖radialFourier (fun t => (Φ.value t : ℂ)) x‖ ≤ firstTransferFourierMass Φ := by
  unfold radialFourier firstTransferFourierMass
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∫ z : ℂ, (Φ.value (Complex.normSq z) : ℂ) *
        additiveCharacter (-z * (Real.sqrt x : ℂ))‖ ≤
        ∫ z : ℂ, ‖(Φ.value (Complex.normSq z) : ℂ) *
          additiveCharacter (-z * (Real.sqrt x : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        dsimp only
        rw [norm_mul, first_transfer_additiveCharacter_norm, mul_one])

/-- The closed support stays inside a compact box bounded away from both axes. -/
theorem first_transfer_kernel_tsupport_subset (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (a : ℝ) (hW : SmoothSupported I W) :
    tsupport (firstTransferKernel Φ W a) ⊆
      Set.Icc (fun _ : Fin 2 => I.lo) (fun _ : Fin 2 => I.hi) := by
  apply closure_minimal _ isClosed_Icc
  intro z hz
  have hbox := firstTransferKernel_support I Φ W hW a hz
  exact ⟨fun i => (hbox i).1, fun i => (hbox i).2⟩

theorem first_transfer_kernel_hasCompactSupport (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (a : ℝ) (hW : SmoothSupported I W) :
    HasCompactSupport (firstTransferKernel Φ W a) := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (first_transfer_kernel_tsupport_subset I Φ W a hW)

/-- Continuity at the axes follows from the support bound; division is used
only in the positive-coordinate neighborhood of the closed support. -/
theorem first_transfer_kernel_continuous (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (a : ℝ) (hW : SmoothSupported I W) :
    Continuous (firstTransferKernel Φ W a) := by
  apply continuous_of_tsupport
  intro z hz
  have hbox := first_transfer_kernel_tsupport_subset I Φ W a hW hz
  have hprod : 0 < z 0 * z 1 :=
    mul_pos (I.lo_pos.trans_le (hbox.1 0)) (I.lo_pos.trans_le (hbox.1 1))
  have hroot : (Real.sqrt (z 0 * z 1) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hprod))
  have hbase : ContinuousAt (fun y : BoxSpace 2 => (Real.sqrt (y 0 * y 1) : ℂ)) z := by
    fun_prop
  have hW0 : ContinuousAt (fun y : BoxSpace 2 => W (y 0)) z :=
    hW.1.continuous.continuousAt.comp (continuous_apply 0).continuousAt
  have hW1 : ContinuousAt (fun y : BoxSpace 2 => W (y 1)) z :=
    hW.1.continuous.continuousAt.comp (continuous_apply 1).continuousAt
  have harg : ContinuousAt (fun y : BoxSpace 2 => a / (y 0 * y 1)) z :=
    continuousAt_const.div
      ((continuous_apply 0).continuousAt.mul (continuous_apply 1).continuousAt)
      (ne_of_gt hprod)
  exact (((hbase.inv₀ hroot).mul hW0).mul hW1.star).mul
    ((first_transfer_radialFourier_continuous Φ).continuousAt.comp harg)

/-- A global bound, including outside the support and on the coordinate axes.
No restriction on the frequency parameter is needed at order zero. -/
theorem first_transfer_kernel_norm_le (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (a : ℝ) (hW : SmoothSupported I W) (z : BoxSpace 2) :
    ‖firstTransferKernel Φ W a z‖ ≤
      (I.lo⁻¹ * firstTransferFourierMass Φ) * weightNorm 0 W ^ 2 := by
  have hmass := firstTransferFourierMass_nonneg Φ
  by_cases hz : firstTransferKernel Φ W a z = 0
  · rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr I.lo_pos.le) hmass) (sq_nonneg _)
  have hsupport := firstTransferKernel_support I Φ W hW a hz
  have hz0 := hsupport 0
  have hz1 := hsupport 1
  have hprod : I.lo ^ 2 ≤ z 0 * z 1 := by
    calc
      I.lo ^ 2 = I.lo * I.lo := pow_two _
      _ ≤ z 0 * z 1 := mul_le_mul hz0.1 hz1.1 I.lo_pos.le
        (I.lo_pos.le.trans hz0.1)
  have hroot : I.lo ≤ Real.sqrt (z 0 * z 1) := by
    calc
      I.lo = Real.sqrt (I.lo ^ 2) := (Real.sqrt_sq I.lo_pos.le).symm
      _ ≤ Real.sqrt (z 0 * z 1) := Real.sqrt_le_sqrt hprod
  have hinv : (Real.sqrt (z 0 * z 1))⁻¹ ≤ I.lo⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le I.lo_pos hroot
  have hzero : ‖W (z 0)‖ ≤ weightNorm 0 W := by
    simpa only [iteratedDeriv_zero] using
      norm_iteratedDeriv_le_weightNorm hW (le_refl 0) (z 0)
  have hone : ‖W (z 1)‖ ≤ weightNorm 0 W := by
    simpa only [iteratedDeriv_zero] using
      norm_iteratedDeriv_le_weightNorm hW (le_refl 0) (z 1)
  calc
    ‖firstTransferKernel Φ W a z‖ =
        (Real.sqrt (z 0 * z 1))⁻¹ * ‖W (z 0)‖ * ‖W (z 1)‖ *
          ‖radialFourier (fun t => (Φ.value t : ℂ)) (a / (z 0 * z 1))‖ := by
      simp [firstTransferKernel, Complex.norm_real,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ I.lo⁻¹ * weightNorm 0 W * weightNorm 0 W * firstTransferFourierMass Φ := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hinv hzero (norm_nonneg _)
          (inv_nonneg.mpr I.lo_pos.le)) hone (norm_nonneg _)
          (mul_nonneg (inv_nonneg.mpr I.lo_pos.le) (weightNorm_nonneg hW 0)))
        (first_transfer_radialFourier_norm_le Φ _) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (inv_nonneg.mpr I.lo_pos.le)
          (weightNorm_nonneg hW 0)) (weightNorm_nonneg hW 0))
    _ = _ := by ring

/-- The norm inequality in child K at order zero, uniformly for every real
parameter, with no additional premise beyond the frozen RowWeight interface. -/
theorem first_transfer_kernel_zero_order_bound (I : SupportInterval) (Φ : RowWeight) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (a : ℝ), SmoothSupported I W →
      multiWeightNorm 0 (firstTransferKernel Φ W a) ≤ K * weightNorm 0 W ^ 2 := by
  refine ⟨I.lo⁻¹ * firstTransferFourierMass Φ,
    mul_nonneg (inv_nonneg.mpr I.lo_pos.le) (firstTransferFourierMass_nonneg Φ), ?_⟩
  intro W a hW
  apply QRHLean3.supZero_le
    (mul_nonneg (mul_nonneg (inv_nonneg.mpr I.lo_pos.le)
      (firstTransferFourierMass_nonneg Φ)) (sq_nonneg _))
  rintro r ⟨j, hj, z, rfl⟩
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  simpa only [norm_iteratedFDeriv_zero] using first_transfer_kernel_norm_le I Φ W a hW z

end QRHShort
