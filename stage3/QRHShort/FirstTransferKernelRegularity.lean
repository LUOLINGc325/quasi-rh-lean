import QRHShort.FirstTransferKernelZeroOrder
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Regularity of the literal first-transfer kernel.  The frequency variable is
first parametrized by its square root.  This is the restriction of a Schwartz
Fourier transform to a real line, so no differentiability of the square-root
map at zero is asserted or needed.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

namespace QRHShort

/-- The radial Fourier integral with its square-root frequency as parameter. -/
def firstTransferFourierProfile (Φ : RowWeight) (t : ℝ) : ℂ :=
  (2 / Real.sqrt 3 : ℂ) * ∫ z : ℂ,
    (Φ.value (Complex.normSq z) : ℂ) * additiveCharacter (-z * (t : ℂ))

theorem first_transfer_fourierProfile_eq (Φ : RowWeight) (f : SchwartzMap ℂ ℂ)
    (hf : ∀ z : ℂ, f z = (Φ.value (Complex.normSq z) : ℂ)) (t : ℝ) :
    firstTransferFourierProfile Φ t =
      (2 / Real.sqrt 3 : ℂ) * (𝓕 f) ((2 * t / Real.sqrt 3 : ℝ) * Complex.I) := by
  rw [firstTransferFourierProfile, SchwartzMap.fourier_coe, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [hf z, smul_eq_mul, mul_comm (Complex.exp _)]
    congr 1
    unfold additiveCharacter
    congr 2
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    change ((4 * Real.pi * (-z * (t : ℂ)).im / Real.sqrt 3 : ℝ) : ℂ) =
      ((-2 * Real.pi * (((2 * t / Real.sqrt 3 : ℝ) * Complex.I) *
        (starRingEnd ℂ) z).re : ℝ) : ℂ)
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_im,
      zero_mul, mul_zero, mul_one, zero_sub, sub_zero, zero_add, add_zero]
    push_cast
    ring)

theorem first_transfer_fourierProfile_contDiff (Φ : RowWeight) :
    ContDiff ℝ ∞ (firstTransferFourierProfile Φ) := by
  obtain ⟨f, hf⟩ := Φ.schwartz
  have heq : firstTransferFourierProfile Φ = fun t : ℝ =>
      (2 / Real.sqrt 3 : ℂ) * (𝓕 f) ((2 * t / Real.sqrt 3 : ℝ) * Complex.I) :=
    funext (first_transfer_fourierProfile_eq Φ f hf)
  rw [heq]
  apply contDiff_const.mul
  have hreal : ContDiff ℝ ∞ (fun t : ℝ => 2 * t / Real.sqrt 3) := by fun_prop
  have hfreq : ContDiff ℝ ∞
      (fun t : ℝ => (2 * t / Real.sqrt 3 : ℝ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const
  exact ((𝓕 f).smooth ⊤).comp hfreq

theorem first_transfer_radialFourier_eq_profile (Φ : RowWeight) (x : ℝ) :
    radialFourier (fun t => (Φ.value t : ℂ)) x =
      firstTransferFourierProfile Φ (Real.sqrt x) := rfl

/-- The axes lie outside the closed support.  On its remaining neighborhood,
`sqrt(a / (z₀ z₁)) = sqrt(a) / sqrt(z₀ z₁)`, including when `a = 0`. -/
theorem first_transfer_kernel_contDiff (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (a : ℝ) (hW : SmoothSupported I W) (ha : 0 ≤ a) :
    ContDiff ℝ ∞ (firstTransferKernel Φ W a) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (firstTransferKernel Φ W a)
  · have hbox := first_transfer_kernel_tsupport_subset I Φ W a hW hz
    have hprod : 0 < z 0 * z 1 :=
      mul_pos (I.lo_pos.trans_le (hbox.1 0)) (I.lo_pos.trans_le (hbox.1 1))
    have hroot : Real.sqrt (z 0 * z 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hprod)
    have hbase : ContDiffAt ℝ ∞ (fun y : BoxSpace 2 => Real.sqrt (y 0 * y 1)) z :=
      ((contDiff_apply ℝ ℝ 0).contDiffAt.mul (contDiff_apply ℝ ℝ 1).contDiffAt).sqrt
        (ne_of_gt hprod)
    have hcbase : ContDiffAt ℝ ∞
        (fun y : BoxSpace 2 => (Real.sqrt (y 0 * y 1) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z hbase
    have hW0 : ContDiffAt ℝ ∞ (fun y : BoxSpace 2 => W (y 0)) z :=
      hW.1.contDiffAt.comp z (contDiff_apply ℝ ℝ 0).contDiffAt
    have hW1 : ContDiffAt ℝ ∞ (fun y : BoxSpace 2 => star (W (y 1))) z :=
      Complex.conjCLE.contDiff.contDiffAt.comp z
        (hW.1.contDiffAt.comp z (contDiff_apply ℝ ℝ 1).contDiffAt)
    have harg : ContDiffAt ℝ ∞
        (fun y : BoxSpace 2 => Real.sqrt a / Real.sqrt (y 0 * y 1)) z :=
      contDiffAt_const.div hbase hroot
    have hprofile := (first_transfer_fourierProfile_contDiff Φ).contDiffAt.comp z harg
    have hmul := (((hcbase.inv (by exact_mod_cast hroot)).mul hW0).mul hW1).mul hprofile
    change ContDiffAt ℝ ∞ (fun y => firstTransferKernel Φ W a y) z
    simpa only [firstTransferKernel, first_transfer_radialFourier_eq_profile,
      Real.sqrt_div ha, Function.comp_def, Pi.inv_apply] using hmul
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem first_transfer_kernel_smoothBox (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (a : ℝ) (hW : SmoothSupported I W) (ha : 0 ≤ a) :
    SmoothBox (fun _ : Fin 2 => I) (firstTransferKernel Φ W a) :=
  ⟨first_transfer_kernel_contDiff I Φ W a hW ha,
    firstTransferKernel_support I Φ W hW a⟩

end QRHShort
