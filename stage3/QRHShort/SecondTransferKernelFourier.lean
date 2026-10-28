import QRHShort.SecondTransferReduction
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Regularity of the literal second-transfer kernel.  The frequency variable is
first parametrized by its square root.  This is the restriction of a Schwartz
Fourier transform to a real line, so no differentiability of the square-root
map at zero is asserted or needed.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

namespace QRHShort

/-- The radial Fourier integral with its square-root frequency as parameter. -/
def secondTransferFourierProfile (Φ : RowWeight) (t : ℝ) : ℂ :=
  (2 / Real.sqrt 3 : ℂ) * ∫ z : ℂ,
    (Φ.value (Complex.normSq z) : ℂ) * additiveCharacter (-z * (t : ℂ))

theorem second_transfer_fourierProfile_eq (Φ : RowWeight) (f : SchwartzMap ℂ ℂ)
    (hf : ∀ z : ℂ, f z = (Φ.value (Complex.normSq z) : ℂ)) (t : ℝ) :
    secondTransferFourierProfile Φ t =
      (2 / Real.sqrt 3 : ℂ) * (𝓕 f) ((2 * t / Real.sqrt 3 : ℝ) * Complex.I) := by
  rw [secondTransferFourierProfile, SchwartzMap.fourier_coe, Real.fourier_eq']
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

theorem second_transfer_fourierProfile_contDiff (Φ : RowWeight) :
    ContDiff ℝ ∞ (secondTransferFourierProfile Φ) := by
  obtain ⟨f, hf⟩ := Φ.schwartz
  have heq : secondTransferFourierProfile Φ = fun t : ℝ =>
      (2 / Real.sqrt 3 : ℂ) * (𝓕 f) ((2 * t / Real.sqrt 3 : ℝ) * Complex.I) :=
    funext (second_transfer_fourierProfile_eq Φ f hf)
  rw [heq]
  apply contDiff_const.mul
  have hreal : ContDiff ℝ ∞ (fun t : ℝ => 2 * t / Real.sqrt 3) := by fun_prop
  have hfreq : ContDiff ℝ ∞
      (fun t : ℝ => (2 * t / Real.sqrt 3 : ℝ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const
  exact ((𝓕 f).smooth ⊤).comp hfreq

theorem second_transfer_radialFourier_eq_profile (Φ : RowWeight) (x : ℝ) :
    radialFourier (fun t => (Φ.value t : ℂ)) x =
      secondTransferFourierProfile Φ (Real.sqrt x) := rfl

end QRHShort
