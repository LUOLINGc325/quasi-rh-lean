import QRHShort.SmoothFourierDecay
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.WithLp

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap RealInnerProductSpace
open MeasureTheory Classical
namespace QRHShort

abbrev ESpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

def euclEquiv (d : ℕ) : ESpace d ≃L[ℝ] BoxSpace d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

def logKernelE {d : ℕ} (K : BoxSpace d → ℂ) : ESpace d → ℂ :=
  logKernel K ∘ (euclEquiv d)

def scaledLogSchwartzE {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) : SchwartzMap (ESpace d) ℂ := by
  let φ : ESpace d ≃ₜ BoxSpace d := (euclEquiv d).toHomeomorph
  have hc : HasCompactSupport (logKernelE K) := by
    exact hK.hasCompactSupport_logKernel.comp_homeomorph φ
  have hd : ContDiff ℝ ∞ (logKernelE K) := by
    exact hK.contDiff_logKernel.comp (euclEquiv d).contDiff
  exact (hc.comp_smul (by positivity : (2 * Real.pi : ℝ) ≠ 0)).toSchwartzMap
    (hd.comp (by fun_prop))

lemma scaledLogSchwartzE_apply {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) (u : ESpace d) :
    scaledLogSchwartzE hK u = logKernelE K ((2 * Real.pi) • u) := by
  rfl

lemma inner_toLp {d : ℕ} (y t : BoxSpace d) :
    ⟪(WithLp.toLp 2 y : ESpace d), (WithLp.toLp 2 t : ESpace d)⟫ =
      ∑ i : Fin d, y i * t i := by
  rw [PiLp.inner_apply]
  simp only [PiLp.toLp_apply, RCLike.inner_apply, conj_trivial, mul_comm]


lemma separationCoefficient_eq_euclFourier {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) (t : BoxSpace d) :
    separationCoefficient K t =
      (𝓕 (scaledLogSchwartzE hK)) (WithLp.toLp 2 t : ESpace d) := by
  let a : ℝ := 2 * Real.pi
  let HE : ESpace d → ℂ := fun u =>
    Complex.exp (((-⟪u, (WithLp.toLp 2 t : ESpace d)⟫ : ℝ) : ℂ) * Complex.I) *
      logKernelE K u
  let H : BoxSpace d → ℂ := fun z =>
    Complex.exp (-Complex.I * ((∑ i : Fin d, t i * z i : ℝ) : ℂ)) * logKernel K z
  have hscale := Measure.integral_comp_smul (μ := (volume : Measure (ESpace d))) HE a
  have hmap : (∫ u : ESpace d, HE u) = ∫ z : BoxSpace d, H z := by
    have hp := (PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (BoxSpace d)).measurableEmbedding HE
    calc
      (∫ u : ESpace d, HE u) = ∫ z : BoxSpace d, HE (WithLp.toLp 2 z) := hp.symm
      _ = ∫ z : BoxSpace d, H z := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp [HE, H, logKernelE, euclEquiv]
        rw [inner_toLp]
        congr 1
        · apply congrArg Complex.exp
          push_cast
          simp_rw [mul_comm ((t _ : ℂ)) ((z _ : ℂ))]
          ring
  have hfourier :
      (𝓕 (scaledLogSchwartzE hK)) (WithLp.toLp 2 t : ESpace d) =
        (a ^ Module.finrank ℝ (ESpace d))⁻¹ • ∫ z : BoxSpace d, H z := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    simp only [smul_eq_mul]
    have hpoint :
        (fun u : ESpace d =>
          Complex.exp (((-2 * Real.pi * ⟪u, (WithLp.toLp 2 t : ESpace d)⟫ : ℝ) : ℂ) * Complex.I) *
            scaledLogSchwartzE hK u) =
        (fun u : ESpace d => HE (a • u)) := by
      funext u
      dsimp [HE]
      rw [scaledLogSchwartzE_apply hK]
      congr 1
      rw [real_inner_smul_left]
      dsimp [a]
      ring
    rw [hpoint]
    have hscale' := Measure.integral_comp_smul_of_nonneg
      (μ := (volume : Measure (ESpace d))) HE a (hR := by dsimp [a]; positivity)
    rw [hscale', hmap]
  unfold separationCoefficient
  rw [hfourier]
  have hfd : Module.finrank ℝ (ESpace d) = d := by simp [ESpace]
  have hscalar : ((2 * Real.pi : ℝ) : ℂ) ^ (-(d : ℤ)) =
      (((2 * Real.pi : ℝ) ^ (Module.finrank ℝ (ESpace d)))⁻¹ : ℂ) := by
    rw [hfd]
    rw [← Complex.ofReal_pow]
    norm_num [zpow_neg, Complex.ofReal_inv]
  rw [hscalar]
  dsimp [a]
  congr 1
  · norm_num [Complex.ofReal_inv]
  · apply integral_congr_ae
    filter_upwards [] with z
    change K (fun i => Real.exp (z i)) * _ = _ * K (fun i => Real.exp (z i))
    ring

end QRHShort
