import QRHShort.Energy
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
The test weight in paper2.tex:728--735. Mathlib uses
`mellin W s = integral (y^(s-1) * W y)` on the positive real axis.
We take a nonnegative bump b supported strictly between 1 and 2 and put
phi(y) = y*b(y), W(y) = y^(1-rho)*b(y). Thus W = y^(-rho)*phi
on the positive axis and its Mellin value at rho is the positive integral of b.
Compactly supported continuous weights also have convergent Mellin integrals
at every complex argument; smooth supported weights have entire transforms.
-/

noncomputable section
open scoped Topology
open Classical Filter Set MeasureTheory Asymptotics

namespace QRHShort

private theorem supported_isBigO_atTop {I : SupportInterval} {W : ℝ → ℂ}
    (hsupp : Function.support W ⊆ Icc I.lo I.hi) (a : ℝ) :
    W =O[atTop] (fun y : ℝ => y ^ a) := by
  apply IsBigO.of_bound 0
  filter_upwards [eventually_ge_atTop (I.hi + 1)] with y hy
  have hw : W y = 0 := by
    by_contra hw
    have := (hsupp hw).2
    linarith
  simp only [hw, norm_zero, zero_mul, le_refl]

private theorem supported_isBigO_atZero {I : SupportInterval} {W : ℝ → ℂ}
    (hsupp : Function.support W ⊆ Icc I.lo I.hi) (a : ℝ) :
    W =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ a) := by
  apply IsBigO.of_bound 0
  have hsmall : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y < I.lo :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds I.lo_pos)
  filter_upwards [hsmall] with y hy
  have hw : W y = 0 := by
    by_contra hw
    exact (not_le_of_gt hy) (hsupp hw).1
  simp only [hw, norm_zero, zero_mul, le_refl]

/-- Continuity and support in a compact positive interval suffice for absolute
convergence at every complex Mellin argument. No smoothness is needed. -/
theorem mellinConvergent_of_continuous_supported {I : SupportInterval} {W : ℝ → ℂ}
    (hcont : Continuous W) (hsupp : Function.support W ⊆ Icc I.lo I.hi) (s : ℂ) :
    MellinConvergent W s := by
  exact mellinConvergent_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
    (hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (supported_isBigO_atTop hsupp (-(s.re + 1))) (by linarith)
    (supported_isBigO_atZero hsupp (-(s.re - 1))) (by linarith)

theorem SmoothSupported.mellinConvergent {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (s : ℂ) : MellinConvergent W s :=
  mellinConvergent_of_continuous_supported hW.1.continuous hW.2 s

/-- The norm weight needs continuity rather than smoothness at its zeros. -/
theorem SmoothSupported.norm_mellinConvergent {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (s : ℂ) :
    MellinConvergent (fun y => (‖W y‖ : ℂ)) s := by
  apply mellinConvergent_of_continuous_supported
    (Complex.continuous_ofReal.comp hW.1.continuous.norm) (I := I) (s := s)
  intro y hy
  have hWnz : W y ≠ 0 := by
    intro hw
    apply hy
    change (‖W y‖ : ℂ) = 0
    rw [hw]
    simp
  exact hW.2 hWnz

theorem SmoothSupported.mellin_differentiable {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) : Differentiable ℂ (mellin W) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
    (hW.1.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (supported_isBigO_atTop hW.2 (-(s.re + 1))) (by linarith)
    (supported_isBigO_atZero hW.2 (-(s.re - 1))) (by linarith)

theorem SmoothSupported.mellin_analyticOnNhd {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) : AnalyticOnNhd ℂ (mellin W) univ :=
  hW.mellin_differentiable.differentiableOn.analyticOnNhd isOpen_univ

private def mellinBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem mellinBump_support {y : ℝ} (hy : mellinBump y ≠ 0) :
    y ∈ Icc (1 : ℝ) 2 := by
  have hball : y ∈ Metric.ball (3 / 2 : ℝ) mellinBump.rOut :=
    mellinBump.support_eq ▸ hy
  have habs : |y - 3 / 2| < (1 / 4 : ℝ) := by
    simpa only [Metric.mem_ball, Real.dist_eq, mellinBump] using hball
  constructor <;> linarith [(abs_lt.mp habs).1, (abs_lt.mp habs).2]

private theorem mellinBump_zero_of_lt_one {y : ℝ} (hy : y < 1) : mellinBump y = 0 := by
  by_contra hw
  exact (not_le_of_gt hy) (mellinBump_support hw).1

private theorem weighted_mellinBump_contDiff (a : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℝ => (y : ℂ) ^ a * (mellinBump y : ℂ)) := by
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ℝ => (mellinBump y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (mellinBump.contDiff (n := (⊤ : ℕ∞)))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_id.log hx.ne')
    have hexp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * a)) x :=
      (hlog.mul contDiffAt_const).cexp
    apply (hexp.mul hb.contDiffAt).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      ← Complex.ofReal_log hy.le]
  · have hxone : x < 1 := by linarith
    have hz : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (0 : ℂ)) x :=
      contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxone] with y hy
    simp only [mellinBump_zero_of_lt_one hy, Complex.ofReal_zero, mul_zero]

/-- At any prescribed complex point there is a smooth compactly supported
weight on [1,2] whose actual Mathlib Mellin transform is nonzero. -/
theorem exists_smoothSupported_mellin_ne_zero (ρ : ℂ) :
    ∃ (I : SupportInterval) (W : ℝ → ℂ), SmoothSupported I W ∧ mellin W ρ ≠ 0 := by
  let I : SupportInterval := ⟨1, 2, by norm_num, by norm_num⟩
  let W : ℝ → ℂ := fun y => (y : ℂ) ^ (1 - ρ) * (mellinBump y : ℂ)
  have hW : SmoothSupported I W := by
    refine ⟨weighted_mellinBump_contDiff (1 - ρ), ?_⟩
    intro y hy
    apply mellinBump_support
    intro hb
    exact hy (by simp only [W, hb, Complex.ofReal_zero, mul_zero])
  have hshift : mellin W ρ = mellin (fun y : ℝ => (mellinBump y : ℂ)) 1 := by
    have hexponent : ρ + (1 - ρ) = 1 := by ring
    simpa only [W, smul_eq_mul, hexponent] using
      mellin_cpow_smul (fun y : ℝ => (mellinBump y : ℂ)) ρ (1 - ρ)
  have hvalue : mellin W ρ = ((∫ y : ℝ, mellinBump y) : ℂ) := by
    rw [hshift]
    simp only [mellin, sub_self, Complex.cpow_zero, one_smul]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)]
    have hyone : y < 1 := by
      have : y ≤ 0 := le_of_not_gt hy
      linarith
    simp only [mellinBump_zero_of_lt_one hyone, Complex.ofReal_zero]
  refine ⟨I, W, hW, ?_⟩
  rw [hvalue]
  have hcast : (∫ y : ℝ, (mellinBump y : ℂ)) =
      Complex.ofReal (∫ y : ℝ, (mellinBump y : ℝ)) := by
    exact integral_ofReal
  rw [hcast]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mellinBump.integral_pos (μ := volume)))

end QRHShort
