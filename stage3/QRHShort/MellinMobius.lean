import QRHShort.ContextExistence
import QRHShort.PrimeComparison
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
The analytic part of paper2.tex:742--750: the actual smoothed Möbius sum has
a Mellin integral analytic in Re(s) > 11/12, assuming the pointwise estimate.
The initial Euler-product identity is a separate obligation and is not assumed
by any theorem in this module.
-/

noncomputable section
open scoped BigOperators Topology
open Classical Filter Set MeasureTheory Asymptotics

namespace QRHShort

/-- One fixed finite ideal ball suffices on every bounded positive range of D. -/
theorem originalSum_one_eq_finite_mobius (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D T : ℝ}
    (hD : 0 < D) (hDT : D ≤ T) :
    originalSum c W D 1 =
      ∑ n ∈ boundedDivisibleIdeals 1 (I.hi * T), if Outside c.S n then
        (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0 := by
  rw [originalSum_one_eq_mobius]
  apply tsum_eq_sum
  intro n hn
  by_cases hout : Outside c.S n
  · rw [if_pos hout]
    have hzero : W (normIdeal n / D) = 0 := by
      by_contra hw
      have hnorm : normIdeal n ≤ I.hi * T :=
        ((div_le_iff₀ hD).mp (hW.2 hw).2).trans
          (mul_le_mul_of_nonneg_left hDT (I.lo_pos.trans_le I.ordered).le)
      exact hn (mem_boundedDivisibleIdeals.mpr ⟨hnorm, one_dvd n, hout.1⟩)
    simp only [hzero, mul_zero]
  · exact if_neg hout

/-- Local finite support makes continuity independent of exchanging a limit
with an infinite sum. -/
theorem originalSum_one_continuousAt (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D : ℝ} (hD : 0 < D) :
    ContinuousAt (fun X : ℝ => originalSum c W X 1) D := by
  let P := boundedDivisibleIdeals 1 (I.hi * (D + 1))
  have hfinite : ContinuousAt (fun X : ℝ => ∑ n ∈ P,
      if Outside c.S n then (mobius n : ℂ) * c.nu.onIdeal n *
        W (normIdeal n / X) else 0) D := by
    apply tendsto_finsetSum
    intro n _
    by_cases hn : Outside c.S n
    · simp only [if_pos hn]
      exact continuousAt_const.mul (hW.1.continuous.continuousAt.comp
        (continuousAt_const.div continuousAt_id hD.ne'))
    · simp only [if_neg hn]
      exact continuousAt_const
  apply hfinite.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hD, Iio_mem_nhds (lt_add_one D)] with X hX hupper
  exact originalSum_one_eq_finite_mobius c I hW hX hupper.le

theorem originalSum_one_continuousOn (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) :
    ContinuousOn (fun D : ℝ => originalSum c W D 1) (Ioi 0) :=
  fun _ hD => (originalSum_one_continuousAt c I hW hD).continuousWithinAt

/-- Every surviving ideal has norm at least one, so the sum vanishes near D=0. -/
theorem originalSum_one_eq_zero_of_small_scale (c : ArithmeticContext)
    (I : SupportInterval) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (hscale : I.hi * D < 1) :
    originalSum c W D 1 = 0 := by
  rw [originalSum_one_eq_mobius]
  rw [← tsum_zero]
  apply tsum_congr
  intro n
  by_cases hn : Outside c.S n
  · rw [if_pos hn]
    have hnorm : 1 ≤ normIdeal n := by
      have hnabs : n.absNorm ≠ 0 := fun h => hn.1 (Ideal.absNorm_eq_zero_iff.mp h)
      change (1 : ℝ) ≤ (n.absNorm : ℝ)
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnabs)
    have hw : W (normIdeal n / D) = 0 := by
      by_contra hw
      have hupper := (div_le_iff₀ hD).mp (hW.2 hw).2
      linarith
    simp only [hw, mul_zero]
  · rw [if_neg hn, tsum_zero]

theorem originalSum_one_isBigO_atTop (hp : PointwiseMobiusEstimate)
    (c : ArithmeticContext) (I : SupportInterval) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {ε : ℝ} (hε : 0 < ε) :
    (fun D : ℝ => originalSum c W D 1) =O[atTop]
      (fun D : ℝ => D ^ ((11 : ℝ) / 12 + ε)) := by
  obtain ⟨C, _, hbound⟩ := hp c I W ε hW hε
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with D hD
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 2).trans hD
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hD0 _)]
    using hbound D hD

theorem originalSum_one_isBigO_atZero (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) (b : ℝ) :
    (fun D : ℝ => originalSum c W D 1) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by
  have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
  have hδ : 0 < 1 / I.hi := one_div_pos.mpr hhi
  apply IsBigO.of_bound 0
  have hsmall : ∀ᶠ D : ℝ in 𝓝[>] (0 : ℝ), D < 1 / I.hi :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hsmall] with D hD hsmallD
  have hscale : I.hi * D < 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hhi).mp hsmallD
  rw [originalSum_one_eq_zero_of_small_scale c I hW hD hscale]
  simp only [norm_zero, zero_mul, le_refl]

/-- Mathlib's Mellin convention at -s is ∫ D^(-s-1) A(D) dD. -/
def mobiusMellin (c : ArithmeticContext) (W : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin (fun D : ℝ => originalSum c W D 1) (-s)

theorem mobiusMellin_differentiableAt (hp : PointwiseMobiusEstimate)
    (c : ArithmeticContext) (I : SupportInterval) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {s : ℂ} (hs : (11 : ℝ) / 12 < s.re) :
    DifferentiableAt ℂ (mobiusMellin c W) s := by
  let ε : ℝ := (s.re - (11 : ℝ) / 12) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have htop : (fun D : ℝ => originalSum c W D 1) =O[atTop]
      (fun D : ℝ => D ^ (-(-((11 : ℝ) / 12 + ε)))) := by
    simpa only [neg_neg] using originalSum_one_isBigO_atTop hp c I hW hε
  have hd := mellin_differentiableAt_of_isBigO_rpow
    (a := -((11 : ℝ) / 12 + ε)) (b := (-s).re - 1) (s := -s)
    ((originalSum_one_continuousOn c I hW).locallyIntegrableOn measurableSet_Ioi)
    htop (by dsimp [ε]; linarith)
    (originalSum_one_isBigO_atZero c I hW (-((-s).re - 1))) (by linarith)
  change DifferentiableAt ℂ
    (fun x : ℂ => mellin (fun D : ℝ => originalSum c W D 1) (-x)) s
  convert hd.comp s differentiableAt_id.neg using 1
  rfl

theorem mobiusMellin_analyticOnNhd (hp : PointwiseMobiusEstimate)
    (c : ArithmeticContext) (I : SupportInterval) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) :
    AnalyticOnNhd ℂ (mobiusMellin c W) {s : ℂ | (11 : ℝ) / 12 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (mobiusMellin_differentiableAt hp c I hW hs).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end QRHShort
