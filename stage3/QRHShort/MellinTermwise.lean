import QRHShort.MellinMobius
import QRHShort.MellinWeight
import QRHShort.IdealMobiusSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The termwise Mellin identity in paper2.tex:742--750, in its initial half-plane
Re(s) > 1. Absolute convergence is proved from the actual ideal Möbius series.
No interchange of an infinite sum and an integral is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Classical Set MeasureTheory

namespace QRHShort

/-- The L1 norm of a Mellin integrand, including its change-of-scale factor. -/
theorem integral_norm_mellin_comp_mul (W : ℝ → ℂ) (s : ℂ) {a : ℝ}
    (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * W (a * t)‖) =
      ‖(a : ℂ) ^ (-s)‖ * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * W t‖ := by
  have hpull : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * W (a * t))
      (fun t : ℝ => (a : ℂ) ^ (1 - s) *
        ((↑(a * t) : ℂ) ^ (s - 1) * W (a * t))) (Ioi 0) := by
    intro t ht
    dsimp only [Function.comp_apply]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (le_of_lt ht),
      ← mul_assoc, ← mul_assoc, (by ring : (1 : ℂ) - s = -(s - 1)),
      Complex.cpow_neg, inv_mul_cancel₀, one_mul]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))
  have hfactor : ‖(a : ℂ) ^ (1 - s)‖ * a⁻¹ = ‖(a : ℂ) ^ (-s)‖ := by
    have h : (a : ℂ) ^ (1 - s) * (a : ℂ)⁻¹ = (a : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'),
        Complex.cpow_one, mul_right_comm, mul_inv_cancel₀
          (Complex.ofReal_ne_zero.mpr ha.ne'), one_mul]
    simpa only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha] using congrArg norm h
  calc
    _ = ∫ t in Ioi (0 : ℝ), ‖(a : ℂ) ^ (1 - s)‖ *
        ‖(↑(a * t) : ℂ) ^ (s - 1) * W (a * t)‖ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [Function.comp_apply]
      have hpoint := hpull ht
      dsimp only [Function.comp_apply] at hpoint
      calc
        ‖(t : ℂ) ^ (s - 1) * W (a * t)‖ =
            ‖(a : ℂ) ^ (1 - s) *
              ((↑(a * t) : ℂ) ^ (s - 1) * W (a * t))‖ :=
          congrArg norm hpoint
        _ = _ := norm_mul _ _
    _ = ‖(a : ℂ) ^ (1 - s)‖ * (a⁻¹ *
        ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * W t‖) := by
      rw [integral_const_mul]
      have hcomp := integral_comp_mul_left_Ioi
        (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) * W t‖) 0 ha
      convert congrArg (fun z => ‖(a : ℂ) ^ (1 - s)‖ * z) hcomp using 1 <;>
        simp only [mul_zero, smul_eq_mul]
    _ = _ := by rw [← mul_assoc, hfactor]

private def mobiusMellinTerm (c : ArithmeticContext) (W : ℝ → ℂ) (s : ℂ)
    (n : Ideal O) (t : ℝ) : ℂ :=
  if Outside c.S n then
    (t : ℂ) ^ (s - 1) * ((mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n * t))
  else 0

private theorem mobiusMellinTerm_integrable (c : ArithmeticContext)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    (s : ℂ) (n : Ideal O) :
    IntegrableOn (mobiusMellinTerm c W s n) (Ioi 0) := by
  by_cases hn : Outside c.S n
  · have h := ((MellinConvergent.comp_mul_left (normIdeal_pos hn.1)).mpr
      (hW.mellinConvergent s)).const_smul ((mobius n : ℂ) * c.nu.onIdeal n)
    unfold mobiusMellinTerm
    simp_rw [if_pos hn]
    change IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        ((mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n * t))) (Ioi 0)
    simpa only [MellinConvergent, smul_eq_mul,
      mul_left_comm, mul_assoc] using h
  · unfold mobiusMellinTerm
    simp_rw [if_neg hn]
    exact integrable_zero ℝ ℂ (volume.restrict (Ioi 0))

private theorem integral_norm_mobiusMellinTerm (c : ArithmeticContext)
    (W : ℝ → ℂ) (s : ℂ) (n : Ideal O) :
    (∫ t in Ioi (0 : ℝ), ‖mobiusMellinTerm c W s n t‖) =
      ‖mobiusSeriesTerm c s n‖ *
        ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * W t‖ := by
  by_cases hn : Outside c.S n
  · simp only [mobiusMellinTerm, mobiusSeriesTerm, if_pos hn]
    have hterm (t : ℝ) :
        ‖(t : ℂ) ^ (s - 1) * ((mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n * t))‖ =
        ‖(mobius n : ℂ) * c.nu.onIdeal n‖ *
          ‖(t : ℂ) ^ (s - 1) * W (normIdeal n * t)‖ := by
      rw [show (t : ℂ) ^ (s - 1) *
          ((mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n * t)) =
          ((mobius n : ℂ) * c.nu.onIdeal n) *
            ((t : ℂ) ^ (s - 1) * W (normIdeal n * t)) by ring, norm_mul]
    simp_rw [hterm]
    rw [integral_const_mul, integral_norm_mellin_comp_mul W s (normIdeal_pos hn.1)]
    simp only [norm_mul]
    ring
  · simp only [mobiusMellinTerm, mobiusSeriesTerm, if_neg hn, norm_zero,
      integral_zero, zero_mul]

private theorem integral_mobiusMellinTerm (c : ArithmeticContext)
    (W : ℝ → ℂ) (s : ℂ) (n : Ideal O) :
    (∫ t in Ioi (0 : ℝ), mobiusMellinTerm c W s n t) =
      mobiusSeriesTerm c s n * mellin W s := by
  by_cases hn : Outside c.S n
  · simp only [mobiusMellinTerm, if_pos hn]
    change mellin (fun t => ((mobius n : ℂ) * c.nu.onIdeal n) • W (normIdeal n * t)) s = _
    rw [mellin_const_smul, mellin_comp_mul_left W s (normIdeal_pos hn.1)]
    simp only [smul_eq_mul, mobiusSeriesTerm, if_pos hn, mul_assoc]
  · simp only [mobiusMellinTerm, mobiusSeriesTerm, if_neg hn, integral_zero, zero_mul]

/-- The actual Möbius Mellin integral equals the Mellin transform of the test
weight times the absolutely convergent ideal series in Re(s) > 1. -/
theorem mobiusMellin_eq_mellin_mul_series (c : ArithmeticContext)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    (s : ℂ) (hs : 1 < s.re) :
    mobiusMellin c W s = mellin W s * mobiusSeries c s := by
  have hsum : Summable (fun n : Ideal O =>
      ∫ t in Ioi (0 : ℝ), ‖mobiusMellinTerm c W s n t‖) := by
    simp_rw [integral_norm_mobiusMellinTerm]
    exact (mobiusSeriesTerm_norm_summable c s hs).mul_right _
  have hcongr : EqOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * originalSum c W t⁻¹ 1)
      (fun t : ℝ => ∑' n : Ideal O, mobiusMellinTerm c W s n t) (Ioi 0) := by
    intro t _
    dsimp only [Function.comp_apply]
    change (t : ℂ) ^ (s - 1) * originalSum c W t⁻¹ 1 =
      ∑' n : Ideal O, mobiusMellinTerm c W s n t
    rw [originalSum_one_eq_mobius, ← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : Outside c.S n
    · simp only [if_pos hn, mobiusMellinTerm, div_inv_eq_mul]
    · simp only [if_neg hn, mobiusMellinTerm, mul_zero]
  calc
    mobiusMellin c W s = mellin (fun t : ℝ => originalSum c W t⁻¹ 1) s :=
      (mellin_comp_inv (fun t : ℝ => originalSum c W t 1) s).symm
    _ = ∫ t in Ioi (0 : ℝ), ∑' n : Ideal O, mobiusMellinTerm c W s n t := by
      exact setIntegral_congr_fun measurableSet_Ioi hcongr
    _ = ∑' n : Ideal O, ∫ t in Ioi (0 : ℝ), mobiusMellinTerm c W s n t :=
      (integral_tsum_of_summable_integral_norm
        (mobiusMellinTerm_integrable c hW s) hsum).symm
    _ = ∑' n : Ideal O, mobiusSeriesTerm c s n * mellin W s :=
      tsum_congr (integral_mobiusMellinTerm c W s)
    _ = mellin W s * mobiusSeries c s := by
      rw [tsum_mul_right, mul_comm]
      rfl

end QRHShort
