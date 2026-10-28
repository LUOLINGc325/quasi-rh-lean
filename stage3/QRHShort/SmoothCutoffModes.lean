import QRHShort.SmoothModeBounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith

/-! Fixed smooth cutoffs and the actual Mellin modes used in the mean-square
argument.  The positive extension makes the logarithmic phase smooth on all
of `ℝ`; on the support of the cutoff it is exactly `Real.log`. -/

noncomputable section
open scoped BigOperators ContDiff

namespace QRHShort

private def smoothPositiveExtension (x : ℝ) : ℝ :=
  1 + (x - 1) * Real.smoothTransition (2 * x - 1)

private theorem smoothPositiveExtension_contDiff :
    ContDiff ℝ ∞ smoothPositiveExtension := by
  unfold smoothPositiveExtension
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)))

private theorem smoothPositiveExtension_pos (x : ℝ) :
    0 < smoothPositiveExtension x := by
  unfold smoothPositiveExtension
  by_cases hhalf : x ≤ 1 / 2
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 * x - 1 ≤ 0)]
    norm_num
  · by_cases hone : 1 ≤ x
    · rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * x - 1)]
      linarith
    · have hprod : (1 - x) * Real.smoothTransition (2 * x - 1) ≤ 1 - x :=
        (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (by linarith)).trans_eq
          (mul_one _)
      nlinarith

private theorem smoothPositiveExtension_eq {x : ℝ} (hx : 1 ≤ x) :
    smoothPositiveExtension x = x := by
  unfold smoothPositiveExtension
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * x - 1)]
  ring

theorem exists_smooth_log_extension {a : ℝ} (ha : 0 < a) :
    ∃ L : ℝ → ℝ, ContDiff ℝ ∞ L ∧ ∀ x, a ≤ x → L x = Real.log x := by
  let P (x : ℝ) := a * smoothPositiveExtension (x / a)
  have hP : ContDiff ℝ ∞ P :=
    contDiff_const.mul (smoothPositiveExtension_contDiff.comp (by fun_prop))
  have hPpos (x : ℝ) : 0 < P x := mul_pos ha (smoothPositiveExtension_pos _)
  refine ⟨fun x => Real.log (P x), hP.log (fun x => (hPpos x).ne'), ?_⟩
  intro x hx
  have hax : 1 ≤ x / a := (le_div_iff₀ ha).mpr (by simpa using hx)
  have hPx : P x = x := by
    dsimp [P]
    rw [smoothPositiveExtension_eq hax]
    simpa only [mul_comm a (x / a)] using div_mul_cancel₀ x ha.ne'
  change Real.log (P x) = Real.log x
  rw [hPx]

theorem exists_interval_smooth_cutoff (I Istar : SupportInterval)
    (hlo : Istar.lo < I.lo) (hhi : I.hi < Istar.hi) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      Function.support χ ⊆ Set.Icc Istar.lo Istar.hi ∧
      ∀ x ∈ Set.Icc I.lo I.hi, χ x = 1 := by
  let χ (x : ℝ) :=
    Real.smoothTransition ((x - Istar.lo) / (I.lo - Istar.lo)) *
      Real.smoothTransition ((Istar.hi - x) / (Istar.hi - I.hi))
  have hdlo : 0 < I.lo - Istar.lo := sub_pos.mpr hlo
  have hdhi : 0 < Istar.hi - I.hi := sub_pos.mpr hhi
  have hχ : ContDiff ℝ ∞ χ :=
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop))
  refine ⟨χ, hχ, ?_, ?_⟩
  · intro x hx
    change χ x ≠ 0 at hx
    constructor
    · by_contra h
      apply hx
      dsimp [χ]
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hdlo.le), zero_mul]
    · by_contra h
      apply hx
      dsimp [χ]
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hdhi.le), mul_zero]
  · intro x hx
    have hl : 1 ≤ (x - Istar.lo) / (I.lo - Istar.lo) :=
      (le_div_iff₀ hdlo).mpr (by linarith [hx.1])
    have hr : 1 ≤ (Istar.hi - x) / (Istar.hi - I.hi) :=
      (le_div_iff₀ hdhi).mpr (by linarith [hx.2])
    simp only [χ, Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.one_of_one_le hr, one_mul]

theorem imaginaryExp_star_neg (t x : ℝ) :
    star (imaginaryExp (-t) x) = imaginaryExp t x := by
  simp only [imaginaryExp, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.ofReal_neg, map_neg, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  ring

theorem imaginaryExp_log_eq_cpow (t x : ℝ) (hx : 0 < x) :
    imaginaryExp t (Real.log x) = (x : ℂ) ^ (Complex.I * (t : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold imaginaryExp
  congr 1
  ring

/-- The constant is chosen before the frequency, and these modes are exactly
the cutoff complex powers at every positive argument. -/
theorem exists_mellin_cutoff_modes (I Istar : SupportInterval) (m : ℕ)
    (hlo : Istar.lo < I.lo) (hhi : I.hi < Istar.hi) :
    ∃ (χ : ℝ → ℂ) (F : ℝ → ℝ → ℂ) (A : ℝ), 0 ≤ A ∧
      (∀ x ∈ Set.Icc I.lo I.hi, χ x = 1) ∧
      (∀ t, SmoothSupported Istar (F t)) ∧
      (∀ t, weightNorm m (F t) ≤ A * (1 + |t|) ^ m) ∧
      (∀ t x, 0 < x → F t x = χ x * (x : ℂ) ^ (Complex.I * (t : ℂ))) ∧
      (∀ t x, star (F (-t) x) = F t x) := by
  obtain ⟨χ, hχsmooth, hχsupp, hχone⟩ := exists_interval_smooth_cutoff I Istar hlo hhi
  obtain ⟨L, hL, hLeq⟩ := exists_smooth_log_extension Istar.lo_pos
  let χc (x : ℝ) : ℂ := χ x
  have hχc : SmoothSupported Istar χc := by
    refine ⟨Complex.ofRealCLM.contDiff.comp hχsmooth, ?_⟩
    intro x hx
    apply hχsupp
    change χ x ≠ 0
    intro hz
    exact hx (by simp [χc, hz])
  let F (t x : ℝ) : ℂ := χc x * imaginaryExp t (L x)
  obtain ⟨A, hA, hAb⟩ := cutoff_phase_weightNorm_bound χc hχc L hL m
  refine ⟨χc, F, A, hA, ?_, fun t => (hAb t).1, fun t => (hAb t).2, ?_, ?_⟩
  · intro x hx
    simp only [χc, hχone x hx, Complex.ofReal_one]
  · intro t x hx
    by_cases hz : χ x = 0
    · simp only [F, χc, hz, Complex.ofReal_zero, zero_mul]
    · have hxI := hχsupp hz
      dsimp [F]
      rw [hLeq x hxI.1, imaginaryExp_log_eq_cpow t x hx]
  · intro t x
    change star ((χ x : ℂ) * imaginaryExp (-t) (L x)) =
      (χ x : ℂ) * imaginaryExp t (L x)
    simp only [star_mul, imaginaryExp_star_neg, Complex.star_def, Complex.conj_ofReal] <;>
      ring

end QRHShort

#print axioms QRHShort.exists_smooth_log_extension
#print axioms QRHShort.exists_interval_smooth_cutoff
#print axioms QRHShort.exists_mellin_cutoff_modes
