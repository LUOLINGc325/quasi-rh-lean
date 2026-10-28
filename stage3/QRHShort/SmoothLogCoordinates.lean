import QRHShort.SmoothMultiNorm
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory

namespace QRHShort

def logSupportBox {d : ℕ} (I : Fin d → SupportInterval) : Set (BoxSpace d) :=
  Set.Icc (fun i => Real.log (I i).lo) (fun i => Real.log (I i).hi)

def expCoordinates (d : ℕ) (y : BoxSpace d) : BoxSpace d :=
  fun i => Real.exp (y i)

def logKernel {d : ℕ} (K : BoxSpace d → ℂ) : BoxSpace d → ℂ :=
  K ∘ expCoordinates d

theorem isCompact_logSupportBox {d : ℕ} (I : Fin d → SupportInterval) :
    IsCompact (logSupportBox I) := isCompact_Icc

theorem contDiff_expCoordinates (d : ℕ) :
    ContDiff ℝ ∞ (expCoordinates d) := by
  unfold expCoordinates
  fun_prop

theorem SmoothBox.contDiff_logKernel {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) :
    ContDiff ℝ ∞ (logKernel K) :=
  hK.1.comp (contDiff_expCoordinates d)

theorem SmoothBox.support_logKernel_subset {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) :
    Function.support (logKernel K) ⊆ logSupportBox I := by
  intro y hy
  have hm := hK.2 hy
  constructor
  · intro i
    exact (Real.log_le_iff_le_exp (I i).lo_pos).mpr (hm i).1
  · intro i
    exact (Real.le_log_iff_exp_le ((I i).lo_pos.trans_le (I i).ordered)).mpr (hm i).2

theorem SmoothBox.tsupport_logKernel_subset {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) :
    tsupport (logKernel K) ⊆ logSupportBox I :=
  closure_minimal hK.support_logKernel_subset isClosed_Icc

theorem SmoothBox.hasCompactSupport_logKernel {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) : HasCompactSupport (logKernel K) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_logSupportBox I)
    hK.support_logKernel_subset

/-- The bound is chosen once for the fixed smooth coordinate map and compact
set.  In its application below it is independent of the varying kernel. -/
theorem exists_bound_iteratedFDeriv_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) {S : Set E} (hS : IsCompact S) (q : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ q, ∀ y ∈ S, ‖iteratedFDeriv ℝ i f y‖ ≤ D := by
  classical
  have hex (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ S, ‖iteratedFDeriv ℝ i f y‖ ≤ C := by
    have hc : Continuous (fun y => ‖iteratedFDeriv ℝ i f y‖) :=
      (hf.continuous_iteratedFDeriv (by simp)).norm
    obtain ⟨C, hC⟩ := hS.bddAbove_image hc.continuousOn
    refine ⟨max 0 C, le_max_left _ _, ?_⟩
    intro y hy
    exact (hC (Set.mem_image_of_mem _ hy)).trans (le_max_right _ _)
  choose C hC hCb using hex
  let D : ℝ := 1 + ∑ i ∈ Finset.range (q + 1), C i
  have hsum : 0 ≤ ∑ i ∈ Finset.range (q + 1), C i :=
    Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨D, le_add_of_nonneg_right hsum, ?_⟩
  intro i hi y hy
  exact (hCb i y hy).trans ((Finset.single_le_sum (fun i _ => hC i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans
      (le_add_of_nonneg_left zero_le_one))

theorem logKernel_derivative_bound (d : ℕ) (I : Fin d → SupportInterval) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : BoxSpace d → ℂ, SmoothBox I K →
      ∀ j ≤ q, ∀ y : BoxSpace d,
        ‖iteratedFDeriv ℝ j (logKernel K) y‖ ≤ C * multiWeightNorm q K := by
  classical
  obtain ⟨D, hD, hb⟩ := exists_bound_iteratedFDeriv_on_compact
    (contDiff_expCoordinates d) (isCompact_logSupportBox I) q
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  let C : ℝ := ∑ j ∈ Finset.range (q + 1), (j.factorial : ℝ) * D ^ j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro K hK j hj y
  have hK0 := multiWeightNorm_nonneg hK q
  by_cases hy : y ∈ logSupportBox I
  · have hcomp : ‖iteratedFDeriv ℝ j (logKernel K) y‖ ≤
        (j.factorial : ℝ) * multiWeightNorm q K * D ^ j := by
      apply norm_iteratedFDeriv_comp_le hK.1 (contDiff_expCoordinates d) (by simp) y
      · intro i hi
        exact norm_iteratedFDeriv_le_multiWeightNorm hK (hi.trans hj) _
      · intro i hi₁ hi₂
        exact (hb i (hi₂.trans hj) y hy).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hD hi₁)
    calc
      _ ≤ (j.factorial : ℝ) * multiWeightNorm q K * D ^ j := hcomp
      _ = ((j.factorial : ℝ) * D ^ j) * multiWeightNorm q K := by ring
      _ ≤ C * multiWeightNorm q K := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i : ℕ => (i.factorial : ℝ) * D ^ i)
          (fun i _ => by positivity)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) hK0
  · have hz : iteratedFDeriv ℝ j (logKernel K) y = 0 := by
      by_contra hn
      exact hy (hK.tsupport_logKernel_subset ((support_iteratedFDeriv_subset j) hn))
    simpa only [hz, norm_zero] using mul_nonneg hC hK0

theorem logKernel_derivative_integrable {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) (j : ℕ) :
    Integrable (fun y => ‖iteratedFDeriv ℝ j (logKernel K) y‖) :=
  ((hK.contDiff_logKernel.continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
    (hK.hasCompactSupport_logKernel.iteratedFDeriv j)).norm

theorem logKernel_derivative_integral_bound (d : ℕ)
    (I : Fin d → SupportInterval) (q : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ K : BoxSpace d → ℂ, SmoothBox I K →
      ∀ j ≤ q,
        (∫ y : BoxSpace d, ‖iteratedFDeriv ℝ j (logKernel K) y‖) ≤
          A * multiWeightNorm q K := by
  obtain ⟨C, hC, hCb⟩ := logKernel_derivative_bound d I q
  refine ⟨volume.real (logSupportBox I) * C, by positivity, ?_⟩
  intro K hK j hj
  have hz : ∀ y, y ∉ logSupportBox I →
      ‖iteratedFDeriv ℝ j (logKernel K) y‖ = 0 := by
    intro y hy
    have he : iteratedFDeriv ℝ j (logKernel K) y = 0 := by
      by_contra hn
      exact hy (hK.tsupport_logKernel_subset ((support_iteratedFDeriv_subset j) hn))
    rw [he, norm_zero]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun y : BoxSpace d => ‖iteratedFDeriv ℝ j (logKernel K) y‖)
    (isCompact_logSupportBox I).measure_lt_top (C := C * multiWeightNorm q K)
    (fun y _ => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hCb K hK j hj y)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))] at hb
  convert hb using 1 <;> ring

end QRHShort

#print axioms QRHShort.SmoothBox.hasCompactSupport_logKernel
#print axioms QRHShort.logKernel_derivative_bound
#print axioms QRHShort.logKernel_derivative_integral_bound
