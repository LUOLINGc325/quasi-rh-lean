import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Generic real-variable input for turning a linear mass lower bound into one
with an arbitrary additive logarithmic term.  This file deliberately has no
dependence on the QRH/OAI development: callers only need a function
`mass : ℝ → ℝ`.
-/

noncomputable section

open Filter
open scoped Topology

namespace GenericMass

/-- A positive linear lower bound for a real-valued mass function. -/
def LinearMassLowerBound (mass : ℝ → ℝ) : Prop :=
  ∃ k : ℝ, 0 < k ∧ ∃ Y₀ : ℝ, 1 < Y₀ ∧
    ∀ Y : ℝ, Y₀ ≤ Y → k * Y ≤ mass Y

/-- A linear lower bound after absorbing any prescribed `A * log Y`. -/
def LogMassLowerBound (mass : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 ≤ A →
    ∃ Y₀ : ℝ, 1 < Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      A * Real.log Y + c * Y ≤ mass Y

/--
The ratio `log Y / Y` tends to zero, so a positive linear mass bound absorbs
every fixed logarithmic loss.  The proof uses only the standard Mathlib
limit for `log` versus the identity function.
-/
theorem logMassLowerBound_of_linear {mass : ℝ → ℝ}
    (hlinear : LinearMassLowerBound mass) :
    LogMassLowerBound mass := by
  obtain ⟨k, hk, Y₀, hY₀, hmass⟩ := hlinear
  refine ⟨k / 2, by linarith, ?_⟩
  intro A hA
  have hratio : Tendsto (fun Y : ℝ => A * (Real.log Y / Y)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun Y : ℝ => Real.log Y / Y) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    simpa using hbase.const_mul A
  have hsmall : ∀ᶠ Y : ℝ in atTop,
      A * (Real.log Y / Y) < k / 2 :=
    (tendsto_order.1 hratio).2 (k / 2) (by linarith [hk])
  obtain ⟨T, hT⟩ := eventually_atTop.1 hsmall
  let Y₁ : ℝ := max Y₀ (max T 2)
  have hY₁ : 1 < Y₁ := by
    dsimp [Y₁]
    exact lt_of_lt_of_le (by norm_num)
      ((le_max_right T 2).trans (le_max_right Y₀ (max T 2)))
  refine ⟨Y₁, hY₁, ?_⟩
  intro Y hY
  have hYpos : 0 < Y := zero_lt_one.trans (lt_of_lt_of_le hY₁ hY)
  have hTY : T ≤ Y := by
    exact (le_max_left T 2).trans
      ((le_max_right Y₀ (max T 2)).trans hY)
  have hY₀Y : Y₀ ≤ Y := (le_max_left Y₀ (max T 2)).trans hY
  have hsmallY := hT Y hTY
  have hmul : A * (Real.log Y / Y) * Y < (k / 2) * Y :=
    mul_lt_mul_of_pos_right hsmallY hYpos
  have hlog : A * Real.log Y ≤ (k / 2) * Y := by
    calc
      A * Real.log Y = A * (Real.log Y / Y) * Y := by
        field_simp [ne_of_gt hYpos]
      _ ≤ (k / 2) * Y := hmul.le
  linarith [hmass Y hY₀Y]

end GenericMass

