import QRHShort.SmoothingStatements
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory

namespace QRHShort

def meanSquareTail (t : BoxSpace 2) : ℝ := ((1 + ‖t‖) ^ 4)⁻¹

theorem meanSquareTail_nonneg (t : BoxSpace 2) : 0 ≤ meanSquareTail t := by
  unfold meanSquareTail
  positivity

theorem meanSquareTail_integrable : Integrable meanSquareTail := by
  have h : Integrable (fun t : BoxSpace 2 => (1 + ‖t‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by norm_num [BoxSpace, Module.finrank_fin_fun])
  convert h using 1
  funext t
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖t‖), Real.rpow_ofNat]
  rfl

/-- The derivative loss `2*m` from the two test modes leaves four powers of
decay in the two-dimensional coefficient variable. -/
theorem meanSquareEnvelope_eq (m : ℕ) (A B H : ℝ) (t : BoxSpace 2) :
    (B * H / (1 + ‖t‖) ^ (2 * m + 4)) *
      (A * (1 + ‖t‖) ^ m) * (A * (1 + ‖t‖) ^ m) =
      (B * A ^ 2 * H) * meanSquareTail t := by
  have hp : (1 + ‖t‖) ^ (2 * m + 4) =
      (1 + ‖t‖) ^ m * (1 + ‖t‖) ^ m * (1 + ‖t‖) ^ 4 := by
    calc
      _ = (1 + ‖t‖) ^ ((m + m) + 4) := by congr 1; omega
      _ = _ := by simp only [pow_add]
  have hz : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  unfold meanSquareTail
  rw [hp]
  field_simp [hz]
  <;> ring

theorem meanSquareEnvelope_integrable (m : ℕ) (A B H : ℝ) :
    Integrable (fun t : BoxSpace 2 => (B * H / (1 + ‖t‖) ^ (2 * m + 4)) *
      (A * (1 + ‖t‖) ^ m) * (A * (1 + ‖t‖) ^ m)) := by
  simp_rw [meanSquareEnvelope_eq]
  exact meanSquareTail_integrable.const_mul _

theorem meanSquareEnvelope_integral (m : ℕ) (A B H : ℝ) :
    (∫ t : BoxSpace 2, (B * H / (1 + ‖t‖) ^ (2 * m + 4)) *
      (A * (1 + ‖t‖) ^ m) * (A * (1 + ‖t‖) ^ m)) =
      (B * A ^ 2 * (∫ t : BoxSpace 2, meanSquareTail t)) * H := by
  simp_rw [meanSquareEnvelope_eq]
  rw [integral_const_mul]
  ring

end QRHShort

#print axioms QRHShort.meanSquareTail_integrable
#print axioms QRHShort.meanSquareEnvelope_integrable
#print axioms QRHShort.meanSquareEnvelope_integral
