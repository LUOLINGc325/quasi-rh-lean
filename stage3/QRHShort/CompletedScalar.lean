import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QRHShort.CompletedAssembly

theorem square_shift_bound_identity (H F X V : ℝ) (hV : V ≠ 0) :
    H / V ^ 2 + (H / V ^ 2) ^ 2 * (F * V ^ 2) / X =
      (H + H ^ 2 * F / X) / V ^ 2 := by
  by_cases hX : X = 0
  · simp [hX]
  · field_simp
    <;> ring

/-- A single enlargement handles both the row radius and the enlarged twist.
The exponent `2*C` is independent of the external radius constant `a`. -/
theorem enlarged_ranges {a D C H F : ℝ} (ha : 1 ≤ a) (hD : 2 ≤ D)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hHmax : H ≤ D ^ C)
    (hF : 1 ≤ F) (hFmax : F ≤ D ^ C) :
    2 ≤ a * D ∧ a * H ≤ (a * D) ^ (2 * C) ∧
      D ^ C ≤ (a * D) ^ (2 * C) ∧ F * (a * H) ≤ (a * D) ^ (2 * C) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hD0 : 0 ≤ D := by linarith
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hDC : 1 ≤ D ^ C := Real.one_le_rpow (by linarith) (by linarith)
  have hDC0 : 0 ≤ D ^ C := zero_le_one.trans hDC
  have haexp : a ≤ a ^ (2 * C) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le ha (show (1 : ℝ) ≤ 2 * C by linarith))
  have hDexp : D ^ (2 * C) = (D ^ C) ^ (2 : ℕ) := by
    rw [mul_comm, Real.rpow_mul hD0, Real.rpow_two]
  have hscale : a * (D ^ C) ^ (2 : ℕ) ≤ (a * D) ^ (2 * C) := by
    rw [Real.mul_rpow ha0 hD0, hDexp]
    exact mul_le_mul_of_nonneg_right haexp (sq_nonneg _)
  have hFH : F * (a * H) ≤ (a * D) ^ (2 * C) := by
    apply le_trans _ hscale
    calc
      F * (a * H) = a * (F * H) := by ring
      _ ≤ a * (D ^ C * D ^ C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hFmax hHmax hH0 hDC0) ha0
      _ = a * (D ^ C) ^ (2 : ℕ) := by ring
  refine ⟨hD.trans (le_mul_of_one_le_left hD0 ha), ?_, ?_, hFH⟩
  · exact (le_mul_of_one_le_left (mul_nonneg ha0 hH0) hF).trans hFH
  · have hDCsq : D ^ C ≤ (D ^ C) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (D ^ C - 1)]
    exact hDCsq.trans ((le_mul_of_one_le_left (sq_nonneg _) ha).trans hscale)

theorem radius_polynomial_bound {a H F X : ℝ} (ha : 1 ≤ a) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hX : 0 ≤ X) :
    a * H + (a * H) ^ (2 : ℕ) * F / X ≤
      a ^ (2 : ℕ) * (H + H ^ (2 : ℕ) * F / X) := by
  have haa : a ≤ a ^ (2 : ℕ) := by nlinarith [sq_nonneg (a - 1)]
  have hlin := mul_le_mul_of_nonneg_right haa hH
  calc
    a * H + (a * H) ^ (2 : ℕ) * F / X =
        a * H + a ^ (2 : ℕ) * (H ^ (2 : ℕ) * F / X) := by ring
    _ ≤ a ^ (2 : ℕ) * H + a ^ (2 : ℕ) * (H ^ (2 : ℕ) * F / X) :=
      add_le_add hlin le_rfl
    _ = _ := by ring

end QRHShort.CompletedAssembly

#print axioms QRHShort.CompletedAssembly.square_shift_bound_identity
#print axioms QRHShort.CompletedAssembly.enlarged_ranges
#print axioms QRHShort.CompletedAssembly.radius_polynomial_bound
