import QRH.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace QRH

/-- Squaring the positive-gap estimate yields the advertised contraction factor. -/
theorem gap_square_bound {D κ H X F : ℝ} (hD : 1 ≤ D)
    (hH : 1 ≤ H) (hX : 1 ≤ X) (hF : 1 ≤ F)
    (hgap : H ≤ (X * F) * D ^ (-κ)) :
    H * (H / (X * F)) ^ 2 ≤ D ^ (-2 * κ) * H := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hXF : 0 < X * F :=
    mul_pos (lt_of_lt_of_le zero_lt_one hX) (lt_of_lt_of_le zero_lt_one hF)
  have hratio : H / (X * F) ≤ D ^ (-κ) :=
    (div_le_iff₀ hXF).2 (by simpa only [mul_comm] using hgap)
  have hratio0 : 0 ≤ H / (X * F) := div_nonneg hH0 (le_of_lt hXF)
  have hsquare : (H / (X * F)) ^ 2 ≤ (D ^ (-κ)) ^ 2 := by
    simpa only [sq] using mul_self_le_mul_self hratio0 hratio
  have hpower : (D ^ (-κ)) ^ (2 : ℕ) = D ^ (-2 * κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]
    congr 1
    norm_num <;> ring
  calc
    H * (H / (X * F)) ^ 2 ≤ H * (D ^ (-κ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hH0
    _ = D ^ (-2 * κ) * H := by rw [hpower, mul_comm]

/-- The contraction takes a (j+1)-stage height to a j-stage height. -/
theorem induction_power_bound {D κ H : ℝ} (hD : 1 ≤ D) (hκ : 0 < κ)
    (j : ℕ) (hH : H ≤ D ^ (((j : ℝ) + 1) * κ)) :
    D ^ (-2 * κ) * H ≤ D ^ ((j : ℝ) * κ) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  calc
    D ^ (-2 * κ) * H ≤ D ^ (-2 * κ) * D ^ (((j : ℝ) + 1) * κ) :=
      mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg (le_of_lt hDpos) _)
    _ = D ^ (-2 * κ + ((j : ℝ) + 1) * κ) :=
      (Real.rpow_add hDpos _ _).symm
    _ ≤ D ^ ((j : ℝ) * κ) :=
      Real.rpow_le_rpow_of_exponent_le hD (by nlinarith)

/-- A finite induction height covers the entire bounded parameter range. -/
theorem finite_stage_exists {κ C : ℝ} (hκ : 0 < κ) :
    ∃ j : ℕ, C ≤ (j : ℝ) * κ ∧
      ∀ D : ℝ, 1 ≤ D → D ^ C ≤ D ^ ((j : ℝ) * κ) := by
  obtain ⟨j, hj⟩ := exists_nat_ge (C / κ)
  have hC : C ≤ (j : ℝ) * κ := (div_le_iff₀ hκ).mp hj
  exact ⟨j, hC, fun D hD => Real.rpow_le_rpow_of_exponent_le hD hC⟩

end QRH
