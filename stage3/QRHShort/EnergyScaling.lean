import QRHShort.WeightNorm
import QRHShort.EnergySupport
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

/-!
Constant scaling and normalization of the actual arithmetic weights and energies.
Multiplication by a nonzero field constant preserves summability, so the scaling
identities also hold for totalized sums. Actual column and finite outer convergence
are supplied separately by `EnergySupport` and `FiniteSupport`.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

private theorem scaled_masked_tsum {α : Type*} (P : α → Prop) (v : α → ℝ)
    [DecidablePred P] (s a : ℝ) :
    s * (∑' x, if P x then a * v x else 0) =
      a * (s * ∑' x, if P x then v x else 0) := by
  calc
    _ = s * ∑' x, a * (if P x then v x else 0) := by
      congr 1
      apply tsum_congr
      intro x
      split_ifs <;> simp
    _ = _ := by rw [tsum_mul_left]; ring

private theorem weighted_square_tsum_const_mul {α : Type*}
    (w : α → ℝ) (v : α → ℂ) (a : ℂ) :
    (∑' x, w x * ‖a * v x‖ ^ 2) = ‖a‖ ^ 2 * ∑' x, w x * ‖v x‖ ^ 2 := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  rw [norm_mul, mul_pow]
  ring

theorem columnSum_const_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X : ℝ) (k : O) (f : Ideal O) (a : ℂ) :
    columnSum c ξ (fun x => a * W x) X k f = a * columnSum c ξ W X k f := by
  unfold columnSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  split_ifs <;> ring

theorem rowEnergy_const_mul (column : O → ℂ) (H : ℝ) (a : ℂ) :
    rowEnergy (fun k => a * column k) H = ‖a‖ ^ 2 * rowEnergy column H := by
  unfold rowEnergy
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  split_ifs
  · rw [norm_mul, mul_pow]
  · simp

theorem energy_const_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (H X F : ℝ) (a : ℂ) :
    energy c ξ (fun x => a * W x) H X F = ‖a‖ ^ 2 * energy c ξ W H X F := by
  unfold energy
  simp_rw [columnSum_const_mul, rowEnergy_const_mul]
  convert scaled_masked_tsum
    (fun f : Ideal O => SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F)
    (fun f => rowEnergy (fun k => columnSum c ξ W X k f) H) ((X * F)⁻¹) (‖a‖ ^ 2) using 1
  all_goals
    congr 1
    apply tsum_congr
    intro f
    by_cases h : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F <;>
      simp [h]

theorem smoothedEnergy_const_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : ℝ → ℝ) (W : ℝ → ℂ) (H L F : ℝ) (a : ℂ) :
    smoothedEnergy c ξ Φ (fun x => a * W x) H L F =
      ‖a‖ ^ 2 * smoothedEnergy c ξ Φ W H L F := by
  unfold smoothedEnergy
  simp_rw [columnSum_const_mul, weighted_square_tsum_const_mul]
  convert scaled_masked_tsum
    (fun f : Ideal O => SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F)
    (fun f => ∑' k : O, Φ (normElement k / H) * ‖columnSum c ξ W L k f‖ ^ 2)
    ((L * F)⁻¹) (‖a‖ ^ 2) using 1
  all_goals
    congr 1
    apply tsum_congr
    intro f
    by_cases h : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F <;>
      simp [h]

theorem columnSum_eq_zero_of_weightNorm_eq_zero {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (hzero : weightNorm J W = 0)
    (c : ArithmeticContext) (ξ : RayCharacter c) (X : ℝ) (k : O) (f : Ideal O) :
    columnSum c ξ W X k f = 0 := by
  rw [(weightNorm_eq_zero_iff hW J).mp hzero]
  simp [columnSum]

theorem energy_eq_zero_of_weightNorm_eq_zero {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (hzero : weightNorm J W = 0)
    (c : ArithmeticContext) (ξ : RayCharacter c) (H X F : ℝ) :
    energy c ξ W H X F = 0 := by
  rw [(weightNorm_eq_zero_iff hW J).mp hzero]
  simp [energy, rowEnergy, columnSum]

theorem smoothedEnergy_eq_zero_of_weightNorm_eq_zero {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (hzero : weightNorm J W = 0)
    (c : ArithmeticContext) (ξ : RayCharacter c) (Φ : ℝ → ℝ) (H L F : ℝ) :
    smoothedEnergy c ξ Φ W H L F = 0 := by
  rw [(weightNorm_eq_zero_iff hW J).mp hzero]
  simp [smoothedEnergy, columnSum]

/-- Normalize by the real finite derivative norm, viewed as a complex scalar. -/
def normalizedWeight (J : ℕ) (W : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (weightNorm J W : ℂ)⁻¹ * W x

theorem SmoothSupported.normalizedWeight {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) : SmoothSupported I (normalizedWeight J W) :=
  hW.const_mul _

theorem weightNorm_normalizedWeight {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (hne : weightNorm J W ≠ 0) :
    weightNorm J (normalizedWeight J W) = 1 := by
  unfold QRHShort.normalizedWeight
  rw [ weightNorm_const_mul hW, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (weightNorm_nonneg hW J)]
  exact inv_mul_cancel₀ hne

theorem energy_normalizedWeight {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (c : ArithmeticContext) (ξ : RayCharacter c)
    (H X F : ℝ) :
    energy c ξ (normalizedWeight J W) H X F = energy c ξ W H X F / weightNorm J W ^ 2 := by
  unfold QRHShort.normalizedWeight
  rw [ energy_const_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (weightNorm_nonneg hW J), inv_pow, div_eq_mul_inv, mul_comm]

theorem smoothedEnergy_normalizedWeight {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : ℝ → ℝ) (H L F : ℝ) :
    smoothedEnergy c ξ Φ (normalizedWeight J W) H L F =
      smoothedEnergy c ξ Φ W H L F / weightNorm J W ^ 2 := by
  unfold QRHShort.normalizedWeight
  rw [ smoothedEnergy_const_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (weightNorm_nonneg hW J), inv_pow, div_eq_mul_inv, mul_comm]

theorem energy_eq_weightNorm_sq_mul_normalizedWeight {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (c : ArithmeticContext) (ξ : RayCharacter c)
    (H X F : ℝ) :
    energy c ξ W H X F = weightNorm J W ^ 2 * energy c ξ (normalizedWeight J W) H X F := by
  by_cases hzero : weightNorm J W = 0
  · rw [energy_eq_zero_of_weightNorm_eq_zero hW J hzero c ξ H X F, hzero]
    simp
  · have h := (eq_div_iff (pow_ne_zero 2 hzero)).mp
      (energy_normalizedWeight hW J c ξ H X F)
    simpa only [mul_comm] using h.symm

theorem smoothedEnergy_eq_weightNorm_sq_mul_normalizedWeight
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W) (J : ℕ)
    (c : ArithmeticContext) (ξ : RayCharacter c) (Φ : ℝ → ℝ) (H L F : ℝ) :
    smoothedEnergy c ξ Φ W H L F =
      weightNorm J W ^ 2 * smoothedEnergy c ξ Φ (normalizedWeight J W) H L F := by
  by_cases hzero : weightNorm J W = 0
  · rw [smoothedEnergy_eq_zero_of_weightNorm_eq_zero hW J hzero c ξ Φ H L F, hzero]
    simp
  · have h := (eq_div_iff (pow_ne_zero 2 hzero)).mp
      (smoothedEnergy_normalizedWeight hW J c ξ Φ H L F)
    simpa only [mul_comm] using h.symm

end QRHShort
