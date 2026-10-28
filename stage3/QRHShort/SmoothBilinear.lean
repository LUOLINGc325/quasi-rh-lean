import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The finite-row and integral inequalities in `lem:smooth-mean-square`.
The common coefficient majorant is taken before integrating; none of these
bounds introduces a factor depending on the number of rows. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QRHShort

theorem weighted_norm_pairing_le_sqrt {ρ : Type*} [Fintype ρ]
    (w : ρ → ℝ) (u v : ρ → ℂ) (hw : ∀ r, 0 ≤ w r)
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hu : (∑ r, w r * ‖u r‖ ^ 2) ≤ M₁)
    (hv : (∑ r, w r * ‖v r‖ ^ 2) ≤ M₂) :
    (∑ r, w r * ‖u r‖ * ‖v r‖) ≤ Real.sqrt (M₁ * M₂) := by
  classical
  have hS : 0 ≤ ∑ r, w r * ‖u r‖ * ‖v r‖ :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (mul_nonneg (hw r) (norm_nonneg _))
      (norm_nonneg _))
  apply (sq_le_sq₀ hS (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (mul_nonneg hM₁ hM₂)]
  calc
    (∑ r, w r * ‖u r‖ * ‖v r‖) ^ 2 ≤
        (∑ r, w r * ‖u r‖ ^ 2) * ∑ r, w r * ‖v r‖ ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun r _ => mul_nonneg (hw r) (sq_nonneg _))
        (fun r _ => mul_nonneg (hw r) (sq_nonneg _))
        (fun r _ => le_of_eq (by ring))
    _ ≤ M₁ * M₂ := mul_le_mul hu hv
      (Finset.sum_nonneg (fun r _ => mul_nonneg (hw r) (sq_nonneg _))) hM₁

theorem weighted_bilinear_common_majorant {ρ : Type*} [Fintype ρ]
    (w : ρ → ℝ) (c b u v : ρ → ℂ) {B M₁ M₂ : ℝ}
    (hw : ∀ r, 0 ≤ w r) (hc : ∀ r, ‖c r‖ ≤ w r)
    (hB : 0 ≤ B) (hb : ∀ r, ‖b r‖ ≤ B)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hu : (∑ r, w r * ‖u r‖ ^ 2) ≤ M₁)
    (hv : (∑ r, w r * ‖v r‖ ^ 2) ≤ M₂) :
    ‖∑ r, c r * b r * u r * star (v r)‖ ≤ B * Real.sqrt (M₁ * M₂) := by
  classical
  calc
    _ ≤ ∑ r, ‖c r * b r * u r * star (v r)‖ := norm_sum_le _ _
    _ ≤ ∑ r, B * (w r * ‖u r‖ * ‖v r‖) := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, norm_mul, norm_mul, norm_star]
      calc
        ‖c r‖ * ‖b r‖ * ‖u r‖ * ‖v r‖ ≤
            w r * B * ‖u r‖ * ‖v r‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul (hc r) (hb r) (norm_nonneg _) (hw r))
              (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    _ = B * ∑ r, w r * ‖u r‖ * ‖v r‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ B * Real.sqrt (M₁ * M₂) := mul_le_mul_of_nonneg_left
      (weighted_norm_pairing_le_sqrt w u v hw hM₁ hM₂ hu hv) hB

/-- A single integrable coefficient envelope controls every finite row family. -/
theorem weighted_bilinear_integral_common_majorant
    {α ρ : Type*} [MeasurableSpace α] [Fintype ρ] {μ : Measure α}
    (w : ρ → ℝ) (c : ρ → ℂ) (b u v : ρ → α → ℂ)
    (B p q : α → ℝ) {M₁ M₂ : ℝ}
    (hw : ∀ r, 0 ≤ w r) (hc : ∀ r, ‖c r‖ ≤ w r)
    (hB : ∀ x, 0 ≤ B x) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hb : ∀ r x, ‖b r x‖ ≤ B x) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hu : ∀ x, (∑ r, w r * ‖u r x‖ ^ 2) ≤ M₁ * p x ^ 2)
    (hv : ∀ x, (∑ r, w r * ‖v r x‖ ^ 2) ≤ M₂ * q x ^ 2)
    (hprod : ∀ r, Integrable (fun x => c r * b r x * u r x * star (v r x)) μ)
    (hmass : Integrable (fun x => B x * p x * q x) μ) :
    ‖∑ r, ∫ x, c r * b r x * u r x * star (v r x) ∂μ‖ ≤
      Real.sqrt (M₁ * M₂) * ∫ x, B x * p x * q x ∂μ := by
  classical
  have hpoint (x : α) :
      ‖∑ r, c r * b r x * u r x * star (v r x)‖ ≤
        Real.sqrt (M₁ * M₂) * (B x * p x * q x) := by
    have ht := weighted_bilinear_common_majorant w c (fun r => b r x)
      (fun r => u r x) (fun r => v r x) hw hc (hB x) (fun r => hb r x)
      (mul_nonneg hM₁ (sq_nonneg _)) (mul_nonneg hM₂ (sq_nonneg _)) (hu x) (hv x)
    have hs : Real.sqrt ((M₁ * p x ^ 2) * (M₂ * q x ^ 2)) =
        Real.sqrt (M₁ * M₂) * p x * q x := by
      rw [show (M₁ * p x ^ 2) * (M₂ * q x ^ 2) =
        (M₁ * M₂) * (p x * q x) ^ 2 by ring,
        Real.sqrt_mul (mul_nonneg hM₁ hM₂), Real.sqrt_sq (mul_nonneg (hp x) (hq x))]
      ring
    rw [hs] at ht
    convert ht using 1 <;> ring
  rw [← integral_finsetSum _ (fun r _ => hprod r)]
  calc
    _ ≤ ∫ x, Real.sqrt (M₁ * M₂) * (B x * p x * q x) ∂μ :=
      norm_integral_le_of_norm_le (hmass.const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

end QRHShort

#print axioms QRHShort.weighted_norm_pairing_le_sqrt
#print axioms QRHShort.weighted_bilinear_common_majorant
#print axioms QRHShort.weighted_bilinear_integral_common_majorant
