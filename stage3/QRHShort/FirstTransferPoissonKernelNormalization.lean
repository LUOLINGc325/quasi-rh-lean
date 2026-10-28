import QRHShort.FirstTransferReduction
import Mathlib.Tactic.FieldSimp

/-! Exact scalar normalization of the literal kernel after Poisson summation.
The square-root and Fourier-argument identities precede the coupled identity. -/

noncomputable section

open Classical

namespace QRHShort

theorem first_transfer_poisson_kernel_argument {NC NT Nd L x₁ x₂ : ℝ}
    (hNC : 0 < NC) (hNT : 0 < NT) (hNd : 0 < Nd) (hL : 0 < L)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (H v : ℝ) :
    H * v / (Nd * ((NT * x₁) * (NT * x₂))) =
      (H * v * NC ^ 2 / (L ^ 2 * Nd)) /
        ((x₁ / (L / (NC * NT))) * (x₂ / (L / (NC * NT)))) := by
  field_simp

theorem first_transfer_poisson_kernel_prefactor {NC NT Nd L F x₁ x₂ : ℝ}
    (hNC : 0 < NC) (hNT : 0 < NT) (hNd : 0 < Nd) (hL : 0 < L) (hF : 0 < F)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (H : ℝ) :
    (((L * F)⁻¹ : ℝ) : ℂ) * (H : ℂ) /
        (Real.sqrt ((NT * x₁) * (NT * x₂)) : ℂ) / (Nd : ℂ) =
      ((H * NC / (Nd * L ^ 2 * F) : ℝ) : ℂ) *
        (Real.sqrt ((x₁ / (L / (NC * NT))) * (x₂ / (L / (NC * NT)))) : ℂ)⁻¹ := by
  let ell : ℝ := L / (NC * NT)
  have hell : 0 < ell := div_pos hL (mul_pos hNC hNT)
  have hs : 0 < Real.sqrt (x₁ * x₂) := Real.sqrt_pos.mpr (mul_pos hx₁ hx₂)
  have hroot₁ : Real.sqrt ((NT * x₁) * (NT * x₂)) =
      NT * Real.sqrt (x₁ * x₂) := by
    rw [show (NT * x₁) * (NT * x₂) = NT ^ 2 * (x₁ * x₂) by ring,
      Real.sqrt_mul (sq_nonneg NT), Real.sqrt_sq hNT.le]
  have hroot₂ : Real.sqrt ((x₁ / ell) * (x₂ / ell)) =
      Real.sqrt (x₁ * x₂) / ell := by
    rw [show (x₁ / ell) * (x₂ / ell) = (x₁ * x₂) / ell ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hx₁.le hx₂.le), Real.sqrt_sq hell.le]
  have hreal : (L * F)⁻¹ * H / Real.sqrt ((NT * x₁) * (NT * x₂)) / Nd =
      (H * NC / (Nd * L ^ 2 * F)) * (Real.sqrt ((x₁ / ell) * (x₂ / ell)))⁻¹ := by
    rw [hroot₁, hroot₂]
    dsimp only [ell]
    field_simp
  exact_mod_cast hreal

theorem first_transfer_poisson_kernel_normalization (Φ : RowWeight) (W : ℝ → ℂ)
    {NC NT Nd L F x₁ x₂ : ℝ}
    (hNC : 0 < NC) (hNT : 0 < NT) (hNd : 0 < Nd) (hL : 0 < L) (hF : 0 < F)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (H v : ℝ) :
    (((L * F)⁻¹ : ℝ) : ℂ) * (H : ℂ) /
        (Real.sqrt ((NT * x₁) * (NT * x₂)) : ℂ) / (Nd : ℂ) *
        W (x₁ / (L / (NC * NT))) * star (W (x₂ / (L / (NC * NT)))) *
        radialFourier (fun x => (Φ.value x : ℂ))
          (H * v / (Nd * ((NT * x₁) * (NT * x₂)))) =
      ((H * NC / (Nd * L ^ 2 * F) : ℝ) : ℂ) *
        firstTransferKernel Φ W (H * v * NC ^ 2 / (L ^ 2 * Nd))
          ![x₁ / (L / (NC * NT)), x₂ / (L / (NC * NT))] := by
  simp only [firstTransferKernel, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [first_transfer_poisson_kernel_argument hNC hNT hNd hL hx₁ hx₂,
    first_transfer_poisson_kernel_prefactor hNC hNT hNd hL hF hx₁ hx₂]
  ring

end QRHShort
