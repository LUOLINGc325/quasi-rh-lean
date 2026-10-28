import QRHShort.FirstTransferPoissonPreMobiusFrequencies

/-! Exact scalar normalization of each finite ray-expanded Poisson summand.
The only identity passed to the helper is the already proved pointwise ray
expansion at this same frequency; the energy theorem supplies it uniformly. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort
open FirstTransferRayFourier

theorem first_transfer_preMobius_normalize_ray_expansion
    (c : ArithmeticContext) (Φ : RowWeight) (W : ℝ → ℂ) {L F : ℝ}
    (hL : 0 < L) (hF : 0 < F) (H : ℝ) {C d a b : Ideal O}
    (hC : C ≠ ⊥) (hd : d ≠ ⊥) (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (f : Ideal O) (h : O) (l : RayFourierIndex c → ℂ) (A : ℂ)
    (hA : A = firstTransferOffDiagonalLead C f *
      W (normIdeal (C * a) / L) * star (W (normIdeal (C * b) / L)) *
      ∑ ψ : RayFourierIndex c, l ψ *
        (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
          (h * primaryGenerator f ^ 2) a *
          star (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
            (h * primaryGenerator f ^ 2) b))) :
    (mobius d : ℂ) *
      ((((L * F)⁻¹ : ℝ) : ℂ) * (H : ℂ) /
        (Real.sqrt (normIdeal (a * b)) : ℂ) / (normIdeal d : ℂ)) * A *
      radialFourier (fun x => (Φ.value x : ℂ))
        (H * normElement h / (normIdeal d * normIdeal (a * b))) =
      ∑ ψ : RayFourierIndex c, l ψ *
        firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h (a, b) := by
  have hn := first_transfer_poisson_kernel_normalization_ideals Φ W hC
    (show (1 : Ideal O) ≠ ⊥ by simp) hd ha hb hL hF H (normElement h)
  have hone : normIdeal (1 : Ideal O) = 1 := by simp [normIdeal]
  simp only [one_mul, hone, mul_one] at hn
  rw [hA, first_transfer_preMobius_weight_argument hC,
    first_transfer_preMobius_weight_argument hC]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ψ _
  calc
    _ = l ψ * (mobius d : ℂ) * firstTransferOffDiagonalLead C f *
        (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
          (h * primaryGenerator f ^ 2) a *
          star (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
            (h * primaryGenerator f ^ 2) b)) *
        (((((L * F)⁻¹ : ℝ) : ℂ) * (H : ℂ) /
          (Real.sqrt (normIdeal (a * b)) : ℂ) / (normIdeal d : ℂ) *
          W (normIdeal a / (L / normIdeal C)) * star (W (normIdeal b / (L / normIdeal C)))) *
          radialFourier (fun x => (Φ.value x : ℂ))
            (H * normElement h / (normIdeal d * normIdeal (a * b)))) := by ring
    _ = _ := by
      rw [hn]
      simp only [firstTransferPreMobiusKernelTerm, firstTransferOffDiagonalPairKernel]
      ring

end QRHShort
