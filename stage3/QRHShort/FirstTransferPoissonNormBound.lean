import QRHShort.FirstTransferRayFamilyFinite

/-! Local norm consequences of an explicitly supplied concrete energy
identity.  These lemmas do not assert that the Poisson/Gauss assembly identity
holds; its proof remains a separate obligation for every application. -/

noncomputable section

open Classical
open scoped BigOperators

namespace QRHShort

theorem first_transfer_finite_ray_bilinear_norm_le {R : Type*} [Fintype R]
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (η : R → RayCharacter c) (l : R → ℂ) (W : ℝ → ℂ) (H L F B : ℝ)
    (hl : (∑ r : R, ‖l r‖) ≤ B) :
    ‖∑ r : R, l r * firstTransferBilinear c I Φ (η r) W H L F‖ ≤
      B * QRHLean3.supZero {v : ℝ | ∃ ξ : RayCharacter c,
        v = ‖firstTransferBilinear c I Φ ξ W H L F‖} := by
  let S : ℝ := QRHLean3.supZero {v : ℝ | ∃ ξ : RayCharacter c,
    v = ‖firstTransferBilinear c I Φ ξ W H L F‖}
  have hS : 0 ≤ S := first_transfer_bilinear_supZero_nonneg c I Φ W H L F
  calc
    ‖∑ r : R, l r * firstTransferBilinear c I Φ (η r) W H L F‖ ≤
        ∑ r : R, ‖l r * firstTransferBilinear c I Φ (η r) W H L F‖ :=
      norm_sum_le _ _
    _ = ∑ r : R, ‖l r‖ * ‖firstTransferBilinear c I Φ (η r) W H L F‖ := by
      simp only [norm_mul]
    _ ≤ ∑ r : R, ‖l r‖ * S := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (first_transfer_bilinear_norm_le_supZero c I Φ (η r) W H L F) (norm_nonneg _)
    _ = (∑ r : R, ‖l r‖) * S := (Finset.sum_mul _ _ _).symm
    _ ≤ B * S := mul_le_mul_of_nonneg_right hl hS

theorem first_transfer_poisson_norm_bound_additive {R : Type*} [Fintype R]
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (ξ : RayCharacter c) (η : R → RayCharacter c) (l : R → ℂ)
    (W : ℝ → ℂ) (H L F B Kz : ℝ) (Z : ℂ)
    (hl : (∑ r : R, ‖l r‖) ≤ B)
    (hZ : ‖Z‖ ≤ Kz * H * weightNorm 0 W ^ 2)
    (heq : (smoothedEnergy c ξ Φ.value W H L F : ℂ) =
      Z + ∑ r : R, l r * firstTransferBilinear c I Φ (η r) W H L F) :
    smoothedEnergy c ξ Φ.value W H L F ≤
      Kz * (H * weightNorm 0 W ^ 2) +
        B * QRHLean3.supZero {v : ℝ | ∃ ξ₁ : RayCharacter c,
          v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖} := by
  have hreal : smoothedEnergy c ξ Φ.value W H L F ≤
      ‖(smoothedEnergy c ξ Φ.value W H L F : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      le_abs_self (smoothedEnergy c ξ Φ.value W H L F)
  calc
    smoothedEnergy c ξ Φ.value W H L F ≤
        ‖(smoothedEnergy c ξ Φ.value W H L F : ℂ)‖ := hreal
    _ = ‖Z + ∑ r : R, l r * firstTransferBilinear c I Φ (η r) W H L F‖ :=
      congrArg norm heq
    _ ≤ ‖Z‖ + ‖∑ r : R, l r * firstTransferBilinear c I Φ (η r) W H L F‖ :=
      norm_add_le _ _
    _ ≤ Kz * H * weightNorm 0 W ^ 2 +
        B * QRHLean3.supZero {v : ℝ | ∃ ξ₁ : RayCharacter c,
          v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖} :=
      add_le_add hZ (first_transfer_finite_ray_bilinear_norm_le c I Φ η l W H L F B hl)
    _ = _ := by ring

theorem first_transfer_poisson_norm_bound {R : Type*} [Fintype R]
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (ξ : RayCharacter c) (η : R → RayCharacter c) (l : R → ℂ)
    (W : ℝ → ℂ) (H L F B Kz : ℝ) (Z : ℂ)
    (_hB : 0 ≤ B) (_hKz : 0 ≤ Kz) (hH : 0 ≤ H)
    (hl : (∑ r : R, ‖l r‖) ≤ B)
    (hZ : ‖Z‖ ≤ Kz * H * weightNorm 0 W ^ 2)
    (heq : (smoothedEnergy c ξ Φ.value W H L F : ℂ) =
      Z + ∑ r : R, l r * firstTransferBilinear c I Φ (η r) W H L F) :
    smoothedEnergy c ξ Φ.value W H L F ≤
      max Kz B * (H * weightNorm 0 W ^ 2 +
        QRHLean3.supZero {v : ℝ | ∃ ξ₁ : RayCharacter c,
          v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖}) := by
  have hX : 0 ≤ H * weightNorm 0 W ^ 2 := mul_nonneg hH (sq_nonneg _)
  have hS := first_transfer_bilinear_supZero_nonneg c I Φ W H L F
  calc
    smoothedEnergy c ξ Φ.value W H L F ≤
        Kz * (H * weightNorm 0 W ^ 2) +
          B * QRHLean3.supZero {v : ℝ | ∃ ξ₁ : RayCharacter c,
            v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖} :=
      first_transfer_poisson_norm_bound_additive c I Φ ξ η l W H L F B Kz Z hl hZ heq
    _ ≤ max Kz B * (H * weightNorm 0 W ^ 2) +
        max Kz B * QRHLean3.supZero {v : ℝ | ∃ ξ₁ : RayCharacter c,
          v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖} :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hS)
    _ = _ := by ring

end QRHShort
