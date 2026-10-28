import QRHShort.FirstTransferGaussRayExpansion
import QRHShort.FirstTransferGaussCRT

/-! The finite ray expansion of the actual primitive paired Gauss sum,
with one coefficient bound chosen before the original ray character. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort
open FirstTransferRayFourier

theorem first_transfer_primitive_paired_gauss_uniform_ray_expansion
    (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : RayCharacter c,
      ∃ l : RayFourierIndex c → ℂ,
        (∑ ψ : RayFourierIndex c, ‖l ψ‖) ≤ B ∧
        ∀ (a b : Ideal O) (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
          (hab : IsRelPrime a b),
          coefficient ξ.val a * star (coefficient ξ.val b) *
            (firstTransferPrimitivePairedCharacter c ha hb hab).gauss =
              ∑ ψ : RayFourierIndex c, l ψ *
                ((mobius a : ℂ) * (mobius b : ℂ) *
                  rayValue (rayFourierCharacter c ψ).val a *
                    star (rayValue (rayFourierCharacter c ψ).val b)) := by
  obtain ⟨B, hB, hexp⟩ := first_transfer_gauss_factor_uniform_ray_expansion c hc
  refine ⟨B, hB, ?_⟩
  intro ξ
  obtain ⟨l, hl, hidentity⟩ := hexp ξ
  refine ⟨l, hl, ?_⟩
  intro a b ha hb hab
  rw [first_transfer_primitive_paired_gauss_crt c ha hb hab]
  exact hidentity a b ha hb hab

end QRHShort
