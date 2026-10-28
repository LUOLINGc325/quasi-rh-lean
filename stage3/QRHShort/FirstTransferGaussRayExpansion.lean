import QRHShort.FirstTransferGaussCoefficient
import QRHShort.FirstTransferRayFourierInput

/-! Finite ray expansion of the explicitly simplified paired Gauss factor.
The remaining CRT theorem must identify that factor with the actual paired
Gauss sum; this file does not assume such an identification. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort
open FirstTransferRayFourier

theorem first_transfer_gauss_factor_uniform_ray_expansion
    (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : RayCharacter c,
      ∃ l : RayFourierIndex c → ℂ,
        (∑ ψ : RayFourierIndex c, ‖l ψ‖) ≤ B ∧
        ∀ a b : Ideal O, SquarefreeOutside c.S a → SquarefreeOutside c.S b →
          IsRelPrime a b →
          coefficient ξ.val a * star (coefficient ξ.val b) * firstTransferPairedGaussFactor a b =
            ∑ ψ : RayFourierIndex c, l ψ *
              ((mobius a : ℂ) * (mobius b : ℂ) *
                rayValue (rayFourierCharacter c ψ).val a *
                  star (rayValue (rayFourierCharacter c ψ).val b)) := by
  obtain ⟨B, hB, hexp⟩ := exists_uniform_twisted_ray_expansion c
  refine ⟨B, hB, ?_⟩
  intro ξ
  have hG : ∀ z, ‖reciprocityG c hc z‖ ≤ 1 := by
    obtain ⟨R, hG, _⟩ := Classical.choose_spec hc
    exact fun z => (hG z).le
  obtain ⟨l, hl, hidentity⟩ := hexp ξ (reciprocityG c hc) hG
  refine ⟨l, hl, ?_⟩
  intro a b ha hb hab
  calc
    _ = ((mobius a : ℂ) * (mobius b : ℂ)) *
        (rayValue ξ.val a * star (rayValue ξ.val b) *
          reciprocityG c hc (idealClass c a * (idealClass c b)⁻¹)) := by
      rw [first_transfer_coefficient_pairedGaussFactor c hc ξ ha hb hab]
      ring
    _ = ((mobius a : ℂ) * (mobius b : ℂ)) *
        ∑ ψ : RayFourierIndex c, l ψ * rayValue (rayFourierCharacter c ψ).val a *
          star (rayValue (rayFourierCharacter c ψ).val b) := by
      rw [hidentity a b ha.1 hb.1]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ _
      ring

end QRHShort
