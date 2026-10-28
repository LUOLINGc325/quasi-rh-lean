import QRHShort.FirstTransferPoissonEnergyExpansion
import QRHShort.FirstTransferGcdReindex

/-! Reindex the actual expanded smoothed energy by its ideal gcd. The
restricted pair series is finitely supported, and the proved equivalence
transfers its summability to the literal three-ideal expression. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def firstTransferPoissonEnergyGcdTerm (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (H L : ℝ) (f : Ideal O)
    (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if firstTransferGcdTripleAdmissible c t then
    firstTransferPoissonEnergyCoefficient c ξ W L f (t.1 * t.2.1) *
      star (firstTransferPoissonEnergyCoefficient c ξ W L f (t.1 * t.2.2)) *
        ∑' k : O, firstTransferPoissonEnergyCharacterRow Φ H (t.1 * t.2.1) (t.1 * t.2.2) k
  else 0

theorem first_transfer_poisson_energy_gcd_row (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (H : ℝ) {L : ℝ} (hL : 0 < L) (f : Ideal O) :
    Summable (firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f) ∧
      (∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
        firstTransferPoissonEnergyCoefficient c ξ W L f n₁ *
          star (firstTransferPoissonEnergyCoefficient c ξ W L f n₂) *
            ∑' k : O, firstTransferPoissonEnergyCharacterRow Φ H n₁ n₂ k) =
        ∑' t : Ideal O × Ideal O × Ideal O, firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f t := by
  let g : Ideal O × Ideal O → ℂ := fun p =>
    firstTransferPoissonEnergyCoefficient c ξ W L f p.1 *
      star (firstTransferPoissonEnergyCoefficient c ξ W L f p.2) *
        ∑' k : O, firstTransferPoissonEnergyCharacterRow Φ H p.1 p.2 k
  have hfinite : Function.HasFiniteSupport g := by
    apply ((firstTransferIdealWindow I L).finite_toSet.prod
      (firstTransferIdealWindow I L).finite_toSet).subset
    intro p hp
    constructor
    · apply first_transfer_poisson_energy_coefficient_support c ξ hW hL f
      intro hz
      exact hp (by simp only [g, hz, zero_mul])
    · apply first_transfer_poisson_energy_coefficient_support c ξ hW hL f
      intro hz
      exact hp (by simp only [g, hz, star_zero, mul_zero, zero_mul])
  have hrestrict : (fun p : Ideal O × Ideal O =>
      if firstTransferGcdPairAdmissible c p then g p else 0) = g := by
    funext p
    by_cases ha : SquarefreeOutside c.S p.1
    · by_cases hb : SquarefreeOutside c.S p.2
      · rw [if_pos (show firstTransferGcdPairAdmissible c p from ⟨ha, hb⟩)]
      · simp only [firstTransferGcdPairAdmissible, ha, hb, and_false, if_false,
          g, firstTransferPoissonEnergyCoefficient, if_neg hb, star_zero, mul_zero, zero_mul]
    · simp only [firstTransferGcdPairAdmissible, ha, false_and, if_false,
        g, firstTransferPoissonEnergyCoefficient, if_neg ha, zero_mul]
  have hs : Summable g := summable_of_hasFiniteSupport hfinite
  have hrestricted : Summable (fun p => if firstTransferGcdPairAdmissible c p then g p else 0) := by
    rw [hrestrict]
    exact hs
  obtain ⟨ht, heq⟩ := first_transfer_gcd_indicator_reindex c g hrestricted
  refine ⟨ht, ?_⟩
  rw [hrestrict] at heq
  exact hs.tsum_prod.symm.trans heq

theorem first_transfer_poisson_energy_gcd_expansion (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) :
    (smoothedEnergy c ξ Φ.value W H L F : ℂ) =
      (((L * F)⁻¹ : ℝ) : ℂ) * ∑' f : Ideal O,
        if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
          ∑' t : Ideal O × Ideal O × Ideal O, firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f t
        else 0 := by
  rw [first_transfer_poisson_energy_expansion c ξ Φ hW hH hL hF]
  congr 1
  apply tsum_congr
  intro f
  by_cases hf : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F
  · rw [if_pos hf, if_pos hf]
    exact (first_transfer_poisson_energy_gcd_row c ξ Φ hW H hL f).2
  · rw [if_neg hf, if_neg hf]

end QRHShort
