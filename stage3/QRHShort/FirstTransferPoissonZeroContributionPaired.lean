import QRHShort.FirstTransferPoissonZeroContribution
import QRHShort.FirstTransferPairedCharacterPrimitivity

/-! For the primitive paired row, zero frequency is supported only at the
pair of unit denominator ideals. -/

noncomputable section

open Classical

namespace QRHShort

theorem first_transfer_paired_character_eq_one_iff (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    (firstTransferPrimitivePairedCharacter c ha hb hab).character = 1 ↔
      a = ⊤ ∧ b = ⊤ := by
  rw [first_transfer_primitive_character_eq_one_iff,
    firstTransferPrimitivePairedCharacter_modulus]
  constructor
  · intro h
    exact ⟨top_unique (h ▸ (show a * b ≤ a from Ideal.mul_le_left)),
      top_unique (h ▸ (show a * b ≤ b from Ideal.mul_le_right))⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem first_transfer_paired_poissonZeroTerm_eq_zero (hz : PoissonZeroStatement)
    (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hpair : ¬ (a = ⊤ ∧ b = ⊤))
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) :
    poissonZeroTerm (firstTransferPrimitivePairedCharacter c ha hb hab) r Φ H = 0 := by
  apply first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal hz
  exact mt (first_transfer_paired_character_eq_one_iff c ha hb hab).mp hpair

theorem first_transfer_paired_poissonZeroTerm_ne_zero_imp (hz : PoissonZeroStatement)
    (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ)
    (hterm : poissonZeroTerm (firstTransferPrimitivePairedCharacter c ha hb hab) r Φ H ≠ 0) :
    a = ⊤ ∧ b = ⊤ := by
  by_contra hpair
  exact hterm (first_transfer_paired_poissonZeroTerm_eq_zero hz c ha hb hab hpair r Φ H)

theorem first_transfer_paired_poissonZeroTerm_norm_le_indicator
    (hz : PoissonZeroStatement) (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (r : Ideal O) (hr : r ≠ ⊥)
    (Φ : RowWeight) (H : ℝ) (hH : 0 < H) :
    ‖poissonZeroTerm (firstTransferPrimitivePairedCharacter c ha hb hab)
      r (fun x => (Φ.value x : ℂ)) H‖ ≤
      if a = ⊤ ∧ b = ⊤ then
        H * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ else 0 := by
  by_cases hpair : a = ⊤ ∧ b = ⊤
  · rw [ite_eq_left hpair]
    exact first_transfer_poissonZeroTerm_norm_le hz _ r hr Φ H hH
  · rw [ite_eq_right hpair,
      first_transfer_paired_poissonZeroTerm_eq_zero hz c ha hb hab hpair, norm_zero]

end QRHShort
