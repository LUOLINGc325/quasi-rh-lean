import QRHShort.FirstTransferGaussCRTReindex
import QRHShort.FirstTransferLatticeAdditive

/-!
The literal additive phase is well-defined on each outside quotient and
splits under the opposite-generator CRT representatives.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The additive factor appearing in the frozen ideal Gauss sums. -/
def firstTransferGaussPhase (n : Ideal O) (x : O ⧸ n) : ℂ :=
  additiveCharacter (embedding (residueLift n x) / embedding (primaryGenerator n))

theorem first_transfer_gauss_phase_apply_mk (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O) :
    firstTransferGaussPhase n (Ideal.Quotient.mk n x) =
      additiveCharacter (embedding x / embedding (primaryGenerator n)) := by
  have hgen := (first_transfer_primaryGenerator_spec_and_primary_outside c hn).1
  have hne : primaryGenerator n ≠ 0 := by
    intro h
    apply hn.1
    rw [← hgen, h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  apply first_transfer_gauss_additive_div_congr hne
  rw [hgen]
  exact firstTransferResidueLift_spec n _

theorem first_transfer_gauss_phase_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (u v : O) :
    firstTransferGaussPhase (a * b) (Ideal.Quotient.mk (a * b)
      (primaryGenerator b * u + primaryGenerator a * v)) =
      additiveCharacter (embedding u / embedding (primaryGenerator a)) *
        additiveCharacter (embedding v / embedding (primaryGenerator b)) := by
  have hab := (first_transfer_outside_mul_iff c a b).mpr ⟨ha, hb⟩
  have hne (n : Ideal O) (hn : Outside c.S n) : embedding (primaryGenerator n) ≠ 0 := by
    intro h
    apply hn.1
    rw [← (first_transfer_primaryGenerator_spec_and_primary_outside c hn).1,
      embedding_eq_zero.mp h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  rw [first_transfer_gauss_phase_apply_mk c hab,
    first_transfer_primaryGenerator_mul_outside c ha hb,
    embedding_add, embedding_mul, embedding_mul, embedding_mul]
  have harg :
      (embedding (primaryGenerator b) * embedding u +
        embedding (primaryGenerator a) * embedding v) /
        (embedding (primaryGenerator a) * embedding (primaryGenerator b)) =
      embedding u / embedding (primaryGenerator a) +
        embedding v / embedding (primaryGenerator b) := by
    field_simp [hne a ha, hne b hb]
  rw [harg, first_transfer_additiveCharacter_add]

/-- Exact factorization before normalizing, valid also for unit-ideal
quotients and for any chosen finite enumerations of the quotients. -/
theorem first_transfer_paired_gauss_crt_sum (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    [Fintype (O ⧸ a)] [Fintype (O ⧸ b)] [Fintype (O ⧸ (a * b))] :
    (∑ x : O ⧸ (a * b), firstTransferPairedResidueCharacter c ha hb hab x *
      firstTransferGaussPhase (a * b) x) =
      (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) *
        (∑ u : O ⧸ a, sexticSymbol a (residueLift a u) * firstTransferGaussPhase a u) *
        (∑ v : O ⧸ b, star (sexticSymbol b (residueLift b v)) * firstTransferGaussPhase b v) := by
  rw [first_transfer_gauss_crt_reindex a b
    (first_transfer_ideal_isCoprime_of_isRelPrime hab)
    (primaryGenerator a) (primaryGenerator b)
    (first_transfer_primaryGenerator_spec_and_primary_outside c ha).1
    (first_transfer_primaryGenerator_spec_and_primary_outside c hb).1]
  simp_rw [first_transfer_gauss_crt_paired_value c ha hb hab,
    first_transfer_gauss_phase_crt c ha hb]
  simp only [firstTransferGaussPhase, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

end QRHShort
