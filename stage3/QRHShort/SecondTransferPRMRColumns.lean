import QRHShort.SecondTransferReduction
import QRHShort.PrimeComparison
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def secondTransferPRMRColumn (c : ArithmeticContext) (z : SecondTransferIndex c)
    (n : Ideal O) : ℂ :=
  if SquarefreeOutside c.S n ∧ IsRelPrime n z.excluded then
    coefficient z.character.val n * sexticSymbol n z.frequency *
      sexticSymbol n (primaryGenerator z.twist) ^ (4 : ℕ)
  else 0

def secondTransferPRMRColumns (I : SupportInterval) (L : ℝ) : Finset (Ideal O) :=
  boundedDivisibleIdeals 1 ((enlarged I).hi * L)

theorem second_transfer_prmr_columnScale_bounds {c : ArithmeticContext}
    (z : SecondTransferIndex c) {L : ℝ} (hL : 0 < L) :
    0 < z.columnScale L ∧ z.columnScale L ≤ L := by
  have hp : 0 < (2 : ℝ) ^ z.rBlock * (2 : ℝ) ^ z.fBlock := by positivity
  have hone : 1 ≤ (2 : ℝ) ^ z.rBlock * (2 : ℝ) ^ z.fBlock :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by norm_num))
  exact ⟨div_pos hL hp, div_le_self hL.le hone⟩

theorem second_transfer_prmr_column_support {c : ArithmeticContext}
    (I : SupportInterval) (z : SecondTransferIndex c) {L : ℝ} (hL : 0 < L)
    {V : ℝ → ℂ} (hV : SmoothSupported (enlarged I) V) :
    Function.support (fun n => secondTransferPRMRColumn c z n *
      V (normIdeal n / z.columnScale L)) ⊆
        (secondTransferPRMRColumns I L : Set (Ideal O)) := by
  intro n hn
  have hc : secondTransferPRMRColumn c z n ≠ 0 := (mul_ne_zero_iff.mp hn).1
  have hv : V (normIdeal n / z.columnScale L) ≠ 0 := (mul_ne_zero_iff.mp hn).2
  have hs : SquarefreeOutside c.S n ∧ IsRelPrime n z.excluded := by
    by_contra h
    exact hc (by simp only [secondTransferPRMRColumn, if_neg h])
  have hx := (hV.2 hv).2
  have hscale := second_transfer_prmr_columnScale_bounds z hL
  apply mem_boundedDivisibleIdeals.mpr
  exact ⟨((div_le_iff₀ hscale.1).mp hx).trans
    (mul_le_mul_of_nonneg_left hscale.2
      ((enlarged I).lo_pos.le.trans (enlarged I).ordered)), one_dvd _, hs.1.1.1⟩

theorem second_transfer_prmr_column_hasFiniteSupport {c : ArithmeticContext}
    (I : SupportInterval) (z : SecondTransferIndex c) {L : ℝ} (hL : 0 < L)
    {V : ℝ → ℂ} (hV : SmoothSupported (enlarged I) V) :
    Function.HasFiniteSupport (fun n => secondTransferPRMRColumn c z n *
      V (normIdeal n / z.columnScale L)) :=
  (secondTransferPRMRColumns I L).finite_toSet.subset
    (second_transfer_prmr_column_support I z hL hV)

theorem second_transfer_prmr_column_complete {c : ArithmeticContext}
    (I : SupportInterval) (z : SecondTransferIndex c) {L : ℝ} (hL : 0 < L)
    {V : ℝ → ℂ} (hV : SmoothSupported (enlarged I) V) :
    (∑ n : Fin (secondTransferPRMRColumns I L).card,
      secondTransferPRMRColumn c z ((secondTransferPRMRColumns I L).equivFin.symm n) *
        V (normIdeal ((secondTransferPRMRColumns I L).equivFin.symm n) /
          z.columnScale L)) =
      excludedColumnSum c z.character V z.excluded (z.columnScale L)
        z.frequency z.twist := by
  let s := secondTransferPRMRColumns I L
  have hsum : (∑' n : Ideal O, secondTransferPRMRColumn c z n *
      V (normIdeal n / z.columnScale L)) =
      ∑ n : Fin s.card, secondTransferPRMRColumn c z (s.equivFin.symm n) *
        V (normIdeal (s.equivFin.symm n) / z.columnScale L) := by
    rw [← tsum_subtype_eq_of_support_subset
      (second_transfer_prmr_column_support I z hL hV), tsum_fintype]
    exact (s.equivFin.symm.sum_comp _).symm
  rw [← hsum]
  unfold excludedColumnSum
  apply tsum_congr
  intro n
  simp only [secondTransferPRMRColumn, ite_mul, zero_mul]

end QRHShort
