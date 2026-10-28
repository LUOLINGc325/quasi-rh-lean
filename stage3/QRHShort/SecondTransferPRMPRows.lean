import QRHShort.SecondTransferReduction
import QRHShort.SecondTransferPRMPHarmonic

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def secondTransferPRMPRadius (I : SupportInterval) (L : ℝ) : ℝ := max 1 (2 * I.hi * L)
def secondTransferPRMPBox (I : SupportInterval) (L : ℝ) : Finset (Ideal O) :=
  boundedDivisibleIdeals 1 (secondTransferPRMPRadius I L)
def secondTransferPRMPAdmissible (c : ArithmeticContext) (I : SupportInterval)
    (L : ℝ) (C t : Ideal O) : Prop :=
  SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
    normIdeal C * normIdeal t ≤ 2 * I.hi * L

theorem second_transfer_prmp_one_le_norm {n : Ideal O} (hn : n ≠ ⊥) :
    1 ≤ normIdeal n := by
  have h : 1 ≤ n.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h => hn (Ideal.absNorm_eq_zero_iff.mp h))
  change (1 : ℝ) ≤ (n.absNorm : ℝ)
  exact_mod_cast h

theorem second_transfer_prmp_admissible_mem (c : ArithmeticContext) (I : SupportInterval)
    {L : ℝ} {C t : Ideal O} (h : secondTransferPRMPAdmissible c I L C t) :
    C ∈ secondTransferPRMPBox I L ∧ t ∈ secondTransferPRMPBox I L := by
  have hC := second_transfer_prmp_one_le_norm h.1.1.1
  have ht := second_transfer_prmp_one_le_norm h.2.1.1.1
  constructor
  · apply mem_boundedDivisibleIdeals.mpr
    exact ⟨((le_mul_of_one_le_right (zero_le_one.trans hC) ht).trans h.2.2.2).trans
      (le_max_right _ _), one_dvd _, h.1.1.1⟩
  · apply mem_boundedDivisibleIdeals.mpr
    exact ⟨((le_mul_of_one_le_left (zero_le_one.trans ht) hC).trans h.2.2.2).trans
      (le_max_right _ _), one_dvd _, h.2.1.1.1⟩

theorem second_transfer_prmp_divisor_mem (I : SupportInterval) {L : ℝ} {C d : Ideal O}
    (hC : C ∈ secondTransferPRMPBox I L) (hd : d ∣ C) : d ∈ secondTransferPRMPBox I L := by
  have hC₀ := (mem_boundedDivisibleIdeals.mp hC).2.2
  have hd₀ : d ≠ ⊥ := ne_zero_of_dvd_ne_zero hC₀ hd
  have hnorm : normIdeal d ≤ normIdeal C := by
    have hpos : 0 < C.absNorm := Nat.pos_of_ne_zero
      (fun h => hC₀ (Ideal.absNorm_eq_zero_iff.mp h))
    change (d.absNorm : ℝ) ≤ (C.absNorm : ℝ)
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)
  exact mem_boundedDivisibleIdeals.mpr
    ⟨hnorm.trans (mem_boundedDivisibleIdeals.mp hC).1, one_dvd _, hd₀⟩

/-- Every original outer and divisor index is truncated using its genuine
finite support. The row function itself is arbitrary. -/
theorem second_transfer_prmp_truncate {α : Type*} [NormedAddCommGroup α]
    (c : ArithmeticContext) (I : SupportInterval) (L : ℝ)
    (f : Ideal O → Ideal O → Ideal O → α) :
    (∑' C : Ideal O, ∑' t : Ideal O,
      if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) =
      ∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
        if secondTransferPRMPAdmissible c I L C t then
          ∑ d ∈ secondTransferPRMPBox I L, if d ∣ C then f C d t else 0 else 0 := by
  have hCzero (C : Ideal O) (hC : C ∉ secondTransferPRMPBox I L) :
      (∑' t : Ideal O, if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) = 0 := by
    have hz (t : Ideal O) : (if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) = 0 :=
      ite_eq_right (fun h => hC (second_transfer_prmp_admissible_mem c I h).1)
    simp only [hz, tsum_zero]
  rw [tsum_eq_sum hCzero]
  apply Finset.sum_congr rfl
  intro C hC
  have htzero (t : Ideal O) (ht : t ∉ secondTransferPRMPBox I L) :
      (if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) = 0 :=
    ite_eq_right (fun h => ht (second_transfer_prmp_admissible_mem c I h).2)
  rw [tsum_eq_sum htzero]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · apply tsum_eq_sum
    intro d hd
    exact ite_eq_right (fun hdiv => hd (second_transfer_prmp_divisor_mem I hC hdiv))
  · rfl

theorem second_transfer_prmp_zero_scale_identity {H L F Sigma cI NC Nd Nt : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hC : 0 < NC)
    (hd : 0 < Nd) (ht : 0 < Nt) :
    (H * NC / (Nd * L ^ 2 * F)) *
      (cI * Sigma * L * F * Nd / (H * NC ^ 2)) * (L / (NC * Nt)) =
        cI * Sigma / (NC ^ 2 * Nt) := by
  field_simp

end QRHShort
