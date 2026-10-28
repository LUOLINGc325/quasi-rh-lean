import QRHShort.FirstTransferOffDiagonalReindex

/-!
The exact outer-row cutoff and nested column sums for the actual pair
reindexing.  The finite-window version matches the pre-Möbius row directly.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_offDiagonal_pairKernel_tsum_prod
    (c : ArithmeticContext) (ξ : RayCharacter c) (C d t : Ideal O)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {ell : ℝ} (hell : 0 < ell) (β : ℝ) (z : O) :
    (∑' p : Ideal O × Ideal O,
      firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z p) =
    ∑' x : Ideal O, ∑' y : Ideal O,
      firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z (x, y) := by
  have hs : Summable (firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z) :=
    summable_of_hasFiniteSupport
      (first_transfer_offDiagonal_pairKernel_hasFiniteSupport c ξ C d t I Φ hW hell β z)
  exact hs.tsum_prod

theorem first_transfer_offDiagonal_pair_reindex_cutoff
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {C d f : Ideal O}
    (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C)
    {L : ℝ} (hL : 0 < L) (β : ℝ) (h : O) :
    firstTransferOffDiagonalLead C f *
      (∑' p : Ideal O × Ideal O, if IsRelPrime p.1 p.2 then
        firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
          (h * primaryGenerator f ^ 2) p else 0) =
    ∑' t : Ideal O, if SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L ∧
        IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t then
      (mobius t : ℂ) * ∑' p : Ideal O × Ideal O,
        firstTransferOffDiagonalPairKernel c ξ C d t Φ W
          (L / (normIdeal C * normIdeal t)) β (h * primaryGenerator f ^ 2) p
    else 0 := by
  rw [first_transfer_offDiagonal_pair_reindex c ξ I Φ hW hC hf hd hL β h]
  apply tsum_congr
  intro t
  by_cases hr : SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
      IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t
  · rw [ite_eq_left hr]
    by_cases hbound : normIdeal C * normIdeal t ≤ 2 * I.hi * L
    · rw [ite_eq_left ⟨hr.1, hr.2.1, hbound, hr.2.2⟩]
    · rw [ite_eq_right (fun hh => hbound hh.2.2.1)]
      have hzero (p : Ideal O × Ideal O) :
          firstTransferOffDiagonalPairKernel c ξ C d t Φ W
            (L / (normIdeal C * normIdeal t)) β (h * primaryGenerator f ^ 2) p = 0 :=
        first_transfer_offDiagonal_pairKernel_zero_of_outer_cutoff c ξ I Φ hW
          hC.1 hr.1.1.1 d hL (lt_of_not_ge hbound) β (h * primaryGenerator f ^ 2) p
      simp only [hzero, tsum_zero, mul_zero]
  · rw [ite_eq_right hr, ite_eq_right (fun hh => hr ⟨hh.1, hh.2.1, hh.2.2.2⟩)]

/-- The literal nested-column form used in firstTransferBilinear.  No
relative-primality test between x and y remains on the right. -/
theorem first_transfer_offDiagonal_pair_reindex_cutoff_nested
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {C d f : Ideal O}
    (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C)
    {L : ℝ} (hL : 0 < L) (β : ℝ) (h : O) :
    firstTransferOffDiagonalLead C f *
      (∑' p : Ideal O × Ideal O, if IsRelPrime p.1 p.2 then
        firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
          (h * primaryGenerator f ^ 2) p else 0) =
    ∑' t : Ideal O, if SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L ∧
        IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t then
      (mobius t : ℂ) * ∑' x : Ideal O, ∑' y : Ideal O,
        firstTransferOffDiagonalPairKernel c ξ C d t Φ W
          (L / (normIdeal C * normIdeal t)) β (h * primaryGenerator f ^ 2) (x, y)
    else 0 := by
  rw [first_transfer_offDiagonal_pair_reindex_cutoff c ξ I Φ hW hC hf hd hL β h]
  apply tsum_congr
  intro t
  by_cases hr : SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
      normIdeal C * normIdeal t ≤ 2 * I.hi * L ∧
      IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t
  · rw [ite_eq_left hr, ite_eq_left hr,
      first_transfer_offDiagonal_pairKernel_tsum_prod c ξ C d t I Φ hW
        (div_pos hL (mul_pos (normIdeal_pos hC.1) (normIdeal_pos hr.1.1.1))) β
        (h * primaryGenerator f ^ 2)]
  · rw [ite_eq_right hr, ite_eq_right hr]

/-- Direct interface from the actual finite coprime pair window to the
frozen t-row restrictions and nested literal coefficient/kernel expression. -/
theorem first_transfer_offDiagonal_window_pair_reindex
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {C d f : Ideal O}
    (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C)
    {L : ℝ} (hL : 0 < L) (β : ℝ) (h : O) :
    firstTransferOffDiagonalLead C f *
      (∑ p ∈ (firstTransferIdealWindow I (L / normIdeal C)).product
          (firstTransferIdealWindow I (L / normIdeal C)),
        if IsRelPrime p.1 p.2 then
          firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
            (h * primaryGenerator f ^ 2) p else 0) =
    ∑' t : Ideal O, if SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L ∧
        IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t then
      (mobius t : ℂ) * ∑' x : Ideal O, ∑' y : Ideal O,
        firstTransferCoefficient c ξ C d t (h * primaryGenerator f ^ 2) x *
          star (firstTransferCoefficient c ξ C d t (h * primaryGenerator f ^ 2) y) *
          firstTransferKernel Φ W β
            ![normIdeal x / (L / (normIdeal C * normIdeal t)),
              normIdeal y / (L / (normIdeal C * normIdeal t))]
    else 0 := by
  rw [← first_transfer_offDiagonal_coprime_pair_eq_sum_window c ξ C d 1 I Φ hW
    (div_pos hL (normIdeal_pos hC.1)) β (h * primaryGenerator f ^ 2)]
  exact first_transfer_offDiagonal_pair_reindex_cutoff_nested c ξ I Φ hW hC hf hd hL β h

end QRHShort
