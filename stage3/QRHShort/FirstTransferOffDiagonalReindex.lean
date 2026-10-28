import QRHShort.FirstTransferOffDiagonalReindexPointwise
import QRHShort.FirstTransferMobiusReindex

/-!
Actual fixed-(C,d,f,h) pair integration.  The Möbius input and the transformed
joint (t,x,y) expression have finite support before any series is regrouped.
All residual column restrictions are those inside firstTransferCoefficient;
there is no relative-primality condition between the two residual columns.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferOffDiagonalInput (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d f : Ideal O) (Φ : RowWeight) (W : ℝ → ℂ) (L β : ℝ) (h : O)
    (p : Ideal O × Ideal O) : ℂ :=
  firstTransferOffDiagonalLead C f *
    firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
      (h * primaryGenerator f ^ 2) p

def firstTransferOffDiagonalRowAdmissible (c : ArithmeticContext)
    (C f : Ideal O) (h : O) (t : Ideal O) : Prop :=
  SquarefreeOutside c.S t ∧ IsRelPrime C t ∧ IsRelPrime f (C * t) ∧
    IsRelPrime (principal h) t

def firstTransferOffDiagonalReindexedTerm (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d f : Ideal O) (Φ : RowWeight) (W : ℝ → ℂ) (L β : ℝ) (h : O)
    (q : Ideal O × Ideal O × Ideal O) : ℂ :=
  if firstTransferOffDiagonalRowAdmissible c C f h q.1 then
    (mobius q.1 : ℂ) * firstTransferOffDiagonalPairKernel c ξ C d q.1 Φ W
      (L / (normIdeal C * normIdeal q.1)) β (h * primaryGenerator f ^ 2) q.2
  else 0

theorem first_transfer_offDiagonal_input_hasFiniteSupport
    (c : ArithmeticContext) (ξ : RayCharacter c) {C : Ideal O} (hC : C ≠ ⊥)
    (d f : Ideal O) (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {L : ℝ} (hL : 0 < L) (β : ℝ) (h : O) :
    Function.HasFiniteSupport (firstTransferOffDiagonalInput c ξ C d f Φ W L β h) :=
  Function.HasFiniteSupport.mul_right _
    (first_transfer_offDiagonal_pairKernel_hasFiniteSupport c ξ C d 1 I Φ hW
      (div_pos hL (normIdeal_pos hC)) β (h * primaryGenerator f ^ 2))

theorem first_transfer_offDiagonal_mobiusTerm_eq
    (c : ArithmeticContext) (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ)
    {C d f : Ideal O} (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C)
    (L β : ℝ) (h : O) (q : Ideal O × Ideal O × Ideal O) :
    firstTransferMobiusTripleTerm c (firstTransferOffDiagonalInput c ξ C d f Φ W L β h) q =
      firstTransferOffDiagonalReindexedTerm c ξ C d f Φ W L β h q := by
  by_cases htri : firstTransferMobiusTripleAdmissible c q
  · rw [firstTransferMobiusTripleTerm, ite_eq_left htri, firstTransferOffDiagonalInput,
      first_transfer_offDiagonal_pairKernel_mul c ξ Φ W hC htri.1 htri.2.1 htri.2.2.1
        hf htri.2.2.2.1 htri.2.2.2.2 hd L β h]
    by_cases hr : IsRelPrime C q.1 ∧ IsRelPrime f (C * q.1) ∧ IsRelPrime (principal h) q.1
    · have hrow : firstTransferOffDiagonalRowAdmissible c C f h q.1 := ⟨htri.1, hr⟩
      rw [ite_eq_left hr, firstTransferOffDiagonalReindexedTerm, ite_eq_left hrow]
    · have hrow : ¬ firstTransferOffDiagonalRowAdmissible c C f h q.1 := fun h => hr h.2
      rw [ite_eq_right hr, mul_zero, firstTransferOffDiagonalReindexedTerm, ite_eq_right hrow]
  · rw [firstTransferMobiusTripleTerm, ite_eq_right htri]
    by_cases ht : SquarefreeOutside c.S q.1
    · have hzero : firstTransferOffDiagonalPairKernel c ξ C d q.1 Φ W
          (L / (normIdeal C * normIdeal q.1)) β (h * primaryGenerator f ^ 2) q.2 = 0 := by
        by_contra hn
        exact htri ⟨ht, first_transfer_offDiagonal_pairKernel_columns_of_ne_zero
          c ξ C d q.1 Φ W (L / (normIdeal C * normIdeal q.1)) β
          (h * primaryGenerator f ^ 2) hn⟩
      simp only [firstTransferOffDiagonalReindexedTerm, hzero, mul_zero, ite_self]
    · have hrow : ¬ firstTransferOffDiagonalRowAdmissible c C f h q.1 := fun h => ht h.1
      rw [firstTransferOffDiagonalReindexedTerm, ite_eq_right hrow]

/-- Finiteness is transported from the actual kernel-supported original pair
through its finite set of common divisors, before the joint sum is split. -/
theorem first_transfer_offDiagonal_reindexed_hasFiniteSupport
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {C d f : Ideal O}
    (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C)
    {L : ℝ} (hL : 0 < L) (β : ℝ) (h : O) :
    Function.HasFiniteSupport (firstTransferOffDiagonalReindexedTerm c ξ C d f Φ W L β h) := by
  have hfinite := first_transfer_mobius_tripleTerm_hasFiniteSupport c
    (firstTransferOffDiagonalInput c ξ C d f Φ W L β h)
    (first_transfer_offDiagonal_input_hasFiniteSupport c ξ hC.1 d f I Φ hW hL β h)
  have heq := funext (first_transfer_offDiagonal_mobiusTerm_eq c ξ Φ W hC hf hd L β h)
  rwa [heq] at hfinite

theorem first_transfer_offDiagonal_reindexed_summable
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {C d f : Ideal O}
    (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C)
    {L : ℝ} (hL : 0 < L) (β : ℝ) (h : O) :
    Summable (firstTransferOffDiagonalReindexedTerm c ξ C d f Φ W L β h) :=
  summable_of_hasFiniteSupport
    (first_transfer_offDiagonal_reindexed_hasFiniteSupport c ξ I Φ hW hC hf hd hL β h)

theorem first_transfer_offDiagonal_input_filter (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d f : Ideal O) (Φ : RowWeight) (W : ℝ → ℂ) (L β : ℝ) (h : O)
    (p : Ideal O × Ideal O) :
    (if SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧ IsRelPrime p.1 p.2 then
      firstTransferOffDiagonalInput c ξ C d f Φ W L β h p else 0) =
    firstTransferOffDiagonalLead C f * (if IsRelPrime p.1 p.2 then
      firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
        (h * primaryGenerator f ^ 2) p else 0) := by
  by_cases hrel : IsRelPrime p.1 p.2
  · by_cases hp : SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2
    · rw [ite_eq_left ⟨hp.1, hp.2, hrel⟩, ite_eq_left hrel]
      rfl
    · have hzero : firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
          (h * primaryGenerator f ^ 2) p = 0 := by
        by_contra hn
        have hcols := first_transfer_offDiagonal_pairKernel_columns_of_ne_zero c ξ C d 1
          Φ W (L / normIdeal C) β (h * primaryGenerator f ^ 2) hn
        exact hp ⟨hcols.1, hcols.2.1⟩
      rw [ite_eq_right (fun hh => hp ⟨hh.1, hh.2.1⟩), ite_eq_left hrel, hzero, mul_zero]
  · rw [ite_eq_right (fun hh => hrel hh.2.2), ite_eq_right hrel, mul_zero]

/-- Exact Möbius removal for the literal fixed-row pair.  The remaining
columns are unrestricted relative to one another. -/
theorem first_transfer_offDiagonal_pair_reindex
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {C d f : Ideal O}
    (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C)
    {L : ℝ} (hL : 0 < L) (β : ℝ) (h : O) :
    firstTransferOffDiagonalLead C f *
      (∑' p : Ideal O × Ideal O, if IsRelPrime p.1 p.2 then
        firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
          (h * primaryGenerator f ^ 2) p else 0) =
    ∑' t : Ideal O, if SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t then
      (mobius t : ℂ) * ∑' p : Ideal O × Ideal O,
        firstTransferOffDiagonalPairKernel c ξ C d t Φ W
          (L / (normIdeal C * normIdeal t)) β (h * primaryGenerator f ^ 2) p
    else 0 := by
  have hfinite := first_transfer_offDiagonal_input_hasFiniteSupport c ξ hC.1 d f I Φ hW hL β h
  have hsum := first_transfer_offDiagonal_reindexed_summable c ξ I Φ hW hC hf hd hL β h
  calc
    _ = ∑' p : Ideal O × Ideal O,
        if SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧ IsRelPrime p.1 p.2 then
          firstTransferOffDiagonalInput c ξ C d f Φ W L β h p else 0 := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun p => (first_transfer_offDiagonal_input_filter c ξ C d f Φ W L β h p).symm)
    _ = ∑' q : Ideal O × Ideal O × Ideal O,
        firstTransferMobiusTripleTerm c (firstTransferOffDiagonalInput c ξ C d f Φ W L β h) q := by
      simpa only [first_transfer_mobius_tripleTerm_eq] using
        first_transfer_mobius_remove_pair_coprimality c
          (firstTransferOffDiagonalInput c ξ C d f Φ W L β h) hfinite
    _ = ∑' q : Ideal O × Ideal O × Ideal O,
        firstTransferOffDiagonalReindexedTerm c ξ C d f Φ W L β h q :=
      tsum_congr (first_transfer_offDiagonal_mobiusTerm_eq c ξ Φ W hC hf hd L β h)
    _ = ∑' t : Ideal O, ∑' p : Ideal O × Ideal O,
        firstTransferOffDiagonalReindexedTerm c ξ C d f Φ W L β h (t, p) := hsum.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro t
      by_cases hr : SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
          IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t
      · have hr' : firstTransferOffDiagonalRowAdmissible c C f h t := hr
        simp only [firstTransferOffDiagonalReindexedTerm, ite_eq_left hr', ite_eq_left hr,
          tsum_mul_left]
      · have hr' : ¬ firstTransferOffDiagonalRowAdmissible c C f h t := hr
        simp only [firstTransferOffDiagonalReindexedTerm, ite_eq_right hr', ite_eq_right hr,
          tsum_zero]

end QRHShort
