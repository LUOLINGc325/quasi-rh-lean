import QRHShort.FirstTransferPoissonPreMobiusDefinition
import QRHShort.FirstTransferOffDiagonalReindexCutoff

/-!
Aggregation of the actual fixed-row Möbius identity. All outer ideal and
frequency series are reduced to the original finite ranges before commuting
their order. The residual columns retain their literal nested sums.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferPreMobiusPostRow (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ)
    (C d f : Ideal O) (h : O) (t : Ideal O) : ℂ :=
  if SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
      normIdeal C * normIdeal t ≤ 2 * I.hi * L ∧
      IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t then
    (mobius d : ℂ) * ((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
      ((mobius t : ℂ) * ∑' x : Ideal O, ∑' y : Ideal O,
        firstTransferOffDiagonalPairKernel c ξ C d t Φ W
          (L / (normIdeal C * normIdeal t))
          (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
          (h * primaryGenerator f ^ 2) (x, y))
  else 0

theorem first_transfer_preMobius_postRow_support (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (H L F : ℝ) {C : Ideal O} (hC : Outside c.S C) (d f : Ideal O) (h : O) :
    Function.support (firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h) ⊆
      (firstTransferPreMobiusOuter c I L : Set (Ideal O)) := by
  intro t ht
  have hr : SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
      normIdeal C * normIdeal t ≤ 2 * I.hi * L ∧
      IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t := by
    by_contra hr
    exact ht (by simp only [firstTransferPreMobiusPostRow, if_neg hr])
  apply mem_firstTransferPreMobiusOuter.mpr
  refine ⟨hr.1, ?_⟩
  exact (le_mul_of_one_le_left (normIdeal_pos hr.1.1.1).le
    (first_transfer_one_le_normIdeal hC.1)).trans hr.2.2.1

theorem first_transfer_preMobius_postRow_tsum_eq_sum (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (H L F : ℝ) {C : Ideal O} (hC : Outside c.S C) (d f : Ideal O) (h : O) :
    (∑' t : Ideal O, firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h t) =
      ∑ t ∈ firstTransferPreMobiusOuter c I L,
        firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h t := by
  apply tsum_eq_sum
  intro t ht
  by_contra hne
  exact ht (first_transfer_preMobius_postRow_support c I Φ ξ W H L F hC d f h hne)

theorem first_transfer_preMobius_pair_sum_reindex (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (H F : ℝ) {L : ℝ} (hL : 0 < L)
    {C d f : Ideal O} (hC : Outside c.S C) (hf : Outside c.S f) (hd : d ∣ C) (h : O) :
    (∑ p ∈ firstTransferPreMobiusPairWindow I L C,
      if IsRelPrime p.1 p.2 then firstTransferPreMobiusKernelTerm c Φ ξ W H L F C d f h p else 0) =
      ∑ t ∈ firstTransferPreMobiusOuter c I L,
        firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h t := by
  rw [← first_transfer_preMobius_postRow_tsum_eq_sum c I Φ ξ W H L F hC d f h]
  calc
    _ = (mobius d : ℂ) * ((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
        (firstTransferOffDiagonalLead C f *
          ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
            if IsRelPrime p.1 p.2 then
              firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C)
                (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
                (h * primaryGenerator f ^ 2) p else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp only [firstTransferPreMobiusKernelTerm, mul_zero]
      ring
    _ = _ := by
      unfold firstTransferPreMobiusPairWindow
      rw [first_transfer_offDiagonal_window_pair_reindex c ξ I Φ hW hC hf hd hL
        (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d)) h]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro t
      unfold firstTransferPreMobiusPostRow
      split_ifs
      · rfl
      · simp only [mul_zero]

theorem first_transfer_preMobius_finite_sum_comm
    (D T F : Finset (Ideal O)) (J : Ideal O → Finset O)
    (g : Ideal O → Ideal O → O → Ideal O → ℂ) :
    (∑ d ∈ D, ∑ f ∈ F, ∑ h ∈ J d, ∑ t ∈ T, g d f h t) =
      ∑ t ∈ T, ∑ d ∈ D, ∑ f ∈ F, ∑ h ∈ J d, g d f h t := by
  calc
    _ = ∑ d ∈ D, ∑ f ∈ F, ∑ t ∈ T, ∑ h ∈ J d, g d f h t := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, ∑ t ∈ T, ∑ f ∈ F, ∑ h ∈ J d, g d f h t := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem first_transfer_preMobius_divisor_tsum (c : ArithmeticContext) {C : Ideal O}
    (hC : SquarefreeOutside c.S C) (v : Ideal O → ℂ) :
    (∑' d : Ideal O, if d ∣ C then v d else 0) =
      ∑ d ∈ firstTransferPoissonDivisors C, v d := by
  simpa only [first_transfer_outsideRadical_eq_self_of_squarefree hC.1.1 hC.2] using
    first_transfer_poisson_divisor_tsum_eq_sum C v

theorem first_transfer_preMobius_dyadic_tsum (c : ArithmeticContext) (F : ℝ)
    (P : Ideal O → Prop) (v : Ideal O → ℂ) :
    (∑' f : Ideal O, if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F ∧ P f
      then v f else 0) =
      ∑ f ∈ firstTransferPoissonDiagonalDyadic c F, if P f then v f else 0 := by
  have hz (f : Ideal O) (hf : f ∉ firstTransferPoissonDiagonalDyadic c F) :
      (if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F ∧ P f
        then v f else 0) = 0 := by
    apply if_neg
    exact fun h => hf (mem_firstTransferPoissonDiagonalDyadic.mpr ⟨h.1, h.2.1, h.2.2.1⟩)
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro f hf
  obtain ⟨hs, hlo, hhi⟩ := mem_firstTransferPoissonDiagonalDyadic.mp hf
  by_cases hp : P f
  · rw [if_pos ⟨hs, hlo, hhi, hp⟩, if_pos hp]
  · rw [if_neg (fun h => hp h.2.2.2), if_neg hp]

theorem first_transfer_preMobius_frequency_tsum (I : SupportInterval) (Φ : RowWeight)
    (H L : ℝ) (C d : Ideal O) (P : O → Prop) (v : O → ℂ) :
    (∑' h : O, if h ≠ 0 ∧ P h ∧ normElement h ≤
      Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal d / (H * normIdeal C ^ 2) then v h else 0) =
      ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d, if P h then v h else 0 := by
  have hz (h : O) (hh : h ∉ firstTransferPreMobiusFrequencies I Φ H L C d) :
      (if h ≠ 0 ∧ P h ∧ normElement h ≤
        Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal d / (H * normIdeal C ^ 2) then v h else 0) = 0 := by
    apply if_neg
    exact fun hmem => hh (mem_firstTransferPreMobiusFrequencies.mpr ⟨hmem.1, hmem.2.2⟩)
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro h hh
  obtain ⟨hne, hbound⟩ := mem_firstTransferPreMobiusFrequencies.mp hh
  by_cases hp : P h
  · rw [if_pos ⟨hne, hp, hbound⟩, if_pos hp]
  · rw [if_neg (fun hmem => hp hmem.2.1), if_neg hp]

theorem first_transfer_bilinear_eq_finite_postRows (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) :
    firstTransferBilinear c I Φ ξ W H L F =
      ∑ C ∈ firstTransferPreMobiusOuter c I L,
        ∑ t ∈ firstTransferPreMobiusOuter c I L,
          ∑ d ∈ firstTransferPoissonDivisors C,
            ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
              ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
                firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h t := by
  let P (C d t f : Ideal O) (h : O) : ℂ :=
    ∑' x : Ideal O, ∑' y : Ideal O,
      firstTransferOffDiagonalPairKernel c ξ C d t Φ W
        (L / (normIdeal C * normIdeal t))
        (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
        (h * primaryGenerator f ^ 2) (x, y)
  let R (C t : Ideal O) : ℂ := ∑' d : Ideal O, if d ∣ C then
    (mobius d : ℂ) * (mobius t : ℂ) * ((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
      ∑' f : Ideal O, if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F ∧
        IsRelPrime f (C * t) then
          ∑' h : O, if h ≠ 0 ∧ IsRelPrime (principal h) t ∧ normElement h ≤
            Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal d / (H * normIdeal C ^ 2)
            then P C d t f h else 0
        else 0
    else 0
  let G (C t : Ideal O) : ℂ := if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧
    IsRelPrime C t ∧ normIdeal C * normIdeal t ≤ 2 * I.hi * L then R C t else 0
  change (∑' C : Ideal O, ∑' t : Ideal O, G C t) = _
  have hCzero (C : Ideal O) (hnot : C ∉ firstTransferPreMobiusOuter c I L) :
      (∑' t : Ideal O, G C t) = 0 := by
    have hz (t : Ideal O) : G C t = 0 := by
      unfold G
      apply if_neg
      intro hr
      exact hnot (mem_firstTransferPreMobiusOuter.mpr ⟨hr.1,
        (le_mul_of_one_le_right (normIdeal_pos hr.1.1.1).le
          (first_transfer_one_le_normIdeal hr.2.1.1.1)).trans hr.2.2.2⟩)
    simp only [hz, tsum_zero]
  rw [tsum_eq_sum hCzero]
  apply Finset.sum_congr rfl
  intro C hCmem
  have hC := (mem_firstTransferPreMobiusOuter.mp hCmem).1
  have htzero (t : Ideal O) (hnot : t ∉ firstTransferPreMobiusOuter c I L) : G C t = 0 := by
    unfold G
    apply if_neg
    intro hr
    exact hnot (mem_firstTransferPreMobiusOuter.mpr ⟨hr.2.1,
      (le_mul_of_one_le_left (normIdeal_pos hr.2.1.1.1).le
        (first_transfer_one_le_normIdeal hr.1.1.1)).trans hr.2.2.2⟩)
  rw [tsum_eq_sum htzero]
  apply Finset.sum_congr rfl
  intro t htmem
  by_cases hct : SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
      normIdeal C * normIdeal t ≤ 2 * I.hi * L
  · simp only [G, if_pos hct]
    unfold R
    rw [first_transfer_preMobius_divisor_tsum c hC]
    apply Finset.sum_congr rfl
    intro d hd
    rw [first_transfer_preMobius_dyadic_tsum c F (fun f => IsRelPrime f (C * t)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hfc : IsRelPrime f (C * t)
    · rw [if_pos hfc, first_transfer_preMobius_frequency_tsum I Φ H L C d
        (fun h => IsRelPrime (principal h) t), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hht : IsRelPrime (principal h) t
      · rw [if_pos hht]
        unfold firstTransferPreMobiusPostRow
        rw [if_pos ⟨hct.2.1, hct.2.2.1, hct.2.2.2, hfc, hht⟩]
        unfold P
        ring
      · rw [if_neg hht, mul_zero]
        unfold firstTransferPreMobiusPostRow
        rw [if_neg (fun hr => hht hr.2.2.2.2)]
    · rw [if_neg hfc, mul_zero]
      have hz (h : O) : firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h t = 0 := by
        unfold firstTransferPreMobiusPostRow
        exact if_neg (fun hr => hfc hr.2.2.2.1)
      simp only [hz, Finset.sum_const_zero]
  · have hz (d f : Ideal O) (h : O) :
        firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h t = 0 := by
      unfold firstTransferPreMobiusPostRow
      exact if_neg (fun hr => hct ⟨hC, hr.1, hr.2.1, hr.2.2.1⟩)
    simp only [G, if_neg hct, hz, Finset.sum_const_zero]

theorem first_transfer_preMobius_bilinear_eq (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (H F : ℝ) {L : ℝ} (hL : 0 < L) :
    firstTransferPreMobiusBilinear c I Φ ξ W H L F =
      firstTransferBilinear c I Φ ξ W H L F := by
  rw [first_transfer_bilinear_eq_finite_postRows]
  unfold firstTransferPreMobiusBilinear
  apply Finset.sum_congr rfl
  intro C hCmem
  have hC := (mem_firstTransferPreMobiusOuter.mp hCmem).1
  calc
    _ = ∑ d ∈ firstTransferPoissonDivisors C,
        ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
          ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
            ∑ t ∈ firstTransferPreMobiusOuter c I L,
              firstTransferPreMobiusPostRow c I Φ ξ W H L F C d f h t := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdC : d ∣ C := by
        have := mem_firstTransferPoissonDivisors.mp hd
        simpa only [first_transfer_outsideRadical_eq_self_of_squarefree hC.1.1 hC.2] using this
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro h hh
      exact first_transfer_preMobius_pair_sum_reindex c I Φ ξ hW H F hL hC.1
        (mem_firstTransferPoissonDiagonalDyadic.mp hf).1.1 hdC h
    _ = _ := first_transfer_preMobius_finite_sum_comm _ _ _ _ _

end QRHShort
