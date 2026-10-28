import QRHShort.FirstTransferPoissonPreMobiusZeroBound

/-! Sum the proved pointwise zero-frequency bound over the actual finite
ranges, then apply the existing weighted ideal-counting theorem. -/

noncomputable section

open Classical
open scoped BigOperators

namespace QRHShort

theorem first_transfer_preMobius_zero_outer_sum_le_columns
    (c : ArithmeticContext) (I : SupportInterval) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {L : ℝ} (hL : 0 < L) :
    (∑ C ∈ firstTransferPreMobiusOuter c I L, ‖W (normIdeal C / L)‖ ^ 2) ≤
      firstTransferPoissonDiagonalColumns c W L := by
  calc
    _ = ∑ C ∈ firstTransferPreMobiusOuter c I L,
        if SquarefreeOutside c.S C then ‖W (normIdeal C / L)‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact (ite_eq_left (mem_firstTransferPreMobiusOuter.mp hC).1).symm
    _ ≤ ∑' C : Ideal O,
        if SquarefreeOutside c.S C then ‖W (normIdeal C / L)‖ ^ 2 else 0 := by
      apply Summable.sum_le_tsum
      · intro C _
        split_ifs
        · exact sq_nonneg _
        · exact le_rfl
      · exact first_transfer_poisson_diagonal_columns_summable c I hW hL
    _ = _ := rfl

theorem first_transfer_preMobius_zero_norm_le_diagonal
    (hz : PoissonZeroStatement) (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) :
    ‖firstTransferPreMobiusZero c I Φ ξ W H L F‖ ≤
      ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ *
        (H / (L * F) * (∑' f : Ideal O,
          if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
            firstTransferPoissonDiagonalColumns c W L else 0)) := by
  let A : ℝ := H / (L * F) * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖
  have hA : 0 ≤ A := mul_nonneg (div_nonneg hH.le (mul_pos hL hF).le) (norm_nonneg _)
  have hrow (f : Ideal O) :
      ‖∑ C ∈ firstTransferPreMobiusOuter c I L,
        ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
          firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2)‖ ≤
        A * firstTransferPoissonDiagonalColumns c W L := by
    calc
      _ ≤ ∑ C ∈ firstTransferPreMobiusOuter c I L,
          ‖∑ p ∈ firstTransferPreMobiusPairWindow I L C,
            firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ C ∈ firstTransferPreMobiusOuter c I L, A * ‖W (normIdeal C / L)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro C hC
        exact first_transfer_preMobius_zero_pair_sum_norm_le hz c hc I Φ ξ W hH hL hF f
          (mem_firstTransferPreMobiusOuter.mp hC).1
      _ = A * ∑ C ∈ firstTransferPreMobiusOuter c I L, ‖W (normIdeal C / L)‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ A * firstTransferPoissonDiagonalColumns c W L :=
        mul_le_mul_of_nonneg_left (first_transfer_preMobius_zero_outer_sum_le_columns c I hW hL) hA
  rw [first_transfer_poisson_diagonal_outer_eq]
  calc
    ‖firstTransferPreMobiusZero c I Φ ξ W H L F‖ ≤
        ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
          ‖∑ C ∈ firstTransferPreMobiusOuter c I L,
            ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
              firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _f ∈ firstTransferPoissonDiagonalDyadic c F,
        A * firstTransferPoissonDiagonalColumns c W L :=
      Finset.sum_le_sum (fun f _ => hrow f)
    _ = (firstTransferPoissonDiagonalDyadic c F).card *
        (A * firstTransferPoissonDiagonalColumns c W L) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by dsimp only [A]; ring

/-- The constant precedes the character, weight, scales, and even the
Poisson-zero premise.  The arithmetic premise supplies the original
coefficient normalization and is not replaced by a diagonal assumption. -/
theorem first_transfer_preMobius_zero_bound (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (hc : ArithmeticRelations c) :
    ∃ Kz : ℝ, 0 ≤ Kz ∧ ∀ (_hz : PoissonZeroStatement) (ξ : RayCharacter c)
      (W : ℝ → ℂ) (H L F : ℝ), SmoothSupported I W →
      0 < H → 0 < L → 0 < F →
      ‖firstTransferPreMobiusZero c I Φ ξ W H L F‖ ≤ Kz * H * weightNorm 0 W ^ 2 := by
  obtain ⟨K, hK, hdiag⟩ := first_transfer_poisson_diagonal_bound I
  refine ⟨‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ * K,
    mul_nonneg (norm_nonneg _) hK, ?_⟩
  intro hz ξ W H L F hW hH hL hF
  have hd := hdiag c W H L F hW hH.le hL hF
  calc
    ‖firstTransferPreMobiusZero c I Φ ξ W H L F‖ ≤
        ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ *
          (H / (L * F) * (∑' f : Ideal O,
            if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
              firstTransferPoissonDiagonalColumns c W L else 0)) :=
      first_transfer_preMobius_zero_norm_le_diagonal hz c hc I Φ ξ hW hH hL hF
    _ ≤ ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ *
        (K * H * weightNorm 0 W ^ 2) := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = _ := by ring

theorem first_transfer_preMobius_zero_bound_of_one_le (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (hc : ArithmeticRelations c) :
    ∃ Kz : ℝ, 0 ≤ Kz ∧ ∀ (_hz : PoissonZeroStatement) (ξ : RayCharacter c)
      (W : ℝ → ℂ) (H L F : ℝ), SmoothSupported I W →
      1 ≤ H → 1 ≤ L → 1 ≤ F →
      ‖firstTransferPreMobiusZero c I Φ ξ W H L F‖ ≤ Kz * H * weightNorm 0 W ^ 2 := by
  obtain ⟨Kz, hKz, hbound⟩ := first_transfer_preMobius_zero_bound c I Φ hc
  exact ⟨Kz, hKz, fun hz ξ W H L F hW hH hL hF =>
    hbound hz ξ W H L F hW (zero_lt_one.trans_le hH)
      (zero_lt_one.trans_le hL) (zero_lt_one.trans_le hF)⟩

end QRHShort
