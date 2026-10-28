import QRHShort.IdealCounting
import QRHShort.EnergySupport

/-!
The ideal-counting bound used in paper2.tex:2282--2284. Both ideal ranges
are genuinely finitely supported. This is the displayed counting majorant;
identifying a Poisson zero-frequency contribution with it is a separate task.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferPoissonDiagonalColumns (c : ArithmeticContext) (W : ℝ → ℂ)
    (L : ℝ) : ℝ :=
  ∑' C : Ideal O, if SquarefreeOutside c.S C then ‖W (normIdeal C / L)‖ ^ 2 else 0

def firstTransferPoissonDiagonalDyadic (c : ArithmeticContext) (F : ℝ) : Finset (Ideal O) :=
  (boundedDivisibleIdeals 1 (2 * F)).filter (fun f =>
    SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F)

theorem mem_firstTransferPoissonDiagonalDyadic {c : ArithmeticContext} {F : ℝ}
    {f : Ideal O} : f ∈ firstTransferPoissonDiagonalDyadic c F ↔
      SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F := by
  constructor
  · intro hf
    exact (Finset.mem_filter.mp hf).2
  · intro hf
    exact Finset.mem_filter.mpr
      ⟨mem_boundedDivisibleIdeals.mpr ⟨hf.2.2.le, one_dvd _, hf.1.1.1⟩, hf⟩

theorem first_transfer_poisson_diagonal_columns_support (c : ArithmeticContext)
    (I : SupportInterval) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) :
    Function.support (fun C : Ideal O =>
      if SquarefreeOutside c.S C then ‖W (normIdeal C / L)‖ ^ 2 else 0) ⊆
        (boundedDivisibleIdeals 1 (I.hi * L) : Set (Ideal O)) := by
  intro C hC
  by_cases hs : SquarefreeOutside c.S C
  · have hw : W (normIdeal C / L) ≠ 0 := by
      intro hw
      exact hC (by simp only [if_pos hs, hw, norm_zero, pow_two, mul_zero])
    exact mem_boundedDivisibleIdeals.mpr
      ⟨(div_le_iff₀ hL).mp (hW.2 hw).2, one_dvd _, hs.1.1⟩
  · exact False.elim (hC (if_neg hs))

theorem first_transfer_poisson_diagonal_columns_hasFiniteSupport (c : ArithmeticContext)
    (I : SupportInterval) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) :
    Function.HasFiniteSupport (fun C : Ideal O =>
      if SquarefreeOutside c.S C then ‖W (normIdeal C / L)‖ ^ 2 else 0) :=
  (boundedDivisibleIdeals 1 (I.hi * L)).finite_toSet.subset
    (first_transfer_poisson_diagonal_columns_support c I hW hL)

theorem first_transfer_poisson_diagonal_columns_summable (c : ArithmeticContext)
    (I : SupportInterval) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) :
    Summable (fun C : Ideal O =>
      if SquarefreeOutside c.S C then ‖W (normIdeal C / L)‖ ^ 2 else 0) :=
  summable_of_hasFiniteSupport
    (first_transfer_poisson_diagonal_columns_hasFiniteSupport c I hW hL)

theorem first_transfer_poisson_diagonal_rows_hasFiniteSupport (c : ArithmeticContext)
    (F v : ℝ) : Function.HasFiniteSupport (fun f : Ideal O =>
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then v else 0) := by
  apply (firstTransferPoissonDiagonalDyadic c F).finite_toSet.subset
  intro f hf
  by_cases hs : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F
  · exact mem_firstTransferPoissonDiagonalDyadic.mpr hs
  · exact False.elim (hf (if_neg hs))

theorem first_transfer_poisson_diagonal_rows_summable (c : ArithmeticContext)
    (F v : ℝ) : Summable (fun f : Ideal O =>
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then v else 0) :=
  summable_of_hasFiniteSupport (first_transfer_poisson_diagonal_rows_hasFiniteSupport c F v)

theorem first_transfer_poisson_diagonal_outer_eq (c : ArithmeticContext) (F v : ℝ) :
    (∑' f : Ideal O,
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then v else 0) =
        (firstTransferPoissonDiagonalDyadic c F).card * v := by
  have hzero (f : Ideal O) (hf : f ∉ firstTransferPoissonDiagonalDyadic c F) :
      (if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then v else 0) = 0 := by
    apply if_neg
    exact fun hs => hf (mem_firstTransferPoissonDiagonalDyadic.mpr hs)
  rw [tsum_eq_sum hzero]
  calc
    _ = ∑ _f ∈ firstTransferPoissonDiagonalDyadic c F, v := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [if_pos (mem_firstTransferPoissonDiagonalDyadic.mp hf)]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem first_transfer_poisson_diagonal_dyadic_count :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ArithmeticContext) (F : ℝ), 0 < F →
      ((firstTransferPoissonDiagonalDyadic c F).card : ℝ) ≤ K * F := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  refine ⟨2 * C, mul_nonneg (by norm_num) hC.le, fun c F hF => ?_⟩
  calc
    ((firstTransferPoissonDiagonalDyadic c F).card : ℝ) ≤
        ((boundedDivisibleIdeals 1 (2 * F)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ C * (2 * F) := hcount _ (mul_pos (by norm_num) hF)
    _ = (2 * C) * F := by ring

theorem first_transfer_poisson_diagonal_columns_bound (I : SupportInterval) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ArithmeticContext) (W : ℝ → ℂ) (L : ℝ),
      SmoothSupported I W → 0 < L →
        firstTransferPoissonDiagonalColumns c W L ≤ K * L * weightNorm 0 W ^ 2 := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
  refine ⟨C * I.hi, mul_nonneg hC.le hhi.le, fun c W L hW hL => ?_⟩
  have heq : firstTransferPoissonDiagonalColumns c W L =
      ∑ n ∈ boundedDivisibleIdeals 1 (I.hi * L),
        if SquarefreeOutside c.S n then ‖W (normIdeal n / L)‖ ^ 2 else 0 := by
    apply tsum_eq_sum
    intro n hn
    by_contra hne
    exact hn (first_transfer_poisson_diagonal_columns_support c I hW hL hne)
  have hnorm (n : Ideal O) : ‖W (normIdeal n / L)‖ ^ 2 ≤ weightNorm 0 W ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (weightNorm_nonneg hW 0)).2
    simpa only [iteratedDeriv_zero] using
      norm_iteratedDeriv_le_weightNorm hW (le_refl 0) (normIdeal n / L)
  calc
    firstTransferPoissonDiagonalColumns c W L = _ := heq
    _ ≤ ∑ _n ∈ boundedDivisibleIdeals 1 (I.hi * L), weightNorm 0 W ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs
      · exact hnorm n
      · exact sq_nonneg _
    _ = ((boundedDivisibleIdeals 1 (I.hi * L)).card : ℝ) * weightNorm 0 W ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * (I.hi * L)) * weightNorm 0 W ^ 2 :=
      mul_le_mul_of_nonneg_right (hcount _ (mul_pos hhi hL)) (sq_nonneg _)
    _ = (C * I.hi) * L * weightNorm 0 W ^ 2 := by ring

theorem first_transfer_poisson_diagonal_bound (I : SupportInterval) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ArithmeticContext) (W : ℝ → ℂ) (H L F : ℝ),
      SmoothSupported I W → 0 ≤ H → 0 < L → 0 < F →
        H / (L * F) *
          (∑' f : Ideal O,
            if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
              ∑' C : Ideal O,
                if SquarefreeOutside c.S C then ‖W (normIdeal C / L)‖ ^ 2 else 0
            else 0) ≤ K * H * weightNorm 0 W ^ 2 := by
  obtain ⟨Kc, hKc, hcolumns⟩ := first_transfer_poisson_diagonal_columns_bound I
  obtain ⟨Kf, hKf, hcount⟩ := first_transfer_poisson_diagonal_dyadic_count
  refine ⟨Kc * Kf, mul_nonneg hKc hKf, fun c W H L F hW hH hL hF => ?_⟩
  change H / (L * F) *
    (∑' f : Ideal O,
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        firstTransferPoissonDiagonalColumns c W L else 0) ≤ _
  rw [first_transfer_poisson_diagonal_outer_eq]
  have hcol0 : 0 ≤ firstTransferPoissonDiagonalColumns c W L := by
    apply tsum_nonneg
    intro n
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have hproduct := mul_le_mul (hcount c F hF) (hcolumns c W L hW hL) hcol0
    (mul_nonneg hKf hF.le)
  calc
    _ ≤ H / (L * F) * ((Kf * F) * (Kc * L * weightNorm 0 W ^ 2)) :=
      mul_le_mul_of_nonneg_left hproduct (div_nonneg hH (mul_pos hL hF).le)
    _ = (Kc * Kf) * H * weightNorm 0 W ^ 2 := by
      field_simp [ne_of_gt hL, ne_of_gt hF]

end QRHShort
