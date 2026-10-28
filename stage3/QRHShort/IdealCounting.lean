import QRHShort.PrimeComparison
import QRHShort.WeightNorm
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Data.Set.Card

/-!
The number-field ideal-counting asymptotic gives a uniform linear bound for
nonzero ideals of bounded norm. Combined with `PrimeComparison`, this proves
the `D / Y` error for rows indexed by ideals in `(Y / 2, Y]`, conditional only
on the two explicitly stated residue-symbol identities and a weight bound.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace QRHShort

private theorem exists_pos_eventually_le {f : ℝ → ℝ} {L : ℝ}
    (h : Tendsto f atTop (𝓝 L)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X in atTop, f X ≤ C := by
  refine ⟨max 1 (L + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  exact Filter.Tendsto.eventually_le_const
    ((lt_add_one L).trans_le (le_max_right _ _)) h

theorem card_finite_normIdeal_le_eq_natCard (X : ℝ) :
    (finite_normIdeal_le X).toFinset.card =
      Nat.card {n : Ideal O // (n.absNorm : ℝ) ≤ X} := by
  change (finite_normIdeal_le X).toFinset.card =
    {n : Ideal O | normIdeal n ≤ X}.ncard
  exact (Set.ncard_eq_toFinset_card _ (finite_normIdeal_le X)).symm

theorem exists_ideal_norm_count_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X →
      ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ C * X := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_eventually_le
    (NumberField.Ideal.tendsto_norm_le_div_atTop K)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hbound
  let M : ℝ := max 1 T
  let N : ℝ := ((finite_normIdeal_le M).toFinset.card : ℝ)
  refine ⟨max C N, hC.trans_le (le_max_left _ _), ?_⟩
  intro X hX
  have hmax : 0 ≤ max C N := (hC.trans_le (le_max_left _ _)).le
  by_cases hX1 : 1 ≤ X
  · have hsub : (boundedDivisibleIdeals 1 X).card ≤
        (finite_normIdeal_le X).toFinset.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    by_cases hTX : T ≤ X
    · have hlarge : ((finite_normIdeal_le X).toFinset.card : ℝ) ≤ C * X := by
        rw [card_finite_normIdeal_le_eq_natCard]
        exact (div_le_iff₀ hX).mp (hT X hTX)
      have hsub' : ((boundedDivisibleIdeals 1 X).card : ℝ) ≤
          ((finite_normIdeal_le X).toFinset.card : ℝ) := by exact_mod_cast hsub
      exact hsub'.trans (hlarge.trans (mul_le_mul_of_nonneg_right
        (le_max_left C N) hX.le))
    · have hXM : X ≤ M := (not_le.mp hTX).le.trans (le_max_right _ _)
      have hsmall : ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ N := by
        apply Nat.cast_le.mpr
        apply hsub.trans
        apply Finset.card_le_card
        intro n hn
        exact (finite_normIdeal_le M).mem_toFinset.mpr
          (((finite_normIdeal_le X).mem_toFinset.mp hn).trans hXM)
      exact hsmall.trans ((le_max_right C N).trans
        (le_mul_of_one_le_right hmax hX1))
  · have hempty : boundedDivisibleIdeals 1 X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hnX, _, hn0⟩ := mem_boundedDivisibleIdeals.mp hn
      have hnNat : 1 ≤ n.absNorm := Nat.one_le_iff_ne_zero.mpr
        (fun h => hn0 (Ideal.absNorm_eq_zero_iff.mp h))
      have hnOne : (1 : ℝ) ≤ normIdeal n := by
        change (1 : ℝ) ≤ (n.absNorm : ℝ)
        exact_mod_cast hnNat
      exact hX1 (hnOne.trans hnX)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hmax hX.le

theorem exists_originalSum_sixth_error_constant (c : ArithmeticContext)
    (I : SupportInterval) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {B : ℝ} (hB : 0 ≤ B) (hWbound : ∀ x : ℝ, ‖W x‖ ≤ B)
    (hone : ∀ n : Ideal O, Outside c.S n → sexticSymbol n 1 = 1) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (D Y : ℝ), 0 < D → 0 < Y →
      ∀ p : Ideal O, p ≠ ⊥ → Y / 2 ≤ normIdeal p →
      (∀ n : Ideal O, Outside c.S n →
        sexticSymbol n (primaryGenerator p ^ (6 : ℕ)) = if p ∣ n then 0 else 1) →
      ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
        E * D / Y := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  refine ⟨2 * (C * B * I.hi), ?_, ?_⟩
  · exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg hC.le hB) (I.lo_pos.trans_le I.ordered).le)
  · intro D Y hD hY p hp hNp hsixth
    have h := originalSum_sub_sixth_norm_le_div_scale c I hW hD
      (div_pos hY (by norm_num)) hB hC.le hWbound hcount hp hNp hone hsixth
    convert h using 1 <;> ring

/-- The row-comparison constant is uniform over smooth weights and derivative
orders; only the fixed support interval enters the constant. -/
theorem exists_sixth_row_error_weightNorm (I : SupportInterval) :
    ∃ E : ℝ, 0 < E ∧ ∀ (c : ArithmeticContext) (W : ℝ → ℂ),
      SmoothSupported I W → ∀ (J : ℕ) (D Y : ℝ), 0 < D → 0 < Y →
      ∀ p : Ideal O, p ≠ ⊥ → Y / 2 ≤ normIdeal p →
      (∀ n : Ideal O, Outside c.S n → sexticSymbol n 1 = 1) →
      (∀ n : Ideal O, Outside c.S n →
        sexticSymbol n (primaryGenerator p ^ (6 : ℕ)) = if p ∣ n then 0 else 1) →
      ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
        E * weightNorm J W * D / Y := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  refine ⟨2 * C * I.hi, mul_pos (mul_pos (by norm_num) hC)
    (I.lo_pos.trans_le I.ordered), ?_⟩
  intro c W hW J D Y hD hY p hp hNp hone hsixth
  have hWbound : ∀ x : ℝ, ‖W x‖ ≤ weightNorm J W := by
    intro x
    simpa only [iteratedDeriv_zero] using
      norm_iteratedDeriv_le_weightNorm hW (Nat.zero_le J) x
  have h := originalSum_sub_sixth_norm_le_div_scale c I hW hD
    (div_pos hY (by norm_num)) (weightNorm_nonneg hW J) hC.le hWbound hcount hp
    hNp hone hsixth
  convert h using 1 <;> ring

end QRHShort
