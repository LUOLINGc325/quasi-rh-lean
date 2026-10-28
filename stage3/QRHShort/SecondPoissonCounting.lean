import QRHShort.FiniteSupport
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Data.Set.Card

/-! The number-field ideal-counting input used by the second Poisson zero
term. Kept independent of the sixth-power row comparison. -/

noncomputable section
open Classical Filter
open scoped Topology

namespace QRHShort.SecondPoissonProof

def boundedIdeals (X : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le X).toFinset.filter (fun n => n ≠ ⊥)

@[simp] theorem mem_boundedIdeals {n : Ideal O} {X : ℝ} :
    n ∈ boundedIdeals X ↔ normIdeal n ≤ X ∧ n ≠ ⊥ := by
  simp only [boundedIdeals, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]

private theorem exists_pos_eventually_le {f : ℝ → ℝ} {L : ℝ}
    (h : Tendsto f atTop (𝓝 L)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ X in atTop, f X ≤ A := by
  refine ⟨max 1 (L + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  exact Filter.Tendsto.eventually_le_const
    ((lt_add_one L).trans_le (le_max_right _ _)) h

/-- A linear bound for nonzero ideals, valid at every positive real scale,
including scales below one. The constant depends only on the fixed field. -/
theorem exists_ideal_count_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ X : ℝ, 0 < X →
      ((boundedIdeals X).card : ℝ) ≤ A * X := by
  obtain ⟨A, hA, hbound⟩ := exists_pos_eventually_le
    (NumberField.Ideal.tendsto_norm_le_div_atTop K)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hbound
  let M : ℝ := max 1 T
  let N : ℝ := ((finite_normIdeal_le M).toFinset.card : ℝ)
  refine ⟨max A N, hA.trans_le (le_max_left _ _), ?_⟩
  intro X hX
  have hmax : 0 ≤ max A N := (hA.trans_le (le_max_left _ _)).le
  by_cases hX1 : 1 ≤ X
  · have hsub : (boundedIdeals X).card ≤ (finite_normIdeal_le X).toFinset.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    by_cases hTX : T ≤ X
    · have hlarge : ((finite_normIdeal_le X).toFinset.card : ℝ) ≤ A * X := by
        have he : (finite_normIdeal_le X).toFinset.card =
            Nat.card {n : Ideal O // (n.absNorm : ℝ) ≤ X} := by
          change (finite_normIdeal_le X).toFinset.card =
            {n : Ideal O | normIdeal n ≤ X}.ncard
          exact (Set.ncard_eq_toFinset_card _ (finite_normIdeal_le X)).symm
        rw [he]
        exact (div_le_iff₀ hX).mp (hT X hTX)
      have hsub' : ((boundedIdeals X).card : ℝ) ≤
          ((finite_normIdeal_le X).toFinset.card : ℝ) := by exact_mod_cast hsub
      exact hsub'.trans (hlarge.trans
        (mul_le_mul_of_nonneg_right (le_max_left A N) hX.le))
    · have hXM : X ≤ M := (not_le.mp hTX).le.trans (le_max_right _ _)
      have hsmall : ((boundedIdeals X).card : ℝ) ≤ N := by
        apply Nat.cast_le.mpr
        apply hsub.trans
        apply Finset.card_le_card
        intro n hn
        exact (finite_normIdeal_le M).mem_toFinset.mpr
          (((finite_normIdeal_le X).mem_toFinset.mp hn).trans hXM)
      exact hsmall.trans ((le_max_right A N).trans
        (le_mul_of_one_le_right hmax hX1))
  · have hempty : boundedIdeals X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hnX, hn0⟩ := mem_boundedIdeals.mp hn
      have hnNat : 1 ≤ n.absNorm := Nat.one_le_iff_ne_zero.mpr
        (fun h => hn0 (Ideal.absNorm_eq_zero_iff.mp h))
      have hnOne : (1 : ℝ) ≤ normIdeal n := by
        change (1 : ℝ) ≤ (n.absNorm : ℝ)
        exact_mod_cast hnNat
      exact hX1 (hnOne.trans hnX)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hmax hX.le

end QRHShort.SecondPoissonProof
