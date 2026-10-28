import QRHShort.SecondPoissonCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The two uniform inverse-norm sums needed in a prepared dyadic block.
The existing number-field ideal count is reused without arithmetic restrictions. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

theorem prepared_inverse_norm_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (U : ℝ) (s : Finset (Ideal O)), 0 < U →
      (∀ n ∈ s, n ≠ ⊥ ∧ U ≤ normIdeal n ∧ normIdeal n ≤ 2 * U) →
      (∑ n ∈ s, (normIdeal n)⁻¹) ≤ B := by
  obtain ⟨A, hA, hcount⟩ := SecondPoissonProof.exists_ideal_count_constant
  refine ⟨2 * A, by positivity, ?_⟩
  intro U s hU hs
  have hsub : s ⊆ SecondPoissonProof.boundedIdeals (2 * U) := by
    intro n hn
    exact SecondPoissonProof.mem_boundedIdeals.mpr ⟨(hs n hn).2.2, (hs n hn).1⟩
  have hcard : (s.card : ℝ) ≤ A * (2 * U) := by
    have hc : (s.card : ℝ) ≤ (SecondPoissonProof.boundedIdeals (2 * U)).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hcount (2 * U) (by positivity))
  calc
    _ ≤ ∑ n ∈ s, U⁻¹ :=
      Finset.sum_le_sum (fun n hn => inv_anti₀ hU (hs n hn).2.1)
    _ = (s.card : ℝ) * U⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A * (2 * U)) * U⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hU.le)
    _ = 2 * A := by field_simp [ne_of_gt hU] <;> ring

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.prepared_inverse_norm_bound
