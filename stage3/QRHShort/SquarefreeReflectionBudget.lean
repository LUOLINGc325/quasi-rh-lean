import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The finite recombination and small-power accounting in
paper2.tex:2169--2186. This module has no arithmetic or analytic hypotheses. -/

noncomputable section
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly

theorem norm_sum_sq_le_card_sum (N : ℕ) (z : Fin N → ℂ) :
    ‖∑ i, z i‖ ^ 2 ≤ (N : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
  calc
    ‖∑ i, z i‖ ^ 2 ≤ (∑ i, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ (N : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _i : Fin N => (1 : ℝ)) (fun i : Fin N => ‖z i‖))

/-- One small-power loss for each of the two finite recombinations and
one for the prepared estimate. The conductor constant contributes a third
factor of `B`, but no additional power of `D`. Empty families are allowed. -/
theorem reflection_packet_budget (N : ℕ) (E : Fin N → ℝ)
    (F K B D w P δ : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hD : 0 < D) (hw : 0 ≤ w) (hP : 0 ≤ P)
    (hcover : F ≤ (N : ℝ) * ∑ i, E i)
    (hN : (N : ℝ) ≤ B * D ^ δ)
    (hE : ∀ i, E i ≤ K * D ^ δ * w * (B * P)) :
    F ≤ (K * B ^ 3) * D ^ (δ + δ + δ) * w * P := by
  have hQ : 0 ≤ K * D ^ δ * w * (B * P) := by positivity
  have hsum : (∑ i, E i) ≤ (N : ℝ) * (K * D ^ δ * w * (B * P)) := by
    calc
      (∑ i, E i) ≤ ∑ _i : Fin N, K * D ^ δ * w * (B * P) :=
        Finset.sum_le_sum (fun i _ => hE i)
      _ = _ := by simp
  calc
    F ≤ (N : ℝ) * ∑ i, E i := hcover
    _ ≤ (N : ℝ) * ((N : ℝ) * (K * D ^ δ * w * (B * P))) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ (B * D ^ δ) * ((B * D ^ δ) * (K * D ^ δ * w * (B * P))) :=
      mul_le_mul hN (mul_le_mul_of_nonneg_right hN hQ)
        (mul_nonneg (Nat.cast_nonneg _) hQ) (by positivity)
    _ = (K * B ^ 3) * D ^ (δ + δ + δ) * w * P := by
      rw [Real.rpow_add hD, Real.rpow_add hD]
      ring

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.norm_sum_sq_le_card_sum
#print axioms QRHShort.SquarefreeAssembly.reflection_packet_budget
