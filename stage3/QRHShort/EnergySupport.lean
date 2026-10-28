import QRHShort.FiniteSupport
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Convergence interfaces for the concrete energy sums. Compactly supported ideal
weights, element norm balls and dyadic ideal bands have finite support. Column,
row and outer ideal summability are separate conclusions; nonnegativity by itself
does not certify convergence of a totalized infinite sum.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem columnSum_summable {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (c : ArithmeticContext) (ξ : RayCharacter c)
    (X : ℝ) (hX : 0 < X) (k : O) (f : Ideal O) :
    Summable (fun n : Ideal O => if SquarefreeOutside c.S n then
      coefficient ξ.val n * sexticSymbol n k *
        sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / X)
      else 0) := by
  have hfinite := weighted_ideal_hasFiniteSupport (W := W) (D := X)
    (fun n => if SquarefreeOutside c.S n then
      coefficient ξ.val n * sexticSymbol n k *
        sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) else 0) I hW.2 hX
  apply summable_of_hasFiniteSupport
  simpa only [ite_mul, zero_mul] using hfinite

theorem excludedColumnSum_summable {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (c : ArithmeticContext) (ξ : RayCharacter c)
    (r : Ideal O) (X : ℝ) (hX : 0 < X) (k : O) (f : Ideal O) :
    Summable (fun n : Ideal O => if SquarefreeOutside c.S n ∧ IsRelPrime n r then
      coefficient ξ.val n * sexticSymbol n k *
        sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / X)
      else 0) := by
  have hfinite := weighted_ideal_hasFiniteSupport (W := W) (D := X)
    (fun n => if SquarefreeOutside c.S n ∧ IsRelPrime n r then
      coefficient ξ.val n * sexticSymbol n k *
        sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) else 0) I hW.2 hX
  apply summable_of_hasFiniteSupport
  simpa only [ite_mul, zero_mul] using hfinite

theorem rowEnergy_summable (column : O → ℂ) (H : ℝ) :
    Summable (fun k : O => if 0 < normElement k ∧ normElement k ≤ H then
      ‖column k‖ ^ 2 else 0) := by
  apply summable_of_hasFiniteSupport
  apply (finite_normElement_le H).subset
  intro k hk
  by_contra hnorm
  apply hk
  simp only [show ¬ (0 < normElement k ∧ normElement k ≤ H) from fun h => hnorm h.2,
    if_false]

theorem dyadic_ideal_summable (P : Ideal O → Prop) (F : ℝ) (v : Ideal O → ℝ) :
    Summable (fun f : Ideal O =>
      if P f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then v f else 0) := by
  apply summable_of_hasFiniteSupport
  apply (finite_normIdeal_le (2 * F)).subset
  intro f hf
  by_cases h : P f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F
  · exact h.2.2.le
  · exact False.elim (hf (if_neg h))

theorem energy_outer_summable (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (H X F : ℝ) :
    Summable (fun f : Ideal O =>
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => columnSum c ξ W X k f) H else 0) := by
  exact dyadic_ideal_summable (SquarefreeOutside c.S) F
    (fun f => rowEnergy (fun k => columnSum c ξ W X k f) H)

theorem excludedEnergy_outer_summable (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (r : Ideal O) (H X F : ℝ) :
    Summable (fun f : Ideal O =>
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => excludedColumnSum c ξ W r X k f) H else 0) := by
  exact dyadic_ideal_summable (SquarefreeOutside c.S) F
    (fun f => rowEnergy (fun k => excludedColumnSum c ξ W r X k f) H)

theorem rowEnergy_nonneg (column : O → ℂ) (H : ℝ) : 0 ≤ rowEnergy column H := by
  apply tsum_nonneg
  intro k
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem originalMeanSquare_nonneg (c : ArithmeticContext) (W : ℝ → ℂ) (D H : ℝ) :
    0 ≤ originalMeanSquare c W D H := by
  exact rowEnergy_nonneg (originalSum c W D) H

theorem energy_nonneg (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (H X F : ℝ) (hX : 0 ≤ X) (hF : 0 ≤ F) : 0 ≤ energy c ξ W H X F := by
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg hX hF))
  apply tsum_nonneg
  intro f
  split_ifs
  · exact rowEnergy_nonneg _ H
  · exact le_rfl

theorem excludedEnergy_nonneg (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (r : Ideal O) (H X F : ℝ) (hX : 0 ≤ X) (hF : 0 ≤ F) :
    0 ≤ excludedEnergy c ξ W r H X F := by
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg hX hF))
  apply tsum_nonneg
  intro f
  split_ifs
  · exact rowEnergy_nonneg _ H
  · exact le_rfl

theorem smoothedEnergy_nonneg (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : ℝ → ℝ) (W : ℝ → ℂ) (H L F : ℝ)
    (hΦ : ∀ x, 0 ≤ Φ x) (hL : 0 ≤ L) (hF : 0 ≤ F) :
    0 ≤ smoothedEnergy c ξ Φ W H L F := by
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg hL hF))
  apply tsum_nonneg
  intro f
  split_ifs
  · exact tsum_nonneg (fun k => mul_nonneg (hΦ _) (sq_nonneg _))
  · exact le_rfl

/-- The row weight need only be nonnegative on the nonnegative half-line,
which is the condition supplied by the manuscript's `RowWeight`. -/
theorem smoothedEnergy_nonneg_of_nonneg_on (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : ℝ → ℝ) (W : ℝ → ℂ) (H L F : ℝ)
    (hΦ : ∀ x, 0 ≤ x → 0 ≤ Φ x) (hH : 0 ≤ H) (hL : 0 ≤ L) (hF : 0 ≤ F) :
    0 ≤ smoothedEnergy c ξ Φ W H L F := by
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg hL hF))
  apply tsum_nonneg
  intro f
  split_ifs
  · apply tsum_nonneg
    intro k
    apply mul_nonneg (hΦ _ ?_) (sq_nonneg _)
    exact div_nonneg (Nat.cast_nonneg ((principal k).absNorm)) hH
  · exact le_rfl

end QRHShort
