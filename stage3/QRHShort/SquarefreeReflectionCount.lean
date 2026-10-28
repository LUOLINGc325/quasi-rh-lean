import QRHShort.FiniteSupport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! The small-power estimate for finitely many local choices per prime.
Only finiteness of bounded ideal-norm balls is needed. In particular this
does not import an unproved ideal divisor-counting estimate. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

theorem reflection_choices_small_power (a δ : ℝ) (ha : 1 ≤ a) (hδ : 0 < δ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ P : Finset (Ideal O),
      (∀ p ∈ P, 1 ≤ normIdeal p) →
      a ^ P.card ≤ B * (∏ p ∈ P, normIdeal p) ^ δ := by
  let small : Finset (Ideal O) := (finite_normIdeal_le (a ^ δ⁻¹)).toFinset
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  refine ⟨a ^ small.card, one_le_pow₀ ha, ?_⟩
  intro P hP
  have hterm : ∀ p ∈ P,
      a ≤ (if p ∈ small then a else 1) * normIdeal p ^ δ := by
    intro p hp
    by_cases hs : p ∈ small
    · rw [if_pos hs]
      exact le_mul_of_one_le_right ha0 (Real.one_le_rpow (hP p hp) hδ.le)
    · rw [if_neg hs, one_mul]
      have hn : ¬ normIdeal p ≤ a ^ δ⁻¹ := by simpa [small] using hs
      have h := Real.rpow_le_rpow (Real.rpow_nonneg ha0 δ⁻¹)
        (le_of_lt (lt_of_not_ge hn)) hδ.le
      simpa only [Real.rpow_inv_rpow ha0 hδ.ne'] using h
  have hfilter : (P.filter (fun p => p ∈ small)).card ≤ small.card :=
    Finset.card_le_card (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hweights : (∏ p ∈ P, if p ∈ small then a else 1) =
      a ^ (P.filter (fun p => p ∈ small)).card := by
    rw [← Finset.prod_filter, Finset.prod_const]
  calc
    a ^ P.card = ∏ _p ∈ P, a := (Finset.prod_const a).symm
    _ ≤ ∏ p ∈ P, (if p ∈ small then a else 1) * normIdeal p ^ δ :=
      Finset.prod_le_prod₀ (fun _ _ => ha0) hterm
    _ = a ^ (P.filter (fun p => p ∈ small)).card *
        (∏ p ∈ P, normIdeal p) ^ δ := by
      rw [Finset.prod_mul_distrib, hweights,
        Real.finsetProd_rpow P normIdeal (fun p hp => zero_le_one.trans (hP p hp)) δ]
    _ ≤ a ^ small.card * (∏ p ∈ P, normIdeal p) ^ δ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ha hfilter)
        (Real.rpow_nonneg (Finset.prod_nonneg (fun p hp => zero_le_one.trans (hP p hp))) δ)

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.reflection_choices_small_power
