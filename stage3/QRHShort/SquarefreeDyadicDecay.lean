import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Dyadic decay for the squarefree completed estimate.

An arbitrarily small positive power of `Z` replaces the logarithmic loss in
the unweighted dyadic sum.  The same argument with `s = 1 / 2` treats the
square-root term.  Both losses can subsequently be absorbed using `Z ≤ D^C`.
This module is independent of the arithmetic and reflection statements.
-/

noncomputable section
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly

theorem inverse_square_le_rpow {x r : ℝ} (hx : 0 < x)
    (hr : 0 ≤ r) (hr₂ : r ≤ 2) :
    (1 + x) ^ (-2 : ℝ) ≤ x ^ (-r) := by
  by_cases hx₁ : 1 ≤ x
  · exact (Real.rpow_le_rpow_of_nonpos hx (by linarith) (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith))
  · exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)).trans
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx
        (le_of_not_ge hx₁) (neg_nonpos.mpr hr))

theorem nat_pow_rpow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (r : ℝ) :
    (x ^ n) ^ r = (x ^ r) ^ n := by
  rw [← Real.rpow_natCast_mul hx, mul_comm (n : ℝ) r,
    Real.rpow_mul_natCast hx]

def dyadicDecay (s Z : ℝ) (p : ℕ × ℕ) : ℝ :=
  ((2 : ℝ) ^ p.1) ^ s *
    (1 + (2 : ℝ) ^ p.1 * (8 : ℝ) ^ p.2 / Z) ^ (-2 : ℝ)

theorem dyadicDecay_nonneg (s Z : ℝ) (hZ : 0 < Z) (p : ℕ × ℕ) :
    0 ≤ dyadicDecay s Z p := by
  unfold dyadicDecay
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)

theorem dyadicDecay_le_geometric {s δ Z : ℝ} (hs : 0 ≤ s)
    (hδ : 0 < δ) (hcap : s + δ ≤ 2) (hZ : 0 < Z) (p : ℕ × ℕ) :
    dyadicDecay s Z p ≤ Z ^ (s + δ) *
      (((2 : ℝ) ^ (-δ)) ^ p.1 * ((8 : ℝ) ^ (-(s + δ))) ^ p.2) := by
  let U : ℝ := (2 : ℝ) ^ p.1
  let B : ℝ := (8 : ℝ) ^ p.2
  have hU : 0 < U := by positivity
  have hB : 0 < B := by positivity
  have hdec := inverse_square_le_rpow (div_pos (mul_pos hU hB) hZ)
    (show 0 ≤ s + δ by linarith) hcap
  change U ^ s * (1 + U * B / Z) ^ (-2 : ℝ) ≤ _
  calc
    U ^ s * (1 + U * B / Z) ^ (-2 : ℝ) ≤
        U ^ s * (U * B / Z) ^ (-(s + δ)) :=
      mul_le_mul_of_nonneg_left hdec (Real.rpow_nonneg hU.le _)
    _ = (U ^ s * U ^ (-(s + δ))) * B ^ (-(s + δ)) * Z ^ (s + δ) := by
      rw [Real.div_rpow (mul_nonneg hU.le hB.le) hZ.le,
        Real.mul_rpow hU.le hB.le, Real.rpow_neg hZ.le, div_inv_eq_mul]
      ring
    _ = U ^ (-δ) * B ^ (-(s + δ)) * Z ^ (s + δ) := by
      rw [← Real.rpow_add hU, show s + -(s + δ) = -δ by ring]
    _ = Z ^ (s + δ) *
        (((2 : ℝ) ^ (-δ)) ^ p.1 * ((8 : ℝ) ^ (-(s + δ))) ^ p.2) := by
      dsimp [U, B]
      rw [nat_pow_rpow_comm (by norm_num), nat_pow_rpow_comm (by norm_num)]
      ring

/-- The constant depends only on the two exponents, uniformly for every `Z > 0`.
The statement includes absolute summability because every summand is nonnegative. -/
theorem dyadicDecay_sum_bound {s δ : ℝ} (hs : 0 ≤ s)
    (hδ : 0 < δ) (hcap : s + δ ≤ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℝ, 0 < Z →
      Summable (dyadicDecay s Z) ∧
        (∑' p : ℕ × ℕ, dyadicDecay s Z p) ≤ K * Z ^ (s + δ) := by
  let q : ℝ := (2 : ℝ) ^ (-δ)
  let r : ℝ := (8 : ℝ) ^ (-(s + δ))
  have hq₀ : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hr₀ : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hq₁ : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hδ)
  have hr₁ : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq := summable_geometric_of_lt_one hq₀ hq₁
  have hr := summable_geometric_of_lt_one hr₀ hr₁
  have hprod : Summable (fun p : ℕ × ℕ => q ^ p.1 * r ^ p.2) :=
    hq.mul_of_nonneg hr (fun n => pow_nonneg hq₀ n) (fun n => pow_nonneg hr₀ n)
  refine ⟨(1 - q)⁻¹ * (1 - r)⁻¹,
    mul_pos (inv_pos.mpr (sub_pos.mpr hq₁)) (inv_pos.mpr (sub_pos.mpr hr₁)), ?_⟩
  intro Z hZ
  have hmaj := hprod.mul_left (Z ^ (s + δ))
  have hle : ∀ p : ℕ × ℕ, dyadicDecay s Z p ≤
      Z ^ (s + δ) * (q ^ p.1 * r ^ p.2) :=
    dyadicDecay_le_geometric hs hδ hcap hZ
  have hsum : Summable (dyadicDecay s Z) :=
    hmaj.of_nonneg_of_le (dyadicDecay_nonneg s Z hZ) hle
  refine ⟨hsum, (Summable.tsum_le_tsum hle hsum hmaj).trans_eq ?_⟩
  rw [hprod.tsum_mul_left, ← hq.tsum_mul_tsum hr hprod,
    tsum_geometric_of_lt_one hq₀ hq₁, tsum_geometric_of_lt_one hr₀ hr₁]
  ring

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.inverse_square_le_rpow
#print axioms QRHShort.SquarefreeAssembly.dyadicDecay_sum_bound
