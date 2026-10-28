import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Absorb the quadratic sieve's small power using one extra decay factor.
This is independent of the theta transform and of all arithmetic statements. -/

noncomputable section

namespace QRHShort.SquarefreeAssembly

theorem prepared_small_power_absorb {ε C : ℝ}
    (hε : 0 < ε) (hC : 1 ≤ C) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ L : ℝ, 1 ≤ L →
      ∃ M : ℝ, 0 ≤ M ∧
      ∀ D H U Y z : ℝ, 2 ≤ D → 1 ≤ H → H ≤ D ^ C →
        0 < U → 0 < Y → Y ≤ L * D ^ C → 0 ≤ z → U ≤ 81 * Y * z →
        (H * U) ^ σ * (1 + z) ^ (-2 : ℝ) ≤ M * D ^ ε := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let σ : ℝ := min (ε / (2 * C)) 1
  have hσ : 0 < σ := lt_min (div_pos hε (by positivity)) zero_lt_one
  have hσcap : σ ≤ 1 := min_le_right _ _
  have hexp : (2 * C) * σ ≤ ε := by
    have h := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (min_le_left (ε / (2 * C)) 1)
    dsimp [σ]
    nlinarith
  refine ⟨σ, hσ, hσcap, ?_⟩
  intro L hL
  refine ⟨(81 * L) ^ σ, by positivity, ?_⟩
  intro D H U Y z hD hH hHC hU hY hYL hz hUz
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpos : 0 < 1 + z := by positivity
  have hUz' : U ≤ 81 * (L * D ^ C) * (1 + z) := by
    calc
      U ≤ 81 * Y * z := hUz
      _ ≤ 81 * (L * D ^ C) * z :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hYL (by norm_num)) hz
      _ ≤ 81 * (L * D ^ C) * (1 + z) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hprod : H * U ≤ ((81 * L) * D ^ (2 * C)) * (1 + z) := by
    calc
      H * U ≤ D ^ C * (81 * (L * D ^ C) * (1 + z)) :=
        mul_le_mul hHC hUz' hU.le (Real.rpow_nonneg hDpos.le _)
      _ = ((81 * L) * (D ^ C * D ^ C)) * (1 + z) := by ring
      _ = _ := by rw [← Real.rpow_add hDpos, show C + C = 2 * C by ring]
  have hpow : (H * U) ^ σ ≤
      ((81 * L) ^ σ * D ^ ((2 * C) * σ)) * (1 + z) ^ σ := by
    apply (Real.rpow_le_rpow (mul_nonneg hHpos.le hU.le) hprod hσ.le).trans_eq
    rw [Real.mul_rpow (by positivity : 0 ≤ (81 * L) * D ^ (2 * C)) hzpos.le,
      Real.mul_rpow (by positivity : 0 ≤ 81 * L) (Real.rpow_nonneg hDpos.le _),
      ← Real.rpow_mul hDpos.le]
  have hdec : (1 + z) ^ σ * (1 + z) ^ (-2 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hzpos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  calc
    (H * U) ^ σ * (1 + z) ^ (-2 : ℝ) ≤
        (((81 * L) ^ σ * D ^ ((2 * C) * σ)) * (1 + z) ^ σ) *
          (1 + z) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hzpos.le _)
    _ = ((81 * L) ^ σ * D ^ ((2 * C) * σ)) *
        ((1 + z) ^ σ * (1 + z) ^ (-2 : ℝ)) := by ring
    _ ≤ ((81 * L) ^ σ * D ^ ((2 * C) * σ)) * 1 :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    _ ≤ (81 * L) ^ σ * D ^ ε := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (by positivity)

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.prepared_small_power_absorb
