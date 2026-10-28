import QRHLean3.Definitions
import QRH.Powers

namespace QRHLean3

/-- Abstract uniform-height predicate, not a new analytic axiom.
`Bound J ε D H` may package other fixed parameters and support dependence. -/
def StageBound (Bound : ℕ → ℝ → ℝ → ℝ → Prop) (κ : ℝ)
    (j : ℕ) (ε : ℝ) (J : ℕ) : Prop :=
  ∀ D H : ℝ, 1 ≤ D → H ≤ D ^ ((j : ℝ) * κ) → Bound J ε D H

/-- I1: all chosen orders satisfy J ≥ 1. -/
theorem derivativeOrder_pos (cubeOrder : ℝ → ℕ) (j : ℕ) (ε : ℝ) :
    1 ≤ derivativeOrder cubeOrder j ε := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    exact le_trans (le_trans (by decide : 1 ≤ 12) (Nat.le_add_left 12 _))
      (le_max_right _ _)

/-- I2: dominate the cube-reduction order at ε/3. -/
theorem cube_order_le (cubeOrder : ℝ → ℕ) (j : ℕ) (ε : ℝ) :
    cubeOrder (ε / 3) ≤ derivativeOrder cubeOrder (j + 1) ε := by
  exact le_max_left _ _

/-- I3: dominate the transfer order 4m+12. -/
theorem transfer_order_le (cubeOrder : ℝ → ℕ) (j : ℕ) (ε : ℝ) :
    4 * derivativeOrder cubeOrder j (ε / 3) + 12 ≤
      derivativeOrder cubeOrder (j + 1) ε := by
  exact le_max_right _ _

/-- I4: finite induction with shrinking loss and growing derivative order.
This is an induction principle, not an assertion of the analytic step. -/
theorem derivative_induction (cubeOrder : ℝ → ℕ) (P : ℕ → ℝ → ℕ → Prop)
    (hbase : ∀ ε : ℝ, 0 < ε → P 0 ε 1)
    (hstep : ∀ (j : ℕ) (ε : ℝ) (m J : ℕ), 0 < ε → 1 ≤ J →
      cubeOrder (ε / 3) ≤ J → 4 * m + 12 ≤ J →
      P j (ε / 3) m → P (j + 1) ε J) :
    ∀ (j : ℕ) (ε : ℝ), 0 < ε → P j ε (derivativeOrder cubeOrder j ε) := by
  intro j
  induction j with
  | zero =>
    intro ε hε
    exact hbase ε hε
  | succ j ih =>
    intro ε hε
    exact hstep j ε (derivativeOrder cubeOrder j (ε / 3))
      (derivativeOrder cubeOrder (j + 1) ε) hε
      (derivativeOrder_pos cubeOrder (j + 1) ε)
      (cube_order_le cubeOrder j ε) (transfer_order_le cubeOrder j ε)
      (ih (ε / 3) (div_pos hε (by norm_num)))

/-- I5: conditional outer induction using the previously proved finite-stage cap.
Base and step remain hypotheses. The witness J is chosen before D and H. -/
theorem uniform_outer_induction {κ C : ℝ} (hκ : 0 < κ)
    (cubeOrder : ℝ → ℕ) (Bound : ℕ → ℝ → ℝ → ℝ → Prop)
    (hbase : ∀ ε : ℝ, 0 < ε → StageBound Bound κ 0 ε 1)
    (hstep : ∀ (j : ℕ) (ε : ℝ) (m J : ℕ), 0 < ε → 1 ≤ J →
      cubeOrder (ε / 3) ≤ J → 4 * m + 12 ≤ J →
      StageBound Bound κ j (ε / 3) m → StageBound Bound κ (j + 1) ε J) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 1 ≤ J ∧
      ∀ D H : ℝ, 1 ≤ D → H ≤ D ^ C → Bound J ε D H := by
  intro ε hε
  obtain ⟨j, _, hj⟩ := QRH.finite_stage_exists (C := C) hκ
  refine ⟨derivativeOrder cubeOrder j ε, derivativeOrder_pos cubeOrder j ε, ?_⟩
  intro D H hD hH
  exact derivative_induction cubeOrder (fun j ε J => StageBound Bound κ j ε J)
    hbase hstep j ε hε D H hD (hH.trans (hj D hD))

end QRHLean3
