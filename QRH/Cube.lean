import QRH.Definitions

namespace QRH

/-- A nonempty long branch forces the second branch of the cutoff minimum. -/
theorem active_cutoff {H X hc b : ℝ} (hH : 1 ≤ H) (hX : 1 ≤ X)
    (h : LongBranch H X hc b) :
    X < H ^ 2 ∧ hc ^ 3 = X ^ 2 / H ^ 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one h.b_one_le
  have hbcube : b ^ 3 < X := by
    simpa only [one_mul] using
      (lt_div_iff₀ (pow_pos hbpos 3)).mp h.column_gt_one
  have hccube : hc ^ 3 < b ^ 3 :=
    pow_lt_pow_left₀ h.above_cutoff h.hc_nonneg (by decide)
  have hmin : min X (X ^ 2 / H ^ 2) < X := by
    rw [← h.cutoff]
    exact hccube.trans hbcube
  have hsecond : X ^ 2 / H ^ 2 < X := by
    by_contra hn
    rw [min_eq_left (le_of_not_gt hn)] at hmin
    exact (lt_irrefl X) hmin
  have hactive : X < H ^ 2 := by
    apply (mul_lt_mul_iff_of_pos_left hXpos).mp
    simpa only [pow_two] using (div_lt_iff₀ (pow_pos hHpos 2)).mp hsecond
  exact ⟨hactive, h.cutoff.trans (min_eq_right hsecond.le)⟩

/-- The elementary range of the long-branch column scale. -/
theorem column_range {H X hc b : ℝ} (hX : 1 ≤ X)
    (h : LongBranch H X hc b) :
    1 < X / b ^ 3 ∧ X / b ^ 3 ≤ X := by
  refine ⟨h.column_gt_one, ?_⟩
  have hb : 1 ≤ b ^ 3 := one_le_pow₀ h.b_one_le
  exact div_le_self (le_trans zero_le_one hX) hb

/-- The cube-reduction supremum has no long-branch parameters in this case. -/
theorem no_long_branch {H X hc b : ℝ} (hH : 1 ≤ H) (hX : 1 ≤ X)
    (hshort : H ^ 2 ≤ X) : ¬ LongBranch H X hc b := by
  intro h
  exact (not_lt_of_ge hshort) (active_cutoff hH hX h).1

end QRH
