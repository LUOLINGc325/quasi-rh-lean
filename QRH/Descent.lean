import QRH.Cube
import QRH.Powers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace QRH

/-- The strict algebraic inequality displayed in the canonical-proof descent. -/
theorem transfer_strict_contraction {H X F hc b H' X' F' : ℝ}
    (hH : 1 ≤ H) (hX : 1 ≤ X) (hF : 1 ≤ F)
    (hb : LongBranch H X hc b) (ht : TransferBounds H X F b H' X' F') :
    H' < H * (H / (X * F)) ^ 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb.b_one_le
  have hcube : hc ^ 3 < b ^ 3 :=
    pow_lt_pow_left₀ hb.above_cutoff hb.hc_nonneg (by decide)
  have hcut := (active_cutoff hH hX hb).2
  have hcross : X ^ 2 < b ^ 3 * H ^ 2 := by
    exact (div_lt_iff₀ (sq_pos_of_pos hHpos)).mp (hcut ▸ hcube)
  have hcolumn : X / b ^ 3 < H ^ 2 / X := by
    apply (div_lt_div_iff₀ (pow_pos hbpos 3) hXpos).mpr
    nlinarith only [hcross]
  calc
    H' ≤ H * (X / b ^ 3) / ((X * F) * F) := ht.row_le
    _ < H * (H ^ 2 / X) / ((X * F) * F) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hcolumn hHpos) (by positivity)
    _ = H * (H / (X * F)) ^ 2 := by
      field_simp [ne_of_gt hXpos, ne_of_gt hFpos]
      <;> ring

/-- The transfer parameters satisfy the original canonical range and gap. -/
theorem transfer_preserves_range {D κ C H X F hc b H' X' F' : ℝ}
    (hp : ParentRange D κ C H X F) (hb : LongBranch H X hc b)
    (ht : TransferBounds H X F b H' X' F') :
    ParentRange D κ C H' X' F' := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hp.X_one_le
  have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hp.F_one_le
  have hX'pos : 0 < X' := lt_of_lt_of_le zero_lt_one ht.X_one_le
  have hF'pos : 0 < F' := lt_of_lt_of_le zero_lt_one ht.F_one_le
  have hX_le : X ≤ X * F := by
    simpa using mul_le_mul_of_nonneg_left hp.F_one_le hXpos.le
  have hratio : H / (X * F) ≤ D ^ (-κ) :=
    (div_le_iff₀ (mul_pos hXpos hFpos)).mpr (by simpa [mul_comm] using hp.gap)
  exact {
    H_one_le := ht.H_one_le
    X_one_le := ht.X_one_le
    F_one_le := ht.F_one_le
    product_le := ht.product_le.trans
      ((column_range hp.X_one_le hb).2.trans (hX_le.trans hp.product_le))
    gap := by
      simpa [mul_comm] using
        (div_le_iff₀ (mul_pos hX'pos hF'pos)).mp (ht.ratio_le.trans hratio) }

/-- The complete parameter step; no energy estimate is asserted here. -/
theorem canonical_parameter_step {D κ C H X F hc b H' X' F' : ℝ}
    (hD : 1 ≤ D) (hκ : 0 < κ) (j : ℕ)
    (hp : ParentRange D κ C H X F) (hb : LongBranch H X hc b)
    (ht : TransferBounds H X F b H' X' F')
    (hstage : H ≤ D ^ (((j : ℝ) + 1) * κ)) :
    H' < H * (H / (X * F)) ^ 2 ∧
    H * (H / (X * F)) ^ 2 ≤ D ^ (-2 * κ) * H ∧
    H' ≤ D ^ ((j : ℝ) * κ) ∧ ParentRange D κ C H' X' F' := by
  have hs := transfer_strict_contraction hp.H_one_le hp.X_one_le hp.F_one_le hb ht
  have hg := gap_square_bound hD hp.H_one_le hp.X_one_le hp.F_one_le hp.gap
  exact ⟨hs, hg, hs.le.trans (hg.trans (induction_power_bound hD hκ j hstage)),
    transfer_preserves_range hp hb ht⟩

end QRH
