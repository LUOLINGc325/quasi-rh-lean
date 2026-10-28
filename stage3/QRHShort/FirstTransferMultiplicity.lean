import QRHShort.FirstTransferMultiplicityDomination
import QRHShort.FirstTransferFiniteModelConstruction

/-! Child M: the concrete finite model is dominated by the actual first form.
The row fibers have the proved D^ε bound, and the comparison with the infinite
first form uses its joint summability for every allowed smooth test. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_finite_reduction :
    FirstTransferFiniteReductionStatement := by
  intro C ε hC hε c I Φ cI _hrel hcI
  obtain ⟨K, hK, hfiber⟩ := first_transfer_admissible_fiber_bound C ε hC hε I Φ
  refine ⟨K, hK.le, ?_⟩
  intro ξ D H L F Sigma hD hrange
  have hH : 0 < H := zero_lt_one.trans_le hrange.1
  have hL : 0 < L := zero_lt_one.trans_le hrange.2.2.1
  have hF : 0 < F := zero_lt_one.trans_le hrange.2.2.2.2.1
  have hSigma : 0 < Sigma := zero_lt_one.trans_le hrange.2.2.2.2.2.2.1
  have hLF : L * F ≤ Sigma := (le_max_right H (L * F)).trans hrange.2.2.2.2.2.2.2.2
  have hcIpos : 0 < cI := zero_lt_one.trans_le ((le_max_left _ _).trans hcI)
  refine ⟨firstTransferConcreteModel c I Φ ξ (F := F) hH hL, ?_⟩
  intro U hU
  rw [firstTransferConcreteModel_quadratic_eq_sum_rows c I Φ ξ hH hL hU]
  let rows := firstTransferModelRows c I Φ H L F
  have hrow : ∀ r ∈ rows, firstTransferRowAdmissible c I Φ H L F r :=
    fun r hr => (first_transfer_bilinear_row_ranges_finite c I Φ H L F).mem_toFinset.mp hr
  let v : (Ideal O × Ideal O × Ideal O) × O → ℝ := fun p =>
    firstTransferFormSummand c I Φ ξ U cI H L F Sigma p.1 p.2
  have hv : ∀ p, 0 ≤ v p := fun p =>
    first_transfer_formSummand_nonneg c I Φ ξ U hcIpos.le hH.le hL.le hF.le hSigma.le p.1 p.2
  have hsum : Summable v :=
    firstForm_joint_summable c I (halfEnlarged I) Φ ξ hU hcIpos hH hL hF hSigma
  have hKD : 0 ≤ K * D ^ ε :=
    mul_nonneg hK.le (Real.rpow_nonneg (le_trans (by norm_num) hD) _)
  calc
    _ ≤ ∑ r ∈ rows, v (firstTransferRowImage r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact first_transfer_quadratic_row_le_formSummand c I Φ ξ U hcI hH hL hF hSigma
        hLF r (hrow r hr)
    _ ≤ (K * D ^ ε) * ∑' p, v p := by
      apply first_transfer_finset_image_sum_le rows firstTransferRowImage v
        (K * D ^ ε) hKD hv hsum
      intro p hp
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      have hcard :
          ((rows.filter (fun s => firstTransferRowImage s = firstTransferRowImage r)).card : ℝ) ≤
            (Nat.card (firstTransferFiber c (firstTransferRowImage r).2) : ℝ) := by
        exact_mod_cast first_transfer_row_fiber_card_le c I Φ H L F rows hrow r hr
      exact hcard.trans (hfiber c D H L F Sigma r hD hrange (hrow r hr))
    _ = K * D ^ ε * firstForm c I Φ ξ U cI H L F Sigma := by
      rw [firstForm_eq_joint_tsum c I (halfEnlarged I) Φ ξ hU hcIpos hH hL hF hSigma]

end QRHShort
