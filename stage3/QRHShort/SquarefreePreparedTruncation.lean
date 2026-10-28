import QRHShort.SquarefreePreparedStatements
import QRHShort.SquarefreePreparedLimits

/-! A finite analytic child of `PreparedThetaEstimateStep`.

The remaining estimate is for arbitrary finite subsets of the original
three-index series, with the original uniformity in the weight and coefficients.
Absolute convergence and passage to the mean square of the infinite series
are proved below and are not assumed as additional analytic inputs.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

/-- Finite-column analytic obligation. The derivative order precedes `S`, `I`,
and `L`, exactly as in the frozen prepared estimate. The bound is independent
of the finite subset, which may depend on all the displayed data. -/
def PreparedThetaTruncationEstimate : Prop :=
  ∀ ε C : ℝ, 0 < ε → 1 ≤ C → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (S : Finset (Ideal O)) (I : SupportInterval) (L : ℝ), 1 ≤ L →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (D H Y a : ℝ)
        (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ),
        SmoothSupported I W → 2 ≤ D → 1 ≤ H → H ≤ D ^ C →
        0 < Y → Y ≤ L * D ^ C → 0 ≤ a →
        (∀ r n b, ‖A r n b‖ ≤ a) →
        (∀ r k, k ∈ sieveRows S H → ‖coeff r k‖ ≤ 1) →
        ∀ t : Finset (ℕ × Ideal O × Ideal O),
          (∑ k ∈ sieveRows S H,
            ‖∑ q ∈ t, preparedThetaTerm W H Y A coeff k q‖ ^ 2) ≤
            K * D ^ ε * weightNorm J W ^ 2 * a ^ 2 * (H + Y)

/-- The unresolved finite analytic child has only the original four upstream
statements as premises. It does not assume the prepared estimate itself. -/
def PreparedThetaTruncationStep : Prop :=
  ThetaBoundsStatement → QuadraticEstimate → SmoothSeparationStatement →
    RecombinationStatement → PreparedThetaTruncationEstimate

theorem prepared_theta_estimate_of_truncation (h : PreparedThetaTruncationEstimate) :
    PreparedThetaEstimate := by
  intro ε C hε hC
  obtain ⟨J, hJ, hbound⟩ := h ε C hε hC
  refine ⟨J, hJ, ?_⟩
  intro S I L hL
  obtain ⟨K, hK, hbound⟩ := hbound S I L hL
  refine ⟨K, hK, ?_⟩
  intro W D H Y a A coeff hW hD hH hHC hY hYL ha hA hcoeff
  simpa only [preparedThetaRow] using
    prepared_rows_of_finite_bounds (sieveRows S H)
      (fun k q => preparedThetaTerm W H Y A coeff k q)
      (K * D ^ ε * weightNorm J W ^ 2 * a ^ 2 * (H + Y))
      (hbound W D H Y a A coeff hW hD hH hHC hY hYL ha hA hcoeff)

theorem prepared_theta_step_of_truncation (h : PreparedThetaTruncationStep) :
    PreparedThetaEstimateStep := by
  intro htheta hquadratic hseparation hrecombination
  exact prepared_theta_estimate_of_truncation
    (h htheta hquadratic hseparation hrecombination)

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.prepared_theta_estimate_of_truncation
#print axioms QRHShort.SquarefreeAssembly.prepared_theta_step_of_truncation
