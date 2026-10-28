import QRHShort.SecondTransferPRMPAbsorb

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def secondTransferPRMPZero (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (cI H L F Sigma : ℝ) : ℂ :=
  ∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
    ∑ d ∈ secondTransferPRMPBox I L,
      if secondTransferPRMPAdmissible c I L C t ∧ d ∣ C then
        ((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
          secondPoissonZero c Φ U C t
            (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))
            (L / (normIdeal C * normIdeal t)) else 0

theorem second_transfer_prmp_zero_row_norm_le (c : ArithmeticContext) (Φ : RowWeight)
    (U : ℝ → ℂ) {K cI H L F Sigma : ℝ} (_hK : 0 ≤ K) (hcI : 0 < cI)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    {C d t : Ideal O} (hC : C ≠ ⊥) (hd : d ≠ ⊥) (ht : t ≠ ⊥)
    (hzero : ∀ Y ell : ℝ, 0 < Y → 0 < ell →
      ‖secondPoissonZero c Φ U C t Y ell‖ ≤ K * Y * ell * weightNorm 0 U ^ 2) :
    ‖((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
      secondPoissonZero c Φ U C t
        (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))
        (L / (normIdeal C * normIdeal t))‖ ≤
      (K * cI * Sigma * weightNorm 0 U ^ 2) * (normIdeal C ^ 2 * normIdeal t)⁻¹ := by
  have hNC := normIdeal_pos hC
  have hNd := normIdeal_pos hd
  have hNt := normIdeal_pos ht
  have hw : 0 ≤ H * normIdeal C / (normIdeal d * L ^ 2 * F) := by positivity
  have hY : 0 < cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2) := by positivity
  have hell : 0 < L / (normIdeal C * normIdeal t) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc
    _ ≤ (H * normIdeal C / (normIdeal d * L ^ 2 * F)) *
        (K * (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2)) *
          (L / (normIdeal C * normIdeal t)) * weightNorm 0 U ^ 2) :=
      mul_le_mul_of_nonneg_left (hzero _ _ hY hell) hw
    _ = _ := by
      have hs := second_transfer_prmp_zero_scale_identity hH hL hF hNC hNd hNt
        (Sigma := Sigma) (cI := cI)
      calc
        _ = K * weightNorm 0 U ^ 2 *
            ((H * normIdeal C / (normIdeal d * L ^ 2 * F)) *
              (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2)) *
                (L / (normIdeal C * normIdeal t))) := by ring
        _ = _ := by rw [hs]; ring

theorem second_transfer_prmp_zero_norm_le_mass (hp : SecondPoissonStatement)
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : ℝ → ℂ) (cI H L F Sigma : ℝ),
      SmoothSupported (halfEnlarged I) U → 0 < cI → 0 < H → 0 < L → 0 < F → 0 < Sigma →
      ‖secondTransferPRMPZero c I Φ U cI H L F Sigma‖ ≤
        (K * cI * Sigma * weightNorm 0 U ^ 2) * secondTransferPRMPMass I L := by
  obtain ⟨K, hK, hk⟩ := hp.2 (halfEnlarged I) Φ
  refine ⟨K, hK, ?_⟩
  intro U cI H L F Sigma hU hcI hH hL hF hSigma
  let A : ℝ := K * cI * Sigma * weightNorm 0 U ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpnt (C t d : Ideal O) (hC : C ∈ secondTransferPRMPBox I L)
      (ht : t ∈ secondTransferPRMPBox I L) :
      ‖if secondTransferPRMPAdmissible c I L C t ∧ d ∣ C then
        ((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
          secondPoissonZero c Φ U C t
            (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))
            (L / (normIdeal C * normIdeal t)) else 0‖ ≤
        A * (if d ∣ C then (normIdeal C ^ 2 * normIdeal t)⁻¹ else 0) := by
    have hNC := normIdeal_pos (mem_boundedDivisibleIdeals.mp hC).2.2
    have hNt := normIdeal_pos (mem_boundedDivisibleIdeals.mp ht).2.2
    by_cases hh : secondTransferPRMPAdmissible c I L C t ∧ d ∣ C
    · rw [ite_eq_left hh, ite_eq_left hh.2]
      exact second_transfer_prmp_zero_row_norm_le c Φ U hK hcI hH hL hF hSigma
        (mem_boundedDivisibleIdeals.mp hC).2.2
        (ne_zero_of_dvd_ne_zero (mem_boundedDivisibleIdeals.mp hC).2.2 hh.2)
        (mem_boundedDivisibleIdeals.mp ht).2.2
        (fun Y ell hY hell => hk c U C t Y ell hY hell hU)
    · rw [ite_eq_right hh, norm_zero]
      exact mul_nonneg hA (by split_ifs <;> positivity)
  unfold secondTransferPRMPZero
  calc
    _ ≤ ∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
        ∑ d ∈ secondTransferPRMPBox I L,
          A * (if d ∣ C then (normIdeal C ^ 2 * normIdeal t)⁻¹ else 0) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro C hC
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro t ht
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun d _ => hpnt C t d hC ht)
    _ = _ := by simp only [secondTransferPRMPMass, Finset.mul_sum, A]

end QRHShort
