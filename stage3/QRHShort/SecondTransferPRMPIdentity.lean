import QRHShort.SecondTransferPRMPCoefficients
import QRHShort.SecondTransferPRMPZero
import QRHShort.SecondTransferPRMPNativeRows

noncomputable section
open Classical
open scoped BigOperators
namespace QRHShort

private theorem second_transfer_prmp_raw_ite {α : Type*} [Zero α]
    (c : ArithmeticContext) (I : SupportInterval) (L : ℝ) (C t : Ideal O) (v : α) :
    (if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C*normIdeal t ≤ 2*I.hi*L then v else 0) =
      (if secondTransferPRMPAdmissible c I L C t then v else 0) := by
  by_cases ha : secondTransferPRMPAdmissible c I L C t
  · have hr : SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C*normIdeal t ≤ 2*I.hi*L := ha
    rw [ite_eq_left hr, ite_eq_left ha]
  · have hr : ¬(SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C*normIdeal t ≤ 2*I.hi*L) := ha
    rw [ite_eq_right hr, ite_eq_right ha]

set_option backward.isDefEq.respectTransparency false in
theorem second_transfer_prmp_sum_identity (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ)
    (cI H L F Sigma : ℝ)
    (hrow : ∀ C d t : Ideal O, secondTransferPRMPAdmissible c I L C t → d ∣ C →
      ((∑' y : O, Φ.value
          (normElement y / (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ (2 : ℕ)))) *
        ‖firstColumn c ξ C d t U (L / (normIdeal C * normIdeal t)) y‖ ^ (2 : ℕ) : ℝ) : ℂ) =
        secondPoissonZero c Φ U C t
          (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ (2 : ℕ)))
          (L / (normIdeal C * normIdeal t)) +
        secondPoissonDual c (halfEnlarged I) Φ U coeffs C d t
          (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ (2 : ℕ)))
          (L / (normIdeal C * normIdeal t))) :
    (firstForm c I Φ ξ U cI H L F Sigma : ℂ) =
      secondTransferPRMPZero c I Φ U cI H L F Sigma +
        secondTransferDual c I Φ U coeffs cI H L F Sigma := by
  have hreal := second_transfer_prmp_truncate_native (α := ℝ) c I L (fun C d t =>
    (H * normIdeal C / (normIdeal d * L ^ (2 : ℕ) * F)) *
      ∑' y : O, Φ.value
        (normElement y / (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ (2 : ℕ)))) *
          ‖firstColumn c ξ C d t U (L / (normIdeal C * normIdeal t)) y‖ ^ (2 : ℕ))
  have hdual := second_transfer_prmp_truncate_native (α := ℂ) c I L (fun C d t =>
    ((H * normIdeal C / (normIdeal d * L ^ (2 : ℕ) * F) : ℝ) : ℂ) *
      secondPoissonDual c (halfEnlarged I) Φ U coeffs C d t
        (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ (2 : ℕ)))
        (L / (normIdeal C * normIdeal t)))
  have hfirst : (firstForm c I Φ ξ U cI H L F Sigma : ℂ) =
      ((∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
        if secondTransferPRMPAdmissible c I L C t then
          ∑ d ∈ secondTransferPRMPBox I L, if d ∣ C then
            (H*normIdeal C/(normIdeal d*L^2*F))*
              ∑' y : O, Φ.value
                (normElement y/(cI*Sigma*L*F*normIdeal d/(H*normIdeal C^2)))*
                ‖firstColumn c ξ C d t U (L/(normIdeal C*normIdeal t)) y‖^2
          else 0 else 0 : ℝ) : ℂ) := by
    simpa only [firstForm, ← second_transfer_prmp_raw_ite] using
      congrArg Complex.ofReal hreal
  have hsecond : secondTransferDual c I Φ U coeffs cI H L F Sigma =
      ∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
        if secondTransferPRMPAdmissible c I L C t then
          ∑ d ∈ secondTransferPRMPBox I L, if d ∣ C then
            ((H*normIdeal C/(normIdeal d*L^2*F) : ℝ) : ℂ)*
              secondPoissonDual c (halfEnlarged I) Φ U coeffs C d t
                (cI*Sigma*L*F*normIdeal d/(H*normIdeal C^2))
                (L/(normIdeal C*normIdeal t))
          else 0 else 0 := by
    simpa only [secondTransferDual, ← second_transfer_prmp_raw_ite] using hdual
  rw [hfirst, hsecond]
  unfold secondTransferPRMPZero
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hadm : secondTransferPRMPAdmissible c I L C t
  · simp only [hadm, true_and, ite_true]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ C
    · simp only [hd, ite_true]
      push_cast
      have hrow_cast := hrow C d t hadm hd
      push_cast at hrow_cast
      rw [hrow_cast]
      ring
    · simp [hd]
  · simp [hadm]

end QRHShort
