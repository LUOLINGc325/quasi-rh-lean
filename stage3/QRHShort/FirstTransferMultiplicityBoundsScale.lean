import QRHShort.FirstTransferMultiplicityBoundsFiber
import QRHShort.FirstTransferFiniteSupportBilinear

/-!
The actual first-Poisson cutoff puts every nonzero row image inside a fixed
polynomial norm range. Applying the proved squarefree-fiber estimate gives the
uniform D^ε multiplicity bound under the frozen TransferRange conditions.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_admissible_image_ne_zero (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (H L F : ℝ) (r : FirstTransferRowIndex)
    (hr : firstTransferRowAdmissible c I Φ H L F r) :
    r.2.2 * primaryGenerator r.2.1 ^ 2 ≠ 0 :=
  first_transfer_fiber_image_ne_zero c hr.2.1.1.1 hr.2.2.1

/-- A coarse polynomial bound suffices because the divisor exponent can
be chosen arbitrarily small before the scales. -/
theorem first_transfer_admissible_image_norm_le (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) {D C H L F Sigma : ℝ}
    (hD : 0 < D) (hrange : TransferRange D C H L F Sigma)
    (r : FirstTransferRowIndex) (hr : firstTransferRowAdmissible c I Φ H L F r) :
    normElement (r.2.2 * primaryGenerator r.2.1 ^ 2) ≤
      (4 * Φ.fourierCap * I.hi ^ 2) * D ^ (4 * C) := by
  obtain ⟨hH, _, hL, hLD, hF, hFD, _, _, _⟩ := hrange
  have hcap : 0 < Φ.fourierCap := Φ.cap_pos
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hCpos := normIdeal_pos hr.1.1.1.1
  have hC1 := first_transfer_one_le_normIdeal hr.1.1.1.1
  have hdle := first_transfer_normIdeal_le_of_dvd hr.1.1.1.1 hr.1.2.2.2.2
  have hdle2 : normIdeal r.1.2.2 ≤ normIdeal r.1.1 ^ 2 := by
    nlinarith
  have hdH : normIdeal r.1.2.2 ≤ H * normIdeal r.1.1 ^ 2 :=
    hdle2.trans (le_mul_of_one_le_left (sq_nonneg _) hH)
  have hfreq : normElement r.2.2 ≤ Φ.fourierCap * I.hi ^ 2 * L ^ 2 := by
    apply hr.2.2.2.2.trans
    apply (div_le_iff₀ (mul_pos hHpos (pow_pos hCpos 2))).mpr
    exact mul_le_mul_of_nonneg_left hdH (by positivity)
  have hf : normIdeal r.2.1 ≤ 2 * F := hr.2.1.2.2.1.le
  have hn0 : 0 ≤ normElement r.2.2 := Nat.cast_nonneg _
  have hnf0 : 0 ≤ normIdeal r.2.1 := Nat.cast_nonneg _
  have hD0 : 0 ≤ D ^ C := Real.rpow_nonneg hD.le _
  have hLF : L * F ≤ (D ^ C) ^ (2 : ℕ) := by
    simpa only [pow_two] using mul_le_mul hLD hFD hF0 hD0
  have himage := first_transfer_frequency_image_le
    (show 0 ≤ Φ.fourierCap * I.hi ^ 2 by positivity) hL0 hF0 hn0 hnf0
    hfreq hf (le_refl (L * F))
  rw [first_transfer_fiber_image_norm c hr.2.1.1.1]
  calc
    normElement r.2.2 * normIdeal r.2.1 ^ 2 ≤
        (4 * Φ.fourierCap * I.hi ^ 2) * (L * F) ^ 2 := by
      convert himage using 1 <;> ring
    _ ≤ (4 * Φ.fourierCap * I.hi ^ 2) * ((D ^ C) ^ (2 : ℕ)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hL0 hF0) hLF 2) (by positivity)
    _ = (4 * Φ.fourierCap * I.hi ^ 2) * D ^ (4 * C) := by
      rw [← pow_mul, ← Real.rpow_mul_natCast hD.le]
      congr 2
      norm_num
      ring

/-- Uniform multiplicity of the actual row images. The constant is chosen
before the context, character, scales, and row; no arithmetic relation is
needed for this counting statement. -/
theorem first_transfer_admissible_fiber_bound (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε)
    (I : SupportInterval) (Φ : RowWeight) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ArithmeticContext) (D H L F Sigma : ℝ)
      (r : FirstTransferRowIndex), 2 ≤ D → TransferRange D C H L F Sigma →
      firstTransferRowAdmissible c I Φ H L F r →
      (Nat.card (firstTransferFiber c (r.2.2 * primaryGenerator r.2.1 ^ 2)) : ℝ) ≤
        K * D ^ ε := by
  have hA : 0 < 4 * C := mul_pos (by norm_num) (zero_lt_one.trans_le hC)
  have hB : 0 < 4 * Φ.fourierCap * I.hi ^ 2 :=
    mul_pos (mul_pos (by norm_num) Φ.cap_pos) (sq_pos_of_pos (I.lo_pos.trans_le I.ordered))
  obtain ⟨K, hK, hbound⟩ := first_transfer_fiber_bound_of_norm_le (4 * C)
    (4 * Φ.fourierCap * I.hi ^ 2) ε hA hB hε
  refine ⟨K, hK, ?_⟩
  intro c D H L F Sigma r hD hrange hr
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  exact hbound c D _ hDpos (first_transfer_admissible_image_ne_zero c I Φ H L F r hr)
    (first_transfer_admissible_image_norm_le c I Φ hDpos hrange r hr)

end QRHShort
