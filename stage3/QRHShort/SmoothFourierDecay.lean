import QRHShort.SmoothLogCoordinates
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QRHShort

def logFourierPairing (d : ℕ) : BoxSpace d →L[ℝ] BoxSpace d →L[ℝ] ℝ :=
  (2 * Real.pi)⁻¹ • ∑ i : Fin d,
    (ContinuousLinearMap.proj i : BoxSpace d →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj i : BoxSpace d →L[ℝ] ℝ)

theorem logFourierPairing_apply (d : ℕ) (y t : BoxSpace d) :
    logFourierPairing d y t = (2 * Real.pi)⁻¹ * ∑ i : Fin d, y i * t i := by
  simp [logFourierPairing, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem logFourierPairing_single (d : ℕ) (i : Fin d) (t : BoxSpace d) :
    logFourierPairing d (Pi.single i (2 * Real.pi)) t = t i := by
  simp [logFourierPairing_apply, Pi.single_apply] <;>
    field_simp [Real.pi_ne_zero] <;> ring

theorem separationCoefficient_eq_logFourier {d : ℕ} (K : BoxSpace d → ℂ)
    (t : BoxSpace d) :
    separationCoefficient K t = ((2 * Real.pi : ℝ) : ℂ) ^ (-(d : ℤ)) *
      VectorFourier.fourierIntegral Real.fourierChar volume
        (logFourierPairing d).toLinearMap₁₂ (logKernel K) t := by
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  unfold separationCoefficient
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun y => ?_)
  have hphase : -2 * Real.pi * logFourierPairing d y t =
      -(∑ i : Fin d, t i * y i) := by
    rw [logFourierPairing_apply]
    simp_rw [mul_comm (t _) (y _)]
    field_simp [Real.pi_ne_zero]
    <;> ring
  change logKernel K y * Complex.exp (-Complex.I * ((∑ i : Fin d, t i * y i : ℝ) : ℂ)) =
    Complex.exp (((-2 * Real.pi * logFourierPairing d y t : ℝ) : ℂ) * Complex.I) *
      logKernel K y
  rw [hphase, Complex.ofReal_neg]
  rw [show -Complex.I * ((∑ i : Fin d, t i * y i : ℝ) : ℂ) =
    -((∑ i : Fin d, t i * y i : ℝ) : ℂ) * Complex.I by ring]
  exact mul_comm _ _

theorem logKernel_fourier_power_bound (I : Fin 2 → SupportInterval) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : BoxSpace 2 → ℂ, SmoothBox I K →
      ∀ t : BoxSpace 2,
        ‖t‖ ^ q * ‖VectorFourier.fourierIntegral Real.fourierChar volume
          (logFourierPairing 2).toLinearMap₁₂ (logKernel K) t‖ ≤
          C * multiWeightNorm q K := by
  classical
  obtain ⟨A, hA, hAb⟩ := logKernel_derivative_integral_bound 2 I q
  let C : ℝ := (2 * Real.pi) ^ q * 2 ^ q * (q + 1) * A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K hK t
  have hint (k n : ℕ) (hk : (k : ℕ∞) ≤ 0) (_hn : (n : ℕ∞) ≤ ⊤) :
      Integrable (fun y : BoxSpace 2 => ‖y‖ ^ k *
        ‖iteratedFDeriv ℝ n (logKernel K) y‖) := by
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (ENat.natCast_le_natCast.mp hk)
    subst k
    simpa only [pow_zero, one_mul] using logKernel_derivative_integrable hK n
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm t
  change ‖t i‖ = ‖t‖ at hi
  have hp := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (logFourierPairing 2) (f := logKernel K) (K := 0) (N := ⊤)
    hK.contDiff_logKernel hint (k := 0) (n := q) (by simp) (by simp)
    (Pi.single i (2 * Real.pi)) t
  rw [logFourierPairing_single, ← Real.norm_eq_abs, hi] at hp
  have hp' : ‖t‖ ^ q * ‖VectorFourier.fourierIntegral Real.fourierChar volume
      (logFourierPairing 2).toLinearMap₁₂ (logKernel K) t‖ ≤
      (2 * Real.pi) ^ q * 2 ^ q *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (q + 1),
          ∫ y : BoxSpace 2, ‖y‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (logKernel K) y‖ := by
    simpa only [norm_iteratedFDeriv_zero, Pi.norm_single, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos),
      pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_add] using hp
  have hsum : (∑ p ∈ Finset.range 1 ×ˢ Finset.range (q + 1),
      ∫ y : BoxSpace 2, ‖y‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (logKernel K) y‖) ≤
      (q + 1) * (A * multiWeightNorm q K) := by
    calc
      _ ≤ ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (q + 1), A * multiWeightNorm q K := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : p.1 = 0 := Nat.eq_zero_of_le_zero
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hp).1))
        have hpq : p.2 ≤ q := Nat.lt_succ_iff.mp
          (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
        simpa only [hp0, pow_zero, one_mul] using hAb K hK p.2 hpq
      _ = _ := by simp
  calc
    _ ≤ (2 * Real.pi) ^ q * 2 ^ q *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (q + 1),
          ∫ y : BoxSpace 2, ‖y‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (logKernel K) y‖ := hp'
    _ ≤ (2 * Real.pi) ^ q * 2 ^ q * ((q + 1) * (A * multiWeightNorm q K)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * multiWeightNorm q K := by dsimp [C]; ring

theorem separationCoefficient_pointwise_bound (I : Fin 2 → SupportInterval) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : BoxSpace 2 → ℂ, SmoothBox I K →
      ∀ t : BoxSpace 2,
        (1 + ‖t‖) ^ q * ‖separationCoefficient K t‖ ≤ C * multiWeightNorm q K := by
  obtain ⟨A, hA, hAb⟩ := logKernel_derivative_integral_bound 2 I q
  obtain ⟨D, hD, hDb⟩ := logKernel_fourier_power_bound I q
  let Z : ℝ := ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(2 : ℤ))‖
  let C : ℝ := Z * (2 ^ q * (A + D))
  have hZ : 0 ≤ Z := norm_nonneg _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K hK t
  let F : ℂ := VectorFourier.fourierIntegral Real.fourierChar volume
    (logFourierPairing 2).toLinearMap₁₂ (logKernel K) t
  have hK0 := multiWeightNorm_nonneg hK q
  have h0 : ‖F‖ ≤ A * multiWeightNorm q K := by
    calc
      _ ≤ ∫ y : BoxSpace 2, ‖logKernel K y‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm
          Real.fourierChar volume (logFourierPairing 2).toLinearMap₁₂ (logKernel K) t
      _ ≤ A * multiWeightNorm q K := by
        simpa only [norm_iteratedFDeriv_zero] using hAb K hK 0 (Nat.zero_le q)
  have hq : ‖t‖ ^ q * ‖F‖ ≤ D * multiWeightNorm q K := hDb K hK t
  have hw : (1 + ‖t‖) ^ q * ‖F‖ ≤ (2 ^ q * (A + D)) * multiWeightNorm q K := by
    by_cases ht : ‖t‖ ≤ 1
    · calc
        _ ≤ 2 ^ q * ‖F‖ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) q) (norm_nonneg _)
        _ ≤ 2 ^ q * (A * multiWeightNorm q K) :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
        _ ≤ 2 ^ q * ((A + D) * multiWeightNorm q K) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hK0) (by positivity)
        _ = _ := by ring
    · have ht' : 1 ≤ ‖t‖ := (lt_of_not_ge ht).le
      calc
        _ ≤ (2 * ‖t‖) ^ q * ‖F‖ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) q) (norm_nonneg _)
        _ = 2 ^ q * (‖t‖ ^ q * ‖F‖) := by rw [mul_pow, mul_assoc]
        _ ≤ 2 ^ q * (D * multiWeightNorm q K) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ 2 ^ q * ((A + D) * multiWeightNorm q K) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hK0) (by positivity)
        _ = _ := by ring
  rw [separationCoefficient_eq_logFourier, norm_mul]
  calc
    _ = Z * ((1 + ‖t‖) ^ q * ‖F‖) := by dsimp [Z, F]; ring
    _ ≤ Z * ((2 ^ q * (A + D)) * multiWeightNorm q K) :=
      mul_le_mul_of_nonneg_left hw hZ
    _ = C * multiWeightNorm q K := by dsimp [C]; ring

theorem separationCoefficient_uniform_row_bound (I : Fin 2 → SupportInterval) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℕ) (K : Fin R → BoxSpace 2 → ℂ),
      (∀ r, SmoothBox I (K r)) → ∀ r t,
        ‖separationCoefficient (K r) t‖ ≤
          C * QRHLean3.supZero {v | ∃ r : Fin R, v = multiWeightNorm q (K r)} /
            (1 + ‖t‖) ^ q := by
  obtain ⟨C, hC, hCb⟩ := separationCoefficient_pointwise_bound I q
  refine ⟨C, hC, ?_⟩
  intro R K hK r t
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖t‖) ^ q)).mpr
  calc
    _ = (1 + ‖t‖) ^ q * ‖separationCoefficient (K r) t‖ := mul_comm _ _
    _ ≤ C * multiWeightNorm q (K r) := hCb (K r) (hK r) t
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_row_multiWeightNorm q K r) hC

end QRHShort

#print axioms QRHShort.separationCoefficient_eq_logFourier
#print axioms QRHShort.separationCoefficient_pointwise_bound
#print axioms QRHShort.separationCoefficient_uniform_row_bound
