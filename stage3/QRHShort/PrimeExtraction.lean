import QRHLean3.Loss
import Mathlib.Analysis.Complex.Norm

/-!
Finite-family and exponent calculations from `paper2.tex:700–728`.
The index set is abstract: the arithmetic sixth-power rows, their comparison
estimate, the mean-square theorem, and the prime-ideal count remain explicit
hypotheses. This module does not prove these arithmetic inputs.
-/

open scoped BigOperators

namespace QRHShort

/-- PE1: the row comparison gives twice the average square plus twice the error square. -/
theorem finite_mean_square_extraction {ι : Type*} (P : Finset ι) (hP : P.Nonempty)
    (A₀ : ℂ) (A : ι → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (herror : ∀ p ∈ P, ‖A₀ - A p‖ ≤ R) :
    ‖A₀‖ ^ 2 ≤ (2 / (P.card : ℝ)) * (∑ p ∈ P, ‖A p‖ ^ 2) + 2 * R ^ 2 := by
  have hcard : 0 < (P.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hP)
  have hrow : ∀ p ∈ P, ‖A₀‖ ^ 2 ≤ 2 * ‖A p‖ ^ 2 + 2 * R ^ 2 := by
    intro p hp
    have htriangle : ‖A₀‖ ≤ ‖A p‖ + R := by
      calc
        ‖A₀‖ = ‖A p + (A₀ - A p)‖ := by congr 1; ring
        _ ≤ ‖A p‖ + ‖A₀ - A p‖ := norm_add_le _ _
        _ ≤ ‖A p‖ + R := add_le_add le_rfl (herror p hp)
    have hsquare : ‖A₀‖ ^ 2 ≤ (‖A p‖ + R) ^ 2 := by
      simpa only [sq] using mul_self_le_mul_self (norm_nonneg A₀) htriangle
    nlinarith only [hsquare, sq_nonneg (‖A p‖ - R)]
  have hsum := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hsum
  calc
    ‖A₀‖ ^ 2 ≤ (2 * (∑ p ∈ P, ‖A p‖ ^ 2) + (P.card : ℝ) * (2 * R ^ 2)) /
        (P.card : ℝ) := by
      apply (le_div_iff₀ hcard).2
      nlinarith only [hsum]
    _ = (2 / (P.card : ℝ)) * (∑ p ∈ P, ‖A p‖ ^ 2) + 2 * R ^ 2 := by
      field_simp [hcard.ne']
      <;> ring

/-- PE2: a lower bound for the number of rows converts the finite average into a power bound. -/
theorem prime_cardinality_extraction {ι : Type*} (P : Finset ι) (hP : P.Nonempty)
    (A₀ : ℂ) (A : ι → ℂ) {D Y c B K θ η : ℝ}
    (hD : 0 < D) (hY : 1 < Y) (hc : 0 < c) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (herror : ∀ p ∈ P, ‖A₀ - A p‖ ≤ B * D / Y)
    (hmean : (∑ p ∈ P, ‖A p‖ ^ 2) ≤ K * D ^ (2 + θ + η))
    (hcard : c * Y / Real.log Y ≤ (P.card : ℝ)) :
    ‖A₀‖ ^ 2 ≤ (2 * K / c) * D ^ (2 + θ + η) * Real.log Y / Y +
      2 * (B * D / Y) ^ 2 := by
  have hcardpos : 0 < (P.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hP)
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hcount : c * Y ≤ (P.card : ℝ) * Real.log Y :=
    (div_le_iff₀ hlog).mp hcard
  have hinv : 1 / (P.card : ℝ) ≤ Real.log Y / (c * Y) := by
    apply (div_le_div_iff₀ hcardpos (mul_pos hc hY0)).2
    simpa only [one_mul, mul_one, mul_comm] using hcount
  have hpow : 0 ≤ D ^ (2 + θ + η) := Real.rpow_nonneg hD.le _
  calc
    ‖A₀‖ ^ 2 ≤ (2 / (P.card : ℝ)) * (∑ p ∈ P, ‖A p‖ ^ 2) +
        2 * (B * D / Y) ^ 2 :=
      finite_mean_square_extraction P hP A₀ A (by positivity) herror
    _ ≤ (2 / (P.card : ℝ)) * (K * D ^ (2 + θ + η)) +
        2 * (B * D / Y) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hmean
        (div_nonneg (by norm_num) hcardpos.le)) le_rfl
    _ = (1 / (P.card : ℝ)) * (2 * K * D ^ (2 + θ + η)) +
        2 * (B * D / Y) ^ 2 := by ring
    _ ≤ (Real.log Y / (c * Y)) * (2 * K * D ^ (2 + θ + η)) +
        2 * (B * D / Y) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right hinv
        (mul_nonneg (mul_nonneg (by norm_num) hK) hpow)) le_rfl
    _ = (2 * K / c) * D ^ (2 + θ + η) * Real.log Y / Y +
        2 * (B * D / Y) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- PE3: substituting the sixth-root row scale produces the exponents in the paper. -/
theorem prime_power_identities {D : ℝ} (hD : 0 < D) (θ η : ℝ) :
    D ^ (2 + θ + 2 * η) / D ^ ((1 + θ) / 6) =
      D ^ ((11 : ℝ) / 6 + 5 * θ / 6 + 2 * η) ∧
    (D / D ^ ((1 + θ) / 6)) ^ (2 : ℕ) = D ^ ((5 : ℝ) / 3 - θ / 3) := by
  constructor
  · rw [← Real.rpow_sub hD]
    congr 1
    ring
  · calc
      (D / D ^ ((1 + θ) / 6)) ^ (2 : ℕ) =
          (D ^ (1 - (1 + θ) / 6)) ^ (2 : ℕ) := by
        rw [Real.rpow_sub hD, Real.rpow_one]
      _ = D ^ ((1 - (1 + θ) / 6) * 2) :=
        (Real.rpow_mul_natCast hD.le _ 2).symm
      _ = D ^ ((5 : ℝ) / 3 - θ / 3) := by congr 1; ring

/-- PE4: an explicit logarithmic loss, with its constant uniform in D. -/
theorem prime_log_loss {D θ η : ℝ} (hD : 0 < D) (hθ : 0 ≤ θ) (hη : 0 < η) :
    Real.log (D ^ ((1 + θ) / 6)) ≤ ((1 + θ) / (6 * η)) * D ^ η := by
  rw [Real.log_rpow hD]
  calc
    (1 + θ) / 6 * Real.log D ≤ (1 + θ) / 6 * (D ^ η / η) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hD.le hη) (by positivity)
    _ = (1 + θ) / (6 * η) * D ^ η := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- PE5: the finite prime-row model yields the pointwise 11/12 exponent with explicit loss. -/
theorem prime_rows_pointwise {ι : Type*} (P : Finset ι) (hP : P.Nonempty)
    (A₀ : ℂ) (A : ι → ℂ) {D c B K θ η : ℝ}
    (hD : 1 < D) (hc : 0 < c) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hθ : 0 ≤ θ) (hη : 0 < η)
    (herror : ∀ p ∈ P, ‖A₀ - A p‖ ≤ B * D / D ^ ((1 + θ) / 6))
    (hmean : (∑ p ∈ P, ‖A p‖ ^ 2) ≤ K * D ^ (2 + θ + η))
    (hcard : c * D ^ ((1 + θ) / 6) / Real.log (D ^ ((1 + θ) / 6)) ≤
      (P.card : ℝ)) :
    ‖A₀‖ ≤ Real.sqrt (2 * K * ((1 + θ) / (6 * η)) / c + 2 * B ^ 2) *
      D ^ ((11 : ℝ) / 12 + 5 * θ / 12 + η) := by
  have hD0 : 0 < D := zero_lt_one.trans hD
  have hY : 1 < D ^ ((1 + θ) / 6) := Real.one_lt_rpow hD (by positivity)
  have hY0 : 0 < D ^ ((1 + θ) / 6) := zero_lt_one.trans hY
  have hL : 0 ≤ (1 + θ) / (6 * η) := by positivity
  have hC : 0 ≤ 2 * K * ((1 + θ) / (6 * η)) / c + 2 * B ^ 2 := by positivity
  have hlog := prime_log_loss hD0 hθ hη
  have hpower := prime_power_identities hD0 θ η
  have hmain :
      (2 * K / c) * D ^ (2 + θ + η) * Real.log (D ^ ((1 + θ) / 6)) /
          D ^ ((1 + θ) / 6) ≤
        (2 * K * ((1 + θ) / (6 * η)) / c) *
          D ^ ((11 : ℝ) / 6 + 5 * θ / 6 + 2 * η) := by
    calc
      _ ≤ (2 * K / c) * D ^ (2 + θ + η) *
          (((1 + θ) / (6 * η)) * D ^ η) / D ^ ((1 + θ) / 6) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity)) hY0.le
      _ = (2 * K * ((1 + θ) / (6 * η)) / c) *
          (D ^ (2 + θ + 2 * η) / D ^ ((1 + θ) / 6)) := by
        have hcombine : D ^ (2 + θ + η) * D ^ η = D ^ (2 + θ + 2 * η) := by
          rw [← Real.rpow_add hD0]
          congr 1
          ring
        calc
          _ = (2 * K * ((1 + θ) / (6 * η)) / c) *
              ((D ^ (2 + θ + η) * D ^ η) / D ^ ((1 + θ) / 6)) := by ring
          _ = _ := by rw [hcombine]
      _ = _ := by rw [hpower.1]
  have herr : 2 * (B * D / D ^ ((1 + θ) / 6)) ^ 2 ≤
      (2 * B ^ 2) * D ^ ((11 : ℝ) / 6 + 5 * θ / 6 + 2 * η) := by
    calc
      _ = (2 * B ^ 2) * (D / D ^ ((1 + θ) / 6)) ^ (2 : ℕ) := by ring
      _ = (2 * B ^ 2) * D ^ ((5 : ℝ) / 3 - θ / 3) := by rw [hpower.2]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hD.le (by linarith)) (by positivity)
  have hbound := prime_cardinality_extraction P hP A₀ A hD0 hY hc hB hK
    herror hmean hcard
  have hsquare : ‖A₀‖ ^ 2 ≤
      (Real.sqrt (2 * K * ((1 + θ) / (6 * η)) / c + 2 * B ^ 2) *
        D ^ ((11 : ℝ) / 12 + 5 * θ / 12 + η)) ^ 2 := by
    calc
      ‖A₀‖ ^ 2 ≤ (2 * K * ((1 + θ) / (6 * η)) / c + 2 * B ^ 2) *
          D ^ ((11 : ℝ) / 6 + 5 * θ / 6 + 2 * η) := by
        calc
          _ ≤ _ := hbound.trans (add_le_add hmain herr)
          _ = _ := by ring
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt hC, ← Real.rpow_mul_natCast hD0.le]
        congr 2
        ring
  exact le_of_sq_le_sq hsquare (by positivity)

/-- PE6: theta and the mean-square loss can meet every requested positive exponent loss. -/
theorem arbitrarily_small_prime_losses {ε : ℝ} (hε : 0 < ε) :
    ∃ θ η : ℝ, 0 < θ ∧ θ ≤ (1 : ℝ) / 10 ∧ 0 < η ∧ 5 * θ / 12 + η ≤ ε := by
  refine ⟨min ((1 : ℝ) / 10) ε, ε / 2, ?_, min_le_left _ _, by positivity, ?_⟩
  · exact lt_min_iff.mpr ⟨by norm_num, hε⟩
  · have hsmall := min_le_right ((1 : ℝ) / 10) ε
    linarith

/-- PE7: the preceding model with a chosen loss implies the requested pointwise exponent. -/
theorem prime_rows_requested_loss {ι : Type*} (P : Finset ι) (hP : P.Nonempty)
    (A₀ : ℂ) (A : ι → ℂ) {D c B K θ η ε : ℝ}
    (hD : 1 < D) (hc : 0 < c) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hθ : 0 ≤ θ) (hη : 0 < η) (hloss : 5 * θ / 12 + η ≤ ε)
    (herror : ∀ p ∈ P, ‖A₀ - A p‖ ≤ B * D / D ^ ((1 + θ) / 6))
    (hmean : (∑ p ∈ P, ‖A p‖ ^ 2) ≤ K * D ^ (2 + θ + η))
    (hcard : c * D ^ ((1 + θ) / 6) / Real.log (D ^ ((1 + θ) / 6)) ≤
      (P.card : ℝ)) :
    ‖A₀‖ ≤ Real.sqrt (2 * K * ((1 + θ) / (6 * η)) / c + 2 * B ^ 2) *
      D ^ ((11 : ℝ) / 12 + ε) := by
  have hpoint := prime_rows_pointwise P hP A₀ A hD hc hB hK hθ hη
    herror hmean hcard
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hD.le (by linarith)) (Real.sqrt_nonneg _))

end QRHShort
