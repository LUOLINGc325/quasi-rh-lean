import QRHShort.SecondPoissonStatements

noncomputable section

namespace QRHShort.SecondPoissonProof

theorem secondPoissonKernel_eq_zero_of_x₁_not_mem
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ) (Y ell : ℝ)
    (g e : Ideal O) (h : O) (x₁ x₂ : ℝ)
    (hU : SmoothSupported I U) (hx₁ : x₁ ∉ Set.Icc I.lo I.hi) :
    secondPoissonKernel Φ U Y ell g e h x₁ x₂ = 0 := by
  have hUx₁ : U x₁ = 0 := by
    by_contra hne
    exact hx₁ (hU.2 hne)
  simp [secondPoissonKernel, hUx₁]

theorem secondPoissonKernel_eq_zero_of_x₂_not_mem
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ) (Y ell : ℝ)
    (g e : Ideal O) (h : O) (x₁ x₂ : ℝ)
    (hU : SmoothSupported I U) (hx₂ : x₂ ∉ Set.Icc I.lo I.hi) :
    secondPoissonKernel Φ U Y ell g e h x₁ x₂ = 0 := by
  have hUx₂ : U x₂ = 0 := by
    by_contra hne
    exact hx₂ (hU.2 hne)
  simp [secondPoissonKernel, hUx₂]

theorem radialFourier_eq_zero_of_gt_fourierCap
    (Φ : RowWeight) {z : ℝ} (hz : Φ.fourierCap < z) :
    radialFourier (fun x => (Φ.value x : ℂ)) z = 0 := by
  have hz0 : 0 < z := lt_trans Φ.cap_pos hz
  by_contra hne
  have hbound := Φ.fourier_support ⟨hne, le_of_lt hz0⟩
  exact (not_lt_of_ge hbound.2) hz

theorem secondPoissonKernel_eq_zero_of_fourier_argument_gt_cap
    (Φ : RowWeight) (U : ℝ → ℂ) (Y ell : ℝ) (g e : Ideal O) (h : O)
    (x₁ x₂ : ℝ)
    (hcap : Φ.fourierCap <
      Y * normElement h * normIdeal g ^ (2 : ℕ) /
        (normIdeal e * ell ^ (2 : ℕ) * x₁ * x₂)) :
    secondPoissonKernel Φ U Y ell g e h x₁ x₂ = 0 := by
  simp [secondPoissonKernel,
    radialFourier_eq_zero_of_gt_fourierCap Φ hcap]

/-- The precise frequency cutoff in the frozen five-index dual sum. -/
theorem secondPoissonKernel_eq_zero_of_frequency_gt
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (Y ell : ℝ) (g e : Ideal O) (h : O) (x₁ x₂ : ℝ)
    (hY : 0 < Y) (hell : 0 < ell)
    (hg : 0 < normIdeal g) (he : 0 < normIdeal e)
    (hx₁ : x₁ ∈ Set.Icc I.lo I.hi) (hx₂ : x₂ ∈ Set.Icc I.lo I.hi)
    (hh : Φ.fourierCap * I.hi ^ (2 : ℕ) * ell ^ (2 : ℕ) * normIdeal e /
      (Y * normIdeal g ^ (2 : ℕ)) < normElement h) :
    secondPoissonKernel Φ U Y ell g e h x₁ x₂ = 0 := by
  have hx₁pos : 0 < x₁ := I.lo_pos.trans_le hx₁.1
  have hx₂pos : 0 < x₂ := I.lo_pos.trans_le hx₂.1
  have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
  have hprod : x₁ * x₂ ≤ I.hi ^ (2 : ℕ) := by
    simpa only [pow_two] using mul_le_mul hx₁.2 hx₂.2 hx₂pos.le hhi.le
  apply secondPoissonKernel_eq_zero_of_fourier_argument_gt_cap
  apply (lt_div_iff₀ (mul_pos (mul_pos (mul_pos he (pow_pos hell 2))
    hx₁pos) hx₂pos)).mpr
  have hfreq := (div_lt_iff₀ (mul_pos hY (pow_pos hg 2))).mp hh
  have hupper := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg Φ.cap_pos.le (mul_nonneg he.le (sq_nonneg ell)))
  nlinarith only [hfreq, hupper]

end QRHShort.SecondPoissonProof
