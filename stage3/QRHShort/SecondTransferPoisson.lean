import QRHShort.SecondTransferPRMPIdentity

noncomputable section
namespace QRHShort

/-- Sum the actual finite Poisson rows and bound their total zero mass. -/
theorem second_transfer_poisson_bound (hp : SecondPoissonStatement) :
    SecondTransferPoissonBound := by
  intro C ε q hC hε c I Φ cI hc hcI
  have hcI1 : 1 ≤ cI := (le_max_left _ _).trans hcI
  have hcI0 : 0 < cI := by linarith
  obtain ⟨B, hB, hb⟩ := second_transfer_prmp_uniform_coefficients hp c hc
  obtain ⟨Kz, hKz, hz⟩ := second_transfer_prmp_zero_norm_le_mass hp c I Φ
  obtain ⟨Km, hKm, hm⟩ := second_transfer_prmp_mass_absorb C ε I hC hε
  let K : ℝ := B + Kz*cI*Km
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro ξ U D H L F Sigma hU hD hrange
  rcases hrange with ⟨hH, hHD, hL, hLD, hF, hFD, hSigma, hSD, hlast⟩
  have hH0 : 0 < H := by linarith
  have hL0 : 0 < L := by linarith
  have hF0 : 0 < F := by linarith
  have hSigma0 : 0 < Sigma := by linarith
  obtain ⟨coeffs, hcoeffs, hmass, hrows⟩ := hb ξ
  have hBK : B ≤ K := by
    dsimp [K]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨coeffs, hcoeffs, hmass.trans hBK, ?_⟩
  have hrow (C d t : Ideal O) (ha : secondTransferPRMPAdmissible c I L C t) (hd : d ∣ C) :=
    hrows (halfEnlarged I) Φ U C d t
      (cI*Sigma*L*F*normIdeal d/(H*normIdeal C^2)) (L/(normIdeal C*normIdeal t))
      ha.1 ha.2.1 ha.2.2.1 hd
      (by have hNC := normIdeal_pos ha.1.1.1
          have hNd := normIdeal_pos (ne_zero_of_dvd_ne_zero ha.1.1.1 hd)
          positivity)
      (by have hNC := normIdeal_pos ha.1.1.1
          have hNt := normIdeal_pos ha.2.1.1.1
          positivity) hU
  have hid := second_transfer_prmp_sum_identity c I Φ ξ U coeffs cI H L F Sigma hrow
  have hw : weightNorm 0 U ^ 2 ≤ weightNorm q U ^ 2 :=
    pow_le_pow_left₀ (weightNorm_nonneg hU 0) (weightNorm_mono hU (Nat.zero_le q)) 2
  have hzero := hz U cI H L F Sigma hU hcI0 hH0 hL0 hF0 hSigma0
  have hpow : 0 ≤ D^ε := Real.rpow_nonneg (by linarith) _
  have hzero' : ‖secondTransferPRMPZero c I Φ U cI H L F Sigma‖ ≤
      K*D^ε*Sigma*weightNorm q U^2 := by
    calc
      _ ≤ (Kz*cI*Sigma*weightNorm 0 U^2)*secondTransferPRMPMass I L := hzero
      _ ≤ (Kz*cI*Sigma*weightNorm 0 U^2)*(Km*D^ε) :=
        mul_le_mul_of_nonneg_left (hm D L hD hL hLD) (by positivity)
      _ ≤ (Kz*cI*Sigma*weightNorm q U^2)*(Km*D^ε) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw (by positivity)) (by positivity)
      _ = (Kz*cI*Km)*D^ε*Sigma*weightNorm q U^2 := by ring
      _ ≤ K*D^ε*Sigma*weightNorm q U^2 := by
        have hcoef : Kz*cI*Km ≤ K := by dsimp [K]; linarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hpow) hSigma0.le)
          (sq_nonneg _)
  have hnorm : firstForm c I Φ ξ U cI H L F Sigma ≤
      ‖secondTransferPRMPZero c I Φ U cI H L F Sigma‖ +
        ‖secondTransferDual c I Φ U coeffs cI H L F Sigma‖ := by
    calc
      _ ≤ ‖(firstForm c I Φ ξ U cI H L F Sigma : ℂ)‖ := by
        simpa only [Complex.ofReal_re] using
          Complex.re_le_norm (firstForm c I Φ ξ U cI H L F Sigma : ℂ)
      _ = ‖secondTransferPRMPZero c I Φ U cI H L F Sigma +
          secondTransferDual c I Φ U coeffs cI H L F Sigma‖ := congrArg norm hid
      _ ≤ _ := norm_add_le _ _
  exact hnorm.trans (add_le_add hzero' le_rfl)

end QRHShort
