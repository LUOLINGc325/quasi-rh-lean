import QRHShort.SmoothSeparationCandidate2
import QRHShort.SmoothCutoffModes
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FinCases

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap RealInnerProductSpace
open MeasureTheory Classical
namespace QRHShort

lemma mellinMode_norm_one {d : ℕ} {x t : BoxSpace d} (hx : ∀ i, 0 < x i) :
    ‖mellinMode x t‖ = 1 := by
  unfold mellinMode
  rw [norm_prod]
  have hnorm (i : Fin d) : ‖(x i : ℂ) ^ (Complex.I * (t i : ℂ))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx i)]
    simp
  simp_rw [hnorm]
  simp

lemma mellinMode_continuous {d : ℕ} {x : BoxSpace d} (hx : ∀ i, 0 < x i) :
    Continuous (mellinMode x) := by
  unfold mellinMode
  apply continuous_finset_prod
  intro i hi
  apply Continuous.const_cpow
  · fun_prop
  · left
    exact (Complex.ofReal_ne_zero.mpr (hx i).ne')

lemma smooth_inv_integrable {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) :
    Integrable (fun t : BoxSpace d => separationCoefficient K t) := by
  let F := scaledLogSchwartzE hK
  have hFi : Integrable (fun u : ESpace d => (F u : ℂ)) := by
    exact F.integrable
  have hFti : Integrable (fun u : ESpace d => (𝓕 F) u) := by
    exact (𝓕 F).integrable
  have hcomp := (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_of_integrable hFti
  dsimp [F] at hcomp
  have hfun : (fun t : BoxSpace d => separationCoefficient K t) =
      (fun t : BoxSpace d => (𝓕 (scaledLogSchwartzE hK)) (WithLp.toLp 2 t : ESpace d)) := by
    funext t
    exact (separationCoefficient_eq_euclFourier hK t)
  rw [hfun]
  exact hcomp

end QRHShort

namespace QRHShort

lemma mellinMode_eq_phase {d : ℕ} {x t : BoxSpace d}
    (hx : ∀ i, 0 < x i) :
    mellinMode x t = Complex.exp
      (((2 * Real.pi * ⟪(WithLp.toLp 2 t : ESpace d),
        (WithLp.toLp 2 (fun i => Real.log (x i) / (2 * Real.pi)) : ESpace d)⟫ : ℝ) : ℂ) * Complex.I) := by
  unfold mellinMode
  have hprod : (∏ i : Fin d, (x i : ℂ) ^ (Complex.I * (t i : ℂ))) =
      ∏ i : Fin d, Complex.exp (((Real.log (x i) : ℂ) * (Complex.I * (t i : ℂ)))) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hx i).ne')]
    rw [← Complex.ofReal_log (hx i).le]
  rw [hprod, ← Complex.exp_sum]
  congr 1
  rw [inner_toLp]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [Real.pi_ne_zero] <;> ring

end QRHShort

namespace QRHShort

lemma scaledLogSchwartzE_logpoint {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) {x : BoxSpace d}
    (hx : ∀ i, 0 < x i) :
    scaledLogSchwartzE hK (WithLp.toLp 2
      (fun i => Real.log (x i) / (2 * Real.pi)) : ESpace d) = K x := by
  rw [scaledLogSchwartzE_apply hK]
  change logKernel K ((2 * Real.pi) •
    (WithLp.toLp 2 (fun i => Real.log (x i) / (2 * Real.pi)) : ESpace d)) = K x
  simp only [logKernel, Function.comp_apply, expCoordinates]
  apply congrArg K
  funext i
  simp only [expCoordinates, Pi.smul_apply]
  change Real.exp ((2 * Real.pi) * (Real.log (x i) / (2 * Real.pi))) = x i
  have hcancel : (2 * Real.pi) * (Real.log (x i) / (2 * Real.pi)) = Real.log (x i) := by
    field_simp [Real.pi_ne_zero]
  rw [hcancel, Real.exp_log (hx i)]

end QRHShort

namespace QRHShort

lemma smooth_separation_inversion {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) (x : BoxSpace d)
    (hx : ∀ i, 0 < x i) :
    Integrable (fun t => separationCoefficient K t * mellinMode x t) ∧
      K x = ∫ t : BoxSpace d, separationCoefficient K t * mellinMode x t := by
  let F := scaledLogSchwartzE hK
  let y : BoxSpace d := fun i => Real.log (x i) / (2 * Real.pi)
  let u0 : ESpace d := WithLp.toLp 2 y
  have hcoeff : Integrable (fun t : BoxSpace d => separationCoefficient K t) :=
    smooth_inv_integrable hK
  have hmodec : Continuous (mellinMode x) := mellinMode_continuous hx
  have hmode_norm : ∀ t : BoxSpace d, ‖mellinMode x t‖ ≤ (1 : ℝ) := by
    intro t
    rw [mellinMode_norm_one hx]
  have hint : Integrable (fun t : BoxSpace d =>
      mellinMode x t • separationCoefficient K t) :=
    hcoeff.bdd_smul 1 hmodec.aestronglyMeasurable
      (Filter.Eventually.of_forall hmode_norm)
  have hint' : Integrable (fun t : BoxSpace d =>
      separationCoefficient K t * mellinMode x t) := by
    simpa [smul_eq_mul, mul_comm] using hint
  refine ⟨hint', ?_⟩
  have hF : Continuous (fun u : ESpace d => (F u : ℂ)) := F.continuous
  have hFi : Integrable (fun u : ESpace d => (F u : ℂ)) := F.integrable
  have hFti : Integrable (fun u : ESpace d => ((𝓕 F) u : ℂ)) := (𝓕 F).integrable
  have hinv := hF.fourierInv_fourier_eq hFi hFti
  have hpoint := congrFun hinv u0
  rw [Real.fourierInv_eq'] at hpoint
  have hmap := (PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (BoxSpace d)).measurableEmbedding
      (fun u : ESpace d =>
        Complex.exp (((2 * Real.pi * ⟪u, u0⟫ : ℝ) : ℂ) * Complex.I) * (𝓕 F) u)
  have hmap' :
      (∫ t : BoxSpace d,
          Complex.exp (((2 * Real.pi * ⟪(WithLp.toLp 2 t : ESpace d), u0⟫ : ℝ) : ℂ) * Complex.I) *
            (𝓕 F) (WithLp.toLp 2 t : ESpace d)) =
        ∫ u : WithLp 2 (Fin d → ℝ),
          Complex.exp (((2 * Real.pi * ⟪u, u0⟫ : ℝ) : ℂ) * Complex.I) * (𝓕 F) u := by
    exact hmap
  have hA :
      (∫ t : BoxSpace d, separationCoefficient K t * mellinMode x t) =
        ∫ t : BoxSpace d,
          Complex.exp (((2 * Real.pi * ⟪(WithLp.toLp 2 t : ESpace d), u0⟫ : ℝ) : ℂ) * Complex.I) *
            (𝓕 F) (WithLp.toLp 2 t : ESpace d) := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [separationCoefficient_eq_euclFourier hK t]
    rw [mellinMode_eq_phase hx]
    simp [y, u0]
    ring
  have htrans :
      (∫ t : BoxSpace d, separationCoefficient K t * mellinMode x t) =
        ∫ u : WithLp 2 (Fin d → ℝ),
          Complex.exp (((2 * Real.pi * ⟪u, u0⟫ : ℝ) : ℂ) * Complex.I) * (𝓕 F) u :=
    hA.trans hmap'

  calc
    K x = F u0 := (scaledLogSchwartzE_logpoint hK hx).symm
    _ = ∫ u : WithLp 2 (Fin d → ℝ),
        Complex.exp (((2 * Real.pi * ⟪u, u0⟫ : ℝ) : ℂ) * Complex.I) * (𝓕 F) u := by
      have hFc : ∀ u : WithLp 2 (Fin d → ℝ), (𝓕 F) u =
          (𝓕 (fun v : WithLp 2 (Fin d → ℝ) => F v)) u := by
        intro u
        exact congrFun (SchwartzMap.fourier_coe F) u
      rw [← hpoint]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hFc]
      simp [smul_eq_mul]
    _ = ∫ t : BoxSpace d, separationCoefficient K t * mellinMode x t := htrans.symm

end QRHShort

namespace QRHShort

lemma logKernel_fourier_power_bound_generic_pos {d : ℕ} (hd : 0 < d)
    (I : Fin d → SupportInterval) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : BoxSpace d → ℂ, SmoothBox I K →
      ∀ t : BoxSpace d,
        ‖t‖ ^ q * ‖VectorFourier.fourierIntegral Real.fourierChar volume
          (logFourierPairing d).toLinearMap₁₂ (logKernel K) t‖ ≤
          C * multiWeightNorm q K := by
  classical
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨A, hA, hAb⟩ := logKernel_derivative_integral_bound d I q
  let C : ℝ := (2 * Real.pi) ^ q * 2 ^ q * (q + 1) * A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K hK t
  have hint (k n : ℕ) (hk : (k : ℕ∞) ≤ 0) (_hn : (n : ℕ∞) ≤ ⊤) :
      Integrable (fun y : BoxSpace d => ‖y‖ ^ k *
        ‖iteratedFDeriv ℝ n (logKernel K) y‖) := by
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (ENat.natCast_le_natCast.mp hk)
    subst k
    simpa only [pow_zero, one_mul] using logKernel_derivative_integrable hK n
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm t
  change ‖t i‖ = ‖t‖ at hi
  have hp := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (logFourierPairing d) (f := logKernel K) (K := 0) (N := ⊤)
    hK.contDiff_logKernel hint (k := 0) (n := q) (by simp) (by simp)
    (Pi.single i (2 * Real.pi)) t
  rw [logFourierPairing_single, ← Real.norm_eq_abs, hi] at hp
  have hp' : ‖t‖ ^ q * ‖VectorFourier.fourierIntegral Real.fourierChar volume
      (logFourierPairing d).toLinearMap₁₂ (logKernel K) t‖ ≤
      (2 * Real.pi) ^ q * 2 ^ q *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (q + 1),
          ∫ y : BoxSpace d, ‖y‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (logKernel K) y‖ := by
    simpa only [norm_iteratedFDeriv_zero, Pi.norm_single, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos),
      pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_add] using hp
  have hsum : (∑ p ∈ Finset.range 1 ×ˢ Finset.range (q + 1),
      ∫ y : BoxSpace d, ‖y‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (logKernel K) y‖) ≤
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
          ∫ y : BoxSpace d, ‖y‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (logKernel K) y‖ := hp'
    _ ≤ (2 * Real.pi) ^ q * 2 ^ q * ((q + 1) * (A * multiWeightNorm q K)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * multiWeightNorm q K := by dsimp [C]; ring

end QRHShort

namespace QRHShort

lemma separationCoefficient_pointwise_bound_generic_pos {d : ℕ} (hd : 0 < d)
    (I : Fin d → SupportInterval) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : BoxSpace d → ℂ, SmoothBox I K →
      ∀ t : BoxSpace d,
        (1 + ‖t‖) ^ q * ‖separationCoefficient K t‖ ≤ C * multiWeightNorm q K := by
  obtain ⟨A, hA, hAb⟩ := logKernel_derivative_integral_bound d I q
  obtain ⟨D, hD, hDb⟩ := logKernel_fourier_power_bound_generic_pos hd I q
  let Z : ℝ := ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(d : ℤ))‖
  let C : ℝ := Z * (2 ^ q * (A + D))
  have hZ : 0 ≤ Z := norm_nonneg _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K hK t
  let F : ℂ := VectorFourier.fourierIntegral Real.fourierChar volume
    (logFourierPairing d).toLinearMap₁₂ (logKernel K) t
  have hK0 := multiWeightNorm_nonneg hK q
  have h0 : ‖F‖ ≤ A * multiWeightNorm q K := by
    calc
      _ ≤ ∫ y : BoxSpace d, ‖logKernel K y‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm
          Real.fourierChar volume (logFourierPairing d).toLinearMap₁₂ (logKernel K) t
      _ ≤ A * multiWeightNorm q K := by
        simpa only [norm_iteratedFDeriv_zero] using hAb K hK 0 (Nat.zero_le q)
  have hq : ‖t‖ ^ q * ‖F‖ ≤ D * multiWeightNorm q K :=
    hDb K hK t
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

end QRHShort

namespace QRHShort

lemma separationCoefficient_continuous {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) :
    Continuous (separationCoefficient K) := by
  have hfun : separationCoefficient K =
      (fun t : BoxSpace d => (𝓕 (scaledLogSchwartzE hK))
        (WithLp.toLp 2 t : ESpace d)) := by
    funext t
    exact separationCoefficient_eq_euclFourier hK t
  rw [hfun]
  exact (𝓕 (scaledLogSchwartzE hK)).continuous.comp
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

lemma smooth_separation_weighted_pos {d : ℕ} (hd : 0 < d)
    (I : Fin d → SupportInterval) (J q : ℕ) (hqeven : Even q)
    (hJq : J + d < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : BoxSpace d → ℂ, SmoothBox I K →
      Integrable (fun t => ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) ∧
      (∫ t : BoxSpace d, ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) ≤
        C * multiWeightNorm q K := by
  obtain ⟨D, hD, hDb⟩ := separationCoefficient_pointwise_bound_generic_pos hd I q
  have hJlt : J < q := lt_of_le_of_lt (Nat.le_add_right J d) hJq
  have hnat : d < q - J := by omega
  have hcast : (J : ℝ) + (d : ℝ) < (q : ℝ) := by exact_mod_cast hJq
  have hr : (d : ℝ) < ((q : ℝ) - (J : ℝ)) := by linarith
  have hbracket : Integrable (fun t : BoxSpace d =>
      (1 + ‖t‖) ^ (-((q : ℝ) - (J : ℝ)))) := by
    apply integrable_one_add_norm
    simpa [Module.finrank_fin_fun] using hr
  let B : ℝ := ∫ t : BoxSpace d, (1 + ‖t‖) ^ (-((q : ℝ) - (J : ℝ)))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨D * B, mul_nonneg hD hB, ?_⟩
  intro K hK
  have hc : Continuous (separationCoefficient K) := separationCoefficient_continuous hK
  have hweight : Continuous (fun t : BoxSpace d =>
      ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) := by fun_prop
  have htarget : ∀ t : BoxSpace d,
      ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J ≤
        (D * multiWeightNorm q K) * (1 + ‖t‖) ^ (-((q : ℝ) - (J : ℝ))) := by
    intro t
    have hp := hDb K hK t
    have ha : 0 < 1 + ‖t‖ := by positivity
    have hpow : (1 + ‖t‖) ^ (-((q : ℝ) - (J : ℝ))) =
        ((1 + ‖t‖) ^ ((q : ℝ) - (J : ℝ)))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt ha)]
    have hpowsub : (1 + ‖t‖) ^ ((q : ℝ) - (J : ℝ)) =
        (1 + ‖t‖) ^ (q : ℝ) / (1 + ‖t‖) ^ (J : ℝ) := by
      rw [Real.rpow_sub ha]
    rw [hpow, hpowsub]
    have hden : 0 < (1 + ‖t‖) ^ q := by positivity
    have hquot : ‖separationCoefficient K t‖ ≤
        D * multiWeightNorm q K / (1 + ‖t‖) ^ q := by
      apply (le_div_iff₀ hden).mpr
      simpa [mul_comm] using hp
    calc
      _ ≤ (D * multiWeightNorm q K / (1 + ‖t‖) ^ q) * (1 + ‖t‖) ^ J :=
        mul_le_mul_of_nonneg_right hquot (by positivity)
      _ = (D * multiWeightNorm q K) *
          ((1 + ‖t‖) ^ J / (1 + ‖t‖) ^ q) := by ring
      _ = _ := by
        field_simp [ne_of_gt ha]
        rw [← Real.rpow_natCast (1 + ‖t‖) q, ← Real.rpow_natCast (1 + ‖t‖) J]
        ring
  let G : BoxSpace d → ℝ := fun t =>
    (D * multiWeightNorm q K) * (1 + ‖t‖) ^ (-((q : ℝ) - (J : ℝ)))
  have hG : Integrable G := hbracket.const_mul (D * multiWeightNorm q K)
  have hi : Integrable (fun t : BoxSpace d =>
      ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) :=
    hG.mono' hweight.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
        exact htarget t))
  refine ⟨hi, ?_⟩
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t : BoxSpace d => by positivity))
    hG (Filter.Eventually.of_forall htarget)
  calc
    _ ≤ ∫ t : BoxSpace d, G t := hmono
    _ = (D * multiWeightNorm q K) * B := by
      dsimp [G, B]
      rw [MeasureTheory.integral_const_mul]
    _ = (D * B) * multiWeightNorm q K := by ring

end QRHShort

namespace QRHShort

lemma smooth_separation_weighted_zero
    (I : Fin 0 → SupportInterval) (J q : ℕ) (hqeven : Even q)
    (hJq : J + 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : BoxSpace 0 → ℂ, SmoothBox I K →
      Integrable (fun t => ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) ∧
      (∫ t : BoxSpace 0, ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) ≤
        C * multiWeightNorm q K := by
  obtain ⟨A, hA, hAb⟩ := logKernel_derivative_integral_bound 0 I q
  have hvol : (volume : Measure (BoxSpace 0)).real Set.univ = 1 := by
    rw [show (volume : Measure (BoxSpace 0)) = Measure.dirac (default : BoxSpace 0) by
      change Measure.pi (fun i : Fin 0 => (volume : Measure ℝ)) = _
      apply Measure.pi_of_empty]
    simp [Measure.real_def]
  refine ⟨A, hA, ?_⟩
  intro K hK
  have hK0 := multiWeightNorm_nonneg hK q
  have hnormint : (∫ y : BoxSpace 0, ‖logKernel K y‖) ≤
      A * multiWeightNorm q K := by
    simpa only [norm_iteratedFDeriv_zero] using hAb K hK 0 (Nat.zero_le q)
  have hcoeff : ∀ t : BoxSpace 0, ‖separationCoefficient K t‖ ≤
      A * multiWeightNorm q K := by
    intro t
    rw [separationCoefficient_eq_logFourier]
    rw [norm_mul]
    simp
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (logFourierPairing 0).toLinearMap₁₂ (logKernel K) t).trans hnormint
  have hi : Integrable (fun t : BoxSpace 0 =>
      ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) :=
    Integrable.of_subsingleton
  refine ⟨hi, ?_⟩
  have hinter : (∫ t : BoxSpace 0,
      ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) =
      ‖separationCoefficient K (default : BoxSpace 0)‖ := by
    rw [MeasureTheory.integral_unique, hvol]
    simp only [one_smul]
    have hnorm0 : ∀ t : BoxSpace 0, ‖t‖ = 0 := by
      intro t
      apply norm_eq_zero.mpr
      exact Subsingleton.elim _ _
    simp [hnorm0]
    congr 1
  rw [hinter]
  simpa using hcoeff (default : BoxSpace 0)

end QRHShort

namespace QRHShort

lemma smooth_separation_statement_candidate : SmoothSeparationStatement := by
  intro d I
  constructor
  · intro K hK x hx
    exact smooth_separation_inversion hK x hx
  · intro J q hqeven hJq
    by_cases hd : d = 0
    · subst d
      exact smooth_separation_weighted_zero I J q hqeven hJq
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      exact smooth_separation_weighted_pos hdpos I J q hqeven hJq

#print axioms QRHShort.smooth_separation_statement_candidate

end QRHShort
