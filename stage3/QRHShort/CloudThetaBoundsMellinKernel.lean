import QRHShort.ThetaBoundsReduction
import QRHShort.WeightNorm
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Bounds for the literal theta Mellin kernel. Gamma estimates below are
adapted from the read-only upstream beta-integral argument. The reciprocal
Gamma recurrence is global, including the totalized Gamma zeros at its poles. -/

noncomputable section
open scoped BigOperators FourierTransform ContDiff
open Classical MeasureTheory Filter Set

namespace QRHShort.CloudBatch
open ThetaBoundsProof

def gammaMultiplier (s : ℂ) : ℂ :=
  Complex.Gamma ((7 / 6 : ℂ) + s) * Complex.Gamma ((5 / 6 : ℂ) + s) /
    (Complex.Gamma ((7 / 6 : ℂ) - s) * Complex.Gamma ((5 / 6 : ℂ) - s))


theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

def realBeta (a b : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)

theorem realBeta_nonneg (a b : ℝ) : 0 ≤ realBeta a b := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem gammaMultiplier_left_bound (t : ℝ) :
    ‖gammaMultiplier ((-(1 / 4) : ℝ) + t * Complex.I)‖ ≤
      (Real.Gamma (11 / 12) / Real.Gamma (17 / 12)) *
      (Real.Gamma (7 / 12) / Real.Gamma (13 / 12)) := by
  have h1 := Gamma_shifted_pair_bound (7 / 6) (-(1 / 4)) t 0 (by norm_num) (by norm_num)
  have h2 := Gamma_shifted_pair_bound (5 / 6) (-(1 / 4)) t 0 (by norm_num) (by norm_num)
  norm_num only [Nat.cast_zero, add_zero, show (7 / 6 : ℝ) + -(1 / 4) = 11 / 12 by norm_num,
    show (7 / 6 : ℝ) - -(1 / 4) = 17 / 12 by norm_num,
    show (5 / 6 : ℝ) + -(1 / 4) = 7 / 12 by norm_num,
    show (5 / 6 : ℝ) - -(1 / 4) = 13 / 12 by norm_num] at h1 h2
  have heq : gammaMultiplier ((-(1 / 4) : ℝ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + ((-(1 / 4) : ℝ) + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - ((-(1 / 4) : ℝ) + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + ((-(1 / 4) : ℝ) + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - ((-(1 / 4) : ℝ) + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 11 / 12)).le
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 17 / 12)).le)

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod₀
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤
        C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤
      B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring

theorem gammaMultiplier_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6) (by norm_num) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6) (by norm_num) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : gammaMultiplier ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega


/-- Compact derivative bounds for a fixed smooth map. The derivative order
is an input; its choice does not depend on the compact set. -/
theorem mellin_compact_derivative_bounds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : ContDiff ℝ ∞ f)
    (K : Set ℝ) (hK : IsCompact K) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ B := by
    obtain ⟨B,hB⟩ := hK.bddAbove_image
      ((hf.continuous_iteratedFDeriv (by simp)).norm.continuousOn)
    refine ⟨max 0 B,le_max_left _ _,?_⟩
    intro x hx
    exact (hB (Set.mem_image_of_mem _ hx)).trans (le_max_right _ _)
  choose B hB hbound using hb
  let D := 1 + ∑ i ∈ Finset.range (n+1), B i
  have hs : 0 ≤ ∑ i ∈ Finset.range (n+1), B i := Finset.sum_nonneg (fun i _ => hB i)
  refine ⟨D,by dsimp [D]; linarith,?_⟩
  intro i hi x hx
  have hsingle : B i ≤ ∑ k ∈ Finset.range (n+1), B k :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_range.mpr (by omega))
  exact (hbound i x hx).trans (by dsimp [D]; linarith)

def mellinLogFamily (V : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  (Real.exp (-σ*u) : ℂ) * V (Real.exp (-u))

theorem mellin_logFamily_smooth {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (σ : ℝ) : ContDiff ℝ ∞ (mellinLogFamily V σ) := by
  unfold mellinLogFamily
  exact ((Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp))).mul
    (hV.1.comp (contDiff_neg.exp))

theorem mellin_logFamily_support {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log I.hi) (-Real.log I.lo) := by
  intro x hx
  have hv : V (Real.exp (-x)) ≠ 0 := (mul_ne_zero_iff.mp hx).2
  have hh := hV.2 hv
  have hlo := Real.log_le_log I.lo_pos hh.1
  have hhi := Real.log_le_log (Real.exp_pos (-x)) hh.2
  simp only [Real.log_exp] at hlo hhi
  constructor <;> linarith

theorem mellin_logFamily_compact {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (σ : ℝ) : HasCompactSupport (mellinLogFamily V σ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (mellin_logFamily_support hV σ)

/-- The logarithmic pullback has its n-th derivative controlled by the same
order n of the original compactly supported weight, uniformly over weights. -/
theorem mellin_logFamily_derivative_bound (I : SupportInterval) (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℂ), SmoothSupported I V →
      ∀ x ∈ Set.Icc (-Real.log I.hi) (-Real.log I.lo),
        ‖iteratedDeriv n (mellinLogFamily V σ) x‖ ≤ C * weightNorm n V := by
  let K := Set.Icc (-Real.log I.hi) (-Real.log I.lo)
  have hf : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (-x)) := contDiff_neg.exp
  have hg : ContDiff ℝ ∞ (fun x : ℝ => (Real.exp (-σ*x) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)
  obtain ⟨D,hD,hd⟩ := mellin_compact_derivative_bounds _ hf K isCompact_Icc n
  obtain ⟨B,hB,hb⟩ := mellin_compact_derivative_bounds _ hg K isCompact_Icc n
  let Q : ℝ := ∑ k ∈ Finset.range (n+1), (k.factorial : ℝ) * D ^ k
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let C : ℝ := ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * B * Q
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro V hV x hx
  have hN : 0 ≤ weightNorm n V := weightNorm_nonneg hV n
  have hcomp (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun x : ℝ => V (Real.exp (-x))) x‖ ≤ Q * weightNorm n V := by
    have hc := norm_iteratedFDeriv_comp_le hV.1 hf (by simp : (i : ℕ∞ω) ≤ ∞) x
      (C := weightNorm n V) (D := D)
      (fun k hk => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact norm_iteratedDeriv_le_weightNorm hV (hk.trans hi) _)
      (fun k hk hki => (hd k (hki.trans hi) x hx).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ hD hk))
    have hsingle : (i.factorial : ℝ) * D ^ i ≤ Q :=
      Finset.single_le_sum (f := fun k : ℕ => (k.factorial : ℝ) * D ^ k)
        (fun k _ => by positivity) (Finset.mem_range.mpr (by omega))
    apply hc.trans
    calc
      (i.factorial : ℝ) * weightNorm n V * D ^ i =
          ((i.factorial : ℝ) * D ^ i) * weightNorm n V := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsingle hN
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hm := norm_iteratedFDeriv_mul_le hg (hV.1.comp hf) x (n := n) (by simp)
  apply hm.trans
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * B * (Q * weightNorm n V) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) x hx)
          (Nat.cast_nonneg _)) (hcomp (n-k) (Nat.sub_le _ _))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hB))
    _ = ∑ k ∈ Finset.range (n+1), ((n.choose k : ℝ) * B * Q) * weightNorm n V := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = C * weightNorm n V := (Finset.sum_mul _ _ _).symm

theorem mellin_tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- Genuine integrability and the same-order L1 derivative bound. -/
theorem mellin_logFamily_derivative_L1 (I : SupportInterval) (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℂ), SmoothSupported I V →
      Integrable (iteratedDeriv n (mellinLogFamily V σ)) ∧
      (∫ x : ℝ, ‖iteratedDeriv n (mellinLogFamily V σ) x‖) ≤ C * weightNorm n V := by
  obtain ⟨B,hB,hbound⟩ := mellin_logFamily_derivative_bound I σ n
  let K := Set.Icc (-Real.log I.hi) (-Real.log I.lo)
  refine ⟨volume.real K * B,mul_nonneg ENNReal.toReal_nonneg hB,?_⟩
  intro V hV
  have hs := mellin_logFamily_smooth hV σ
  have hc (k : ℕ) : HasCompactSupport (iteratedDeriv k (mellinLogFamily V σ)) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using mellin_logFamily_compact hV σ
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  refine ⟨(hs.continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport (hc n),?_⟩
  have hsupport : Function.support (iteratedDeriv n (mellinLogFamily V σ)) ⊆ K :=
    (subset_tsupport _).trans ((mellin_tsupport_iteratedDeriv_subset _ n).trans
      (closure_minimal (mellin_logFamily_support hV σ) isClosed_Icc))
  have hz : ∀ x, x ∉ K → ‖iteratedDeriv n (mellinLogFamily V σ) x‖ = 0 := by
    intro x hx
    have hh : iteratedDeriv n (mellinLogFamily V σ) x = 0 := by
      by_contra hh
      exact hx (hsupport hh)
    rw [hh,norm_zero]
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun x => ‖iteratedDeriv n (mellinLogFamily V σ) x‖)
    (isCompact_Icc.measure_lt_top) (C := B * weightNorm n V)
    (fun x hx => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hbound V hV x hx)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))] at hi
  convert hi using 1 <;> dsimp [K] <;> ring

theorem mellin_literal_eq_standard (V : ℝ → ℂ) (s : ℂ) :
    mellinTransform V s = mellin V s := by
  unfold mellinTransform mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one,smul_eq_mul]
  ring

theorem mellin_literal_eq_logFourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellinTransform V (contourPoint σ t) =
      𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_literal_eq_standard,mellin_eq_fourier]
  simp only [contourPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,Complex.I_im,mul_one,zero_add]
  rfl

/-- Fixed-order rapid decay; n is chosen before the support interval. -/
theorem mellin_literal_power_bound (I : SupportInterval) (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℂ), SmoothSupported I V → ∀ t : ℝ,
      (1 + |t|) ^ n * ‖mellinTransform V (contourPoint σ t)‖ ≤ C * weightNorm n V := by
  obtain ⟨Cn,hCn,hnd⟩ := mellin_logFamily_derivative_L1 I σ n
  obtain ⟨C0,hC0,h0d⟩ := mellin_logFamily_derivative_L1 I σ 0
  refine ⟨(2 : ℝ) ^ n * (C0+Cn),by positivity,?_⟩
  intro V hV t
  have hs := mellin_logFamily_smooth hV σ
  have hi (k : ℕ) : Integrable (iteratedDeriv k (mellinLogFamily V σ)) := by
    obtain ⟨C,hC,hb⟩ := mellin_logFamily_derivative_L1 I σ k
    exact (hb V hV).1
  have hfour := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k hk => hi k) (by simp : (n : ℕ∞) ≤ ⊤)) (t/(2*Real.pi))
  have hnorm : ‖𝓕 (iteratedDeriv n (mellinLogFamily V σ)) (t/(2*Real.pi))‖ =
      |t| ^ n * ‖mellinTransform V (contourPoint σ t)‖ := by
    rw [hfour,mellin_literal_eq_logFourier,norm_smul,norm_pow]
    have he : (2 * Real.pi * Complex.I * (t/(2*Real.pi) : ℝ) : ℂ) = (t : ℂ) * Complex.I := by
      push_cast
      field_simp
      <;> ring
    rw [he,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
  have hp : |t| ^ n * ‖mellinTransform V (contourPoint σ t)‖ ≤ Cn * weightNorm n V := by
    rw [← hnorm]
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ ℝ) _ _).trans (hnd V hV).2
  have hz : ‖mellinTransform V (contourPoint σ t)‖ ≤ C0 * weightNorm n V := by
    rw [mellin_literal_eq_logFourier]
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ ℝ) _ _).trans
    exact (h0d V hV).2.trans (mul_le_mul_of_nonneg_left (weightNorm_mono hV (Nat.zero_le n)) hC0)
  have hN := weightNorm_nonneg hV n
  by_cases ht : |t| ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ n * ‖mellinTransform V (contourPoint σ t)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) n) (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ n * (C0 * weightNorm n V) := mul_le_mul_of_nonneg_left hz (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCn) (by positivity)) hN
  · have ht' : 1 ≤ |t| := (lt_of_not_ge ht).le
    calc
      _ ≤ (2*|t|) ^ n * ‖mellinTransform V (contourPoint σ t)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) n) (norm_nonneg _)
      _ = (2 : ℝ) ^ n * (|t| ^ n * ‖mellinTransform V (contourPoint σ t)‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ n * (Cn * weightNorm n V) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hC0) (by positivity)) hN

theorem mellin_literal_continuous {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (σ : ℝ) :
    Continuous (fun u : ℝ => mellinTransform V (contourPoint σ u)) := by
  have hi : Integrable (mellinLogFamily V σ) :=
    (mellin_logFamily_smooth hV σ).continuous.integrable_of_hasCompactSupport
      (mellin_logFamily_compact hV σ)
  have hc : Continuous (𝓕 (mellinLogFamily V σ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have heq : (fun u : ℝ => mellinTransform V (contourPoint σ u)) =
      fun u => 𝓕 (mellinLogFamily V σ) (u/(2*Real.pi)) :=
    funext (mellin_literal_eq_logFourier V σ)
  rw [heq]
  exact hc.comp (continuous_id.div_const _)

theorem mellin_gamma_vertical_continuous (a σ : ℝ) (ha : 0 < a+σ) :
    Continuous (fun u : ℝ => Complex.Gamma ((a : ℂ) + contourPoint σ u)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply (Complex.continuousAt_Gamma _ (fun m => ?_)).comp (by unfold contourPoint; fun_prop)
  intro hh
  have hr := congrArg Complex.re hh
  simp only [contourPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.neg_re,Complex.natCast_re] at hr
  linarith [Nat.cast_nonneg (α := ℝ) m]

theorem mellin_kernel_continuous {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (j : ℕ) (σ : ℝ) (hσ : -(1/4 : ℝ) ≤ σ) :
    Continuous (mellinKernel j V σ) := by
  have hpoint : Continuous (contourPoint σ) := by unfold contourPoint; fun_prop
  have hneg (u : ℝ) : -contourPoint σ u = contourPoint (-σ) (-u) := by
    unfold contourPoint
    push_cast
    ring
  have hm : Continuous (fun u => mellinTransform V (-contourPoint σ u)) := by
    simp_rw [hneg]
    exact (mellin_literal_continuous hV (-σ)).comp continuous_neg
  have h1 := mellin_gamma_vertical_continuous (7/6) σ (by linarith)
  have h2 := mellin_gamma_vertical_continuous (5/6) σ (by linarith)
  have h3 : Continuous (fun u => (Complex.Gamma ((7/6 : ℂ) - contourPoint σ u))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp (continuous_const.sub hpoint)
  have h4 : Continuous (fun u => (Complex.Gamma ((5/6 : ℂ) - contourPoint σ u))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp (continuous_const.sub hpoint)
  have hb : Continuous (fun u : ℝ =>
      ((((2*Real.pi)^4/27 : ℝ) : ℂ) ^ (-contourPoint σ u))) :=
    hpoint.neg.const_cpow (.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : 0 < (2*Real.pi)^4/27))))
  have hconst : Continuous (fun _u : ℝ => ((2*Real.pi : ℝ) : ℂ)⁻¹) := continuous_const
  convert (((hconst.mul (hpoint.neg.pow j)).mul hm).mul
    ((h1.mul h2).mul (h3.mul h4))).mul hb using 1
  ext u
  simp only [mellinKernel,gammaMultiplier,div_eq_mul_inv,mul_inv_rev,
    Complex.ofReal_div,Complex.ofReal_ofNat,Pi.mul_apply,Pi.pow_apply,Pi.neg_apply]
  push_cast
  ring

theorem mellin_kernel_norm_formula (j : ℕ) (V : ℝ → ℂ) (σ u : ℝ) :
    ‖mellinKernel j V σ u‖ =
      (2*Real.pi)⁻¹ * ‖contourPoint σ u‖ ^ j *
        ‖mellinTransform V (-contourPoint σ u)‖ * ‖gammaMultiplier (contourPoint σ u)‖ *
          (((2*Real.pi)^4/27 : ℝ) ^ (-σ)) := by
  change ‖((2*Real.pi : ℝ) : ℂ)⁻¹ * (-contourPoint σ u)^j *
    mellinTransform V (-contourPoint σ u) * gammaMultiplier (contourPoint σ u) *
      ((((2*Real.pi)^4/27 : ℝ) : ℂ) ^ (-contourPoint σ u))‖ = _
  simp only [norm_mul,norm_inv,norm_pow,norm_neg,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi),
    contour_cpow_norm (by positivity : 0 < (2*Real.pi)^4/27)]

/-- A Cauchy majorant with a derivative order chosen before I. -/
theorem mellin_kernel_cauchy_bound (A j : ℕ) (I : SupportInterval) (σ : ℝ)
    (hσ : σ ∈ Set.Icc (-(1/4 : ℝ)) (A : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℂ), SmoothSupported I V → ∀ u : ℝ,
      ‖mellinKernel j V σ u‖ ≤
        C * weightNorm (4*A+4+j+2) V / (1+u^2) := by
  let g := 4*A+4
  let n := g+j+2
  obtain ⟨Cg,hCg,hgamma⟩ := gammaMultiplier_strip_bound A
  obtain ⟨Cm,hCm,hmellin⟩ := mellin_literal_power_bound I (-σ) n
  let P : ℝ := (2*Real.pi)⁻¹ * (|σ|+1)^j * Cg * (((2*Real.pi)^4/27 : ℝ)^(-σ))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨P*Cm,mul_nonneg hP hCm,?_⟩
  intro V hV u
  have hm := hmellin V hV (-u)
  have heq : contourPoint (-σ) (-u) = -contourPoint σ u := by
    unfold contourPoint
    push_cast
    ring
  rw [heq,abs_neg] at hm
  have hg := hgamma σ hσ u
  change ‖gammaMultiplier (contourPoint σ u)‖ ≤ Cg*(1+|u|)^g at hg
  have ht : ‖contourPoint σ u‖ ≤ (|σ|+1)*(1+|u|) := by
    have hh := norm_add_le (σ : ℂ) ((u : ℂ)*Complex.I)
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at hh
    change ‖(σ : ℂ)+(u : ℂ)*Complex.I‖ ≤ _
    nlinarith [abs_nonneg σ,abs_nonneg u]
  have htj : ‖contourPoint σ u‖^j ≤ (|σ|+1)^j*(1+|u|)^j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ht j
  have hw : (1+|u|)^2 * ‖mellinKernel j V σ u‖ ≤ (P*Cm)*weightNorm n V := by
    rw [mellin_kernel_norm_formula]
    calc
      _ ≤ (1+|u|)^2 * ((2*Real.pi)⁻¹ * ((|σ|+1)^j*(1+|u|)^j) *
          ‖mellinTransform V (-contourPoint σ u)‖ * (Cg*(1+|u|)^g) *
            (((2*Real.pi)^4/27 : ℝ)^(-σ))) := by
        gcongr
      _ = P * ((1+|u|)^n * ‖mellinTransform V (-contourPoint σ u)‖) := by
        dsimp only [P,n]
        rw [pow_add,pow_add]
        ring
      _ ≤ P*(Cm*weightNorm n V) := mul_le_mul_of_nonneg_left hm hP
      _ = _ := by ring
  apply (le_div_iff₀ (by positivity : 0 < 1+u^2)).mpr
  have hb : 1+u^2 ≤ (1+|u|)^2 := by nlinarith [abs_nonneg u,sq_abs u]
  simpa only [n,g,mul_comm] using (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans hw

/-- Absolute integrability and the L1 norm bound for any contour in the strip. -/
theorem mellin_kernel_L1_bound (A j : ℕ) (I : SupportInterval) (σ : ℝ)
    (hσ : σ ∈ Set.Icc (-(1/4 : ℝ)) (A : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℂ), SmoothSupported I V →
      Integrable (mellinKernel j V σ) ∧
        (∫ u : ℝ, ‖mellinKernel j V σ u‖) ≤ C * weightNorm (4*A+4+j+2) V := by
  obtain ⟨C,hC,hbound⟩ := mellin_kernel_cauchy_bound A j I σ hσ
  refine ⟨C*Real.pi,mul_nonneg hC Real.pi_pos.le,?_⟩
  intro V hV
  have hc := mellin_kernel_continuous hV j σ hσ.1
  have hmajor : Integrable (fun u : ℝ =>
      (C*weightNorm (4*A+4+j+2) V) * (1+u^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hb (u : ℝ) : ‖mellinKernel j V σ u‖ ≤
      (C*weightNorm (4*A+4+j+2) V) * (1+u^2)⁻¹ := by
    simpa only [div_eq_mul_inv] using hbound V hV u
  have hi : Integrable (mellinKernel j V σ) :=
    hmajor.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ u : ℝ, (C*weightNorm (4*A+4+j+2) V) * (1+u^2)⁻¹ :=
      integral_mono hi.norm hmajor hb
    _ = (C*weightNorm (4*A+4+j+2) V)*Real.pi := by
      rw [integral_const_mul,integral_univ_inv_one_add_sq]
    _ = _ := by ring

/-- The exact pinned statement. The derivative order is selected before
I; only the multiplicative constant is allowed to depend on its support. -/
theorem theta_bounds_mellin_kernel_proved : MellinKernelBoundStatement := by
  intro A j hA
  let N : ℕ := ⌈A⌉₊
  let J : ℕ := 4*N+4+j+2
  refine ⟨J,by dsimp [J]; omega,?_⟩
  intro I
  have hlo : (-(1/4 : ℝ)) ∈ Set.Icc (-(1/4 : ℝ)) (N : ℝ) := by
    exact ⟨le_rfl,by have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith⟩
  have hhi : A ∈ Set.Icc (-(1/4 : ℝ)) (N : ℝ) :=
    ⟨by linarith, Nat.le_ceil A⟩
  obtain ⟨Clo,hClo,hloB⟩ := mellin_kernel_L1_bound N j I (-(1/4 : ℝ)) hlo
  obtain ⟨Chi,hChi,hhiB⟩ := mellin_kernel_L1_bound N j I A hhi
  refine ⟨max Clo Chi,hClo.trans (le_max_left _ _),?_⟩
  intro V hV σ hσ
  have hnorm : 0 ≤ weightNorm J V := weightNorm_nonneg hV J
  rcases hσ with rfl | rfl
  · refine ⟨(hloB V hV).1,(hloB V hV).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnorm
  · refine ⟨(hhiB V hV).1,(hhiB V hV).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hnorm

end QRHShort.CloudBatch
