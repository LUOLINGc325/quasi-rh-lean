import QRHShort.ReflectionReduction
import QRHShort.ArithmeticBasics
import QRHShort.PrimeComparison
import QRHShort.HeckeMultiplicative
import QRHShort.WeightNorm
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Analytic prerequisites for the literal reflection Mellin transfer.
The analytic rectangle and compact-source estimates below are reproduced
from the independently checked theta contour proof, in a fresh namespace. -/

noncomputable section
open scoped BigOperators FourierTransform ContDiff Topology
open Classical MeasureTheory Filter Set Asymptotics

namespace QRHShort.CloudBatch.ReflectionMellin
open ReflectionProof

local instance : Countable O := Finsupp.Countable.of_moduleFinite (R := ℤ)

theorem ideal_norm_one_le {a : Ideal O} (ha : a ≠ ⊥) : 1 ≤ normIdeal a := by
  have hn : a.absNorm ≠ 0 := fun h => ha (Ideal.absNorm_eq_zero_iff.mp h)
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)

def contourPoint (sigma u : ℝ) : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I

/-- The complete Mellin multiplier, with x-dependence removed. -/
def mellinKernel (j : ℕ) (V : ℝ → ℂ) (sigma u : ℝ) : ℂ :=
  let t := contourPoint sigma u
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (-t) ^ j * mellinTransform V (-t) *
    (Complex.Gamma (7 / 6 + t) * Complex.Gamma (5 / 6 + t) /
      (Complex.Gamma (7 / 6 - t) * Complex.Gamma (5 / 6 - t))) *
    ((((2 * Real.pi) ^ (4 : ℕ) / 27 : ℝ) : ℂ) ^ (-t))

def shiftedWeight (j : ℕ) (V : ℝ → ℂ) (sigma x : ℝ) : ℂ :=
  ∫ u : ℝ, mellinKernel j V sigma u * (x : ℂ) ^ (-contourPoint sigma u)

/-- At the original contour and derivative order zero, the normalized kernel
is exactly the frozen theta transform, without any analytic assumptions. -/
theorem shiftedWeight_zero (V : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    shiftedWeight 0 V 0 x = thetaWeight V x := by
  unfold shiftedWeight thetaWeight
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  have harg : (2 * Real.pi) ^ (4 : ℕ) * x / 27 =
      ((2 * Real.pi) ^ (4 : ℕ) / 27) * x := by ring
  rw [harg]
  simp only [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (by positivity) hx.le]
  simp only [mellinKernel, contourPoint, Complex.ofReal_zero, zero_add,
    pow_zero, mul_one, neg_mul, Complex.ofReal_inv]
  ring


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



theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

def mellinLogFamily (V : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  Real.exp (-σ * u) • V (Real.exp (-u))

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)


open MeasureTheory Filter Set

def mellinData (V : ℝ → ℂ) (s : ℂ) : ℂ := mellin V (-s) * gammaMultiplier s

def mellinEulerData (V : ℝ → ℂ) (j : ℕ) (s : ℂ) : ℂ := (-s) ^ j * mellinData V s

theorem mellinData_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellinData V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hsupp hV
    (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

theorem mellinEulerData_strip_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinData_strip_decay V a b ha hsupp hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    hlocal htop (by linarith) hbot (by linarith)

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)


theorem mellinEulerData_differentiableAt (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (mellinEulerData V j) s :=
  (differentiableAt_id.neg.pow j).mul
    (kernelMellinIntegrand_differentiableAt V a b ha hsupp hV s hs)

theorem mellinEulerData_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinEulerData_differentiableAt V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv,Function.comp_def] using hb σ hσ t)

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm


def inverseMellinIntegrand (V : ℝ → ℂ) (j : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (-s) * mellinEulerData V j s

theorem inverseMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (inverseMellinIntegrand V j y) s := by
  exact (differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (mellinEulerData_differentiableAt V a b ha hsupp hV j s hs)

theorem inverseMellinIntegrand_vertical_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (mellinEulerData_vertical_integrable V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem inverseMellinIntegrand_strip_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [inverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring


theorem mellin_literal_eq_standard (V : ℝ → ℂ) (s : ℂ) :
    mellinTransform V s = mellin V s := by
  unfold mellinTransform mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hx.ne'),Complex.cpow_one,smul_eq_mul]
  ring

def thetaMellinScale : ℝ := (2*Real.pi)^4/27

theorem thetaMellinScale_pos : 0 < thetaMellinScale := by unfold thetaMellinScale; positivity

theorem mellin_kernel_eq_eulerData (j : ℕ) (V : ℝ → ℂ) (σ u : ℝ) :
    mellinKernel j V σ u = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      mellinEulerData V j (contourPoint σ u) *
        (thetaMellinScale : ℂ)^(-contourPoint σ u) := by
  simp only [mellinKernel,mellinEulerData,mellinData,gammaMultiplier,
    mellin_literal_eq_standard,thetaMellinScale]
  ring

/-- Exact 2π normalization and the actual positive x-sampling scale. -/
theorem shiftedWeight_eq_inverse (j : ℕ) (V : ℝ → ℂ) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) :
    shiftedWeight j V σ x = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ u : ℝ, inverseMellinIntegrand V j (thetaMellinScale*x) (contourPoint σ u) := by
  unfold shiftedWeight
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [mellin_kernel_eq_eulerData]
  simp only [inverseMellinIntegrand,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg thetaMellinScale_pos.le hx.le]
  ring

/-- Rectangle/Cauchy contour shift with the horizontal integrals proved to
vanish from the uniform strip bound. No totalized-integral shortcut is used. -/
theorem inverseMellin_integral_shift {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (A j : ℕ) (σ : ℝ)
    (hσ : σ ∈ Set.Icc (-(1/4 : ℝ)) (A : ℝ)) (y : ℝ) (hy : 0 < y) :
    (∫ u : ℝ, inverseMellinIntegrand V j y (contourPoint 0 u)) =
      ∫ u : ℝ, inverseMellinIntegrand V j y (contourPoint σ u) := by
  obtain ⟨C,hC,hb⟩ := inverseMellinIntegrand_strip_bound V I.lo I.hi I.lo_pos hV.2 hV.1 A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1/4 : ℝ)) (A : ℝ) :=
    ⟨by norm_num,Nat.cast_nonneg _⟩
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1/4 : ℝ)) (A : ℝ)) :
      (∫ u : ℝ, inverseMellinIntegrand V j y (contourPoint (-(1/4 : ℝ)) u)) =
        ∫ u : ℝ, inverseMellinIntegrand V j y (contourPoint ρ u) := by
    apply integral_eq_of_strip_decay (inverseMellinIntegrand V j y) (-(1/4)) ρ C hρ.1
    · intro z hzlo hzhi
      exact inverseMellinIntegrand_differentiableAt V I.lo I.hi I.lo_pos hV.2 hV.1 j y hy z
        (by linarith)
    · exact inverseMellinIntegrand_vertical_integrable V I.lo I.hi I.lo_pos hV.2 hV.1 A j
        (-(1/4)) ⟨le_rfl,hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V I.lo I.hi I.lo_pos hV.2 hV.1 A j ρ hρ y hy
    · intro r hr u
      exact hb r ⟨hr.1,hr.2.trans hρ.2⟩ u
  exact (hshift 0 h0).symm.trans (hshift σ hσ)

/-- Equality of the literal shifted integrals for every allowed real contour. -/
theorem shiftedWeight_eq_axis {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (j : ℕ) (σ : ℝ) (hσ : -(1/4 : ℝ) ≤ σ)
    {x : ℝ} (hx : 0 < x) : shiftedWeight j V 0 x = shiftedWeight j V σ x := by
  rw [shiftedWeight_eq_inverse j V 0 hx,shiftedWeight_eq_inverse j V σ hx,
    inverseMellin_integral_shift hV ⌈σ⌉₊ j σ ⟨hσ,Nat.le_ceil σ⟩
      (thetaMellinScale*x) (mul_pos thetaMellinScale_pos hx)]


/-- Vertical integrability of the actual compact-source Mellin transform. -/
theorem compact_mellin_verticalIntegrable {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (σ : ℝ) : Complex.VerticalIntegrable (mellin V) σ := by
  obtain ⟨C, hC, hb⟩ := compact_source_mellin_strip_decay V I.lo I.hi I.lo_pos
    hV.2 hV.1 σ σ 2
  have hd := compact_source_mellin_differentiable V I.lo I.hi I.lo_pos hV.2 hV.1
  have hc : Continuous (fun t : ℝ => mellin V ((σ : ℂ) + t * Complex.I)) :=
    hd.continuous.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [div_eq_mul_inv] using
      weighted_two_to_cauchy (norm_nonneg _) t (hb σ ⟨le_rfl,le_rfl⟩ t))

/-- Mathlib inversion for the frozen literal Mellin transform, with exact
real-axis parametrization and its 2π normalization. -/
theorem literal_mellin_inversion {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ u : ℝ, (x : ℂ) ^ (-contourPoint σ u) *
        mellinTransform V (contourPoint σ u)) = V x := by
  have h := mellinInv_mellin_eq σ V hx (compact_source_mellin_convergent V I.lo I.hi I.lo_pos hV.2 hV.1 σ)
    (compact_mellin_verticalIntegrable hV σ) hV.1.continuous.continuousAt
  simpa only [mellinInv, one_div, smul_eq_mul, Complex.real_smul, contourPoint,
    mellin_literal_eq_standard, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using h

/-- Exact theta kernel on every permitted shifted contour, expressed with
the original reflection gamma factor. No contour premise is assumed. -/
theorem thetaWeight_reflection_integral {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) (σ : ℝ) (hσ : -(1 / 4 : ℝ) ≤ σ)
    {x : ℝ} (hx : 0 < x) :
    thetaWeight V x = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ u : ℝ, mellinTransform V (-contourPoint σ u) *
        reflectionGammaFactor (1 / 2 - contourPoint σ u) *
        (x : ℂ) ^ (-contourPoint σ u) := by
  rw [← shiftedWeight_zero V hx, shiftedWeight_eq_axis hV 0 σ hσ hx]
  unfold shiftedWeight
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [reflectionGammaFactor_half_sub]
  simp only [mellinKernel, pow_zero, mul_one]
  ring

/-- Multiplying by sqrt preserves the actual positive support interval. -/
theorem sqrt_weight_smoothSupported {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) :
    SmoothSupported I (fun x => (Real.sqrt x : ℂ) * W x) := by
  refine ⟨?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : 0 < x
    · exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp x
        (Real.contDiffAt_sqrt hx.ne')).mul hW.1.contDiffAt
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      have hxI : x < I.lo := (le_of_not_gt hx).trans_lt I.lo_pos
      filter_upwards [Iio_mem_nhds hxI] with y hy
      have hWy : W y = 0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hW.2 hn).1
      simp only [hWy, mul_zero]
  · intro x hx
    apply hW.2
    intro h
    exact hx (by change (Real.sqrt x : ℂ) * W x = 0; rw [h,mul_zero])

/-- Literal Mellin shift for the square-root weight appearing in dualThetaSum. -/
theorem sqrt_weight_mellin (W : ℝ → ℂ) (s : ℂ) :
    mellinTransform (fun x => (Real.sqrt x : ℂ) * W x) s =
      mellinTransform W (s + 1 / 2) := by
  simp_rw [mellin_literal_eq_standard]
  rw [← mellin_cpow_smul W s (1 / 2 : ℂ)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hsqrt : (Real.sqrt x : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
    norm_num
  simp only [hsqrt, smul_eq_mul]


def sourceMellinIntegrand (V : ℝ → ℂ) (X : ℝ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  mellin V (s - 1 / 2) * (X : ℂ) ^ (s - 1 / 2) * F s

theorem sourceMellinIntegrand_differentiable {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) : Differentiable ℂ (sourceMellinIntegrand V X F) := by
  apply Differentiable.mul _ hF
  apply Differentiable.mul
  · exact (compact_source_mellin_differentiable V I.lo I.hi I.lo_pos hV.2 hV.1).comp
      (differentiable_id.sub_const _)
  · exact (differentiable_id.sub_const _).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))

/-- Polynomial strip growth of the continued source is dominated by the
actual Mellin decay of the supported test. -/
theorem sourceMellinIntegrand_strip_decay {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ}
    (hF : StripPolynomialGrowth F) (a b : ℝ) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖sourceMellinIntegrand V X F ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨Cf, B, hCf, hB, hFb⟩ := hF a b hab
  let n : ℕ := ⌈B⌉₊
  obtain ⟨Cv, hCv, hVb⟩ := compact_source_mellin_strip_decay V I.lo I.hi I.lo_pos
    hV.2 hV.1 (a - 1 / 2) (b - 1 / 2) (n + 2)
  have hxc : Continuous (fun σ : ℝ => X ^ (σ - 1 / 2)) :=
    (Real.continuous_const_rpow hX.ne').comp (continuous_id.sub continuous_const)
  obtain ⟨Dx, hDx⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image hxc.continuousOn
  let Cx : ℝ := |Dx| + 1
  have hCx : 0 ≤ Cx := by dsimp only [Cx]; positivity
  refine ⟨Cx * Cf * Cv, by positivity, ?_⟩
  intro σ hσ t
  have hcpow : ‖(X : ℂ) ^ (((σ : ℂ) + t * Complex.I) - 1 / 2)‖ ≤ Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have hre : (((σ : ℂ) + t * Complex.I) - 1 / 2).re = σ - 1 / 2 := by simp
    rw [hre]
    exact (hDx (Set.mem_image_of_mem _ hσ)).trans (by
      dsimp only [Cx]; linarith [le_abs_self Dx])
  have hf := hFb ((σ : ℂ) + t * Complex.I) (by simpa using hσ.1) (by simpa using hσ.2)
  have hre : (((σ : ℂ) + t * Complex.I) - 1 / 2) =
      (((σ - 1 / 2 : ℝ) : ℂ) + t * Complex.I) := by push_cast; ring
  have hv := hVb (σ - 1 / 2) ⟨by linarith [hσ.1],by linarith [hσ.2]⟩ t
  rw [← hre] at hv
  have hBpow : (1 + |t|) ^ B ≤ (1 + |t|) ^ n := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t] : 1 ≤ 1 + |t|)
      (Nat.le_ceil B)
    simpa only [Real.rpow_natCast] using h
  have hFnorm : ‖F ((σ : ℂ) + t * Complex.I)‖ ≤ Cf * (1 + |t|) ^ n := by
    apply hf.trans
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    exact mul_le_mul_of_nonneg_left hBpow hCf
  apply weighted_two_to_cauchy (norm_nonneg _) t
  rw [sourceMellinIntegrand, norm_mul, norm_mul]
  calc
    _ ≤ (1 + |t|) ^ 2 *
        (‖mellin V (((σ : ℂ) + t * Complex.I) - 1 / 2)‖ * Cx *
          (Cf * (1 + |t|) ^ n)) := by gcongr
    _ = (Cx * Cf) * ((1 + |t|) ^ (n + 2) *
        ‖mellin V (((σ : ℂ) + t * Complex.I) - 1 / 2)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (mul_nonneg hCx hCf)

/-- The first actual contour transfer uses only the supplied entire source
continuation and its polynomial strip growth. -/
theorem sourceMellin_contour_shift {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hgrowth : StripPolynomialGrowth F)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ, sourceMellinIntegrand V X F ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, sourceMellinIntegrand V X F ((b : ℂ) + t * Complex.I) := by
  obtain ⟨C, hC, hb⟩ := sourceMellinIntegrand_strip_decay hV hX hgrowth a b hab
  have hd := sourceMellinIntegrand_differentiable hV hX hF
  have hi (σ : ℝ) (hσ : σ ∈ Icc a b) :
      Integrable (fun t : ℝ => sourceMellinIntegrand V X F ((σ : ℂ) + t * Complex.I)) := by
    apply (integrable_inv_one_add_sq.const_mul C).mono'
      (hd.continuous.comp (by fun_prop)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      simpa only [div_eq_mul_inv,Function.comp_def] using hb σ hσ t)
  exact integral_eq_of_strip_decay (sourceMellinIntegrand V X F) a b C hab
    (fun z _ _ => hd z) (hi a ⟨le_rfl,hab⟩) (hi b ⟨hab,le_rfl⟩) hb


/-- A vertical Dirichlet family with summable coefficient norms may be
integrated against an actual L1 multiplier. The domination and convergence
are proved here rather than supplied as a termwise-integration premise. -/
theorem integral_tsum_constant_norm {ι : Type*} [Countable ι]
    (f : ι → ℝ → ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hmeas : ∀ i, AEStronglyMeasurable (f i))
    (hnorm : ∀ i u, ‖f i u‖ = ‖f i 0‖)
    (hsum : Summable (fun i => ‖f i 0‖)) :
    (∑' i, ∫ u : ℝ, k u * f i u) = ∫ u : ℝ, k u * ∑' i, f i u := by
  have hint (i : ι) : Integrable (fun u => k u * f i u) := by
    apply (hk.norm.mul_const ‖f i 0‖).mono'
      (hk.aestronglyMeasurable.mul (hmeas i))
    exact Filter.Eventually.of_forall (fun u => by simp only [Pi.mul_apply,norm_mul,hnorm,le_refl])
  have hL1 (i : ι) : (∫ u : ℝ, ‖k u * f i u‖) =
      (∫ u : ℝ, ‖k u‖) * ‖f i 0‖ := by
    simp_rw [norm_mul, hnorm]
    exact integral_mul_const _ _
  have h := integral_tsum_of_summable_integral_norm hint (by
    simp_rw [hL1]
    exact hsum.mul_left _)
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with u
  exact tsum_mul_left

/-- Actual source terms have constant modulus along each vertical line.
The positive ideal norms come from the source's own support condition. -/
theorem sourceDirichletTerm_vertical_norm (c : ArithmeticContext)
    (Ψ : Ideal O → ℂ) (σ u : ℝ) (nb : Ideal O × Ideal O) :
    ‖sourceDirichletTerm c Ψ (contourPoint σ u) nb‖ =
      ‖sourceDirichletTerm c Ψ (σ : ℂ) nb‖ := by
  unfold sourceDirichletTerm
  split_ifs with h
  · have hn : 0 < normIdeal nb.1 := normIdeal_pos h.1.1.1
    have hb : 0 < normIdeal nb.2 := normIdeal_pos h.2.1
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hb]
    congr 2 <;> simp [contourPoint, Complex.mul_re]
  · rfl


/-- Termwise integration of the actual source Dirichlet series in its initial
half-plane, with absolute convergence deduced from SourceContinuation. -/
theorem sourceDirichlet_integral_termwise (c : ArithmeticContext)
    (Ψ : Ideal O → ℂ) (F : ℂ → ℂ) (hF : SourceContinuation c Ψ F)
    (σ : ℝ) (hσ : 2 < σ) (k : ℝ → ℂ) (hk : Integrable k) :
    (∫ u : ℝ, k u * F (contourPoint σ u)) =
      ∑' nb : Ideal O × Ideal O,
        ∫ u : ℝ, k u * sourceDirichletTerm c Ψ (contourPoint σ u) nb := by
  let f : (Ideal O × Ideal O) → ℝ → ℂ :=
    fun nb u => sourceDirichletTerm c Ψ (contourPoint σ u) nb
  have hmeas (nb : Ideal O × Ideal O) : AEStronglyMeasurable (f nb) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [f,sourceDirichletTerm]
    split_ifs with h
    · have hn : (normIdeal nb.1 : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (normIdeal_pos h.1.1.1).ne'
      have hb : (normIdeal nb.2 : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (normIdeal_pos h.2.1).ne'
      have hncp : Continuous (fun u : ℝ => (normIdeal nb.1 : ℂ) ^ (-contourPoint σ u)) :=
        (show Continuous (fun u : ℝ => -contourPoint σ u) by unfold contourPoint; fun_prop).const_cpow
          (Or.inl hn)
      have hbcp : Continuous (fun u : ℝ => (normIdeal nb.2 : ℂ) ^
          (-(3 : ℂ) * contourPoint σ u + 1 / 2)) :=
        (show Continuous (fun u : ℝ => -(3 : ℂ) * contourPoint σ u + 1 / 2) by
          unfold contourPoint; fun_prop).const_cpow (Or.inl hb)
      exact (continuous_const.mul hncp).mul hbcp
    · exact continuous_const
  have hnorm (nb : Ideal O × Ideal O) (u : ℝ) : ‖f nb u‖ = ‖f nb 0‖ :=
    (sourceDirichletTerm_vertical_norm c Ψ σ u nb).trans
      (sourceDirichletTerm_vertical_norm c Ψ σ 0 nb).symm
  have hsum : Summable (fun nb => ‖f nb 0‖) := by
    have h := (hF.2.1 (σ : ℂ) (by simpa using hσ)).summable.norm
    simpa only [f,contourPoint,Complex.ofReal_zero,zero_mul,add_zero] using h
  calc
    _ = ∫ u : ℝ, k u * ∑' nb, f nb u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [(hF.2.1 (contourPoint σ u) (by simpa [contourPoint] using hσ)).tsum_eq]
    _ = _ := (integral_tsum_constant_norm f k hk hmeas hnorm hsum).symm


def sourceWeightedTerm (c : ArithmeticContext) (Ψ : Ideal O → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (nb : Ideal O × Ideal O) : ℂ :=
  if SquarefreeOutside c.S nb.1 ∧ Outside c.S nb.2 then
    (star (alpha nb.1) * gauss 2 nb.1 * Ψ nb.1 *
      star (alpha nb.2) ^ (3 : ℕ) * Ψ nb.2 ^ (3 : ℕ)) /
      ((Real.sqrt (normIdeal nb.1) : ℂ) * (normIdeal nb.2 : ℂ)) *
      (Real.sqrt (normIdeal nb.1 * normIdeal nb.2 ^ (3 : ℕ) / X) : ℂ) *
      W (normIdeal nb.1 * normIdeal nb.2 ^ (3 : ℕ) / X)
  else 0

/-- Compact support gives genuine joint finite support of the original
completed n,b sum, before any Mellin interchange. -/
theorem sourceWeightedTerm_hasFiniteSupport (c : ArithmeticContext)
    (Ψ : Ideal O → ℂ) {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) :
    Function.HasFiniteSupport (sourceWeightedTerm c Ψ W X) := by
  apply ((finite_normIdeal_le (I.hi * X)).prod
    (finite_normIdeal_le (I.hi * X))).subset
  intro nb hnb
  have h : SquarefreeOutside c.S nb.1 ∧ Outside c.S nb.2 := by
    by_contra hn
    exact hnb (by simp only [sourceWeightedTerm,ite_eq_right hn])
  have hw : W (normIdeal nb.1 * normIdeal nb.2 ^ (3 : ℕ) / X) ≠ 0 := by
    intro hz
    exact hnb (by simp only [sourceWeightedTerm,ite_eq_left h,hz,mul_zero])
  have hn1 : 1 ≤ normIdeal nb.1 := ideal_norm_one_le h.1.1.1
  have hb1 : 1 ≤ normIdeal nb.2 := ideal_norm_one_le h.2.1
  have hbound := (div_le_iff₀ hX).mp (hW.2 hw).2
  have hb3 : 1 ≤ normIdeal nb.2 ^ (3 : ℕ) := one_le_pow₀ hb1
  have hnle : normIdeal nb.1 ≤ normIdeal nb.1 * normIdeal nb.2 ^ (3 : ℕ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hb3
  have hble : normIdeal nb.2 ≤ normIdeal nb.1 * normIdeal nb.2 ^ (3 : ℕ) := by
    apply (le_self_pow₀ hb1 (by decide : (3 : ℕ) ≠ 0)).trans
    exact le_mul_of_one_le_left (by positivity) hn1
  exact ⟨hnle.trans hbound,hble.trans hbound⟩

theorem completedSum_eq_joint (c : ArithmeticContext)
    (Ψ : Ideal O → ℂ) {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) :
    completedSum c Ψ W X = ∑' nb : Ideal O × Ideal O, sourceWeightedTerm c Ψ W X nb := by
  have hs : Summable (sourceWeightedTerm c Ψ W X) :=
    summable_of_hasFiniteSupport (sourceWeightedTerm_hasFiniteSupport c Ψ hW hX)
  rw [hs.tsum_prod]
  unfold completedSum
  apply tsum_congr
  intro n
  by_cases hn : SquarefreeOutside c.S n
  · rw [ite_eq_left hn]
    apply tsum_congr
    intro b
    by_cases hb : Outside c.S b
    · have hnb : SquarefreeOutside c.S n ∧ Outside c.S b := ⟨hn,hb⟩
      simp only [sourceWeightedTerm,ite_eq_left hnb,ite_eq_left hb]
      ring
    · simp only [sourceWeightedTerm,ite_eq_right hb,
        show ¬ (SquarefreeOutside c.S n ∧ Outside c.S b) from fun h => hb h.2,
        ite_false]
  · have hz (b : Ideal O) : sourceWeightedTerm c Ψ W X (n,b) = 0 :=
      ite_eq_right (fun h => hn h.1)
    simp only [ite_eq_right hn,hz,tsum_zero]


/-- Exact scalar normalization of the source spectral variable. -/
theorem source_cpow_normalization {a b X : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX : 0 < X) (s : ℂ) :
    (a : ℂ) ^ (-s) * (b : ℂ) ^ (-(3 : ℂ) * s + 1 / 2) *
      (X : ℂ) ^ (s - 1 / 2) =
      ((Real.sqrt a : ℂ) * (b : ℂ))⁻¹ *
        ((a * b ^ (3 : ℕ) / X : ℝ) : ℂ) ^ (-(s - 1 / 2)) := by
  have han : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbn : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hbpow (r : ℂ) : ((b ^ (3 : ℕ) : ℝ) : ℂ) ^ r = (b : ℂ) ^ ((3 : ℂ) * r) := by
    simpa only [Real.rpow_ofNat, Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hb.le (3 : ℝ) r).symm
  have hsqrt : (Real.sqrt a : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    norm_num
  have hscale : ((a * b ^ (3 : ℕ) / X : ℝ) : ℂ) ^ (-(s - 1 / 2)) =
      (a : ℂ) ^ (-(s - 1 / 2)) * (b : ℂ) ^ ((3 : ℂ) * (-(s - 1 / 2))) *
        (X : ℂ) ^ (s - 1 / 2) := by
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (by positivity) hX.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (by positivity), hbpow,
      div_eq_mul_inv]
    have hinv : ((X : ℂ) ^ (-(s - 1 / 2)))⁻¹ = (X : ℂ) ^ (s - 1 / 2) := by
      rw [Complex.cpow_neg,inv_inv]
    rw [hinv]
  have hcoeff : ((Real.sqrt a : ℂ) * (b : ℂ))⁻¹ =
      (a : ℂ) ^ (-(1 / 2 : ℂ)) * (b : ℂ) ^ (-(1 : ℂ)) := by
    simp only [hsqrt,mul_inv,Complex.cpow_neg,Complex.cpow_one]
  rw [hscale,hcoeff]
  symm
  calc
    _ = ((a : ℂ) ^ (-(1 / 2 : ℂ)) * (a : ℂ) ^ (-(s - 1 / 2))) *
        ((b : ℂ) ^ (-(1 : ℂ)) * (b : ℂ) ^ ((3 : ℂ) * (-(s - 1 / 2)))) *
          (X : ℂ) ^ (s - 1 / 2) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ han,← Complex.cpow_add _ _ hbn]
      have h1 : -(1 / 2 : ℂ) + -(s - 1 / 2) = -s := by ring
      have h2 : -(1 : ℂ) + 3 * -(s - 1 / 2) = -3 * s + 1 / 2 := by ring
      rw [h1,h2]


/-- Evaluation of each actual source mode by Mellin inversion, including
zero support and both ideal normalization factors. -/
theorem source_mode_mellin_inversion (c : ArithmeticContext) (Ψ : Ideal O → ℂ)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) (σ : ℝ) (nb : Ideal O × Ideal O) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ u : ℝ,
      mellinTransform (fun x => (Real.sqrt x : ℂ) * W x) (contourPoint σ u - 1 / 2) *
        (X : ℂ) ^ (contourPoint σ u - 1 / 2) *
        sourceDirichletTerm c Ψ (contourPoint σ u) nb) =
      sourceWeightedTerm c Ψ W X nb := by
  by_cases hn : SquarefreeOutside c.S nb.1 ∧ Outside c.S nb.2
  swap
  · simp only [sourceDirichletTerm,sourceWeightedTerm,ite_eq_right hn,mul_zero,
      integral_zero]
  let V : ℝ → ℂ := fun x => (Real.sqrt x : ℂ) * W x
  let y : ℝ := normIdeal nb.1 * normIdeal nb.2 ^ (3 : ℕ) / X
  let a : ℂ := (star (alpha nb.1) * gauss 2 nb.1 * Ψ nb.1 *
    star (alpha nb.2) ^ (3 : ℕ) * Ψ nb.2 ^ (3 : ℕ)) /
      ((Real.sqrt (normIdeal nb.1) : ℂ) * (normIdeal nb.2 : ℂ))
  have hnpos := normIdeal_pos hn.1.1.1
  have hbpos := normIdeal_pos hn.2.1
  have hy : 0 < y := by dsimp only [y]; positivity
  have hpoint (u : ℝ) : contourPoint σ u - 1 / 2 = contourPoint (σ - 1 / 2) u := by
    unfold contourPoint
    push_cast
    ring
  have heq (u : ℝ) :
      mellinTransform V (contourPoint σ u - 1 / 2) *
        (X : ℂ) ^ (contourPoint σ u - 1 / 2) *
        sourceDirichletTerm c Ψ (contourPoint σ u) nb =
      a * ((y : ℂ) ^ (-contourPoint (σ - 1 / 2) u) *
        mellinTransform V (contourPoint (σ - 1 / 2) u)) := by
    rw [sourceDirichletTerm,ite_eq_left hn]
    have h := source_cpow_normalization hnpos hbpos hX (contourPoint σ u)
    dsimp only [a,y]
    rw [← hpoint]
    calc
      _ = (star (alpha nb.1) * gauss 2 nb.1 * Ψ nb.1 *
          star (alpha nb.2) ^ (3 : ℕ) * Ψ nb.2 ^ (3 : ℕ)) *
          ((normIdeal nb.1 : ℂ) ^ (-contourPoint σ u) *
            (normIdeal nb.2 : ℂ) ^ (-(3 : ℂ) * contourPoint σ u + 1 / 2) *
            (X : ℂ) ^ (contourPoint σ u - 1 / 2)) *
          mellinTransform V (contourPoint σ u - 1 / 2) := by ring
      _ = _ := by rw [h]; ring
  change ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ u : ℝ,
    mellinTransform V (contourPoint σ u - 1 / 2) *
      (X : ℂ) ^ (contourPoint σ u - 1 / 2) *
      sourceDirichletTerm c Ψ (contourPoint σ u) nb) = _
  simp_rw [heq]
  rw [integral_const_mul]
  calc
    _ = a * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ u : ℝ, (y : ℂ) ^ (-contourPoint (σ - 1 / 2) u) *
          mellinTransform V (contourPoint (σ - 1 / 2) u)) := by ring
    _ = a * V y := by rw [literal_mellin_inversion (sqrt_weight_smoothSupported hW) _ hy]
    _ = _ := by simp only [sourceWeightedTerm,ite_eq_left hn,a,V,y]; ring

theorem source_weight_multiplier_integrable {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) {X : ℝ} (hX : 0 < X) (σ : ℝ) :
    Integrable (fun u : ℝ => mellinTransform V (contourPoint σ u - 1 / 2) *
      (X : ℂ) ^ (contourPoint σ u - 1 / 2)) := by
  have hpoint (u : ℝ) : contourPoint σ u - 1 / 2 = contourPoint (σ - 1 / 2) u := by
    unfold contourPoint
    push_cast
    ring
  simp_rw [hpoint,mellin_literal_eq_standard]
  have hm := compact_mellin_verticalIntegrable hV (σ - 1 / 2)
  have hd := compact_source_mellin_differentiable V I.lo I.hi I.lo_pos hV.2 hV.1
  have hcM : Continuous (fun u : ℝ => mellin V (contourPoint (σ - 1 / 2) u)) :=
    hd.continuous.comp (by unfold contourPoint; fun_prop)
  have hcX : Continuous (fun u : ℝ => (X : ℂ) ^ (contourPoint (σ - 1 / 2) u)) :=
    (show Continuous (contourPoint (σ - 1 / 2)) by unfold contourPoint; fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  apply (hm.norm.mul_const (X ^ (σ - 1 / 2))).mono'
    (hcM.mul hcX).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    simp only [Pi.mul_apply]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [contourPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,mul_zero,zero_mul,sub_zero,add_zero,le_refl])

/-- The literal completed sum is the original source integral, with no
termwise-interchange or convergence obligation left as a hypothesis. -/
theorem completedSum_source_integral (c : ArithmeticContext) (Ψ : Ideal O → ℂ)
    (F : ℂ → ℂ) (hF : SourceContinuation c Ψ F)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) (σ : ℝ) (hσ : 2 < σ) :
    completedSum c Ψ W X = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ u : ℝ, sourceMellinIntegrand (fun x => (Real.sqrt x : ℂ) * W x)
        X F (contourPoint σ u) := by
  let V : ℝ → ℂ := fun x => (Real.sqrt x : ℂ) * W x
  have hterm := sourceDirichlet_integral_termwise c Ψ F hF σ hσ
    (fun u => mellinTransform V (contourPoint σ u - 1 / 2) *
      (X : ℂ) ^ (contourPoint σ u - 1 / 2))
    (source_weight_multiplier_integrable (sqrt_weight_smoothSupported hW) hX σ)
  rw [completedSum_eq_joint c Ψ hW hX]
  simp only [sourceMellinIntegrand,← mellin_literal_eq_standard]
  rw [hterm,← tsum_mul_left]
  apply tsum_congr
  intro nb
  exact (source_mode_mellin_inversion c Ψ hW hX σ nb).symm


theorem lambda_ne_zero : lambda ≠ 0 := by
  have hw : omega ^ 2 + omega + 1 = 0 := by
    simpa only [omega,IsUnit.unit_spec] using
      IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ K)
  have hl : lambda ^ 2 = (-3 : O) := by
    unfold lambda
    linear_combination 4 * hw
  intro h
  rw [h,zero_pow (by decide)] at hl
  norm_num at hl

theorem dual_frequency_ne_zero {m : O} (hm : m ≠ 0) :
    embedding lambda ^ (-4 : ℤ) * embedding m ≠ 0 := by
  have hLam : embedding lambda ≠ 0 := by
    rw [← embedding_zero]
    exact fun h => lambda_ne_zero (embedding_injective h)
  have hm' : embedding m ≠ 0 := by
    rw [← embedding_zero]
    exact fun h => hm (embedding_injective h)
  exact mul_ne_zero (zpow_ne_zero _ hLam) hm'

theorem normElement_pos_of_ne_zero {z : O} (hz : z ≠ 0) : 0 < normElement z := by
  have hp : principal z ≠ ⊥ := by
    intro h
    exact hz (Ideal.span_singleton_eq_bot.mp h)
  exact normIdeal_pos hp

/-- The actual dual coefficient has constant modulus along vertical lines. -/
theorem dualDirichletTerm_vertical_norm (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (σ u : ℝ) (m : O) :
    ‖dualDirichletTerm d A j (contourPoint σ u) m‖ =
      ‖dualDirichletTerm d A j (σ : ℂ) m‖ := by
  unfold dualDirichletTerm
  split_ifs with hm
  · rfl
  · have hq : 0 < Complex.normSq (embedding lambda ^ (-4 : ℤ) * embedding m) :=
      Complex.normSq_pos.mpr (dual_frequency_ne_zero hm)
    simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hq]
    congr 1
    simp [contourPoint]

/-- The dual Dirichlet series may be integrated on any of its convergent
vertical lines against an actual L1 multiplier. -/
theorem dualDirichlet_integral_termwise (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (σ : ℝ)
    (hsum : Summable (dualDirichletTerm d A j (σ : ℂ)))
    (k : ℝ → ℂ) (hk : Integrable k) :
    (∫ u : ℝ, k u * dualDirichlet d A j (contourPoint σ u)) =
      ∑' m : O, ∫ u : ℝ, k u * dualDirichletTerm d A j (contourPoint σ u) m := by
  let f : O → ℝ → ℂ := fun m u => dualDirichletTerm d A j (contourPoint σ u) m
  have hmeas (m : O) : AEStronglyMeasurable (f m) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [f,dualDirichletTerm]
    split_ifs with hm
    · exact continuous_const
    · have hq : 0 < Complex.normSq (embedding lambda ^ (-4 : ℤ) * embedding m) :=
        Complex.normSq_pos.mpr (dual_frequency_ne_zero hm)
      exact continuous_const.mul ((show Continuous (fun u : ℝ => -contourPoint σ u) by
        unfold contourPoint; fun_prop).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne')))
  have hnorm (m : O) (u : ℝ) : ‖f m u‖ = ‖f m 0‖ :=
    (dualDirichletTerm_vertical_norm d A j σ u m).trans
      (dualDirichletTerm_vertical_norm d A j σ 0 m).symm
  have hsum' : Summable (fun m => ‖f m 0‖) := by
    simpa only [f,contourPoint,Complex.ofReal_zero,zero_mul,add_zero] using hsum.norm
  exact (integral_tsum_constant_norm f k hk hmeas hnorm hsum').symm

/-- The scalar normalization of a nonzero dual frequency. -/
theorem dual_cpow_normalization {q r X : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hX : 0 < X) (t : ℂ) :
    (q : ℂ) ^ (-(1 / 2 + t)) * (r : ℂ) ^ (2 * t) * (X : ℂ) ^ (-t) =
      (Real.sqrt q : ℂ)⁻¹ * ((q * X / r ^ (2 : ℕ) : ℝ) : ℂ) ^ (-t) := by
  have hqn : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hsqrt : (Real.sqrt q : ℂ) = (q : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hq.le]
    norm_num
  have hrpow (s : ℂ) : ((r ^ (2 : ℕ) : ℝ) : ℂ) ^ s = (r : ℂ) ^ ((2 : ℂ) * s) := by
    simpa only [Real.rpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hr.le (2 : ℝ) s).symm
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hq.le hX.le,hrpow]
  have hinv : ((r : ℂ) ^ (2 * -t))⁻¹ = (r : ℂ) ^ (2 * t) := by
    rw [mul_neg,Complex.cpow_neg,inv_inv]
  simp only [div_eq_mul_inv]
  rw [hinv,hsqrt,← Complex.cpow_neg]
  calc
    _ = (q : ℂ) ^ (-(1 / 2 + t)) * (r : ℂ) ^ (2 * t) * (X : ℂ) ^ (-t) := rfl
    _ = ((q : ℂ) ^ (-(1 / 2 : ℂ)) * (q : ℂ) ^ (-t)) *
        (X : ℂ) ^ (-t) * (r : ℂ) ^ (2 * t) := by
      rw [← Complex.cpow_add _ _ hqn]
      have he : -(1 / 2 : ℂ) + -t = -(1 / 2 + t) := by ring
      rw [he]
      ring
    _ = _ := by ring


def dualMellinMultiplier (V : ℝ → ℂ) (r X τ u : ℝ) : ℂ :=
  let t := contourPoint τ u
  mellinTransform V (-t) * reflectionGammaFactor (1 / 2 - t) *
    (r : ℂ) ^ (2 * t) * (X : ℂ) ^ (-t)

theorem dual_multiplier_eq_inverse (V : ℝ → ℂ) {r X : ℝ} (hr : 0 < r)
    (hX : 0 < X) (τ u : ℝ) :
    dualMellinMultiplier V r X τ u =
      inverseMellinIntegrand V 0 (thetaMellinScale * X / r ^ (2 : ℕ)) (contourPoint τ u) := by
  have hs := dual_cpow_normalization (q := 1) (by norm_num) hr hX (contourPoint τ u)
  simp only [Complex.ofReal_one,Complex.one_cpow,one_mul,Real.sqrt_one,inv_one] at hs
  dsimp only [dualMellinMultiplier,inverseMellinIntegrand,mellinEulerData,mellinData]
  rw [reflectionGammaFactor_half_sub]
  have harg : thetaMellinScale * X / r ^ (2 : ℕ) = thetaMellinScale * (X / r ^ (2 : ℕ)) := by ring
  rw [harg,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg thetaMellinScale_pos.le (by positivity)]
  rw [← hs]
  simp only [mellin_literal_eq_standard,pow_zero,one_mul,thetaMellinScale,gammaMultiplier]
  ring

theorem dual_multiplier_integrable {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) {r X : ℝ} (hr : 0 < r) (hX : 0 < X)
    (τ : ℝ) (hτ : -(1 / 4 : ℝ) ≤ τ) : Integrable (dualMellinMultiplier V r X τ) := by
  change Integrable (fun u : ℝ => dualMellinMultiplier V r X τ u)
  simp_rw [dual_multiplier_eq_inverse V hr hX]
  exact inverseMellinIntegrand_vertical_integrable V I.lo I.hi I.lo_pos hV.2 hV.1
    ⌈τ⌉₊ 0 τ ⟨hτ,Nat.le_ceil τ⟩ _
      (div_pos (mul_pos thetaMellinScale_pos hX) (sq_pos_of_pos hr))

/-- Evaluation of the actual nonzero dual modes, with the literal
1/‖ell‖ factor in dualThetaSum. -/
theorem dual_mode_mellin_integral (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) {X : ℝ} (hX : 0 < X)
    (hden : reflectionDenominator d A ≠ 0) (τ : ℝ) (hτ : -(1 / 4 : ℝ) ≤ τ)
    (m : O) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ u : ℝ,
      dualMellinMultiplier V (normElement (reflectionDenominator d A)) X τ u *
        dualDirichletTerm d A j (contourPoint (τ + 1 / 2) u) m) =
      (if m = 0 then 0 else
        let ell := embedding lambda ^ (-4 : ℤ) * embedding m
        cuspCoefficient d.cusp ell * (ell / (‖ell‖ : ℂ)) / (‖ell‖ : ℂ) *
          d.phase m * (∏ p ∈ A, thetaLocalFactor p (j p) m) *
          thetaWeight V (Complex.normSq ell * X /
            normElement (reflectionDenominator d A) ^ (2 : ℕ))) := by
  by_cases hm : m = 0
  · simp only [dualDirichletTerm,ite_eq_left hm,mul_zero,integral_zero]
  let ell := embedding lambda ^ (-4 : ℤ) * embedding m
  let q : ℝ := Complex.normSq ell
  let r : ℝ := normElement (reflectionDenominator d A)
  let b : ℂ := cuspCoefficient d.cusp ell * (ell / (‖ell‖ : ℂ)) *
    d.phase m * (∏ p ∈ A,thetaLocalFactor p (j p) m)
  have hq : 0 < q := Complex.normSq_pos.mpr (dual_frequency_ne_zero hm)
  have hr : 0 < r := normElement_pos_of_ne_zero hden
  have hy : 0 < q * X / r ^ (2 : ℕ) := by positivity
  have hroot : Real.sqrt q = ‖ell‖ := by
    rw [show q = ‖ell‖ ^ 2 from Complex.normSq_eq_norm_sq ell,Real.sqrt_sq (norm_nonneg _)]
  have hpoint (u : ℝ) : contourPoint (τ + 1 / 2) u = 1 / 2 + contourPoint τ u := by
    unfold contourPoint
    push_cast
    ring
  have heq (u : ℝ) :
      dualMellinMultiplier V r X τ u *
        dualDirichletTerm d A j (contourPoint (τ + 1 / 2) u) m =
      (b / (‖ell‖ : ℂ)) * (mellinTransform V (-contourPoint τ u) *
        reflectionGammaFactor (1 / 2 - contourPoint τ u) *
        ((q * X / r ^ (2 : ℕ) : ℝ) : ℂ) ^ (-contourPoint τ u)) := by
    simp only [dualDirichletTerm,ite_eq_right hm,dualMellinMultiplier,hpoint]
    change _ = _
    have h := dual_cpow_normalization hq hr hX (contourPoint τ u)
    rw [hroot] at h
    dsimp only [b,q,r,ell] at h ⊢
    calc
      _ = (cuspCoefficient d.cusp (embedding lambda ^ (-4 : ℤ) * embedding m) *
          ((embedding lambda ^ (-4 : ℤ) * embedding m) /
            (‖embedding lambda ^ (-4 : ℤ) * embedding m‖ : ℂ)) * d.phase m *
            (∏ p ∈ A,thetaLocalFactor p (j p) m)) *
          (mellinTransform V (-contourPoint τ u) *
            reflectionGammaFactor (1 / 2 - contourPoint τ u)) *
          (((Complex.normSq (embedding lambda ^ (-4 : ℤ) * embedding m) : ℝ) : ℂ) ^
            (-(1 / 2 + contourPoint τ u)) *
            (normElement (reflectionDenominator d A) : ℂ) ^ (2 * contourPoint τ u) *
            (X : ℂ) ^ (-contourPoint τ u)) := by ring
      _ = _ := by rw [h]; ring
  change ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ u : ℝ,
    dualMellinMultiplier V r X τ u *
      dualDirichletTerm d A j (contourPoint (τ + 1 / 2) u) m) = _
  simp_rw [heq]
  rw [integral_const_mul]
  rw [ite_eq_right hm]
  calc
    _ = (b / (‖ell‖ : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ u : ℝ, mellinTransform V (-contourPoint τ u) *
          reflectionGammaFactor (1 / 2 - contourPoint τ u) *
          ((q * X / r ^ (2 : ℕ) : ℝ) : ℂ) ^ (-contourPoint τ u)) := by ring
    _ = (b / (‖ell‖ : ℂ)) * thetaWeight V (q * X / r ^ (2 : ℕ)) := by
      rw [← thetaWeight_reflection_integral hV τ hτ hy]
    _ = _ := by dsimp only [b,q,r,ell]; ring

/-- The literal dual theta sum equals its absolutely justified shifted
Mellin integral on every convergent dual Dirichlet line. -/
theorem dualThetaSum_mellin_integral (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) {I : SupportInterval} {V : ℝ → ℂ}
    (hV : SmoothSupported I V) {X : ℝ} (hX : 0 < X)
    (hden : reflectionDenominator d A ≠ 0) (τ : ℝ) (hτ : -(1 / 4 : ℝ) ≤ τ)
    (hsum : Summable (dualDirichletTerm d A j ((τ + 1 / 2 : ℝ) : ℂ))) :
    dualThetaSum d A j V X = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ u : ℝ, dualMellinMultiplier V (normElement (reflectionDenominator d A)) X τ u *
        dualDirichlet d A j (contourPoint (τ + 1 / 2) u) := by
  rw [dualDirichlet_integral_termwise d A j (τ + 1 / 2) hsum _
    (dual_multiplier_integrable hV (normElement_pos_of_ne_zero hden) hX τ hτ),
    ← tsum_mul_left]
  unfold dualThetaSum
  apply tsum_congr
  intro m
  exact (dual_mode_mellin_integral d A j hV hX hden τ hτ m).symm


theorem integrable_mul_tsum_constant_norm {ι : Type*} [Countable ι]
    (f : ι → ℝ → ℂ) (k : ℝ → ℂ) (hk : Integrable k)
    (hmeas : ∀ i, AEStronglyMeasurable (f i))
    (hnorm : ∀ i u, ‖f i u‖ = ‖f i 0‖)
    (hsum : Summable (fun i => ‖f i 0‖)) :
    Integrable (fun u : ℝ => k u * ∑' i, f i u) := by
  have hgm : AEStronglyMeasurable (fun u : ℝ => ∑' i, f i u) :=
    (AEMeasurable.tsum (fun i => (hmeas i).aemeasurable)).aestronglyMeasurable
  apply (hk.norm.mul_const (∑' i, ‖f i 0‖)).mono' (hk.aestronglyMeasurable.mul hgm)
  filter_upwards [] with u
  simp only [Pi.mul_apply,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hsum' : Summable (fun i => ‖f i u‖) := by simpa only [hnorm] using hsum
  simpa only [hnorm] using norm_tsum_le_tsum_norm hsum'

theorem dualDirichletTerm_vertical_continuous (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (σ : ℝ) (m : O) :
    Continuous (fun u : ℝ => dualDirichletTerm d A j (contourPoint σ u) m) := by
  dsimp only [dualDirichletTerm]
  split_ifs with hm
  · exact continuous_const
  · have hq : 0 < Complex.normSq (embedding lambda ^ (-4 : ℤ) * embedding m) :=
      Complex.normSq_pos.mpr (dual_frequency_ne_zero hm)
    exact continuous_const.mul ((show Continuous (fun u : ℝ => -contourPoint σ u) by
      unfold contourPoint; fun_prop).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne')))

theorem dualDirichlet_multiplier_integrable (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (σ : ℝ)
    (hsum : Summable (dualDirichletTerm d A j (σ : ℂ)))
    (k : ℝ → ℂ) (hk : Integrable k) :
    Integrable (fun u : ℝ => k u * dualDirichlet d A j (contourPoint σ u)) := by
  let f : O → ℝ → ℂ := fun m u => dualDirichletTerm d A j (contourPoint σ u) m
  apply integrable_mul_tsum_constant_norm f k hk
  · intro m
    exact (dualDirichletTerm_vertical_continuous d A j σ m).aestronglyMeasurable
  · intro m u
    exact (dualDirichletTerm_vertical_norm d A j σ u m).trans
      (dualDirichletTerm_vertical_norm d A j σ 0 m).symm
  · simpa only [f,contourPoint,Complex.ofReal_zero,zero_mul,add_zero] using hsum.norm

/-- The supplied reflection equation identifies the continued source
integrand with the actual finite family of dual Dirichlet integrands. -/
theorem reflected_source_integrand {N : ℕ} (data : Fin N → ReflectionDatum)
    (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (coeff : Fin N → Finset (Ideal O) → ℂ) (F : ℂ → ℂ)
    (hF : HasReflectionEquation data P j coeff F)
    (V : ℝ → ℂ) (X : ℝ) (u : ℝ) :
    sourceMellinIntegrand V X F (1 / 2 - contourPoint (7 / 2) u) =
      ∑ h : Fin N, ∑ A ∈ P.powerset,
        if AdmissibleActive P j A then coeff h A *
          (dualMellinMultiplier V (normElement (reflectionDenominator (data h) A)) X (7 / 2) u *
            dualDirichlet (data h) A j (contourPoint 4 u)) else 0 := by
  have hs : (1 / 2 - contourPoint (7 / 2) u).re < -1 := by
    norm_num [contourPoint,Complex.sub_re,Complex.mul_re]
  have heq := hF.2 _ hs
  have h0 : (1 / 2 - contourPoint (7 / 2) u) - 1 / 2 = -contourPoint (7 / 2) u := by ring
  have h1 : 1 - 2 * (1 / 2 - contourPoint (7 / 2) u) = 2 * contourPoint (7 / 2) u := by ring
  have h2 : 1 - (1 / 2 - contourPoint (7 / 2) u) = contourPoint 4 u := by
    unfold contourPoint
    push_cast
    ring
  rw [sourceMellinIntegrand,heq,h0]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro A _
  by_cases ha : AdmissibleActive P j A
  · simp only [ite_eq_left ha,h1,h2]
    dsimp only [dualMellinMultiplier]
    rw [mellin_literal_eq_standard]
    ring
  · simp only [ite_eq_right ha,mul_zero]

/-- All analytic interchanges for the finite reflected family are now
justified by the supplied convergent dual Dirichlet series. -/
theorem reflected_source_integral {N : ℕ} (data : Fin N → ReflectionDatum)
    (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (coeff : Fin N → Finset (Ideal O) → ℂ) (F : ℂ → ℂ)
    (hdual : DualDirichletConvergence data P j)
    (href : HasReflectionEquation data P j coeff F)
    {I : SupportInterval} {V : ℝ → ℂ} (hV : SmoothSupported I V)
    {X : ℝ} (hX : 0 < X) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ u : ℝ, sourceMellinIntegrand V X F (1 / 2 - contourPoint (7 / 2) u)) =
      ∑ h : Fin N, ∑ A ∈ P.powerset,
        if AdmissibleActive P j A then coeff h A * dualThetaSum (data h) A j V X else 0 := by
  have hfour : (7 / 2 : ℝ) + 1 / 2 = 4 := by norm_num
  have hint (h : Fin N) (A : Finset (Ideal O)) :
      Integrable (fun u : ℝ => if AdmissibleActive P j A then coeff h A *
        (dualMellinMultiplier V (normElement (reflectionDenominator (data h) A)) X (7 / 2) u *
          dualDirichlet (data h) A j (contourPoint 4 u)) else 0) := by
    by_cases ha : AdmissibleActive P j A
    · simp only [ite_eq_left ha]
      exact (dualDirichlet_multiplier_integrable (data h) A j 4
        (hdual h A ha 4 (by norm_num)) _
        (dual_multiplier_integrable hV (normElement_pos_of_ne_zero (href.1 h A ha)) hX
          (7 / 2) (by norm_num))).const_mul (coeff h A)
    · simpa only [ite_eq_right ha] using (integrable_zero ℝ ℂ volume : Integrable (fun _ : ℝ => (0 : ℂ)))
  simp_rw [reflected_source_integrand data P j coeff F href V X]
  rw [integral_finset_sum _ (fun h _ => integrable_finsetSum _ (fun A _ => hint h A))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [integral_finset_sum _ (fun A _ => hint h A)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases ha : AdmissibleActive P j A
  · simp only [ite_eq_left ha]
    rw [integral_const_mul]
    have hd := dualThetaSum_mellin_integral (data h) A j hV hX (href.1 h A ha)
      (7 / 2) (by norm_num) (by simpa only [hfour,Complex.ofReal_ofNat] using hdual h A ha 4 (by norm_num))
    rw [hfour] at hd
    rw [hd]
    ring
  · simp only [ite_eq_right ha,integral_zero,mul_zero]

end QRHShort.CloudBatch.ReflectionMellin

namespace QRHShort.CloudBatch

/-- Exact Mellin transfer from the original source continuation and its
functional equation; no additional contour or convergence input is assumed. -/
theorem reflection_mellin_transfer_proved : ReflectionProof.ReflectionMellinTransferStatement := by
  intro c Ψ N data P j coeff F hsource hdual href I W X hW hX
  let V : ℝ → ℂ := fun x => (Real.sqrt x : ℂ) * W x
  have hV : SmoothSupported I V := ReflectionMellin.sqrt_weight_smoothSupported hW
  have hshift := ReflectionMellin.sourceMellin_contour_shift hV hX hsource.1 hsource.2.2
    (-3) 3 (by norm_num)
  have hflip : (∫ u : ℝ, ReflectionMellin.sourceMellinIntegrand V X F
      (ReflectionMellin.contourPoint (-3) u)) =
      ∫ u : ℝ, ReflectionMellin.sourceMellinIntegrand V X F
        (1 / 2 - ReflectionMellin.contourPoint (7 / 2) u) := by
    rw [← integral_neg_eq_self (fun u : ℝ => ReflectionMellin.sourceMellinIntegrand V X F
      (ReflectionMellin.contourPoint (-3) u)) volume]
    apply integral_congr_ae
    filter_upwards [] with u
    congr 1
    unfold ReflectionMellin.contourPoint
    push_cast
    ring
  rw [ReflectionMellin.completedSum_source_integral c Ψ F hsource hW hX 3 (by norm_num)]
  change ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    (∫ u : ℝ, ReflectionMellin.sourceMellinIntegrand V X F
      (ReflectionMellin.contourPoint 3 u)) = _
  have hshift' :
      (∫ u : ℝ, ReflectionMellin.sourceMellinIntegrand V X F
        (ReflectionMellin.contourPoint (-3) u)) =
      ∫ u : ℝ, ReflectionMellin.sourceMellinIntegrand V X F
        (ReflectionMellin.contourPoint 3 u) := hshift
  rw [← hshift',hflip]
  exact ReflectionMellin.reflected_source_integral data P j coeff F hdual href hV hX

end QRHShort.CloudBatch
