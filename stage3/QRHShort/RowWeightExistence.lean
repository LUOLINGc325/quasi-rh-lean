import QRHShort.AnalyticObjects
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
A real radial band-limited Schwartz majorant. A radial bump supported in the
ball of radius 1/8 has a Fourier transform bounded below on the unit ball.
Squaring and normalizing this transform gives the desired positive weight;
the convolution identity supplies its compact Fourier support.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ComplexConjugate Convolution Pointwise

namespace QRHShort
namespace RowWeightConstruction

private def seed (z : ℂ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((16 : ℝ) • z)

private theorem seed_nonneg (z : ℂ) : 0 ≤ seed z :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc 2 _).1

private theorem seed_zero : seed 0 = 1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace ℂ).eq_one 2 (by norm_num)
  simp

private theorem seed_norm_eq {z w : ℂ} (h : ‖z‖ = ‖w‖) : seed z = seed w := by
  change Real.smoothTransition ((2 - ‖(16 : ℝ) • z‖) / (2 - 1)) =
    Real.smoothTransition ((2 - ‖(16 : ℝ) • w‖) / (2 - 1))
  rw [norm_smul, norm_smul, h]

private theorem seed_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) seed := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have h := (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth
    (2, (16 : ℝ) • z) ⟨by norm_num, Set.mem_univ _⟩
  have hout : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun)
      ((2 : ℝ), (16 : ℝ) • z) :=
    h.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      ⟨by norm_num, Set.mem_univ _⟩)
  have hpair : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => ((2 : ℝ), (16 : ℝ) • w)) z :=
    contDiffAt_const.prodMk (ContDiffAt.const_smul (16 : ℝ) contDiffAt_id)
  exact hout.comp (f := fun w : ℂ => ((2 : ℝ), (16 : ℝ) • w)) z hpair

private theorem seed_support {z : ℂ} (hz : seed z ≠ 0) : ‖z‖ < 1 / 8 := by
  have hm : (16 : ℝ) • z ∈ Function.support
      ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) := hz
  rw [(ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)] at hm
  have hn : 16 * ‖z‖ < 2 := by simpa [Metric.mem_ball, norm_smul] using hm
  linarith

private theorem seed_compact : HasCompactSupport seed := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℂ) (1 / 8))
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using (seed_support hz).le

private def seedSchwartz : SchwartzMap ℂ ℝ := seed_compact.toSchwartzMap seed_smooth

private def bump : SchwartzMap ℂ ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM seedSchwartz

private theorem bump_apply (z : ℂ) : bump z = (seed z : ℂ) := rfl

private theorem bump_compact : HasCompactSupport (bump : ℂ → ℂ) := by
  exact seed_compact.comp_left (g := Complex.ofReal) (by simp)

private def transformed : SchwartzMap ℂ ℂ := 𝓕 bump

private theorem transformed_isometry (A : ℂ ≃ₗᵢ[ℝ] ℂ) (z : ℂ) :
    transformed (A z) = transformed z := by
  have hb : (bump : ℂ → ℂ) ∘ A = bump := by
    funext w
    change (seed (A w) : ℂ) = (seed w : ℂ)
    rw [seed_norm_eq (A.norm_map w)]
  have h := Real.fourier_comp_linearIsometry A (bump : ℂ → ℂ) z
  rw [hb] at h
  exact h.symm

private theorem transformed_neg (z : ℂ) : transformed (-z) = transformed z :=
  transformed_isometry (LinearIsometryEquiv.neg ℝ) z

private theorem transformed_conj (z : ℂ) : conj (transformed z) = transformed (-z) := by
  change conj (𝓕 (bump : ℂ → ℂ) z) = 𝓕 (bump : ℂ → ℂ) (-z)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [smul_eq_mul, bump_apply, map_mul, map_neg, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_right,
    Complex.ofReal_neg, mul_neg, neg_mul]

private theorem transformed_real (z : ℂ) : ((transformed z).re : ℂ) = transformed z := by
  have h := (transformed_conj z).trans (transformed_neg z)
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im h
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

private theorem transformed_radial (z : ℂ) :
    transformed (‖z‖ : ℂ) = transformed z := by
  by_cases hz : z = 0
  · simp [hz]
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let u : ℂ := z / (‖z‖ : ℂ)
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    exact div_self hnorm
  have hu0 : u ≠ 0 := by intro h; simpa [h] using hu
  let A : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { (LinearEquiv.smulOfNeZero ℂ ℂ u hu0).restrictScalars ℝ with
      norm_map' := by intro w; change ‖u * w‖ = ‖w‖; rw [norm_mul, hu, one_mul] }
  have hA : A (‖z‖ : ℂ) = z := by
    change (z / (‖z‖ : ℂ)) * (‖z‖ : ℂ) = z
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hnorm)
  have h := transformed_isometry A (‖z‖ : ℂ)
  rw [hA] at h
  exact h.symm

private def normalization : ℝ := (∫ z : ℂ, seed z) / 2

private theorem normalization_pos : 0 < normalization := by
  apply div_pos _ (by norm_num)
  exact integral_pos_of_integrable_nonneg_nonzero (x := (0 : ℂ)) seed_smooth.continuous
    seedSchwartz.integrable seed_nonneg (by rw [seed_zero]; norm_num)

private theorem modulation_re (t a : ℝ) :
    (Complex.exp ((t : ℂ) * Complex.I) * (a : ℂ)).re = Real.cos t * a := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]

private theorem transformed_lower {z : ℂ} (hz : ‖z‖ ≤ 1) :
    normalization ≤ (transformed z).re := by
  let f : ℂ → ℂ := fun v =>
    Complex.exp (((-2 * Real.pi * inner ℝ v z : ℝ) : ℂ) * Complex.I) * bump v
  have hfcompact : HasCompactSupport f := bump_compact.mul_left
  have hfcontinuous : Continuous f := by dsimp only [f]; fun_prop
  have hfi : Integrable f := hfcontinuous.integrable_of_hasCompactSupport hfcompact
  have hpoint (v : ℂ) : seed v / 2 ≤ (f v).re := by
    have hfre : (f v).re = Real.cos (-2 * Real.pi * inner ℝ v z) * seed v := by
      change (Complex.exp (((-2 * Real.pi * inner ℝ v z : ℝ) : ℂ) * Complex.I)
        * bump v).re = _
      rw [bump_apply, modulation_re]
    rw [hfre]
    by_cases hv : seed v = 0
    · simp only [hv, zero_div, mul_zero, le_refl]
    have hn := seed_support hv
    have hi : |inner ℝ v z| ≤ ‖v‖ :=
      (abs_real_inner_le_norm v z).trans (mul_le_of_le_one_right (norm_nonneg v) hz)
    have hp : |-2 * Real.pi * inner ℝ v z| ≤ 1 := by
      simp only [abs_mul, abs_neg, abs_of_pos Real.pi_pos,
        abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      calc
        2 * Real.pi * |inner ℝ v z| ≤ 2 * Real.pi * ‖v‖ :=
          mul_le_mul_of_nonneg_left hi (by positivity)
        _ ≤ 8 * ‖v‖ := mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four])
          (norm_nonneg v)
        _ ≤ 1 := by linarith
    have hsq : (-2 * Real.pi * inner ℝ v z) ^ 2 ≤ 1 := by
      nlinarith [abs_le.mp hp, sq_abs (-2 * Real.pi * inner ℝ v z)]
    have hcos : (1 : ℝ) / 2 ≤ Real.cos (-2 * Real.pi * inner ℝ v z) := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := -2 * Real.pi * inner ℝ v z)]
    nlinarith [mul_le_mul_of_nonneg_right hcos (seed_nonneg v)]
  have hbound := integral_mono (seedSchwartz.integrable.div_const 2) hfi.re hpoint
  rw [integral_div] at hbound
  change normalization ≤ ∫ v : ℂ, (f v).re at hbound
  have hFourier : transformed z = ∫ v : ℂ, f v := by
    change 𝓕 (bump : ℂ → ℂ) z = _
    rw [Real.fourier_eq']
    rfl
  calc
    normalization ≤ ∫ v : ℂ, (f v).re := hbound
    _ = (∫ v : ℂ, f v).re := integral_re hfi
    _ = (transformed z).re := congrArg Complex.re hFourier.symm

private def square : SchwartzMap ℂ ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) transformed transformed

private def majorantSchwartz : SchwartzMap ℂ ℂ :=
  ((normalization : ℂ)⁻¹) ^ 2 • square

private def weightValue (x : ℝ) : ℝ :=
  ((transformed (Real.sqrt x : ℂ)).re / normalization) ^ 2

private theorem majorant_radial (z : ℂ) :
    majorantSchwartz z = (weightValue (Complex.normSq z) : ℂ) := by
  change ((normalization : ℂ)⁻¹) ^ 2 * (transformed z * transformed z) =
    ((((transformed (Real.sqrt (Complex.normSq z) : ℂ)).re / normalization) ^ 2 : ℝ) : ℂ)
  rw [← Complex.norm_def, transformed_radial, ← transformed_real z]
  simp only [Complex.ofReal_pow, Complex.ofReal_re, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

private theorem weightValue_majorant {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ weightValue x := by
  have hr : ‖(Real.sqrt x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
    exact (Real.sqrt_le_sqrt hx.2).trans_eq (by norm_num)
  have hh : 1 ≤ (transformed (Real.sqrt x : ℂ)).re / normalization :=
    (le_div_iff₀ normalization_pos).mpr (by simpa only [one_mul] using transformed_lower hr)
  change 1 ≤ ((transformed (Real.sqrt x : ℂ)).re / normalization) ^ 2
  nlinarith [sq_nonneg ((transformed (Real.sqrt x : ℂ)).re / normalization - 1)]

private theorem convolution_zero {z : ℂ} (hz : 1 / 4 ≤ ‖z‖) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bump bump z = 0 := by
  rw [SchwartzMap.convolution_apply]
  by_contra h
  have hs := MeasureTheory.support_convolution_subset
    (ContinuousLinearMap.mul ℂ ℂ) h
  rcases Set.mem_add.mp hs with ⟨u, hu, v, hv, huv⟩
  have hu' : ‖u‖ < 1 / 8 := seed_support (by
    intro he; apply hu; simp only [bump_apply, he, Complex.ofReal_zero])
  have hv' : ‖v‖ < 1 / 8 := seed_support (by
    intro he; apply hv; simp only [bump_apply, he, Complex.ofReal_zero])
  have hn := norm_add_le u v
  rw [huv] at hn
  linarith

private theorem majorant_fourier_zero {z : ℂ} (hz : 1 / 4 ≤ ‖z‖) :
    𝓕 majorantSchwartz z = 0 := by
  have hc : 𝓕⁻ square = SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bump bump := rfl
  have he := congrArg (fun f : SchwartzMap ℂ ℂ => f (-z)) hc
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at he
  have hsq : (𝓕 square) z = 0 := by
    rw [SchwartzMap.fourier_coe, he]
    exact convolution_zero (by simpa only [norm_neg] using hz)
  simp only [majorantSchwartz, fourier_smul, SchwartzMap.smul_apply, hsq, smul_zero]

private def frequency (x : ℝ) : ℂ := Complex.I * ((2 * Real.sqrt x / Real.sqrt 3 : ℝ) : ℂ)

private theorem frequency_phase (x : ℝ) (z : ℂ) :
    4 * Real.pi * (-z * (Real.sqrt x : ℂ)).im / Real.sqrt 3 =
      -2 * Real.pi * inner ℝ z (frequency x) := by
  simp only [frequency, Complex.inner, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

private theorem character_eq (x : ℝ) (z : ℂ) :
    additiveCharacter (-z * (Real.sqrt x : ℂ)) =
      Complex.exp (((-2 * Real.pi * inner ℝ z (frequency x) : ℝ) : ℂ) * Complex.I) := by
  unfold additiveCharacter
  rw [frequency_phase]

private theorem radialFourier_eq (x : ℝ) :
    radialFourier (fun y => (weightValue y : ℂ)) x =
      (2 / Real.sqrt 3 : ℂ) * 𝓕 majorantSchwartz (frequency x) := by
  unfold radialFourier
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← majorant_radial z, character_eq]
  exact mul_comm _ _

private theorem frequency_large {x : ℝ} (hx : 1 ≤ x) : 1 / 4 ≤ ‖frequency x‖ := by
  have hsx : 1 ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt hx
  have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  rw [frequency, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (by positivity) hs3pos.le)]
  apply (le_div_iff₀ hs3pos).mpr
  nlinarith

end RowWeightConstruction

open RowWeightConstruction in
/-- Existence of a nonnegative radial Schwartz weight which majorizes `[0,1]`
and whose radial Fourier transform has compact support on the nonnegative axis. -/
theorem rowWeight_nonempty : Nonempty RowWeight := by
  refine ⟨{
    value := weightValue
    schwartz := ⟨majorantSchwartz, majorant_radial⟩
    nonnegative := fun x _ => sq_nonneg _
    majorant := fun x hx => weightValue_majorant hx
    fourierCap := 1
    cap_pos := zero_lt_one
    fourier_support := ?_ }⟩
  intro x hx
  refine ⟨hx.2, ?_⟩
  by_contra h
  apply hx.1
  rw [radialFourier_eq, majorant_fourier_zero (frequency_large (le_of_lt (lt_of_not_ge h))),
    mul_zero]

end QRHShort

#print axioms QRHShort.rowWeight_nonempty
