import QRHShort.SmoothBilinear
import QRHShort.SmoothMultiNorm
import QRHShort.WeightNorm
import QRHShort.SmoothFourierDecay
import QRHShort.SmoothCutoffModes
import QRHShort.SmoothEnvelope
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.FinCases

/-!
Finite-sum and integral assembly for the row-dependent smooth mean-square lemma.
The final theorem uses the actual logarithmic Fourier coefficients to obtain a
common pointwise majorant before summing over rows.  The weighted L¹ statement
alone does not bound the integral of a supremum over row-dependent kernels.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QRHShort

theorem finiteTestSum_mul_star {R N₁ N₂ : ℕ}
    (a₁ : Fin R → Fin N₁ → ℂ) (a₂ : Fin R → Fin N₂ → ℂ)
    (x₁ : Fin R → Fin N₁ → ℝ) (x₂ : Fin R → Fin N₂ → ℝ)
    (r : Fin R) (U V : ℝ → ℂ) (z : ℂ) :
    z * finiteTestSum a₁ x₁ r U * star (finiteTestSum a₂ x₂ r V) =
      ∑ n₁ : Fin N₁, ∑ n₂ : Fin N₂,
        (a₁ r n₁ * star (a₂ r n₂)) *
          (z * U (x₁ r n₁) * star (V (x₂ r n₂))) := by
  classical
  simp only [finiteTestSum, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  ring

theorem finiteTestSum_kernel_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {R N₁ N₂ : ℕ}
    (a₁ : Fin R → Fin N₁ → ℂ) (a₂ : Fin R → Fin N₂ → ℂ)
    (x₁ : Fin R → Fin N₁ → ℝ) (x₂ : Fin R → Fin N₂ → ℝ)
    (r : Fin R) (K : BoxSpace 2 → ℂ)
    (b : α → ℂ) (U V : α → ℝ → ℂ)
    (hint : ∀ n₁ n₂, Integrable
      (fun t => b t * U t (x₁ r n₁) * star (V t (x₂ r n₂))) μ)
    (hrep : ∀ n₁ n₂, K ![x₁ r n₁, x₂ r n₂] =
      ∫ t, b t * U t (x₁ r n₁) * star (V t (x₂ r n₂)) ∂μ) :
    Integrable (fun t => b t * finiteTestSum a₁ x₁ r (U t) *
      star (finiteTestSum a₂ x₂ r (V t))) μ ∧
    (∑ n₁ : Fin N₁, ∑ n₂ : Fin N₂,
      a₁ r n₁ * star (a₂ r n₂) * K ![x₁ r n₁, x₂ r n₂]) =
      ∫ t, b t * finiteTestSum a₁ x₁ r (U t) *
        star (finiteTestSum a₂ x₂ r (V t)) ∂μ := by
  classical
  let g (n₁ : Fin N₁) (n₂ : Fin N₂) (t : α) :=
    (a₁ r n₁ * star (a₂ r n₂)) *
      (b t * U t (x₁ r n₁) * star (V t (x₂ r n₂)))
  have hg (n₁ : Fin N₁) (n₂ : Fin N₂) : Integrable (g n₁ n₂) μ :=
    (hint n₁ n₂).const_mul _
  have hgs (n₁ : Fin N₁) : Integrable (fun t => ∑ n₂, g n₁ n₂ t) μ :=
    integrable_finsetSum _ (fun n₂ _ => hg n₁ n₂)
  have heq (t : α) : b t * finiteTestSum a₁ x₁ r (U t) *
      star (finiteTestSum a₂ x₂ r (V t)) = ∑ n₁, ∑ n₂, g n₁ n₂ t :=
    finiteTestSum_mul_star a₁ a₂ x₁ x₂ r (U t) (V t) (b t)
  refine ⟨(integrable_finsetSum _ (fun n₁ _ => hgs n₁)).congr
    (Filter.Eventually.of_forall (fun t => (heq t).symm)), ?_⟩
  calc
    _ = ∑ n₁, ∑ n₂, ∫ t, g n₁ n₂ t ∂μ := by
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      rw [hrep n₁ n₂, ← integral_const_mul]
    _ = ∫ t, ∑ n₁, ∑ n₂, g n₁ n₂ t ∂μ := by
      rw [integral_finsetSum _ (fun n₁ _ => hgs n₁)]
      apply Finset.sum_congr rfl
      intro n₁ _
      exact (integral_finsetSum _ (fun n₂ _ => hg n₁ n₂)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun t => (heq t).symm))

/-- The actual separation formula remains valid after inserting a cutoff which
equals one on the support interval.  This does not use a row-uniform estimate. -/
theorem smooth_separation_with_cutoff (hs : SmoothSeparationStatement)
    {I : SupportInterval} {K : BoxSpace 2 → ℂ}
    (hK : SmoothBox (fun _ : Fin 2 => I) K)
    (χ : ℝ → ℂ) (hχ : ∀ x ∈ Set.Icc I.lo I.hi, χ x = 1)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun t : BoxSpace 2 => separationCoefficient K t *
      (χ x * (x : ℂ) ^ (Complex.I * (t 0 : ℂ))) *
      (χ y * (y : ℂ) ^ (Complex.I * (t 1 : ℂ)))) ∧
    K ![x, y] = ∫ t : BoxSpace 2, separationCoefficient K t *
      (χ x * (x : ℂ) ^ (Complex.I * (t 0 : ℂ))) *
      (χ y * (y : ℂ) ^ (Complex.I * (t 1 : ℂ))) := by
  have hpos : ∀ i : Fin 2, 0 < (![x, y] : BoxSpace 2) i := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
  obtain ⟨hi, he⟩ := (hs 2 (fun _ => I)).1 K hK ![x, y] hpos
  have hfix : (χ x * χ y) * K ![x, y] = K ![x, y] := by
    by_cases hzero : K ![x, y] = 0
    · simp only [hzero, mul_zero]
    · have hmem := hK.2 hzero
      have hxI : x ∈ Set.Icc I.lo I.hi := hmem 0
      have hyI : y ∈ Set.Icc I.lo I.hi := hmem 1
      rw [hχ x hxI, hχ y hyI, one_mul, one_mul]
  have hmode (t : BoxSpace 2) : separationCoefficient K t *
      (χ x * (x : ℂ) ^ (Complex.I * (t 0 : ℂ))) *
      (χ y * (y : ℂ) ^ (Complex.I * (t 1 : ℂ))) =
      (χ x * χ y) * (separationCoefficient K t * mellinMode ![x, y] t) := by
    simp only [mellinMode, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  refine ⟨(hi.const_mul (χ x * χ y)).congr
    (Filter.Eventually.of_forall (fun t => (hmode t).symm)), ?_⟩
  calc
    K ![x, y] = (χ x * χ y) * K ![x, y] := hfix.symm
    _ = (χ x * χ y) * ∫ t : BoxSpace 2,
        separationCoefficient K t * mellinMode ![x, y] t := by rw [he]
    _ = ∫ t : BoxSpace 2, (χ x * χ y) *
        (separationCoefficient K t * mellinMode ![x, y] t) :=
      (integral_const_mul _ _).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun t => (hmode t).symm))

/-- The finite mean-square bounds combine without a factor depending on the
number of rows.  `B` is a single pointwise majorant for every row coefficient. -/
theorem smooth_mean_square_bound_of_common_expansion
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Istar : SupportInterval} {m R N₁ N₂ : ℕ}
    (a₁ : Fin R → Fin N₁ → ℂ) (a₂ : Fin R → Fin N₂ → ℂ)
    (x₁ : Fin R → Fin N₁ → ℝ) (x₂ : Fin R → Fin N₂ → ℝ)
    (w : Fin R → ℝ) (c : Fin R → ℂ) {M₁ M₂ : ℝ}
    (K : Fin R → BoxSpace 2 → ℂ)
    (b : Fin R → α → ℂ) (U V : α → ℝ → ℂ) (B p q : α → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hc : ∀ r, ‖c r‖ ≤ w r)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hmean₁ : ∀ F : ℝ → ℂ, SmoothSupported Istar F →
      (∑ r, w r * ‖finiteTestSum a₁ x₁ r F‖ ^ 2) ≤ M₁ * weightNorm m F ^ 2)
    (hmean₂ : ∀ F : ℝ → ℂ, SmoothSupported Istar F →
      (∑ r, w r * ‖finiteTestSum a₂ x₂ r F‖ ^ 2) ≤ M₂ * weightNorm m F ^ 2)
    (hU : ∀ t, SmoothSupported Istar (U t))
    (hV : ∀ t, SmoothSupported Istar (V t))
    (hp : ∀ t, 0 ≤ p t) (hq : ∀ t, 0 ≤ q t)
    (hUnorm : ∀ t, weightNorm m (U t) ≤ p t)
    (hVnorm : ∀ t, weightNorm m (V t) ≤ q t)
    (hB : ∀ t, 0 ≤ B t) (hb : ∀ r t, ‖b r t‖ ≤ B t)
    (hint : ∀ r n₁ n₂, Integrable
      (fun t => b r t * U t (x₁ r n₁) * star (V t (x₂ r n₂))) μ)
    (hrep : ∀ r n₁ n₂, K r ![x₁ r n₁, x₂ r n₂] =
      ∫ t, b r t * U t (x₁ r n₁) * star (V t (x₂ r n₂)) ∂μ)
    (hmass : Integrable (fun t => B t * p t * q t) μ)
    {C : ℝ} (hmass_bound : (∫ t, B t * p t * q t ∂μ) ≤
      C * QRHLean3.supZero {v | ∃ r : Fin R,
        v = multiWeightNorm (2 * m + 4) (K r)}) :
    ‖∑ r : Fin R, c r * ∑ n₁ : Fin N₁, ∑ n₂ : Fin N₂,
      a₁ r n₁ * star (a₂ r n₂) * K r ![x₁ r n₁, x₂ r n₂]‖ ≤
      C * Real.sqrt (M₁ * M₂) *
        QRHLean3.supZero {v | ∃ r : Fin R,
          v = multiWeightNorm (2 * m + 4) (K r)} := by
  classical
  have hrow (r : Fin R) := finiteTestSum_kernel_integral a₁ a₂ x₁ x₂ r
    (K r) (b r) U V (hint r) (hrep r)
  have hu (t : α) : (∑ r, w r * ‖finiteTestSum a₁ x₁ r (U t)‖ ^ 2) ≤
      M₁ * p t ^ 2 := (hmean₁ (U t) (hU t)).trans
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (weightNorm_nonneg (hU t) m) (hp t)).mpr (hUnorm t)) hM₁)
  have hv (t : α) : (∑ r, w r * ‖finiteTestSum a₂ x₂ r (V t)‖ ^ 2) ≤
      M₂ * q t ^ 2 := (hmean₂ (V t) (hV t)).trans
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (weightNorm_nonneg (hV t) m) (hq t)).mpr (hVnorm t)) hM₂)
  have hprod (r : Fin R) : Integrable (fun t => c r * b r t *
      finiteTestSum a₁ x₁ r (U t) * star (finiteTestSum a₂ x₂ r (V t))) μ := by
    convert (hrow r).1.const_mul (c r) using 1
    ext t
    ring
  have heq : (∑ r : Fin R, c r * ∑ n₁ : Fin N₁, ∑ n₂ : Fin N₂,
      a₁ r n₁ * star (a₂ r n₂) * K r ![x₁ r n₁, x₂ r n₂]) =
      ∑ r, ∫ t, c r * b r t * finiteTestSum a₁ x₁ r (U t) *
        star (finiteTestSum a₂ x₂ r (V t)) ∂μ := by
    apply Finset.sum_congr rfl
    intro r _
    rw [(hrow r).2, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  rw [heq]
  calc
    _ ≤ Real.sqrt (M₁ * M₂) * ∫ t, B t * p t * q t ∂μ :=
      weighted_bilinear_integral_common_majorant w c b
        (fun r t => finiteTestSum a₁ x₁ r (U t))
        (fun r t => finiteTestSum a₂ x₂ r (V t)) B p q hw hc hB hp hq hb
        hM₁ hM₂ hu hv hprod hmass
    _ ≤ Real.sqrt (M₁ * M₂) * (C * QRHLean3.supZero
        {v | ∃ r : Fin R, v = multiWeightNorm (2 * m + 4) (K r)}) :=
      mul_le_mul_of_nonneg_left hmass_bound (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Appendix B's smooth mean-square estimate with its exact frozen interface.
The coefficient bound is uniform in the row, and the constant is chosen before
the number of rows, the coefficients, the sample points, and the kernels. -/
theorem smooth_mean_square_of_separation
    (hs : SmoothSeparationStatement) : SmoothMeanSquareStatement := by
  classical
  intro I Istar m hlo hhi
  obtain ⟨χ, F, A, hA, hχone, hFsmooth, hFnorm, hFpower, hFstar⟩ :=
    exists_mellin_cutoff_modes I Istar m hlo hhi
  obtain ⟨D, hD, hDnorm⟩ :=
    separationCoefficient_uniform_row_bound (fun _ : Fin 2 => I) (2 * m + 4)
  let T : ℝ := ∫ t : BoxSpace 2, meanSquareTail t
  have hT : 0 ≤ T := integral_nonneg meanSquareTail_nonneg
  refine ⟨D * A ^ 2 * T, by positivity, ?_⟩
  intro R N₁ N₂ a₁ a₂ x₁ x₂ w c M₁ M₂ K hx₁ hx₂ hw hc hM₁ hM₂ hmean₁ hmean₂ hK
  let S : ℝ := QRHLean3.supZero
    {v | ∃ r : Fin R, v = multiWeightNorm (2 * m + 4) (K r)}
  have hS : 0 ≤ S := row_multiWeightNorm_nonneg (2 * m + 4) K
  let U (t : BoxSpace 2) := F (t 0)
  let V (t : BoxSpace 2) := F (-t 1)
  let p (t : BoxSpace 2) : ℝ := A * (1 + ‖t‖) ^ m
  let B (t : BoxSpace 2) : ℝ := D * S / (1 + ‖t‖) ^ (2 * m + 4)
  have hcoord (t : BoxSpace 2) (i : Fin 2) : |t i| ≤ ‖t‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm t i
  have hFbound (t : BoxSpace 2) (u : ℝ) (hu : |u| ≤ ‖t‖) :
      weightNorm m (F u) ≤ p t := by
    exact (hFnorm u).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + |u| ≤ 1 + ‖t‖) m) hA)
  have hp (t : BoxSpace 2) : 0 ≤ p t := mul_nonneg hA (by positivity)
  have hU (t : BoxSpace 2) : SmoothSupported Istar (U t) := hFsmooth (t 0)
  have hV (t : BoxSpace 2) : SmoothSupported Istar (V t) := hFsmooth (-t 1)
  have hUnorm (t : BoxSpace 2) : weightNorm m (U t) ≤ p t :=
    hFbound t (t 0) (hcoord t 0)
  have hVnorm (t : BoxSpace 2) : weightNorm m (V t) ≤ p t :=
    hFbound t (-t 1) (by simpa only [abs_neg] using hcoord t 1)
  have hB (t : BoxSpace 2) : 0 ≤ B t :=
    div_nonneg (mul_nonneg hD hS) (by positivity)
  have hb (r : Fin R) (t : BoxSpace 2) : ‖separationCoefficient (K r) t‖ ≤ B t :=
    hDnorm R K hK r t
  have hexp (r : Fin R) (n₁ : Fin N₁) (n₂ : Fin N₂) :
      Integrable (fun t : BoxSpace 2 => separationCoefficient (K r) t *
        U t (x₁ r n₁) * star (V t (x₂ r n₂))) ∧
      K r ![x₁ r n₁, x₂ r n₂] = ∫ t : BoxSpace 2,
        separationCoefficient (K r) t * U t (x₁ r n₁) * star (V t (x₂ r n₂)) := by
    have heq : (fun t : BoxSpace 2 => separationCoefficient (K r) t *
        U t (x₁ r n₁) * star (V t (x₂ r n₂))) =
        (fun t : BoxSpace 2 => separationCoefficient (K r) t *
          (χ (x₁ r n₁) * (x₁ r n₁ : ℂ) ^ (Complex.I * (t 0 : ℂ))) *
          (χ (x₂ r n₂) * (x₂ r n₂ : ℂ) ^ (Complex.I * (t 1 : ℂ)))) := by
      funext t
      change separationCoefficient (K r) t * F (t 0) (x₁ r n₁) *
        star (F (-(t 1)) (x₂ r n₂)) = _
      rw [hFstar, hFpower _ _ (hx₁ r n₁), hFpower _ _ (hx₂ r n₂)]
    rw [heq]
    exact smooth_separation_with_cutoff hs (hK r) χ hχone
      (x₁ r n₁) (x₂ r n₂) (hx₁ r n₁) (hx₂ r n₂)
  have hmass : Integrable (fun t : BoxSpace 2 => B t * p t * p t) :=
    meanSquareEnvelope_integrable m A D S
  have hmass_bound : (∫ t : BoxSpace 2, B t * p t * p t) ≤
      (D * A ^ 2 * T) * QRHLean3.supZero
        {v | ∃ r : Fin R, v = multiWeightNorm (2 * m + 4) (K r)} :=
    le_of_eq (meanSquareEnvelope_integral m A D S)
  exact smooth_mean_square_bound_of_common_expansion (Istar := Istar) (m := m)
    a₁ a₂ x₁ x₂ w c K (fun r => separationCoefficient (K r)) U V B p p
    hw hc hM₁ hM₂ hmean₁ hmean₂ hU hV hp hp hUnorm hVnorm hB hb
    (fun r n₁ n₂ => (hexp r n₁ n₂).1) (fun r n₁ n₂ => (hexp r n₁ n₂).2)
    hmass hmass_bound

end QRHShort

#print axioms QRHShort.finiteTestSum_mul_star
#print axioms QRHShort.finiteTestSum_kernel_integral
#print axioms QRHShort.smooth_separation_with_cutoff
#print axioms QRHShort.smooth_mean_square_bound_of_common_expansion
#print axioms QRHShort.smooth_mean_square_of_separation
