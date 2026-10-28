import QRHShort.SecondPoissonStatements
import QRHShort.SecondPoissonCounting
import QRHShort.WeightNorm

/-! The zero-frequency estimate of `lem:arithmetic-poisson`, independently of
the nonzero-frequency arithmetic and Poisson identities. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SecondPoissonProof

def ZeroBoundStatement : Prop :=
  ∀ (I : SupportInterval) (Φ : RowWeight), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c : ArithmeticContext) (U : ℝ → ℂ) (C t : Ideal O) (Y ell : ℝ),
      0 < Y → 0 < ell → SmoothSupported I U →
      ‖secondPoissonZero c Φ U C t Y ell‖ ≤ K * Y * ell * weightNorm 0 U ^ 2

theorem norm_euler_factor_le_one {P : Ideal O} (hP : P ≠ ⊥) :
    ‖(1 : ℂ) - (normIdeal P : ℂ)⁻¹‖ ≤ 1 := by
  have hn : 1 ≤ normIdeal P := by
    change (1 : ℝ) ≤ (P.absNorm : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun h => hP (Ideal.absNorm_eq_zero_iff.mp h))
  have hi : (normIdeal P)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hi0 : 0 ≤ (normIdeal P)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hn)
  have he : (1 : ℂ) - (normIdeal P : ℂ)⁻¹ =
      ((1 - (normIdeal P)⁻¹ : ℝ) : ℂ) := by simp
  rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hi)]
  exact sub_le_self 1 hi0

theorem norm_euler_product_le_one (g : Ideal O) :
    ‖∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)‖ ≤ 1 := by
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  apply norm_euler_factor_le_one
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp hP)).ne_zero

def zeroSummand (c : ArithmeticContext) (U : ℝ → ℂ)
    (C t : Ideal O) (ell : ℝ) (g : Ideal O) : ℂ :=
  if SquarefreeOutside c.S g ∧ IsRelPrime g (C * t) then
    (‖U (normIdeal g / ell)‖ ^ 2 : ℝ) *
      ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)
  else 0

theorem zeroSummand_eq_zero_off_support (c : ArithmeticContext)
    {I : SupportInterval} {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C t : Ideal O) {ell : ℝ} (hell : 0 < ell) (g : Ideal O)
    (hg : g ∉ boundedIdeals (I.hi * ell)) :
    zeroSummand c U C t ell g = 0 := by
  unfold zeroSummand
  split_ifs with ha
  · have hzero : U (normIdeal g / ell) = 0 := by
      by_contra hu
      exact hg (mem_boundedIdeals.mpr
        ⟨(div_le_iff₀ hell).mp (hU.2 hu).2, ha.1.1.1⟩)
    simp only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Complex.ofReal_zero, zero_mul]
  · rfl

theorem norm_zeroSummand_le (c : ArithmeticContext)
    {I : SupportInterval} {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C t : Ideal O) (ell : ℝ) (g : Ideal O) :
    ‖zeroSummand c U C t ell g‖ ≤ weightNorm 0 U ^ 2 := by
  unfold zeroSummand
  split_ifs with ha
  · rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg ‖U (normIdeal g / ell)‖)]
    calc
      _ ≤ ‖U (normIdeal g / ell)‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (norm_euler_product_le_one g) (sq_nonneg _)
      _ ≤ weightNorm 0 U ^ 2 := by
        rw [mul_one]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        simpa only [iteratedDeriv_zero] using
          norm_iteratedDeriv_le_weightNorm hU (le_refl 0) (normIdeal g / ell)
  · simpa only [norm_zero] using sq_nonneg (weightNorm 0 U)

theorem secondPoisson_zero_bound : ZeroBoundStatement := by
  obtain ⟨A, hA, hcount⟩ := exists_ideal_count_constant
  intro I Φ
  let B : ℝ := ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖
  refine ⟨B * A * I.hi, mul_nonneg (mul_nonneg (norm_nonneg _) hA.le)
    (I.lo_pos.trans_le I.ordered).le, ?_⟩
  intro c U C t Y ell hY hell hU
  have hfinite : (∑' g : Ideal O, zeroSummand c U C t ell g) =
      ∑ g ∈ boundedIdeals (I.hi * ell), zeroSummand c U C t ell g :=
    tsum_eq_sum (fun g hg => zeroSummand_eq_zero_off_support c hU C t hell g hg)
  have hsum : ‖∑' g : Ideal O, zeroSummand c U C t ell g‖ ≤
      A * (I.hi * ell) * weightNorm 0 U ^ 2 := by
    rw [hfinite]
    calc
      _ ≤ ∑ g ∈ boundedIdeals (I.hi * ell),
          ‖zeroSummand c U C t ell g‖ := norm_sum_le _ _
      _ ≤ ∑ _g ∈ boundedIdeals (I.hi * ell), weightNorm 0 U ^ 2 :=
        Finset.sum_le_sum (fun g _ => norm_zeroSummand_le c hU C t ell g)
      _ = ((boundedIdeals (I.hi * ell)).card : ℝ) *
          weightNorm 0 U ^ 2 := by simp
      _ ≤ A * (I.hi * ell) * weightNorm 0 U ^ 2 :=
        mul_le_mul_of_nonneg_right
          (hcount (I.hi * ell) (mul_pos (I.lo_pos.trans_le I.ordered) hell))
          (sq_nonneg _)
  change ‖(Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
    ∑' g : Ideal O, zeroSummand c U C t ell g‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le]
  calc
    _ ≤ (Y * B) * (A * (I.hi * ell) * weightNorm 0 U ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hY.le (norm_nonneg _))
    _ = _ := by dsimp only [B]; ring

end QRHShort.SecondPoissonProof
