import QRHShort.EnergySupport
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Actual finite-support and change-of-order interfaces for the completed sum.
The cube-column identity is an algebraic expansion of the manuscript definition;
it does not assume multiplicativity or a Möbius inversion formula. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The two-index summand in the definition of `completedSum`. -/
def completedSummand (c : ArithmeticContext) (Ψ : Ideal O → ℂ) (W : ℝ → ℂ)
    (X : ℝ) (n b : Ideal O) : ℂ :=
  if SquarefreeOutside c.S n then
    if Outside c.S b then
      (star (alpha n) * gauss 2 n * Ψ n * star (alpha b) ^ (3 : ℕ) * Ψ b ^ (3 : ℕ)) /
        ((Real.sqrt (normIdeal n) : ℂ) * (normIdeal b : ℂ)) *
        ((Real.sqrt (normIdeal n * normIdeal b ^ (3 : ℕ) / X) : ℂ) *
          W (normIdeal n * normIdeal b ^ (3 : ℕ) / X))
    else 0
  else 0

private theorem one_le_normIdeal_of_ne_bot {n : Ideal O} (hn : n ≠ ⊥) :
    1 ≤ normIdeal n := by
  have hnabs : n.absNorm ≠ 0 := fun h => hn (Ideal.absNorm_eq_zero_iff.mp h)
  change (1 : ℝ) ≤ (n.absNorm : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnabs)

/-- Compact support bounds both the squarefree and cube indices. -/
theorem completedSummand_hasFiniteSupport (c : ArithmeticContext)
    (Ψ : Ideal O → ℂ) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {X : ℝ} (hX : 0 < X) :
    Function.HasFiniteSupport (fun p : Ideal O × Ideal O =>
      completedSummand c Ψ W X p.1 p.2) := by
  let R := max 1 (I.hi * X)
  apply ((finite_normIdeal_le R).prod (finite_normIdeal_le R)).subset
  rintro ⟨n, b⟩ hp
  have hn : SquarefreeOutside c.S n := by
    by_contra hn
    exact hp (by simp only [completedSummand, if_neg hn])
  have hb : Outside c.S b := by
    by_contra hb
    exact hp (by simp only [completedSummand, if_pos hn, if_neg hb])
  have hw : W (normIdeal n * normIdeal b ^ (3 : ℕ) / X) ≠ 0 := by
    intro hw
    exact hp (by simp only [completedSummand, if_pos hn, if_pos hb, hw, mul_zero])
  have ha1 : 1 ≤ normIdeal n := one_le_normIdeal_of_ne_bot hn.1.1
  have hb1 : 1 ≤ normIdeal b := one_le_normIdeal_of_ne_bot hb.1
  have ha0 : 0 ≤ normIdeal n := zero_le_one.trans ha1
  have hb0 : 0 ≤ normIdeal b := zero_le_one.trans hb1
  have hbound : normIdeal n * normIdeal b ^ (3 : ℕ) ≤ I.hi * X :=
    (div_le_iff₀ hX).mp (hW.2 hw).2
  have hbcube : normIdeal b ≤ normIdeal b ^ (3 : ℕ) := by
    calc
      normIdeal b = normIdeal b * 1 := (mul_one _).symm
      _ ≤ normIdeal b * normIdeal b ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hb1) hb0
      _ = normIdeal b ^ (3 : ℕ) := by ring
  constructor
  · exact (le_mul_of_one_le_right ha0 (one_le_pow₀ hb1)).trans
      (hbound.trans (le_max_right _ _))
  · exact hbcube.trans ((le_mul_of_one_le_left (pow_nonneg hb0 _) ha1).trans
      (hbound.trans (le_max_right _ _)))

/-- The full double series is a genuinely summable series. -/
theorem completedSummand_summable (c : ArithmeticContext)
    (Ψ : Ideal O → ℂ) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {X : ℝ} (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => completedSummand c Ψ W X p.1 p.2) :=
  summable_of_hasFiniteSupport (completedSummand_hasFiniteSupport c Ψ hW hX)

/-- The summation over cube indices may be moved outside the squarefree sum. -/
theorem completedSum_eq_tsum_swap (c : ArithmeticContext)
    (Ψ : Ideal O → ℂ) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {X : ℝ} (hX : 0 < X) :
    completedSum c Ψ W X =
      ∑' b : Ideal O, ∑' n : Ideal O, completedSummand c Ψ W X n b := by
  calc
    completedSum c Ψ W X =
        ∑' n : Ideal O, ∑' b : Ideal O, completedSummand c Ψ W X n b := by
      unfold completedSum
      apply tsum_congr
      intro n
      by_cases hn : SquarefreeOutside c.S n
      · simp only [completedSummand, if_pos hn]
      · simp only [completedSummand, if_neg hn, tsum_zero]
    _ = _ := (completedSummand_summable c Ψ hW hX).tsum_comm.symm

private theorem completedSummand_eq_column_term (c : ArithmeticContext)
    (ξ : RayCharacter c) (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (k : O) (f n b : Ideal O) (hn : SquarefreeOutside c.S n) (hb : Outside c.S b) :
    completedSummand c (completedTwist c ξ k f) W X n b =
      (star (alpha b) ^ (3 : ℕ) * completedTwist c ξ k f b ^ (3 : ℕ) /
        (normIdeal b : ℂ)) * (Real.sqrt (X / normIdeal b ^ (3 : ℕ)) : ℂ)⁻¹ *
      (coefficient ξ.val n * sexticSymbol n k *
        sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) *
          W (normIdeal n / (X / normIdeal b ^ (3 : ℕ)))) := by
  have ha : 0 < normIdeal n := lt_of_lt_of_le zero_lt_one
    (one_le_normIdeal_of_ne_bot hn.1.1)
  have hbpos : 0 < normIdeal b := lt_of_lt_of_le zero_lt_one
    (one_le_normIdeal_of_ne_bot hb.1)
  have hL : 0 < X / normIdeal b ^ (3 : ℕ) := div_pos hX (pow_pos hbpos _)
  have harg : normIdeal n * normIdeal b ^ (3 : ℕ) / X =
      normIdeal n / (X / normIdeal b ^ (3 : ℕ)) := by
    field_simp [ne_of_gt hX, ne_of_gt hbpos]
    <;> ring
  have hsqrt : Real.sqrt (normIdeal n * normIdeal b ^ (3 : ℕ) / X) =
      Real.sqrt (normIdeal n) / Real.sqrt (X / normIdeal b ^ (3 : ℕ)) := by
    rw [harg, Real.sqrt_div ha.le]
  have hna : (Real.sqrt (normIdeal n) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr ha))
  have hnb : (normIdeal b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hbpos)
  have hnl : (Real.sqrt (X / normIdeal b ^ (3 : ℕ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hL))
  simp only [completedSummand, if_pos hn, if_pos hb]
  rw [hsqrt]
  simp only [Complex.ofReal_div, harg, completedTwist, if_pos hn.1, if_pos hb, coefficient]
  field_simp [hna, hnb, hnl]
  <;> ring

/-- The actual completed row is a weighted sum of the original columns at the
cube-divided scales, with the exact reciprocal-norm and square-root factors. -/
theorem completedRow_eq_cube_columns (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) (k : O) (f : Ideal O) :
    completedRow c ξ W X k f = ∑' b : Ideal O, if Outside c.S b then
      (star (alpha b) ^ (3 : ℕ) * completedTwist c ξ k f b ^ (3 : ℕ) /
        (normIdeal b : ℂ)) * (Real.sqrt (X / normIdeal b ^ (3 : ℕ)) : ℂ)⁻¹ *
      columnSum c ξ W (X / normIdeal b ^ (3 : ℕ)) k f else 0 := by
  unfold completedRow
  rw [completedSum_eq_tsum_swap c (completedTwist c ξ k f) hW hX]
  apply tsum_congr
  intro b
  by_cases hb : Outside c.S b
  · rw [if_pos hb]
    unfold columnSum
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : SquarefreeOutside c.S n
    · rw [if_pos hn]
      exact completedSummand_eq_column_term c ξ W hX k f n b hn hb
    · simp only [completedSummand, if_neg hn, mul_zero]
  · simp only [if_neg hb]
    trans ∑' _n : Ideal O, (0 : ℂ)
    · apply tsum_congr
      intro n
      simp only [completedSummand, if_neg hb, ite_self]
    · exact tsum_zero

end QRHShort
