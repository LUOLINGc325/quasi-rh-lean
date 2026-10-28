import QRHShort.IdealMobiusCancellation
import QRHShort.IdealMobiusSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
The full ideal Möbius series in the absolute convergence half-plane. Its inverse
identity with the actual Hecke continuation follows by grouping an absolutely
convergent product by the product ideal and applying finite divisor cancellation.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

@[simp] theorem heckeSeriesTerm_bot (χ : HeckeCharacter) (s : ℂ) :
    heckeSeriesTerm χ s ⊥ = 0 := by
  simp [heckeSeriesTerm]

@[simp] theorem heckeSeriesTerm_one (χ : HeckeCharacter) (s : ℂ) :
    heckeSeriesTerm χ s 1 = 1 := by
  rw [heckeSeriesTerm]
  simp only [show (1 : Ideal O) ≠ ⊥ by simp, if_neg, normIdeal, χ.onIdeal_one]
  norm_num

theorem heckeSeriesTerm_mul (χ : HeckeCharacter) (s : ℂ) (a b : Ideal O) :
    heckeSeriesTerm χ s (a * b) = heckeSeriesTerm χ s a * heckeSeriesTerm χ s b := by
  by_cases ha : a = ⊥
  · simp only [ha, Ideal.bot_mul, heckeSeriesTerm_bot, zero_mul]
  by_cases hb : b = ⊥
  · simp only [hb, Ideal.mul_bot, heckeSeriesTerm_bot, mul_zero]
  have hab : a * b ≠ ⊥ := mul_ne_zero ha hb
  rw [heckeSeriesTerm, if_neg hab, heckeSeriesTerm, if_neg ha,
    heckeSeriesTerm, if_neg hb, χ.onIdeal_mul, normIdeal_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (normIdeal_pos ha).le (normIdeal_pos hb).le]
  exact mul_div_mul_comm _ _ _ _

def fullMobiusSeriesTerm (χ : HeckeCharacter) (s : ℂ) (n : Ideal O) : ℂ :=
  (mobius n : ℂ) * heckeSeriesTerm χ s n

def fullMobiusSeries (χ : HeckeCharacter) (s : ℂ) : ℂ :=
  ∑' n : Ideal O, fullMobiusSeriesTerm χ s n

theorem fullMobiusSeriesTerm_norm_le (χ : HeckeCharacter) (s : ℂ) (n : Ideal O) :
    ‖fullMobiusSeriesTerm χ s n‖ ≤ ‖heckeSeriesTerm χ s n‖ := by
  rw [fullMobiusSeriesTerm, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_mobius_le_one n) (norm_nonneg _)).trans_eq
    (one_mul _)

theorem fullMobiusSeriesTerm_norm_summable (χ : HeckeCharacter) (s : ℂ)
    (hs : 1 < s.re) : Summable (fun n : Ideal O => ‖fullMobiusSeriesTerm χ s n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fullMobiusSeriesTerm_norm_le χ s) (heckeSeriesTerm_norm_summable χ s hs)

theorem fullMobiusSeriesTerm_summable (χ : HeckeCharacter) (s : ℂ) (hs : 1 < s.re) :
    Summable (fullMobiusSeriesTerm χ s) :=
  (fullMobiusSeriesTerm_norm_summable χ s hs).of_norm

theorem fullMobiusSeries_hasSum (χ : HeckeCharacter) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fullMobiusSeriesTerm χ s) (fullMobiusSeries χ s) :=
  (fullMobiusSeriesTerm_summable χ s hs).hasSum

private def divisorFactorEquiv (n : Ideal O) (hn : n ≠ ⊥) :
    {d : Ideal O // d ∈ idealDivisors n hn} ≃
      {ab : Ideal O × Ideal O // ab.1 * ab.2 = n} where
  toFun d :=
    ⟨(d.val, Classical.choose ((mem_idealDivisors n hn d.val).mp d.property)),
      (Classical.choose_spec ((mem_idealDivisors n hn d.val).mp d.property)).symm⟩
  invFun ab :=
    ⟨ab.val.1, (mem_idealDivisors n hn ab.val.1).mpr
      ⟨ab.val.2, ab.property.symm⟩⟩
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv ab := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    have ha : ab.val.1 ≠ 0 := by
      intro h
      apply hn
      rw [← ab.property, h, zero_mul]
      simp
    apply mul_left_cancel₀ ha
    exact (Classical.choose_spec
      ((mem_idealDivisors n hn ab.val.1).mp
        ((mem_idealDivisors n hn ab.val.1).mpr ⟨ab.val.2, ab.property.symm⟩))).symm.trans
      ab.property.symm

private theorem mobius_product_fiber (χ : HeckeCharacter) (s : ℂ) (n : Ideal O) :
    (∑' ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = n},
      fullMobiusSeriesTerm χ s ab.val.1 * heckeSeriesTerm χ s ab.val.2) =
        if n = 1 then 1 else 0 := by
  by_cases hn : n = ⊥
  · subst n
    rw [if_neg (by simp)]
    have hzero : ∀ ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = (⊥ : Ideal O)},
        fullMobiusSeriesTerm χ s ab.val.1 * heckeSeriesTerm χ s ab.val.2 = 0 := by
      intro ab
      rcases Ideal.mul_eq_bot.mp ab.property with ha | hb
      · simp only [fullMobiusSeriesTerm, ha, heckeSeriesTerm_bot, mul_zero, zero_mul]
      · simp only [hb, heckeSeriesTerm_bot, mul_zero]
    simpa only [hzero] using
      (hasSum_zero : HasSum (fun _ : {ab : Ideal O × Ideal O // ab.1 * ab.2 = (⊥ : Ideal O)} =>
        (0 : ℂ)) 0).tsum_eq
  let e := divisorFactorEquiv n hn
  calc
    (∑' ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = n},
        fullMobiusSeriesTerm χ s ab.val.1 * heckeSeriesTerm χ s ab.val.2) =
      ∑' d : {d : Ideal O // d ∈ idealDivisors n hn},
        fullMobiusSeriesTerm χ s (e d).val.1 * heckeSeriesTerm χ s (e d).val.2 :=
      (e.tsum_eq _).symm
    _ = ∑' d : {d : Ideal O // d ∈ idealDivisors n hn},
        (mobius d.val : ℂ) * heckeSeriesTerm χ s n := by
      apply tsum_congr
      intro d
      rw [fullMobiusSeriesTerm, mul_assoc, ← heckeSeriesTerm_mul, (e d).property] <;> rfl
    _ = (∑ d ∈ idealDivisors n hn, (mobius d : ℂ)) * heckeSeriesTerm χ s n := by
      rw [tsum_mul_right]
      have htsum := Finset.tsum_subtype (idealDivisors n hn)
        (fun d : Ideal O => (mobius d : ℂ))
      rw [htsum]
    _ = if n = 1 then 1 else 0 := by
      rw [sum_idealDivisors_mobius_complex]
      split_ifs with h
      · subst n
        rw [heckeSeriesTerm_one, one_mul]
      · rw [zero_mul]

/-- Euler–Möbius inversion derived from absolute convergence and ideal divisors. -/
theorem heckeL_mul_fullMobiusSeries (χ : HeckeCharacter) (s : ℂ) (hs : 1 < s.re) :
    HeckeL χ s * fullMobiusSeries χ s = 1 := by
  have hpair := (fullMobiusSeries_hasSum χ s hs).mul (HeckeL_hasSum χ s hs)
    (summable_mul_of_summable_norm
      (fullMobiusSeriesTerm_norm_summable χ s hs) (heckeSeriesTerm_norm_summable χ s hs))
  have hgroup := hpair.tsum_fiberwise (fun ab : Ideal O × Ideal O => ab.1 * ab.2)
  change HasSum (fun n : Ideal O =>
    ∑' ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = n},
      fullMobiusSeriesTerm χ s ab.val.1 * heckeSeriesTerm χ s ab.val.2)
    (fullMobiusSeries χ s * HeckeL χ s) at hgroup
  simp_rw [mobius_product_fiber] at hgroup
  have h := hgroup.unique (hasSum_ite_eq (1 : Ideal O) (1 : ℂ))
  simpa only [mul_comm] using h

end QRHShort
