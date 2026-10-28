import QRHShort.HeckeMultiplicative
import QRHShort.PrimeComparison
import QRHShort.External
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Absolute convergence of the actual ideal Möbius series outside the finite set S.
It follows from the already stated Hecke series input and the elementary bound
on the Möbius function. This file does not assume an Euler product identity.
-/

noncomputable section
open Classical

namespace QRHShort

def mobiusSeriesTerm (c : ArithmeticContext) (s : ℂ) (n : Ideal O) : ℂ :=
  if Outside c.S n then
    (mobius n : ℂ) * c.nu.onIdeal n * (normIdeal n : ℂ) ^ (-s)
  else 0

theorem mobiusSeriesTerm_norm_le (c : ArithmeticContext) (s : ℂ) (n : Ideal O) :
    ‖mobiusSeriesTerm c s n‖ ≤ ‖heckeSeriesTerm c.nu s n‖ := by
  by_cases hn : Outside c.S n
  · rw [mobiusSeriesTerm, if_pos hn, heckeSeriesTerm, if_neg hn.1,
      Complex.cpow_neg, div_eq_mul_inv, mul_assoc, norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_mobius_le_one n) (norm_nonneg _)).trans_eq
      (one_mul _)
  · simp only [mobiusSeriesTerm, if_neg hn, norm_zero, norm_nonneg]

theorem heckeSeriesTerm_norm_summable (χ : HeckeCharacter) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : Ideal O => ‖heckeSeriesTerm χ s n‖) :=
  (HeckeL_hasSum χ s hs).summable.norm

theorem mobiusSeriesTerm_norm_summable (c : ArithmeticContext) (s : ℂ)
    (hs : 1 < s.re) : Summable (fun n : Ideal O => ‖mobiusSeriesTerm c s n‖) := by
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg (mobiusSeriesTerm c s n))
    (mobiusSeriesTerm_norm_le c s) (heckeSeriesTerm_norm_summable c.nu s hs)

theorem mobiusSeriesTerm_summable (c : ArithmeticContext) (s : ℂ) (hs : 1 < s.re) :
    Summable (mobiusSeriesTerm c s) :=
  (mobiusSeriesTerm_norm_summable c s hs).of_norm

def mobiusSeries (c : ArithmeticContext) (s : ℂ) : ℂ :=
  ∑' n : Ideal O, mobiusSeriesTerm c s n

theorem mobiusSeries_hasSum (c : ArithmeticContext) (s : ℂ) (hs : 1 < s.re) :
    HasSum (mobiusSeriesTerm c s) (mobiusSeries c s) :=
  (mobiusSeriesTerm_summable c s hs).hasSum

end QRHShort
