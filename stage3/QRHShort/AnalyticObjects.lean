import QRHShort.Energy
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The Fourier weight and the intermediate forms in §§3 and 6 of paper2.tex.
All sums are literal sums over the Eisenstein integers or their ideals. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace QRHShort

def radialFourier (Φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2 / Real.sqrt 3 : ℂ) * ∫ z : ℂ,
    Φ (Complex.normSq z) * additiveCharacter (-z * (Real.sqrt x : ℂ))

def RadialSchwartz (Φ : ℝ → ℂ) : Prop :=
  ∃ f : SchwartzMap ℂ ℂ, ∀ z : ℂ, f z = Φ (Complex.normSq z)

structure RowWeight where
  value : ℝ → ℝ
  schwartz : RadialSchwartz (fun x => (value x : ℂ))
  nonnegative : ∀ x, 0 ≤ x → 0 ≤ value x
  majorant : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ value x
  fourierCap : ℝ
  cap_pos : 0 < fourierCap
  fourier_support : Function.support (radialFourier (fun x => (value x : ℂ))) ∩
    Set.Ici 0 ⊆ Set.Icc 0 fourierCap

def primeFactors (a : Ideal O) : Finset (Ideal O) :=
  (UniqueFactorizationMonoid.normalizedFactors a).toFinset

def outsideRadical (S : Finset (Ideal O)) (a : Ideal O) : Ideal O :=
  ∏ P ∈ (primeFactors a).filter (fun P => P ∉ S), P

def divisorCount (a : Ideal O) : ℕ := Nat.card {d : Ideal O // d ∣ a}

def chosenGenerator (a : Ideal O) : O :=
  if a = ⊥ then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors a).map
      (fun P => if IsRelPrime P (principal 3) then primaryGenerator P
        else idealGenerator P)).prod

def firstColumn (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) (U : ℝ → ℂ) (ell : ℝ) (y : O) : ℂ :=
  ∑' n : Ideal O, if SquarefreeOutside c.S n ∧ IsRelPrime n t then
    (mobius n : ℂ) * rayValue ξ.val n * star (sexticSymbol n y) *
      sexticSymbol n (primaryGenerator C) ^ (4 : ℕ) *
      sexticSymbol n (primaryGenerator d) * U (normIdeal n / ell)
  else 0

def firstForm (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (ξ : RayCharacter c) (U : ℝ → ℂ) (cI H L F Sigma : ℝ) : ℝ :=
  ∑' C : Ideal O, ∑' t : Ideal O,
    if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L then
      ∑' d : Ideal O, if d ∣ C then
        (H * normIdeal C / (normIdeal d * L ^ (2 : ℕ) * F)) *
        ∑' y : O, Φ.value (normElement y /
          (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ (2 : ℕ)))) *
          ‖firstColumn c ξ C d t U (L / (normIdeal C * normIdeal t)) y‖ ^ 2
      else 0
    else 0

def cubeValues (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (H X F hc : ℝ) : Set ℝ :=
  {v | ∃ b : Ideal O, Outside c.S b ∧ hc < normIdeal b ∧
    1 < X / normIdeal b ^ (3 : ℕ) ∧
    v = energy c ξ W H (X / normIdeal b ^ (3 : ℕ)) F}

def TransferRange (D C H L F Sigma : ℝ) : Prop :=
  1 ≤ H ∧ H ≤ D ^ C ∧ 1 ≤ L ∧ L ≤ D ^ C ∧
  1 ≤ F ∧ F ≤ D ^ C ∧ 1 ≤ Sigma ∧ Sigma ≤ D ^ C ∧ max H (L * F) ≤ Sigma

end QRHShort
