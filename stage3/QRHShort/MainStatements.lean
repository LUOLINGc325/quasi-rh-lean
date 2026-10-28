import QRHShort.External
import QRHShort.Energy
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! The actual L-functions and counting function in `thm:main` and
`cor:primes-ap`, paper2.tex:73–96. The totalized value at the pole of a
principal L-function is excluded explicitly. -/

noncomputable section
open Classical

namespace QRHShort

def PointwiseMobiusEstimate : Prop :=
  ∀ (c : ArithmeticContext) (I : SupportInterval) (W : ℝ → ℂ) (ε : ℝ),
    SmoothSupported I W → 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ D : ℝ, 2 ≤ D → ‖originalSum c W D 1‖ ≤ C * D ^ ((11 : ℝ) / 12 + ε)

def HeckeZeroFreeStatement : Prop :=
  ∀ (χ : HeckeCharacter) (s : ℂ), (11 : ℝ) / 12 < s.re →
    (s ≠ 1 ∨ χ.residue ≠ 1) → HeckeL χ s ≠ 0

def DirichletZeroFreeStatement : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    (11 : ℝ) / 12 < s.re → (s ≠ 1 ∨ χ ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0

def MainStatement : Prop := HeckeZeroFreeStatement ∧ DirichletZeroFreeStatement

def primeAPCount (x : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p % q = a % q)).card

def PrimeAPStatement : Prop :=
  ∃ C : ℕ, ∀ (x : ℝ) (q a : ℕ), 2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
    Nat.Coprime a q →
    |(primeAPCount x q a : ℝ) -
      (Nat.totient q : ℝ)⁻¹ * ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹| ≤
        (C : ℝ) * x ^ ((11 : ℝ) / 12) * Real.log x

end QRHShort
