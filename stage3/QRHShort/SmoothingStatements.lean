import QRHShort.AnalyticObjects
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The two smooth-separation lemmas in Appendix B, paper2.tex:3491–3616.
The coefficient is the Fourier transform in logarithmic coordinates, with
the normalization printed in the manuscript. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace QRHShort

abbrev BoxSpace (d : ℕ) := Fin d → ℝ

def SmoothBox {d : ℕ} (I : Fin d → SupportInterval) (K : BoxSpace d → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K ∧
    Function.support K ⊆ {x | ∀ i, x i ∈ Set.Icc (I i).lo (I i).hi}

def multiWeightNorm {d : ℕ} (q : ℕ) (K : BoxSpace d → ℂ) : ℝ :=
  QRHLean3.supZero {r | ∃ j : ℕ, j ≤ q ∧ ∃ x, r = ‖iteratedFDeriv ℝ j K x‖}

def mellinMode {d : ℕ} (x t : BoxSpace d) : ℂ :=
  ∏ i : Fin d, (x i : ℂ) ^ (Complex.I * (t i : ℂ))

def separationCoefficient {d : ℕ} (K : BoxSpace d → ℂ) (t : BoxSpace d) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ (-(d : ℤ)) *
    ∫ y : BoxSpace d, K (fun i => Real.exp (y i)) *
      Complex.exp (-Complex.I * (∑ i : Fin d, t i * y i : ℝ))

def SmoothSeparationStatement : Prop :=
  ∀ (d : ℕ) (I : Fin d → SupportInterval),
    (∀ K : BoxSpace d → ℂ, SmoothBox I K →
      ∀ x : BoxSpace d, (∀ i, 0 < x i) →
        Integrable (fun t => separationCoefficient K t * mellinMode x t) ∧
        K x = ∫ t : BoxSpace d, separationCoefficient K t * mellinMode x t) ∧
    (∀ J q : ℕ, Even q → J + d < q → ∃ C : ℝ, 0 ≤ C ∧
      ∀ K : BoxSpace d → ℂ, SmoothBox I K →
        Integrable (fun t => ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) ∧
        (∫ t : BoxSpace d, ‖separationCoefficient K t‖ * (1 + ‖t‖) ^ J) ≤
          C * multiWeightNorm q K)

def finiteTestSum {R N : ℕ} (a : Fin R → Fin N → ℂ)
    (x : Fin R → Fin N → ℝ) (r : Fin R) (U : ℝ → ℂ) : ℂ :=
  ∑ n : Fin N, a r n * U (x r n)

def SmoothMeanSquareStatement : Prop :=
  ∀ (I Istar : SupportInterval) (m : ℕ), Istar.lo < I.lo → I.hi < Istar.hi →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R N₁ N₂ : ℕ)
      (a₁ : Fin R → Fin N₁ → ℂ) (a₂ : Fin R → Fin N₂ → ℂ)
      (x₁ : Fin R → Fin N₁ → ℝ) (x₂ : Fin R → Fin N₂ → ℝ)
      (w : Fin R → ℝ) (c : Fin R → ℂ) (M₁ M₂ : ℝ)
      (K : Fin R → BoxSpace 2 → ℂ),
      (∀ r n, 0 < x₁ r n) → (∀ r n, 0 < x₂ r n) →
      (∀ r, 0 ≤ w r) → (∀ r, ‖c r‖ ≤ w r) → 0 ≤ M₁ → 0 ≤ M₂ →
      (∀ U : ℝ → ℂ, SmoothSupported Istar U →
        (∑ r : Fin R, w r * ‖finiteTestSum a₁ x₁ r U‖ ^ 2) ≤ M₁ * weightNorm m U ^ 2) →
      (∀ U : ℝ → ℂ, SmoothSupported Istar U →
        (∑ r : Fin R, w r * ‖finiteTestSum a₂ x₂ r U‖ ^ 2) ≤ M₂ * weightNorm m U ^ 2) →
      (∀ r, SmoothBox (fun _ : Fin 2 => I) (K r)) →
      ‖∑ r : Fin R, c r * ∑ n₁ : Fin N₁, ∑ n₂ : Fin N₂,
        a₁ r n₁ * star (a₂ r n₂) * K r ![x₁ r n₁, x₂ r n₂]‖ ≤
        C * Real.sqrt (M₁ * M₂) *
          QRHLean3.supZero {v | ∃ r : Fin R, v = multiWeightNorm (2 * m + 4) (K r)}

end QRHShort
