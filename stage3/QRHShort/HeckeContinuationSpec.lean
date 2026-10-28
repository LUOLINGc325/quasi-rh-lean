import QRHShort.Arithmetic
import QRHShort.HeckeFamily
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section
namespace QRHShort

/-- The actual ideal Dirichlet series; the zero ideal is omitted by assigning
its term zero. Complex powers use the principal logarithm, which agrees with
the real logarithm on the positive norms of nonzero ideals. -/
def heckeSeriesTerm (χ : HeckeCharacter) (s : ℂ) (a : Ideal O) : ℂ :=
  if a = ⊥ then 0 else χ.onIdeal a / (normIdeal a : ℂ) ^ s

/-- Agreement with the ideal Dirichlet series in its absolute convergence
half-plane and holomorphy away from the possible principal-character pole.
No claim is made about the arbitrarily totalized value at that pole. -/
def HeckeContinuationSpec (χ : HeckeCharacter) (L : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, 1 < s.re → HasSum (heckeSeriesTerm χ s) (L s)) ∧
    AnalyticOnNhd ℂ L {s : ℂ | s ≠ 1 ∨ χ.residue ≠ 1}

end QRHShort
