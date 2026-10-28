import QRHShort.AnalyticObjects
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Concrete coefficients and transforms used in the four theta lemmas.
The arithmetic formulas are Dunn--Radziwill, arXiv:2109.07463v3,
(5.7), (5.13), (5.14); they define functions, not extra hypotheses.
The consistency of the coefficient relations and the automorphy laws
are separate obligations. No transformation estimate is assumed here.
-/

noncomputable section
open scoped BigOperators
open Classical MeasureTheory

namespace QRHShort

def lambda : O := 1 + 2 * omega

def breve (z : ℂ) : ℂ :=
  Complex.exp ((2 * Real.pi : ℝ) * Complex.I * (z + star z))

/-- The cubic symbol is defined independently of the sextic symbol, since
the prime above 2 occurs in the theta coefficients. -/
def cubicAtPrime (P : Ideal O) (a : O) : ℂ :=
  ∑ j ∈ Finset.range 3,
    if Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3) =
        Ideal.Quotient.mk P (omega ^ j)
    then embedding (omega ^ j) else 0

def cubicSymbol (n : Ideal O) (a : O) : ℂ :=
  if n = ⊥ then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors n).map
      (fun P => cubicAtPrime P a)).prod

/-- Unnormalized cubic Gauss sum, with the trace character used by DR (2.1). -/
def cubicGauss (r c : O) : ℂ :=
  if h : principal c ≠ ⊥ then
    letI : Finite (O ⧸ principal c) := Ring.HasFiniteQuotients.finiteQuotient h
    letI : Fintype (O ⧸ principal c) := Fintype.ofFinite _
    ∑ x : O ⧸ principal c,
      cubicSymbol (principal c) (residueLift (principal c) x) *
        breve (embedding (r * residueLift (principal c) x) / embedding c)
  else 0

def ninthPhase (j : Fin 3) : ℂ :=
  if j.val = 0 then 1 else
    Complex.exp ((if j.val = 1 then -1 else 1) *
      (2 * Real.pi / 9 : ℝ) * Complex.I)

def PrimaryCubeData (n b : O) : Prop :=
  n ≠ 0 ∧ b ≠ 0 ∧ IsPrimary n ∧ IsPrimary b ∧ Squarefree (principal n)

/-- Nonzero cases in the explicit formula (5.7). The sign ambiguity is
recorded by `s`; the coefficient is even. -/
def TauFormula (ell v : ℂ) : Prop :=
  ∃ n b : O, PrimaryCubeData n b ∧ ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
    ((∃ (k : ℕ) (j : Fin 3), 1 ≤ k ∧
      ell = s * embedding omega ^ j.val *
        embedding lambda ^ ((3 : ℤ) * k - 4) * embedding (n * b ^ 3) ∧
      v = ninthPhase j * star (cubicGauss (omega ^ j.val * lambda ^ 2) n) *
        (‖embedding b / embedding n‖ : ℂ) *
        ((3 : ℝ) ^ ((k : ℝ) / 2 + 2) : ℝ)) ∨
     (∃ k : ℕ,
      ell = s * embedding lambda ^ ((3 : ℤ) * k - 3) * embedding (n * b ^ 3) ∧
      v = star (cubicGauss 1 n) * (‖embedding b / embedding n‖ : ℂ) *
        ((3 : ℝ) ^ ((k : ℝ) / 2 + 5 / 2) : ℝ)))

def tau (ell : ℂ) : ℂ :=
  if h : ∃ v : ℂ, TauFormula ell v then Classical.choose h else 0

/-- Cases in DR (5.13) and (5.14). `second = false` selects tau_1. -/
def AuxiliaryTauFormula (second : Bool) (ell v : ℂ) : Prop :=
  ∃ n b : O, PrimaryCubeData n b ∧ ∃ j : Fin 3,
    ell = (if second then -1 else 1) * embedding omega ^ j.val *
      embedding lambda ^ (-4 : ℤ) * embedding (n * b ^ 3) ∧
    v = 9 * embedding omega ^ (if second then (j.val + 2) % 3 else (j.val + 1) % 3) *
      ninthPhase j * star (cubicGauss (omega ^ j.val * lambda ^ 2) n) *
      (‖embedding b / embedding n‖ : ℂ)

def auxiliaryTau (second : Bool) (ell : ℂ) : ℂ :=
  if h : ∃ v : ℂ, AuxiliaryTauFormula second ell v then Classical.choose h else 0

inductive ThetaCusp where
  | zero | plus | minus
  deriving DecidableEq

instance : Fintype ThetaCusp where
  elems := {ThetaCusp.zero, ThetaCusp.plus, ThetaCusp.minus}
  complete := by
    intro σ
    cases σ <;> simp

def cuspCoefficient (σ : ThetaCusp) (ell : ℂ) : ℂ :=
  star (match σ with
    | .zero => tau (-ell)
    | .plus => embedding omega * auxiliaryTau true (embedding omega * (-ell)) * breve (-ell)
    | .minus => embedding omega ^ 2 *
        auxiliaryTau false (embedding omega ^ 2 * (-ell)) * breve (-ell))

/-- Integral definition of the real modified Bessel function K, for x > 0. -/
def besselK (ν x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)

def thetaMode (ell z : ℂ) (v : ℝ) : ℂ :=
  (v * besselK (1 / 3) (4 * Real.pi * ‖ell‖ * v) : ℝ) * breve (ell * z)

def cubicTheta (z : ℂ) (v : ℝ) : ℂ :=
  ((3 : ℝ) ^ (5 / 2 : ℝ) / 2 * v ^ (2 / 3 : ℝ) : ℝ) +
    ∑' m : O, if m = 0 then 0 else
      tau (embedding lambda ^ (-3 : ℤ) * embedding m) *
        thetaMode (embedding lambda ^ (-3 : ℤ) * embedding m) z v

def thetaMultiplier (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) (n : O) : ℂ :=
  if IsPrimary n ∧ Outside c.S (principal n) then
    sexticSymbol (principal n) lambda ^ (2 : ℕ) *
      completedTwist c ξ k f (principal n)
  else 0

def twistedTheta (φ : O → ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  ∑' m : O, if m = 0 then 0 else
    cuspCoefficient .zero (embedding lambda ^ (-3 : ℤ) * embedding m) * φ m *
      thetaMode (embedding lambda ^ (-3 : ℤ) * embedding m) z v

def finiteFourier (φ : O → ℂ) (q : O) (h : O ⧸ principal q) : ℂ :=
  if hq : principal q ≠ ⊥ then
    letI : Finite (O ⧸ principal q) := Ring.HasFiniteQuotients.finiteQuotient hq
    letI : Fintype (O ⧸ principal q) := Fintype.ofFinite _
    (normElement q : ℂ)⁻¹ * ∑ n : O ⧸ principal q,
      φ (residueLift (principal q) n) *
        additiveCharacter (-embedding (residueLift (principal q) h *
          residueLift (principal q) n) / embedding q)
  else 0

/-- Powers extended by zero, including exponent zero at a multiple of p. -/
def localCharacterPower (p : Ideal O) (j : ℤ) (x : O) : ℂ :=
  if x ∈ p then 0 else sexticSymbol p x ^ j

def thetaLocalFactor (p : Ideal O) (j : Fin 6) (x : O) : ℂ :=
  if j.val = 0 then (Real.sqrt (normIdeal p) : ℂ)⁻¹ * localCharacterPower p (-2) x
  else if j.val = 4 then
    (Real.sqrt (normIdeal p) : ℂ)⁻¹ * (-1 + if x ∈ p then (normIdeal p : ℂ) else 0)
  else localCharacterPower p (-(j.val : ℤ) - 2) x

def mellinTransform (V : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), V x * (x : ℂ) ^ s / (x : ℂ)

/-- The vertical contour in equation (theta-weight), parametrized by t = iu. -/
def thetaWeight (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2 * Real.pi : ℝ)⁻¹ * ∫ u : ℝ,
    mellinTransform V (-(u : ℂ) * Complex.I) *
      (Complex.Gamma (7 / 6 + (u : ℂ) * Complex.I) *
        Complex.Gamma (5 / 6 + (u : ℂ) * Complex.I) /
        (Complex.Gamma (7 / 6 - (u : ℂ) * Complex.I) *
          Complex.Gamma (5 / 6 - (u : ℂ) * Complex.I))) *
      (((2 * Real.pi) ^ (4 : ℕ) * x / 27 : ℝ) : ℂ) ^ (-(u : ℂ) * Complex.I)

def eulerDerivative : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | j + 1, f => fun x => (x : ℂ) * deriv (eulerDerivative j f) x

end QRHShort
