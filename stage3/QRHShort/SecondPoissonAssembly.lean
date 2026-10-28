import QRHShort.SecondPoissonZero
import QRHShort.SecondPoissonSupport

/-!
Internal obligations for `Manuscript.arithmetic_poisson_step`, following the
three steps in paper2.tex:2367--2494. These are definitions of propositions;
none is asserted as a theorem or added as an axiom. The conditional assembly
has exactly the frozen `SecondPoissonStatement` as its conclusion.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SecondPoissonProof

def RayExpansion (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ) : Prop :=
  ∀ a : Ideal O, Outside c.S a →
    rayValue ξ₁.val a * reciprocityG c hc ((idealClass c a)⁻¹) =
      ∑' ξ : RayCharacter c, coeffs ξ * rayValue ξ.val a

/-- Finite harmonic analysis on the fixed ray class group. -/
def RayExpansionStatement : Prop :=
  ∀ (c : ArithmeticContext) (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c),
    ∃ coeffs : RayCharacter c → ℂ, (Function.support coeffs).Finite ∧
      RayExpansion c hc ξ₁ coeffs

/-- The column before removing the mutual coprimality of the two columns.
Unlike `secondPoissonCoefficient`, this has no inserted common divisor `w`.
The individual coprimality with `g*C*t` is imposed in `coprimeDual`. -/
def coprimeCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d e : Ideal O) (h : O) (n : Ideal O) : ℂ :=
  coefficient ξ.val n * sexticSymbol n (primaryGenerator (d * e) * h) *
    sexticSymbol n (primaryGenerator (C * e)) ^ (4 : ℕ)

/-- The displayed intermediate nonzero-frequency sum in the manuscript,
before inserting `∑_{w | z₁, w | z₂} μ(w)`.
All sums are the actual totalized sums, so their interchange and finite
support remain obligations of the two identities below. -/
def coprimeDual (c : ArithmeticContext) (Φ : RowWeight) (U : ℝ → ℂ)
    (coeffs : RayCharacter c → ℂ) (C d t : Ideal O) (Y ell : ℝ) : ℂ :=
  ∑' g : Ideal O, if SquarefreeOutside c.S g ∧ IsRelPrime g (C * t) then
    ∑' e : Ideal O, if e ∣ g then
      ∑' h : O, if h ≠ 0 then
        ∑' ξ : RayCharacter c,
          (Y : ℂ) * (mobius e : ℂ) * coeffs ξ * normIdeal g /
            ((normIdeal e : ℂ) * ell) *
            ∑' n₁ : Ideal O, if SquarefreeOutside c.S n₁ ∧
                IsRelPrime n₁ (g * C * t) then
              ∑' n₂ : Ideal O, if SquarefreeOutside c.S n₂ ∧
                  IsRelPrime n₂ (g * C * t) ∧ IsRelPrime n₁ n₂ then
                coprimeCoefficient c ξ C d e h n₁ *
                  star (coprimeCoefficient c ξ C d e h n₂) *
                  secondPoissonKernel Φ U Y ell g e h
                    (normIdeal n₁ / (ell / normIdeal g))
                    (normIdeal n₂ / (ell / normIdeal g))
              else 0
            else 0
      else 0
    else 0
  else 0

/-- Expand the square, extract `g = gcd(n₁,n₂)`, apply the frozen primitive
Poisson identity, and evaluate its Gauss factor using `ArithmeticRelations`.
The diagonal zero frequency is precisely the frozen `secondPoissonZero`. -/
def CoprimePoissonStatement : Prop :=
  ArithmeticStatement → PoissonStatement →
  ∀ (c : ArithmeticContext) (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c)
      (coeffs : RayCharacter c → ℂ),
    (Function.support coeffs).Finite → RayExpansion c hc ξ₁ coeffs →
    ∀ (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
      (C d t : Ideal O) (Y ell : ℝ),
      SquarefreeOutside c.S C → SquarefreeOutside c.S t → IsRelPrime C t → d ∣ C →
      0 < Y → 0 < ell → SmoothSupported I U →
      ((∑' y : O, Φ.value (normElement y / Y) *
        ‖firstColumn c ξ₁ C d t U ell y‖ ^ 2 : ℝ) : ℂ) =
          secondPoissonZero c Φ U C t Y ell + coprimeDual c Φ U coeffs C d t Y ell

/-- Insert the ideal Möbius coprimality identity, set `zᵢ = w*nᵢ`,
use arithmetic coefficient multiplicativity, and enforce Fourier support.
The conclusion includes all five transformed indices and their exact bounds. -/
def MobiusRecombinationStatement : Prop :=
  ∀ (c : ArithmeticContext), ArithmeticRelations c →
    ∀ (coeffs : RayCharacter c → ℂ), (Function.support coeffs).Finite →
    ∀ (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
      (C d t : Ideal O) (Y ell : ℝ),
      SquarefreeOutside c.S C → SquarefreeOutside c.S t → IsRelPrime C t → d ∣ C →
      0 < Y → 0 < ell → SmoothSupported I U →
      coprimeDual c Φ U coeffs C d t Y ell =
        secondPoissonDual c I Φ U coeffs C d t Y ell

theorem arithmetic_poisson_step_of_components
    (ha : ArithmeticStatement) (hp : PoissonStatement)
    (hexp : RayExpansionStatement) (hpoisson : CoprimePoissonStatement)
    (hmobius : MobiusRecombinationStatement) : SecondPoissonStatement := by
  refine ⟨?_, secondPoisson_zero_bound⟩
  intro c hc ξ₁
  obtain ⟨coeffs, hfinite, hexpansion⟩ := hexp c hc ξ₁
  refine ⟨coeffs, hfinite, hexpansion, ?_⟩
  intro I Φ U C d t Y ell hC ht hCt hd hY hell hU
  rw [hpoisson ha hp c hc ξ₁ coeffs hfinite hexpansion I Φ U C d t Y ell
      hC ht hCt hd hY hell hU,
    hmobius c hc coeffs hfinite I Φ U C d t Y ell hC ht hCt hd hY hell hU]

end QRHShort.SecondPoissonProof
