import QRHShort.PoissonStatements

/-! `lem:arithmetic-poisson`, paper2.tex:2351–2422. All five transformed
indices, the zero frequency and the two-column kernel remain explicit. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def quotientIdeal (g e : Ideal O) : Ideal O :=
  if h : e ∣ g then Classical.choose h else ⊤

def secondPoissonKernel (Φ : RowWeight) (U : ℝ → ℂ) (Y ell : ℝ)
    (g e : Ideal O) (h : O) (x₁ x₂ : ℝ) : ℂ :=
  ((Real.sqrt x₁ : ℂ)⁻¹ * U x₁) * star ((Real.sqrt x₂ : ℂ)⁻¹ * U x₂) *
    radialFourier (fun x => (Φ.value x : ℂ))
      (Y * normElement h * normIdeal g ^ (2 : ℕ) /
        (normIdeal e * ell ^ (2 : ℕ) * x₁ * x₂))

def secondPoissonCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t g e w : Ideal O) (h : O) (n : Ideal O) : ℂ :=
  if IsRelPrime n (t * quotientIdeal g e) then
    coefficient ξ.val n * sexticSymbol n (primaryGenerator (d * e) * h) *
      sexticSymbol n (primaryGenerator (C * e * w)) ^ (4 : ℕ)
  else 0

def secondPoissonZero (c : ArithmeticContext) (Φ : RowWeight) (U : ℝ → ℂ)
    (C t : Ideal O) (Y ell : ℝ) : ℂ :=
  Y * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
    ∑' g : Ideal O, if SquarefreeOutside c.S g ∧ IsRelPrime g (C * t) then
      (‖U (normIdeal g / ell)‖ ^ 2 : ℝ) *
        ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹) else 0

def secondPoissonDual (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ)
    (C d t : Ideal O) (Y ell : ℝ) : ℂ :=
  ∑' g : Ideal O, if SquarefreeOutside c.S g ∧ IsRelPrime g (C * t) then
    ∑' e : Ideal O, if e ∣ g then
      ∑' w : Ideal O, if SquarefreeOutside c.S w ∧ normIdeal (g * w) ≤ I.hi * ell then
        ∑' h : O, if h ≠ 0 ∧ IsRelPrime w (g * C * t * principal h) ∧
            normElement h ≤ Φ.fourierCap * I.hi ^ (2 : ℕ) * ell ^ (2 : ℕ) * normIdeal e /
              (Y * normIdeal g ^ (2 : ℕ)) then
          ∑' ξ : RayCharacter c,
            (Y : ℂ) * (mobius e : ℂ) * (mobius w : ℂ) * coeffs ξ *
              normIdeal g / ((normIdeal e : ℂ) * ell) *
              ∑' n₁ : Ideal O, if SquarefreeOutside c.S n₁ then
                ∑' n₂ : Ideal O, if SquarefreeOutside c.S n₂ then
                  secondPoissonCoefficient c ξ C d t g e w h n₁ *
                    star (secondPoissonCoefficient c ξ C d t g e w h n₂) *
                    secondPoissonKernel Φ U Y ell g e h
                      (normIdeal n₁ / (ell / normIdeal (g * w)))
                      (normIdeal n₂ / (ell / normIdeal (g * w)))
                else 0
              else 0
        else 0
      else 0
    else 0
  else 0

def SecondPoissonStatement : Prop :=
  (∀ (c : ArithmeticContext) (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c),
    ∃ coeffs : RayCharacter c → ℂ, (Function.support coeffs).Finite ∧
      (∀ a : Ideal O, Outside c.S a →
        rayValue ξ₁.val a * reciprocityG c hc ((idealClass c a)⁻¹) =
          ∑' ξ : RayCharacter c, coeffs ξ * rayValue ξ.val a) ∧
      ∀ (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
        (C d t : Ideal O) (Y ell : ℝ),
        SquarefreeOutside c.S C → SquarefreeOutside c.S t → IsRelPrime C t → d ∣ C →
        0 < Y → 0 < ell → SmoothSupported I U →
        ((∑' y : O, Φ.value (normElement y / Y) *
          ‖firstColumn c ξ₁ C d t U ell y‖ ^ 2 : ℝ) : ℂ) =
            secondPoissonZero c Φ U C t Y ell +
              secondPoissonDual c I Φ U coeffs C d t Y ell) ∧
  (∀ (I : SupportInterval) (Φ : RowWeight), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c : ArithmeticContext) (U : ℝ → ℂ) (C t : Ideal O) (Y ell : ℝ),
      0 < Y → 0 < ell → SmoothSupported I U →
      ‖secondPoissonZero c Φ U C t Y ell‖ ≤ K * Y * ell * weightNorm 0 U ^ 2)

end QRHShort
