import QRHShort.AnalyticObjects
import QRHShort.ArithmeticStatements

/-! Statements of `lem:poisson` and `lem:remove-exclusions`.
Primitivity refers to factorization of the character on units; an induced
character need not have the same zero extension on nonunits. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

structure PrimitiveResidueCharacter where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  character : MulChar (O ⧸ modulus) ℂ
  primitive : ∀ (d : Ideal O), d ≠ ⊥ → modulus ≤ d →
    (∃ ψ : MulChar (O ⧸ d) ℂ, ∀ a : O,
      IsUnit (Ideal.Quotient.mk modulus a) →
      character (Ideal.Quotient.mk modulus a) = ψ (Ideal.Quotient.mk d a)) →
    d = modulus

def PrimitiveResidueCharacter.value (χ : PrimitiveResidueCharacter) (a : O) : ℂ :=
  χ.character (Ideal.Quotient.mk χ.modulus a)

def PrimitiveResidueCharacter.gauss (χ : PrimitiveResidueCharacter) : ℂ :=
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  (Real.sqrt (normIdeal χ.modulus) : ℂ)⁻¹ *
    ∑ x : O ⧸ χ.modulus, χ.character x *
      additiveCharacter
        (embedding (residueLift χ.modulus x) / embedding (chosenGenerator χ.modulus))

def poissonZeroTerm (χ : PrimitiveResidueCharacter) (r : Ideal O)
    (Φ : ℝ → ℂ) (H : ℝ) : ℂ :=
  H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
    ∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
      (mobius d : ℂ) * χ.value (chosenGenerator d) / (normIdeal d : ℂ) *
        star (χ.value 0) * radialFourier Φ 0 else 0

def PoissonStatement : Prop :=
  ∀ (χ : PrimitiveResidueCharacter) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ),
    r ≠ ⊥ → 0 < H → RadialSchwartz Φ →
    (∑' k : O, if IsRelPrime (principal k) r then
      χ.value k * Φ (normElement k / H) else 0) =
      H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
        ∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
          (mobius d : ℂ) * χ.value (chosenGenerator d) / (normIdeal d : ℂ) *
            ∑' h : O, star (χ.value h) *
              radialFourier Φ (H * normElement h / (normIdeal d * normIdeal χ.modulus))
          else 0

def PoissonZeroStatement : Prop :=
  (∀ χ : PrimitiveResidueCharacter, χ.character ≠ 1 → star (χ.value 0) = 0) ∧
  (∀ (χ : PrimitiveResidueCharacter) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ),
    χ.character = 1 → χ.modulus = ⊤ → r ≠ ⊥ → 0 < H → RadialSchwartz Φ →
      poissonZeroTerm χ r Φ H = H * radialFourier Φ 0 *
        ∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹))

def RemoveExclusionsStatement : Prop :=
  ∀ (c : ArithmeticContext), ArithmeticRelations c →
  ∀ (I : SupportInterval) (ξ : RayCharacter c) (W : ℝ → ℂ)
      (r : Ideal O) (H X F : ℝ),
    r ≠ ⊥ → SmoothSupported I W → 0 < H → 0 < X → 1 ≤ F →
    excludedEnergy c ξ W r H X F ≤
      (divisorCount (outsideRadical c.S r) : ℝ) *
        ∑' d : Ideal O, if d ∣ outsideRadical c.S r then
          energy c ξ W H (X / normIdeal d) (F * normIdeal d) else 0

end QRHShort
