import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
Concrete arithmetic objects for paper2.tex (11/12 manuscript), §§1, 3 and Appendix A.
These are definitions, not hypotheses asserting the manuscript's estimates. In particular,
the fallback in `primaryGenerator` is totalization; its correctness on ideals prime to 3
is a separate proof obligation. No theorem of the 7/8 manuscript is imported here.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def omega : O := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def rawEmbedding : K →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- Select the complex embedding for which the distinguished cube root has positive
imaginary part. The number field and its ideals are the actual Mathlib objects. -/
def embedding (z : O) : ℂ :=
  if 0 < (rawEmbedding (omega : K)).im then rawEmbedding (z : K)
  else star (rawEmbedding (z : K))

def normIdeal (a : Ideal O) : ℝ := a.absNorm

def principal (z : O) : Ideal O := Ideal.span {z}

def normElement (z : O) : ℝ := normIdeal (principal z)

def IsPrimary (z : O) : Prop := z - 1 ∈ Ideal.span {(3 : O)}

def primaryGenerator (a : Ideal O) : O :=
  if h : ∃ z : O, principal z = a ∧ IsPrimary z then Classical.choose h else 0

def Outside (S : Finset (Ideal O)) (a : Ideal O) : Prop :=
  a ≠ ⊥ ∧ ∀ P ∈ S, ¬ P ∣ a

def SquarefreeOutside (S : Finset (Ideal O)) (a : Ideal O) : Prop :=
  Outside S a ∧ Squarefree a

def mobius (a : Ideal O) : ℤ := UniqueFactorizationMonoid.moebius a

/-- A fixed primitive sixth root in the ring of integers. -/
def rootSix : O := -omega ^ 2

/-- The sixth-power residue symbol at an unramified prime, defined by the usual
congruence. The hypotheses that the prime avoids 2 and 3 occur in the theorems,
not in this total definition. -/
def sexticAtPrime (P : Ideal O) (a : O) : ℂ :=
  ∑ j ∈ Finset.range 6,
    if Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) =
        Ideal.Quotient.mk P (rootSix ^ j)
    then embedding (rootSix ^ j) else 0

/-- Multiplicative extension in the denominator, including repeated prime factors. -/
def sexticSymbol (n : Ideal O) (a : O) : ℂ :=
  if n = ⊥ then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors n).map
      (fun P => sexticAtPrime P a)).prod

def alpha (n : Ideal O) : ℂ :=
  embedding (primaryGenerator n) / (‖embedding (primaryGenerator n)‖ : ℂ)

def additiveCharacter (z : ℂ) : ℂ :=
  Complex.exp (((4 * Real.pi * z.im / Real.sqrt 3 : ℝ) : ℂ) * Complex.I)

def residueLift (n : Ideal O) (x : O ⧸ n) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective x)

/-- Normalized Gauss sums in the convention of paper2.tex:800--805. -/
def gauss (j : ℤ) (n : Ideal O) : ℂ :=
  if hn : n ≠ ⊥ then
    letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn
    letI : Fintype (O ⧸ n) := Fintype.ofFinite _
    (Real.sqrt (normIdeal n) : ℂ)⁻¹ *
      ∑ x : O ⧸ n, sexticSymbol n (residueLift n x) ^ j *
        additiveCharacter (embedding (residueLift n x) / embedding (primaryGenerator n))
  else 0

/-- Finite-order Hecke characters of an imaginary quadratic field of class number one
are ray characters trivial on units. Nonprimitive moduli are allowed. -/
structure HeckeCharacter where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_trivial : ∀ u : Oˣ, residue (Ideal.Quotient.mk modulus (u : O)) = 1

def HeckeCharacter.onElement (χ : HeckeCharacter) (a : O) : ℂ :=
  χ.residue (Ideal.Quotient.mk χ.modulus a)

/-- Away from the ramified prime this agrees with evaluation on ideals. The analytic
Hecke series below will use an arbitrary ideal generator, so it also includes ideals
above 3 when they are prime to the modulus. -/
def rayValue (χ : HeckeCharacter) (a : Ideal O) : ℂ :=
  χ.onElement (primaryGenerator a)

def idealGenerator (a : Ideal O) : O :=
  Submodule.IsPrincipal.generator a

def HeckeCharacter.onIdeal (χ : HeckeCharacter) (a : Ideal O) : ℂ :=
  if a = ⊥ then 0 else χ.onElement (idealGenerator a)

structure ArithmeticContext where
  nu : HeckeCharacter
  S : Finset (Ideal O)
  prime_S : ∀ P ∈ S, Prime P
  above_two : ∀ P : Ideal O, Prime P → P ∣ principal 2 → P ∈ S
  above_three : ∀ P : Ideal O, Prime P → P ∣ principal 3 → P ∈ S
  conductor_S : ∀ P : Ideal O, Prime P → P ∣ nu.modulus → P ∈ S
  rayModulus : Ideal O
  rayModulus_ne_bot : rayModulus ≠ ⊥
  ray_supported : ∀ P : Ideal O, Prime P → P ∣ rayModulus → P ∈ S
  nu_factors : rayModulus ≤ nu.modulus

def RayCharacter (c : ArithmeticContext) :=
  {χ : HeckeCharacter // χ.modulus = c.rayModulus}

def coefficient (ξ : HeckeCharacter) (n : Ideal O) : ℂ :=
  star (alpha n) * gauss 2 n * rayValue ξ n

end QRHShort
