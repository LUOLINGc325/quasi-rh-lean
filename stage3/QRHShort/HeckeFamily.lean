import QRHShort.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The hypotheses of Goldmakher–Louvel, Definition 1, specialized to the
fixed field K and order two. The assertion that our residue-symbol family
satisfies these hypotheses belongs to the internal quadratic-sieve proof. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def HeckeCharacter.IsPrimitive (χ : HeckeCharacter) : Prop :=
  ∀ (d : Ideal O), d ≠ ⊥ → χ.modulus ≤ d →
    (∃ ψ : MulChar (O ⧸ d) ℂ, ∀ a : O,
      IsUnit (Ideal.Quotient.mk χ.modulus a) →
      χ.onElement a = ψ (Ideal.Quotient.mk d a)) → d = χ.modulus

def FamilyIdeal (m a : Ideal O) : Prop :=
  a ≠ ⊥ ∧ IsRelPrime a m

structure QuadraticHeckeFamily where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  G : Type
  [group : CommGroup G]
  [finite : Fintype G]
  classOf : Ideal O → G
  class_one : classOf 1 = 1
  class_mul : ∀ a b, FamilyIdeal modulus a → FamilyIdeal modulus b →
    classOf (a * b) = classOf a * classOf b
  character : Ideal O → HeckeCharacter
  primitive : ∀ a, FamilyIdeal modulus a → Squarefree a → (character a).IsPrimitive
  quadratic : ∀ a, FamilyIdeal modulus a → Squarefree a →
    ∀ x : O, IsUnit (Ideal.Quotient.mk (character a).modulus x) →
      (character a).onElement x ^ (2 : ℕ) = 1
  reciprocityFactor : G → G → ℂ
  factor_order_two : ∀ x y, reciprocityFactor x y ^ (2 : ℕ) = 1
  reciprocity : ∀ a b, FamilyIdeal modulus a → FamilyIdeal modulus b →
    Squarefree a → Squarefree b → IsRelPrime a b →
      (character a).onIdeal b = (character b).onIdeal a *
        reciprocityFactor (classOf a) (classOf b)
  product_conductor : ∀ a b, FamilyIdeal modulus a → FamilyIdeal modulus b →
    Squarefree a → Squarefree b → IsRelPrime a b → classOf a = classOf b →
      ∃ ψ : HeckeCharacter, ψ.modulus = a * b ∧ ψ.IsPrimitive ∧
        ∀ x : O, IsUnit (Ideal.Quotient.mk
          (a * b * (character a).modulus * (character b).modulus) x) →
          ψ.onElement x = (character a).onElement x * (character b).onElement x

def QuadraticFamilySieve (F : QuadraticHeckeFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M N : ℝ) (coeffs : Ideal O → ℂ), 1 ≤ M → 1 ≤ N →
      (∑' a : Ideal O, if FamilyIdeal F.modulus a ∧ Squarefree a ∧ normIdeal a ≤ M then
        ‖∑' b : Ideal O, if FamilyIdeal F.modulus b ∧ Squarefree b ∧ normIdeal b ≤ N then
          coeffs b * (F.character b).onIdeal a else 0‖ ^ 2 else 0) ≤
        C * (M * N) ^ ε * (M + N) *
          ∑' b : Ideal O, if FamilyIdeal F.modulus b ∧ Squarefree b ∧ normIdeal b ≤ N
            then ‖coeffs b‖ ^ 2 else 0

end QRHShort
