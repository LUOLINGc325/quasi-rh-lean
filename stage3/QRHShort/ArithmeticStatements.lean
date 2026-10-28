import QRHShort.Arithmetic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Concrete statement of paper2.tex, Lemma `lem:arithmetic` (lines 823–861).
The existence of a sufficiently large ray modulus is part of the conclusion.
None of the reciprocity or Gauss identities is a field of `ArithmeticContext`. -/

noncomputable section
open Classical

namespace QRHShort

def globalUnitImage (c : ArithmeticContext) : Subgroup (O ⧸ c.rayModulus)ˣ :=
  (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom).range

abbrev RayClass (c : ArithmeticContext) :=
  (O ⧸ c.rayModulus)ˣ ⧸ globalUnitImage c

def rayClass (c : ArithmeticContext) (a : O) : RayClass c :=
  if h : IsUnit (Ideal.Quotient.mk c.rayModulus a) then
    QuotientGroup.mk h.unit else 1

def idealClass (c : ArithmeticContext) (a : Ideal O) : RayClass c :=
  rayClass c (primaryGenerator a)

def ArithmeticRelations (c : ArithmeticContext) : Prop :=
  ∃ G : RayClass c → ℂ, ∃ R : RayClass c → RayClass c → ℂ,
    (∀ a, ‖G a‖ = 1) ∧
    (∀ a b, R a b = 1 ∨ R a b = -1) ∧
    (∀ a b, R a b = R b a) ∧
    (∀ a a' b, R (a * a') b = R a b * R a' b) ∧
    (∀ a b b', R a (b * b') = R a b * R a b') ∧
    (∀ a b, G (a * b) = G a * G b * R a b) ∧
    (∀ a b : Ideal O, Outside c.S a → Outside c.S b → IsRelPrime a b →
      sexticSymbol b (primaryGenerator a) =
        R (idealClass c a) (idealClass c b) * sexticSymbol a (primaryGenerator b)) ∧
    (∀ n : Ideal O, SquarefreeOutside c.S n →
      gauss 2 n ^ (3 : ℕ) = (mobius n : ℂ) * alpha n ∧
      gauss 1 n * gauss 2 n = (mobius n : ℂ) * alpha n * G (idealClass c n) ∧
      G (idealClass c n) = star (sexticSymbol n 4) * gauss 3 n ∧
      gauss 1 n * gauss (-1) n = sexticSymbol n (-1) ∧
      star (alpha n) * gauss 2 n * gauss 1 n = (mobius n : ℂ) * G (idealClass c n) ∧
      (mobius n : ℂ) * gauss (-1) n =
        sexticSymbol n (-1) * (G (idealClass c n))⁻¹ * star (alpha n) * gauss 2 n) ∧
    (∀ (ξ : RayCharacter c) (a b : Ideal O),
      SquarefreeOutside c.S a → SquarefreeOutside c.S b → IsRelPrime a b →
      coefficient ξ.val (a * b) = coefficient ξ.val a * coefficient ξ.val b *
        sexticSymbol b (primaryGenerator a) ^ (4 : ℕ)) ∧
    (∀ a b : Ideal O, Outside c.S a → Outside c.S b →
      sexticSymbol a (-1) * star (G (idealClass c a)) * G (idealClass c b) *
        R (idealClass c a) (idealClass c b) =
          G (idealClass c b * (idealClass c a)⁻¹))

def ArithmeticStatement : Prop :=
  ∀ (ν : HeckeCharacter) (S : Finset (Ideal O)),
    (∀ P ∈ S, Prime P) →
    (∀ P : Ideal O, Prime P → P ∣ principal 2 → P ∈ S) →
    (∀ P : Ideal O, Prime P → P ∣ principal 3 → P ∈ S) →
    (∀ P : Ideal O, Prime P → P ∣ ν.modulus → P ∈ S) →
    ∃ c : ArithmeticContext, c.nu = ν ∧ c.S = S ∧ ArithmeticRelations c

def reciprocityG (c : ArithmeticContext) (hc : ArithmeticRelations c) : RayClass c → ℂ :=
  Classical.choose hc

end QRHShort
