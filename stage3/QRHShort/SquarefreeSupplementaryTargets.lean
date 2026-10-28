import QRHShort.SquarefreeSResidualFinite

/-! Unproved supplementary reciprocity targets. These are proposition
definitions, not axioms or proofs. The unit slice is already established by
`exists_all_unit_residual_characters`; S-prime generators remain to be treated. -/

noncomputable section
open Classical

namespace QRHShort.SquarefreeReflection

/-- The full target from the relay3/relay4 draft, with all quantifiers retained. -/
def SResidualRayTarget (c : ArithmeticContext) : Prop :=
  ∃ M : Ideal O, M ≠ ⊥ ∧ M ≤ c.rayModulus ∧
    (∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) ∧
    ∀ r : SResidueIndex c, ∃ χ : HeckeCharacter,
      χ.modulus = M ∧ ∀ n : Ideal O, Outside c.S n →
        rayValue χ n = SResidual c r n

def SupplementaryReciprocityStatement : Prop :=
  ∀ c : ArithmeticContext, ArithmeticRelations c → SResidualRayTarget c

/-- The remaining generator slice, on every outside ideal at a common
nonzero S-supported refinement of the original modulus. -/
def SPrimeGeneratorRayTarget (c : ArithmeticContext) : Prop :=
  ∃ M : Ideal O, M ≠ ⊥ ∧ M ≤ c.rayModulus ∧
    (∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) ∧
    ∀ p : c.S, ∃ χ : HeckeCharacter,
      χ.modulus = M ∧ ∀ n : Ideal O, Outside c.S n →
        rayValue χ n = sexticSymbol n (idealGenerator p.val)

def SPrimeGeneratorReciprocityStatement : Prop :=
  ∀ c : ArithmeticContext, ArithmeticRelations c → SPrimeGeneratorRayTarget c

end QRHShort.SquarefreeReflection
