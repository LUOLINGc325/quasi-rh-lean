import QRHShort.QuadraticOrder
import QRHShort.QuadraticRayClass

/-! Specialization of the order-dividing-two node to the existing candidate ray
class map.  The core `QuadraticOrder` file does not need this class map or its
sextic-symbol bridge.  Reciprocity is reduced to the explicit class-invariance
interface below. -/

noncomputable section

namespace QRHShort

abbrev quadraticRayReciprocityFactor : QuadraticRayGroup → QuadraticRayGroup → ℂ :=
  quadraticReciprocityFactor quadraticRayClass

theorem quadraticRayReciprocityFactor_order_two :
    ∀ x y, quadraticRayReciprocityFactor x y ^ (2 : ℕ) = 1 :=
  quadraticReciprocityFactor_order_two quadraticRayClass

/-- This is the exact remaining interface for the chosen factor; in particular,
the order theorem does not imply the required constancy on ray classes. -/
theorem quadraticRayReciprocity_iff_classInvariant :
    (∀ p : QuadraticReciprocityPair,
      (quadraticCharacter p.left).onIdeal p.right =
        (quadraticCharacter p.right).onIdeal p.left *
          quadraticRayReciprocityFactor
            (quadraticRayClass p.left) (quadraticRayClass p.right)) ↔
    (∀ p q : QuadraticReciprocityPair,
      quadraticRayClass p.left = quadraticRayClass q.left →
      quadraticRayClass p.right = quadraticRayClass q.right →
      quadraticReciprocityDefect p.left p.right =
        quadraticReciprocityDefect q.left q.right) :=
  (quadraticReciprocity_iff_defect quadraticRayClass quadraticRayReciprocityFactor).trans
    (quadraticReciprocityFactor_spec_iff quadraticRayClass)

end QRHShort

#print axioms QRHShort.quadraticRayReciprocityFactor_order_two
#print axioms QRHShort.quadraticRayReciprocity_iff_classInvariant
