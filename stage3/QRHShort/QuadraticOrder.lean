import QRHShort.QuadraticConcrete

/-!
The order-dividing-two node of the concrete quadratic family.

`QuadraticHeckeFamily.factor_order_two` means `f x y ^ 2 = 1`, not
`orderOf (f x y) = 2`.  The former also covers the unit ideal and an empty
prime-factor family.  In particular, no nontriviality hypothesis belongs here.

The new arithmetic step below proves that evaluation at an admissible coprime
ideal is a square root of one.  It uses the product modulus directly, and never
uses `sexticAtPrime_cube_eq_quadraticResidueChar`, an OAI reciprocity theorem, or
`quadraticCharacter_modulus` (whose formula is expressed via the sextic symbol).

Selecting one admissible ideal pair for each realized pair of ray classes then
gives a concrete factor with the exact `factor_order_two` field.  This does NOT
prove reciprocity: the final equivalence states the remaining obligation that
the defect agrees with the chosen value on every pair in the same classes.
No such obligation is assumed or asserted as a theorem here.

Source candidate only: this file and its copied upstream dependencies have not
been run through Lean in this task.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- Passing from coprime ideals to a unit in the quotient also works for `I = 1`.
The quotient is then the zero ring, whose unique element is a unit. -/
theorem quadratic_idealGenerator_isUnit {I J : Ideal O} (h : IsRelPrime I J) :
    IsUnit (Ideal.Quotient.mk I (idealGenerator J)) := by
  have hcop : IsCoprime I J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact Ideal.isUnit_iff.mp
      (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
  have hI : principal (idealGenerator I) = I := Ideal.span_singleton_generator I
  have hJ : principal (idealGenerator J) = J := Ideal.span_singleton_generator J
  have hgen : IsCoprime (idealGenerator J) (idealGenerator I) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    change IsCoprime (principal (idealGenerator J)) (principal (idealGenerator I))
    rw [hI, hJ]
    exact hcop.symm
  have hzero : Ideal.Quotient.mk I (idealGenerator I) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.IsPrincipal.generator_mem I)
  exact isCoprime_zero_right.mp (by
    simpa only [hzero] using hgen.map (Ideal.Quotient.mk I))

/-- The correction prime is already excluded by the fixed family modulus six. -/
theorem quadraticCharacter_modulus_relPrime (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hsqa : Squarefree a) (hab : IsRelPrime a b) :
    IsRelPrime (quadraticCharacter a).modulus b := by
  rw [quadraticCharacter, dif_pos ⟨ha, hsqa⟩, correctedQuadraticHecke_modulus,
    quadraticFactor_prod ha.1 hsqa]
  split_ifs
  · exact hab
  · have hl : IsRelPrime quadraticLambdaIdeal b :=
      (hb.2.of_dvd_right (quadraticLambda_dvd_three.trans quadratic_three_dvd_six)).symm
    exact hl.mul_left hab

/-- The exact quadratic field, transported from elements to coprime ideals. -/
theorem quadraticCharacter_onIdeal_sq (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hsqa : Squarefree a) (hab : IsRelPrime a b) :
    (quadraticCharacter a).onIdeal b ^ (2 : ℕ) = 1 := by
  rw [HeckeCharacter.onIdeal, if_neg hb.1]
  exact quadraticCharacter_quadratic a ha hsqa (idealGenerator b)
    (quadratic_idealGenerator_isUnit
      (quadraticCharacter_modulus_relPrime a b ha hb hsqa hab))

/-- On admissible coprime pairs this product is also the quotient of the two
values, since each value is its own inverse. -/
def quadraticReciprocityDefect (a b : Ideal O) : ℂ :=
  (quadraticCharacter a).onIdeal b * (quadraticCharacter b).onIdeal a

theorem quadraticReciprocityDefect_sq (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hsqa : Squarefree a) (hsqb : Squarefree b) (hab : IsRelPrime a b) :
    quadraticReciprocityDefect a b ^ (2 : ℕ) = 1 := by
  rw [quadraticReciprocityDefect, mul_pow,
    quadraticCharacter_onIdeal_sq a b ha hb hsqa hab,
    quadraticCharacter_onIdeal_sq b a hb ha hsqb hab.symm, one_mul]

theorem quadraticCharacter_onIdeal_eq_mul_defect (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hsqb : Squarefree b) (hab : IsRelPrime a b) :
    (quadraticCharacter a).onIdeal b =
      (quadraticCharacter b).onIdeal a * quadraticReciprocityDefect a b := by
  have hsq := quadraticCharacter_onIdeal_sq b a hb ha hsqb hab.symm
  calc
    (quadraticCharacter a).onIdeal b =
        (quadraticCharacter a).onIdeal b *
          (quadraticCharacter b).onIdeal a ^ (2 : ℕ) := by rw [hsq, mul_one]
    _ = (quadraticCharacter b).onIdeal a * quadraticReciprocityDefect a b := by
      unfold quadraticReciprocityDefect
      ring

/-- Exactly the ideal-pair hypotheses of the frozen `reciprocity` field. -/
structure QuadraticReciprocityPair where
  left : Ideal O
  right : Ideal O
  left_mem : FamilyIdeal (principal 6) left
  right_mem : FamilyIdeal (principal 6) right
  left_squarefree : Squarefree left
  right_squarefree : Squarefree right
  coprime : IsRelPrime left right

/-- Define the factor using an actual admissible pair when the classes are
realized, and use one otherwise.  No surjectivity of `classOf` is required. -/
def quadraticReciprocityFactor {G : Type*} (classOf : Ideal O → G) (x y : G) : ℂ :=
  if h : ∃ p : QuadraticReciprocityPair, classOf p.left = x ∧ classOf p.right = y then
    quadraticReciprocityDefect (Classical.choose h).left (Classical.choose h).right
  else 1

/-- The exact frozen field, for every pair of classes, including unrealized pairs. -/
theorem quadraticReciprocityFactor_order_two {G : Type*} (classOf : Ideal O → G) :
    ∀ x y, quadraticReciprocityFactor classOf x y ^ (2 : ℕ) = 1 := by
  intro x y
  unfold quadraticReciprocityFactor
  split_ifs with h
  · let p : QuadraticReciprocityPair := Classical.choose h
    exact quadraticReciprocityDefect_sq p.left p.right p.left_mem p.right_mem
      p.left_squarefree p.right_squarefree p.coprime
  · exact one_pow 2

/-- This equivalence exposes, rather than assumes, the missing reciprocity
interface.  Squaring the factor alone does not establish this equality. -/
theorem quadraticReciprocity_iff_defect {G : Type*} (classOf : Ideal O → G)
    (factor : G → G → ℂ) :
    (∀ p : QuadraticReciprocityPair,
      (quadraticCharacter p.left).onIdeal p.right =
        (quadraticCharacter p.right).onIdeal p.left *
          factor (classOf p.left) (classOf p.right)) ↔
    (∀ p : QuadraticReciprocityPair,
      quadraticReciprocityDefect p.left p.right =
        factor (classOf p.left) (classOf p.right)) := by
  constructor
  · intro h p
    have hsq := quadraticCharacter_onIdeal_sq p.right p.left p.right_mem p.left_mem
      p.right_squarefree p.coprime.symm
    calc
      quadraticReciprocityDefect p.left p.right =
          ((quadraticCharacter p.right).onIdeal p.left *
            factor (classOf p.left) (classOf p.right)) *
              (quadraticCharacter p.right).onIdeal p.left := by
        unfold quadraticReciprocityDefect
        rw [h p]
      _ = (quadraticCharacter p.right).onIdeal p.left ^ (2 : ℕ) *
          factor (classOf p.left) (classOf p.right) := by ring
      _ = factor (classOf p.left) (classOf p.right) := by rw [hsq, one_mul]
  · intro h p
    rw [← h p]
    exact quadraticCharacter_onIdeal_eq_mul_defect p.left p.right p.left_mem
      p.right_mem p.right_squarefree p.coprime

/-- Descent to classes is precisely the still-missing arithmetic assertion.
This is an equivalence, not an additional hypothesis on the frozen family. -/
theorem quadraticReciprocityFactor_spec_iff {G : Type*} (classOf : Ideal O → G) :
    (∀ p : QuadraticReciprocityPair,
      quadraticReciprocityDefect p.left p.right =
        quadraticReciprocityFactor classOf (classOf p.left) (classOf p.right)) ↔
    (∀ p q : QuadraticReciprocityPair,
      classOf p.left = classOf q.left → classOf p.right = classOf q.right →
      quadraticReciprocityDefect p.left p.right =
        quadraticReciprocityDefect q.left q.right) := by
  constructor
  · intro h p q hl hr
    rw [h p, h q, hl, hr]
  · intro h p
    have hex : ∃ q : QuadraticReciprocityPair,
        classOf q.left = classOf p.left ∧ classOf q.right = classOf p.right :=
      ⟨p, rfl, rfl⟩
    rw [quadraticReciprocityFactor, dif_pos hex]
    exact h p (Classical.choose hex) (Classical.choose_spec hex).1.symm
      (Classical.choose_spec hex).2.symm

/-- An empty product is allowed by the frozen interface and stays trivial after
the correction.  This is why an exact-order-two replacement would be false. -/
theorem correctedQuadraticHecke_empty_onElement {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i)) (x : O) :
    (correctedQuadraticHecke P hpair hne hlambda).onElement x = 1 := by
  rw [correctedQuadraticHecke_onElement]
  simp [quadraticElementProduct]

end QRHShort

#print axioms QRHShort.quadraticCharacter_onIdeal_sq
#print axioms QRHShort.quadraticReciprocityFactor_order_two
#print axioms QRHShort.quadraticReciprocity_iff_defect
