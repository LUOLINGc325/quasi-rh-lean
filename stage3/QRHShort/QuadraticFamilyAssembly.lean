import QRHShort.QuadraticRayInvariant
import QRHShort.External

/-!
Explicit remaining arithmetic inputs for the concrete quadratic family.
These are propositions, not axioms. The family and the external sieve below
are conditional on class invariance until its arithmetic proof is supplied.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The unresolved descent assertion for the actual reciprocity defect. -/
def QuadraticRayClassInvariantStatement : Prop :=
  ∀ p q : QuadraticReciprocityPair,
    quadraticRayClass p.left = quadraticRayClass q.left →
    quadraticRayClass p.right = quadraticRayClass q.right →
    quadraticReciprocityDefect p.left p.right =
      quadraticReciprocityDefect q.left q.right

/-- A finer arithmetic child: an actual bilinear correction for prime pairs.
Both homomorphism structures are required to pass to composite ideals. -/
def QuadraticPrimeRayReciprocityStatement : Prop :=
  ∃ B : QuadraticRayGroup →* (QuadraticRayGroup →* ℂ),
    ∀ P Q : Ideal O, Prime P → Prime Q →
      FamilyIdeal (principal 6) P → FamilyIdeal (principal 6) Q →
      IsRelPrime P Q →
      quadraticReciprocityDefect P Q = B (quadraticRayClass P) (quadraticRayClass Q)

theorem quadraticFamilyIdeal_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal O)
    (h : ∀ i ∈ s, FamilyIdeal (principal 6) (f i)) :
    FamilyIdeal (principal 6) (∏ i ∈ s, f i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i hi => (h i hi).1),
    IsRelPrime.prod_left (fun i hi => (h i hi).2)⟩

theorem quadraticRayClass_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal O)
    (h : ∀ i ∈ s, FamilyIdeal (principal 6) (f i)) :
    quadraticRayClass (∏ i ∈ s, f i) = ∏ i ∈ s, quadraticRayClass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using quadraticRayClass_one
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, FamilyIdeal (principal 6) (f j) :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      quadraticRayClass_mul _ _ (h i (Finset.mem_insert_self i s))
        (quadraticFamilyIdeal_prod s f hs), ih hs]

theorem quadraticRayClassInvariant_of_primeRayReciprocity
    (h : QuadraticPrimeRayReciprocityStatement) : QuadraticRayClassInvariantStatement := by
  obtain ⟨B, hB⟩ := h
  have hdef (p : QuadraticReciprocityPair) :
      quadraticReciprocityDefect p.left p.right =
        B (quadraticRayClass p.left) (quadraticRayClass p.right) := by
    rw [quadraticReciprocityDefect_eq_prod_primePairs p.left p.right
      p.left_mem p.right_mem p.left_squarefree p.right_squarefree]
    calc
      (∏ i : QuadraticFactor p.left, ∏ j : QuadraticFactor p.right,
          quadraticReciprocityDefect (quadraticFactorIdeal p.left i)
            (quadraticFactorIdeal p.right j)) =
          ∏ i : QuadraticFactor p.left, ∏ j : QuadraticFactor p.right,
            B (quadraticRayClass (quadraticFactorIdeal p.left i))
              (quadraticRayClass (quadraticFactorIdeal p.right j)) := by
        apply Finset.prod_congr rfl
        intro i _
        apply Finset.prod_congr rfl
        intro j _
        exact hB _ _ (quadraticFactor_prime _ i) (quadraticFactor_prime _ j)
          (quadraticFactor_family _ p.left_mem i)
          (quadraticFactor_family _ p.right_mem j) (p.primePair i j).coprime
      _ = B (∏ i : QuadraticFactor p.left,
            quadraticRayClass (quadraticFactorIdeal p.left i))
          (∏ j : QuadraticFactor p.right,
            quadraticRayClass (quadraticFactorIdeal p.right j)) := by
        simp only [map_prod, MonoidHom.finsetProd_apply]
        exact Finset.prod_comm
      _ = B (quadraticRayClass p.left) (quadraticRayClass p.right) := by
        rw [← quadraticRayClass_prod Finset.univ (quadraticFactorIdeal p.left)
          (fun i _ => quadraticFactor_family _ p.left_mem i),
          ← quadraticRayClass_prod Finset.univ (quadraticFactorIdeal p.right)
          (fun j _ => quadraticFactor_family _ p.right_mem j),
          quadraticFactor_prod p.left_mem.1 p.left_squarefree,
          quadraticFactor_prod p.right_mem.1 p.right_squarefree]
  intro p q hl hr
  rw [hdef p, hdef q, hl, hr]

/-- All fields have exactly the strength of the unchanged external input.
The single remaining arithmetic hypothesis is displayed as a parameter. -/
def concreteQuadraticFamily (h : QuadraticRayClassInvariantStatement) :
    QuadraticHeckeFamily where
  modulus := principal 6
  modulus_ne_bot := Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  G := QuadraticRayGroup
  classOf := quadraticRayClass
  class_one := quadraticRayClass_one
  class_mul := quadraticRayClass_mul
  character := quadraticCharacter
  primitive := quadraticCharacter_primitive
  quadratic := quadraticCharacter_quadratic
  reciprocityFactor := quadraticRayReciprocityFactor
  factor_order_two := quadraticRayReciprocityFactor_order_two
  reciprocity := by
    intro a b ha hb hsqa hsqb hab
    exact (quadraticRayReciprocity_iff_classInvariant.mpr h)
      ⟨a, b, ha, hb, hsqa, hsqb, hab⟩
  product_conductor := quadraticRayClass_product_conductor


end QRHShort

#print axioms QRHShort.quadraticRayClassInvariant_of_primeRayReciprocity
#print axioms QRHShort.concreteQuadraticFamily
