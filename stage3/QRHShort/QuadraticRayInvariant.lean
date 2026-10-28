import QRHShort.QuadraticRayOrder
import QRHShort.QuadraticRayInvariantLocal

/-!
Arithmetic reductions for the exact class-invariance obligation at the end of
`QuadraticRayOrder`.  No class-invariance or reciprocity hypothesis is introduced.

The results below extract the actual congruence encoded by the class map, prove
both multiplication laws for the actual defect, and expand an admissible pair
into its actual prime-ideal pairs.  At prime ideals the remaining factors are
identified with ordinary quadratic residue characters.

The full class-invariance obligation is NOT proved here.  In particular, equality
of the products of the prime classes does not identify the individual prime
classes.  A prime-pair formula with a multiplicative correction on ray classes
is still required; neither the order-two theorem nor the product expansion
supplies that arithmetic formula.  The main module depends on upstream source
candidates; ray-class invariance itself remains an explicit arithmetic input.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

/-- The first coordinate of the existing class map really is the primary
generator modulo four; no equality of chosen unit witnesses is assumed. -/
theorem quadraticRayClass_eq_modFour (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (h : quadraticRayClass a = quadraticRayClass b) :
    Ideal.Quotient.mk (principal (4 : O)) (primaryGenerator a) =
      Ideal.Quotient.mk (principal (4 : O)) (primaryGenerator b) := by
  have he := congrArg (fun g : QuadraticRayGroup =>
    (g.1 : O ⧸ principal (4 : O))) h
  simpa only [quadraticRayClass, dif_pos ha, dif_pos hb,
    IsUnit.unit_spec] using he

/-- Exact content of equality in the current candidate ray group. -/
theorem quadraticRayClass_eq_iff (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b) :
    quadraticRayClass a = quadraticRayClass b ↔
      (12 : O) ∣ primaryGenerator a - primaryGenerator b ∧
        sexticSymbol a (-1) ^ (3 : ℕ) = sexticSymbol b (-1) ^ (3 : ℕ) := by
  have hpa := (quadratic_primaryGenerator_spec a
    (ha.2.of_dvd_right quadratic_three_dvd_six)).2
  have hpb := (quadratic_primaryGenerator_spec b
    (hb.2.of_dvd_right quadratic_three_dvd_six)).2
  constructor
  · intro h
    exact ⟨(quadraticRay_primary_modFour_eq_iff hpa hpb).mp
      (quadraticRayClass_eq_modFour a b ha hb h),
      quadraticRayClass_eq_sign a b ha hb h⟩
  · rintro ⟨hcong, hsign⟩
    rw [quadraticRayClass, dif_pos ha, quadraticRayClass, dif_pos hb]
    apply Prod.ext
    · apply Units.ext
      simpa only [IsUnit.unit_spec] using
        (quadraticRay_primary_modFour_eq_iff hpa hpb).mpr hcong
    · apply Subtype.ext
      apply Units.ext
      simpa only [rootsOfUnity.coe_mkOfPowEq] using hsign

theorem quadraticFactor_family (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (i : QuadraticFactor a) :
    FamilyIdeal (principal 6) (quadraticFactorIdeal a i) := by
  refine ⟨(quadraticFactor_prime a i).ne_zero, ?_⟩
  intro d hd h6
  exact ha.2 (hd.trans (quadraticFactor_dvd a i)) h6

/-- Multiplication in the parameter ideal, on the actual admissible inputs.
The evaluation ideal need not be squarefree or coprime to either parameter. -/
theorem quadraticCharacter_mul_onIdeal (a b c : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hc : FamilyIdeal (principal 6) c)
    (hsqa : Squarefree a) (hsqb : Squarefree b) (hab : IsRelPrime a b) :
    (quadraticCharacter (a * b)).onIdeal c =
      (quadraticCharacter a).onIdeal c * (quadraticCharacter b).onIdeal c := by
  have habm : FamilyIdeal (principal 6) (a * b) :=
    ⟨mul_ne_zero ha.1 hb.1, ha.2.mul_left hb.2⟩
  have hsqab : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨hab, hsqa, hsqb⟩
  have hc3 := hc.2.of_dvd_right quadratic_three_dvd_six
  rw [quadraticCharacter_onIdeal (a * b) habm hsqab c hc.1 hc3,
    quadraticCharacter_onIdeal a ha hsqa c hc.1 hc3,
    quadraticCharacter_onIdeal b hb hsqb c hc.1 hc3,
    quadratic_sexticSymbol_mul, mul_pow]

theorem quadraticReciprocityDefect_comm (a b : Ideal O) :
    quadraticReciprocityDefect a b = quadraticReciprocityDefect b a :=
  mul_comm _ _

theorem quadraticReciprocityDefect_mul_left (a b c : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hc : FamilyIdeal (principal 6) c)
    (hsqa : Squarefree a) (hsqb : Squarefree b) (hab : IsRelPrime a b) :
    quadraticReciprocityDefect (a * b) c =
      quadraticReciprocityDefect a c * quadraticReciprocityDefect b c := by
  unfold quadraticReciprocityDefect
  rw [quadraticCharacter_mul_onIdeal a b c ha hb hc hsqa hsqb hab,
    HeckeCharacter.onIdeal_mul]
  ring

theorem quadraticReciprocityDefect_mul_right (a b c : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hc : FamilyIdeal (principal 6) c)
    (hsqb : Squarefree b) (hsqc : Squarefree c) (hbc : IsRelPrime b c) :
    quadraticReciprocityDefect a (b * c) =
      quadraticReciprocityDefect a b * quadraticReciprocityDefect a c := by
  rw [quadraticReciprocityDefect_comm a (b * c),
    quadraticReciprocityDefect_mul_left b c a hb hc ha hsqb hsqc hbc,
    quadraticReciprocityDefect_comm b a, quadraticReciprocityDefect_comm c a]

/-- A multiplicative symbol in the denominator; this does not interchange its
two arguments and hence makes no reciprocity assertion. -/
private def quadraticSymbolIdealHom (z : O) : Ideal O →* ℂ where
  toFun a := sexticSymbol a z ^ (3 : ℕ)
  map_one' := by
    change sexticSymbol (1 : Ideal O) z ^ (3 : ℕ) = 1
    rw [sexticSymbol, if_neg (show (1 : Ideal O) ≠ ⊥ from one_ne_zero),
      normalizedFactors_one]
    simp
  map_mul' a b := by rw [quadratic_sexticSymbol_mul, mul_pow]

/-- Expand the parameter of the concrete character using its actual prime
factors, including the empty product when the parameter ideal is one. -/
theorem quadraticCharacter_onIdeal_factor_left (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsqa : Squarefree a)
    (hb : FamilyIdeal (principal 6) b) :
    (quadraticCharacter a).onIdeal b =
      ∏ i : QuadraticFactor a, (quadraticCharacter (quadraticFactorIdeal a i)).onIdeal b := by
  have hb3 := hb.2.of_dvd_right quadratic_three_dvd_six
  calc
    (quadraticCharacter a).onIdeal b =
        quadraticSymbolIdealHom (primaryGenerator b) a :=
      quadraticCharacter_onIdeal a ha hsqa b hb.1 hb3
    _ = quadraticSymbolIdealHom (primaryGenerator b)
        (∏ i : QuadraticFactor a, quadraticFactorIdeal a i) := by
      rw [quadraticFactor_prod ha.1 hsqa]
    _ = ∏ i : QuadraticFactor a,
        quadraticSymbolIdealHom (primaryGenerator b) (quadraticFactorIdeal a i) :=
      map_prod _ _ _
    _ = ∏ i : QuadraticFactor a,
        (quadraticCharacter (quadraticFactorIdeal a i)).onIdeal b := by
      apply Finset.prod_congr rfl
      intro i _
      exact (quadraticCharacter_onIdeal (quadraticFactorIdeal a i)
        (quadraticFactor_family a ha i) (quadraticFactor_prime a i).squarefree
        b hb.1 hb3).symm

theorem quadraticCharacter_onIdeal_factor_right (a b : Ideal O)
    (hb : b ≠ ⊥) (hsqb : Squarefree b) :
    (quadraticCharacter a).onIdeal b =
      ∏ j : QuadraticFactor b, (quadraticCharacter a).onIdeal (quadraticFactorIdeal b j) := by
  calc
    (quadraticCharacter a).onIdeal b =
        (quadraticCharacter a).onIdealHom
          (∏ j : QuadraticFactor b, quadraticFactorIdeal b j) := by
      rw [quadraticFactor_prod hb hsqb]
      rfl
    _ = ∏ j : QuadraticFactor b,
        (quadraticCharacter a).onIdeal (quadraticFactorIdeal b j) := map_prod _ _ _

/-- Actual two-variable prime expansion.  No correction factor or constancy
hypothesis occurs in this theorem; shared primes are also allowed here. -/
theorem quadraticReciprocityDefect_eq_prod_primePairs (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (hsqa : Squarefree a) (hsqb : Squarefree b) :
    quadraticReciprocityDefect a b =
      ∏ i : QuadraticFactor a, ∏ j : QuadraticFactor b,
        quadraticReciprocityDefect (quadraticFactorIdeal a i) (quadraticFactorIdeal b j) := by
  have hab : (quadraticCharacter a).onIdeal b =
      ∏ i : QuadraticFactor a, ∏ j : QuadraticFactor b,
        (quadraticCharacter (quadraticFactorIdeal a i)).onIdeal
          (quadraticFactorIdeal b j) := by
    rw [quadraticCharacter_onIdeal_factor_left a b ha hsqa hb]
    apply Finset.prod_congr rfl
    intro i _
    exact quadraticCharacter_onIdeal_factor_right _ b hb.1 hsqb
  have hba : (quadraticCharacter b).onIdeal a =
      ∏ i : QuadraticFactor a, ∏ j : QuadraticFactor b,
        (quadraticCharacter (quadraticFactorIdeal b j)).onIdeal
          (quadraticFactorIdeal a i) := by
    calc
      (quadraticCharacter b).onIdeal a =
          ∏ j : QuadraticFactor b, ∏ i : QuadraticFactor a,
            (quadraticCharacter (quadraticFactorIdeal b j)).onIdeal
              (quadraticFactorIdeal a i) := by
        rw [quadraticCharacter_onIdeal_factor_left b a hb hsqb ha]
        apply Finset.prod_congr rfl
        intro j _
        exact quadraticCharacter_onIdeal_factor_right _ a ha.1 hsqa
      _ = _ := Finset.prod_comm
  rw [quadraticReciprocityDefect, hab, hba]
  simp only [quadraticReciprocityDefect, Finset.prod_mul_distrib]

/-- Every factor used in the previous expansion is again an admissible pair
when the original pair is admissible.  Thus the reduction does not forget the
nonzero, coprimality, or squarefreeness side conditions. -/
def QuadraticReciprocityPair.primePair (p : QuadraticReciprocityPair)
    (i : QuadraticFactor p.left) (j : QuadraticFactor p.right) : QuadraticReciprocityPair where
  left := quadraticFactorIdeal p.left i
  right := quadraticFactorIdeal p.right j
  left_mem := quadraticFactor_family p.left p.left_mem i
  right_mem := quadraticFactor_family p.right p.right_mem j
  left_squarefree := (quadraticFactor_prime p.left i).squarefree
  right_squarefree := (quadraticFactor_prime p.right j).squarefree
  coprime := by
    intro d hdi hdj
    exact p.coprime (hdi.trans (quadraticFactor_dvd p.left i))
      (hdj.trans (quadraticFactor_dvd p.right j))

/-- Prime evaluation is the ordinary quadratic residue symbol in the actual
residue field.  The correction at three vanishes on the primary generator. -/
theorem quadraticCharacter_prime_onIdeal (P b : Ideal O) [P.IsMaximal]
    (hP : Prime P) (hPm : FamilyIdeal (principal 6) P)
    (hb : FamilyIdeal (principal 6) b) :
    (quadraticCharacter P).onIdeal b =
      quadraticResidueChar P (Ideal.Quotient.mk P (primaryGenerator b)) := by
  rw [quadraticCharacter_onIdeal P hPm hP.squarefree b hb.1
    (hb.2.of_dvd_right quadratic_three_dvd_six), sexticSymbol, if_neg hPm.1,
    normalizedFactors_irreducible hP.irreducible, normalize_eq,
    Multiset.map_singleton, Multiset.prod_singleton]
  apply sexticAtPrime_cube_eq_quadraticResidueChar P
  · intro h
    exact hP.not_unit (hPm.2 dvd_rfl (h.trans quadratic_two_dvd_six))
  · intro h
    exact hP.not_unit (hPm.2 dvd_rfl (h.trans quadratic_three_dvd_six))

/-- The unresolved prime-pair arithmetic is precisely this explicit product,
not a consequence of its square being one. -/
theorem quadraticReciprocityDefect_prime_eq (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hP : Prime P) (hQ : Prime Q)
    (hPm : FamilyIdeal (principal 6) P) (hQm : FamilyIdeal (principal 6) Q) :
    quadraticReciprocityDefect P Q =
      quadraticResidueChar P (Ideal.Quotient.mk P (primaryGenerator Q)) *
        quadraticResidueChar Q (Ideal.Quotient.mk Q (primaryGenerator P)) := by
  rw [quadraticReciprocityDefect,
    quadraticCharacter_prime_onIdeal P Q hP hPm hQm,
    quadraticCharacter_prime_onIdeal Q P hQ hQm hPm]

/-
Precise remaining arithmetic interface (NOT an assumption or a proved result):

  ∃ B : QuadraticRayGroup →* (QuadraticRayGroup →* ℂ),
    ∀ P Q : Ideal O, Prime P → Prime Q →
      FamilyIdeal (principal 6) P → FamilyIdeal (principal 6) Q →
      IsRelPrime P Q →
      quadraticReciprocityDefect P Q = B (quadraticRayClass P) (quadraticRayClass Q)

Here the two monoid-hom structures matter: constancy just for prime pairs
does not imply constancy for products with the same total class.  A concrete
Eisenstein quadratic reciprocity calculation must identify the explicit
residue-character product in `quadraticReciprocityDefect_prime_eq` with such
a multiplicative local correction.  Rational Legendre/Jacobi reciprocity in
Mathlib does not itself provide this number-field assertion.
-/

end QRHShort

#print axioms QRHShort.quadraticRayClass_eq_iff
#print axioms QRHShort.quadraticReciprocityDefect_mul_left
#print axioms QRHShort.quadraticReciprocityDefect_mul_right
#print axioms QRHShort.quadraticReciprocityDefect_eq_prod_primePairs
#print axioms QRHShort.quadraticReciprocityDefect_prime_eq
