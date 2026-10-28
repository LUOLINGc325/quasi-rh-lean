import QRHShort.QuadraticConcrete

/-!
The exact product-conductor clause for the concrete quadratic characters.
The equality of signs at `-1` is the component that will be read from equality
of finite ray classes.  No sieve theorem or reciprocity assertion is used here.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem quadratic_sexticSymbol_mul (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, sexticSymbol]
  by_cases hb : b = ⊥
  · simp [hb, sexticSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, if_neg ha, if_neg hb, if_neg hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

theorem quadraticCharacter_onElement (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a) (x : O) :
    (quadraticCharacter a).onElement x =
      if sexticSymbol a (-1) ^ (3 : ℕ) = 1 then sexticSymbol a x ^ (3 : ℕ)
      else sexticSymbol a x ^ (3 : ℕ) *
        quadraticResidueChar quadraticLambdaIdeal (Ideal.Quotient.mk quadraticLambdaIdeal x) := by
  rw [quadraticCharacter, dif_pos ⟨ha, hsq⟩, correctedQuadraticHecke_onElement,
    quadraticFactor_product_eq_sextic_cube ha.1 ha.2 hsq (-1),
    quadraticFactor_product_eq_sextic_cube ha.1 ha.2 hsq x]

theorem quadratic_sextic_neg_one_sq (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a) :
    (sexticSymbol a (-1) ^ (3 : ℕ)) ^ (2 : ℕ) = 1 := by
  rw [← quadraticFactor_product_eq_sextic_cube ha.1 ha.2 hsq (-1)]
  exact quadraticElementProduct_neg_one_sq _

/-- The primitive product has exactly modulus `a * b`, even when each
individual character needs the auxiliary prime above three. -/
theorem quadraticCharacter_product_conductor
    (a b : Ideal O) (ha : FamilyIdeal (principal 6) a)
    (hb : FamilyIdeal (principal 6) b) (hsqa : Squarefree a) (hsqb : Squarefree b)
    (hcop : IsRelPrime a b)
    (hsame : sexticSymbol a (-1) ^ (3 : ℕ) = sexticSymbol b (-1) ^ (3 : ℕ)) :
    ∃ ψ : HeckeCharacter, ψ.modulus = a * b ∧ ψ.IsPrimitive ∧
      ∀ x : O, IsUnit (Ideal.Quotient.mk
        (a * b * (quadraticCharacter a).modulus * (quadraticCharacter b).modulus) x) →
        ψ.onElement x = (quadraticCharacter a).onElement x *
          (quadraticCharacter b).onElement x := by
  have hab : FamilyIdeal (principal 6) (a * b) :=
    ⟨mul_ne_zero ha.1 hb.1, ha.2.mul_left hb.2⟩
  have hsqab : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨hcop, hsqa, hsqb⟩
  have hsignab : sexticSymbol (a * b) (-1) ^ (3 : ℕ) = 1 := by
    rw [quadratic_sexticSymbol_mul, mul_pow, hsame]
    simpa only [pow_two] using quadratic_sextic_neg_one_sq b hb hsqb
  refine ⟨quadraticCharacter (a * b), ?_, quadraticCharacter_primitive _ hab hsqab, ?_⟩
  · rw [quadraticCharacter_modulus _ hab hsqab, if_pos hsignab]
  · intro x hx
    rw [quadraticCharacter_onElement _ hab hsqab, if_pos hsignab,
      quadraticCharacter_onElement a ha hsqa, quadraticCharacter_onElement b hb hsqb,
      quadratic_sexticSymbol_mul, mul_pow]
    by_cases hsa : sexticSymbol a (-1) ^ (3 : ℕ) = 1
    · have hsb : sexticSymbol b (-1) ^ (3 : ℕ) = 1 := hsame.symm.trans hsa
      rw [if_pos hsa, if_pos hsb]
    · have hsb : sexticSymbol b (-1) ^ (3 : ℕ) ≠ 1 := fun h => hsa (hsame.trans h)
      rw [if_neg hsa, if_neg hsb]
      have hma : (quadraticCharacter a).modulus = quadraticLambdaIdeal * a := by
        rw [quadraticCharacter_modulus a ha hsqa, if_neg hsa]
      have hle : a * b * (quadraticCharacter a).modulus * (quadraticCharacter b).modulus ≤
          quadraticLambdaIdeal := calc
        _ ≤ a * b * (quadraticCharacter a).modulus := Ideal.mul_le_left
        _ ≤ (quadraticCharacter a).modulus := Ideal.mul_le_right
        _ = quadraticLambdaIdeal * a := hma
        _ ≤ quadraticLambdaIdeal := Ideal.mul_le_left
      have hux : IsUnit (Ideal.Quotient.mk quadraticLambdaIdeal x) := by
        simpa only [Ideal.Quotient.factor_mk] using
          hx.map (Ideal.Quotient.factor hle)
      have hl2 := quadraticResidueChar_sq quadraticLambdaIdeal
        (Ideal.Quotient.mk quadraticLambdaIdeal x) hux
      calc
        sexticSymbol a x ^ (3 : ℕ) * sexticSymbol b x ^ (3 : ℕ) =
            (sexticSymbol a x ^ (3 : ℕ) * sexticSymbol b x ^ (3 : ℕ)) *
              quadraticResidueChar quadraticLambdaIdeal
                (Ideal.Quotient.mk quadraticLambdaIdeal x) ^ (2 : ℕ) := by
          rw [hl2, mul_one]
        _ = _ := by ring

end QRHShort

#print axioms QRHShort.quadraticCharacter_product_conductor
