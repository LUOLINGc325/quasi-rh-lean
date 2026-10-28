import QRHShort.ArithmeticStatements
import QRHShort.SquarefreeOmegaRayRefinement

/-! Unit supplements at the explicit common modulus.  The negative supplement
descends from the diagonal reciprocity factor in the frozen arithmetic relations.
For products of unit powers we use the already checked root-six formula. -/

noncomputable section
open Classical

namespace QRHShort.SquarefreeReflection

open RayValuePrerequisites

structure ReciprocityData (c : ArithmeticContext) where
  value : RayClass c → RayClass c → ℂ
  sign : ∀ a b, value a b = 1 ∨ value a b = -1
  symmetric : ∀ a b, value a b = value b a
  mul_left : ∀ a a' b, value (a * a') b = value a b * value a' b
  mul_right : ∀ a b b', value a (b * b') = value a b * value a b'
  reciprocity : ∀ a b : Ideal O, Outside c.S a → Outside c.S b → IsRelPrime a b →
    sexticSymbol b (primaryGenerator a) =
      value (idealClass c a) (idealClass c b) * sexticSymbol a (primaryGenerator b)

def reciprocitySection {c : ArithmeticContext} (d : ReciprocityData c)
    (b : RayClass c) : RayClass c →* ℂ where
  toFun a := d.value a b
  map_one' := by
    have h11 : (1 : RayClass c) * 1 = 1 := one_mul (1 : RayClass c)
    rcases d.sign 1 b with h | h
    · exact h
    · have hmul := d.mul_left 1 1 b
      rw [h11] at hmul
      norm_num [h] at hmul
  map_mul' a a' := d.mul_left a a' b

/-- A homomorphism on the quotient by global units is a Hecke character. -/
def rayCharacterOfHom (c : ArithmeticContext) (f : RayClass c →* ℂ) :
    RayCharacter c :=
  ⟨{ modulus := c.rayModulus
     modulus_ne_bot := c.rayModulus_ne_bot
     residue := MulChar.ofUnitHom
       (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c)))
     unit_trivial := by
       intro u
       let v : (O ⧸ c.rayModulus)ˣ :=
         Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u
       have hv : (QuotientGroup.mk' (globalUnitImage c)) v = 1 :=
         (QuotientGroup.eq_one_iff v).mpr ⟨u, rfl⟩
       change MulChar.ofUnitHom
         (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c)))
         (v : O ⧸ c.rayModulus) = 1
       rw [MulChar.ofUnitHom_coe]
       simp only [MonoidHom.comp_apply, hv, map_one, Units.val_one] }, rfl⟩

theorem rayCharacterOfHom_onElement (c : ArithmeticContext)
    (f : RayClass c →* ℂ) {x : O}
    (hx : IsUnit (Ideal.Quotient.mk c.rayModulus x)) :
    (rayCharacterOfHom c f).val.onElement x = f (rayClass c x) := by
  unfold HeckeCharacter.onElement rayCharacterOfHom rayClass
  rw [dite_eq_left hx]
  have h := MulChar.ofUnitHom_coe
    (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c))) hx.unit
  simpa only [hx.unit_spec, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits,
    QuotientGroup.mk'_apply] using h

theorem rayCharacterOfHom_rayValue (c : ArithmeticContext)
    (f : RayClass c →* ℂ) {n : Ideal O} (hn : Outside c.S n) :
    rayValue (rayCharacterOfHom c f).val n = f (idealClass c n) :=
  rayCharacterOfHom_onElement c f
    (primaryGenerator_unit_mod_supported c c.rayModulus c.rayModulus_ne_bot
      c.ray_supported hn)

def reciprocityDiagonal {c : ArithmeticContext} (d : ReciprocityData c) :
    RayClass c →* ℂ where
  toFun a := d.value a a
  map_one' := (reciprocitySection d 1).map_one
  map_mul' a b := by
    rw [d.mul_left, d.mul_right, d.mul_right, d.symmetric b a]
    rcases d.sign a b with h | h <;> simp only [h] <;> ring

/-- The negative-unit supplement factors through the original ray modulus. -/
theorem exists_negative_unit_character (c : ArithmeticContext)
    (hc : ArithmeticRelations c) :
    ∃ χ : RayCharacter c, ∀ n : Ideal O, Outside c.S n →
      rayValue χ.val n = sexticSymbol n (-1) := by
  obtain ⟨G, R, hG, hsign, hsym, hleft, hright, hGmul, hrec,
    hgauss, hcoeff, hquot⟩ := hc
  let d : ReciprocityData c := ⟨R, hsign, hsym, hleft, hright, hrec⟩
  have hRone : R 1 1 = 1 := (reciprocitySection d 1).map_one
  have hGne : G 1 ≠ 0 := by
    intro h
    have hnorm := hG 1
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hGsquare : G 1 = G 1 * G 1 := by
    have h11 : (1 : RayClass c) * 1 = 1 := one_mul (1 : RayClass c)
    simpa only [h11, hRone, mul_one] using hGmul 1 1
  have hGone : G 1 = 1 :=
    (mul_left_cancel₀ hGne (by simpa only [mul_one] using hGsquare)).symm
  refine ⟨rayCharacterOfHom c (reciprocityDiagonal d), ?_⟩
  intro n hn
  rw [rayCharacterOfHom_rayValue c _ hn]
  change R (idealClass c n) (idealClass c n) = sexticSymbol n (-1)
  have hnorm : star (G (idealClass c n)) * G (idealClass c n) = 1 := by
    simpa only [starRingEnd_apply, hG, one_pow, Complex.ofReal_one] using
      Complex.conj_mul' (G (idealClass c n))
  have hq := hquot n n hn hn
  rw [mul_assoc (sexticSymbol n (-1)) (star (G (idealClass c n)))
    (G (idealClass c n)), hnorm, mul_one, mul_inv_cancel (idealClass c n), hGone] at hq
  have hRR : R (idealClass c n) (idealClass c n) *
      R (idealClass c n) (idealClass c n) = 1 := by
    rcases hsign (idealClass c n) (idealClass c n) with h | h <;> norm_num [h]
  symm
  calc
    sexticSymbol n (-1) = sexticSymbol n (-1) *
        (R (idealClass c n) (idealClass c n) *
          R (idealClass c n) (idealClass c n)) := by rw [hRR, mul_one]
    _ = (sexticSymbol n (-1) * R (idealClass c n) (idealClass c n)) *
        R (idealClass c n) (idealClass c n) := (mul_assoc _ _ _).symm
    _ = R (idealClass c n) (idealClass c n) := by rw [hq, one_mul]

def negativeUnitCharacter (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    RayCharacter c := Classical.choose (exists_negative_unit_character c hc)

theorem negativeUnitCharacter_rayValue (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {n : Ideal O} (hn : Outside c.S n) :
    rayValue (negativeUnitCharacter c hc).val n = sexticSymbol n (-1) :=
  Classical.choose_spec (exists_negative_unit_character c hc) n hn

/-- The required numerator product law follows directly from the root-six
formula, including either exponent being zero. -/
theorem sexticSymbol_unit_power (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (e j : ℕ) :
    sexticSymbol n ((-1 : O) ^ e * omega ^ j) =
      sexticSymbol n (-1) ^ e * sexticSymbol n omega ^ j := by
  let k := (n.absNorm - 1) / 6
  have hneg : sexticSymbol n (-1) = embedding (-1) ^ k := by
    simpa only [rootSix_cube] using sexticSymbol_rootSix_pow_formula c hn 3
  have hu : (-1 : O) ^ e * omega ^ j = rootSix ^ (3 * e + 2 * j) := by
    rw [pow_add, pow_mul, pow_mul, rootSix_cube, rootSix_sq]
  calc
    sexticSymbol n ((-1 : O) ^ e * omega ^ j) =
        embedding ((-1 : O) ^ e * omega ^ j) ^ k := by
      rw [hu]
      exact sexticSymbol_rootSix_pow_formula c hn _
    _ = (embedding (-1) ^ k) ^ e * (embedding omega ^ k) ^ j := by
      rw [← embeddingHom_apply ((-1 : O) ^ e * omega ^ j)]
      simp only [map_mul, map_pow, embeddingHom_apply, mul_pow, ← pow_mul, Nat.mul_comm]
    _ = sexticSymbol n (-1) ^ e * sexticSymbol n omega ^ j := by
      rw [hneg, sexticSymbol_omega_formula c hn]

private theorem mulChar_pow_apply_of_isUnit {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (k : ℕ) {x : R} (hx : IsUnit x) :
    (χ ^ k) x = χ x ^ k := by
  simpa only [hx.unit_spec] using MulChar.pow_apply_coe χ k hx.unit

/-- Every product of powers of the two actual unit supplements is a character
    at the same explicit common modulus. -/
theorem exists_unit_power_character (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (e j : ℕ) :
    ∃ χ : HeckeCharacter, χ.modulus = unitSupplementModulus c ∧
      ∀ n : Ideal O, Outside c.S n →
        rayValue χ n = sexticSymbol n ((-1 : O) ^ e * omega ^ j) := by
  let M := unitSupplementModulus c
  have hM := unitSupplementModulus_ne_bot c
  have hS := unitSupplementModulus_supported c
  have hnegM : M ≤ (negativeUnitCharacter c hc).val.modulus := by
    rw [(negativeUnitCharacter c hc).property]
    change c.rayModulus * omegaHeckeCharacter.modulus ≤ c.rayModulus
    exact Ideal.mul_le_left
  let neg := refineHeckeCharacter (negativeUnitCharacter c hc).val M hM hnegM
  let om := refineHeckeCharacter omegaHeckeCharacter M hM Ideal.mul_le_right
  let negResidue : MulChar (O ⧸ M) ℂ := neg.residue
  let omResidue : MulChar (O ⧸ M) ℂ := om.residue
  let χ : HeckeCharacter :=
    { modulus := M
      modulus_ne_bot := hM
      residue := negResidue ^ e * omResidue ^ j
      unit_trivial := by
        intro u
        have hu := u.isUnit.map (Ideal.Quotient.mk M)
        rw [MulChar.mul_apply, mulChar_pow_apply_of_isUnit _ _ hu,
          mulChar_pow_apply_of_isUnit _ _ hu]
        change neg.onElement (u : O) ^ e * om.onElement (u : O) ^ j = 1
        rw [show neg.onElement (u : O) = 1 from neg.unit_trivial u,
          show om.onElement (u : O) = 1 from om.unit_trivial u, one_pow, one_pow, one_mul] }
  refine ⟨χ, rfl, ?_⟩
  intro n hn
  have hx := primaryGenerator_unit_mod_supported c M hM hS hn
  have hnegValue : neg.onElement (primaryGenerator n) = sexticSymbol n (-1) :=
    (refineHeckeCharacter_onElement (negativeUnitCharacter c hc).val M hM hnegM hx).trans
      (negativeUnitCharacter_rayValue c hc hn)
  have homValue : om.onElement (primaryGenerator n) = sexticSymbol n omega :=
    (refineHeckeCharacter_onElement omegaHeckeCharacter M hM Ideal.mul_le_right hx).trans
      (omegaHeckeCharacter_rayValue c hn)
  change (negResidue ^ e * omResidue ^ j)
    (Ideal.Quotient.mk M (primaryGenerator n)) = _
  rw [MulChar.mul_apply, mulChar_pow_apply_of_isUnit _ _ hx,
    mulChar_pow_apply_of_isUnit _ _ hx]
  change neg.onElement (primaryGenerator n) ^ e *
    om.onElement (primaryGenerator n) ^ j = _
  rw [hnegValue, homValue, sexticSymbol_unit_power c hn]

set_option pp.fullNames true
#print axioms mulChar_pow_apply_of_isUnit

end QRHShort.SquarefreeReflection

#print axioms QRHShort.ArithmeticRelations
#print axioms QRHShort.SquarefreeReflection.ReciprocityData
#print axioms QRHShort.SquarefreeReflection.reciprocitySection
#print axioms QRHShort.SquarefreeReflection.rayCharacterOfHom
#print axioms QRHShort.SquarefreeReflection.rayCharacterOfHom_onElement
#print axioms QRHShort.SquarefreeReflection.rayCharacterOfHom_rayValue
#print axioms QRHShort.SquarefreeReflection.reciprocityDiagonal
#print axioms QRHShort.SquarefreeReflection.exists_negative_unit_character
#print axioms QRHShort.SquarefreeReflection.negativeUnitCharacter
#print axioms QRHShort.SquarefreeReflection.negativeUnitCharacter_rayValue
#print axioms QRHShort.SquarefreeReflection.sexticSymbol_unit_power
#print axioms QRHShort.SquarefreeReflection.exists_unit_power_character
