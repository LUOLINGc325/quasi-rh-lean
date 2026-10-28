import QRHShort.SquarefreeRayDescent

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.SquarefreeReflection

/-- Pull back the character on residue UNITS, and then extend by zero on
    nonunits.  This retains the correct imprimitive zero extension. -/
def refineHeckeCharacter (χ : HeckeCharacter) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ χ.modulus) : HeckeCharacter where
  modulus := M
  modulus_ne_bot := hM
  residue := MulChar.ofUnitHom
    (χ.residue.toUnitHom.comp (Units.map (Ideal.Quotient.factor hle).toMonoidHom))
  unit_trivial := by
    intro u
    let v : (O ⧸ M)ˣ := Units.map (Ideal.Quotient.mk M).toMonoidHom u
    change MulChar.ofUnitHom
      (χ.residue.toUnitHom.comp (Units.map (Ideal.Quotient.factor hle).toMonoidHom))
      (v : O ⧸ M) = 1
    rw [MulChar.ofUnitHom_coe]
    change χ.residue (Ideal.Quotient.mk χ.modulus (u : O)) = 1
    exact χ.unit_trivial u

theorem refineHeckeCharacter_onElement (χ : HeckeCharacter) (M : Ideal O)
    (hM : M ≠ ⊥) (hle : M ≤ χ.modulus) {x : O}
    (hx : IsUnit (Ideal.Quotient.mk M x)) :
    (refineHeckeCharacter χ M hM hle).onElement x = χ.onElement x := by
  change MulChar.ofUnitHom
    (χ.residue.toUnitHom.comp (Units.map (Ideal.Quotient.factor hle).toMonoidHom))
    (Ideal.Quotient.mk M x) = χ.residue (Ideal.Quotient.mk χ.modulus x)
  rw [← hx.unit_spec, MulChar.ofUnitHom_coe]
  change χ.residue (Ideal.Quotient.factor hle (hx.unit : O ⧸ M)) =
    χ.residue (Ideal.Quotient.mk χ.modulus x)
  rw [hx.unit_spec, Ideal.Quotient.factor_mk]

/-- Multiplication of ideals refines both original conductors. -/
def unitSupplementModulus (c : ArithmeticContext) : Ideal O :=
  c.rayModulus * omegaHeckeCharacter.modulus

theorem unitSupplementModulus_ne_bot (c : ArithmeticContext) :
    unitSupplementModulus c ≠ ⊥ := by
  intro h
  rcases Ideal.mul_eq_bot.mp h with h | h
  · exact c.rayModulus_ne_bot h
  · exact omegaHeckeCharacter.modulus_ne_bot h

theorem unitSupplementModulus_supported (c : ArithmeticContext) :
    ∀ p : Ideal O, Prime p → p ∣ unitSupplementModulus c → p ∈ c.S := by
  intro p hp h
  rcases hp.dvd_or_dvd h with h | h
  · exact c.ray_supported p hp h
  · exact omegaHeckeCharacter_supported c p hp h

/-- The actual omega character can be put below the ORIGINAL ray modulus
    without adding any prime to S. -/
theorem exists_omega_character_refining_ray (c : ArithmeticContext) :
    ∃ M : Ideal O, M ≠ ⊥ ∧ M ≤ c.rayModulus ∧
      (∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) ∧
      ∃ χ : HeckeCharacter, χ.modulus = M ∧
        ∀ n : Ideal O, Outside c.S n → rayValue χ n = sexticSymbol n omega := by
  let M := unitSupplementModulus c
  have hM := unitSupplementModulus_ne_bot c
  have hS := unitSupplementModulus_supported c
  let χ := refineHeckeCharacter omegaHeckeCharacter M hM Ideal.mul_le_right
  refine ⟨M, hM, Ideal.mul_le_left, hS, χ, rfl, ?_⟩
  intro n hn
  change (refineHeckeCharacter omegaHeckeCharacter M hM Ideal.mul_le_right).onElement
    (primaryGenerator n) = _
  exact (refineHeckeCharacter_onElement omegaHeckeCharacter M hM Ideal.mul_le_right
    (primaryGenerator_unit_mod_supported c M hM hS hn)).trans
      (omegaHeckeCharacter_rayValue c hn)

end QRHShort.SquarefreeReflection

set_option pp.fullNames true
#print axioms QRHShort.SquarefreeReflection.refineHeckeCharacter
#print axioms QRHShort.SquarefreeReflection.refineHeckeCharacter_onElement
#print axioms QRHShort.SquarefreeReflection.unitSupplementModulus_ne_bot
#print axioms QRHShort.SquarefreeReflection.unitSupplementModulus_supported
#print axioms QRHShort.SquarefreeReflection.exists_omega_character_refining_ray
