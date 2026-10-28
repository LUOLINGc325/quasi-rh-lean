import QRHShort.SquarefreeUnitPowerCharacter

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.SquarefreeReflection

def SProduct (c : ArithmeticContext) (e : c.S → ℕ) : O :=
  ∏ p : c.S, idealGenerator p.val ^ e p

abbrev SResidueIndex (c : ArithmeticContext) := Oˣ × (c.S → Fin 6)

def SRepresentative (c : ArithmeticContext) (r : SResidueIndex c) : O :=
  (r.1 : O) * SProduct c (fun p => (r.2 p).val)

def SResidual (c : ArithmeticContext) (r : SResidueIndex c) (n : Ideal O) : ℂ :=
  sexticSymbol n (SRepresentative c r)

/-- All six actual integer-ring units are covered at once.  This proves the
    entire unit slice of SResidualRayTarget, not the S-prime-generator slice. -/
theorem exists_all_unit_residual_characters (c : ArithmeticContext)
    (hc : ArithmeticRelations c) :
    ∃ M : Ideal O, M ≠ ⊥ ∧ M ≤ c.rayModulus ∧
      (∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) ∧
      ∀ u : Oˣ, ∃ χ : HeckeCharacter, χ.modulus = M ∧
        ∀ n : Ideal O, Outside c.S n →
          rayValue χ n = SResidual c (u, fun _ => 0) n := by
  refine ⟨unitSupplementModulus c, unitSupplementModulus_ne_bot c,
    Ideal.mul_le_left, unitSupplementModulus_supported c, ?_⟩
  intro u
  let η : Oˣ := ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
    (by decide)).unit
  have hη : (η : O) = omega := IsUnit.unit_spec _
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem
    (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
  change u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at hu
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu
  have hpow : ∃ e j : ℕ, (u : O) = (-1 : O) ^ e * omega ^ j := by
    rcases hu with h | h | h | h | h | h
    · exact ⟨0, 0, by simp [h]⟩
    · exact ⟨1, 0, by simp [h]⟩
    · exact ⟨0, 1, by simp [h, hη]⟩
    · exact ⟨1, 1, by simp [h, hη]⟩
    · exact ⟨0, 2, by simp [h, hη]⟩
    · exact ⟨1, 2, by simp [h, hη]⟩
  obtain ⟨e, j, hpow⟩ := hpow
  obtain ⟨χ, hχ, heval⟩ := exists_unit_power_character c hc e j
  refine ⟨χ, hχ, ?_⟩
  intro n hn
  simpa only [SResidual, SRepresentative, SProduct, Fin.val_zero, pow_zero,
    Finset.prod_const_one, mul_one, hpow] using heval n hn

end QRHShort.SquarefreeReflection

set_option pp.fullNames true
#print axioms QRHShort.SquarefreeReflection.SProduct
#print axioms QRHShort.SquarefreeReflection.SRepresentative
#print axioms QRHShort.SquarefreeReflection.SResidual
#print axioms QRHShort.SquarefreeReflection.exists_all_unit_residual_characters
