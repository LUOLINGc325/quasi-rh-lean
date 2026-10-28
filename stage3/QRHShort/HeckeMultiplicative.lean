import QRHShort.Arithmetic
import Mathlib.LinearAlgebra.Countable

/-!
The actual ideal character is independent of the chosen principal generator:
two generators differ by a unit, on which the residue character is trivial.
No multiplicative property of the choice of generators is assumed.
-/

noncomputable section

namespace QRHShort

/-- A principal ideal is recovered from its chosen generator. -/
theorem idealGenerator_injective : Function.Injective idealGenerator := by
  intro a b h
  exact (Ideal.span_singleton_generator a).symm.trans
    ((congrArg principal h).trans (Ideal.span_singleton_generator b))

/-- Ideal-indexed series in this fixed number field have a countable index. -/
instance ideal_countable : Countable (Ideal O) := by
  letI : Countable O := Finsupp.Countable.of_moduleFinite (R := ℤ)
  exact Function.Injective.countable idealGenerator_injective

theorem HeckeCharacter.onElement_one (χ : HeckeCharacter) : χ.onElement 1 = 1 := by
  simp only [HeckeCharacter.onElement, map_one]

theorem HeckeCharacter.onElement_mul (χ : HeckeCharacter) (a b : O) :
    χ.onElement (a * b) = χ.onElement a * χ.onElement b := by
  simp only [HeckeCharacter.onElement, map_mul]

theorem HeckeCharacter.onElement_mul_unit (χ : HeckeCharacter) (a : O) (u : Oˣ) :
    χ.onElement (a * (u : O)) = χ.onElement a := by
  rw [χ.onElement_mul, show χ.onElement (u : O) = 1 from χ.unit_trivial u, mul_one]

theorem HeckeCharacter.onElement_eq_of_associated (χ : HeckeCharacter) {a b : O}
    (h : Associated a b) : χ.onElement a = χ.onElement b := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, χ.onElement_mul_unit]

theorem HeckeCharacter.onIdeal_of_generator (χ : HeckeCharacter) {I : Ideal O} {a : O}
    (hI : I ≠ ⊥) (ha : principal a = I) : χ.onIdeal I = χ.onElement a := by
  rw [HeckeCharacter.onIdeal, if_neg hI]
  apply χ.onElement_eq_of_associated
  apply Ideal.span_singleton_eq_span_singleton.mp
  change principal (idealGenerator I) = principal a
  exact (Ideal.span_singleton_generator I).trans ha.symm

theorem HeckeCharacter.onIdeal_bot (χ : HeckeCharacter) : χ.onIdeal ⊥ = 0 := by
  simp [HeckeCharacter.onIdeal]

theorem HeckeCharacter.onIdeal_one (χ : HeckeCharacter) : χ.onIdeal 1 = 1 := by
  calc
    χ.onIdeal 1 = χ.onElement 1 :=
      χ.onIdeal_of_generator (by simp) (by simp [principal])
    _ = 1 := χ.onElement_one

theorem HeckeCharacter.onIdeal_mul (χ : HeckeCharacter) (I J : Ideal O) :
    χ.onIdeal (I * J) = χ.onIdeal I * χ.onIdeal J := by
  by_cases hI : I = ⊥
  · simp only [hI, Ideal.bot_mul, χ.onIdeal_bot, zero_mul]
  by_cases hJ : J = ⊥
  · simp only [hJ, Ideal.mul_bot, χ.onIdeal_bot, mul_zero]
  have hIJ : I * J ≠ ⊥ := by
    intro h
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact hI h
    · exact hJ h
  calc
    χ.onIdeal (I * J) = χ.onElement (idealGenerator I * idealGenerator J) :=
      χ.onIdeal_of_generator hIJ (by
        change Ideal.span {idealGenerator I * idealGenerator J} = I * J
        rw [← Ideal.span_singleton_mul_span_singleton]
        exact congrArg₂ (· * ·)
          (Ideal.span_singleton_generator I) (Ideal.span_singleton_generator J))
    _ = χ.onElement (idealGenerator I) * χ.onElement (idealGenerator J) :=
      χ.onElement_mul _ _
    _ = χ.onIdeal I * χ.onIdeal J := by
      rw [HeckeCharacter.onIdeal, if_neg hI, HeckeCharacter.onIdeal, if_neg hJ]

/-- The choice-independent ideal character, including its zero-ideal value. -/
def HeckeCharacter.onIdealHom (χ : HeckeCharacter) : Ideal O →*₀ ℂ where
  toFun := χ.onIdeal
  map_zero' := χ.onIdeal_bot
  map_one' := χ.onIdeal_one
  map_mul' := χ.onIdeal_mul

end QRHShort
