import QRHShort.ArithmeticRayReciprocity
import OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace

/-! The supplement at -1, for arbitrary outside ideals including prime powers.
The finite-field formula is reused from the sixth-root supplement.  The norm
modulo four is computed in the actual Eisenstein coordinate ring. -/

noncomputable section
set_option autoImplicit false
open Classical

namespace QRHShort.ArithmeticProof.Ray
namespace MinusOne

open SquarefreeReflection.RayValuePrerequisites
open OAI.ActualEisensteinCoordinates hiding O omega
open OAI

abbrev ModFour := O ⧸ principal (4 : O)

-- Reuse the residue descent from the existing primary-class candidate.
theorem residue_eq_of_four_dvd_sub (c d : O) (h : (4 : O) ∣ c - d) :
    residue c = residue d := by
  obtain ⟨z, hz⟩ := h
  have he : c = eval ((coords d).1 + 4 * (coords z).1)
      ((coords d).2 + 4 * (coords z).2) := by
    calc
      c = d + 4 * z := by linear_combination hz
      _ = eval (coords d).1 (coords d).2 + 4 * eval (coords z).1 (coords z).2 := by
        rw [eval_coords, eval_coords]
      _ = _ := by simp only [eval]; push_cast; ring
  rw [he, residue_eval]
  simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]

def residueQuotientFour : ModFour → EisensteinEPrimaryPhase.Coord :=
  Quotient.lift residue (fun c d h => residue_eq_of_four_dvd_sub c d
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Quotient.sound h))))

@[simp] theorem residueQuotientFour_mk (c : O) :
    residueQuotientFour (Ideal.Quotient.mk (principal 4) c) = residue c := rfl

theorem residue_one : residue (1 : O) = (1, 0) := by
  simpa [eval] using residue_eval 1 0

theorem residue_neg_one : residue (-1 : O) = (-1, 0) := by
  simpa [eval] using residue_eval (-1) 0

theorem residue_delta : residue (1 + 2 * omega) = (1, 2) := by
  simpa [eval, QRHShort.omega, OAI.ActualEisensteinCoordinates.omega] using residue_eval 1 2

theorem quotient_one : residueQuotientFour (1 : ModFour) = (1, 0) := residue_one

theorem quotient_mul (x y : ModFour) :
    residueQuotientFour (x * y) =
      EisensteinEPrimaryPhase.mul (residueQuotientFour x) (residueQuotientFour y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact residue_mul

theorem unit_odd (u : ModFourˣ) :
    EisensteinEPrimaryPhase.odd (residueQuotientFour (u : ModFour)) := by
  have h : ∀ r s : EisensteinEPrimaryPhase.Coord,
      EisensteinEPrimaryPhase.mul r s = (1, 0) → EisensteinEPrimaryPhase.odd r := by
    decide +kernel
  apply h _ (residueQuotientFour (↑u⁻¹ : ModFour))
  rw [← quotient_mul, Units.mul_inv, quotient_one]

theorem representative_residue (x : LocalClass) :
    residue (representative x) = EisensteinEPrimaryPhase.rep x.toAdd.1 x.toAdd.2 := by
  unfold representative
  rw [residue_mul]
  fin_cases x <;>
    simp +decide [EisensteinEPrimaryPhase.rep, residue_one, residue_neg_one,
      residue_delta, EisensteinEPrimaryPhase.mul, ZMod.val]

/-- The absolute ideal norm is the positive Eisenstein coordinate norm. -/
theorem absNorm_mod_four (z : O) :
    ((principal z).absNorm : ZMod 4) = EisensteinEPrimaryPhase.norm (residue z) := by
  rw [principal, Ideal.absNorm_span_singleton,
    ActualEisensteinCubic.algebraNorm_eq_coordinate_norm,
    ← Int.cast_natCast, Int.natCast_natAbs,
    abs_of_nonneg (ShortDraftLatticeCount.qO_nonneg z)]
  simp only [ShortDraftLatticeCount.q, residue, EisensteinEPrimaryPhase.norm,
    Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_mul]
  ring

/-- A unit-square multiplier leaves precisely the second norm bit. -/
theorem localClass_absNorm (z : O) (x : LocalClass) (hx : HasLocalClass z x) :
    ((principal z).absNorm : ZMod 4) = if x.toAdd.2 = 0 then 1 else 3 := by
  obtain ⟨u, hu⟩ := hx
  have h := congrArg residueQuotientFour hu
  rw [quotient_mul, pow_two, quotient_mul, residueQuotientFour_mk,
    residueQuotientFour_mk, representative_residue] at h
  rw [absNorm_mod_four, h]
  exact EisensteinEPrimaryPhase.norm_squareclass _ _ _ (unit_odd u)

/-- The existing sixth-root formula evaluates -1 at every outside ideal. -/
theorem symbol_formula (c : ArithmeticContext) {a : Ideal O} (ha : Outside c.S a) :
    sexticSymbol a (-1) = (-1 : ℂ) ^ ((a.absNorm - 1) / 6) := by
  have hneg : embedding (-1 : O) = (-1 : ℂ) := by
    rw [← embeddingHom_apply, map_neg, map_one]
  simpa only [rootSix_cube, hneg] using
    sexticSymbol_rootSix_pow_formula c ha 3

/-- For norms congruent to one modulo six, the exponent parity is read mod four. -/
theorem sign_of_norm (n : ℕ) (hn : n % 6 = 1) (f : ZMod 2)
    (hf : (n : ZMod 4) = if f = 0 then 1 else 3) :
    (-1 : ℂ) ^ ((n - 1) / 6) = if f = 0 then 1 else -1 := by
  have hpow := pow_eq_pow_mod ((n - 1) / 6) (by norm_num : (-1 : ℂ) ^ 2 = 1)
  rw [hpow]
  by_cases h : f = 0
  · rw [if_pos h] at hf ⊢
    have hmod : n % 4 = 1 := by
      have hv := congrArg ZMod.val hf
      simpa only [ZMod.val_natCast, ZMod.val_one_eq_one_mod] using hv
    have he : ((n - 1) / 6) % 2 = 0 := by omega
    rw [he, pow_zero]
  · rw [if_neg h] at hf ⊢
    have hmod : n % 4 = 3 := by
      have hv := congrArg ZMod.val hf
      simpa only [ZMod.val_natCast, ZMod.val_ofNat] using hv
    have he : ((n - 1) / 6) % 2 = 1 := by omega
    rw [he, pow_one]

end MinusOne

/-- The frozen supplementary-law statement, without additional arithmetic inputs. -/
theorem sexticMinusOneSquareClass : SexticMinusOneSquareClassStatement := by
  intro c a ha x hx
  rw [MinusOne.symbol_formula c ha, correction_diagonal]
  apply MinusOne.sign_of_norm _
    (SquarefreeReflection.RayValuePrerequisites.outside_absNorm_mod_six c ha)
  have h := MinusOne.localClass_absNorm (primaryGenerator a) x hx
  rwa [(SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c ha).1] at h

end QRHShort.ArithmeticProof.Ray

#print axioms QRHShort.ArithmeticProof.Ray.sexticMinusOneSquareClass

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let target := `QRHShort.ArithmeticProof.Ray.sexticMinusOneSquareClass
  for ax in (← collectAxioms target) do
    unless allowed.contains ax do
      throwError "Minus-one supplement: forbidden axiom {ax} in {target}"
  logInfo "MINUS_ONE_AUDIT target=SexticMinusOneSquareClassStatement forbidden=0"
