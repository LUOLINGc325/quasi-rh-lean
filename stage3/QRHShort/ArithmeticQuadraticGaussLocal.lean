import QRHShort.ArithmeticRayReciprocity
import OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization

/-! Identify the upstream four-term quadratic phase with the frozen square-class values. -/
noncomputable section
set_option autoImplicit false
open Classical

namespace QRHShort.ArithmeticProof.Ray.QuadraticGauss
open OAI.QuadraticGaussRay
open OAI.ActualEisensteinCoordinates hiding O omega

theorem quotient_mk (z : O) :
    residueQuotientFour (Ideal.Quotient.mk (principal 4) z) = residue z := rfl

theorem quotient_mul (x y : O ⧸ principal 4) :
    residueQuotientFour (x * y) = OAI.EisensteinEPrimaryPhase.mul
      (residueQuotientFour x) (residueQuotientFour y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact residue_mul

theorem quotient_one : residueQuotientFour (1 : O ⧸ principal 4) = (1, 0) := by
  change residue (1 : O) = (1, 0)
  simpa [eval] using residue_eval 1 0

theorem unit_odd (u : (O ⧸ principal 4)ˣ) :
    OAI.EisensteinEPrimaryPhase.odd (residueQuotientFour (u : O ⧸ principal 4)) := by
  have h : ∀ r s : OAI.EisensteinEPrimaryPhase.Coord,
      OAI.EisensteinEPrimaryPhase.mul r s = (1, 0) → OAI.EisensteinEPrimaryPhase.odd r := by
    decide +kernel
  apply h _ (residueQuotientFour (↑u⁻¹ : O ⧸ principal 4))
  rw [← quotient_mul, Units.mul_inv, quotient_one]

theorem representative_residue (x : LocalClass) :
    residue (representative x) = OAI.EisensteinEPrimaryPhase.rep x.toAdd.1 x.toAdd.2 := by
  have h1 : residue (1 : O) = (1, 0) := by simpa [eval] using residue_eval 1 0
  have hn : residue (-1 : O) = (-1, 0) := by simpa [eval] using residue_eval (-1) 0
  have hd : residue (1 + 2 * omega) = (1, 2) := by
    simpa [eval, QRHShort.omega, OAI.ActualEisensteinCoordinates.omega] using residue_eval 1 2
  fin_cases x
  · change residue ((-1 : O) ^ 0 * (1 + 2 * omega) ^ 0) = (1, 0)
    simpa using h1
  · change residue ((-1 : O) ^ 0 * (1 + 2 * omega) ^ 1) = (1, 2)
    simpa using hd
  · change residue ((-1 : O) ^ 1 * (1 + 2 * omega) ^ 0) = (-1, 0)
    simpa using hn
  · change residue ((-1 : O) ^ 1 * (1 + 2 * omega) ^ 1) = (-1, -2)
    simp only [pow_one, residue_mul, hn, hd]
    decide +kernel

set_option maxHeartbeats 2000000 in
/-- Evaluate the twelve odd residues before substituting their square-class coordinates. -/
theorem rayValue_bits (r : OAI.EisensteinEPrimaryPhase.Coord)
    (hr : OAI.EisensteinEPrimaryPhase.odd r) :
    quadraticRayValue r = gamma (Multiplicative.ofAdd (OAI.EisensteinEPrimaryPhase.bits r)) := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp +decide [OAI.EisensteinEPrimaryPhase.odd] at hr <;>
    simp +decide [OAI.EisensteinEPrimaryPhase.bits, OAI.EisensteinEPrimaryPhase.signBit,
      OAI.EisensteinEPrimaryPhase.normBit, gamma] <;>
    norm_num [quadraticRayValue, OAI.ActualEisensteinCubic.breveGaussianFourTerms_formula,
      ZMod.val, zpow_neg, Complex.I_sq, Complex.I_pow_three, Complex.inv_I] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.inv_I]

/-- The upstream Gaussian four-term expression on the actual four square classes. -/
theorem rayValue_squareclass (x : LocalClass) (u : OAI.EisensteinEPrimaryPhase.Coord)
    (hu : OAI.EisensteinEPrimaryPhase.odd u) :
    quadraticRayValue (OAI.EisensteinEPrimaryPhase.mul
      (OAI.EisensteinEPrimaryPhase.rep x.toAdd.1 x.toAdd.2)
      (OAI.EisensteinEPrimaryPhase.mul u u)) = gamma x := by
  have hrep : ∀ e f : OAI.EisensteinEPrimaryPhase.Bit,
      OAI.EisensteinEPrimaryPhase.odd (OAI.EisensteinEPrimaryPhase.rep e f) := by
    decide +kernel
  rw [rayValue_bits _ (OAI.EisensteinEPrimaryPhase.odd_mul _ _ (hrep _ _)
    (OAI.EisensteinEPrimaryPhase.odd_mul _ _ hu hu)),
    OAI.EisensteinEPrimaryPhase.bits_squareclass _ _ _ hu]
  simp

theorem rayValue_of_hasLocalClass {z : O} {x : LocalClass} (hx : HasLocalClass z x) :
    quadraticRayValue (residue z) = gamma x := by
  obtain ⟨u, hu⟩ := hx
  have he := congrArg residueQuotientFour hu
  rw [quotient_mk, quotient_mul, quotient_mk,
    pow_two, quotient_mul, representative_residue] at he
  rw [he]
  exact rayValue_squareclass x _ (unit_odd u)

end QRHShort.ArithmeticProof.Ray.QuadraticGauss

#print axioms QRHShort.ArithmeticProof.Ray.QuadraticGauss.rayValue_of_hasLocalClass
