import QRHShort.ArithmeticRayReciprocity
import QRHShort.CubicGaussEvaluation
import OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open Classical
open scoped BigOperators

/-! Sextic reciprocity: concrete symbol and mod-four coordinate bridges.
The prime-symbol candidate is reused from ArithmeticQuadraticGauss. -/

namespace QRHShort.ArithmeticProof.Ray.Sextic
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites
open CubicGauss
open OAI.ConcreteTraceCRT (eisEmbedding eisTraceModChar)
open OAI.QuadraticGaussRay
open OAI.ActualEisensteinCoordinates hiding O omega

theorem prime_char_ne_two (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] : ringChar (O ⧸ P) ≠ 2 := by
  apply OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem
  intro htwo
  exact hn.2 P (c.above_two P hp (Ideal.dvd_span_singleton.mpr htwo)) (dvd_refl P)

theorem sixth_root_lift_injective {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a b : O} (ha : a ^ (6 : ℕ) = 1) (hb : b ^ (6 : ℕ) = 1)
    (hab : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) : a = b := by
  have hroot : IsPrimitiveRoot rootSix 6 := by
    refine ⟨rootSix_pow_six, ?_⟩
    intro l hl
    exact hζ.dvd_of_pow_eq_one l (by rw [← map_pow, hl, map_one])
  obtain ⟨i, hi, hie⟩ := hroot.eq_pow_of_pow_eq_one ha
  obtain ⟨j, hj, hje⟩ := hroot.eq_pow_of_pow_eq_one hb
  rw [← hie, ← hje, map_pow, map_pow] at hab
  have hij := hζ.pow_inj hi hj hab
  subst j
  exact hie.symm.trans hje

/-- Identify the actual sixth-power-residue definition with the upstream
multiplicative character, including its zero value. -/
theorem prime_sextic_symbol (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] (a : O) :
    sexticSymbol P a = OAI.ActualEisensteinCubic.canonicalSextic P
      (prime_good c hp hn) (Ideal.Quotient.mk P a) := by
  let χ := OAI.ActualEisensteinCubic.sexticChar P (prime_good c hp hn)
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hp hn
  rw [sexticSymbol_prime hp]
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hp hζ ha,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, MulChar.map_zero]
  have hunit : IsUnit (Ideal.Quotient.mk P a) :=
    isUnit_iff_ne_zero.mpr (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hχpow : χ (Ideal.Quotient.mk P a) ^ (6 : ℕ) = 1 := by
    rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
      (OAI.ActualEisensteinCubic.sexticChar_powers P (prime_good c hp hn)).2.2]
    exact MulChar.one_apply hunit
  obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ ha
  have hpow : (rootSix ^ j) ^ (6 : ℕ) = 1 := by
    rw [← pow_mul, Nat.mul_comm j 6, pow_mul, rootSix_pow_six, one_pow]
  have hreduce : Ideal.Quotient.mk P (χ (Ideal.Quotient.mk P a)) =
      Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) := by
    have hu := OAI.ActualEisensteinCubic.sexticChar_reduce_unit P
      (prime_good c hp hn) (prime_char_ne_two c hp hn) hunit.unit
    simpa only [IsUnit.unit_spec, Ideal.absNorm_apply, Submodule.cardQuot_apply, χ] using hu
  have he : rootSix ^ j = χ (Ideal.Quotient.mk P a) :=
    sixth_root_lift_injective hζ hpow hχpow (ht.symm.trans hreduce.symm)
  rw [sexticAtPrime_eq_of_test hζ hj ht, he, embedding_eq_eisEmbedding]
  rfl

open OAI
open EisensteinEPrimaryPhase (Coord odd bits)

def elementClass (a : O) : LocalClass := Multiplicative.ofAdd (bits (residue a))

theorem quotient_mk (a : O) :
    residueQuotientFour (Ideal.Quotient.mk (principal (4 : O)) a) = residue a := rfl

theorem quotient_mul (x y : O ⧸ principal (4 : O)) :
    residueQuotientFour (x * y) =
      EisensteinEPrimaryPhase.mul (residueQuotientFour x) (residueQuotientFour y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact residue_mul

theorem quotient_one : residueQuotientFour (1 : O ⧸ principal (4 : O)) = (1, 0) := by
  change residue (1 : O) = (1, 0)
  simpa [eval] using residue_eval 1 0

theorem unit_odd (u : (O ⧸ principal (4 : O))ˣ) :
    odd (residueQuotientFour (u : O ⧸ principal (4 : O))) := by
  have h : ∀ r s : Coord, EisensteinEPrimaryPhase.mul r s = (1, 0) → odd r := by
    decide +kernel
  apply h _ (residueQuotientFour (↑u⁻¹ : O ⧸ principal (4 : O)))
  rw [← quotient_mul, Units.mul_inv, quotient_one]

theorem primary_odd (c : ArithmeticContext) {a : Ideal O} (ha : Outside c.S a) :
    odd (residue (primaryGenerator a)) := by
  have hs : ∀ P : Ideal O, Prime P → P ∣ principal (4 : O) → P ∈ c.S := by
    intro P hP hdiv
    have he : principal (4 : O) = principal (2 : O) * principal 2 := by
      simp only [principal, Ideal.span_singleton_mul_span_singleton]
      norm_num
    rw [he] at hdiv
    exact (hP.dvd_mul.mp hdiv).elim (c.above_two P hP) (c.above_two P hP)
  have hu := primaryGenerator_unit_mod_supported c (principal 4)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)) hs ha
  simpa only [IsUnit.unit_spec, quotient_mk] using unit_odd hu.unit

theorem elementClass_one : elementClass 1 = 1 := by
  have h : residue (1 : O) = (1, 0) := by simpa [eval] using residue_eval 1 0
  change bits (residue (1 : O)) = (0, 0)
  rw [h]
  decide +kernel

theorem elementClass_mul (a b : O) (ha : odd (residue a)) (hb : odd (residue b)) :
    elementClass (a * b) = elementClass a * elementClass b := by
  change bits (residue (a * b)) = bits (residue a) + bits (residue b)
  rw [residue_mul]
  exact EisensteinEPrimaryPhase.bits_mul _ _ ha hb

theorem primary_class_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    elementClass (primaryGenerator (a * b)) =
      elementClass (primaryGenerator a) * elementClass (primaryGenerator b) := by
  rw [primaryGenerator_mul c ha hb]
  exact elementClass_mul _ _ (primary_odd c ha) (primary_odd c hb)

/-- The finite coordinates are exactly those of the existing primary-class candidate. -/
theorem representative_residue (x : LocalClass) :
    residue (representative x) = EisensteinEPrimaryPhase.rep x.toAdd.1 x.toAdd.2 := by
  have h1 : residue (1 : O) = (1, 0) := by simpa [eval] using residue_eval 1 0
  have hn : residue (-1 : O) = (-1, 0) := by simpa [eval] using residue_eval (-1) 0
  have hd : residue (1 + 2 * omega) = (1, 2) := by
    simpa [eval, QRHShort.omega, ActualEisensteinCoordinates.omega] using residue_eval 1 2
  have hcases : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide +kernel
  rcases x with ⟨e, f⟩
  change residue ((-1 : O) ^ e.val * (1 + 2 * omega) ^ f.val) =
    EisensteinEPrimaryPhase.rep e f
  have hv : ∀ a : ZMod 2, a.val = if a = 0 then 0 else 1 := by decide +kernel
  rw [hv e, hv f]
  rw [residue_mul]
  rcases hcases e with rfl | rfl <;> rcases hcases f with rfl | rfl <;>
    simp +decide [EisensteinEPrimaryPhase.rep, h1, hn, hd,
      EisensteinEPrimaryPhase.mul, ZMod.val]

theorem elementClass_of_hasLocalClass {a : O} {x : LocalClass}
    (hx : HasLocalClass a x) : elementClass a = x := by
  obtain ⟨u, hu⟩ := hx
  have hr := congrArg residueQuotientFour hu
  rw [quotient_mul, pow_two, quotient_mul, quotient_mk,
    quotient_mk, representative_residue] at hr
  change bits (residue a) = x.toAdd
  rw [hr]
  exact EisensteinEPrimaryPhase.bits_squareclass _ _ _ (unit_odd u)

theorem rayValue_eq_gamma (r : Coord) (hr : odd r) :
    quadraticRayValue r = gamma (Multiplicative.ofAdd (bits r)) := by
  rcases r with ⟨a, b⟩
  have hv : ∀ x : ZMod 4,
      x.val = if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 2 else 3 := by
    decide +kernel
  unfold quadraticRayValue
  rw [hv a, hv b]
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide +kernel
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    simp +decide [EisensteinEPrimaryPhase.odd, gamma,
      bits, EisensteinEPrimaryPhase.signBit, EisensteinEPrimaryPhase.normBit,
      EisensteinEPrimaryPhase.ePrimary, EisensteinEPrimaryPhase.norm,
      EisensteinEPrimaryPhase.mul, ZMod.val] at hr ⊢ <;>
    norm_num [quadraticRayValue,
      OAI.ActualEisensteinCubic.breveGaussianFourTerms_formula, ZMod.val,
      zpow_neg, Complex.I_sq, Complex.I_pow_three, Complex.inv_I] <;>
    ring

theorem rayPair_eq_correction (a b : O) (ha : odd (residue a)) (hb : odd (residue b)) :
    MixedCrossSeparation.quadraticRayPair (residue a) (residue b) =
      correction (elementClass a) (elementClass b) := by
  unfold MixedCrossSeparation.quadraticRayPair
  rw [rayValue_eq_gamma _ (EisensteinEPrimaryPhase.odd_mul _ _ ha hb),
    rayValue_eq_gamma _ ha, rayValue_eq_gamma _ hb, EisensteinEPrimaryPhase.bits_mul _ _ ha hb]
  change gamma (elementClass a * elementClass b) /
    (gamma (elementClass a) * gamma (elementClass b)) = _
  rw [gamma_mul]
  apply (div_eq_iff ?_).mpr
  · ring
  · apply mul_ne_zero <;> apply ne_zero_of_norm_one <;> exact norm_gamma _

end QRHShort.ArithmeticProof.Ray.Sextic

#print axioms QRHShort.ArithmeticProof.Ray.Sextic.prime_sextic_symbol
#print axioms QRHShort.ArithmeticProof.Ray.Sextic.elementClass_of_hasLocalClass
#print axioms QRHShort.ArithmeticProof.Ray.Sextic.rayPair_eq_correction

