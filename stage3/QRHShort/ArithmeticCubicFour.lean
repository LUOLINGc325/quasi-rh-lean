import QRHShort.ArithmeticRayReciprocity
import QRHShort.CubicGaussEvaluation
import OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization

/-! The supplementary character at four on the frozen ray group.
The mod-three unit normalization is reused from the existing primary-class
candidate; the sextic/cubic and complex-embedding bridges are the already
checked CubicGauss declarations.  All ideal factorizations retain multiplicity.
-/
noncomputable section
set_option autoImplicit false
open Classical

namespace QRHShort.ArithmeticProof.Ray.CubicFour
open SquarefreeReflection
open SquarefreeReflection.RayValuePrerequisites
open CubicGauss
open OAI.ActualEisensteinCubic (cubicTwoIdeal cubicTwoIdeal_good cubicChar)
open OAI.ConcreteTraceCRT (eisEmbedding)

abbrev ModThree := O ⧸ principal (3 : O)
abbrev ModFour := O ⧸ principal (4 : O)

def unitModThree : Oˣ →* ModThreeˣ :=
  Units.map (Ideal.Quotient.mk (principal 3)).toMonoidHom

theorem primary_iff_modThree (z : O) :
    IsPrimary z ↔ Ideal.Quotient.mk (principal 3) z = 1 := by
  change z - 1 ∈ principal 3 ↔ _
  constructor
  · intro hz
    have h : Ideal.Quotient.mk (principal 3) (z - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hz
    simpa only [map_sub, map_one, sub_eq_zero] using h
  · intro hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (principal 3) (z - 1) = 0
    simp only [map_sub, map_one, hz, sub_self]

theorem unitModThree_injective : Function.Injective unitModThree := by
  apply (injective_iff_map_eq_one unitModThree).mpr
  intro u hu
  apply primary_unit_eq_one
  apply (primary_iff_modThree _).mpr
  exact congrArg Units.val hu

theorem unitModThree_surjective : Function.Surjective unitModThree := by
  intro x
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (x : ModThree)
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (↑x⁻¹ : ModThree)
  have hzw : (3 : O) ∣ z * w - 1 := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (principal 3) (z * w - 1) = 0
    simp only [map_sub, map_mul, map_one, hz, hw,
      Units.mul_inv, sub_self]
  have hn : ¬ omega - 1 ∣ z := by
    intro hd
    have hd' := dvd_mul_of_dvd_left hd w
    have hd'' := omega_sub_one_dvd_three.trans hzw
    apply omega_sub_one_prime.not_dvd_one
    convert dvd_sub hd' hd'' using 1 <;> ring
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hn
  have he : unitModThree u * x = 1 := by
    apply Units.ext
    change Ideal.Quotient.mk (principal 3) (u : O) * (x : ModThree) = 1
    rw [← hz, ← map_mul]
    exact (primary_iff_modThree _).mp hu
  refine ⟨u⁻¹, ?_⟩
  calc
    unitModThree (u⁻¹) = unitModThree (u⁻¹) * 1 := (mul_one _).symm
    _ = unitModThree (u⁻¹) * (unitModThree u * x) := by rw [he]
    _ = x := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- Every invertible residue modulo three has a unique global unit lift. -/
def unitModThreeEquiv : Oˣ ≃* ModThreeˣ :=
  MulEquiv.ofBijective unitModThree ⟨unitModThree_injective, unitModThree_surjective⟩


abbrev ModTwo := O ⧸ cubicTwoIdeal

theorem twelve_le_two : principal (12 : O) ≤ cubicTwoIdeal := by
  rw [cubicTwoIdeal, Ideal.span_singleton_neg]
  apply Ideal.span_le.mpr
  rintro z (rfl : z = (12 : O))
  exact Ideal.mem_span_singleton.mpr ⟨6, by norm_num⟩

theorem twelve_le_three : principal (12 : O) ≤ principal 3 := by
  apply Ideal.span_le.mpr
  rintro z (rfl : z = (12 : O))
  exact Ideal.mem_span_singleton.mpr ⟨4, by norm_num⟩

def reduceTwo (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12) :
    (O ⧸ c.rayModulus)ˣ →* ModTwoˣ :=
  Units.map (Ideal.Quotient.factor (hc.trans twelve_le_two)).toMonoidHom

def reduceThree (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12) :
    (O ⧸ c.rayModulus)ˣ →* ModThreeˣ :=
  Units.map (Ideal.Quotient.factor (hc.trans twelve_le_three)).toMonoidHom

def globalModTwo : Oˣ →* ModTwoˣ :=
  Units.map (Ideal.Quotient.mk cubicTwoIdeal).toMonoidHom

/-- Remove the unique global unit specified by reduction modulo three. -/
def normalizedTwo (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12) :
    (O ⧸ c.rayModulus)ˣ →* ModTwoˣ :=
  reduceTwo c hc /
    (globalModTwo.comp (unitModThreeEquiv.symm.toMonoidHom.comp (reduceThree c hc)))

theorem normalizedTwo_global (c : ArithmeticContext)
    (hc : c.rayModulus ≤ principal 12) (u : Oˣ) :
    normalizedTwo c hc (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u) = 1 := by
  have hthree : reduceThree c hc
      (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u) = unitModThreeEquiv u := by
    apply Units.ext
    exact Ideal.Quotient.factor_mk _ _
  have htwo : reduceTwo c hc
      (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u) = globalModTwo u := by
    apply Units.ext
    exact Ideal.Quotient.factor_mk _ _
  simp only [normalizedTwo, MonoidHom.div_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, hthree, htwo, MulEquiv.symm_apply_apply, div_self']

theorem normalizedTwo_primary (c : ArithmeticContext)
    (hc : c.rayModulus ≤ principal 12) {z : O}
    (hz : IsPrimary z) (hu : IsUnit (Ideal.Quotient.mk c.rayModulus z)) :
    (normalizedTwo c hc hu.unit : ModTwo) = Ideal.Quotient.mk cubicTwoIdeal z := by
  have hthree : reduceThree c hc hu.unit = 1 := by
    apply Units.ext
    change Ideal.Quotient.factor _ (hu.unit : O ⧸ c.rayModulus) = 1
    rw [IsUnit.unit_spec, Ideal.Quotient.factor_mk]
    exact (primary_iff_modThree z).mp hz
  simp only [normalizedTwo, MonoidHom.div_apply, MonoidHom.comp_apply,
    hthree, map_one, div_one]
  change Ideal.Quotient.factor _ (hu.unit : O ⧸ c.rayModulus) = _
  rw [IsUnit.unit_spec, Ideal.Quotient.factor_mk]

def fixedValue (z : O) : ℂ :=
  eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
    (Ideal.Quotient.mk cubicTwoIdeal z))

theorem fixedValue_mul (z w : O) : fixedValue (z * w) = fixedValue z * fixedValue w := by
  simp only [fixedValue, map_mul]

/-- The existing bridge identifies the frozen symbol, including its embedding,
with the cubic symbol; primary cubic reciprocity then moves its denominator to two. -/
theorem prime_four (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) : sexticSymbol P 4 = fixedValue (primaryGenerator P) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hfour : sexticSymbol P 4 = sexticSymbol P (-2) ^ (2 : ℕ) := by
    rw [pow_two, ← sexticSymbol_mul_numerator c hn]
    norm_num
  rw [hfour, prime_cubic_symbol c hp hn]
  unfold fixedValue
  congr 1
  have hs := primaryGenerator_spec_outside c hn
  exact OAI.ActualEisensteinCubic.cubic_reciprocity_primary P cubicTwoIdeal
    (prime_good c hp hn) cubicTwoIdeal_good (primaryGenerator P) (-2)
    hs.1.symm rfl (primary_lambda_sq hs.2) OAI.ActualEisensteinCubic.neg_two_primary

theorem symbol_mul_denominator {a b : Ideal O} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  have hab : a * b ≠ ⊥ := by
    intro h
    exact (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab,
    UniqueFactorizationMonoid.normalizedFactors_mul ha hb,
    Multiset.map_add, Multiset.prod_add]

/-- Prime powers and repeated normalized factors are included in this induction. -/
theorem ideal_four (c : ArithmeticContext) {a : Ideal O} (ha : Outside c.S a) :
    sexticSymbol a 4 = fixedValue (primaryGenerator a) := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun a : Ideal O => Outside c.S a →
      sexticSymbol a 4 = fixedValue (primaryGenerator a)) a ?_ ?_ ?_ ha
  · intro h
    exact (h.1 rfl).elim
  · intro a ha _
    have he : a = 1 := isUnit_iff_eq_one.mp ha
    subst a
    rw [primaryGenerator_one, sexticSymbol,
      ite_eq_right (show (1 : Ideal O) ≠ ⊥ by
        simpa only [Ideal.one_eq_top] using (top_ne_bot : (⊤ : Ideal O) ≠ ⊥)),
      UniqueFactorizationMonoid.normalizedFactors_one]
    simp only [Multiset.map_zero, Multiset.prod_zero, fixedValue, map_one]
  · intro a P _ hp ih h
    have hP : Outside c.S P := outside_of_dvd h (dvd_mul_right P a)
    have ha : Outside c.S a := outside_of_dvd h (dvd_mul_left a P)
    rw [symbol_mul_denominator hP.1 ha.1, primaryGenerator_mul c hP ha,
      fixedValue_mul, prime_four c hp hP, ih ha]

/-- Conjugation is part of the frozen convention. -/
def twoUnits : ModTwoˣ →* ℂ where
  toFun u := star (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good (u : ModTwo)))
  map_one' := by simp
  map_mul' u v := by simp only [Units.val_mul, map_mul, star_mul']

theorem twoUnits_cube (u : ModTwoˣ) : twoUnits u ^ (3 : ℕ) = 1 := by
  have h : cubicChar cubicTwoIdeal cubicTwoIdeal_good (u : ModTwo) ^ (3 : ℕ) = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
      OAI.ActualEisensteinCubic.cubicChar_pow_three, MulChar.one_apply u.isUnit]
  change star (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good (u : ModTwo))) ^
    (3 : ℕ) = 1
  rw [← star_pow, ← map_pow, h, map_one, star_one]

def rayCharacter (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12) :
    RayClass c →* ℂ :=
  QuotientGroup.lift (globalUnitImage c) (twoUnits.comp (normalizedTwo c hc)) (by
    rintro x ⟨u, rfl⟩
    change twoUnits (normalizedTwo c hc
      (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u)) = 1
    rw [normalizedTwo_global, map_one])

theorem rayCharacter_cube (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12)
    (x : RayClass c) : rayCharacter c hc x ^ (3 : ℕ) = 1 := by
  refine Quotient.inductionOn x (fun u => ?_)
  change twoUnits (normalizedTwo c hc u) ^ (3 : ℕ) = 1
  exact twoUnits_cube _

theorem rayCharacter_ideal (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12)
    {a : Ideal O} (ha : Outside c.S a) :
    rayCharacter c hc (idealClass c a) = star (sexticSymbol a 4) := by
  have hu := primaryGenerator_unit_mod_supported c c.rayModulus
    c.rayModulus_ne_bot c.ray_supported ha
  have hp := (primaryGenerator_spec_outside c ha).2
  change rayCharacter c hc (rayClass c (primaryGenerator a)) = _
  rw [rayClass, dif_pos hu]
  change star (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
    (normalizedTwo c hc hu.unit : ModTwo))) = _
  rw [normalizedTwo_primary c hc hp hu]
  exact congrArg star (ideal_four c ha).symm

end QRHShort.ArithmeticProof.Ray.CubicFour

namespace QRHShort.ArithmeticProof.Ray

/-- The original frozen statement, with no remaining arithmetic premises. -/
theorem cubicFourRayCharacter : CubicFourRayCharacterStatement := by
  intro c hc
  exact ⟨CubicFour.rayCharacter c hc, CubicFour.rayCharacter_cube c hc,
    fun a ha => CubicFour.rayCharacter_ideal c hc ha⟩

end QRHShort.ArithmeticProof.Ray

#print axioms QRHShort.ArithmeticProof.Ray.CubicFour.prime_four
#print axioms QRHShort.ArithmeticProof.Ray.CubicFour.ideal_four
#print axioms QRHShort.ArithmeticProof.Ray.cubicFourRayCharacter

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations : Array (Name × ConstantInfo) := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof.Ray.CubicFour).isPrefixOf name ||
          name == `QRHShort.ArithmeticProof.Ray.cubicFourRayCharacter then entries.push (name, info)
      else entries) #[]
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Cubic-four ray: forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Cubic-four ray declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No cubic-four ray declarations audited"
  logInfo m!"CUBIC_FOUR_RAY_AUDIT declarations={checked} forbidden=0 pending_children=0"
