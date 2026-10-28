import QRHShort.ArithmeticRayReciprocity
import OAI.NumberTheory.DirichletL.Cusp.MatrixPhases

/-! Primary normalization modulo three followed by square-class coordinates
modulo four.  The normalization kills every global unit, so the resulting
character is defined on the frozen ray group, for every ray modulus contained in (12).
-/

noncomputable section
set_option autoImplicit false
open Classical

namespace QRHShort.ArithmeticProof.Ray
open SquarefreeReflection.RayValuePrerequisites

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

theorem twelve_le_four : principal (12 : O) ≤ principal 4 := by
  apply Ideal.span_le.mpr
  rintro z (rfl : z = (12 : O))
  exact Ideal.mem_span_singleton.mpr ⟨3, by norm_num⟩

theorem twelve_le_three : principal (12 : O) ≤ principal 3 := by
  apply Ideal.span_le.mpr
  rintro z (rfl : z = (12 : O))
  exact Ideal.mem_span_singleton.mpr ⟨4, by norm_num⟩

def reduceFour (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12) :
    (O ⧸ c.rayModulus)ˣ →* ModFourˣ :=
  Units.map (Ideal.Quotient.factor (hc.trans twelve_le_four)).toMonoidHom

def reduceThree (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12) :
    (O ⧸ c.rayModulus)ˣ →* ModThreeˣ :=
  Units.map (Ideal.Quotient.factor (hc.trans twelve_le_three)).toMonoidHom

def globalModFour : Oˣ →* ModFourˣ :=
  Units.map (Ideal.Quotient.mk (principal 4)).toMonoidHom

/-- Correct a residue by the unique global unit with the same reduction mod 3. -/
def normalizedFour (c : ArithmeticContext) (hc : c.rayModulus ≤ principal 12) :
    (O ⧸ c.rayModulus)ˣ →* ModFourˣ :=
  reduceFour c hc /
    (globalModFour.comp (unitModThreeEquiv.symm.toMonoidHom.comp (reduceThree c hc)))

theorem normalizedFour_global (c : ArithmeticContext)
    (hc : c.rayModulus ≤ principal 12) (u : Oˣ) :
    normalizedFour c hc (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u) = 1 := by
  have hthree : reduceThree c hc
      (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u) = unitModThreeEquiv u := by
    apply Units.ext
    exact Ideal.Quotient.factor_mk _ _
  have hfour : reduceFour c hc
      (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u) = globalModFour u := by
    apply Units.ext
    exact Ideal.Quotient.factor_mk _ _
  simp only [normalizedFour, MonoidHom.div_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, hthree, hfour, MulEquiv.symm_apply_apply, div_self']

theorem normalizedFour_primary (c : ArithmeticContext)
    (hc : c.rayModulus ≤ principal 12) {z : O}
    (hz : IsPrimary z) (hu : IsUnit (Ideal.Quotient.mk c.rayModulus z)) :
    (normalizedFour c hc hu.unit : ModFour) = Ideal.Quotient.mk (principal 4) z := by
  have hthree : reduceThree c hc hu.unit = 1 := by
    apply Units.ext
    change Ideal.Quotient.factor _ (hu.unit : O ⧸ c.rayModulus) = 1
    rw [IsUnit.unit_spec, Ideal.Quotient.factor_mk]
    exact (primary_iff_modThree z).mp hz
  simp only [normalizedFour, MonoidHom.div_apply, MonoidHom.comp_apply,
    hthree, map_one, div_one]
  change Ideal.Quotient.factor _ (hu.unit : O ⧸ c.rayModulus) = _
  rw [IsUnit.unit_spec, Ideal.Quotient.factor_mk]

namespace FourCoordinates
open OAI.ActualEisensteinCoordinates hiding O omega
open OAI

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
    residueQuotientFour (x * y) = EisensteinEPrimaryPhase.mul (residueQuotientFour x) (residueQuotientFour y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact residue_mul

theorem quotient_injective : Function.Injective (residueQuotientFour : ModFour → EisensteinEPrimaryPhase.Coord) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq hab
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨z, hz⟩)

theorem unit_odd (u : ModFourˣ) : EisensteinEPrimaryPhase.odd (residueQuotientFour (u : ModFour)) := by
  have h : ∀ r s : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.mul r s = (1, 0) → EisensteinEPrimaryPhase.odd r := by decide +kernel
  apply h _ (residueQuotientFour (↑u⁻¹ : ModFour))
  rw [← quotient_mul, Units.mul_inv, quotient_one]

theorem odd_isUnit (v : EisensteinEPrimaryPhase.Coord) (hv : EisensteinEPrimaryPhase.odd v) :
    IsUnit (Ideal.Quotient.mk (principal 4) (lift v)) := by
  have h : ∀ v : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd v → ∃ w : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.mul v w = (1, 0) := by
    decide +kernel
  obtain ⟨w, hw⟩ := h v hv
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk (principal 4) (lift w), quotient_injective ?_⟩
  rw [quotient_mul, residueQuotientFour_mk, residueQuotientFour_mk,
    residue_lift, residue_lift, quotient_one]
  exact hw

def coordinates : ModFourˣ →* LocalClass where
  toFun u := Multiplicative.ofAdd (EisensteinEPrimaryPhase.bits (residueQuotientFour (u : ModFour)))
  map_one' := by
    change EisensteinEPrimaryPhase.bits (residueQuotientFour (1 : ModFour)) = (0, 0)
    rw [quotient_one]
    decide +kernel
  map_mul' u v := by
    change EisensteinEPrimaryPhase.bits (residueQuotientFour (↑u * ↑v : ModFour)) = _
    rw [quotient_mul]
    exact EisensteinEPrimaryPhase.bits_mul _ _ (unit_odd u) (unit_odd v)

theorem representative_residue (x : LocalClass) :
    residue (representative x) = EisensteinEPrimaryPhase.rep x.toAdd.1 x.toAdd.2 := by
  have hbit (b : ZMod 2) : b = 0 ∨ b = 1 := by
    have hbound : b.val < 2 := ZMod.val_lt b
    have hval : b.val = 0 ∨ b.val = 1 := by omega
    rcases hval with hzero | hone
    · exact Or.inl ((ZMod.val_eq_zero b).mp hzero)
    · exact Or.inr ((ZMod.val_eq_one (by decide : 1 < 2) b).mp hone)
  rcases hbit x.toAdd.1 with he | he <;>
    rcases hbit x.toAdd.2 with hf | hf <;>
    simp [representative, he, hf, EisensteinEPrimaryPhase.rep, residue_mul,
      residue_one, residue_neg_one, residue_delta, EisensteinEPrimaryPhase.mul,
      ZMod.val_one_eq_one_mod]
  rw [show (-(2 * omega) + -1 : O) = (-1 : O) * (1 + 2 * omega) by ring,
    residue_mul, residue_neg_one, residue_delta]
  norm_num [EisensteinEPrimaryPhase.mul]

/-- The coordinates describe actual unit squares in the quotient ring. -/
theorem coordinates_spec (u : ModFourˣ) :
    ∃ v : ModFourˣ, (u : ModFour) =
      Ideal.Quotient.mk (principal 4) (representative (coordinates u)) * (v : ModFour) ^ 2 := by
  obtain ⟨e, f, v, hv, he⟩ := EisensteinEPrimaryPhase.exists_squareclass
    (residueQuotientFour (u : ModFour)) (unit_odd u)
  have hbits : coordinates u = Multiplicative.ofAdd (e, f) := by
    change EisensteinEPrimaryPhase.bits (residueQuotientFour (u : ModFour)) = (e, f)
    rw [he]
    exact EisensteinEPrimaryPhase.bits_squareclass e f v hv
  refine ⟨(odd_isUnit v hv).unit, quotient_injective ?_⟩
  rw [hbits, quotient_mul, residueQuotientFour_mk, representative_residue,
    pow_two, quotient_mul, IsUnit.unit_spec, residueQuotientFour_mk, residue_lift]
  exact he

end FourCoordinates

/-- The frozen primary square-class ray statement, with no unproved inputs. -/
theorem primarySquareClassRay : PrimarySquareClassRayStatement := by
  intro c hc
  let f := FourCoordinates.coordinates.comp (normalizedFour c hc)
  let k : RayClass c →* LocalClass := QuotientGroup.lift (globalUnitImage c) f (by
    rintro x ⟨u, rfl⟩
    change FourCoordinates.coordinates (normalizedFour c hc
      (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u)) = 1
    rw [normalizedFour_global, map_one])
  refine ⟨k, ?_⟩
  intro a ha
  have hu := SquarefreeReflection.primaryGenerator_unit_mod_supported c c.rayModulus
    c.rayModulus_ne_bot c.ray_supported ha
  have hp := (primaryGenerator_spec_outside c ha).2
  change HasLocalClass (primaryGenerator a)
    (k (rayClass c (primaryGenerator a)))
  rw [rayClass, dif_pos hu]
  change ∃ v : ModFourˣ, Ideal.Quotient.mk (principal 4) (primaryGenerator a) =
    Ideal.Quotient.mk (principal 4) (representative
      (FourCoordinates.coordinates (normalizedFour c hc hu.unit))) * (v : ModFour) ^ 2
  rw [← normalizedFour_primary c hc hp hu]
  exact FourCoordinates.coordinates_spec _

end QRHShort.ArithmeticProof.Ray

#print axioms QRHShort.ArithmeticProof.Ray.unitModThreeEquiv
#print axioms QRHShort.ArithmeticProof.Ray.FourCoordinates.coordinates_spec
#print axioms QRHShort.ArithmeticProof.Ray.primarySquareClassRay

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.checked.get.constants.toList do
    if (`QRHShort.ArithmeticProof.Ray).isPrefixOf name then
      match info with
      | .thmInfo _ | .defnInfo _ =>
        checked := checked + 1
        for ax in (← collectAxioms name) do
          unless allowed.contains ax do
            throwError "Primary square-class ray: forbidden axiom {ax} in {name}"
      | .axiomInfo _ => throwError "Primary square-class ray declares axiom {name}"
      | _ => pure ()
  logInfo m!"PRIMARY_CLASSES_AUDIT declarations={checked} forbidden=0"
