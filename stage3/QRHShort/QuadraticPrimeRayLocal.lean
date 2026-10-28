import QRHShort.QuadraticFamilyAssembly
import OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation

/-!
A bilinear correction on the frozen quadratic ray group. The finite sign table
and its verification are adapted from the upstream `QuadraticAllOddCRT`
calculation; only the earlier, cached Gauss-sum reciprocity modules are imported.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.QuadraticPrimeLocal
open OAI
open OAI.ActualEisensteinCubic
open OAI.QuadraticGaussRay hiding O
open OAI.ActualEisensteinCoordinates hiding O omega
open OAI.EisensteinEPrimaryPhase (Coord odd)

set_option maxRecDepth 4096
set_option maxHeartbeats 0

def quadraticRayExponent (r : Coord) : ZMod 4 :=
  if r∈({(0,1),(0,3),(1,0),(1,1),(3,0),(3,3)} : Finset Coord) then 0
  else if r∈({(1,2),(1,3),(2,3)} : Finset Coord) then 1 else 3

def fourthRoot (a : ZMod 4) : ℂ := Complex.I^(a.val:ℤ)

lemma fourthRoot_add (a b : ZMod 4) : fourthRoot (a+b)=fourthRoot a*fourthRoot b := by
  unfold fourthRoot
  rw [←zpow_add₀ Complex.I_ne_zero]
  apply I_zpow_eq_of_mod_four
  push_cast
  simp

lemma quadraticRayValue_eq_fourthRoot (r : Coord) (hr : odd r) :
    quadraticRayValue r=fourthRoot (quadraticRayExponent r) := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide +kernel
  rcases r with ⟨a,b⟩
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [quadraticRayExponent,fourthRoot,EisensteinEPrimaryPhase.odd,
      quadraticRayValue,breveGaussianFourTerms_formula,Prod.mk.injEq,hcmp,
      ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf

def quadraticRaySign (r s : Coord) : ℤ :=
  if odd r ∧ odd s then
    if quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s then 1 else -1
  else 0

lemma quadraticRaySign_mul_left (r s t : Coord) :
    quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
      quadraticRaySign r t*quadraticRaySign s t := by
  have h : ∀r s t : Coord,
      quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
        quadraticRaySign r t*quadraticRaySign s t := by decide +kernel
  exact h r s t

lemma quadraticRaySign_symm (r s : Coord) : quadraticRaySign r s=quadraticRaySign s r := by
  have h : ∀r s : Coord,quadraticRaySign r s=quadraticRaySign s r := by decide +kernel
  exact h r s

lemma quadraticRaySign_mul_right (r s t : Coord) :
    quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
      quadraticRaySign r s*quadraticRaySign r t := by
  rw [quadraticRaySign_symm r, quadraticRaySign_mul_left,
    quadraticRaySign_symm s r, quadraticRaySign_symm t r]

lemma quadraticRaySign_sq (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRaySign r s^2=1 := by
  unfold quadraticRaySign
  rw [ite_eq_left ⟨hr,hs⟩]
  split_ifs <;> norm_num

lemma quadraticRaySign_exponent (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by
  have h : ∀r s : Coord,odd r → odd s →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
        (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by decide +kernel
  exact h r s hr hs

lemma quadraticRaySign_root (r s : Coord) (hr : odd r) (hs : odd s) :
    fourthRoot (if quadraticRaySign r s=1 then 0 else 2)=(quadraticRaySign r s:ℂ) := by
  by_cases he : quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]

lemma odd_mul (r s : Coord) (hr : odd r) (hs : odd s) : odd (EisensteinEPrimaryPhase.mul r s) := by
  have h : ∀r s : Coord,odd r → odd s → odd (EisensteinEPrimaryPhase.mul r s) := by decide +kernel
  exact h r s hr hs

theorem quadraticRayValue_mul (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul r s)=
      (quadraticRaySign r s:ℂ)*quadraticRayValue r*quadraticRayValue s := by
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul r s hr hs),quadraticRaySign_exponent r s hr hs,
    fourthRoot_add,fourthRoot_add,quadraticRaySign_root r s hr hs,
    quadraticRayValue_eq_fourthRoot r hr,quadraticRayValue_eq_fourthRoot s hs]

lemma quadraticRayValue_ne_zero_of_odd (r : Coord) (hr : odd r) :
    quadraticRayValue r ≠ 0 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  exact zpow_ne_zero _ Complex.I_ne_zero

lemma quadraticRayPair_eq_sign (r s : Coord) (hr : odd r) (hs : odd s) :
    MixedCrossSeparation.quadraticRayPair r s=(quadraticRaySign r s:ℂ) := by
  unfold MixedCrossSeparation.quadraticRayPair
  rw [quadraticRayValue_mul r s hr hs]
  apply (div_eq_iff (mul_ne_zero (quadraticRayValue_ne_zero_of_odd r hr)
    (quadraticRayValue_ne_zero_of_odd s hs))).mpr
  ring


/-- The first coordinate of the original ray group, in explicit mod-four coordinates. -/
def rayCoord (g : QuadraticRayGroup) : Coord :=
  residueQuotientFour (g.1 : QRHShort.O ⧸ principal (4 : QRHShort.O))

lemma residueQuotientFour_mul (x y : QRHShort.O ⧸ principal (4 : QRHShort.O)) :
    residueQuotientFour (x * y) =
      EisensteinEPrimaryPhase.mul (residueQuotientFour x) (residueQuotientFour y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  exact residue_mul a b

lemma rayCoord_one : rayCoord 1 = (1, 0) := by
  change residue (1 : QRHShort.O) = (1, 0)
  simpa [ActualEisensteinCoordinates.eval] using residue_eval 1 0

lemma rayCoord_mul (g h : QuadraticRayGroup) :
    rayCoord (g * h) = EisensteinEPrimaryPhase.mul (rayCoord g) (rayCoord h) :=
  residueQuotientFour_mul _ _

lemma rayCoord_odd (g : QuadraticRayGroup) : odd (rayCoord g) := by
  have h : ∀ r s : Coord, EisensteinEPrimaryPhase.mul r s = (1, 0) → odd r := by
    decide +kernel
  apply h (rayCoord g) (rayCoord g⁻¹)
  rw [← rayCoord_mul, mul_inv_cancel, rayCoord_one]

lemma sign_one_right (r : Coord) (hr : odd r) : quadraticRaySign r (1, 0) = 1 := by
  have h : ∀ r : Coord, odd r → quadraticRaySign r (1, 0) = 1 := by decide +kernel
  exact h r hr

lemma sign_one_left (r : Coord) (hr : odd r) : quadraticRaySign (1, 0) r = 1 := by
  rw [quadraticRaySign_symm]
  exact sign_one_right r hr

/-- Both multiplication laws are proved on the whole frozen ray group. -/
def bilinearCorrection : QuadraticRayGroup →* (QuadraticRayGroup →* ℂ) where
  toFun g :=
    { toFun := fun h => (quadraticRaySign (rayCoord g) (rayCoord h) : ℂ)
      map_one' := by rw [rayCoord_one, sign_one_right _ (rayCoord_odd g), Int.cast_one]
      map_mul' := by
        intro h k
        rw [rayCoord_mul, quadraticRaySign_mul_right, Int.cast_mul] }
  map_one' := by
    ext h
    change (quadraticRaySign (rayCoord 1) (rayCoord h) : ℂ) = 1
    rw [rayCoord_one, sign_one_left _ (rayCoord_odd h), Int.cast_one]
  map_mul' := by
    intro g h
    ext k
    change (quadraticRaySign (rayCoord (g * h)) (rayCoord k) : ℂ) =
      (quadraticRaySign (rayCoord g) (rayCoord k) : ℂ) *
        (quadraticRaySign (rayCoord h) (rayCoord k) : ℂ)
    rw [rayCoord_mul, quadraticRaySign_mul_left, Int.cast_mul]

lemma rayCoord_class (a : Ideal QRHShort.O) (ha : FamilyIdeal (principal 6) a) :
    rayCoord (quadraticRayClass a) = residue (primaryGenerator a) := by
  simp only [rayCoord, quadraticRayClass, dif_pos ha, IsUnit.unit_spec,
    residueQuotientFour_mk]
  rfl

lemma bilinearCorrection_class (a b : Ideal QRHShort.O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b) :
    bilinearCorrection (quadraticRayClass a) (quadraticRayClass b) =
      MixedCrossSeparation.quadraticRayPair
        (residue (primaryGenerator a)) (residue (primaryGenerator b)) := by
  change (quadraticRaySign (rayCoord (quadraticRayClass a))
    (rayCoord (quadraticRayClass b)) : ℂ) = _
  rw [← rayCoord_class a ha, ← rayCoord_class b hb]
  exact (quadraticRayPair_eq_sign _ _ (rayCoord_odd _) (rayCoord_odd _)).symm

end QRHShort.QuadraticPrimeLocal

#print axioms QRHShort.QuadraticPrimeLocal.bilinearCorrection
#print axioms QRHShort.QuadraticPrimeLocal.bilinearCorrection_class
