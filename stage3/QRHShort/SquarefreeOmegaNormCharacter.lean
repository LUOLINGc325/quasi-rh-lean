import QRHShort.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
The actual omega character, constructed without an assumption of supplementary
reciprocity.  Its modulus is (9), its residue character is trivial on EVERY
integer-ring unit, and its values are computed using the actual principal-ideal
norm.  The separate RayDescent file connects it to the frozen Outside formula.
-/

noncomputable section

namespace QRHShort.SquarefreeReflection

/-- The even cubic character modulo 9 sends 2 and 7 to omega, and 4 and 5
    to omega squared.  The exponent is only used on residue units. -/
def omegaExponent9 (a : ZMod 9) : ℕ :=
  match a.val with
  | 2 | 7 => 1
  | 4 | 5 => 2
  | _ => 0

private theorem omegaExponent9_mul :
    ∀ a b : ZMod 9, IsUnit a → IsUnit b →
      omegaExponent9 (a * b) = (omegaExponent9 a + omegaExponent9 b) % 3 := by
  decide

private theorem omegaExponent9_neg :
    ∀ a : ZMod 9, omegaExponent9 (-a) = omegaExponent9 a := by
  decide

private theorem omegaExponent9_natAbs (z : ℤ) :
    omegaExponent9 (z : ZMod 9) = omegaExponent9 (z.natAbs : ZMod 9) := by
  rw [← Int.cast_natCast, Int.natCast_natAbs]
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
  · rw [abs_of_neg (lt_of_not_ge hz), Int.cast_neg, omegaExponent9_neg]

private theorem omegaComplex_cube : embedding omega ^ 3 = 1 := by
  have hO : omega ^ 3 = 1 :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_cube_eq_one
  have hK : (omega : K) ^ 3 = 1 := by
    simpa only [map_pow, map_one] using congrArg (algebraMap O K) hO
  have hC : rawEmbedding (omega : K) ^ 3 = 1 := by
    simpa only [map_pow, map_one] using congrArg rawEmbedding hK
  unfold embedding
  split_ifs
  · exact hC
  · simpa only [star_pow, star_one] using congrArg star hC

/-- An explicit homomorphism on the actual six units of Z/9Z. -/
def omegaUnitHom9 : (ZMod 9)ˣ →* ℂ where
  toFun u := embedding omega ^ omegaExponent9 (u : ZMod 9)
  map_one' := by norm_num [omegaExponent9, ZMod.val_one_eq_one_mod]
  map_mul' u v := by
    change embedding omega ^ omegaExponent9 ((u : ZMod 9) * (v : ZMod 9)) = _
    rw [omegaExponent9_mul _ _ u.isUnit v.isUnit,
      ← pow_eq_pow_mod (omegaExponent9 (u : ZMod 9) +
        omegaExponent9 (v : ZMod 9)) omegaComplex_cube, pow_add]

/-- Modulo (9) the determinant norm depends only on the residue class.
    The matrix argument uses the existing free integer module O, without
    replacing O by a model ring or assuming a norm-congruence law. -/
theorem norm_mod_nine_congr {a b : O}
    (h : Ideal.Quotient.mk (principal (9 : O)) a =
      Ideal.Quotient.mk (principal (9 : O)) b) :
    (Algebra.norm ℤ a : ZMod 9) = (Algebra.norm ℤ b : ZMod 9) := by
  classical
  let B := Module.Free.chooseBasis ℤ O
  let f : O →+* Matrix (Module.Free.ChooseBasisIndex ℤ O)
      (Module.Free.ChooseBasisIndex ℤ O) (ZMod 9) :=
    (Int.castRingHom (ZMod 9)).mapMatrix.comp (Algebra.leftMulMatrix B).toRingHom
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)
  have hf : f a = f b := by
    apply sub_eq_zero.mp
    rw [← map_sub, ht, map_mul, map_ofNat]
    have h9 : (9 : Matrix (Module.Free.ChooseBasisIndex ℤ O)
        (Module.Free.ChooseBasisIndex ℤ O) (ZMod 9)) = 0 := by
      have hZ9 : (9 : ZMod 9) = 0 := by decide
      ext i j
      simp [Matrix.ofNat_apply, hZ9]
    rw [h9, zero_mul]
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det B]
  change (Int.castRingHom (ZMod 9)) ((Algebra.leftMulMatrix B a).det) =
    (Int.castRingHom (ZMod 9)) ((Algebra.leftMulMatrix B b).det)
  rw [(Int.castRingHom (ZMod 9)).map_det, (Int.castRingHom (ZMod 9)).map_det]
  exact congrArg Matrix.det hf

private def normModNine (x : O ⧸ principal (9 : O)) : ZMod 9 :=
  (Algebra.norm ℤ (Quotient.out x) : ZMod 9)

private theorem normModNine_mk (a : O) :
    normModNine (Ideal.Quotient.mk (principal (9 : O)) a) =
      (Algebra.norm ℤ a : ZMod 9) :=
  norm_mod_nine_congr (Ideal.Quotient.mk_out _)

/-- Multiplicative determinant norm on the genuine quotient O/(9). -/
def normModNineHom : (O ⧸ principal (9 : O)) →* ZMod 9 where
  toFun := normModNine
  map_one' := by
    change normModNine (Ideal.Quotient.mk (principal (9 : O)) 1) = 1
    rw [normModNine_mk, map_one, Int.cast_one]
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, normModNine_mk, normModNine_mk, normModNine_mk,
      map_mul, Int.cast_mul]

private def omegaResidue9 : MulChar (O ⧸ principal (9 : O)) ℂ :=
  MulChar.ofUnitHom
    (omegaUnitHom9.comp (Units.map normModNineHom)).toHomUnits

private theorem omegaResidue9_on_unit {x : O ⧸ principal (9 : O)}
    (hx : IsUnit x) :
    omegaResidue9 x = embedding omega ^ omegaExponent9 (normModNineHom x) := by
  have h := MulChar.ofUnitHom_coe
    (omegaUnitHom9.comp (Units.map normModNineHom)).toHomUnits hx.unit
  change omegaResidue9 (hx.unit : O ⧸ principal (9 : O)) =
    embedding omega ^ omegaExponent9
      (normModNineHom (hx.unit : O ⧸ principal (9 : O))) at h
  simpa only [hx.unit_spec] using h

/-- All global units are in the kernel: their integer determinant norms are
    ±1, and this cubic character is even. -/
theorem omegaResidue9_global_unit (u : Oˣ) :
    omegaResidue9 (Ideal.Quotient.mk (principal (9 : O)) (u : O)) = 1 := by
  rw [omegaResidue9_on_unit (u.isUnit.map (Ideal.Quotient.mk _))]
  change embedding omega ^ omegaExponent9
    (normModNine (Ideal.Quotient.mk (principal (9 : O)) (u : O))) = 1
  rw [normModNine_mk]
  rcases Int.isUnit_eq_one_or (u.isUnit.map (Algebra.norm ℤ)) with h | h <;>
    rw [h] <;> norm_num [omegaExponent9, ZMod.val_one_eq_one_mod]

/-- The concrete omega Hecke character has modulus (9), with no abstract
    kernel-triviality or periodicity assumption. -/
def omegaHeckeCharacter : HeckeCharacter where
  modulus := principal (9 : O)
  modulus_ne_bot := by
    intro h
    have h9 : (9 : O) = 0 := Ideal.span_singleton_eq_bot.mp h
    norm_num at h9
  residue := omegaResidue9
  unit_trivial := omegaResidue9_global_unit

/-- Values on every invertible element residue are given by the ACTUAL
    principal-ideal norm, including the unit-independence of that norm. -/
theorem omegaHeckeCharacter_onElement {x : O}
    (hx : IsUnit (Ideal.Quotient.mk (principal (9 : O)) x)) :
    omegaHeckeCharacter.onElement x =
      embedding omega ^ omegaExponent9 (((principal x).absNorm : ℕ) : ZMod 9) := by
  change omegaResidue9 (Ideal.Quotient.mk (principal (9 : O)) x) = _
  rw [omegaResidue9_on_unit hx]
  change embedding omega ^ omegaExponent9
    (normModNine (Ideal.Quotient.mk (principal (9 : O)) x)) = _
  rw [normModNine_mk, omegaExponent9_natAbs, principal, Ideal.absNorm_span_singleton]

/-- The finite exponent table agrees with the previously computed sextic
    omega supplement on EVERY norm that is 1 modulo 6. -/
theorem omegaExponent9_of_mod_six (a : ℕ) (ha : a % 6 = 1) :
    omegaExponent9 (a : ZMod 9) = ((a - 1) / 6) % 3 := by
  have hcases : a % 18 = 1 ∨ a % 18 = 7 ∨ a % 18 = 13 := by omega
  rcases hcases with h | h | h
  · have h9 : a % 9 = 1 := by omega
    have h3 : ((a - 1) / 6) % 3 = 0 := by omega
    simp [omegaExponent9, ZMod.val_natCast, h9, h3]
  · have h9 : a % 9 = 7 := by omega
    have h3 : ((a - 1) / 6) % 3 = 1 := by omega
    simp [omegaExponent9, ZMod.val_natCast, h9, h3]
  · have h9 : a % 9 = 4 := by omega
    have h3 : ((a - 1) / 6) % 3 = 2 := by omega
    simp [omegaExponent9, ZMod.val_natCast, h9, h3]

theorem omegaHeckeCharacter_onElement_formula {x : O}
    (hx : IsUnit (Ideal.Quotient.mk (principal (9 : O)) x))
    (hN : (principal x).absNorm % 6 = 1) :
    omegaHeckeCharacter.onElement x =
      embedding omega ^ (((principal x).absNorm - 1) / 6) := by
  rw [omegaHeckeCharacter_onElement hx, omegaExponent9_of_mod_six _ hN,
    ← pow_eq_pow_mod _ omegaComplex_cube]

/-- No enlargement of the frozen S is required for the omega modulus. -/
theorem omegaHeckeCharacter_supported (c : ArithmeticContext) :
    ∀ p : Ideal O, Prime p → p ∣ omegaHeckeCharacter.modulus → p ∈ c.S := by
  intro p hp hdiv
  apply c.above_three p hp
  apply hp.dvd_of_dvd_pow (n := 2)
  have h9 : principal (9 : O) = principal (3 : O) ^ 2 := by
    rw [principal, principal, Ideal.span_singleton_pow]
    norm_num
  simpa only [omegaHeckeCharacter, h9] using hdiv

end QRHShort.SquarefreeReflection

#print axioms QRHShort.SquarefreeReflection.omegaHeckeCharacter
#print axioms QRHShort.SquarefreeReflection.omegaHeckeCharacter_onElement_formula
#print axioms QRHShort.SquarefreeReflection.omegaHeckeCharacter_supported
