import QRHShort.ArithmeticReduction
import QRHShort.SquarefreeNumeratorProducts
import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Tactic.ByContra
import Lean.Util.CollectAxioms

set_option autoImplicit false

/-!
Inverse-character Gauss sums on finite rings, and their application to the
frozen `InverseGaussEvaluationStatement`.  Multiplicative primitivity is
formulated on ideals, so the argument applies to squarefree composite moduli
and to the unit ideal, not only to finite fields.

The finite Fourier argument follows the elementary argument in
`OAI.NumberTheory.DirichletL.FiniteFourier`; only Mathlib and the verified
arithmetic definitions are imported.  The two concrete primitivity inputs
below are explicit propositions, not axioms or admitted proofs.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ArithmeticProof.InverseGauss
open SquarefreeReflection.RayValuePrerequisites

section FiniteRing
variable {R : Type*} [CommRing R] [Fintype R]

/-- Every nonzero ideal detects a unit on which the character is nontrivial. -/
def PrimitiveOnIdeals (χ : MulChar R ℂ) : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃ u : Rˣ, (u : R) - 1 ∈ I ∧ χ (u : R) ≠ 1

theorem primitiveOnIdeals_of_field {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) : PrimitiveOnIdeals χ := by
  intro I hI
  have htop : I = ⊤ := (Ideal.eq_bot_or_top I).resolve_left hI
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  exact ⟨u, by rw [htop]; trivial, hu⟩

theorem exists_nonzero_annihilator {a : R} (ha : ¬ IsUnit a) :
    ∃ b : R, b ≠ 0 ∧ a * b = 0 := by
  by_contra! h
  apply ha
  apply IsLeftRegular.isUnit_of_finite
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro b hb
  by_contra hb0
  exact h b hb0 hb

theorem exists_unit_stabilizer (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    {a : R} (ha : ¬ IsUnit a) :
    ∃ u : Rˣ, a * (u : R) = a ∧ χ (u : R) ≠ 1 := by
  obtain ⟨b, hb, hab⟩ := exists_nonzero_annihilator ha
  have hI : Ideal.span ({b} : Set R) ≠ ⊥ := by
    intro hI
    have hbI := Ideal.mem_span_singleton_self b
    rw [hI] at hbI
    exact hb hbI
  obtain ⟨u, hu, hχu⟩ := hχ _ hI
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hu
  refine ⟨u, ?_, hχu⟩
  have hzero : a * ((u : R) - 1) = 0 := by
    rw [hd, ← mul_assoc, hab, zero_mul]
  linear_combination hzero

theorem gaussSum_nonunit_shift (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) {a : R} (ha : ¬ IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  obtain ⟨u, hu, hχu⟩ := exists_unit_stabilizer χ hχ ha
  have hshift : (ψ.mulShift a).mulShift (u : R) = ψ.mulShift a := by
    ext x
    simp only [AddChar.mulShift_apply, ← mul_assoc, hu]
  have heq := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hshift] at heq
  exact eq_zero_of_mul_eq_self_left hχu heq

theorem gaussSum_shift (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa only [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [gaussSum_nonunit_shift χ hχ ψ ha, MulChar.map_nonunit _ ha, zero_mul]

theorem fourier_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (x : R) :
    (∑ a : R, (∑ y : R, f y * ψ (a * y)) * ψ (-(a * x))) =
      (Fintype.card R : ℂ) * f x := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y : R, ∑ a : R, f y * ψ (a * y) * ψ (-(a * x))) =
        ∑ y : R, f y * ∑ a : R, ψ (a * (y - x)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (Fintype.card R : ℂ) * f x := by
      simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero]
      simp [mul_ite, mul_comm]

theorem gaussSum_mul_conjugate (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by
  have hinv := fourier_inversion ψ hψ (fun x => χ x) 1
  change (∑ a : R, gaussSum χ (ψ.mulShift a) * ψ (-(a * 1))) = _ at hinv
  simp only [gaussSum_shift χ hχ, mul_one, map_one] at hinv
  rw [star_gaussSum_eq]
  calc
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ =
        ∑ a : R, (χ⁻¹ a * gaussSum χ ψ) * ψ (-a) := by
      change gaussSum χ ψ * (∑ a : R, χ⁻¹ a * ψ⁻¹ a) = _
      rw [Finset.mul_sum]
      simp only [AddChar.inv_apply]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (Fintype.card R : ℂ) := hinv

/-- The inverse-pair identity without a field hypothesis on the finite ring. -/
theorem gaussSum_inverse_pair (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card R : ℂ) := by
  have hminus : χ⁻¹ (-1) = χ (-1) := by
    have hmul : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right hmul
  have hshift := gaussSum_mulShift χ⁻¹ ψ (-1 : Rˣ)
  have hshift_char : ψ.mulShift (-1 : R) = ψ⁻¹ := ψ.inv_mulShift.symm
  rw [Units.coe_neg_one, hshift_char, hminus] at hshift
  calc
    gaussSum χ ψ * gaussSum χ⁻¹ ψ =
        χ (-1) * (gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹) := by
      rw [← hshift]
      ring
    _ = χ (-1) * (Fintype.card R : ℂ) := by
      rw [← star_gaussSum_eq, gaussSum_mul_conjugate χ hχ ψ hψ]

theorem normalized_inverse_pair (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ((Real.sqrt (Fintype.card R) : ℂ)⁻¹ * gaussSum χ ψ) *
      ((Real.sqrt (Fintype.card R) : ℂ)⁻¹ * gaussSum χ⁻¹ ψ) = χ (-1) := by
  have hq : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card R) : ℂ) ^ 2 = (Fintype.card R : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card R) : (0 : ℝ) ≤ _)
  calc
    _ = ((Real.sqrt (Fintype.card R) : ℂ) ^ 2)⁻¹ *
        (gaussSum χ ψ * gaussSum χ⁻¹ ψ) := by rw [pow_two, mul_inv]; ring
    _ = (Fintype.card R : ℂ)⁻¹ * (χ (-1) * (Fintype.card R : ℂ)) := by
      rw [hs, gaussSum_inverse_pair χ hχ ψ hψ]
    _ = χ (-1) := by rw [mul_left_comm, inv_mul_cancel₀ hq, mul_one]

end FiniteRing

end QRHShort.ArithmeticProof.InverseGauss

#print axioms QRHShort.ArithmeticProof.InverseGauss.normalized_inverse_pair


/-! The frozen sextic symbol, including its zero values, as a character of the
actual quotient ring.  No squarefreeness or primitivity is used for descent. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.ArithmeticProof.InverseGauss
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites

@[simp] theorem residueLift_spec (n : Ideal O) (x : O ⧸ n) :
    Ideal.Quotient.mk n (residueLift n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

theorem sexticSymbol_congr (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) {a b : O}
    (hab : Ideal.Quotient.mk n a = Ideal.Quotient.mk n b) :
    sexticSymbol n a = sexticSymbol n b := by
  simp only [sexticSymbol, if_neg hn.1]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hnP : n ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
  have habP : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr
      (hnP ((Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab))
  simp only [sexticAtPrime, habP]

theorem sexticSymbol_zero_of_nonunit (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (a : O) (ha : ¬ IsUnit (Ideal.Quotient.mk n a)) :
    sexticSymbol n a = 0 := by
  by_contra hzero
  have hcop : IsCoprime n (principal a) := by
    apply Ideal.coprime_of_no_prime_ge
    intro P hnP haP hP
    have hP0 : P ≠ ⊥ := fun h => hn.1 (le_bot_iff.mp (h ▸ hnP))
    have hp : Prime P := Ideal.prime_of_isPrime hP0 hP
    have hmem : P ∈ normalizedFactors n :=
      (mem_normalizedFactors_iff hn.1).mpr ⟨hp, Ideal.dvd_iff_le.mpr hnP⟩
    apply hzero
    rw [sexticSymbol, if_neg hn.1]
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.mpr ⟨P, hmem, ?_⟩
    exact sexticAtPrime_zero_of_mem hp
      (outside_quotient_rootSix_isPrimitiveRoot c hp (outside_of_mem_normalizedFactors hn hmem))
      ((Ideal.span_singleton_le_iff_mem P).mp haP)
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp hcop
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hj
  apply ha
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk n b, ?_⟩
  have he := congrArg (Ideal.Quotient.mk n) hij
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hi, zero_add, map_one] at he
  simpa only [hb, map_mul] using he

/-- The actual sextic residue symbol on the quotient, for every ideal outside S. -/
def sexticResidueCharacter (c : ArithmeticContext) (n : Ideal O)
    (hn : Outside c.S n) : MulChar (O ⧸ n) ℂ where
  toFun x := sexticSymbol n (residueLift n x)
  map_one' := by
    rw [sexticSymbol_congr c hn (by simp :
      Ideal.Quotient.mk n (residueLift n 1) = Ideal.Quotient.mk n 1)]
    exact sexticSymbol_one_of_outside c hn
  map_mul' x y := by
    rw [sexticSymbol_congr c hn (by simp :
      Ideal.Quotient.mk n (residueLift n (x * y)) =
        Ideal.Quotient.mk n (residueLift n x * residueLift n y))]
    exact sexticSymbol_mul_numerator c hn _ _
  map_nonunit' x hx :=
    sexticSymbol_zero_of_nonunit c hn _ (by simpa only [residueLift_spec] using hx)

@[simp] theorem sexticResidueCharacter_mk (c : ArithmeticContext) (n : Ideal O)
    (hn : Outside c.S n) (a : O) :
    sexticResidueCharacter c n hn (Ideal.Quotient.mk n a) = sexticSymbol n a := by
  apply sexticSymbol_congr c hn
  exact residueLift_spec _ _

end QRHShort.ArithmeticProof.InverseGauss

#print axioms QRHShort.ArithmeticProof.InverseGauss.sexticResidueCharacter_mk


/-!
The exact inverse Gauss evaluation, conditional only on the two concrete
primitivity statements below.  Neither statement assumes a Gauss sum identity.
The character of the sextic symbol, its descent to the quotient, finite-ring
Fourier inversion, and the square-root normalization are proved above.
The dependencies do not pass through `Manuscript` or `ArithmeticRelations`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ArithmeticProof.InverseGauss

/-- Remaining multiplicative input: the concrete sextic character is primitive
at a squarefree modulus.  For every nonzero ideal of the quotient one must find
a unit congruent to one on which the character is nontrivial. -/
def SexticPrimitivityStatement : Prop :=
  ∀ (c : ArithmeticContext) (n : Ideal O) (hn : SquarefreeOutside c.S n),
    PrimitiveOnIdeals (sexticResidueCharacter c n hn.1)

/-- Remaining additive input: the manuscript's exponential, with its specified
primary generator and embedding, is a primitive additive character on O/n.
The equality on every integral representative includes well-definedness. -/
def AdditivePrimitivityStatement : Prop :=
  ∀ (c : ArithmeticContext) (n : Ideal O), Outside c.S n →
    ∃ ψ : AddChar (O ⧸ n) ℂ, ψ.IsPrimitive ∧
      ∀ a : O, ψ (Ideal.Quotient.mk n a) =
        additiveCharacter (embedding a / embedding (primaryGenerator n))

/-- Exact assembly of the frozen parent, including the unit ideal.  The two
unproved arithmetic inputs remain explicit parameters in the theorem type. -/
theorem inverseGaussEvaluation_of_primitivity
    (hχ : SexticPrimitivityStatement) (hψ : AdditivePrimitivityStatement) :
    InverseGaussEvaluationStatement := by
  intro c n hn
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1.1
  letI : Fintype (O ⧸ n) := Fintype.ofFinite _
  let χ := sexticResidueCharacter c n hn.1
  obtain ⟨ψ, hψprim, hψval⟩ := hψ c n hn.1
  have hψlift (x : O ⧸ n) : ψ x =
      additiveCharacter
        (embedding (residueLift n x) / embedding (primaryGenerator n)) := by
    simpa only [residueLift_spec] using hψval (residueLift n x)
  have hg : gauss 1 n = (Real.sqrt (normIdeal n) : ℂ)⁻¹ * gaussSum χ ψ := by
    simp only [gauss, dif_pos hn.1.1, gaussSum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    change sexticSymbol n (residueLift n x) ^ (1 : ℤ) * _ =
      sexticSymbol n (residueLift n x) * ψ x
    rw [zpow_one, hψlift]
  have hgInv : gauss (-1) n =
      (Real.sqrt (normIdeal n) : ℂ)⁻¹ * gaussSum χ⁻¹ ψ := by
    simp only [gauss, dif_pos hn.1.1, gaussSum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    change sexticSymbol n (residueLift n x) ^ (-1 : ℤ) * _ = χ⁻¹ x * ψ x
    rw [zpow_neg_one, MulChar.inv_apply_eq_inv', hψlift]
    rfl
  have hcard : Fintype.card (O ⧸ n) = n.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hpair := normalized_inverse_pair χ (hχ c n hn) ψ hψprim
  rw [hg, hgInv]
  have hpair' :
      ((Real.sqrt (normIdeal n) : ℂ)⁻¹ * gaussSum χ ψ) *
        ((Real.sqrt (normIdeal n) : ℂ)⁻¹ * gaussSum χ⁻¹ ψ) = χ (-1) := by
    simpa only [hcard, normIdeal] using hpair
  rw [hpair']
  simpa only [map_neg, map_one] using sexticResidueCharacter_mk c n hn.1 (-1)

end QRHShort.ArithmeticProof.InverseGauss

#print axioms QRHShort.ArithmeticProof.InverseGauss.sexticResidueCharacter
#print axioms QRHShort.ArithmeticProof.InverseGauss.normalized_inverse_pair
#print axioms QRHShort.ArithmeticProof.InverseGauss.inverseGaussEvaluation_of_primitivity

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations : Array (Name × ConstantInfo) := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof.InverseGauss).isPrefixOf name then entries.push (name, info)
      else entries) #[]
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      let axioms ← Lean.collectAxioms name
      let forbidden := axioms.filter (fun ax => !allowed.contains ax)
      if !forbidden.isEmpty then
        throwError "InverseGauss audit failed for {name}: {forbidden}"
    | _ => pure ()
  logInfo m!"InverseGauss audit: {checked} declarations; forbidden=0; no sorryAx"
