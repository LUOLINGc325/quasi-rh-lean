import QRHShort.ArithmeticSexticLocal

/-! The frozen sextic reciprocity law, including repeated prime factors.
The prime-pair argument reuses the cubic reciprocity and quadratic Gauss-sum
inputs behind `ConjugateLevelAction.idealRowHom_primary_reciprocity`, with
explicit bridges to the actual QRHShort symbol and mod-four square classes.
-/

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open Classical
open scoped BigOperators

namespace QRHShort.ArithmeticProof.Ray
namespace Sextic
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites CubicGauss
open OAI
open OAI.ActualEisensteinCoordinates hiding O omega

theorem canonicalSextic_congr (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : ActualEisensteinCubic.lambda ∉ P) (hQ : ActualEisensteinCubic.lambda ∉ Q)
    (h : P = Q) (a : O) :
    ActualEisensteinCubic.canonicalSextic P hP (Ideal.Quotient.mk P a) =
      ActualEisensteinCubic.canonicalSextic Q hQ (Ideal.Quotient.mk Q a) := by
  subst Q
  rfl

theorem prime_cube_product (c : ArithmeticContext) (P Q : Ideal O)
    (hP : Prime P) (hQ : Prime Q) (ha : Outside c.S P) (hb : Outside c.S Q)
    (hab : IsRelPrime P Q) :
    sexticSymbol P (primaryGenerator Q) ^ (3 : ℕ) *
      sexticSymbol Q (primaryGenerator P) ^ (3 : ℕ) =
        correction (elementClass (primaryGenerator P)) (elementClass (primaryGenerator Q)) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Q.IsMaximal := (Ideal.isPrime_of_prime hQ).isMaximal hQ.ne_zero
  have hp := primaryGenerator_spec_outside c ha
  have hq := primaryGenerator_spec_outside c hb
  have hp0 : primaryGenerator P ≠ 0 := by
    intro h
    apply ha.1
    rw [← hp.1, h]
    exact Ideal.span_singleton_zero
  have hq0 : primaryGenerator Q ≠ 0 := by
    intro h
    apply hb.1
    rw [← hq.1, h]
    exact Ideal.span_singleton_zero
  have hne : P ≠ Q := by
    intro h
    exact hP.not_isUnit (hab dvd_rfl (h ▸ dvd_rfl))
  have hcopPQ : IsCoprime P Q := Ideal.isCoprime_of_isMaximal hne
  let p : Bool → O := Bool.rec (primaryGenerator P) (primaryGenerator Q)
  have hpall : ∀ i, p i ≠ 0 := by
    intro i
    cases i
    · exact hp0
    · exact hq0
  letI hmax : ∀ i : Bool, (Ideal.span {p i}).IsMaximal := by
    intro i
    cases i
    · change (principal (primaryGenerator P)).IsMaximal
      rw [hp.1]
      infer_instance
    · change (principal (primaryGenerator Q)).IsMaximal
      rw [hq.1]
      infer_instance
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => (Ideal.span {p i} : Ideal O))) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · change IsCoprime (principal (primaryGenerator P)) (principal (primaryGenerator Q))
      rw [hp.1, hq.1]
      exact hcopPQ
    · change IsCoprime (principal (primaryGenerator Q)) (principal (primaryGenerator P))
      rw [hq.1, hp.1]
      exact hcopPQ.symm
    · exact (hij rfl).elim
  have hg : ∀ i, ActualEisensteinCubic.lambda ∉ Ideal.span {p i} := by
    intro i
    cases i
    · change ActualEisensteinCubic.lambda ∉ principal (primaryGenerator P)
      rw [hp.1]
      exact prime_good c hP ha
    · change ActualEisensteinCubic.lambda ∉ principal (primaryGenerator Q)
      rw [hq.1]
      exact prime_good c hQ hb
  have hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2 := by
    intro i
    cases i
    · change ringChar (O ⧸ principal (primaryGenerator P)) ≠ 2
      rw [hp.1]
      exact prime_char_ne_two c hP ha
    · change ringChar (O ⧸ principal (primaryGenerator Q)) ≠ 2
      rw [hq.1]
      exact prime_char_ne_two c hQ hb
  have hcross := MixedCrossSeparation.quadraticCrossPhase_eq_rayPair p hpall hcop hg hc
    ({false} : Finset Bool) ({true} : Finset Bool) (by decide)
  simp only [MixedCrossSeparation.quadraticCrossPhase, Finset.prod_singleton,
    MixedCrossSeparation.crossSymbol] at hcross
  have hpval := @canonicalSextic_congr (Ideal.span {p false}) P
    (hmax false) inferInstance (hg false) (prime_good c hP ha) hp.1 (p true)
  have hqval := @canonicalSextic_congr (Ideal.span {p true}) Q
    (hmax true) inferInstance (hg true) (prime_good c hQ hb) hq.1 (p false)
  rw [hpval, hqval] at hcross
  rw [prime_sextic_symbol c hP ha, prime_sextic_symbol c hQ hb]
  exact hcross.trans (rayPair_eq_correction _ _ (primary_odd c ha) (primary_odd c hb))

theorem prime_reciprocity (c : ArithmeticContext) (P Q : Ideal O)
    (hP : Prime P) (hQ : Prime Q) (ha : Outside c.S P) (hb : Outside c.S Q)
    (hab : IsRelPrime P Q) :
    sexticSymbol Q (primaryGenerator P) =
      correction (elementClass (primaryGenerator P)) (elementClass (primaryGenerator Q)) *
        sexticSymbol P (primaryGenerator Q) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Q.IsMaximal := (Ideal.isPrime_of_prime hQ).isMaximal hQ.ne_zero
  have hp := primaryGenerator_spec_outside c ha
  have hq := primaryGenerator_spec_outside c hb
  have h2 : sexticSymbol Q (primaryGenerator P) ^ (2 : ℕ) =
      sexticSymbol P (primaryGenerator Q) ^ (2 : ℕ) := by
    rw [prime_cubic_symbol c hQ hb, prime_cubic_symbol c hP ha]
    exact congrArg ConcreteTraceCRT.eisEmbedding
      (ActualEisensteinCubic.cubic_reciprocity_primary Q P
        (prime_good c hQ hb) (prime_good c hP ha)
        (primaryGenerator Q) (primaryGenerator P) hq.1.symm hp.1.symm
        (primary_lambda_sq hq.2) (primary_lambda_sq hp.2))
  have h6 := symbol_sixth c hb (primaryGenerator P)
    (by rw [hp.1]; exact hab.symm)
  have h3 := prime_cube_product c P Q hP hQ ha hb hab
  calc
    _ = sexticSymbol Q (primaryGenerator P) * sexticSymbol Q (primaryGenerator P) ^ 6 := by
      rw [h6, mul_one]
    _ = sexticSymbol Q (primaryGenerator P) ^ 3 *
        (sexticSymbol Q (primaryGenerator P) ^ 2) ^ 2 := by ring
    _ = sexticSymbol Q (primaryGenerator P) ^ 3 *
        (sexticSymbol P (primaryGenerator Q) ^ 2) ^ 2 := by rw [h2]
    _ = (sexticSymbol P (primaryGenerator Q) ^ 3 *
        sexticSymbol Q (primaryGenerator P) ^ 3) * sexticSymbol P (primaryGenerator Q) := by ring
    _ = _ := by rw [h3]

theorem symbol_mul_denominator {a b : Ideal O} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  have hab : a * b ≠ ⊥ := by
    intro h
    exact (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab,
    UniqueFactorizationMonoid.normalizedFactors_mul ha hb,
    Multiset.map_add, Multiset.prod_add]

theorem symbol_denominator_one (z : O) : sexticSymbol 1 z = 1 := by
  simp only [sexticSymbol, show (1 : Ideal O) ≠ ⊥ from one_ne_zero, if_false,
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

theorem correction_one_right (x : LocalClass) : correction x 1 = 1 := by
  simp [correction]

theorem correction_one_left (x : LocalClass) : correction 1 x = 1 := by
  rw [correction_symm, correction_one_right]

theorem prime_ideal_reciprocity (c : ArithmeticContext) (P : Ideal O)
    (hP : Prime P) (ha : Outside c.S P) (b : Ideal O)
    (hb : Outside c.S b) (hab : IsRelPrime P b) :
    sexticSymbol b (primaryGenerator P) =
      correction (elementClass (primaryGenerator P)) (elementClass (primaryGenerator b)) *
        sexticSymbol P (primaryGenerator b) := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun b : Ideal O => Outside c.S b → IsRelPrime P b →
      sexticSymbol b (primaryGenerator P) =
        correction (elementClass (primaryGenerator P)) (elementClass (primaryGenerator b)) *
          sexticSymbol P (primaryGenerator b)) b ?_ ?_ ?_ hb hab
  · intro h _
    exact (h.1 rfl).elim
  · intro b hu _ _
    have he : b = 1 := isUnit_iff_eq_one.mp hu
    subst b
    rw [primaryGenerator_one, elementClass_one, correction_one_right,
      sexticSymbol_one_of_outside c ha, symbol_denominator_one, mul_one]
  · intro b Q _ hQ ih h hPQb
    have hQout := outside_of_dvd h (dvd_mul_right Q b)
    have hbout := outside_of_dvd h (dvd_mul_left b Q)
    have hPQ := hPQb.of_dvd_right (dvd_mul_right Q b)
    have hPb := hPQb.of_dvd_right (dvd_mul_left b Q)
    rw [symbol_mul_denominator hQout.1 hbout.1,
      primary_class_mul c hQout hbout, correction_mul_right,
      primaryGenerator_mul c hQout hbout, sexticSymbol_mul_numerator c ha,
      prime_reciprocity c P Q hP hQ ha hQout hPQ, ih hbout hPb]
    ring

theorem ideal_reciprocity (c : ArithmeticContext) (a b : Ideal O)
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b) :
    sexticSymbol b (primaryGenerator a) =
      correction (elementClass (primaryGenerator a)) (elementClass (primaryGenerator b)) *
        sexticSymbol a (primaryGenerator b) := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun a : Ideal O => Outside c.S a → IsRelPrime a b →
      sexticSymbol b (primaryGenerator a) =
        correction (elementClass (primaryGenerator a)) (elementClass (primaryGenerator b)) *
          sexticSymbol a (primaryGenerator b)) a ?_ ?_ ?_ ha hab
  · intro h _
    exact (h.1 rfl).elim
  · intro a hu _ _
    have he : a = 1 := isUnit_iff_eq_one.mp hu
    subst a
    rw [primaryGenerator_one, elementClass_one, correction_one_left,
      sexticSymbol_one_of_outside c hb, symbol_denominator_one, mul_one]
  · intro a P _ hP ih h hPab
    have hPout := outside_of_dvd h (dvd_mul_right P a)
    have haout := outside_of_dvd h (dvd_mul_left a P)
    have hPb := hPab.of_dvd_left (dvd_mul_right P a)
    have hab' := hPab.of_dvd_left (dvd_mul_left a P)
    rw [primary_class_mul c hPout haout, correction_mul_left,
      primaryGenerator_mul c hPout haout, sexticSymbol_mul_numerator c hb,
      symbol_mul_denominator hPout.1 haout.1,
      prime_ideal_reciprocity c P hP hPout b hb hPb, ih haout hab']
    ring

end Sextic

/-- The exact frozen statement, with no unproved arithmetic premises. -/
theorem sexticSquareClassReciprocity : SexticSquareClassReciprocityStatement := by
  intro c a b ha hb hab x y hx hy
  simpa only [Sextic.elementClass_of_hasLocalClass hx, Sextic.elementClass_of_hasLocalClass hy]
    using Sextic.ideal_reciprocity c a b ha hb hab

end QRHShort.ArithmeticProof.Ray

#print axioms QRHShort.ArithmeticProof.Ray.sexticSquareClassReciprocity

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let target := `QRHShort.ArithmeticProof.Ray.sexticSquareClassReciprocity
  for ax in (← collectAxioms target) do
    unless allowed.contains ax do
      throwError "Sextic reciprocity: forbidden axiom {ax} in {target}"
  logInfo "SEXTIC_RECIPROCITY_AUDIT exact_frozen_target=true forbidden=0"
