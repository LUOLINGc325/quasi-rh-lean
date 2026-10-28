import QRHShort.QuadraticPrimeRayLocal

/-!
Prime-pair reciprocity for the frozen concrete quadratic family. The actual
quadratic residue characters are identified with the cubic powers in the
upstream two-prime Gauss-sum formula. All avoidance and coprimality hypotheses
are derived from the original statement.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort
open OAI
open QuadraticPrimeLocal

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

lemma quadraticResidueChar_onElement_congr (I J : Ideal O) [I.IsMaximal] [J.IsMaximal]
    (h : I = J) (x : O) :
    quadraticResidueChar I (Ideal.Quotient.mk I x) =
      quadraticResidueChar J (Ideal.Quotient.mk J x) := by
  subst J
  rfl

theorem quadraticPrime_not_lambda (P : Ideal O) (hP : Prime P)
    (hPm : FamilyIdeal (principal 6) P) : OAI.ActualEisensteinCubic.lambda ∉ P := by
  intro hl
  change omega - 1 ∈ P at hl
  obtain ⟨c, hc⟩ := omega_sub_one_dvd_three
  have h3 : (3 : O) ∈ P := by
    rw [hc]
    exact P.mul_mem_right c hl
  exact hP.not_unit (hPm.2 dvd_rfl
    ((Ideal.dvd_span_singleton.mpr h3).trans quadratic_three_dvd_six))

theorem quadraticPrime_char_ne_two (P : Ideal O) (hP : Prime P)
    (hPm : FamilyIdeal (principal 6) P) : ringChar (O ⧸ P) ≠ 2 := by
  intro hc
  have hz : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
  have h2 : (2 : O) ∈ P :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using hz)
  exact hP.not_unit (hPm.2 dvd_rfl
    ((Ideal.dvd_span_singleton.mpr h2).trans quadratic_two_dvd_six))

theorem quadraticPrime_defect_eq_rayPair (P Q : Ideal O)
    (hP : Prime P) (hQ : Prime Q)
    (hPm : FamilyIdeal (principal 6) P) (hQm : FamilyIdeal (principal 6) Q)
    (hPQ : IsRelPrime P Q) :
    quadraticReciprocityDefect P Q =
      MixedCrossSeparation.quadraticRayPair
        (OAI.ActualEisensteinCoordinates.residue (primaryGenerator P))
        (OAI.ActualEisensteinCoordinates.residue (primaryGenerator Q)) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Q.IsMaximal := (Ideal.isPrime_of_prime hQ).isMaximal hQ.ne_zero
  have hp : principal (primaryGenerator P) = P :=
    (quadratic_primaryGenerator_spec P
      (hPm.2.of_dvd_right quadratic_three_dvd_six)).1
  have hq : principal (primaryGenerator Q) = Q :=
    (quadratic_primaryGenerator_spec Q
      (hQm.2.of_dvd_right quadratic_three_dvd_six)).1
  have hp0 : primaryGenerator P ≠ 0 := by
    intro h
    apply hPm.1
    rw [← hp, h]
    exact Ideal.span_singleton_zero
  have hq0 : primaryGenerator Q ≠ 0 := by
    intro h
    apply hQm.1
    rw [← hq, h]
    exact Ideal.span_singleton_zero
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
      rw [hp]
      infer_instance
    · change (principal (primaryGenerator Q)).IsMaximal
      rw [hq]
      infer_instance
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => (Ideal.span {p i} : Ideal O))) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · change IsCoprime (principal (primaryGenerator P)) (principal (primaryGenerator Q))
      rw [hp, hq]
      exact quadratic_isCoprime_of_isRelPrime hPQ
    · change IsCoprime (principal (primaryGenerator Q)) (principal (primaryGenerator P))
      rw [hq, hp]
      exact quadratic_isCoprime_of_isRelPrime hPQ.symm
    · exact (hij rfl).elim
  have hg : ∀ i, OAI.ActualEisensteinCubic.lambda ∉ Ideal.span {p i} := by
    intro i
    cases i
    · change OAI.ActualEisensteinCubic.lambda ∉ principal (primaryGenerator P)
      rw [hp]
      exact quadraticPrime_not_lambda P hP hPm
    · change OAI.ActualEisensteinCubic.lambda ∉ principal (primaryGenerator Q)
      rw [hq]
      exact quadraticPrime_not_lambda Q hQ hQm
  have hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2 := by
    intro i
    cases i
    · change ringChar (O ⧸ principal (primaryGenerator P)) ≠ 2
      rw [hp]
      exact quadraticPrime_char_ne_two P hP hPm
    · change ringChar (O ⧸ principal (primaryGenerator Q)) ≠ 2
      rw [hq]
      exact quadraticPrime_char_ne_two Q hQ hQm
  have heval (i j : Bool) : MixedCrossSeparation.crossSymbol p hg i j ^ 3 =
      quadraticResidueChar (Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) (p j)) := by
    rw [MixedCrossSeparation.crossSymbol,
      ← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
      OAI.ActualEisensteinCubic.canonicalSextic_pow_three_quadratic]
    rfl
  have hcross := MixedCrossSeparation.quadraticCrossPhase_eq_rayPair p hpall hcop hg hc
    ({false} : Finset Bool) ({true} : Finset Bool) (by decide)
  simp only [MixedCrossSeparation.quadraticCrossPhase, Finset.prod_singleton] at hcross
  rw [heval, heval] at hcross
  rw [quadraticReciprocityDefect_prime_eq P Q hP hQ hPm hQm]
  have hpval := @quadraticResidueChar_onElement_congr (Ideal.span {p false}) P
    (hmax false) inferInstance hp (p true)
  have hqval := @quadraticResidueChar_onElement_congr (Ideal.span {p true}) Q
    (hmax true) inferInstance hq (p false)
  rw [hpval, hqval] at hcross
  simpa only [p] using hcross

/-- The original frozen statement, with no remaining arithmetic premises. -/
theorem quadraticPrimeRayReciprocity : QuadraticPrimeRayReciprocityStatement := by
  refine ⟨bilinearCorrection, ?_⟩
  intro P Q hP hQ hPm hQm hPQ
  rw [bilinearCorrection_class P Q hPm hQm]
  exact quadraticPrime_defect_eq_rayPair P Q hP hQ hPm hQm hPQ

end QRHShort

#print axioms QRHShort.quadraticPrimeRayReciprocity
