import QRHShort.ArithmeticReduction
import QRHShort.SquarefreeNumeratorProducts

/-! Bounds for the concrete multipliers in removal of exclusions. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.RemoveExclusionsProof
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites

theorem norm_mobius_eq_one {d : Ideal O} (hd : Squarefree d) :
    ‖(mobius d : ℂ)‖ = 1 := by
  simp only [mobius, hd.moebius_eq, Int.cast_pow, Int.cast_neg, Int.cast_one,
    norm_pow, norm_neg, norm_one, one_pow]

theorem norm_sexticAtPrime_le_one {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a : O) :
    ‖sexticAtPrime P a‖ ≤ 1 := by
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hP hζ ha, norm_zero]
    exact zero_le_one
  · obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hP hζ ha
    rw [sexticAtPrime_eq_of_test hζ hj ht]
    have hz : embedding (rootSix ^ j) ^ 6 = 1 := by
      rw [← embedding_pow, ← pow_mul, Nat.mul_comm, pow_mul,
        rootSix_pow_six, one_pow, embedding_one]
    exact (Complex.norm_eq_one_of_pow_eq_one hz (by decide)).le

theorem norm_multiset_prod_le_one (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ 1) :
    ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := hs a (Multiset.mem_cons_self a s)
    have hprod := ih (fun z hz => hs z (Multiset.mem_cons_of_mem hz))
    calc
      ‖a‖ * ‖s.prod‖ ≤ 1 * 1 := mul_le_mul ha hprod (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem norm_sexticSymbol_le_one (c : ArithmeticContext) {d : Ideal O}
    (hd : Outside c.S d) (a : O) : ‖sexticSymbol d a‖ ≤ 1 := by
  rw [sexticSymbol, if_neg hd.1]
  apply norm_multiset_prod_le_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  exact norm_sexticAtPrime_le_one (prime_of_normalized_factor P hP)
    (outside_quotient_rootSix_isPrimitiveRoot c (prime_of_normalized_factor P hP)
      (outside_of_mem_normalizedFactors hd hP)) a

theorem norm_hecke_onElement_le_one (χ : HeckeCharacter) (a : O) :
    ‖χ.onElement a‖ ≤ 1 := by
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  change ‖χ.residue (Ideal.Quotient.mk χ.modulus a)‖ ≤ 1
  by_cases h : IsUnit (Ideal.Quotient.mk χ.modulus a)
  · have hunit : ‖χ.residue (h.unit : O ⧸ χ.modulus)‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _)
        (Nat.card_pos (α := (O ⧸ χ.modulus)ˣ)).ne').mp ?_
      rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
        Units.val_one, map_one, norm_one]
    exact hunit.le
  · rw [χ.residue.map_nonunit h, norm_zero]
    exact zero_le_one

theorem norm_gauss_two_eq_one (c : ArithmeticContext) (hc : ArithmeticRelations c)
    {d : Ideal O} (hd : SquarefreeOutside c.S d) : ‖gauss 2 d‖ = 1 := by
  obtain ⟨G, R, _hG, _hR, _hsym, _hl, _hr, _hcoc, _hrec, hgauss, _hmul, _hshift⟩ := hc
  have h := congrArg norm (hgauss d hd).1
  rw [norm_pow, norm_mul, norm_mobius_eq_one hd.2,
    ArithmeticProof.alpha_norm c hd.1, one_mul] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp h

theorem norm_coefficient_le_one (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) {d : Ideal O} (hd : SquarefreeOutside c.S d) :
    ‖coefficient ξ.val d‖ ≤ 1 := by
  simp only [coefficient, norm_mul, norm_star, ArithmeticProof.alpha_norm c hd.1,
    norm_gauss_two_eq_one c hc hd, one_mul, rayValue]
  exact norm_hecke_onElement_le_one ξ.val (primaryGenerator d)

theorem norm_removal_product_le_one (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (d : Ideal O) (k : O) (f : Ideal O)
    (hd : SquarefreeOutside c.S d) :
    ‖(mobius d : ℂ) * coefficient ξ.val d * sexticSymbol d k *
      sexticSymbol d (primaryGenerator f) ^ (4 : ℕ)‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_mobius_eq_one hd.2, one_mul]
  have hfirst : ‖coefficient ξ.val d‖ * ‖sexticSymbol d k‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (norm_coefficient_le_one c hc ξ hd)
      (norm_sexticSymbol_le_one c hd.1 k) (norm_nonneg _) zero_le_one
  have hlast : ‖sexticSymbol d (primaryGenerator f)‖ ^ 4 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_sexticSymbol_le_one c hd.1 (primaryGenerator f)) 4
  simpa only [one_mul] using mul_le_mul hfirst hlast (pow_nonneg (norm_nonneg _) 4)
    zero_le_one

end QRHShort.RemoveExclusionsProof
