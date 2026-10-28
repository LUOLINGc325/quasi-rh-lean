import QRHShort.FirstTransferResidueCharacter
import QRHShort.SquarefreeNumeratorPowers
import QRHShort.QuotientSixthRoot

/-! Literal zero filters and sixth-root algebra for the frozen sextic symbol.
The quotient criterion includes the unit ideal and zero numerators. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort

/-- A residue is a unit exactly when its principal ideal is relatively prime
to the modulus. This also holds for the zero ideal and the unit ideal. -/
theorem first_transfer_isUnit_mk_iff_isRelPrime (n : Ideal O) (z : O) :
    IsUnit (Ideal.Quotient.mk n z) ↔ IsRelPrime (principal z) n := by
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hz
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hmem : z * t - 1 ∈ n := Ideal.Quotient.eq.mp (by
      simpa only [map_mul, map_one] using hv)
    have hzt : z * t ∈ principal z :=
      (principal z).mul_mem_right t (Ideal.mem_span_singleton_self z)
    have hone : (1 : O) ∈ principal z ⊔ n := by
      have h := (principal z ⊔ n).sub_mem
        ((show principal z ≤ principal z ⊔ n from le_sup_left) hzt)
        ((show n ≤ principal z ⊔ n from le_sup_right) hmem)
      convert h using 1 <;> ring
    exact (Ideal.isCoprime_iff_sup_eq.mpr ((Ideal.eq_top_iff_one _).mpr hone)).isRelPrime
  · intro hrel
    have hcop : IsCoprime (principal z) n := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      exact Ideal.isUnit_iff.mp (hrel
        (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hx
    have h := congrArg (Ideal.Quotient.mk n) hxy
    simp only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] at h
    exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk n t, h⟩

theorem first_transfer_sexticSymbol_zero_of_not_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : ¬ IsRelPrime (principal z) n) : sexticSymbol n z = 0 := by
  apply firstTransferSexticSymbol_eq_zero_of_nonunit c hn z
  exact fun h => hz ((first_transfer_isUnit_mk_iff_isRelPrime n z).mp h)

theorem first_transfer_sexticAtPrime_pow_six_of_not_mem (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) (z : O) (hz : z ∉ P) :
    sexticAtPrime P z ^ (6 : ℕ) = 1 := by
  have hζ := SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
    c hP hout
  obtain ⟨j, hj, htest⟩ := SquarefreeReflection.sexticAtPrime_index hP hζ hz
  rw [SquarefreeReflection.RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj htest,
    embedding_pow, ← pow_mul, Nat.mul_comm j 6, pow_mul,
    ← embedding_pow, rootSix_pow_six, embedding_one, one_pow]

theorem first_transfer_sexticSymbol_pow_six_of_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : IsRelPrime (principal z) n) : sexticSymbol n z ^ (6 : ℕ) = 1 := by
  simp only [sexticSymbol, ite_eq_right hn.1]
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro w hw
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hw
  have hprime := prime_of_normalized_factor P hP
  have hzP : z ∉ P := by
    intro hzP
    exact hprime.not_isUnit (hz (Ideal.dvd_span_singleton.mpr hzP)
      (dvd_of_mem_normalizedFactors hP))
  exact first_transfer_sexticAtPrime_pow_six_of_not_mem c hprime
    (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors hn hP) z hzP

theorem first_transfer_sexticSymbol_norm_of_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : IsRelPrime (principal z) n) : ‖sexticSymbol n z‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one
    (first_transfer_sexticSymbol_pow_six_of_isRelPrime c hn z hz) (by decide)

/-- The literal product with its complex conjugate is the exact coprimality
filter, including the modulus-one quotient. -/
theorem first_transfer_sexticSymbol_mul_star (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O) :
    sexticSymbol n z * star (sexticSymbol n z) =
      if IsRelPrime (principal z) n then 1 else 0 := by
  by_cases hz : IsRelPrime (principal z) n
  · rw [ite_eq_left hz]
    simpa only [starRingEnd_apply, first_transfer_sexticSymbol_norm_of_isRelPrime c hn z hz,
      one_pow, Complex.ofReal_one] using Complex.mul_conj' (sexticSymbol n z)
  · rw [ite_eq_right hz, first_transfer_sexticSymbol_zero_of_not_isRelPrime c hn z hz,
      star_zero, zero_mul]

theorem first_transfer_sexticSymbol_pow_four_eq_star_pow_two (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O) :
    sexticSymbol n z ^ (4 : ℕ) = star (sexticSymbol n z ^ (2 : ℕ)) := by
  by_cases hz : IsRelPrime (principal z) n
  · have h6 := first_transfer_sexticSymbol_pow_six_of_isRelPrime c hn z hz
    have hnorm := first_transfer_sexticSymbol_norm_of_isRelPrime c hn z hz
    have hne : sexticSymbol n z ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide)] at h6
      exact zero_ne_one h6
    have hstar : star (sexticSymbol n z ^ (2 : ℕ)) * sexticSymbol n z ^ (2 : ℕ) = 1 := by
      simpa only [starRingEnd_apply, norm_pow, hnorm, one_pow, Complex.ofReal_one] using
        Complex.conj_mul' (sexticSymbol n z ^ (2 : ℕ))
    apply mul_right_cancel₀ (pow_ne_zero 2 hne)
    rw [hstar]
    calc
      sexticSymbol n z ^ 4 * sexticSymbol n z ^ 2 = sexticSymbol n z ^ 6 := by ring
      _ = 1 := h6
  · rw [first_transfer_sexticSymbol_zero_of_not_isRelPrime c hn z hz]
    simp only [zero_pow (by decide : (4 : ℕ) ≠ 0),
      zero_pow (by decide : (2 : ℕ) ≠ 0), star_zero]

theorem first_transfer_sexticSymbol_fourth_numerator (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O) :
    sexticSymbol n (z ^ (4 : ℕ)) = star (sexticSymbol n (z ^ (2 : ℕ))) := by
  simp only [SquarefreeReflection.sexticSymbol_pow_numerator c hn]
  exact first_transfer_sexticSymbol_pow_four_eq_star_pow_two c hn z

/-- The fourth-power factor absorbs into the conjugated numerator without
any coprimality hypothesis; both sides have the same zero extension. -/
theorem first_transfer_sexticSymbol_fourth_mul_star (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (f h : O) :
    sexticSymbol n f ^ (4 : ℕ) * star (sexticSymbol n h) =
      star (sexticSymbol n (h * f ^ (2 : ℕ))) := by
  rw [first_transfer_sexticSymbol_pow_four_eq_star_pow_two c hn f,
    ← SquarefreeReflection.sexticSymbol_pow_numerator c hn f 2,
    ← star_mul,
    ← SquarefreeReflection.sexticSymbol_mul_numerator c hn h (f ^ 2)]

end QRHShort

#print axioms QRHShort.first_transfer_isUnit_mk_iff_isRelPrime
#print axioms QRHShort.first_transfer_sexticSymbol_mul_star
#print axioms QRHShort.first_transfer_sexticSymbol_pow_four_eq_star_pow_two
#print axioms QRHShort.first_transfer_sexticSymbol_fourth_mul_star
