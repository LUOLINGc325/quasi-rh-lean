import QRHShort.SquarefreeNumeratorProducts

/-! The frozen sextic symbol as a literal multiplicative character of its residue ring.
The construction also covers the unit ideal, whose quotient ring is trivial. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem firstTransferResidueLift_spec (n : Ideal O) (x : O ⧸ n) :
    Ideal.Quotient.mk n (residueLift n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

/-- Every local factor in the frozen symbol depends only on the residue modulo
the full denominator, including when that denominator has repeated factors. -/
theorem firstTransferSexticSymbol_congr {n : Ideal O} {a b : O}
    (hab : Ideal.Quotient.mk n a = Ideal.Quotient.mk n b) :
    sexticSymbol n a = sexticSymbol n b := by
  by_cases hn : n = ⊥
  · simp only [sexticSymbol, ite_eq_left hn]
  simp only [sexticSymbol, ite_eq_right hn]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hnP : n ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
  have habP : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b :=
    Ideal.Quotient.eq.mpr (hnP (Ideal.Quotient.eq.mp hab))
  simp only [sexticAtPrime, habP]

def firstTransferResidueValue (n : Ideal O) (x : O ⧸ n) : ℂ :=
  sexticSymbol n (residueLift n x)

@[simp] theorem firstTransferResidueValue_apply_mk (n : Ideal O) (a : O) :
    firstTransferResidueValue n (Ideal.Quotient.mk n a) = sexticSymbol n a :=
  firstTransferSexticSymbol_congr (firstTransferResidueLift_spec n _)

/-- A nonunit in the residue ring lies in a prime factor of the denominator,
so one of the actual local sextic factors is zero. -/
theorem firstTransferSexticSymbol_eq_zero_of_nonunit (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (a : O)
    (ha : ¬ IsUnit (Ideal.Quotient.mk n a)) : sexticSymbol n a = 0 := by
  have hproper : principal a ⊔ n ≠ ⊤ := by
    intro htop
    have hone : (1 : O) ∈ principal a ⊔ n := htop ▸ Submodule.mem_top
    obtain ⟨u, b, hb, heq⟩ := Ideal.mem_span_singleton_sup.mp hone
    apply ha
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk n u, ?_⟩
    have heq' := congrArg (Ideal.Quotient.mk n) heq
    simpa only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero] using heq'
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal (principal a ⊔ n) hproper
  have hnP : n ≤ P := le_trans le_sup_right hle
  have hPzero : P ≠ ⊥ := by
    intro hP
    apply hn.1
    exact le_antisymm (hP ▸ hnP) bot_le
  have hP : Prime P := Ideal.prime_of_isPrime hPzero hPmax.isPrime
  have hPmem : P ∈ normalizedFactors n :=
    (mem_normalizedFactors_iff hn.1).mpr ⟨hP, Ideal.dvd_iff_le.mpr hnP⟩
  have haP : a ∈ P := (le_trans le_sup_left hle) (Ideal.mem_span_singleton_self a)
  simp only [sexticSymbol, ite_eq_right hn.1]
  apply Multiset.prod_eq_zero
  apply Multiset.mem_map.mpr
  refine ⟨P, hPmem, ?_⟩
  exact SquarefreeReflection.sexticAtPrime_zero_of_mem hP
    (SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
      c hP (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors
        hn hPmem)) haP

/-- The literal sextic character of the actual quotient ring, without a
nontriviality assumption on that ring. -/
def firstTransferResidueCharacter (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : MulChar (O ⧸ n) ℂ where
  toFun := firstTransferResidueValue n
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk n), firstTransferResidueValue_apply_mk]
    exact SquarefreeReflection.sexticSymbol_one_of_outside c hn
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, firstTransferResidueValue_apply_mk,
      firstTransferResidueValue_apply_mk, firstTransferResidueValue_apply_mk]
    exact SquarefreeReflection.sexticSymbol_mul_numerator c hn a b
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [firstTransferResidueValue_apply_mk]
    exact firstTransferSexticSymbol_eq_zero_of_nonunit c hn a hx

@[simp] theorem firstTransferResidueCharacter_apply (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O ⧸ n) :
    firstTransferResidueCharacter c hn x = sexticSymbol n (residueLift n x) := rfl

@[simp] theorem firstTransferResidueCharacter_apply_mk (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (a : O) :
    firstTransferResidueCharacter c hn (Ideal.Quotient.mk n a) = sexticSymbol n a :=
  firstTransferResidueValue_apply_mk n a

end QRHShort

#print axioms QRHShort.firstTransferSexticSymbol_congr
#print axioms QRHShort.firstTransferSexticSymbol_eq_zero_of_nonunit
#print axioms QRHShort.firstTransferResidueCharacter
#print axioms QRHShort.firstTransferResidueCharacter_apply_mk
