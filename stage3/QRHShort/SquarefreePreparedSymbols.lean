import QRHShort.QuotientSixthRoot
import QRHShort.SquarefreeSieveRows
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-! The numerator factor and its norm in a prepared row. The denominator
only needs to avoid 6; no arithmetic context or reciprocity is assumed. -/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.SquarefreeAssembly

namespace PreparedSymbolAux

theorem rootSix_pow_mod (m : ℕ) : rootSix ^ (m % 6) = rootSix ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 6, pow_add, pow_mul, rootSix_pow_six,
    one_pow, mul_one]

theorem eq_of_test {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a : O} {j : ℕ} (hj : j < 6)
    (ht : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) =
      Ideal.Quotient.mk P (rootSix ^ j)) :
    sexticAtPrime P a = embedding (rootSix ^ j) := by
  unfold sexticAtPrime
  rw [Finset.sum_eq_single j]
  · exact if_pos ht
  · intro i hi hij
    apply if_neg
    intro hiTest
    apply hij
    apply hζ.pow_inj (Finset.mem_range.mp hi) hj
    simpa only [map_pow] using hiTest.symm.trans ht
  · exact fun h => (h (Finset.mem_range.mpr hj)).elim

theorem sixth_power_test {F : Type*} [Field F] [Fintype F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (a : F) :
    (a ^ (6 : ℕ)) ^ ((Fintype.card F - 1) / 6) = if a = 0 then 0 else 1 := by
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  have hdvd : 6 ∣ Fintype.card F - 1 :=
    (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero (by decide)))
  have hpos : 0 < (Fintype.card F - 1) / 6 :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by decide)
  by_cases ha : a = 0
  · simp [ha, Nat.ne_of_gt hpos]
  · rw [if_neg ha, ← pow_mul, Nat.mul_div_cancel' hdvd]
    exact FiniteField.pow_card_sub_one_eq_one a ha

theorem zero_of_mem {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a : O} (ha : a ∈ P) : sexticAtPrime P a = 0 := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have ht6 := sixth_power_test hζ (Ideal.Quotient.mk P a)
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr ha)] at ht6
  have ht : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 6)
    simpa only [← pow_mul, Nat.mul_comm, hcard] using ht6
  unfold sexticAtPrime
  apply Finset.sum_eq_zero
  intro j _
  apply if_neg
  rw [ht, map_pow]
  exact (pow_ne_zero j (hζ.ne_zero (by decide))).symm

theorem index {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a : O} (ha : a ∉ P) :
    ∃ j < 6, Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) =
      Ideal.Quotient.mk P (rootSix ^ j) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have ht6 := sixth_power_test hζ (Ideal.Quotient.mk P a)
  rw [if_neg (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))] at ht6
  have ht : (Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6)) ^ 6 = 1 := by
    simpa only [← pow_mul, Nat.mul_comm, hcard] using ht6
  obtain ⟨j, hj, heq⟩ := hζ.eq_pow_of_pow_eq_one ht
  exact ⟨j, hj, by simpa only [map_pow] using heq.symm⟩

theorem mul {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a b : O) :
    sexticAtPrime P (a * b) = sexticAtPrime P a * sexticAtPrime P b := by
  by_cases ha : a ∈ P
  · rw [zero_of_mem hP hζ (P.mul_mem_right b ha), zero_of_mem hP hζ ha, zero_mul]
  by_cases hb : b ∈ P
  · rw [zero_of_mem hP hζ (P.mul_mem_left a hb), zero_of_mem hP hζ hb, mul_zero]
  obtain ⟨i, hi, hit⟩ := index hP hζ ha
  obtain ⟨j, hj, hjt⟩ := index hP hζ hb
  have hij : Ideal.Quotient.mk P (a * b) ^ ((P.absNorm - 1) / 6) =
      Ideal.Quotient.mk P (rootSix ^ ((i + j) % 6)) := by
    rw [rootSix_pow_mod, map_mul, mul_pow, hit, hjt, ← map_mul, ← pow_add]
  rw [eq_of_test hζ (Nat.mod_lt _ (by decide)) hij,
    eq_of_test hζ hi hit, eq_of_test hζ hj hjt,
    rootSix_pow_mod, pow_add, embedding_mul]

theorem norm_le_one {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a : O) :
    ‖sexticAtPrime P a‖ ≤ 1 := by
  by_cases ha : a ∈ P
  · simp [zero_of_mem hP hζ ha]
  · obtain ⟨j, hj, ht⟩ := index hP hζ ha
    rw [eq_of_test hζ hj ht, norm_embedding_rootSix_pow]

theorem factor_primitive {k P : Ideal O} (hcop : IsRelPrime k (principal 6))
    (hP : P ∈ normalizedFactors k) :
    IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6 := by
  have hprime := prime_of_normalized_factor P hP
  have hnot : ¬ P ∣ principal 6 :=
    fun h => hprime.not_unit (hcop (dvd_of_mem_normalizedFactors hP) h)
  have htwo : principal 2 ∣ principal 6 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr ⟨3, by ring⟩
  have hthree : principal 3 ∣ principal 6 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr ⟨2, by ring⟩
  exact quotient_rootSix_isPrimitiveRoot P (fun h => hnot (h.trans htwo))
    (fun h => hnot (h.trans hthree))

end PreparedSymbolAux

theorem prepared_sexticSymbol_mul {k : Ideal O} (hk : k ≠ ⊥)
    (hcop : IsRelPrime k (principal 6)) (a b : O) :
    sexticSymbol k (a * b) = sexticSymbol k a * sexticSymbol k b := by
  simp only [sexticSymbol, if_neg hk]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  exact PreparedSymbolAux.mul (prime_of_normalized_factor P hP)
    (PreparedSymbolAux.factor_primitive hcop hP) a b

theorem prepared_sexticSymbol_norm_le_one {k : Ideal O} (hk : k ≠ ⊥)
    (hcop : IsRelPrime k (principal 6)) (a : O) : ‖sexticSymbol k a‖ ≤ 1 := by
  have hprod (s : Multiset (Ideal O))
      (hs : ∀ P ∈ s, ‖sexticAtPrime P a‖ ≤ 1) :
      ‖(s.map (fun P => sexticAtPrime P a)).prod‖ ≤ 1 := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons P s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      have hP := hs P (Multiset.mem_cons_self P s)
      have ht := ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ))
      exact (mul_le_mul hP ht (norm_nonneg _) zero_le_one).trans (by norm_num)
  rw [sexticSymbol, if_neg hk]
  exact hprod _ (fun P hP => PreparedSymbolAux.norm_le_one
    (prime_of_normalized_factor P hP) (PreparedSymbolAux.factor_primitive hcop hP) a)

theorem prepared_row_cubic_symbol_factor {S : Finset (Ideal O)} {H : ℝ}
    {k : Ideal O} (hk : k ∈ sieveRows S H) (n b : Ideal O) :
    sexticSymbol k (primaryGenerator n * primaryGenerator b) ^ (3 : ℕ) =
      sexticSymbol k (primaryGenerator b) ^ (3 : ℕ) *
        sexticSymbol k (primaryGenerator n) ^ (3 : ℕ) ∧
      ‖sexticSymbol k (primaryGenerator b) ^ (3 : ℕ)‖ ≤ 1 := by
  obtain ⟨hout, hcop, _⟩ := (mem_sieveRows S H k).mp hk
  refine ⟨?_, ?_⟩
  · rw [prepared_sexticSymbol_mul hout.1.1 hcop, mul_pow, mul_comm]
  · rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _)
      (prepared_sexticSymbol_norm_le_one hout.1.1 hcop _) 3).trans (by norm_num)

end QRHShort.SquarefreeAssembly
