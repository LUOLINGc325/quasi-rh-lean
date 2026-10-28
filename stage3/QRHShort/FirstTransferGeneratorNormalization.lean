import QRHShort.FirstTransferResidueCharacter
import QRHShort.AnalyticObjects

/-! Generator normalization for the actual first-transfer Gauss sums.
Only arithmetic definitions and the already verified local primary-generator
construction are imported. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort
open SquarefreeReflection.RayValuePrerequisites

@[simp] theorem first_transfer_outside_one (c : ArithmeticContext) : Outside c.S 1 := by
  refine ⟨by simp, ?_⟩
  intro p hp
  exact (c.prime_S p hp).not_dvd_one

theorem first_transfer_outside_mul_iff (c : ArithmeticContext) (a b : Ideal O) :
    Outside c.S (a * b) ↔ Outside c.S a ∧ Outside c.S b := by
  constructor
  · intro h
    constructor
    · refine ⟨?_, fun p hp hpa => h.2 p hp (dvd_mul_of_dvd_left hpa b)⟩
      intro ha
      exact h.1 (by rw [ha, Ideal.bot_mul])
    · refine ⟨?_, fun p hp hpb => h.2 p hp (dvd_mul_of_dvd_right hpb a)⟩
      intro hb
      exact h.1 (by rw [hb, Ideal.mul_bot])
  · rintro ⟨ha, hb⟩
    refine ⟨fun h => (Ideal.mul_eq_bot.mp h).elim ha.1 hb.1, ?_⟩
    intro p hp hdiv
    exact ((c.prime_S p hp).dvd_mul.mp hdiv).elim (ha.2 p hp) (hb.2 p hp)

theorem first_transfer_outside_of_dvd (c : ArithmeticContext) {a b : Ideal O}
    (hb : Outside c.S b) (hab : a ∣ b) : Outside c.S a := by
  refine ⟨?_, fun p hp hpa => hb.2 p hp (hpa.trans hab)⟩
  intro ha
  apply hb.1
  exact bot_unique (ha ▸ Ideal.dvd_iff_le.mp hab)

theorem first_transfer_primaryGenerator_spec_and_primary_outside (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) :
    principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) :=
  primaryGenerator_spec_outside c ha

theorem first_transfer_isPrimary_mul {a b : O} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  apply (isPrimary_iff_three_dvd _).mpr
  have h := dvd_add (dvd_mul_of_dvd_left ((isPrimary_iff_three_dvd a).mp ha) b)
    ((isPrimary_iff_three_dvd b).mp hb)
  convert h using 1 <;> ring

/-- The frozen primary condition removes every unit ambiguity. -/
theorem first_transfer_isPrimary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) :
    u = 1 := by
  have hthree := (isPrimary_iff_three_dvd (u : O)).mp hu
  have hlambda : (omega - 1) ^ (2 : ℕ) ∣ (3 : O) := by
    refine ⟨-omega ^ (2 : ℕ), ?_⟩
    rw [omega_sub_one_sq]
    calc
      (3 : O) = 3 * omega ^ (3 : ℕ) := by rw [omega_cube, mul_one]
      _ = -3 * omega * -omega ^ (2 : ℕ) := by ring
  have hcong : ∃ n : ℤ, (omega - 1) ^ (2 : ℕ) ∣ ((u : O) - n) :=
    ⟨1, by simpa only [Int.cast_one] using hlambda.trans hthree⟩
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u hcong with h | h
  · exact h
  · exfalso
    have hneg : omega - 1 ∣ (-1 : O) - 1 := by
      simpa only [h, Units.val_neg, Units.val_one] using
        omega_sub_one_dvd_three.trans hthree
    apply omega_sub_one_prime.not_dvd_one
    convert dvd_add omega_sub_one_dvd_three hneg using 1 <;> ring

theorem first_transfer_primary_eq_of_principal_eq {a b : O}
    (ha : IsPrimary a) (hb : IsPrimary b) (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [first_transfer_isPrimary_unit_eq_one u hup, Units.val_one, mul_one] using hu

@[simp] theorem first_transfer_primaryGenerator_one : primaryGenerator 1 = 1 := by
  have h : ∃ z : O, principal z = 1 ∧ IsPrimary z :=
    ⟨1, by simp [principal], by simp [IsPrimary]⟩
  have hs : principal (primaryGenerator 1) = 1 ∧ IsPrimary (primaryGenerator 1) := by
    simpa only [primaryGenerator, dite_eq_left h] using Classical.choose_spec h
  exact first_transfer_primary_eq_of_principal_eq hs.2 (by simp [IsPrimary])
    (hs.1.trans (by simp [principal]))

theorem first_transfer_primaryGenerator_mul_outside (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) :
    primaryGenerator (a * b) = primaryGenerator a * primaryGenerator b := by
  have ha' := first_transfer_primaryGenerator_spec_and_primary_outside c ha
  have hb' := first_transfer_primaryGenerator_spec_and_primary_outside c hb
  have hab' := first_transfer_primaryGenerator_spec_and_primary_outside c
    ((first_transfer_outside_mul_iff c a b).mpr ⟨ha, hb⟩)
  apply first_transfer_primary_eq_of_principal_eq hab'.2
    (first_transfer_isPrimary_mul ha'.2 hb'.2)
  rw [hab'.1]
  change a * b = Ideal.span {primaryGenerator a * primaryGenerator b}
  rw [← Ideal.span_singleton_mul_span_singleton]
  change a * b = principal (primaryGenerator a) * principal (primaryGenerator b)
  rw [ha'.1, hb'.1]

theorem first_transfer_prime_isRelPrime_three (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    IsRelPrime P (principal 3) := by
  apply hP.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hthree
  exact hout.2 P (c.above_three P hP hthree) (dvd_refl P)

theorem first_transfer_chosenGenerator_eq_prod (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) :
    chosenGenerator n = ((normalizedFactors n).map primaryGenerator).prod := by
  rw [chosenGenerator, ite_eq_right hn.1]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  exact ite_eq_left (first_transfer_prime_isRelPrime_three c
    (prime_of_normalized_factor P hP) (outside_of_mem_normalizedFactors hn hP))

theorem first_transfer_isPrimary_multiset_prod (s : Multiset O)
    (hs : ∀ a ∈ s, IsPrimary a) : IsPrimary s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp [IsPrimary]
  | @cons a s ih =>
    rw [Multiset.prod_cons]
    exact first_transfer_isPrimary_mul (hs a (by simp))
      (ih (fun b hb => hs b (by simp [hb])))

/-- The fixed product of prime generators generates the full ideal and is
primary for every denominator outside S, including the empty product. -/
theorem first_transfer_chosenGenerator_spec_outside (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) :
    principal (chosenGenerator n) = n ∧ IsPrimary (chosenGenerator n) := by
  rw [first_transfer_chosenGenerator_eq_prod c hn]
  constructor
  · rw [principal, ← Ideal.multiset_prod_span_singleton, Multiset.map_map]
    calc
      ((normalizedFactors n).map (fun P =>
          Ideal.span {primaryGenerator P})).prod = (normalizedFactors n).prod := by
        apply congrArg Multiset.prod
        simpa only [principal, Multiset.map_id'] using
          (Multiset.map_congr rfl (fun P hP =>
            (first_transfer_primaryGenerator_spec_and_primary_outside c
              (outside_of_mem_normalizedFactors hn hP)).1))
      _ = n := Ideal.prod_normalizedFactors_eq_self hn.1
  · apply first_transfer_isPrimary_multiset_prod
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    exact (first_transfer_primaryGenerator_spec_and_primary_outside c
      (outside_of_mem_normalizedFactors hn hP)).2

/-- The Poisson and frozen Gauss definitions use exactly the same generator
on the actual denominators outside S. -/
theorem first_transfer_chosenGenerator_eq_primaryGenerator (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) : chosenGenerator n = primaryGenerator n := by
  have hc := first_transfer_chosenGenerator_spec_outside c hn
  have hp := first_transfer_primaryGenerator_spec_and_primary_outside c hn
  exact first_transfer_primary_eq_of_principal_eq hc.2 hp.2 (hc.1.trans hp.1.symm)

@[simp] theorem first_transfer_sexticSymbol_unit_ideal (z : O) : sexticSymbol 1 z = 1 := by
  have h : (1 : Ideal O) ≠ ⊥ := by simp
  simp only [sexticSymbol, ite_eq_right h, normalizedFactors_one,
    Multiset.map_zero, Multiset.prod_zero]

/-- Multiplicativity in the denominator for the literal frozen symbol,
including zero denominators and repeated prime factors. -/
theorem first_transfer_sexticSymbol_mul (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, sexticSymbol]
  by_cases hb : b = ⊥
  · simp [hb, sexticSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

end QRHShort

#print axioms QRHShort.first_transfer_outside_of_dvd
#print axioms QRHShort.first_transfer_primaryGenerator_mul_outside
#print axioms QRHShort.first_transfer_chosenGenerator_spec_outside
#print axioms QRHShort.first_transfer_chosenGenerator_eq_primaryGenerator
#print axioms QRHShort.first_transfer_sexticSymbol_mul
