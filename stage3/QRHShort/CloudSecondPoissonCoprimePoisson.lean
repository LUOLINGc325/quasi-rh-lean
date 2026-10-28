import QRHShort.SecondPoissonAssembly
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import QRHShort.SmoothedSummability
import QRHShort.PrimaryGenerator
import QRHShort.SquarefreeNumeratorProducts
import QRHShort.AnalyticObjects
import QRHShort.QuotientSixthRoot
import QRHShort.SquarefreeRayDescent
import QRHShort.SquarefreePrimeSymbol
import QRHShort.PoissonStatements
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import QRHShort.SquarefreeNumeratorPowers
import QRHShort.ArithmeticStatements
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring

noncomputable section
open Classical
namespace QRHShort.CloudBatch.SecondCoprime
theorem first_transfer_primaryGenerator_spec_outside (c : ArithmeticContext)
    {f : Ideal O} (hf : Outside c.S f) : principal (primaryGenerator f) = f := by
  let z := idealGenerator f
  have hz : principal z = f := Ideal.span_singleton_generator f
  have hp : Prime (principal (omega - 1)) :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have hthree : principal (omega - 1) ∣ principal 3 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three
  have hnot : ¬ omega - 1 ∣ z := by
    intro hdiv
    apply hf.2 _ (c.above_three _ hp hthree)
    rw [← hz]
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr hdiv
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  have hex : ∃ a : O, principal a = f ∧ IsPrimary a :=
    ⟨(u : O) * z, (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz, hu⟩
  simpa only [primaryGenerator, dif_pos hex] using (Classical.choose_spec hex).1

theorem first_transfer_principal_ne_bot {y : O} (hy : y ≠ 0) : principal y ≠ ⊥ := by
  intro h
  exact hy (Ideal.span_singleton_eq_bot.mp h)

theorem first_transfer_primaryGenerator_ne_zero (c : ArithmeticContext)
    {f : Ideal O} (hf : Outside c.S f) : primaryGenerator f ≠ 0 := by
  intro h
  apply hf.1
  rw [← first_transfer_primaryGenerator_spec_outside c hf, h]
  simp [principal]


end QRHShort.CloudBatch.SecondCoprime


/-! The frozen sextic symbol as a literal multiplicative character of its residue ring.
The construction also covers the unit ideal, whose quotient ring is trivial. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch.SecondCoprime

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

end QRHShort.CloudBatch.SecondCoprime



/-! Generator normalization for the actual first-transfer Gauss sums.
Only arithmetic definitions and the already verified local primary-generator
construction are imported. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch.SecondCoprime
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

end QRHShort.CloudBatch.SecondCoprime



/-!
Local nontriviality of the literal sixth-power residue symbol. The finite-field
power map is onto the roots of unity of the prescribed order, using a generator
of the cyclic unit group. Evaluation then uses the frozen defining residue test.
No reciprocity, Gauss-sum evaluation, or primitivity premise is assumed.
-/

noncomputable section
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

/-- In a finite field containing a primitive m-th root, the usual power
test reaches every m-th root on a nonzero field element. -/
theorem first_transfer_finiteField_power_test_surjective {F : Type*}
    [Field F] [Fintype F] {m : ℕ} (hm : m ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) {w : F} (hw : w ^ m = 1) :
    ∃ a : F, a ≠ 0 ∧ a ^ ((Fintype.card F - 1) / m) = w := by
  letI : NeZero m := ⟨hm⟩
  have hMpos : 0 < Fintype.card F - 1 := by
    have hcard : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hdiv : m ∣ Fintype.card F - 1 :=
    (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero hm))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hgen : IsPrimitiveRoot (g : F) (Fintype.card F - 1) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have htest : IsPrimitiveRoot ((g : F) ^ ((Fintype.card F - 1) / m)) m :=
    hgen.pow hMpos (Nat.div_mul_cancel hdiv).symm
  obtain ⟨j, _, hj⟩ := htest.eq_pow_of_pow_eq_one hw
  refine ⟨(g : F) ^ j, pow_ne_zero j g.ne_zero, ?_⟩
  simpa only [← pow_mul, Nat.mul_comm] using hj

/-- Each of the six literal complex root values occurs at a residue unit. -/
theorem first_transfer_sexticAtPrime_surjective (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) (j : ℕ) (hj : j < 6) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      sexticAtPrime P a = embedding (rootSix ^ j) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hP hout
  have hroot : (Ideal.Quotient.mk P rootSix ^ j) ^ (6 : ℕ) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨x, hx, htest⟩ := first_transfer_finiteField_power_test_surjective
    (by decide : (6 : ℕ) ≠ 0) hζ hroot
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨a, ?_, ?_⟩
  · rw [ha]
    exact isUnit_iff_ne_zero.mpr hx
  · have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    apply SquarefreeReflection.RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj
    simpa only [hcard, ha, map_pow] using htest

theorem first_transfer_sexticAtPrime_hits_rootSix (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      sexticAtPrime P a = embedding rootSix := by
  simpa only [pow_one] using first_transfer_sexticAtPrime_surjective c hP hout 1 (by decide)

theorem first_transfer_embedding_rootSix_ne_one : embedding rootSix ≠ 1 := by
  intro h
  have hc : embedding rootSix ^ 3 = (-1 : ℂ) := by
    rw [← embedding_pow, rootSix_cube, embedding_neg, embedding_one]
  rw [h] at hc
  norm_num at hc

/-- A unit witness proves genuine nontriviality, independently of how a
multiplicative character on the residue ring is bundled. -/
theorem first_transfer_sexticAtPrime_nontrivial (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧ sexticAtPrime P a ≠ 1 := by
  obtain ⟨a, ha, hvalue⟩ := first_transfer_sexticAtPrime_hits_rootSix c hP hout
  exact ⟨a, ha, hvalue ▸ first_transfer_embedding_rootSix_ne_one⟩

end QRHShort.CloudBatch.SecondCoprime


/-!
Nontriviality and prime-modulus primitivity of the actual residue character.
Primitivity is stated as an explicit quotient-factorization property: a
character modulo an ideal J containing P that agrees on every unit modulo P
must already have J = P. Agreement is on units, as required for characters
extended by zero on nonunits.
-/

noncomputable section
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_prime_character_hits_rootSix (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      firstTransferResidueCharacter c hout (Ideal.Quotient.mk P a) = embedding rootSix := by
  obtain ⟨a, ha, hv⟩ := first_transfer_sexticAtPrime_hits_rootSix c hP hout
  refine ⟨a, ha, ?_⟩
  rw [firstTransferResidueCharacter_apply_mk, SquarefreeReflection.sexticSymbol_prime hP]
  exact hv

/-- The bundled character is genuinely nontrivial on residue units. -/
theorem first_transfer_prime_character_ne_one (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    firstTransferResidueCharacter c hout ≠ 1 := by
  intro h
  obtain ⟨a, ha, hv⟩ := first_transfer_prime_character_hits_rootSix c hP hout
  rw [h, MulChar.one_apply ha] at hv
  exact first_transfer_embedding_rootSix_ne_one hv.symm

/-- Prime-modulus primitivity, expressed without introducing a new
conductor definition or a squarefree CRT assertion. -/
theorem first_transfer_prime_character_primitive (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P)
    (J : Ideal O) (hPJ : P ≤ J) (χ : MulChar (O ⧸ J) ℂ)
    (hagrees : ∀ a : O, IsUnit (Ideal.Quotient.mk P a) →
      firstTransferResidueCharacter c hout (Ideal.Quotient.mk P a) =
        χ (Ideal.Quotient.mk J a)) : J = P := by
  have hmax : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  by_cases hJ : J = ⊤
  · subst J
    obtain ⟨a, ha, hv⟩ := first_transfer_prime_character_hits_rootSix c hP hout
    have htop : Ideal.Quotient.mk (⊤ : Ideal O) a = 1 := Subsingleton.elim _ _
    have heq := hagrees a ha
    rw [htop, map_one, hv] at heq
    exact False.elim (first_transfer_embedding_rootSix_ne_one heq)
  · exact (hmax.eq_of_le hJ hPJ).symm

end QRHShort.CloudBatch.SecondCoprime


/-!
The literal paired row character on the quotient by the product modulus.
The product quotient is identified by CRT, including when either factor is
the unit ideal and its quotient ring is trivial.
-/

noncomputable section
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_ideal_isCoprime_of_isRelPrime {a b : Ideal O}
    (hab : IsRelPrime a b) : IsCoprime a b := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp (hab
    (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

theorem first_transfer_quotient_mul_isUnit_iff (a b : Ideal O) (hab : IsCoprime a b)
    (x : O ⧸ (a * b)) :
    IsUnit x ↔ IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x) ∧
      IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  rw [← isUnit_map_iff e x, Prod.isUnit_iff]
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

/-- A prescribed unit in one factor and 1 in the other lift to a unit of the
actual product quotient. No nontriviality of either quotient is required. -/
theorem first_transfer_crt_unit_lift (a b : Ideal O) (hab : IsCoprime a b)
    (u : O) (hu : IsUnit (Ideal.Quotient.mk a u)) :
    ∃ x : O, Ideal.Quotient.mk a x = Ideal.Quotient.mk a u ∧
      Ideal.Quotient.mk b x = 1 ∧ IsUnit (Ideal.Quotient.mk (a * b) x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (e.symm (Ideal.Quotient.mk a u, (1 : O ⧸ b)))
  have heq : e (Ideal.Quotient.mk (a * b) x) = (Ideal.Quotient.mk a u, (1 : O ⧸ b)) := by
    rw [hx, e.apply_symm_apply]
  have hxa : Ideal.Quotient.mk a x = Ideal.Quotient.mk a u := by
    simpa only [e, Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
      using congrArg Prod.fst heq
  have hxb : Ideal.Quotient.mk b x = 1 := by
    simpa only [e, Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
      using congrArg Prod.snd heq
  refine ⟨x, hxa, hxb, ?_⟩
  apply (first_transfer_quotient_mul_isUnit_iff a b hab _).mpr
  simpa only [Ideal.Quotient.factor_mk, hxa, hxb] using And.intro hu isUnit_one

/-- The quotient character has exactly the manuscript's sextic factor and
conjugate sextic factor, with zero extension on every nonunit. -/
def firstTransferPairedResidueCharacter (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b) :
    MulChar (O ⧸ (a * b)) ℂ where
  toFun x := firstTransferResidueCharacter c ha (Ideal.Quotient.factor Ideal.mul_le_left x) *
    star (firstTransferResidueCharacter c hb (Ideal.Quotient.factor Ideal.mul_le_right x))
  map_one' := by simp only [map_one, star_one, mul_one]
  map_mul' := by
    intro x y
    simp only [map_mul, star_mul]
    ring
  map_nonunit' := by
    intro x hx
    have hnot := mt (first_transfer_quotient_mul_isUnit_iff a b
      (first_transfer_ideal_isCoprime_of_isRelPrime hab) x).mpr hx
    by_cases hxa : IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x)
    · have hxb : ¬ IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) :=
        fun h => hnot ⟨hxa, h⟩
      rw [(firstTransferResidueCharacter c hb).map_nonunit hxb, star_zero, mul_zero]
    · rw [(firstTransferResidueCharacter c ha).map_nonunit hxa, zero_mul]

@[simp] theorem firstTransferPairedResidueCharacter_apply_mk (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (x : O) :
    firstTransferPairedResidueCharacter c ha hb hab (Ideal.Quotient.mk (a * b) x) =
      sexticSymbol a x * star (sexticSymbol b x) := by
  change firstTransferResidueCharacter c ha
      (Ideal.Quotient.factor Ideal.mul_le_left (Ideal.Quotient.mk (a * b) x)) *
    star (firstTransferResidueCharacter c hb
      (Ideal.Quotient.factor Ideal.mul_le_right (Ideal.Quotient.mk (a * b) x))) = _
  simp only [Ideal.Quotient.factor_mk, firstTransferResidueCharacter_apply_mk]

theorem first_transfer_sexticSymbol_eq_one_of_mk_eq_one (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) {x : O} (hx : Ideal.Quotient.mk a x = 1) :
    sexticSymbol a x = 1 := by
  rw [← firstTransferResidueCharacter_apply_mk c ha, hx, map_one]

end QRHShort.CloudBatch.SecondCoprime


/-!
Primitivity of the paired literal character.  If a prime factor of one
squarefree denominator were absent from an inducing modulus, CRT supplies a
unit which is 1 modulo that inducing modulus but has a nontrivial local
sextic value.  The proof uses precisely agreement on product-modulus units.
-/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_squarefree_dvd_of_prime_dvd {n J : Ideal O}
    (hn : n ≠ ⊥) (hJ : J ≠ ⊥) (hsq : Squarefree n)
    (hprime : ∀ P : Ideal O, Prime P → P ∣ n → P ∣ J) : n ∣ J := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hn hJ).mpr
  apply (Multiset.le_iff_subset ((squarefree_iff_nodup_normalizedFactors hn).mp hsq)).mpr
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact (mem_normalizedFactors_iff hJ).mpr ⟨hp, hprime P hp (dvd_of_mem_normalizedFactors hP)⟩

/-- Missing a prime factor of the left denominator produces a unit witness
whose paired literal value is nontrivial, while its residue modulo J is 1. -/
theorem first_transfer_paired_left_missing_prime_witness (c : ArithmeticContext)
    {a b J P : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hP : Prime P) (hPa : P ∣ a)
    (hmod : a * b ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
      Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
  obtain ⟨A, hA⟩ := hPa
  have hPa' : P ∣ a := ⟨A, hA⟩
  have hAa : A ∣ a := ⟨P, hA.trans (mul_comm _ _)⟩
  have hPout := first_transfer_outside_of_dvd c ha.1 hPa'
  have hAout := first_transfer_outside_of_dvd c ha.1 hAa
  have hsq : Squarefree (P * (A * b)) := by
    rw [← mul_assoc, ← hA]
    exact squarefree_mul_iff.mpr ⟨hab, ha.2, hb.2⟩
  have hcop : IsCoprime P (A * b) :=
    first_transfer_ideal_isCoprime_of_isRelPrime (IsRelPrime.of_squarefree_mul hsq)
  have hJdiv : J ∣ P * (A * b) := by
    rw [← mul_assoc, ← hA]
    exact Ideal.dvd_iff_le.mpr hmod
  have hJrest : J ∣ A * b :=
    ((hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot).symm).dvd_of_dvd_mul_left hJdiv
  obtain ⟨u, hu, hζ⟩ := first_transfer_prime_character_hits_rootSix c hP hPout
  obtain ⟨x, hxP, hxrest, hxunit⟩ := first_transfer_crt_unit_lift P (A * b) hcop u hu
  have hxJ : Ideal.Quotient.mk J x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (Ideal.le_of_dvd hJrest)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxA : Ideal.Quotient.mk A x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (show A * b ≤ A from Ideal.mul_le_left)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxb : Ideal.Quotient.mk b x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (show A * b ≤ b from Ideal.mul_le_right)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxPvalue : sexticSymbol P x = embedding rootSix := by
    apply (firstTransferSexticSymbol_congr hxP).trans
    simpa only [firstTransferResidueCharacter_apply_mk] using hζ
  have hxvalue : sexticSymbol a x * star (sexticSymbol b x) = embedding rootSix := by
    rw [hA, first_transfer_sexticSymbol_mul,
      first_transfer_sexticSymbol_eq_one_of_mk_eq_one c hAout hxA,
      first_transfer_sexticSymbol_eq_one_of_mk_eq_one c hb.1 hxb, hxPvalue]
    simp only [star_one, mul_one]
  refine ⟨x, ?_, hxJ, ?_⟩
  · rw [hA, mul_assoc]
    exact hxunit
  · rw [hxvalue]
    exact first_transfer_embedding_rootSix_ne_one

theorem first_transfer_paired_right_missing_prime_witness (c : ArithmeticContext)
    {a b J P : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hP : Prime P) (hPb : P ∣ b)
    (hmod : a * b ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
      Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
  obtain ⟨x, hxunit, hxJ, hxvalue⟩ := first_transfer_paired_left_missing_prime_witness c
    hb ha hab.symm hP hPb (by simpa only [mul_comm] using hmod) hnot
  refine ⟨x, ?_, hxJ, ?_⟩
  · rw [mul_comm a b]
    exact hxunit
  · intro h
    apply hxvalue
    have hh := congrArg star h
    simpa only [star_mul, star_star, star_one, mul_comm] using hh

/-- The exact unit-agreement condition required by PrimitiveResidueCharacter. -/
theorem firstTransferPairedResidueCharacter_primitive (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (J : Ideal O) (hJ : J ≠ ⊥) (hmod : a * b ≤ J)
    (ψ : MulChar (O ⧸ J) ℂ)
    (hagrees : ∀ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) →
      firstTransferPairedResidueCharacter c ha.1 hb.1 hab (Ideal.Quotient.mk (a * b) x) =
        ψ (Ideal.Quotient.mk J x)) : J = a * b := by
  have hab0 : a * b ≠ ⊥ := mul_ne_zero ha.1.1 hb.1.1
  have hsq : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨hab, ha.2, hb.2⟩
  have hdiv : a * b ∣ J := first_transfer_squarefree_dvd_of_prime_dvd hab0 hJ hsq (by
    intro P hP hPab
    by_contra hnot
    have hex : ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
        Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
      rcases hP.dvd_mul.mp hPab with hPa | hPb
      · exact first_transfer_paired_left_missing_prime_witness c ha hb hab hP hPa hmod hnot
      · exact first_transfer_paired_right_missing_prime_witness c ha hb hab hP hPb hmod hnot
    obtain ⟨x, hxunit, hxJ, hxvalue⟩ := hex
    apply hxvalue
    have h := hagrees x hxunit
    simpa only [firstTransferPairedResidueCharacter_apply_mk, hxJ, map_one] using h)
  exact le_antisymm (Ideal.le_of_dvd hdiv) hmod

/-- A primitive character for the literal paired sextic row, including the
principal character when both denominator ideals are the unit ideal. -/
def firstTransferPrimitivePairedCharacter (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b) :
    PrimitiveResidueCharacter where
  modulus := a * b
  modulus_ne_bot := mul_ne_zero ha.1.1 hb.1.1
  character := firstTransferPairedResidueCharacter c ha.1 hb.1 hab
  primitive := by
    intro J hJ hmod hfactor
    obtain ⟨ψ, hagrees⟩ := hfactor
    exact firstTransferPairedResidueCharacter_primitive c ha hb hab J hJ hmod ψ hagrees

@[simp] theorem firstTransferPrimitivePairedCharacter_modulus (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) : (firstTransferPrimitivePairedCharacter c ha hb hab).modulus = a * b := rfl

@[simp] theorem firstTransferPrimitivePairedCharacter_value (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (x : O) :
    (firstTransferPrimitivePairedCharacter c ha hb hab).value x =
      sexticSymbol a x * star (sexticSymbol b x) :=
  firstTransferPairedResidueCharacter_apply_mk c ha.1 hb.1 hab x

end QRHShort.CloudBatch.SecondCoprime


/-!
The actual CRT reindexing used in the paired Gauss sum. Multiplication by
the opposite generator gives permutations of the two quotient rings, so the
representatives B*u + A*v cover the product quotient exactly once. Quotients
by the unit ideal are included throughout.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_gauss_crt_generator_isUnit (a b : Ideal O)
    (hab : IsCoprime a b) (B : O) (hB : principal B = b) :
    IsUnit (Ideal.Quotient.mk a B) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hab.exists
  rw [← hB] at hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hy
  have h := congrArg (Ideal.Quotient.mk a) hxy
  simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    zero_add, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk a t, h⟩

/-- Reindexing by the actual Chinese-remainder bijection after multiplying
the two quotient coordinates by the opposite generators. -/
theorem first_transfer_gauss_crt_reindex (a b : Ideal O) (hab : IsCoprime a b)
    (A B : O) (hA : principal A = a) (hB : principal B = b)
    [Fintype (O ⧸ a)] [Fintype (O ⧸ b)] [Fintype (O ⧸ (a * b))]
    (f : O ⧸ (a * b) → ℂ) :
    (∑ x : O ⧸ (a * b), f x) =
      ∑ u : O ⧸ a, ∑ v : O ⧸ b,
        f (Ideal.Quotient.mk (a * b) (B * residueLift a u + A * residueLift b v)) := by
  let hBa := first_transfer_gauss_crt_generator_isUnit a b hab B hB
  let hAb := first_transfer_gauss_crt_generator_isUnit b a hab.symm A hA
  let base := Ideal.quotientMulEquivQuotientProd a b hab
  let e : (O ⧸ a) × (O ⧸ b) ≃ O ⧸ (a * b) :=
    (hBa.unit.mulLeft.prodCongr hAb.unit.mulLeft).trans base.toEquiv.symm
  have hAzero : Ideal.Quotient.mk a A = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hA]
    exact Ideal.mem_span_singleton_self A
  have hBzero : Ideal.Quotient.mk b B = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hB]
    exact Ideal.mem_span_singleton_self B
  have he (u : O ⧸ a) (v : O ⧸ b) : e (u, v) =
      Ideal.Quotient.mk (a * b) (B * residueLift a u + A * residueLift b v) := by
    apply base.injective
    change base (base.symm (hBa.unit * u, hAb.unit * v)) = _
    rw [base.apply_symm_apply]
    apply Prod.ext
    · change hBa.unit * u = (Ideal.quotientMulEquivQuotientProd a b hab
        (Ideal.Quotient.mk (a * b) _)).1
      rw [Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
      simp only [map_add, map_mul, hAzero, zero_mul, add_zero,
        firstTransferResidueLift_spec, IsUnit.unit_spec]
    · change hAb.unit * v = (Ideal.quotientMulEquivQuotientProd a b hab
        (Ideal.Quotient.mk (a * b) _)).2
      rw [Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
      simp only [map_add, map_mul, hBzero, zero_mul, zero_add,
        firstTransferResidueLift_spec, IsUnit.unit_spec]
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [he]

theorem first_transfer_gauss_crt_paired_value (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (u v : O) :
    firstTransferPairedResidueCharacter c ha hb hab
      (Ideal.Quotient.mk (a * b)
        (primaryGenerator b * u + primaryGenerator a * v)) =
      (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) *
        (sexticSymbol a u * star (sexticSymbol b v)) := by
  have hAzero : Ideal.Quotient.mk a (primaryGenerator a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : primaryGenerator a ∈ principal (primaryGenerator a) :=
      Ideal.mem_span_singleton_self _
    rw [(first_transfer_primaryGenerator_spec_and_primary_outside c ha).1] at hm
    exact hm
  have hBzero : Ideal.Quotient.mk b (primaryGenerator b) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : primaryGenerator b ∈ principal (primaryGenerator b) :=
      Ideal.mem_span_singleton_self _
    rw [(first_transfer_primaryGenerator_spec_and_primary_outside c hb).1] at hm
    exact hm
  have hleft : sexticSymbol a (primaryGenerator b * u + primaryGenerator a * v) =
      sexticSymbol a (primaryGenerator b) * sexticSymbol a u := by
    rw [← firstTransferResidueCharacter_apply_mk c ha]
    simp only [map_add, map_mul, hAzero, zero_mul, add_zero,
      firstTransferResidueCharacter_apply_mk]
  have hright : sexticSymbol b (primaryGenerator b * u + primaryGenerator a * v) =
      sexticSymbol b (primaryGenerator a) * sexticSymbol b v := by
    rw [← firstTransferResidueCharacter_apply_mk c hb]
    simp only [map_add, map_mul, hBzero, zero_mul, zero_add,
      firstTransferResidueCharacter_apply_mk]
  rw [firstTransferPairedResidueCharacter_apply_mk, hleft, hright, star_mul]
  ring

/-- Complex conjugation is exactly the frozen negative first power,
including the zero extension at nonunits. -/
theorem first_transfer_gauss_sextic_star_eq_neg_one (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O) :
    star (sexticSymbol n x) = sexticSymbol n x ^ (-1 : ℤ) := by
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1
  rw [← firstTransferResidueCharacter_apply_mk c hn,
    MulChar.star_apply', MulChar.inv_apply_eq_inv', zpow_neg_one]

end QRHShort.CloudBatch.SecondCoprime


/-!
The lattice-triviality and representative invariance needed by the Gauss CRT
calculation. These use the actual integral power basis and selected embedding.
The frozen EisensteinBasis/AdditiveCharacter files are not changed.
-/

noncomputable section
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

def first_transfer_eisensteinPowerBasis : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

theorem first_transfer_eisensteinPowerBasis_dim : first_transfer_eisensteinPowerBasis.dim = 2 := by
  change (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

def first_transfer_eisensteinBasis : Module.Basis (Fin 2) ℤ O :=
  first_transfer_eisensteinPowerBasis.basis.reindex (finCongr first_transfer_eisensteinPowerBasis_dim)

theorem first_transfer_eisensteinBasis_zero : first_transfer_eisensteinBasis 0 = 1 := by
  rw [first_transfer_eisensteinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change first_transfer_eisensteinPowerBasis.gen ^ (0 : ℕ) = 1
  exact pow_zero _

theorem first_transfer_eisensteinBasis_one : first_transfer_eisensteinBasis 1 = omega := by
  rw [first_transfer_eisensteinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change first_transfer_eisensteinPowerBasis.gen ^ (1 : ℕ) = omega
  rw [pow_one]
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

theorem first_transfer_eisenstein_coords (a : O) :
    a = (first_transfer_eisensteinBasis.repr a 0 : O) + (first_transfer_eisensteinBasis.repr a 1 : O) * omega := by
  simpa [Fin.sum_univ_two, first_transfer_eisensteinBasis_zero, first_transfer_eisensteinBasis_one,
    Algebra.smul_def] using (first_transfer_eisensteinBasis.sum_repr a).symm

@[simp] theorem first_transfer_embedding_intCast (x : ℤ) : embedding (x : O) = (x : ℂ) := by
  simpa only [embeddingHom_apply] using map_intCast embeddingHom x

theorem first_transfer_embedding_omega_im : (embedding omega).im = Real.sqrt 3 / 2 := by
  let w := embedding omega
  have hp : w ^ 2 + w + 1 = 0 := by
    simpa only [embedding_add, embedding_pow, embedding_one, embedding_zero] using
      congrArg embedding omega_sq_add_omega_add_one
  have hr : w.re ^ 2 - w.im ^ 2 + w.re + 1 = 0 := by
    simpa only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
      Complex.zero_re] using congrArg Complex.re hp
  have hi : 2 * w.re * w.im + w.im = 0 := by
    have h := congrArg Complex.im hp
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im,
      Complex.zero_im] at h
    nlinarith
  have hne : w.im ≠ 0 := by
    intro h
    rw [h] at hr
    nlinarith [sq_nonneg (w.re + (1 : ℝ) / 2)]
  have hre : w.re = -(1 : ℝ) / 2 := by
    have hf : (2 * w.re + 1) * w.im = 0 := by nlinarith
    have hz := (mul_eq_zero.mp hf).resolve_right hne
    linarith
  have hnonneg : 0 ≤ w.im := by
    dsimp [w, embedding]
    split_ifs with h
    · exact h.le
    · simpa only [Complex.star_def, Complex.conj_im] using
        neg_nonneg.mpr (le_of_not_gt h)
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : w.im ^ 2 = (3 : ℝ) / 4 := by nlinarith
  change w.im = _
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

theorem first_transfer_additiveCharacter_add (z w : ℂ) :
    additiveCharacter (z + w) = additiveCharacter z * additiveCharacter w := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_im]
  push_cast
  ring

@[simp] theorem first_transfer_additiveCharacter_embedding (a : O) :
    additiveCharacter (embedding a) = 1 := by
  let y : ℤ := first_transfer_eisensteinBasis.repr a 1
  have him : (embedding a).im = (y : ℝ) * Real.sqrt 3 / 2 := by
    rw [first_transfer_eisenstein_coords a, embedding_add, embedding_mul,
      first_transfer_embedding_intCast, first_transfer_embedding_intCast]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, zero_add, add_zero, first_transfer_embedding_omega_im]
    dsimp [y]
    ring
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hexp : 4 * Real.pi * (embedding a).im / Real.sqrt 3 =
      (y : ℝ) * (2 * Real.pi) := by
    rw [him]
    field_simp [hs]
    <;> ring
  rw [additiveCharacter, hexp]
  push_cast
  simpa only [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I y

theorem first_transfer_additiveCharacter_add_embedding (z : ℂ) (a : O) :
    additiveCharacter (z + embedding a) = additiveCharacter z := by
  rw [first_transfer_additiveCharacter_add, first_transfer_additiveCharacter_embedding, mul_one]

@[simp] theorem first_transfer_additiveCharacter_zero : additiveCharacter 0 = 1 := by
  simp [additiveCharacter]

/-- The additive phase is unchanged by any change of integral representative
modulo its nonzero principal denominator. -/
theorem first_transfer_gauss_additive_div_congr {g x y : O} (hg : g ≠ 0)
    (hxy : Ideal.Quotient.mk (principal g) x = Ideal.Quotient.mk (principal g) y) :
    additiveCharacter (embedding x / embedding g) =
      additiveCharacter (embedding y / embedding g) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hxy)
  have hx : x = y + g * z := by linear_combination hz
  have hg' : embedding g ≠ 0 := fun h => hg (embedding_eq_zero.mp h)
  have harg : embedding x / embedding g = embedding y / embedding g + embedding z := by
    rw [hx, embedding_add, embedding_mul]
    field_simp [hg']
  rw [harg, first_transfer_additiveCharacter_add_embedding]

end QRHShort.CloudBatch.SecondCoprime


/-!
The literal additive phase is well-defined on each outside quotient and
splits under the opposite-generator CRT representatives.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

/-- The additive factor appearing in the frozen ideal Gauss sums. -/
def firstTransferGaussPhase (n : Ideal O) (x : O ⧸ n) : ℂ :=
  additiveCharacter (embedding (residueLift n x) / embedding (primaryGenerator n))

theorem first_transfer_gauss_phase_apply_mk (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O) :
    firstTransferGaussPhase n (Ideal.Quotient.mk n x) =
      additiveCharacter (embedding x / embedding (primaryGenerator n)) := by
  have hgen := (first_transfer_primaryGenerator_spec_and_primary_outside c hn).1
  have hne : primaryGenerator n ≠ 0 := by
    intro h
    apply hn.1
    rw [← hgen, h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  apply first_transfer_gauss_additive_div_congr hne
  rw [hgen]
  exact firstTransferResidueLift_spec n _

theorem first_transfer_gauss_phase_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (u v : O) :
    firstTransferGaussPhase (a * b) (Ideal.Quotient.mk (a * b)
      (primaryGenerator b * u + primaryGenerator a * v)) =
      additiveCharacter (embedding u / embedding (primaryGenerator a)) *
        additiveCharacter (embedding v / embedding (primaryGenerator b)) := by
  have hab := (first_transfer_outside_mul_iff c a b).mpr ⟨ha, hb⟩
  have hne (n : Ideal O) (hn : Outside c.S n) : embedding (primaryGenerator n) ≠ 0 := by
    intro h
    apply hn.1
    rw [← (first_transfer_primaryGenerator_spec_and_primary_outside c hn).1,
      embedding_eq_zero.mp h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  rw [first_transfer_gauss_phase_apply_mk c hab,
    first_transfer_primaryGenerator_mul_outside c ha hb,
    embedding_add, embedding_mul, embedding_mul, embedding_mul]
  have harg :
      (embedding (primaryGenerator b) * embedding u +
        embedding (primaryGenerator a) * embedding v) /
        (embedding (primaryGenerator a) * embedding (primaryGenerator b)) =
      embedding u / embedding (primaryGenerator a) +
        embedding v / embedding (primaryGenerator b) := by
    field_simp [hne a ha, hne b hb]
  rw [harg, first_transfer_additiveCharacter_add]

/-- Exact factorization before normalizing, valid also for unit-ideal
quotients and for any chosen finite enumerations of the quotients. -/
theorem first_transfer_paired_gauss_crt_sum (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    [Fintype (O ⧸ a)] [Fintype (O ⧸ b)] [Fintype (O ⧸ (a * b))] :
    (∑ x : O ⧸ (a * b), firstTransferPairedResidueCharacter c ha hb hab x *
      firstTransferGaussPhase (a * b) x) =
      (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) *
        (∑ u : O ⧸ a, sexticSymbol a (residueLift a u) * firstTransferGaussPhase a u) *
        (∑ v : O ⧸ b, star (sexticSymbol b (residueLift b v)) * firstTransferGaussPhase b v) := by
  rw [first_transfer_gauss_crt_reindex a b
    (first_transfer_ideal_isCoprime_of_isRelPrime hab)
    (primaryGenerator a) (primaryGenerator b)
    (first_transfer_primaryGenerator_spec_and_primary_outside c ha).1
    (first_transfer_primaryGenerator_spec_and_primary_outside c hb).1]
  simp_rw [first_transfer_gauss_crt_paired_value c ha hb hab,
    first_transfer_gauss_phase_crt c ha hb]
  simp only [firstTransferGaussPhase, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

end QRHShort.CloudBatch.SecondCoprime


/-!
CRT factorization of the actual normalized paired Gauss sum. The twist,
normalization, residue representatives, and chosen generators agree with
the frozen definitions, including the unit-ideal cases.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_gauss_sqrt_norm_inv_mul (a b : Ideal O) :
    (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ =
      (Real.sqrt (normIdeal a) : ℂ)⁻¹ * (Real.sqrt (normIdeal b) : ℂ)⁻¹ := by
  simp only [normIdeal, map_mul, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, mul_inv]

/-- The exact normalized CRT identity for the literal paired character.
No primitivity or nontriviality assumption on the quotient is needed. -/
theorem first_transfer_paired_gauss_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    [Fintype (O ⧸ (a * b))] :
    (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ *
      (∑ x : O ⧸ (a * b), firstTransferPairedResidueCharacter c ha hb hab x *
        additiveCharacter (embedding (residueLift (a * b) x) /
          embedding (chosenGenerator (a * b)))) =
      sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
        gauss 1 a * gauss (-1) b := by
  letI : Finite (O ⧸ a) := Ring.HasFiniteQuotients.finiteQuotient ha.1
  letI : Finite (O ⧸ b) := Ring.HasFiniteQuotients.finiteQuotient hb.1
  letI : Fintype (O ⧸ a) := Fintype.ofFinite _
  letI : Fintype (O ⧸ b) := Fintype.ofFinite _
  have hout := (first_transfer_outside_mul_iff c a b).mpr ⟨ha, hb⟩
  rw [first_transfer_chosenGenerator_eq_primaryGenerator c hout]
  change (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ *
    (∑ x : O ⧸ (a * b), firstTransferPairedResidueCharacter c ha hb hab x *
      firstTransferGaussPhase (a * b) x) = _
  rw [first_transfer_paired_gauss_crt_sum c ha hb hab,
    first_transfer_gauss_sqrt_norm_inv_mul]
  simp_rw [first_transfer_gauss_sextic_star_eq_neg_one c hb]
  simp only [gauss, dif_pos ha.1, dif_pos hb.1, zpow_one, firstTransferGaussPhase]
  ring

/-- The preceding finite-sum formula is precisely the Gauss sum attached
to the concrete primitive character for a squarefree coprime pair. -/
theorem first_transfer_primitive_paired_gauss_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    (firstTransferPrimitivePairedCharacter c ha hb hab).gauss =
      sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
        gauss 1 a * gauss (-1) b := by
  letI : Finite (O ⧸ (a * b)) :=
    Ring.HasFiniteQuotients.finiteQuotient (mul_ne_zero ha.1.1 hb.1.1)
  letI : Fintype (O ⧸ (a * b)) := Fintype.ofFinite _
  exact first_transfer_paired_gauss_crt c ha.1 hb.1 hab

end QRHShort.CloudBatch.SecondCoprime


/-!
The actual ideal-gcd decomposition of squarefree outside pairs.  Ideals have
trivial units, so the common factor is the literal normalized ideal gcd, and
the two remaining factors are unique rather than merely associated.
-/

noncomputable section
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

def firstTransferGcdPairAdmissible (c : ArithmeticContext) (p : Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2

def firstTransferGcdTripleAdmissible (c : ArithmeticContext)
    (t : Ideal O × Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧ SquarefreeOutside c.S t.2.2 ∧
    IsRelPrime t.1 t.2.1 ∧ IsRelPrime t.1 t.2.2 ∧ IsRelPrime t.2.1 t.2.2

abbrev FirstTransferGcdPairs (c : ArithmeticContext) :=
  {p : Ideal O × Ideal O // firstTransferGcdPairAdmissible c p}

abbrev FirstTransferGcdTriples (c : ArithmeticContext) :=
  {t : Ideal O × Ideal O × Ideal O // firstTransferGcdTripleAdmissible c t}

/-- Reconstruction multiplies both residual ideals by their common factor. -/
def firstTransferGcdReconstruct (c : ArithmeticContext) :
    FirstTransferGcdTriples c → FirstTransferGcdPairs c := fun t =>
  ⟨(t.1.1 * t.1.2.1, t.1.1 * t.1.2.2),
    ⟨(first_transfer_outside_mul_iff c _ _).mpr ⟨t.2.1.1, t.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨t.2.2.2.2.1, t.2.1.2, t.2.2.1.2⟩⟩,
    ⟨(first_transfer_outside_mul_iff c _ _).mpr ⟨t.2.1.1, t.2.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨t.2.2.2.2.2.1, t.2.1.2, t.2.2.2.1.2⟩⟩⟩

@[simp] theorem firstTransferGcdReconstruct_val (c : ArithmeticContext)
    (t : FirstTransferGcdTriples c) :
    (firstTransferGcdReconstruct c t).1 = (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2) := rfl

/-- The reconstructed pair has exactly C as its actual ideal gcd. -/
theorem firstTransferGcdReconstruct_gcd (c : ArithmeticContext) (t : FirstTransferGcdTriples c) :
    gcd (firstTransferGcdReconstruct c t).1.1 (firstTransferGcdReconstruct c t).1.2 = t.1.1 := by
  have hunit : gcd t.1.2.1 t.1.2.2 = 1 :=
    (gcd_isUnit_iff_isRelPrime.mpr t.2.2.2.2.2.2).eq_one
  change gcd (t.1.1 * t.1.2.1) (t.1.1 * t.1.2.2) = t.1.1
  rw [gcd_mul_left, normalize_eq, hunit, mul_one]

theorem firstTransferGcdReconstruct_injective (c : ArithmeticContext) :
    Function.Injective (firstTransferGcdReconstruct c) := by
  intro t s h
  have hC : t.1.1 = s.1.1 := by
    calc
      t.1.1 = gcd (firstTransferGcdReconstruct c t).1.1
          (firstTransferGcdReconstruct c t).1.2 := (firstTransferGcdReconstruct_gcd c t).symm
      _ = gcd (firstTransferGcdReconstruct c s).1.1
          (firstTransferGcdReconstruct c s).1.2 :=
        congrArg (fun p : FirstTransferGcdPairs c => gcd p.1.1 p.1.2) h
      _ = s.1.1 := firstTransferGcdReconstruct_gcd c s
  have hpair : (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2) =
      (s.1.1 * s.1.2.1, s.1.1 * s.1.2.2) := congrArg Subtype.val h
  apply Subtype.ext
  apply Prod.ext hC
  apply Prod.ext
  · apply mul_left_cancel₀ t.2.1.1.1
    simpa only [hC] using congrArg Prod.fst hpair
  · apply mul_left_cancel₀ t.2.1.1.1
    simpa only [hC] using congrArg Prod.snd hpair

/-- Extraction starts with Mathlib's literal gcd factorization; squarefreeness
forces each residual factor to be coprime to the common factor as well. -/
theorem firstTransferGcdReconstruct_surjective (c : ArithmeticContext) :
    Function.Surjective (firstTransferGcdReconstruct c) := by
  intro p
  obtain ⟨u, v, hu, hv, huv⟩ := extract_gcd p.1.1 p.1.2
  let C := gcd p.1.1 p.1.2
  have hC : SquarefreeOutside c.S C :=
    ⟨first_transfer_outside_of_dvd c p.2.1.1 (gcd_dvd_left _ _),
      p.2.1.2.squarefree_of_dvd (gcd_dvd_left _ _)⟩
  have hudiv : u ∣ p.1.1 := ⟨C, hu.trans (mul_comm _ _)⟩
  have hvdiv : v ∣ p.1.2 := ⟨C, hv.trans (mul_comm _ _)⟩
  have huout : SquarefreeOutside c.S u :=
    ⟨first_transfer_outside_of_dvd c p.2.1.1 hudiv, p.2.1.2.squarefree_of_dvd hudiv⟩
  have hvout : SquarefreeOutside c.S v :=
    ⟨first_transfer_outside_of_dvd c p.2.2.1 hvdiv, p.2.2.2.squarefree_of_dvd hvdiv⟩
  have hCu : IsRelPrime C u := IsRelPrime.of_squarefree_mul (hu ▸ p.2.1.2)
  have hCv : IsRelPrime C v := IsRelPrime.of_squarefree_mul (hv ▸ p.2.2.2)
  have huv' : IsRelPrime u v := gcd_isUnit_iff_isRelPrime.mp huv
  refine ⟨⟨(C, u, v), hC, huout, hvout, hCu, hCv, huv'⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hu.symm hv.symm

theorem firstTransferGcdReconstruct_bijective (c : ArithmeticContext) :
    Function.Bijective (firstTransferGcdReconstruct c) :=
  ⟨firstTransferGcdReconstruct_injective c, firstTransferGcdReconstruct_surjective c⟩

/-- The forward map reconstructs the pair; the inverse is its unique gcd triple. -/
def firstTransferGcdEquiv (c : ArithmeticContext) :
    FirstTransferGcdTriples c ≃ FirstTransferGcdPairs c :=
  Equiv.ofBijective (firstTransferGcdReconstruct c) (firstTransferGcdReconstruct_bijective c)

@[simp] theorem firstTransferGcdEquiv_apply (c : ArithmeticContext) (t : FirstTransferGcdTriples c) :
    firstTransferGcdEquiv c t = firstTransferGcdReconstruct c t := rfl

theorem firstTransferGcdEquiv_symm_gcd (c : ArithmeticContext) (p : FirstTransferGcdPairs c) :
    ((firstTransferGcdEquiv c).symm p).1.1 = gcd p.1.1 p.1.2 := by
  have h := firstTransferGcdReconstruct_gcd c ((firstTransferGcdEquiv c).symm p)
  change gcd (firstTransferGcdEquiv c ((firstTransferGcdEquiv c).symm p)).1.1
    (firstTransferGcdEquiv c ((firstTransferGcdEquiv c).symm p)).1.2 = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem firstTransferGcdEquiv_symm_reconstruct (c : ArithmeticContext) (p : FirstTransferGcdPairs c) :
    let t := (firstTransferGcdEquiv c).symm p
    p.1.1 = t.1.1 * t.1.2.1 ∧ p.1.2 = t.1.1 * t.1.2.2 := by
  have h := congrArg Subtype.val ((firstTransferGcdEquiv c).apply_symm_apply p)
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

end QRHShort.CloudBatch.SecondCoprime


/-!
Finite and summable reindexing by the genuine gcd equivalence.  The infinite
series API returns summability of the transformed series together with its
value identity, so no convergence is inferred from totalized tsum notation.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_gcd_sum_reindex {E : Type*} [AddCommMonoid E]
    (c : ArithmeticContext) (s : Finset (FirstTransferGcdPairs c))
    (f : FirstTransferGcdPairs c → E) :
    ∑ p ∈ s, f p =
      ∑ t ∈ s.map (firstTransferGcdEquiv c).symm.toEmbedding,
        f (firstTransferGcdReconstruct c t) := by
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  change f p = f (firstTransferGcdEquiv c ((firstTransferGcdEquiv c).symm p))
  rw [Equiv.apply_symm_apply]

theorem first_transfer_gcd_summable_iff {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : FirstTransferGcdPairs c → E) :
    Summable (fun t : FirstTransferGcdTriples c => f (firstTransferGcdReconstruct c t)) ↔
      Summable f :=
  (firstTransferGcdEquiv c).summable_iff

theorem first_transfer_gcd_summable_reindex {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : FirstTransferGcdPairs c → E) (hf : Summable f) :
    Summable (fun t : FirstTransferGcdTriples c => f (firstTransferGcdReconstruct c t)) ∧
      (∑' p, f p) = ∑' t : FirstTransferGcdTriples c, f (firstTransferGcdReconstruct c t) :=
  ⟨(first_transfer_gcd_summable_iff c f).mpr hf, ((firstTransferGcdEquiv c).tsum_eq f).symm⟩

/-- An unbundled form ready for literal ideal-pair expansions: both transformed
restrictions and all three coprimalities are exactly those of the gcd triple. -/
theorem first_transfer_gcd_indicator_reindex {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : Ideal O × Ideal O → E)
    (hf : Summable (fun p : Ideal O × Ideal O =>
      if firstTransferGcdPairAdmissible c p then f p else 0)) :
    Summable (fun t : Ideal O × Ideal O × Ideal O =>
      if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0) ∧
    (∑' p : Ideal O × Ideal O, if firstTransferGcdPairAdmissible c p then f p else 0) =
      ∑' t : Ideal O × Ideal O × Ideal O,
        if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
  have hpairIndicator : ({p | firstTransferGcdPairAdmissible c p}.indicator f) =
      (fun p => if firstTransferGcdPairAdmissible c p then f p else 0) := by
    funext p
    exact Set.indicator_apply _ _ _
  have htripleIndicator : ({t | firstTransferGcdTripleAdmissible c t}.indicator
      (fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))) =
      (fun t => if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2)
        else 0) := by
    funext t
    exact Set.indicator_apply _ _ _
  have hpair : Summable (fun p : FirstTransferGcdPairs c => f p.1) := by
    apply (summable_subtype_iff_indicator
      (s := {p | firstTransferGcdPairAdmissible c p}) (f := f)).mpr
    rw [hpairIndicator]
    exact hf
  obtain ⟨htriple, heq⟩ := first_transfer_gcd_summable_reindex c
    (fun p : FirstTransferGcdPairs c => f p.1) hpair
  have htriple' := (summable_subtype_iff_indicator
    (s := {t | firstTransferGcdTripleAdmissible c t})
    (f := fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))).mp htriple
  refine ⟨?_, ?_⟩
  · rw [htripleIndicator] at htriple'
    exact htriple'
  · have hp : (∑' p : FirstTransferGcdPairs c, f p.1) =
        ∑' p : Ideal O × Ideal O, if firstTransferGcdPairAdmissible c p then f p else 0 := by
      have h := tsum_subtype {p | firstTransferGcdPairAdmissible c p} f
      simp_rw [hpairIndicator] at h
      exact h
    have ht : (∑' t : FirstTransferGcdTriples c, f (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2)) =
        ∑' t : Ideal O × Ideal O × Ideal O,
          if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
      have h := tsum_subtype {t | firstTransferGcdTripleAdmissible c t}
        (fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))
      simp_rw [htripleIndicator] at h
      exact h
    exact hp.symm.trans (heq.trans ht)

end QRHShort.CloudBatch.SecondCoprime


/-! Literal zero filters and sixth-root algebra for the frozen sextic symbol.
The quotient criterion includes the unit ideal and zero numerators. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch.SecondCoprime

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

end QRHShort.CloudBatch.SecondCoprime



/-!
The arithmetic simplification of the explicit two-factor Gauss expression.
Its identification with the Gauss sum of the primitive paired character is a
separate CRT obligation. All symbols here are the frozen literal definitions.
-/

noncomputable section
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_norm_alpha_eq_one (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : ‖alpha n‖ = 1 := by
  have h : embedding (primaryGenerator n) ≠ 0 :=
    fun hz => first_transfer_primaryGenerator_ne_zero c hn (embedding_eq_zero.mp hz)
  simp only [alpha, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]

theorem first_transfer_mobius_sq {n : Ideal O} (hn : Squarefree n) :
    (mobius n : ℂ) ^ 2 = 1 := by
  simp [mobius, hn.moebius_eq, ← pow_mul, Nat.mul_comm]

theorem first_transfer_norm_mobius_eq_one {n : Ideal O} (hn : Squarefree n) :
    ‖(mobius n : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (first_transfer_mobius_sq hn) (by decide)

theorem first_transfer_norm_sexticSymbol_of_unit (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk n z)) : ‖sexticSymbol n z‖ = 1 := by
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1
  letI : Fintype (O ⧸ n) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hz
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity
    ((firstTransferResidueCharacter c hn).apply_mem_rootsOfUnity u)
  simpa only [MulChar.coe_equivToUnitHom, hu,
    firstTransferResidueCharacter_apply_mk] using h

theorem first_transfer_primaryGenerator_unit_of_isRelPrime (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b)
    (hab : IsRelPrime a b) : IsUnit (Ideal.Quotient.mk a (primaryGenerator b)) := by
  have hcop : IsCoprime a b := by
    apply Ideal.coprime_of_no_prime_ge
    intro p hap hbp hp
    have hp0 : p ≠ ⊥ := by
      intro h
      exact ha.1 (le_bot_iff.mp (h ▸ hap))
    exact (Ideal.prime_of_isPrime hp0 hp).not_unit
      (hab (Ideal.dvd_iff_le.mpr hap) (Ideal.dvd_iff_le.mpr hbp))
  obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
  rw [← first_transfer_primaryGenerator_spec_outside c hb] at hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hy
  have h := congrArg (Ideal.Quotient.mk a) hxy
  simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    zero_add, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk a t, h⟩

theorem first_transfer_norm_gauss_two (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {n : Ideal O} (hn : SquarefreeOutside c.S n) :
    ‖gauss 2 n‖ = 1 := by
  obtain ⟨G, R, _, _, _, _, _, _, _, hgauss, _, _⟩ := hc
  have h := congrArg norm (hgauss n hn).1
  rw [norm_pow, norm_mul, first_transfer_norm_mobius_eq_one hn.2,
    first_transfer_norm_alpha_eq_one c hn.1, mul_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    (h.trans (one_pow 3).symm)

/-- The explicit expression that the separate CRT Gauss calculation must
identify with the normalized Gauss sum of the paired primitive character. -/
def firstTransferPairedGaussFactor (a b : Ideal O) : ℂ :=
  sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
    gauss 1 a * gauss (-1) b

theorem first_transfer_coefficient_pairedGaussFactor (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    coefficient ξ.val a * star (coefficient ξ.val b) * firstTransferPairedGaussFactor a b =
      (mobius a : ℂ) * (mobius b : ℂ) *
        (rayValue ξ.val a * star (rayValue ξ.val b)) *
          reciprocityG c hc (idealClass c a * (idealClass c b)⁻¹) := by
  obtain ⟨R, hG, hsign, hsym, _, _, _, hrec, hgauss, _, hquot⟩ := Classical.choose_spec hc
  let G := reciprocityG c hc
  have hcross : sexticSymbol a (primaryGenerator b) *
      star (sexticSymbol b (primaryGenerator a)) = R (idealClass c a) (idealClass c b) := by
    rw [hrec a b ha.1 hb.1 hab, star_mul]
    have hn : ‖sexticSymbol a (primaryGenerator b)‖ = 1 :=
      first_transfer_norm_sexticSymbol_of_unit c ha.1 _
        (first_transfer_primaryGenerator_unit_of_isRelPrime c ha.1 hb.1 hab)
    have hunit : sexticSymbol a (primaryGenerator b) *
        star (sexticSymbol a (primaryGenerator b)) = 1 := by
      simpa only [starRingEnd_apply, hn, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (sexticSymbol a (primaryGenerator b))
    rcases hsign (idealClass c a) (idealClass c b) with h | h <;>
      simp only [h, star_one, star_neg, one_mul, mul_one, mul_neg] <;> simpa using hunit
  have hα : star (alpha b) * alpha b = 1 := by
    simpa only [starRingEnd_apply, first_transfer_norm_alpha_eq_one c hb.1,
      one_pow, Complex.ofReal_one] using Complex.conj_mul' (alpha b)
  have hg₂ : gauss 2 b * star (gauss 2 b) = 1 := by
    simpa only [starRingEnd_apply, first_transfer_norm_gauss_two c hc hb,
      one_pow, Complex.ofReal_one] using Complex.mul_conj' (gauss 2 b)
  have hGb : (G (idealClass c b))⁻¹ = star (G (idealClass c b)) :=
    Complex.inv_eq_conj (hG (idealClass c b))
  have hbminus : alpha b * star (gauss 2 b) * gauss (-1) b =
      (mobius b : ℂ) * sexticSymbol b (-1) * star (G (idealClass c b)) := by
    calc
      _ = (mobius b : ℂ) * ((mobius b : ℂ) * gauss (-1) b) *
          (alpha b * star (gauss 2 b)) := by
        rw [show (mobius b : ℂ) * ((mobius b : ℂ) * gauss (-1) b) =
          (mobius b : ℂ) ^ 2 * gauss (-1) b by ring,
          first_transfer_mobius_sq hb.2, one_mul]
        ring
      _ = (mobius b : ℂ) *
          (sexticSymbol b (-1) * (G (idealClass c b))⁻¹ * star (alpha b) * gauss 2 b) *
          (alpha b * star (gauss 2 b)) := by
        rw [(hgauss b hb).2.2.2.2.2]
        rfl
      _ = ((mobius b : ℂ) * sexticSymbol b (-1) * star (G (idealClass c b))) *
          (star (alpha b) * alpha b) * (gauss 2 b * star (gauss 2 b)) := by
        rw [hGb]
        ring
      _ = _ := by rw [hα, hg₂, mul_one, mul_one]
  have hga : star (alpha a) * gauss 2 a * gauss 1 a =
      (mobius a : ℂ) * G (idealClass c a) := (hgauss a ha).2.2.2.2.1
  have hq : sexticSymbol b (-1) * star (G (idealClass c b)) * G (idealClass c a) *
      R (idealClass c a) (idealClass c b) =
        G (idealClass c a * (idealClass c b)⁻¹) := by
    rw [hsym (idealClass c a) (idealClass c b)]
    exact hquot b a hb.1 ha.1
  unfold coefficient firstTransferPairedGaussFactor
  rw [star_mul, star_mul, star_star]
  calc
    _ = (star (alpha a) * gauss 2 a * gauss 1 a) *
        (alpha b * star (gauss 2 b) * gauss (-1) b) *
        (rayValue ξ.val a * star (rayValue ξ.val b)) *
        (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) := by ring
    _ = ((mobius a : ℂ) * G (idealClass c a)) *
        ((mobius b : ℂ) * sexticSymbol b (-1) * star (G (idealClass c b))) *
        (rayValue ξ.val a * star (rayValue ξ.val b)) * R (idealClass c a) (idealClass c b) := by
      rw [hga, hbminus, hcross]
    _ = (mobius a : ℂ) * (mobius b : ℂ) * (rayValue ξ.val a * star (rayValue ξ.val b)) *
        (sexticSymbol b (-1) * star (G (idealClass c b)) * G (idealClass c a) *
          R (idealClass c a) (idealClass c b)) := by ring
    _ = _ := by rw [hq]

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
theorem first_transfer_one_le_normIdeal {a : Ideal O} (ha : a ≠ ⊥) :
    1 ≤ normIdeal a := by
  have h : 1 ≤ a.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h => ha (Ideal.absNorm_eq_zero_iff.mp h))
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast h

theorem first_transfer_normIdeal_le_of_dvd {d C : Ideal O}
    (hC : C ≠ ⊥) (hd : d ∣ C) : normIdeal d ≤ normIdeal C := by
  have hpos : 0 < C.absNorm := Nat.pos_of_ne_zero
    (fun h => hC (Ideal.absNorm_eq_zero_iff.mp h))
  change (d.absNorm : ℝ) ≤ (C.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)

theorem first_transfer_divisors_finite {C : Ideal O} (hC : C ≠ ⊥) :
    {d : Ideal O | d ∣ C}.Finite :=
  (finite_normIdeal_le (normIdeal C)).subset
    (fun _ hd => first_transfer_normIdeal_le_of_dvd hC hd)


end QRHShort.CloudBatch.SecondCoprime


/-!
Finite support and the exact zero/nonzero-frequency split of the literal
Poisson right-hand side. The original row equality is used only through the
explicit PoissonStatement premise. No zero-frequency evaluation is assumed.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_poisson_outsideRadical_ne_bot (S : Finset (Ideal O)) (r : Ideal O) :
    outsideRadical S r ≠ ⊥ := by
  unfold outsideRadical
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  apply UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
  have hp := (Finset.mem_filter.mp hP).1
  simpa only [primeFactors, Multiset.mem_toFinset] using hp

def firstTransferPoissonDivisors (r : Ideal O) : Finset (Ideal O) :=
  (first_transfer_divisors_finite (first_transfer_poisson_outsideRadical_ne_bot ∅ r)).toFinset

theorem mem_firstTransferPoissonDivisors {r d : Ideal O} :
    d ∈ firstTransferPoissonDivisors r ↔ d ∣ outsideRadical ∅ r := by
  simp only [firstTransferPoissonDivisors, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

def firstTransferPoissonDivisorCoefficient (χ : PrimitiveResidueCharacter) (d : Ideal O) : ℂ :=
  (mobius d : ℂ) * χ.value (chosenGenerator d) / (normIdeal d : ℂ)

def firstTransferPoissonDualTerm (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    (H : ℝ) (d : Ideal O) (h : O) : ℂ :=
  star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
    (H * normElement h / (normIdeal d * normIdeal χ.modulus))

def firstTransferPoissonFrequencies (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    (H : ℝ) (d : Ideal O) : Finset O :=
  (finite_normElement_le (Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H)).toFinset.erase 0

theorem mem_firstTransferPoissonFrequencies {χ : PrimitiveResidueCharacter} {Φ : RowWeight}
    {H : ℝ} {d : Ideal O} {h : O} :
    h ∈ firstTransferPoissonFrequencies χ Φ H d ↔
      h ≠ 0 ∧ normElement h ≤ Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H := by
  simp only [firstTransferPoissonFrequencies, Finset.mem_erase, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, ne_eq]

theorem first_transfer_poisson_dual_support (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    Function.support (firstTransferPoissonDualTerm χ Φ H d) ⊆
      {h : O | normElement h ≤ Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H} := by
  intro h hh
  have hden : 0 < normIdeal d * normIdeal χ.modulus :=
    mul_pos (normIdeal_pos hd) (normIdeal_pos χ.modulus_ne_bot)
  have hfourier : radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal d * normIdeal χ.modulus)) ≠ 0 := by
    intro hz
    exact hh (by simp only [firstTransferPoissonDualTerm, hz, mul_zero])
  have hx : 0 ≤ H * normElement h / (normIdeal d * normIdeal χ.modulus) :=
    div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _)) hden.le
  have hcap := (Φ.fourier_support ⟨hfourier, hx⟩).2
  apply (le_div_iff₀ hH).mpr
  calc
    normElement h * H = H * normElement h := mul_comm _ _
    _ ≤ Φ.fourierCap * (normIdeal d * normIdeal χ.modulus) := (div_le_iff₀ hden).mp hcap
    _ = Φ.fourierCap * normIdeal d * normIdeal χ.modulus := by ring

theorem first_transfer_poisson_dual_hasFiniteSupport (χ : PrimitiveResidueCharacter)
    (Φ : RowWeight) {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    Function.HasFiniteSupport (firstTransferPoissonDualTerm χ Φ H d) :=
  (finite_normElement_le (Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H)).subset
    (first_transfer_poisson_dual_support χ Φ hH hd)

theorem first_transfer_poisson_dual_summable (χ : PrimitiveResidueCharacter)
    (Φ : RowWeight) {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    Summable (firstTransferPoissonDualTerm χ Φ H d) :=
  summable_of_hasFiniteSupport (first_transfer_poisson_dual_hasFiniteSupport χ Φ hH hd)

theorem first_transfer_poisson_dual_zero (χ : PrimitiveResidueCharacter)
    (Φ : RowWeight) (H : ℝ) (d : Ideal O) :
    firstTransferPoissonDualTerm χ Φ H d 0 =
      star (χ.value 0) * radialFourier (fun x => (Φ.value x : ℂ)) 0 := by
  simp only [firstTransferPoissonDualTerm, normElement, principal, Ideal.span_singleton_zero,
    normIdeal, Ideal.absNorm_bot, Nat.cast_zero, mul_zero, zero_div]

theorem first_transfer_poisson_dual_split (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    (∑' h : O, firstTransferPoissonDualTerm χ Φ H d h) =
      star (χ.value 0) * radialFourier (fun x => (Φ.value x : ℂ)) 0 +
        ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d,
          firstTransferPoissonDualTerm χ Φ H d h := by
  have hs := first_transfer_poisson_dual_summable χ Φ hH hd
  have hzero (h : O) (hh : h ∉ firstTransferPoissonFrequencies χ Φ H d) :
      (if h = 0 then 0 else firstTransferPoissonDualTerm χ Φ H d h) = 0 := by
    by_cases hh0 : h = 0
    · rw [if_pos hh0]
    · rw [if_neg hh0]
      by_contra hne
      exact hh (mem_firstTransferPoissonFrequencies.mpr
        ⟨hh0, first_transfer_poisson_dual_support χ Φ hH hd hne⟩)
  have htail : (∑' h : O, if h = 0 then 0 else firstTransferPoissonDualTerm χ Φ H d h) =
      ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d, firstTransferPoissonDualTerm χ Φ H d h := by
    rw [tsum_eq_sum hzero]
    apply Finset.sum_congr rfl
    intro h hh
    rw [if_neg (mem_firstTransferPoissonFrequencies.mp hh).1]
  rw [hs.tsum_eq_add_tsum_ite 0, first_transfer_poisson_dual_zero, htail]

theorem first_transfer_poisson_divisor_hasFiniteSupport (r : Ideal O) (v : Ideal O → ℂ) :
    Function.HasFiniteSupport (fun d : Ideal O =>
      if d ∣ outsideRadical ∅ r then v d else 0) := by
  apply (firstTransferPoissonDivisors r).finite_toSet.subset
  intro d hd
  by_cases hdiv : d ∣ outsideRadical ∅ r
  · exact mem_firstTransferPoissonDivisors.mpr hdiv
  · exact False.elim (hd (if_neg hdiv))

theorem first_transfer_poisson_divisor_tsum_eq_sum (r : Ideal O) (v : Ideal O → ℂ) :
    (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then v d else 0) =
      ∑ d ∈ firstTransferPoissonDivisors r, v d := by
  have hzero (d : Ideal O) (hd : d ∉ firstTransferPoissonDivisors r) :
      (if d ∣ outsideRadical ∅ r then v d else 0) = 0 := by
    apply if_neg
    exact fun hdiv => hd (mem_firstTransferPoissonDivisors.mpr hdiv)
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro d hd
  rw [if_pos (mem_firstTransferPoissonDivisors.mp hd)]

theorem first_transfer_poisson_dual_joint_hasFiniteSupport (χ : PrimitiveResidueCharacter)
    (r : Ideal O) (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    Function.HasFiniteSupport (fun p : Ideal O × O =>
      if p.1 ∣ outsideRadical ∅ r then
        firstTransferPoissonDivisorCoefficient χ p.1 * firstTransferPoissonDualTerm χ Φ H p.1 p.2
      else 0) := by
  have hfinite := (first_transfer_divisors_finite
    (first_transfer_poisson_outsideRadical_ne_bot ∅ r)).biUnion (fun d _ =>
      (finite_normElement_le (Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H)).image
        (fun h => (d, h)))
  apply hfinite.subset
  rintro ⟨d, h⟩ hp
  have hd : d ∣ outsideRadical ∅ r := by
    by_contra hnot
    exact hp (if_neg hnot)
  have hd0 : d ≠ ⊥ := ne_zero_of_dvd_ne_zero
    (first_transfer_poisson_outsideRadical_ne_bot ∅ r) hd
  have hdual : firstTransferPoissonDualTerm χ Φ H d h ≠ 0 := by
    intro hz
    exact hp (by simp only [if_pos hd, hz, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨d, hd, ⟨h,
    first_transfer_poisson_dual_support χ Φ hH hd0 hdual, rfl⟩⟩

theorem first_transfer_poisson_dual_joint_summable (χ : PrimitiveResidueCharacter)
    (r : Ideal O) (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    Summable (fun p : Ideal O × O =>
      if p.1 ∣ outsideRadical ∅ r then
        firstTransferPoissonDivisorCoefficient χ p.1 * firstTransferPoissonDualTerm χ Φ H p.1 p.2
      else 0) :=
  summable_of_hasFiniteSupport (first_transfer_poisson_dual_joint_hasFiniteSupport χ r Φ hH)

theorem first_transfer_poisson_truncation (hp : PoissonStatement)
    (χ : PrimitiveResidueCharacter) (r : Ideal O) (Φ : RowWeight)
    {H : ℝ} (hr : r ≠ ⊥) (hH : 0 < H) :
    (∑' k : O, if IsRelPrime (principal k) r then
      χ.value k * (Φ.value (normElement k / H) : ℂ) else 0) =
      poissonZeroTerm χ r (fun x => (Φ.value x : ℂ)) H +
        H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
          ∑ d ∈ firstTransferPoissonDivisors r,
            firstTransferPoissonDivisorCoefficient χ d *
              ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d,
                firstTransferPoissonDualTerm χ Φ H d h := by
  rw [hp χ r (fun x => (Φ.value x : ℂ)) H hr hH Φ.schwartz]
  change H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
      (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
        firstTransferPoissonDivisorCoefficient χ d * ∑' h : O, firstTransferPoissonDualTerm χ Φ H d h
        else 0) = _
  rw [first_transfer_poisson_divisor_tsum_eq_sum]
  have hsplit : (∑ d ∈ firstTransferPoissonDivisors r,
      firstTransferPoissonDivisorCoefficient χ d * ∑' h : O, firstTransferPoissonDualTerm χ Φ H d h) =
      (∑ d ∈ firstTransferPoissonDivisors r, firstTransferPoissonDivisorCoefficient χ d *
        (star (χ.value 0) * radialFourier (fun x => (Φ.value x : ℂ)) 0)) +
      ∑ d ∈ firstTransferPoissonDivisors r, firstTransferPoissonDivisorCoefficient χ d *
        ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d, firstTransferPoissonDualTerm χ Φ H d h := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [first_transfer_poisson_dual_split χ Φ hH (ne_zero_of_dvd_ne_zero
      (first_transfer_poisson_outsideRadical_ne_bot ∅ r) (mem_firstTransferPoissonDivisors.mp hd)), mul_add]
  rw [hsplit, mul_add]
  congr 1
  unfold poissonZeroTerm
  rw [first_transfer_poisson_divisor_tsum_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  unfold firstTransferPoissonDivisorCoefficient
  ring

end QRHShort.CloudBatch.SecondCoprime


/-!
Poisson applied to the literal common-factor row. The common symbol supplies
the exclusion ideal, while the two residual symbols are the actual primitive
paired character. The Gauss factor remains that character's literal Gauss sum.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_outsideRadical_eq_self_of_squarefree {C : Ideal O}
    (hC : C ≠ ⊥) (hsq : Squarefree C) : outsideRadical ∅ C = C := by
  have hnodup := (squarefree_iff_nodup_normalizedFactors hC).mp hsq
  have hfilter : (primeFactors C).filter (fun P => P ∉ (∅ : Finset (Ideal O))) =
      primeFactors C := by simp
  unfold outsideRadical
  rw [hfilter]
  change ((normalizedFactors C).dedup.map (fun P => P)).prod = C
  rw [Multiset.map_id', Multiset.dedup_eq_self.mpr hnodup]
  exact Ideal.prod_normalizedFactors_eq_self hC

theorem first_transfer_poisson_divisors_eq_squarefree {C : Ideal O}
    (hC : C ≠ ⊥) (hsq : Squarefree C) :
    firstTransferPoissonDivisors C = (first_transfer_divisors_finite hC).toFinset := by
  ext d
  simp only [mem_firstTransferPoissonDivisors,
    first_transfer_outsideRadical_eq_self_of_squarefree hC hsq, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]

theorem first_transfer_poisson_divisor_generator (c : ArithmeticContext) {C d : Ideal O}
    (hC : Outside c.S C) (hd : d ∣ C) : chosenGenerator d = primaryGenerator d :=
  first_transfer_chosenGenerator_eq_primaryGenerator c (first_transfer_outside_of_dvd c hC hd)

theorem first_transfer_poisson_gcd_symbol_row (c : ArithmeticContext) {C a b : Ideal O}
    (hC : Outside c.S C) (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (k : O) :
    sexticSymbol (C * a) k * star (sexticSymbol (C * b) k) =
      if IsRelPrime (principal k) C then
        (firstTransferPrimitivePairedCharacter c ha hb hab).value k else 0 := by
  rw [first_transfer_sexticSymbol_mul, first_transfer_sexticSymbol_mul, star_mul]
  calc
    (sexticSymbol C k * sexticSymbol a k) * (star (sexticSymbol b k) * star (sexticSymbol C k)) =
        (sexticSymbol C k * star (sexticSymbol C k)) *
          (sexticSymbol a k * star (sexticSymbol b k)) := by ring
    _ = _ := by
      rw [first_transfer_sexticSymbol_mul_star c hC k,
        firstTransferPrimitivePairedCharacter_value]
      split_ifs <;> simp only [one_mul, zero_mul]

theorem first_transfer_poisson_gcd_row_eq (c : ArithmeticContext) {C a b : Ideal O}
    (hC : Outside c.S C) (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (Φ : RowWeight) (H : ℝ) :
    (∑' k : O, (Φ.value (normElement k / H) : ℂ) *
      sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) =
      ∑' k : O, if IsRelPrime (principal k) C then
        (firstTransferPrimitivePairedCharacter c ha hb hab).value k *
          (Φ.value (normElement k / H) : ℂ) else 0 := by
  apply tsum_congr
  intro k
  calc
    _ = (Φ.value (normElement k / H) : ℂ) *
        (sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) := by ring
    _ = _ := by
      rw [first_transfer_poisson_gcd_symbol_row c hC ha hb hab k]
      split_ifs
      · ring
      · simp only [mul_zero]

theorem first_transfer_poisson_gcd_row_truncation (hp : PoissonStatement)
    (c : ArithmeticContext) {C a b : Ideal O} (hC : SquarefreeOutside c.S C)
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b)
    (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    let χ := firstTransferPrimitivePairedCharacter c ha hb hab
    (∑' k : O, (Φ.value (normElement k / H) : ℂ) *
      sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) =
      poissonZeroTerm χ C (fun x => (Φ.value x : ℂ)) H +
        H * χ.gauss / (Real.sqrt (normIdeal (a * b)) : ℂ) *
          ∑ d ∈ (first_transfer_divisors_finite hC.1.1).toFinset,
            ((mobius d : ℂ) * χ.value (primaryGenerator d) / (normIdeal d : ℂ)) *
              ∑ h ∈ (finite_normElement_le
                (Φ.fourierCap * normIdeal d * normIdeal (a * b) / H)).toFinset.erase 0,
                star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
                  (H * normElement h / (normIdeal d * normIdeal (a * b))) := by
  dsimp only
  rw [first_transfer_poisson_gcd_row_eq c hC.1 ha hb hab Φ H,
    first_transfer_poisson_truncation hp (firstTransferPrimitivePairedCharacter c ha hb hab)
      C Φ hC.1.1 hH,
    first_transfer_poisson_divisors_eq_squarefree hC.1.1 hC.2]
  congr 1
  unfold firstTransferPoissonDivisorCoefficient firstTransferPoissonFrequencies firstTransferPoissonDualTerm
  simp only [firstTransferPrimitivePairedCharacter_modulus]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdC : d ∣ C := (first_transfer_divisors_finite hC.1.1).mem_toFinset.mp hd
  rw [first_transfer_poisson_divisor_generator c hC.1 hdC]

end QRHShort.CloudBatch.SecondCoprime


/-!
Finite divisor cancellation for the actual ideals of the fixed cyclotomic field.
The finite divisor set is obtained from unique factorization; the zero ideal is
excluded because its divisor set is infinite. No analytic identity is assumed.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch.SecondCoprime

/-- All ideal divisors of a nonzero ideal. -/
def idealDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) := by
  exact (first_transfer_divisors_finite hn).toFinset

@[simp] theorem mem_idealDivisors (n : Ideal O) (hn : n ≠ ⊥) (d : Ideal O) :
    d ∈ idealDivisors n hn ↔ d ∣ n := by
  simp [idealDivisors]

private theorem normalizedFactors_finset_prod (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : normalizedFactors (∏ p ∈ s, p) = s.val := by
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
    (normalizedFactors_prod_of_prime (m := s.val) hp)

private theorem prime_finset_prod_ne_zero (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : (∏ p ∈ s, p) ≠ (0 : Ideal O) := by
  exact Finset.prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)

private theorem prime_finset_prod_squarefree (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : Squarefree (∏ p ∈ s, p) := by
  apply (squarefree_iff_nodup_normalizedFactors
    (prime_finset_prod_ne_zero s hp)).mpr
  rw [normalizedFactors_finset_prod s hp]
  exact s.nodup

/-- A finite set of distinct prime ideals gives the usual Möbius sign. -/
theorem prime_finset_mobius (s : Finset (Ideal O)) (hp : ∀ p ∈ s, Prime p) :
    mobius (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  rw [mobius, (prime_finset_prod_squarefree s hp).moebius_eq,
    factors_eq_normalizedFactors, normalizedFactors_finset_prod s hp] <;> rfl

/-- Every squarefree divisor is the product of a subset of the prime support. -/
theorem squarefree_divisor_eq_prod {n d : Ideal O} (hn : n ≠ ⊥)
    (hd : d ∣ n) (hsq : Squarefree d) :
    ∃ t ⊆ (normalizedFactors n).toFinset, (∏ p ∈ t, p) = d := by
  have hd0 : d ≠ 0 := by
    intro h
    apply hn
    exact (show n = 0 from by simpa only [h, zero_dvd_iff] using hd).trans Ideal.zero_eq_bot
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn).mp hd
  have hnodup := (squarefree_iff_nodup_normalizedFactors hd0).mp hsq
  refine ⟨(normalizedFactors d).toFinset, ?_, ?_⟩
  · intro p hp
    exact Multiset.mem_toFinset.mpr
      (Multiset.subset_of_le hle (Multiset.mem_toFinset.mp hp))
  · calc
      (∏ p ∈ (normalizedFactors d).toFinset, p) =
          (normalizedFactors d).toFinset.val.prod :=
        (Finset.prod_val _).symm
      _ = (normalizedFactors d).prod := by
        rw [Multiset.toFinset_val, hnodup.dedup]
      _ = d := Ideal.prod_normalizedFactors_eq_self hd0

private theorem primeSubset_prod_properties {n : Ideal O} (hn : n ≠ ⊥)
    {t : Finset (Ideal O)} (ht : t ⊆ (normalizedFactors n).toFinset) :
    (∏ p ∈ t, p) ∣ n ∧ Squarefree (∏ p ∈ t, p) := by
  have hp : ∀ p ∈ t, Prime p := fun p h =>
    prime_of_normalized_factor p (Multiset.mem_toFinset.mp (ht h))
  refine ⟨?_, prime_finset_prod_squarefree t hp⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors
    (prime_finset_prod_ne_zero t hp) hn).mpr
  rw [normalizedFactors_finset_prod t hp]
  apply (Multiset.le_iff_subset t.nodup).mpr
  intro p h
  exact Multiset.mem_toFinset.mp (ht h)

private theorem primeSubset_prod_injective {n : Ideal O}
    {t u : Finset (Ideal O)} (ht : t ⊆ (normalizedFactors n).toFinset)
    (hu : u ⊆ (normalizedFactors n).toFinset)
    (h : (∏ p ∈ t, p) = ∏ p ∈ u, p) : t = u := by
  have hpt : ∀ p ∈ t, Prime p := fun p hp =>
    prime_of_normalized_factor p (Multiset.mem_toFinset.mp (ht hp))
  have hpu : ∀ p ∈ u, Prime p := fun p hp =>
    prime_of_normalized_factor p (Multiset.mem_toFinset.mp (hu hp))
  apply Finset.val_injective
  rw [← normalizedFactors_finset_prod t hpt, ← normalizedFactors_finset_prod u hpu]
  exact congrArg normalizedFactors h

/-- Multiplicative weights turn finite Möbius divisor sums into Euler factors. -/
theorem sum_idealDivisors_mobius_mul (n : Ideal O) (hn : n ≠ ⊥)
    (f : Ideal O →* ℂ) :
    (∑ d ∈ idealDivisors n hn, (mobius d : ℂ) * f d) =
      ∏ p ∈ (normalizedFactors n).toFinset, (1 - f p) := by
  let P := (normalizedFactors n).toFinset
  have hfilter : (∑ d ∈ idealDivisors n hn, (mobius d : ℂ) * f d) =
      ∑ d ∈ (idealDivisors n hn).filter Squarefree, (mobius d : ℂ) * f d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hsq : Squarefree d
    · simp only [hsq, if_pos]
    · simp only [hsq, if_neg, mobius, moebius_of_not_squarefree hsq,
        Int.cast_zero, zero_mul, ite_false]
  have hsum : (∑ t ∈ P.powerset, (-1 : ℂ) ^ t.card * ∏ p ∈ t, f p) =
      ∑ d ∈ (idealDivisors n hn).filter Squarefree, (mobius d : ℂ) * f d := by
    apply Finset.sum_bij (fun t _ => ∏ p ∈ t, p)
    · intro t ht
      rcases primeSubset_prod_properties hn (Finset.mem_powerset.mp ht) with ⟨hd, hsq⟩
      exact Finset.mem_filter.mpr ⟨(mem_idealDivisors n hn _).mpr hd, hsq⟩
    · intro t ht u hu h
      exact primeSubset_prod_injective (Finset.mem_powerset.mp ht)
        (Finset.mem_powerset.mp hu) h
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hsq⟩
      obtain ⟨t, ht, hprod⟩ := squarefree_divisor_eq_prod hn
        ((mem_idealDivisors n hn d).mp hd) hsq
      exact ⟨t, Finset.mem_powerset.mpr ht, hprod⟩
    · intro t ht
      have hp : ∀ p ∈ t, Prime p := fun p h =>
        prime_of_normalized_factor p
          (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp ht) h))
      have hsign : (mobius (∏ p ∈ t, p) : ℂ) = (-1 : ℂ) ^ t.card := by
        exact_mod_cast prime_finset_mobius t hp
      rw [hsign, map_prod]
  have hprod : (∏ p ∈ P, (1 - f p)) =
      ∑ t ∈ P.powerset, (-1 : ℂ) ^ t.card * ∏ p ∈ t, f p := by
    simpa only [Finset.prod_const_one, mul_one] using
      (Finset.prod_sub (fun _ : Ideal O => (1 : ℂ)) f P)
  exact hfilter.trans (hsum.symm.trans hprod.symm)

/-- The squarefree ideal generated by a finite prime set has exactly these factors. -/
theorem sum_primeProductDivisors_mobius_mul (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hn : (∏ P ∈ S, P) ≠ ⊥) (f : Ideal O →* ℂ) :
    (∑ d ∈ idealDivisors (∏ P ∈ S, P) hn, (mobius d : ℂ) * f d) =
      ∏ P ∈ S, (1 - f P) := by
  simpa only [normalizedFactors_finset_prod S hS, Finset.val_toFinset] using
    sum_idealDivisors_mobius_mul (∏ P ∈ S, P) hn f

/-- Ideal-indexed form of the finite weighted divisor identity. -/
theorem tsum_ideal_dvd_mobius_mul (n : Ideal O) (hn : n ≠ ⊥)
    (f : Ideal O →* ℂ) :
    (∑' d : Ideal O, if d ∣ n then (mobius d : ℂ) * f d else 0) =
      ∏ p ∈ (normalizedFactors n).toFinset, (1 - f p) := by
  rw [tsum_eq_sum (s := idealDivisors n hn) (fun d hd =>
    if_neg (fun h => hd ((mem_idealDivisors n hn d).mpr h)))]
  calc
    (∑ d ∈ idealDivisors n hn, if d ∣ n then (mobius d : ℂ) * f d else 0) =
        ∑ d ∈ idealDivisors n hn, (mobius d : ℂ) * f d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact if_pos ((mem_idealDivisors n hn d).mp hd)
    _ = _ := sum_idealDivisors_mobius_mul n hn f

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
/-- The nonprincipal zero-frequency term vanishes, including the distinction
between a nontrivial quotient ring and the modulus-one quotient. -/
theorem primitive_character_zero_of_nonprincipal (χ : PrimitiveResidueCharacter)
    (hχ : χ.character ≠ 1) : star (χ.value 0) = 0 := by
  rcases subsingleton_or_nontrivial (O ⧸ χ.modulus) with hsub | hnontrivial
  · have hprincipal : χ.character = 1 := by
      apply MulChar.equivToUnitHom.injective
      ext x
      have hx : (x : O ⧸ χ.modulus) = 1 := hsub.elim _ _
      simp only [MulChar.coe_equivToUnitHom, hx, map_one]
    exact (hχ hprincipal).elim
  · letI := hnontrivial
    simp [PrimitiveResidueCharacter.value, MulChar.map_zero]

@[simp] theorem chosenGenerator_top : chosenGenerator (⊤ : Ideal O) = 1 := by
  have hfac : normalizedFactors (⊤ : Ideal O) = 0 := by
    rw [← Ideal.one_eq_top]
    exact normalizedFactors_one
  simp only [chosenGenerator, if_neg top_ne_bot, hfac, Multiset.map_zero, Multiset.prod_zero]

theorem primitive_character_value_of_modulus_top (χ : PrimitiveResidueCharacter)
    (hmod : χ.modulus = ⊤) (a : O) : χ.value a = 1 := by
  letI : Subsingleton (O ⧸ χ.modulus) := Ideal.Quotient.subsingleton_iff.mpr hmod
  have hmk : Ideal.Quotient.mk χ.modulus a = 1 := Subsingleton.elim _ _
  simp only [PrimitiveResidueCharacter.value, hmk, map_one]

/-- The modulus-one Gauss sum equals one for the actual representatives in
its definition, since the additive character is trivial on the lattice. -/
theorem primitive_gauss_of_modulus_top (χ : PrimitiveResidueCharacter)
    (hmod : χ.modulus = ⊤) : χ.gauss = 1 := by
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  letI : Subsingleton (O ⧸ χ.modulus) := Ideal.Quotient.subsingleton_iff.mpr hmod
  have hnorm : normIdeal χ.modulus = 1 := by simp [hmod, normIdeal]
  have hgen : embedding (chosenGenerator χ.modulus) = 1 := by
    rw [hmod, chosenGenerator_top, embedding_one]
  have hvalue (x : O ⧸ χ.modulus) : χ.character x = 1 := by
    have hx : x = 1 := Subsingleton.elim _ _
    rw [hx, map_one]
  letI : Unique (O ⧸ χ.modulus) := Unique.mk' (O ⧸ χ.modulus)
  simp [PrimitiveResidueCharacter.gauss, hnorm, hgen, hvalue,
    first_transfer_additiveCharacter_embedding]


end QRHShort.CloudBatch.SecondCoprime


/-! Both zero-frequency assertions in `lem:poisson`, paper2.tex:875--921.
The principal term uses an actual finite ideal-divisor Euler identity.
-/

noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.CloudBatch.SecondCoprime

def reciprocalIdealNorm : Ideal O →* ℂ where
  toFun d := (normIdeal d : ℂ)⁻¹
  map_one' := by simp [normIdeal]
  map_mul' := by
    intro a b
    simp [normIdeal, map_mul, mul_inv_rev, mul_comm]

theorem outsideRadical_empty_ne_bot (r : Ideal O) :
    outsideRadical ∅ r ≠ ⊥ := by
  change (∏ P ∈ (primeFactors r).filter (fun P => P ∉ ∅), P) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  have hp : Prime P := prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)
  exact hp.ne_zero

theorem tsum_radical_mobius_div_norm (r : Ideal O) :
    (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
      (mobius d : ℂ) / (normIdeal d : ℂ) else 0) =
        ∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹) := by
  let n := outsideRadical ∅ r
  have hn : n ≠ ⊥ := outsideRadical_empty_ne_bot r
  have hS : ∀ P ∈ primeFactors r, Prime P := fun P hP =>
    prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hprod : n = ∏ P ∈ primeFactors r, P := by
    simp [n, outsideRadical]
  have hsum := sum_primeProductDivisors_mobius_mul
    (primeFactors r) hS (hprod ▸ hn) reciprocalIdealNorm
  have hideal : idealDivisors (∏ P ∈ primeFactors r, P) (hprod ▸ hn) = idealDivisors n hn := by
    ext d
    simp only [mem_idealDivisors, ← hprod]
  rw [hideal] at hsum
  rw [tsum_eq_sum (s := idealDivisors n hn) (fun d hd =>
    if_neg (fun h => hd ((mem_idealDivisors n hn d).mpr h)))]
  calc
    _ = ∑ d ∈ idealDivisors n hn, (mobius d : ℂ) * reciprocalIdealNorm d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [if_pos ((mem_idealDivisors n hn d).mp hd)]
      rfl
    _ = _ := hsum

theorem poissonZeroTerm_eq_euler (χ : PrimitiveResidueCharacter)
    (hmod : χ.modulus = ⊤) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) :
    poissonZeroTerm χ r Φ H = H * radialFourier Φ 0 *
      ∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹) := by
  have hnorm : normIdeal χ.modulus = 1 := by simp [hmod, normIdeal]
  have hval := primitive_character_value_of_modulus_top χ hmod
  unfold poissonZeroTerm
  rw [primitive_gauss_of_modulus_top χ hmod, hnorm]
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one, div_one, hval,
    star_one, mul_one]
  have htsum : (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
      (mobius d : ℂ) / (normIdeal d : ℂ) * radialFourier Φ 0 else 0) =
      (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
        (mobius d : ℂ) / (normIdeal d : ℂ) else 0) * radialFourier Φ 0 := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro d
    split_ifs <;> simp
  rw [htsum, tsum_radical_mobius_div_norm]
  ring

/-- The full zero-frequency assertion is proved independently of Poisson
summation itself. No arithmetic reciprocity relation is assumed here. -/
theorem poisson_zero_statement : PoissonZeroStatement := by
  constructor
  · exact primitive_character_zero_of_nonprincipal
  · intro χ r Φ H _hχ hmod _hr _hH _hΦ
    exact poissonZeroTerm_eq_euler χ hmod r Φ H

end QRHShort.CloudBatch.SecondCoprime


/-! The actual Poisson zero term has only a principal contribution.  Its
Euler product has norm at most one.  The Poisson-zero statement is retained
as an explicit permitted premise; no additive-character theorem is imported. -/

noncomputable section

open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_primitive_character_eq_one_iff (χ : PrimitiveResidueCharacter) :
    χ.character = 1 ↔ χ.modulus = ⊤ := by
  constructor
  · intro hχ
    apply Eq.symm
    apply χ.primitive ⊤ top_ne_bot le_top
    refine ⟨1, ?_⟩
    intro a ha
    rw [hχ, MulChar.one_apply ha]
    let : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have hx : Ideal.Quotient.mk (⊤ : Ideal O) a = 1 := Subsingleton.elim _ _
    rw [hx, map_one]
  · intro hmod
    let : Subsingleton (O ⧸ χ.modulus) := Ideal.Quotient.subsingleton_iff.mpr hmod
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    simp only [hx, Units.val_one, map_one]

theorem first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal
    (hz : PoissonZeroStatement) (χ : PrimitiveResidueCharacter) (hχ : χ.character ≠ 1)
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) : poissonZeroTerm χ r Φ H = 0 := by
  unfold poissonZeroTerm
  simp only [hz.1 χ hχ, mul_zero, zero_mul, ite_self, tsum_zero]

theorem first_transfer_poissonZeroTerm_eq_zero_of_modulus_ne_top
    (hz : PoissonZeroStatement) (χ : PrimitiveResidueCharacter) (hχ : χ.modulus ≠ ⊤)
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) : poissonZeroTerm χ r Φ H = 0 :=
  first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal hz χ
    (mt (first_transfer_primitive_character_eq_one_iff χ).mp hχ) r Φ H

theorem first_transfer_zero_contribution_one_le_normIdeal {a : Ideal O} (ha : a ≠ ⊥) :
    1 ≤ normIdeal a := by
  let : Finite (O ⧸ a) := Ring.HasFiniteQuotients.finiteQuotient ha
  have hN : a.absNorm ≠ 0 := (Ideal.absNorm_ne_zero_iff a).mpr inferInstance
  have hNat : 1 ≤ a.absNorm := Nat.one_le_iff_ne_zero.mpr hN
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast hNat

theorem first_transfer_zero_euler_factor_norm_le_one {P : Ideal O} (hP : P ≠ ⊥) :
    ‖(1 : ℂ) - (normIdeal P : ℂ)⁻¹‖ ≤ 1 := by
  have hN := first_transfer_zero_contribution_one_le_normIdeal hP
  have hN0 : 0 ≤ normIdeal P := le_trans zero_le_one hN
  have hi0 : 0 ≤ (normIdeal P)⁻¹ := inv_nonneg.mpr hN0
  have hi1 : (normIdeal P)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have hsub : 0 ≤ 1 - (normIdeal P)⁻¹ := sub_nonneg.mpr hi1
  have hcast : (1 : ℂ) - (normIdeal P : ℂ)⁻¹ =
      ((1 - (normIdeal P)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsub]
  exact sub_le_self _ hi0

theorem first_transfer_zero_euler_product_norm_le_one (r : Ideal O) :
    ‖∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  have hp : Prime P := prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  exact first_transfer_zero_euler_factor_norm_le_one hp.ne_zero

theorem first_transfer_poissonZeroTerm_norm_le (hz : PoissonZeroStatement)
    (χ : PrimitiveResidueCharacter) (r : Ideal O) (hr : r ≠ ⊥)
    (Φ : RowWeight) (H : ℝ) (hH : 0 < H) :
    ‖poissonZeroTerm χ r (fun x => (Φ.value x : ℂ)) H‖ ≤
      H * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ := by
  by_cases hχ : χ.character = 1
  · rw [hz.2 χ r (fun x => (Φ.value x : ℂ)) H hχ
      ((first_transfer_primitive_character_eq_one_iff χ).mp hχ) hr hH Φ.schwartz]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    exact mul_le_of_le_one_right (mul_nonneg hH.le (norm_nonneg _))
      (first_transfer_zero_euler_product_norm_le_one r)
  · rw [first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal hz χ hχ, norm_zero]
    exact mul_nonneg hH.le (norm_nonneg _)

end QRHShort.CloudBatch.SecondCoprime


/-! For the primitive paired row, zero frequency is supported only at the
pair of unit denominator ideals. -/

noncomputable section

open Classical

namespace QRHShort.CloudBatch.SecondCoprime

theorem first_transfer_paired_character_eq_one_iff (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    (firstTransferPrimitivePairedCharacter c ha hb hab).character = 1 ↔
      a = ⊤ ∧ b = ⊤ := by
  rw [first_transfer_primitive_character_eq_one_iff,
    firstTransferPrimitivePairedCharacter_modulus]
  constructor
  · intro h
    exact ⟨top_unique (h ▸ (show a * b ≤ a from Ideal.mul_le_left)),
      top_unique (h ▸ (show a * b ≤ b from Ideal.mul_le_right))⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem first_transfer_paired_poissonZeroTerm_eq_zero (hz : PoissonZeroStatement)
    (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hpair : ¬ (a = ⊤ ∧ b = ⊤))
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) :
    poissonZeroTerm (firstTransferPrimitivePairedCharacter c ha hb hab) r Φ H = 0 := by
  apply first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal hz
  exact mt (first_transfer_paired_character_eq_one_iff c ha hb hab).mp hpair

theorem first_transfer_paired_poissonZeroTerm_ne_zero_imp (hz : PoissonZeroStatement)
    (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ)
    (hterm : poissonZeroTerm (firstTransferPrimitivePairedCharacter c ha hb hab) r Φ H ≠ 0) :
    a = ⊤ ∧ b = ⊤ := by
  by_contra hpair
  exact hterm (first_transfer_paired_poissonZeroTerm_eq_zero hz c ha hb hab hpair r Φ H)

theorem first_transfer_paired_poissonZeroTerm_norm_le_indicator
    (hz : PoissonZeroStatement) (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (r : Ideal O) (hr : r ≠ ⊥)
    (Φ : RowWeight) (H : ℝ) (hH : 0 < H) :
    ‖poissonZeroTerm (firstTransferPrimitivePairedCharacter c ha hb hab)
      r (fun x => (Φ.value x : ℂ)) H‖ ≤
      if a = ⊤ ∧ b = ⊤ then
        H * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ else 0 := by
  by_cases hpair : a = ⊤ ∧ b = ⊤
  · rw [ite_eq_left hpair]
    exact first_transfer_poissonZeroTerm_norm_le hz _ r hr Φ H hH
  · rw [ite_eq_right hpair,
      first_transfer_paired_poissonZeroTerm_eq_zero hz c ha hb hab hpair, norm_zero]

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
/-- Transport the residue character along its specified modulus equality. -/
def residueAtRayModulus (c : ArithmeticContext) (ξ : RayCharacter c) :
    MulChar (O ⧸ c.rayModulus) ℂ :=
  ξ.property ▸ ξ.val.residue

theorem residueAtRayModulus_onElement (c : ArithmeticContext) (ξ : RayCharacter c)
    (x : O) :
    residueAtRayModulus c ξ (Ideal.Quotient.mk c.rayModulus x) = ξ.val.onElement x := by
  rcases ξ with ⟨⟨M, hM, r, hu⟩, h⟩
  change M = c.rayModulus at h
  subst M
  rfl

theorem residueAtRayModulus_unit_trivial (c : ArithmeticContext) (ξ : RayCharacter c)
    (u : Oˣ) :
    residueAtRayModulus c ξ (Ideal.Quotient.mk c.rayModulus (u : O)) = 1 := by
  rw [residueAtRayModulus_onElement]
  exact ξ.val.unit_trivial u

def rayUnitHom (c : ArithmeticContext) (ξ : RayCharacter c) :
    (O ⧸ c.rayModulus)ˣ →* ℂ where
  toFun u := residueAtRayModulus c ξ (u : O ⧸ c.rayModulus)
  map_one' := (residueAtRayModulus c ξ).map_one
  map_mul' u v := (residueAtRayModulus c ξ).map_mul u v

theorem globalUnitImage_le_rayUnitHom_ker (c : ArithmeticContext) (ξ : RayCharacter c) :
    globalUnitImage c ≤ (rayUnitHom c ξ).ker := by
  rintro u ⟨v, rfl⟩
  exact residueAtRayModulus_unit_trivial c ξ v

/-- The actual ray character descended to the quotient by global units. -/
def rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c) : RayClass c →* ℂ :=
  QuotientGroup.lift (globalUnitImage c) (rayUnitHom c ξ)
    (globalUnitImage_le_rayUnitHom_ker c ξ)

theorem rayClassCharacter_rayClass (c : ArithmeticContext) (ξ : RayCharacter c)
    {x : O} (hx : IsUnit (Ideal.Quotient.mk c.rayModulus x)) :
    rayClassCharacter c ξ (rayClass c x) = ξ.val.onElement x := by
  unfold rayClass rayClassCharacter
  rw [dite_eq_left hx, QuotientGroup.lift_mk']
  change residueAtRayModulus c ξ (hx.unit : O ⧸ c.rayModulus) = _
  rw [hx.unit_spec, residueAtRayModulus_onElement]

theorem rayValue_eq_rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c)
    {a : Ideal O} (ha : Outside c.S a) :
    rayValue ξ.val a = rayClassCharacter c ξ (idealClass c a) :=
  (rayClassCharacter_rayClass c ξ (SquarefreeReflection.primaryGenerator_unit_mod_supported c c.rayModulus c.rayModulus_ne_bot c.ray_supported ha)).symm

theorem norm_rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c)
    (z : RayClass c) : ‖rayClassCharacter c ξ z‖ = 1 := by
  let : Finite (O ⧸ c.rayModulus) := Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  let : Finite (RayClass c) := inferInstance
  exact ((rayClassCharacter c ξ).isOfFinOrder (isOfFinOrder_of_finite z)).norm_eq_one

theorem rayClassCharacter_mul_inv (c : ArithmeticContext) (ξ : RayCharacter c)
    (x y : RayClass c) :
    rayClassCharacter c ξ (x * y⁻¹) =
      rayClassCharacter c ξ x * star (rayClassCharacter c ξ y) := by
  have hinv : rayClassCharacter c ξ y⁻¹ = (rayClassCharacter c ξ y)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, hinv, Complex.inv_eq_conj (norm_rayClassCharacter c ξ y)]
  rfl


end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open scoped BigOperators
open Classical
open SecondPoissonProof

theorem outside_pow (c : ArithmeticContext) {a : Ideal O} (ha : Outside c.S a) (k : ℕ) :
    Outside c.S (a ^ k) := by
  induction k with
  | zero => simpa using first_transfer_outside_one c
  | succ k hk => simpa only [pow_succ] using
      (first_transfer_outside_mul_iff c _ _).mpr ⟨hk, ha⟩

theorem rayClass_mul {c : ArithmeticContext} {x y : O}
    (hx : IsUnit (Ideal.Quotient.mk c.rayModulus x))
    (hy : IsUnit (Ideal.Quotient.mk c.rayModulus y)) :
    rayClass c (x * y) = rayClass c x * rayClass c y := by
  have hxy : IsUnit (Ideal.Quotient.mk c.rayModulus (x * y)) := by
    simpa only [map_mul] using hx.mul hy
  unfold rayClass
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hxy]
  rw [← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  simp only [IsUnit.unit_spec, Units.val_mul, map_mul]

theorem idealClass_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    idealClass c (a * b) = idealClass c a * idealClass c b := by
  unfold idealClass
  rw [first_transfer_primaryGenerator_mul_outside c ha hb]
  exact rayClass_mul
    (SquarefreeReflection.primaryGenerator_unit_mod_supported c c.rayModulus
      c.rayModulus_ne_bot c.ray_supported ha)
    (SquarefreeReflection.primaryGenerator_unit_mod_supported c c.rayModulus
      c.rayModulus_ne_bot c.ray_supported hb)

theorem idealClass_one (c : ArithmeticContext) : idealClass c 1 = 1 := by
  have hpg : primaryGenerator (1 : Ideal O) = 1 := by
    apply first_transfer_primary_eq_of_principal_eq
      (first_transfer_primaryGenerator_spec_and_primary_outside c (first_transfer_outside_one c)).2
      (by simp [IsPrimary])
    simpa only [principal, Ideal.span_singleton_one, ← Ideal.one_eq_top] using
      (first_transfer_primaryGenerator_spec_and_primary_outside c (first_transfer_outside_one c)).1
  simp only [idealClass, hpg, rayClass, map_one, dite_eq_left isUnit_one]
  have hu : (isUnit_one : IsUnit (1 : O ⧸ c.rayModulus)).unit = 1 := by
    apply Units.ext
    exact IsUnit.unit_spec isUnit_one
  rw [hu]
  rfl

theorem idealClass_pow (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) (k : ℕ) : idealClass c (a ^ k) = idealClass c a ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using idealClass_one c
  | succ k hk => rw [pow_succ, idealClass_mul c (outside_pow c ha k) ha, hk, pow_succ]

set_option backward.isDefEq.respectTransparency false in
theorem ray_expansion_pair (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ)
    (hexp : RayExpansion c hc ξ₁ coeffs) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    rayValue ξ₁.val a * star (rayValue ξ₁.val b) *
      reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) =
      ∑' ξ : RayCharacter c, coeffs ξ * rayValue ξ.val a * star (rayValue ξ.val b) := by
  letI : Finite (O ⧸ c.rayModulus) := Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  letI : Finite (RayClass c) := inferInstance
  let m := orderOf (idealClass c b)
  have hm : 0 < m := orderOf_pos (idealClass c b)
  have hpow : idealClass c b ^ (m - 1) = (idealClass c b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_one_add_one hm.ne', pow_orderOf_eq_one]
  let n := a * b ^ (m - 1)
  have hn : Outside c.S n := (first_transfer_outside_mul_iff c _ _).mpr
    ⟨ha, outside_pow c hb _⟩
  have hcl : idealClass c n = idealClass c a * (idealClass c b)⁻¹ := by
    dsimp only [n]
    rw [idealClass_mul c ha (outside_pow c hb _), idealClass_pow c hb, hpow]
  have hray (ξ : RayCharacter c) :
      rayValue ξ.val n = rayValue ξ.val a * star (rayValue ξ.val b) := by
    rw [rayValue_eq_rayClassCharacter c ξ hn, hcl, rayClassCharacter_mul_inv,
      ← rayValue_eq_rayClassCharacter c ξ ha, ← rayValue_eq_rayClassCharacter c ξ hb]
  have hclInv : (idealClass c n)⁻¹ = idealClass c b * (idealClass c a)⁻¹ := by
    calc
      _ = (idealClass c a * (idealClass c b)⁻¹)⁻¹ := congrArg Inv.inv hcl
      _ = ((idealClass c b)⁻¹)⁻¹ * (idealClass c a)⁻¹ :=
        mul_inv_rev (idealClass c a) ((idealClass c b)⁻¹)
      _ = _ := congrArg (fun z : RayClass c => z * (idealClass c a)⁻¹) (inv_inv (idealClass c b))
  have h := hexp n hn
  rw [hclInv] at h
  simp_rw [hray] at h
  simpa only [mul_assoc] using h

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
theorem first_transfer_sexticSymbol_uniform_bound (n : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : O, ‖sexticSymbol n y‖ ≤ B := by
  have hprime (P : Ideal O) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : O, ‖sexticAtPrime P y‖ ≤ B := by
    refine ⟨∑ j ∈ Finset.range 6, ‖embedding (rootSix ^ j)‖,
      Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
    intro y
    unfold sexticAtPrime
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (embedding (rootSix ^ j))
  have hprod (s : Multiset (Ideal O)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : O,
      ‖(s.map (fun P => sexticAtPrime P y)).prod‖ ≤ B := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, zero_le_one, by intro y; simp⟩
    | @cons P s ih =>
      obtain ⟨A, hA, hPA⟩ := hprime P
      obtain ⟨B, hB, hSB⟩ := ih
      refine ⟨A * B, mul_nonneg hA hB, ?_⟩
      intro y
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul (hPA y) (hSB y) (norm_nonneg _) hA
  by_cases hn : n = ⊥
  · exact ⟨0, le_rfl, by intro y; simp [sexticSymbol, hn]⟩
  · obtain ⟨B, hB, hbound⟩ := hprod (UniqueFactorizationMonoid.normalizedFactors n)
    exact ⟨B, hB, by intro y; simpa only [sexticSymbol, if_neg hn] using hbound y⟩


theorem first_transfer_poisson_finite_rows_summable {α : Type*} (s : Finset α)
    (g : α → O → ℂ) (hzero : ∀ a ∉ s, ∀ k, g a k = 0)
    (hrow : ∀ a, Summable (g a)) :
    Summable (fun p : α × O => g p.1 p.2) := by
  apply summable_norm_iff.mp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro a
    exact (hrow a).norm
  · apply summable_of_hasFiniteSupport
    apply s.finite_toSet.subset
    intro a ha
    by_contra hnot
    exact ha (by simp only [hzero a hnot, norm_zero, tsum_zero])


end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open scoped BigOperators
open Classical
open SecondPoissonProof

def columnCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (U : ℝ → ℂ) (C d t : Ideal O) (ell : ℝ) (n : Ideal O) : ℂ :=
  if SquarefreeOutside c.S n ∧ IsRelPrime n t then
    (mobius n : ℂ) * rayValue ξ.val n *
      sexticSymbol n (primaryGenerator C) ^ (4 : ℕ) *
      sexticSymbol n (primaryGenerator d) * U (normIdeal n / ell)
  else 0

theorem columnCoefficient_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C d t : Ideal O) {ell : ℝ} (hell : 0 < ell) :
    Function.HasFiniteSupport (columnCoefficient c ξ U C d t ell) := by
  apply (finite_normIdeal_le (I.hi * ell)).subset
  intro n hn
  by_cases ha : SquarefreeOutside c.S n ∧ IsRelPrime n t
  · have hUn : U (normIdeal n / ell) ≠ 0 := by
      intro hz
      exact hn (by simp only [columnCoefficient, if_pos ha, hz, mul_zero])
    exact (div_le_iff₀ hell).mp (hU.2 hUn).2
  · exact False.elim (hn (by simp only [columnCoefficient, if_neg ha]))

theorem firstColumn_eq_columnCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (U : ℝ → ℂ) (C d t : Ideal O) (ell : ℝ) (y : O) :
    firstColumn c ξ C d t U ell y =
      ∑' n : Ideal O, columnCoefficient c ξ U C d t ell n * star (sexticSymbol n y) := by
  unfold firstColumn
  apply tsum_congr
  intro n
  by_cases hn : SquarefreeOutside c.S n ∧ IsRelPrime n t
  · simp only [if_pos hn, columnCoefficient]
    ring
  · simp only [if_neg hn, columnCoefficient, zero_mul]

def conjugateSymbolRow (Φ : RowWeight) (Y : ℝ) (a b : Ideal O) (y : O) : ℂ :=
  (Φ.value (normElement y / Y) : ℂ) * star (sexticSymbol a y) * sexticSymbol b y

theorem conjugateSymbolRow_summable (Φ : RowWeight) {Y : ℝ} (hY : 0 < Y)
    (a b : Ideal O) : Summable (conjugateSymbolRow Φ Y a b) := by
  obtain ⟨A, hA, ha⟩ := first_transfer_sexticSymbol_uniform_bound a
  obtain ⟨B, hB, hb⟩ := first_transfer_sexticSymbol_uniform_bound b
  apply Summable.of_norm_bounded (((rowWeight_element_summable Φ hY).mul_right A).mul_right B)
  intro y
  have hphi : 0 ≤ Φ.value (normElement y / Y) :=
    Φ.nonnegative _ (div_nonneg (Nat.cast_nonneg _) hY.le)
  simp only [conjugateSymbolRow, norm_mul, norm_star, Complex.norm_real,
    Real.norm_of_nonneg hphi]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (ha y) hphi) (hb y) (norm_nonneg _)
    (mul_nonneg hphi hA)

def weightedPairTerm (Φ : RowWeight) (Y : ℝ) (A : Ideal O → ℂ)
    (p : Ideal O × Ideal O) (y : O) : ℂ :=
  A p.1 * star (A p.2) * conjugateSymbolRow Φ Y p.1 p.2 y

theorem weightedPairTerm_joint_summable (Φ : RowWeight) {Y : ℝ} (hY : 0 < Y)
    (A : Ideal O → ℂ) (hA : Function.HasFiniteSupport A) :
    Summable (fun p : (Ideal O × Ideal O) × O => weightedPairTerm Φ Y A p.1 p.2) := by
  apply first_transfer_poisson_finite_rows_summable (hA.toFinset.product hA.toFinset)
  · intro p hp y
    have hz : p.1 ∉ hA.toFinset ∨ p.2 ∉ hA.toFinset := by
      by_contra hn
      push_neg at hn
      exact hp (Finset.mem_product.mpr hn)
    rcases hz with h | h
    · have ha : A p.1 = 0 := by
        by_contra hn
        exact h (hA.mem_toFinset.mpr hn)
      simp only [weightedPairTerm, ha, zero_mul]
    · have ha : A p.2 = 0 := by
        by_contra hn
        exact h (hA.mem_toFinset.mpr hn)
      simp only [weightedPairTerm, ha, star_zero, mul_zero, zero_mul]
  · intro p
    exact (conjugateSymbolRow_summable Φ hY p.1 p.2).mul_left _

theorem finite_column_square (A : Ideal O → ℂ) (hA : Function.HasFiniteSupport A) (y : O) :
    ((‖∑' n : Ideal O, A n * star (sexticSymbol n y)‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : Ideal O × Ideal O,
        A p.1 * star (A p.2) * star (sexticSymbol p.1 y) * sexticSymbol p.2 y := by
  let s := hA.toFinset
  have hz (n : Ideal O) (hn : n ∉ s) : A n = 0 := by
    by_contra ha
    exact hn (hA.mem_toFinset.mpr ha)
  have hcol : (∑' n : Ideal O, A n * star (sexticSymbol n y)) =
      ∑ n ∈ s, A n * star (sexticSymbol n y) :=
    tsum_eq_sum (fun n hn => by rw [hz n hn, zero_mul])
  have hpair (p : Ideal O × Ideal O) (hp : p ∉ s.product s) :
      A p.1 * star (A p.2) * star (sexticSymbol p.1 y) * sexticSymbol p.2 y = 0 := by
    have hh : p.1 ∉ s ∨ p.2 ∉ s := by
      by_contra hn
      push_neg at hn
      exact hp (Finset.mem_product.mpr hn)
    rcases hh with h | h
    · simp only [hz p.1 h, zero_mul]
    · simp only [hz p.2 h, star_zero, mul_zero, zero_mul]
  calc
    _ = (∑' n : Ideal O, A n * star (sexticSymbol n y)) *
        star (∑' n : Ideal O, A n * star (sexticSymbol n y)) := by
      simpa only [Complex.ofReal_pow, starRingEnd_apply] using
        (Complex.mul_conj' (∑' n : Ideal O, A n * star (sexticSymbol n y))).symm
    _ = (∑ n ∈ s, A n * star (sexticSymbol n y)) *
        star (∑ n ∈ s, A n * star (sexticSymbol n y)) := by rw [hcol]
    _ = ∑ p ∈ s.product s,
        A p.1 * star (A p.2) * star (sexticSymbol p.1 y) * sexticSymbol p.2 y := by
      rw [Finset.product_eq_sprod, Finset.sum_product, star_sum, Finset.sum_mul]
      simp only [star_mul, star_star, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := (tsum_eq_sum hpair).symm

set_option maxHeartbeats 800000 in
theorem finite_column_energy_expansion (Φ : RowWeight) {Y : ℝ} (hY : 0 < Y)
    (A : Ideal O → ℂ) (hA : Function.HasFiniteSupport A) :
    ((∑' y : O, Φ.value (normElement y / Y) *
      ‖∑' n : Ideal O, A n * star (sexticSymbol n y)‖ ^ 2 : ℝ) : ℂ) =
      ∑' a : Ideal O, ∑' b : Ideal O, A a * star (A b) *
        ∑' y : O, conjugateSymbolRow Φ Y a b y := by
  have hs := weightedPairTerm_joint_summable Φ hY A hA
  rw [Complex.ofReal_tsum]
  have hpoint (y : O) :
      ((Φ.value (normElement y / Y) *
        ‖∑' n : Ideal O, A n * star (sexticSymbol n y)‖ ^ 2 : ℝ) : ℂ) =
        ∑' p : Ideal O × Ideal O, weightedPairTerm Φ Y A p y := by
    rw [Complex.ofReal_mul, finite_column_square A hA y, ← tsum_mul_left]
    apply tsum_congr
    intro p
    unfold weightedPairTerm conjugateSymbolRow
    ring
  simp_rw [hpoint]
  rw [hs.tsum_comm, hs.prod.tsum_prod]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  rw [← tsum_mul_left]
  rfl

def gcdEnergyTerm (c : ArithmeticContext) (Φ : RowWeight) (Y : ℝ)
    (A : Ideal O → ℂ) (p : Ideal O × Ideal O × Ideal O) : ℂ :=
  if firstTransferGcdTripleAdmissible c p then
    A (p.1 * p.2.1) * star (A (p.1 * p.2.2)) *
      ∑' y : O, conjugateSymbolRow Φ Y (p.1 * p.2.1) (p.1 * p.2.2) y
  else 0

theorem firstColumn_energy_gcd (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (Φ : RowWeight) (C d t : Ideal O) {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    Summable (gcdEnergyTerm c Φ Y (columnCoefficient c ξ U C d t ell)) ∧
      ((∑' y : O, Φ.value (normElement y / Y) *
        ‖firstColumn c ξ C d t U ell y‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : Ideal O × Ideal O × Ideal O,
        gcdEnergyTerm c Φ Y (columnCoefficient c ξ U C d t ell) p := by
  let A := columnCoefficient c ξ U C d t ell
  have hA := columnCoefficient_hasFiniteSupport c ξ hU C d t hell
  let f : Ideal O × Ideal O → ℂ := fun p =>
    A p.1 * star (A p.2) * ∑' y : O, conjugateSymbolRow Φ Y p.1 p.2 y
  have hf : Function.HasFiniteSupport f := by
    apply (hA.prod hA).subset
    intro p hp
    constructor
    · intro hz
      change A p.1 = 0 at hz
      exact hp (by simp only [f, hz, zero_mul])
    · intro hz
      change A p.2 = 0 at hz
      exact hp (by simp only [f, hz, star_zero, mul_zero, zero_mul])
  have hrestrict : (fun p : Ideal O × Ideal O =>
      if firstTransferGcdPairAdmissible c p then f p else 0) = f := by
    funext p
    by_cases ha : SquarefreeOutside c.S p.1
    · by_cases hb : SquarefreeOutside c.S p.2
      · rw [if_pos (show firstTransferGcdPairAdmissible c p from ⟨ha, hb⟩)]
      · simp only [firstTransferGcdPairAdmissible, ha, hb, and_false, if_false,
          f, A, columnCoefficient, hb, false_and, if_false, star_zero, mul_zero, zero_mul]
    · simp only [firstTransferGcdPairAdmissible, ha, false_and, if_false,
        f, A, columnCoefficient, ha, false_and, if_false, zero_mul]
  have hs : Summable f := summable_of_hasFiniteSupport hf
  have hrestricted : Summable (fun p => if firstTransferGcdPairAdmissible c p then f p else 0) := by
    rw [hrestrict]
    exact hs
  obtain ⟨ht, heq⟩ := first_transfer_gcd_indicator_reindex c f hrestricted
  refine ⟨ht, ?_⟩
  rw [hrestrict] at heq
  simp_rw [firstColumn_eq_columnCoefficient]
  rw [finite_column_energy_expansion Φ hY A hA]
  exact hs.tsum_prod.symm.trans heq

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

def gaussNormalizer (n : Ideal O) : ℂ := star (alpha n) * gauss 2 n

theorem gaussNormalizer_mul_star (c : ArithmeticContext) (hc : ArithmeticRelations c)
    {n : Ideal O} (hn : SquarefreeOutside c.S n) :
    gaussNormalizer n * star (gaussNormalizer n) = 1 := by
  have hnorm : ‖gaussNormalizer n‖ = 1 := by
    simp only [gaussNormalizer, norm_mul, norm_star,
      first_transfer_norm_alpha_eq_one c hn.1, first_transfer_norm_gauss_two c hc hn, one_mul]
  simpa only [starRingEnd_apply, hnorm, one_pow, Complex.ofReal_one] using
    Complex.mul_conj' (gaussNormalizer n)

theorem rayValue_mul_star (c : ArithmeticContext) (ξ : RayCharacter c)
    {n : Ideal O} (hn : Outside c.S n) : rayValue ξ.val n * star (rayValue ξ.val n) = 1 := by
  have hnorm : ‖rayValue ξ.val n‖ = 1 := by
    rw [rayValue_eq_rayClassCharacter c ξ hn]
    exact norm_rayClassCharacter c ξ _
  simpa only [starRingEnd_apply, hnorm, one_pow, Complex.ofReal_one] using
    Complex.mul_conj' (rayValue ξ.val n)

theorem paired_gauss_reverse_normalization (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    (mobius a : ℂ) * (mobius b : ℂ) *
      (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss =
      gaussNormalizer a * star (gaussNormalizer b) *
        reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) := by
  let χ := firstTransferPrimitivePairedCharacter c hb ha hab.symm
  have h := first_transfer_coefficient_pairedGaussFactor c hc ξ₁ hb ha hab.symm
  rw [firstTransferPairedGaussFactor, ← first_transfer_primitive_paired_gauss_crt c hb ha hab.symm] at h
  have hunit (n : Ideal O) (hn : Outside c.S n) := rayValue_mul_star c ξ₁ hn
  have hprod : rayValue ξ₁.val b * star (rayValue ξ₁.val a) ≠ 0 := by
    apply mul_ne_zero
    · exact left_ne_zero_of_mul_eq_one (hunit b hb.1)
    · exact star_ne_zero.mpr (left_ne_zero_of_mul_eq_one (hunit a ha.1))
  have hraw : gaussNormalizer b * star (gaussNormalizer a) * χ.gauss =
      (mobius b : ℂ) * (mobius a : ℂ) *
        reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) := by
    apply mul_left_cancel₀ hprod
    calc
      _ = coefficient ξ₁.val b * star (coefficient ξ₁.val a) * χ.gauss := by
        simp only [coefficient, gaussNormalizer, star_mul, star_star]
        ring
      _ = _ := h
      _ = _ := by ring
  have hgauss : χ.gauss = gaussNormalizer a * star (gaussNormalizer b) *
      ((mobius b : ℂ) * (mobius a : ℂ) *
        reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹)) := by
    calc
      _ = (gaussNormalizer a * star (gaussNormalizer b)) *
          (gaussNormalizer b * star (gaussNormalizer a) * χ.gauss) := by
        calc
          _ = (gaussNormalizer a * star (gaussNormalizer a)) *
              (gaussNormalizer b * star (gaussNormalizer b)) * χ.gauss := by
            rw [gaussNormalizer_mul_star c hc ha, gaussNormalizer_mul_star c hc hb]
            ring
          _ = _ := by ring
      _ = _ := by rw [hraw]
  change (mobius a : ℂ) * (mobius b : ℂ) * χ.gauss = _
  rw [hgauss]
  calc
    _ = (mobius a : ℂ) ^ 2 * (mobius b : ℂ) ^ 2 *
        (gaussNormalizer a * star (gaussNormalizer b) *
          reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹)) := by ring
    _ = _ := by rw [first_transfer_mobius_sq ha.2, first_transfer_mobius_sq hb.2]; ring

theorem paired_gauss_given_ray_expansion (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ)
    (hexp : RayExpansion c hc ξ₁ coeffs)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    (mobius a : ℂ) * (mobius b : ℂ) * rayValue ξ₁.val a * star (rayValue ξ₁.val b) *
      (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss =
      ∑' ξ : RayCharacter c, coeffs ξ * coefficient ξ.val a * star (coefficient ξ.val b) := by
  calc
    _ = (rayValue ξ₁.val a * star (rayValue ξ₁.val b)) *
        ((mobius a : ℂ) * (mobius b : ℂ) *
          (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss) := by ring
    _ = (gaussNormalizer a * star (gaussNormalizer b)) *
        (rayValue ξ₁.val a * star (rayValue ξ₁.val b) *
          reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹)) := by
      rw [paired_gauss_reverse_normalization c hc ξ₁ ha hb hab]
      ring
    _ = (gaussNormalizer a * star (gaussNormalizer b)) *
        ∑' ξ : RayCharacter c, coeffs ξ * rayValue ξ.val a * star (rayValue ξ.val b) := by
      rw [ray_expansion_pair c hc ξ₁ coeffs hexp ha.1 hb.1]
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro ξ
      simp only [gaussNormalizer, coefficient, star_mul, star_star]
      ring

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

def rawColumnCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d n : Ideal O) : ℂ :=
  (mobius n : ℂ) * rayValue ξ.val n *
    sexticSymbol n (primaryGenerator C) ^ (4 : ℕ) * sexticSymbol n (primaryGenerator d)

theorem rawColumnCoefficient_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d : Ideal O) {g a : Ideal O} (hg : SquarefreeOutside c.S g)
    (ha : SquarefreeOutside c.S a) (hga : IsRelPrime g a) :
    rawColumnCoefficient c ξ C d (g * a) =
      rawColumnCoefficient c ξ C d g * rawColumnCoefficient c ξ C d a := by
  have hray : rayValue ξ.val (g * a) = rayValue ξ.val g * rayValue ξ.val a := by
    simp only [rayValue, first_transfer_primaryGenerator_mul_outside c hg.1 ha.1,
      HeckeCharacter.onElement, map_mul]
  simp only [rawColumnCoefficient, mobius, hga.moebius_mul, Int.cast_mul, hray,
    first_transfer_sexticSymbol_mul, mul_pow]
  ring

theorem rawColumnCoefficient_mul_star (c : ArithmeticContext) (ξ : RayCharacter c)
    {C d n : Ideal O} (hC : Outside c.S C) (hd : d ∣ C)
    (hn : SquarefreeOutside c.S n) :
    rawColumnCoefficient c ξ C d n * star (rawColumnCoefficient c ξ C d n) =
      if IsRelPrime C n then 1 else 0 := by
  have hdout := first_transfer_outside_of_dvd c hC hd
  have hCsymbol : sexticSymbol n (primaryGenerator C) * star (sexticSymbol n (primaryGenerator C)) =
      if IsRelPrime C n then 1 else 0 := by
    rw [first_transfer_sexticSymbol_mul_star c hn.1,
      (first_transfer_primaryGenerator_spec_and_primary_outside c hC).1]
  simp only [rawColumnCoefficient, star_mul, star_pow, star_intCast]
  calc
    _ = (mobius n : ℂ) ^ 2 * (rayValue ξ.val n * star (rayValue ξ.val n)) *
        (sexticSymbol n (primaryGenerator C) * star (sexticSymbol n (primaryGenerator C))) ^ (4 : ℕ) *
        (sexticSymbol n (primaryGenerator d) * star (sexticSymbol n (primaryGenerator d))) := by ring
    _ = _ := by
      rw [first_transfer_mobius_sq hn.2, rayValue_mul_star c ξ hn.1, hCsymbol]
      by_cases hCn : IsRelPrime C n
      · have hdn := hCn.of_dvd_left hd
        rw [if_pos hCn, first_transfer_sexticSymbol_mul_star c hn.1,
          (first_transfer_primaryGenerator_spec_and_primary_outside c hdout).1, if_pos hdn]
        norm_num
      · simp only [if_neg hCn, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul]

theorem rawColumnCoefficient_zero (c : ArithmeticContext) (ξ : RayCharacter c)
    {C d n : Ideal O} (hC : Outside c.S C) (hd : d ∣ C)
    (hn : SquarefreeOutside c.S n) (hCn : ¬ IsRelPrime C n) :
    rawColumnCoefficient c ξ C d n = 0 := by
  have h := rawColumnCoefficient_mul_star c ξ hC hd hn
  rw [if_neg hCn] at h
  by_contra hz
  exact mul_ne_zero hz (star_ne_zero.mpr hz) h

theorem sexticSymbol_pow_five (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (z : O) : sexticSymbol n z ^ (5 : ℕ) = star (sexticSymbol n z) := by
  by_cases hcop : IsRelPrime (principal z) n
  · have h6 := first_transfer_sexticSymbol_pow_six_of_isRelPrime c hn z hcop
    have hu := first_transfer_sexticSymbol_mul_star c hn z
    rw [if_pos hcop] at hu
    calc
      _ = sexticSymbol n z ^ 6 * star (sexticSymbol n z) := by
        calc
          _ = sexticSymbol n z ^ 5 * (sexticSymbol n z * star (sexticSymbol n z)) := by rw [hu]; ring
          _ = _ := by ring
      _ = _ := by rw [h6, one_mul]
  · rw [first_transfer_sexticSymbol_zero_of_not_isRelPrime c hn z hcop]
    norm_num

theorem coprimeCoefficient_factor (c : ArithmeticContext) (ξ : RayCharacter c)
    {C d e n : Ideal O} (hC : Outside c.S C) (hd : d ∣ C)
    (he : Outside c.S e) (hn : Outside c.S n) (h : O) :
    coprimeCoefficient c ξ C d e h n = coefficient ξ.val n *
      sexticSymbol n (primaryGenerator C) ^ (4 : ℕ) * sexticSymbol n (primaryGenerator d) *
      star (sexticSymbol n (primaryGenerator e)) * sexticSymbol n h := by
  have hdout := first_transfer_outside_of_dvd c hC hd
  rw [coprimeCoefficient, first_transfer_primaryGenerator_mul_outside c hdout he,
    first_transfer_primaryGenerator_mul_outside c hC he]
  simp only [SquarefreeReflection.sexticSymbol_mul_numerator c hn, mul_pow]
  calc
    _ = coefficient ξ.val n * sexticSymbol n (primaryGenerator C) ^ (4 : ℕ) *
        sexticSymbol n (primaryGenerator d) * sexticSymbol n (primaryGenerator e) ^ (5 : ℕ) *
        sexticSymbol n h := by ring
    _ = _ := by rw [sexticSymbol_pow_five c hn]

theorem poisson_coefficient_given_expansion (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ)
    (hexp : RayExpansion c hc ξ₁ coeffs) {C d e a b : Ideal O}
    (hC : Outside c.S C) (hd : d ∣ C) (he : Outside c.S e)
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (h : O) :
    rawColumnCoefficient c ξ₁ C d a * star (rawColumnCoefficient c ξ₁ C d b) *
      (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss *
      (firstTransferPrimitivePairedCharacter c hb ha hab.symm).value (primaryGenerator e) *
      star ((firstTransferPrimitivePairedCharacter c hb ha hab.symm).value h) =
      ∑' ξ : RayCharacter c, coeffs ξ *
        (coprimeCoefficient c ξ C d e h a * star (coprimeCoefficient c ξ C d e h b)) := by
  let K : ℂ := (sexticSymbol a (primaryGenerator C) ^ (4 : ℕ) *
      star (sexticSymbol b (primaryGenerator C) ^ (4 : ℕ))) *
    (sexticSymbol a (primaryGenerator d) * star (sexticSymbol b (primaryGenerator d))) *
    (star (sexticSymbol a (primaryGenerator e)) * sexticSymbol b (primaryGenerator e)) *
    (sexticSymbol a h * star (sexticSymbol b h))
  have hraw : rawColumnCoefficient c ξ₁ C d a * star (rawColumnCoefficient c ξ₁ C d b) *
      (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss *
      (firstTransferPrimitivePairedCharacter c hb ha hab.symm).value (primaryGenerator e) *
      star ((firstTransferPrimitivePairedCharacter c hb ha hab.symm).value h) =
      ((mobius a : ℂ) * (mobius b : ℂ) * rayValue ξ₁.val a * star (rayValue ξ₁.val b) *
        (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss) * K := by
    simp only [rawColumnCoefficient, firstTransferPrimitivePairedCharacter_value,
      star_mul, star_star, star_intCast, star_pow, K]
    ring
  rw [hraw, paired_gauss_given_ray_expansion c hc ξ₁ coeffs hexp ha hb hab, ← tsum_mul_right]
  apply tsum_congr
  intro ξ
  rw [coprimeCoefficient_factor c ξ hC hd he ha.1 h,
    coprimeCoefficient_factor c ξ hC hd he hb.1 h]
  simp only [K, star_mul, star_star, star_pow]
  ring

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

theorem poisson_nonzero_tsum (hp : PoissonStatement)
    (χ : PrimitiveResidueCharacter) (r : Ideal O) (Φ : RowWeight)
    {Y : ℝ} (hr : r ≠ ⊥) (hY : 0 < Y) :
    (∑' k : O, if IsRelPrime (principal k) r then
      χ.value k * (Φ.value (normElement k / Y) : ℂ) else 0) =
      poissonZeroTerm χ r (fun x => (Φ.value x : ℂ)) Y +
        Y * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
          ∑' e : Ideal O, if e ∣ outsideRadical ∅ r then
            firstTransferPoissonDivisorCoefficient χ e *
              ∑' h : O, if h ≠ 0 then firstTransferPoissonDualTerm χ Φ Y e h else 0
          else 0 := by
  rw [first_transfer_poisson_truncation hp χ r Φ hr hY,
    first_transfer_poisson_divisor_tsum_eq_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  have he0 := ne_zero_of_dvd_ne_zero
    (first_transfer_poisson_outsideRadical_ne_bot ∅ r) (mem_firstTransferPoissonDivisors.mp he)
  symm
  rw [tsum_eq_sum (s := firstTransferPoissonFrequencies χ Φ Y e) (fun h hh => ?_)]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [if_pos (mem_firstTransferPoissonFrequencies.mp hh).1]
  · by_cases hh0 : h = 0
    · simp only [hh0, ne_eq, not_true_eq_false, if_false]
    · rw [if_pos hh0]
      by_contra hz
      exact hh (mem_firstTransferPoissonFrequencies.mpr
        ⟨hh0, first_transfer_poisson_dual_support χ Φ hY he0 hz⟩)

theorem conjugate_gcd_row_poisson (hp : PoissonStatement) (c : ArithmeticContext)
    {g a b : Ideal O} (hg : SquarefreeOutside c.S g)
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (Φ : RowWeight) {Y : ℝ} (hY : 0 < Y) :
    (∑' y : O, conjugateSymbolRow Φ Y (g * a) (g * b) y) =
      poissonZeroTerm (firstTransferPrimitivePairedCharacter c hb ha hab.symm) g
        (fun x => (Φ.value x : ℂ)) Y +
        Y * (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss /
          (Real.sqrt (normIdeal (a * b)) : ℂ) *
          ∑' e : Ideal O, if e ∣ g then
            firstTransferPoissonDivisorCoefficient
              (firstTransferPrimitivePairedCharacter c hb ha hab.symm) e *
              ∑' h : O, if h ≠ 0 then firstTransferPoissonDualTerm
                (firstTransferPrimitivePairedCharacter c hb ha hab.symm) Φ Y e h else 0
          else 0 := by
  have hrow := first_transfer_poisson_gcd_row_eq c hg.1 hb ha hab.symm Φ Y
  have heq : (∑' y : O, conjugateSymbolRow Φ Y (g * a) (g * b) y) =
      ∑' y : O, (Φ.value (normElement y / Y) : ℂ) *
        sexticSymbol (g * b) y * star (sexticSymbol (g * a) y) := by
    apply tsum_congr
    intro y
    unfold conjugateSymbolRow
    ring
  rw [heq, hrow, poisson_nonzero_tsum hp _ g Φ hg.1.1 hY,
    first_transfer_outsideRadical_eq_self_of_squarefree hg.1.1 hg.2]
  simp only [firstTransferPrimitivePairedCharacter_modulus, mul_comm b a]

theorem second_kernel_normalization (Φ : RowWeight) (U : ℝ → ℂ)
    {g e a b : Ideal O} (hg : g ≠ ⊥) (he : e ≠ ⊥)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) {ell : ℝ} (hell : 0 < ell) (Y : ℝ) (h : O) :
    (Y : ℂ) / (Real.sqrt (normIdeal (a * b)) : ℂ) / (normIdeal e : ℂ) *
      U (normIdeal (g * a) / ell) * star (U (normIdeal (g * b) / ell)) *
      radialFourier (fun x => (Φ.value x : ℂ))
        (Y * normElement h / (normIdeal e * normIdeal (a * b))) =
      (Y : ℂ) * normIdeal g / ((normIdeal e : ℂ) * ell) *
        secondPoissonKernel Φ U Y ell g e h
          (normIdeal a / (ell / normIdeal g))
          (normIdeal b / (ell / normIdeal g)) := by
  have hNg := normIdeal_pos hg
  have hNe := normIdeal_pos he
  have hNa := normIdeal_pos ha
  have hNb := normIdeal_pos hb
  let x := normIdeal a / (ell / normIdeal g)
  let y := normIdeal b / (ell / normIdeal g)
  have hx : 0 < x := div_pos hNa (div_pos hell hNg)
  have hy : 0 < y := div_pos hNb (div_pos hell hNg)
  have hsampleA : normIdeal (g * a) / ell = x := by
    rw [normIdeal_mul]
    dsimp only [x]
    field_simp
  have hsampleB : normIdeal (g * b) / ell = y := by
    rw [normIdeal_mul]
    dsimp only [y]
    field_simp
  have harg : Y * normElement h * normIdeal g ^ (2 : ℕ) /
      (normIdeal e * ell ^ (2 : ℕ) * x * y) =
      Y * normElement h / (normIdeal e * normIdeal (a * b)) := by
    rw [normIdeal_mul]
    dsimp only [x, y]
    field_simp
    <;> ring
  have hroot : Real.sqrt x * Real.sqrt y =
      Real.sqrt (normIdeal (a * b)) * normIdeal g / ell := by
    rw [← Real.sqrt_mul hx.le, normIdeal_mul]
    have hxy : x * y = (normIdeal a * normIdeal b) * (normIdeal g / ell) ^ 2 := by
      dsimp only [x, y]
      field_simp
      <;> ring
    rw [hxy, Real.sqrt_mul (mul_pos hNa hNb).le,
      Real.sqrt_sq (div_pos hNg hell).le]
    ring
  have hrootC : (Real.sqrt x : ℂ) * (Real.sqrt y : ℂ) =
      (Real.sqrt (normIdeal (a * b)) : ℂ) * normIdeal g / ell := by
    exact_mod_cast hroot
  rw [hsampleA, hsampleB]
  change _ = (Y : ℂ) * normIdeal g / ((normIdeal e : ℂ) * ell) *
    secondPoissonKernel Φ U Y ell g e h x y
  unfold secondPoissonKernel
  rw [harg]
  simp only [star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hs : (Real.sqrt (normIdeal (a * b)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (normIdeal_pos (mul_ne_zero ha hb)))
  have hxC : (Real.sqrt x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hx)
  have hyC : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hy)
  have hscalar : (Y : ℂ) / (Real.sqrt (normIdeal (a * b)) : ℂ) / (normIdeal e : ℂ) =
      (Y : ℂ) * normIdeal g / ((normIdeal e : ℂ) * ell) *
        ((Real.sqrt x : ℂ)⁻¹ * (Real.sqrt y : ℂ)⁻¹) := by
    rw [← mul_inv, hrootC]
    have hgC : (normIdeal g : ℂ) ≠ 0 := by exact_mod_cast hNg.ne'
    have heC : (normIdeal e : ℂ) ≠ 0 := by exact_mod_cast hNe.ne'
    have hellC : (ell : ℂ) ≠ 0 := by exact_mod_cast hell.ne'
    field_simp [hgC, heC, hellC]
  rw [hscalar]
  ring

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

def outerAdmissible (c : ArithmeticContext) (C t g : Ideal O) : Prop :=
  SquarefreeOutside c.S g ∧ IsRelPrime g (C * t)

def pairAdmissible (c : ArithmeticContext) (C t g : Ideal O) (p : Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ IsRelPrime p.1 (g * C * t) ∧
    SquarefreeOutside c.S p.2 ∧ IsRelPrime p.2 (g * C * t) ∧ IsRelPrime p.1 p.2

def residualEnergyTerm (c : ArithmeticContext) (ξ : RayCharacter c) (Φ : RowWeight)
    (U : ℝ → ℂ) (C d t g : Ideal O) (Y ell : ℝ) (p : Ideal O × Ideal O) : ℂ :=
  if pairAdmissible c C t g p then
    rawColumnCoefficient c ξ C d p.1 * star (rawColumnCoefficient c ξ C d p.2) *
      U (normIdeal (g * p.1) / ell) * star (U (normIdeal (g * p.2) / ell)) *
      ∑' y : O, conjugateSymbolRow Φ Y (g * p.1) (g * p.2) y
  else 0

theorem columnCoefficient_eq_raw (c : ArithmeticContext) (ξ : RayCharacter c)
    (U : ℝ → ℂ) (C d t : Ideal O) (ell : ℝ) (n : Ideal O) :
    columnCoefficient c ξ U C d t ell n =
      if SquarefreeOutside c.S n ∧ IsRelPrime n t then
        rawColumnCoefficient c ξ C d n * U (normIdeal n / ell) else 0 := rfl

theorem columnCoefficient_zero_of_t (c : ArithmeticContext) (ξ : RayCharacter c)
    (U : ℝ → ℂ) (C d t : Ideal O) (ell : ℝ) (n : Ideal O)
    (hnt : ¬ IsRelPrime n t) : columnCoefficient c ξ U C d t ell n = 0 := by
  simp only [columnCoefficient, hnt, and_false, if_false]

theorem columnCoefficient_zero_of_raw (c : ArithmeticContext) (ξ : RayCharacter c)
    (U : ℝ → ℂ) (C d t : Ideal O) (ell : ℝ) (n : Ideal O)
    (hn : rawColumnCoefficient c ξ C d n = 0) :
    columnCoefficient c ξ U C d t ell n = 0 := by
  rw [columnCoefficient_eq_raw]
  split_ifs <;> simp only [hn, zero_mul]

theorem columnCoefficient_mul_good (c : ArithmeticContext) (ξ : RayCharacter c)
    (U : ℝ → ℂ) (C d t : Ideal O) (ell : ℝ) {g a : Ideal O}
    (hg : SquarefreeOutside c.S g) (ha : SquarefreeOutside c.S a)
    (hga : IsRelPrime g a) (hgt : IsRelPrime g t) (hat : IsRelPrime a t) :
    columnCoefficient c ξ U C d t ell (g * a) =
      rawColumnCoefficient c ξ C d g * rawColumnCoefficient c ξ C d a *
        U (normIdeal (g * a) / ell) := by
  rw [columnCoefficient_eq_raw,
    if_pos (show SquarefreeOutside c.S (g * a) ∧ IsRelPrime (g * a) t from
      ⟨⟨(first_transfer_outside_mul_iff c _ _).mpr ⟨hg.1, ha.1⟩,
        squarefree_mul_iff.mpr ⟨hga, hg.2, ha.2⟩⟩, hgt.mul_left hat⟩),
    rawColumnCoefficient_mul c ξ C d hg ha hga]

theorem pairAdmissible_triple (c : ArithmeticContext) {C t g a b : Ideal O}
    (hg : SquarefreeOutside c.S g) (hp : pairAdmissible c C t g (a, b)) :
    firstTransferGcdTripleAdmissible c (g, a, b) := by
  rcases hp with ⟨ha, hat, hb, hbt, hab⟩
  have hga : IsRelPrime g a :=
    ((IsRelPrime.mul_right_iff.mp (IsRelPrime.mul_right_iff.mp hat).1).1).symm
  have hgb : IsRelPrime g b :=
    ((IsRelPrime.mul_right_iff.mp (IsRelPrime.mul_right_iff.mp hbt).1).1).symm
  exact ⟨hg, ha, hb, hga, hgb, hab⟩

theorem gcdEnergyTerm_eq_residual (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (U : ℝ → ℂ) {C d : Ideal O} (hC : Outside c.S C) (hd : d ∣ C)
    (t : Ideal O) (Y ell : ℝ) (g a b : Ideal O) :
    gcdEnergyTerm c Φ Y (columnCoefficient c ξ U C d t ell) (g, a, b) =
      if outerAdmissible c C t g then residualEnergyTerm c ξ Φ U C d t g Y ell (a, b) else 0 := by
  by_cases hadm : firstTransferGcdTripleAdmissible c (g, a, b)
  · rcases hadm with ⟨hg, ha, hb, hga, hgb, hab⟩
    have htriple : firstTransferGcdTripleAdmissible c (g, a, b) := ⟨hg, ha, hb, hga, hgb, hab⟩
    rw [gcdEnergyTerm, if_pos htriple]
    by_cases hgt : IsRelPrime g t
    · by_cases hCg : IsRelPrime C g
      · have hog : outerAdmissible c C t g := ⟨hg, hCg.symm.mul_right hgt⟩
        rw [if_pos hog]
        by_cases hat : IsRelPrime a t
        · by_cases hbt : IsRelPrime b t
          · rw [columnCoefficient_mul_good c ξ U C d t ell hg ha hga hgt hat,
              columnCoefficient_mul_good c ξ U C d t ell hg hb hgb hgt hbt]
            by_cases hCa : IsRelPrime C a
            · by_cases hCb : IsRelPrime C b
              · have hp : pairAdmissible c C t g (a, b) :=
                  ⟨ha, (hga.symm.mul_right hCa.symm).mul_right hat,
                    hb, (hgb.symm.mul_right hCb.symm).mul_right hbt, hab⟩
                rw [residualEnergyTerm, if_pos hp]
                calc
                  _ = (rawColumnCoefficient c ξ C d g * star (rawColumnCoefficient c ξ C d g)) *
                      (rawColumnCoefficient c ξ C d a * star (rawColumnCoefficient c ξ C d b) *
                        U (normIdeal (g * a) / ell) * star (U (normIdeal (g * b) / ell)) *
                          ∑' y : O, conjugateSymbolRow Φ Y (g * a) (g * b) y) := by
                    simp only [star_mul]
                    ring
                  _ = _ := by rw [rawColumnCoefficient_mul_star c ξ hC hd hg, if_pos hCg, one_mul]
              · have hz := rawColumnCoefficient_zero c ξ hC hd hb hCb
                have hp : ¬ pairAdmissible c C t g (a, b) := by
                  intro hh
                  exact hCb ((IsRelPrime.mul_right_iff.mp
                    (IsRelPrime.mul_right_iff.mp hh.2.2.2.1).1).2).symm
                simp only [residualEnergyTerm, if_neg hp, hz, star_zero, mul_zero, zero_mul]
            · have hz := rawColumnCoefficient_zero c ξ hC hd ha hCa
              have hp : ¬ pairAdmissible c C t g (a, b) := by
                intro hh
                exact hCa ((IsRelPrime.mul_right_iff.mp
                  (IsRelPrime.mul_right_iff.mp hh.2.1).1).2).symm
              simp only [residualEnergyTerm, if_neg hp, hz, mul_zero, zero_mul]
          · have hgbt : ¬ IsRelPrime (g * b) t := by
              intro hh
              exact hbt (IsRelPrime.mul_left_iff.mp hh).2
            have hp : ¬ pairAdmissible c C t g (a, b) := by
              intro hh
              exact hbt (IsRelPrime.mul_right_iff.mp hh.2.2.2.1).2
            rw [columnCoefficient_zero_of_t c ξ U C d t ell (g * b) hgbt]
            simp only [star_zero, mul_zero, zero_mul, residualEnergyTerm, if_neg hp]
        · have hgat : ¬ IsRelPrime (g * a) t := by
            intro hh
            exact hat (IsRelPrime.mul_left_iff.mp hh).2
          have hp : ¬ pairAdmissible c C t g (a, b) := by
            intro hh
            exact hat (IsRelPrime.mul_right_iff.mp hh.2.1).2
          rw [columnCoefficient_zero_of_t c ξ U C d t ell (g * a) hgat]
          simp only [zero_mul, residualEnergyTerm, if_neg hp]
      · have hz := rawColumnCoefficient_zero c ξ hC hd hg hCg
        have hraw : rawColumnCoefficient c ξ C d (g * a) = 0 := by
          rw [rawColumnCoefficient_mul c ξ C d hg ha hga, hz, zero_mul]
        have hog : ¬ outerAdmissible c C t g := by
          intro hh
          exact hCg (IsRelPrime.mul_right_iff.mp hh.2).1.symm
        rw [columnCoefficient_zero_of_raw c ξ U C d t ell (g * a) hraw, if_neg hog]
        simp only [zero_mul]
    · have hgat : ¬ IsRelPrime (g * a) t := by
        intro hh
        exact hgt (IsRelPrime.mul_left_iff.mp hh).1
      have hog : ¬ outerAdmissible c C t g := by
        intro hh
        exact hgt (IsRelPrime.mul_right_iff.mp hh.2).2
      rw [columnCoefficient_zero_of_t c ξ U C d t ell (g * a) hgat, if_neg hog]
      simp only [zero_mul]
  · rw [gcdEnergyTerm, if_neg hadm]
    by_cases hog : outerAdmissible c C t g
    · rw [if_pos hog, residualEnergyTerm]
      have hp : ¬ pairAdmissible c C t g (a, b) :=
        fun hp => hadm (pairAdmissible_triple c hog.1 hp)
      rw [if_neg hp]
    · rw [if_neg hog]

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

def dualJointTerm (c : ArithmeticContext) (Φ : RowWeight) (U : ℝ → ℂ)
    (coeffs : RayCharacter c → ℂ) (C d t g : Ideal O) (Y ell : ℝ)
    (p : (Ideal O × Ideal O) × (Ideal O × O × RayCharacter c)) : ℂ :=
  if p.2.1 ∣ g ∧ p.2.2.1 ≠ 0 ∧ pairAdmissible c C t g p.1 then
    (Y : ℂ) * (mobius p.2.1 : ℂ) * coeffs p.2.2.2 * normIdeal g /
      ((normIdeal p.2.1 : ℂ) * ell) *
      (coprimeCoefficient c p.2.2.2 C d p.2.1 p.2.2.1 p.1.1 *
        star (coprimeCoefficient c p.2.2.2 C d p.2.1 p.2.2.1 p.1.2)) *
      secondPoissonKernel Φ U Y ell g p.2.1 p.2.2.1
        (normIdeal p.1.1 / (ell / normIdeal g))
        (normIdeal p.1.2 / (ell / normIdeal g))
  else 0

theorem sample_argument {g a : Ideal O} (hg : g ≠ ⊥) {ell : ℝ} (hell : 0 < ell) :
    normIdeal (g * a) / ell = normIdeal a / (ell / normIdeal g) := by
  rw [normIdeal_mul]
  field_simp

theorem dualJointTerm_hasFiniteSupport (c : ArithmeticContext)
    (coeffs : RayCharacter c → ℂ) (hcoeff : (Function.support coeffs).Finite)
    {I : SupportInterval} (Φ : RowWeight) {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C d t : Ideal O) {g : Ideal O} (hg : g ≠ ⊥)
    {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    Function.HasFiniteSupport (dualJointTerm c Φ U coeffs C d t g Y ell) := by
  let B := I.hi * (ell / normIdeal g)
  let R := Φ.fourierCap * I.hi ^ (2 : ℕ) * ell ^ (2 : ℕ) * normIdeal g /
    (Y * normIdeal g ^ (2 : ℕ))
  apply (((finite_normIdeal_le B).prod (finite_normIdeal_le B)).prod
    ((first_transfer_divisors_finite hg).prod ((finite_normElement_le R).prod hcoeff))).subset
  intro p hp
  have hadm : p.2.1 ∣ g ∧ p.2.2.1 ≠ 0 ∧ pairAdmissible c C t g p.1 := by
    by_contra hh
    exact hp (by simp only [dualJointTerm, if_neg hh])
  have he0 : p.2.1 ≠ ⊥ := ne_zero_of_dvd_ne_zero hg hadm.1
  have hk : secondPoissonKernel Φ U Y ell g p.2.1 p.2.2.1
      (normIdeal p.1.1 / (ell / normIdeal g))
      (normIdeal p.1.2 / (ell / normIdeal g)) ≠ 0 := by
    intro hz
    exact hp (by simp only [dualJointTerm, if_pos hadm, hz, mul_zero])
  have hξ : coeffs p.2.2.2 ≠ 0 := by
    intro hz
    exact hp (by simp only [dualJointTerm, if_pos hadm, hz, mul_zero, zero_mul, zero_div])
  have hx : normIdeal p.1.1 / (ell / normIdeal g) ∈ Set.Icc I.lo I.hi := by
    by_contra hx
    exact hk (secondPoissonKernel_eq_zero_of_x₁_not_mem I Φ U Y ell g p.2.1 p.2.2.1 _ _ hU hx)
  have hy : normIdeal p.1.2 / (ell / normIdeal g) ∈ Set.Icc I.lo I.hi := by
    by_contra hy
    exact hk (secondPoissonKernel_eq_zero_of_x₂_not_mem I Φ U Y ell g p.2.1 p.2.2.1 _ _ hU hy)
  have hfreq : normElement p.2.2.1 ≤ Φ.fourierCap * I.hi ^ (2 : ℕ) * ell ^ (2 : ℕ) *
      normIdeal p.2.1 / (Y * normIdeal g ^ (2 : ℕ)) := by
    by_contra hh
    exact hk (secondPoissonKernel_eq_zero_of_frequency_gt I Φ U Y ell g p.2.1 p.2.2.1 _ _
      hY hell (normIdeal_pos hg) (normIdeal_pos he0) hx hy (lt_of_not_ge hh))
  have hfreqR : normElement p.2.2.1 ≤ R := by
    apply hfreq.trans
    apply div_le_div_of_nonneg_right _ (mul_nonneg hY.le (sq_nonneg _))
    apply mul_le_mul_of_nonneg_left (first_transfer_normIdeal_le_of_dvd hg hadm.1)
    exact mul_nonneg (mul_nonneg Φ.cap_pos.le (sq_nonneg I.hi)) (sq_nonneg ell)
  exact ⟨⟨(div_le_iff₀ (div_pos hell (normIdeal_pos hg))).mp hx.2,
      (div_le_iff₀ (div_pos hell (normIdeal_pos hg))).mp hy.2⟩,
    hadm.1, hfreqR, hξ⟩

theorem dualJointTerm_reorder (c : ArithmeticContext)
    (coeffs : RayCharacter c → ℂ) (hcoeff : (Function.support coeffs).Finite)
    {I : SupportInterval} (Φ : RowWeight) {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C d t : Ideal O) {g : Ideal O} (hg : g ≠ ⊥)
    {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    (∑' a : Ideal O, ∑' b : Ideal O, ∑' e : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c,
      dualJointTerm c Φ U coeffs C d t g Y ell ((a, b), (e, h, ξ))) =
      ∑' e : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c, ∑' a : Ideal O, ∑' b : Ideal O,
        dualJointTerm c Φ U coeffs C d t g Y ell ((a, b), (e, h, ξ)) := by
  let f := dualJointTerm c Φ U coeffs C d t g Y ell
  have hs : Summable f := summable_of_hasFiniteSupport
    (dualJointTerm_hasFiniteSupport c coeffs hcoeff Φ hU C d t hg hY hell)
  have hleft : (∑' p : Ideal O × Ideal O, ∑' z : Ideal O × O × RayCharacter c, f (p, z)) =
      ∑' a : Ideal O, ∑' b : Ideal O, ∑' e : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c,
        f ((a, b), (e, h, ξ)) := by
    rw [hs.prod.tsum_prod]
    apply tsum_congr
    intro a
    apply tsum_congr
    intro b
    rw [(hs.prod_factor (a, b)).tsum_prod]
    apply tsum_congr
    intro e
    exact ((hs.prod_factor (a, b)).prod_factor e).tsum_prod
  have hright : (∑' z : Ideal O × O × RayCharacter c, ∑' p : Ideal O × Ideal O, f (p, z)) =
      ∑' e : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c, ∑' a : Ideal O, ∑' b : Ideal O,
        f ((a, b), (e, h, ξ)) := by
    calc
      _ = ∑' e : Ideal O, ∑' q : O × RayCharacter c, ∑' p : Ideal O × Ideal O, f (p, (e, q)) :=
        hs.prod_symm.prod.tsum_prod
      _ = _ := by
        apply tsum_congr
        intro e
        calc
          _ = ∑' h : O, ∑' ξ : RayCharacter c, ∑' p : Ideal O × Ideal O, f (p, (e,h,ξ)) :=
            (hs.prod_symm.prod.prod_factor e).tsum_prod
          _ = _ := by
            apply tsum_congr
            intro h
            apply tsum_congr
            intro ξ
            exact (hs.prod_symm.prod_factor (e, h, ξ)).tsum_prod
  exact hleft.symm.trans ((Summable.tsum_comm (f := fun p z => f (p,z)) hs).symm.trans hright)

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

theorem normalize_poisson_pair (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ)
    (hexp : RayExpansion c hc ξ₁ coeffs) (Φ : RowWeight) (U : ℝ → ℂ)
    {C d g e a b : Ideal O} (hC : Outside c.S C) (hd : d ∣ C)
    (hg : SquarefreeOutside c.S g) (he : e ∣ g)
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) {ell : ℝ} (hell : 0 < ell) (Y : ℝ) (h : O) :
    (rawColumnCoefficient c ξ₁ C d a * star (rawColumnCoefficient c ξ₁ C d b) *
      U (normIdeal (g * a) / ell) * star (U (normIdeal (g * b) / ell))) *
      ((Y : ℂ) * (firstTransferPrimitivePairedCharacter c hb ha hab.symm).gauss /
        (Real.sqrt (normIdeal (a * b)) : ℂ)) *
      (firstTransferPoissonDivisorCoefficient (firstTransferPrimitivePairedCharacter c hb ha hab.symm) e *
        firstTransferPoissonDualTerm (firstTransferPrimitivePairedCharacter c hb ha hab.symm) Φ Y e h) =
      ∑' ξ : RayCharacter c,
        (Y : ℂ) * (mobius e : ℂ) * coeffs ξ * normIdeal g / ((normIdeal e : ℂ) * ell) *
          (coprimeCoefficient c ξ C d e h a * star (coprimeCoefficient c ξ C d e h b)) *
            secondPoissonKernel Φ U Y ell g e h
              (normIdeal a / (ell / normIdeal g))
              (normIdeal b / (ell / normIdeal g)) := by
  have heout := first_transfer_outside_of_dvd c hg.1 he
  have hpoint := poisson_coefficient_given_expansion c hc ξ₁ coeffs hexp hC hd heout ha hb hab h
  have hnormal := second_kernel_normalization Φ U hg.1.1 heout.1 ha.1.1 hb.1.1 hell Y h
  let χ := firstTransferPrimitivePairedCharacter c hb ha hab.symm
  let S : ℂ := (mobius e : ℂ) *
    ((Y : ℂ) / (Real.sqrt (normIdeal (a * b)) : ℂ) / (normIdeal e : ℂ) *
      U (normIdeal (g * a) / ell) * star (U (normIdeal (g * b) / ell)) *
      radialFourier (fun x => (Φ.value x : ℂ))
        (Y * normElement h / (normIdeal e * normIdeal (a * b))))
  calc
    _ = S * (rawColumnCoefficient c ξ₁ C d a * star (rawColumnCoefficient c ξ₁ C d b) *
        χ.gauss * χ.value (primaryGenerator e) * star (χ.value h)) := by
      simp only [S, χ, firstTransferPoissonDivisorCoefficient,
        firstTransferPoissonDualTerm, firstTransferPrimitivePairedCharacter_modulus,
        first_transfer_chosenGenerator_eq_primaryGenerator c heout, mul_comm b a]
      ring
    _ = S * ∑' ξ : RayCharacter c, coeffs ξ *
        (coprimeCoefficient c ξ C d e h a * star (coprimeCoefficient c ξ C d e h b)) := by
      rw [hpoint]
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro ξ
      dsimp only [S]
      rw [hnormal]
      ring

theorem rawColumnCoefficient_one (c : ArithmeticContext) (ξ : RayCharacter c) (C d : Ideal O) :
    rawColumnCoefficient c ξ C d 1 = 1 := by
  have hray : rayValue ξ.val (1 : Ideal O) = 1 := by
    rw [rayValue_eq_rayClassCharacter c ξ (first_transfer_outside_one c), idealClass_one, map_one]
  have h1 : (1 : Ideal O) ≠ ⊥ := by rw [Ideal.one_eq_top]; exact top_ne_bot
  have hs (z : O) : sexticSymbol (1 : Ideal O) z = 1 := by
    rw [sexticSymbol, if_neg h1, normalizedFactors_one]
    rfl
  have hm : (mobius (1 : Ideal O) : ℂ) = 1 := by
    simp only [mobius, moebius_one, Int.cast_one]
  rw [rawColumnCoefficient, hm, hray, hs, hs]
  ring

def zeroPairTerm (Φ : RowWeight) (U : ℝ → ℂ) (g : Ideal O) (Y ell : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  if p.1 = 1 ∧ p.2 = 1 then
    (‖U (normIdeal g / ell)‖ ^ (2 : ℕ) : ℝ) *
      ((Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
        ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹))
  else 0

theorem zero_pair_evaluation (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (U : ℝ → ℂ) (C d : Ideal O) {g a b : Ideal O}
    (hg : SquarefreeOutside c.S g) (ha : SquarefreeOutside c.S a)
    (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b)
    {Y : ℝ} (hY : 0 < Y) (ell : ℝ) :
    (rawColumnCoefficient c ξ C d a * star (rawColumnCoefficient c ξ C d b) *
      U (normIdeal (g * a) / ell) * star (U (normIdeal (g * b) / ell))) *
      poissonZeroTerm (firstTransferPrimitivePairedCharacter c hb ha hab.symm) g
        (fun x => (Φ.value x : ℂ)) Y = zeroPairTerm Φ U g Y ell (a, b) := by
  by_cases hp : a = 1 ∧ b = 1
  · rcases hp with ⟨rfl, rfl⟩
    let χ := firstTransferPrimitivePairedCharacter c hb ha hab.symm
    have hmod : χ.modulus = ⊤ := by
      change (1 : Ideal O) * 1 = ⊤
      rw [one_mul, Ideal.one_eq_top]
    have hχ : χ.character = 1 := (first_transfer_primitive_character_eq_one_iff χ).mpr hmod
    have hz := poisson_zero_statement.2 χ g (fun x => (Φ.value x : ℂ)) Y
      hχ hmod hg.1.1 hY Φ.schwartz
    change _ * poissonZeroTerm χ g (fun x => (Φ.value x : ℂ)) Y = _
    rw [hz]
    simp only [rawColumnCoefficient_one, star_one, one_mul, mul_one,
      zeroPairTerm, and_self, if_true]
    have hu := Complex.mul_conj' (U (normIdeal g / ell))
    simp only [starRingEnd_apply] at *
    rw [hu]
    simp only [Complex.ofReal_pow]
  · have hp' : ¬ (b = ⊤ ∧ a = ⊤) := by
      simpa only [← Ideal.one_eq_top, and_comm] using hp
    rw [first_transfer_paired_poissonZeroTerm_eq_zero poisson_zero_statement c hb ha hab.symm hp']
    simp only [mul_zero, zeroPairTerm, if_neg hp]

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

theorem pairAdmissible_one (c : ArithmeticContext) (C t g : Ideal O) :
    pairAdmissible c C t g (1, 1) :=
  ⟨⟨first_transfer_outside_one c, squarefree_one⟩, isRelPrime_one_left,
    ⟨first_transfer_outside_one c, squarefree_one⟩, isRelPrime_one_left, isRelPrime_one_left⟩

theorem zeroPairTerm_eq_zero_of_not_pair (c : ArithmeticContext)
    (Φ : RowWeight) (U : ℝ → ℂ) (C t g : Ideal O) (Y ell : ℝ)
    (a b : Ideal O) (hp : ¬ pairAdmissible c C t g (a,b)) :
    zeroPairTerm Φ U g Y ell (a,b) = 0 := by
  have hnot : ¬ (a = 1 ∧ b = 1) := by
    rintro ⟨rfl, rfl⟩
    exact hp (pairAdmissible_one c C t g)
  exact if_neg hnot

theorem residualEnergyTerm_poisson (hp : PoissonStatement) (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ)
    (hexp : RayExpansion c hc ξ₁ coeffs) (Φ : RowWeight) (U : ℝ → ℂ)
    {C d g : Ideal O} (hC : Outside c.S C) (hd : d ∣ C)
    (hg : SquarefreeOutside c.S g) (t : Ideal O) {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell)
    (a b : Ideal O) :
    residualEnergyTerm c ξ₁ Φ U C d t g Y ell (a,b) =
      zeroPairTerm Φ U g Y ell (a,b) +
        ∑' e : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c,
          dualJointTerm c Φ U coeffs C d t g Y ell ((a,b),(e,h,ξ)) := by
  by_cases hadm : pairAdmissible c C t g (a,b)
  · have ha := hadm.1
    have hb := hadm.2.2.1
    have hab := hadm.2.2.2.2
    let χ := firstTransferPrimitivePairedCharacter c hb ha hab.symm
    let A : ℂ := rawColumnCoefficient c ξ₁ C d a * star (rawColumnCoefficient c ξ₁ C d b) *
      U (normIdeal (g*a) / ell) * star (U (normIdeal (g*b) / ell))
    rw [residualEnergyTerm, if_pos hadm]
    change A * (∑' y : O, conjugateSymbolRow Φ Y (g*a) (g*b) y) = _
    rw [conjugate_gcd_row_poisson hp c hg ha hb hab Φ hY, mul_add]
    have hzero : A * poissonZeroTerm χ g (fun x => (Φ.value x : ℂ)) Y =
        zeroPairTerm Φ U g Y ell (a,b) :=
      zero_pair_evaluation c ξ₁ Φ U C d hg ha hb hab hY ell
    change A * poissonZeroTerm χ g (fun x => (Φ.value x : ℂ)) Y + _ = _
    rw [hzero]
    congr 1
    change A * (((Y : ℂ) * χ.gauss / (Real.sqrt (normIdeal (a*b)) : ℂ)) *
      ∑' e : Ideal O, if e ∣ g then
        firstTransferPoissonDivisorCoefficient χ e *
          ∑' h : O, if h ≠ 0 then firstTransferPoissonDualTerm χ Φ Y e h else 0
      else 0) = _
    rw [← mul_assoc, ← tsum_mul_left]
    apply tsum_congr
    intro e
    by_cases he : e ∣ g
    · rw [if_pos he]
      rw [← mul_assoc, ← tsum_mul_left]
      apply tsum_congr
      intro h
      by_cases hh : h ≠ 0
      · rw [if_pos hh]
        calc
          _ = A * ((Y : ℂ) * χ.gauss / (Real.sqrt (normIdeal (a*b)) : ℂ)) *
              (firstTransferPoissonDivisorCoefficient χ e * firstTransferPoissonDualTerm χ Φ Y e h) := by ring
          _ = ∑' ξ : RayCharacter c,
              (Y : ℂ) * (mobius e : ℂ) * coeffs ξ * normIdeal g / ((normIdeal e : ℂ) * ell) *
                (coprimeCoefficient c ξ C d e h a * star (coprimeCoefficient c ξ C d e h b)) *
                  secondPoissonKernel Φ U Y ell g e h
                    (normIdeal a / (ell / normIdeal g))
                    (normIdeal b / (ell / normIdeal g)) :=
            normalize_poisson_pair c hc ξ₁ coeffs hexp Φ U hC hd hg he ha hb hab hell Y h
          _ = _ := by
            apply tsum_congr
            intro ξ
            rw [dualJointTerm, if_pos (show e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g (a,b) from
              ⟨he, hh, hadm⟩)]
      · have hnot : ¬ (e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g (a,b)) := fun hz => hh hz.2.1
        simp only [if_neg hh, mul_zero, dualJointTerm, if_neg hnot, tsum_zero]
    · have hnot (h : O) : ¬ (e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g (a,b)) := fun hz => he hz.1
      simp only [if_neg he, mul_zero, dualJointTerm, if_neg (hnot _), tsum_zero]
  · rw [residualEnergyTerm, if_neg hadm, zeroPairTerm_eq_zero_of_not_pair c Φ U C t g Y ell a b hadm]
    have hnot (e : Ideal O) (h : O) :
        ¬ (e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g (a,b)) := fun hz => hadm hz.2.2
    simp only [dualJointTerm, if_neg (hnot _ _), tsum_zero, add_zero]

theorem zeroPairTerm_hasFiniteSupport (Φ : RowWeight) (U : ℝ → ℂ)
    (g : Ideal O) (Y ell : ℝ) : Function.HasFiniteSupport (zeroPairTerm Φ U g Y ell) := by
  apply (Set.finite_singleton ((1 : Ideal O),(1 : Ideal O))).subset
  intro p hp
  have hh : p.1 = 1 ∧ p.2 = 1 := by
    by_contra hh
    exact hp (if_neg hh)
  exact Prod.ext hh.1 hh.2

theorem zeroPairTerm_tsum (Φ : RowWeight) (U : ℝ → ℂ) (g : Ideal O) (Y ell : ℝ) :
    (∑' p : Ideal O × Ideal O, zeroPairTerm Φ U g Y ell p) =
      (‖U (normIdeal g / ell)‖ ^ (2 : ℕ) : ℝ) *
        ((Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
          ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)) := by
  have heq : zeroPairTerm Φ U g Y ell = fun p : Ideal O × Ideal O =>
      if p = (1,1) then
        (‖U (normIdeal g / ell)‖ ^ (2 : ℕ) : ℝ) *
          ((Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
            ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)) else 0 := by
    funext p
    simp only [zeroPairTerm, Prod.ext_iff]
  rw [heq, tsum_ite_eq]

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

def coprimeOuterRow (c : ArithmeticContext) (Φ : RowWeight) (U : ℝ → ℂ)
    (coeffs : RayCharacter c → ℂ) (C d t : Ideal O) (Y ell : ℝ) (g : Ideal O) : ℂ :=
  ∑' e : Ideal O, if e ∣ g then
    ∑' h : O, if h ≠ 0 then
      ∑' ξ : RayCharacter c,
        (Y : ℂ) * (mobius e : ℂ) * coeffs ξ * normIdeal g / ((normIdeal e : ℂ) * ell) *
          ∑' a : Ideal O, if SquarefreeOutside c.S a ∧ IsRelPrime a (g*C*t) then
            ∑' b : Ideal O, if SquarefreeOutside c.S b ∧ IsRelPrime b (g*C*t) ∧ IsRelPrime a b then
              coprimeCoefficient c ξ C d e h a * star (coprimeCoefficient c ξ C d e h b) *
                secondPoissonKernel Φ U Y ell g e h
                  (normIdeal a / (ell / normIdeal g))
                  (normIdeal b / (ell / normIdeal g))
            else 0
          else 0
    else 0
  else 0

theorem dualJointTerm_tsum_eq_outerRow (c : ArithmeticContext)
    (coeffs : RayCharacter c → ℂ) (hcoeff : (Function.support coeffs).Finite)
    {I : SupportInterval} (Φ : RowWeight) {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C d t : Ideal O) {g : Ideal O} (hg : g ≠ ⊥)
    {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    (∑' z : Ideal O × O × RayCharacter c, ∑' p : Ideal O × Ideal O,
      dualJointTerm c Φ U coeffs C d t g Y ell (p,z)) =
      coprimeOuterRow c Φ U coeffs C d t Y ell g := by
  let f := dualJointTerm c Φ U coeffs C d t g Y ell
  have hs : Summable f := summable_of_hasFiniteSupport
    (dualJointTerm_hasFiniteSupport c coeffs hcoeff Φ hU C d t hg hY hell)
  calc
    _ = ∑' e : Ideal O, ∑' q : O × RayCharacter c, ∑' p : Ideal O × Ideal O, f (p,(e,q)) :=
      hs.prod_symm.prod.tsum_prod
    _ = _ := by
      unfold coprimeOuterRow
      apply tsum_congr
      intro e
      have hδ := (hs.prod_symm.prod.prod_factor e).tsum_prod
      change (∑' q : O × RayCharacter c, ∑' p : Ideal O × Ideal O, f (p,(e,q))) =
        ∑' h : O, ∑' ξ : RayCharacter c, ∑' p : Ideal O × Ideal O, f (p,(e,h,ξ)) at hδ
      rw [hδ]
      by_cases he : e ∣ g
      · rw [if_pos he]
        apply tsum_congr
        intro h
        by_cases hh : h ≠ 0
        · rw [if_pos hh]
          apply tsum_congr
          intro ξ
          have hpSum := (hs.prod_symm.prod_factor (e,h,ξ)).tsum_prod
          change (∑' p : Ideal O × Ideal O, f (p,(e,h,ξ))) =
            ∑' a : Ideal O, ∑' b : Ideal O, f ((a,b),(e,h,ξ)) at hpSum
          rw [hpSum, ← tsum_mul_left]
          apply tsum_congr
          intro a
          by_cases ha : SquarefreeOutside c.S a ∧ IsRelPrime a (g*C*t)
          · rw [if_pos ha, ← tsum_mul_left]
            apply tsum_congr
            intro b
            by_cases hb : SquarefreeOutside c.S b ∧ IsRelPrime b (g*C*t) ∧ IsRelPrime a b
            · have hp : pairAdmissible c C t g (a,b) := ⟨ha.1,ha.2,hb.1,hb.2.1,hb.2.2⟩
              simp only [f, dualJointTerm,
                if_pos (show e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g (a,b) from ⟨he,hh,hp⟩), if_pos hb]
              ring
            · have hp : ¬ pairAdmissible c C t g (a,b) := by
                intro hp
                exact hb ⟨hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
              have hnot : ¬ (e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g (a,b)) := fun hz => hp hz.2.2
              simp only [f, dualJointTerm, if_neg hnot, if_neg hb, mul_zero]
          · have hp (b : Ideal O) : ¬ pairAdmissible c C t g (a,b) := fun hp => ha ⟨hp.1,hp.2.1⟩
            have hnot (b : Ideal O) : ¬ (e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g (a,b)) :=
              fun hz => hp b hz.2.2
            simp only [f, dualJointTerm, if_neg (hnot _), tsum_zero, if_neg ha, mul_zero]
        · have hnot (p : Ideal O × Ideal O) : ¬ (e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g p) :=
            fun hz => hh hz.2.1
          simp only [f, dualJointTerm, if_neg (hnot _), tsum_zero, if_neg hh]
      · have hnot (h : O) (p : Ideal O × Ideal O) : ¬ (e ∣ g ∧ h ≠ 0 ∧ pairAdmissible c C t g p) :=
          fun hz => he hz.1
        simp only [f, dualJointTerm, if_neg (hnot _ _), tsum_zero, if_neg he]

theorem residualEnergyTerm_tsum (hp : PoissonStatement) (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ)
    (hcoeff : (Function.support coeffs).Finite) (hexp : RayExpansion c hc ξ₁ coeffs)
    {I : SupportInterval} (Φ : RowWeight) {U : ℝ → ℂ} (hU : SmoothSupported I U)
    {C d g : Ideal O} (hC : Outside c.S C) (hd : d ∣ C)
    (hg : SquarefreeOutside c.S g) (t : Ideal O) {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    (∑' p : Ideal O × Ideal O, residualEnergyTerm c ξ₁ Φ U C d t g Y ell p) =
      (‖U (normIdeal g / ell)‖ ^ (2 : ℕ) : ℝ) *
        ((Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
          ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)) +
      coprimeOuterRow c Φ U coeffs C d t Y ell g := by
  let f := dualJointTerm c Φ U coeffs C d t g Y ell
  have hs : Summable f := summable_of_hasFiniteSupport
    (dualJointTerm_hasFiniteSupport c coeffs hcoeff Φ hU C d t hg.1.1 hY hell)
  have hpoint (p : Ideal O × Ideal O) :
      residualEnergyTerm c ξ₁ Φ U C d t g Y ell p =
        zeroPairTerm Φ U g Y ell p + ∑' z : Ideal O × O × RayCharacter c, f (p,z) := by
    rcases p with ⟨a,b⟩
    rw [residualEnergyTerm_poisson hp c hc ξ₁ coeffs hexp Φ U hC hd hg t hY hell a b]
    congr 1
    calc
      _ = ∑' e : Ideal O, ∑' q : O × RayCharacter c, f ((a,b),(e,q)) := by
        apply tsum_congr
        intro e
        exact ((hs.prod_factor (a,b)).prod_factor e).tsum_prod.symm
      _ = _ := (hs.prod_factor (a,b)).tsum_prod.symm
  calc
    _ = ∑' p : Ideal O × Ideal O, (zeroPairTerm Φ U g Y ell p +
        ∑' z : Ideal O × O × RayCharacter c, f (p,z)) := tsum_congr hpoint
    _ = (∑' p : Ideal O × Ideal O, zeroPairTerm Φ U g Y ell p) +
        ∑' p : Ideal O × Ideal O, ∑' z : Ideal O × O × RayCharacter c, f (p,z) :=
      (summable_of_hasFiniteSupport (zeroPairTerm_hasFiniteSupport Φ U g Y ell)).tsum_add hs.prod
    _ = _ := by
      rw [zeroPairTerm_tsum]
      congr 1
      calc
        _ = ∑' z : Ideal O × O × RayCharacter c, ∑' p : Ideal O × Ideal O, f (p,z) :=
          (Summable.tsum_comm (f := fun p z => f (p,z)) hs).symm
        _ = _ := dualJointTerm_tsum_eq_outerRow c coeffs hcoeff Φ hU C d t hg.1.1 hY hell

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch.SecondCoprime
open Classical
open scoped BigOperators
open SecondPoissonProof

theorem zeroSummand_hasFiniteSupport (c : ArithmeticContext)
    {I : SupportInterval} {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C t : Ideal O) {ell : ℝ} (hell : 0 < ell) :
    Function.HasFiniteSupport (zeroSummand c U C t ell) := by
  apply (boundedIdeals (I.hi * ell)).finite_toSet.subset
  intro g hg
  by_contra hh
  exact hg (zeroSummand_eq_zero_off_support c hU C t hell g hh)

theorem column_energy_poisson (hp : PoissonStatement) (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ₁ : RayCharacter c) (coeffs : RayCharacter c → ℂ)
    (hcoeff : (Function.support coeffs).Finite) (hexp : RayExpansion c hc ξ₁ coeffs)
    {I : SupportInterval} (Φ : RowWeight) {U : ℝ → ℂ} (hU : SmoothSupported I U)
    {C d : Ideal O} (hC : Outside c.S C) (hd : d ∣ C) (t : Ideal O)
    {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    ((∑' y : O, Φ.value (normElement y / Y) *
      ‖firstColumn c ξ₁ C d t U ell y‖ ^ 2 : ℝ) : ℂ) =
      secondPoissonZero c Φ U C t Y ell + coprimeDual c Φ U coeffs C d t Y ell := by
  let A := columnCoefficient c ξ₁ U C d t ell
  let f := gcdEnergyTerm c Φ Y A
  obtain ⟨hs, hstart⟩ := firstColumn_energy_gcd c ξ₁ hU Φ C d t hY hell
  let E : Ideal O → ℂ := fun g => ∑' p : Ideal O × Ideal O, f (g,p)
  let Z : Ideal O → ℂ := fun g =>
    ((Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0) * zeroSummand c U C t ell g
  let D : Ideal O → ℂ := fun g =>
    if outerAdmissible c C t g then coprimeOuterRow c Φ U coeffs C d t Y ell g else 0
  have hE : Summable E := hs.prod
  have hZ : Summable Z :=
    (summable_of_hasFiniteSupport (zeroSummand_hasFiniteSupport c hU C t hell)).mul_left _
  have hpoint (g : Ideal O) : E g = Z g + D g := by
    by_cases hg : outerAdmissible c C t g
    · have hterm (p : Ideal O × Ideal O) : f (g,p) =
          residualEnergyTerm c ξ₁ Φ U C d t g Y ell p := by
        rcases p with ⟨a,b⟩
        exact (gcdEnergyTerm_eq_residual c ξ₁ Φ U hC hd t Y ell g a b).trans (if_pos hg)
      change (∑' p : Ideal O × Ideal O, f (g,p)) = _
      rw [tsum_congr hterm, residualEnergyTerm_tsum hp c hc ξ₁ coeffs hcoeff hexp Φ hU
        hC hd hg.1 t hY hell]
      have hraw : SquarefreeOutside c.S g ∧ IsRelPrime g (C*t) := hg
      have hzg : Z g = ((Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0) *
          ((‖U (normIdeal g / ell)‖ ^ (2 : ℕ) : ℝ) *
            ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)) := by
        change _ * (if SquarefreeOutside c.S g ∧ IsRelPrime g (C*t) then _ else 0) = _
        rw [if_pos hraw]
      have hdg : D g = coprimeOuterRow c Φ U coeffs C d t Y ell g := if_pos hg
      rw [hzg, hdg]
      ring
    · have hterm (p : Ideal O × Ideal O) : f (g,p) = 0 := by
        rcases p with ⟨a,b⟩
        exact (gcdEnergyTerm_eq_residual c ξ₁ Φ U hC hd t Y ell g a b).trans (if_neg hg)
      change (∑' p : Ideal O × Ideal O, f (g,p)) = _
      have hraw : ¬ (SquarefreeOutside c.S g ∧ IsRelPrime g (C*t)) := hg
      have hzg : Z g = 0 := by
        change _ * (if SquarefreeOutside c.S g ∧ IsRelPrime g (C*t) then _ else 0) = _
        rw [if_neg hraw, mul_zero]
      have hdg : D g = 0 := if_neg hg
      simp only [hterm, tsum_zero, hzg, hdg, add_zero]
  have hD : Summable D := by
    apply (hE.sub hZ).congr
    intro g
    have h := hpoint g
    linear_combination h
  calc
    _ = ∑' g : Ideal O, E g := hstart.trans hs.tsum_prod
    _ = ∑' g : Ideal O, (Z g + D g) := tsum_congr hpoint
    _ = (∑' g : Ideal O, Z g) + ∑' g : Ideal O, D g := hZ.tsum_add hD
    _ = _ := by
      have hz : (∑' g : Ideal O, Z g) = secondPoissonZero c Φ U C t Y ell := by
        rw [show (∑' g : Ideal O, Z g) =
          ((Y : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0) *
            ∑' g : Ideal O, zeroSummand c U C t ell g from tsum_mul_left]
        rfl
      rw [hz]
      congr 1
      unfold coprimeDual
      apply tsum_congr
      intro g
      dsimp only [D]
      by_cases hg : outerAdmissible c C t g
      · have hraw : SquarefreeOutside c.S g ∧ IsRelPrime g (C*t) := hg
        rw [if_pos hg, if_pos hraw]
        rfl
      · have hraw : ¬ (SquarefreeOutside c.S g ∧ IsRelPrime g (C*t)) := hg
        rw [if_neg hg, if_neg hraw]

end QRHShort.CloudBatch.SecondCoprime

namespace QRHShort.CloudBatch
open SecondPoissonProof

theorem second_poisson_coprime_poisson_proved : CoprimePoissonStatement := by
  intro _ha hp c hc ξ₁ coeffs hcoeff hexp I Φ U C d t Y ell hC _ht _hCt hd hY hell hU
  exact SecondCoprime.column_energy_poisson hp c hc ξ₁ coeffs hcoeff hexp Φ hU hC.1 hd t hY hell

end QRHShort.CloudBatch
