import QRHShort.SquarefreeOmegaNormCharacter
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
The actual omega character agrees with the sextic symbol at every ideal outside
S, including composite ideals and repeated prime factors. The prerequisites
below are isolated from the reflection and analytic assembly; they use the
frozen arithmetic definitions and no supplementary reciprocity assumptions.
-/

noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.SquarefreeReflection
namespace RayValuePrerequisites

/-- Bundle the selected embedding so that its ring laws are available explicitly. -/
def embeddingHom : O →+* ℂ :=
  if 0 < (rawEmbedding (omega : K)).im then
    rawEmbedding.toRingHom.comp (algebraMap O K)
  else
    (starRingEnd ℂ).comp (rawEmbedding.toRingHom.comp (algebraMap O K))

@[simp] theorem embeddingHom_apply (z : O) : embeddingHom z = embedding z := by
  unfold embeddingHom embedding
  split_ifs <;> rfl

@[simp] theorem embedding_one : embedding 1 = 1 := by
  simpa only [embeddingHom_apply] using map_one embeddingHom

@[simp] theorem embedding_pow (x : O) (n : ℕ) :
    embedding (x ^ n) = embedding x ^ n := by
  simpa only [embeddingHom_apply] using map_pow embeddingHom x n

@[simp] theorem omega_cube : omega ^ 3 = 1 :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_cube_eq_one

@[simp] theorem rootSix_pow_six : rootSix ^ 6 = 1 := by
  calc
    rootSix ^ 6 = (omega ^ 3) ^ 4 := by unfold rootSix; ring
    _ = 1 := by rw [omega_cube, one_pow]

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  simpa only [omega, IsUnit.unit_spec] using
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem rootSix_sq : rootSix ^ 2 = omega := by
  calc
    rootSix ^ 2 = omega ^ 3 * omega := by unfold rootSix; ring
    _ = omega := by rw [omega_cube, one_mul]

theorem rootSix_cube : rootSix ^ 3 = -1 := by
  calc
    rootSix ^ 3 = -(omega ^ 3) ^ 2 := by unfold rootSix; ring
    _ = -1 := by rw [omega_cube, one_pow]

theorem quotient_omega_isPrimitiveRoot (P : Ideal O) (hthree : ¬ P ∣ principal 3) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let w : O ⧸ P := Ideal.Quotient.mk P omega
  have hthree' : (3 : O ⧸ P) ≠ 0 := by
    intro h
    apply hthree
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h)
  have hw3 : w ^ 3 = 1 := by
    simpa only [map_pow, map_one] using congrArg (Ideal.Quotient.mk P) omega_cube
  have hwpoly : w ^ 2 + w + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg (Ideal.Quotient.mk P) omega_sq_add_omega_add_one
  have hw1 : w ≠ 1 := by
    intro h
    apply hthree'
    calc
      (3 : O ⧸ P) = 1 ^ 2 + 1 + 1 := by ring
      _ = 0 := by simpa only [h] using hwpoly
  refine IsPrimitiveRoot.mk_of_lt w (by decide) hw3 ?_
  intro l hl hl3
  interval_cases l
  · simpa only [pow_one] using hw1
  · intro h
    apply hw1
    calc
      w = w ^ 2 * w := by rw [h, one_mul]
      _ = w ^ 3 := by ring
      _ = 1 := hw3

theorem quotient_rootSix_isPrimitiveRoot (P : Ideal O)
    (htwo : ¬ P ∣ principal 2) (hthree : ¬ P ∣ principal 3) :
    IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6 := by
  let r : O ⧸ P := Ideal.Quotient.mk P rootSix
  have htwo' : (2 : O ⧸ P) ≠ 0 := by
    intro h
    apply htwo
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h)
  have hneg : (-1 : O ⧸ P) ≠ 1 := by
    intro h
    apply htwo'
    calc
      (2 : O ⧸ P) = 1 + 1 := by ring
      _ = 1 + -1 := by rw [h]
      _ = 0 := by ring
  have hr6 : r ^ 6 = 1 := by
    simpa only [map_pow, map_one] using
      congrArg (Ideal.Quotient.mk P) rootSix_pow_six
  have hr3 : r ^ 3 = -1 := by
    simpa only [map_pow, map_neg, map_one] using
      congrArg (Ideal.Quotient.mk P) rootSix_cube
  have hr2 : r ^ 2 = Ideal.Quotient.mk P omega := by
    simpa only [map_pow] using congrArg (Ideal.Quotient.mk P) rootSix_sq
  have hw := quotient_omega_isPrimitiveRoot P hthree
  have hr1 : r ≠ 1 := by
    intro h
    apply hneg
    simpa only [h, one_pow] using hr3.symm
  refine IsPrimitiveRoot.mk_of_lt r (by decide) hr6 ?_
  intro l hl hl6
  interval_cases l
  · simpa only [pow_one] using hr1
  · rw [hr2]
    exact hw.ne_one (by decide)
  · rw [hr3]
    exact hneg
  · intro h
    apply hw.pow_ne_one_of_pos_of_lt (l := 2) (by decide) (by decide)
    calc
      (Ideal.Quotient.mk P omega) ^ 2 = (r ^ 2) ^ 2 := by rw [hr2]
      _ = r ^ 4 := by ring
      _ = 1 := h
  · intro h
    apply hr1
    calc
      r = 1 * r := by rw [one_mul]
      _ = r ^ 5 * r := by rw [h]
      _ = r ^ 6 := by ring
      _ = 1 := hr6

theorem outside_quotient_rootSix_isPrimitiveRoot (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (houtside : Outside c.S P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6 := by
  have hnot : P ∉ c.S := by
    intro hmem
    exact houtside.2 P hmem (dvd_refl P)
  exact quotient_rootSix_isPrimitiveRoot P
    (fun h => hnot (c.above_two P hP h))
    (fun h => hnot (c.above_three P hP h))

theorem omega_sub_one_sq : (omega - 1) ^ (2 : ℕ) = -3 * omega := by
  linear_combination omega_sq_add_omega_add_one

theorem omega_sub_one_prime : Prime (omega - 1) :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem omega_sub_one_dvd_three : omega - 1 ∣ (3 : O) :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_sub_one_dvd_prime'

theorem omega_sub_one_residues (a : O) :
    omega - 1 ∣ a ∨ omega - 1 ∣ a - 1 ∨ omega - 1 ∣ a + 1 :=
  IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one
    (IsCyclotomicExtension.zeta_spec 3 ℚ K) a

theorem isPrimary_iff_three_dvd (a : O) : IsPrimary a ↔ (3 : O) ∣ a - 1 :=
  Ideal.mem_span_singleton

private theorem exists_primary_unit_of_congr_one (a : O) (ha : omega - 1 ∣ a - 1) :
    ∃ u : Oˣ, IsPrimary ((u : O) * a) := by
  let η : Oˣ := ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
    (by decide)).unit
  have hη : (η : O) = omega := IsUnit.unit_spec _
  obtain ⟨t, ht⟩ := ha
  rcases omega_sub_one_residues t with h0 | h1 | hm1
  · obtain ⟨v, hv⟩ := h0
    refine ⟨1, (isPrimary_iff_three_dvd _).mpr ⟨-omega * v, ?_⟩⟩
    simp only [Units.val_one, one_mul]
    rw [ht, hv]
    calc
      (omega - 1) * ((omega - 1) * v) = (omega - 1) ^ (2 : ℕ) * v := by ring
      _ = 3 * (-omega * v) := by rw [omega_sub_one_sq]; ring
  · obtain ⟨v, hv⟩ := h1
    have haform : a = omega + (omega - 1) ^ (2 : ℕ) * v := by
      linear_combination ht + (omega - 1) * hv
    refine ⟨η ^ (2 : ℕ), (isPrimary_iff_three_dvd _).mpr ⟨-v, ?_⟩⟩
    simp only [Units.val_pow_eq_pow_val, hη]
    rw [haform, omega_sub_one_sq]
    calc
      omega ^ (2 : ℕ) * (omega + -3 * omega * v) - 1 =
          omega ^ (3 : ℕ) - 3 * omega ^ (3 : ℕ) * v - 1 := by ring
      _ = 3 * -v := by rw [omega_cube]; ring
  · obtain ⟨v, hv⟩ := hm1
    have haform : a = 2 - omega + (omega - 1) ^ (2 : ℕ) * v := by
      linear_combination ht + (omega - 1) * hv
    refine ⟨η, (isPrimary_iff_three_dvd _).mpr ⟨omega - omega ^ (2 : ℕ) * v, ?_⟩⟩
    rw [hη, haform, omega_sub_one_sq]
    calc
      omega * (2 - omega + -3 * omega * v) - 1 =
          -(omega ^ (2 : ℕ) + omega + 1) + 3 * omega - 3 * omega ^ (2 : ℕ) * v := by ring
      _ = 3 * (omega - omega ^ (2 : ℕ) * v) := by
        rw [omega_sq_add_omega_add_one]
        ring

/-- A sixth-root unit adjusts every element prime to omega - 1 to be primary. -/
theorem exists_primary_unit_of_not_dvd (a : O) (ha : ¬ omega - 1 ∣ a) :
    ∃ u : Oˣ, IsPrimary ((u : O) * a) := by
  rcases omega_sub_one_residues a with h0 | h1 | hm1
  · exact (ha h0).elim
  · exact exists_primary_unit_of_congr_one a h1
  · have hneg : omega - 1 ∣ -a - 1 := by
      convert dvd_neg.mpr hm1 using 1 <;> ring
    obtain ⟨u, hu⟩ := exists_primary_unit_of_congr_one (-a) hneg
    refine ⟨-u, ?_⟩
    simpa only [Units.val_neg, neg_mul, mul_neg] using hu

/-- Excluding the prime above three gives a primary generator for every ideal,
not only for a prime ideal. -/
theorem exists_primary_generator_outside (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : ∃ z : O, principal z = a ∧ IsPrimary z := by
  let z := idealGenerator a
  have hz : principal z = a := Ideal.span_singleton_generator a
  have hp : Prime (principal (omega - 1)) :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have hthree : principal (omega - 1) ∣ principal 3 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three
  have hnot : ¬ omega - 1 ∣ z := by
    intro hdiv
    apply ha.2 _ (c.above_three _ hp hthree)
    rw [← hz]
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr hdiv
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  refine ⟨(u : O) * z, ?_, hu⟩
  exact (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz

theorem primaryGenerator_spec_outside (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) :
    principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) := by
  have h := exists_primary_generator_outside c ha
  simpa only [primaryGenerator, dif_pos h] using Classical.choose_spec h

/-- Every prime factor of an ideal outside `S` is itself outside `S`. -/
theorem outside_of_mem_normalizedFactors {S : Finset (Ideal O)} {n P : Ideal O}
    (hn : Outside S n) (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors n) :
    Outside S P := by
  refine ⟨(UniqueFactorizationMonoid.prime_of_normalized_factor P hP).ne_zero, ?_⟩
  intro q hq hqP
  exact hn.2 q hq (hqP.trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP))

theorem rootSix_pow_mod (m : ℕ) : rootSix ^ (m % 6) = rootSix ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 6, pow_add, pow_mul, rootSix_pow_six,
    one_pow, mul_one]

theorem sexticAtPrime_eq_of_test {P : Ideal O}
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

/-- Evaluation at any power of the distinguished sixth root uses its actual
finite-field defining test, without any reciprocity hypothesis. -/
theorem sexticAtPrime_rootSix_pow_formula {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (j : ℕ) :
    sexticAtPrime P (rootSix ^ j) =
      embedding ((rootSix ^ j) ^ ((P.absNorm - 1) / 6)) := by
  let k := (P.absNorm - 1) / 6
  have ht : Ideal.Quotient.mk P (rootSix ^ j) ^ k =
      Ideal.Quotient.mk P (rootSix ^ ((j * k) % 6)) := by
    rw [rootSix_pow_mod]
    simp only [map_pow, pow_mul]
  have h := sexticAtPrime_eq_of_test hζ (Nat.mod_lt (j * k) (by decide)) ht
  simpa only [rootSix_pow_mod, pow_mul] using h

/-- The prime omega supplement; the right side is a concrete complex root. -/
theorem sexticAtPrime_omega_formula {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) :
    sexticAtPrime P omega = embedding omega ^ ((P.absNorm - 1) / 6) := by
  simpa only [rootSix_sq, embedding_pow] using
    sexticAtPrime_rootSix_pow_formula hζ 2

/-- Away from 2 and 3, the finite residue field has order 1 modulo 6. -/
theorem prime_absNorm_mod_six {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) :
    P.absNorm % 6 = 1 := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hgt : 1 < P.absNorm := by rw [hcard]; exact Fintype.one_lt_card
  have hdvd : 6 ∣ P.absNorm - 1 := by
    rw [hcard]
    exact (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one _ (hζ.ne_zero (by decide)))
  obtain ⟨k, hk⟩ := hdvd
  omega

private theorem multiset_absNorm_mod_six (m : Multiset (Ideal O))
    (hm : ∀ P ∈ m, P.absNorm % 6 = 1) : m.prod.absNorm % 6 = 1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons P m ih =>
    rw [Multiset.prod_cons, map_mul, Nat.mul_mod,
      hm P (Multiset.mem_cons_self P m),
      ih (fun Q hQ => hm Q (Multiset.mem_cons_of_mem hQ))]

/-- The elementary exponent identity which makes the local formula extend
multiplicatively.  No claim about a residue-symbol API is used here. -/
private theorem sixth_index_mul (z : ℂ) (hz : z ^ 6 = 1)
    (a b : ℕ) (ha : a % 6 = 1) (hb : b % 6 = 1) :
    z ^ ((a * b - 1) / 6) = z ^ ((a - 1) / 6) * z ^ ((b - 1) / 6) := by
  have ha' : a = 1 + 6 * (a / 6) := by omega
  have hb' : b = 1 + 6 * (b / 6) := by omega
  have hprod : a * b =
      1 + 6 * (a / 6 + b / 6 + 6 * ((a / 6) * (b / 6))) := by
    calc
      a * b = (1 + 6 * (a / 6)) * (1 + 6 * (b / 6)) :=
        congrArg₂ (· * ·) ha' hb'
      _ = _ := by ring
  have ea : (a - 1) / 6 = a / 6 := by omega
  have eb : (b - 1) / 6 = b / 6 := by omega
  have ep : (a * b - 1) / 6 =
      a / 6 + b / 6 + 6 * ((a / 6) * (b / 6)) := by omega
  rw [ep, pow_add, pow_mul, hz, one_pow, mul_one, pow_add, ea, eb]

/-- The norm congruence applies to arbitrary powers and composite denominators. -/
theorem outside_absNorm_mod_six (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : n.absNorm % 6 = 1 := by
  rw [← Ideal.prod_normalizedFactors_eq_self hn.1]
  apply multiset_absNorm_mod_six
  intro P hP
  exact prime_absNorm_mod_six (prime_of_normalized_factor P hP)
    (outside_quotient_rootSix_isPrimitiveRoot c (prime_of_normalized_factor P hP)
      (outside_of_mem_normalizedFactors hn hP))

/-- Full multiplicative extension of the actual supplementary formula. -/
theorem sexticSymbol_rootSix_pow_formula (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (j : ℕ) :
    sexticSymbol n (rootSix ^ j) =
      embedding (rootSix ^ j) ^ ((n.absNorm - 1) / 6) := by
  have hsix : embedding (rootSix ^ j) ^ 6 = 1 := by
    rw [← embedding_pow, ← pow_mul, Nat.mul_comm j 6, pow_mul,
      rootSix_pow_six, one_pow, embedding_one]
  have hm : ∀ m : Multiset (Ideal O),
      (∀ P ∈ m, Prime P ∧
        IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) →
      (m.map (fun P => sexticAtPrime P (rootSix ^ j))).prod =
        embedding (rootSix ^ j) ^ ((m.prod.absNorm - 1) / 6) := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | @cons P m ih =>
      intro h
      have hP := h P (Multiset.mem_cons_self P m)
      have ht : ∀ Q ∈ m, Prime Q ∧
          IsPrimitiveRoot (Ideal.Quotient.mk Q rootSix) 6 :=
        fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ)
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul,
        sexticAtPrime_rootSix_pow_formula hP.2, embedding_pow, ih ht]
      exact (sixth_index_mul _ hsix _ _
        (prime_absNorm_mod_six hP.1 hP.2)
        (multiset_absNorm_mod_six m
          (fun Q hQ => prime_absNorm_mod_six (ht Q hQ).1 (ht Q hQ).2))).symm
  rw [sexticSymbol, if_neg hn.1]
  have h := hm (normalizedFactors n) (fun P hP =>
    ⟨prime_of_normalized_factor P hP,
      outside_quotient_rootSix_isPrimitiveRoot c (prime_of_normalized_factor P hP)
        (outside_of_mem_normalizedFactors hn hP)⟩)
  simpa only [Ideal.prod_normalizedFactors_eq_self hn.1] using h

/-- The omega supplement is now proved at every ideal outside the fixed S. -/
theorem sexticSymbol_omega_formula (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) :
    sexticSymbol n omega = embedding omega ^ ((n.absNorm - 1) / 6) := by
  simpa only [rootSix_sq] using sexticSymbol_rootSix_pow_formula c hn 2

end RayValuePrerequisites

open RayValuePrerequisites

/-- Any modulus supported on the frozen S is coprime to every Outside ideal. -/
theorem outside_coprime_supported_modulus (c : ArithmeticContext) (M : Ideal O)
    (hM : M ≠ ⊥) (hS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S)
    {n : Ideal O} (hn : Outside c.S n) : IsCoprime n M := by
  apply Ideal.coprime_of_no_prime_ge
  intro p hnp hmp hp
  have hp₀ : p ≠ ⊥ := by
    intro h
    exact hM (le_bot_iff.mp (h ▸ hmp))
  have hp' := Ideal.prime_of_isPrime hp₀ hp
  exact hn.2 p (hS p hp' (Ideal.dvd_iff_le.mpr hmp))
    (Ideal.dvd_iff_le.mpr hnp)

theorem primaryGenerator_unit_mod_supported (c : ArithmeticContext)
    (M : Ideal O) (hM : M ≠ ⊥)
    (hS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S)
    {n : Ideal O} (hn : Outside c.S n) :
    IsUnit (Ideal.Quotient.mk M (primaryGenerator n)) := by
  obtain ⟨i, hi, j, hj, hij⟩ :=
    (outside_coprime_supported_modulus c M hM hS hn).exists
  rw [← (primaryGenerator_spec_outside c hn).1] at hi
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hi
  have h := congrArg (Ideal.Quotient.mk M) hij
  have hj₀ := Ideal.Quotient.eq_zero_iff_mem.mpr hj
  simp only [map_add, map_mul, hj₀, add_zero, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk M b, h⟩

/-- Actual descent, valid at EVERY ideal outside S, not just at prime ideals
    or at norms in a scalar model.  No arithmetic relation is needed here. -/
theorem omegaHeckeCharacter_rayValue (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) :
    rayValue omegaHeckeCharacter n = sexticSymbol n omega := by
  have hx := primaryGenerator_unit_mod_supported c omegaHeckeCharacter.modulus
    omegaHeckeCharacter.modulus_ne_bot (omegaHeckeCharacter_supported c) hn
  have hgen := (primaryGenerator_spec_outside c hn).1
  have hN : (principal (primaryGenerator n)).absNorm % 6 = 1 := by
    rw [hgen]
    exact outside_absNorm_mod_six c hn
  rw [rayValue, omegaHeckeCharacter_onElement_formula hx hN, hgen,
    sexticSymbol_omega_formula c hn]

end QRHShort.SquarefreeReflection

set_option pp.fullNames true

#print axioms QRHShort.SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
#print axioms QRHShort.SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside
#print axioms QRHShort.SquarefreeReflection.RayValuePrerequisites.outside_absNorm_mod_six
#print axioms QRHShort.SquarefreeReflection.RayValuePrerequisites.sexticSymbol_omega_formula
#print axioms QRHShort.SquarefreeReflection.primaryGenerator_unit_mod_supported
#print axioms QRHShort.SquarefreeReflection.omegaHeckeCharacter_rayValue
