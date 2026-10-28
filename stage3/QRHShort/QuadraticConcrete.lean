import QRHShort.QuadraticCorrection
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
The actual primitive quadratic Hecke characters attached to squarefree ideals
coprime to 6, and their exact evaluation as `sexticSymbol ^ 3` on primary
generators.  Reciprocity and the final sieve assembly are separate remaining
obligations; no instance of `QuadraticHeckeFamily` is asserted here.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

abbrev QuadraticFactor (a : Ideal O) := ↥(normalizedFactors a).toFinset

def quadraticFactorIdeal (a : Ideal O) (i : QuadraticFactor a) : Ideal O := i.val

theorem quadraticFactor_prime (a : Ideal O) (i : QuadraticFactor a) :
    Prime (quadraticFactorIdeal a i) :=
  prime_of_normalized_factor i.val (Multiset.mem_toFinset.mp i.property)

theorem quadraticFactor_dvd (a : Ideal O) (i : QuadraticFactor a) :
    quadraticFactorIdeal a i ∣ a :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp i.property)

instance quadraticFactor_maximal (a : Ideal O) (i : QuadraticFactor a) :
    (quadraticFactorIdeal a i).IsMaximal :=
  (Ideal.isPrime_of_prime (quadraticFactor_prime a i)).isMaximal
    (quadraticFactor_prime a i).ne_zero

theorem quadraticFactor_pairwise (a : Ideal O) :
    Pairwise (Function.onFun IsCoprime (quadraticFactorIdeal a)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hij (Subtype.ext h)

theorem quadraticFactor_prod_ne_bot (a : Ideal O) :
    Finset.univ.prod (quadraticFactorIdeal a) ≠ ⊥ :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (quadraticFactor_prime a i).ne_zero)

theorem quadraticFactor_prod {a : Ideal O} (ha : a ≠ ⊥) (hsq : Squarefree a) :
    Finset.univ.prod (quadraticFactorIdeal a) = a := by
  have hnodup := (squarefree_iff_nodup_normalizedFactors ha).mp hsq
  calc
    Finset.univ.prod (quadraticFactorIdeal a) =
        ∏ P ∈ (normalizedFactors a).toFinset, P := by
      exact Finset.prod_coe_sort (s := (normalizedFactors a).toFinset) (f := id)
    _ = (normalizedFactors a).toFinset.val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors a).prod := by rw [Multiset.toFinset_val, hnodup.dedup]
    _ = a := Ideal.prod_normalizedFactors_eq_self ha

theorem quadratic_two_dvd_six : principal 2 ∣ principal 6 := by
  apply Ideal.dvd_span_singleton.mpr
  exact Ideal.mem_span_singleton.mpr ⟨3, by ring⟩

theorem quadratic_three_dvd_six : principal 3 ∣ principal 6 := by
  apply Ideal.dvd_span_singleton.mpr
  exact Ideal.mem_span_singleton.mpr ⟨2, by ring⟩

theorem quadraticLambda_dvd_three : quadraticLambdaIdeal ∣ principal 3 :=
  Ideal.dvd_span_singleton.mpr (Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three)

theorem quadraticFactor_not_dvd_six (a : Ideal O) (hcop : IsRelPrime a (principal 6))
    (i : QuadraticFactor a) : ¬ quadraticFactorIdeal a i ∣ principal 6 :=
  fun h => (quadraticFactor_prime a i).not_unit (hcop (quadraticFactor_dvd a i) h)

theorem quadraticFactor_lambda_coprime (a : Ideal O) (hcop : IsRelPrime a (principal 6))
    (i : QuadraticFactor a) : IsCoprime quadraticLambdaIdeal (quadraticFactorIdeal a i) := by
  apply Ideal.isCoprime_of_isMaximal
  intro h
  apply quadraticFactor_not_dvd_six a hcop i
  rw [← h]
  exact quadraticLambda_dvd_three.trans quadratic_three_dvd_six

theorem quadraticFactor_odd (a : Ideal O) (hcop : IsRelPrime a (principal 6))
    (i : QuadraticFactor a) : ringChar (O ⧸ quadraticFactorIdeal a i) ≠ 2 := by
  intro hchar
  have htwo : (2 : O ⧸ quadraticFactorIdeal a i) = 0 :=
    (ringChar.spec _ 2).mpr (by rw [hchar])
  apply quadraticFactor_not_dvd_six a hcop i
  apply Dvd.dvd.trans _ quadratic_two_dvd_six
  apply Ideal.dvd_span_singleton.mpr
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using htwo)

theorem quadraticFactor_product_eq_sextic_cube {a : Ideal O}
    (ha : a ≠ ⊥) (hcop : IsRelPrime a (principal 6)) (hsq : Squarefree a) (x : O) :
    quadraticElementProduct (quadraticFactorIdeal a) x = sexticSymbol a x ^ (3 : ℕ) := by
  have hnodup := (squarefree_iff_nodup_normalizedFactors ha).mp hsq
  rw [sexticSymbol, if_neg ha, ← Multiset.prod_map_pow]
  calc
    quadraticElementProduct (quadraticFactorIdeal a) x =
        ∏ i : QuadraticFactor a, sexticAtPrime (quadraticFactorIdeal a i) x ^ (3 : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (sexticAtPrime_cube_eq_quadraticResidueChar (quadraticFactorIdeal a i)
        (fun h => quadraticFactor_not_dvd_six a hcop i (h.trans quadratic_two_dvd_six))
        (fun h => quadraticFactor_not_dvd_six a hcop i (h.trans quadratic_three_dvd_six)) x).symm
    _ = ∏ P ∈ (normalizedFactors a).toFinset, sexticAtPrime P x ^ (3 : ℕ) := by
      exact Finset.prod_coe_sort (s := (normalizedFactors a).toFinset)
        (f := fun P => sexticAtPrime P x ^ (3 : ℕ))
    _ = ((normalizedFactors a).map (fun P => sexticAtPrime P x ^ (3 : ℕ))).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]

theorem quadratic_primaryGenerator_spec (a : Ideal O) (hcop : IsRelPrime a (principal 3)) :
    principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) := by
  let z := idealGenerator a
  have hz : principal z = a := Ideal.span_singleton_generator a
  have hp : Prime quadraticLambdaIdeal :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have hnot : ¬ omega - 1 ∣ z := by
    intro hdiv
    apply hp.not_unit
    apply hcop _ quadraticLambda_dvd_three
    rw [← hz]
    exact Ideal.dvd_span_singleton.mpr (Ideal.mem_span_singleton.mpr hdiv)
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  have hex : ∃ x : O, principal x = a ∧ IsPrimary x :=
    ⟨(u : O) * z, (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz, hu⟩
  simpa only [primaryGenerator, dif_pos hex] using Classical.choose_spec hex

def quadraticTrivialHecke : HeckeCharacter where
  modulus := 1
  modulus_ne_bot := one_ne_zero
  residue := 1
  unit_trivial := fun u => MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk 1))

/-- The concrete character used on the actual squarefree rows. -/
def quadraticCharacter (a : Ideal O) : HeckeCharacter :=
  if ha : FamilyIdeal (principal 6) a ∧ Squarefree a then
    correctedQuadraticHecke (quadraticFactorIdeal a) (quadraticFactor_pairwise a)
      (quadraticFactor_prod_ne_bot a) (quadraticFactor_lambda_coprime a ha.1.2)
  else quadraticTrivialHecke

theorem quadraticCharacter_primitive (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a) :
    (quadraticCharacter a).IsPrimitive := by
  rw [quadraticCharacter, dif_pos ⟨ha, hsq⟩]
  exact correctedQuadraticHecke_primitive _ _ _ _ (quadraticFactor_odd a ha.2)

theorem quadraticCharacter_quadratic (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a) (x : O)
    (hx : IsUnit (Ideal.Quotient.mk (quadraticCharacter a).modulus x)) :
    (quadraticCharacter a).onElement x ^ (2 : ℕ) = 1 := by
  rw [quadraticCharacter, dif_pos ⟨ha, hsq⟩] at *
  exact correctedQuadraticHecke_quadratic _ _ _ _ x hx

theorem quadraticCharacter_modulus (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a) :
    (quadraticCharacter a).modulus =
      if sexticSymbol a (-1) ^ (3 : ℕ) = 1 then a else quadraticLambdaIdeal * a := by
  rw [quadraticCharacter, dif_pos ⟨ha, hsq⟩, correctedQuadraticHecke_modulus,
    quadraticFactor_prod ha.1 hsq,
    quadraticFactor_product_eq_sextic_cube ha.1 ha.2 hsq]

theorem quadraticCharacter_onPrimary (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a) (x : O) (hx : IsPrimary x) :
    (quadraticCharacter a).onElement x = sexticSymbol a x ^ (3 : ℕ) := by
  rw [quadraticCharacter, dif_pos ⟨ha, hsq⟩, correctedQuadraticHecke_primary _ _ _ _ x hx]
  exact quadraticFactor_product_eq_sextic_cube ha.1 ha.2 hsq x

/-- Exact identification with the kernel in the frozen quadratic estimate,
including zero values when the two ideals share a prime. -/
theorem quadraticCharacter_onIdeal (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a)
    (b : Ideal O) (hb : b ≠ ⊥) (hb3 : IsRelPrime b (principal 3)) :
    (quadraticCharacter a).onIdeal b =
      sexticSymbol a (primaryGenerator b) ^ (3 : ℕ) := by
  have hgen := quadratic_primaryGenerator_spec b hb3
  rw [(quadraticCharacter a).onIdeal_of_generator hb hgen.1]
  exact quadraticCharacter_onPrimary a ha hsq _ hgen.2

end QRHShort

#print axioms QRHShort.quadraticCharacter_primitive
#print axioms QRHShort.quadraticCharacter_onIdeal
