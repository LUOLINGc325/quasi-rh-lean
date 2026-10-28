import QRHShort.QuadraticProductConductor
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
The finite multiplicative class map for the concrete quadratic family.  The
first coordinate is the primary generator modulo four; the second records
the sign that controls the auxiliary factor at the prime above three.
Multiplicativity is proved for all ideals coprime to six, including ideals
with repeated prime factors, as required by `QuadraticHeckeFamily`.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem quadratic_isPrimary_mul {a b : O} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  apply (isPrimary_iff_three_dvd _).mpr
  have h := dvd_add (dvd_mul_of_dvd_left ((isPrimary_iff_three_dvd a).mp ha) b)
    ((isPrimary_iff_three_dvd b).mp hb)
  convert h using 1 <;> ring

theorem quadratic_isPrimary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) : u = 1 := by
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

theorem quadratic_primary_eq_of_principal_eq {a b : O}
    (ha : IsPrimary a) (hb : IsPrimary b) (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [quadratic_isPrimary_unit_eq_one u hup, Units.val_one, mul_one] using hu

theorem quadratic_primaryGenerator_one : primaryGenerator 1 = 1 := by
  have hs := quadratic_primaryGenerator_spec 1 isRelPrime_one_left
  exact quadratic_primary_eq_of_principal_eq hs.2 (by simp [IsPrimary])
    (hs.1.trans (by simp [principal]))

theorem quadratic_primaryGenerator_mul {a b : Ideal O}
    (ha : IsRelPrime a (principal 3)) (hb : IsRelPrime b (principal 3)) :
    primaryGenerator (a * b) = primaryGenerator a * primaryGenerator b := by
  have ha' := quadratic_primaryGenerator_spec a ha
  have hb' := quadratic_primaryGenerator_spec b hb
  have hab' := quadratic_primaryGenerator_spec (a * b) (ha.mul_left hb)
  apply quadratic_primary_eq_of_principal_eq hab'.2 (quadratic_isPrimary_mul ha'.2 hb'.2)
  rw [hab'.1]
  change a * b = Ideal.span {primaryGenerator a * primaryGenerator b}
  rw [← Ideal.span_singleton_mul_span_singleton]
  change a * b = principal (primaryGenerator a) * principal (primaryGenerator b)
  rw [ha'.1, hb'.1]

/-- The sign has order two without any squarefreeness hypothesis. -/
theorem quadratic_sextic_neg_one_sq_all (a : Ideal O) (ha : FamilyIdeal (principal 6) a) :
    (sexticSymbol a (-1) ^ (3 : ℕ)) ^ (2 : ℕ) = 1 := by
  rw [sexticSymbol, if_neg ha.1, ← Multiset.prod_map_pow, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  have hprime : Prime P := prime_of_normalized_factor P hP
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hnot : ¬ P ∣ principal 6 := fun h =>
    hprime.not_unit (ha.2 (dvd_of_mem_normalizedFactors hP) h)
  rw [sexticAtPrime_cube_eq_quadraticResidueChar P
    (fun h => hnot (h.trans quadratic_two_dvd_six))
    (fun h => hnot (h.trans quadratic_three_dvd_six))]
  exact quadraticResidueChar_sq _ _ ((isUnit_neg_one : IsUnit (-1 : O)).map
    (Ideal.Quotient.mk P))

theorem quadratic_isCoprime_of_isRelPrime {a b : Ideal O} (h : IsRelPrime a b) :
    IsCoprime a b := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left)
    (Ideal.dvd_iff_le.mpr le_sup_right))

theorem quadratic_primary_mod_four_unit (a : Ideal O) (ha : FamilyIdeal (principal 6) a) :
    IsUnit (Ideal.Quotient.mk (principal 4) (primaryGenerator a)) := by
  have h2 : IsRelPrime a (principal 2) := ha.2.of_dvd_right quadratic_two_dvd_six
  have h4 : IsRelPrime a (principal 4) := by
    have h := h2.mul_right h2
    have hmul : principal (2 : O) * principal 2 = principal 4 := by
      change Ideal.span {(2 : O)} * Ideal.span {(2 : O)} = Ideal.span {(4 : O)}
      rw [Ideal.span_singleton_mul_span_singleton]
      norm_num
    rwa [hmul] at h
  have hcop : IsCoprime (primaryGenerator a) (4 : O) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    change IsCoprime (principal (primaryGenerator a)) (principal 4)
    rw [(quadratic_primaryGenerator_spec a
      (ha.2.of_dvd_right quadratic_three_dvd_six)).1]
    exact quadratic_isCoprime_of_isRelPrime h4
  have hzero : Ideal.Quotient.mk (principal 4) (4 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  exact isCoprime_zero_right.mp (by
    simpa only [hzero] using hcop.map (Ideal.Quotient.mk (principal 4)))

instance quadratic_four_neZero : NeZero (principal (4 : O)) :=
  ⟨Ideal.span_singleton_eq_bot.not.mpr (by norm_num)⟩

abbrev QuadraticRayGroup := (O ⧸ principal (4 : O))ˣ × rootsOfUnity 2 ℂ

instance quadraticRayGroup_fintype : Fintype QuadraticRayGroup := Fintype.ofFinite _

def quadraticRayClass (a : Ideal O) : QuadraticRayGroup :=
  if ha : FamilyIdeal (principal 6) a then
    ((quadratic_primary_mod_four_unit a ha).unit,
      rootsOfUnity.mkOfPowEq (sexticSymbol a (-1) ^ (3 : ℕ))
        (quadratic_sextic_neg_one_sq_all a ha))
  else 1

theorem quadraticRayClass_one : quadraticRayClass 1 = 1 := by
  have h1 : FamilyIdeal (principal 6) 1 := ⟨one_ne_zero, isRelPrime_one_left⟩
  rw [quadraticRayClass, dif_pos h1]
  apply Prod.ext
  · apply Units.ext
    simp only [IsUnit.unit_spec, quadratic_primaryGenerator_one, map_one, Units.val_one,
      Prod.fst_one]
  · apply Subtype.ext
    apply Units.ext
    change sexticSymbol (1 : Ideal O) (-1) ^ (3 : ℕ) = 1
    rw [sexticSymbol, if_neg (show (1 : Ideal O) ≠ ⊥ from one_ne_zero),
      normalizedFactors_one]
    simp

theorem quadraticRayClass_mul (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b) :
    quadraticRayClass (a * b) = quadraticRayClass a * quadraticRayClass b := by
  have hab : FamilyIdeal (principal 6) (a * b) :=
    ⟨mul_ne_zero ha.1 hb.1, ha.2.mul_left hb.2⟩
  rw [quadraticRayClass, dif_pos hab, quadraticRayClass, dif_pos ha,
    quadraticRayClass, dif_pos hb]
  apply Prod.ext
  · apply Units.ext
    simp only [Prod.fst_mul, Units.val_mul, IsUnit.unit_spec]
    rw [quadratic_primaryGenerator_mul (ha.2.of_dvd_right quadratic_three_dvd_six)
      (hb.2.of_dvd_right quadratic_three_dvd_six), map_mul]
  · apply Subtype.ext
    apply Units.ext
    simp only [Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, rootsOfUnity.coe_mkOfPowEq]
    rw [quadratic_sexticSymbol_mul, mul_pow]

theorem quadraticRayClass_eq_sign (a b : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hb : FamilyIdeal (principal 6) b)
    (h : quadraticRayClass a = quadraticRayClass b) :
    sexticSymbol a (-1) ^ (3 : ℕ) = sexticSymbol b (-1) ^ (3 : ℕ) := by
  have he := congrArg (fun g : QuadraticRayGroup => ((g.2 : ℂˣ) : ℂ)) h
  simpa only [quadraticRayClass, dif_pos ha, dif_pos hb,
    rootsOfUnity.coe_mkOfPowEq] using he

theorem quadraticRayClass_product_conductor
    (a b : Ideal O) (ha : FamilyIdeal (principal 6) a)
    (hb : FamilyIdeal (principal 6) b) (hsqa : Squarefree a) (hsqb : Squarefree b)
    (hcop : IsRelPrime a b) (hclass : quadraticRayClass a = quadraticRayClass b) :
    ∃ ψ : HeckeCharacter, ψ.modulus = a * b ∧ ψ.IsPrimitive ∧
      ∀ x : O, IsUnit (Ideal.Quotient.mk
        (a * b * (quadraticCharacter a).modulus * (quadraticCharacter b).modulus) x) →
        ψ.onElement x = (quadraticCharacter a).onElement x *
          (quadraticCharacter b).onElement x :=
  quadraticCharacter_product_conductor a b ha hb hsqa hsqb hcop
    (quadraticRayClass_eq_sign a b ha hb hclass)

end QRHShort

#print axioms QRHShort.quadraticRayClass_mul
#print axioms QRHShort.quadraticRayClass_product_conductor
