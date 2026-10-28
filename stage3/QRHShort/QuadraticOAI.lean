import QRHShort.QuadraticPrimeReciprocity
import OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss

/-!
Glue between the concrete family support predicate and the OAI quadratic-sieve
row interface.  The finite-family estimate itself remains the upstream OAI
result; this file only packages the hypotheses needed at the QRH boundary.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

open OAI

/-- Every squarefree ideal in the `(6)`-family is OAI-admissible. -/
theorem family_admissible (a : Ideal O) (ha : FamilyIdeal (principal 6) a)
    (hsq : Squarefree a) : OAI.CanonicalQuadraticSieve.Admissible a := by
  refine ⟨ha.1, hsq, ?_⟩
  intro P hP
  have hprime : Prime P :=
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hPdiv : P ∣ a :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hPm : FamilyIdeal (principal 6) P := by
    refine ⟨hprime.ne_zero, ?_⟩
    intro d hd h6
    exact ha.2 (hd.trans hPdiv) h6
  exact ⟨quadraticPrime_not_lambda P hprime hPm,
    quadraticPrime_char_ne_two P hprime hPm⟩

/-- At every prime factor of a family ideal, the concrete sextic symbol cubed
agrees with OAI canonical quadratic residue character. -/
theorem prime_sextic_symbol_of_family (P : Ideal O) [P.IsMaximal] (hP : Prime P)
    (hPm : FamilyIdeal (principal 6) P) (x : O) :
    sexticAtPrime P x ^ (3 : ℕ) =
      (OAI.ActualEisensteinCubic.canonicalSextic P
        (quadraticPrime_not_lambda P hP hPm)) (Ideal.Quotient.mk P x) ^ (3 : ℕ) := by
  have htwo : ¬ P ∣ principal 2 := by
    intro h
    exact hP.not_unit (hPm.2 dvd_rfl (h.trans quadratic_two_dvd_six))
  have hthree : ¬ P ∣ principal 3 := by
    intro h
    exact hP.not_unit (hPm.2 dvd_rfl (h.trans quadratic_three_dvd_six))
  rw [sexticAtPrime_cube_eq_quadraticResidueChar P htwo hthree x]
  rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
    OAI.ActualEisensteinCubic.canonicalSextic_pow_three_quadratic]
  rfl

/-- Package the ambient-family row identity from OAI. -/
theorem oai_quadraticRow_eq_ambient
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F,
      OAI.CanonicalQuadraticSieve.Admissible I)
    (I : Ideal O) (hI : I ∈ F) (z : O) :
    OAI.CanonicalQuadraticSieve.quadraticRow I z =
      (OAI.ConcretePrimeRowBridge.idealSexticRow F
        (fun J hJ => (hF J hJ).1)
        (fun J hJ P hP => (hF J hJ).2.2 P hP |>.1) I z) ^ (3 : ℕ) := by
  exact OAI.CanonicalQuadraticSieve.quadraticRow_eq F hF I hI z

/- The singleton-family row is exactly the cubed concrete sextic symbol. -/
theorem oai_quadraticRow_eq_sextic_cube (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) (hsq : Squarefree a) (x : O) :
    OAI.CanonicalQuadraticSieve.quadraticRow a x = sexticSymbol a x ^ (3 : ℕ) := by
  have hadm : OAI.CanonicalQuadraticSieve.Admissible a :=
    family_admissible a ha hsq
  have hF : ∀ I ∈ ({a} : Finset (Ideal O)),
      OAI.CanonicalQuadraticSieve.Admissible I := by
    intro I hI
    simpa only [Finset.mem_singleton.mp hI] using hadm
  have hfac_pool (i : OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O))) :
      i.val ∈ normalizedFactors a := by
    obtain ⟨I, hI, hfac⟩ :=
      OAI.ConcretePrimeRowBridge.mem_primePool_iff.mp i.property
    simpa only [Finset.mem_singleton.mp hI] using hfac
  have hFpos : ∀ I ∈ ({a} : Finset (Ideal O)), I ≠ ⊥ := by
    intro I hI
    simpa only [Finset.mem_singleton.mp hI] using ha.1
  letI : ∀ i : OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O)),
      i.val.IsMaximal :=
    OAI.ConcretePrimeRowBridge.primePool_maximal {a} hFpos
  let f : OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O)) → ℂ :=
    fun i => (OAI.ActualEisensteinCubic.canonicalSextic i.val
      ((hF a (Finset.mem_singleton_self a)).2.2 i.val (hfac_pool i)).1)
      (Ideal.Quotient.mk i.val x)
  rw [oai_quadraticRow_eq_ambient {a} hF a (Finset.mem_singleton_self a) x]
  simp only [OAI.ConcretePrimeRowBridge.idealSexticRow,
    OAI.ActualEisensteinCubic.finiteSquarefreeRow,
    OAI.CanonicalQuadraticSieve.idealSupport_singleton_univ,
    Finset.prod_pow]
  change (∏ i : OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O)), f i) ^ (3 : ℕ) = _
  have hnodup : (normalizedFactors a).Nodup :=
    (squarefree_iff_nodup_normalizedFactors ha.1).mp hsq
  rw [sexticSymbol, if_neg ha.1, ← Multiset.prod_map_pow]
  have hprod :
      (∏ P ∈ (normalizedFactors a).toFinset, sexticAtPrime P x ^ (3 : ℕ)) =
        (Multiset.map (fun P => sexticAtPrime P x ^ (3 : ℕ))
          (normalizedFactors a)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
  rw [← hprod]
  let idx (i : OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O)))
      (_hi : i ∈ (OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O))).attach) :
      Ideal O := i.val
  calc
    (∏ i : OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O)), f i) ^ (3 : ℕ) =
        (∏ i ∈ (OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O))).attach, f i) ^ (3 : ℕ) := by
      exact congrArg (fun z : ℂ => z ^ (3 : ℕ)) (Finset.prod_coe_sort_eq_attach _ _)
    _ = ∏ i ∈ (OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O))).attach,
        f i ^ (3 : ℕ) := by rw [Finset.prod_pow]
    _ = ∏ P ∈ (normalizedFactors a).toFinset, sexticAtPrime P x ^ (3 : ℕ) := by
      apply Finset.prod_bij idx
      · intro i hi
        obtain ⟨I, hI, hfac⟩ :=
          OAI.ConcretePrimeRowBridge.mem_primePool_iff.mp i.property
        have hIa : I = a := Finset.mem_singleton.mp hI
        exact Multiset.mem_toFinset.mpr (hIa ▸ hfac)
      · intro i hi j hj hij
        exact Subtype.ext hij
      · intro j hj
        have hfac : j ∈ normalizedFactors a := Multiset.mem_toFinset.mp hj
        have hp : j ∈ OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O)) := by
          apply OAI.ConcretePrimeRowBridge.mem_primePool_iff.mpr
          exact ⟨a, Finset.mem_singleton_self a, hfac⟩
        let i : OAI.ConcretePrimeRowBridge.primePool ({a} : Finset (Ideal O)) := ⟨j, hp⟩
        exact ⟨i, by simp, rfl⟩
      · intro i hi
        obtain ⟨I, hI, hfac⟩ :=
          OAI.ConcretePrimeRowBridge.mem_primePool_iff.mp i.property
        have hIa : I = a := Finset.mem_singleton.mp hI
        have hPfac : i.val ∈ normalizedFactors a := hIa ▸ hfac
        have hprime : Prime i.val :=
          UniqueFactorizationMonoid.prime_of_normalized_factor i.val hPfac
        have hPm : FamilyIdeal (principal 6) i := by
          refine ⟨hprime.ne_zero, ?_⟩
          intro d hd h6
          exact ha.2 (hd.trans
            (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPfac)) h6
        simpa [f, idx] using (prime_sextic_symbol_of_family i.val hprime hPm x).symm

/- The two totalized primary-generator choices agree on the concrete family.
The OAI choice is primary modulo `lambda ^ 2`; the identity
`3 ∣ lambda ^ 2` converts this to the QRH modulo-three primary condition. -/
theorem oai_primaryGenerator_eq_quadratic (a : Ideal O)
    (ha : FamilyIdeal (principal 6) a) :
    OAI.CompletedGauss.primaryGenerator a = primaryGenerator a := by
  have hO0 : OAI.CompletedGauss.primaryGenerator a ≠ 0 := by
    apply OAI.PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors a ha.1
    intro P hP
    have hprime : Prime P :=
      UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    have hPdiv : P ∣ a :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hPm : FamilyIdeal (principal 6) P := by
      refine ⟨hprime.ne_zero, ?_⟩
      intro d hd h6
      exact ha.2 (hd.trans hPdiv) h6
    exact quadraticPrime_not_lambda P hprime hPm
  have hO := OAI.CompletedGauss.primaryGenerator_spec a hO0
  have hOprim : IsPrimary (OAI.CompletedGauss.primaryGenerator a) := by
    apply (isPrimary_iff_three_dvd _).mpr
    have hthree : (3 : O) ∣
        (OAI.CompletedGauss.primaryGenerator a - 1) := by
      apply (show (3 : O) ∣ (OAI.ActualEisensteinCubic.lambda ^ 2) from
        OAI.CubicEisenstein.three_dvd_lambda_sq).trans
      exact hO.2
    exact hthree
  have hQ := quadratic_primaryGenerator_spec a
    (ha.2.of_dvd_right quadratic_three_dvd_six)
  apply quadratic_primary_eq_of_principal_eq hOprim hQ.2
  exact hO.1.trans hQ.1.symm

theorem quadratic_oai_transfer_row
    (a b : Ideal O) (ha : FamilyIdeal (principal 6) a)
    (hb : FamilyIdeal (principal 6) b) (hsqb : Squarefree b) :
    OAI.CanonicalQuadraticSieve.quadraticRow b
        (OAI.CompletedGauss.primaryGenerator a) =
      (quadraticCharacter b).onIdeal a := by
  rw [oai_quadraticRow_eq_sextic_cube b hb hsqb]
  rw [quadraticCharacter_onIdeal b hb hsqb a ha.1
    (ha.2.of_dvd_right quadratic_three_dvd_six)]
  rw [oai_primaryGenerator_eq_quadratic a ha]

/-- The OAI finite-family bound with rows and columns carrying only the
concrete `(6)`-family hypotheses. -/
theorem oai_finite_family_quadratic_large_sieve
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (M N : ℝ), 1 ≤ M → 1 ≤ N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal O) (cols : n → Ideal O),
      Function.Injective rows → Function.Injective cols →
      (∀ i, FamilyIdeal (principal 6) (rows i) ∧ Squarefree (rows i) ∧
        (Ideal.absNorm (rows i) : ℝ) ≤ M) →
      (∀ j, FamilyIdeal (principal 6) (cols j) ∧ Squarefree (cols j) ∧
        (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      ∀ a : n → ℂ,
      (∑ i, ‖∑ j, OAI.CanonicalQuadraticSieve.quadraticRow (cols j)
        (OAI.CompletedGauss.primaryGenerator (rows i)) * a j‖ ^ 2) ≤
        C * (M * N) ^ ε * (M + N) * ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    OAI.CanonicalQuadraticSieve.finite_family_quadratic_large_sieve ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  apply hbound M N hM hN rows cols hr hc
  · intro i
    exact ⟨family_admissible (rows i) (hrows i).1 (hrows i).2.1,
      (hrows i).2.2⟩
  · intro j
    exact ⟨family_admissible (cols j) (hcols j).1 (hcols j).2.1,
      (hcols j).2.2⟩

end QRHShort

#print axioms QRHShort.family_admissible
#print axioms QRHShort.prime_sextic_symbol_of_family
#print axioms QRHShort.oai_quadraticRow_eq_ambient
#print axioms QRHShort.oai_finite_family_quadratic_large_sieve
#print axioms QRHShort.prime_sextic_symbol_of_family
