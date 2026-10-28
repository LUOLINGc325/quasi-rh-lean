import QRHShort.ThetaCoefficientBridge

/-! The change of additive character in the actual cubic Gauss sum.  The
independently defined cubic and sextic symbols are compared at each prime;
multiplication by lambda then permutes the finite quotient. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ThetaRealizationProof.GaussLambda
open ArithmeticProof SquarefreeReflection
open SquarefreeReflection.RayValuePrerequisites

theorem omega_pow_mod (j : ℕ) : omega ^ (j % 3) = omega ^ j := by
  conv_rhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, omega_cube,
    one_pow, mul_one]

theorem cubicAtPrime_eq_of_test {P : Ideal O}
    (hw : IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3)
    {a : O} {j : ℕ} (hj : j < 3)
    (ht : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3) =
      Ideal.Quotient.mk P (omega ^ j)) :
    cubicAtPrime P a = embedding (omega ^ j) := by
  unfold cubicAtPrime
  rw [Finset.sum_eq_single j]
  · exact if_pos ht
  · intro i hi hij
    apply if_neg
    intro hiTest
    apply hij
    apply hw.pow_inj (Finset.mem_range.mp hi) hj
    simpa only [map_pow] using hiTest.symm.trans ht
  · exact fun h => (h (Finset.mem_range.mpr hj)).elim

theorem cubicAtPrime_eq_sexticAtPrime_sq {P : Ideal O} (hP : Prime P)
    (hz : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a : O) :
    cubicAtPrime P a = sexticAtPrime P a ^ (2 : ℕ) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hdvd : 6 ∣ P.absNorm - 1 := by
    rw [hcard]
    exact (hz.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one _ (hz.ne_zero (by decide)))
  have hexp : (P.absNorm - 1) / 3 = ((P.absNorm - 1) / 6) * 2 := by omega
  have hw : IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
    simpa only [← map_pow, rootSix_sq] using
      hz.pow_of_dvd (p := 2) (by decide) (by decide)
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hP hz ha, zero_pow (by decide)]
    have hpos : 0 < (P.absNorm - 1) / 3 := by
      have hc := Fintype.one_lt_card (α := O ⧸ P)
      rw [← hcard] at hc
      omega
    unfold cubicAtPrime
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_pow (Nat.ne_of_gt hpos), map_pow]
    exact (pow_ne_zero j (hw.ne_zero (by decide))).symm
  · obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hP hz ha
    have ht3 : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3) =
        Ideal.Quotient.mk P (omega ^ (j % 3)) := by
      calc
        _ = (Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6)) ^ 2 := by
          rw [← pow_mul, hexp]
        _ = Ideal.Quotient.mk P ((rootSix ^ j) ^ 2) := by simp only [ht, map_pow]
        _ = _ := by
          congr 1
          rw [← pow_mul, Nat.mul_comm j 2, pow_mul, rootSix_sq, omega_pow_mod]
    rw [cubicAtPrime_eq_of_test hw (Nat.mod_lt _ (by decide)) ht3,
      sexticAtPrime_eq_of_test hz hj ht, ← embedding_pow]
    congr 1
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, rootSix_sq, omega_pow_mod]

theorem cubicSymbol_eq_sexticSymbol_sq (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (a : O) : cubicSymbol n a = sexticSymbol n a ^ (2 : ℕ) := by
  rw [cubicSymbol, sexticSymbol, if_neg hn.1, if_neg hn.1,
    ← Multiset.prod_map_pow]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  exact cubicAtPrime_eq_sexticAtPrime_sq
    (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    (outside_quotient_rootSix_isPrimitiveRoot c
      (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
      (outside_of_mem_normalizedFactors hn hP)) a

theorem symbol_congr {n : Ideal O} {a b : O}
    (hab : Ideal.Quotient.mk n a = Ideal.Quotient.mk n b) :
    sexticSymbol n a = sexticSymbol n b := by
  by_cases hn : n = ⊥
  · simp [sexticSymbol, hn]
  simp only [sexticSymbol, if_neg hn]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hnP : n ≤ P := Ideal.dvd_iff_le.mp
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
  have habP : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr
      (hnP ((Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab))
  simp only [sexticAtPrime, habP]

theorem additive_eq_breveE (z : ℂ) :
    additiveCharacter z = OAI.ShortDraftTrace.breveE (z / OAI.ConcreteTraceCRT.eisLam) := by
  change additiveCharacter z =
    OAI.ShortDraftTrace.breveE (z / (1 + 2 * OAI.ShortDraftTrace.ω₃))
  rw [OAI.ShortDraftTrace.breveE_div_lam_eq_e]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

theorem additive_lattice (a : O) : additiveCharacter (embedding a) = 1 := by
  rw [additive_eq_breveE, embedding_eq_eisEmbedding]
  exact OAI.ConcreteTraceCRT.eisPeriod OAI.ShortDraftTrace.breveE
    OAI.ConcreteBreveE.breveE_period_coordinates a

theorem additive_add (z w : ℂ) :
    additiveCharacter (z + w) = additiveCharacter z * additiveCharacter w := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_im]
  push_cast
  ring

theorem phase_congr {n : O} (hn : n ≠ 0) {a b : O}
    (hab : Ideal.Quotient.mk (principal n) a = Ideal.Quotient.mk (principal n) b) :
    additiveCharacter (embedding a / embedding n) =
      additiveCharacter (embedding b / embedding n) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab)
  have ha : a = b + n * t := by linear_combination ht
  have he := embedding_ne_zero hn
  calc
    _ = additiveCharacter (embedding b / embedding n + embedding t) := by
      rw [ha, ← embeddingHom_apply, map_add, map_mul]
      simp only [embeddingHom_apply]
      congr 1
      field_simp [he]
      <;> ring
    _ = _ := by rw [additive_add, additive_lattice, mul_one]

theorem lambda_unit (c : ArithmeticContext) {n : Ideal O} (hn : Outside c.S n) :
    IsUnit (Ideal.Quotient.mk n lambda) := by
  have hc : IsCoprime (principal lambda) n := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact Ideal.isUnit_iff.mp ((lambda_coprime c hn).symm
      (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
  obtain ⟨i, hi, j, hj, hij⟩ := hc.exists
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hi
  have h := congrArg (Ideal.Quotient.mk n) hij
  simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hj,
    add_zero, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk n b, h⟩

@[simp] theorem lift_spec (n : Ideal O) (x : O ⧸ n) :
    Ideal.Quotient.mk n (residueLift n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

theorem sqrt_gauss_eq_sum (c : ArithmeticContext) (n : O) (hp : IsPrimary n)
    (ho : Outside c.S (principal n))
    [inst : Fintype (O ⧸ principal n)] :
    (Real.sqrt (normElement n) : ℂ) * gauss 2 (principal n) =
      ∑ x : O ⧸ principal n, sexticSymbol (principal n) (residueLift (principal n) x) ^ (2 : ℕ) *
        additiveCharacter (embedding (residueLift (principal n) x) / embedding n) := by
  have hn : n ≠ 0 := fun h => ho.1 (by simp [principal, h])
  have hs : (Real.sqrt (normElement n) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, sqrt_normElement]
    exact norm_ne_zero_iff.mpr (embedding_ne_zero hn)
  unfold gauss
  rw [dif_pos ho.1, primaryGenerator_principal hp]
  change (Real.sqrt (normElement n) : ℂ) *
    ((Real.sqrt (normElement n) : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  rw [Subsingleton.elim (Fintype.ofFinite (O ⧸ principal n)) inst]
  apply Finset.sum_congr rfl
  intro x _
  rw [zpow_ofNat]

theorem cubicGauss_lambda_shift (c : ArithmeticContext) (n : O) (hp : IsPrimary n)
    (ho : Outside c.S (principal n)) :
    cubicGauss 1 n * sexticSymbol (principal n) lambda ^ (2 : ℕ) =
      (Real.sqrt (normElement n) : ℂ) * gauss 2 (principal n) := by
  letI : Finite (O ⧸ principal n) := Ring.HasFiniteQuotients.finiteQuotient ho.1
  letI : Fintype (O ⧸ principal n) := Fintype.ofFinite _
  have hn : n ≠ 0 := fun h => ho.1 (by simp [principal, h])
  obtain ⟨u, hu⟩ := lambda_unit c ho
  rw [sqrt_gauss_eq_sum c n hp ho, cubicGauss, dif_pos ho.1, Finset.sum_mul]
  apply Fintype.sum_equiv u.mulLeft
  intro x
  have hx : Ideal.Quotient.mk (principal n)
      (lambda * residueLift (principal n) x) =
      Ideal.Quotient.mk (principal n) (residueLift (principal n) (u.mulLeft x)) := by
    simp only [map_mul, lift_spec, Units.mulLeft_apply, hu]
  rw [cubicSymbol_eq_sexticSymbol_sq c ho, one_mul, breve_eq_additiveCharacter_lambda]
  rw [← mul_div_assoc, ← ArithmeticProof.embedding_mul]
  rw [phase_congr hn hx, ← symbol_congr hx, sexticSymbol_mul_numerator c ho, mul_pow]
  ring

end QRHShort.ThetaRealizationProof.GaussLambda

namespace QRHShort.ThetaRealizationProof

theorem cubicGaussLambdaNormalization : CubicGaussLambdaNormalizationStatement := by
  intro c n hp _hs ho
  exact GaussLambda.cubicGauss_lambda_shift c n hp ho

end QRHShort.ThetaRealizationProof

#print axioms QRHShort.ThetaRealizationProof.cubicGaussLambdaNormalization

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let target := `QRHShort.ThetaRealizationProof.cubicGaussLambdaNormalization
  unless env.contains target do throwError "Missing named normalization theorem"
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`QRHShort.ThetaRealizationProof.GaussLambda).isPrefixOf name || name == target then
      match info with
      | .thmInfo _ | .defnInfo _ =>
        checked := checked + 1
        for ax in (← collectAxioms name) do
          unless allowed.contains ax do
            throwError "Gauss lambda normalization depends on forbidden axiom {ax} in {name}"
      | .axiomInfo _ => throwError "Gauss lambda normalization declares an axiom: {name}"
      | _ => pure ()
  logInfo m!"GAUSS_LAMBDA_AXIOMS_CHECKED={checked} FORBIDDEN=0"
