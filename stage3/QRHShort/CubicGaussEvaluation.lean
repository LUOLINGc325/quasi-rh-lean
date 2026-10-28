import QRHShort.ArithmeticReduction
import QRHShort.SquarefreeNumeratorProducts
import QRHShort.SquarefreePrimeSymbol
import OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
import Lean.Util.CollectAxioms

/-! The cubic Gauss evaluation in the frozen normalization. The CRT formula is
an explicit upstream input; all remaining claims concern the concrete objects
of `QRHShort.Arithmetic`, including the choice of complex embedding. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ArithmeticProof.CubicGauss
open SquarefreeReflection
open SquarefreeReflection.RayValuePrerequisites
open OAI.ConcreteTraceCRT (eisEmbedding eisTraceModChar eisLam)
open OAI.EisensteinEmbedding (omega3)

theorem embedding_omega_eq : embedding omega = omega3 := by
  have hq : embedding omega ^ 2 + embedding omega + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero, embeddingHom_apply] using
      congrArg embeddingHom omega_sq_add_omega_add_one
  have hr := congrArg Complex.re hq
  have hi := congrArg Complex.im hq
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
    Complex.zero_re] at hr
  simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im,
    Complex.zero_im] at hi
  have hn : 0 ≤ (embedding omega).im := by
    unfold embedding
    split_ifs with h
    · exact h.le
    · exact neg_nonneg.mpr (le_of_not_gt h)
  have hne : (embedding omega).im ≠ 0 := by
    intro h
    rw [h] at hr
    nlinarith [sq_nonneg ((embedding omega).re + (1 / 2 : ℝ))]
  have hfac : (2 * (embedding omega).re + 1) * (embedding omega).im = 0 := by
    nlinarith [hi]
  have hre : (embedding omega).re = -(1 / 2 : ℝ) := by
    have := (mul_eq_zero.mp hfac).resolve_right hne
    linarith
  have him : (embedding omega).im = Real.sqrt 3 / 2 := by
    rw [hre] at hr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  apply Complex.ext <;> norm_num [omega3, hre, him]

theorem embedding_eq_eisEmbedding (a : O) : embedding a = eisEmbedding a := by
  have he : embeddingHom = eisEmbedding := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change embeddingHom omega = eisEmbedding omega
    rw [embeddingHom_apply, embedding_omega_eq]
    simpa only [eisEmbedding, omega, OAI.EisensteinEmbedding.pb,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen] using
      (OAI.EisensteinEmbedding.embedding_gen omega3
        OAI.EisensteinEmbedding.omega3_sq).symm
  simpa only [embeddingHom_apply] using congrArg (fun f : O →+* ℂ => f a) he

theorem additiveCharacter_eq_breveE (z : ℂ) :
    additiveCharacter z = OAI.ShortDraftTrace.breveE (z / eisLam) := by
  change additiveCharacter z =
    OAI.ShortDraftTrace.breveE (z / (1 + 2 * OAI.ShortDraftTrace.ω₃))
  rw [OAI.ShortDraftTrace.breveE_div_lam_eq_e]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

theorem additiveCharacter_embedding (a : O) : additiveCharacter (embedding a) = 1 := by
  rw [additiveCharacter_eq_breveE, embedding_eq_eisEmbedding]
  exact OAI.ConcreteTraceCRT.eisPeriod OAI.ShortDraftTrace.breveE
    OAI.ConcreteBreveE.breveE_period_coordinates a

theorem primaryGenerator_one : primaryGenerator 1 = 1 := by
  have hp : principal 1 = (1 : Ideal O) := by simp [principal]
  have hi : IsPrimary 1 := by simp [IsPrimary]
  have he : ∃ a : O, principal a = 1 ∧ IsPrimary a := ⟨1, hp, hi⟩
  have hs : principal (primaryGenerator 1) = 1 ∧ IsPrimary (primaryGenerator 1) := by
    simpa only [primaryGenerator, dif_pos he] using Classical.choose_spec he
  exact primary_unique hs.2 hi (hs.1.trans hp.symm)

theorem alpha_one : alpha 1 = 1 := by
  rw [alpha, primaryGenerator_one, embedding_one]
  norm_num

theorem gauss_two_one : gauss 2 1 = 1 := by
  have hne : (1 : Ideal O) ≠ ⊥ := one_ne_zero
  unfold gauss
  rw [dite_eq_left hne]
  simp only [sexticSymbol, ite_eq_right hne,
    UniqueFactorizationMonoid.normalizedFactors_one,
    Multiset.map_zero, Multiset.prod_zero, one_zpow, one_mul,
    primaryGenerator_one, embedding_one, div_one, additiveCharacter_embedding,
    normIdeal, map_one, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one]
  simp

theorem outside_of_dvd {S : Finset (Ideal O)} {a b : Ideal O}
    (hb : Outside S b) (hab : a ∣ b) : Outside S a := by
  refine ⟨fun ha => hb.1 (le_bot_iff.mp (ha ▸ Ideal.le_of_dvd hab)), ?_⟩
  exact fun P hP hPa => hb.2 P hP (hPa.trans hab)

theorem symbol_sixth (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (a : O) (ha : IsRelPrime n (principal a)) :
    sexticSymbol n a ^ (6 : ℕ) = 1 := by
  have hf : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors n,
      sexticAtPrime P a ^ (6 : ℕ) = 1 := by
    intro P hP
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    have hζ := outside_quotient_rootSix_isPrimitiveRoot c hp
      (outside_of_mem_normalizedFactors hn hP)
    have hnot : a ∉ P := by
      intro hmem
      apply hp.not_isUnit
      exact ha (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
        (Ideal.dvd_span_singleton.mpr hmem)
    obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ hnot
    rw [sexticAtPrime_eq_of_test hζ hj ht, ← embedding_pow, ← pow_mul,
      Nat.mul_comm j 6, pow_mul, rootSix_pow_six, one_pow, embedding_one]
  rw [sexticSymbol, if_neg hn.1, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  exact hf P hP

theorem cube_mul (hcrt : CubicGaussCRTStatement) (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    gauss 2 (a * b) ^ (3 : ℕ) = gauss 2 a ^ (3 : ℕ) * gauss 2 b ^ (3 : ℕ) := by
  have hab' : IsRelPrime a (principal (primaryGenerator b)) := by
    rw [(primaryGenerator_spec_outside c hb.1).1]
    exact hab
  have hba' : IsRelPrime b (principal (primaryGenerator a)) := by
    rw [(primaryGenerator_spec_outside c ha.1).1]
    exact hab.symm
  rw [hcrt c a b ha hb hab]
  simp only [mul_pow, ← pow_mul]
  norm_num only
  rw [symbol_sixth c ha.1 _ hab', symbol_sixth c hb.1 _ hba', mul_one, mul_one]

theorem prime_good (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) : OAI.ActualEisensteinCubic.lambda ∉ P := by
  intro h
  have hthree : P ∣ principal 3 := by
    apply Ideal.dvd_span_singleton.mpr
    obtain ⟨a, ha⟩ := omega_sub_one_dvd_three
    rw [ha]
    exact P.mul_mem_right a h
  exact hn.2 P (c.above_three P hp hthree) (dvd_refl P)

theorem primary_lambda_sq {p : O} (hp : IsPrimary p) :
    OAI.ActualEisensteinCubic.lambda ^ (2 : ℕ) ∣ p - 1 := by
  have hthree : (omega - 1) ^ (2 : ℕ) ∣ (3 : O) := by
    refine ⟨-omega ^ (2 : ℕ), ?_⟩
    rw [omega_sub_one_sq]
    calc
      (3 : O) = 3 * omega ^ (3 : ℕ) := by rw [omega_cube, mul_one]
      _ = -3 * omega * -omega ^ (2 : ℕ) := by ring
  exact hthree.trans ((isPrimary_iff_three_dvd p).mp hp)

theorem cubic_root_lift_injective {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3)
    {a b : O} (ha : a ^ (3 : ℕ) = 1) (hb : b ^ (3 : ℕ) = 1)
    (hab : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) : a = b := by
  have hω : IsPrimitiveRoot omega 3 :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨i, hi, hie⟩ := hω.eq_pow_of_pow_eq_one ha
  obtain ⟨j, hj, hje⟩ := hω.eq_pow_of_pow_eq_one hb
  rw [← hie, ← hje, map_pow, map_pow] at hab
  have hij := hζ.pow_inj hi hj hab
  subst j
  exact hie.symm.trans hje

theorem prime_cubic_symbol (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] (a : O) :
    sexticSymbol P a ^ (2 : ℕ) =
      eisEmbedding (OAI.ActualEisensteinCubic.cubicChar P (prime_good c hp hn)
        (Ideal.Quotient.mk P a)) := by
  let χ := OAI.ActualEisensteinCubic.cubicChar P (prime_good c hp hn)
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hp hn
  rw [sexticSymbol_prime hp]
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hp hζ ha,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, MulChar.map_zero, map_zero]
    norm_num
  have hunit : IsUnit (Ideal.Quotient.mk P a) :=
    isUnit_iff_ne_zero.mpr (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ ha
  have hcube : χ (Ideal.Quotient.mk P a) ^ (3 : ℕ) = 1 := by
    rw [← MulChar.pow_apply' χ (by decide : 3 ≠ 0)]
    rw [OAI.ActualEisensteinCubic.cubicChar_pow_three]
    exact MulChar.one_apply hunit
  have hcard : P.absNorm = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hmod := prime_absNorm_mod_six hp hζ
  have hexp : (P.absNorm - 1) / 6 * 2 = (Nat.card (O ⧸ P) - 1) / 3 := by
    omega
  have hpow : ((rootSix ^ j) ^ (2 : ℕ)) ^ (3 : ℕ) = 1 := by
    rw [← pow_mul, ← pow_mul]
    have hm : j * (2 * 3) = 6 * j := by omega
    rw [hm, pow_mul, rootSix_pow_six, one_pow]
  have he : (rootSix ^ j) ^ (2 : ℕ) = χ (Ideal.Quotient.mk P a) := by
    apply cubic_root_lift_injective
      (OAI.ActualEisensteinCubic.omega_reduced_primitive P (prime_good c hp hn))
      hpow hcube
    rw [map_pow, ← ht, ← pow_mul, hexp]
    exact (OAI.ActualEisensteinCubic.cubicChar_reduce P (prime_good c hp hn)
      (Ideal.Quotient.mk P a)).symm
  rw [sexticAtPrime_eq_of_test hζ hj ht, ← embedding_pow, he,
    embedding_eq_eisEmbedding]

theorem trace_char_mk {P : Ideal O} (p : O) (hp : p ≠ 0)
    (hP : P = Ideal.span {p}) (a : O) :
    (hP.symm ▸ eisTraceModChar OAI.ShortDraftTrace.breveE
      OAI.ConcreteBreveE.breveE_period_coordinates p hp)
      (Ideal.Quotient.mk P a) =
        additiveCharacter (embedding a / embedding p) := by
  subst P
  rw [eisTraceModChar, OAI.IdealGaussCRT.traceModChar_mk,
    additiveCharacter_eq_breveE, embedding_eq_eisEmbedding, embedding_eq_eisEmbedding]
  congr 1
  ring

theorem sqrt_norm_prime (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] :
    Real.sqrt (normIdeal P) = ‖eisEmbedding (primaryGenerator P)‖ := by
  have hs := primaryGenerator_spec_outside c hn
  have hnorm := OAI.ActualEisensteinCubic.primary_generator_mul_conj_eq_card P
    (prime_good c hp hn) (primaryGenerator P) hs.1.symm (primary_lambda_sq hs.2)
  have hc := congrArg eisEmbedding hnorm
  rw [map_mul, OAI.ActualEisensteinCubic.eisEmbedding_conjO, map_natCast] at hc
  have hq : (‖eisEmbedding (primaryGenerator P)‖ : ℂ) ^ (2 : ℕ) =
      (P.absNorm : ℂ) := by
    rw [← Complex.mul_conj']
    simpa only [starRingEnd_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hc
  have hr : ‖eisEmbedding (primaryGenerator P)‖ ^ (2 : ℕ) = normIdeal P := by
    change ‖eisEmbedding (primaryGenerator P)‖ ^ (2 : ℕ) = (P.absNorm : ℝ)
    exact_mod_cast hq
  rw [← hr, Real.sqrt_sq (norm_nonneg _)]

theorem prime_cube (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) : gauss 2 P ^ (3 : ℕ) = -alpha P := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let p := primaryGenerator P
  have hs := primaryGenerator_spec_outside c hn
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    have hpg : primaryGenerator P = 0 := h
    rw [← hs.1, hpg]
    simp [principal]
  have hP : P = Ideal.span {p} := hs.1.symm
  let ψ : AddChar (O ⧸ P) ℂ := hP.symm ▸ eisTraceModChar OAI.ShortDraftTrace.breveE
    OAI.ConcreteBreveE.breveE_period_coordinates p hp0
  have he : gauss 2 P =
      gaussSum ((OAI.ActualEisensteinCubic.cubicChar P (prime_good c hp hn)).ringHomComp
        eisEmbedding) ψ / (‖eisEmbedding p‖ : ℂ) := by
    unfold gauss
    rw [dite_eq_left hn.1, sqrt_norm_prime c hp hn]
    conv_rhs => rw [div_eq_mul_inv]
    rw [mul_comm]
    congr 1
    unfold gaussSum
    apply Finset.sum_congr rfl
    intro x _
    have hx : Ideal.Quotient.mk P (residueLift P x) = x :=
      Classical.choose_spec (Ideal.Quotient.mk_surjective x)
    have ht := trace_char_mk p hp0 hP (residueLift P x)
    rw [hx] at ht
    simp only [zpow_ofNat, prime_cubic_symbol c hp hn, hx,
      MulChar.ringHomComp_apply]
    rw [← ht]
  rw [he]
  have hcube := OAI.ActualEisensteinCubic.cubicGauss_normalized_cube_breveE
    P (prime_good c hp hn) p hP hp0 (primary_lambda_sq hs.2)
  simpa only [ψ, p, alpha, embedding_eq_eisEmbedding, neg_div] using hcube

/-- The frozen target, with only its separately routed CRT predecessor as an
explicit premise. No reciprocity law is needed: cubing removes both twists. -/
theorem cubicGaussEvaluation_of_crt (hcrt : CubicGaussCRTStatement) :
    CubicGaussEvaluationStatement := by
  intro c n hn
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun a : Ideal O => SquarefreeOutside c.S a →
      gauss 2 a ^ (3 : ℕ) = (mobius a : ℂ) * alpha a) n ?_ ?_ ?_ hn
  · intro h
    exact (h.1.1 rfl).elim
  · intro a ha _
    have he : a = 1 := isUnit_iff_eq_one.mp ha
    subst a
    rw [gauss_two_one, alpha_one]
    change (1 : ℂ) ^ (3 : ℕ) = (UniqueFactorizationMonoid.moebius (1 : Ideal O) : ℂ) * 1
    rw [UniqueFactorizationMonoid.moebius_one]
    norm_num
  · intro a P _ hp ih h
    have hfac := squarefree_mul_iff.mp h.2
    have hP : SquarefreeOutside c.S P :=
      ⟨outside_of_dvd h.1 (dvd_mul_right P a), hfac.2.1⟩
    have ha : SquarefreeOutside c.S a :=
      ⟨outside_of_dvd h.1 (dvd_mul_left a P), hfac.2.2⟩
    have hm : (mobius (P * a) : ℂ) = (mobius P : ℂ) * (mobius a : ℂ) := by
      simp only [mobius, hfac.1.moebius_mul, Int.cast_mul]
    have hpμ : (mobius P : ℂ) = -1 := by
      simp [mobius, hp.irreducible.moebius_eq]
    rw [cube_mul hcrt c hP ha hfac.1, prime_cube c hp hP.1, ih ha, hm,
      alpha_mul c hP.1 ha.1, hpμ]
    ring

end QRHShort.ArithmeticProof.CubicGauss

#print axioms QRHShort.ArithmeticProof.CubicGauss.cubicGaussEvaluation_of_crt

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations : Array (Name × ConstantInfo) := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof.CubicGauss).isPrefixOf name then entries.push (name, info)
      else entries) #[]
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Cubic Gauss proof depends on forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Cubic Gauss proof declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No cubic Gauss declarations audited"
  logInfo m!"CUBIC_GAUSS_AUDIT declarations={checked} forbidden=0 pending_inputs=CRT"
