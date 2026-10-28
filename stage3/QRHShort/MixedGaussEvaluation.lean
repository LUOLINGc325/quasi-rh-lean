import QRHShort.ArithmeticReduction
import QRHShort.SquarefreeNumeratorProducts
import QRHShort.SquarefreePrimeSymbol
import OAI.NumberTheory.DirichletL.GaussSum.SexticNormalization
import Lean.Util.CollectAxioms

/-! Mixed Gauss--Jacobi evaluation in the frozen normalization.  All character,
embedding, additive trace, and square-root conventions are compared explicitly.
The remaining CRT input is a proposition parameter, never an axiom. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ArithmeticProof.MixedGauss
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
  apply Complex.ext <;> simp [omega3, hre, him] <;> norm_num

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

theorem outside_of_dvd {S : Finset (Ideal O)} {a b : Ideal O}
    (hb : Outside S b) (hab : a ∣ b) : Outside S a := by
  refine ⟨fun ha => hb.1 ?_, ?_⟩
  · have hz : a = 0 := ha
    rw [hz] at hab
    exact zero_dvd_iff.mp hab
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

theorem prime_char_ne_two (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] : ringChar (O ⧸ P) ≠ 2 := by
  apply OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem
  intro htwo
  exact hn.2 P (c.above_two P hp (Ideal.dvd_span_singleton.mpr htwo)) (dvd_refl P)

theorem sixth_root_lift_injective {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a b : O} (ha : a ^ (6 : ℕ) = 1) (hb : b ^ (6 : ℕ) = 1)
    (hab : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) : a = b := by
  have hroot : IsPrimitiveRoot rootSix 6 := by
    refine ⟨rootSix_pow_six, ?_⟩
    intro l hl
    exact hζ.dvd_of_pow_eq_one l (by rw [← map_pow, hl, map_one])
  obtain ⟨i, hi, hie⟩ := hroot.eq_pow_of_pow_eq_one ha
  obtain ⟨j, hj, hje⟩ := hroot.eq_pow_of_pow_eq_one hb
  rw [← hie, ← hje, map_pow, map_pow] at hab
  have hij := hζ.pow_inj hi hj hab
  subst j
  exact hie.symm.trans hje

/-- Identify the actual sixth-power-residue definition with the upstream
multiplicative character, including its zero value. -/
theorem prime_sextic_symbol (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] (a : O) :
    sexticSymbol P a = OAI.ActualEisensteinCubic.canonicalSextic P
      (prime_good c hp hn) (Ideal.Quotient.mk P a) := by
  let χ := OAI.ActualEisensteinCubic.sexticChar P (prime_good c hp hn)
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hp hn
  rw [sexticSymbol_prime hp]
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hp hζ ha,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, MulChar.map_zero]
  have hunit : IsUnit (Ideal.Quotient.mk P a) :=
    isUnit_iff_ne_zero.mpr (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hχpow : χ (Ideal.Quotient.mk P a) ^ (6 : ℕ) = 1 := by
    rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
      (OAI.ActualEisensteinCubic.sexticChar_powers P (prime_good c hp hn)).2.2]
    exact MulChar.one_apply hunit
  obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ ha
  have hpow : (rootSix ^ j) ^ (6 : ℕ) = 1 := by
    rw [← pow_mul, Nat.mul_comm j 6, pow_mul, rootSix_pow_six, one_pow]
  have hreduce : Ideal.Quotient.mk P (χ (Ideal.Quotient.mk P a)) =
      Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) := by
    have hu := OAI.ActualEisensteinCubic.sexticChar_reduce_unit P
      (prime_good c hp hn) (prime_char_ne_two c hp hn) hunit.unit
    simpa only [IsUnit.unit_spec, Ideal.absNorm_apply, Submodule.cardQuot_apply, χ] using hu
  have he : rootSix ^ j = χ (Ideal.Quotient.mk P a) :=
    sixth_root_lift_injective hζ hpow hχpow (ht.symm.trans hreduce.symm)
  rw [sexticAtPrime_eq_of_test hζ hj ht, he, embedding_eq_eisEmbedding]
  rfl

theorem primaryGenerator_ne_zero (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : primaryGenerator n ≠ 0 := by
  intro hz
  apply hn.1
  calc
    n = principal (primaryGenerator n) := (primaryGenerator_spec_outside c hn).1.symm
    _ = principal 0 := congrArg principal hz
    _ = ⊥ := Submodule.span_zero_singleton O

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the concrete normalized sum and its canonical finite-field model.
The positive exponent is necessary because multiplicative characters vanish at zero. -/
theorem prime_gauss_model (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] (j : ℕ) (hj : j ≠ 0) :
    gauss (j : ℤ) P =
      gaussSum (OAI.ActualEisensteinCubic.canonicalSextic P (prime_good c hp hn) ^ j)
        ((primaryGenerator_spec_outside c hn).1 ▸
          eisTraceModChar OAI.ShortDraftTrace.breveE
            OAI.ConcreteBreveE.breveE_period_coordinates (primaryGenerator P)
            (primaryGenerator_ne_zero c hn)) /
        (‖eisEmbedding (primaryGenerator P)‖ : ℂ) := by
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  unfold gauss
  rw [dif_pos hn.1, sqrt_norm_prime c hp hn]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  unfold gaussSum
  apply Finset.sum_congr rfl
  intro x _
  have hx : Ideal.Quotient.mk P (residueLift P x) = x :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective x)
  have ht := trace_char_mk (primaryGenerator P)
    (primaryGenerator_ne_zero c hn)
    (primaryGenerator_spec_outside c hn).1.symm (residueLift P x)
  rw [hx] at ht
  simp only [zpow_natCast, prime_sextic_symbol c hp hn, hx,
    MulChar.pow_apply' _ hj]
  rw [← ht] <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Unconditional prime case of the frozen mixed Gauss statement. -/
theorem prime_mixed (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) :
    gauss 1 P * gauss 2 P =
      gauss 2 P ^ (3 : ℕ) * (star (sexticSymbol P 4) * gauss 3 P) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let p := primaryGenerator P
  have hpn : p ≠ 0 := primaryGenerator_ne_zero c hn
  let χ := OAI.ActualEisensteinCubic.canonicalSextic P (prime_good c hp hn)
  have hprime := OAI.ActualEisensteinCubic.breveGamma1_gamma2_relation P
    (prime_good c hp hn) (prime_char_ne_two c hp hn) p
    (primaryGenerator_spec_outside c hn).1.symm hpn
    (primary_lambda_sq (primaryGenerator_spec_outside c hn).2)
  have hg1 : gauss 1 P = OAI.ActualEisensteinCubic.breveGamma1 P
      (prime_good c hp hn) p (primaryGenerator_spec_outside c hn).1.symm hpn := by
    simpa only [Nat.cast_one, pow_one, OAI.ActualEisensteinCubic.breveGamma1, p, principal]
      using prime_gauss_model c hp hn 1 (by decide)
  have hg2 : gauss 2 P = OAI.ActualEisensteinCubic.breveGamma2 P
      (prime_good c hp hn) p (primaryGenerator_spec_outside c hn).1.symm hpn := by
    exact prime_gauss_model c hp hn 2 (by decide)
  have hg3 : gauss 3 P = OAI.ActualEisensteinCubic.breveGamma3 P
      (prime_good c hp hn) p (primaryGenerator_spec_outside c hn).1.symm hpn :=
    prime_gauss_model c hp hn 3 (by decide)
  have hinv : (χ (Ideal.Quotient.mk P (4 : O)))⁻¹ =
      star (sexticSymbol P 4) := by
    rw [prime_sextic_symbol c hp hn]
    exact ((MulChar.star_apply' χ _).trans (MulChar.inv_apply_eq_inv' χ _)).symm
  rw [hg1, hg2, hg3]
  rw [hprime]
  change (χ (Ideal.Quotient.mk P (4 : O)))⁻¹ * _ * _ = _
  rw [hinv]
  ring

end QRHShort.ArithmeticProof.MixedGauss

#print axioms QRHShort.ArithmeticProof.MixedGauss.prime_sextic_symbol
#print axioms QRHShort.ArithmeticProof.MixedGauss.prime_mixed

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof.MixedGauss).isPrefixOf name then entries.push (name, info)
      else entries) (#[] : Array (Name × ConstantInfo))
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Mixed Gauss proof depends on forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Mixed Gauss proof declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No mixed Gauss declarations audited"
  logInfo m!"MIXED_GAUSS_AUDIT declarations={checked} forbidden=0"
