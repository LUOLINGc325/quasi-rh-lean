import QRHShort.ThetaRealizationReduction
import QRHShort.SquarefreeNumeratorProducts
import OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

/-!
The coefficient bridge is reduced to two strictly arithmetic inputs: uniqueness
of the explicit TauFormula value on the unramified cube slice, and a change of
additive character in the cubic Gauss sum. Neither input is an axiom. All twists,
primary generators, denominator products, and archimedean factors are handled
here, without assuming the manuscript's theta-realization endpoint.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ThetaRealizationProof
open ArithmeticProof SquarefreeReflection
open SquarefreeReflection.RayValuePrerequisites

def cubeSliceValue (n b : O) : ℂ :=
  star (cubicGauss 1 n) * (‖embedding b / embedding n‖ : ℂ) *
    (((3 : ℝ) ^ (5 / 2 : ℝ) : ℝ) : ℂ)

/-- Squarefree/cube decomposition is unique even when n and b share primes.
This removes the factorization part of the remaining TauFormula uniqueness. -/
theorem primaryCubeData_injective {n b n' b' : O}
    (hnb : PrimaryCubeData n b) (hnb' : PrimaryCubeData n' b')
    (he : n * b ^ 3 = n' * b' ^ 3) : n = n' ∧ b = b' := by
  have hp0 (x : O) (hx : x ≠ 0) : principal x ≠ (0 : Ideal O) := by
    intro h
    exact hx (Ideal.span_singleton_eq_bot.mp h)
  have hn0 := hp0 n hnb.1
  have hb0 := hp0 b hnb.2.1
  have hn'0 := hp0 n' hnb'.1
  have hb'0 := hp0 b' hnb'.2.1
  have hfac := congrArg UniqueFactorizationMonoid.normalizedFactors
    (congrArg principal he)
  simp only [principal_cube,
    UniqueFactorizationMonoid.normalizedFactors_mul hn0 (pow_ne_zero 3 hb0),
    UniqueFactorizationMonoid.normalizedFactors_mul hn'0 (pow_ne_zero 3 hb'0),
    UniqueFactorizationMonoid.normalizedFactors_pow] at hfac
  have hcount (P : Ideal O) := congrArg (Multiset.count P) hfac
  simp [succ_nsmul, Multiset.count_add] at hcount
  have hncount := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hn0).mp hnb.2.2.2.2)
  have hn'count := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hn'0).mp hnb'.2.2.2.2)
  have hnfac : UniqueFactorizationMonoid.normalizedFactors (principal n) =
      UniqueFactorizationMonoid.normalizedFactors (principal n') := by
    apply Multiset.ext.mpr
    intro P
    have := hcount P
    have := hncount P
    have := hn'count P
    omega
  have hbfac : UniqueFactorizationMonoid.normalizedFactors (principal b) =
      UniqueFactorizationMonoid.normalizedFactors (principal b') := by
    apply Multiset.ext.mpr
    intro P
    have := hcount P
    have := hncount P
    have := hn'count P
    omega
  have hnideal : principal n = principal n' := by
    rw [← Ideal.prod_normalizedFactors_eq_self hn0,
      ← Ideal.prod_normalizedFactors_eq_self hn'0, hnfac]
  have hbideal : principal b = principal b' := by
    rw [← Ideal.prod_normalizedFactors_eq_self hb0,
      ← Ideal.prod_normalizedFactors_eq_self hb'0, hbfac]
  exact ⟨primary_unique hnb.2.2.1 hnb'.2.2.1 hnideal,
    primary_unique hnb.2.2.2.1 hnb'.2.2.2.1 hbideal⟩

/-- The remaining uniqueness input, specialized to the actual frequency used
by the coefficient bridge. Existence is proved below from the k=0 branch. -/
def TauCubeSliceUniquenessStatement : Prop :=
  ∀ n b : O, PrimaryCubeData n b → ∀ v : ℂ,
    TauFormula (-frequency (n * b ^ 3)) v → v = cubeSliceValue n b

/-- Change from DR's unnormalized cubic sum to the manuscript's normalized
sextic sum, including the lambda factor from the two additive characters. -/
def CubicGaussLambdaNormalizationStatement : Prop :=
  ∀ (c : ArithmeticContext) (n : O), IsPrimary n →
    Squarefree (principal n) → Outside c.S (principal n) →
    cubicGauss 1 n * sexticSymbol (principal n) lambda ^ (2 : ℕ) =
      (Real.sqrt (normElement n) : ℂ) * gauss 2 (principal n)

theorem cubeSliceValue_formula (n b : O) (hnb : PrimaryCubeData n b) :
    TauFormula (-frequency (n * b ^ 3)) (cubeSliceValue n b) := by
  refine ⟨n, b, hnb, -1, Or.inr rfl, Or.inr ⟨0, ?_, ?_⟩⟩
  · simp [frequency]
  · norm_num [cubeSliceValue]

theorem tau_cubeSlice (hu : TauCubeSliceUniquenessStatement)
    (n b : O) (hnb : PrimaryCubeData n b) :
    tau (-frequency (n * b ^ 3)) = cubeSliceValue n b := by
  have hex : ∃ v : ℂ, TauFormula (-frequency (n * b ^ 3)) v :=
    ⟨_, cubeSliceValue_formula n b hnb⟩
  unfold tau
  rw [dif_pos hex]
  exact hu n b hnb _ (Classical.choose_spec hex)

theorem cuspCoefficient_cubeSlice (hu : TauCubeSliceUniquenessStatement)
    (n b : O) (hnb : PrimaryCubeData n b) :
    cuspCoefficient .zero (frequency (n * b ^ 3)) =
      cubicGauss 1 n * (‖embedding b / embedding n‖ : ℂ) *
        (((3 : ℝ) ^ (5 / 2 : ℝ) : ℝ) : ℂ) := by
  change star (tau (-frequency (n * b ^ 3))) = _
  rw [tau_cubeSlice hu n b hnb]
  simp [cubeSliceValue, star_mul] <;> ring

theorem sexticSymbol_mul_denominator (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, sexticSymbol]
  by_cases hb : b = ⊥
  · simp [hb, sexticSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, if_neg ha, if_neg hb, if_neg hab,
    UniqueFactorizationMonoid.normalizedFactors_mul ha hb,
    Multiset.map_add, Multiset.prod_add]

theorem sexticSymbol_cube_denominator (a : Ideal O) (z : O) :
    sexticSymbol (a ^ 3) z = sexticSymbol a z ^ 3 := by
  rw [show a ^ 3 = a * a * a by ring, sexticSymbol_mul_denominator,
    sexticSymbol_mul_denominator]
  ring

theorem outside_cube (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : Outside c.S (a ^ 3) := by
  rw [show a ^ 3 = a * a * a by ring]
  exact outside_mul c (outside_mul c ha ha) ha

theorem completedTwist_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    completedTwist c ξ k f (a * b) =
      completedTwist c ξ k f a * completedTwist c ξ k f b := by
  simp only [completedTwist, if_pos ha, if_pos hb, if_pos (outside_mul c ha hb),
    rayValue_mul c ξ.val ha hb, sexticSymbol_mul_denominator, mul_pow]
  ring

theorem completedTwist_cube (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) {a : Ideal O} (ha : Outside c.S a) :
    completedTwist c ξ k f (a ^ 3) = completedTwist c ξ k f a ^ 3 := by
  rw [show a ^ 3 = a * a * a by ring,
    completedTwist_mul c ξ k f (outside_mul c ha ha) ha,
    completedTwist_mul c ξ k f ha ha]
  ring

theorem primary_cube {b : O} (hb : IsPrimary b) : IsPrimary (b ^ 3) := by
  rw [show b ^ 3 = b * b * b by ring]
  exact primary_mul (primary_mul hb hb) hb

theorem principal_lambda_dvd_three : principal lambda ∣ principal (3 : O) := by
  apply Ideal.dvd_span_singleton.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨-lambda, ?_⟩
  unfold lambda
  linear_combination 4 * omega_sq_add_omega_add_one

theorem lambda_coprime (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : IsRelPrime a (principal lambda) := by
  have hthree : principal (3 : O) ≠ ⊥ := by
    intro h
    have hz : (3 : O) = 0 := Ideal.span_singleton_eq_bot.mp h
    norm_num at hz
  exact (outside_coprime_supported_modulus c (principal 3) hthree
    c.above_three ha).isRelPrime.of_dvd_right principal_lambda_dvd_three

theorem sexticSymbol_lambda_sixth (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : sexticSymbol a lambda ^ (6 : ℕ) = 1 := by
  have hf : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors a,
      sexticAtPrime P lambda ^ (6 : ℕ) = 1 := by
    intro P hP
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    have hζ := outside_quotient_rootSix_isPrimitiveRoot c hp
      (outside_of_mem_normalizedFactors ha hP)
    have hnot : lambda ∉ P := by
      intro hmem
      apply hp.not_isUnit
      exact lambda_coprime c ha
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
        (Ideal.dvd_span_singleton.mpr hmem)
    obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ hnot
    rw [sexticAtPrime_eq_of_test hζ hj ht, ← embedding_pow, ← pow_mul,
      Nat.mul_comm j 6, pow_mul, rootSix_pow_six, one_pow, embedding_one]
  rw [sexticSymbol, if_neg ha.1, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  exact hf P hP

theorem thetaMultiplier_cube (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) (n b : O) (hn : IsPrimary n) (hb : IsPrimary b)
    (hno : Outside c.S (principal n)) (hbo : Outside c.S (principal b)) :
    thetaMultiplier c ξ k f (n * b ^ 3) =
      sexticSymbol (principal n) lambda ^ (2 : ℕ) *
        completedTwist c ξ k f (principal n) *
        completedTwist c ξ k f (principal b) ^ (3 : ℕ) := by
  have hnb := outside_mul c hno (outside_cube c hbo)
  have hp : IsPrimary (n * b ^ 3) := primary_mul hn (primary_cube hb)
  simp only [thetaMultiplier, principal_cube, hp, hnb, and_self, ite_true,
    completedTwist_mul c ξ k f hno (outside_cube c hbo),
    completedTwist_cube c ξ k f hbo, sexticSymbol_mul_denominator,
    sexticSymbol_cube_denominator, mul_pow]
  rw [← pow_mul, show 3 * 2 = 6 from rfl, sexticSymbol_lambda_sixth c hbo]
  ring

theorem embedding_eq_eisEmbedding (a : O) :
    embedding a = OAI.ConcreteTraceCRT.eisEmbedding a := by
  have hω : embedding omega = OAI.EisensteinEmbedding.omega3 := by
    have hLambda := embedding_lambda
    rw [← embeddingHom_apply, lambda, map_add, map_one, map_mul, map_ofNat,
      embeddingHom_apply] at hLambda
    apply Complex.ext
    · have h := congrArg Complex.re hLambda
      norm_num [Complex.mul_re, OAI.EisensteinEmbedding.omega3] at h ⊢
      linarith
    · have h := congrArg Complex.im hLambda
      norm_num [Complex.mul_im, OAI.EisensteinEmbedding.omega3] at h ⊢
      linarith
  have he : embeddingHom = OAI.ConcreteTraceCRT.eisEmbedding := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change embeddingHom omega = OAI.ConcreteTraceCRT.eisEmbedding omega
    rw [embeddingHom_apply, hω]
    simpa only [OAI.ConcreteTraceCRT.eisEmbedding, omega, OAI.EisensteinEmbedding.pb,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen] using
      (OAI.EisensteinEmbedding.embedding_gen OAI.EisensteinEmbedding.omega3
        OAI.EisensteinEmbedding.omega3_sq).symm
  simpa only [embeddingHom_apply] using congrArg (fun f : O →+* ℂ => f a) he

theorem sqrt_normElement (a : O) : Real.sqrt (normElement a) = ‖embedding a‖ := by
  rw [embedding_eq_eisEmbedding, normElement, normIdeal, principal,
    ← OAI.ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_norm_mul_ratio (n b : O) (hn : n ≠ 0) :
    (Real.sqrt (normElement n) : ℂ) * (‖embedding b / embedding n‖ : ℂ) =
      (Real.sqrt (normElement b) : ℂ) := by
  rw [sqrt_normElement, sqrt_normElement, norm_div, Complex.ofReal_div]
  field_simp [norm_ne_zero_iff.mpr (embedding_ne_zero hn)]

/-- The exact additive-character conversion needed by the Gauss child. -/
theorem breve_eq_additiveCharacter_lambda (z : ℂ) :
    breve z = additiveCharacter (embedding lambda * z) := by
  have hs : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  unfold breve additiveCharacter
  rw [embedding_lambda, Complex.star_def, Complex.add_conj]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one,
    one_mul, sub_zero]
  congr 1
  push_cast
  field_simp [hs]
  <;> ring

theorem coefficientBridge_of_children (hu : TauCubeSliceUniquenessStatement)
    (hg : CubicGaussLambdaNormalizationStatement) : CoefficientBridgeStatement := by
  intro c _hc ξ k f _hf n b hnb hno hbo
  change cuspCoefficient .zero (frequency (n * b ^ 3)) * _ = _
  rw [cuspCoefficient_cubeSlice hu n b hnb,
    thetaMultiplier_cube c ξ k f n b hnb.2.2.1 hnb.2.2.2.1 hno hbo]
  calc
    _ = (((3 : ℝ) ^ (5 / 2 : ℝ) : ℝ) : ℂ) *
        (cubicGauss 1 n * sexticSymbol (principal n) lambda ^ (2 : ℕ)) *
        (‖embedding b / embedding n‖ : ℂ) * completedTwist c ξ k f (principal n) *
        completedTwist c ξ k f (principal b) ^ (3 : ℕ) := by ring
    _ = _ := by
      rw [hg c n hnb.2.2.1 hnb.2.2.2.2 hno]
      calc
        _ = (((3 : ℝ) ^ (5 / 2 : ℝ) : ℝ) : ℂ) *
            ((Real.sqrt (normElement n) : ℂ) * (‖embedding b / embedding n‖ : ℂ)) *
            gauss 2 (principal n) * completedTwist c ξ k f (principal n) *
            completedTwist c ξ k f (principal b) ^ (3 : ℕ) := by ring
        _ = _ := by rw [sqrt_norm_mul_ratio n b hnb.1]

end QRHShort.ThetaRealizationProof

#print axioms QRHShort.ThetaRealizationProof.cubeSliceValue_formula
#print axioms QRHShort.ThetaRealizationProof.primaryCubeData_injective
#print axioms QRHShort.ThetaRealizationProof.thetaMultiplier_cube
#print axioms QRHShort.ThetaRealizationProof.sqrt_normElement
#print axioms QRHShort.ThetaRealizationProof.breve_eq_additiveCharacter_lambda
#print axioms QRHShort.ThetaRealizationProof.coefficientBridge_of_children

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`QRHShort.ThetaRealizationProof).isPrefixOf name then
      match info with
      | .thmInfo _ | .defnInfo _ =>
        checked := checked + 1
        for ax in (← collectAxioms name) do
          unless allowed.contains ax do
            throwError "Coefficient bridge depends on forbidden axiom {ax} in {name}"
      | .axiomInfo _ => throwError "Coefficient bridge declares an axiom: {name}"
      | _ => pure ()
  if checked == 0 then throwError "No coefficient bridge declarations audited"
  logInfo m!"THETA_COEFFICIENT_BRIDGE_AUDIT declarations={checked} forbidden=0 pending_children=2"
