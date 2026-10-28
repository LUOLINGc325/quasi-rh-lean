import QRHShort.ThetaStatements
import QRHShort.ArithmeticReduction
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Lean.Util.CollectAxioms

/-!
The two identities in `ThetaRealizationStatement` are assembled below from
explicit, smaller proof obligations. These obligations are propositions, not
axioms or admitted theorems. No manuscript endpoint is imported.

The coefficient obligation is the local identity used in paper2.tex:1708.
The other obligations isolate finite Fourier inversion and convergence of the
concrete theta expansion. The additive-character normalization is proved here.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ThetaRealizationProof
open ArithmeticProof
open SquarefreeReflection.RayValuePrerequisites

def PrimaryOutside (c : ArithmeticContext) (n : O) : Prop :=
  n ≠ 0 ∧ IsPrimary n ∧ Outside c.S (principal n)

theorem primaryGenerator_principal {n : O} (hn : IsPrimary n) :
    primaryGenerator (principal n) = n := by
  have hex : ∃ z : O, principal z = principal n ∧ IsPrimary z := ⟨n, rfl, hn⟩
  have hs : principal (primaryGenerator (principal n)) = principal n ∧
      IsPrimary (primaryGenerator (principal n)) := by
    simpa only [primaryGenerator, dite_eq_left hex] using Classical.choose_spec hex
  exact primary_unique hs.2 hn hs.1

def primaryIdealEquiv (c : ArithmeticContext) :
    {n : O // PrimaryOutside c n} ≃ {a : Ideal O // Outside c.S a} where
  toFun n := ⟨principal n, n.property.2.2⟩
  invFun a := ⟨primaryGenerator a, by
    have hs := primaryGenerator_spec_outside c a.property
    refine ⟨?_, hs.2, ?_⟩
    · intro hz
      apply a.property.1
      rw [← hs.1, hz]
      simp [principal]
    · simpa only [hs.1] using a.property⟩
  left_inv n := Subtype.ext (primaryGenerator_principal n.property.2.1)
  right_inv a := Subtype.ext (primaryGenerator_spec_outside c a.property).1

theorem tsum_primary (c : ArithmeticContext) (F : Ideal O → ℂ) :
    (∑' a : Ideal O, if Outside c.S a then F a else 0) =
      ∑' n : O, if PrimaryOutside c n then F (principal n) else 0 := by
  calc
    _ = ∑' a : {a : Ideal O // Outside c.S a}, F a :=
      (tsum_subtype {a : Ideal O | Outside c.S a} F).symm
    _ = ∑' n : {n : O // PrimaryOutside c n}, F (principal n) :=
      ((primaryIdealEquiv c).tsum_eq (fun a => F a)).symm
    _ = _ := tsum_subtype {n : O | PrimaryOutside c n} (fun n => F (principal n))

theorem tsum_squarefree_primary (c : ArithmeticContext) (F : Ideal O → ℂ) :
    (∑' a : Ideal O, if SquarefreeOutside c.S a then F a else 0) =
      ∑' n : O, if n ≠ 0 ∧ IsPrimary n ∧ Squarefree (principal n) ∧
        Outside c.S (principal n) then F (principal n) else 0 := by
  convert tsum_primary c (fun a => if Squarefree a then F a else 0) using 1
  · apply tsum_congr
    intro a
    by_cases ho : Outside c.S a <;> by_cases hs : Squarefree a <;>
      simp [SquarefreeOutside, ho, hs]
  · apply tsum_congr
    intro n
    by_cases hp : PrimaryOutside c n <;> by_cases hs : Squarefree (principal n) <;>
      simp_all [PrimaryOutside]

def idealTerm (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (X : ℝ) (k : O) (f n b : Ideal O) : ℂ :=
  (star (alpha n) * gauss 2 n * completedTwist c ξ k f n *
    star (alpha b) ^ (3 : ℕ) * completedTwist c ξ k f b ^ (3 : ℕ)) /
    ((Real.sqrt (normIdeal n) : ℂ) * (normIdeal b : ℂ)) *
    ((Real.sqrt (normIdeal n * normIdeal b ^ (3 : ℕ) / X) : ℂ) *
      W (normIdeal n * normIdeal b ^ (3 : ℕ) / X))

def thetaTerm (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (X : ℝ) (k : O) (f : Ideal O) (n b : O) : ℂ :=
  cuspCoefficient .zero (embedding lambda ^ (-3 : ℤ) * embedding (n * b ^ 3)) *
    thetaMultiplier c ξ k f (n * b ^ 3) *
    star (embedding (n * b ^ 3) / (‖embedding (n * b ^ 3)‖ : ℂ)) *
    W (normElement (n * b ^ 3) / X)

theorem completedRow_reindex (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X : ℝ) (k : O) (f : Ideal O) :
    completedRow c ξ W X k f =
      ∑' n : O, if n ≠ 0 ∧ IsPrimary n ∧ Squarefree (principal n) ∧
          Outside c.S (principal n) then
        ∑' b : O, if PrimaryOutside c b then
          idealTerm c ξ W X k f (principal n) (principal b) else 0
      else 0 := by
  change (∑' n : Ideal O, if SquarefreeOutside c.S n then
    ∑' b : Ideal O, if Outside c.S b then idealTerm c ξ W X k f n b else 0
    else 0) = _
  rw [tsum_squarefree_primary]
  apply tsum_congr
  intro n
  split_ifs
  · exact tsum_primary c _
  · rfl

theorem principal_cube (n b : O) :
    principal (n * b ^ 3) = principal n * principal b ^ 3 := by
  simp only [principal, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_pow]

theorem normElement_cube (n b : O) :
    normElement (n * b ^ 3) = normElement n * normElement b ^ 3 := by
  simp only [normElement, principal_cube, normIdeal, map_mul, map_pow,
    Nat.cast_mul, Nat.cast_pow]

theorem phase_cube {n b : O} (hn : IsPrimary n) (hb : IsPrimary b) :
    embedding (n * b ^ 3) / (‖embedding (n * b ^ 3)‖ : ℂ) =
      alpha (principal n) * alpha (principal b) ^ 3 := by
  simp only [alpha, primaryGenerator_principal hn, primaryGenerator_principal hb,
    ArithmeticProof.embedding_mul, embedding_pow, norm_mul, norm_pow,
    Complex.ofReal_mul, Complex.ofReal_pow, div_pow]
  exact mul_div_mul_comm _ _ _ _

theorem normElement_pos {n : O} (hn : n ≠ 0) : 0 < normElement n := by
  have hp : principal n ≠ ⊥ := fun h => hn (Ideal.span_singleton_eq_bot.mp h)
  unfold normElement normIdeal
  exact_mod_cast Nat.pos_of_ne_zero (fun h => hp (Ideal.absNorm_eq_zero_iff.mp h))

theorem sqrt_cube_ratio {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) :
    Real.sqrt (a * b ^ 3 / X) / (Real.sqrt a * b) = Real.sqrt b / Real.sqrt X := by
  have hb3 : b ^ 3 = b ^ 2 * b := by ring
  rw [Real.sqrt_div (mul_nonneg ha.le (pow_nonneg hb.le _)),
    Real.sqrt_mul ha.le, hb3, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  field_simp [ne_of_gt hb, ne_of_gt (Real.sqrt_pos.2 ha),
    ne_of_gt (Real.sqrt_pos.2 hX)]

/-- The nonzero coefficient identity at the squarefree/cube indices.
This requires uniqueness of the chosen TauFormula value and compatibility of
the cubic and normalized sextic Gauss sums; neither is assumed as an axiom. -/
def CoefficientBridgeStatement : Prop :=
  ∀ (c : ArithmeticContext), ArithmeticRelations c →
    ∀ (ξ : RayCharacter c) (k : O) (f : Ideal O), Outside c.S f →
      ∀ n b : O, PrimaryCubeData n b → Outside c.S (principal n) →
        Outside c.S (principal b) →
        cuspCoefficient .zero (embedding lambda ^ (-3 : ℤ) * embedding (n * b ^ 3)) *
          thetaMultiplier c ξ k f (n * b ^ 3) =
          (((3 : ℝ) ^ (5 / 2 : ℝ) : ℝ) : ℂ) * (Real.sqrt (normElement b) : ℂ) *
            gauss 2 (principal n) * completedTwist c ξ k f (principal n) *
            completedTwist c ξ k f (principal b) ^ (3 : ℕ)

theorem term_normalization (hcoeff : CoefficientBridgeStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (k : O) (f : Ideal O)
    (hf : Outside c.S f) (n b : O) (hn : PrimaryCubeData n b)
    (hno : Outside c.S (principal n)) (hbo : Outside c.S (principal b)) :
    idealTerm c ξ W X k f (principal n) (principal b) =
      (((3 : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt X : ℝ) : ℂ)⁻¹ *
        thetaTerm c ξ W X k f n b := by
  have ha := normElement_pos hn.1
  have hb := normElement_pos hn.2.1
  have hs : (Real.sqrt (normElement n * normElement b ^ 3 / X) : ℂ) /
      ((Real.sqrt (normElement n) : ℂ) * (normElement b : ℂ)) =
        (Real.sqrt (normElement b) : ℂ) / (Real.sqrt X : ℂ) := by
    exact_mod_cast sqrt_cube_ratio ha hb hX
  have hC : (((3 : ℝ) ^ (5 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _))
  have hRX : (Real.sqrt X : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hX))
  unfold thetaTerm
  rw [hcoeff c hc ξ k f hf n b hn hno hbo, phase_cube hn.2.2.1 hn.2.2.2.1,
    normElement_cube]
  change idealTerm c ξ W X k f (principal n) (principal b) = _
  calc
    _ = (star (alpha (principal n)) * gauss 2 (principal n) *
        completedTwist c ξ k f (principal n) * star (alpha (principal b)) ^ 3 *
        completedTwist c ξ k f (principal b) ^ 3) *
        ((Real.sqrt (normElement n * normElement b ^ 3 / X) : ℂ) /
          ((Real.sqrt (normElement n) : ℂ) * (normElement b : ℂ))) *
        W (normElement n * normElement b ^ 3 / X) := by
          unfold idealTerm normElement
          ring
    _ = _ := by
      rw [hs]
      simp only [Complex.ofReal_mul, star_mul, star_pow]
      field_simp [hC, hRX]

theorem row_realization (hcoeff : CoefficientBridgeStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (k : O) (f : Ideal O)
    (hf : Outside c.S f) :
    completedRow c ξ W X k f =
      (((3 : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt X : ℝ) : ℂ)⁻¹ *
        ∑' n : O, if n ≠ 0 ∧ IsPrimary n ∧ Squarefree (principal n) ∧
            Outside c.S (principal n) then
          ∑' b : O, if PrimaryOutside c b then thetaTerm c ξ W X k f n b else 0
        else 0 := by
  rw [completedRow_reindex, ← tsum_mul_left]
  apply tsum_congr
  intro n
  split_ifs with hn
  · rw [← tsum_mul_left]
    apply tsum_congr
    intro b
    split_ifs with hb
    · exact term_normalization hcoeff c hc ξ W X hX k f hf n b
        ⟨hn.1, hb.1, hn.2.1, hb.2.1, hn.2.2.1⟩ hn.2.2.2 hb.2.2
    · simp
  · simp

def frequency (m : O) : ℂ := embedding lambda ^ (-3 : ℤ) * embedding m

def conjugateTerm (z : ℂ) (v : ℝ) (m : O) : ℂ :=
  if m = 0 then 0 else cuspCoefficient .zero (frequency m) * thetaMode (frequency m) z v

def thetaConstant (v : ℝ) : ℂ :=
  ((3 : ℝ) ^ (5 / 2 : ℝ) / 2 * v ^ (2 / 3 : ℝ) : ℝ)

/-- Finite Fourier inversion for the concrete trace character and the actual
quotient. Proving this entails nondegeneracy of the trace pairing. -/
def FourierInversionStatement : Prop :=
  ∀ (φ : O → ℂ) (q : O), principal q ≠ ⊥ →
    (∀ a b : O, a - b ∈ principal q → φ a = φ b) →
    ∀ m : O, φ m = ∑' h : O ⧸ principal q, finiteFourier φ q h *
      additiveCharacter (embedding (m * residueLift (principal q) h) / embedding q)

/-- Compatibility of the two character conventions under the fixed oriented
embedding, including the factor lambda^2 in the translation. -/
def PhaseCompatibilityStatement : Prop :=
  ∀ m h q : O,
    breve (frequency m * (embedding (lambda ^ 2 * h) / embedding q)) =
      additiveCharacter (embedding (m * h) / embedding q)

/-- Convergence is an explicit child; no rearrangement relies on the default
value of a divergent tsum. This statement only involves the concrete series. -/
def ThetaSummabilityStatement : Prop :=
  ∀ (z : ℂ) (v : ℝ), 0 < v → Summable (conjugateTerm z v)

@[simp] theorem embedding_zero : embedding 0 = 0 := by
  simpa only [embeddingHom_apply] using map_zero embeddingHom

@[simp] theorem embedding_neg (m : O) : embedding (-m) = -embedding m := by
  simpa only [embeddingHom_apply] using map_neg embeddingHom m

@[simp] theorem frequency_neg (m : O) : frequency (-m) = -frequency m := by
  simp [frequency]

theorem embedding_omega_quadratic :
    embedding omega ^ 2 + embedding omega + 1 = 0 := by
  simpa only [map_add, map_pow, map_one, map_zero, embeddingHom_apply] using
    congrArg embeddingHom omega_sq_add_omega_add_one

theorem embedding_omega_im_pos : 0 < (embedding omega).im := by
  have hr := congrArg Complex.re embedding_omega_quadratic
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
    Complex.zero_re] at hr
  have hne : (embedding omega).im ≠ 0 := by
    intro hz
    rw [hz] at hr
    nlinarith [sq_nonneg ((embedding omega).re + (1 / 2 : ℝ))]
  have hnonneg : 0 ≤ (embedding omega).im := by
    unfold embedding
    split_ifs with h
    · exact h.le
    · change 0 ≤ -(rawEmbedding (omega : K)).im
      exact neg_nonneg.mpr (le_of_not_gt h)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem embedding_lambda : embedding lambda = (Real.sqrt 3 : ℂ) * Complex.I := by
  have hr := congrArg Complex.re embedding_omega_quadratic
  have hi := congrArg Complex.im embedding_omega_quadratic
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
    Complex.zero_re] at hr
  simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im,
    Complex.zero_im] at hi
  have hy := embedding_omega_im_pos
  have hfactor : (2 * (embedding omega).re + 1) * (embedding omega).im = 0 := by
    nlinarith [hi]
  have hx : (embedding omega).re = -(1 / 2 : ℝ) := by
    have h := (mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hy)
    linarith
  have himag : 2 * (embedding omega).im = Real.sqrt 3 := by
    rw [hx] at hr
    have hsq : (2 * (embedding omega).im) ^ 2 = 3 := by nlinarith
    rw [← hsq, Real.sqrt_sq (by positivity)]
  rw [← embeddingHom_apply, lambda, map_add, map_one, map_mul, map_ofNat,
    embeddingHom_apply]
  apply Complex.ext
  · norm_num [Complex.mul_re, hx]
  · simpa [Complex.mul_im] using himag

theorem phase_compatibility : PhaseCompatibilityStatement := by
  intro m h q
  have hLambda : embedding lambda ≠ 0 := by
    rw [embedding_lambda]
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (by norm_num : (0 : ℝ) < 3)))) Complex.I_ne_zero
  have hfreq : frequency m * (embedding (lambda ^ 2 * h) / embedding q) =
      (embedding (m * h) / embedding q) / embedding lambda := by
    by_cases hq : embedding q = 0
    · simp [hq]
    · simp only [frequency, ArithmeticProof.embedding_mul, embedding_pow,
        zpow_neg, zpow_ofNat]
      field_simp [hLambda, hq] <;> ring
  rw [hfreq, embedding_lambda]
  let u := embedding (m * h) / embedding q
  change breve (u / ((Real.sqrt 3 : ℂ) * Complex.I)) = additiveCharacter u
  have hre : (u / ((Real.sqrt 3 : ℂ) * Complex.I)).re = u.im / Real.sqrt 3 := by
    rw [div_mul_eq_div_div, Complex.div_I]
    simp [Complex.mul_re]
  unfold breve additiveCharacter
  rw [show u / ((Real.sqrt 3 : ℂ) * Complex.I) +
      star (u / ((Real.sqrt 3 : ℂ) * Complex.I)) =
      ((2 * (u / ((Real.sqrt 3 : ℂ) * Complex.I)).re : ℝ) : ℂ) from
        Complex.add_conj _]
  rw [hre]
  congr 1
  push_cast
  ring

@[simp] theorem thetaMultiplier_zero (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) : thetaMultiplier c ξ k f 0 = 0 := by
  simp [thetaMultiplier, Outside, principal]

theorem breve_add (z w : ℂ) : breve (z + w) = breve z * breve w := by
  unfold breve
  rw [star_add]
  rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (z + w + (star z + star w)) =
    ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (z + star z) +
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (w + star w) by ring]
  exact Complex.exp_add _ _

theorem star_breve (z : ℂ) : star (breve z) = breve (-z) := by
  unfold breve
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.star_def, map_ofNat] <;> ring

theorem star_thetaMode (ell z : ℂ) (v : ℝ) :
    star (thetaMode ell z v) = thetaMode (-ell) z v := by
  simp [thetaMode, star_breve, neg_mul]

theorem conjugate_cubicTheta (z : ℂ) (v : ℝ) :
    star (cubicTheta z v) = thetaConstant v + ∑' m : O, conjugateTerm z v m := by
  unfold cubicTheta
  rw [star_add, tsum_star]
  have hc : star (((3 : ℝ) ^ (5 / 2 : ℝ) / 2 * v ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
      thetaConstant v := by simp [thetaConstant]
  rw [hc]
  congr 1
  rw [← (Equiv.neg O).tsum_eq]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · simp [hm, conjugateTerm]
  · simp only [Equiv.neg_apply, neg_eq_zero, hm, ite_false, star_mul, star_thetaMode,
      embedding_neg, mul_neg, neg_neg, conjugateTerm, frequency, cuspCoefficient]
    ring

theorem conjugateTerm_translate (hphase : PhaseCompatibilityStatement)
    (z : ℂ) (v : ℝ) (m h q : O) :
    conjugateTerm (z + embedding (lambda ^ 2 * h) / embedding q) v m =
      conjugateTerm z v m *
        additiveCharacter (embedding (m * h) / embedding q) := by
  by_cases hm : m = 0
  · simp [conjugateTerm, hm]
  · simp only [conjugateTerm, hm, ite_false, thetaMode, mul_add, breve_add]
    rw [hphase m h q]
    ring

theorem twistedTheta_eq (φ : O → ℂ) (z : ℂ) (v : ℝ) :
    twistedTheta φ z v = ∑' m : O, conjugateTerm z v m * φ m := by
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · simp [conjugateTerm, hm]
  · simp only [hm, ite_false, conjugateTerm, frequency]
    ring

theorem fourier_zero (hinv : FourierInversionStatement)
    (c : ArithmeticContext) (ξ : RayCharacter c) (k : O) (f : Ideal O)
    (q : O) (hq : principal q ≠ ⊥)
    (hper : ∀ a b : O, a - b ∈ principal q →
      thetaMultiplier c ξ k f a = thetaMultiplier c ξ k f b) :
    (∑' h : O ⧸ principal q, finiteFourier (thetaMultiplier c ξ k f) q h) = 0 := by
  simpa [additiveCharacter] using (hinv (thetaMultiplier c ξ k f) q hq hper 0).symm

theorem theta_translates (hinv : FourierInversionStatement)
    (hphase : PhaseCompatibilityStatement) (hsum : ThetaSummabilityStatement)
    (c : ArithmeticContext) (ξ : RayCharacter c) (k : O) (f : Ideal O)
    (q : O) (hq : principal q ≠ ⊥)
    (hper : ∀ a b : O, a - b ∈ principal q →
      thetaMultiplier c ξ k f a = thetaMultiplier c ξ k f b)
    (z : ℂ) (v : ℝ) (hv : 0 < v) :
    twistedTheta (thetaMultiplier c ξ k f) z v =
      ∑' h : O ⧸ principal q, finiteFourier (thetaMultiplier c ξ k f) q h *
        star (cubicTheta (z + embedding (lambda ^ 2 * residueLift (principal q) h) /
          embedding q) v) := by
  letI : Finite (O ⧸ principal q) := Ring.HasFiniteQuotients.finiteQuotient hq
  letI : Fintype (O ⧸ principal q) := Fintype.ofFinite _
  let φ := thetaMultiplier c ξ k f
  have hzero : (∑ h : O ⧸ principal q, finiteFourier φ q h) = 0 := by
    simpa only [tsum_fintype] using fourier_zero hinv c ξ k f q hq hper
  rw [twistedTheta_eq]
  conv_rhs => rw [tsum_fintype]
  simp_rw [conjugate_cubicTheta, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hzero, zero_mul, zero_add]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun h _ =>
    (hsum (z + embedding (lambda ^ 2 * residueLift (principal q) h) / embedding q)
      v hv).mul_left (finiteFourier φ q h))]
  apply tsum_congr
  intro m
  simp_rw [conjugateTerm_translate hphase]
  change conjugateTerm z v m * φ m = _
  rw [hinv φ q hq hper m, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Exact assembly of the frozen endpoint; the three children are explicit
parameters, and `ArithmeticStatement` remains the original upstream input. -/
theorem theta_realization_step_of_components (_ha : ArithmeticStatement)
    (hcoeff : CoefficientBridgeStatement) (hinv : FourierInversionStatement)
    (hsum : ThetaSummabilityStatement) :
    ThetaRealizationStatement := by
  constructor
  · intro c hc ξ I W X k f _hW hX hf
    rw [row_realization hcoeff c hc ξ W X hX k f hf]
    congr 1
    apply tsum_congr
    intro n
    by_cases hn : n ≠ 0 ∧ IsPrimary n ∧ Squarefree (principal n) ∧
        Outside c.S (principal n)
    · simp only [hn, ne_eq, not_false_eq_true, and_true, ite_true]
      apply tsum_congr
      intro b
      by_cases hb : b ≠ 0 ∧ IsPrimary b ∧ Outside c.S (principal b)
      · simp only [PrimaryOutside, hb, ne_eq, not_false_eq_true, and_true,
          ite_true, thetaTerm]
      · simp only [PrimaryOutside, hb, ite_false]
    · simp only [hn, ite_false]
  · intro c ξ k f q hq hper z v hv
    exact theta_translates hinv phase_compatibility hsum c ξ k f q hq hper z v hv

end QRHShort.ThetaRealizationProof

#print axioms QRHShort.ThetaRealizationProof.completedRow_reindex
#print axioms QRHShort.ThetaRealizationProof.row_realization
#print axioms QRHShort.ThetaRealizationProof.conjugate_cubicTheta
#print axioms QRHShort.ThetaRealizationProof.phase_compatibility
#print axioms QRHShort.ThetaRealizationProof.theta_translates
#print axioms QRHShort.ThetaRealizationProof.theta_realization_step_of_components

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations : Array (Name × ConstantInfo) := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ThetaRealizationProof).isPrefixOf name then entries.push (name, info)
      else entries) #[]
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Theta realization depends on forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Theta realization declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No theta realization declarations audited"
  logInfo m!"THETA_REALIZATION_AUDIT declarations={checked} forbidden=0 pending_children=3"
