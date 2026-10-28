import QRHShort.ThetaStatements
import QRHShort.ArithmeticBasics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms

/-!
Reduction of the frozen theta bounds to arithmetic and analytic subproblems.
The support assertion follows directly from the explicit coefficient formulas.
All remaining inputs below are explicit propositions, never additional axioms.
-/

noncomputable section
open Classical MeasureTheory

namespace QRHShort.ThetaBoundsProof

def Supported (ell : ℂ) : Prop :=
  ∃ (u : Oˣ) (m : ℤ) (n b : O), -4 ≤ m ∧ PrimaryCubeData n b ∧
    ell = embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3)

def omegaUnit : Oˣ :=
  ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
    (by decide)).unit

@[simp] theorem omegaUnit_val : (omegaUnit : O) = omega :=
  IsUnit.unit_spec _

def signUnit (second : Bool) : Oˣ := if second then -1 else 1

@[simp] theorem embedding_signUnit (second : Bool) :
    embedding (signUnit second : O) = (if second then -1 else 1 : ℂ) := by
  cases second <;> simp [signUnit]

theorem supported_unit_mul (u : Oˣ) {ell : ℂ} (h : Supported ell) :
    Supported (embedding (u : O) * ell) := by
  rcases h with ⟨v, m, n, b, hm, hn, he⟩
  refine ⟨u * v, m, n, b, hm, hn, ?_⟩
  simp only [Units.val_mul, embedding_mul, he]
  ring

theorem supported_unit_mul_iff (u : Oˣ) (ell : ℂ) :
    Supported (embedding (u : O) * ell) ↔ Supported ell := by
  constructor
  · intro h
    have hinv : embedding ((u⁻¹ : Oˣ) : O) * (embedding (u : O) * ell) = ell := by
      rw [← mul_assoc, ← embedding_mul]
      simp
    simpa only [hinv] using supported_unit_mul u⁻¹ h
  · exact supported_unit_mul u

theorem supported_neg {ell : ℂ} (h : Supported ell) : Supported (-ell) := by
  simpa using supported_unit_mul (-1) h

theorem tau_spec {ell : ℂ} (h : tau ell ≠ 0) : TauFormula ell (tau ell) := by
  by_cases hex : ∃ v : ℂ, TauFormula ell v
  · simpa only [tau, dite_eq_left hex] using Classical.choose_spec hex
  · simp [tau, hex] at h

theorem auxiliaryTau_spec (second : Bool) {ell : ℂ} (h : auxiliaryTau second ell ≠ 0) :
    AuxiliaryTauFormula second ell (auxiliaryTau second ell) := by
  by_cases hex : ∃ v : ℂ, AuxiliaryTauFormula second ell v
  · simpa only [auxiliaryTau, dite_eq_left hex] using Classical.choose_spec hex
  · simp [auxiliaryTau, hex] at h

theorem tauFormula_supported {ell v : ℂ} (h : TauFormula ell v) : Supported ell := by
  rcases h with ⟨n, b, hn, s, hs, h⟩
  have hu : ∃ u : Oˣ, embedding (u : O) = s := by
    rcases hs with rfl | rfl
    · exact ⟨1, embedding_one⟩
    · exact ⟨-1, by simp⟩
  rcases hu with ⟨u, hu⟩
  rcases h with ⟨k, j, hk, he, _hv⟩ | ⟨k, he, _hv⟩
  · refine ⟨u * omegaUnit ^ j.val, 3 * (k : ℤ) - 4, n, b, by omega, hn, ?_⟩
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, embedding_mul, embedding_pow,
      omegaUnit_val, hu] using he
  · exact ⟨u, 3 * (k : ℤ) - 3, n, b, by omega, hn, by simpa only [hu] using he⟩

theorem auxiliaryTauFormula_supported (second : Bool) {ell v : ℂ}
    (h : AuxiliaryTauFormula second ell v) : Supported ell := by
  rcases h with ⟨n, b, hn, j, he, _hv⟩
  refine ⟨signUnit second * omegaUnit ^ j.val, -4, n, b, le_rfl, hn, ?_⟩
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, embedding_mul, embedding_pow,
    omegaUnit_val, embedding_signUnit] using he

theorem cuspCoefficient_supported (σ : ThetaCusp) (ell : ℂ)
    (h : cuspCoefficient σ ell ≠ 0) : Supported ell := by
  cases σ with
  | zero =>
    have ht : tau (-ell) ≠ 0 := by
      intro hz
      exact h (by simp only [cuspCoefficient, hz, mul_zero, zero_mul, star_zero])
    simpa only [neg_neg] using supported_neg (tauFormula_supported (tau_spec ht))
  | plus =>
    have ht : auxiliaryTau true (embedding omega * (-ell)) ≠ 0 := by
      intro hz
      exact h (by simp only [cuspCoefficient, hz, mul_zero, zero_mul, star_zero])
    have hs := auxiliaryTauFormula_supported true (auxiliaryTau_spec true ht)
    have hs' : Supported (-ell) := (supported_unit_mul_iff omegaUnit (-ell)).mp
      (by simpa only [omegaUnit_val] using hs)
    simpa only [neg_neg] using supported_neg hs'
  | minus =>
    have ht : auxiliaryTau false (embedding omega ^ 2 * (-ell)) ≠ 0 := by
      intro hz
      exact h (by simp only [cuspCoefficient, hz, mul_zero, zero_mul, star_zero])
    have hs := auxiliaryTauFormula_supported false (auxiliaryTau_spec false ht)
    have hs' : Supported (-ell) := (supported_unit_mul_iff (omegaUnit ^ 2) (-ell)).mp
      (by simpa only [Units.val_pow_eq_pow_val, embedding_pow, omegaUnit_val] using hs)
    simpa only [neg_neg] using supported_neg hs'

@[simp] theorem breve_norm (z : ℂ) : ‖breve z‖ = 1 := by
  simp [breve, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

@[simp] theorem ninthPhase_norm (j : Fin 3) : ‖ninthPhase j‖ = 1 := by
  unfold ninthPhase
  split_ifs <;> simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem cuspCoefficient_zero_norm (ell : ℂ) :
    ‖cuspCoefficient .zero ell‖ = ‖tau (-ell)‖ := by
  simp [cuspCoefficient]

theorem cuspCoefficient_plus_norm (ell : ℂ) :
    ‖cuspCoefficient .plus ell‖ = ‖auxiliaryTau true (embedding omega * (-ell))‖ := by
  simp [cuspCoefficient, norm_mul]

theorem cuspCoefficient_minus_norm (ell : ℂ) :
    ‖cuspCoefficient .minus ell‖ = ‖auxiliaryTau false (embedding omega ^ 2 * (-ell))‖ := by
  simp [cuspCoefficient, norm_mul, norm_pow]

/-- The scale in the frozen coefficient bound, without its numerical factor 27. -/
def cubeScale (m : ℤ) (b : O) : ℝ :=
  (3 : ℝ) ^ ((m : ℝ) / 6) * ‖embedding b‖

theorem cubeScale_nonneg (m : ℤ) (b : O) : 0 ≤ cubeScale m b :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (norm_nonneg _)

/-- Arithmetic child: the squarefree cubic Gauss sum estimate, including
non-coprime numerators. Primary moduli avoid the prime above 3. -/
def CubicGaussBoundStatement : Prop :=
  ∀ (r n : O), n ≠ 0 → IsPrimary n → Squarefree (principal n) →
    ‖cubicGauss r n‖ ≤ ‖embedding n‖

/-- The ideal-theoretic part of cube-scale uniqueness. Adapted from the
read-only upstream `GaussSum/BesselReflection.lean:416`; only Mathlib facts
are used here, with the present frozen ring of integers. -/
theorem squarefree_cube_decomposition_unique {I J I' J' : Ideal O}
    (hJ : J ≠ 0) (hJ' : J' ≠ 0) (hI : Squarefree I) (hI' : Squarefree I')
    (h : I * J ^ 3 = I' * J' ^ 3) : I = I' ∧ J = J' := by
  let nf := UniqueFactorizationMonoid.normalizedFactors (α := Ideal O)
  have hf := congrArg nf h
  dsimp only [nf] at hf
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hI.ne_zero (pow_ne_zero _ hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI'.ne_zero (pow_ne_zero _ hJ'),
    UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_pow] at hf
  have hi := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hi' := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI'.ne_zero).mp hI'
  have hc (P : Ideal O) : (nf I).count P = (nf I').count P ∧
      (nf J).count P = (nf J').count P := by
    have he := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at he
    have h1 := Multiset.nodup_iff_count_le_one.mp hi P
    have h2 := Multiset.nodup_iff_count_le_one.mp hi' P
    dsimp only [nf]
    omega
  constructor
  · calc
      I = (nf I).prod := (Ideal.prod_normalizedFactors_eq_self hI.ne_zero).symm
      _ = (nf I').prod := congrArg Multiset.prod (Multiset.ext.mpr (fun P => (hc P).1))
      _ = I' := Ideal.prod_normalizedFactors_eq_self hI'.ne_zero
  · calc
      J = (nf J).prod := (Ideal.prod_normalizedFactors_eq_self hJ).symm
      _ = (nf J').prod := congrArg Multiset.prod (Multiset.ext.mpr (fun P => (hc P).2))
      _ = J' := Ideal.prod_normalizedFactors_eq_self hJ'

/-- Arithmetic child: a squarefree/cube representation determines its scale.
This is a uniqueness assertion about the actual Eisenstein integers, including
separation of the lambda valuation. No coefficient values occur in the input. -/
def PrimaryCubeScaleStatement : Prop :=
  ∀ (u u' : Oˣ) (m m' : ℤ) (n b n' b' : O),
    PrimaryCubeData n b → PrimaryCubeData n' b' →
    embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3) =
      embedding (u' : O) * embedding lambda ^ m' * embedding (n' * b' ^ 3) →
    cubeScale m b = cubeScale m' b'

/-- A bound valid for every representation of the given frequency. -/
def CoefficientBound (ell v : ℂ) : Prop :=
  ∀ (u : Oˣ) (m : ℤ) (n b : O), -4 ≤ m → PrimaryCubeData n b →
    ell = embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3) →
    ‖v‖ ≤ 27 * cubeScale m b

theorem bound_of_representation (hscale : PrimaryCubeScaleStatement)
    {ell v : ℂ} {u : Oˣ} {m : ℤ} {n b : O} (hn : PrimaryCubeData n b)
    (he : ell = embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3))
    (hb : ‖v‖ ≤ 27 * cubeScale m b) : CoefficientBound ell v := by
  intro u' m' n' b' _hm' hn' he'
  rw [← hscale u u' m m' n b n' b' hn hn' (he.symm.trans he')]
  exact hb

theorem gauss_ratio_bound (hgauss : CubicGaussBoundStatement) (r : O)
    {n b : O} (hn : PrimaryCubeData n b) :
    ‖star (cubicGauss r n) * (‖embedding b / embedding n‖ : ℂ)‖ ≤ ‖embedding b‖ := by
  have hnpos : 0 < ‖embedding n‖ := norm_pos_iff.mpr (embedding_eq_zero.not.mpr hn.1)
  calc
    _ = ‖cubicGauss r n‖ * (‖embedding b‖ / ‖embedding n‖) := by
      simp [norm_mul, norm_div]
    _ ≤ ‖embedding n‖ * (‖embedding b‖ / ‖embedding n‖) :=
      mul_le_mul_of_nonneg_right (hgauss r n hn.1 hn.2.2.1 hn.2.2.2.2)
        (div_nonneg (norm_nonneg _) hnpos.le)
    _ = ‖embedding b‖ := by field_simp [ne_of_gt hnpos]

theorem three_power_bound {a : ℝ} {m : ℤ} (h : a ≤ 3 + (m : ℝ) / 6) :
    (3 : ℝ) ^ a ≤ 27 * (3 : ℝ) ^ ((m : ℝ) / 6) := by
  calc
    _ ≤ (3 : ℝ) ^ (3 + (m : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = _ := by rw [Real.rpow_add (by norm_num)]; norm_num

theorem tauFormula_bound (hgauss : CubicGaussBoundStatement)
    (hscale : PrimaryCubeScaleStatement) {ell v : ℂ} (h : TauFormula ell v) :
    CoefficientBound ell v := by
  rcases h with ⟨n, b, hn, s, hs, h⟩
  have hu : ∃ u : Oˣ, embedding (u : O) = s := by
    rcases hs with rfl | rfl
    · exact ⟨1, embedding_one⟩
    · exact ⟨-1, by simp⟩
  rcases hu with ⟨u, hu⟩
  rcases h with ⟨k, j, hk, he, hv⟩ | ⟨k, he, hv⟩
  · apply bound_of_representation hscale hn (u := u * omegaUnit ^ j.val)
      (m := 3 * (k : ℤ) - 4)
      (by simpa only [Units.val_mul, Units.val_pow_eq_pow_val, embedding_mul, embedding_pow,
        omegaUnit_val, hu] using he)
    have hpow := three_power_bound (a := (k : ℝ) / 2 + 2)
      (m := 3 * (k : ℤ) - 4) (by push_cast; linarith)
    calc
      ‖v‖ = ‖star (cubicGauss (omega ^ j.val * lambda ^ 2) n) *
          (‖embedding b / embedding n‖ : ℂ)‖ * (3 : ℝ) ^ ((k : ℝ) / 2 + 2) := by
        rw [hv]
        simp [norm_mul, Real.rpow_nonneg]
      _ ≤ ‖embedding b‖ * (3 : ℝ) ^ ((k : ℝ) / 2 + 2) :=
        mul_le_mul_of_nonneg_right (gauss_ratio_bound hgauss _ hn)
          (Real.rpow_nonneg (by norm_num) _)
      _ ≤ ‖embedding b‖ * (27 * (3 : ℝ) ^ (((3 * (k : ℤ) - 4 : ℤ) : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = _ := by unfold cubeScale; ring
  · apply bound_of_representation hscale hn (u := u) (m := 3 * (k : ℤ) - 3)
      (by simpa only [hu] using he)
    have hpow := three_power_bound (a := (k : ℝ) / 2 + 5 / 2)
      (m := 3 * (k : ℤ) - 3) (by push_cast; linarith)
    calc
      ‖v‖ = ‖star (cubicGauss 1 n) * (‖embedding b / embedding n‖ : ℂ)‖ *
          (3 : ℝ) ^ ((k : ℝ) / 2 + 5 / 2) := by
        rw [hv]
        simp [norm_mul, Real.rpow_nonneg]
      _ ≤ ‖embedding b‖ * (3 : ℝ) ^ ((k : ℝ) / 2 + 5 / 2) :=
        mul_le_mul_of_nonneg_right (gauss_ratio_bound hgauss _ hn)
          (Real.rpow_nonneg (by norm_num) _)
      _ ≤ ‖embedding b‖ * (27 * (3 : ℝ) ^ (((3 * (k : ℤ) - 3 : ℤ) : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = _ := by unfold cubeScale; ring

theorem auxiliaryTauFormula_bound (hgauss : CubicGaussBoundStatement)
    (hscale : PrimaryCubeScaleStatement) (second : Bool) {ell v : ℂ}
    (h : AuxiliaryTauFormula second ell v) : CoefficientBound ell v := by
  rcases h with ⟨n, b, hn, j, he, hv⟩
  apply bound_of_representation hscale hn (u := signUnit second * omegaUnit ^ j.val)
    (m := -4) (by simpa only [Units.val_mul, Units.val_pow_eq_pow_val, embedding_mul,
      embedding_pow, omegaUnit_val, embedding_signUnit] using he)
  have hpow : (9 : ℝ) ≤ 27 * (3 : ℝ) ^ (((-4 : ℤ) : ℝ) / 6) := by
    convert three_power_bound (a := 2) (m := -4) (by norm_num) using 1 <;> norm_num
  calc
    ‖v‖ = 9 * ‖star (cubicGauss (omega ^ j.val * lambda ^ 2) n) *
        (‖embedding b / embedding n‖ : ℂ)‖ := by
      rw [hv]
      cases second <;> simp [norm_mul, norm_pow] <;> ring
    _ ≤ 9 * ‖embedding b‖ :=
      mul_le_mul_of_nonneg_left (gauss_ratio_bound hgauss _ hn) (by norm_num)
    _ ≤ (27 * (3 : ℝ) ^ (((-4 : ℤ) : ℝ) / 6)) * ‖embedding b‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = _ := by unfold cubeScale; ring

theorem tau_bound (hgauss : CubicGaussBoundStatement) (hscale : PrimaryCubeScaleStatement)
    (ell : ℂ) : CoefficientBound ell (tau ell) := by
  by_cases hz : tau ell = 0
  · intro u m n b _hm _hn _he
    rw [hz, norm_zero]
    exact mul_nonneg (by norm_num) (cubeScale_nonneg m b)
  · exact tauFormula_bound hgauss hscale (tau_spec hz)

theorem auxiliaryTau_bound (hgauss : CubicGaussBoundStatement)
    (hscale : PrimaryCubeScaleStatement) (second : Bool) (ell : ℂ) :
    CoefficientBound ell (auxiliaryTau second ell) := by
  by_cases hz : auxiliaryTau second ell = 0
  · intro u m n b _hm _hn _he
    rw [hz, norm_zero]
    exact mul_nonneg (by norm_num) (cubeScale_nonneg m b)
  · exact auxiliaryTauFormula_bound hgauss hscale second (auxiliaryTau_spec second hz)

theorem cuspCoefficient_bound (hgauss : CubicGaussBoundStatement)
    (hscale : PrimaryCubeScaleStatement) (σ : ThetaCusp) (ell : ℂ) :
    CoefficientBound ell (cuspCoefficient σ ell) := by
  intro u m n b hm hn he
  cases σ with
  | zero =>
    rw [cuspCoefficient_zero_norm]
    apply tau_bound hgauss hscale (-ell) (-u) m n b hm hn
    simp only [Units.val_neg, embedding_neg, he]
    ring
  | plus =>
    rw [cuspCoefficient_plus_norm]
    apply auxiliaryTau_bound hgauss hscale true (embedding omega * (-ell))
      (-omegaUnit * u) m n b hm hn
    simp only [Units.val_mul, Units.val_neg, embedding_mul, embedding_neg, omegaUnit_val, he]
    ring
  | minus =>
    rw [cuspCoefficient_minus_norm]
    apply auxiliaryTau_bound hgauss hscale false (embedding omega ^ 2 * (-ell))
      (-(omegaUnit ^ 2) * u) m n b hm hn
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, embedding_mul, embedding_neg,
      embedding_pow, omegaUnit_val, he]
    ring

/-- The point sigma + iu on a vertical contour. -/
def contourPoint (sigma u : ℝ) : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I

/-- The complete Mellin multiplier, with x-dependence removed. -/
def mellinKernel (j : ℕ) (V : ℝ → ℂ) (sigma u : ℝ) : ℂ :=
  let t := contourPoint sigma u
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (-t) ^ j * mellinTransform V (-t) *
    (Complex.Gamma (7 / 6 + t) * Complex.Gamma (5 / 6 + t) /
      (Complex.Gamma (7 / 6 - t) * Complex.Gamma (5 / 6 - t))) *
    ((((2 * Real.pi) ^ (4 : ℕ) / 27 : ℝ) : ℂ) ^ (-t))

def shiftedWeight (j : ℕ) (V : ℝ → ℂ) (sigma x : ℝ) : ℂ :=
  ∫ u : ℝ, mellinKernel j V sigma u * (x : ℂ) ^ (-contourPoint sigma u)

/-- At the original contour and derivative order zero, the normalized kernel
is exactly the frozen theta transform, without any analytic assumptions. -/
theorem shiftedWeight_zero (V : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    shiftedWeight 0 V 0 x = thetaWeight V x := by
  unfold shiftedWeight thetaWeight
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  have harg : (2 * Real.pi) ^ (4 : ℕ) * x / 27 =
      ((2 * Real.pi) ^ (4 : ℕ) / 27) * x := by ring
  rw [harg]
  simp only [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (by positivity) hx.le]
  simp only [mellinKernel, contourPoint, Complex.ofReal_zero, zero_add,
    pow_zero, mul_one, neg_mul, Complex.ofReal_inv]
  ring

/-- Analytic child: differentiation and moving the original imaginary-axis
contour. The domain stays to the right of the first numerator pole -5/6.
A proof route is in upstream `Mellin/InverseContour.lean:124,196`; it must be
adapted to the present definitions without importing the whole manuscript. -/
def MellinContourShiftStatement : Prop :=
  ∀ (j : ℕ) (I : SupportInterval) (V : ℝ → ℂ), SmoothSupported I V →
    ∀ sigma : ℝ, -(1 / 4 : ℝ) ≤ sigma → ∀ x : ℝ, 0 < x →
      eulerDerivative j (thetaWeight V) x = shiftedWeight j V sigma x

/-- Analytic child: absolute integrability and a uniform L1 bound for the two
shifted kernels. J depends on A,j only; K may also depend on the support interval.
Its proof needs polynomial bounds for the Gamma quotient and integration by
parts for the compactly supported Mellin transform. Upstream
`QuadraticSieve/MainTermDifference.lean:204-377,532-655` and
`Mellin/UniformKernelBounds.lean:193-313` provide candidate arguments, but
the derivative order here must be uniform over support intervals I. -/
def MellinKernelBoundStatement : Prop :=
  ∀ (A : ℝ) (j : ℕ), 0 < A → ∃ J : ℕ, 1 ≤ J ∧
    ∀ I : SupportInterval, ∃ K : ℝ, 0 ≤ K ∧ ∀ V : ℝ → ℂ,
      SmoothSupported I V → ∀ sigma : ℝ, (sigma = -(1 / 4 : ℝ) ∨ sigma = A) →
        Integrable (mellinKernel j V sigma) ∧
          (∫ u : ℝ, ‖mellinKernel j V sigma u‖) ≤ K * weightNorm J V

theorem contour_cpow_norm {x : ℝ} (hx : 0 < x) (sigma u : ℝ) :
    ‖(x : ℂ) ^ (-contourPoint sigma u)‖ = x ^ (-sigma) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [contourPoint, Complex.mul_re]

theorem shiftedWeight_norm_le (j : ℕ) (V : ℝ → ℂ) (sigma : ℝ)
    {x : ℝ} (hx : 0 < x) :
    ‖shiftedWeight j V sigma x‖ ≤
      (∫ u : ℝ, ‖mellinKernel j V sigma u‖) * x ^ (-sigma) := by
  calc
    _ ≤ ∫ u : ℝ, ‖mellinKernel j V sigma u *
        (x : ℂ) ^ (-contourPoint sigma u)‖ := norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_mul, contour_cpow_norm hx]
      exact integral_mul_const _ _

theorem thetaWeight_bound (hshift : MellinContourShiftStatement)
    (hkernel : MellinKernelBoundStatement) :
    ∀ (A : ℝ) (j : ℕ), 0 < A → ∃ J : ℕ, 1 ≤ J ∧
      ∀ I : SupportInterval, ∃ K : ℝ, 0 ≤ K ∧ ∀ V : ℝ → ℂ,
        SmoothSupported I V → ∀ x : ℝ, 0 < x →
          ‖eulerDerivative j (thetaWeight V) x‖ ≤
            K * weightNorm J V * min (x ^ (1 / 4 : ℝ)) (x ^ (-A)) := by
  intro A j hA
  obtain ⟨J, hJ, hkernel⟩ := hkernel A j hA
  refine ⟨J, hJ, ?_⟩
  intro I
  obtain ⟨K, hK, hkernel⟩ := hkernel I
  refine ⟨K, hK, ?_⟩
  intro V hV x hx
  have hlo := hkernel V hV (-(1 / 4 : ℝ)) (Or.inl rfl)
  have hhi := hkernel V hV A (Or.inr rfl)
  have hkw : 0 ≤ K * weightNorm J V :=
    (integral_nonneg (fun u => norm_nonneg (mellinKernel j V (-(1 / 4 : ℝ)) u))).trans hlo.2
  rw [mul_min_of_nonneg _ _ hkw]
  apply le_min
  · rw [hshift j I V hV _ le_rfl x hx]
    have h := (shiftedWeight_norm_le j V (-(1 / 4 : ℝ)) hx).trans
      (mul_le_mul_of_nonneg_right hlo.2 (Real.rpow_nonneg hx.le _))
    simpa only [neg_neg] using h
  · rw [hshift j I V hV A (by linarith) x hx]
    exact (shiftedWeight_norm_le j V A hx).trans
      (mul_le_mul_of_nonneg_right hhi.2 (Real.rpow_nonneg hx.le _))

/-- Exact assembly of the original frozen endpoint from the four children.
The support assertion has no premises; all arithmetic and analytic inputs
remaining open are visible in this theorem's type. -/
theorem theta_bounds_of_inputs (hgauss : CubicGaussBoundStatement)
    (hscale : PrimaryCubeScaleStatement) (hshift : MellinContourShiftStatement)
    (hkernel : MellinKernelBoundStatement) : ThetaBoundsStatement := by
  refine ⟨cuspCoefficient_supported, ?_, thetaWeight_bound hshift hkernel⟩
  intro sigma u m n b hm hn
  have h := cuspCoefficient_bound hgauss hscale sigma
    (embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3))
    u m n b hm hn rfl
  simpa only [cubeScale, mul_assoc] using h

end QRHShort.ThetaBoundsProof

#print axioms QRHShort.ThetaBoundsProof.cuspCoefficient_supported
#print axioms QRHShort.ThetaBoundsProof.squarefree_cube_decomposition_unique
#print axioms QRHShort.ThetaBoundsProof.shiftedWeight_zero
#print axioms QRHShort.ThetaBoundsProof.cuspCoefficient_bound
#print axioms QRHShort.ThetaBoundsProof.thetaWeight_bound
#print axioms QRHShort.ThetaBoundsProof.theta_bounds_of_inputs

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations : Array (Name × ConstantInfo) := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ThetaBoundsProof).isPrefixOf name then entries.push (name, info)
      else entries) #[]
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Theta bounds reduction depends on forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Theta bounds reduction declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No theta bounds declarations audited"
  logInfo m!"THETA_BOUNDS_AUDIT declarations={checked} forbidden=0 pending_children=4"
