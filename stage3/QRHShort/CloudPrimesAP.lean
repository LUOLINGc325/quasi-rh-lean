import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

import Mathlib.Analysis.Complex.AbsMax

import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Calculus.LogDeriv

import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

import Mathlib.Analysis.SpecialFunctions.Log.Base
import QRHShort.PrimeAPAssembly
import QRHShort.MainStatements
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Data.Nat.Factorization.Induction

noncomputable section
open Classical Finset MeasureTheory
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPAux

/-- Exact finite character orthogonality for the actual residue condition. -/
theorem finite_residue_fourier {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ s, if (n : ZMod q) = a then f n else 0) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * ∑ n ∈ s, f n * χ n := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  symm
  calc
    _ = ∑ n ∈ s, (q.totient : ℂ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n) * f n := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
      by_cases h : (n : ZMod q) = a
      · simp [h, hφ]
      · simp [h, Ne.symm h]

/-- Averaging over the characters does not enlarge a uniform error: their
exact cardinality cancels the totient in finite Fourier inversion. -/
theorem norm_fourier_error_le {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (T : DirichletCharacter ℂ q → ℂ) (x E : ℝ)
    (hT : ∀ χ, ‖T χ - if χ = 1 then (x : ℂ) else 0‖ ≤ E) :
    ‖(q.totient : ℂ)⁻¹ * (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * T χ) -
      (x : ℂ) / (q.totient : ℂ)‖ ≤ E := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hinv : IsUnit a⁻¹ := by
    obtain ⟨u, rfl⟩ := ha
    rw [ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have hmain : (∑ χ : DirichletCharacter ℂ q,
      χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0)) = (x : ℂ) := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [MulChar.one_apply hinv, one_mul]
  have herr : (q.totient : ℂ)⁻¹ *
      (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * T χ) -
      (x : ℂ) / (q.totient : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * (T χ - if χ = 1 then (x : ℂ) else 0) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hmain]
    ring
  rw [herr, norm_mul, norm_inv, norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖χ a⁻¹ * (T χ - if χ = 1 then (x : ℂ) else 0)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ _χ : DirichletCharacter ℂ q, E := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one a⁻¹)).trans (hT χ)
    _ = E := by
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      exact inv_mul_cancel_left₀ hφ E

/-- The finite Mangoldt progression estimate with exactly the same constant
as the bound for all twisted sums. No analytic estimate is assumed here beyond
that explicitly displayed finite-sum bound. -/
theorem mangoldt_residue_error_le {q : ℕ} [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (s : Finset ℕ) (x E : ℝ)
    (hT : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
        if χ = 1 then (x : ℂ) else 0‖ ≤ E) :
    |(∑ n ∈ s, if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0) -
      x / (q.totient : ℝ)| ≤ E := by
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hsum : ((∑ n ∈ s,
      if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0 : ℝ) : ℂ) =
      ∑ n ∈ s, if (n : ZMod q) = (a : ZMod q)
        then (ArithmeticFunction.vonMangoldt n : ℂ) else 0 := by
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n % q = a % q
    · have he : (n : ZMod q) = (a : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff' n a q).mpr h
      simp [h, he]
    · have he : (n : ZMod q) ≠ (a : ZMod q) :=
        fun hna => h ((ZMod.natCast_eq_natCast_iff' n a q).mp hna)
      simp [h, he]
  have hbound := norm_fourier_error_le (a : ZMod q) hu
    (fun χ => ∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) x E hT
  rw [← finite_residue_fourier (a : ZMod q) hu s
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)), ← hsum] at hbound
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hbound

/-- The endpoint contribution in Abel summation removes exactly one log. -/
theorem abel_error_endpoint_le (C x e : ℝ) (hx : 2 ≤ x)
    (he : |e| ≤ C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2) :
    |e / Real.log x| ≤ C * x ^ ((11 : ℝ) / 12) * Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [abs_div, abs_of_pos hlog]
  calc
    _ ≤ (C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2) / Real.log x :=
      div_le_div_of_nonneg_right he hlog.le
    _ = _ := by field_simp [hlog.ne']

/-- Quantitative Abel error integration with the exact exponent 11/12.
The displayed integrability premise records the genuine integral used here;
no totalized divergent integral is used to justify a rearrangement. -/
theorem abel_error_integral_le (C x : ℝ) (hC : 0 ≤ C) (hx : 2 ≤ x)
    (e : ℝ → ℝ)
    (he : ∀ t ∈ Set.Icc (2 : ℝ) x,
      |e t| ≤ C * t ^ ((11 : ℝ) / 12) * (Real.log t) ^ 2)
    (hint : IntervalIntegrable (fun t => e t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x) :
    |∫ t in (2 : ℝ)..x, e t / (t * (Real.log t) ^ 2)| ≤
      (12 / 11 : ℝ) * C * x ^ ((11 : ℝ) / 12) := by
  have hpower : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 12))
      MeasureTheory.volume 2 x :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) x) :
      ‖e t / (t * (Real.log t) ^ 2)‖ ≤ C * t ^ (-(1 : ℝ) / 12) := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hpow : t ^ (-(1 : ℝ) / 12) = t ^ ((11 : ℝ) / 12) / t := by
      rw [show -(1 : ℝ) / 12 = (11 : ℝ) / 12 - 1 by norm_num,
        Real.rpow_sub ht0, Real.rpow_one]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (pow_pos hlog 2))]
    calc
      _ ≤ (C * t ^ ((11 : ℝ) / 12) * (Real.log t) ^ 2) /
          (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right (he t ht) (by positivity)
      _ = _ := by rw [hpow]; field_simp [ht0.ne', hlog.ne']
  have hle := (intervalIntegral.norm_integral_le_integral_norm hx
    (f := fun t => e t / (t * (Real.log t) ^ 2))).trans
    (intervalIntegral.integral_mono_on hx hint.norm (hpower.const_mul C) hpoint)
  rw [Real.norm_eq_abs] at hle
  have h_eval : (∫ t in (2 : ℝ)..x, C * t ^ (-(1 : ℝ) / 12)) =
      C * ((x ^ ((11 : ℝ) / 12) - (2 : ℝ) ^ ((11 : ℝ) / 12)) /
        ((11 : ℝ) / 12)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : -1 < -(1 : ℝ) / 12))]
    norm_num
  rw [h_eval] at hle
  refine hle.trans ?_
  calc
    _ ≤ C * (x ^ ((11 : ℝ) / 12) / ((11 : ℝ) / 12)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact sub_le_self _ (by positivity)
    _ = _ := by ring

/-- The actual twisted Mangoldt series continues as the actual negative
logarithmic derivative in the zero-free region. This is a holomorphic
continuation statement, with genuine `HasSum` on the original half-plane;
it contains no assertion of uniform conductor growth or a Perron estimate. -/
theorem twisted_mangoldt_analytic_continuation
    (hz : DirichletZeroFreeStatement) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∀ s : ℂ, 1 < s.re →
      HasSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / (n : ℂ) ^ s)
        (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)) ∧
    AnalyticOnNhd ℂ
      (fun s => -deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
      {s : ℂ | (11 : ℝ) / 12 < s.re ∧ (s ≠ 1 ∨ χ ≠ 1)} := by
  constructor
  · intro s hs
    have hseries := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      ← DirichletCharacter.LFunction_eq_LSeries χ hs] at hseries
    apply HasSum.congr_fun hseries
    intro n
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp [LSeries.term, hn, mul_comm]
  · have hopen : IsOpen {s : ℂ | s ≠ 1 ∨ χ ≠ 1} := by
      by_cases hχ : χ = 1
      · simpa only [hχ, ne_eq, not_true_eq_false, or_false] using
          (isOpen_ne : IsOpen {s : ℂ | s ≠ 1})
      · simp [hχ]
    have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
        {s : ℂ | s ≠ 1 ∨ χ ≠ 1} := by
      apply DifferentiableOn.analyticOnNhd _ hopen
      intro s hs
      exact (DirichletCharacter.differentiableAt_LFunction χ s hs).differentiableWithinAt
    intro s hs
    exact ((hL s hs.2).deriv.neg).div (hL s hs.2) (hz q χ s hs.1 hs.2)


/-- The exact finite floor-prefix shape used by theta is measurable. -/
theorem floor_prefix_sum_measurable (c : ℕ → ℝ) :
    Measurable (fun t : ℝ => ∑ n ∈ Icc 0 ⌊t⌋₊, c n) :=
  (measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 0 N, c n)).comp Nat.measurable_floor

/-- No analytic estimate is needed for the actual theta step-function's
integrability on a finite positive interval. -/
theorem floor_prefix_sum_intervalIntegrable (c : ℕ → ℝ) (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => ∑ n ∈ Icc 0 ⌊t⌋₊, c n) volume 2 x := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
  apply Measure.integrableOn_of_bounded (M := ∑ n ∈ Icc 0 ⌊x⌋₊, ‖c n‖)
    (measure_Icc_lt_top.ne) (floor_prefix_sum_measurable c).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊t⌋₊, ‖c n‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc le_rfl (Nat.floor_mono ht.2)) (fun _ _ _ => norm_nonneg _)

/-- The true theta error divided by t log²t is interval integrable. This
applies directly with c(n)=if prime/residue then log n else 0. -/
theorem floor_prefix_error_quotient_intervalIntegrable
    (c : ℕ → ℝ) (A x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      ((∑ n ∈ Icc 0 ⌊t⌋₊, c n) - A * t) / (t * (Real.log t) ^ 2)) volume 2 x := by
  have hf := floor_prefix_sum_intervalIntegrable c x hx
  have hA : IntervalIntegrable (fun t : ℝ => A * t) volume 2 x :=
    (continuous_const.mul continuous_id).intervalIntegrable 2 x
  have hinv : ContinuousOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have htlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1] : 1 < t)).ne'
    have hden : t * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 htlog)
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  simpa only [div_eq_mul_inv] using (hf.sub hA).mul_continuousOn hinv

/-- The boundary at 2 is retained in the exact main-term identity. -/
theorem abel_main_term_identity (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) =
      x / Real.log x - 2 / Real.log 2 +
        ∫ t in (2 : ℝ)..x, ((Real.log t) ^ 2)⁻¹ := by
  have hlog : ∀ t ∈ Set.uIcc (2 : ℝ) x, Real.log t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact (Real.log_pos (by linarith [ht.1] : 1 < t)).ne'
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) x, t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    linarith [ht.1]
  have hi₁ : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ContinuousAt.continuousWithinAt (by
      have ht0 := hpos t ht
      have htL := hlog t ht
      fun_prop)
  have hi₂ : IntervalIntegrable (fun t : ℝ => ((Real.log t) ^ 2)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ContinuousAt.continuousWithinAt (by
      have ht0 := hpos t ht
      have htL := hlog t ht
      have htL2 : (Real.log t) ^ 2 ≠ 0 := pow_ne_zero 2 htL
      fun_prop (disch := assumption))
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (2 : ℝ) x) :
      HasDerivAt (fun t : ℝ => t / Real.log t)
        ((Real.log t)⁻¹ - ((Real.log t) ^ 2)⁻¹) t := by
    have h := (hasDerivAt_id t).div (Real.hasDerivAt_log (hpos t ht)) (hlog t ht)
    convert h using 1
    · funext y
      rfl
    · dsimp only [id_eq]
      field_simp [hpos t ht,hlog t ht]
      <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi₁.sub hi₂)
  rw [intervalIntegral.integral_sub hi₁ hi₂] at he
  linarith

/-- A uniform q-independent error budget: A=1/φ(q) only uses 0≤A≤1. -/
theorem abel_error_budget (C x A U V : ℝ) (hC : 0 ≤ C) (hx : 2 ≤ x)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hU : |U| ≤ C * x ^ ((11 : ℝ) / 12) * Real.log x)
    (hV : |V| ≤ (12 / 11 : ℝ) * C * x ^ ((11 : ℝ) / 12)) :
    |U + V + 2 * A / Real.log 2| ≤
      (C + (12 / 11 : ℝ) * C / Real.log 2 + 2 / (Real.log 2) ^ 2) *
        x ^ ((11 : ℝ) / 12) * Real.log x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hpx : 1 ≤ x ^ ((11 : ℝ) / 12) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hlogx : 0 ≤ Real.log x := hl2.le.trans hlx
  have hv : (12 / 11 : ℝ) * C * x ^ ((11 : ℝ) / 12) ≤
      ((12 / 11 : ℝ) * C / Real.log 2) * x ^ ((11 : ℝ) / 12) * Real.log x := by
    calc
      _ = ((12 / 11 : ℝ) * C / Real.log 2) * x ^ ((11 : ℝ) / 12) * Real.log 2 := by
        field_simp [hl2.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hlx (by positivity)
  have hb : 2 * A / Real.log 2 ≤
      (2 / (Real.log 2) ^ 2) * x ^ ((11 : ℝ) / 12) * Real.log x := by
    calc
      _ ≤ 2 / Real.log 2 := div_le_div_of_nonneg_right (by linarith) hl2.le
      _ = (2 / (Real.log 2) ^ 2) * Real.log 2 := by field_simp [hl2.ne']
      _ ≤ (2 / (Real.log 2) ^ 2) * (x ^ ((11 : ℝ) / 12) * Real.log x) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hlx.trans (le_mul_of_one_le_left hlogx hpx)
      _ = _ := by ring
  calc
    _ ≤ |U| + |V| + |2 * A / Real.log 2| := (abs_add_le _ _).trans
      (add_le_add (abs_add_le U V) (le_refl |2 * A / Real.log 2|))
    _ ≤ C * x ^ ((11 : ℝ) / 12) * Real.log x +
        ((12 / 11 : ℝ) * C / Real.log 2) * x ^ ((11 : ℝ) / 12) * Real.log x +
        (2 / (Real.log 2) ^ 2) * x ^ ((11 : ℝ) / 12) * Real.log x := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * A / Real.log 2)]
      exact add_le_add (add_le_add hU (hV.trans hv)) hb
    _ = _ := by ring



/-- A finite-prefix Abel transfer, retaining its literal lower endpoint 2.
All integral identities below are proved from the actual integrable functions. -/
theorem finite_prefix_abel_transfer
    (c : ℕ → ℝ) (A C x N : ℝ)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hC : 0 ≤ C) (hx : 2 ≤ x)
    (hθ : ∀ t ∈ Set.Icc (2 : ℝ) x,
      |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - A * t| ≤
        C * t ^ ((11 : ℝ) / 12) * (Real.log t) ^ 2)
    (hAbel : N = (∑ n ∈ Icc 0 ⌊x⌋₊, c n) / Real.log x +
      ∫ t in (2 : ℝ)..x, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * (Real.log t) ^ 2)) :
    |N - A * ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹| ≤
      (C + (12 / 11 : ℝ) * C / Real.log 2 + 2 / (Real.log 2) ^ 2) *
        x ^ ((11 : ℝ) / 12) * Real.log x := by
  let Θ : ℝ → ℝ := fun t => ∑ n ∈ Icc 0 ⌊t⌋₊, c n
  let E : ℝ → ℝ := fun t => Θ t - A * t
  have hθquot : IntervalIntegrable (fun t : ℝ => Θ t / (t * (Real.log t) ^ 2)) volume 2 x := by
    simpa only [Θ,zero_mul,sub_zero] using
      floor_prefix_error_quotient_intervalIntegrable c 0 x hx
  have hEquot : IntervalIntegrable (fun t : ℝ => E t / (t * (Real.log t) ^ 2)) volume 2 x := by
    exact floor_prefix_error_quotient_intervalIntegrable c A x hx
  have hlog₂ : IntervalIntegrable (fun t : ℝ => ((Real.log t) ^ 2)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have htL : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1] : 1 < t)).ne'
    have htL2 : (Real.log t) ^ 2 ≠ 0 := pow_ne_zero 2 htL
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hsplit : (∫ t in (2 : ℝ)..x, E t / (t * (Real.log t) ^ 2)) =
      (∫ t in (2 : ℝ)..x, Θ t / (t * (Real.log t) ^ 2)) -
        A * ∫ t in (2 : ℝ)..x, ((Real.log t) ^ 2)⁻¹ := by
    calc
      _ = ∫ t in (2 : ℝ)..x,
          Θ t / (t * (Real.log t) ^ 2) - A * ((Real.log t) ^ 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        have htL : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1] : 1 < t)).ne'
        dsimp only [E]
        field_simp [ht0,htL]
        <;> ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hθquot (hlog₂.const_mul A),
          intervalIntegral.integral_const_mul]
  have hdecomp : N - A * (∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) =
      E x / Real.log x + (∫ t in (2 : ℝ)..x, E t / (t * (Real.log t) ^ 2)) +
        2 * A / Real.log 2 := by
    rw [hAbel,hsplit,abel_main_term_identity x hx]
    dsimp only [E,Θ]
    simp only [div_eq_mul_inv]
    ring
  rw [hdecomp]
  apply abel_error_budget C x A _ _ hC hx hA0 hA1
  · exact abel_error_endpoint_le C x (E x) hx (hθ x ⟨hx,le_rfl⟩)
  · exact abel_error_integral_le C x hC hx E hθ hEquot

end QRHShort.CloudBatch.PrimesAPAux

namespace QRHShort.CloudBatch.PrimeAPLargeHelpers

theorem totient_square_lower (n : ℕ) :
    n ≤ 2 * Nat.totient n ^ 2 ∧ (Odd n → n ≤ Nat.totient n ^ 2) := by
  apply induction_on_primes (motive := fun n : ℕ =>
    n ≤ 2 * Nat.totient n ^ 2 ∧ (Odd n → n ≤ Nat.totient n ^ 2))
  · simp
  · norm_num
  · intro p m hp hm
    by_cases hp2 : p = 2
    · subst p
      constructor
      · rcases Nat.even_or_odd m with heven | hodd
        · rw [Nat.totient_two_mul_of_even heven]
          nlinarith [hm.1]
        · rw [Nat.totient_two_mul_of_odd hodd]
          nlinarith [hm.2 hodd]
      · rintro ⟨k, hk⟩
        omega
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hpred : p ≤ (p - 1) ^ 2 := by
        have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
        nlinarith
      have hphi : (p - 1) * Nat.totient m ≤ Nat.totient (p * m) := by
        simpa only [Nat.totient_prime hp] using Nat.totient_super_multiplicative p m
      have hsq : ((p - 1) * Nat.totient m) ^ 2 ≤ Nat.totient (p * m) ^ 2 := by gcongr
      constructor
      · calc
          p * m ≤ p * (2 * Nat.totient m ^ 2) := Nat.mul_le_mul_left _ hm.1
          _ ≤ 2 * ((p - 1) * Nat.totient m) ^ 2 := by
            have hh := Nat.mul_le_mul_right (2 * Nat.totient m ^ 2) hpred
            nlinarith
          _ ≤ 2 * Nat.totient (p * m) ^ 2 := Nat.mul_le_mul_left _ hsq
      · intro hodd
        have hmOdd : Odd m := (Nat.odd_mul.mp hodd).2
        calc
          p * m ≤ p * Nat.totient m ^ 2 := Nat.mul_le_mul_left _ (hm.2 hmOdd)
          _ ≤ ((p - 1) * Nat.totient m) ^ 2 := by
            have hh := Nat.mul_le_mul_right (Nat.totient m ^ 2) hpred
            nlinarith
          _ ≤ Nat.totient (p * m) ^ 2 := hsq

theorem mangoldt_progression_large_bounds (x : ℝ) (q a : ℕ)
    (hx : 2 ≤ x) (hxq : x < (q : ℝ)) :
    0 ≤ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0) ∧
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0) ≤ Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hnq (n : ℕ) (hn : n ∈ Finset.Icc 0 ⌊x⌋₊) : n < q := by
    have hnx : (n : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hx0)
    exact_mod_cast hnx.trans_lt hxq
  have hΛ (n : ℕ) (hn : n ∈ Finset.Icc 0 ⌊x⌋₊) :
      ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
    by_cases hn0 : n = 0
    · simpa only [hn0, ArithmeticFunction.map_zero] using hlog
    · apply ArithmeticFunction.vonMangoldt_le_log.trans
      apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0)
      exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hx0)
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · rfl
  · by_cases hr : a % q ∈ Finset.Icc 0 ⌊x⌋₊
    · rw [Finset.sum_eq_single (a % q)]
      · simpa only [Nat.mod_mod, if_true] using hΛ (a % q) hr
      · intro n hn hne
        rw [Nat.mod_eq_of_lt (hnq n hn), if_neg hne]
      · intro hn
        exact (hn hr).elim
    · have hz (n : ℕ) (hn : n ∈ Finset.Icc 0 ⌊x⌋₊) :
          (if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0) = 0 := by
        rw [Nat.mod_eq_of_lt (hnq n hn)]
        apply if_neg
        intro h
        exact hr (h ▸ hn)
      rw [Finset.sum_eq_zero hz]
      exact hlog

theorem large_modulus_main_term (x : ℝ) (q : ℕ)
    (hx : 2 ≤ x) (hq : 1 ≤ q) (hxq : x < (q : ℝ)) :
    0 ≤ x / (Nat.totient q : ℝ) ∧ x / (Nat.totient q : ℝ) ≤ 2 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hφ : 0 < (Nat.totient q : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hq)
  have htot : (q : ℝ) ≤ 2 * (Nat.totient q : ℝ) ^ 2 := by
    exact_mod_cast (totient_square_lower q).1
  have hmain0 : 0 ≤ x / (Nat.totient q : ℝ) := div_nonneg hx0 hφ.le
  refine ⟨hmain0, ?_⟩
  have hsq : (x / (Nat.totient q : ℝ)) ^ 2 ≤ 2 * x := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hφ)).mpr
    have hh := mul_le_mul_of_nonneg_left (hxq.le.trans htot) hx0
    nlinarith only [hh]
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  calc
    _ = Real.sqrt ((x / (Nat.totient q : ℝ)) ^ 2) := (Real.sqrt_sq hmain0).symm
    _ ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    _ ≤ 2 * Real.sqrt x := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)

theorem large_error_absorbed (x : ℝ) (hx : 2 ≤ x) :
    Real.log x + 2 * Real.sqrt x ≤
      (1 / Real.log 2 + 2 / (Real.log 2) ^ 2) *
        x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := by
  let l := Real.log 2
  let X := x ^ ((11 : ℝ) / 12)
  have hl : 0 < l := Real.log_pos (by norm_num)
  have hL : l ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hL0 : 0 ≤ Real.log x := hl.le.trans hL
  have hX0 : 0 ≤ X := Real.rpow_nonneg (by linarith) _
  have hX1 : 1 ≤ X := Real.one_le_rpow (by linarith) (by norm_num)
  have hsqrt : Real.sqrt x ≤ X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlogBound : Real.log x ≤ X * (Real.log x) ^ 2 / l := by
    apply (le_div_iff₀ hl).mpr
    calc
      _ ≤ (Real.log x) ^ 2 := by nlinarith
      _ ≤ X * (Real.log x) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hX1
  have hsquare : l ^ 2 ≤ (Real.log x) ^ 2 := by nlinarith
  have hsqrtBound : Real.sqrt x ≤ X * (Real.log x) ^ 2 / l ^ 2 := by
    apply hsqrt.trans
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    exact mul_le_mul_of_nonneg_left hsquare hX0
  calc
    _ ≤ X * (Real.log x) ^ 2 / l + 2 * (X * (Real.log x) ^ 2 / l ^ 2) := by gcongr
    _ = _ := by dsimp only [X, l]; ring

theorem large_modulus_psi_literal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (q a : ℕ),
      2 ≤ x → 1 ≤ q → x < (q : ℝ) →
        |(∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0) -
          x / (Nat.totient q : ℝ)| ≤
            C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := by
  refine ⟨1 / Real.log 2 + 2 / (Real.log 2) ^ 2, by positivity, ?_⟩
  intro x q a hx hq hxq
  obtain ⟨hpsi0, hpsi⟩ := mangoldt_progression_large_bounds x q a hx hxq
  obtain ⟨hmain0, hmain⟩ := large_modulus_main_term x q hx hq hxq
  calc
    _ ≤ |∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0| +
        |x / (Nat.totient q : ℝ)| := abs_sub _ _
    _ = (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0) +
        x / (Nat.totient q : ℝ) := by rw [abs_of_nonneg hpsi0, abs_of_nonneg hmain0]
    _ ≤ Real.log x + 2 * Real.sqrt x := add_le_add hpsi hmain
    _ ≤ _ := large_error_absorbed x hx


end QRHShort.CloudBatch.PrimeAPLargeHelpers

namespace QRHShort.CloudBatch

theorem character_orthogonality_step_proved :
    PrimeAP.CharacterOrthogonalityStep := by
  rintro ⟨C, hC, h⟩
  refine ⟨C, hC, ?_⟩
  intro x q a hx hq hqx ha
  letI : NeZero q := ⟨by omega⟩
  apply PrimesAPAux.mangoldt_residue_error_le a ha (Icc 0 ⌊x⌋₊) x
    (C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2)
  intro χ
  exact h q χ x hx hqx

theorem large_modulus_psi_estimate_proved :
    PrimeAP.LargeModulusPsiEstimate := by
  obtain ⟨C, hC, h⟩ := PrimeAPLargeHelpers.large_modulus_psi_literal
  refine ⟨C, hC, ?_⟩
  intro x q a hx hq hxq _ha
  exact h x q a hx hq hxq

theorem partial_summation_step_proved : PrimeAP.PartialSummationStep := by
  rintro ⟨C, hC, h⟩
  refine ⟨C + (12 / 11 : ℝ) * C / Real.log 2 + 2 / (Real.log 2) ^ 2,
    by positivity, ?_⟩
  intro x q a hx hq _hqx ha
  have hφ : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.totient_pos.mpr (by omega : 0 < q)))
  apply PrimesAPAux.finite_prefix_abel_transfer
    (fun n : ℕ => if Nat.Prime n ∧ n % q = a % q then Real.log n else 0)
    (Nat.totient q : ℝ)⁻¹ C x (primeAPCount x q a : ℝ)
    (by positivity) (inv_le_one_of_one_le₀ hφ) hC hx
  · intro t ht
    simpa only [PrimeAP.theta, div_eq_mul_inv, mul_comm] using h t q a ht.1 hq ha
  · exact PrimeAP.prime_count_partial_summation x q a hx

/-- Conditional localization of the sole remaining analytic obligation.
This is deliberately not the required `primes_ap_step_proved` endpoint. -/
theorem primes_ap_of_zeroFreeTwisted
    (hz : PrimeAP.ZeroFreeTwistedStep) : MainStatement → PrimeAPStatement :=
  PrimeAP.primes_ap_step_of_children hz character_orthogonality_step_proved
    large_modulus_psi_estimate_proved partial_summation_step_proved

end QRHShort.CloudBatch

namespace QRHShort.CloudBatch.PrimesAPAux

/-- The literal imprimitive twist differs from its primitive character only
at prime powers whose base divides the original level. This estimate uses the
actual inclusive Mangoldt sums, including the term at zero. -/
theorem norm_twistedPsi_sub_primitive_le_bad
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖PrimeAP.twistedPsi χ x - PrimeAP.twistedPsi χ.primitiveCharacter x‖ ≤
      ∑ n ∈ Icc 0 ⌊x⌋₊,
        if ¬Nat.Coprime n q then ArithmeticFunction.vonMangoldt n else 0 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  unfold PrimeAP.twistedPsi
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  by_cases hn : Nat.Coprime n q
  · have he : χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod q) := by
      simpa only [Int.cast_natCast] using
        χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
    rw [if_neg (not_not.mpr hn)]
    simp only [he, sub_self, norm_zero, le_refl]
  · have hz : χ (n : ZMod q) = 0 := by
      simpa only [Int.cast_natCast] using
        (χ.apply_eq_zero_iff (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hn)
    simp only [hz, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)),
      hn, not_false_eq_true, ite_true]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (χ.primitiveCharacter.norm_le_one _)

end QRHShort.CloudBatch.PrimesAPAux

namespace QRHShort.CloudBatch.PrimeAPImprimitiveWeight

theorem bad_prime_power_dvd (N q n : ℕ) (hnN : n ≤ N)
    (hn : IsPrimePow n) (hbad : ¬ Nat.Coprime n q) :
    n ∣ q ^ Nat.log 2 N := by
  obtain ⟨k, hk, hk0, p, _hpn, hnp, hp⟩ := (isPrimePow_nat_iff_bounded_log n).mp hn
  have hpq : p ∣ q := by
    by_contra hh
    have hc : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hh
    apply hbad
    simpa only [hnp] using hc.pow_left k
  rw [hnp]
  exact (pow_dvd_pow_of_dvd hpq k).trans
    (pow_dvd_pow q (hk.trans (Nat.log_mono_right hnN)))

theorem bad_mangoldt_sum_le_natLog (N q : ℕ) (hq : 1 ≤ q) :
    (∑ n ∈ Finset.Icc 0 N,
      if ¬ Nat.Coprime n q then ArithmeticFunction.vonMangoldt n else 0) ≤
      (Nat.log 2 N : ℝ) * Real.log q := by
  let S := (Finset.Icc 0 N).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n)
  have heq : (∑ n ∈ Finset.Icc 0 N,
      if ¬ Nat.Coprime n q then ArithmeticFunction.vonMangoldt n else 0) =
      ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hbad : ¬ Nat.Coprime n q
    · by_cases hpow : IsPrimePow n
      · simp [hbad, hpow]
      · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
        simp [hbad, hpow, hz]
    · simp [hbad]
  have hsub : S ⊆ (q ^ Nat.log 2 N).divisors := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hbad, hpow⟩
    exact Nat.mem_divisors.mpr
      ⟨bad_prime_power_dvd N q n (Finset.mem_Icc.mp hnI).2 hpow hbad,
        pow_ne_zero _ (Nat.ne_of_gt hq)⟩
  rw [heq]
  calc
    _ ≤ ∑ n ∈ (q ^ Nat.log 2 N).divisors, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = _ := by
      rw [ArithmeticFunction.vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

theorem natLog_floor_mul_log_two_le (x : ℝ) (hx : 2 ≤ x) :
    (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 ≤ Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hfpos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnlog := Real.natLog_le_logb ⌊x⌋₊ 2
  rw [Real.logb] at hnlog
  have hK := (le_div_iff₀ hlog2).mp hnlog
  exact hK.trans (Real.log_le_log (by exact_mod_cast hfpos) (Nat.floor_le hx0))

theorem bad_mangoldt_sum_le_log_mul_log (x : ℝ) (q : ℕ)
    (hx : 2 ≤ x) (hq : 1 ≤ q) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
      if ¬ Nat.Coprime n q then ArithmeticFunction.vonMangoldt n else 0) ≤
      (Real.log q / Real.log 2) * Real.log x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : (Nat.log 2 ⌊x⌋₊ : ℝ) ≤ Real.log x / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (natLog_floor_mul_log_two_le x hx)
  calc
    _ ≤ (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := bad_mangoldt_sum_le_natLog _ q hq
    _ ≤ (Real.log x / Real.log 2) * Real.log q :=
      mul_le_mul_of_nonneg_right hK (Real.log_natCast_nonneg q)
    _ = _ := by ring

end QRHShort.CloudBatch.PrimeAPImprimitiveWeight


namespace QRHShort.CloudBatch.PrimesAPAux

/-- Removing all imprimitive Euler factors costs at most two logarithms,
with a constant independent of the character and its conductor. -/
theorem norm_twistedPsi_sub_primitive_le_log
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (hx : 2 ≤ x) :
    ‖PrimeAP.twistedPsi χ x - PrimeAP.twistedPsi χ.primitiveCharacter x‖ ≤
      (Real.log q / Real.log 2) * Real.log x :=
  (norm_twistedPsi_sub_primitive_le_bad χ x).trans
    (PrimeAPImprimitiveWeight.bad_mangoldt_sum_le_log_mul_log x q hx
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))

/-- The original uniform twisted estimate is equivalent to its restriction
to primitive characters. The reverse direction proves the missing Euler-factor
error estimate, with the explicit uniform increase `1 / log 2`. -/
theorem twistedMangoldtEstimate_iff_primitive :
    PrimeAP.TwistedMangoldtEstimate ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
        ∀ x : ℝ, 2 ≤ x → (q : ℝ) ≤ x →
          ‖PrimeAP.twistedPsi χ x - if χ = 1 then (x : ℂ) else 0‖ ≤
            C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := by
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun q _ χ _ x hx hqx => h q χ x hx hqx⟩
  · rintro ⟨C, hC, h⟩
    refine ⟨C + (Real.log 2)⁻¹, add_nonneg hC (by positivity), ?_⟩
    intro q _ χ x hx hqx
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hlevel : (χ.conductor : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    have hprim := h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      x hx (hlevel.trans hqx)
    have hone : χ.primitiveCharacter = 1 ↔ χ = 1 := by
      simpa only [χ.changeLevel_primitiveCharacter] using
        (DirichletCharacter.changeLevel_eq_one_iff
          (χ := χ.primitiveCharacter) χ.conductor_dvd_level).symm
    simp only [hone] at hprim
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlogq : Real.log q ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast NeZero.pos q) hqx
    have hp : 1 ≤ x ^ ((11 : ℝ) / 12) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have herror :
        ‖PrimeAP.twistedPsi χ x - PrimeAP.twistedPsi χ.primitiveCharacter x‖ ≤
          (Real.log 2)⁻¹ * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := by
      calc
        _ ≤ (Real.log q / Real.log 2) * Real.log x :=
          norm_twistedPsi_sub_primitive_le_log χ x hx
        _ ≤ (Real.log x / Real.log 2) * Real.log x :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlogq hlog2.le) hlogx
        _ = (Real.log 2)⁻¹ * (Real.log x) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (inv_nonneg.mpr hlog2.le) hp) (sq_nonneg _)
    calc
      _ = ‖(PrimeAP.twistedPsi χ x - PrimeAP.twistedPsi χ.primitiveCharacter x) +
          (PrimeAP.twistedPsi χ.primitiveCharacter x - if χ = 1 then (x : ℂ) else 0)‖ := by
            congr 1
            abel
      _ ≤ ‖PrimeAP.twistedPsi χ x - PrimeAP.twistedPsi χ.primitiveCharacter x‖ +
          ‖PrimeAP.twistedPsi χ.primitiveCharacter x - if χ = 1 then (x : ℂ) else 0‖ :=
        norm_add_le _ _
      _ ≤ (Real.log 2)⁻¹ * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 +
          C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := add_le_add herror hprim
      _ = _ := by ring

end QRHShort.CloudBatch.PrimesAPAux

open Filter Set Asymptotics Complex
open scoped Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem finEquiv_apply {q : ℕ} [NeZero q] (i : Fin q) :
    ZMod.finEquiv q i = (i.val : ZMod q) := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    apply Fin.ext
    change i.val = i.val % (q + 1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

theorem complete_shifted_sum_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q)) = 0 := by
  let e : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv.trans (Equiv.addRight 1)
  have heq : (∑ i : Fin q, χ ((i.val + 1 : ℕ) : ZMod q)) = ∑ z : ZMod q, χ z := by
    apply Fintype.sum_equiv e _ _
    intro i
    simp only [Nat.cast_add, Nat.cast_one]
    change χ ((i.val : ZMod q) + 1) = χ (ZMod.finEquiv q i + 1)
    rw [finEquiv_apply]
  calc
    _ = ∑ i : Fin q, χ ((i.val + 1 : ℕ) : ZMod q) :=
      (Fin.sum_univ_eq_sum_range (fun n : ℕ => χ ((n + 1 : ℕ) : ZMod q)) q).symm
    _ = _ := heq.trans (χ.sum_eq_zero_of_ne_one hχ)

theorem sum_Icc_eq_shifted_range {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)) =
      ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) := by
  symm
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro a ha b hb hab
    omega
  · intro n hn
    have hnI := Finset.mem_Icc.mp hn
    refine ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n hn
    rfl

theorem prefix_sum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  let f : ℕ → ℂ := fun n => χ ((n + 1 : ℕ) : ZMod q)
  have hperiod (m n : ℕ) : f (q * m + n) = f n := by
    simp only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self,
      zero_mul, zero_add]
  have hblocks (m : ℕ) : (∑ n ∈ Finset.range (q * m), f n) = 0 := by
    induction m with
    | zero => simp
    | succ m hm =>
      rw [Nat.mul_succ, Finset.sum_range_add, hm]
      simp only [zero_add, hperiod]
      exact complete_shifted_sum_zero χ hχ
  have hN : N = q * (N / q) + N % q := (Nat.div_add_mod N q).symm
  have hrem : (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range (N % q), f n := by
    conv_lhs => rw [hN]
    rw [Finset.sum_range_add, hblocks]
    simp only [zero_add, hperiod]
  rw [sum_Icc_eq_shifted_range χ N]
  change ‖∑ n ∈ Finset.range N, f n‖ ≤ _
  rw [hrem]
  calc
    _ ≤ ∑ n ∈ Finset.range (N % q), ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range (N % q), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact χ.norm_le_one _
    _ = ((N % q : ℕ) : ℝ) := by simp
    _ ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le

def characterPrefixCutoff {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  if 1 < t then ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ (n : ZMod q) else 0

theorem prefixCutoff_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Measurable (characterPrefixCutoff χ) := by
  have hsum : Measurable (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ (n : ZMod q)) :=
    (measurable_of_countable (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q))).comp
      Nat.measurable_floor
  exact Measurable.ite measurableSet_Ioi hsum measurable_const

theorem prefixCutoff_eq_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : t ≤ 1) : characterPrefixCutoff χ t = 0 := if_neg (not_lt.mpr ht)

theorem prefixCutoff_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖characterPrefixCutoff χ t‖ ≤ (q : ℝ) := by
  unfold characterPrefixCutoff
  split_ifs
  · exact prefix_sum_norm_le χ hχ _
  · simpa only [norm_zero] using (Nat.cast_nonneg q : (0 : ℝ) ≤ q)

theorem prefixCutoff_locallyIntegrableOn {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    LocallyIntegrableOn (characterPrefixCutoff χ) (Set.Ioi (0 : ℝ)) := by
  apply (locallyIntegrableOn_const (s := Set.Ioi (0 : ℝ)) (q : ℂ)).mono
    (prefixCutoff_measurable χ).aestronglyMeasurable
  filter_upwards [] with t
  calc
    ‖characterPrefixCutoff χ t‖ ≤ (q : ℝ) := prefixCutoff_norm_le χ hχ t
    _ = ‖(q : ℂ)‖ := by simp

end QRHShort.CloudBatch.PrimesAPGrowthAux


namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem cutoff_mellin_eq_integral (f : ℝ → ℂ)
    (hfzero : ∀ t ≤ 1, f t = 0) (s : ℂ) :
    mellin f (-s) = ∫ t in Ioi (1 : ℝ), f t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (s := Ioi (1 : ℝ)) measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [show -s - 1 = -(s + 1) by ring, mul_comm]
  · intro t ht
    rw [hfzero t (le_of_not_gt ht.2), mul_zero]

theorem bounded_cutoff_mellin_data (f : ℝ → ℂ) (C : ℝ)
    (hfc : LocallyIntegrableOn f (Ioi (0 : ℝ)))
    (hfbound : ∀ t, ‖f t‖ ≤ C) (hfzero : ∀ t ≤ 1, f t = 0)
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent f (-s) ∧
      DifferentiableAt ℂ (fun z : ℂ => mellin f (-z)) s := by
  have htop : f =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound C
    exact Eventually.of_forall fun t => by simpa using hfbound t
  have hbot : f =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-(-s.re - 1))) := by
    apply IsBigO.of_bound 0
    have ht : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [ht] with t ht
    simp only [hfzero t ht.le, norm_zero, zero_mul, le_refl]
  have hst : (-s).re < 0 := by simpa only [neg_re] using neg_neg_of_pos hs
  have hsb : -s.re - 1 < (-s).re := by simp only [neg_re]; linarith
  refine ⟨mellinConvergent_of_isBigO_rpow hfc htop hst hbot hsb, ?_⟩
  exact (mellin_differentiableAt_of_isBigO_rpow hfc htop hst hbot hsb).comp s
    differentiableAt_id.neg

theorem norm_bounded_cutoff_mellin_le (f : ℝ → ℂ) (C : ℝ)
    (hfc : LocallyIntegrableOn f (Ioi (0 : ℝ)))
    (hfbound : ∀ t, ‖f t‖ ≤ C) (hfzero : ∀ t ≤ 1, f t = 0)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin f (-s)‖ ≤ C / s.re := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hfbound 0)
  have hconv := (bounded_cutoff_mellin_data f C hfc hfbound hfzero hs).1
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • f t) (Ioi (0 : ℝ)) at hconv
  have hi : IntegrableOn (fun t : ℝ => f t * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    have hmono := hconv.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    convert hmono using 1
    ext t
    simp only [smul_eq_mul]
    rw [show -s - 1 = -(s + 1) by ring, mul_comm]
  have hipow : IntegrableOn (fun t : ℝ => C * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one).const_mul C
  rw [cutoff_mellin_eq_integral f hfzero s]
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), ‖f t * (t : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1 : ℝ), C * t ^ (-s.re - 1) := by
      apply integral_mono_ae hi.norm hipow
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
      simp only [neg_re, add_re, one_re]
      convert mul_le_mul_of_nonneg_right (hfbound t)
        (Real.rpow_nonneg (zero_lt_one.trans ht).le (-s.re - 1)) using 1 <;> ring_nf
    _ = C / s.re := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one]
      simp only [Real.one_rpow]
      field_simp [hs.ne']
      ring

end QRHShort.CloudBatch.PrimesAPGrowthAux


namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- On its original half-plane the actual Dirichlet L-function equals the
Mellin transform of the bounded, nonprincipal character prefix. -/
theorem LFunction_eq_prefix_mellin_of_one_lt
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = s * mellin (characterPrefixCutoff χ) (-s) := by
  have hO : (fun N : ℕ => ∑ n ∈ Icc 1 N, χ n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (0 : ℝ)) := by
    apply IsBigO.of_bound (q : ℝ)
    exact Eventually.of_forall fun N => by simpa using prefix_sum_norm_le χ hχ N
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    LSeries_eq_mul_integral (fun n : ℕ => χ n) (r := 0) (by norm_num) (by linarith)
      (χ.LSeriesSummable_of_one_lt_re hs) hO,
    cutoff_mellin_eq_integral (characterPrefixCutoff χ)
      (fun t ht => prefixCutoff_eq_zero χ ht) s]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only [characterPrefixCutoff]
  change 1 < t at ht
  rw [if_pos ht]

/-- Analytic continuation of the actual bounded-prefix integral extends its
literal equality with `LFunction` throughout `Re s > 0`. -/
theorem LFunction_eq_prefix_mellin
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * mellin (characterPrefixCutoff χ) (-s) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 0 < z.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hopen
  have hM : AnalyticOnNhd ℂ
      (fun z : ℂ => z * mellin (characterPrefixCutoff χ) (-z)) {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    exact (differentiableAt_id.mul
      (bounded_cutoff_mellin_data (characterPrefixCutoff χ) (q : ℝ)
        (prefixCutoff_locallyIntegrableOn χ hχ) (prefixCutoff_norm_le χ hχ)
        (fun t ht => prefixCutoff_eq_zero χ ht) hz).2).differentiableWithinAt
  have heq : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z * mellin (characterPrefixCutoff χ) (-z)) := by
    have hnb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnb] with z hz
    exact LFunction_eq_prefix_mellin_of_one_lt χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hM
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re})
    heq hs

/-- A polynomial bound with an explicit uniform dependence on the level and
height, derived from a genuinely convergent integral for the literal L-function. -/
theorem norm_LFunction_le_level_mul_norm_div_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [LFunction_eq_prefix_mellin χ hχ hs, norm_mul]
  calc
    _ ≤ ‖s‖ * ((q : ℝ) / s.re) := mul_le_mul_of_nonneg_left
      (norm_bounded_cutoff_mellin_le (characterPrefixCutoff χ) (q : ℝ)
        (prefixCutoff_locallyIntegrableOn χ hχ) (prefixCutoff_norm_le χ hχ)
        (fun t ht => prefixCutoff_eq_zero χ ht) hs) (norm_nonneg s)
    _ = _ := by ring

end QRHShort.CloudBatch.PrimesAPGrowthAux


namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem inv_square_tail_three_range_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 3) ^ 2) ≤
      1 / 2 - 1 / ((N : ℝ) + 2) := by
  induction N with
  | zero => norm_num
  | succ N hN =>
    have h2 : 0 < (N : ℝ) + 2 := by positivity
    have h3 : 0 < (N : ℝ) + 3 := by positivity
    have hstep : 1 / ((N : ℝ) + 3) ^ 2 ≤
        1 / ((N : ℝ) + 2) - 1 / ((N : ℝ) + 3) := by
      calc
        _ ≤ 1 / (((N : ℝ) + 2) * ((N : ℝ) + 3)) :=
          one_div_le_one_div_of_le (mul_pos h2 h3) (by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
        _ = _ := by field_simp [h2.ne', h3.ne'] <;> ring
    rw [Finset.sum_range_succ]
    push_cast
    rw [show (N : ℝ) + 1 + 2 = (N : ℝ) + 3 by ring]
    linarith

theorem inv_square_tail_two_range_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 2) ^ 2) ≤ (3 / 4 : ℝ) := by
  cases N with
  | zero => norm_num
  | succ N =>
    have hsplit : (∑ n ∈ Finset.range (N + 1), 1 / ((n : ℝ) + 2) ^ 2) =
        1 / 4 + ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 3) ^ 2 := by
      rw [Finset.sum_range_succ']
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc] <;> ring
    rw [hsplit]
    have h := inv_square_tail_three_range_le N
    have hpos : 0 ≤ 1 / ((N : ℝ) + 2) := by positivity
    linarith

theorem inv_square_tail_two_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) :=
  summable_of_sum_range_le (fun _ => by positivity) inv_square_tail_two_range_le

theorem inv_square_tail_two_tsum_le :
    (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2) ≤ (3 / 4 : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => by positivity) inv_square_tail_two_range_le

theorem LFunction_re_two_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 2) :
    (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  let f : ℕ → ℂ := fun n => χ (n : ZMod q)
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have hseries : Summable (LSeries.term f s) := χ.LSeriesSummable_of_one_lt_re hs1
  have htail : Summable (fun n : ℕ => LSeries.term f s (n + 2)) :=
    (summable_nat_add_iff 2).mpr hseries
  have hterm (n : ℕ) : ‖LSeries.term f s (n + 2)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    rw [LSeries.norm_term_eq, if_neg (show n + 2 ≠ 0 by omega), hs, Real.rpow_two]
    have hh := div_le_div_of_nonneg_right (χ.norm_le_one ((n + 2 : ℕ) : ZMod q))
      (sq_nonneg ((n + 2 : ℕ) : ℝ))
    simpa only [f, Nat.cast_add, Nat.cast_ofNat] using hh
  have htailnorm : ‖∑' n : ℕ, LSeries.term f s (n + 2)‖ ≤ (3 / 4 : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ, ‖LSeries.term f s (n + 2)‖ := norm_tsum_le_tsum_norm htail.norm
      _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 :=
        Summable.tsum_le_tsum hterm htail.norm inv_square_tail_two_summable
      _ ≤ _ := inv_square_tail_two_tsum_le
  have hinitial : (∑ n ∈ Finset.range 2, LSeries.term f s n) = 1 := by
    norm_num [Finset.sum_range_succ, LSeries.term, f]
  have hsplit : DirichletCharacter.LFunction χ s =
      1 + ∑' n : ℕ, LSeries.term f s (n + 2) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
    change (∑' n : ℕ, LSeries.term f s n) = _
    have hh := hseries.sum_add_tsum_nat_add 2
    rw [hinitial] at hh
    exact hh.symm
  have hreverse : 1 ≤ ‖DirichletCharacter.LFunction χ s‖ +
      ‖∑' n : ℕ, LSeries.term f s (n + 2)‖ := by
    rw [hsplit]
    simpa only [add_sub_cancel_right, norm_one] using
      norm_sub_le (1 + ∑' n : ℕ, LSeries.term f s (n + 2))
        (∑' n : ℕ, LSeries.term f s (n + 2))
  linarith

theorem LFunction_center_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (1 / 4 : ℝ) ≤
      ‖DirichletCharacter.LFunction χ ((2 : ℂ) + (T : ℂ) * Complex.I)‖ := by
  apply LFunction_re_two_lower χ
  simp

end QRHShort.CloudBatch.PrimesAPGrowthAux


namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- A uniform Jensen bound for the actual nonprincipal Dirichlet L-function.
The inner ball covers the half-critical strip in a fixed height window. -/
theorem LFunction_local_zero_count_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    (((∑ᶠ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (Metric.closedBall (2 + (T : ℂ) * Complex.I) (7 / 4)) u) : ℤ) : ℝ) ≤
      Real.log (32 * (q : ℝ) * (|T| + 4)) / Real.log (15 / 14) := by
  let c : ℂ := 2 + (T : ℂ) * Complex.I
  let M : ℝ := 8 * (q : ℝ) * (|T| + 4)
  have hc : c.re = 2 := by simp [c]
  have hc_norm : ‖c‖ ≤ |T| + 2 := by
    calc
      _ ≤ ‖(2 : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]; ring
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos q)
  have hM : 1 ≤ M := by
    have hm := mul_le_mul hq
      (show (4 : ℝ) ≤ |T| + 4 by linarith [abs_nonneg T])
      (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg q)
    dsimp only [M]
    nlinarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hbound : ∀ z ∈ Metric.sphere c |(15 / 8 : ℝ)|,
      ‖DirichletCharacter.LFunction χ z‖ ≤ M := by
    intro z hz
    have hd : ‖z - c‖ = (15 / 8 : ℝ) := by
      simpa only [Metric.mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 15 / 8)] using hz
    have hrez : (1 / 8 : ℝ) ≤ z.re := by
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hc, hd] at hre
      linarith [neg_le_abs (z.re - 2)]
    have hnz : ‖z‖ ≤ |T| + 4 := by
      calc
        _ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add z c
        _ ≤ (15 / 8 : ℝ) + (|T| + 2) := by rw [hd]; gcongr
        _ ≤ _ := by linarith
    calc
      _ ≤ (q : ℝ) * ‖z‖ / z.re :=
        norm_LFunction_le_level_mul_norm_div_re χ hχ (by linarith)
      _ ≤ (q : ℝ) * (|T| + 4) / (1 / 8) := by gcongr
      _ = M := by dsimp only [M]; ring
  have hcenter : (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ c‖ := by
    exact LFunction_center_lower χ T
  have hnorm : 0 < ‖DirichletCharacter.LFunction χ c‖ := lt_of_lt_of_le (by norm_num) hcenter
  have hne : DirichletCharacter.LFunction χ c ≠ 0 := norm_pos_iff.mp hnorm
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (Metric.closedBall c |(15 / 8 : ℝ)|) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hj := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := (7 / 4 : ℝ)) (R := (15 / 8 : ℝ)) (M := M)
    (by norm_num) (by norm_num) hM ha hne hbound
  have hratio : M / ‖DirichletCharacter.LFunction χ c‖ ≤ 4 * M := by
    calc
      _ ≤ M / (1 / 4) := by gcongr
      _ = _ := by ring
  have hlog : Real.log (M / ‖DirichletCharacter.LFunction χ c‖) ≤
      Real.log (32 * (q : ℝ) * (|T| + 4)) := by
    have hh := Real.log_le_log (div_pos (by linarith : 0 < M) hnorm) hratio
    convert hh using 1 <;> dsimp only [M] <;> congr 1 <;> ring
  have hlogratio : 0 ≤ Real.log (15 / 14 : ℝ) := Real.log_nonneg (by norm_num)
  have hr : (15 / 8 : ℝ) / (7 / 4) = 15 / 14 := by norm_num
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4), hr] at hj
  exact hj.trans (div_le_div_of_nonneg_right hlog hlogratio)

end QRHShort.CloudBatch.PrimesAPGrowthAux

open Filter Set Asymptotics Complex
open scoped Topology BigOperators


noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Extract exactly the actual divisor in a compact ball from an entire,
nonzero function. The quotient is entire globally and has no zeros in that
ball; the factorization is pointwise, including at the removed zeros. -/
theorem entire_extract_ball_divisor {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) (hfc : f c ≠ 0) (r : ℝ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ z : ℂ, f z =
        (∏ᶠ u : ℂ, (fun w : ℂ => w - u) ^
          (MeromorphicOn.divisor f (closedBall c r) u)) z * g z) ∧
      ∀ z ∈ closedBall c r, g z ≠ 0 := by
  let D := MeromorphicOn.divisor f (closedBall c r)
  let P : ℂ → ℂ := ∏ᶠ u : ℂ, (fun w : ℂ => w - u) ^ D u
  let g : ℂ → ℂ := toMeromorphicNFOn (P⁻¹ * f) univ
  have hfa (z : ℂ) : AnalyticAt ℂ f z := hf.analyticAt z
  have hfm : MeromorphicOn f (univ : Set ℂ) := fun z _ => (hfa z).meromorphicAt
  have hfac : AnalyticOnNhd ℂ f (closedBall c r) := fun z _ => hfa z
  have hfcorder : meromorphicOrderAt f c = 0 :=
    (hfa c).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfc
  have hfinite (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ :=
    hfm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ c) (mem_univ z) (by rw [hfcorder]; exact WithTop.zero_ne_top)
  have hDfinite : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall c r)
  have hDnonneg (z : ℂ) : 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfac z
  have hPa (z : ℂ) : AnalyticAt ℂ P z :=
    Function.FactorizedRational.analyticAt (hDnonneg z)
  have hPm : MeromorphicOn P (univ : Set ℂ) := fun z _ => (hPa z).meromorphicAt
  have hratio : MeromorphicOn (P⁻¹ * f) (univ : Set ℂ) := hPm.inv.mul hfm
  have hgnf : MeromorphicNFOn g (univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hDorder (z : ℂ) (hz : z ∈ closedBall c r) :
      (D z : WithTop ℤ) = meromorphicOrderAt f z := by
    dsimp only [D]
    rw [hfac.meromorphicOn.divisor_apply hz,
      WithTop.coe_untop₀_of_ne_top (hfinite z)]
  have hgorder (z : ℂ) :
      meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z := by
    change meromorphicOrderAt (toMeromorphicNFOn (P⁻¹ * f) univ) z = _
    rw [meromorphicOrderAt_toMeromorphicNFOn hratio (mem_univ z),
      meromorphicOrderAt_mul (hPm z (mem_univ z)).inv (hfm z (mem_univ z)),
      meromorphicOrderAt_inv,
      Function.FactorizedRational.meromorphicOrderAt_eq (D : ℂ → ℤ) hDfinite]
  have hgorderzero (z : ℂ) (hz : z ∈ closedBall c r) : meromorphicOrderAt g z = 0 := by
    rw [hgorder z, ← hDorder z hz,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    simp
  have hga (z : ℂ) : AnalyticAt ℂ g z := by
    apply (hgnf (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_cases hz : z ∈ closedBall c r
    · exact le_of_eq (hgorderzero z hz).symm
    · have hdz : D z = 0 := D.apply_eq_zero_of_notMem hz
      rw [hgorder z, hdz]
      simpa only [WithTop.coe_zero, neg_zero, zero_add] using (hfa z).meromorphicOrderAt_nonneg
  refine ⟨g, fun z => (hga z).differentiableAt, ?_, ?_⟩
  · intro z
    have hPfinite : meromorphicOrderAt P z ≠ ⊤ :=
      Function.FactorizedRational.meromorphicOrderAt_ne_top (D : ℂ → ℤ)
    have hPnz : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hPm z (mem_univ z))).mp hPfinite
    have hgn : g =ᶠ[𝓝[≠] z] P⁻¹ * f :=
      hratio.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
    have heq : (fun w : ℂ => P w * g w) =ᶠ[𝓝[≠] z] f := by
      filter_upwards [hgn, hPnz] with w hw hn
      rw [hw]
      simp only [Pi.mul_apply, Pi.inv_apply, mul_inv_cancel_left₀ hn]
    have hlim₁ : Tendsto (fun w : ℂ => P w * g w) (𝓝[≠] z) (𝓝 (P z * g z)) :=
      ((hPa z).continuousAt.mul (hga z).continuousAt).mono_left nhdsWithin_le_nhds
    have hlim₂ : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hf z).continuousAt.mono_left nhdsWithin_le_nhds
    exact (tendsto_nhds_unique hlim₁ (hlim₂.congr' heq.symm)).symm
  · intro z hz
    exact (hgnf (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp (hgorderzero z hz)

end QRHShort.CloudBatch.PrimesAPGrowthAux



noncomputable section
open Classical Function
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem factorMultiplicitySum_eq_sum {d : ℂ → ℤ} (hd : d.HasFiniteSupport) :
    (∑ᶠ u, d u) = ∑ u ∈ hd.toFinset, d u := by
  apply finsum_eq_sum_of_support_subset
  intro u hu
  exact hd.mem_toFinset.mpr hu

theorem factorMultiplicitySum_nonneg {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hnonneg : ∀ u, 0 ≤ d u) : 0 ≤ ∑ᶠ u, d u := by
  rw [factorMultiplicitySum_eq_sum hd]
  exact Finset.sum_nonneg (fun u _ => hnonneg u)

theorem product_zpow_eq_zpow_sum (s : Finset ℂ) (d : ℂ → ℤ)
    {a : ℝ} (ha : a ≠ 0) :
    (∏ u ∈ s, a ^ d u) = a ^ (∑ u ∈ s, d u) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert u s hu hs =>
    rw [Finset.prod_insert hu, Finset.sum_insert hu, hs, zpow_add₀ ha]

theorem factorizedProduct_norm_eq_prod {d : ℂ → ℤ} (hd : d.HasFiniteSupport) (z : ℂ) :
    ‖(∏ᶠ u, (fun w : ℂ => w - u) ^ d u) z‖ =
      ∏ u ∈ hd.toFinset, ‖z - u‖ ^ d u := by
  rw [Function.FactorizedRational.finprod_eq_fun hd]
  change ‖∏ᶠ u, (z-u) ^ d u‖ = _
  have hsub : (fun u : ℂ => (z-u) ^ d u).mulSupport ⊆ hd.toFinset := by
    intro u hu
    apply hd.mem_toFinset.mpr
    change d u ≠ 0
    intro hz
    exact hu (by change (z-u) ^ d u = 1; rw [hz, zpow_zero])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, norm_prod]
  simp only [norm_zpow]

theorem factorizedProduct_center_norm_le {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hnonneg : ∀ u, 0 ≤ d u) {c : ℂ} {r : ℝ}
    (hsupp : d.support ⊆ Metric.closedBall c r) (hr : 0 < r) :
    ‖(∏ᶠ u, (fun w : ℂ => w - u) ^ d u) c‖ ≤ r ^ (∑ᶠ u, d u) := by
  rw [factorizedProduct_norm_eq_prod hd, factorMultiplicitySum_eq_sum hd]
  calc
    _ ≤ ∏ u ∈ hd.toFinset, r ^ d u := by
      apply Finset.prod_le_prod₀
      · intro u hu
        exact zpow_nonneg (norm_nonneg _) _
      · intro u hu
        have huc : dist u c ≤ r := Metric.mem_closedBall.mp (hsupp (hd.mem_toFinset.mp hu))
        have hnorm : ‖c-u‖ ≤ r := by
          calc
            _ = dist u c := by rw [dist_eq_norm, norm_sub_rev]
            _ ≤ _ := huc
        exact zpow_le_zpow_left₀ (hnonneg u) (norm_nonneg _) hnorm
    _ = _ := product_zpow_eq_zpow_sum hd.toFinset d hr.ne'

theorem factorizedProduct_circle_norm_ge {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hnonneg : ∀ u, 0 ≤ d u) {c z : ℂ} {r R : ℝ}
    (hsupp : d.support ⊆ Metric.closedBall c r) (_hr : 0 < r)
    (hR : r < R) (hz : dist z c = R) :
    (R-r) ^ (∑ᶠ u, d u) ≤ ‖(∏ᶠ u, (fun w : ℂ => w-u) ^ d u) z‖ := by
  rw [factorizedProduct_norm_eq_prod hd, factorMultiplicitySum_eq_sum hd]
  calc
    _ = ∏ u ∈ hd.toFinset, (R-r) ^ d u :=
      (product_zpow_eq_zpow_sum hd.toFinset d (sub_pos.mpr hR).ne').symm
    _ ≤ ∏ u ∈ hd.toFinset, ‖z-u‖ ^ d u := by
      apply Finset.prod_le_prod₀
      · intro u hu
        exact zpow_nonneg (sub_pos.mpr hR).le _
      · intro u hu
        have huc : dist u c ≤ r := Metric.mem_closedBall.mp (hsupp (hd.mem_toFinset.mp hu))
        have hnormDist : R-r ≤ dist z u := by
          have htri := dist_triangle z u c
          rw [hz] at htri
          linarith
        have hnorm : R-r ≤ ‖z-u‖ := by
          simpa only [dist_eq_norm] using hnormDist
        exact zpow_le_zpow_left₀ (hnonneg u) (sub_pos.mpr hR).le hnorm

end QRHShort.CloudBatch.PrimesAPGrowthAux



noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- An actual normalized analytic logarithm on a zero-free disk, constructed
from a primitive of the literal logarithmic derivative. -/
theorem exists_normalized_log_on_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (ball c r))
    (hn : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ H : ℂ → ℂ, H c = 0 ∧
      (∀ z ∈ ball c r, HasDerivAt H (logDeriv g z) z) ∧
      (∀ z ∈ ball c r, Complex.exp (H z) = g z / g c) ∧
      ∀ z ∈ ball c r,
        (H z).re = Real.log ‖g z‖ - Real.log ‖g c‖ := by
  have hld : DifferentiableOn ℂ (logDeriv g) (ball c r) :=
    (hg.deriv isOpen_ball).div hg hn
  obtain ⟨H, hHc, hH⟩ := hld.isExactOn_ball.with_val_at c 0
  have hHd : DifferentiableOn ℂ H (ball c r) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hEd : DifferentiableOn ℂ (fun z => Complex.exp (H z)) (ball c r) :=
    Complex.differentiable_exp.comp_differentiableOn hHd
  have hldeq : EqOn (logDeriv (fun z => Complex.exp (H z))) (logDeriv g) (ball c r) := by
    intro z hz
    have hd : deriv (fun w => Complex.exp (H w)) z =
        Complex.exp (H z) * logDeriv g z := by
      simpa only [Function.comp_def] using
        ((Complex.hasDerivAt_exp (H z)).comp z (hH z hz)).deriv
    rw [logDeriv_apply, hd]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  obtain ⟨k, hk, hkg⟩ :=
    (logDeriv_eqOn_iff hEd hg isOpen_ball (convex_ball c r).isPreconnected hn
      (fun z _ => Complex.exp_ne_zero (H z))).mp hldeq
  have hc : c ∈ ball c r := mem_ball_self hr
  have hkcenter : 1 = k * g c := by
    simpa only [hHc, Complex.exp_zero, Pi.smul_apply, smul_eq_mul] using hkg hc
  have heq (z : ℂ) (hz : z ∈ ball c r) : Complex.exp (H z) = g z / g c := by
    have hz' := hkg hz
    simp only [Pi.smul_apply, smul_eq_mul] at hz'
    rw [hz']
    apply (eq_div_iff (hn c hc)).mpr
    calc
      k * g z * g c = (k * g c) * g z := by ring
      _ = g z := by rw [← hkcenter, one_mul]
  refine ⟨H, hHc, hH, heq, ?_⟩
  intro z hz
  have he := congrArg norm (heq z hz)
  rw [Complex.norm_exp, norm_div] at he
  rw [← Real.log_exp (H z).re, he,
    Real.log_div (norm_ne_zero_iff.mpr (hn z hz)) (norm_ne_zero_iff.mpr (hn c hc))]

/-- A concrete Borel--Carathéodory/Cauchy estimate on nested disks.
The real-part bound is the only size input; it controls the derivative on
the closed inner disk. -/
theorem norm_deriv_le_of_re_le_on_ball {H : ℂ → ℂ} {c : ℂ} {B : ℝ}
    (hB : 0 < B) (hH : DifferentiableOn ℂ H (ball c (7/4)))
    (hHc : H c = 0) (hre : ∀ z ∈ ball c (7/4), (H z).re ≤ B)
    {z : ℂ} (hz : z ∈ closedBall c (5/4)) :
    ‖deriv H z‖ ≤ 96 * B := by
  let J : ℂ → ℂ := fun w => H (c + w)
  have hJ : DifferentiableOn ℂ J (ball 0 (7/4)) := by
    apply hH.comp (by fun_prop)
    intro w hw
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have hJ0 : J 0 = 0 := by simpa [J] using hHc
  have hJre : MapsTo J (ball 0 (7/4)) {w | w.re ≤ B} := by
    intro w hw
    exact hre (c+w) (by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw)
  have hinner (w : ℂ) (hw : w ∈ closedBall c (3/2)) : ‖H w‖ ≤ 12 * B := by
    have hnorm : ‖w-c‖ ≤ 3/2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hw
    have hw' : w-c ∈ ball (0:ℂ) (7/4) := by
      rw [mem_ball_zero_iff]
      linarith
    have hb := Complex.borelCaratheodory_zero hB hJ hJre (by norm_num) hw' hJ0
    have hJw : J (w-c) = H w := by simp [J]
    rw [hJw] at hb
    have hden : 0 < (7/4:ℝ) - ‖w-c‖ := by linarith
    refine hb.trans ((div_le_iff₀ hden).mpr ?_)
    nlinarith [norm_nonneg (w-c)]
  have hsubset : ball z (1/4) ⊆ ball c (7/4) := by
    intro w hw
    have hz' : dist z c ≤ 5/4 := hz
    have hw' : dist w z < 1/4 := hw
    have := dist_triangle w z c
    change dist w c < 7/4
    linarith
  have hmaps : MapsTo H (ball z (1/4)) (closedBall (H z) (24*B)) := by
    intro w hw
    have hz' : dist z c ≤ 5/4 := hz
    have hw' : dist w z < 1/4 := hw
    have hwc : w ∈ closedBall c (3/2) := by
      have := dist_triangle w z c
      change dist w c ≤ 3/2
      linarith
    have hzc : z ∈ closedBall c (3/2) := by
      change dist z c ≤ 3/2
      linarith
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hinner w hwc, hinner z hzc])
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hH.mono hsubset) hmaps (by norm_num)
  convert hd using 1 <;> ring

end QRHShort.CloudBatch.PrimesAPGrowthAux




noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Circle bounds for the original function give bounds for its entire
quotient after extracting a finite divisor. -/
theorem factorized_quotient_norm_bounds {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hnonneg : ∀ u, 0 ≤ d u) {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {c : ℂ} {r R M m : ℝ} (hsupp : d.support ⊆ closedBall c r)
    (hr : 0 < r) (hR : r < R)
    (hfact : ∀ z, f z = (∏ᶠ u, (fun w : ℂ => w-u) ^ d u) z * g z)
    (hcenter : m ≤ ‖f c‖) (hcircle : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    m / r ^ (∑ᶠ u, d u) ≤ ‖g c‖ ∧
      ∀ z ∈ closedBall c R, ‖g z‖ ≤ M / (R-r) ^ (∑ᶠ u, d u) := by
  constructor
  · apply (div_le_iff₀ (zpow_pos hr _)).mpr
    calc
      m ≤ ‖f c‖ := hcenter
      _ = ‖(∏ᶠ u, (fun w : ℂ => w-u) ^ d u) c‖ * ‖g c‖ := by
        rw [hfact c, norm_mul]
      _ ≤ r ^ (∑ᶠ u, d u) * ‖g c‖ :=
        mul_le_mul_of_nonneg_right
          (factorizedProduct_center_norm_le hd hnonneg hsupp hr) (norm_nonneg _)
      _ = ‖g c‖ * r ^ (∑ᶠ u, d u) := mul_comm _ _
  · intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg.diffContOnCl
    · intro w hw
      have hws : w ∈ sphere c R := frontier_ball_subset_sphere hw
      apply (le_div_iff₀ (zpow_pos (sub_pos.mpr hR) _)).mpr
      calc
        ‖g w‖ * (R-r) ^ (∑ᶠ u, d u) ≤
            ‖g w‖ * ‖(∏ᶠ u, (fun v : ℂ => v-u) ^ d u) w‖ :=
          mul_le_mul_of_nonneg_left
            (factorizedProduct_circle_norm_ge hd hnonneg hsupp hr hR (mem_sphere.mp hws))
            (norm_nonneg _)
        _ = ‖f w‖ := by rw [hfact w, norm_mul, mul_comm]
        _ ≤ M := hcircle w hws
    · rw [closure_ball c (lt_trans hr hR).ne']
      exact hz

theorem factorized_quotient_log_norm_le {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hnonneg : ∀ u, 0 ≤ d u) {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {c : ℂ} {r R M m : ℝ} (hsupp : d.support ⊆ closedBall c r)
    (hr : 0 < r) (hR : r < R) (hM : 0 < M) (hm : 0 < m)
    (hfact : ∀ z, f z = (∏ᶠ u, (fun w : ℂ => w-u) ^ d u) z * g z)
    (hcenter : m ≤ ‖f c‖) (hcircle : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall c R) (hgz : g z ≠ 0) :
    Real.log ‖g z‖ - Real.log ‖g c‖ ≤
      Real.log (M/m) + ((∑ᶠ u, d u : ℤ) : ℝ) * Real.log (r/(R-r)) := by
  obtain ⟨hc, hbound⟩ := factorized_quotient_norm_bounds hd hnonneg hg hsupp hr hR
    hfact hcenter hcircle
  have hδ : 0 < R-r := sub_pos.mpr hR
  calc
    _ ≤ Real.log (M / (R-r) ^ (∑ᶠ u, d u)) -
        Real.log (m / r ^ (∑ᶠ u, d u)) :=
      sub_le_sub (Real.log_le_log (norm_pos_iff.mpr hgz) (hbound z hz))
        (Real.log_le_log (div_pos hm (zpow_pos hr _)) hc)
    _ = _ := by
      rw [Real.log_div hM.ne' (zpow_ne_zero _ hδ.ne'),
        Real.log_div hm.ne' (zpow_ne_zero _ hr.ne'),
        Real.log_div hM.ne' hm.ne', Real.log_div hr.ne' hδ.ne',
        Real.log_zpow, Real.log_zpow]
      ring

/-- The zero-free quotient has a logarithmic derivative bounded by the
original circle growth and the number of extracted zeros. -/
theorem factorized_quotient_logDeriv_le {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hnonneg : ∀ u, 0 ≤ d u) {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {c : ℂ} {M m : ℝ} (hsupp : d.support ⊆ closedBall c (7/4))
    (hM : 0 < M) (hm : 0 < m)
    (hfact : ∀ z, f z = (∏ᶠ u, (fun w : ℂ => w-u) ^ d u) z * g z)
    (hcenter : m ≤ ‖f c‖) (hcircle : ∀ z ∈ sphere c (15/8), ‖f z‖ ≤ M)
    (hn : ∀ z ∈ ball c (7/4), g z ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall c (5/4)) :
    ‖logDeriv g z‖ ≤ 96 *
      (Real.log (M/m) + ((∑ᶠ u, d u : ℤ) : ℝ) * Real.log 14 + 1) := by
  let B := Real.log (M/m) + ((∑ᶠ u, d u : ℤ) : ℝ) * Real.log 14
  have hbound (w : ℂ) (hw : w ∈ ball c (7/4)) :
      Real.log ‖g w‖ - Real.log ‖g c‖ ≤ B := by
    have hwR : w ∈ closedBall c (15/8) := by
      have hw' : dist w c < 7/4 := hw
      change dist w c ≤ 15/8
      linarith
    have hb := factorized_quotient_log_norm_le hd hnonneg hg hsupp
      (by norm_num) (by norm_num : (7/4:ℝ) < 15/8) hM hm hfact hcenter hcircle hwR (hn w hw)
    norm_num only [show (7/4:ℝ)/(15/8-7/4) = 14 by norm_num] at hb
    exact hb
  have hB : 0 < B+1 := by
    have := hbound c (mem_ball_self (by norm_num))
    simp only [sub_self] at this
    linarith
  obtain ⟨H, hHc, hHd, hHe, hHre⟩ := exists_normalized_log_on_ball
    (by norm_num : (0:ℝ)<7/4) hg.differentiableOn hn
  have hz' : z ∈ ball c (7/4) := by
    have hz₀ : dist z c ≤ 5/4 := hz
    change dist z c < 7/4
    linarith
  have hD := norm_deriv_le_of_re_le_on_ball hB
    (fun w hw => (hHd w hw).differentiableAt.differentiableWithinAt) hHc
    (fun w hw => by rw [hHre w hw]; exact (hbound w hw).trans (by linarith)) hz
  rw [(hHd z hz').deriv] at hD
  exact hD

end QRHShort.CloudBatch.PrimesAPGrowthAux



noncomputable section
open Classical Function
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem linear_factor_logDeriv (u z : ℂ) :
    logDeriv (fun w : ℂ => w-u) z = 1 / (z-u) := by
  have hd : HasDerivAt (fun w : ℂ => w-u) 1 z := by
    simpa only [id_eq] using (hasDerivAt_id z).sub_const u
  rw [logDeriv_apply, hd.deriv]

theorem factorizedProduct_logDeriv {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    {z : ℂ} (hz : z ∉ d.support) :
    logDeriv (∏ᶠ u, (fun w : ℂ => w-u) ^ d u) z =
      ∑ᶠ u, (d u : ℂ) / (z-u) := by
  have hsub : (fun u : ℂ => (fun w : ℂ => w-u) ^ d u).mulSupport ⊆ hd.toFinset := by
    rw [Function.FactorizedRational.mulSupport]
    intro u hu
    exact hd.mem_toFinset.mpr hu
  have hprod : (∏ᶠ u, (fun w : ℂ => w-u) ^ d u) =
      ∏ u ∈ hd.toFinset, (fun w : ℂ => w-u) ^ d u :=
    finprod_eq_prod_of_mulSupport_subset _ hsub
  have hroot (u : ℂ) (hu : u ∈ hd.toFinset) : z-u ≠ 0 := by
    intro heq
    have hzu := sub_eq_zero.mp heq
    exact hz (hzu.symm ▸ (hd.mem_toFinset.mp hu))
  have hlinear (u : ℂ) : DifferentiableAt ℂ (fun w : ℂ => w-u) z := by fun_prop
  have hnonzero (u : ℂ) (hu : u ∈ hd.toFinset) :
      ((fun w : ℂ => w-u) ^ d u) z ≠ 0 := by
    simpa only [Pi.pow_apply] using zpow_ne_zero (d u) (hroot u hu)
  have hdiff (u : ℂ) (hu : u ∈ hd.toFinset) :
      DifferentiableAt ℂ ((fun w : ℂ => w-u) ^ d u) z :=
    (hlinear u).zpow (Or.inl (hroot u hu))
  rw [hprod, logDeriv_prod hnonzero hdiff]
  calc
    _ = ∑ u ∈ hd.toFinset, (d u : ℂ) / (z-u) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Pi.pow_def, logDeriv_fun_zpow (hlinear u) (d u), linear_factor_logDeriv,
        mul_one_div]
    _ = _ := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro u hu
      apply hd.mem_toFinset.mpr
      change d u ≠ 0
      intro hd0
      exact hu (by change (d u : ℂ) / (z-u) = 0; simp only [hd0, Int.cast_zero, zero_div])

end QRHShort.CloudBatch.PrimesAPGrowthAux



noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- An exact local partial-fraction approximation, with a quantitative bound
for the logarithmic derivative of the actual entire quotient. -/
theorem entire_logDeriv_remainder_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (hcenter : m ≤ ‖f c‖) (hcircle : ∀ z ∈ sphere c (15/8), ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall c (5/4)) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor f (closedBall c (7/4)) u : ℂ) / (z-u)‖ ≤
      96 * (Real.log (M/m) +
        (((∑ᶠ u : ℂ, MeromorphicOn.divisor f (closedBall c (7/4)) u) : ℤ) : ℝ) *
          Real.log 14 + 1) := by
  let D := MeromorphicOn.divisor f (closedBall c (7/4))
  let P : ℂ → ℂ := ∏ᶠ u : ℂ, (fun w : ℂ => w-u) ^ D u
  have hfc : f c ≠ 0 := norm_pos_iff.mp (hm.trans_le hcenter)
  obtain ⟨g, hg, hfact, hgn⟩ := entire_extract_ball_divisor hf c hfc (7/4)
  have hDfinite : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall _ _)
  have hfa : AnalyticOnNhd ℂ f (closedBall c (7/4)) := fun w _ => hf.analyticAt w
  have hDnonneg (w : ℂ) : 0 ≤ D w := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa w
  have hzD : z ∈ closedBall c (7/4) := by
    have hz' : dist z c ≤ 5/4 := hz
    change dist z c ≤ 7/4
    linarith
  have hDz : D z = 0 := by
    dsimp only [D]
    rw [hfa.meromorphicOn.divisor_apply hzD,
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz]
    rfl
  have hPn : P z ≠ 0 := Function.FactorizedRational.ne_zero hDz
  have hPa : DifferentiableAt ℂ P z :=
    (Function.FactorizedRational.analyticAt (hDnonneg z)).differentiableAt
  have heq : f = P * g := funext hfact
  have hld : logDeriv f z = (∑ᶠ u : ℂ, (D u : ℂ)/(z-u)) + logDeriv g z := by
    calc
      logDeriv f z = logDeriv (P*g) z := congrArg (fun F => logDeriv F z) heq
      _ = logDeriv P z + logDeriv g z := logDeriv_mul z hPn (hgn z hzD) hPa (hg z)
      _ = _ := by
        rw [show logDeriv P z = ∑ᶠ u : ℂ, (D u : ℂ)/(z-u) from
          factorizedProduct_logDeriv hDfinite (Function.notMem_support.mpr hDz)]
  have hbound := factorized_quotient_logDeriv_le hDfinite hDnonneg hg
    D.supportWithinDomain hM hm hfact hcenter hcircle
    (fun w hw => hgn w (ball_subset_closedBall hw)) hz
  change ‖logDeriv f z - ∑ᶠ u : ℂ, (D u : ℂ)/(z-u)‖ ≤ _
  rw [hld, add_sub_cancel_left]
  exact hbound

/-- Uniform local partial fractions for the literal nonprincipal Dirichlet
L-function. The zeros and their multiplicities are its actual compact divisor;
the remainder is bounded independently of the conductor and the height apart
from the displayed logarithm. No zero-free hypothesis is used here. -/
theorem LFunction_local_logDeriv_remainder_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ)
    {z : ℂ} (hz : z ∈ closedBall (2+(T:ℂ)*Complex.I) (5/4))
    (hz0 : DirichletCharacter.LFunction χ z ≠ 0) :
    ‖logDeriv (DirichletCharacter.LFunction χ) z -
      ∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (closedBall (2+(T:ℂ)*Complex.I) (7/4)) u : ℂ) / (z-u)‖ ≤
      96 * ((1 + Real.log 14 / Real.log (15/14)) *
        Real.log (32*(q:ℝ)*(|T|+4)) + 1) := by
  let c : ℂ := 2+(T:ℂ)*Complex.I
  let M : ℝ := 8*(q:ℝ)*(|T|+4)
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hM : 0 < M := by dsimp only [M]; positivity
  have hc : c.re = 2 := by simp [c]
  have hc_norm : ‖c‖ ≤ |T|+2 := by
    calc
      _ ≤ ‖(2:ℂ)‖ + ‖(T:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]; ring
  have hbound : ∀ w ∈ sphere c (15/8), ‖DirichletCharacter.LFunction χ w‖ ≤ M := by
    intro w hw
    have hd : ‖w-c‖ = (15/8:ℝ) := by simpa only [mem_sphere, dist_eq_norm] using hw
    have hrew : (1/8:ℝ) ≤ w.re := by
      have hre := Complex.abs_re_le_norm (w-c)
      rw [Complex.sub_re, hc, hd] at hre
      linarith [neg_le_abs (w.re-2)]
    have hnw : ‖w‖ ≤ |T|+4 := by
      calc
        _ ≤ ‖w-c‖+‖c‖ := norm_le_norm_sub_add w c
        _ ≤ (15/8:ℝ)+(|T|+2) := by rw [hd]; gcongr
        _ ≤ _ := by linarith
    calc
      _ ≤ (q:ℝ)*‖w‖/w.re := norm_LFunction_le_level_mul_norm_div_re χ hχ (by linarith)
      _ ≤ (q:ℝ)*(|T|+4)/(1/8) := by gcongr
      _ = M := by dsimp only [M]; ring
  have hb := entire_logDeriv_remainder_le (DirichletCharacter.differentiable_LFunction hχ)
    hM (by norm_num : (0:ℝ)<1/4) (LFunction_center_lower χ T) hbound hz hz0
  have hratio : M/(1/4) = 32*(q:ℝ)*(|T|+4) := by dsimp only [M]; ring
  rw [hratio] at hb
  have hN := LFunction_local_zero_count_le χ hχ T
  have hlog14 : 0 ≤ Real.log (14:ℝ) := Real.log_nonneg (by norm_num)
  refine hb.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hN hlog14
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ)≤96)
  calc
    _ ≤ Real.log (32*(q:ℝ)*(|T|+4)) +
        (Real.log (32*(q:ℝ)*(|T|+4)) / Real.log (15/14)) * Real.log 14 + 1 := by
      linarith [hmul]
    _ = _ := by ring

end QRHShort.CloudBatch.PrimesAPGrowthAux





noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

def zetaFloorErrorCutoff (t : ℝ) : ℂ :=
  if 1 < t then (⌊t⌋₊ : ℂ) - (t : ℂ) else 0

theorem zetaFloorErrorCutoff_eq_zero {t : ℝ} (ht : t ≤ 1) :
    zetaFloorErrorCutoff t = 0 := if_neg (not_lt.mpr ht)

theorem zetaFloorErrorCutoff_measurable : Measurable zetaFloorErrorCutoff := by
  have hfloor : Measurable (fun t : ℝ => (⌊t⌋₊ : ℂ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℂ))).comp Nat.measurable_floor
  exact Measurable.ite measurableSet_Ioi
    (hfloor.sub Complex.continuous_ofReal.measurable) measurable_const

theorem zetaFloorErrorCutoff_norm_le (t : ℝ) : ‖zetaFloorErrorCutoff t‖ ≤ 1 := by
  unfold zetaFloorErrorCutoff
  split_ifs with ht
  · have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    have hfr := Nat.self_sub_floor_lt_one t
    have he : (⌊t⌋₊ : ℂ) - (t : ℂ) = (((⌊t⌋₊ : ℝ) - t : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sub, Complex.ofReal_natCast]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hfl)]
    linarith
  · simp

theorem zetaFloorErrorCutoff_locallyIntegrableOn :
    LocallyIntegrableOn zetaFloorErrorCutoff (Ioi (0 : ℝ)) := by
  apply (locallyIntegrableOn_const (s := Ioi (0 : ℝ)) (1 : ℂ)).mono
    zetaFloorErrorCutoff_measurable.aestronglyMeasurable
  filter_upwards [] with t
  simpa only [norm_one] using zetaFloorErrorCutoff_norm_le t

/-- On the original half-plane, the pole-removed principal L-function is
given by the bounded floor-error Mellin integral. -/
theorem regularizedZeta_eq_mellin_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s =
      s + s*(s-1)*mellin zetaFloorErrorCutoff (-s) := by
  let χ : DirichletCharacter ℂ 1 := 1
  have hprefix (N : ℕ) : (∑ n ∈ Icc 1 N, χ n) = (N : ℂ) := by
    simp [χ, MulChar.one_apply (isUnit_of_subsingleton _), Nat.card_Icc]
  have hO : (fun N : ℕ => ∑ n ∈ Icc 1 N, χ n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with N
    simp [hprefix]
  have hL := LSeries_eq_mul_integral (fun n : ℕ => χ n) (r := 1) (by norm_num) hs
    (χ.LSeriesSummable_of_one_lt_re hs) hO
  simp only [hprefix] at hL
  have hconv := (bounded_cutoff_mellin_data zetaFloorErrorCutoff 1
    zetaFloorErrorCutoff_locallyIntegrableOn zetaFloorErrorCutoff_norm_le
    (fun t ht => zetaFloorErrorCutoff_eq_zero ht) (by linarith : 0 < s.re)).1
  change IntegrableOn (fun t : ℝ => (t : ℂ)^(-s-1) • zetaFloorErrorCutoff t)
    (Ioi (0 : ℝ)) at hconv
  have hiE : IntegrableOn
      (fun t : ℝ => zetaFloorErrorCutoff t * (t : ℂ)^(-(s+1))) (Ioi (1 : ℝ)) := by
    have hi := hconv.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
    convert hi using 1
    ext t
    simp only [smul_eq_mul]
    rw [show -s-1 = -(s+1) by ring, mul_comm]
  have hsneg : (-s).re < -1 := by simpa only [neg_re] using neg_lt_neg hs
  have hipow := integrableOn_Ioi_cpow_of_lt hsneg zero_lt_one
  have hsplit : (∫ t : ℝ in Ioi 1, (⌊t⌋₊ : ℂ)*(t:ℂ)^(-(s+1))) =
      1/(s-1) + mellin zetaFloorErrorCutoff (-s) := by
    have heq : (∫ t : ℝ in Ioi 1, (⌊t⌋₊ : ℂ)*(t:ℂ)^(-(s+1))) =
        ∫ t : ℝ in Ioi 1, (t:ℂ)^(-s) + zetaFloorErrorCutoff t*(t:ℂ)^(-(s+1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 1 < t at ht
      have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (by linarith : t ≠ 0)
      have hp : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
        calc
          _ = (t:ℂ)^(1:ℂ) * (t:ℂ)^(-(s+1)) := by rw [cpow_one]
          _ = (t:ℂ)^((1:ℂ)+-(s+1)) := (cpow_add _ _ ht0).symm
          _ = _ := by congr 1; ring
      simp only [zetaFloorErrorCutoff, if_pos ht]
      rw [← hp]
      ring
    rw [heq, integral_add hipow hiE,
      ← cutoff_mellin_eq_integral zetaFloorErrorCutoff
        (fun t ht => zetaFloorErrorCutoff_eq_zero ht) s,
      integral_Ioi_cpow_of_lt hsneg zero_lt_one]
    simp only [Complex.ofReal_one, one_cpow]
    congr 1
    rw [show -s+1 = -(s-1) by ring, neg_div_neg_eq]
  have hs1 : s ≠ 1 := by intro h; simpa only [h, one_re, lt_self_iff_false] using hs
  have hsub : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  change Function.update (fun w : ℂ => (w-1)*DirichletCharacter.LFunction χ w) 1 _ s = _
  rw [Function.update_of_ne hs1, DirichletCharacter.LFunction_eq_LSeries χ hs, hL, hsplit]
  field_simp [hsub]

/-- The bounded Mellin expression equals the genuine entire regularization,
including its value at the removed pole. -/
theorem regularizedZeta_eq_mellin {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s =
      s + s*(s-1)*mellin zetaFloorErrorCutoff (-s) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1)
      {z : ℂ | 0 < z.re} :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd hopen
  have hM : AnalyticOnNhd ℂ
      (fun z : ℂ => z + z*(z-1)*mellin zetaFloorErrorCutoff (-z)) {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    have hm := (bounded_cutoff_mellin_data zetaFloorErrorCutoff 1
      zetaFloorErrorCutoff_locallyIntegrableOn zetaFloorErrorCutoff_norm_le
      (fun t ht => zetaFloorErrorCutoff_eq_zero ht) hz).2
    exact (differentiableAt_id.add
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hm)).differentiableWithinAt
  have heq : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      (fun z : ℂ => z + z*(z-1)*mellin zetaFloorErrorCutoff (-z)) := by
    have hnb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnb] with z hz
    exact regularizedZeta_eq_mellin_of_one_lt hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hM
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (2:ℂ)∈{z:ℂ|0<z.re}) heq hs

theorem norm_regularizedZeta_le {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ 1 s‖ ≤ ‖s‖ + ‖s‖*‖s-1‖/s.re := by
  rw [regularizedZeta_eq_mellin hs]
  calc
    _ ≤ ‖s‖ + ‖s*(s-1)*mellin zetaFloorErrorCutoff (-s)‖ := norm_add_le _ _
    _ = ‖s‖ + ‖s‖*‖s-1‖*‖mellin zetaFloorErrorCutoff (-s)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖*‖s-1‖*(1/s.re) := by
      gcongr
      exact norm_bounded_cutoff_mellin_le zetaFloorErrorCutoff 1
        zetaFloorErrorCutoff_locallyIntegrableOn zetaFloorErrorCutoff_norm_le
        (fun t ht => zetaFloorErrorCutoff_eq_zero ht) hs
    _ = _ := by ring

end QRHShort.CloudBatch.PrimesAPGrowthAux



noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem entire_local_zero_count_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {M m : ℝ} (hM : 1 ≤ M) (hm : 0 < m)
    (hcenter : m ≤ ‖f c‖) (hcircle : ∀ z ∈ sphere c (15/8), ‖f z‖ ≤ M) :
    (((∑ᶠ u : ℂ, MeromorphicOn.divisor f (closedBall c (7/4)) u) : ℤ) : ℝ) ≤
      Real.log (M/m) / Real.log (15/14) := by
  have hnorm : 0 < ‖f c‖ := hm.trans_le hcenter
  have ha : AnalyticOnNhd ℂ f (closedBall c |(15/8:ℝ)|) := fun z _ => hf.analyticAt z
  have hcirc : ∀ z ∈ sphere c |(15/8:ℝ)|, ‖f z‖ ≤ M := by
    simpa only [abs_of_pos (by norm_num : (0:ℝ)<15/8)] using hcircle
  have hj := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := (7/4:ℝ)) (R := (15/8:ℝ)) (M := M)
    (by norm_num) (by norm_num) hM ha (norm_pos_iff.mp hnorm) hcirc
  have hratio : M / ‖f c‖ ≤ M/m :=
    div_le_div_of_nonneg_left (by linarith : 0≤M) hm hcenter
  have hlog := Real.log_le_log (div_pos (by linarith : 0<M) hnorm) hratio
  rw [abs_of_pos (by norm_num : (0:ℝ)<7/4),
    show (15/8:ℝ)/(7/4) = 15/14 by norm_num] at hj
  exact hj.trans (div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num)))

theorem regularizedZeta_local_norm_data (T : ℝ) :
    (1/4:ℝ) ≤ ‖DirichletCharacter.LFunctionTrivChar₁ 1 (2+(T:ℂ)*Complex.I)‖ ∧
    ∀ s ∈ sphere (2+(T:ℂ)*Complex.I) (15/8),
      ‖DirichletCharacter.LFunctionTrivChar₁ 1 s‖ ≤ 16*(|T|+4)^2 := by
  let c : ℂ := 2+(T:ℂ)*Complex.I
  have hc : c.re = 2 := by simp [c]
  have hcn : c ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [hc, Complex.one_re] at this
    norm_num at this
  have hc_norm : ‖c‖ ≤ |T|+2 := by
    calc
      _ ≤ ‖(2:ℂ)‖+‖(T:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs]; ring
  constructor
  · change (1/4:ℝ) ≤ ‖DirichletCharacter.LFunctionTrivChar₁ 1 c‖
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hcn, norm_mul]
    have hn : 1 ≤ ‖c-1‖ := by
      have hr := Complex.abs_re_le_norm (c-1)
      simpa only [Complex.sub_re, hc, Complex.one_re, show |(2:ℝ)-1|=1 by norm_num] using hr
    have hl := LFunction_center_lower (1 : DirichletCharacter ℂ 1) T
    calc
      (1/4:ℝ) = 1*(1/4) := by ring
      _ ≤ ‖c-1‖*‖DirichletCharacter.LFunctionTrivChar 1 c‖ :=
        mul_le_mul hn hl (by norm_num) (norm_nonneg _)
  · intro s hs
    have hd : ‖s-c‖ = (15/8:ℝ) := by simpa only [mem_sphere, dist_eq_norm] using hs
    have hres : (1/8:ℝ) ≤ s.re := by
      have hr := Complex.abs_re_le_norm (s-c)
      rw [Complex.sub_re, hc, hd] at hr
      linarith [neg_le_abs (s.re-2)]
    have hns : ‖s‖ ≤ |T|+4 := by
      calc
        _ ≤ ‖s-c‖+‖c‖ := norm_le_norm_sub_add s c
        _ ≤ (15/8:ℝ)+(|T|+2) := by rw [hd]; gcongr
        _ ≤ _ := by linarith
    have hns1 : ‖s-1‖ ≤ |T|+5 := by
      calc
        _ ≤ ‖s‖+‖(1:ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_one]; linarith
    calc
      _ ≤ ‖s‖+‖s‖*‖s-1‖/s.re := norm_regularizedZeta_le (by linarith)
      _ ≤ (|T|+4)+(|T|+4)*(|T|+5)/(1/8) := by gcongr
      _ ≤ 16*(|T|+4)^2 := by nlinarith [abs_nonneg T, sq_nonneg (|T|+4)]

theorem regularizedZeta_logDeriv_eq {s : ℂ} (hs : s ≠ 1)
    (hL : DirichletCharacter.LFunctionTrivChar 1 s ≠ 0) :
    logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) s =
      logDeriv (DirichletCharacter.LFunctionTrivChar 1) s + 1/(s-1) := by
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs,
    DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs, logDeriv_apply]
  field_simp [hL, sub_ne_zero.mpr hs]

theorem regularizedZeta_ne_zero_right (hZ : QRHShort.DirichletZeroFreeStatement)
    {s : ℂ} (hs : (11:ℝ)/12 < s.re) : DirichletCharacter.LFunctionTrivChar₁ 1 s ≠ 0 := by
  by_cases h : s=1
  · subst s
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (hZ 1 1 s hs (.inl h))

/-- The principal primitive case uses the genuine pole-removed entire
function, its actual zeros, and the explicit pole term. -/
theorem regularizedZeta_local_estimates (T : ℝ) :
    ((((∑ᶠ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1)
      (closedBall (2+(T:ℂ)*Complex.I) (7/4)) u) : ℤ) : ℝ) ≤
      Real.log (64*(|T|+4)^2) / Real.log (15/14)) ∧
    ∀ s ∈ closedBall (2+(T:ℂ)*Complex.I) (5/4), s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar 1 s ≠ 0 →
      ‖logDeriv (DirichletCharacter.LFunctionTrivChar 1) s + 1/(s-1) -
        ∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1)
          (closedBall (2+(T:ℂ)*Complex.I) (7/4)) u : ℂ)/(s-u)‖ ≤
        96*((1+Real.log 14/Real.log (15/14))*Real.log (64*(|T|+4)^2)+1) := by
  obtain ⟨hc, hcircle⟩ := regularizedZeta_local_norm_data T
  have hM : 1 ≤ 16*(|T|+4)^2 := by nlinarith [abs_nonneg T, sq_nonneg (|T|+4)]
  have hratio : 16*(|T|+4)^2/(1/4) = 64*(|T|+4)^2 := by ring
  have hN := entire_local_zero_count_le (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1)
    hM (by norm_num : (0:ℝ)<1/4) hc hcircle
  rw [hratio] at hN
  refine ⟨hN, ?_⟩
  intro s hs hs1 hLs
  have hZs : DirichletCharacter.LFunctionTrivChar₁ 1 s ≠ 0 := by
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hLs
  have hb := entire_logDeriv_remainder_le (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1)
    (by linarith : 0 < 16*(|T|+4)^2) (by norm_num : (0:ℝ)<1/4) hc hcircle hs hZs
  rw [regularizedZeta_logDeriv_eq hs1 hLs, hratio] at hb
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ)≤96)
  have hmul := mul_le_mul_of_nonneg_right hN (Real.log_nonneg (by norm_num : (1:ℝ)≤14))
  calc
    _ ≤ Real.log (64*(|T|+4)^2) +
        (Real.log (64*(|T|+4)^2)/Real.log (15/14))*Real.log 14 + 1 := by linarith [hmul]
    _ = _ := by ring

end QRHShort.CloudBatch.PrimesAPGrowthAux




noncomputable section
open Classical Finset
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPAux

def positiveQuadratic (u : ℝ) : ℝ := (max u 0) ^ 2 / 2

def quadraticDifference (x h n : ℝ) : ℝ :=
  (positiveQuadratic (x + 2*h - n) - 2 * positiveQuadratic (x + h - n) +
    positiveQuadratic (x - n)) / h^2

theorem quadraticDifference_eq_one {x h n : ℝ} (hh : 0 < h) (hn : n ≤ x) :
    quadraticDifference x h n = 1 := by
  have h₀ : 0 ≤ x - n := sub_nonneg.mpr hn
  have h₁ : 0 ≤ x + h - n := by linarith
  have h₂ : 0 ≤ x + 2*h - n := by linarith
  simp only [quadraticDifference, positiveQuadratic, max_eq_left h₀,
    max_eq_left h₁, max_eq_left h₂]
  field_simp
  <;> nlinarith [ne_of_gt hh]

theorem quadraticDifference_eq_zero {x h n : ℝ} (hh : 0 < h)
    (hn : x + 2*h ≤ n) : quadraticDifference x h n = 0 := by
  have h₀ : x - n ≤ 0 := by linarith
  have h₁ : x + h - n ≤ 0 := by linarith
  have h₂ : x + 2*h - n ≤ 0 := by linarith
  simp [quadraticDifference, positiveQuadratic, max_eq_right h₀,
    max_eq_right h₁, max_eq_right h₂]

theorem quadraticDifference_mem_Icc {x h n : ℝ} (hh : 0 < h) :
    quadraticDifference x h n ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hn : n ≤ x
  · rw [quadraticDifference_eq_one hh hn]
    exact ⟨zero_le_one, le_rfl⟩
  by_cases hn₂ : x + 2*h ≤ n
  · rw [quadraticDifference_eq_zero hh hn₂]
    exact ⟨le_rfl, zero_le_one⟩
  have h₀ : x - n ≤ 0 := by linarith
  have h₂ : 0 ≤ x + 2*h - n := by linarith
  have hh₂ : 0 < h^2 := sq_pos_of_pos hh
  simp only [Set.mem_Icc, quadraticDifference, positiveQuadratic,
    max_eq_right h₀, max_eq_left h₂, zero_pow (by decide : 2 ≠ 0), zero_div,
    add_zero]
  by_cases hmid : 0 ≤ x + h - n
  · rw [max_eq_left hmid]
    have hs : (n-x)^2 ≤ h^2 := by
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    constructor
    · apply (le_div_iff₀ hh₂).mpr
      nlinarith [sq_nonneg (n-x)]
    · apply (div_le_iff₀ hh₂).mpr
      nlinarith [sq_nonneg (n-x)]
  · rw [max_eq_right (le_of_not_ge hmid)]
    have hs : (x+2*h-n)^2 ≤ h^2 := by
      exact pow_le_pow_left₀ h₂ (by linarith) 2
    constructor
    · apply (le_div_iff₀ hh₂).mpr
      nlinarith [sq_nonneg (x+2*h-n)]
    · apply (div_le_iff₀ hh₂).mpr
      nlinarith

theorem finite_quadraticDifference_error_eq
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (p : ι → ℝ)
    {x h : ℝ} (hh : 0 < h) :
    (∑ i ∈ s, a i * (quadraticDifference x h (p i) : ℂ)) -
      (∑ i ∈ s, if p i ≤ x then a i else 0) =
      ∑ i ∈ s.filter (fun i => x < p i ∧ p i ≤ x+2*h),
        a i * (quadraticDifference x h (p i) : ℂ) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : p i ≤ x
  · simp [hx, not_lt.mpr hx, quadraticDifference_eq_one hh hx]
  · have hx' : x < p i := lt_of_not_ge hx
    by_cases htop : p i ≤ x+2*h
    · simp [hx, hx', htop]
    · have hz := quadraticDifference_eq_zero hh (le_of_not_ge htop)
      simp [hx, hx', htop, hz]

theorem finite_quadraticDifference_error_norm_le
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (p : ι → ℝ)
    {x h : ℝ} (hh : 0 < h) :
    ‖(∑ i ∈ s, a i * (quadraticDifference x h (p i) : ℂ)) -
      (∑ i ∈ s, if p i ≤ x then a i else 0)‖ ≤
      ∑ i ∈ s.filter (fun i => x < p i ∧ p i ≤ x+2*h), ‖a i‖ := by
  rw [finite_quadraticDifference_error_eq s a p hh]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hD := quadraticDifference_mem_Icc (x := x) (n := p i) hh
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD.1]
  exact mul_le_of_le_one_right (norm_nonneg _) hD.2

def quadraticPrefix (a : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, a n * (positiveQuadratic (y-n) : ℂ)

theorem quadraticPrefix_eq_common (a : ℕ → ℂ) {y Y : ℝ}
    (hy : 0 ≤ y) (hyY : y ≤ Y) :
    quadraticPrefix a y =
      ∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, a n * (positiveQuadratic (y-n) : ℂ) := by
  unfold quadraticPrefix
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono hyY)⟩
  · intro n hnY hny
    have hn : y ≤ (n : ℝ) := by
      have hn' : ¬ n ≤ ⌊y⌋₊ := by simpa using hny
      exact (lt_of_not_ge ((Nat.le_floor_iff hy).not.mp hn')).le
    simp [positiveQuadratic, max_eq_right (sub_nonpos.mpr hn)]

theorem quadraticPrefix_difference_eq_common (a : ℕ → ℂ) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 < h) :
    (quadraticPrefix a (x+2*h) - 2*quadraticPrefix a (x+h) +
      quadraticPrefix a x) / (h : ℂ)^2 =
      ∑ n ∈ Finset.Icc 0 ⌊x+2*h⌋₊,
        a n * (quadraticDifference x h n : ℂ) := by
  rw [quadraticPrefix_eq_common a (by linarith : 0 ≤ x+2*h) le_rfl,
    quadraticPrefix_eq_common a (by linarith : 0 ≤ x+h) (by linarith : x+h ≤ x+2*h),
    quadraticPrefix_eq_common a hx (by linarith : x ≤ x+2*h)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  unfold quadraticDifference
  push_cast
  ring

theorem quadraticPrefix_unsmoothing_norm_le (a : ℕ → ℂ) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 < h) :
    ‖(quadraticPrefix a (x+2*h) - 2*quadraticPrefix a (x+h) +
        quadraticPrefix a x) / (h : ℂ)^2 - ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, a n‖ ≤
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+2*h⌋₊, ‖a n‖ := by
  have hY : 0 ≤ x+2*h := by linarith
  have hf : (Finset.Icc 0 ⌊x+2*h⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x) =
      Finset.Icc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [← Nat.le_floor_iff hx]
    constructor
    · rintro ⟨⟨hn0, _⟩, hnx⟩
      exact ⟨hn0, hnx⟩
    · rintro ⟨hn0, hnx⟩
      exact ⟨⟨hn0, hnx.trans (Nat.floor_mono (by linarith : x ≤ x+2*h))⟩, hnx⟩
  have hs : (Finset.Icc 0 ⌊x+2*h⌋₊).filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x+2*h) =
      Finset.Ioc ⌊x⌋₊ ⌊x+2*h⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, hnY⟩, hnx, _⟩
      exact ⟨(Nat.floor_lt hx).mpr hnx, hnY⟩
    · rintro ⟨hnx, hnY⟩
      exact ⟨⟨Nat.zero_le n, hnY⟩, (Nat.floor_lt hx).mp hnx,
        (Nat.le_floor_iff hY).mp hnY⟩
  have he := finite_quadraticDifference_error_norm_le
    (Finset.Icc 0 ⌊x+2*h⌋₊) a (fun n : ℕ => (n : ℝ)) (x := x) hh
  rw [← Finset.sum_filter, hf, hs] at he
  rw [quadraticPrefix_difference_eq_common a hx hh]
  exact he

theorem quadratic_shortInterval_card_le {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    ((Finset.Ioc ⌊x⌋₊ ⌊x+2*h⌋₊).card : ℝ) ≤ 2*h+1 := by
  rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : x ≤ x+2*h))]
  have hfloor := Nat.floor_le (show 0 ≤ x+2*h by linarith)
  have hfloor' := Nat.lt_floor_add_one x
  linarith

theorem quadraticPrefix_eq_polynomial (a : ℕ → ℂ) {y : ℝ} (hy : 0 ≤ y) :
    quadraticPrefix a y = ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
      a n * (((y : ℂ) - n)^2 / 2) := by
  unfold quadraticPrefix
  apply Finset.sum_congr rfl
  intro n hn
  have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy).mp (Finset.mem_Icc.mp hn).2
  simp only [positiveQuadratic, max_eq_left (sub_nonneg.mpr hny)]
  push_cast <;> rfl

theorem mangoldt_quadraticPrefix_unsmoothing_norm_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) {x h : ℝ} (hx : 2 ≤ x) (hh : 0 < h) :
    ‖(quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) (x+2*h) -
       2*quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) (x+h) +
       quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) x) /
        (h : ℂ)^2 -
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ ≤
      (2*h+1)*Real.log (x+2*h) := by
  have hx0 : 0 ≤ x := by linarith
  have hY : 0 ≤ x+2*h := by linarith
  have hlog : 0 ≤ Real.log (x+2*h) := Real.log_nonneg (by linarith)
  refine (quadraticPrefix_unsmoothing_norm_le _ hx0 hh).trans ?_
  calc
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+2*h⌋₊,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖) ≤
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+2*h⌋₊, Real.log (x+2*h) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnx : x < (n : ℝ) := (Nat.floor_lt hx0).mp (Finset.mem_Ioc.mp hn).1
      have hnY : (n : ℝ) ≤ x+2*h :=
        (Nat.le_floor_iff hY).mp (Finset.mem_Ioc.mp hn).2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc
        ArithmeticFunction.vonMangoldt n * ‖χ n‖ ≤ ArithmeticFunction.vonMangoldt n :=
          mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
        _ ≤ Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log (x+2*h) := Real.log_le_log (by linarith) hnY
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+2*h⌋₊).card : ℝ) * Real.log (x+2*h) := by simp
    _ ≤ (2*h+1)*Real.log (x+2*h) :=
      mul_le_mul_of_nonneg_right (quadratic_shortInterval_card_le hx0 hh) hlog

end QRHShort.CloudBatch.PrimesAPAux

noncomputable section
open Classical Finset
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPAux

theorem quadratic_kernel_scale {x u : ℝ} (hx : 0 < x) :
    ((((max (1-u/x) 0)^2/2 : ℝ) : ℂ)) =
      ((((max (x-u) 0)^2/2 : ℝ) : ℂ)) / (x : ℂ)^2 := by
  have he : 1-u/x = (x-u)/x := by field_simp [hx.ne'] <;> ring
  have hm : max (1-u/x) 0 = max (x-u) 0 / x := by
    rw [he, ← max_div_div_right hx.le (x-u) 0]
    simp
  rw [hm]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  push_cast
  field_simp [hxC]
  <;> ring

theorem quadratic_kernel_term_zero (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ∉ Finset.Icc 0 ⌊x⌋₊) :
    a n * ((((max (1-(n:ℝ)/x) 0)^2/2 : ℝ) : ℂ)) = 0 := by
  have hnx : x < (n : ℝ) := by
    apply (Nat.floor_lt hx.le).mp
    simpa using hn
  have hdiv : 1 ≤ (n : ℝ)/x := (le_div_iff₀ hx).mpr (by linarith)
  simp [max_eq_right (sub_nonpos.mpr hdiv)]

theorem quadratic_kernel_hasFiniteSupport (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    Function.HasFiniteSupport
      (fun n : ℕ => a n * ((((max (1-(n:ℝ)/x) 0)^2/2 : ℝ) : ℂ))) := by
  apply (Finset.Icc 0 ⌊x⌋₊).finite_toSet.subset
  intro n hn
  by_contra hnot
  exact hn (quadratic_kernel_term_zero a hx hnot)

/-- This infinite sum is genuinely finitely supported, including its term at zero.
The coefficient `a 0` is unrestricted. -/
theorem quadratic_kernel_tsum_eq_finite_prefix (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, a n * ((((max (1-(n:ℝ)/x) 0)^2/2 : ℝ) : ℂ))) =
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
        a n * ((((max (x-(n:ℝ)) 0)^2/2 : ℝ) : ℂ))) / (x : ℂ)^2 := by
  rw [tsum_eq_sum (s := Finset.Icc 0 ⌊x⌋₊) (fun n hn => quadratic_kernel_term_zero a hx hn)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [quadratic_kernel_scale hx]
  ring

end QRHShort.CloudBatch.PrimesAPAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

def rieszKernel2 (t : ℝ) : ℂ := (((max (1-t) 0)^2 / 2 : ℝ) : ℂ)

theorem rieszKernel2_continuous : Continuous rieszKernel2 := by
  unfold rieszKernel2
  fun_prop

theorem rieszKernel2_eq_zero {t : ℝ} (ht : 1 ≤ t) : rieszKernel2 t = 0 := by
  simp [rieszKernel2, max_eq_right (sub_nonpos.mpr ht)]

theorem integral_cpow_zero_one {s : ℂ} (hs : -1 < s.re) :
    (∫ t : ℝ in Ioo 0 1, (t:ℂ)^s) = 1/(s+1) := by
  have hs1 : s+1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1), integral_cpow (.inl hs)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_cpow, zero_cpow hs1, sub_zero]

/-- The quadratic cutoff has a genuinely convergent Mellin transform on the
positive half-plane, with its exact rational value. -/
theorem rieszKernel2_mellin_data {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent rieszKernel2 s ∧
      mellin rieszKernel2 s = 1/(s*(s+1)*(s+2)) := by
  let A : ℝ → ℂ := fun t => (t:ℂ)^(s-1)
  let B : ℝ → ℂ := fun t => (t:ℂ)^s
  let C : ℝ → ℂ := fun t => (t:ℂ)^(s+1)
  let F : ℝ → ℂ := fun t => (t:ℂ)^(s-1)*rieszKernel2 t
  let G : ℝ → ℂ := fun t => (A t-2*B t+C t)/2
  have hsa : -1 < (s-1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hsb : -1 < s.re := by linarith
  have hsc : -1 < (s+1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hiA : IntegrableOn A (Ioo (0:ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).mpr hsa
  have hiB : IntegrableOn B (Ioo (0:ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).mpr hsb
  have hiC : IntegrableOn C (Ioo (0:ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).mpr hsc
  have hiG : IntegrableOn G (Ioo (0:ℝ) 1) :=
    ((hiA.sub (hiB.const_mul 2)).add hiC).div_const 2
  have hFG : EqOn F G (Ioo (0:ℝ) 1) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    have hp1 : (t:ℂ)^s = (t:ℂ)^(s-1)*(t:ℂ) := by
      simpa only [sub_add_cancel, cpow_one] using cpow_add (s-1) 1 ht0
    have hp2 : (t:ℂ)^(s+1) = (t:ℂ)^(s-1)*(t:ℂ)^2 := by
      have h := cpow_add (s-1) 2 ht0
      rw [show s-1+2 = s+1 by ring, cpow_two] at h
      exact h
    dsimp only [F, G, A, B, C, rieszKernel2]
    rw [max_eq_left (sub_nonneg.mpr ht.2.le)]
    push_cast
    rw [hp1, hp2]
    ring
  have hiF : IntegrableOn F (Ioo (0:ℝ) 1) := hiG.congr_fun hFG.symm measurableSet_Ioo
  have hFzero : ∀ t ∈ Ioi (0:ℝ) \ Ioo 0 1, F t = 0 := by
    intro t ht
    have ht1 : 1 ≤ t := le_of_not_gt (fun h => ht.2 ⟨ht.1, h⟩)
    simp only [F, rieszKernel2_eq_zero ht1, mul_zero]
  refine ⟨?_, ?_⟩
  · simpa only [MellinConvergent, smul_eq_mul] using
      hiF.of_forall_sdiff_eq_zero measurableSet_Ioi hFzero
  · change (∫ t in Ioi (0:ℝ), F t) = _
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (s := Ioo (0:ℝ) 1) (t := Ioi (0:ℝ)) measurableSet_Ioi Ioo_subset_Ioi_self hFzero]
    rw [setIntegral_congr_fun measurableSet_Ioo hFG]
    change (∫ t in Ioo (0:ℝ) 1, (A t-2*B t+C t)/2) = _
    rw [integral_div,
      integral_add (f := fun t => A t-2*B t) (g := C) (hiA.sub (hiB.const_mul 2)) hiC,
      integral_sub (f := A) (g := fun t => 2*B t) hiA (hiB.const_mul 2), integral_const_mul]
    change ((∫ t in Ioo (0:ℝ) 1, (t:ℂ)^(s-1)) -
      2*(∫ t in Ioo (0:ℝ) 1, (t:ℂ)^s) +
        (∫ t in Ioo (0:ℝ) 1, (t:ℂ)^(s+1)))/2 = _
    rw [integral_cpow_zero_one hsa, integral_cpow_zero_one hsb,
      integral_cpow_zero_one hsc, sub_add_cancel, show s+1+1=s+2 by ring]
    have hs0 : s ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hs
    have hs1 : s+1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hs2 : s+2 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
      linarith
    field_simp [hs0, hs1, hs2] <;> ring

/-- An integrable uniform majorant on every positive vertical line. -/
theorem norm_rieszMellin_vertical_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖(1:ℂ)/((σ+(t:ℂ)*Complex.I)*(σ+(t:ℂ)*Complex.I+1)*
      (σ+(t:ℂ)*Complex.I+2))‖ ≤ σ⁻¹*(1+t^2)⁻¹ := by
  let z : ℂ := σ+(t:ℂ)*Complex.I
  have hzn : σ ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    simpa [z, abs_of_pos hσ] using h
  have h1 : ‖z+1‖^2 = (σ+1)^2+t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z, sq]
  have h2 : ‖z+2‖^2 = (σ+2)^2+t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z, sq]
  have h12 : ‖z+1‖ ≤ ‖z+2‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [h1, h2]
    nlinarith
  have hsq : 1+t^2 ≤ ‖z+1‖^2 := by rw [h1]; nlinarith
  have hprod : σ*(1+t^2) ≤ ‖z‖*‖z+1‖*‖z+2‖ := by
    calc
      _ ≤ ‖z‖*(1+t^2) := mul_le_mul_of_nonneg_right hzn (by positivity)
      _ ≤ ‖z‖*(‖z+1‖*‖z+1‖) := by
        simpa only [pow_two] using (mul_le_mul_of_nonneg_left hsq (norm_nonneg z))
      _ ≤ ‖z‖*(‖z+1‖*‖z+2‖) := by gcongr
      _ = _ := by ring
  change ‖(1:ℂ)/(z*(z+1)*(z+2))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, norm_mul]
  calc
    _ ≤ 1/(σ*(1+t^2)) :=
      one_div_le_one_div_of_le (mul_pos hσ (by positivity)) hprod
    _ = _ := by rw [one_div, mul_inv_rev]; ring

theorem rieszMellin_verticalIntegrable {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1)*(s+2))) σ := by
  have hz (t : ℝ) (a : ℝ) (ha : 0 ≤ a) : (σ:ℂ)+(t:ℂ)*Complex.I+(a:ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, add_zero, Complex.zero_re] at this
    linarith
  have hc : Continuous (fun t : ℝ => (1:ℂ)/
      ((σ+(t:ℂ)*Complex.I)*(σ+(t:ℂ)*Complex.I+1)*(σ+(t:ℂ)*Complex.I+2))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · simpa only [Complex.ofReal_zero, add_zero] using hz t 0 le_rfl
    · simpa only [Complex.ofReal_one] using hz t 1 zero_le_one
    · simpa using hz t 2 (by norm_num)
  apply (integrable_inv_one_add_sq.const_mul σ⁻¹).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  exact norm_rieszMellin_vertical_le hσ t

/-- Genuine inverse Mellin formula for the continuous quadratic cutoff.
Both Mellin convergence and vertical absolute integrability are proved. -/
theorem rieszKernel2_inverse_mellin {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1)*(s+2))) y = rieszKernel2 y := by
  have heq (t : ℝ) : mellin rieszKernel2 (σ+(t:ℂ)*Complex.I) =
      1/((σ+(t:ℂ)*Complex.I)*(σ+(t:ℂ)*Complex.I+1)*
        (σ+(t:ℂ)*Complex.I+2)) :=
    (rieszKernel2_mellin_data (by simpa using hσ)).2
  have hVi : VerticalIntegrable (mellin rieszKernel2) σ := by
    exact (rieszMellin_verticalIntegrable hσ).congr
      (Eventually.of_forall fun t => (heq t).symm)
  calc
    _ = mellinInv σ (mellin rieszKernel2) y := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [heq t]
    _ = _ := mellinInv_mellin_eq σ rieszKernel2 hy
      (rieszKernel2_mellin_data (by simpa using hσ)).1 hVi rieszKernel2_continuous.continuousAt

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Absolute convergence on a vertical line justifies multiplying the actual
Dirichlet series by an integrable kernel and interchanging its sum and integral.
The conclusion includes genuine integrability of the full series. -/
theorem LSeries_vertical_integral_exchange {a : ℕ → ℂ} {σ : ℝ}
    (ha : LSeriesSummable a (σ:ℂ)) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun t : ℝ => LSeries a (σ+(t:ℂ)*Complex.I)*g t) ∧
      (∫ t : ℝ, LSeries a (σ+(t:ℂ)*Complex.I)*g t) =
        ∑' n : ℕ, ∫ t : ℝ, LSeries.term a (σ+(t:ℂ)*Complex.I) n * g t := by
  have ha' : Summable (LSeries.term a (σ:ℂ)) := ha
  have hnorm (n : ℕ) (t : ℝ) :
      ‖LSeries.term a (σ+(t:ℂ)*Complex.I) n‖ = ‖LSeries.term a (σ:ℂ) n‖ := by
    simp only [LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
  have hcont (n : ℕ) : Continuous (fun t : ℝ => LSeries.term a (σ+(t:ℂ)*Complex.I) n) := by
    have hd : Differentiable ℂ (fun s : ℂ => LSeries.term a s n) :=
      fun s => (LSeries.hasDerivAt_term a n s).differentiableAt
    exact hd.continuous.comp (by fun_prop)
  have hcontL : Continuous (fun t : ℝ => LSeries a (σ+(t:ℂ)*Complex.I)) := by
    change Continuous (fun t : ℝ => ∑' n, LSeries.term a (σ+(t:ℂ)*Complex.I) n)
    exact continuous_tsum hcont ha'.norm (fun n t => (hnorm n t).le)
  have hboundL (t : ℝ) :
      ‖LSeries a (σ+(t:ℂ)*Complex.I)‖ ≤ ∑' n : ℕ, ‖LSeries.term a (σ:ℂ) n‖ := by
    have hs : Summable (fun n : ℕ => ‖LSeries.term a (σ+(t:ℂ)*Complex.I) n‖) :=
      ha'.norm.congr (fun n => (hnorm n t).symm)
    calc
      _ ≤ ∑' n : ℕ, ‖LSeries.term a (σ+(t:ℂ)*Complex.I) n‖ := norm_tsum_le_tsum_norm hs
      _ = _ := tsum_congr (fun n => hnorm n t)
  have hint (n : ℕ) : Integrable
      (fun t : ℝ => LSeries.term a (σ+(t:ℂ)*Complex.I) n * g t) := by
    apply (hg.norm.const_mul ‖LSeries.term a (σ:ℂ) n‖).mono'
      ((hcont n).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards [] with t
    simp only [Pi.mul_apply]
    rw [norm_mul, hnorm]
  have hnormint (n : ℕ) :
      (∫ t : ℝ, ‖LSeries.term a (σ+(t:ℂ)*Complex.I) n * g t‖) =
        ‖LSeries.term a (σ:ℂ) n‖ * ∫ t : ℝ, ‖g t‖ := by
    simp_rw [norm_mul, hnorm]
    exact integral_const_mul _ _
  have hsum : Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖LSeries.term a (σ+(t:ℂ)*Complex.I) n * g t‖) := by
    simpa only [hnormint] using ha'.norm.mul_right (∫ t : ℝ, ‖g t‖)
  constructor
  · apply (hg.norm.const_mul (∑' n : ℕ, ‖LSeries.term a (σ:ℂ) n‖)).mono'
      (hcontL.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards [] with t
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hboundL t) (norm_nonneg _)
  · calc
      _ = ∫ t : ℝ, ∑' n : ℕ, LSeries.term a (σ+(t:ℂ)*Complex.I) n * g t := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [LSeries, tsum_mul_right]
      _ = _ := (integral_tsum_of_summable_integral_norm hint hsum).symm

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- A genuine quadratic Perron formula obtained from absolute convergence,
the exact inverse Mellin kernel, and its actual finite support. -/
theorem quadraticPrefix_mellinInv_LSeries {a : ℕ → ℂ} (ha0 : a 0 = 0)
    {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ha : LSeriesSummable a (σ:ℂ)) :
    Integrable (fun t : ℝ => ((1/x:ℝ):ℂ)^(-(σ+(t:ℂ)*Complex.I)) *
      (LSeries a (σ+(t:ℂ)*Complex.I) /
        ((σ+(t:ℂ)*Complex.I)*(σ+(t:ℂ)*Complex.I+1)*(σ+(t:ℂ)*Complex.I+2)))) ∧
    PrimesAPAux.quadraticPrefix a x = (x:ℂ)^2 *
      mellinInv σ (fun s : ℂ => LSeries a s / (s*(s+1)*(s+2))) (1/x) := by
  let K : ℂ → ℂ := fun s => 1/(s*(s+1)*(s+2))
  let G : ℝ → ℂ := fun t => ((1/x:ℝ):ℂ)^(-(σ+(t:ℂ)*Complex.I))*K (σ+(t:ℂ)*Complex.I)
  let r : ℝ := 1/(2*Real.pi)
  have hxinv : 0 < 1/x := one_div_pos.mpr hx
  have hFi : Integrable (fun t : ℝ => K (σ+(t:ℂ)*Complex.I)) := rieszMellin_verticalIntegrable hσ
  have hpcont : Continuous (fun t : ℝ => ((1/x:ℝ):ℂ)^(-(σ+(t:ℂ)*Complex.I))) :=
    (show Continuous (fun t : ℝ => -(σ+(t:ℂ)*Complex.I)) by fun_prop).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hxinv.ne'))
  have hG : Integrable G := by
    apply (hFi.norm.const_mul ((1/x:ℝ)^(-σ))).mono'
      (hpcont.aestronglyMeasurable.mul hFi.aestronglyMeasurable)
    filter_upwards [] with t
    simp only [Pi.mul_apply, G, norm_mul, norm_cpow_eq_rpow_re_of_pos hxinv, Complex.neg_re,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, le_refl]
  obtain ⟨hint, hexchange⟩ := LSeries_vertical_integral_exchange ha hG
  have hfun : (fun t : ℝ => ((1/x:ℝ):ℂ)^(-(σ+(t:ℂ)*Complex.I)) *
      (LSeries a (σ+(t:ℂ)*Complex.I) /
        ((σ+(t:ℂ)*Complex.I)*(σ+(t:ℂ)*Complex.I+1)*(σ+(t:ℂ)*Complex.I+2)))) =
      (fun t : ℝ => LSeries a (σ+(t:ℂ)*Complex.I)*G t) := by
    funext t
    dsimp only [G, K]
    ring
  refine ⟨hfun.symm ▸ hint, ?_⟩
  have hterm (n : ℕ) :
      r • (∫ t : ℝ, LSeries.term a (σ+(t:ℂ)*Complex.I) n * G t) =
        a n * rieszKernel2 ((n:ℝ)/x) := by
    by_cases hn : n=0
    · subst n
      simp only [LSeries.term_zero, zero_mul, integral_zero, smul_zero, ha0]
    · have hnp : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hp (s : ℂ) : (((n:ℝ)/x:ℝ):ℂ)^(-s) =
          (n:ℂ)^(-s)*((1/x:ℝ):ℂ)^(-s) := by
        rw [show (n:ℝ)/x = (n:ℝ)*(1/x) by ring, Complex.ofReal_mul,
          mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hxinv.le]
        simp only [Complex.ofReal_natCast]
      have heq : (fun t : ℝ => LSeries.term a (σ+(t:ℂ)*Complex.I) n * G t) =
          (fun t : ℝ => a n *
            ((((n:ℝ)/x:ℝ):ℂ)^(-(σ+(t:ℂ)*Complex.I))*K (σ+(t:ℂ)*Complex.I))) := by
        funext t
        rw [LSeries.term_of_ne_zero hn, hp]
        dsimp only [G]
        rw [div_eq_mul_inv, ← cpow_neg]
        ring
      rw [heq, integral_const_mul, ← mul_smul_comm]
      change a n * mellinInv σ K ((n:ℝ)/x) = _
      rw [rieszKernel2_inverse_mellin hσ (div_pos hnp hx)]
  have hm : mellinInv σ (fun s : ℂ => LSeries a s/(s*(s+1)*(s+2))) (1/x) =
      PrimesAPAux.quadraticPrefix a x/(x:ℂ)^2 := by
    calc
      _ = r • (∫ t : ℝ, LSeries a (σ+(t:ℂ)*Complex.I)*G t) := by
        unfold mellinInv
        congr 1
        simp only [smul_eq_mul]
        rw [hfun]
      _ = r • (∑' n : ℕ, ∫ t : ℝ, LSeries.term a (σ+(t:ℂ)*Complex.I) n*G t) := by
        rw [hexchange]
      _ = ∑' n : ℕ, a n * rieszKernel2 ((n:ℝ)/x) := by
        rw [← tsum_const_smul'' r]
        exact tsum_congr hterm
      _ = _ := by
        simpa only [rieszKernel2, PrimesAPAux.quadraticPrefix, PrimesAPAux.positiveQuadratic] using
          PrimesAPAux.quadratic_kernel_tsum_eq_finite_prefix a hx
  have hxn : (x:ℂ)^2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hx.ne')
  calc
    _ = mellinInv σ (fun s : ℂ => LSeries a s/(s*(s+1)*(s+2))) (1/x)*(x:ℂ)^2 :=
      ((eq_div_iff hxn).mp hm).symm
    _ = _ := mul_comm _ _

/-- Quadratic Perron for the literal twisted Mangoldt coefficients and the
literal continued Dirichlet L-function; no zero-free premise is needed. -/
theorem mangoldt_quadraticPrefix_perron {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ x : ℝ} (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ => ((1/x:ℝ):ℂ)^(-(σ+(t:ℂ)*Complex.I)) *
      (-logDeriv (DirichletCharacter.LFunction χ) (σ+(t:ℂ)*Complex.I) /
        ((σ+(t:ℂ)*Complex.I)*(σ+(t:ℂ)*Complex.I+1)*(σ+(t:ℂ)*Complex.I+2)))) ∧
    PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n) x =
      (x:ℂ)^2 * mellinInv σ
        (fun s : ℂ => -logDeriv (DirichletCharacter.LFunction χ) s/(s*(s+1)*(s+2))) (1/x) := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n
  have ha0 : a 0 = 0 := by simp [a]
  have ha : LSeriesSummable a (σ:ℂ) := by
    simpa [LSeriesSummable, LSeries.term, a, Pi.mul_def, mul_comm] using
      χ.LSeriesSummable_twist_vonMangoldt (by simpa using hσ : 1 < (σ:ℂ).re)
  have hL (s : ℂ) (hs : 1 < s.re) : LSeries a s = -logDeriv (DirichletCharacter.LFunction χ) s := by
    have hseries := (χ.LSeriesSummable_twist_vonMangoldt hs).LSeriesHasSum
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      ← DirichletCharacter.LFunction_eq_LSeries χ hs] at hseries
    have hsum : HasSum (LSeries.term a s) (-logDeriv (DirichletCharacter.LFunction χ) s) := by
      simpa only [LSeriesHasSum, LSeries.term, a, Pi.mul_def, mul_comm, logDeriv_apply, neg_div] using hseries
    exact hsum.tsum_eq
  have hline (t : ℝ) : LSeries a (σ+(t:ℂ)*Complex.I) =
      -logDeriv (DirichletCharacter.LFunction χ) (σ+(t:ℂ)*Complex.I) :=
    hL _ (by simpa using hσ)
  obtain ⟨hint, heq⟩ := quadraticPrefix_mellinInv_LSeries ha0 (by linarith : 0<σ) hx ha
  constructor
  · simpa only [hline] using hint
  · rw [heq]
    congr 1
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hline]

end QRHShort.CloudBatch.PrimesAPGrowthAux


noncomputable section
open Complex MeasureTheory Set
open scoped Interval

namespace QRHShort.CloudBatch.PrimesAPRectAux

def rectIntegral (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ) + c * I)) -
    (∫ x : ℝ in a..b, f ((x : ℂ) + d * I)) +
    I * (∫ y : ℝ in c..d, f ((b : ℂ) + y * I)) -
    I * (∫ y : ℝ in c..d, f ((a : ℂ) + y * I))

theorem integral_inv_horizontal (a b : ℝ) (v : ℂ) (hv : v.im ≠ 0) :
    (∫ x : ℝ in a..b, ((x : ℂ) + v)⁻¹) =
      Complex.log ((b : ℂ) + v) - Complex.log ((a : ℂ) + v) := by
  have hn (x : ℝ) : (x : ℂ) + v ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    exact hv (by simpa using hi)
  have hc : Continuous (fun x : ℝ => ((x : ℂ) + v)⁻¹) :=
    (Complex.continuous_ofReal.add continuous_const).inv₀ hn
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable a b)
  intro x _
  have hs : (x : ℂ) + v ∈ Complex.slitPlane := by
    simp [Complex.mem_slitPlane_iff, hv]
  simpa only [id_eq, one_div] using!
    (((hasDerivAt_id (x : ℂ)).add_const v).clog hs).comp_ofReal

theorem integral_inv_vertical_pos (c d : ℝ) (v : ℂ) (hv : 0 < v.re) :
    I * (∫ y : ℝ in c..d, (v + y * I)⁻¹) =
      Complex.log (v + d * I) - Complex.log (v + c * I) := by
  have hn (y : ℝ) : v + y * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have : v.re = 0 := by simpa using hr
    linarith
  have hc : Continuous (fun y : ℝ => I * (v + y * I)⁻¹) :=
    ((continuous_const.add (Complex.continuous_ofReal.mul_const I)).inv₀ hn).const_mul I
  have hd (y : ℝ) : HasDerivAt (fun t : ℝ => Complex.log (v + t * I))
      (I * (v + y * I)⁻¹) y := by
    have hs : v + y * I ∈ Complex.slitPlane := by
      simp [Complex.mem_slitPlane_iff, hv]
    simpa only [id_eq, one_mul, div_eq_mul_inv] using!
      ((((hasDerivAt_id (y : ℂ)).mul_const I).const_add v).clog hs).comp_ofReal
  simpa only [intervalIntegral.integral_const_mul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable c d)

theorem integral_inv_vertical_neg (c d : ℝ) (v : ℂ) (hv : v.re < 0) :
    I * (∫ y : ℝ in c..d, (v + y * I)⁻¹) =
      Complex.log (-(v + d * I)) - Complex.log (-(v + c * I)) := by
  have hn (y : ℝ) : v + y * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have : v.re = 0 := by simpa using hr
    linarith
  have hc : Continuous (fun y : ℝ => I * (v + y * I)⁻¹) :=
    ((continuous_const.add (Complex.continuous_ofReal.mul_const I)).inv₀ hn).const_mul I
  have hd (y : ℝ) : HasDerivAt (fun t : ℝ => Complex.log (-(v + t * I)))
      (I * (v + y * I)⁻¹) y := by
    have hs : -(v + y * I) ∈ Complex.slitPlane := by
      simp only [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact Or.inl (neg_pos.mpr hv)
    simpa only [id_eq, Pi.neg_apply, one_mul, neg_div_neg_eq, div_eq_mul_inv,
      inv_neg, neg_mul_neg] using!
      (((((hasDerivAt_id (y : ℂ)).mul_const I).const_add v).neg).clog hs).comp_ofReal
  simpa only [intervalIntegral.integral_const_mul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable c d)

theorem log_sub_log_neg_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    Complex.log z - Complex.log (-z) = Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.sub_im, Complex.log_im,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]
    ring

theorem log_sub_log_neg_of_im_neg (z : ℂ) (hz : z.im < 0) :
    Complex.log z - Complex.log (-z) = -(Real.pi * I) := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.sub_im, Complex.log_im,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hz, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]
    ring

theorem rectIntegral_inv_zero (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectIntegral a b c d (fun z : ℂ => z⁻¹) = (2 * Real.pi : ℂ) * I := by
  unfold rectIntegral
  rw [integral_inv_horizontal a b (c * I) (by simpa using hc.ne),
    integral_inv_horizontal a b (d * I) (by simpa using hd.ne'),
    integral_inv_vertical_pos c d (b : ℂ) (by simpa using hb),
    integral_inv_vertical_neg c d (a : ℂ) (by simpa using ha)]
  have htop := log_sub_log_neg_of_im_pos ((a : ℂ) + d * I) (by simpa using hd)
  have hbot := log_sub_log_neg_of_im_neg ((a : ℂ) + c * I) (by simpa using hc)
  linear_combination htop - hbot

end QRHShort.CloudBatch.PrimesAPRectAux

noncomputable section
open Complex MeasureTheory Set
open scoped Interval Topology
namespace QRHShort.CloudBatch.PrimesAPRectAux

theorem rectIntegral_inv_translate (a b c d : ℝ) (u : ℂ) :
    rectIntegral a b c d (fun z => (z - u)⁻¹) =
      rectIntegral (a-u.re) (b-u.re) (c-u.im) (d-u.im) (fun z => z⁻¹) := by
  have hh (t : ℝ) :
      (∫ x : ℝ in a..b, ((x : ℂ) + t * I - u)⁻¹) =
        ∫ x : ℝ in a-u.re..b-u.re, ((x : ℂ) + (t-u.im) * I)⁻¹ := by
    have he (x : ℝ) : (x : ℂ) + t * I - u =
        ((x-u.re : ℝ) : ℂ) + (t-u.im) * I := by
      apply Complex.ext <;> simp <;> ring
    simp_rw [he]
    exact intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => ((x:ℂ)+(t-u.im)*I)⁻¹) u.re
  have hv (t : ℝ) :
      (∫ y : ℝ in c..d, ((t : ℂ) + y * I - u)⁻¹) =
        ∫ y : ℝ in c-u.im..d-u.im, (((t-u.re : ℝ) : ℂ) + y * I)⁻¹ := by
    have he (y : ℝ) : (t : ℂ) + y * I - u =
        ((t-u.re : ℝ) : ℂ) + ((y-u.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    simp_rw [he]
    exact intervalIntegral.integral_comp_sub_right
      (fun y : ℝ => (((t-u.re:ℝ):ℂ)+y*I)⁻¹) u.im
  unfold rectIntegral
  rw [hh c, hh d, hv b, hv a]
  simp only [Complex.ofReal_sub]

theorem rectIntegral_inv_sub (a b c d : ℝ) (u : ℂ)
    (hau : a < u.re) (hub : u.re < b) (hcu : c < u.im) (hud : u.im < d) :
    rectIntegral a b c d (fun z => (z-u)⁻¹) = (2*Real.pi : ℂ)*I := by
  rw [rectIntegral_inv_translate]
  exact rectIntegral_inv_zero _ _ _ _ (sub_neg.mpr hau) (sub_pos.mpr hub)
    (sub_neg.mpr hcu) (sub_pos.mpr hud)

def RectIntegrable (a b c d : ℝ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+c*I)) volume a b ∧
  IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+d*I)) volume a b ∧
  IntervalIntegrable (fun y : ℝ => f ((b:ℂ)+y*I)) volume c d ∧
  IntervalIntegrable (fun y : ℝ => f ((a:ℂ)+y*I)) volume c d

theorem mem_rectangle {a b c d x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    (x:ℂ)+y*I ∈ Set.Icc a b ×ℂ Set.Icc c d := by
  change ((x:ℂ)+y*I).re ∈ Set.Icc a b ∧ ((x:ℂ)+y*I).im ∈ Set.Icc c d
  simpa using And.intro hx hy

theorem rectIntegrable_of_continuousOn (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℂ → ℂ) (hf : ContinuousOn f (Set.Icc a b ×ℂ Set.Icc c d)) :
    RectIntegrable a b c d f := by
  have hh (t : ℝ) (ht : t ∈ Set.Icc c d) :
      IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+t*I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
    intro x hx
    rw [uIcc_of_le hab] at hx
    change ((x:ℂ)+t*I).re ∈ Set.Icc a b ∧ ((x:ℂ)+t*I).im ∈ Set.Icc c d
    simpa using And.intro hx ht
  have hv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      IntervalIntegrable (fun y : ℝ => f ((t:ℂ)+y*I)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (continuous_const.add (Complex.continuous_ofReal.mul_const I)).continuousOn
    intro y hy
    rw [uIcc_of_le hcd] at hy
    change ((t:ℂ)+y*I).re ∈ Set.Icc a b ∧ ((t:ℂ)+y*I).im ∈ Set.Icc c d
    simpa using And.intro ht hy
  exact ⟨hh c ⟨le_rfl,hcd⟩, hh d ⟨hcd,le_rfl⟩,
    hv b ⟨hab,le_rfl⟩, hv a ⟨le_rfl,hab⟩⟩

theorem rectIntegral_add (a b c d : ℝ) (f g : ℂ → ℂ)
    (hf : RectIntegrable a b c d f) (hg : RectIntegrable a b c d g) :
    rectIntegral a b c d (fun z => f z + g z) =
      rectIntegral a b c d f + rectIntegral a b c d g := by
  unfold rectIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem rectIntegral_mul_const (a b c d : ℝ) (f : ℂ → ℂ) (v : ℂ) :
    rectIntegral a b c d (fun z => f z * v) = rectIntegral a b c d f * v := by
  simp only [rectIntegral, intervalIntegral.integral_mul_const]
  ring

theorem rectIntegral_eq_zero (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Set.Icc a b ×ℂ Set.Icc c d)) :
    rectIntegral a b c d f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f ((a:ℂ)+c*I) ((b:ℂ)+d*I)
  simpa [rectIntegral, uIcc_of_le hab, uIcc_of_le hcd, smul_eq_mul] using
    h (by simpa [uIcc_of_le hab,uIcc_of_le hcd] using hf)

theorem rectIntegral_congr_boundary (a b c d : ℝ) (f g : ℂ → ℂ)
    (h : ∀ z : ℂ, z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d → f z = g z) :
    rectIntegral a b c d f = rectIntegral a b c d g := by
  have h₁ : (∫ x : ℝ in a..b, f ((x:ℂ)+c*I)) =
      ∫ x : ℝ in a..b, g ((x:ℂ)+c*I) :=
    intervalIntegral.integral_congr (fun x _ => h _ (Or.inr (Or.inr (Or.inl (by simp)))))
  have h₂ : (∫ x : ℝ in a..b, f ((x:ℂ)+d*I)) =
      ∫ x : ℝ in a..b, g ((x:ℂ)+d*I) :=
    intervalIntegral.integral_congr (fun x _ => h _ (Or.inr (Or.inr (Or.inr (by simp)))))
  have h₃ : (∫ y : ℝ in c..d, f ((b:ℂ)+y*I)) =
      ∫ y : ℝ in c..d, g ((b:ℂ)+y*I) :=
    intervalIntegral.integral_congr (fun y _ => h _ (Or.inr (Or.inl (by simp))))
  have h₄ : (∫ y : ℝ in c..d, f ((a:ℂ)+y*I)) =
      ∫ y : ℝ in c..d, g ((a:ℂ)+y*I) :=
    intervalIntegral.integral_congr (fun y _ => h _ (Or.inl (by simp)))
  simp only [rectIntegral, h₁, h₂, h₃, h₄]

theorem rectIntegrable_inv_sub (a b c d : ℝ) (u : ℂ)
    (hau : a < u.re) (hub : u.re < b) (hcu : c < u.im) (hud : u.im < d) :
    RectIntegrable a b c d (fun z => (z-u)⁻¹) := by
  have hh (t : ℝ) (ht : t ≠ u.im) :
      Continuous (fun x : ℝ => ((x:ℂ)+t*I-u)⁻¹) := by
    apply ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀
    intro x hx
    apply ht
    have hi := congrArg Complex.im hx
    simpa using sub_eq_zero.mp (by simpa using hi : t-u.im = 0)
  have hv (t : ℝ) (ht : t ≠ u.re) :
      Continuous (fun y : ℝ => ((t:ℂ)+y*I-u)⁻¹) := by
    apply ((continuous_const.add (Complex.continuous_ofReal.mul_const I)).sub continuous_const).inv₀
    intro y hy
    apply ht
    have hr := congrArg Complex.re hy
    simpa using sub_eq_zero.mp (by simpa using hr : t-u.re = 0)
  exact ⟨(hh c hcu.ne).intervalIntegrable a b,
    (hh d hud.ne').intervalIntegrable a b,
    (hv b hub.ne').intervalIntegrable c d, (hv a hau.ne).intervalIntegrable c d⟩

theorem RectIntegrable.mul_const {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : RectIntegrable a b c d f) (v : ℂ) :
    RectIntegrable a b c d (fun z => f z * v) :=
  ⟨hf.1.mul_const v, hf.2.1.mul_const v, hf.2.2.1.mul_const v, hf.2.2.2.mul_const v⟩

/-- The genuine Cauchy formula on a rectangle, with no residue or contour hypothesis. -/
theorem rectIntegral_cauchy (a b c d : ℝ) (u : ℂ) (K : ℂ → ℂ)
    (hau : a < u.re) (hub : u.re < b) (hcu : c < u.im) (hud : u.im < d)
    (hK : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d, DifferentiableAt ℂ K z) :
    rectIntegral a b c d (fun z => (z-u)⁻¹ * K z) = (2*Real.pi : ℂ)*I*K u := by
  have hab := hau.le.trans hub.le
  have hcd := hcu.le.trans hud.le
  have hu : u ∈ Set.Icc a b ×ℂ Set.Icc c d := ⟨⟨hau.le,hub.le⟩,⟨hcu.le,hud.le⟩⟩
  have hun : Set.Icc a b ×ℂ Set.Icc c d ∈ 𝓝 u := by
    rw [← mem_interior_iff_mem_nhds, interior_reProdIm, interior_Icc, interior_Icc]
    exact ⟨⟨hau,hub⟩,⟨hcu,hud⟩⟩
  let F : ℂ → ℂ := dslope K u
  have hcK : ContinuousOn K (Set.Icc a b ×ℂ Set.Icc c d) :=
    fun z hz => (hK z hz).continuousAt.continuousWithinAt
  have hcF : ContinuousOn F (Set.Icc a b ×ℂ Set.Icc c d) :=
    (continuousOn_dslope hun).2 ⟨hcK,hK u hu⟩
  have hdF : ∀ z ∈ Set.Ioo a b ×ℂ Set.Ioo c d \ {u}, DifferentiableAt ℂ F z := by
    intro z hz
    apply (differentiableAt_dslope_of_ne (by simpa using hz.2 : z ≠ u)).2
    exact hK z ⟨⟨hz.1.1.1.le,hz.1.1.2.le⟩,⟨hz.1.2.1.le,hz.1.2.2.le⟩⟩
  have hzero : rectIntegral a b c d F = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      F ((a:ℂ)+c*I) ((b:ℂ)+d*I) {u} (countable_singleton u)
    simpa [rectIntegral, uIcc_of_le hab, uIcc_of_le hcd, min_eq_left hab,
      max_eq_right hab, min_eq_left hcd, max_eq_right hcd, smul_eq_mul] using
        h (by simpa [uIcc_of_le hab,uIcc_of_le hcd] using hcF)
          (by simpa [min_eq_left hab,max_eq_right hab,min_eq_left hcd,max_eq_right hcd] using hdF)
  have heq : rectIntegral a b c d (fun z => (z-u)⁻¹*K z) =
      rectIntegral a b c d (fun z => F z + (z-u)⁻¹*K u) := by
    apply rectIntegral_congr_boundary
    intro z hz
    have hne : z ≠ u := by
      intro he
      subst z
      rcases hz with he | he | he | he <;> linarith
    dsimp [F]
    rw [dslope_of_ne K hne, slope, smul_eq_mul, vsub_eq_sub]
    ring
  rw [heq, rectIntegral_add _ _ _ _ _ _
    (rectIntegrable_of_continuousOn _ _ _ _ hab hcd F hcF)
    ((rectIntegrable_inv_sub _ _ _ _ u hau hub hcu hud).mul_const (K u)),
    hzero, zero_add, rectIntegral_mul_const, rectIntegral_inv_sub _ _ _ _ u hau hub hcu hud]

theorem rectIntegral_cauchy_of_not_mem (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (u : ℂ) (K : ℂ → ℂ) (hu : u ∉ Set.Icc a b ×ℂ Set.Icc c d)
    (hK : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d, DifferentiableAt ℂ K z) :
    rectIntegral a b c d (fun z => (z-u)⁻¹*K z) = 0 := by
  apply rectIntegral_eq_zero _ _ _ _ hab hcd
  intro z hz
  exact (((differentiableAt_id.sub_const u).inv
    (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hu))).mul (hK z hz)).differentiableWithinAt

end QRHShort.CloudBatch.PrimesAPRectAux

noncomputable section
open Classical Complex MeasureTheory Set
open scoped Interval BigOperators
namespace QRHShort.CloudBatch.PrimesAPRectAux

/-- Either side of a contour-safe point: strictly inside, or outside the closed rectangle. -/
def RectSafe (a b c d : ℝ) (u : ℂ) : Prop :=
  u ∈ Set.Ioo a b ×ℂ Set.Ioo c d ∨ u ∉ Set.Icc a b ×ℂ Set.Icc c d

theorem rectSafe_ne_boundary {a b c d : ℝ} {u z : ℂ}
    (hu : RectSafe a b c d u) (hz : z ∈ Set.Icc a b ×ℂ Set.Icc c d)
    (hb : z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) : z-u ≠ 0 := by
  intro he
  have hzu := sub_eq_zero.mp he
  subst z
  rcases hu with hu | hu
  · rcases hb with hb | hb | hb | hb <;>
      linarith [hu.1.1, hu.1.2, hu.2.1, hu.2.2]
  · exact hu hz

theorem rectIntegrable_cauchy_kernel (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (u : ℂ) (hu : RectSafe a b c d u) (K : ℂ → ℂ)
    (hK : ContinuousOn K (Set.Icc a b ×ℂ Set.Icc c d)) :
    RectIntegrable a b c d (fun z => (z-u)⁻¹*K z) := by
  have hh (t : ℝ) (ht : t = c ∨ t = d) :
      IntervalIntegrable (fun x : ℝ => (((x:ℂ)+t*I)-u)⁻¹*K ((x:ℂ)+t*I))
        volume a b := by
    have ht' : t ∈ Set.Icc c d := by
      rcases ht with rfl | rfl
      · exact ⟨le_rfl,hcd⟩
      · exact ⟨hcd,le_rfl⟩
    have hmem (x : ℝ) (hx : x ∈ [[a,b]]) : (x:ℂ)+t*I ∈ Set.Icc a b ×ℂ Set.Icc c d := by
      rw [uIcc_of_le hab] at hx
      exact mem_rectangle hx ht'
    have hn (x : ℝ) (hx : x ∈ [[a,b]]) : (x:ℂ)+t*I-u ≠ 0 := by
      apply rectSafe_ne_boundary hu (hmem x hx)
      rcases ht with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by simp)))
      · exact Or.inr (Or.inr (Or.inr (by simp)))
    apply ContinuousOn.intervalIntegrable
    exact (((Complex.continuous_ofReal.add continuous_const).sub
      continuous_const).continuousOn.inv₀ hn).mul
        (hK.comp (Complex.continuous_ofReal.add continuous_const).continuousOn hmem)
  have hv (t : ℝ) (ht : t = a ∨ t = b) :
      IntervalIntegrable (fun y : ℝ => (((t:ℂ)+y*I)-u)⁻¹*K ((t:ℂ)+y*I))
        volume c d := by
    have ht' : t ∈ Set.Icc a b := by
      rcases ht with rfl | rfl
      · exact ⟨le_rfl,hab⟩
      · exact ⟨hab,le_rfl⟩
    have hmem (y : ℝ) (hy : y ∈ [[c,d]]) : (t:ℂ)+y*I ∈ Set.Icc a b ×ℂ Set.Icc c d := by
      rw [uIcc_of_le hcd] at hy
      exact mem_rectangle ht' hy
    have hn (y : ℝ) (hy : y ∈ [[c,d]]) : (t:ℂ)+y*I-u ≠ 0 := by
      apply rectSafe_ne_boundary hu (hmem y hy)
      rcases ht with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (by simp))
    apply ContinuousOn.intervalIntegrable
    exact (((continuous_const.add (Complex.continuous_ofReal.mul_const I)).sub
      continuous_const).continuousOn.inv₀ hn).mul
        (hK.comp (continuous_const.add (Complex.continuous_ofReal.mul_const I)).continuousOn hmem)
  exact ⟨hh c (Or.inl rfl), hh d (Or.inr rfl), hv b (Or.inr rfl), hv a (Or.inl rfl)⟩

theorem rectIntegral_sum {ι : Type*} (a b c d : ℝ) (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, RectIntegrable a b c d (F i)) :
    rectIntegral a b c d (fun z => ∑ i ∈ s, F i z) =
      ∑ i ∈ s, rectIntegral a b c d (F i) := by
  classical
  unfold rectIntegral
  rw [intervalIntegral.integral_finset_sum (fun i hi => (hF i hi).1),
    intervalIntegral.integral_finset_sum (fun i hi => (hF i hi).2.1),
    intervalIntegral.integral_finset_sum (fun i hi => (hF i hi).2.2.1),
    intervalIntegral.integral_finset_sum (fun i hi => (hF i hi).2.2.2)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

theorem rectIntegrable_sum {ι : Type*} (a b c d : ℝ) (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, RectIntegrable a b c d (F i)) :
    RectIntegrable a b c d (fun z => ∑ i ∈ s, F i z) := by
  exact ⟨by simpa only [Finset.sum_fn] using IntervalIntegrable.sum s (fun i hi => (hF i hi).1),
    by simpa only [Finset.sum_fn] using IntervalIntegrable.sum s (fun i hi => (hF i hi).2.1),
    by simpa only [Finset.sum_fn] using IntervalIntegrable.sum s (fun i hi => (hF i hi).2.2.1),
    by simpa only [Finset.sum_fn] using IntervalIntegrable.sum s (fun i hi => (hF i hi).2.2.2)⟩

/-- A finite-divisor residue formula proved from the actual rectangle Cauchy theorem. -/
theorem rectIntegral_finite_poles (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (S : Finset ℂ) (w : ℂ → ℂ) (K H : ℂ → ℂ)
    (hS : ∀ u ∈ S, RectSafe a b c d u)
    (hK : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d, DifferentiableAt ℂ K z)
    (hH : DifferentiableOn ℂ H (Set.Icc a b ×ℂ Set.Icc c d)) :
    rectIntegral a b c d (fun z => (∑ u ∈ S, w u/(z-u)*K z) + H z) =
      (2*Real.pi : ℂ)*I * ∑ u ∈ S.filter (fun u => u ∈ Set.Ioo a b ×ℂ Set.Ioo c d), w u*K u := by
  classical
  have hcont : ContinuousOn K (Set.Icc a b ×ℂ Set.Icc c d) :=
    fun z hz => (hK z hz).continuousAt.continuousWithinAt
  have hi (u : ℂ) (hu : u ∈ S) :
      RectIntegrable a b c d (fun z => w u/(z-u)*K z) := by
    have hh := (rectIntegrable_cauchy_kernel a b c d hab hcd u (hS u hu) K hcont).mul_const (w u)
    have he : (fun z : ℂ => w u/(z-u)*K z) =
        (fun z : ℂ => ((z-u)⁻¹*K z)*w u) := by
      funext z
      simp only [div_eq_mul_inv]
      ring
    rw [he]
    exact hh
  have hres (u : ℂ) (hu : u ∈ S) :
      rectIntegral a b c d (fun z => w u/(z-u)*K z) =
        if u ∈ Set.Ioo a b ×ℂ Set.Ioo c d then (2*Real.pi : ℂ)*I*(w u*K u) else 0 := by
    have hr : rectIntegral a b c d (fun z => w u/(z-u)*K z) =
        rectIntegral a b c d (fun z => (z-u)⁻¹*K z) * w u := by
      rw [← rectIntegral_mul_const]
      congr 1
      funext z
      simp only [div_eq_mul_inv]
      ring
    rw [hr]
    rcases hS u hu with hin | hout
    · rw [if_pos hin, rectIntegral_cauchy a b c d u K hin.1.1 hin.1.2 hin.2.1 hin.2.2 hK]
      ring
    · have hn : u ∉ Set.Ioo a b ×ℂ Set.Ioo c d := by
        intro hu'
        exact hout ⟨⟨hu'.1.1.le,hu'.1.2.le⟩,⟨hu'.2.1.le,hu'.2.2.le⟩⟩
      rw [if_neg hn, rectIntegral_cauchy_of_not_mem a b c d hab hcd u K hout hK, zero_mul]
  rw [rectIntegral_add _ _ _ _ _ _ (rectIntegrable_sum _ _ _ _ S _ hi)
    (rectIntegrable_of_continuousOn _ _ _ _ hab hcd H hH.continuousOn),
    rectIntegral_eq_zero _ _ _ _ hab hcd H hH, add_zero, rectIntegral_sum _ _ _ _ S _ hi]
  simp_rw [Finset.sum_congr rfl (fun u hu => hres u hu)]
  rw [Finset.sum_filter]
  simp only [Finset.mul_sum, mul_ite, mul_zero]

end QRHShort.CloudBatch.PrimesAPRectAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators
namespace QRHShort.CloudBatch.PrimesAPRectAux

/-- An unconditional contour shift for an actual entire function: the only zeros
on the right are its own compact divisor, with its actual multiplicities. -/
theorem rectIntegral_entire_logDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (v : ℂ) (hfv : f v ≠ 0) (r a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hrect : Set.Icc a b ×ℂ Set.Icc c d ⊆ closedBall v r)
    (hboundary : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d,
      z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d → f z ≠ 0)
    (K : ℂ → ℂ) (hK : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d, DifferentiableAt ℂ K z) :
    let D := MeromorphicOn.divisor f (closedBall v r)
    let S := (D.finiteSupport (isCompact_closedBall v r)).toFinset
    rectIntegral a b c d (fun z => logDeriv f z * K z) =
      (2*Real.pi : ℂ)*I *
        ∑ u ∈ S.filter (fun u => u ∈ Set.Ioo a b ×ℂ Set.Ioo c d), (D u : ℂ)*K u := by
  let D := MeromorphicOn.divisor f (closedBall v r)
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport :=
    D.finiteSupport (isCompact_closedBall v r)
  let S := hDfin.toFinset
  change rectIntegral a b c d (fun z => logDeriv f z * K z) =
    (2*Real.pi : ℂ)*I * ∑ u ∈ S.filter (fun u => u ∈ Set.Ioo a b ×ℂ Set.Ioo c d), (D u : ℂ)*K u
  have hfa : AnalyticOnNhd ℂ f (closedBall v r) := fun z _ => hf.analyticAt z
  have hDnonneg (z : ℂ) : 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa z
  have hDzero (z : ℂ) (hz : z ∈ Set.Icc a b ×ℂ Set.Icc c d) (hfn : f z ≠ 0) : D z = 0 := by
    dsimp only [D]
    rw [hfa.meromorphicOn.divisor_apply (hrect hz),
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfn]
    rfl
  have hS : ∀ u ∈ S, RectSafe a b c d u := by
    intro u hu
    have hn : D u ≠ 0 := hDfin.mem_toFinset.mp hu
    by_cases huc : u ∈ Set.Icc a b ×ℂ Set.Icc c d
    · left
      have hn₁ : u.re ≠ a := fun he => hn (hDzero u huc (hboundary u huc (Or.inl he)))
      have hn₂ : u.re ≠ b := fun he => hn (hDzero u huc (hboundary u huc (Or.inr (Or.inl he))))
      have hn₃ : u.im ≠ c := fun he => hn (hDzero u huc (hboundary u huc (Or.inr (Or.inr (Or.inl he)))))
      have hn₄ : u.im ≠ d := fun he => hn (hDzero u huc (hboundary u huc (Or.inr (Or.inr (Or.inr he)))))
      exact ⟨⟨lt_of_le_of_ne huc.1.1 hn₁.symm,lt_of_le_of_ne huc.1.2 hn₂⟩,
        ⟨lt_of_le_of_ne huc.2.1 hn₃.symm,lt_of_le_of_ne huc.2.2 hn₄⟩⟩
    · exact Or.inr huc
  obtain ⟨g,hg,hfact,hgn⟩ := PrimesAPGrowthAux.entire_extract_ball_divisor hf v hfv r
  let P : ℂ → ℂ := ∏ᶠ u : ℂ, (fun w : ℂ => w-u) ^ D u
  have heqf : f = P*g := funext hfact
  have hldg (z : ℂ) (hz : z ∈ Set.Icc a b ×ℂ Set.Icc c d) :
      DifferentiableAt ℂ (logDeriv g) z := by
    change DifferentiableAt ℂ (fun w => deriv g w / g w) z
    exact (hg.analyticAt z).deriv.differentiableAt.div (hg z) (hgn z (hrect hz))
  have hH : DifferentiableOn ℂ (fun z => logDeriv g z*K z) (Set.Icc a b ×ℂ Set.Icc c d) :=
    fun z hz => ((hldg z hz).mul (hK z hz)).differentiableWithinAt
  have hident : rectIntegral a b c d (fun z => logDeriv f z*K z) =
      rectIntegral a b c d (fun z => (∑ u ∈ S, (D u:ℂ)/(z-u)*K z) + logDeriv g z*K z) := by
    have hh (z : ℂ) (hz : z ∈ Set.Icc a b ×ℂ Set.Icc c d)
        (hb : z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) :
        logDeriv f z*K z = (∑ u ∈ S, (D u:ℂ)/(z-u)*K z)+logDeriv g z*K z := by
      have hDz := hDzero z hz (hboundary z hz hb)
      have hPn : P z ≠ 0 := Function.FactorizedRational.ne_zero hDz
      have hPa : DifferentiableAt ℂ P z :=
        (Function.FactorizedRational.analyticAt (hDnonneg z)).differentiableAt
      have hsum : (∑ᶠ u : ℂ, (D u:ℂ)/(z-u)) = ∑ u ∈ S, (D u:ℂ)/(z-u) := by
        apply finsum_eq_sum_of_support_subset
        intro u hu
        apply hDfin.mem_toFinset.mpr
        change D u ≠ 0
        intro hd0
        exact hu (by simp only [hd0,Int.cast_zero,zero_div])
      have hld : logDeriv f z = (∑ u ∈ S, (D u:ℂ)/(z-u))+logDeriv g z := by
        calc
          logDeriv f z = logDeriv (P*g) z := congrArg (fun F => logDeriv F z) heqf
          _ = logDeriv P z + logDeriv g z := logDeriv_mul z hPn (hgn z (hrect hz)) hPa (hg z)
          _ = _ := by
            rw [show logDeriv P z = ∑ᶠ u : ℂ, (D u:ℂ)/(z-u) from
              PrimesAPGrowthAux.factorizedProduct_logDeriv hDfin (Function.notMem_support.mpr hDz),hsum]
      rw [hld,add_mul,Finset.sum_mul]
    unfold rectIntegral
    have hbottom := intervalIntegral.integral_congr (μ := volume) (fun x hx => hh ((x:ℂ)+c*I)
      (by rw [uIcc_of_le hab] at hx; exact mem_rectangle hx ⟨le_rfl,hcd⟩)
      (Or.inr (Or.inr (Or.inl (by simp)))))
    have htop := intervalIntegral.integral_congr (μ := volume) (fun x hx => hh ((x:ℂ)+d*I)
      (by rw [uIcc_of_le hab] at hx; exact mem_rectangle hx ⟨hcd,le_rfl⟩)
      (Or.inr (Or.inr (Or.inr (by simp)))))
    have hright := intervalIntegral.integral_congr (μ := volume) (fun y hy => hh ((b:ℂ)+y*I)
      (by rw [uIcc_of_le hcd] at hy; exact mem_rectangle ⟨hab,le_rfl⟩ hy)
      (Or.inr (Or.inl (by simp))))
    have hleft := intervalIntegral.integral_congr (μ := volume) (fun y hy => hh ((a:ℂ)+y*I)
      (by rw [uIcc_of_le hcd] at hy; exact mem_rectangle ⟨le_rfl,hab⟩ hy)
      (Or.inl (by simp)))
    rw [hbottom,htop,hright,hleft]
  rw [hident]
  exact rectIntegral_finite_poles a b c d hab hcd S (fun u => (D u:ℂ)) K
    (fun z => logDeriv g z*K z) hS hK hH

end QRHShort.CloudBatch.PrimesAPRectAux


noncomputable section
open Classical Function
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- A finite divisor with nonnegative multiplicities has its resolvent bounded
by its total multiplicity divided by the actual separation from its support. -/
theorem factorized_resolvent_norm_le {d : ℂ → ℤ} (hd : d.HasFiniteSupport)
    (hnonneg : ∀ u, 0 ≤ d u) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ u ∈ d.support, δ ≤ ‖z-u‖) :
    ‖∑ᶠ u, (d u : ℂ) / (z-u)‖ ≤ ((∑ᶠ u, d u : ℤ) : ℝ) / δ := by
  have hsum : (∑ᶠ u, (d u : ℂ) / (z-u)) =
      ∑ u ∈ hd.toFinset, (d u : ℂ) / (z-u) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    apply hd.mem_toFinset.mpr
    change d u ≠ 0
    intro hz
    exact hu (by change (d u : ℂ) / (z-u) = 0; simp [hz])
  have hmass : (∑ᶠ u, d u) = ∑ u ∈ hd.toFinset, d u := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    exact hd.mem_toFinset.mpr hu
  rw [hsum, hmass, Int.cast_sum, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
  rw [norm_div, Complex.norm_int_of_nonneg (hnonneg u)]
  exact div_le_div_of_nonneg_left (by exact_mod_cast hnonneg u : (0:ℝ) ≤ (d u:ℝ)) hδ
    (hsep u (hd.mem_toFinset.mp hu))

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- The fixed local divisor contains only actual zeros. Separation of the
critical-strip zeros suffices: zeros left of one half have distance at least
one quarter from every point in the contour strip. -/
theorem entire_local_divisor_separation {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf2 : f 2 ≠ 0) (hright : ∀ u, f u=0 → u.re ≤ 1)
    {z : ℂ} {U δ : ℝ} (hzlo : (3:ℝ)/4 ≤ z.re) (hzhi : z.re ≤ 2)
    (hzU : |z.im| ≤ U) (hδ : 0 < δ) (hδhi : δ ≤ 1/4)
    (hsep : ∀ u : ℂ, f u=0 → 1/2 ≤ u.re → u.re ≤ 1 → |u.im| ≤ U+2 →
      δ ≤ ‖z-u‖) :
    f z ≠ 0 ∧ z ∈ closedBall (2+(z.im:ℂ)*Complex.I) (5/4) ∧
      ∀ u ∈ (MeromorphicOn.divisor f
        (closedBall (2+(z.im:ℂ)*Complex.I) (7/4))).support, δ ≤ ‖z-u‖ := by
  have hzn : f z ≠ 0 := by
    intro hz0
    have hh := hsep z hz0 (by linarith) (hright z hz0) (by linarith)
    simp only [sub_self, norm_zero] at hh
    exact hδ.not_ge hh
  have hzb : z ∈ closedBall (2+(z.im:ℂ)*Complex.I) (5/4) := by
    have heq : z-(2+(z.im:ℂ)*Complex.I) = ((z.re-2:ℝ):ℂ) := by
      apply Complex.ext <;> simp
    rw [mem_closedBall, dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨hzn, hzb, ?_⟩
  intro u hu
  let V := closedBall (2+(z.im:ℂ)*Complex.I) (7/4)
  have hfa : AnalyticOnNhd ℂ f V := fun w _ => hf.analyticAt w
  have hfm : MeromorphicOn f (univ : Set ℂ) := fun w _ => (hf.analyticAt w).meromorphicAt
  have hfinite (w : ℂ) : meromorphicOrderAt f w ≠ ⊤ :=
    hfm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ 2) (mem_univ w) (by
        rw [(hf.analyticAt 2).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf2]
        exact WithTop.zero_ne_top)
  have hzero : V ∩ f ⁻¹' {0} = (MeromorphicOn.divisor f V).support :=
    hfa.meromorphicNFOn.zero_set_eq_divisor_support (fun w => hfinite w)
  have hu' : u ∈ V ∩ f ⁻¹' {0} := by rw [hzero]; exact hu
  have hu0 : f u=0 := hu'.2
  by_cases hulow : 1/2 ≤ u.re
  · apply hsep u hu0 hulow (hright u hu0)
    have hn : ‖u-(2+(z.im:ℂ)*Complex.I)‖ ≤ (7/4:ℝ) := by
      simpa only [V, mem_closedBall, dist_eq_norm] using hu'.1
    have hi := (Complex.abs_im_le_norm (u-(2+(z.im:ℂ)*Complex.I))).trans hn
    have him : (u-(2+(z.im:ℂ)*Complex.I)).im = u.im-z.im := by simp
    rw [him] at hi
    calc
      |u.im| = |(u.im-z.im)+z.im| := congrArg abs (by ring)
      _ ≤ |u.im-z.im|+|z.im| := abs_add_le _ _
      _ ≤ 7/4+U := add_le_add hi hzU
      _ ≤ U+2 := by linarith
  · have hnorm := Complex.abs_re_le_norm (z-u)
    rw [Complex.sub_re] at hnorm
    have hr := le_abs_self (z.re-u.re)
    linarith

/-- Actual zero-free input gives a uniform distance from every local zero on
the right Perron line; the divisor is the literal continued L-function's. -/
theorem LFunction_right_divisor_separation
    (hZ : QRHShort.DirichletZeroFreeStatement) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℂ}
    (hzlo : 1 ≤ z.re) (hzhi : z.re ≤ 2) :
    DirichletCharacter.LFunction χ z ≠ 0 ∧
      z ∈ closedBall (2+(z.im:ℂ)*Complex.I) (5/4) ∧
      ∀ u ∈ (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (closedBall (2+(z.im:ℂ)*Complex.I) (7/4))).support,
        (1:ℝ)/12 ≤ ‖z-u‖ := by
  have hroot (u : ℂ) (hu : DirichletCharacter.LFunction χ u=0) : u.re ≤ (11:ℝ)/12 := by
    by_contra! hh
    exact hZ q χ u hh (.inr hχ) hu
  have hf2 : DirichletCharacter.LFunction χ 2 ≠ 0 := hZ q χ 2 (by norm_num) (.inr hχ)
  apply entire_local_divisor_separation (DirichletCharacter.differentiable_LFunction hχ)
    hf2 (fun u hu => (hroot u hu).trans (by norm_num)) (by linarith) hzhi
    (le_refl |z.im|) (by norm_num) (by norm_num)
  intro u hu _ _ _
  have hr := hroot u hu
  have hn := Complex.abs_re_le_norm (z-u)
  rw [Complex.sub_re] at hn
  linarith [le_abs_self (z.re-u.re)]


/-- Quantitative logarithmic-derivative control on any separated contour
point in the fixed strip. Only genuine critical-strip zeros must be avoided. -/
theorem LFunction_separated_logDeriv_le
    (hZ : QRHShort.DirichletZeroFreeStatement) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℂ} {U δ : ℝ}
    (hzlo : (3:ℝ)/4 ≤ z.re) (hzhi : z.re ≤ 2) (hzU : |z.im| ≤ U)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/4)
    (hsep : ∀ u : ℂ, DirichletCharacter.LFunction χ u=0 →
      1/2 ≤ u.re → u.re ≤ 1 → |u.im| ≤ U+2 → δ ≤ ‖z-u‖) :
    DirichletCharacter.LFunction χ z ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤
        (Real.log (32*(q:ℝ)*(|z.im|+4))/Real.log (15/14))/δ +
        96*((1+Real.log 14/Real.log (15/14))*Real.log (32*(q:ℝ)*(|z.im|+4))+1) := by
  have hf := DirichletCharacter.differentiable_LFunction hχ
  have hf2 : DirichletCharacter.LFunction χ 2 ≠ 0 := hZ q χ 2 (by norm_num) (.inr hχ)
  have hright (u : ℂ) (hu : DirichletCharacter.LFunction χ u=0) : u.re ≤ 1 := by
    by_contra! hh
    exact hZ q χ u (by linarith) (.inr hχ) hu
  obtain ⟨hzn, hzb, hdist⟩ := entire_local_divisor_separation hf hf2 hright
    hzlo hzhi hzU hδ hδhi hsep
  refine ⟨hzn, ?_⟩
  let D := MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
    (closedBall (2+(z.im:ℂ)*Complex.I) (7/4))
  have hfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall _ _)
  have hnonneg (u : ℂ) : 0 ≤ D u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
  have hsum := factorized_resolvent_norm_le hfin hnonneg hδ hdist
  have hN := LFunction_local_zero_count_le χ hχ z.im
  have hrem := LFunction_local_logDeriv_remainder_le χ hχ z.im hzb hzn
  calc
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) z -
          ∑ᶠ u : ℂ, (D u:ℂ)/(z-u)‖ + ‖∑ᶠ u : ℂ, (D u:ℂ)/(z-u)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 96*((1+Real.log 14/Real.log (15/14))*Real.log (32*(q:ℝ)*(|z.im|+4))+1) +
        (((∑ᶠ u : ℂ, D u):ℤ):ℝ)/δ := add_le_add hrem hsum
    _ ≤ _ := by
      have hd := div_le_div_of_nonneg_right hN hδ.le
      linarith

/-- On the entire right Perron line the zero-free input supplies the required
separation automatically, so the bound grows only logarithmically in height. -/
theorem LFunction_right_logDeriv_le
    (hZ : QRHShort.DirichletZeroFreeStatement) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℂ}
    (hzlo : 1 ≤ z.re) (hzhi : z.re ≤ 2) :
    ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤
      12*(Real.log (32*(q:ℝ)*(|z.im|+4))/Real.log (15/14)) +
      96*((1+Real.log 14/Real.log (15/14))*Real.log (32*(q:ℝ)*(|z.im|+4))+1) := by
  have hsep (u : ℂ) (hu : DirichletCharacter.LFunction χ u=0)
      (_ : 1/2 ≤ u.re) (_ : u.re ≤ 1) (_ : |u.im| ≤ |z.im|+2) :
      (1:ℝ)/12 ≤ ‖z-u‖ := by
    have hr : u.re ≤ (11:ℝ)/12 := by
      by_contra! hh
      exact hZ q χ u hh (.inr hχ) hu
    have hn := Complex.abs_re_le_norm (z-u)
    rw [Complex.sub_re] at hn
    linarith [le_abs_self (z.re-u.re)]
  have hb := (LFunction_separated_logDeriv_le hZ χ hχ (by linarith) hzhi
    (le_refl |z.im|) (by norm_num : (0:ℝ)<1/12) (by norm_num) hsep).2
  convert hb using 1 <;> ring

end QRHShort.CloudBatch.PrimesAPGrowthAux




noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- The same quantitative separated-contour bound for the genuine entire
regularization of the principal primitive L-function. -/
theorem regularizedZeta_separated_logDeriv_le
    (hZ : QRHShort.DirichletZeroFreeStatement) {z : ℂ} {U δ : ℝ}
    (hzlo : (3:ℝ)/4 ≤ z.re) (hzhi : z.re ≤ 2) (hzU : |z.im| ≤ U)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/4)
    (hsep : ∀ u : ℂ, DirichletCharacter.LFunctionTrivChar₁ 1 u=0 →
      1/2 ≤ u.re → u.re ≤ 1 → |u.im| ≤ U+2 → δ ≤ ‖z-u‖) :
    DirichletCharacter.LFunctionTrivChar₁ 1 z ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) z‖ ≤
        (Real.log (64*(|z.im|+4)^2)/Real.log (15/14))/δ +
        96*((1+Real.log 14/Real.log (15/14))*Real.log (64*(|z.im|+4)^2)+1) := by
  have hf := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hf2 : DirichletCharacter.LFunctionTrivChar₁ 1 2 ≠ 0 :=
    regularizedZeta_ne_zero_right hZ (by norm_num)
  have hright (u : ℂ) (hu : DirichletCharacter.LFunctionTrivChar₁ 1 u=0) : u.re ≤ 1 := by
    by_contra! hh
    exact regularizedZeta_ne_zero_right hZ (by linarith) hu
  obtain ⟨hzn, hzb, hdist⟩ := entire_local_divisor_separation hf hf2 hright
    hzlo hzhi hzU hδ hδhi hsep
  refine ⟨hzn, ?_⟩
  let D := MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1)
    (closedBall (2+(z.im:ℂ)*Complex.I) (7/4))
  have hfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall _ _)
  have hnonneg (u : ℂ) : 0 ≤ D u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
  have hsum := factorized_resolvent_norm_le hfin hnonneg hδ hdist
  have hN := (regularizedZeta_local_estimates z.im).1
  obtain ⟨hc, hcircle⟩ := regularizedZeta_local_norm_data z.im
  have hM : 0 < 16*(|z.im|+4)^2 := by positivity
  have hrem := entire_logDeriv_remainder_le hf hM (by norm_num : (0:ℝ)<1/4)
    hc hcircle hzb hzn
  rw [show 16*(|z.im|+4)^2/(1/4)=64*(|z.im|+4)^2 by ring] at hrem
  have hrem' : ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) z -
      ∑ᶠ u : ℂ, (D u:ℂ)/(z-u)‖ ≤
      96*((1+Real.log 14/Real.log (15/14))*Real.log (64*(|z.im|+4)^2)+1) := by
    refine hrem.trans ?_
    have hh := mul_le_mul_of_nonneg_right hN (Real.log_nonneg (by norm_num : (1:ℝ)≤14))
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤96)
    calc
      _ ≤ Real.log (64*(|z.im|+4)^2) +
          (Real.log (64*(|z.im|+4)^2)/Real.log (15/14))*Real.log 14 + 1 := by linarith
      _ = _ := by ring
  calc
    _ ≤ ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) z -
          ∑ᶠ u : ℂ, (D u:ℂ)/(z-u)‖ + ‖∑ᶠ u : ℂ, (D u:ℂ)/(z-u)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 96*((1+Real.log 14/Real.log (15/14))*Real.log (64*(|z.im|+4)^2)+1) +
        (((∑ᶠ u : ℂ, D u):ℤ):ℝ)/δ := add_le_add hrem' hsum
    _ ≤ _ := by
      have hd := div_le_div_of_nonneg_right hN hδ.le
      linarith

/-- The principal pole contributes at most one on the distant right tails.
The remaining growth is logarithmic in height, uniformly on real parts [1,2]. -/
theorem zeta_right_logDeriv_le (hZ : QRHShort.DirichletZeroFreeStatement)
    {z : ℂ} (hzlo : 1 ≤ z.re) (hzhi : z.re ≤ 2) (hzim : 1 ≤ |z.im|) :
    ‖logDeriv (DirichletCharacter.LFunctionTrivChar 1) z‖ ≤
      12*(Real.log (64*(|z.im|+4)^2)/Real.log (15/14)) +
      96*((1+Real.log 14/Real.log (15/14))*Real.log (64*(|z.im|+4)^2)+1) + 1 := by
  have hsep (u : ℂ) (hu : DirichletCharacter.LFunctionTrivChar₁ 1 u=0)
      (_ : 1/2 ≤ u.re) (_ : u.re ≤ 1) (_ : |u.im| ≤ |z.im|+2) :
      (1:ℝ)/12 ≤ ‖z-u‖ := by
    have hr : u.re ≤ (11:ℝ)/12 := by
      by_contra! hh
      exact regularizedZeta_ne_zero_right hZ hh hu
    have hn := Complex.abs_re_le_norm (z-u)
    rw [Complex.sub_re] at hn
    linarith [le_abs_self (z.re-u.re)]
  obtain ⟨hzn, hb⟩ := regularizedZeta_separated_logDeriv_le hZ (by linarith) hzhi
    (le_refl |z.im|) (by norm_num : (0:ℝ)<1/12) (by norm_num) hsep
  have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hzim
  have hL : DirichletCharacter.LFunctionTrivChar 1 z ≠ 0 := by
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1] at hzn
    exact (mul_ne_zero_iff.mp hzn).2
  have heq : logDeriv (DirichletCharacter.LFunctionTrivChar 1) z =
      logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) z - 1/(z-1) := by
    rw [regularizedZeta_logDeriv_eq hz1 hL]
    ring
  have hpole : ‖(1:ℂ)/(z-1)‖ ≤ 1 := by
    have hn : (1:ℝ) ≤ ‖z-1‖ := by
      have hh := Complex.abs_im_le_norm (z-1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at hh
      exact hzim.trans hh
    rw [norm_div, norm_one]
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  have hh := add_le_add hb hpole
  convert hh using 1 <;> ring

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Local multiplicity counts give an actual finite set of zeros in a
bounded critical strip, with a linear loss in its height. -/
theorem entire_strip_zero_finset {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf2 : f 2 ≠ 0) {U B : ℝ} (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hlocal : ∀ k : ℤ, |(k:ℝ)| ≤ U+2 →
      (((∑ᶠ z : ℂ, MeromorphicOn.divisor f
        (closedBall (2+((k:ℝ):ℂ)*Complex.I) (7/4)) z) : ℤ) : ℝ) ≤ B) :
    ∃ S : Finset ℂ,
      (∀ z : ℂ, z ∈ S ↔ f z=0 ∧ 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ U) ∧
      (S.card:ℝ) ≤ (2*U+5)*B := by
  let N : ℕ := ⌈U+1⌉₊
  let J : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let D (k : ℤ) := MeromorphicOn.divisor f (closedBall (2+((k:ℝ):ℂ)*Complex.I) (7/4))
  have hfin (k : ℤ) : (D k : ℂ → ℤ).HasFiniteSupport := (D k).finiteSupport (isCompact_closedBall _ _)
  let Z (k : ℤ) : Finset ℂ := (hfin k).toFinset
  let S := (J.biUnion Z).filter (fun z : ℂ => 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ U)
  have hNlo : U+1 ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < U+2 := by
    simpa only [show U+1+1=U+2 by ring] using Nat.ceil_lt_add_one (by linarith : 0≤U+1)
  have hfm : MeromorphicOn f (univ:Set ℂ) := fun z _ => (hf.analyticAt z).meromorphicAt
  have hfinit (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ :=
    hfm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ 2) (mem_univ z) (by
        rw [(hf.analyticAt 2).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf2]
        exact WithTop.zero_ne_top)
  have hfa (k : ℤ) : AnalyticOnNhd ℂ f (closedBall (2+((k:ℝ):ℂ)*Complex.I) (7/4)) :=
    fun z _ => hf.analyticAt z
  have hzero (k : ℤ) :
      (closedBall (2+((k:ℝ):ℂ)*Complex.I) (7/4)) ∩ f ⁻¹' {0} = (D k).support :=
    (hfa k).meromorphicNFOn.zero_set_eq_divisor_support (fun z => hfinit z)
  have hnonneg (k : ℤ) (z : ℂ) : 0 ≤ D k z :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hfa k) z
  refine ⟨S, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨hzU, hstrip⟩ := Finset.mem_filter.mp hz
      obtain ⟨k, hk, hzK⟩ := Finset.mem_biUnion.mp hzU
      have hsup := (hfin k).mem_toFinset.mp hzK
      change z ∈ (D k).support at hsup
      rw [← hzero k] at hsup
      exact ⟨hsup.2, hstrip⟩
    · rintro ⟨hz0, hlow, hhigh, him⟩
      let k : ℤ := round z.im
      have hround : |z.im-(k:ℝ)| ≤ 1/2 := abs_sub_round z.im
      have hk : k ∈ J := by
        have hr := abs_le.mp hround
        have hi := abs_le.mp him
        apply Finset.mem_Icc.mpr
        constructor
        · have h : -(N:ℝ) ≤ (k:ℝ) := by linarith
          exact_mod_cast h
        · have h : (k:ℝ) ≤ (N:ℝ) := by linarith
          exact_mod_cast h
      have hball : z ∈ closedBall (2+((k:ℝ):ℂ)*Complex.I) (7/4) := by
        rw [mem_closedBall, dist_eq_norm]
        apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤7/4)).mp
        have hreal : |z.re-2| ≤ 3/2 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hreal2 : (z.re-2)^2 ≤ (3/2:ℝ)^2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hreal
        have him2 : (z.im-(k:ℝ))^2 ≤ (1/2:ℝ)^2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hround
        rw [Complex.sq_norm, Complex.normSq_apply]
        norm_num
        nlinarith
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨k, hk, ?_⟩, hlow, hhigh, him⟩
      apply (hfin k).mem_toFinset.mpr
      change z ∈ (D k).support
      rw [← hzero k]
      exact ⟨hball, hz0⟩
  · have hZcard (k : ℤ) (hk : k ∈ J) : ((Z k).card:ℝ) ≤ B := by
      have hk' := Finset.mem_Icc.mp hk
      have hkr : |(k:ℝ)| ≤ U+2 := by
        apply (abs_le.mpr ⟨?_, ?_⟩)
        · have h : -(N:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk'.1
          linarith
        · have h : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast hk'.2
          linarith
      calc
        _ = ∑ z ∈ Z k, (1:ℝ) := by simp
        _ ≤ ∑ z ∈ Z k, (D k z:ℝ) := by
          apply Finset.sum_le_sum
          intro z hz
          have hn : D k z ≠ 0 := (hfin k).mem_toFinset.mp hz
          have hp : (1:ℤ) ≤ D k z := by have := hnonneg k z; omega
          exact_mod_cast hp
        _ = (((∑ᶠ z : ℂ, D k z):ℤ):ℝ) := by
          rw [factorMultiplicitySum_eq_sum (hfin k)]
          simp only [Z, Int.cast_sum]
        _ ≤ B := hlocal k hkr
    have hJcard : (J.card:ℝ) ≤ 2*U+5 := by
      have hc : J.card = 2*N+1 := by dsimp only [J]; rw [Int.card_Icc]; omega
      rw [hc]
      push_cast
      linarith
    calc
      _ ≤ ((J.biUnion Z).card:ℝ) := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ ∑ k ∈ J, ((Z k).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ J, B := Finset.sum_le_sum hZcard
      _ = (J.card:ℝ)*B := by simp
      _ ≤ (2*U+5)*B := mul_le_mul_of_nonneg_right hJcard hB

theorem LFunction_strip_zero_finset {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {U : ℝ} (hU : 0 ≤ U) :
    ∃ S : Finset ℂ,
      (∀ z : ℂ, z ∈ S ↔ DirichletCharacter.LFunction χ z=0 ∧
        1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ U) ∧
      (S.card:ℝ) ≤ (2*U+5)*
        (Real.log (32*(q:ℝ)*(U+6))/Real.log (15/14)) := by
  have hq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos q)
  have hQ : 1 ≤ 32*(q:ℝ)*(U+6) := by nlinarith
  have hc : DirichletCharacter.LFunction χ 2 ≠ 0 := by
    have hh := LFunction_center_lower χ 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hh
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hh)
  apply entire_strip_zero_finset (DirichletCharacter.differentiable_LFunction hχ) hc hU
    (div_nonneg (Real.log_nonneg hQ) (Real.log_nonneg (by norm_num)))
  intro k hk
  refine (LFunction_local_zero_count_le χ hχ (k:ℝ)).trans ?_
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith : |(k:ℝ)|+4 ≤ U+6) (by positivity)

theorem regularizedZeta_strip_zero_finset {U : ℝ} (hU : 0 ≤ U) :
    ∃ S : Finset ℂ,
      (∀ z : ℂ, z ∈ S ↔ DirichletCharacter.LFunctionTrivChar₁ 1 z=0 ∧
        1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ U) ∧
      (S.card:ℝ) ≤ (2*U+5)*
        (Real.log (64*(U+6)^2)/Real.log (15/14)) := by
  have hQ : 1 ≤ 64*(U+6)^2 := by nlinarith [sq_nonneg U]
  have hc : DirichletCharacter.LFunctionTrivChar₁ 1 2 ≠ 0 := by
    have hh := (regularizedZeta_local_norm_data 0).1
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hh
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hh)
  apply entire_strip_zero_finset (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1) hc hU
    (div_nonneg (Real.log_nonneg hQ) (Real.log_nonneg (by norm_num)))
  intro k hk
  refine ((regularizedZeta_local_estimates (k:ℝ)).1).trans ?_
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  apply Real.log_le_log (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤64)
  exact (sq_le_sq₀ (by positivity) (by linarith : (0:ℝ)≤U+6)).mpr (by linarith)

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- A finite set cannot occupy all of a grid of one more points, even after
thickening each of its points by a quarter of the grid spacing. -/
theorem finite_grid_avoidance (S : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Icc a b, ∀ s ∈ S,
      (b-a) / (4 * ((S.card : ℝ)+1)) ≤ |t-s| := by
  let δ : ℝ := (b-a) / ((S.card : ℝ)+1)
  have hden : 0 < (S.card : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hab) hden
  have hwidth : ((S.card : ℝ)+1) * δ = b-a := by
    dsimp [δ]
    field_simp [ne_of_gt hden]
  let point : Fin (S.card+1) → ℝ := fun i => a + (i.val : ℝ) * δ
  have hpoint (i : Fin (S.card+1)) : point i ∈ Set.Icc a b := by
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hi1 : (i.val : ℝ) ≤ (S.card : ℝ)+1 := by
      exact_mod_cast (le_of_lt i.isLt)
    constructor
    · dsimp [point]
      exact le_add_of_nonneg_right (mul_nonneg hi0 hδ.le)
    · have hmul := mul_le_mul_of_nonneg_right hi1 hδ.le
      dsimp [point]
      nlinarith
  have hex : ∃ i : Fin (S.card+1), ∀ s ∈ S, δ/4 ≤ |point i-s| := by
    by_contra h
    push_neg at h
    choose f hfmem hfclose using h
    let fsub : Fin (S.card+1) → S := fun i => ⟨f i, hfmem i⟩
    have hinj : Function.Injective fsub := by
      intro i j heq
      have hf : f i = f j := congrArg Subtype.val heq
      have hsmall : |point i-point j| < δ/2 := by
        calc
          |point i-point j| = |(point i-f i)+(f i-point j)| := by congr 1 <;> ring
          _ ≤ |point i-f i| + |f i-point j| := abs_add_le _ _
          _ = |point i-f i| + |point j-f j| := by rw [hf, abs_sub_comm (f j)]
          _ < δ/2 := by linarith [hfclose i, hfclose j]
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · have hcast : (i.val : ℝ)+1 ≤ (j.val : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hij)
        have hgap : δ ≤ point j-point i := by
          have hmul := mul_le_mul_of_nonneg_right hcast hδ.le
          dsimp [point]
          nlinarith
        have hlow := (abs_lt.mp hsmall).1
        linarith
      · have hcast : (j.val : ℝ)+1 ≤ (i.val : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hji)
        have hgap : δ ≤ point i-point j := by
          have hmul := mul_le_mul_of_nonneg_right hcast hδ.le
          dsimp [point]
          nlinarith
        have hupp := (abs_lt.mp hsmall).2
        linarith
    have hcard := Fintype.card_le_of_injective fsub hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨point i, hpoint i, ?_⟩
  intro s hs
  have heq : (b-a) / (4 * ((S.card : ℝ)+1)) = δ/4 := by
    dsimp [δ]
    field_simp [ne_of_gt hden]
    <;> ring
  rw [heq]
  exact hi s hs

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem log_cubic_tail_pointwise {Q T t : ℝ} (hQ : 1 ≤ Q) (hT : 1 ≤ T)
    (ht : T ≤ t) :
    0 ≤ (Real.log (Q*(t+4))+1)/t^3 ∧
      (Real.log (Q*(t+4))+1)/t^3 ≤ (Real.log (Q*(T+4))+1)/(T*t^2) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hA : 1 ≤ Q*(T+4) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Q-1) (by linarith : 0 ≤ T+4)]
  have hB : 1 ≤ Q*(t+4) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Q-1) (by linarith : 0 ≤ t+4)]
  have hlogA : 0 ≤ Real.log (Q*(T+4)) := Real.log_nonneg hA
  have hlogB : 0 ≤ Real.log (Q*(t+4)) := Real.log_nonneg hB
  let r : ℝ := t/T
  have hr : 1 ≤ r := (le_div_iff₀ hT0).mpr (by linarith)
  have hr0 : 0 < r := by linarith
  have htr : t = T*r := by dsimp only [r]; field_simp [hT0.ne']
  have hmult : Q*(t+4) ≤ (Q*(T+4))*r := by
    have he : t+4 ≤ (T+4)*r := by nlinarith
    convert mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ Q) using 1 <;> ring
  have hl : Real.log (Q*(t+4)) ≤ Real.log (Q*(T+4)) + Real.log r := by
    rw [← Real.log_mul (by linarith : Q*(T+4) ≠ 0) hr0.ne']
    exact Real.log_le_log (by linarith) hmult
  have hnum : Real.log (Q*(t+4))+1 ≤ (Real.log (Q*(T+4))+1)*r := by
    have hlr := Real.log_le_sub_one_of_pos hr0
    nlinarith [mul_nonneg hlogA (by linarith : 0 ≤ r-1)]
  constructor
  · positivity
  · calc
      (Real.log (Q*(t+4))+1)/t^3 ≤
          ((Real.log (Q*(T+4))+1)*r)/t^3 :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = (Real.log (Q*(T+4))+1)/(T*t^2) := by
        dsimp only [r]
        field_simp [hT0.ne', ht0.ne']
        <;> ring

/-- The logarithmic cubic tail is truly integrable, with an explicit bound
uniform in the two scale parameters. -/
theorem log_cubic_tail_integral_le {Q T : ℝ} (hQ : 1 ≤ Q) (hT : 1 ≤ T) :
    IntegrableOn (fun t : ℝ => (Real.log (Q*(t+4))+1)/t^3) (Ioi T) ∧
      (∫ t : ℝ in Ioi T, (Real.log (Q*(t+4))+1)/t^3) ≤
        (Real.log (Q*(T+4))+1)/T^2 := by
  have hT0 : 0 < T := by linarith
  let C : ℝ := Real.log (Q*(T+4))+1
  let f : ℝ → ℝ := fun t => (Real.log (Q*(t+4))+1)/t^3
  let g : ℝ → ℝ := fun t => (C/T)*t^(-2 : ℝ)
  have hiG : IntegrableOn g (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT0).const_mul (C/T)
  have hGeq (t : ℝ) (ht : T < t) : g t = C/(T*t^2) := by
    dsimp only [g]
    rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
    field_simp [hT0.ne', (hT0.trans ht).ne']
    <;> ring
  have hmf : Measurable f := by dsimp only [f]; fun_prop
  have hiF : IntegrableOn f (Ioi T) := by
    apply hiG.mono' hmf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpoint := log_cubic_tail_pointwise hQ hT ht.le
    rw [Real.norm_eq_abs, abs_of_nonneg hpoint.1, hGeq t ht]
    exact hpoint.2
  refine ⟨hiF, ?_⟩
  calc
    (∫ t : ℝ in Ioi T, f t) ≤ ∫ t : ℝ in Ioi T, g t := by
      apply integral_mono_ae hiF hiG
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hGeq t ht]
      exact (log_cubic_tail_pointwise hQ hT ht.le).2
    _ = C/T^2 := by
      dsimp only [g]
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT0]
      norm_num [Real.rpow_neg_one]
      field_simp
      <;> ring

end QRHShort.CloudBatch.PrimesAPGrowthAux


noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPExplicitAux

def quadraticPerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x:ℂ)^(s+2)/(s*(s+1)*(s+2))

def quadraticPerronIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction χ) s * quadraticPerronKernel x s

theorem quadraticPerronKernel_scale {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x:ℂ)^2 * (((1/x:ℝ):ℂ)^(-s)) = (x:ℂ)^(s+2) := by
  have hxn : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.ofReal_div,Complex.ofReal_one,one_div,
    Complex.inv_cpow_ofReal_nonneg hx.le,Complex.cpow_neg,inv_inv,
    Complex.cpow_add _ _ hxn]
  have ht : (x:ℂ)^(2:ℂ) = (x:ℂ)^2 := by
    simpa using Complex.cpow_natCast (x:ℂ) 2
  rw [ht]
  ring

theorem quadraticPerronKernel_differentiableAt {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (quadraticPerronKernel x) s := by
  have h0 : s ≠ 0 := by intro h; subst s; simp at hs
  have h1 : s+1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  have h2 : s+2 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  exact ((differentiableAt_id.add_const (2:ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).div
      ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
        (differentiableAt_id.add_const 2)) (mul_ne_zero (mul_ne_zero h0 h1) h2)

theorem quadraticPerronKernel_one (x : ℝ) : quadraticPerronKernel x 1 = (x:ℂ)^3/6 := by
  unfold quadraticPerronKernel
  norm_num [show (x:ℂ)^(3:ℂ) = (x:ℂ)^3 by simpa using Complex.cpow_natCast (x:ℂ) 3]

/-- Literal Perron, written with the actual entire power kernel and real height measure. -/
theorem mangoldt_quadraticPrefix_vertical {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {c x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    Integrable (fun t : ℝ => quadraticPerronIntegrand χ x ((c:ℂ)+t*I)) ∧
    PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n) x =
      (1/(2*Real.pi):ℂ) * ∫ t : ℝ, quadraticPerronIntegrand χ x ((c:ℂ)+t*I) := by
  obtain ⟨hint,hperron⟩ := PrimesAPGrowthAux.mangoldt_quadraticPrefix_perron χ hc hx
  let G : ℝ → ℂ := fun t => (((1/x:ℝ):ℂ)^(-((c:ℂ)+t*I))) *
    (-logDeriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I) /
      (((c:ℂ)+t*I)*((c:ℂ)+t*I+1)*((c:ℂ)+t*I+2)))
  have he (t : ℝ) : quadraticPerronIntegrand χ x ((c:ℂ)+t*I) = (x:ℂ)^2 * G t := by
    dsimp only [quadraticPerronIntegrand,quadraticPerronKernel,G]
    rw [← quadraticPerronKernel_scale hx]
    ring
  constructor
  · simp_rw [he]
    exact hint.const_mul ((x:ℂ)^2)
  · rw [hperron]
    unfold mellinInv
    simp_rw [he]
    rw [integral_const_mul]
    change (x:ℂ)^2 * (((1/(2*Real.pi):ℝ):ℂ) * (∫ t : ℝ, G t)) = _
    push_cast
    ring

end QRHShort.CloudBatch.PrimesAPExplicitAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology
namespace QRHShort.CloudBatch.PrimesAPExplicitAux
open PrimesAPRectAux

def contourBoundary (a c T : ℝ) : Set ℂ :=
  {z | z ∈ Set.Icc a c ×ℂ Set.Icc (-T) T ∧
    (z.re = a ∨ z.re = c ∨ z.im = -T ∨ z.im = T)}

def rectangleZeroSum (f : ℂ → ℂ) (x a c T : ℝ) : ℂ :=
  let D := MeromorphicOn.divisor f (closedBall (2:ℂ) (T+3))
  let S := (D.finiteSupport (isCompact_closedBall (2:ℂ) (T+3))).toFinset
  ∑ u ∈ S.filter (fun u => u ∈ Set.Ioo a c ×ℂ Set.Ioo (-T) T),
    (D u:ℂ)*quadraticPerronKernel x u

theorem rectangle_subset_disk {a c T : ℝ} (ha : 0 ≤ a) (hc : c ≤ 2) :
    Set.Icc a c ×ℂ Set.Icc (-T) T ⊆ closedBall (2:ℂ) (T+3) := by
  intro z hz
  change dist z (2:ℂ) ≤ T+3
  rw [dist_eq_norm]
  have hr : |z.re-2| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩
  have hi : |z.im| ≤ T := abs_le.mpr hz.2
  have h := Complex.norm_le_abs_re_add_abs_im (z-2)
  norm_num at h
  linarith

theorem rectIntegral_congr_on_boundary {a c T : ℝ} (hac : a ≤ c) (hT : 0 ≤ T)
    (F G : ℂ → ℂ) (he : ∀ z ∈ contourBoundary a c T, F z = G z) :
    rectIntegral a c (-T) T F = rectIntegral a c (-T) T G := by
  have ht : -T ≤ T := by linarith
  have hb := intervalIntegral.integral_congr (μ := volume) (fun t hx =>
    he ((t:ℂ)+(-T)*I) ⟨by rw [Set.uIcc_of_le hac] at hx; simpa only [Complex.ofReal_neg] using mem_rectangle hx ⟨le_rfl,ht⟩,
      Or.inr (Or.inr (Or.inl (by simp)))⟩)
  have hu := intervalIntegral.integral_congr (μ := volume) (fun t hx =>
    he ((t:ℂ)+T*I) ⟨by rw [Set.uIcc_of_le hac] at hx; exact mem_rectangle hx ⟨ht,le_rfl⟩,
      Or.inr (Or.inr (Or.inr (by simp)))⟩)
  have hr := intervalIntegral.integral_congr (μ := volume) (fun t hx =>
    he ((c:ℂ)+t*I) ⟨by rw [Set.uIcc_of_le ht] at hx; exact mem_rectangle ⟨hac,le_rfl⟩ hx,
      Or.inr (Or.inl (by simp))⟩)
  have hl := intervalIntegral.integral_congr (μ := volume) (fun t hx =>
    he ((a:ℂ)+t*I) ⟨by rw [Set.uIcc_of_le ht] at hx; exact mem_rectangle ⟨le_rfl,hac⟩ hx,
      Or.inl (by simp)⟩)
  unfold rectIntegral
  simp only [Complex.ofReal_neg]
  rw [hb,hu,hr,hl]

theorem rectIntegrable_of_continuousAt_boundary {a c T : ℝ} (hac : a ≤ c) (hT : 0 ≤ T)
    (F : ℂ → ℂ) (hF : ∀ z ∈ contourBoundary a c T, ContinuousAt F z) :
    RectIntegrable a c (-T) T F := by
  have ht : -T ≤ T := by linarith
  have hh (v : ℝ) (hv : v = -T ∨ v = T) :
      IntervalIntegrable (fun t : ℝ => F ((t:ℂ)+v*I)) volume a c := by
    apply ContinuousOn.intervalIntegrable
    intro t ht'
    rw [Set.uIcc_of_le hac] at ht'
    have hvm : v ∈ Set.Icc (-T) T := by
      rcases hv with rfl | rfl
      · exact ⟨le_rfl,ht⟩
      · exact ⟨ht,le_rfl⟩
    have hbd : (t:ℂ)+v*I ∈ contourBoundary a c T := by
      refine ⟨mem_rectangle ht' hvm,?_⟩
      rcases hv with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by simp)))
      · exact Or.inr (Or.inr (Or.inr (by simp)))
    have hcurve : ContinuousAt (fun u : ℝ => (u:ℂ)+v*I) t :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    exact ((hF _ hbd).comp_of_eq hcurve rfl).continuousWithinAt
  have hv (v : ℝ) (hv : v = a ∨ v = c) :
      IntervalIntegrable (fun t : ℝ => F ((v:ℂ)+t*I)) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht'
    rw [Set.uIcc_of_le ht] at ht'
    have hvm : v ∈ Set.Icc a c := by
      rcases hv with rfl | rfl
      · exact ⟨le_rfl,hac⟩
      · exact ⟨hac,le_rfl⟩
    have hbd : (v:ℂ)+t*I ∈ contourBoundary a c T := by
      refine ⟨mem_rectangle hvm ht',?_⟩
      rcases hv with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (by simp))
    have hcurve : ContinuousAt (fun u : ℝ => (v:ℂ)+u*I) t :=
      (continuous_const.add (Complex.continuous_ofReal.mul_const I)).continuousAt
    exact ((hF _ hbd).comp_of_eq hcurve rfl).continuousWithinAt
  exact ⟨hh (-T) (Or.inl rfl),hh T (Or.inr rfl),hv c (Or.inr rfl),hv a (Or.inl rfl)⟩

theorem rectIntegral_neg (a c T : ℝ) (F : ℂ → ℂ) :
    rectIntegral a c (-T) T (fun z => -F z) = -rectIntegral a c (-T) T F := by
  simp only [rectIntegral,intervalIntegral.integral_neg]
  ring

theorem rectIntegral_sub (a c T : ℝ) (F G : ℂ → ℂ)
    (hF : RectIntegrable a c (-T) T F) (hG : RectIntegrable a c (-T) T G) :
    rectIntegral a c (-T) T (fun z => F z-G z) =
      rectIntegral a c (-T) T F - rectIntegral a c (-T) T G := by
  unfold rectIntegral
  rw [intervalIntegral.integral_sub hF.1 hG.1,
    intervalIntegral.integral_sub hF.2.1 hG.2.1,
    intervalIntegral.integral_sub hF.2.2.1 hG.2.2.1,
    intervalIntegral.integral_sub hF.2.2.2 hG.2.2.2]
  ring

theorem integral_split_height {F : ℝ → ℂ} (hF : Integrable F) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ, F t) = (∫ t : ℝ in -T..T, F t) + ∫ t : ℝ in {t | T < |t|}, F t := by
  have hs : (Set.Icc (-T) T)ᶜ = {t : ℝ | T < |t|} := by
    ext t
    simp only [Set.mem_compl_iff,Set.mem_Icc,Set.mem_setOf_eq,← abs_le,not_le]
  have he := integral_add_compl (μ := volume) (s := Set.Icc (-T) T) measurableSet_Icc hF
  rw [hs,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at he
  exact he.symm

/-- The horizontal sign and the real-height normalization follow algebraically
from the counterclockwise rectangle, rather than being extra formula assumptions. -/
theorem perron_rectangle_shift (F : ℂ → ℂ) (P R : ℂ) (a c T : ℝ) (hT : 0 ≤ T)
    (hF : Integrable (fun t : ℝ => F ((c:ℂ)+t*I)))
    (hP : P = (1/(2*Real.pi):ℂ) * ∫ t : ℝ, F ((c:ℂ)+t*I))
    (hR : rectIntegral a c (-T) T F = (2*Real.pi:ℂ)*I*R) :
    P = R + (1/(2*Real.pi):ℂ) * (∫ t : ℝ in -T..T, F ((a:ℂ)+t*I)) +
      (I/(2*Real.pi):ℂ) * ((∫ u : ℝ in a..c, F ((u:ℂ)+(-T)*I)) -
        (∫ u : ℝ in a..c, F ((u:ℂ)+T*I))) +
      (1/(2*Real.pi):ℂ) * ∫ t : ℝ in {t | T < |t|}, F ((c:ℂ)+t*I) := by
  have hv : (∫ t : ℝ in -T..T, F ((c:ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((a:ℂ)+t*I)) +
      I*((∫ u : ℝ in a..c, F ((u:ℂ)+(-T)*I)) -
        (∫ u : ℝ in a..c, F ((u:ℂ)+T*I))) + (2*Real.pi:ℂ)*R := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      I*(∫ t : ℝ in -T..T, F ((c:ℂ)+t*I)) =
          (2*Real.pi:ℂ)*I*R -
          ((∫ u : ℝ in a..c, F ((u:ℂ)+(-T)*I)) - (∫ u : ℝ in a..c, F ((u:ℂ)+T*I))) +
          I*(∫ t : ℝ in -T..T, F ((a:ℂ)+t*I)) := by
        dsimp only [rectIntegral] at hR
        simp only [Complex.ofReal_neg] at hR
        linear_combination hR
      _ = _ := by simp only [mul_add,mul_sub,← mul_assoc,Complex.I_mul_I]; ring
  rw [hP,integral_split_height hF hT,hv]
  generalize (∫ t : ℝ in -T..T, F ((a:ℂ)+t*I)) = L
  generalize (∫ u : ℝ in a..c, F ((u:ℂ)+(-T)*I)) = B
  generalize (∫ u : ℝ in a..c, F ((u:ℂ)+T*I)) = U
  generalize (∫ t : ℝ in {t | T < |t|}, F ((c:ℂ)+t*I)) = E
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp]
  <;> ring

end QRHShort.CloudBatch.PrimesAPExplicitAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology
namespace QRHShort.CloudBatch.PrimesAPExplicitAux
open PrimesAPRectAux

/-- All three errors are literal contour or set integrals, with their exact normalizations. -/
def contourError (F : ℂ → ℂ) (a c T : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ) * (∫ t : ℝ in -T..T, F ((a:ℂ)+t*I)) +
  (I/(2*Real.pi):ℂ) * ((∫ u : ℝ in a..c, F ((u:ℂ)+(-T)*I)) -
    (∫ u : ℝ in a..c, F ((u:ℂ)+T*I))) +
  (1/(2*Real.pi):ℂ) * ∫ t : ℝ in {t | T < |t|}, F ((c:ℂ)+t*I)

theorem logDeriv_differentiableAt_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : ℂ} (hs : f s ≠ 0) : DifferentiableAt ℂ (logDeriv f) s := by
  change DifferentiableAt ℂ (fun z => deriv f z / f z) s
  exact (hf.analyticAt s).deriv.differentiableAt.div (hf s) hs

theorem rectIntegrable_logDeriv_kernel {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x a c T : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a ≤ c) (hT : 0 ≤ T)
    (hb : ∀ z ∈ contourBoundary a c T, f z ≠ 0) :
    RectIntegrable a c (-T) T (fun z => logDeriv f z * quadraticPerronKernel x z) := by
  apply rectIntegrable_of_continuousAt_boundary hac hT
  intro z hz
  exact ((logDeriv_differentiableAt_of_entire hf (hb z hz)).mul
    (quadraticPerronKernel_differentiableAt hx (ha.trans_le hz.1.1.1))).continuousAt

theorem entire_rect_kernel_identity {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf2 : f 2 ≠ 0)
    {x a c T : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a ≤ c) (hc : c ≤ 2) (hT : 0 ≤ T)
    (hb : ∀ z ∈ contourBoundary a c T, f z ≠ 0) :
    rectIntegral a c (-T) T (fun z => logDeriv f z*quadraticPerronKernel x z) =
      (2*Real.pi:ℂ)*I*rectangleZeroSum f x a c T := by
  exact rectIntegral_entire_logDeriv hf 2 hf2 (T+3) a c (-T) T hac (by linarith)
    (rectangle_subset_disk ha.le hc) (fun z hz hbd => hb z ⟨hz,hbd⟩)
    (quadraticPerronKernel x) (fun z hz => quadraticPerronKernel_differentiableAt hx (ha.trans_le hz.1.1))

/-- A finite-height explicit formula for the literal nonprincipal L-function.
Neither Perron inversion nor a residue formula is assumed here. -/
theorem nonprincipal_quadratic_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x a c T : ℝ} (hx : 0 < x) (ha : 0 < a) (ha1 : a < 1)
    (hc : 1 < c) (hc2 : c ≤ 2) (hT : 0 < T)
    (hb : ∀ z ∈ contourBoundary a c T, DirichletCharacter.LFunction χ z ≠ 0) :
    Integrable (fun t : ℝ => quadraticPerronIntegrand χ x ((c:ℂ)+t*I)) ∧
    RectIntegrable a c (-T) T (quadraticPerronIntegrand χ x) ∧
    PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n) x =
      -rectangleZeroSum (DirichletCharacter.LFunction χ) x a c T +
        contourError (quadraticPerronIntegrand χ x) a c T := by
  have hac : a ≤ c := ha1.le.trans hc.le
  have hf : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hf2 : DirichletCharacter.LFunction χ 2 ≠ 0 := by
    have hn : (1/4:ℝ) ≤ ‖DirichletCharacter.LFunction χ 2‖ := by
      simpa using PrimesAPGrowthAux.LFunction_center_lower χ 0
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hn)
  have hlog := entire_rect_kernel_identity hf hf2 hx ha hac hc2 hT.le hb
  have hres : rectIntegral a c (-T) T (quadraticPerronIntegrand χ x) =
      (2*Real.pi:ℂ)*I*(-rectangleZeroSum (DirichletCharacter.LFunction χ) x a c T) := by
    calc
      _ = -rectIntegral a c (-T) T
          (fun z => logDeriv (DirichletCharacter.LFunction χ) z*quadraticPerronKernel x z) := by
        change rectIntegral a c (-T) T
          (fun z => -logDeriv (DirichletCharacter.LFunction χ) z*quadraticPerronKernel x z) = _
        simpa only [neg_mul] using
          rectIntegral_neg a c T (fun z => logDeriv (DirichletCharacter.LFunction χ) z*quadraticPerronKernel x z)
      _ = _ := by rw [hlog]; ring
  obtain ⟨hint,hperron⟩ := mangoldt_quadraticPrefix_vertical χ hc hx
  refine ⟨hint,?_,?_⟩
  · apply rectIntegrable_of_continuousAt_boundary hac hT.le
    intro z hz
    exact (((logDeriv_differentiableAt_of_entire hf (hb z hz)).neg).mul
      (quadraticPerronKernel_differentiableAt hx (ha.trans_le hz.1.1.1))).continuousAt
  · simpa only [contourError,add_assoc] using
      perron_rectangle_shift (quadraticPerronIntegrand χ x) _ _ a c T hT.le hint hperron hres

end QRHShort.CloudBatch.PrimesAPExplicitAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology
namespace QRHShort.CloudBatch.PrimesAPExplicitAux
open PrimesAPRectAux

theorem contourBoundary_ne_one {a c T : ℝ} (ha : a < 1) (hc : 1 < c) (hT : 0 < T)
    {z : ℂ} (hz : z ∈ contourBoundary a c T) : z ≠ 1 := by
  intro he
  subst z
  rcases hz.2 with h | h | h | h <;> norm_num at h <;> linarith

theorem LFunction_analyticAt_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (by simpa using hz))).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds (by simpa using hs))

theorem principal_ne_zero_of_regularized {s : ℂ} (hs : s ≠ 1)
    (hZ : DirichletCharacter.LFunctionTrivChar₁ 1 s ≠ 0) :
    DirichletCharacter.LFunctionTrivChar 1 s ≠ 0 := by
  intro hL
  apply hZ
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs,hL,mul_zero]

theorem principal_integrand_decomposition {x : ℝ} {s : ℂ} (hs : s ≠ 1)
    (hZ : DirichletCharacter.LFunctionTrivChar₁ 1 s ≠ 0) :
    quadraticPerronIntegrand (1 : DirichletCharacter ℂ 1) x s =
      (s-1)⁻¹*quadraticPerronKernel x s -
        logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) s * quadraticPerronKernel x s := by
  have hL := principal_ne_zero_of_regularized hs hZ
  rw [PrimesAPGrowthAux.regularizedZeta_logDeriv_eq hs hL]
  change -logDeriv (DirichletCharacter.LFunctionTrivChar 1) s*quadraticPerronKernel x s = _
  simp only [one_div]
  ring

/-- The primitive principal explicit formula uses the genuine entire
pole-removed zeta function and produces the exact main term x^3/6. -/
theorem principal_quadratic_explicit {x a c T : ℝ}
    (hx : 0 < x) (ha : 0 < a) (ha1 : a < 1) (hc : 1 < c) (hc2 : c ≤ 2) (hT : 0 < T)
    (hb : ∀ z ∈ contourBoundary a c T, DirichletCharacter.LFunctionTrivChar₁ 1 z ≠ 0) :
    Integrable (fun t : ℝ => quadraticPerronIntegrand (1 : DirichletCharacter ℂ 1) x ((c:ℂ)+t*I)) ∧
    RectIntegrable a c (-T) T (quadraticPerronIntegrand (1 : DirichletCharacter ℂ 1) x) ∧
    PrimesAPAux.quadraticPrefix
        (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*(1 : DirichletCharacter ℂ 1) n) x =
      (x:ℂ)^3/6 - rectangleZeroSum (DirichletCharacter.LFunctionTrivChar₁ 1) x a c T +
        contourError (quadraticPerronIntegrand (1 : DirichletCharacter ℂ 1) x) a c T := by
  have hac : a ≤ c := ha1.le.trans hc.le
  have hheight : -T ≤ T := by linarith
  have hf := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hf2 : DirichletCharacter.LFunctionTrivChar₁ 1 2 ≠ 0 := by
    have hn : (1/4:ℝ) ≤ ‖DirichletCharacter.LFunctionTrivChar₁ 1 2‖ := by
      simpa using (PrimesAPGrowthAux.regularizedZeta_local_norm_data 0).1
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hn)
  have hK : ∀ z ∈ Set.Icc a c ×ℂ Set.Icc (-T) T, DifferentiableAt ℂ (quadraticPerronKernel x) z :=
    fun z hz => quadraticPerronKernel_differentiableAt hx (ha.trans_le hz.1.1)
  have hKc : ContinuousOn (quadraticPerronKernel x) (Set.Icc a c ×ℂ Set.Icc (-T) T) :=
    fun z hz => (hK z hz).continuousAt.continuousWithinAt
  have hOne : (1:ℂ) ∈ Set.Ioo a c ×ℂ Set.Ioo (-T) T :=
    ⟨⟨by simpa using ha1,by simpa using hc⟩,
      ⟨by simpa using neg_lt_zero.mpr hT,by simpa using hT⟩⟩
  have hpole := rectIntegral_cauchy a c (-T) T 1 (quadraticPerronKernel x)
    hOne.1.1 hOne.1.2 hOne.2.1 hOne.2.2 hK
  have hpolei := rectIntegrable_cauchy_kernel a c (-T) T hac hheight 1
    (Or.inl hOne) (quadraticPerronKernel x) hKc
  have hregulari := rectIntegrable_logDeriv_kernel hf hx ha hac hT.le hb
  have hregular := entire_rect_kernel_identity hf hf2 hx ha hac hc2 hT.le hb
  have hres : rectIntegral a c (-T) T
      (quadraticPerronIntegrand (1 : DirichletCharacter ℂ 1) x) =
      (2*Real.pi:ℂ)*I*((x:ℂ)^3/6 -
        rectangleZeroSum (DirichletCharacter.LFunctionTrivChar₁ 1) x a c T) := by
    calc
      _ = rectIntegral a c (-T) T (fun s => (s-1)⁻¹*quadraticPerronKernel x s -
          logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) s*quadraticPerronKernel x s) := by
        apply rectIntegral_congr_on_boundary hac hT.le
        intro z hz
        exact principal_integrand_decomposition (contourBoundary_ne_one ha1 hc hT hz) (hb z hz)
      _ = _ := by
        rw [rectIntegral_sub _ _ _ _ _ hpolei hregulari,hpole,hregular,quadraticPerronKernel_one]
        ring
  obtain ⟨hint,hperron⟩ := mangoldt_quadraticPrefix_vertical (1 : DirichletCharacter ℂ 1) hc hx
  refine ⟨hint,?_,?_⟩
  · apply rectIntegrable_of_continuousAt_boundary hac hT.le
    intro z hz
    have hzn := contourBoundary_ne_one ha1 hc hT hz
    have hLn := principal_ne_zero_of_regularized hzn (hb z hz)
    have hLa := LFunction_analyticAt_ne_one (1 : DirichletCharacter ℂ 1) hzn
    have hld : ContinuousAt (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))) z := by
      change ContinuousAt (fun w => deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) w /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) w) z
      exact hLa.deriv.continuousAt.div hLa.continuousAt hLn
    exact hld.neg.mul (hK z hz.1).continuousAt
  · simpa only [contourError,add_assoc] using
      perron_rectangle_shift (quadraticPerronIntegrand (1 : DirichletCharacter ℂ 1) x) _ _
        a c T hT.le hint hperron hres

end QRHShort.CloudBatch.PrimesAPExplicitAux


noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Two applications of the mean value inequality retain the complete
second-difference cancellation, also for complex-valued functions. -/
theorem second_difference_norm_le {F F' F'' : ℝ → ℂ} {x h M : ℝ}
    (hh : 0 < h)
    (hF : ∀ t ∈ Set.Icc x (x+2*h), HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.Icc x (x+2*h), HasDerivAt F' (F'' t) t)
    (hbound : ∀ t ∈ Set.Icc x (x+2*h), ‖F'' t‖ ≤ M) :
    ‖F (x+2*h)-2*F (x+h)+F x‖ ≤ M*h^2 := by
  have hinc (t : ℝ) (ht : t ∈ Set.Icc x (x+h)) : ‖F' (t+h)-F' t‖ ≤ M*h := by
    have hsub : Set.Icc t (t+h) ⊆ Set.Icc x (x+2*h) := by
      intro u hu
      exact ⟨by linarith [ht.1, hu.1], by linarith [ht.2, hu.2]⟩
    have hb := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u hu => (hF' u (hsub hu)).hasDerivWithinAt)
      (fun u hu => hbound u (hsub (Ico_subset_Icc_self hu)))
      (t+h) (right_mem_Icc.mpr (by linarith : t≤t+h))
    simpa only [add_sub_cancel_left] using hb
  let G : ℝ → ℂ := fun t => F (t+h)-F t
  have hG (t : ℝ) (ht : t ∈ Set.Icc x (x+h)) :
      HasDerivWithinAt G (F' (t+h)-F' t) (Set.Icc x (x+h)) t := by
    have ht0 : t ∈ Set.Icc x (x+2*h) := ⟨ht.1, by linarith [ht.2]⟩
    have ht1 : t+h ∈ Set.Icc x (x+2*h) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hF (t+h) ht1).comp_add_const t h |>.sub (hF t ht0)).hasDerivWithinAt
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hG
    (fun t ht => hinc t (Ico_subset_Icc_self ht))
    (x+h) (right_mem_Icc.mpr (by linarith : x≤x+h))
  dsimp only [G] at hb
  convert hb using 1
  · congr 1
    rw [show x+h+h=x+2*h by ring]
    ring
  · ring

/-- Differencing the quadratic Perron residue before taking its norm removes
both shifted denominator factors. This is the bound used on the zero terms
and on the left edge, without losing the leading exponent. -/
theorem quadratic_cpow_difference_norm_le {ρ : ℂ} {x h : ℝ}
    (hρ : 0 < ρ.re) (hx : 0 < x) (hh : 0 < h) :
    ‖(((x+2*h:ℝ):ℂ)^(ρ+2)/(ρ*(ρ+1)*(ρ+2)) -
        2*((x+h:ℝ):ℂ)^(ρ+2)/(ρ*(ρ+1)*(ρ+2)) +
        (x:ℂ)^(ρ+2)/(ρ*(ρ+1)*(ρ+2))) / (h:ℂ)^2‖ ≤
      (x+2*h)^ρ.re / ‖ρ‖ := by
  let F : ℝ → ℂ := fun t => (t:ℂ)^(ρ+2)/(ρ*(ρ+1)*(ρ+2))
  let F' : ℝ → ℂ := fun t => (t:ℂ)^(ρ+1)/(ρ*(ρ+1))
  let F'' : ℝ → ℂ := fun t => (t:ℂ)^ρ/ρ
  let M : ℝ := (x+2*h)^ρ.re/‖ρ‖
  have hρ0 : ρ ≠ 0 := by intro h; simpa [h] using hρ
  have hρ1 : ρ ≠ -1 := by intro h; subst ρ; norm_num at hρ
  have hρ2 : ρ+1 ≠ -1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re] at this
    linarith
  have hF (t : ℝ) (ht : t ∈ Set.Icc x (x+2*h)) : HasDerivAt F (F' t) t := by
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx ht.1)
    have hd := (hasDerivAt_ofReal_cpow_const' ht0 hρ2).div_const (ρ*(ρ+1))
    convert hd using 1
    ext u
    dsimp only [F]
    rw [show ρ+1+1=ρ+2 by ring, div_div]
    congr 1 <;> ring
  have hF' (t : ℝ) (ht : t ∈ Set.Icc x (x+2*h)) : HasDerivAt F' (F'' t) t := by
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx ht.1)
    have hd := (hasDerivAt_ofReal_cpow_const' ht0 hρ1).div_const ρ
    convert hd using 1
    ext u
    dsimp only [F']
    rw [div_div]
    congr 1 <;> ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc x (x+2*h)) : ‖F'' t‖ ≤ M := by
    dsimp only [F'', M]
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hx ht.1)]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith [ht.1]) ht.2 hρ.le)
      (norm_nonneg _)
  have hb := second_difference_norm_le hh hF hF' hbound
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  calc
    _ = ‖F (x+2*h)-2*F (x+h)+F x‖/h^2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      congr 1
      dsimp only [F]
      ring_nf
    _ ≤ (M*h^2)/h^2 := div_le_div_of_nonneg_right hb hh2.le
    _ = M := mul_div_cancel_right₀ M hh2.ne'

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- A single finite set supplies both a left abscissa and a symmetric height.
The separation is controlled by the actual cardinality of that set. -/
theorem finite_complex_contour_separation (S : Finset ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    let δ : ℝ := 1/(400*((S.card:ℝ)+1))
    ∃ a ∈ Set.Icc (3/4:ℝ) (19/25), ∃ T ∈ Set.Icc Y (2*Y),
      (∀ u ∈ S, ∀ t : ℝ, δ ≤ ‖(a:ℂ)+(t:ℂ)*Complex.I-u‖) ∧
      (∀ u ∈ S, ∀ b : ℝ,
        δ ≤ ‖(b:ℂ)+(T:ℂ)*Complex.I-u‖ ∧ δ ≤ ‖(b:ℂ)-(T:ℂ)*Complex.I-u‖) := by
  let R := S.image Complex.re
  let J := S.image (fun u : ℂ => |u.im|)
  let δ : ℝ := 1/(400*((S.card:ℝ)+1))
  obtain ⟨a, ha, hasep⟩ := finite_grid_avoidance R (by norm_num : (3/4:ℝ)<19/25)
  obtain ⟨T, hT, hTsep⟩ := finite_grid_avoidance J (by linarith : Y<2*Y)
  have hRcard : (R.card:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast Finset.card_image_le
  have hJcard : (J.card:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast Finset.card_image_le
  have hδR : δ ≤ (19/25-3/4)/(4*((R.card:ℝ)+1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    norm_num
    nlinarith
  have hδJ : δ ≤ (2*Y-Y)/(4*((J.card:ℝ)+1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hY) (show (0:ℝ)≤(S.card:ℝ)+1 by positivity)
    nlinarith
  have hTp : 0 < T := lt_of_lt_of_le (by linarith : (0:ℝ)<Y) hT.1
  refine ⟨a, ha, T, hT, ?_, ?_⟩
  · intro u hu t
    have hh := hδR.trans (hasep u.re (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
    calc
      _ ≤ |a-u.re| := hh
      _ = |((a:ℂ)+(t:ℂ)*Complex.I-u).re| := by simp
      _ ≤ _ := Complex.abs_re_le_norm _
  · intro u hu b
    have hh := hδJ.trans (hTsep |u.im| (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
    constructor
    · calc
        _ ≤ abs (T - abs u.im) := hh
        _ ≤ |T-u.im| := by
          simpa only [abs_of_pos hTp] using abs_abs_sub_abs_le_abs_sub T u.im
        _ = |((b:ℂ)+(T:ℂ)*Complex.I-u).im| := by simp
        _ ≤ _ := Complex.abs_im_le_norm _
    · calc
        _ ≤ abs (T - abs u.im) := hh
        _ ≤ |-T-u.im| := by
          simpa only [abs_neg, abs_of_pos hTp] using abs_abs_sub_abs_le_abs_sub (-T) u.im
        _ = |((b:ℂ)-(T:ℂ)*Complex.I-u).im| := by simp
        _ ≤ _ := Complex.abs_im_le_norm _

/-- A bounded finite set containing the relevant actual zeros produces a
zero-free rectangle and quantitative separation for its left and horizontal
edges. The right edge follows from the stated genuine zero-free half-plane. -/
theorem finite_zero_set_good_contour {f : ℂ → ℂ} (S : Finset ℂ)
    {Y B c : ℝ} (hY : 1 ≤ Y) (hc : 1 < c) (hc2 : c ≤ 2)
    (hroot : ∀ u, f u=0 → u.re ≤ (11:ℝ)/12)
    (hcover : ∀ u, f u=0 → 1/2 ≤ u.re → u.re ≤ 1 → |u.im| ≤ 2*Y+4 → u ∈ S)
    (hcard : (S.card:ℝ) ≤ B) :
    ∃ a ∈ Set.Icc (3/4:ℝ) (19/25), ∃ T ∈ Set.Icc Y (2*Y), ∃ δ : ℝ,
      0 < δ ∧ δ ≤ 1/4 ∧ δ⁻¹ ≤ 400*(B+1) ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        z.re=a ∨ z.re=c ∨ z.im= -T ∨ z.im=T → f z ≠ 0) ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        z.re=a ∨ z.im= -T ∨ z.im=T →
        ∀ u : ℂ, f u=0 → 1/2 ≤ u.re → u.re ≤ 1 → |u.im| ≤ T+2 → δ ≤ ‖z-u‖) := by
  obtain ⟨a, ha, T, hT, hleft, hhor⟩ := finite_complex_contour_separation S hY
  let δ : ℝ := 1/(400*((S.card:ℝ)+1))
  have hδp : 0 < δ := by dsimp only [δ]; positivity
  have hδhi : δ ≤ 1/4 := by
    dsimp only [δ]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) S.card]
  have hδinv : δ⁻¹ ≤ 400*(B+1) := by
    dsimp only [δ]
    rw [one_div, inv_inv]
    linarith
  have hgeom (z : ℂ) (hz : z.re=a ∨ z.im= -T ∨ z.im=T)
      (u : ℂ) (hu : u ∈ S) : δ ≤ ‖z-u‖ := by
    rcases hz with hz | hz | hz
    · have heq : z=(a:ℂ)+(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
      rw [heq]
      exact hleft u hu z.im
    · have heq : z=(z.re:ℂ)-(T:ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
      rw [heq]
      exact (hhor u hu z.re).2
    · have heq : z=(z.re:ℂ)+(T:ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
      rw [heq]
      exact (hhor u hu z.re).1
  refine ⟨a, ha, T, hT, δ, hδp, hδhi, hδinv, ?_, ?_⟩
  · intro z hzlo _ hzT hside hz0
    have hzr := hroot z hz0
    have hzS : z ∈ S := hcover z hz0 (by linarith [ha.1]) (by linarith)
      (by linarith [hT.2])
    have hg : z.re=a ∨ z.im= -T ∨ z.im=T := by
      rcases hside with h | h | h | h
      · exact Or.inl h
      · have hre : c ≤ (11:ℝ)/12 := by simpa only [h] using hzr
        linarith
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hh := hgeom z hg z hzS
    simp only [sub_self, norm_zero] at hh
    exact hδp.not_ge hh
  · intro z _ _ _ hz u hu0 hulo huhi huT
    exact hgeom z hz u (hcover u hu0 hulo huhi (by linarith [hT.2]))


/-- The finite set, abscissa, height and separation are all constructed from
the literal nonprincipal L-function. -/
theorem LFunction_good_contour (hZ : QRHShort.DirichletZeroFreeStatement)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {Y c : ℝ} (hY : 1 ≤ Y) (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ a ∈ Set.Icc (3/4:ℝ) (19/25), ∃ T ∈ Set.Icc Y (2*Y), ∃ δ : ℝ,
      0 < δ ∧ δ ≤ 1/4 ∧
      δ⁻¹ ≤ 400*((4*Y+13)*(Real.log (32*(q:ℝ)*(2*Y+10))/Real.log (15/14))+1) ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        z.re=a ∨ z.re=c ∨ z.im= -T ∨ z.im=T → DirichletCharacter.LFunction χ z ≠ 0) ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        z.re=a ∨ z.im= -T ∨ z.im=T →
        ∀ u : ℂ, DirichletCharacter.LFunction χ u=0 →
          1/2 ≤ u.re → u.re ≤ 1 → |u.im| ≤ T+2 → δ ≤ ‖z-u‖) := by
  obtain ⟨S, hS, hcard⟩ := LFunction_strip_zero_finset χ hχ
    (by linarith : (0:ℝ)≤2*Y+4)
  apply finite_zero_set_good_contour S hY hc hc2
  · intro u hu
    by_contra! hh
    exact hZ q χ u hh (.inr hχ) hu
  · intro u hu hlo hhi him
    exact (hS u).mpr ⟨hu, hlo, hhi, him⟩
  · simpa only [show 2*(2*Y+4)+5=4*Y+13 by ring,
      show 2*Y+4+6=2*Y+10 by ring] using hcard

/-- The principal primitive case uses the actual regularized zeta function,
so the pole at one is not confused with a zero to avoid. -/
theorem regularizedZeta_good_contour (hZ : QRHShort.DirichletZeroFreeStatement)
    {Y c : ℝ} (hY : 1 ≤ Y) (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ a ∈ Set.Icc (3/4:ℝ) (19/25), ∃ T ∈ Set.Icc Y (2*Y), ∃ δ : ℝ,
      0 < δ ∧ δ ≤ 1/4 ∧
      δ⁻¹ ≤ 400*((4*Y+13)*(Real.log (64*(2*Y+10)^2)/Real.log (15/14))+1) ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        z.re=a ∨ z.re=c ∨ z.im= -T ∨ z.im=T →
          DirichletCharacter.LFunctionTrivChar₁ 1 z ≠ 0) ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        z.re=a ∨ z.im= -T ∨ z.im=T →
        ∀ u : ℂ, DirichletCharacter.LFunctionTrivChar₁ 1 u=0 →
          1/2 ≤ u.re → u.re ≤ 1 → |u.im| ≤ T+2 → δ ≤ ‖z-u‖) := by
  obtain ⟨S, hS, hcard⟩ := regularizedZeta_strip_zero_finset
    (by linarith : (0:ℝ)≤2*Y+4)
  apply finite_zero_set_good_contour S hY hc hc2
  · intro u hu
    by_contra! hh
    exact regularizedZeta_ne_zero_right hZ hh hu
  · intro u hu hlo hhi him
    exact (hS u).mpr ⟨hu, hlo, hhi, him⟩
  · simpa only [show 2*(2*Y+4)+5=4*Y+13 by ring,
      show 2*Y+4+6=2*Y+10 by ring] using hcard

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Uniform real algebra for the separated-contour logarithmic budget. -/
theorem separated_log_budget_bound {d p Y L A δ : ℝ}
    (hd : 0 < d) (hp : 0 ≤ p) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hA : 0 ≤ A ∧ A ≤ 2*L) (_hδ : 0 < δ)
    (hinv : δ⁻¹ ≤ 400*((4*Y+13)*(A/d)+1)) :
    A/d/δ + 96*(p*A+1) + 5 ≤
      (800*(34/d+1)/d+192*p+101)*Y*L^2 := by
  have hY0 : 0 ≤ Y := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hAd0 : 0 ≤ A/d := div_nonneg hA.1 hd.le
  have hAd : A/d ≤ 2*L/d := div_le_div_of_nonneg_right hA.2 hd.le
  have hYL : 1 ≤ Y*L := by
    have hmul := mul_le_mul_of_nonneg_left hL hY0
    nlinarith
  have hlinear : 4*Y+13 ≤ 17*Y := by linarith
  have hpair : (4*Y+13)*(A/d) ≤ (17*Y)*(2*L/d) :=
    mul_le_mul hlinear hAd hAd0 (by positivity)
  have hinv' : δ⁻¹ ≤ 400*(34/d+1)*Y*L := by
    calc
      δ⁻¹ ≤ 400*((4*Y+13)*(A/d)+1) := hinv
      _ ≤ 400*((17*Y)*(2*L/d)+Y*L) :=
        mul_le_mul_of_nonneg_left (add_le_add hpair hYL) (by norm_num)
      _ = 400*(34/d+1)*Y*L := by ring
  have hscale0 : 0 ≤ 400*(34/d+1)*Y*L := by positivity
  have hfirst : A/d/δ ≤ (800*(34/d+1)/d)*Y*L^2 := by
    calc
      A/d/δ = (A/d)*δ⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (A/d)*(400*(34/d+1)*Y*L) :=
        mul_le_mul_of_nonneg_left hinv' hAd0
      _ ≤ (2*L/d)*(400*(34/d+1)*Y*L) :=
        mul_le_mul_of_nonneg_right hAd hscale0
      _ = (800*(34/d+1)/d)*Y*L^2 := by ring
  have hLsq : L ≤ L^2 := by
    have hmul := mul_le_mul_of_nonneg_left hL hL0
    nlinarith
  have hLsq1 : 1 ≤ L^2 := hL.trans hLsq
  have hpA : p*A ≤ p*(2*L) := mul_le_mul_of_nonneg_left hA.2 hp
  have hpL : 192*p*L ≤ 192*p*L^2 :=
    mul_le_mul_of_nonneg_left hLsq (by positivity)
  have hconst : (101 : ℝ) ≤ 101*L^2 := by nlinarith
  have hrest : 96*(p*A+1)+5 ≤ (192*p+101)*Y*L^2 := by
    calc
      96*(p*A+1)+5 ≤ (192*p+101)*L^2 := by nlinarith
      _ ≤ Y*((192*p+101)*L^2) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hY (show 0 ≤ (192*p+101)*L^2 by positivity)
      _ = (192*p+101)*Y*L^2 := by ring
  calc
    A/d/δ + 96*(p*A+1)+5 = A/d/δ + (96*(p*A+1)+5) := by ring
    _ ≤ (800*(34/d+1)/d)*Y*L^2 + (192*p+101)*Y*L^2 := add_le_add hfirst hrest
    _ = (800*(34/d+1)/d+192*p+101)*Y*L^2 := by ring

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- A selected left or horizontal side stays uniformly away from the principal pole. -/
theorem selected_contour_pole_bound {a T : ℝ} (ha : a ≤ (19:ℝ)/25) (hT : 1 ≤ T)
    {z : ℂ} (hside : z.re=a ∨ z.im= -T ∨ z.im=T) :
    z ≠ 1 ∧ ‖(1:ℂ)/(z-1)‖ ≤ 5 := by
  have hn : (1:ℝ)/5 ≤ ‖z-1‖ := by
    rcases hside with hr | hi | hi
    · have hh := Complex.abs_re_le_norm (z-1)
      simp only [Complex.sub_re, Complex.one_re] at hh
      linarith [neg_le_abs (z.re-1)]
    · have hh := Complex.abs_im_le_norm (z-1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero, hi, abs_neg,
        abs_of_pos (by linarith : 0<T)] at hh
      linarith
    · have hh := Complex.abs_im_le_norm (z-1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero, hi,
        abs_of_pos (by linarith : 0<T)] at hh
      linarith
  refine ⟨?_, ?_⟩
  · intro hz
    simp only [hz, sub_self, norm_zero] at hn
    linarith
  · rw [norm_div, norm_one]
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/5) hn
    norm_num at hh
    simpa only [one_div] using hh

/-- The actual primitive family admits a common quantitative choice of
contour. One absolute constant is selected before the character, height and
right abscissa; the left and horizontal logarithmic derivatives cost only
height times two logarithms. -/
theorem primitive_LFunction_good_contour_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hZ : QRHShort.DirichletZeroFreeStatement)
      (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ Y c : ℝ, 1 ≤ Y → 1 < c → c ≤ 2 →
      ∃ a ∈ Set.Icc (3/4:ℝ) (19/25), ∃ T ∈ Set.Icc Y (2*Y),
        (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
          z.re=a ∨ z.re=c ∨ z.im= -T ∨ z.im=T → DirichletCharacter.LFunction χ z ≠ 0) ∧
        (∀ z : ℂ, a ≤ z.re → z.re ≤ c → |z.im| ≤ T →
          z.re=a ∨ z.im= -T ∨ z.im=T →
          ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤
            C*Y*(Real.log (64*(q:ℝ)*(2*Y+10))+1)^2) := by
  let d : ℝ := Real.log (15/14)
  let p : ℝ := 1+Real.log 14/d
  let C : ℝ := 800*(34/d+1)/d+192*p+101
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hp : 0 ≤ p := by
    dsimp only [p]
    exact add_nonneg zero_le_one (div_nonneg (Real.log_nonneg (by norm_num)) hd.le)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro hZ q _ χ hprim Y c hY hc hc2
  let L : ℝ := Real.log (64*(q:ℝ)*(2*Y+10))+1
  have hq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos q)
  have hq0 : 0 < (q:ℝ) := by linarith
  have hv : 0 < 2*Y+10 := by linarith
  have hL : 1 ≤ L := by
    have hh : 0 ≤ Real.log (64*(q:ℝ)*(2*Y+10)) := by
      apply Real.log_nonneg
      nlinarith
    dsimp only [L]
    linarith
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by
      have hh : (1 : DirichletCharacter ℂ q).conductor=q := hprim
      rw [DirichletCharacter.conductor_one] at hh
      exact hh.symm
    subst q
    let A : ℝ := Real.log (64*(2*Y+10)^2)
    have hA0 : 0 ≤ A := Real.log_nonneg (by nlinarith [sq_nonneg Y])
    have hAL : A ≤ 2*L := by
      dsimp only [A, L]
      norm_num only [Nat.cast_one, mul_one]
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hv.ne'), Real.log_pow,
        Real.log_mul (by norm_num) hv.ne']
      norm_num only
      nlinarith [Real.log_nonneg (by norm_num : (1:ℝ)≤64)]
    obtain ⟨a, ha, T, hT, δ, hδ, hδhi, hinv, hbound, hsep⟩ :=
      regularizedZeta_good_contour hZ hY hc hc2
    have hT1 : 1 ≤ T := hY.trans hT.1
    have hordinary (z : ℂ) (hzlo : a ≤ z.re) (hzhi : z.re ≤ c) (hzT : |z.im| ≤ T)
        (hside : z.re=a ∨ z.re=c ∨ z.im= -T ∨ z.im=T) :
        DirichletCharacter.LFunctionTrivChar 1 z ≠ 0 := by
      have hz1 : z ≠ 1 := by
        intro hz
        subst z
        simp only [Complex.one_re, Complex.one_im] at hside
        rcases hside with hh | hh | hh | hh <;> linarith [ha.2]
      have hh := hbound z hzlo hzhi hzT hside
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1] at hh
      exact (mul_ne_zero_iff.mp hh).2
    refine ⟨a, ha, T, hT, hordinary, ?_⟩
    intro z hzlo hzhi hzT hside
    obtain ⟨hz1, hpole⟩ := selected_contour_pole_bound ha.2 hT1 hside
    have hb := (regularizedZeta_separated_logDeriv_le hZ (ha.1.trans hzlo)
      (hzhi.trans hc2) hzT hδ hδhi (hsep z hzlo hzhi hzT hside)).2
    have hAz : Real.log (64*(|z.im|+4)^2) ≤ A := by
      apply Real.log_le_log (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤64)
      exact (sq_le_sq₀ (by positivity) hv.le).mpr (by linarith [hT.2])
    have hside' : z.re=a ∨ z.re=c ∨ z.im= -T ∨ z.im=T := by
      rcases hside with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr hh))
    have hLz := hordinary z hzlo hzhi hzT hside'
    have heq : logDeriv (DirichletCharacter.LFunctionTrivChar 1) z =
        logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) z - 1/(z-1) := by
      rw [regularizedZeta_logDeriv_eq hz1 hLz]
      ring
    have hnorm : ‖logDeriv (DirichletCharacter.LFunctionTrivChar 1) z‖ ≤ A/d/δ+96*(p*A+1)+5 := by
      rw [heq]
      have hn := norm_sub_le (logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) z) (1/(z-1))
      have h₁ := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hAz hd.le) hδ.le
      have h₂ := mul_le_mul_of_nonneg_left hAz hp
      change ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) z - 1/(z-1)‖ ≤ _
      dsimp only [d, p] at h₁ h₂ ⊢
      linarith
    refine hnorm.trans ?_
    exact separated_log_budget_bound hd hp hY hL ⟨hA0, hAL⟩ hδ hinv
  · let A : ℝ := Real.log (32*(q:ℝ)*(2*Y+10))
    have hA0 : 0 ≤ A := by apply Real.log_nonneg; nlinarith
    have hAL : A ≤ 2*L := by
      have hh : A ≤ Real.log (64*(q:ℝ)*(2*Y+10)) := by
        apply Real.log_le_log (by positivity)
        nlinarith [mul_pos hq0 hv]
      dsimp only [L] at hL ⊢
      linarith
    obtain ⟨a, ha, T, hT, δ, hδ, hδhi, hinv, hbound, hsep⟩ :=
      LFunction_good_contour hZ χ hχ hY hc hc2
    refine ⟨a, ha, T, hT, hbound, ?_⟩
    intro z hzlo hzhi hzT hside
    have hb := (LFunction_separated_logDeriv_le hZ χ hχ (ha.1.trans hzlo)
      (hzhi.trans hc2) hzT hδ hδhi (hsep z hzlo hzhi hzT hside)).2
    have hAz : Real.log (32*(q:ℝ)*(|z.im|+4)) ≤ A := by
      apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith [hT.2]) (by positivity)
    have hnorm : ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤ A/d/δ+96*(p*A+1)+5 := by
      have h₁ := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hAz hd.le) hδ.le
      have h₂ := mul_le_mul_of_nonneg_left hAz hp
      dsimp only [d, p] at h₁ h₂ ⊢
      linarith
    refine hnorm.trans ?_
    exact separated_log_budget_bound hd hp hY hL ⟨hA0, hAL⟩ hδ hinv

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

theorem round_natAbs_cast_le (t : ℝ) :
    ((round t).natAbs : ℝ) ≤ |t| + 1/2 := by
  have hr := abs_le.mp (abs_sub_round t)
  have hcast : ((round t).natAbs : ℝ) = |(round t : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hcast]
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs t]
  · linarith [le_abs_self t]

theorem complex_reciprocal_norm_le_round {u : ℂ} (hu : (1/2 : ℝ) ≤ u.re) :
    1 / ‖u‖ ≤ 4 / (((round u.im).natAbs : ℝ)+1) := by
  have hn : (1/2 : ℝ) ≤ ‖u‖ := hu.trans (Complex.re_le_norm u)
  have hnorm : 0 < ‖u‖ := by linarith
  have hden : 0 < ((round u.im).natAbs : ℝ)+1 := by positivity
  apply (div_le_div_iff₀ hnorm hden).mpr
  have hr := round_natAbs_cast_le u.im
  have hi := Complex.abs_im_le_norm u
  nlinarith

/-- Combining the two signed rounding bins of a fixed absolute index costs
at most twice the original per-bin mass. -/
theorem round_natAbs_bin_mass_le (S : Finset ℂ) (w : ℂ → ℝ)
    {U B : ℝ} (hw : ∀ u ∈ S, 0 ≤ w u)
    (hbin : ∀ k : ℤ, |(k : ℝ)| ≤ U+2 →
      ∑ u ∈ S.filter (fun u => round u.im = k), w u ≤ B)
    (n : ℕ) (hn : (n : ℝ) ≤ U+2) :
    ∑ u ∈ S.filter (fun u => (round u.im).natAbs = n), w u ≤ 2*B := by
  have hp := hbin (n : ℤ) (by simpa using hn)
  have hm := hbin (-(n : ℤ)) (by simpa using hn)
  calc
    (∑ u ∈ S.filter (fun u => (round u.im).natAbs = n), w u) ≤
        (∑ u ∈ S.filter (fun u => round u.im = (n : ℤ)), w u) +
        ∑ u ∈ S.filter (fun u => round u.im = -(n : ℤ)), w u := by
      simp only [Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro u hu
      have hw0 := hw u hu
      by_cases h : (round u.im).natAbs = n
      · rw [if_pos h]
        have heq : round u.im = (n : ℤ) ∨ round u.im = -(n : ℤ) := by
          simpa only [h] using Int.natAbs_eq (round u.im)
        rcases heq with hp | hm
        · rw [if_pos hp]
          by_cases hm : round u.im = -(n : ℤ)
          · rw [if_pos hm]
            linarith [hw u hu]
          · rw [if_neg hm]
            simp
        · rw [if_pos hm]
          by_cases hp : round u.im = (n : ℤ)
          · rw [if_pos hp]
            linarith [hw u hu]
          · rw [if_neg hp]
            simp
      · rw [if_neg h]
        positivity
    _ ≤ 2*B := by linarith

/-- A uniform mass bound in every unit-height rounding bin gives a logarithmic
bound for the finite sum of reciprocal distances from the origin. -/
theorem finite_weighted_reciprocal_sum_le (S : Finset ℂ) (w : ℂ → ℝ)
    {U B : ℝ} (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hw : ∀ u ∈ S, 0 ≤ w u)
    (hre : ∀ u ∈ S, (1/2 : ℝ) ≤ u.re)
    (him : ∀ u ∈ S, |u.im| ≤ U)
    (hbin : ∀ k : ℤ, |(k : ℝ)| ≤ U+2 →
      ∑ u ∈ S.filter (fun u => round u.im = k), w u ≤ B) :
    ∑ u ∈ S, w u / ‖u‖ ≤ 8*B*(1+Real.log (U+3)) := by
  let N : ℕ := ⌊U+1⌋₊
  have hU1 : 0 ≤ U+1 := by linarith
  have hN : (N : ℝ) ≤ U+1 := Nat.floor_le hU1
  have hindex (u : ℂ) (hu : u ∈ S) : (round u.im).natAbs ∈ Finset.range (N+1) := by
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply (Nat.le_floor_iff hU1).mpr
    have hr := round_natAbs_cast_le u.im
    linarith [him u hu]
  have hsum : (∑ u ∈ S, w u / ‖u‖) =
      ∑ n ∈ Finset.range (N+1),
        ∑ u ∈ S.filter (fun u => (round u.im).natAbs = n), w u / ‖u‖ := by
    exact (Finset.sum_fiberwise_of_maps_to hindex (fun u => w u / ‖u‖)).symm
  rw [hsum]
  have hterm (n : ℕ) (hn : n ∈ Finset.range (N+1)) :
      (∑ u ∈ S.filter (fun u => (round u.im).natAbs = n), w u / ‖u‖) ≤
        8*B / ((n : ℝ)+1) := by
    have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hnreal : (n : ℝ) ≤ U+2 := by
      have hcast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      linarith
    have hm := round_natAbs_bin_mass_le S w hw hbin n hnreal
    have hden : 0 ≤ 4 / ((n : ℝ)+1) := by positivity
    calc
      (∑ u ∈ S.filter (fun u => (round u.im).natAbs = n), w u / ‖u‖) ≤
          ∑ u ∈ S.filter (fun u => (round u.im).natAbs = n),
            (4 / ((n : ℝ)+1)) * w u := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨huS, hround⟩ := Finset.mem_filter.mp hu
        have hr := complex_reciprocal_norm_le_round (hre u huS)
        rw [hround] at hr
        have hmul := mul_le_mul_of_nonneg_left hr (hw u huS)
        convert hmul using 1 <;> ring
      _ = (4 / ((n : ℝ)+1)) *
          ∑ u ∈ S.filter (fun u => (round u.im).natAbs = n), w u := by
        rw [Finset.mul_sum]
      _ ≤ (4 / ((n : ℝ)+1)) * (2*B) := mul_le_mul_of_nonneg_left hm hden
      _ = 8*B / ((n : ℝ)+1) := by ring
  calc
    (∑ n ∈ Finset.range (N+1),
        ∑ u ∈ S.filter (fun u => (round u.im).natAbs = n), w u / ‖u‖) ≤
        ∑ n ∈ Finset.range (N+1), 8*B / ((n : ℝ)+1) := Finset.sum_le_sum hterm
    _ = 8*B*(harmonic (N+1) : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast,
        Rat.cast_one, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
      rw [Finset.mul_sum]
    _ ≤ 8*B*(1+Real.log (N+1 : ℕ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (N+1)) (by positivity)
    _ ≤ 8*B*(1+Real.log (U+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      apply Real.log_le_log (by positivity)
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Actual global multiplicities in any finite rounded-height bin are bounded
by the corresponding compact local divisor. No global finite-support assertion
is made about the entire function's divisor. -/
theorem entire_round_bin_mass_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (S : Finset ℂ) (hre : ∀ u ∈ S, (3:ℝ)/4 ≤ u.re ∧ u.re ≤ 1) (k : ℤ) :
    (∑ u ∈ S.filter (fun u => round u.im=k),
      (MeromorphicOn.divisor f Set.univ u : ℝ)) ≤
      (((∑ᶠ u : ℂ, MeromorphicOn.divisor f
        (closedBall (2+((k:ℝ):ℂ)*Complex.I) (7/4)) u):ℤ):ℝ) := by
  let V := closedBall (2+((k:ℝ):ℂ)*Complex.I) (7/4)
  let D := MeromorphicOn.divisor f V
  let A := S.filter (fun u => round u.im=k)
  have hfa : AnalyticOnNhd ℂ f V := fun u _ => hf.analyticAt u
  have hfm : MeromorphicOn f (Set.univ : Set ℂ) := fun u _ => (hf.analyticAt u).meromorphicAt
  have hnonneg (u : ℂ) : 0 ≤ D u := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa u
  have hfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall _ _)
  have hval (u : ℂ) (hu : u ∈ A) : MeromorphicOn.divisor f Set.univ u = D u := by
    have hum := Finset.mem_filter.mp hu
    have hur := hre u hum.1
    have hr : |u.re-2| ≤ 5/4 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hi : |u.im-(k:ℝ)| ≤ 1/2 := by simpa only [hum.2] using abs_sub_round u.im
    have hball : u ∈ V := by
      rw [mem_closedBall, dist_eq_norm]
      calc
        _ ≤ |(u-(2+((k:ℝ):ℂ)*Complex.I)).re| +
            |(u-(2+((k:ℝ):ℂ)*Complex.I)).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |u.re-2|+|u.im-(k:ℝ)| := by simp
        _ ≤ 7/4 := by linarith
    change MeromorphicOn.divisor f Set.univ u = MeromorphicOn.divisor f V u
    rw [hfm.divisor_apply (mem_univ u), hfa.meromorphicOn.divisor_apply hball]
  have hmass : (∑ u ∈ A, D u) ≤ ∑ᶠ u : ℂ, D u := by
    calc
      _ ≤ ∑ u ∈ A ∪ hfin.toFinset, D u :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun u _ _ => hnonneg u)
      _ = _ := by
        symm
        apply finsum_eq_sum_of_support_subset
        intro u hu
        exact Finset.mem_union_right _ (hfin.mem_toFinset.mpr hu)
  calc
    _ = ∑ u ∈ A, (D u:ℝ) := Finset.sum_congr rfl (fun u hu => congrArg (fun n : ℤ => (n:ℝ)) (hval u hu))
    _ ≤ _ := by
      rw [← Int.cast_sum]
      exact_mod_cast hmass

/-- A harmonic-height bound for genuine zero multiplicities at arbitrary
finite points of the contour strip. The global divisor is used only pointwise. -/
theorem LFunction_strip_zero_weight_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (S : Finset ℂ)
    {U : ℝ} (hU : 0 ≤ U)
    (hre : ∀ u ∈ S, (3:ℝ)/4 ≤ u.re ∧ u.re ≤ 1)
    (him : ∀ u ∈ S, |u.im| ≤ U) :
    (∑ u ∈ S, (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) Set.univ u:ℝ)/‖u‖) ≤
      8*(Real.log (32*(q:ℝ)*(U+6))/Real.log (15/14))*(1+Real.log (U+3)) := by
  have hf := DirichletCharacter.differentiable_LFunction hχ
  have hq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos q)
  have hQ : 1 ≤ 32*(q:ℝ)*(U+6) := by nlinarith
  apply finite_weighted_reciprocal_sum_le S
    (fun u => (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) Set.univ u:ℝ)) hU
    (div_nonneg (Real.log_nonneg hQ) (Real.log_nonneg (by norm_num)))
  · intro u _
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
  · intro u hu
    linarith [(hre u hu).1]
  · exact him
  · intro k hk
    refine (entire_round_bin_mass_le hf S hre k).trans
      ((LFunction_local_zero_count_le χ hχ (k:ℝ)).trans ?_)
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith : |(k:ℝ)|+4 ≤ U+6) (by positivity)

theorem regularizedZeta_strip_zero_weight_le (S : Finset ℂ)
    {U : ℝ} (hU : 0 ≤ U)
    (hre : ∀ u ∈ S, (3:ℝ)/4 ≤ u.re ∧ u.re ≤ 1)
    (him : ∀ u ∈ S, |u.im| ≤ U) :
    (∑ u ∈ S, (MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1) Set.univ u:ℝ)/‖u‖) ≤
      8*(Real.log (64*(U+6)^2)/Real.log (15/14))*(1+Real.log (U+3)) := by
  have hf := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hQ : 1 ≤ 64*(U+6)^2 := by nlinarith [sq_nonneg U]
  apply finite_weighted_reciprocal_sum_le S
    (fun u => (MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1) Set.univ u:ℝ)) hU
    (div_nonneg (Real.log_nonneg hQ) (Real.log_nonneg (by norm_num)))
  · intro u _
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
  · intro u hu
    linarith [(hre u hu).1]
  · exact him
  · intro k hk
    refine (entire_round_bin_mass_le hf S hre k).trans
      (((regularizedZeta_local_estimates (k:ℝ)).1).trans ?_)
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤64)
    exact (sq_le_sq₀ (by positivity) (by linarith : (0:ℝ)≤U+6)).mpr (by linarith)

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Second differencing a finite residue sum retains the reciprocal-zero
weight; it does not replace it by the much larger unweighted zero count. -/
theorem finite_quadratic_residue_sum_norm_le (S : Finset ℂ) (d : ℂ → ℤ)
    {x h α : ℝ} (hx : 1 ≤ x) (hh : 0 < h)
    (hd : ∀ u ∈ S, 0 ≤ d u) (hre : ∀ u ∈ S, 0 < u.re ∧ u.re ≤ α) :
    let K : ℝ → ℂ → ℂ := fun y u => (y:ℂ)^(u+2)/(u*(u+1)*(u+2))
    ‖((∑ u ∈ S, (d u:ℂ)*K (x+2*h) u) -
      2*(∑ u ∈ S, (d u:ℂ)*K (x+h) u) +
      (∑ u ∈ S, (d u:ℂ)*K x u))/(h:ℂ)^2‖ ≤
        (x+2*h)^α * ∑ u ∈ S, (d u:ℝ)/‖u‖ := by
  let K : ℝ → ℂ → ℂ := fun y u => (y:ℂ)^(u+2)/(u*(u+1)*(u+2))
  have heq : ((∑ u ∈ S, (d u:ℂ)*K (x+2*h) u) -
      2*(∑ u ∈ S, (d u:ℂ)*K (x+h) u) +
      (∑ u ∈ S, (d u:ℂ)*K x u))/(h:ℂ)^2 =
      ∑ u ∈ S, (d u:ℂ)*((K (x+2*h) u-2*K (x+h) u+K x u)/(h:ℂ)^2) := by
    have hm : (∑ u ∈ S, (d u:ℂ)*(2*K (x+h) u)) =
        2*∑ u ∈ S, (d u:ℂ)*K (x+h) u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    calc
      _ = (∑ u ∈ S, (d u:ℂ)*(K (x+2*h) u-2*K (x+h) u+K x u))/(h:ℂ)^2 := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hm]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro u _
        ring
  change ‖((∑ u ∈ S, (d u:ℂ)*K (x+2*h) u) -
      2*(∑ u ∈ S, (d u:ℂ)*K (x+h) u) +
      (∑ u ∈ S, (d u:ℂ)*K x u))/(h:ℂ)^2‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ u ∈ S, ‖(d u:ℂ)*((K (x+2*h) u-2*K (x+h) u+K x u)/(h:ℂ)^2)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S, (x+2*h)^α*((d u:ℝ)/‖u‖) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, Complex.norm_int_of_nonneg (hd u hu)]
      have hdu : (0:ℝ) ≤ (d u:ℝ) := by exact_mod_cast hd u hu
      have hb := quadratic_cpow_difference_norm_le (hre u hu).1
        (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx) hh
      have hb' : ‖(K (x+2*h) u-2*K (x+h) u+K x u)/(h:ℂ)^2‖ ≤
          (x+2*h)^u.re/‖u‖ := by
        convert hb using 1 <;> congr 1 <;> simp only [K] <;> ring
      calc
        _ ≤ (d u:ℝ)*((x+2*h)^u.re/‖u‖) := mul_le_mul_of_nonneg_left hb' hdu
        _ ≤ (d u:ℝ)*((x+2*h)^α/‖u‖) := by
          apply mul_le_mul_of_nonneg_left _ hdu
          apply div_le_div_of_nonneg_right _ (norm_nonneg _)
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (hre u hu).2
        _ = _ := by ring
    _ = _ := (Finset.mul_sum ..).symm

/-- The leading zero term has the required x^(11/12) scale and only two
logarithmic factors, for the actual nonprincipal L-function's multiplicities. -/
theorem LFunction_zero_difference_norm_le
    (hZ : QRHShort.DirichletZeroFreeStatement) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (S : Finset ℂ)
    {x h U : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hU : 0 ≤ U)
    (hS : ∀ u ∈ S, DirichletCharacter.LFunction χ u=0 ∧ (3:ℝ)/4 ≤ u.re ∧ |u.im| ≤ U) :
    let D := MeromorphicOn.divisor (DirichletCharacter.LFunction χ) Set.univ
    let K : ℝ → ℂ → ℂ := fun y u => (y:ℂ)^(u+2)/(u*(u+1)*(u+2))
    ‖((∑ u ∈ S, (D u:ℂ)*K (x+2*h) u) -
      2*(∑ u ∈ S, (D u:ℂ)*K (x+h) u) +
      (∑ u ∈ S, (D u:ℂ)*K x u))/(h:ℂ)^2‖ ≤
        (x+2*h)^((11:ℝ)/12) *
          (8*(Real.log (32*(q:ℝ)*(U+6))/Real.log (15/14))*(1+Real.log (U+3))) := by
  let D := MeromorphicOn.divisor (DirichletCharacter.LFunction χ) Set.univ
  have hf := DirichletCharacter.differentiable_LFunction hχ
  have hnonneg (u : ℂ) : 0 ≤ D u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
  have hupper (u : ℂ) (hu : u ∈ S) : u.re ≤ (11:ℝ)/12 := by
    by_contra! hh
    exact hZ q χ u hh (.inr hχ) (hS u hu).1
  have hre (u : ℂ) (hu : u ∈ S) : (3:ℝ)/4 ≤ u.re ∧ u.re ≤ 1 :=
    ⟨(hS u hu).2.1, (hupper u hu).trans (by norm_num)⟩
  have hb := finite_quadratic_residue_sum_norm_le S (D:ℂ→ℤ) hx hh
    (fun u _ => hnonneg u) (fun u hu => ⟨by linarith [(hre u hu).1], hupper u hu⟩)
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_left
    (LFunction_strip_zero_weight_le χ hχ S hU hre (fun u hu => (hS u hu).2.2)) (by positivity)

theorem regularizedZeta_zero_difference_norm_le
    (hZ : QRHShort.DirichletZeroFreeStatement) (S : Finset ℂ)
    {x h U : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hU : 0 ≤ U)
    (hS : ∀ u ∈ S, DirichletCharacter.LFunctionTrivChar₁ 1 u=0 ∧ (3:ℝ)/4 ≤ u.re ∧ |u.im| ≤ U) :
    let D := MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1) Set.univ
    let K : ℝ → ℂ → ℂ := fun y u => (y:ℂ)^(u+2)/(u*(u+1)*(u+2))
    ‖((∑ u ∈ S, (D u:ℂ)*K (x+2*h) u) -
      2*(∑ u ∈ S, (D u:ℂ)*K (x+h) u) +
      (∑ u ∈ S, (D u:ℂ)*K x u))/(h:ℂ)^2‖ ≤
        (x+2*h)^((11:ℝ)/12) *
          (8*(Real.log (64*(U+6)^2)/Real.log (15/14))*(1+Real.log (U+3))) := by
  let D := MeromorphicOn.divisor (DirichletCharacter.LFunctionTrivChar₁ 1) Set.univ
  have hf := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hnonneg (u : ℂ) : 0 ≤ D u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
  have hupper (u : ℂ) (hu : u ∈ S) : u.re ≤ (11:ℝ)/12 := by
    by_contra! hh
    exact regularizedZeta_ne_zero_right hZ hh (hS u hu).1
  have hre (u : ℂ) (hu : u ∈ S) : (3:ℝ)/4 ≤ u.re ∧ u.re ≤ 1 :=
    ⟨(hS u hu).2.1, (hupper u hu).trans (by norm_num)⟩
  have hb := finite_quadratic_residue_sum_norm_le S (D:ℂ→ℤ) hx hh
    (fun u _ => hnonneg u) (fun u hu => ⟨by linarith [(hre u hu).1], hupper u hu⟩)
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_left
    (regularizedZeta_strip_zero_weight_le S hU hre (fun u hu => (hS u hu).2.2)) (by positivity)

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux
open PrimesAPExplicitAux

/-- The exact finite set used by the explicit formula consists of actual
zeros with their actual global multiplicities, restricted to the rectangle. -/
theorem rectangle_zero_points {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a c T : ℝ) :
    let D := MeromorphicOn.divisor f (closedBall (2:ℂ) (T+3))
    let S := (D.finiteSupport (isCompact_closedBall (2:ℂ) (T+3))).toFinset.filter
      (fun u => u ∈ Set.Ioo a c ×ℂ Set.Ioo (-T) T)
    (∀ u ∈ S, f u=0 ∧ a<u.re ∧ u.re<c ∧ |u.im|<T) ∧
      (∀ u ∈ S, D u=MeromorphicOn.divisor f Set.univ u) := by
  let V := closedBall (2:ℂ) (T+3)
  let D := MeromorphicOn.divisor f V
  let S := (D.finiteSupport (isCompact_closedBall (2:ℂ) (T+3))).toFinset.filter
    (fun u => u ∈ Set.Ioo a c ×ℂ Set.Ioo (-T) T)
  have hfa : AnalyticOnNhd ℂ f V := fun u _ => hf.analyticAt u
  have hfm : MeromorphicOn f (Set.univ : Set ℂ) := fun u _ => (hf.analyticAt u).meromorphicAt
  have hsup (u : ℂ) (hu : u ∈ S) : u ∈ D.support :=
    (D.finiteSupport (isCompact_closedBall (2:ℂ) (T+3))).mem_toFinset.mp (Finset.mem_filter.mp hu).1
  constructor
  · intro u hu
    have hn : D u ≠ 0 := hsup u hu
    have hu0 : f u=0 := by
      by_contra hfn
      apply hn
      change MeromorphicOn.divisor f V u=0
      rw [hfa.meromorphicOn.divisor_apply (D.supportWithinDomain (hsup u hu)),
        (hf.analyticAt u).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfn]
      rfl
    have hh := (Finset.mem_filter.mp hu).2
    exact ⟨hu0, hh.1.1, hh.1.2, abs_lt.mpr hh.2⟩
  · intro u hu
    change MeromorphicOn.divisor f V u=MeromorphicOn.divisor f Set.univ u
    rw [hfa.meromorphicOn.divisor_apply (D.supportWithinDomain (hsup u hu)),
      hfm.divisor_apply (mem_univ u)]

/-- The leading-zero estimate in the exact finite-divisor form consumed by
the actual nonprincipal explicit formula. -/
theorem LFunction_rectangleZeroSum_difference_norm_le
    (hZ : QRHShort.DirichletZeroFreeStatement) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x h a c T : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (ha : (3:ℝ)/4 ≤ a) (hT : 0 ≤ T) :
    ‖(rectangleZeroSum (DirichletCharacter.LFunction χ) (x+2*h) a c T -
      2*rectangleZeroSum (DirichletCharacter.LFunction χ) (x+h) a c T +
      rectangleZeroSum (DirichletCharacter.LFunction χ) x a c T)/(h:ℂ)^2‖ ≤
      (x+2*h)^((11:ℝ)/12) *
        (8*(Real.log (32*(q:ℝ)*(T+6))/Real.log (15/14))*(1+Real.log (T+3))) := by
  let f := DirichletCharacter.LFunction χ
  let D := MeromorphicOn.divisor f (closedBall (2:ℂ) (T+3))
  let S := (D.finiteSupport (isCompact_closedBall (2:ℂ) (T+3))).toFinset.filter
    (fun u => u ∈ Set.Ioo a c ×ℂ Set.Ioo (-T) T)
  have hf := DirichletCharacter.differentiable_LFunction hχ
  have hdata := rectangle_zero_points hf a c T
  have hpoints (u : ℂ) (hu : u ∈ S) : f u=0 ∧ (3:ℝ)/4 ≤ u.re ∧ |u.im|≤T := by
    have hd := hdata.1 u hu
    exact ⟨hd.1, by linarith [hd.2.1], hd.2.2.2.le⟩
  have hb := LFunction_zero_difference_norm_le hZ χ hχ S hx hh hT hpoints
  have heq (y : ℝ) : rectangleZeroSum f y a c T =
      ∑ u ∈ S, (MeromorphicOn.divisor f Set.univ u:ℂ)*
        ((y:ℂ)^(u+2)/(u*(u+1)*(u+2))) := by
    change (∑ u ∈ S, (D u:ℂ)*((y:ℂ)^(u+2)/(u*(u+1)*(u+2)))) = _
    apply Finset.sum_congr rfl
    intro u hu
    rw [hdata.2 u hu]
  change ‖(rectangleZeroSum f (x+2*h) a c T -
      2*rectangleZeroSum f (x+h) a c T + rectangleZeroSum f x a c T)/(h:ℂ)^2‖ ≤ _
  rw [heq (x+2*h), heq (x+h), heq x]
  exact hb

/-- The same exact finite-divisor estimate for the pole-removed principal
function, retaining its genuine value at one. -/
theorem regularizedZeta_rectangleZeroSum_difference_norm_le
    (hZ : QRHShort.DirichletZeroFreeStatement)
    {x h a c T : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (ha : (3:ℝ)/4 ≤ a) (hT : 0 ≤ T) :
    ‖(rectangleZeroSum (DirichletCharacter.LFunctionTrivChar₁ 1) (x+2*h) a c T -
      2*rectangleZeroSum (DirichletCharacter.LFunctionTrivChar₁ 1) (x+h) a c T +
      rectangleZeroSum (DirichletCharacter.LFunctionTrivChar₁ 1) x a c T)/(h:ℂ)^2‖ ≤
      (x+2*h)^((11:ℝ)/12) *
        (8*(Real.log (64*(T+6)^2)/Real.log (15/14))*(1+Real.log (T+3))) := by
  let f := DirichletCharacter.LFunctionTrivChar₁ 1
  let D := MeromorphicOn.divisor f (closedBall (2:ℂ) (T+3))
  let S := (D.finiteSupport (isCompact_closedBall (2:ℂ) (T+3))).toFinset.filter
    (fun u => u ∈ Set.Ioo a c ×ℂ Set.Ioo (-T) T)
  have hf := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hdata := rectangle_zero_points hf a c T
  have hpoints (u : ℂ) (hu : u ∈ S) : f u=0 ∧ (3:ℝ)/4 ≤ u.re ∧ |u.im|≤T := by
    have hd := hdata.1 u hu
    exact ⟨hd.1, by linarith [hd.2.1], hd.2.2.2.le⟩
  have hb := regularizedZeta_zero_difference_norm_le hZ S hx hh hT hpoints
  have heq (y : ℝ) : rectangleZeroSum f y a c T =
      ∑ u ∈ S, (MeromorphicOn.divisor f Set.univ u:ℂ)*
        ((y:ℂ)^(u+2)/(u*(u+1)*(u+2))) := by
    change (∑ u ∈ S, (D u:ℂ)*((y:ℂ)^(u+2)/(u*(u+1)*(u+2)))) = _
    apply Finset.sum_congr rfl
    intro u hu
    rw [hdata.2 u hu]
  change ‖(rectangleZeroSum f (x+2*h) a c T -
      2*rectangleZeroSum f (x+h) a c T + rectangleZeroSum f x a c T)/(h:ℂ)^2‖ ≤ _
  rw [heq (x+2*h), heq (x+h), heq x]
  exact hb

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- All three denominator factors retain the height decay of the genuine
quadratic Perron kernel on horizontal edges and right tails. -/
theorem quadratic_cpow_kernel_height_norm_le {s : ℂ} {x c : ℝ}
    (hx : 1 ≤ x) (hs : s.re ≤ c) (him : 0 < |s.im|) :
    ‖(x:ℂ)^(s+2)/(s*(s+1)*(s+2))‖ ≤ x^(c+2)/|s.im|^3 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hn₀ := Complex.abs_im_le_norm s
  have hn₁ : |s.im| ≤ ‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hn₂ : |s.im| ≤ ‖s+2‖ := by simpa using Complex.abs_im_le_norm (s+2)
  have hden : |s.im|^3 ≤ ‖s‖*‖s+1‖*‖s+2‖ := by
    calc
      _ = |s.im| * |s.im| * |s.im| := by ring
      _ ≤ _ := by gcongr
  rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
  have he : (s+2).re=s.re+2 := by simp
  rw [he]
  have hnum : x^(s.re+2) ≤ x^(c+2) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  exact div_le_div₀ (Real.rpow_nonneg hx0.le _) hnum (pow_pos him 3) hden

/-- A complementary difference bound for horizontal edges and right tails.
Here all height decay is retained; the second-derivative bound is used instead
on the left edge and zero residues. -/
theorem quadratic_cpow_difference_height_norm_le {s : ℂ} {x h c : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hc : 1 ≤ c) (hs : s.re ≤ c) (him : 0 < |s.im|) :
    ‖(((x+2*h:ℝ):ℂ)^(s+2)/(s*(s+1)*(s+2)) -
        2*(((x+h:ℝ):ℂ)^(s+2)/(s*(s+1)*(s+2))) +
        (x:ℂ)^(s+2)/(s*(s+1)*(s+2))) / (h:ℂ)^2‖ ≤
      4*(x+2*h)^(c+2)/(h^2*|s.im|^3) := by
  let F : ℝ → ℂ := fun y => (y:ℂ)^(s+2)/(s*(s+1)*(s+2))
  let M : ℝ := (x+2*h)^(c+2)/|s.im|^3
  have hbound (y : ℝ) (hy : y ∈ Set.Icc x (x+2*h)) : ‖F y‖ ≤ M := by
    refine (quadratic_cpow_kernel_height_norm_le (hx.trans hy.1) hs him).trans ?_
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith [hy.1]) hy.2 (by linarith))
      (le_of_lt (pow_pos him 3))
  have h0 := hbound x ⟨le_rfl, by linarith⟩
  have h1 := hbound (x+h) ⟨by linarith, by linarith⟩
  have h2 := hbound (x+2*h) ⟨by linarith, le_rfl⟩
  have hb : ‖F (x+2*h)-2*F (x+h)+F x‖ ≤ 4*M := by
    have hn := norm_add_le (F (x+2*h)-2*F (x+h)) (F x)
    have hs' := norm_sub_le (F (x+2*h)) (2*F (x+h))
    rw [norm_mul] at hs'
    norm_num at hs'
    linarith
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ (4*M)/h^2 := div_le_div_of_nonneg_right hb (sq_nonneg h)
    _ = _ := by dsimp only [M]; ring

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- The spare exponent 1/150 absorbs one logarithm. -/
theorem scale_log_cube_absorb {x : ℝ} (hx : 2 ≤ x) :
    x ^ (91/100 : ℝ) * (Real.log x)^3 ≤
      150 * x ^ (11/12 : ℝ) * (Real.log x)^2 := by
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≤ 150 * x ^ (1/150 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1/150 by norm_num)
    simpa only [div_eq_mul_inv, one_mul, inv_inv, mul_comm] using h
  have hn : 0 ≤ x ^ (91/100 : ℝ) * (Real.log x)^2 :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) (sq_nonneg _)
  calc
    x ^ (91/100 : ℝ) * (Real.log x)^3 =
        (x ^ (91/100 : ℝ) * (Real.log x)^2) * Real.log x := by ring
    _ ≤ (x ^ (91/100 : ℝ) * (Real.log x)^2) *
        (150 * x ^ (1/150 : ℝ)) := mul_le_mul_of_nonneg_left hl hn
    _ = 150 * x ^ (11/12 : ℝ) * (Real.log x)^2 := by
      rw [show (11/12 : ℝ) = 91/100 + 1/150 by norm_num, Real.rpow_add hx0]
      ring

/-- The chosen smoothing and height scales stay in their required ranges. -/
theorem scale_parameter_ranges {x : ℝ} (hx : 2 ≤ x) :
    0 < x ^ (9/10 : ℝ) ∧ x ^ (9/10 : ℝ) ≤ x ∧
      1 ≤ x ^ (3/20 : ℝ) ∧ x ^ (3/20 : ℝ) ≤ x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  exact ⟨Real.rpow_pos_of_pos hx0 _,
    Real.rpow_le_self_of_one_le hx1 (by norm_num),
    Real.one_le_rpow hx1 (by norm_num),
    Real.rpow_le_self_of_one_le hx1 (by norm_num)⟩

/-- Exact normalization of the polynomial tail at the chosen scales. -/
theorem scale_tail_identity {x : ℝ} (hx : 0 < x) :
    x^3 / ((x ^ (9/10 : ℝ))^2 * (x ^ (3/20 : ℝ))^2) = x ^ (9/10 : ℝ) := by
  rw [← Real.rpow_mul_natCast hx.le (9/10 : ℝ) 2,
    ← Real.rpow_mul_natCast hx.le (3/20 : ℝ) 2,
    ← Real.rpow_add hx,
    ← Real.rpow_natCast x 3,
    ← Real.rpow_sub hx]
  norm_num

/-- A single absolute constant controls the auxiliary scale logarithms,
chosen before both the height x and the modulus q. -/
theorem scale_log_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x q : ℝ, 2 ≤ x → 1 ≤ q → q ≤ x →
      Real.log (32*q*(2*x ^ (3/20 : ℝ)+10)) ≤ C*Real.log x ∧
      Real.log (64*(2*x ^ (3/20 : ℝ)+10)^2) ≤ C*Real.log x ∧
      1+Real.log (2*x ^ (3/20 : ℝ)+3) ≤ C*Real.log x := by
  let A : ℝ := 1+Real.log 9216
  let C : ℝ := A / Real.log 2 + 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl9216 : 0 ≤ Real.log 9216 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x q hx hq hqx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq0 : 0 < q := by linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hmul := mul_le_mul_of_nonneg_left hlx (div_nonneg hA hl2.le)
  have habsorb : A ≤ (A / Real.log 2) * Real.log x := by
    simpa only [div_mul_cancel₀ A (ne_of_gt hl2)] using hmul
  have hcommon : A + 2*Real.log x ≤ C*Real.log x := by
    calc
      A + 2*Real.log x ≤ (A / Real.log 2)*Real.log x + 2*Real.log x :=
        add_le_add habsorb le_rfl
      _ = C*Real.log x := by dsimp [C]; ring
  obtain ⟨_, _, hY1, hYx⟩ := scale_parameter_ranges hx
  have hlin : 2*x ^ (3/20 : ℝ)+10 ≤ 12*x := by linarith
  have hlin0 : 0 < 2*x ^ (3/20 : ℝ)+10 := by linarith
  have hshort : 2*x ^ (3/20 : ℝ)+3 ≤ 5*x := by linarith
  have hshort0 : 0 < 2*x ^ (3/20 : ℝ)+3 := by linarith
  have hlog384 : Real.log 384 ≤ Real.log 9216 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog5 : Real.log 5 ≤ Real.log 9216 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hfirst : 32*q*(2*x ^ (3/20 : ℝ)+10) ≤ 384*x^2 := by
    calc
      32*q*(2*x ^ (3/20 : ℝ)+10) ≤ 32*q*(12*x) :=
        mul_le_mul_of_nonneg_left hlin (by positivity)
      _ ≤ 32*x*(12*x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqx (by norm_num)) (by positivity)
      _ = 384*x^2 := by ring
  have hsecond : 64*(2*x ^ (3/20 : ℝ)+10)^2 ≤ 9216*x^2 := by
    calc
      64*(2*x ^ (3/20 : ℝ)+10)^2 ≤ 64*(12*x)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlin0.le hlin 2) (by norm_num)
      _ = 9216*x^2 := by ring
  have hlogfirst : Real.log (32*q*(2*x ^ (3/20 : ℝ)+10)) ≤
      Real.log 384 + 2*Real.log x := by
    calc
      _ ≤ Real.log (384*x^2) := Real.log_le_log (by positivity) hfirst
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hx0.ne'), Real.log_pow]; norm_num
  have hlogsecond : Real.log (64*(2*x ^ (3/20 : ℝ)+10)^2) ≤
      Real.log 9216 + 2*Real.log x := by
    calc
      _ ≤ Real.log (9216*x^2) := Real.log_le_log (by positivity) hsecond
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hx0.ne'), Real.log_pow]; norm_num
  have hlogshort : Real.log (2*x ^ (3/20 : ℝ)+3) ≤ Real.log 5 + Real.log x := by
    calc
      _ ≤ Real.log (5*x) := Real.log_le_log hshort0 hshort
      _ = _ := Real.log_mul (by norm_num) hx0.ne'
  refine ⟨?_, ?_, ?_⟩
  · apply le_trans hlogfirst
    apply le_trans _ hcommon
    dsimp [A]
    linarith
  · apply le_trans hlogsecond
    apply le_trans _ hcommon
    dsimp [A]
    linarith
  · apply le_trans (add_le_add le_rfl hlogshort)
    apply le_trans _ hcommon
    dsimp [A]
    linarith

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- The standard right contour line and smoothing interval have a uniform
polynomial bound; all quantities here are ordinary real scalars. -/
theorem scale_contour_power_bound {x : ℝ} (hx : 2 ≤ x) :
    1 < 1+1/(1+Real.log x) ∧ 1+1/(1+Real.log x) ≤ 2 ∧
      (x+2*x ^ (9/10 : ℝ)) ^ ((1+1/(1+Real.log x))+2) ≤
        81*Real.exp 1*x^3 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hden : 0 < 1+Real.log x := by linarith
  let ε : ℝ := 1/(1+Real.log x)
  let c : ℝ := 1+ε
  have hε : 0 < ε := one_div_pos.mpr hden
  have hε1 : ε ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hc1 : 1 < c := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by dsimp [c]; linarith
  have hfrac : Real.log x/(1+Real.log x) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have hxε : x^ε ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    dsimp [ε]
    simpa only [div_eq_mul_inv, one_mul, mul_one] using hfrac
  have h3 : (3 : ℝ) ^ (c+2) ≤ 81 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 3 by norm_num) (show c+2 ≤ (4 : ℝ) by linarith)
    norm_num at h
    exact h
  have hxpow : x ^ (c+2) ≤ x^3*Real.exp 1 := by
    rw [show c+2 = (3 : ℝ)+ε by dsimp [c]; ring, Real.rpow_add hx0]
    have h := mul_le_mul_of_nonneg_left hxε (show 0 ≤ x ^ (3 : ℝ) by positivity)
    simpa only [Real.rpow_ofNat] using h
  have hhx : x ^ (9/10 : ℝ) ≤ x :=
    Real.rpow_le_self_of_one_le hx1 (by norm_num)
  have hbase : x+2*x ^ (9/10 : ℝ) ≤ 3*x := by linarith
  refine ⟨hc1, hc2, ?_⟩
  change (x+2*x ^ (9/10 : ℝ)) ^ (c+2) ≤ 81*Real.exp 1*x^3
  calc
    (x+2*x ^ (9/10 : ℝ)) ^ (c+2) ≤ (3*x) ^ (c+2) :=
      Real.rpow_le_rpow (by positivity) hbase (by linarith)
    _ = (3 : ℝ) ^ (c+2) * x ^ (c+2) := Real.mul_rpow (by norm_num) hx0.le
    _ ≤ 81*(x^3*Real.exp 1) := mul_le_mul h3 hxpow (by positivity) (by norm_num)
    _ = 81*Real.exp 1*x^3 := by ring

/-- The augmented conductor-height logarithm has an absolute constant,
chosen before x and the real modulus q. -/
theorem scale_augmented_log_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x q : ℝ, 2 ≤ x → 1 ≤ q → q ≤ x →
      Real.log (64*q*(2*x ^ (3/20 : ℝ)+10))+1 ≤ K*Real.log x := by
  let A : ℝ := 1+Real.log 768
  let K : ℝ := A / Real.log 2 + 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl768 : 0 ≤ Real.log 768 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro x q hx hq hqx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq0 : 0 < q := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hmul := mul_le_mul_of_nonneg_left hlx (div_nonneg hA hl2.le)
  have habsorb : A ≤ (A / Real.log 2)*Real.log x := by
    simpa only [div_mul_cancel₀ A (ne_of_gt hl2)] using hmul
  have hcommon : A+2*Real.log x ≤ K*Real.log x := by
    calc
      A+2*Real.log x ≤ (A / Real.log 2)*Real.log x+2*Real.log x :=
        add_le_add habsorb le_rfl
      _ = K*Real.log x := by dsimp [K]; ring
  have hY1 : 1 ≤ x ^ (3/20 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hYx : x ^ (3/20 : ℝ) ≤ x := Real.rpow_le_self_of_one_le hx1 (by norm_num)
  have hlin : 2*x ^ (3/20 : ℝ)+10 ≤ 12*x := by linarith
  have hprod : 64*q*(2*x ^ (3/20 : ℝ)+10) ≤ 768*x^2 := by
    calc
      64*q*(2*x ^ (3/20 : ℝ)+10) ≤ 64*q*(12*x) :=
        mul_le_mul_of_nonneg_left hlin (by positivity)
      _ ≤ 64*x*(12*x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqx (by norm_num)) (by positivity)
      _ = 768*x^2 := by ring
  have hlog : Real.log (64*q*(2*x ^ (3/20 : ℝ)+10)) ≤
      Real.log 768+2*Real.log x := by
    calc
      _ ≤ Real.log (768*x^2) := Real.log_le_log (by positivity) hprod
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hx0.ne'), Real.log_pow]; norm_num
  calc
    Real.log (64*q*(2*x ^ (3/20 : ℝ)+10))+1 ≤
        (Real.log 768+2*Real.log x)+1 := add_le_add hlog le_rfl
    _ = A+2*Real.log x := by dsimp [A]; ring
    _ ≤ K*Real.log x := hcommon

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset
open scoped BigOperators

namespace QRHShort.CloudBatch.PrimesAPAux

/-- A transparent reduction from a uniform primitive quadratic-smoothed bound.
The smoothed estimate is the explicit unresolved analytic input to this helper. -/
theorem twistedMangoldtEstimate_of_primitive_quadratic_smoothed
    (hsmooth : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2 ≤ x → (q : ℝ) ≤ x →
      let h := x ^ ((9 : ℝ)/10)
      ‖(quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) (x+2*h) -
        2*quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) (x+h) +
        quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) x) /
          (h : ℂ)^2 - (if χ = 1 then ((x+h : ℝ) : ℂ) else 0)‖ ≤
        C*x^((11 : ℝ)/12)*(Real.log x)^2) :
    PrimeAP.TwistedMangoldtEstimate := by
  obtain ⟨C, hC, hbound⟩ := hsmooth
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  let k : ℝ := 1+Real.log 3/Real.log 2
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  apply twistedMangoldtEstimate_iff_primitive.mpr
  refine ⟨C+3*k/Real.log 2+1/(Real.log 2)^2, by positivity, ?_⟩
  intro q _ χ hprim x hx hqx
  let h : ℝ := x^((9 : ℝ)/10)
  let p : ℝ := x^((11 : ℝ)/12)
  let D : ℂ :=
    (quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) (x+2*h) -
      2*quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) (x+h) +
      quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) x) /
      (h : ℂ)^2
  let M : ℂ := if χ = 1 then (x : ℂ) else 0
  let Mh : ℂ := if χ = 1 then ((x+h : ℝ) : ℂ) else 0
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hh0 : 0 < h := Real.rpow_pos_of_pos hx0 _
  have hh1 : 1 ≤ h := Real.one_le_rpow hx1 (by norm_num)
  have hhx : h ≤ x := Real.rpow_le_self_of_one_le hx1 (by norm_num)
  have hhp : h ≤ p := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hp0 : 0 ≤ p := Real.rpow_nonneg hx0.le _
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogY0 : 0 ≤ Real.log (x+2*h) := Real.log_nonneg (by linarith)
  have hlogY : Real.log (x+2*h) ≤ k*Real.log x := by
    have hx3 : 0 < 3*x := by positivity
    have hY : 0 < x+2*h := by linarith
    have hlog3x : Real.log (x+2*h) ≤ Real.log 3+Real.log x := by
      rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx0.ne']
      exact Real.log_le_log hY (by linarith)
    have hconst : Real.log 3 ≤ (Real.log 3/Real.log 2)*Real.log x := by
      calc
        Real.log 3 = (Real.log 3/Real.log 2)*Real.log 2 := by field_simp [hlog2.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog2x (div_nonneg hlog3 hlog2.le)
    dsimp only [k]
    nlinarith
  have hlogabsorb : Real.log x ≤ (Real.log x)^2/Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    nlinarith [mul_nonneg hlogx (sub_nonneg.mpr hlog2x)]
  have herr : ‖PrimeAP.twistedPsi χ x-D‖ ≤
      (3*k/Real.log 2)*p*(Real.log x)^2 := by
    rw [norm_sub_rev]
    calc
      ‖D-PrimeAP.twistedPsi χ x‖ ≤ (2*h+1)*Real.log (x+2*h) := by
        simpa only [D, PrimeAP.twistedPsi] using
          mangoldt_quadraticPrefix_unsmoothing_norm_le χ hx hh0
      _ ≤ (3*p)*(k*Real.log x) :=
        mul_le_mul (by linarith) hlogY hlogY0 (by positivity)
      _ = (3*k*p)*Real.log x := by ring
      _ ≤ (3*k*p)*((Real.log x)^2/Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogabsorb (by positivity)
      _ = (3*k/Real.log 2)*p*(Real.log x)^2 := by ring
  have hlogsq : (Real.log 2)^2 ≤ (Real.log x)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog2x) (add_nonneg hlogx hlog2.le)]
  have hratio : 1 ≤ (Real.log x)^2/(Real.log 2)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hlog2)).mpr (by simpa using hlogsq)
  have hshift : h ≤ (1/(Real.log 2)^2)*p*(Real.log x)^2 := by
    calc
      h ≤ p := hhp
      _ ≤ p*((Real.log x)^2/(Real.log 2)^2) := le_mul_of_one_le_right hp0 hratio
      _ = _ := by ring
  have hmain : ‖Mh-M‖ ≤ h := by
    dsimp only [Mh, M]
    split_ifs with hχ
    · simp only [← Complex.ofReal_sub, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hh0.le, le_refl]
    · simp only [sub_self, norm_zero]
      exact hh0.le
  have hD : ‖D-Mh‖ ≤ C*p*(Real.log x)^2 := hbound q χ hprim x hx hqx
  change ‖PrimeAP.twistedPsi χ x-M‖ ≤ _
  calc
    _ = ‖(PrimeAP.twistedPsi χ x-D)+(D-Mh)+(Mh-M)‖ := by congr 1; abel
    _ ≤ ‖PrimeAP.twistedPsi χ x-D‖+‖D-Mh‖+‖Mh-M‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (3*k/Real.log 2)*p*(Real.log x)^2 + C*p*(Real.log x)^2 +
        (1/(Real.log 2)^2)*p*(Real.log x)^2 :=
      add_le_add (add_le_add herr hD) (hmain.trans hshift)
    _ = _ := by dsimp only [p]; ring

end QRHShort.CloudBatch.PrimesAPAux

noncomputable section
open Classical MeasureTheory Set

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Both logarithmic cubic tails are genuinely integrable. Reflection preserves
Lebesgue measure; no convergence premise is required from the caller. -/
theorem log_cubic_two_tails_integral_le {Q T : ℝ} (hQ : 1 ≤ Q) (hT : 1 ≤ T) :
    IntegrableOn (fun t : ℝ => (Real.log (Q*(|t|+4))+1)/|t|^3)
      {t : ℝ | T < |t|} ∧
      (∫ t : ℝ in {t : ℝ | T < |t|}, (Real.log (Q*(|t|+4))+1)/|t|^3) ≤
        2*(Real.log (Q*(T+4))+1)/T^2 := by
  let f : ℝ → ℝ := fun t => (Real.log (Q*(t+4))+1)/t^3
  let F : ℝ → ℝ := fun t => f |t|
  have hT0 : 0 < T := by linarith
  have hdata := log_cubic_tail_integral_le hQ hT
  have hi : IntegrableOn f (Ioi T) := hdata.1
  have hiNeg : IntegrableOn (fun t : ℝ => f (-t)) (Iio (-T)) := by
    have hn := (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hi
    simpa only [Function.comp_def, neg_preimage, neg_Ioi] using hn
  have hiPosF : IntegrableOn F (Ioi T) := by
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [F]
    rw [abs_of_pos (hT0.trans ht)]
  have hiNegF : IntegrableOn F (Iio (-T)) := by
    apply hiNeg.congr_fun _ measurableSet_Iio
    intro t ht
    dsimp only [F]
    rw [abs_of_neg (by linarith [show t < -T from ht])]
  have hpos : (∫ t : ℝ in Ioi T, F t) = ∫ t : ℝ in Ioi T, f t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [F]
    rw [abs_of_pos (hT0.trans ht)]
  have hneg : (∫ t : ℝ in Iio (-T), F t) = ∫ t : ℝ in Ioi T, f t := by
    calc
      _ = ∫ t : ℝ in Iic (-T), F t := integral_Iic_eq_integral_Iio.symm
      _ = ∫ t : ℝ in Iic (-T), f (-t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        dsimp only [F]
        rw [abs_of_neg (by linarith [show t ≤ -T from ht])]
      _ = _ := by simpa only [neg_neg] using integral_comp_neg_Iic (-T) f
  have hset : {t : ℝ | T < |t|} = Iio (-T) ∪ Ioi T := by
    ext t
    simp only [mem_setOf_eq, mem_union, Set.mem_Iio, Set.mem_Ioi]
    by_cases ht : t < 0
    · rw [abs_of_neg ht]
      constructor
      · intro hh
        exact Or.inl (by linarith)
      · rintro (hh | hh) <;> linarith
    · rw [abs_of_nonneg (le_of_not_gt ht)]
      constructor
      · exact Or.inr
      · rintro (hh | hh) <;> linarith
  have hdisj : Disjoint (Iio (-T)) (Ioi T) := by
    apply Set.disjoint_left.mpr
    intro t hn hp
    have hn' : t < -T := hn
    have hp' : T < t := hp
    linarith
  change IntegrableOn F {t : ℝ | T < |t|} ∧ _
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact hiNegF.union hiPosF
  · change (∫ t : ℝ in {t : ℝ | T < |t|}, F t) ≤ _
    rw [hset, setIntegral_union hdisj measurableSet_Ioi hiNegF hiPosF, hneg, hpos]
    calc
      _ ≤ (Real.log (Q*(T+4))+1)/T^2+(Real.log (Q*(T+4))+1)/T^2 :=
        add_le_add hdata.2 hdata.2
      _ = _ := by ring

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical MeasureTheory Set Complex
open scoped ComplexConjugate

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

def verticalReciprocal (σ t : ℝ) : ℝ := ‖(σ : ℂ) + (t : ℂ)*I‖⁻¹

theorem verticalReciprocal_continuous {σ : ℝ} (hσ : 0 < σ) :
    Continuous (verticalReciprocal σ) := by
  have hs (t : ℝ) : σ ≤ ‖(σ : ℂ) + (t : ℂ)*I‖ := by
    simpa using Complex.re_le_norm ((σ : ℂ) + (t : ℂ)*I)
  unfold verticalReciprocal
  apply Continuous.inv₀ (by fun_prop : Continuous (fun t : ℝ => ‖(σ : ℂ)+(t : ℂ)*I‖))
  intro t
  exact (hσ.trans_le (hs t)).ne'

theorem verticalReciprocal_even (σ t : ℝ) :
    verticalReciprocal σ (-t) = verticalReciprocal σ t := by
  have he : (σ : ℂ) + ((-t : ℝ) : ℂ)*I = conj ((σ : ℂ)+(t : ℂ)*I) := by
    apply Complex.ext <;> simp
  simp only [verticalReciprocal, he, Complex.norm_conj]

/-- The reciprocal vertical norm has only logarithmic integral growth.
Its actual integrability and the central contribution are retained explicitly. -/
theorem verticalReciprocal_intervalIntegral_le {σ T : ℝ} (hσ : 0 < σ) (hT : 1 ≤ T) :
    IntervalIntegrable (verticalReciprocal σ) volume (-T) T ∧
      (∫ t in (-T)..T, verticalReciprocal σ t) ≤ 2/σ + 2*Real.log T := by
  let f : ℝ → ℝ := verticalReciprocal σ
  have hfc : Continuous f := verticalReciprocal_continuous hσ
  have hs (t : ℝ) : σ ≤ ‖(σ : ℂ) + (t : ℂ)*I‖ := by
    simpa using Complex.re_le_norm ((σ : ℂ) + (t : ℂ)*I)
  have htNorm (t : ℝ) : t ≤ ‖(σ : ℂ) + (t : ℂ)*I‖ := by
    simpa using Complex.im_le_norm ((σ : ℂ) + (t : ℂ)*I)
  have hsmall : (∫ t in (0 : ℝ)..1, f t) ≤ σ⁻¹ := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, σ⁻¹ := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hfc.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
        intro t ht
        exact inv_anti₀ hσ (hs t)
      _ = σ⁻¹ := by simp
  have hInv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    change t ≠ 0
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  have hT0 : 0 < T := by linarith
  have hlarge : (∫ t in (1 : ℝ)..T, f t) ≤ Real.log T := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..T, t⁻¹ := by
        apply intervalIntegral.integral_mono_on hT (hfc.intervalIntegrable 1 T) hInv
        intro t ht
        exact inv_anti₀ (by linarith [ht.1] : 0 < t) (htNorm t)
      _ = Real.log T := by rw [integral_inv_of_pos zero_lt_one hT0]; simp
  have hpos : (∫ t in (0 : ℝ)..T, f t) ≤ σ⁻¹+Real.log T := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfc.intervalIntegrable 0 1) (hfc.intervalIntegrable 1 T)]
    exact add_le_add hsmall hlarge
  have hneg : (∫ t in (-T)..(0 : ℝ), f t) = ∫ t in (0 : ℝ)..T, f t := by
    have he := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := T)
    simpa only [f, verticalReciprocal_even, neg_zero] using he.symm
  refine ⟨hfc.intervalIntegrable (-T) T, ?_⟩
  change (∫ t in (-T)..T, f t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hfc.intervalIntegrable (-T) 0) (hfc.intervalIntegrable 0 T), hneg]
  simpa only [div_eq_mul_inv] using (by linarith :
    (∫ t in (0 : ℝ)..T, f t) + (∫ t in (0 : ℝ)..T, f t) ≤
      2*σ⁻¹+2*Real.log T)

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Finset MeasureTheory Filter Set Asymptotics Complex Metric
open scoped BigOperators Topology

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- One absolute constant controls the actual logarithmic derivatives of all
primitive characters on the distant right Perron tails. The principal case is
reduced to level one by its actual conductor, and its pole is retained. -/
theorem primitive_LFunction_right_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hZ : QRHShort.DirichletZeroFreeStatement)
      (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → 1 ≤ |z.im| →
        ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤
          C*(Real.log (64*(q:ℝ)*(|z.im|+4))+1) := by
  let d : ℝ := Real.log (15/14)
  let p : ℝ := 1+Real.log 14/d
  let B : ℝ := 12/d+96*p
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hp : 0 ≤ p := by
    dsimp only [p]
    exact add_nonneg zero_le_one (div_nonneg (Real.log_nonneg (by norm_num)) hd.le)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨2*B+97, by positivity, ?_⟩
  intro hZ q _ χ hprim z hzlo hzhi him
  let A : ℝ := Real.log (64*(q:ℝ)*(|z.im|+4))
  have hq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos q)
  have hq0 : 0 < (q:ℝ) := by linarith
  have hv : 0 < |z.im|+4 := by positivity
  have hA : 0 ≤ A := by
    apply Real.log_nonneg
    have hv4 : 4 ≤ |z.im|+4 := by linarith [abs_nonneg z.im]
    nlinarith
  have hfinish {E : ℝ} (hE : E ≤ 2*A)
      (hb : ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤ B*E+97) :
      ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤ (2*B+97)*(A+1) := by
    have hm := mul_le_mul_of_nonneg_left hE hB
    nlinarith
  change ‖logDeriv (DirichletCharacter.LFunction χ) z‖ ≤ (2*B+97)*(A+1)
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by
      have hh : (1 : DirichletCharacter ℂ q).conductor=q := hprim
      rw [DirichletCharacter.conductor_one] at hh
      exact hh.symm
    subst q
    have hE : Real.log (64*(|z.im|+4)^2) ≤ 2*A := by
      dsimp only [A]
      norm_num only [Nat.cast_one, mul_one]
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hv.ne'), Real.log_pow,
        Real.log_mul (by norm_num) hv.ne']
      norm_num only
      nlinarith [Real.log_nonneg (by norm_num : (1:ℝ)≤64)]
    apply hfinish hE
    have hb := zeta_right_logDeriv_le hZ hzlo hzhi him
    convert hb using 1 <;> dsimp only [B, p, d] <;> ring
  · have hE : Real.log (32*(q:ℝ)*(|z.im|+4)) ≤ 2*A := by
      have hm : Real.log (32*(q:ℝ)*(|z.im|+4)) ≤ A := by
        apply Real.log_le_log (by positivity)
        nlinarith [mul_pos hq0 hv]
      linarith
    apply hfinish hE
    have hb := LFunction_right_logDeriv_le hZ χ hχ hzlo hzhi
    refine hb.trans ?_
    dsimp only [B, p, d]
    have he : 12*(Real.log (32*(q:ℝ)*(|z.im|+4))/Real.log (15/14)) +
        96*((1+Real.log 14/Real.log (15/14))*Real.log (32*(q:ℝ)*(|z.im|+4))+1) =
        (12/Real.log (15/14)+96*(1+Real.log 14/Real.log (15/14)))*
          Real.log (32*(q:ℝ)*(|z.im|+4))+96 := by ring
    rw [he]
    linarith

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology
namespace QRHShort.CloudBatch.PrimesAPExplicitAux
open PrimesAPRectAux

def secondQuotient (f : ℝ → ℂ) (x h : ℝ) : ℂ :=
  (f (x+2*h)-2*f (x+h)+f x)/(h:ℂ)^2

def kernelDifference (x h : ℝ) (s : ℂ) : ℂ :=
  secondQuotient (fun y => quadraticPerronKernel y s) x h

theorem secondQuotient_add (f g : ℝ → ℂ) (x h : ℝ) :
    secondQuotient (fun y => f y+g y) x h = secondQuotient f x h+secondQuotient g x h := by
  unfold secondQuotient
  ring

theorem secondQuotient_sub (f g : ℝ → ℂ) (x h : ℝ) :
    secondQuotient (fun y => f y-g y) x h = secondQuotient f x h-secondQuotient g x h := by
  unfold secondQuotient
  ring

theorem secondQuotient_const_mul (c : ℂ) (f : ℝ → ℂ) (x h : ℝ) :
    secondQuotient (fun y => c*f y) x h = c*secondQuotient f x h := by
  unfold secondQuotient
  ring

theorem integrable_secondQuotient {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℝ → α → ℂ) (x h : ℝ) (h0 : Integrable (F x) μ)
    (h1 : Integrable (F (x+h)) μ) (h2 : Integrable (F (x+2*h)) μ) :
    Integrable (fun t => secondQuotient (fun y => F y t) x h) μ :=
  ((h2.sub (h1.const_mul 2)).add h0).div_const ((h:ℂ)^2)

theorem integral_secondQuotient {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℝ → α → ℂ) (x h : ℝ) (h0 : Integrable (F x) μ)
    (h1 : Integrable (F (x+h)) μ) (h2 : Integrable (F (x+2*h)) μ) :
    (∫ t, secondQuotient (fun y => F y t) x h ∂μ) =
      secondQuotient (fun y => ∫ t, F y t ∂μ) x h := by
  dsimp only [secondQuotient]
  rw [integral_div]
  have ha := integral_add (h2.sub (h1.const_mul 2)) h0
  simp only [Pi.sub_apply] at ha
  rw [ha,integral_sub h2 (h1.const_mul 2),integral_const_mul]

theorem intervalIntegrable_secondQuotient (F : ℝ → ℝ → ℂ) (x h a b : ℝ)
    (h0 : IntervalIntegrable (F x) volume a b)
    (h1 : IntervalIntegrable (F (x+h)) volume a b)
    (h2 : IntervalIntegrable (F (x+2*h)) volume a b) :
    IntervalIntegrable (fun t => secondQuotient (fun y => F y t) x h) volume a b :=
  ((h2.sub (h1.const_mul 2)).add h0).div_const ((h:ℂ)^2)

theorem intervalIntegral_secondQuotient (F : ℝ → ℝ → ℂ) (x h a b : ℝ)
    (h0 : IntervalIntegrable (F x) volume a b)
    (h1 : IntervalIntegrable (F (x+h)) volume a b)
    (h2 : IntervalIntegrable (F (x+2*h)) volume a b) :
    (∫ t : ℝ in a..b, secondQuotient (fun y => F y t) x h) =
      secondQuotient (fun y => ∫ t : ℝ in a..b, F y t) x h := by
  unfold secondQuotient
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (h2.sub (h1.const_mul 2)) h0,
    intervalIntegral.integral_sub h2 (h1.const_mul 2),intervalIntegral.integral_const_mul]

theorem rectIntegrable_secondQuotient (F : ℝ → ℂ → ℂ) (x h a c T : ℝ)
    (h0 : RectIntegrable a c (-T) T (F x))
    (h1 : RectIntegrable a c (-T) T (F (x+h)))
    (h2 : RectIntegrable a c (-T) T (F (x+2*h))) :
    RectIntegrable a c (-T) T (fun s => secondQuotient (fun y => F y s) x h) := by
  exact ⟨intervalIntegrable_secondQuotient _ _ _ _ _ h0.1 h1.1 h2.1,
    intervalIntegrable_secondQuotient _ _ _ _ _ h0.2.1 h1.2.1 h2.2.1,
    intervalIntegrable_secondQuotient _ _ _ _ _ h0.2.2.1 h1.2.2.1 h2.2.2.1,
    intervalIntegrable_secondQuotient _ _ _ _ _ h0.2.2.2 h1.2.2.2 h2.2.2.2⟩

/-- All finite edges and the actual infinite tail are differenced inside their
integrals, using their proved integrability at the three smoothing parameters. -/
theorem contourError_secondQuotient (F : ℝ → ℂ → ℂ) (x h a c T : ℝ)
    (h0 : RectIntegrable a c (-T) T (F x))
    (h1 : RectIntegrable a c (-T) T (F (x+h)))
    (h2 : RectIntegrable a c (-T) T (F (x+2*h)))
    (hi0 : Integrable (fun t : ℝ => F x ((c:ℂ)+t*I)))
    (hi1 : Integrable (fun t : ℝ => F (x+h) ((c:ℂ)+t*I)))
    (hi2 : Integrable (fun t : ℝ => F (x+2*h) ((c:ℂ)+t*I))) :
    secondQuotient (fun y => contourError (F y) a c T) x h =
      contourError (fun s => secondQuotient (fun y => F y s) x h) a c T := by
  have hb := intervalIntegral_secondQuotient (fun y t => F y ((t:ℂ)+(-T)*I))
    x h a c (by simpa only [Complex.ofReal_neg] using h0.1)
    (by simpa only [Complex.ofReal_neg] using h1.1)
    (by simpa only [Complex.ofReal_neg] using h2.1)
  have hu := intervalIntegral_secondQuotient (fun y t => F y ((t:ℂ)+T*I))
    x h a c h0.2.1 h1.2.1 h2.2.1
  have hl := intervalIntegral_secondQuotient (fun y t => F y ((a:ℂ)+t*I))
    x h (-T) T h0.2.2.2 h1.2.2.2 h2.2.2.2
  have he := integral_secondQuotient (volume.restrict {t : ℝ | T < |t|})
    (fun y t => F y ((c:ℂ)+t*I)) x h hi0.integrableOn hi1.integrableOn hi2.integrableOn
  unfold contourError
  rw [secondQuotient_add,secondQuotient_add,secondQuotient_const_mul,
    secondQuotient_const_mul,secondQuotient_sub,secondQuotient_const_mul,
    ← hl,← hb,← hu,← he]

theorem weighted_kernel_secondQuotient (D : ℂ → ℂ) (x h : ℝ) (s : ℂ) :
    secondQuotient (fun y => D s*quadraticPerronKernel y s) x h = D s*kernelDifference x h s :=
  secondQuotient_const_mul (D s) (fun y => quadraticPerronKernel y s) x h

end QRHShort.CloudBatch.PrimesAPExplicitAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology
namespace QRHShort.CloudBatch.PrimesAPExplicitAux
open PrimesAPGrowthAux PrimesAPRectAux

theorem kernelDifference_vertical_bound {x h : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hs : 0 < s.re) :
    ‖kernelDifference x h s‖ ≤ (x+2*h)^s.re/‖s‖ := by
  simpa only [kernelDifference,secondQuotient,quadraticPerronKernel,mul_div_assoc] using
    quadratic_cpow_difference_norm_le hs hx hh

theorem kernelDifference_height_bound {x h c : ℝ} {s : ℂ}
    (hx : 1 ≤ x) (hh : 0 < h) (hc : 1 ≤ c) (hs : s.re ≤ c) (him : 0 < |s.im|) :
    ‖kernelDifference x h s‖ ≤ 4*(x+2*h)^(c+2)/(h^2*|s.im|^3) := by
  exact quadratic_cpow_difference_height_norm_le hx hh hc hs him

theorem left_difference_integral_bound (D : ℂ → ℂ) {x h a T M : ℝ}
    (hx : 0 < x) (hh : 0 < h) (ha : 0 < a) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hD : ∀ t ∈ Set.Icc (-T) T, ‖D ((a:ℂ)+t*I)‖ ≤ M) :
    ‖∫ t : ℝ in -T..T, D ((a:ℂ)+t*I)*kernelDifference x h ((a:ℂ)+t*I)‖ ≤
      M*(x+2*h)^a*(2/a+2*Real.log T) := by
  obtain ⟨hint,hbound⟩ := verticalReciprocal_intervalIntegral_le ha hT
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖D ((a:ℂ)+t*I)*kernelDifference x h ((a:ℂ)+t*I)‖ ≤
        (M*(x+2*h)^a)*verticalReciprocal a t := by
    have hk : ‖kernelDifference x h ((a:ℂ)+t*I)‖ ≤
        (x+2*h)^a/‖(a:ℂ)+t*I‖ := by
      simpa using kernelDifference_vertical_bound hx hh (by simpa using ha : 0 < ((a:ℂ)+t*I).re)
    rw [norm_mul]
    refine (mul_le_mul (hD t ht) hk (norm_nonneg _) hM).trans_eq ?_
    unfold verticalReciprocal
    ring
  calc
    _ ≤ ∫ t : ℝ in -T..T, (M*(x+2*h)^a)*verticalReciprocal a t := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall (fun t ht => hpoint t (Set.Ioc_subset_Icc_self ht)))
      exact hint.const_mul _
    _ = (M*(x+2*h)^a)*(∫ t : ℝ in -T..T, verticalReciprocal a t) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

theorem horizontal_difference_integral_bound (D : ℂ → ℂ) {x h a c T v M : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hc : 1 ≤ c) (hac : a ≤ c) (hT : 0 < T)
    (hv : |v| = T) (hM : 0 ≤ M)
    (hD : ∀ u ∈ Set.Icc a c, ‖D ((u:ℂ)+v*I)‖ ≤ M) :
    ‖∫ u : ℝ in a..c, D ((u:ℂ)+v*I)*kernelDifference x h ((u:ℂ)+v*I)‖ ≤
      (c-a)*M*4*(x+2*h)^(c+2)/(h^2*T^3) := by
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc a c) :
      ‖D ((u:ℂ)+v*I)*kernelDifference x h ((u:ℂ)+v*I)‖ ≤
        M*(4*(x+2*h)^(c+2)/(h^2*T^3)) := by
    have hk : ‖kernelDifference x h ((u:ℂ)+v*I)‖ ≤ 4*(x+2*h)^(c+2)/(h^2*T^3) := by
      simpa [hv] using kernelDifference_height_bound hx hh hc
        (by simpa using hu.2 : ((u:ℂ)+v*I).re ≤ c) (by simpa [hv] using hT : 0 < |((u:ℂ)+v*I).im|)
    rw [norm_mul]
    exact mul_le_mul (hD u hu) hk (norm_nonneg _) hM
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := c) (fun u hu => hpoint u (by
      rw [Set.uIoc_of_le hac] at hu
      exact Set.Ioc_subset_Icc_self hu))
  rw [abs_of_nonneg (sub_nonneg.mpr hac)] at hb
  refine hb.trans_eq ?_
  ring

theorem tail_difference_integral_bound (D : ℂ → ℂ) {x h c T Q M : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hc : 1 ≤ c) (hT : 1 ≤ T) (hQ : 1 ≤ Q) (hM : 0 ≤ M)
    (hD : ∀ t : ℝ, T < |t| →
      ‖D ((c:ℂ)+t*I)‖ ≤ M*(Real.log (Q*(|t|+4))+1)) :
    ‖∫ t : ℝ in {t | T < |t|}, D ((c:ℂ)+t*I)*kernelDifference x h ((c:ℂ)+t*I)‖ ≤
      8*M*(x+2*h)^(c+2)/h^2*((Real.log (Q*(T+4))+1)/T^2) := by
  obtain ⟨hint,hbound⟩ := log_cubic_two_tails_integral_le hQ hT
  let A : ℝ := 4*M*(x+2*h)^(c+2)/h^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (t : ℝ) (ht : T < |t|) :
      ‖D ((c:ℂ)+t*I)*kernelDifference x h ((c:ℂ)+t*I)‖ ≤
        A*((Real.log (Q*(|t|+4))+1)/|t|^3) := by
    have hlog : 0 ≤ Real.log (Q*(|t|+4))+1 := by
      have hp : 1 ≤ Q*(|t|+4) := by
        calc
          1 ≤ 1*(|t|+4) := by linarith [abs_nonneg t]
          _ ≤ Q*(|t|+4) := mul_le_mul_of_nonneg_right hQ (by positivity)
      linarith [Real.log_nonneg hp]
    have hk : ‖kernelDifference x h ((c:ℂ)+t*I)‖ ≤ 4*(x+2*h)^(c+2)/(h^2*|t|^3) := by
      simpa using kernelDifference_height_bound hx hh hc
        (by simp : ((c:ℂ)+t*I).re ≤ c) (by simpa using (by linarith : 0 < |t|) : 0 < |((c:ℂ)+t*I).im|)
    rw [norm_mul]
    refine (mul_le_mul (hD t ht) hk (norm_nonneg _) (mul_nonneg hM hlog)).trans_eq ?_
    dsimp only [A]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  calc
    _ ≤ ∫ t : ℝ in {t | T < |t|}, A*((Real.log (Q*(|t|+4))+1)/|t|^3) := by
      apply MeasureTheory.norm_integral_le_of_norm_le (hint.const_mul A)
      filter_upwards [ae_restrict_mem ((isOpen_lt continuous_const continuous_abs).measurableSet)] with t ht
      exact hpoint t ht
    _ = A * ∫ t : ℝ in {t | T < |t|}, (Real.log (Q*(|t|+4))+1)/|t|^3 := integral_const_mul _ _
    _ ≤ A*(2*(Real.log (Q*(T+4))+1)/T^2) := mul_le_mul_of_nonneg_left hbound hA
    _ = _ := by dsimp only [A]; ring

theorem norm_contourError_le (F : ℂ → ℂ) (a c T : ℝ) :
    ‖contourError F a c T‖ ≤
      ‖∫ t : ℝ in -T..T, F ((a:ℂ)+t*I)‖ +
      ‖∫ u : ℝ in a..c, F ((u:ℂ)+(-T)*I)‖ +
      ‖∫ u : ℝ in a..c, F ((u:ℂ)+T*I)‖ +
      ‖∫ t : ℝ in {t | T < |t|}, F ((c:ℂ)+t*I)‖ := by
  have hr : ‖(1/(2*Real.pi):ℂ)‖ ≤ 1 := by
    have hn : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
    simp only [norm_div,norm_one,norm_mul,hn,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hi : ‖(I/(2*Real.pi):ℂ)‖ ≤ 1 := by
    simpa only [norm_div,norm_I,norm_one] using hr
  have hreal (z : ℂ) : ‖(1/(2*Real.pi):ℂ)*z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg z) hr
  have himag (z : ℂ) : ‖(I/(2*Real.pi):ℂ)*z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg z) hi
  unfold contourError
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add (hreal _) (himag _))) (hreal _)).trans ?_
  have h := norm_sub_le (∫ u : ℝ in a..c, F ((u:ℂ)+(-T)*I)) (∫ u : ℝ in a..c, F ((u:ℂ)+T*I))
  linarith

theorem contour_difference_error_bound (D : ℂ → ℂ) {x h a c T Q M R : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (ha : 0 < a) (hc : 1 ≤ c) (hac : a ≤ c)
    (hT : 1 ≤ T) (hQ : 1 ≤ Q) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hleft : ∀ t ∈ Set.Icc (-T) T, ‖D ((a:ℂ)+t*I)‖ ≤ M)
    (hbottom : ∀ u ∈ Set.Icc a c, ‖D ((u:ℂ)+(-T)*I)‖ ≤ M)
    (htop : ∀ u ∈ Set.Icc a c, ‖D ((u:ℂ)+T*I)‖ ≤ M)
    (hright : ∀ t : ℝ, T < |t| → ‖D ((c:ℂ)+t*I)‖ ≤ R*(Real.log (Q*(|t|+4))+1)) :
    ‖contourError (fun s => D s*kernelDifference x h s) a c T‖ ≤
      M*(x+2*h)^a*(2/a+2*Real.log T) +
      8*(c-a)*M*(x+2*h)^(c+2)/(h^2*T^3) +
      8*R*(x+2*h)^(c+2)/h^2*((Real.log (Q*(T+4))+1)/T^2) := by
  have hl := left_difference_integral_bound D (by linarith : 0 < x) hh ha hT hM hleft
  have hb := horizontal_difference_integral_bound D (T := T) (v := -T) hx hh hc hac (by linarith : 0 < T)
    (by rw [abs_neg,abs_of_pos (by linarith : 0 < T)]) hM
    (by simpa only [Complex.ofReal_neg] using hbottom)
  simp only [Complex.ofReal_neg] at hb
  have hu := horizontal_difference_integral_bound D hx hh hc hac (by linarith : 0 < T)
    (abs_of_pos (by linarith : 0 < T)) hM htop
  have he := tail_difference_integral_bound D hx hh hc hT hQ hR hright
  refine (norm_contourError_le _ a c T).trans ?_
  refine (add_le_add (add_le_add (add_le_add hl hb) hu) he).trans_eq ?_
  ring

end QRHShort.CloudBatch.PrimesAPExplicitAux

noncomputable section

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- Uniform control of the left contour's power for every selected abscissa. -/
theorem scale_left_power_bound {x a : ℝ} (hx : 2 ≤ x)
    (ha : a ∈ Set.Icc (3/4 : ℝ) (19/25 : ℝ)) :
    x ^ (3/20 : ℝ) * (x+2*x ^ (9/10 : ℝ))^a ≤ 3*x ^ (91/100 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have ha1 : a ≤ 1 := by linarith [ha.2]
  obtain ⟨hh0, hhx, hY1, hYx⟩ := scale_parameter_ranges hx
  have hbase : x+2*x ^ (9/10 : ℝ) ≤ 3*x := by linarith
  have hpow : (x+2*x ^ (9/10 : ℝ))^a ≤ 3*x ^ (19/25 : ℝ) := by
    calc
      (x+2*x ^ (9/10 : ℝ))^a ≤ (3*x)^a :=
        Real.rpow_le_rpow (by positivity) hbase ha0
      _ = (3 : ℝ)^a*x^a := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 3*x ^ (19/25 : ℝ) :=
        mul_le_mul (Real.rpow_le_self_of_one_le (by norm_num) ha1)
          (Real.rpow_le_rpow_of_exponent_le hx1 ha.2)
          (Real.rpow_nonneg hx0.le _) (by norm_num)
  calc
    x ^ (3/20 : ℝ) * (x+2*x ^ (9/10 : ℝ))^a ≤
        x ^ (3/20 : ℝ)*(3*x ^ (19/25 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0.le _)
    _ = 3*x ^ (91/100 : ℝ) := by
      rw [show (91/100 : ℝ) = 3/20+19/25 by norm_num, Real.rpow_add hx0]
      ring

/-- The purely real three-term contour error reduces to its left-edge term
and a common positive tail scale. Every analytic input is absent here. -/
theorem contour_raw_three_term_bound {CL CR X h Y a c L T P J : ℝ}
    (hCL : 0 ≤ CL) (hCR : 0 ≤ CR) (hX : 0 ≤ X)
    (hh : 0 < h) (hY : 0 < Y) (hTY : Y ≤ T) (hL : 1 ≤ L)
    (hafrac : 2/a ≤ 3) (hca0 : 0 ≤ c-a) (hca2 : c-a ≤ 2)
    (hlogT : Real.log T ≤ L) (hJ : J ≤ L) (hP : 0 ≤ P) :
    (CL*Y*L^2)*X^a*(2/a+2*Real.log T) +
        8*(c-a)*(CL*Y*L^2)*P/(h^2*T^3) +
        8*CR*P/h^2*(J/T^2) ≤
      5*CL*(Y*X^a)*L^3 +
        (16*CL+8*CR)*L^2*(P/(h^2*Y^2)) := by
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 < T := hY.trans_le hTY
  have hfac : 2/a+2*Real.log T ≤ 5*L := by linarith
  have hleft : (CL*Y*L^2)*X^a*(2/a+2*Real.log T) ≤ 5*CL*(Y*X^a)*L^3 := by
    calc
      (CL*Y*L^2)*X^a*(2/a+2*Real.log T) ≤ (CL*Y*L^2)*X^a*(5*L) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = 5*CL*(Y*X^a)*L^3 := by ring
  have hnum : 8*(c-a)*(CL*Y*L^2)*P ≤ 16*CL*Y*L^2*P := by
    have hmul := mul_le_mul_of_nonneg_right hca2
      (show 0 ≤ 8*CL*Y*L^2*P by positivity)
    convert hmul using 1 <;> ring
  have hden3 : h^2*Y^3 ≤ h^2*T^3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY.le hTY 3) (sq_nonneg h)
  have hhorizontal : 8*(c-a)*(CL*Y*L^2)*P/(h^2*T^3) ≤
      16*CL*L^2*(P/(h^2*Y^2)) := by
    calc
      8*(c-a)*(CL*Y*L^2)*P/(h^2*T^3) ≤ (16*CL*Y*L^2*P)/(h^2*T^3) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (16*CL*Y*L^2*P)/(h^2*Y^3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden3
      _ = 16*CL*L^2*(P/(h^2*Y^2)) := by
        field_simp [hh.ne', hY.ne']
        <;> ring
  have hden2 : Y^2 ≤ T^2 := pow_le_pow_left₀ hY.le hTY 2
  have hratio : J/T^2 ≤ L/Y^2 := by
    calc
      J/T^2 ≤ L/T^2 := div_le_div_of_nonneg_right hJ (sq_nonneg T)
      _ ≤ L/Y^2 := div_le_div_of_nonneg_left hL0 (by positivity) hden2
  have hLsq : L ≤ L^2 := by
    have hmul := mul_le_mul_of_nonneg_left hL hL0
    nlinarith
  have hright : 8*CR*P/h^2*(J/T^2) ≤ 8*CR*L^2*(P/(h^2*Y^2)) := by
    calc
      8*CR*P/h^2*(J/T^2) ≤ 8*CR*P/h^2*(L/Y^2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (8*CR*(P/(h^2*Y^2)))*L := by
        field_simp [hh.ne', hY.ne']
        <;> ring
      _ ≤ (8*CR*(P/(h^2*Y^2)))*L^2 :=
        mul_le_mul_of_nonneg_left hLsq (by positivity)
      _ = 8*CR*L^2*(P/(h^2*Y^2)) := by ring
  calc
    (CL*Y*L^2)*X^a*(2/a+2*Real.log T) +
        8*(c-a)*(CL*Y*L^2)*P/(h^2*T^3) + 8*CR*P/h^2*(J/T^2) ≤
      5*CL*(Y*X^a)*L^3 + 16*CL*L^2*(P/(h^2*Y^2)) +
        8*CR*L^2*(P/(h^2*Y^2)) := add_le_add (add_le_add hleft hhorizontal) hright
    _ = 5*CL*(Y*X^a)*L^3+(16*CL+8*CR)*L^2*(P/(h^2*Y^2)) := by ring

/-- The literal real contour error has the target uniform power-logarithmic
bound, with its constant chosen before all tested scales and contour points. -/
theorem contour_error_scale_bound (CL CR : ℝ) (hCL : 0 ≤ CL) (hCR : 0 ≤ CR) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x q a T : ℝ, 2 ≤ x → 1 ≤ q → q ≤ x →
      a ∈ Set.Icc (3/4 : ℝ) (19/25 : ℝ) →
      T ∈ Set.Icc (x ^ (3/20 : ℝ)) (2*x ^ (3/20 : ℝ)) →
      let h := x ^ (9/10 : ℝ)
      let Y := x ^ (3/20 : ℝ)
      let c := 1+1/(1+Real.log x)
      let L := Real.log (64*q*(2*Y+10))+1
      let M := CL*Y*L^2
      M*(x+2*h)^a*(2/a+2*Real.log T) +
        8*(c-a)*M*(x+2*h)^(c+2)/(h^2*T^3) +
        8*CR*(x+2*h)^(c+2)/h^2*((Real.log ((64*q)*(T+4))+1)/T^2) ≤
      C*x ^ (11/12 : ℝ)*(Real.log x)^2 := by
  obtain ⟨K, hK0, hK⟩ := scale_augmented_log_bound
  let C : ℝ := 2250*CL*K^3 + 81*Real.exp 1*(16*CL+8*CR)*K^2
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro x q a T hx hq hqx ha hTrange
  let h : ℝ := x ^ (9/10 : ℝ)
  let Y : ℝ := x ^ (3/20 : ℝ)
  let c : ℝ := 1+1/(1+Real.log x)
  let L : ℝ := Real.log (64*q*(2*Y+10))+1
  let X : ℝ := x+2*h
  let P : ℝ := X^(c+2)
  let J : ℝ := Real.log ((64*q)*(T+4))+1
  change (CL*Y*L^2)*X^a*(2/a+2*Real.log T) +
      8*(c-a)*(CL*Y*L^2)*P/(h^2*T^3) + 8*CR*P/h^2*(J/T^2) ≤
    C*x ^ (11/12 : ℝ)*(Real.log x)^2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq0 : 0 < q := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨hh0, hhx, hY1, hYx⟩ := scale_parameter_ranges hx
  change 0 < h at hh0
  change h ≤ x at hhx
  change 1 ≤ Y at hY1
  change Y ≤ x at hYx
  have hY0 : 0 < Y := by linarith
  have hTY : Y ≤ T := hTrange.1
  have hT2Y : T ≤ 2*Y := hTrange.2
  have hT0 : 0 < T := hY0.trans_le hTY
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hP0 : 0 ≤ P := Real.rpow_nonneg hX0 _
  have h64q : 1 ≤ 64*q := by linarith
  have hS0 : 0 ≤ 2*Y+10 := by linarith
  have harg1 : 1 ≤ 64*q*(2*Y+10) := by
    have hmul := mul_le_mul_of_nonneg_right h64q hS0
    linarith
  have hL1 : 1 ≤ L := by
    have hl := Real.log_nonneg harg1
    dsimp [L]
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hLT : Real.log T ≤ L := by
    have hargT : T ≤ 64*q*(2*Y+10) := by
      have hmul := mul_le_mul_of_nonneg_right h64q hS0
      linarith
    have hl := Real.log_le_log hT0 hargT
    dsimp [L]
    linarith
  have hJL : J ≤ L := by
    have hprod : (64*q)*(T+4) ≤ (64*q)*(2*Y+10) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hl := Real.log_le_log (show 0 < (64*q)*(T+4) by positivity) hprod
    exact add_le_add hl le_rfl
  have hLK : L ≤ K*Real.log x := by
    simpa only [L, Y] using hK x q hx hq hqx
  obtain ⟨hc1, hc2, hPbound⟩ := scale_contour_power_bound hx
  change 1 < c at hc1
  change c ≤ 2 at hc2
  change P ≤ 81*Real.exp 1*x^3 at hPbound
  have ha0 : 0 < a := by linarith [ha.1]
  have hafrac : 2/a ≤ 3 := (div_le_iff₀ ha0).mpr (by linarith [ha.1])
  have hca0 : 0 ≤ c-a := by linarith [ha.2]
  have hca2 : c-a ≤ 2 := by linarith [ha.1]
  have hraw := contour_raw_three_term_bound hCL hCR hX0 hh0 hY0 hTY hL1
    hafrac hca0 hca2 hLT hJL hP0
  have hshape : Y*X^a ≤ 3*x ^ (91/100 : ℝ) := by
    simpa only [Y, X, h] using scale_left_power_bound hx ha
  have hLpow2 : L^2 ≤ (K*Real.log x)^2 := pow_le_pow_left₀ hL0 hLK 2
  have hLpow3 : L^3 ≤ (K*Real.log x)^3 := pow_le_pow_left₀ hL0 hLK 3
  have hleft : 5*CL*(Y*X^a)*L^3 ≤
      (2250*CL*K^3)*x ^ (11/12 : ℝ)*(Real.log x)^2 := by
    calc
      5*CL*(Y*X^a)*L^3 ≤ 5*CL*(3*x ^ (91/100 : ℝ))*L^3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshape (by positivity)) (by positivity)
      _ ≤ 15*CL*x ^ (91/100 : ℝ)*(K*Real.log x)^3 := by
        have hm := mul_le_mul_of_nonneg_left hLpow3
          (show 0 ≤ 15*CL*x ^ (91/100 : ℝ) by positivity)
        convert hm using 1 <;> ring
      _ = (15*CL*K^3)*(x ^ (91/100 : ℝ)*(Real.log x)^3) := by ring
      _ ≤ (15*CL*K^3)*(150*x ^ (11/12 : ℝ)*(Real.log x)^2) :=
        mul_le_mul_of_nonneg_left (scale_log_cube_absorb hx) (by positivity)
      _ = (2250*CL*K^3)*x ^ (11/12 : ℝ)*(Real.log x)^2 := by ring
  have htail : x^3/(h^2*Y^2) = x ^ (9/10 : ℝ) := by
    simpa only [h, Y] using scale_tail_identity hx0
  have hR : P/(h^2*Y^2) ≤ 81*Real.exp 1*x ^ (11/12 : ℝ) := by
    calc
      P/(h^2*Y^2) ≤ (81*Real.exp 1*x^3)/(h^2*Y^2) :=
        div_le_div_of_nonneg_right hPbound (by positivity)
      _ = (81*Real.exp 1)*(x^3/(h^2*Y^2)) := by ring
      _ = (81*Real.exp 1)*x ^ (9/10 : ℝ) := by rw [htail]
      _ ≤ 81*Real.exp 1*x ^ (11/12 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by positivity)
  have hright : (16*CL+8*CR)*L^2*(P/(h^2*Y^2)) ≤
      (81*Real.exp 1*(16*CL+8*CR)*K^2)*x ^ (11/12 : ℝ)*(Real.log x)^2 := by
    calc
      (16*CL+8*CR)*L^2*(P/(h^2*Y^2)) ≤
          ((16*CL+8*CR)*(K*Real.log x)^2)*(81*Real.exp 1*x ^ (11/12 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLpow2 (by positivity)) hR (by positivity) (by positivity)
      _ = (81*Real.exp 1*(16*CL+8*CR)*K^2)*x ^ (11/12 : ℝ)*(Real.log x)^2 := by ring
  calc
    (CL*Y*L^2)*X^a*(2/a+2*Real.log T) +
        8*(c-a)*(CL*Y*L^2)*P/(h^2*T^3) + 8*CR*P/h^2*(J/T^2) ≤
      5*CL*(Y*X^a)*L^3+(16*CL+8*CR)*L^2*(P/(h^2*Y^2)) := hraw
    _ ≤ (2250*CL*K^3)*x ^ (11/12 : ℝ)*(Real.log x)^2 +
        (81*Real.exp 1*(16*CL+8*CR)*K^2)*x ^ (11/12 : ℝ)*(Real.log x)^2 := add_le_add hleft hright
    _ = C*x ^ (11/12 : ℝ)*(Real.log x)^2 := by dsimp [C]; ring

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section

namespace QRHShort.CloudBatch.PrimesAPGrowthAux

/-- One absolute constant bounds both raw leading zero contributions at all
the permitted smoothing and height scales. -/
theorem scale_zero_leading_bounds :
    ∃ CZ : ℝ, 0 ≤ CZ ∧ ∀ x q h T : ℝ,
      2 ≤ x → 1 ≤ q → q ≤ x → 0 < h → h ≤ x → 0 ≤ T →
      T ≤ 2*x^(3/20 : ℝ) →
      (x+2*h)^(11/12 : ℝ) *
          (8*(Real.log (32*q*(T+6))/Real.log (15/14 : ℝ))*(1+Real.log (T+3))) ≤
        CZ*x^(11/12 : ℝ)*(Real.log x)^2 ∧
      (x+2*h)^(11/12 : ℝ) *
          (8*(Real.log (64*(T+6)^2)/Real.log (15/14 : ℝ))*(1+Real.log (T+3))) ≤
        CZ*x^(11/12 : ℝ)*(Real.log x)^2 := by
  obtain ⟨C, hC, hscale⟩ := scale_log_bounds
  have hd : 0 < Real.log (15/14 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨24*C^2/Real.log (15/14 : ℝ), by positivity, ?_⟩
  intro x q h T hx hq hqx hh hhx hT hTY
  obtain ⟨hL1, hL2, hS⟩ := hscale x q hx hq hqx
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hT6 : T+6 ≤ 2*x^(3/20 : ℝ)+10 := by linarith
  have hT3 : T+3 ≤ 2*x^(3/20 : ℝ)+3 := by linarith
  have hraw1 : Real.log (32*q*(T+6)) ≤ C*Real.log x := by
    apply le_trans _ hL1
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left hT6 (by positivity)
  have hraw2 : Real.log (64*(T+6)^2) ≤ C*Real.log x := by
    apply le_trans _ hL2
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ T+6) hT6 2) (by norm_num)
  have hshort : 1+Real.log (T+3) ≤ C*Real.log x := by
    apply le_trans _ hS
    exact add_le_add (le_refl (1 : ℝ)) (Real.log_le_log (by linarith) hT3)
  have hshort0 : 0 ≤ 1+Real.log (T+3) := by
    have := Real.log_nonneg (show 1 ≤ T+3 by linarith)
    linarith
  have hpow : (x+2*h)^(11/12 : ℝ) ≤ 3*x^(11/12 : ℝ) := by
    calc
      _ ≤ (3*x)^(11/12 : ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 3^(11/12 : ℝ)*x^(11/12 : ℝ) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 3*x^(11/12 : ℝ) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num))
        (Real.rpow_nonneg hx0.le _)
  have hpow0 : 0 ≤ (x+2*h)^(11/12 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hfinal (ell : ℝ) (hell : ell ≤ C*Real.log x) :
      (x+2*h)^(11/12 : ℝ) *
          (8*(ell/Real.log (15/14 : ℝ))*(1+Real.log (T+3))) ≤
        (24*C^2/Real.log (15/14 : ℝ))*x^(11/12 : ℝ)*(Real.log x)^2 := by
    have hprod : 8*(ell/Real.log (15/14 : ℝ))*(1+Real.log (T+3)) ≤
        8*((C*Real.log x)/Real.log (15/14 : ℝ))*(C*Real.log x) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hell hd.le) (by norm_num))
        hshort hshort0 (by positivity)
    calc
      _ ≤ (x+2*h)^(11/12 : ℝ) *
          (8*((C*Real.log x)/Real.log (15/14 : ℝ))*(C*Real.log x)) :=
        mul_le_mul_of_nonneg_left hprod hpow0
      _ ≤ (3*x^(11/12 : ℝ)) *
          (8*((C*Real.log x)/Real.log (15/14 : ℝ))*(C*Real.log x)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by ring
  exact ⟨hfinal _ hraw1, hfinal _ hraw2⟩

end QRHShort.CloudBatch.PrimesAPGrowthAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology
namespace QRHShort.CloudBatch.PrimesAPExplicitAux
open PrimesAPGrowthAux PrimesAPRectAux

def primitiveZeroSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y a c T : ℝ) : ℂ :=
  if χ=1 then rectangleZeroSum (DirichletCharacter.LFunctionTrivChar₁ 1) y a c T
  else rectangleZeroSum (DirichletCharacter.LFunction χ) y a c T

theorem primitive_quadratic_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    {x a c T : ℝ} (hx : 0 < x) (ha : 0 < a) (ha1 : a < 1)
    (hc : 1 < c) (hc2 : c ≤ 2) (hT : 0 < T)
    (hb : ∀ z ∈ contourBoundary a c T, DirichletCharacter.LFunction χ z ≠ 0) :
    Integrable (fun t : ℝ => quadraticPerronIntegrand χ x ((c:ℂ)+t*I)) ∧
    RectIntegrable a c (-T) T (quadraticPerronIntegrand χ x) ∧
    PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n) x =
      (if χ=1 then (x:ℂ)^3/6 else 0) - primitiveZeroSum χ x a c T +
        contourError (quadraticPerronIntegrand χ x) a c T := by
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by
      have hh : (1 : DirichletCharacter ℂ q).conductor=q := hprim
      rw [DirichletCharacter.conductor_one] at hh
      exact hh.symm
    subst q
    have hbZ : ∀ z ∈ contourBoundary a c T, DirichletCharacter.LFunctionTrivChar₁ 1 z ≠ 0 := by
      intro z hz
      rw [DirichletCharacter.LFunctionTrivChar₁,
        Function.update_of_ne (contourBoundary_ne_one ha1 hc hT hz)]
      exact mul_ne_zero (sub_ne_zero.mpr (contourBoundary_ne_one ha1 hc hT hz)) (hb z hz)
    simpa only [primitiveZeroSum,if_pos rfl,ite_true] using principal_quadratic_explicit hx ha ha1 hc hc2 hT hbZ
  · simpa only [primitiveZeroSum,if_neg hχ,zero_sub] using
      nonprincipal_quadratic_explicit χ hχ hx ha ha1 hc hc2 hT hb

theorem primitive_zero_difference_uniform :
    ∃ CZ : ℝ, 0 ≤ CZ ∧ ∀ (hZ : QRHShort.DirichletZeroFreeStatement)
      (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (x h a c T : ℝ), 2 ≤ x → (q:ℝ) ≤ x → 0 < h → h ≤ x →
      (3:ℝ)/4 ≤ a → 0 ≤ T → T ≤ 2*x^(3/20:ℝ) →
      ‖secondQuotient (fun y => primitiveZeroSum χ y a c T) x h‖ ≤
        CZ*x^(11/12:ℝ)*(Real.log x)^2 := by
  obtain ⟨CZ,hCZ,hs⟩ := scale_zero_leading_bounds
  refine ⟨CZ,hCZ,?_⟩
  intro hZ q _ χ x h a c T hx hqx hh hhx ha hT hTY
  have hq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos q)
  have hscale := hs x (q:ℝ) h T hx hq hqx hh hhx hT hTY
  by_cases hχ : χ=1
  · have hb := regularizedZeta_rectangleZeroSum_difference_norm_le (c := c) hZ
      (by linarith : 1 ≤ x) hh ha hT
    simpa only [secondQuotient,primitiveZeroSum,if_pos hχ] using hb.trans hscale.2
  · have hb := LFunction_rectangleZeroSum_difference_norm_le (c := c) hZ χ hχ
      (by linarith : 1 ≤ x) hh ha hT
    simpa only [secondQuotient,primitiveZeroSum,if_neg hχ] using hb.trans hscale.1

theorem secondQuotient_cubic_main {x h : ℝ} (hh : 0 < h) :
    secondQuotient (fun y => (y:ℂ)^3/6) x h = ((x+h:ℝ):ℂ) := by
  have hn : (h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  dsimp only [secondQuotient]
  push_cast
  field_simp [hn]
  <;> ring

theorem secondQuotient_main {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x h : ℝ} (hh : 0 < h) :
    secondQuotient (fun y => if χ=1 then (y:ℂ)^3/6 else 0) x h =
      if χ=1 then ((x+h:ℝ):ℂ) else 0 := by
  by_cases hχ : χ=1
  · simpa only [if_pos hχ] using (secondQuotient_cubic_main (x := x) hh)
  · simp only [secondQuotient,if_neg hχ,mul_zero,sub_self,add_zero,zero_div]

theorem secondQuotient_explicit_error (P M Z E : ℝ → ℂ) (x h : ℝ)
    (h0 : P x = M x-Z x+E x)
    (h1 : P (x+h) = M (x+h)-Z (x+h)+E (x+h))
    (h2 : P (x+2*h) = M (x+2*h)-Z (x+2*h)+E (x+2*h)) :
    ‖secondQuotient P x h-secondQuotient M x h‖ ≤
      ‖secondQuotient Z x h‖+‖secondQuotient E x h‖ := by
  have he : secondQuotient P x h-secondQuotient M x h =
      -secondQuotient Z x h+secondQuotient E x h := by
    dsimp only [secondQuotient]
    rw [h0,h1,h2]
    ring
  rw [he]
  simpa only [norm_neg] using norm_add_le (-secondQuotient Z x h) (secondQuotient E x h)

end QRHShort.CloudBatch.PrimesAPExplicitAux

noncomputable section
open Classical Complex MeasureTheory Set Metric
open scoped Interval BigOperators Topology
namespace QRHShort.CloudBatch.PrimesAPExplicitAux
open PrimesAPGrowthAux PrimesAPRectAux

/-- The actual primitive family satisfies the uniform smoothed estimate.
All constants are selected before the modulus, character and real height. -/
theorem primitive_quadratic_smoothed_estimate (hZ : QRHShort.DirichletZeroFreeStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2 ≤ x → (q:ℝ) ≤ x →
      let h := x^(9/10:ℝ)
      ‖(PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n) (x+2*h) -
        2*PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n) (x+h) +
        PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n) x)/(h:ℂ)^2 -
          (if χ=1 then ((x+h:ℝ):ℂ) else 0)‖ ≤ C*x^(11/12:ℝ)*(Real.log x)^2 := by
  obtain ⟨CL,hCL,hgood⟩ := primitive_LFunction_good_contour_growth
  obtain ⟨CR,hCR,hright⟩ := primitive_LFunction_right_growth
  obtain ⟨CE,hCE,hscaleE⟩ := contour_error_scale_bound CL CR hCL hCR
  obtain ⟨CZ,hCZ,hzero⟩ := primitive_zero_difference_uniform
  refine ⟨CZ+CE,add_nonneg hCZ hCE,?_⟩
  intro q _ χ hprim x hx hqx
  let h : ℝ := x^(9/10:ℝ)
  let Y : ℝ := x^(3/20:ℝ)
  let c : ℝ := 1+1/(1+Real.log x)
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos q)
  obtain ⟨hh,hhx,hY,hYx⟩ := scale_parameter_ranges hx
  change 0 < h at hh
  change h ≤ x at hhx
  change 1 ≤ Y at hY
  change Y ≤ x at hYx
  have hcdata := scale_contour_power_bound hx
  have hc1 : 1 < c := hcdata.1
  have hc2 : c ≤ 2 := hcdata.2.1
  obtain ⟨a,ha,T,hT,hboundary,hside⟩ := hgood hZ q χ hprim Y c hY hc1 hc2
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hac : a ≤ c := ha1.le.trans hc1.le
  have hT1 : 1 ≤ T := hY.trans hT.1
  have hT0 : 0 < T := by linarith
  have hb : ∀ z ∈ contourBoundary a c T, DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hz
    exact hboundary z hz.1.1.1 hz.1.1.2 (abs_le.mpr hz.1.2) hz.2
  let P : ℝ → ℂ := PrimesAPAux.quadraticPrefix (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n)
  let M : ℝ → ℂ := fun y => if χ=1 then (y:ℂ)^3/6 else 0
  let Z : ℝ → ℂ := fun y => primitiveZeroSum χ y a c T
  let E : ℝ → ℂ := fun y => contourError (quadraticPerronIntegrand χ y) a c T
  have hform (y : ℝ) (hy : 0 < y) :
      Integrable (fun t : ℝ => quadraticPerronIntegrand χ y ((c:ℂ)+t*I)) ∧
      RectIntegrable a c (-T) T (quadraticPerronIntegrand χ y) ∧ P y=M y-Z y+E y :=
    primitive_quadratic_explicit χ hprim hy ha0 ha1 hc1 hc2 hT0 hb
  have hf0 := hform x hx0
  have hf1 := hform (x+h) (by linarith)
  have hf2 := hform (x+2*h) (by linarith)
  have hZE : ‖secondQuotient Z x h‖ ≤ CZ*x^(11/12:ℝ)*(Real.log x)^2 :=
    hzero hZ q χ x h a c T hx hqx hh hhx ha.1 hT0.le hT.2
  let D : ℂ → ℂ := fun s => -logDeriv (DirichletCharacter.LFunction χ) s
  let L : ℝ := Real.log (64*(q:ℝ)*(2*Y+10))+1
  have hML : 0 ≤ CL*Y*L^2 := by positivity
  have hleft : ∀ t ∈ Set.Icc (-T) T, ‖D ((a:ℂ)+t*I)‖ ≤ CL*Y*L^2 := by
    intro t ht
    dsimp only [D]
    rw [norm_neg]
    exact hside _ (by simp) (by simpa using hac) (by simpa using abs_le.mpr ht)
      (Or.inl (by simp))
  have hbottom : ∀ u ∈ Set.Icc a c, ‖D ((u:ℂ)+(-T)*I)‖ ≤ CL*Y*L^2 := by
    intro u hu
    dsimp only [D]
    rw [norm_neg]
    exact hside _ (by simpa using hu.1) (by simpa using hu.2)
      (by simp [abs_of_pos hT0]) (Or.inr (Or.inl (by simp)))
  have htop : ∀ u ∈ Set.Icc a c, ‖D ((u:ℂ)+T*I)‖ ≤ CL*Y*L^2 := by
    intro u hu
    dsimp only [D]
    rw [norm_neg]
    exact hside _ (by simpa using hu.1) (by simpa using hu.2)
      (by simp [abs_of_pos hT0]) (Or.inr (Or.inr (by simp)))
  have hright' : ∀ t : ℝ, T < |t| →
      ‖D ((c:ℂ)+t*I)‖ ≤ CR*(Real.log ((64*(q:ℝ))*(|t|+4))+1) := by
    intro t ht
    dsimp only [D]
    rw [norm_neg]
    simpa using hright hZ q χ hprim ((c:ℂ)+t*I)
      (by simpa using hc1.le) (by simpa using hc2) (by simpa using hT1.trans ht.le)
  have hraw := contour_difference_error_bound D (x := x) (h := h) (a := a) (c := c)
    (T := T) (Q := 64*(q:ℝ)) (M := CL*Y*L^2) (R := CR)
    hx1 hh ha0 hc1.le hac hT1 (by linarith) hML hCR hleft hbottom htop hright'
  have hscaled := hscaleE x (q:ℝ) a T hx hq hqx ha hT
  have hlin := contourError_secondQuotient (quadraticPerronIntegrand χ) x h a c T
    hf0.2.1 hf1.2.1 hf2.2.1 hf0.1 hf1.1 hf2.1
  have hpoint (s : ℂ) : secondQuotient (fun y => quadraticPerronIntegrand χ y s) x h =
      D s*kernelDifference x h s := weighted_kernel_secondQuotient D x h s
  simp_rw [hpoint] at hlin
  have hEE : ‖secondQuotient E x h‖ ≤ CE*x^(11/12:ℝ)*(Real.log x)^2 := by
    change ‖secondQuotient (fun y => contourError (quadraticPerronIntegrand χ y) a c T) x h‖ ≤ _
    rw [hlin]
    exact hraw.trans hscaled
  have hsum := secondQuotient_explicit_error P M Z E x h hf0.2.2 hf1.2.2 hf2.2.2
  have hmain : secondQuotient M x h = if χ=1 then ((x+h:ℝ):ℂ) else 0 :=
    secondQuotient_main χ hh
  rw [hmain] at hsum
  change ‖secondQuotient P x h-(if χ=1 then ((x+h:ℝ):ℂ) else 0)‖ ≤ _
  refine hsum.trans ((add_le_add hZE hEE).trans_eq ?_)
  ring

end QRHShort.CloudBatch.PrimesAPExplicitAux

namespace QRHShort.CloudBatch

theorem zero_free_twisted_step_proved : PrimeAP.ZeroFreeTwistedStep := by
  intro hZ
  exact PrimesAPAux.twistedMangoldtEstimate_of_primitive_quadratic_smoothed
    (PrimesAPExplicitAux.primitive_quadratic_smoothed_estimate hZ)

/-- The original AP endpoint, with exactly its original statement and no
additional analytic premise. -/
theorem primes_ap_step_proved : MainStatement → PrimeAPStatement :=
  primes_ap_of_zeroFreeTwisted zero_free_twisted_step_proved

end QRHShort.CloudBatch
