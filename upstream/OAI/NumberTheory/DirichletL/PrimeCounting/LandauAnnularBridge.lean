import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OAI.NumberTheory.DirichletL.Hecke.RayPrimes
import OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass

namespace OAI

open scoped Classical Topology
open Filter

namespace SevenEighths.HeckeRayPrimes

open SevenEighths.PNT.AnnularPrimeMass
open SevenEighths.PNT.IdealPrimeMass
open HeckeFamily

noncomputable section

def dyadicCutoff (y : ℝ) : ℝ := (y - (1 / 2 : ℝ)) * (1 - y)

theorem dyadicCutoff_nonneg {y : ℝ} (hy : y ∈ Set.Icc (1 / 2 : ℝ) 1) :
    0 ≤ dyadicCutoff y := by
  unfold dyadicCutoff
  exact mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)

theorem dyadicCutoff_le_one {y : ℝ} (hy : y ∈ Set.Icc (1 / 2 : ℝ) 1) :
    dyadicCutoff y ≤ 1 := by
  unfold dyadicCutoff
  nlinarith [sq_nonneg (y - (3 / 4 : ℝ))]

theorem dyadicCutoff_integral :
    (0 : ℝ) < ∫ y in (1 / 2 : ℝ)..1, dyadicCutoff y := by
  apply intervalIntegral.integral_pos (by norm_num)
  · unfold dyadicCutoff
    fun_prop
  · intro y hy
    exact dyadicCutoff_nonneg ⟨hy.1.le, hy.2⟩
  · refine ⟨3 / 4, ?_, ?_⟩ <;> norm_num [dyadicCutoff]

variable (M : Ideal O) [NeZero M]

/-- In the PID `O`, the principal ray of modulus `1 = ⊤` contains every
nonzero ideal.  This is the set-level identification needed to turn the
principal-ray prime mass into the unrestricted ideal prime mass. -/
theorem principalIdeals_one {I : Ideal O} :
    I ∈ RayOrthogonality.principalIdeals (1 : Ideal O) ↔ I ≠ ⊥ := by
  unfold RayOrthogonality.principalIdeals
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, Submodule.IsPrincipal.generator I,
      Ideal.span_singleton_generator I, ?_⟩
    unfold RayOrthogonality.principalResidue
    refine ⟨1, ?_⟩
    apply (Ideal.Quotient.eq).2
    simp

/-- The principal ray prime theorem already yields positive mass in every
smooth annulus whose cutoff has positive integral.  This is the analytic
step used by the later sharp dyadic conversion; it is stated separately so
that the conversion only has to handle finite sums and endpoint errors. -/
theorem principalRay_primeLogAnnular_eventually_pos
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hI : 0 < ∫ y in a..b, φ y) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      0 < primeLogAnnularSum (RayOrthogonality.principalIdeals M)
        φ a b x := by
  have hA : 0 < ((RayOrthogonality.rayCard M : ℝ)⁻¹) := by
    apply inv_pos.mpr
    exact_mod_cast RayOrthogonality.rayCard_pos M
  have hlim := primeLogAnnularSum_div_tendsto
    (C := RayOrthogonality.principalIdeals M)
    (hmass := classCoeff_ratio_tendsto M)
    φ hφ hφ' ha hab hφa hφb
  have htarget : 0 < ((RayOrthogonality.rayCard M : ℝ)⁻¹) *
      (∫ y in a..b, φ y) := mul_pos hA hI
  have hev : ∀ᶠ x : ℝ in atTop,
      0 < primeLogAnnularSum (RayOrthogonality.principalIdeals M)
        φ a b x / x :=
    (hlim.eventually (Ioi_mem_nhds htarget))
  obtain ⟨x₀, hx₀⟩ := (eventually_atTop.1 hev)
  refine ⟨max x₀ 1, ?_⟩
  intro x hx
  have hx1 : 0 < x := lt_of_lt_of_le zero_lt_one (le_max_right _ _ |>.trans hx)
  have hquot := hx₀ x (le_max_left _ _ |>.trans hx)
  rcases (div_pos_iff.mp hquot) with hpos | hneg
  · exact hpos.1
  · exfalso
    linarith [hneg.2, hx1]

/-! A quantitative form used by the sharp dyadic conversion. -/
theorem principalRay_primeLogAnnular_eventually_linear
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hI : 0 < ∫ y in a..b, φ y) :
    ∃ d : ℝ, 0 < d ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      d * x ≤ primeLogAnnularSum (RayOrthogonality.principalIdeals M)
        φ a b x := by
  have hA : 0 < ((RayOrthogonality.rayCard M : ℝ)⁻¹) := by
    apply inv_pos.mpr
    exact_mod_cast RayOrthogonality.rayCard_pos M
  have hlim := primeLogAnnularSum_div_tendsto
    (C := RayOrthogonality.principalIdeals M)
    (hmass := classCoeff_ratio_tendsto M)
    φ hφ hφ' ha hab hφa hφb
  let d : ℝ := (((RayOrthogonality.rayCard M : ℝ)⁻¹) *
    (∫ y in a..b, φ y)) / 2
  have hd : 0 < d := half_pos (mul_pos hA hI)
  have hev : ∀ᶠ x : ℝ in atTop,
      d < primeLogAnnularSum (RayOrthogonality.principalIdeals M)
        φ a b x / x := by
    apply hlim.eventually
    have htarget : 0 < ((RayOrthogonality.rayCard M : ℝ)⁻¹) *
        (∫ y in a..b, φ y) := mul_pos hA hI
    have : d < ((RayOrthogonality.rayCard M : ℝ)⁻¹) *
        (∫ y in a..b, φ y) := by dsimp [d]; linarith
    exact Ioi_mem_nhds this
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 hev
  refine ⟨d, hd, max x₁ 1, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one
    (le_max_right _ _ |>.trans hx)
  have hquot := hx₁ x (le_max_left _ _ |>.trans hx)
  exact (lt_div_iff₀ hxpos).mp hquot |>.le

end

end SevenEighths.HeckeRayPrimes

end OAI
