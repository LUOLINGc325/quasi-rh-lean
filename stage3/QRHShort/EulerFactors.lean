import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Finite Euler factors for actual complex powers in the open right half-plane.
The norm bounds are explicit local hypotheses; no Euler-product convergence
or arithmetic identification is asserted here.
-/

open scoped BigOperators

namespace QRHShort

/-- The term subtracted from one in a local Euler factor has norm less than one. -/
theorem norm_euler_term_lt_one {q : ℕ} {ζ s : ℂ}
    (hq : 2 ≤ q) (hζ : ‖ζ‖ ≤ 1) (hs : 0 < s.re) :
    ‖ζ * (q : ℂ) ^ (-s)‖ < 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  have hq1 : 1 < (q : ℝ) :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : 1 < 2) hq)
  rw [norm_mul]
  calc
    ‖ζ‖ * ‖(q : ℂ) ^ (-s)‖ ≤ 1 * ‖(q : ℂ) ^ (-s)‖ :=
      mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
    _ = (q : ℝ) ^ (-s.re) := by
      rw [one_mul, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (neg_lt_zero.mpr hs)

/-- Every local Euler factor is nonzero when the real part of the argument is positive. -/
theorem euler_factor_ne_zero {q : ℕ} {ζ s : ℂ}
    (hq : 2 ≤ q) (hζ : ‖ζ‖ ≤ 1) (hs : 0 < s.re) :
    1 - ζ * (q : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have heq : ζ * (q : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := norm_euler_term_lt_one hq hζ hs
  rw [heq, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

/-- A finite family of these Euler factors has nonzero product, including the empty family. -/
theorem finite_euler_product_ne_zero {ι : Type*} (S : Finset ι)
    (q : ι → ℕ) (ζ : ι → ℂ) {s : ℂ}
    (hq : ∀ i ∈ S, 2 ≤ q i) (hζ : ∀ i ∈ S, ‖ζ i‖ ≤ 1) (hs : 0 < s.re) :
    (∏ i ∈ S, (1 - ζ i * (q i : ℂ) ^ (-s))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact euler_factor_ne_zero (hq i hi) (hζ i hi) hs

/-- A nonzero finite Euler product has no zero factor. -/
theorem euler_factor_ne_zero_of_product_ne_zero {ι : Type*} (S : Finset ι)
    (q : ι → ℕ) (ζ : ι → ℂ) (s : ℂ) {i : ι} (hi : i ∈ S)
    (hprod : (∏ j ∈ S, (1 - ζ j * (q j : ℂ) ^ (-s))) ≠ 0) :
    1 - ζ i * (q i : ℂ) ^ (-s) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mp hprod i hi

/-- A local Euler factor with a positive natural base is an entire function. -/
theorem euler_factor_analyticAt {q : ℕ} (hq : 0 < q) (ζ s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => 1 - ζ * (q : ℂ) ^ (-z)) s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  simp_rw [Complex.cpow_def_of_ne_zero hq0]
  exact analyticAt_const.sub
    (analyticAt_const.mul ((analyticAt_const.mul analyticAt_id.neg).cexp'))

/-- Finite products of the actual complex-power Euler factors are entire. -/
theorem finite_euler_product_analytic {ι : Type*} (S : Finset ι)
    (q : ι → ℕ) (ζ : ι → ℂ) (hq : ∀ i ∈ S, 0 < q i) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∏ i ∈ S, (1 - ζ i * (q i : ℂ) ^ (-s)))
      Set.univ := by
  classical
  revert hq
  induction S using Finset.induction_on with
  | empty =>
      intro _ s _
      simpa only [Finset.prod_empty] using
        (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := s))
  | @insert i S hi ih =>
      intro hq s _
      simp only [Finset.prod_insert hi]
      exact (euler_factor_analyticAt (hq i (Finset.mem_insert_self i S)) (ζ i) s).mul
        (ih (fun j hj => hq j (Finset.mem_insert_of_mem hj)) s (Set.mem_univ s))

/-- The entire finite Euler product is complex differentiable everywhere. -/
theorem finite_euler_product_differentiable {ι : Type*} (S : Finset ι)
    (q : ι → ℕ) (ζ : ι → ℂ) (hq : ∀ i ∈ S, 0 < q i) :
    Differentiable ℂ (fun s : ℂ => ∏ i ∈ S, (1 - ζ i * (q i : ℂ) ^ (-s))) :=
  fun s => (finite_euler_product_analytic S q ζ hq s (Set.mem_univ s)).differentiableAt

end QRHShort
