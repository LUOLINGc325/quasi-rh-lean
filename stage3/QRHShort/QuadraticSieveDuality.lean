import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite complex large-sieve duality, with no change in the constant.
The transpose here has no conjugation, as required by the actual symbol kernel. -/

noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace QRHShort

theorem quadratic_finite_transpose_bound {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ x : κ → ℂ,
      (∑ i ∈ s, ‖∑ j ∈ t, x j * A i j‖ ^ 2) ≤ B * ∑ j ∈ t, ‖x j‖ ^ 2)
    (y : ι → ℂ) :
    (∑ j ∈ t, ‖∑ i ∈ s, y i * A i j‖ ^ 2) ≤ B * ∑ i ∈ s, ‖y i‖ ^ 2 := by
  classical
  let v : κ → ℂ := fun j => ∑ i ∈ s, y i * A i j
  let x : κ → ℂ := fun j => conj (v j)
  let w : ι → ℂ := fun i => ∑ j ∈ t, x j * A i j
  let S : ℝ := ∑ j ∈ t, ‖v j‖ ^ 2
  let T : ℝ := ∑ i ∈ s, ‖y i‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpair : (S : ℂ) = ∑ i ∈ s, y i * w i := by
    calc
      (S : ℂ) = ∑ j ∈ t, v j * x j := by
        simp [S, x, Complex.mul_conj']
      _ = ∑ i ∈ s, y i * w i := by
        simp only [v, w, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hnorm : S ≤ ∑ i ∈ s, ‖y i‖ * ‖w i‖ := by
    calc
      S = ‖(S : ℂ)‖ := (Complex.norm_of_nonneg hS).symm
      _ = ‖∑ i ∈ s, y i * w i‖ := congrArg norm hpair
      _ ≤ ∑ i ∈ s, ‖y i * w i‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul]
  have hcs : S ^ 2 ≤ T * ∑ i ∈ s, ‖w i‖ ^ 2 := by
    have hsquare := (sq_le_sq₀ hS (Finset.sum_nonneg (fun _ _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 hnorm
    exact hsquare.trans
      (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖y i‖) (fun i => ‖w i‖))
  have hw : (∑ i ∈ s, ‖w i‖ ^ 2) ≤ B * S := by
    simpa only [w, x, S, Complex.norm_conj] using hA x
  have hsq : S ^ 2 ≤ T * (B * S) :=
    hcs.trans (mul_le_mul_of_nonneg_left hw hT)
  change S ≤ B * T
  by_cases hzero : S = 0
  · simpa only [hzero] using mul_nonneg hB hT
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    apply (mul_le_mul_iff_of_pos_right hpos).mp
    nlinarith only [hsq]

end QRHShort

#print axioms QRHShort.quadratic_finite_transpose_bound
