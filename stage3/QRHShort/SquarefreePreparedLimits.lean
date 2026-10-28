import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

/-! Passing from uniform finite prepared sums to absolutely convergent rows.
The finite subsets here are arbitrary, rather than an exhaustion chosen after
the coefficients. This is what makes the absolute-convergence conclusion valid.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace QRHShort.SquarefreeAssembly

private theorem sum_abs_le_of_sum_bound {ι : Type*} (f : ι → ℝ) (M : ℝ)
    (h : ∀ t : Finset ι, |∑ i ∈ t, f i| ≤ M) (s : Finset ι) :
    (∑ i ∈ s, |f i|) ≤ 2 * M := by
  classical
  have hpos := (le_abs_self _).trans (h (s.filter fun i => 0 ≤ f i))
  have hneg := (neg_le_abs _).trans (h (s.filter fun i => ¬ 0 ≤ f i))
  have heq : (∑ i ∈ s, |f i|) =
      (∑ i ∈ s.filter (fun i => 0 ≤ f i), f i) -
        ∑ i ∈ s.filter (fun i => ¬ 0 ≤ f i), f i := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ f i
    · simp [hi, abs_of_nonneg hi]
    · simp [hi, abs_of_neg (lt_of_not_ge hi)]
  rw [heq]
  linarith

/-- Bounded sums over all finite subsets of a complex family force absolute
convergence. A bound only along one sequence of partial sums would not suffice. -/
theorem summable_norm_of_finite_sum_bound {ι : Type*} (f : ι → ℂ) (M : ℝ)
    (h : ∀ t : Finset ι, ‖∑ i ∈ t, f i‖ ≤ M) :
    Summable (fun i => ‖f i‖) := by
  have hre : ∀ t : Finset ι, |∑ i ∈ t, (f i).re| ≤ M := by
    intro t
    simpa only [← Complex.re_sum] using (Complex.abs_re_le_norm _).trans (h t)
  have him : ∀ t : Finset ι, |∑ i ∈ t, (f i).im| ≤ M := by
    intro t
    simpa only [← Complex.im_sum] using (Complex.abs_im_le_norm _).trans (h t)
  apply summable_of_sum_le (c := 4 * M) (fun _ => norm_nonneg _)
  intro t
  calc
    (∑ i ∈ t, ‖f i‖) ≤ ∑ i ∈ t, (|(f i).re| + |(f i).im|) :=
      Finset.sum_le_sum fun i _ => Complex.norm_le_abs_re_add_abs_im _
    _ = (∑ i ∈ t, |(f i).re|) + ∑ i ∈ t, |(f i).im| := Finset.sum_add_distrib
    _ ≤ 4 * M := by
      linarith [sum_abs_le_of_sum_bound (fun i => (f i).re) M hre t,
        sum_abs_le_of_sum_bound (fun i => (f i).im) M him t]

/-- A finite-row mean-square bound for every finite column set proves both
absolute convergence and the same mean-square bound for the actual `tsum`. -/
theorem prepared_rows_of_finite_bounds {ι ρ : Type*} (rows : Finset ρ)
    (f : ρ → ι → ℂ) (B : ℝ)
    (h : ∀ t : Finset ι, (∑ k ∈ rows, ‖∑ i ∈ t, f k i‖ ^ 2) ≤ B) :
    (∀ k ∈ rows, Summable (fun i => ‖f k i‖)) ∧
      (∑ k ∈ rows, ‖∑' i, f k i‖ ^ 2) ≤ B := by
  classical
  have hB : 0 ≤ B := by simpa using h ∅
  have habs : ∀ k ∈ rows, Summable (fun i => ‖f k i‖) := by
    intro k hk
    apply summable_norm_of_finite_sum_bound (f k) (B + 1)
    intro t
    have hsq : ‖∑ i ∈ t, f k i‖ ^ 2 ≤ B :=
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖∑ i ∈ t, f j i‖) hk).trans (h t)
    nlinarith [sq_nonneg (‖∑ i ∈ t, f k i‖ - 1)]
  refine ⟨habs, ?_⟩
  have hlim : Tendsto (fun t : Finset ι => ∑ k ∈ rows, ‖∑ i ∈ t, f k i‖ ^ 2)
      atTop (nhds (∑ k ∈ rows, ‖∑' i, f k i‖ ^ 2)) := by
    apply tendsto_finset_sum
    intro k hk
    exact ((habs k hk).of_norm.hasSum.norm).pow 2
  exact le_of_tendsto hlim (Eventually.of_forall h)

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.summable_norm_of_finite_sum_bound
#print axioms QRHShort.SquarefreeAssembly.prepared_rows_of_finite_bounds
