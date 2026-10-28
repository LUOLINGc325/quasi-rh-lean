import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Weighted recombination, `paper2.tex:3621–3650`, Lemma `lem:recombine`.
The integral statement is over an arbitrary measure space, hence includes Lebesgue
measure on `ℝ^d`. Its integrability assumptions express the finite nonnegative mass
and finite weighted energy in the paper. It proves actual integrability of every
coefficient-product integral with positive outer weight. A zero outer weight
contributes zero and imposes no integrability condition on the unused product.
-/

open scoped BigOperators
open MeasureTheory

namespace QRHShort

private theorem norm_mul_sq_le (b : ℝ) (z v : ℂ) (hz : ‖z‖ ≤ b) :
    ‖z * v‖ ^ 2 ≤ b * (b * ‖v‖ ^ 2) := by
  calc
    ‖z * v‖ ^ 2 = ‖z‖ ^ 2 * ‖v‖ ^ 2 := by rw [norm_mul, mul_pow]
    _ ≤ b ^ 2 * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hz 2) (sq_nonneg _)
    _ = b * (b * ‖v‖ ^ 2) := by ring

private theorem norm_sum_sq_le_of_sq_le_mul {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ i, ‖z i‖ ^ 2 ≤ a i * b i) :
    ‖∑ i, z i‖ ^ 2 ≤ (∑ i, a i) * ∑ i, b i := by
  classical
  calc
    ‖∑ i, z i‖ ^ 2 ≤ (∑ i, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (∑ i, a i) * ∑ i, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun i _ => ha i) (fun i _ => hb i) (fun i _ => hz i)

private theorem weighted_sum_swap {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (w : ρ → ℝ) (M : ℝ) (e : ι → ρ → ℝ) :
    (∑ r, w r * (M * ∑ i, e i r)) = M * ∑ i, ∑ r, w r * e i r := by
  classical
  calc
    _ = M * ∑ r, ∑ i, w r * e i r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_left_comm, Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm]

/-- An integral Cauchy--Schwarz form that retains every integrability premise. -/
private theorem integral_sq_le_mass_energy {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (t f g : α → ℝ)
    (hti : Integrable t μ) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (ht : ∀ x, t x ^ 2 ≤ f x * g x) :
    (∫ x, t x ∂μ) ^ 2 ≤ (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
  let B := ∫ x, g x ∂μ
  let T := ∫ x, t x ∂μ
  change T ^ 2 ≤ (∫ x, f x ∂μ) * B
  by_cases hB : B = 0
  · have hg0 : g =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hg hgi).mp hB
    have hT : T = 0 := by
      change (∫ x, t x ∂μ) = 0
      calc
        (∫ x, t x ∂μ) = ∫ _, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hg0] with x hx
          have hs : t x ^ 2 = 0 := le_antisymm (by simpa [hx] using ht x) (sq_nonneg _)
          exact sq_eq_zero_iff.mp hs
        _ = 0 := by simp
    simp [hT, hB]
  · have hBpos : 0 < B := lt_of_le_of_ne (integral_nonneg hg) (Ne.symm hB)
    have hp (x : α) : 2 * (t x * B * T) ≤ f x * B ^ 2 + g x * T ^ 2 := by
      apply two_mul_le_add_of_sq_le_mul
        (mul_nonneg (hf x) (sq_nonneg B)) (mul_nonneg (hg x) (sq_nonneg T))
      calc
        (t x * B * T) ^ 2 = t x ^ 2 * (B * T) ^ 2 := by ring
        _ ≤ (f x * g x) * (B * T) ^ 2 :=
          mul_le_mul_of_nonneg_right (ht x) (sq_nonneg _)
        _ = (f x * B ^ 2) * (g x * T ^ 2) := by ring
    have hi := integral_mono (((hti.mul_const B).mul_const T).const_mul 2)
      ((hfi.mul_const (B ^ 2)).add (hgi.mul_const (T ^ 2))) hp
    simp only [Pi.add_apply] at hi
    rw [integral_add (hfi.mul_const (B ^ 2)) (hgi.mul_const (T ^ 2))] at hi
    simp only [integral_const_mul, integral_mul_const] at hi
    change 2 * (T * B * T) ≤ (∫ x, f x ∂μ) * B ^ 2 + B * T ^ 2 at hi
    apply (mul_le_mul_iff_right₀ hBpos).mp
    nlinarith only [hi]

/-- The finite-sum form of weighted recombination. -/
theorem recombine_sum {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (w : ρ → ℝ) (b : ι → ℝ) (c F : ι → ρ → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hb : ∀ i, 0 ≤ b i)
    (hbound : ∀ i r, ‖c i r‖ ≤ b i) :
    (∑ r, w r * ‖∑ i, c i r * F i r‖ ^ 2) ≤
      (∑ i, b i) * ∑ i, b i * ∑ r, w r * ‖F i r‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ r, w r * ((∑ i, b i) * ∑ i, b i * ‖F i r‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_left _ (hw r)
      exact norm_sum_sq_le_of_sq_le_mul (fun i => c i r * F i r)
        b (fun i => b i * ‖F i r‖ ^ 2) hb
        (fun i => mul_nonneg (hb i) (sq_nonneg _))
        (fun i => norm_mul_sq_le (b i) (c i r) (F i r) (hbound i r))
    _ = (∑ i, b i) * ∑ i, ∑ r, w r * (b i * ‖F i r‖ ^ 2) :=
      weighted_sum_swap w _ _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- The integral form of weighted recombination. The first conclusion ensures
that no active term uses the default Bochner integral of a nonintegrable function.
Zero-weight indices may be discarded from both sides of the inequality. -/
theorem recombine_integral {ι ρ α : Type*} [Fintype ι] [Fintype ρ]
    [MeasurableSpace α] (μ : Measure α)
    (w : ρ → ℝ) (b : ι → α → ℝ) (c F : ι → ρ → α → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hb : ∀ i x, 0 ≤ b i x)
    (hc : ∀ i r, Measurable (c i r)) (hF : ∀ i r, Measurable (F i r))
    (hbound : ∀ i r x, ‖c i r x‖ ≤ b i x)
    (hmass : ∀ i, Integrable (b i) μ)
    (henergy : ∀ i, Integrable (fun x => b i x * ∑ r, w r * ‖F i r x‖ ^ 2) μ) :
    (∀ i r, 0 < w r → Integrable (fun x => c i r x * F i r x) μ) ∧
      (∑ r, w r * ‖∑ i, ∫ x, c i r x * F i r x ∂μ‖ ^ 2) ≤
        (∑ i, ∫ x, b i x ∂μ) *
          ∑ i, ∫ x, b i x * ∑ r, w r * ‖F i r x‖ ^ 2 ∂μ := by
  classical
  let E (i : ι) (r : ρ) (x : α) := b i x * ‖F i r x‖ ^ 2
  have hEnonneg (i : ι) (r : ρ) (x : α) : 0 ≤ E i r x :=
    mul_nonneg (hb i x) (sq_nonneg _)
  have hEi (i : ι) (r : ρ) (hr : 0 < w r) : Integrable (E i r) μ := by
    apply ((henergy i).div_const (w r)).mono'
      ((hmass i).aestronglyMeasurable.mul ((hF i r).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖E i r x‖ ≤ (b i x * ∑ r, w r * ‖F i r x‖ ^ 2) / w r
    rw [Real.norm_of_nonneg (hEnonneg i r x)]
    apply (le_div_iff₀ hr).mpr
    have hs := Finset.single_le_sum
      (fun s (_ : s ∈ Finset.univ) => mul_nonneg (hw s) (sq_nonneg ‖F i s x‖))
      (Finset.mem_univ r)
    have hmul := mul_le_mul_of_nonneg_left hs (hb i x)
    dsimp only [E]
    nlinarith only [hmul]
  have hprod (i : ι) (r : ρ) (hr : 0 < w r) :
      Integrable (fun x => c i r x * F i r x) μ := by
    apply (((hmass i).add (hEi i r hr)).div_const 2).mono'
      ((hc i r).mul (hF i r)).aestronglyMeasurable
    filter_upwards [] with x
    have hn : 2 * ‖F i r x‖ ≤ 1 + ‖F i r x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖F i r x‖ - 1)]
    have hn' := mul_le_mul_of_nonneg_left hn (hb i x)
    have hc' := mul_le_mul_of_nonneg_right (hbound i r x) (norm_nonneg (F i r x))
    change ‖c i r x * F i r x‖ ≤ (b i x + E i r x) / 2
    rw [norm_mul]
    dsimp only [E]
    nlinarith only [hn', hc']
  refine ⟨hprod, ?_⟩
  have hWEi (i : ι) (r : ρ) : Integrable (fun x => w r * E i r x) μ := by
    obtain hr | hr := (hw r).eq_or_lt
    · simp [← hr]
    · exact (hEi i r hr).const_mul (w r)
  have hrow (r : ρ) (hr : 0 < w r) :
      ‖∑ i, ∫ x, c i r x * F i r x ∂μ‖ ^ 2 ≤
        (∑ i, ∫ x, b i x ∂μ) * ∑ i, ∫ x, E i r x ∂μ := by
    apply norm_sum_sq_le_of_sq_le_mul
      (fun i => ∫ x, c i r x * F i r x ∂μ)
      (fun i => ∫ x, b i x ∂μ) (fun i => ∫ x, E i r x ∂μ)
      (fun i => integral_nonneg (hb i)) (fun i => integral_nonneg (hEnonneg i r))
    intro i
    calc
      ‖∫ x, c i r x * F i r x ∂μ‖ ^ 2 ≤
          (∫ x, ‖c i r x * F i r x‖ ∂μ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2
      _ ≤ (∫ x, b i x ∂μ) * ∫ x, E i r x ∂μ :=
        integral_sq_le_mass_energy _ _ _ (hprod i r hr).norm (hmass i) (hEi i r hr)
          (hb i) (hEnonneg i r)
          (fun x => norm_mul_sq_le (b i x) (c i r x) (F i r x) (hbound i r x))
  calc
    _ ≤ ∑ r, w r * ((∑ i, ∫ x, b i x ∂μ) * ∑ i, ∫ x, E i r x ∂μ) := by
      apply Finset.sum_le_sum
      intro r _
      obtain hr | hr := (hw r).eq_or_lt
      · simp [← hr]
      · exact mul_le_mul_of_nonneg_left (hrow r hr) (hw r)
    _ = (∑ i, ∫ x, b i x ∂μ) * ∑ i, ∑ r, w r * ∫ x, E i r x ∂μ :=
      weighted_sum_swap w _ _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ r, w r * ∫ x, E i r x ∂μ) = ∫ x, ∑ r, w r * E i r x ∂μ := by
          rw [integral_finsetSum Finset.univ (fun r _ => hWEi i r)]
          simp only [integral_const_mul]
        _ = ∫ x, b i x * ∑ r, w r * ‖F i r x‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          dsimp only [E]
          ring

end QRHShort
