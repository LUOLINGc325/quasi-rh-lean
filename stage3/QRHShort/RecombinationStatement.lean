import QRHShort.Recombination

/-! The two forms of `lem:recombine`, paper2.tex:3621–3650.
The integral formulation includes its necessary measurability and integrability
conditions explicitly. Both components are proved in `Recombination.lean`. -/

open scoped BigOperators
open MeasureTheory

namespace QRHShort

def RecombinationStatement : Prop :=
  (∀ (ι ρ : Type) [Fintype ι] [Fintype ρ]
    (w : ρ → ℝ) (b : ι → ℝ) (c F : ι → ρ → ℂ),
    (∀ r, 0 ≤ w r) → (∀ i, 0 ≤ b i) → (∀ i r, ‖c i r‖ ≤ b i) →
    (∑ r, w r * ‖∑ i, c i r * F i r‖ ^ 2) ≤
      (∑ i, b i) * ∑ i, b i * ∑ r, w r * ‖F i r‖ ^ 2) ∧
  (∀ (ι ρ α : Type) [Fintype ι] [Fintype ρ] [MeasurableSpace α]
    (μ : Measure α) (w : ρ → ℝ) (b : ι → α → ℝ) (c F : ι → ρ → α → ℂ),
    (∀ r, 0 ≤ w r) → (∀ i x, 0 ≤ b i x) →
    (∀ i r, Measurable (c i r)) → (∀ i r, Measurable (F i r)) →
    (∀ i r x, ‖c i r x‖ ≤ b i x) →
    (∀ i, Integrable (b i) μ) →
    (∀ i, Integrable (fun x => b i x * ∑ r, w r * ‖F i r x‖ ^ 2) μ) →
    (∀ i r, 0 < w r → Integrable (fun x => c i r x * F i r x) μ) ∧
      (∑ r, w r * ‖∑ i, ∫ x, c i r x * F i r x ∂μ‖ ^ 2) ≤
        (∑ i, ∫ x, b i x ∂μ) *
          ∑ i, ∫ x, b i x * ∑ r, w r * ‖F i r x‖ ^ 2 ∂μ)

theorem recombination_statement : RecombinationStatement := by
  constructor
  · intro ι ρ _ _
    exact recombine_sum
  · intro ι ρ α _ _ _
    exact recombine_integral

end QRHShort
