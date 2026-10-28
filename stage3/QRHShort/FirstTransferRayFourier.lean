import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! A finite Fourier expansion with a coefficient bound chosen before the
function being expanded.  The bound is the finite matrix norm of the Fourier
coordinate map in the delta basis; no estimate from arithmetic is assumed. -/

noncomputable section

open Classical
open scoped BigOperators

namespace QRHShort.FirstTransferRayFourier

variable (A : Type*) [AddCommGroup A] [Fintype A]

/-- Fourier coefficients in the complex character basis. -/
def coefficients (g : A → ℂ) (ψ : AddChar A ℂ) : ℂ :=
  (AddChar.complexBasis A).repr g ψ

/-- A finite bound depending only on the group and the chosen Fourier basis. -/
def coefficientBound : ℝ :=
  ∑ ψ : AddChar A ℂ, ∑ x : A, ‖coefficients A (Pi.single x 1) ψ‖

theorem coefficientBound_nonneg : 0 ≤ coefficientBound A := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem coefficients_eq_sum_delta (g : A → ℂ) (ψ : AddChar A ℂ) :
    coefficients A g ψ =
      ∑ x : A, g x * coefficients A (Pi.single x 1) ψ := by
  have hg : g = ∑ x : A, g x • Pi.single x (1 : ℂ) := by
    ext y
    simp [Pi.single_apply]
  unfold coefficients
  conv_lhs => rw [hg, map_sum]
  simp

theorem sum_norm_coefficients_le (g : A → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) :
    ∑ ψ : AddChar A ℂ, ‖coefficients A g ψ‖ ≤ coefficientBound A := by
  apply Finset.sum_le_sum
  intro ψ _
  rw [coefficients_eq_sum_delta]
  calc
    ‖∑ x : A, g x * coefficients A (Pi.single x 1) ψ‖ ≤
        ∑ x : A, ‖g x * coefficients A (Pi.single x 1) ψ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x : A, ‖coefficients A (Pi.single x 1) ψ‖ := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hg x) (norm_nonneg _)).trans_eq (one_mul _)

theorem expansion (g : A → ℂ) (x : A) :
    g x = ∑ ψ : AddChar A ℂ, coefficients A g ψ * ψ x := by
  simpa only [coefficients, AddChar.complexBasis_apply, Fintype.sum_apply,
    Pi.smul_apply, smul_eq_mul] using
    (congr_fun ((AddChar.complexBasis A).sum_repr g) x).symm

theorem expansion_sub (g : A → ℂ) (x y : A) :
    g (x - y) =
      ∑ ψ : AddChar A ℂ, coefficients A g ψ * ψ x * star (ψ y) := by
  rw [expansion A g (x - y)]
  apply Finset.sum_congr rfl
  intro ψ _
  rw [sub_eq_add_neg, ψ.map_add_eq_mul, ψ.map_neg_eq_conj]
  exact (mul_assoc _ _ _).symm

/-- The constant is selected before the bounded function, and the characters
are the complete, fixed finite character group. -/
theorem exists_uniform_expansion :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : A → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      ∃ l : AddChar A ℂ → ℂ,
        (∑ ψ : AddChar A ℂ, ‖l ψ‖) ≤ B ∧
        ∀ x y : A, g (x - y) =
          ∑ ψ : AddChar A ℂ, l ψ * ψ x * star (ψ y) := by
  refine ⟨coefficientBound A, coefficientBound_nonneg A, ?_⟩
  intro g hg
  exact ⟨coefficients A g, sum_norm_coefficients_le A g hg, expansion_sub A g⟩

end QRHShort.FirstTransferRayFourier
