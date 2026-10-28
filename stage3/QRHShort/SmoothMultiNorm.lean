import QRHShort.SmoothingStatements
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section
open scoped BigOperators

namespace QRHShort

theorem SmoothBox.hasCompactSupport {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) : HasCompactSupport K := by
  apply HasCompactSupport.of_support_subset_isCompact _ hK.2
  have hbox : {x : BoxSpace d | ∀ i, x i ∈ Set.Icc (I i).lo (I i).hi} =
      Set.Icc (fun i => (I i).lo) (fun i => (I i).hi) := by
    ext x
    constructor
    · intro hx
      exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
    · intro hx i
      exact ⟨hx.1 i, hx.2 i⟩
  rw [hbox]
  exact isCompact_Icc

theorem multiWeightNorm_bddAbove {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) (q : ℕ) :
    BddAbove {v : ℝ | ∃ j : ℕ, j ≤ q ∧ ∃ x, v = ‖iteratedFDeriv ℝ j K x‖} := by
  obtain ⟨C, _, hC⟩ := hK.hasCompactSupport.exists_bound_iteratedFDeriv hK.1 q
  exact ⟨C, by rintro v ⟨j, hj, x, rfl⟩; exact hC j hj x⟩

theorem multiWeightNorm_nonneg {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) (q : ℕ) :
    0 ≤ multiWeightNorm q K :=
  QRHLean3.supZero_nonneg (multiWeightNorm_bddAbove hK q)

theorem norm_iteratedFDeriv_le_multiWeightNorm {d : ℕ}
    {I : Fin d → SupportInterval} {K : BoxSpace d → ℂ}
    (hK : SmoothBox I K) {j q : ℕ} (hj : j ≤ q) (x : BoxSpace d) :
    ‖iteratedFDeriv ℝ j K x‖ ≤ multiWeightNorm q K :=
  QRHLean3.le_supZero (multiWeightNorm_bddAbove hK q) ⟨j, hj, x, rfl⟩

theorem norm_le_multiWeightNorm {d : ℕ} {I : Fin d → SupportInterval}
    {K : BoxSpace d → ℂ} (hK : SmoothBox I K) (q : ℕ) (x : BoxSpace d) :
    ‖K x‖ ≤ multiWeightNorm q K := by
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_le_multiWeightNorm hK (Nat.zero_le q) x

theorem row_multiWeightNorm_bddAbove {R d : ℕ} (q : ℕ)
    (K : Fin R → BoxSpace d → ℂ) :
    BddAbove {v : ℝ | ∃ r : Fin R, v = multiWeightNorm q (K r)} := by
  have heq : {v : ℝ | ∃ r : Fin R, v = multiWeightNorm q (K r)} =
      Set.range (fun r => multiWeightNorm q (K r)) := by
    ext v
    constructor <;> rintro ⟨r, hr⟩ <;> exact ⟨r, hr.symm⟩
  rw [heq]
  exact (Set.finite_range _).bddAbove

theorem row_multiWeightNorm_nonneg {R d : ℕ} (q : ℕ)
    (K : Fin R → BoxSpace d → ℂ) :
    0 ≤ QRHLean3.supZero {v : ℝ | ∃ r : Fin R, v = multiWeightNorm q (K r)} :=
  QRHLean3.supZero_nonneg (row_multiWeightNorm_bddAbove q K)

theorem le_row_multiWeightNorm {R d : ℕ} (q : ℕ)
    (K : Fin R → BoxSpace d → ℂ) (r : Fin R) :
    multiWeightNorm q (K r) ≤
      QRHLean3.supZero {v : ℝ | ∃ r : Fin R, v = multiWeightNorm q (K r)} :=
  QRHLean3.le_supZero (row_multiWeightNorm_bddAbove q K) ⟨r, rfl⟩

end QRHShort

#print axioms QRHShort.multiWeightNorm_bddAbove
#print axioms QRHShort.norm_iteratedFDeriv_le_multiWeightNorm
#print axioms QRHShort.le_row_multiWeightNorm
