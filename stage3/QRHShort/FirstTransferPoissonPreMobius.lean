import QRHShort.FirstTransferPoissonPreMobiusRow
import QRHShort.FirstTransferPoissonPreMobiusReorder

/-!
Exact bounded integration of the original smoothed energy through Poisson
and the uniform finite ray expansion, before Möbius reindexing. Every
exchange after the initial genuine gcd series is between finite sums.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort
open FirstTransferRayFourier

/-- The actual original energy equals its literal zero-frequency contribution
plus a uniformly bounded finite ray combination of the pre-Möbius bilinear
expression. The ray coefficients are chosen before even the support interval,
row weight, smooth test, or scales. -/
theorem first_transfer_preMobius_energy_uniform_expansion (hp : PoissonStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : RayCharacter c,
      ∃ l : RayFourierIndex c → ℂ,
        (∑ ψ : RayFourierIndex c, ‖l ψ‖) ≤ B ∧
        ∀ (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (H L F : ℝ),
          SmoothSupported I W → 0 < H → 0 < L → 0 < F →
          (smoothedEnergy c ξ Φ.value W H L F : ℂ) =
            firstTransferPreMobiusZero c I Φ ξ W H L F +
              ∑ ψ : RayFourierIndex c, l ψ *
                firstTransferPreMobiusBilinear c I Φ (rayFourierCharacter c ψ) W H L F := by
  obtain ⟨B, hB, hexp⟩ := first_transfer_poisson_coefficient_uniform_expansion c hc
  refine ⟨B, hB, ?_⟩
  intro ξ
  obtain ⟨l, hl, hidentity⟩ := hexp ξ
  refine ⟨l, hl, ?_⟩
  intro I Φ W H L F hW hH hL hF
  have hrow (C : Ideal O) (hC : SquarefreeOutside c.S C) (f : Ideal O)
      (p : Ideal O × Ideal O) :
      (((L * F)⁻¹ : ℝ) : ℂ) * firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, p.1, p.2) =
      firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2) +
        ∑ ψ : RayFourierIndex c, l ψ *
          (∑ d ∈ firstTransferPoissonDivisors C,
            ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
              if IsRelPrime p.1 p.2 then
                firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h p
              else 0) := by
    by_cases hadm : firstTransferGcdTripleAdmissible c (C, p.1, p.2)
    · have hp := first_transfer_preMobius_poisson_row hp c I Φ ξ hW hH hL hF hC
        hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2 f l (by
          intro d h
          exact hidentity C p.1 p.2 f d h W L hC hadm.2.1 hadm.2.2.1
            hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2)
      simpa only [ite_eq_left hadm.2.2.2.2.2] using hp
    · have hzero (ψ : RayFourierIndex c) (d : Ideal O) (h : O) :
          (if IsRelPrime p.1 p.2 then
            firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h p
          else 0) = 0 := by
        rw [← first_transfer_preMobius_kernelTerm_admissible c Φ (rayFourierCharacter c ψ)
          W H L F hC d f h p, ite_eq_right hadm]
      simp only [firstTransferPoissonEnergyGcdTerm, ite_eq_right hadm,
        firstTransferPreMobiusZeroTerm, dite_eq_right hadm, hzero,
        Finset.sum_const_zero, mul_zero, zero_add]
  calc
    (smoothedEnergy c ξ Φ.value W H L F : ℂ) =
        ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
          ∑ C ∈ firstTransferPreMobiusOuter c I L,
            ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
              (((L * F)⁻¹ : ℝ) : ℂ) *
                firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, p.1, p.2) := by
      rw [first_transfer_preMobius_energy_finite c ξ Φ hW hH hL hF]
      simp only [Finset.mul_sum]
    _ = ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
          ∑ C ∈ firstTransferPreMobiusOuter c I L,
            ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
              (firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2) +
                ∑ ψ : RayFourierIndex c, l ψ *
                  (∑ d ∈ firstTransferPoissonDivisors C,
                    ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
                      if IsRelPrime p.1 p.2 then
                        firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ)
                          W H L F C d f h p else 0)) := by
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro C hC
      apply Finset.sum_congr rfl
      intro p hp
      exact hrow C (mem_firstTransferPreMobiusOuter.mp hC).1 f p
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      change firstTransferPreMobiusZero c I Φ ξ W H L F + _ = _
      rw [first_transfer_preMobius_finite_reorder]

end QRHShort
