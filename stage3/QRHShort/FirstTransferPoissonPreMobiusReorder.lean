import QRHShort.FirstTransferPoissonPreMobiusDefinition

/-! Finite commutation of the actual pre-Möbius expression and its character
expansion. No weight, scale, or convergence hypotheses are needed. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

theorem first_transfer_preMobius_finite_reorder (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (H L F : ℝ)
    {ι : Type*} [Fintype ι] (l : ι → ℂ) (η : ι → RayCharacter c) :
    (∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
      ∑ C ∈ firstTransferPreMobiusOuter c I L,
        ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
          ∑ ψ : ι, l ψ *
            (∑ d ∈ firstTransferPoissonDivisors C,
              ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
                if IsRelPrime p.1 p.2 then
                  firstTransferPreMobiusKernelTerm c Φ (η ψ) W H L F C d f h p else 0)) =
      ∑ ψ : ι, l ψ * firstTransferPreMobiusBilinear c I Φ (η ψ) W H L F := by
  let fs := firstTransferPoissonDiagonalDyadic c F
  let Cs := firstTransferPreMobiusOuter c I L
  let Ps := firstTransferPreMobiusPairWindow I L
  let Ds := firstTransferPoissonDivisors
  let Hs := firstTransferPreMobiusFrequencies I Φ H L
  let A (ψ : ι) (f C : Ideal O) (p : Ideal O × Ideal O) (d : Ideal O) (h : O) : ℂ :=
    if IsRelPrime p.1 p.2 then
      firstTransferPreMobiusKernelTerm c Φ (η ψ) W H L F C d f h p else 0
  change (∑ f ∈ fs, ∑ C ∈ Cs, ∑ p ∈ Ps C, ∑ ψ : ι,
      l ψ * (∑ d ∈ Ds C, ∑ h ∈ Hs C d, A ψ f C p d h)) =
    ∑ ψ : ι, l ψ * (∑ C ∈ Cs, ∑ d ∈ Ds C, ∑ f ∈ fs,
      ∑ h ∈ Hs C d, ∑ p ∈ Ps C, A ψ f C p d h)
  calc
    _ = ∑ f ∈ fs, ∑ ψ : ι, ∑ C ∈ Cs, ∑ p ∈ Ps C,
        l ψ * (∑ d ∈ Ds C, ∑ h ∈ Hs C d, A ψ f C p d h) := by
      apply Finset.sum_congr rfl
      intro f hf
      calc
        _ = ∑ C ∈ Cs, ∑ ψ : ι, ∑ p ∈ Ps C,
            l ψ * (∑ d ∈ Ds C, ∑ h ∈ Hs C d, A ψ f C p d h) := by
          apply Finset.sum_congr rfl
          intro C hC
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ ψ : ι, ∑ f ∈ fs, ∑ C ∈ Cs, ∑ p ∈ Ps C,
        l ψ * (∑ d ∈ Ds C, ∑ h ∈ Hs C d, A ψ f C p d h) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ψ hψ
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C hC
      calc
        _ = ∑ f ∈ fs, ∑ d ∈ Ds C, ∑ h ∈ Hs C d, ∑ p ∈ Ps C,
            l ψ * A ψ f C p d h := by
          apply Finset.sum_congr rfl
          intro f hf
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

end QRHShort

#print axioms QRHShort.first_transfer_preMobius_finite_reorder
