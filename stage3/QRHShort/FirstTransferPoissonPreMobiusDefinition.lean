import QRHShort.FirstTransferPoissonPreMobiusRanges
import QRHShort.FirstTransferOffDiagonalReindexPointwise

/-! The literal finite off-diagonal expression before Möbius reindexing,
and the literal zero-frequency contribution from the same finite expansion. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def firstTransferPreMobiusKernelTerm (c : ArithmeticContext) (Φ : RowWeight)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) (C d f : Ideal O) (h : O)
    (p : Ideal O × Ideal O) : ℂ :=
  (mobius d : ℂ) * ((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
    firstTransferOffDiagonalLead C f *
    firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C)
      (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
      (h * primaryGenerator f ^ 2) p

def firstTransferPreMobiusBilinear (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) : ℂ :=
  ∑ C ∈ firstTransferPreMobiusOuter c I L,
    ∑ d ∈ firstTransferPoissonDivisors C,
      ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
        ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
          ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
            if IsRelPrime p.1 p.2 then firstTransferPreMobiusKernelTerm c Φ ξ W H L F C d f h p
            else 0

def firstTransferPreMobiusZeroTerm (c : ArithmeticContext) (Φ : RowWeight)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) (f : Ideal O)
    (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if ht : firstTransferGcdTripleAdmissible c t then
    (((L * F)⁻¹ : ℝ) : ℂ) * firstTransferPoissonEnergyCoefficient c ξ W L f (t.1 * t.2.1) *
      star (firstTransferPoissonEnergyCoefficient c ξ W L f (t.1 * t.2.2)) *
      poissonZeroTerm (firstTransferPrimitivePairedCharacter c ht.2.1 ht.2.2.1 ht.2.2.2.2.2)
        t.1 (fun x => (Φ.value x : ℂ)) H
  else 0

def firstTransferPreMobiusZero (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) : ℂ :=
  ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
    ∑ C ∈ firstTransferPreMobiusOuter c I L,
      ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
        firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2)

/-- No original C-column restrictions remain: they already hold whenever
the literal coefficient product is nonzero. -/
theorem first_transfer_preMobius_kernelTerm_admissible (c : ArithmeticContext)
    (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) {C : Ideal O}
    (hC : SquarefreeOutside c.S C) (d f : Ideal O) (h : O) (p : Ideal O × Ideal O) :
    (if firstTransferGcdTripleAdmissible c (C, p.1, p.2) then
      firstTransferPreMobiusKernelTerm c Φ ξ W H L F C d f h p else 0) =
      if IsRelPrime p.1 p.2 then firstTransferPreMobiusKernelTerm c Φ ξ W H L F C d f h p
      else 0 := by
  by_cases hpair : IsRelPrime p.1 p.2
  · rw [ite_eq_left hpair]
    by_cases hadm : firstTransferGcdTripleAdmissible c (C, p.1, p.2)
    · exact ite_eq_left hadm
    · rw [ite_eq_right hadm]
      symm
      by_contra hterm
      have hk : firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C)
          (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
          (h * primaryGenerator f ^ 2) p ≠ 0 := by
        intro hk
        exact hterm (by simp only [firstTransferPreMobiusKernelTerm, hk, mul_zero])
      have hcols := first_transfer_offDiagonal_pairKernel_columns_of_ne_zero c ξ C d 1 Φ W
        (L / normIdeal C) _ (h * primaryGenerator f ^ 2) hk
      have hCcols : IsRelPrime C p.1 ∧ IsRelPrime C p.2 := by
        by_contra hnot
        have hfilter := first_transfer_offDiagonal_pairKernel_coprime_C_filter c ξ hC.1 d 1
          Φ W (L / normIdeal C) (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
          (h * primaryGenerator f ^ 2) p
        rw [ite_eq_right hnot] at hfilter
        exact hk hfilter.symm
      exact hadm ⟨hC, hcols.1, hcols.2.1, hCcols.1, hCcols.2, hpair⟩
  · rw [ite_eq_right hpair]
    exact ite_eq_right (fun h => hpair h.2.2.2.2.2)

end QRHShort
