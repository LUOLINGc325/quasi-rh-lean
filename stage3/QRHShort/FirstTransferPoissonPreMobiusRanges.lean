import QRHShort.FirstTransferPoissonEnergyGcd
import QRHShort.FirstTransferPoissonGcdRow
import QRHShort.FirstTransferPoissonCoefficientExpansion
import QRHShort.FirstTransferPoissonKernelNormalizationSupport
import QRHShort.FirstTransferPoissonZeroContributionPaired

/-! Fixed finite ranges for the Poisson expression before Möbius removal of
pair coprimality. Every range is independent of the smooth weight. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def firstTransferPreMobiusOuter (c : ArithmeticContext) (I : SupportInterval) (L : ℝ) :
    Finset (Ideal O) :=
  (boundedDivisibleIdeals 1 (2 * I.hi * L)).filter (SquarefreeOutside c.S)

theorem mem_firstTransferPreMobiusOuter {c : ArithmeticContext} {I : SupportInterval}
    {L : ℝ} {C : Ideal O} : C ∈ firstTransferPreMobiusOuter c I L ↔
      SquarefreeOutside c.S C ∧ normIdeal C ≤ 2 * I.hi * L := by
  constructor
  · intro h
    exact ⟨(Finset.mem_filter.mp h).2,
      (mem_boundedDivisibleIdeals.mp (Finset.mem_filter.mp h).1).1⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_boundedDivisibleIdeals.mpr
      ⟨h.2, one_dvd _, h.1.1.1⟩, h.1⟩

def firstTransferPreMobiusPairWindow (I : SupportInterval) (L : ℝ) (C : Ideal O) :
    Finset (Ideal O × Ideal O) :=
  (firstTransferIdealWindow I (L / normIdeal C)).product
    (firstTransferIdealWindow I (L / normIdeal C))

def firstTransferPreMobiusFrequencies (I : SupportInterval) (Φ : RowWeight)
    (H L : ℝ) (C d : Ideal O) : Finset O :=
  (finite_normElement_le (Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal d /
    (H * normIdeal C ^ 2))).toFinset.erase 0

theorem mem_firstTransferPreMobiusFrequencies {I : SupportInterval} {Φ : RowWeight}
    {H L : ℝ} {C d : Ideal O} {h : O} :
    h ∈ firstTransferPreMobiusFrequencies I Φ H L C d ↔
      h ≠ 0 ∧ normElement h ≤ Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal d /
        (H * normIdeal C ^ 2) := by
  simp only [firstTransferPreMobiusFrequencies, Finset.mem_erase,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem first_transfer_preMobius_weight_argument {C a : Ideal O} (hC : C ≠ ⊥)
    (L : ℝ) : normIdeal (C * a) / L = normIdeal a / (L / normIdeal C) := by
  rw [normIdeal_mul, div_div_eq_mul_div, mul_comm]

theorem first_transfer_preMobius_energy_coefficient_window (c : ArithmeticContext)
    (ξ : RayCharacter c) {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) (f : Ideal O) {C a : Ideal O} (hC : C ≠ ⊥)
    (hA : firstTransferPoissonEnergyCoefficient c ξ W L f (C * a) ≠ 0) :
    a ∈ firstTransferIdealWindow I (L / normIdeal C) := by
  have hCa := first_transfer_poisson_energy_coefficient_support c ξ hW hL f hA
  have hCa0 := (mem_firstTransferIdealWindow.mp hCa).2
  have ha0 : a ≠ ⊥ := by
    intro h
    exact hCa0 (by rw [h, Ideal.mul_bot])
  have hn := (mem_firstTransferIdealWindow.mp hCa).1
  rw [normIdeal_mul] at hn
  apply mem_firstTransferIdealWindow.mpr
  refine ⟨?_, ha0⟩
  rw [← mul_div_assoc]
  exact (le_div_iff₀ (normIdeal_pos hC)).mpr (by simpa only [mul_comm] using hn)

theorem first_transfer_preMobius_gcd_term_support (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (H : ℝ) {L : ℝ} (hL : 0 < L) (f : Ideal O)
    {C a b : Ideal O}
    (hterm : firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, a, b) ≠ 0) :
    C ∈ firstTransferPreMobiusOuter c I L ∧ (a, b) ∈ firstTransferPreMobiusPairWindow I L C := by
  have hadm : firstTransferGcdTripleAdmissible c (C, a, b) := by
    by_contra h
    exact hterm (if_neg h)
  have hA : firstTransferPoissonEnergyCoefficient c ξ W L f (C * a) ≠ 0 := by
    intro h
    exact hterm (by simp only [firstTransferPoissonEnergyGcdTerm, if_pos hadm, h, zero_mul])
  have hB : firstTransferPoissonEnergyCoefficient c ξ W L f (C * b) ≠ 0 := by
    intro h
    exact hterm (by simp only [firstTransferPoissonEnergyGcdTerm, if_pos hadm,
      h, star_zero, mul_zero, zero_mul])
  have hCa := first_transfer_poisson_energy_coefficient_support c ξ hW hL f hA
  have hNC := (first_transfer_normIdeal_le_of_dvd (mem_firstTransferIdealWindow.mp hCa).2
    (dvd_mul_right C a)).trans (mem_firstTransferIdealWindow.mp hCa).1
  have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
  refine ⟨mem_firstTransferPreMobiusOuter.mpr ⟨hadm.1, ?_⟩, ?_⟩
  · exact hNC.trans (by nlinarith [mul_pos hhi hL])
  · exact Finset.mem_product.mpr
      ⟨first_transfer_preMobius_energy_coefficient_window c ξ hW hL f hadm.1.1.1 hA,
        first_transfer_preMobius_energy_coefficient_window c ξ hW hL f hadm.1.1.1 hB⟩

theorem first_transfer_preMobius_energy_gcd_row_finite (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (H : ℝ) {L : ℝ} (hL : 0 < L) (f : Ideal O) :
    (∑' t : Ideal O × Ideal O × Ideal O,
      firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f t) =
      ∑ C ∈ firstTransferPreMobiusOuter c I L,
        ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
          firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, p.1, p.2) := by
  rw [(first_transfer_poisson_energy_gcd_row c ξ Φ hW H hL f).1.tsum_prod]
  have hzero (C : Ideal O) (hC : C ∉ firstTransferPreMobiusOuter c I L) :
      (∑' p : Ideal O × Ideal O,
        firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, p.1, p.2)) = 0 := by
    have hz (p : Ideal O × Ideal O) :
        firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, p.1, p.2) = 0 := by
      by_contra h
      exact hC (first_transfer_preMobius_gcd_term_support c ξ Φ hW H hL f h).1
    simp only [hz, tsum_zero]
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro C hC
  apply tsum_eq_sum
  intro p hp
  by_contra h
  exact hp (first_transfer_preMobius_gcd_term_support c ξ Φ hW H hL f h).2

theorem first_transfer_preMobius_energy_finite (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) :
    (smoothedEnergy c ξ Φ.value W H L F : ℂ) =
      (((L * F)⁻¹ : ℝ) : ℂ) * ∑ f ∈ firstTransferPoissonDiagonalDyadic c F,
        ∑ C ∈ firstTransferPreMobiusOuter c I L,
          ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
            firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, p.1, p.2) := by
  rw [first_transfer_poisson_energy_gcd_expansion c ξ Φ hW hH hL hF]
  congr 1
  have hzero (f : Ideal O) (hf : f ∉ firstTransferPoissonDiagonalDyadic c F) :
      (if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        ∑' t : Ideal O × Ideal O × Ideal O,
          firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f t else 0) = 0 :=
    if_neg (fun h => hf (mem_firstTransferPoissonDiagonalDyadic.mpr h))
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro f hf
  rw [if_pos (mem_firstTransferPoissonDiagonalDyadic.mp hf),
    first_transfer_preMobius_energy_gcd_row_finite c ξ Φ hW H hL f]

end QRHShort
