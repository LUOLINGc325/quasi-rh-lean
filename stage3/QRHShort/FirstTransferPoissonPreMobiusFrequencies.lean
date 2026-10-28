import QRHShort.FirstTransferPoissonPreMobiusDefinition

/-! Replacing each original Poisson frequency window by the single window
for its C,d row. Both differences contribute zero by the actual Fourier
support, so no infinite-series interchange is involved. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def firstTransferPreMobiusOldFrequencies (Φ : RowWeight) (H : ℝ) (d a b : Ideal O) : Finset O :=
  (finite_normElement_le (Φ.fourierCap * normIdeal d * normIdeal (a * b) / H)).toFinset.erase 0

theorem mem_firstTransferPreMobiusOldFrequencies {Φ : RowWeight} {H : ℝ}
    {d a b : Ideal O} {h : O} :
    h ∈ firstTransferPreMobiusOldFrequencies Φ H d a b ↔
      h ≠ 0 ∧ normElement h ≤ Φ.fourierCap * normIdeal d * normIdeal (a * b) / H := by
  simp only [firstTransferPreMobiusOldFrequencies, Finset.mem_erase,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem first_transfer_preMobius_kernel_old_frequency_bound (Φ : RowWeight)
    (W : ℝ → ℂ) {H L : ℝ} (hH : 0 < H) (hL : 0 < L) {C d a b : Ideal O}
    (hC : C ≠ ⊥) (hd : d ≠ ⊥) (ha : a ≠ ⊥) (hb : b ≠ ⊥) (h : O)
    (hk : firstTransferKernel Φ W
      (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
      ![normIdeal a / (L / normIdeal C), normIdeal b / (L / normIdeal C)] ≠ 0) :
    normElement h ≤ Φ.fourierCap * normIdeal d * normIdeal (a * b) / H := by
  have harg : H * normElement h / (normIdeal d * normIdeal (a * b)) =
      (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d)) /
        ((normIdeal a / (L / normIdeal C)) * (normIdeal b / (L / normIdeal C))) := by
    simpa only [one_mul, mul_one, normIdeal_mul] using
      first_transfer_poisson_kernel_argument (normIdeal_pos hC) (show (0 : ℝ) < 1 by norm_num)
        (normIdeal_pos hd) hL (normIdeal_pos ha) (normIdeal_pos hb) H (normElement h)
  have hfourier : radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal d * normIdeal (a * b))) ≠ 0 := by
    intro hz
    apply hk
    simp only [firstTransferKernel, Matrix.cons_val_zero, Matrix.cons_val_one, ← harg,
      hz, mul_zero]
  have hden : 0 < normIdeal d * normIdeal (a * b) :=
    mul_pos (normIdeal_pos hd) (normIdeal_pos (mul_ne_zero ha hb))
  have hcap := (Φ.fourier_support ⟨hfourier,
    div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _)) hden.le⟩).2
  apply (le_div_iff₀ hH).mpr
  calc
    normElement h * H = H * normElement h := mul_comm _ _
    _ ≤ Φ.fourierCap * (normIdeal d * normIdeal (a * b)) := (div_le_iff₀ hden).mp hcap
    _ = Φ.fourierCap * normIdeal d * normIdeal (a * b) := by ring

theorem first_transfer_preMobius_kernelTerm_frequency_sums (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L : ℝ} (hH : 0 < H) (hL : 0 < L)
    (F : ℝ) {C d a b : Ideal O} (hC : C ≠ ⊥) (hd : d ≠ ⊥)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (f : Ideal O) :
    (∑ h ∈ firstTransferPreMobiusOldFrequencies Φ H d a b,
      firstTransferPreMobiusKernelTerm c Φ ξ W H L F C d f h (a, b)) =
      ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
        firstTransferPreMobiusKernelTerm c Φ ξ W H L F C d f h (a, b) := by
  have hkernel (h : O) (ht : firstTransferPreMobiusKernelTerm c Φ ξ W H L F C d f h (a, b) ≠ 0) :
      firstTransferKernel Φ W (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
        ![normIdeal a / (L / normIdeal C), normIdeal b / (L / normIdeal C)] ≠ 0 := by
    intro hz
    exact ht (by simp only [firstTransferPreMobiusKernelTerm,
      firstTransferOffDiagonalPairKernel, hz, mul_zero])
  apply Finset.sum_congr_of_eq_on_inter
  · intro h hh hnot
    by_contra ht
    apply hnot
    exact mem_firstTransferPreMobiusFrequencies.mpr
      ⟨(mem_firstTransferPreMobiusOldFrequencies.mp hh).1,
        first_transfer_frequency_le_of_kernel_ne_zero I Φ W hW hH hL
          (normIdeal_pos hC) (normIdeal_pos hd) (Nat.cast_nonneg _) (hkernel h ht)⟩
  · intro h hh hnot
    by_contra ht
    apply hnot
    exact mem_firstTransferPreMobiusOldFrequencies.mpr
      ⟨(mem_firstTransferPreMobiusFrequencies.mp hh).1,
        first_transfer_preMobius_kernel_old_frequency_bound Φ W hH hL hC hd ha hb h (hkernel h ht)⟩
  · intro h _ _
    rfl

end QRHShort
