import QRHShort.SecondTransferPRMPRows
noncomputable section
open Classical
open scoped BigOperators
namespace QRHShort
theorem second_transfer_prmp_truncate_native {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]
    (c : ArithmeticContext) (I : SupportInterval) (L : ℝ)
    (f : Ideal O → Ideal O → Ideal O → α) :
    (∑' C : Ideal O, ∑' t : Ideal O,
      if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) =
      ∑ C ∈ secondTransferPRMPBox I L, ∑ t ∈ secondTransferPRMPBox I L,
        if secondTransferPRMPAdmissible c I L C t then
          ∑ d ∈ secondTransferPRMPBox I L, if d ∣ C then f C d t else 0 else 0 := by
  have hCzero (C : Ideal O) (hC : C ∉ secondTransferPRMPBox I L) :
      (∑' t : Ideal O, if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) = 0 := by
    have hz (t : Ideal O) : (if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) = 0 :=
      ite_eq_right (fun h => hC (second_transfer_prmp_admissible_mem c I h).1)
    simp only [hz, tsum_zero]
  rw [tsum_eq_sum hCzero]
  apply Finset.sum_congr rfl
  intro C hC
  have htzero (t : Ideal O) (ht : t ∉ secondTransferPRMPBox I L) :
      (if secondTransferPRMPAdmissible c I L C t then
        ∑' d : Ideal O, if d ∣ C then f C d t else 0 else 0) = 0 :=
    ite_eq_right (fun h => ht (second_transfer_prmp_admissible_mem c I h).2)
  rw [tsum_eq_sum htzero]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · apply tsum_eq_sum
    intro d hd
    exact ite_eq_right (fun hdiv => hd (second_transfer_prmp_divisor_mem I hC hdiv))
  · rfl


end QRHShort
