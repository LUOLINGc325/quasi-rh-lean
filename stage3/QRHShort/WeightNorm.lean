import QRHShort.Energy
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
The finite derivative norm for smooth weights supported in a compact interval.
The order is a natural number, so the zeroth derivative is always included.
-/

noncomputable section
open scoped BigOperators

namespace QRHShort

theorem SmoothSupported.hasCompactSupport {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) : HasCompactSupport W := by
  exact HasCompactSupport.of_support_subset_isCompact
    (show IsCompact (Set.Icc I.lo I.hi) from isCompact_Icc) hW.2

theorem SmoothSupported.const_mul {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (a : ℂ) :
    SmoothSupported I (fun x => a * W x) := by
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul] using hW.1.const_smul a
  · intro x hx
    apply hW.2
    change W x ≠ 0
    exact (mul_ne_zero_iff.mp hx).2

theorem weightNorm_bddAbove {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) :
    BddAbove (insert 0 {r : ℝ | ∃ j : ℕ, j ≤ J ∧ ∃ x : ℝ,
      r = ‖iteratedDeriv j W x‖}) := by
  classical
  have hcompact (j : ℕ) : HasCompactSupport (iteratedDeriv j W) := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using hW.hasCompactSupport
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hbound (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedDeriv j W x‖ ≤ B := by
    have hcontinuous : Continuous (iteratedDeriv j W) :=
      ContDiff.continuous_iteratedDeriv j hW.1 (by simp)
    obtain ⟨B, hB⟩ := ((hcompact j).norm.isCompact_range hcontinuous.norm).bddAbove
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro x
    exact (hB ⟨x, rfl⟩).trans (le_max_right _ _)
  let B (j : ℕ) := Classical.choose (hbound j)
  have hBnonneg (j : ℕ) : 0 ≤ B j := (Classical.choose_spec (hbound j)).1
  have hB (j : ℕ) (x : ℝ) : ‖iteratedDeriv j W x‖ ≤ B j :=
    (Classical.choose_spec (hbound j)).2 x
  refine ⟨∑ j ∈ Finset.range (J + 1), B j, ?_⟩
  intro r hr
  rcases Set.mem_insert_iff.mp hr with hr | ⟨j, hj, x, rfl⟩
  · subst r
    exact Finset.sum_nonneg (fun j _ => hBnonneg j)
  · exact (hB j x).trans (Finset.single_le_sum (fun j _ => hBnonneg j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem weightNorm_nonneg {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) : 0 ≤ weightNorm J W := by
  exact le_csSup (weightNorm_bddAbove hW J) (Set.mem_insert 0 _)

theorem norm_iteratedDeriv_le_weightNorm {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {j J : ℕ} (hj : j ≤ J) (x : ℝ) :
    ‖iteratedDeriv j W x‖ ≤ weightNorm J W := by
  exact le_csSup (weightNorm_bddAbove hW J)
    (Set.mem_insert_of_mem 0 ⟨j, hj, x, rfl⟩)

theorem weightNorm_mono {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {J K : ℕ} (hJK : J ≤ K) :
    weightNorm J W ≤ weightNorm K W := by
  apply QRHLean3.supZero_le (weightNorm_nonneg hW K)
  rintro r ⟨j, hj, x, rfl⟩
  exact norm_iteratedDeriv_le_weightNorm hW (hj.trans hJK) x

theorem weightNorm_eq_zero_iff {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) : weightNorm J W = 0 ↔ W = 0 := by
  constructor
  · intro hzero
    funext x
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [iteratedDeriv_zero, hzero] using
      norm_iteratedDeriv_le_weightNorm hW (Nat.zero_le J) x
  · intro hzero
    subst W
    apply le_antisymm _ (weightNorm_nonneg hW J)
    apply QRHLean3.supZero_le (le_refl 0)
    rintro r ⟨j, hj, x, rfl⟩
    simp

theorem weightNorm_const_mul {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) (a : ℂ) :
    weightNorm J (fun x => a * W x) = ‖a‖ * weightNorm J W := by
  apply le_antisymm
  · apply QRHLean3.supZero_le
      (mul_nonneg (norm_nonneg a) (weightNorm_nonneg hW J))
    rintro r ⟨j, hj, x, rfl⟩
    rw [iteratedDeriv_const_mul_field, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le_weightNorm hW hj x)
      (norm_nonneg a)
  · by_cases ha : a = 0
    · subst a
      simpa only [norm_zero, zero_mul] using weightNorm_nonneg (hW.const_mul 0) J
    · have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
      have hle : weightNorm J W ≤ weightNorm J (fun x => a * W x) / ‖a‖ := by
        apply QRHLean3.supZero_le
          (div_nonneg (weightNorm_nonneg (hW.const_mul a) J) (norm_nonneg a))
        rintro r ⟨j, hj, x, rfl⟩
        apply (le_div_iff₀ hapos).mpr
        calc
          ‖iteratedDeriv j W x‖ * ‖a‖ =
              ‖iteratedDeriv j (fun x => a * W x) x‖ := by
            rw [iteratedDeriv_const_mul_field, norm_mul, mul_comm]
          _ ≤ weightNorm J (fun x => a * W x) :=
            norm_iteratedDeriv_le_weightNorm (hW.const_mul a) hj x
      simpa only [mul_comm] using (le_div_iff₀ hapos).mp hle

end QRHShort
