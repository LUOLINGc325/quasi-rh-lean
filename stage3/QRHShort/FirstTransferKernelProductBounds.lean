import QRHShort.FirstTransferKernelZeroOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-! Product estimates for child K. The amplitude bounds are required only on
the fixed support box. The conclusion keeps the same derivative order on W. -/

noncomputable section
open scoped BigOperators

namespace QRHShort

theorem first_transfer_coord_derivative_le (I : SupportInterval) (W : ℝ → ℂ)
    (hW : SmoothSupported I W) (q j : ℕ) (hj : j ≤ q) (i : Fin 2) (z : BoxSpace 2) :
    ‖iteratedFDeriv ℝ j (fun y : BoxSpace 2 => W (y i)) z‖ ≤ weightNorm q W := by
  let p : BoxSpace 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hp : ‖p‖ ≤ 1 := by
    apply p.opNorm_le_bound (by norm_num)
    intro y
    change ‖y i‖ ≤ 1 * ‖y‖
    simpa only [one_mul] using norm_le_pi_norm y i
  change ‖iteratedFDeriv ℝ j (W ∘ p) z‖ ≤ _
  rw [p.iteratedFDeriv_comp_right hW.1 z (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j W (p z)‖ * ∏ _ : Fin j, ‖p‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j W (p z)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg p) (fun _ _ => hp)).trans_eq
        (by simp)
    _ = ‖iteratedDeriv j W (p z)‖ := by
      rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ weightNorm q W := norm_iteratedDeriv_le_weightNorm hW hj _

theorem first_transfer_conj_coord_derivative_le (I : SupportInterval) (W : ℝ → ℂ)
    (hW : SmoothSupported I W) (q j : ℕ) (hj : j ≤ q) (i : Fin 2) (z : BoxSpace 2) :
    ‖iteratedFDeriv ℝ j (fun y : BoxSpace 2 => star (W (y i))) z‖ ≤ weightNorm q W := by
  have heq := Complex.conjLIE.norm_iteratedFDeriv_comp_left
    (fun y : BoxSpace 2 => W (y i)) z j
  exact heq.trans_le (first_transfer_coord_derivative_le I W hW q j hj i z)

/-- A pointwise Leibniz bound using derivatives through q, with no loss of order. -/
theorem first_transfer_mul_derivative_le (f g : BoxSpace 2 → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (q j : ℕ) (hj : j ≤ q) (z : BoxSpace 2) (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfB : ∀ k ≤ q, ‖iteratedFDeriv ℝ k f z‖ ≤ B)
    (hgC : ∀ k ≤ q, ‖iteratedFDeriv ℝ k g z‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun y => f y * g y) z‖ ≤ (2 : ℝ) ^ q * B * C := by
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (j - i) g z‖ :=
      norm_iteratedFDeriv_mul_le hf hg z (by simp)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfB i hiq) (Nat.cast_nonneg _))
        (hgC (j - i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hB)
    _ = (2 : ℝ) ^ j * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2 : ℝ) ^ q * B * C :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB) hC

/-- The multiplier need only be bounded on the fixed support box; derivatives
of the product vanish off that box. The constant precedes W in applications. -/
theorem first_transfer_kernel_multiplier_bound (I : SupportInterval) (q : ℕ)
    (A : BoxSpace 2 → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAbound : ∀ j ≤ q, ∀ z ∈ Set.Icc (fun _ : Fin 2 => I.lo) (fun _ => I.hi),
      ‖iteratedFDeriv ℝ j A z‖ ≤ B)
    (W : ℝ → ℂ) (hW : SmoothSupported I W) :
    multiWeightNorm q (fun z : BoxSpace 2 => A z * W (z 0) * star (W (z 1))) ≤
      ((2 : ℝ) ^ q) ^ 2 * B * weightNorm q W ^ 2 := by
  let f : BoxSpace 2 → ℂ := fun z => A z * W (z 0) * star (W (z 1))
  have hsupp : Function.support f ⊆
      Set.Icc (fun _ : Fin 2 => I.lo) (fun _ => I.hi) := by
    intro z hz
    have hz0 : W (z 0) ≠ 0 := by
      intro h
      exact hz (by simp [f, h])
    have hz1 : W (z 1) ≠ 0 := by
      intro h
      exact hz (by simp [f, h])
    have hbox : ∀ i : Fin 2, z i ∈ Set.Icc I.lo I.hi := by
      intro i
      refine Fin.cases (hW.2 hz0) (fun k => ?_) i
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      exact hW.2 hz1
    exact ⟨fun i => (hbox i).1, fun i => (hbox i).2⟩
  have htsupp : tsupport f ⊆
      Set.Icc (fun _ : Fin 2 => I.lo) (fun _ => I.hi) :=
    closure_minimal hsupp isClosed_Icc
  have hN := weightNorm_nonneg hW q
  have htwo : 0 ≤ (2 : ℝ) ^ q := by positivity
  have hW0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : BoxSpace 2 => W (y 0)) := hW.1.comp (contDiff_apply ℝ ℝ 0)
  have hW1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : BoxSpace 2 => star (W (y 1))) :=
    Complex.conjCLE.contDiff.comp (hW.1.comp (contDiff_apply ℝ ℝ (1 : Fin 2)))
  apply QRHLean3.supZero_le (mul_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _))
  rintro r ⟨j, hj, z, rfl⟩
  change ‖iteratedFDeriv ℝ j f z‖ ≤ _
  by_cases hd : iteratedFDeriv ℝ j f z = 0
  · rw [hd, norm_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hz := htsupp (support_iteratedFDeriv_subset j hd)
  have hAW : ∀ k ≤ q, ‖iteratedFDeriv ℝ k (fun y : BoxSpace 2 => A y * W (y 0)) z‖ ≤
      (2 : ℝ) ^ q * B * weightNorm q W := by
    intro k hk
    exact first_transfer_mul_derivative_le A (fun y => W (y 0)) hA hW0 q k hk z B
      (weightNorm q W) hB hN (fun m hm => hAbound m hm z hz)
      (fun m hm => first_transfer_coord_derivative_le I W hW q m hm 0 z)
  have hbound := first_transfer_mul_derivative_le
    (fun y : BoxSpace 2 => A y * W (y 0)) (fun y => star (W (y 1)))
    (hA.mul hW0) hW1 q j hj z ((2 : ℝ) ^ q * B * weightNorm q W)
    (weightNorm q W) (mul_nonneg (mul_nonneg htwo hB) hN) hN hAW
    (fun m hm => first_transfer_conj_coord_derivative_le I W hW q m hm 1 z)
  convert hbound using 1 <;> ring

end QRHShort
