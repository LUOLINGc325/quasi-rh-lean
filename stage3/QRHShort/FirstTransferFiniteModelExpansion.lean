import QRHShort.FirstTransferFiniteSupportBilinear

/-!
Exact flattening of the literal first-transfer bilinear expression. Every
product-series rewrite below is justified by the jointly finitely supported
series, before any finite-model or divisor estimate is used.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem firstTransferBilinear_eq_joint_tsum (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) (H F : ℝ) {L : ℝ} (hL : 0 < L) :
    firstTransferBilinear c I Φ ξ W H L F =
      ∑' p : FirstTransferRowIndex × (Ideal O × Ideal O),
        firstTransferBilinearSummand c I Φ ξ W H L F p.1 p.2 := by
  have hs := firstTransferBilinear_joint_summable c I Φ ξ hW H F hL
  rw [hs.tsum_prod, hs.prod.tsum_prod, hs.prod.prod.tsum_prod]
  unfold firstTransferBilinear
  apply tsum_congr
  intro C
  rw [(hs.prod.prod.prod_factor C).tsum_prod]
  apply tsum_congr
  intro t
  by_cases hct : SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
      normIdeal C * normIdeal t ≤ 2 * I.hi * L
  · rw [if_pos hct]
    apply tsum_congr
    intro d
    rw [(hs.prod.prod_factor (C, t, d)).tsum_prod]
    by_cases hd : d ∣ C
    · rw [if_pos hd, ← tsum_mul_left]
      apply tsum_congr
      intro f
      by_cases hf : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F ∧
          IsRelPrime f (C * t)
      · rw [if_pos hf, ← tsum_mul_left]
        apply tsum_congr
        intro h
        rw [(hs.prod_factor ((C, t, d), f, h)).tsum_prod]
        by_cases hh : h ≠ 0 ∧ IsRelPrime (principal h) t ∧
            normElement h ≤ Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal d /
              (H * normIdeal C ^ 2)
        · simp only [if_pos hh, ← tsum_mul_left]
          apply tsum_congr
          intro n₁
          apply tsum_congr
          intro n₂
          have hadm : firstTransferRowAdmissible c I Φ H L F ((C, t, d), f, h) :=
            ⟨⟨hct.1, hct.2.1, hct.2.2.1, hct.2.2.2, hd⟩, hf, hh⟩
          simp only [firstTransferBilinearSummand, if_pos hadm]
        · simp only [if_neg hh, mul_zero]
          simp only [firstTransferBilinearSummand, firstTransferRowAdmissible,
            hh, and_false, if_false, tsum_zero]
      · simp only [if_neg hf, mul_zero]
        simp only [firstTransferBilinearSummand, firstTransferRowAdmissible,
          hf, false_and, and_false, if_false, tsum_zero]
    · simp only [if_neg hd]
      have hnot : ¬ firstTransferTripleAdmissible c (2 * I.hi * L) (C, t, d) :=
        fun hp => hd hp.2.2.2.2
      simp only [firstTransferBilinearSummand, firstTransferRowAdmissible,
        hnot, false_and, if_false, tsum_zero]
  · rw [if_neg hct]
    have hnot (d : Ideal O) :
        ¬ firstTransferTripleAdmissible c (2 * I.hi * L) (C, t, d) :=
      fun hp => hct ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
    simp only [firstTransferBilinearSummand, firstTransferRowAdmissible,
      hnot, false_and, if_false, tsum_zero]

end QRHShort
