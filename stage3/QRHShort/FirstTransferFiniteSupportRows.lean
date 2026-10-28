import QRHShort.FirstTransferFiniteSupport

/-!
Joint summability of the actual first form. The finite ideal coordinates and
the infinite Schwartz-weighted element coordinate are treated separately, then
Tonelli's nonnegative-series criterion justifies the joint series and its
equality to the frozen nested expression.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferTripleAdmissible (c : ArithmeticContext) (B : ℝ)
    (p : Ideal O × Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2.1 ∧
    IsRelPrime p.1 p.2.1 ∧ normIdeal p.1 * normIdeal p.2.1 ≤ B ∧ p.2.2 ∣ p.1

theorem first_transfer_triple_ranges_finite (c : ArithmeticContext) (B : ℝ) :
    {p | firstTransferTripleAdmissible c B p}.Finite := by
  apply ((finite_normIdeal_le B).prod
    ((finite_normIdeal_le B).prod (finite_normIdeal_le B))).subset
  rintro ⟨C, t, d⟩ ⟨hC, ht, _, hbound, hd⟩
  have hC1 := first_transfer_one_le_normIdeal hC.1.1
  have ht1 := first_transfer_one_le_normIdeal ht.1.1
  have hCB : normIdeal C ≤ B :=
    (le_mul_of_one_le_right (zero_le_one.trans hC1) ht1).trans hbound
  exact ⟨hCB, (le_mul_of_one_le_left (zero_le_one.trans ht1) hC1).trans hbound,
    (first_transfer_normIdeal_le_of_dvd hC.1.1 hd).trans hCB⟩

/-- Finite ideal ranges and summable nonnegative rows give a jointly
summable series, with no convergence inferred from a `tsum` value. -/
theorem first_transfer_restricted_rows_summable (c : ArithmeticContext) (B : ℝ)
    (v : (Ideal O × Ideal O × Ideal O) → O → ℝ)
    (hv : ∀ p y, 0 ≤ v p y)
    (hrow : ∀ p, firstTransferTripleAdmissible c B p → Summable (v p)) :
    Summable (fun p : (Ideal O × Ideal O × Ideal O) × O =>
      if firstTransferTripleAdmissible c B p.1 then v p.1 p.2 else 0) := by
  apply (summable_prod_of_nonneg (fun p => by
    split_ifs
    · exact hv p.1 p.2
    · exact le_rfl)).mpr
  constructor
  · intro p
    by_cases hp : firstTransferTripleAdmissible c B p
    · simpa only [if_pos hp] using hrow p hp
    · simp only [if_neg hp, summable_zero]
  · apply summable_of_hasFiniteSupport
    apply (first_transfer_triple_ranges_finite c B).subset
    intro p hp
    by_contra hnot
    change ¬ firstTransferTripleAdmissible c B p at hnot
    exact hp (by simp only [if_neg hnot, tsum_zero])

/-- The literal first-form term, indexed by its three ideals and element. -/
def firstTransferFormSummand (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (U : ℝ → ℂ) (cI H L F Sigma : ℝ)
    (p : Ideal O × Ideal O × Ideal O) (y : O) : ℝ :=
  if firstTransferTripleAdmissible c (2 * I.hi * L) p then
    (H * normIdeal p.1 / (normIdeal p.2.2 * L ^ 2 * F)) *
      (Φ.value (normElement y /
        (cI * Sigma * L * F * normIdeal p.2.2 / (H * normIdeal p.1 ^ 2))) *
        ‖firstColumn c ξ p.1 p.2.2 p.2.1 U
          (L / (normIdeal p.1 * normIdeal p.2.1)) y‖ ^ 2)
  else 0

/-- Joint summability of all four coordinates of the actual first form,
for every compactly supported smooth test and positive scales. -/
theorem firstForm_joint_summable (c : ArithmeticContext) (I J : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) {U : ℝ → ℂ} (hU : SmoothSupported J U)
    {cI H L F Sigma : ℝ} (hcI : 0 < cI) (hH : 0 < H) (hL : 0 < L)
    (hF : 0 < F) (hSigma : 0 < Sigma) :
    Summable (fun p : (Ideal O × Ideal O × Ideal O) × O =>
      firstTransferFormSummand c I Φ ξ U cI H L F Sigma p.1 p.2) := by
  unfold firstTransferFormSummand
  apply first_transfer_restricted_rows_summable c (2 * I.hi * L)
    (fun p y => (H * normIdeal p.1 / (normIdeal p.2.2 * L ^ 2 * F)) *
      (Φ.value (normElement y /
        (cI * Sigma * L * F * normIdeal p.2.2 / (H * normIdeal p.1 ^ 2))) *
        ‖firstColumn c ξ p.1 p.2.2 p.2.1 U
          (L / (normIdeal p.1 * normIdeal p.2.1)) y‖ ^ 2))
  · intro p y
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hF.le)
    · apply mul_nonneg (Φ.nonnegative _ _) (sq_nonneg _)
      exact div_nonneg (Nat.cast_nonneg _) (div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcI.le hSigma.le) hL.le)
          hF.le) (Nat.cast_nonneg _))
        (mul_nonneg hH.le (sq_nonneg _)))
  · rintro ⟨C, t, d⟩ ⟨hC, ht, _, _, hd⟩
    exact (firstForm_actual_row_summable c ξ Φ C d t hU hC.1.1 ht.1.1 hd
      hcI hH hL hF hSigma).mul_left _

/-- The jointly summable series equals the actual nested first form.
All exchanges here are backed by `firstForm_joint_summable`. -/
theorem firstForm_eq_joint_tsum (c : ArithmeticContext) (I J : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) {U : ℝ → ℂ} (hU : SmoothSupported J U)
    {cI H L F Sigma : ℝ} (hcI : 0 < cI) (hH : 0 < H) (hL : 0 < L)
    (hF : 0 < F) (hSigma : 0 < Sigma) :
    firstForm c I Φ ξ U cI H L F Sigma =
      ∑' p : (Ideal O × Ideal O × Ideal O) × O,
        firstTransferFormSummand c I Φ ξ U cI H L F Sigma p.1 p.2 := by
  have hs := firstForm_joint_summable c I J Φ ξ hU hcI hH hL hF hSigma
  rw [hs.tsum_prod, hs.prod.tsum_prod]
  unfold firstForm
  apply tsum_congr
  intro C
  rw [(hs.prod.prod_factor C).tsum_prod]
  apply tsum_congr
  intro t
  by_cases h : SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧
      IsRelPrime C t ∧ normIdeal C * normIdeal t ≤ 2 * I.hi * L
  · rw [if_pos h]
    apply tsum_congr
    intro d
    by_cases hd : d ∣ C
    · simp only [firstTransferFormSummand, firstTransferTripleAdmissible,
        h.1, h.2.1, h.2.2.1, h.2.2.2, hd, and_self, if_true, tsum_mul_left]
    · have hnot : ¬ firstTransferTripleAdmissible c (2 * I.hi * L) (C, t, d) :=
        fun hp => hd hp.2.2.2.2
      simp only [if_neg hd, firstTransferFormSummand, if_neg hnot, tsum_zero]
  · have hnot (d : Ideal O) :
        ¬ firstTransferTripleAdmissible c (2 * I.hi * L) (C, t, d) :=
      fun hp => h ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
    simp only [if_neg h, firstTransferFormSummand, if_neg (hnot _), tsum_zero]

end QRHShort
