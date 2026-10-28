import QRHShort.FirstTransferMultiplicityBoundsScale
import QRHShort.PrimeComparison

/-!
Quadratic domination for child M.  The finite row image keeps all three ideal
coordinates and the literal element `h * primaryGenerator f ^ 2`.  Fibers are
counted only after their finiteness has been proved, and comparison with the
infinite first form uses its established joint summability.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferRowImage (r : FirstTransferRowIndex) :
    (Ideal O × Ideal O × Ideal O) × O :=
  (r.1, r.2.2 * primaryGenerator r.2.1 ^ 2)

theorem first_transfer_admissible_majorant_argument (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) {cI H L F Sigma : ℝ}
    (hcI : max 1 (4 * Φ.fourierCap * I.hi ^ 2) ≤ cI)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (hLF : L * F ≤ Sigma) (r : FirstTransferRowIndex)
    (hr : firstTransferRowAdmissible c I Φ H L F r) :
    normElement (r.2.2 * primaryGenerator r.2.1 ^ 2) /
      (cI * Sigma * L * F * normIdeal r.1.2.2 / (H * normIdeal r.1.1 ^ 2)) ∈
        Set.Icc (0 : ℝ) 1 := by
  have hcIpos : 0 < cI := zero_lt_one.trans_le ((le_max_left _ _).trans hcI)
  have hCpos := normIdeal_pos hr.1.1.1.1
  have hdpos := normIdeal_pos (ne_zero_of_dvd_ne_zero hr.1.1.1.1 hr.1.2.2.2.2)
  have hden : 0 < H * normIdeal r.1.1 ^ 2 := mul_pos hH (pow_pos hCpos 2)
  have hT : 0 < cI * Sigma * L * F * normIdeal r.1.2.2 /
      (H * normIdeal r.1.1 ^ 2) := by positivity
  refine ⟨div_nonneg (Nat.cast_nonneg _) hT.le, (div_le_one hT).mpr ?_⟩
  rw [first_transfer_fiber_image_norm c hr.2.1.1.1]
  let A : ℝ := Φ.fourierCap * I.hi ^ 2 * normIdeal r.1.2.2 /
    (H * normIdeal r.1.1 ^ 2)
  have hA : 0 ≤ A :=
    div_nonneg (mul_nonneg (mul_nonneg Φ.cap_pos.le (sq_nonneg _)) (Nat.cast_nonneg _))
      hden.le
  have hfreq : normElement r.2.2 ≤ A * L ^ 2 := by
    convert hr.2.2.2.2 using 1 <;> dsimp [A] <;> ring
  have himage := first_transfer_frequency_image_le hA hL.le hF.le
    (show 0 ≤ normElement r.2.2 from Nat.cast_nonneg _)
    (show 0 ≤ normIdeal r.2.1 from Nat.cast_nonneg _)
    hfreq hr.2.1.2.2.1.le hLF
  apply himage.trans
  calc
    4 * A * Sigma * L * F =
        (4 * Φ.fourierCap * I.hi ^ 2) *
          (Sigma * L * F * normIdeal r.1.2.2 / (H * normIdeal r.1.1 ^ 2)) := by
      dsimp [A]
      ring
    _ ≤ cI * (Sigma * L * F * normIdeal r.1.2.2 / (H * normIdeal r.1.1 ^ 2)) :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hcI) (by positivity)
    _ = _ := by ring

theorem first_transfer_formSummand_nonneg (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (U : ℝ → ℂ) {cI H L F Sigma : ℝ}
    (hcI : 0 ≤ cI) (hH : 0 ≤ H) (hL : 0 ≤ L) (hF : 0 ≤ F) (hSigma : 0 ≤ Sigma)
    (p : Ideal O × Ideal O × Ideal O) (y : O) :
    0 ≤ firstTransferFormSummand c I Φ ξ U cI H L F Sigma p y := by
  unfold firstTransferFormSummand
  split_ifs
  · apply mul_nonneg
    · exact div_nonneg (mul_nonneg hH (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hF)
    · apply mul_nonneg (Φ.nonnegative _ _) (sq_nonneg _)
      exact div_nonneg (Nat.cast_nonneg _) (div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcI hSigma) hL) hF)
          (Nat.cast_nonneg _)) (mul_nonneg hH (sq_nonneg _)))
  · exact le_rfl

/-- The two Möbius factors can only decrease the positive first-form coefficient. -/
theorem first_transfer_quadratic_row_le_formSummand (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) (U : ℝ → ℂ)
    {cI H L F Sigma : ℝ} (hcI : max 1 (4 * Φ.fourierCap * I.hi ^ 2) ≤ cI)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (hLF : L * F ≤ Sigma) (r : FirstTransferRowIndex)
    (hr : firstTransferRowAdmissible c I Φ H L F r) :
    ‖(mobius r.1.2.2 : ℂ) * (mobius r.1.2.1 : ℂ) *
      (H * normIdeal r.1.1 / (normIdeal r.1.2.2 * L ^ 2 * F) : ℝ)‖ *
        ‖firstColumn c ξ r.1.1 r.1.2.2 r.1.2.1 U
          (L / (normIdeal r.1.1 * normIdeal r.1.2.1))
          (r.2.2 * primaryGenerator r.2.1 ^ 2)‖ ^ 2 ≤
    firstTransferFormSummand c I Φ ξ U cI H L F Sigma
      (firstTransferRowImage r).1 (firstTransferRowImage r).2 := by
  have hpref : 0 ≤ H * normIdeal r.1.1 / (normIdeal r.1.2.2 * L ^ 2 * F) :=
    div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hF.le)
  have hmob : ‖(mobius r.1.2.2 : ℂ) * (mobius r.1.2.1 : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_mobius_le_one _) (norm_mobius_le_one _)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hcoeff : ‖(mobius r.1.2.2 : ℂ) * (mobius r.1.2.1 : ℂ) *
      (H * normIdeal r.1.1 / (normIdeal r.1.2.2 * L ^ 2 * F) : ℝ)‖ ≤
      H * normIdeal r.1.1 / (normIdeal r.1.2.2 * L ^ 2 * F) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpref]
    exact mul_le_of_le_one_left hpref hmob
  have hmajor := Φ.majorant _
    (first_transfer_admissible_majorant_argument c I Φ hcI hH hL hF hSigma hLF r hr)
  change _ ≤ firstTransferFormSummand c I Φ ξ U cI H L F Sigma r.1
    (r.2.2 * primaryGenerator r.2.1 ^ 2)
  rw [firstTransferFormSummand, if_pos hr.1]
  calc
    _ ≤ (H * normIdeal r.1.1 / (normIdeal r.1.2.2 * L ^ 2 * F)) *
        ‖firstColumn c ξ r.1.1 r.1.2.2 r.1.2.1 U
          (L / (normIdeal r.1.1 * normIdeal r.1.2.1))
          (r.2.2 * primaryGenerator r.2.1 ^ 2)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (sq_nonneg _) hmajor) hpref

/-- A finite row fiber injects into the already-proved finite `(f,h)` fiber. -/
theorem first_transfer_row_fiber_card_le (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (H L F : ℝ) (s : Finset FirstTransferRowIndex)
    (hs : ∀ r ∈ s, firstTransferRowAdmissible c I Φ H L F r)
    (r₀ : FirstTransferRowIndex) (hr₀ : r₀ ∈ s) :
    (s.filter (fun r => firstTransferRowImage r = firstTransferRowImage r₀)).card ≤
      Nat.card (firstTransferFiber c (firstTransferRowImage r₀).2) := by
  let R := s.filter (fun r => firstTransferRowImage r = firstTransferRowImage r₀)
  have hy : (firstTransferRowImage r₀).2 ≠ 0 :=
    first_transfer_admissible_image_ne_zero c I Φ H L F r₀ (hs r₀ hr₀)
  let ι : R → firstTransferFiber c (firstTransferRowImage r₀).2 := fun r =>
    ⟨r.1.2, (hs r.1 (Finset.mem_filter.mp r.2).1).2.1.1,
      congrArg Prod.snd (Finset.mem_filter.mp r.2).2⟩
  have hι : Function.Injective ι := by
    intro r t hrt
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Prod.fst (Finset.mem_filter.mp r.2).2).trans
        (congrArg Prod.fst (Finset.mem_filter.mp t.2).2).symm
    · exact congrArg Subtype.val hrt
  letI := (first_transfer_fiber_finite c hy).fintype
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_le_card_of_injective ι hι

/-- Regrouping a genuinely finite sum, followed by comparison with a genuinely
summable nonnegative series. This lemma does not totalize an infinite fiber. -/
theorem first_transfer_finset_image_sum_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (v : β → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ b, 0 ≤ v b) (hsum : Summable v)
    (hcard : ∀ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) ≤ K) :
    ∑ a ∈ s, v (f a) ≤ K * ∑' b, v b := by
  rw [← Finset.sum_fiberwise_of_maps_to' (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) v]
  calc
    _ = ∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) * v b := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ s.image f, K * v b :=
      Finset.sum_le_sum (fun b hb => mul_le_mul_of_nonneg_right (hcard b hb) (hv b))
    _ = K * ∑ b ∈ s.image f, v b := (Finset.mul_sum _ _ _).symm
    _ ≤ K * ∑' b, v b := mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum _ (fun b _ => hv b)) hK

end QRHShort
