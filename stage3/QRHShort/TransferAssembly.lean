import QRHShort.Estimates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Assembly of the first and second Poisson transfer estimates into the transfer
proposition. Both inputs concern the literal arithmetic forms in `Estimates`.
The constants are chosen before the ray character, test and all varying scales.
-/

noncomputable section

namespace QRHLean3

/-- The real supremum convention is nonnegative even for an unbounded family.
This assertion does not claim that members of an unbounded family lie below it. -/
theorem supZero_nonneg_unconditional (s : Set ℝ) : 0 ≤ supZero s := by
  by_cases hs : BddAbove (insert 0 s)
  · exact le_csSup hs (Set.mem_insert 0 s)
  · simp only [supZero, Real.sSup_of_not_bddAbove hs, le_refl]

end QRHLean3

namespace QRHShort

theorem childSup_nonneg (c : ArithmeticContext) (I : SupportInterval) (m : ℕ)
    (H L F Sigma : ℝ) : 0 ≤ childSup c I m H L F Sigma :=
  QRHLean3.supZero_nonneg_unconditional _

/-- The manuscript's transfer proposition follows from its two Poisson transfer
lemmas, taking `j = 2m+4` and allocating half the requested loss to each lemma. -/
theorem transfer_estimate_of_first_second
    (hfirst : FirstTransferEstimate) (hsecond : SecondTransferEstimate) :
    TransferEstimate := by
  intro C ε m hC hε c I Φ hrelations
  let cI : ℝ := max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ))
  have hcI : max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI := le_rfl
  have hεhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  obtain ⟨K₁, hK₁, hfirst⟩ :=
    hfirst C (ε / 2) (2 * m + 4) hC hεhalf c I Φ cI hrelations hcI
  obtain ⟨K₂, hK₂, hsecond⟩ :=
    hsecond C (ε / 2) m hC hεhalf c I Φ cI hrelations hcI
  refine ⟨K₁ * (1 + K₂), mul_nonneg hK₁ (add_nonneg zero_le_one hK₂), ?_⟩
  intro ξ W D H L F Sigma hW hD hrange
  have hD₁ : 1 ≤ D := le_trans (by norm_num) hD
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hD
  have hpow : 1 ≤ D ^ (ε / 2) := Real.one_le_rpow hD₁ hεhalf.le
  have hpow0 : 0 ≤ D ^ (ε / 2) := zero_le_one.trans hpow
  have hSigma : 1 ≤ Sigma := hrange.2.2.2.2.2.2.1
  have hSigma0 : 0 ≤ Sigma := zero_le_one.trans hSigma
  have hS : 1 ≤ 1 + childSup c I m H L F Sigma :=
    le_add_of_nonneg_right (childSup_nonneg c I m H L F Sigma)
  have hS0 : 0 ≤ 1 + childSup c I m H L F Sigma := zero_le_one.trans hS
  let M : ℝ := K₂ * D ^ (ε / 2) * Sigma * (1 + childSup c I m H L F Sigma)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (mul_nonneg hK₂ hpow0) hSigma0) hS0
  have hform (ξ₁ : RayCharacter c) (U : ℝ → ℂ)
      (hU : SmoothSupported (halfEnlarged I) U) :
      firstForm c I Φ ξ₁ U cI H L F Sigma ≤ M * weightNorm (2 * m + 4) U ^ 2 :=
    hsecond ξ₁ U D H L F Sigma hU hD hrange
  have hA := hfirst ξ W D H L F Sigma M hW hD hrange hM hform
  have horder : 2 * (2 * m + 4) + 4 = 4 * m + 12 := by ring
  rw [horder] at hA
  have hSigmabound : Sigma ≤ D ^ (ε / 2) * Sigma * (1 + childSup c I m H L F Sigma) := by
    calc
      Sigma = Sigma * 1 := by ring
      _ ≤ Sigma * (D ^ (ε / 2) * (1 + childSup c I m H L F Sigma)) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hpow hS) hSigma0
      _ = _ := by ring
  have hsum : Sigma + M ≤
      (1 + K₂) * D ^ (ε / 2) * Sigma * (1 + childSup c I m H L F Sigma) := by
    calc
      Sigma + M ≤ D ^ (ε / 2) * Sigma * (1 + childSup c I m H L F Sigma) + M :=
        add_le_add hSigmabound (le_refl M)
      _ = _ := by dsimp only [M]; ring
  have hpowadd : D ^ ε = D ^ (ε / 2) * D ^ (ε / 2) := by
    calc
      D ^ ε = D ^ (ε / 2 + ε / 2) := by congr 1; ring
      _ = _ := Real.rpow_add hDpos _ _
  calc
    smoothedEnergy c ξ Φ.value W H L F ≤
        K₁ * D ^ (ε / 2) * (Sigma + M) * weightNorm (4 * m + 12) W ^ 2 := hA
    _ ≤ K₁ * D ^ (ε / 2) *
        ((1 + K₂) * D ^ (ε / 2) * Sigma * (1 + childSup c I m H L F Sigma)) *
          weightNorm (4 * m + 12) W ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (mul_nonneg hK₁ hpow0)) (sq_nonneg _)
    _ = (K₁ * (1 + K₂)) * D ^ ε * Sigma * weightNorm (4 * m + 12) W ^ 2 *
        (1 + childSup c I m H L F Sigma) := by rw [hpowadd]; ring

end QRHShort
