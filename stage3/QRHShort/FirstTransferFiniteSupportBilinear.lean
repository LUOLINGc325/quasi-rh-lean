import QRHShort.FirstTransferFiniteSupportRows

/-!
Finite ranges for the literal first-transfer bilinear expression. All row
restrictions are independent of the smooth test. The ideal columns become
finite through the fixed support interval, including at zero ideals.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

abbrev FirstTransferRowIndex := (Ideal O × Ideal O × Ideal O) × Ideal O × O

def firstTransferRowAdmissible (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (H L F : ℝ) (r : FirstTransferRowIndex) : Prop :=
  firstTransferTripleAdmissible c (2 * I.hi * L) r.1 ∧
    (SquarefreeOutside c.S r.2.1 ∧ F ≤ normIdeal r.2.1 ∧
      normIdeal r.2.1 < 2 * F ∧ IsRelPrime r.2.1 (r.1.1 * r.1.2.1)) ∧
    (r.2.2 ≠ 0 ∧ IsRelPrime (principal r.2.2) r.1.2.1 ∧
      normElement r.2.2 ≤ Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal r.1.2.2 /
        (H * normIdeal r.1.1 ^ 2))

/-- The complete `(C,t,d,f,h)` row range is finite before any test is chosen. -/
theorem first_transfer_bilinear_row_ranges_finite (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (H L F : ℝ) :
    {r | firstTransferRowAdmissible c I Φ H L F r}.Finite := by
  have hfinite := (first_transfer_triple_ranges_finite c (2 * I.hi * L)).biUnion
    (fun p _ => (((finite_normIdeal_le (2 * F)).prod
      (finite_normElement_le (Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal p.2.2 /
        (H * normIdeal p.1 ^ 2)))).image (fun q => (p, q))))
  apply hfinite.subset
  rintro ⟨p, f, h⟩ hr
  exact Set.mem_iUnion₂.mpr ⟨p, hr.1,
    ⟨(f, h), ⟨hr.2.1.2.2.1.le, hr.2.2.2.2⟩, rfl⟩⟩

theorem firstTransferKernel_ideal_pair_hasFiniteSupport (I : SupportInterval)
    (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W) (a : ℝ)
    {ell : ℝ} (hell : 0 < ell) :
    Function.HasFiniteSupport (fun p : Ideal O × Ideal O =>
      firstTransferKernel Φ W a ![normIdeal p.1 / ell, normIdeal p.2 / ell]) := by
  apply ((finite_normIdeal_le (I.hi * ell)).prod
    (finite_normIdeal_le (I.hi * ell))).subset
  intro p hp
  have hbox := firstTransferKernel_support I Φ W hW a hp
  exact ⟨(div_le_iff₀ hell).mp (by simpa using (hbox 0).2),
    (div_le_iff₀ hell).mp (by simpa using (hbox 1).2)⟩

theorem firstTransferBilinear_columns_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) (C d t : Ideal O) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) (a : ℝ) {ell : ℝ}
    (hell : 0 < ell) (y : O) :
    Function.HasFiniteSupport (fun p : Ideal O × Ideal O =>
      firstTransferCoefficient c ξ C d t y p.1 *
        star (firstTransferCoefficient c ξ C d t y p.2) *
        firstTransferKernel Φ W a ![normIdeal p.1 / ell, normIdeal p.2 / ell]) :=
  Function.HasFiniteSupport.mul_right _
    (firstTransferKernel_ideal_pair_hasFiniteSupport I Φ hW a hell)

/-- The exact bilinear term with all row restrictions combined. -/
def firstTransferBilinearSummand (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ)
    (r : FirstTransferRowIndex) (p : Ideal O × Ideal O) : ℂ :=
  if firstTransferRowAdmissible c I Φ H L F r then
    (mobius r.1.2.2 : ℂ) * (mobius r.1.2.1 : ℂ) *
      (H * normIdeal r.1.1 / (normIdeal r.1.2.2 * L ^ 2 * F) : ℝ) *
      (firstTransferCoefficient c ξ r.1.1 r.1.2.2 r.1.2.1
          (r.2.2 * primaryGenerator r.2.1 ^ 2) p.1 *
        star (firstTransferCoefficient c ξ r.1.1 r.1.2.2 r.1.2.1
          (r.2.2 * primaryGenerator r.2.1 ^ 2) p.2) *
        firstTransferKernel Φ W
          (H * normElement r.2.2 * normIdeal r.1.1 ^ 2 / (L ^ 2 * normIdeal r.1.2.2))
          ![normIdeal p.1 / (L / (normIdeal r.1.1 * normIdeal r.1.2.1)),
            normIdeal p.2 / (L / (normIdeal r.1.1 * normIdeal r.1.2.1))])
  else 0

/-- Every ideal and element coordinate in the bilinear series is jointly
finitely supported. Positivity is required only for the column scale. -/
theorem firstTransferBilinear_joint_hasFiniteSupport (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) (H F : ℝ) {L : ℝ} (hL : 0 < L) :
    Function.HasFiniteSupport (fun p : FirstTransferRowIndex × (Ideal O × Ideal O) =>
      firstTransferBilinearSummand c I Φ ξ W H L F p.1 p.2) := by
  have hfinite := (first_transfer_bilinear_row_ranges_finite c I Φ H L F).biUnion
    (fun r hr => (firstTransferKernel_ideal_pair_hasFiniteSupport I Φ hW
      (H * normElement r.2.2 * normIdeal r.1.1 ^ 2 / (L ^ 2 * normIdeal r.1.2.2))
      (div_pos hL (mul_pos (normIdeal_pos hr.1.1.1.1)
        (normIdeal_pos hr.1.2.1.1.1)))).image (fun p => (r, p)))
  apply hfinite.subset
  rintro ⟨r, p⟩ hp
  have hr : firstTransferRowAdmissible c I Φ H L F r := by
    by_contra hr
    exact hp (by simp only [firstTransferBilinearSummand, if_neg hr])
  have hk : firstTransferKernel Φ W
      (H * normElement r.2.2 * normIdeal r.1.1 ^ 2 / (L ^ 2 * normIdeal r.1.2.2))
      ![normIdeal p.1 / (L / (normIdeal r.1.1 * normIdeal r.1.2.1)),
        normIdeal p.2 / (L / (normIdeal r.1.1 * normIdeal r.1.2.1))] ≠ 0 := by
    intro hk
    exact hp (by simp only [firstTransferBilinearSummand, if_pos hr, hk, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨r, hr, ⟨p, hk, rfl⟩⟩

theorem firstTransferBilinear_joint_summable (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) (H F : ℝ) {L : ℝ} (hL : 0 < L) :
    Summable (fun p : FirstTransferRowIndex × (Ideal O × Ideal O) =>
      firstTransferBilinearSummand c I Φ ξ W H L F p.1 p.2) :=
  summable_of_hasFiniteSupport (firstTransferBilinear_joint_hasFiniteSupport c I Φ ξ hW H F hL)

end QRHShort
