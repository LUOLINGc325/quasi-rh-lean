import QRHShort.FirstTransferCoefficientCancellation
import QRHShort.FirstTransferFiniteSupportBilinear
import QRHShort.FirstTransferPoissonKernelNormalizationSupport

/-!
Pointwise identities for Möbius reindexing of the actual first-transfer pair.
The coefficient retains its literal squarefree and relative-primality filters.
The kernel parameter is arbitrary, including zero and negative parameters.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferOffDiagonalLead (C f : Ideal O) : ℂ :=
  sexticSymbol C (primaryGenerator f) ^ (4 : ℕ) *
    star (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ))

def firstTransferOffDiagonalPairKernel (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) (Φ : RowWeight) (W : ℝ → ℂ) (ell β : ℝ) (z : O)
    (p : Ideal O × Ideal O) : ℂ :=
  firstTransferCoefficient c ξ C d t z p.1 *
    star (firstTransferCoefficient c ξ C d t z p.2) *
    firstTransferKernel Φ W β ![normIdeal p.1 / ell, normIdeal p.2 / ell]

theorem first_transfer_offDiagonal_lead_eq_norm_sq (C f : Ideal O) :
    firstTransferOffDiagonalLead C f =
      (‖sexticSymbol C (primaryGenerator f) ^ (4 : ℕ)‖ ^ 2 : ℝ) := by
  simpa only [firstTransferOffDiagonalLead, starRingEnd_apply, Complex.ofReal_pow] using
    Complex.mul_conj' (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ))

theorem first_transfer_offDiagonal_pairKernel_hasFiniteSupport
    (c : ArithmeticContext) (ξ : RayCharacter c) (C d t : Ideal O)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {ell : ℝ} (hell : 0 < ell) (β : ℝ) (z : O) :
    Function.HasFiniteSupport (firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z) :=
  firstTransferBilinear_columns_hasFiniteSupport c ξ C d t I Φ hW β hell z

theorem first_transfer_offDiagonal_coefficient_columns_of_ne_zero
    (c : ArithmeticContext) (ξ : RayCharacter c) (C d t : Ideal O) (z : O)
    {n : Ideal O} (hn : firstTransferCoefficient c ξ C d t z n ≠ 0) :
    SquarefreeOutside c.S n ∧ IsRelPrime n t := by
  by_contra h
  exact hn (ite_eq_right h)

theorem first_transfer_offDiagonal_pairKernel_columns_of_ne_zero
    (c : ArithmeticContext) (ξ : RayCharacter c) (C d t : Ideal O)
    (Φ : RowWeight) (W : ℝ → ℂ) (ell β : ℝ) (z : O) {p : Ideal O × Ideal O}
    (hp : firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z p ≠ 0) :
    SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧
      IsRelPrime p.1 t ∧ IsRelPrime p.2 t := by
  have hleft : firstTransferCoefficient c ξ C d t z p.1 ≠ 0 := by
    intro h
    exact hp (by simp only [firstTransferOffDiagonalPairKernel, h, zero_mul])
  have hright : firstTransferCoefficient c ξ C d t z p.2 ≠ 0 := by
    intro h
    exact hp (by simp only [firstTransferOffDiagonalPairKernel, h, star_zero, mul_zero, zero_mul])
  have hx := first_transfer_offDiagonal_coefficient_columns_of_ne_zero c ξ C d t z hleft
  have hy := first_transfer_offDiagonal_coefficient_columns_of_ne_zero c ξ C d t z hright
  exact ⟨hx.1, hy.1, hx.2, hy.2⟩

theorem first_transfer_offDiagonal_pairKernel_window_support
    (c : ArithmeticContext) (ξ : RayCharacter c) (C d t : Ideal O)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {ell : ℝ} (hell : 0 < ell) (β : ℝ) (z : O) :
    Function.support (firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z) ⊆
      (firstTransferIdealWindow I ell : Set (Ideal O)) ×ˢ
        (firstTransferIdealWindow I ell : Set (Ideal O)) := by
  intro p hp
  have hcols := first_transfer_offDiagonal_pairKernel_columns_of_ne_zero c ξ C d t Φ W
    ell β z hp
  have hk : firstTransferKernel Φ W β ![normIdeal p.1 / ell, normIdeal p.2 / ell] ≠ 0 := by
    intro hzero
    exact hp (by simp only [firstTransferOffDiagonalPairKernel, hzero, mul_zero])
  have hbox := firstTransferKernel_support I Φ W hW β hk
  exact ⟨mem_firstTransferIdealWindow.mpr
      ⟨(div_le_iff₀ hell).mp (by simpa only [Matrix.cons_val_zero] using (hbox 0).2),
        hcols.1.1.1⟩,
    mem_firstTransferIdealWindow.mpr
      ⟨(div_le_iff₀ hell).mp (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using (hbox 1).2),
        hcols.2.1.1.1⟩⟩

theorem first_transfer_offDiagonal_coprime_pair_eq_sum_window
    (c : ArithmeticContext) (ξ : RayCharacter c) (C d t : Ideal O)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {ell : ℝ} (hell : 0 < ell) (β : ℝ) (z : O) :
    (∑' p : Ideal O × Ideal O, if IsRelPrime p.1 p.2 then
      firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z p else 0) =
    ∑ p ∈ (firstTransferIdealWindow I ell).product (firstTransferIdealWindow I ell),
      if IsRelPrime p.1 p.2 then
        firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z p else 0 := by
  apply tsum_eq_sum
  intro p hp
  by_cases hrel : IsRelPrime p.1 p.2
  · rw [ite_eq_left hrel]
    by_contra hzero
    exact hp (Finset.mem_product.mpr
      (first_transfer_offDiagonal_pairKernel_window_support c ξ C d t I Φ hW hell β z hzero))
  · exact ite_eq_right hrel

/-- The fourth-power numerator already enforces the original C-column
coprimality; no explicit extra filter is needed. -/
theorem first_transfer_offDiagonal_coefficient_zero_of_not_coprime_C
    (c : ArithmeticContext) (ξ : RayCharacter c) {C : Ideal O}
    (hC : Outside c.S C) (d t : Ideal O) (z : O) (n : Ideal O)
    (hn : ¬ IsRelPrime C n) : firstTransferCoefficient c ξ C d t z n = 0 := by
  by_cases hcol : SquarefreeOutside c.S n ∧ IsRelPrime n t
  · have hsymbol : sexticSymbol n (primaryGenerator C) = 0 := by
      apply first_transfer_sexticSymbol_zero_of_not_isRelPrime c hcol.1.1
      rwa [(first_transfer_primaryGenerator_spec_and_primary_outside c hC).1]
    simp only [firstTransferCoefficient, ite_eq_left hcol, hsymbol,
      zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul]
  · exact ite_eq_right hcol

theorem first_transfer_offDiagonal_pairKernel_coprime_C_filter
    (c : ArithmeticContext) (ξ : RayCharacter c) {C : Ideal O}
    (hC : Outside c.S C) (d t : Ideal O) (Φ : RowWeight) (W : ℝ → ℂ)
    (ell β : ℝ) (z : O) (p : Ideal O × Ideal O) :
    (if IsRelPrime C p.1 ∧ IsRelPrime C p.2 then
      firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z p else 0) =
      firstTransferOffDiagonalPairKernel c ξ C d t Φ W ell β z p := by
  by_cases hx : IsRelPrime C p.1
  · by_cases hy : IsRelPrime C p.2
    · exact ite_eq_left ⟨hx, hy⟩
    · rw [ite_eq_right (fun h => hy h.2)]
      simp only [firstTransferOffDiagonalPairKernel,
        first_transfer_offDiagonal_coefficient_zero_of_not_coprime_C c ξ hC d t z p.2 hy,
        star_zero, mul_zero, zero_mul]
  · rw [ite_eq_right (fun h => hx h.1)]
    simp only [firstTransferOffDiagonalPairKernel,
      first_transfer_offDiagonal_coefficient_zero_of_not_coprime_C c ξ hC d t z p.1 hx,
      zero_mul]

theorem first_transfer_offDiagonal_kernel_sample_mul (Φ : RowWeight) (W : ℝ → ℂ)
    (C t x y : Ideal O) (L β : ℝ) :
    firstTransferKernel Φ W β
      ![normIdeal (t * x) / (L / normIdeal C), normIdeal (t * y) / (L / normIdeal C)] =
    firstTransferKernel Φ W β
      ![normIdeal x / (L / (normIdeal C * normIdeal t)),
        normIdeal y / (L / (normIdeal C * normIdeal t))] := by
  have hscale (n : Ideal O) : normIdeal (t * n) / (L / normIdeal C) =
      normIdeal n / (L / (normIdeal C * normIdeal t)) := by
    simp only [normIdeal_mul, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hscale x, hscale y]

/-- The common ideal is removed from the actual coefficient pair and from
both kernel sampling coordinates. No coprimality of x and y is assumed. -/
theorem first_transfer_offDiagonal_pairKernel_mul (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) {C d t x y f : Ideal O}
    (hC : Outside c.S C) (ht : SquarefreeOutside c.S t)
    (hx : SquarefreeOutside c.S x) (hy : SquarefreeOutside c.S y)
    (hf : Outside c.S f) (hxt : IsRelPrime x t) (hyt : IsRelPrime y t)
    (hd : d ∣ C) (L β : ℝ) (h : O) :
    firstTransferOffDiagonalLead C f *
      firstTransferOffDiagonalPairKernel c ξ C d 1 Φ W (L / normIdeal C) β
        (h * primaryGenerator f ^ 2) (t * x, t * y) =
    if IsRelPrime C t ∧ IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t then
      firstTransferOffDiagonalPairKernel c ξ C d t Φ W
        (L / (normIdeal C * normIdeal t)) β (h * primaryGenerator f ^ 2) (x, y)
    else 0 := by
  by_cases hCt : IsRelPrime C t
  · have hcoeff := first_transfer_coefficient_cancellation c ξ hC ht hx hy hf hCt hxt hyt hd h
    have hscaled := congrArg (fun v : ℂ => v * firstTransferKernel Φ W β
      ![normIdeal x / (L / (normIdeal C * normIdeal t)),
        normIdeal y / (L / (normIdeal C * normIdeal t))]) hcoeff
    by_cases hfilter : IsRelPrime f (C * t) ∧ IsRelPrime (principal h) t
    · rw [ite_eq_left hfilter] at hscaled
      rw [ite_eq_left ⟨hCt, hfilter⟩]
      simpa only [firstTransferOffDiagonalPairKernel, firstTransferOffDiagonalLead,
        first_transfer_offDiagonal_kernel_sample_mul, mul_assoc] using hscaled
    · rw [ite_eq_right hfilter, zero_mul] at hscaled
      rw [ite_eq_right (fun h => hfilter h.2)]
      simpa only [firstTransferOffDiagonalPairKernel, firstTransferOffDiagonalLead,
        first_transfer_offDiagonal_kernel_sample_mul, mul_assoc] using hscaled
  · have hzero : firstTransferCoefficient c ξ C d 1
        (h * primaryGenerator f ^ 2) (t * x) = 0 := by
      rw [first_transfer_coefficient_mul c ξ C d _ ht hx hxt,
        first_transfer_offDiagonal_coefficient_zero_of_not_coprime_C c ξ hC d 1 _ t hCt,
        zero_mul]
    rw [ite_eq_right (fun h => hCt h.1)]
    simp only [firstTransferOffDiagonalPairKernel, hzero, zero_mul, mul_zero]

theorem first_transfer_offDiagonal_pairKernel_zero_of_outer_cutoff
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {C t : Ideal O}
    (hC : C ≠ ⊥) (ht : t ≠ ⊥) (d : Ideal O) {L : ℝ} (hL : 0 < L)
    (houter : 2 * I.hi * L < normIdeal C * normIdeal t)
    (β : ℝ) (z : O) (p : Ideal O × Ideal O) :
    firstTransferOffDiagonalPairKernel c ξ C d t Φ W
      (L / (normIdeal C * normIdeal t)) β z p = 0 := by
  by_contra hp
  have hcols := first_transfer_offDiagonal_pairKernel_columns_of_ne_zero c ξ C d t Φ W
    (L / (normIdeal C * normIdeal t)) β z hp
  have hwzero := first_transfer_scaled_weight_eq_zero_of_outer_cutoff I W hW
    (normIdeal_pos hC) (normIdeal_pos ht) hL
    (first_transfer_one_le_normIdeal hcols.1.1.1) houter
  exact hp (by simp only [firstTransferOffDiagonalPairKernel, firstTransferKernel,
    Matrix.cons_val_zero, Matrix.cons_val_one, hwzero, mul_zero, zero_mul])

end QRHShort
