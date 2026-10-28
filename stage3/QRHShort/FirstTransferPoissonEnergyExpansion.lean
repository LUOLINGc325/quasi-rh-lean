import QRHShort.FirstTransferFiniteSupport
import QRHShort.FirstTransferPoissonDiagonal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
The exact square expansion of the original smoothed energy. Ideal columns and
the dyadic ideal rows have finite support; the element rows are genuinely
summable by Schwartz decay. No Poisson or reciprocity identity is used here.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferPoissonEnergyCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (L : ℝ) (f n : Ideal O) : ℂ :=
  if SquarefreeOutside c.S n then
    coefficient ξ.val n * sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) *
      W (normIdeal n / L)
  else 0

def firstTransferPoissonEnergyPair (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (L : ℝ) (f : Ideal O) (p : Ideal O × Ideal O) (k : O) : ℂ :=
  firstTransferPoissonEnergyCoefficient c ξ W L f p.1 *
    star (firstTransferPoissonEnergyCoefficient c ξ W L f p.2) *
      sexticSymbol p.1 k * star (sexticSymbol p.2 k)

def firstTransferPoissonEnergyCharacterRow (Φ : RowWeight) (H : ℝ)
    (n₁ n₂ : Ideal O) (k : O) : ℂ :=
  (Φ.value (normElement k / H) : ℂ) * sexticSymbol n₁ k * star (sexticSymbol n₂ k)

def firstTransferPoissonEnergyTerm (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (H L : ℝ) (f : Ideal O)
    (p : Ideal O × Ideal O) (k : O) : ℂ :=
  (Φ.value (normElement k / H) : ℂ) * firstTransferPoissonEnergyPair c ξ W L f p k

theorem first_transfer_poisson_energy_coefficient_support (c : ArithmeticContext)
    (ξ : RayCharacter c) {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) (f : Ideal O) :
    Function.support (firstTransferPoissonEnergyCoefficient c ξ W L f) ⊆
      (firstTransferIdealWindow I L : Set (Ideal O)) := by
  intro n hn
  by_cases hs : SquarefreeOutside c.S n
  · have hw : W (normIdeal n / L) ≠ 0 := by
      intro hw
      exact hn (by simp only [firstTransferPoissonEnergyCoefficient, if_pos hs, hw, mul_zero])
    exact mem_firstTransferIdealWindow.mpr
      ⟨(div_le_iff₀ hL).mp (hW.2 hw).2, hs.1.1⟩
  · exact False.elim (hn (by simp only [firstTransferPoissonEnergyCoefficient, if_neg hs]))

theorem first_transfer_poisson_energy_coefficient_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) (f : Ideal O) :
    Function.HasFiniteSupport (firstTransferPoissonEnergyCoefficient c ξ W L f) :=
  (firstTransferIdealWindow I L).finite_toSet.subset
    (first_transfer_poisson_energy_coefficient_support c ξ hW hL f)

theorem first_transfer_poisson_column_eq_sum (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) (f : Ideal O) (k : O) :
    columnSum c ξ W L k f = ∑ n ∈ firstTransferIdealWindow I L,
      firstTransferPoissonEnergyCoefficient c ξ W L f n * sexticSymbol n k := by
  have heq : columnSum c ξ W L k f = ∑' n : Ideal O,
      firstTransferPoissonEnergyCoefficient c ξ W L f n * sexticSymbol n k := by
    unfold columnSum
    apply tsum_congr
    intro n
    by_cases hn : SquarefreeOutside c.S n
    · simp only [if_pos hn, firstTransferPoissonEnergyCoefficient]
      ring
    · simp only [if_neg hn, firstTransferPoissonEnergyCoefficient, zero_mul]
  rw [heq]
  apply tsum_eq_sum
  intro n hn
  have hb : firstTransferPoissonEnergyCoefficient c ξ W L f n = 0 := by
    by_contra hb
    exact hn (first_transfer_poisson_energy_coefficient_support c ξ hW hL f hb)
  rw [hb, zero_mul]

theorem first_transfer_poisson_energy_pair_support (c : ArithmeticContext)
    (ξ : RayCharacter c) {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) (f : Ideal O) (k : O) :
    Function.support (fun p => firstTransferPoissonEnergyPair c ξ W L f p k) ⊆
      (firstTransferIdealWindow I L : Set (Ideal O)) ×ˢ
        (firstTransferIdealWindow I L : Set (Ideal O)) := by
  intro p hp
  have hb₁ : firstTransferPoissonEnergyCoefficient c ξ W L f p.1 ≠ 0 := by
    intro hb
    exact hp (by simp only [firstTransferPoissonEnergyPair, hb, zero_mul])
  have hb₂ : firstTransferPoissonEnergyCoefficient c ξ W L f p.2 ≠ 0 := by
    intro hb
    exact hp (by simp only [firstTransferPoissonEnergyPair, hb, star_zero, mul_zero, zero_mul])
  exact ⟨first_transfer_poisson_energy_coefficient_support c ξ hW hL f hb₁,
    first_transfer_poisson_energy_coefficient_support c ξ hW hL f hb₂⟩

theorem first_transfer_poisson_column_square (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {L : ℝ} (hL : 0 < L) (f : Ideal O) (k : O) :
    ((‖columnSum c ξ W L k f‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : Ideal O × Ideal O, firstTransferPoissonEnergyPair c ξ W L f p k := by
  let s := firstTransferIdealWindow I L
  have hz (p : Ideal O × Ideal O) (hp : p ∉ s.product s) :
      firstTransferPoissonEnergyPair c ξ W L f p k = 0 := by
    by_contra hne
    exact hp (Finset.mem_product.mpr
      (first_transfer_poisson_energy_pair_support c ξ hW hL f k hne))
  calc
    _ = columnSum c ξ W L k f * star (columnSum c ξ W L k f) := by
      simpa only [Complex.ofReal_pow, starRingEnd_apply] using
        (Complex.mul_conj' (columnSum c ξ W L k f)).symm
    _ = (∑ n ∈ s, firstTransferPoissonEnergyCoefficient c ξ W L f n * sexticSymbol n k) *
        star (∑ n ∈ s, firstTransferPoissonEnergyCoefficient c ξ W L f n * sexticSymbol n k) := by
      rw [first_transfer_poisson_column_eq_sum c ξ hW hL f k]
    _ = ∑ p ∈ s.product s, firstTransferPoissonEnergyPair c ξ W L f p k := by
      rw [Finset.product_eq_sprod, Finset.sum_product, star_sum, Finset.sum_mul]
      simp only [star_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      unfold firstTransferPoissonEnergyPair
      ring
    _ = _ := (tsum_eq_sum hz).symm

theorem first_transfer_poisson_character_row_summable (Φ : RowWeight)
    {H : ℝ} (hH : 0 < H) (n₁ n₂ : Ideal O) :
    Summable (firstTransferPoissonEnergyCharacterRow Φ H n₁ n₂) := by
  obtain ⟨B₁, hB₁, hb₁⟩ := first_transfer_sexticSymbol_uniform_bound n₁
  obtain ⟨B₂, hB₂, hb₂⟩ := first_transfer_sexticSymbol_uniform_bound n₂
  apply Summable.of_norm_bounded (((rowWeight_element_summable Φ hH).mul_right B₁).mul_right B₂)
  intro k
  have hphi : 0 ≤ Φ.value (normElement k / H) :=
    Φ.nonnegative _ (div_nonneg (Nat.cast_nonneg _) hH.le)
  simp only [firstTransferPoissonEnergyCharacterRow, norm_mul, norm_star, Complex.norm_real,
    Real.norm_of_nonneg hphi]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hb₁ k) hphi) (hb₂ k) (norm_nonneg _)
    (mul_nonneg hphi hB₁)

theorem first_transfer_poisson_energy_term_row_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) (L : ℝ)
    {H : ℝ} (hH : 0 < H) (f : Ideal O) (p : Ideal O × Ideal O) :
    Summable (firstTransferPoissonEnergyTerm c ξ Φ W H L f p) := by
  have hs := (first_transfer_poisson_character_row_summable Φ hH p.1 p.2).mul_left
    (firstTransferPoissonEnergyCoefficient c ξ W L f p.1 *
      star (firstTransferPoissonEnergyCoefficient c ξ W L f p.2))
  apply hs.congr
  intro k
  unfold firstTransferPoissonEnergyTerm firstTransferPoissonEnergyPair firstTransferPoissonEnergyCharacterRow
  ring

theorem first_transfer_poisson_finite_rows_summable {α : Type*} (s : Finset α)
    (g : α → O → ℂ) (hzero : ∀ a ∉ s, ∀ k, g a k = 0)
    (hrow : ∀ a, Summable (g a)) :
    Summable (fun p : α × O => g p.1 p.2) := by
  apply summable_norm_iff.mp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro a
    exact (hrow a).norm
  · apply summable_of_hasFiniteSupport
    apply s.finite_toSet.subset
    intro a ha
    by_contra hnot
    exact ha (by simp only [hzero a hnot, norm_zero, tsum_zero])

theorem first_transfer_poisson_energy_term_joint_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L : ℝ} (hH : 0 < H) (hL : 0 < L) (f : Ideal O) :
    Summable (fun p : (Ideal O × Ideal O) × O =>
      firstTransferPoissonEnergyTerm c ξ Φ W H L f p.1 p.2) := by
  apply first_transfer_poisson_finite_rows_summable
    ((firstTransferIdealWindow I L).product (firstTransferIdealWindow I L))
  · intro p hp k
    unfold firstTransferPoissonEnergyTerm
    have hz : firstTransferPoissonEnergyPair c ξ W L f p k = 0 := by
      by_contra hne
      exact hp (Finset.mem_product.mpr
        (first_transfer_poisson_energy_pair_support c ξ hW hL f k hne))
    rw [hz, mul_zero]
  · exact first_transfer_poisson_energy_term_row_summable c ξ Φ W L hH f

theorem first_transfer_poisson_energy_row_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L : ℝ} (hH : 0 < H) (hL : 0 < L) (f : Ideal O) :
    Summable (fun k : O => Φ.value (normElement k / H) * ‖columnSum c ξ W L k f‖ ^ 2) := by
  obtain ⟨B, hB, hbound⟩ := columnSum_uniform_bound c ξ hW hL f
  apply ((rowWeight_element_summable Φ hH).mul_right (B ^ 2)).of_nonneg_of_le
  · intro k
    exact mul_nonneg (Φ.nonnegative _ (div_nonneg (Nat.cast_nonneg _) hH.le)) (sq_nonneg _)
  · intro k
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound k) 2)
      (Φ.nonnegative _ (div_nonneg (Nat.cast_nonneg _) hH.le))

theorem first_transfer_poisson_energy_outer_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) (H L F : ℝ) :
    Summable (fun f : Ideal O =>
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        ∑' k : O, Φ.value (normElement k / H) * ‖columnSum c ξ W L k f‖ ^ 2 else 0) :=
  dyadic_ideal_summable (SquarefreeOutside c.S) F _

set_option maxHeartbeats 800000 in
theorem first_transfer_poisson_energy_row_expansion (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L : ℝ} (hH : 0 < H) (hL : 0 < L) (f : Ideal O) :
    ((∑' k : O, Φ.value (normElement k / H) * ‖columnSum c ξ W L k f‖ ^ 2 : ℝ) : ℂ) =
      ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
        firstTransferPoissonEnergyCoefficient c ξ W L f n₁ *
          star (firstTransferPoissonEnergyCoefficient c ξ W L f n₂) *
            ∑' k : O, firstTransferPoissonEnergyCharacterRow Φ H n₁ n₂ k := by
  have hs := first_transfer_poisson_energy_term_joint_summable c ξ Φ hW hH hL f
  rw [Complex.ofReal_tsum]
  have hpoint (k : O) :
      ((Φ.value (normElement k / H) * ‖columnSum c ξ W L k f‖ ^ 2 : ℝ) : ℂ) =
        ∑' p : Ideal O × Ideal O, firstTransferPoissonEnergyTerm c ξ Φ W H L f p k := by
    rw [Complex.ofReal_mul, first_transfer_poisson_column_square c ξ hW hL f k,
      ← tsum_mul_left]
    rfl
  simp_rw [hpoint]
  rw [hs.tsum_comm, hs.prod.tsum_prod]
  apply tsum_congr
  intro n₁
  apply tsum_congr
  intro n₂
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold firstTransferPoissonEnergyTerm firstTransferPoissonEnergyPair firstTransferPoissonEnergyCharacterRow
  ring

theorem first_transfer_poisson_energy_full_joint_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L : ℝ} (hH : 0 < H) (hL : 0 < L) (F : ℝ) :
    Summable (fun p : (Ideal O × (Ideal O × Ideal O)) × O =>
      if SquarefreeOutside c.S p.1.1 ∧ F ≤ normIdeal p.1.1 ∧ normIdeal p.1.1 < 2 * F then
        firstTransferPoissonEnergyTerm c ξ Φ W H L p.1.1 p.1.2 p.2 else 0) := by
  apply first_transfer_poisson_finite_rows_summable
    ((firstTransferPoissonDiagonalDyadic c F).product
      ((firstTransferIdealWindow I L).product (firstTransferIdealWindow I L)))
    (fun (q : Ideal O × (Ideal O × Ideal O)) (k : O) =>
      if SquarefreeOutside c.S q.1 ∧ F ≤ normIdeal q.1 ∧ normIdeal q.1 < 2 * F then
        firstTransferPoissonEnergyTerm c ξ Φ W H L q.1 q.2 k else 0)
  · rintro ⟨f, p⟩ hnot k
    by_cases hf : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F
    · rw [if_pos hf]
      by_contra hne
      have hpair : firstTransferPoissonEnergyPair c ξ W L f p k ≠ 0 := by
        intro hz
        exact hne (by simp only [firstTransferPoissonEnergyTerm, hz, mul_zero])
      exact hnot (Finset.mem_product.mpr ⟨mem_firstTransferPoissonDiagonalDyadic.mpr hf,
        Finset.mem_product.mpr (first_transfer_poisson_energy_pair_support c ξ hW hL f k hpair)⟩)
    · rw [if_neg hf]
  · rintro ⟨f, p⟩
    by_cases hf : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F
    · simpa only [if_pos hf] using first_transfer_poisson_energy_term_row_summable c ξ Φ W L hH f p
    · simp only [if_neg hf, summable_zero]

theorem first_transfer_poisson_energy_expansion (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) (_hF : 0 < F) :
    (smoothedEnergy c ξ Φ.value W H L F : ℂ) =
      (((L * F)⁻¹ : ℝ) : ℂ) * ∑' f : Ideal O,
        if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
          ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
            firstTransferPoissonEnergyCoefficient c ξ W L f n₁ *
              star (firstTransferPoissonEnergyCoefficient c ξ W L f n₂) *
                ∑' k : O, firstTransferPoissonEnergyCharacterRow Φ H n₁ n₂ k
        else 0 := by
  unfold smoothedEnergy
  rw [Complex.ofReal_mul, Complex.ofReal_tsum]
  congr 1
  apply tsum_congr
  intro f
  by_cases hf : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F
  · simp only [if_pos hf]
    exact first_transfer_poisson_energy_row_expansion c ξ Φ hW hH hL f
  · simp only [if_neg hf, Complex.ofReal_zero]

end QRHShort
