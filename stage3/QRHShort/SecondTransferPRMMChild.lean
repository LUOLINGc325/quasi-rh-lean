import QRHShort.SecondTransferReduction
import QRHShort.EnergyScaling
import QRHShort.ArithmeticBasics
import QRHShort.PrimeComparison
import Mathlib.Data.Finset.Prod

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

private def symbolBound (n : Ideal O) : ℝ :=
  6 ^ (UniqueFactorizationMonoid.normalizedFactors n).card

private theorem symbolBound_nonneg (n : Ideal O) : 0 ≤ symbolBound n := by
  unfold symbolBound
  positivity

private theorem norm_sexticAtPrime_le_six (P : Ideal O) (k : O) :
    ‖sexticAtPrime P k‖ ≤ 6 := by
  unfold sexticAtPrime
  calc
    _ ≤ ∑ j ∈ Finset.range 6, ‖if
        Ideal.Quotient.mk P k ^ ((P.absNorm - 1) / 6) =
          Ideal.Quotient.mk P (rootSix ^ j)
        then embedding (rootSix ^ j) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range 6, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · exact (norm_embedding_rootSix_pow j).le
      · simp
    _ = 6 := by norm_num

private theorem norm_sexticSymbol_le_symbolBound (n : Ideal O) (k : O) :
    ‖sexticSymbol n k‖ ≤ symbolBound n := by
  have hprod (s : Multiset (Ideal O)) :
      ‖(s.map (fun P => sexticAtPrime P k)).prod‖ ≤ (6 : ℝ) ^ s.card := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons,
        pow_succ]
      simpa only [mul_comm] using mul_le_mul (norm_sexticAtPrime_le_six P k) ih
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
  by_cases hn : n = ⊥
  · simpa only [sexticSymbol, if_pos hn, norm_zero] using symbolBound_nonneg n
  · exact (by simpa only [sexticSymbol, if_neg hn, symbolBound] using
      (hprod (UniqueFactorizationMonoid.normalizedFactors n)))

private theorem norm_coefficient_le_fixed (ξ : HeckeCharacter) (n : Ideal O) :
    ‖coefficient ξ n‖ ≤ ‖alpha n‖ * ‖gauss 2 n‖ := by
  simp only [coefficient, norm_mul, norm_star]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (ξ.norm_onElement_le_one (primaryGenerator n))

/-- A fixed upper scale gives a finite ideal window, uniformly in the character and test. -/
theorem second_transfer_prmm_column_bounded_scale (I : SupportInterval) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ArithmeticContext) (ξ : RayCharacter c)
      (W : ℝ → ℂ) (J : ℕ) (L : ℝ) (k : O) (f : Ideal O),
      SmoothSupported I W → 0 < L → L ≤ T →
      ‖columnSum c ξ W L k f‖ ≤ B * weightNorm J W := by
  let S := (finite_normIdeal_le (I.hi * T)).toFinset
  let b (n : Ideal O) : ℝ :=
    ‖alpha n‖ * ‖gauss 2 n‖ * symbolBound n * symbolBound n ^ (4 : ℕ)
  have hb (n : Ideal O) : 0 ≤ b n := by
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (symbolBound_nonneg n))
      (pow_nonneg (symbolBound_nonneg n) _)
  refine ⟨∑ n ∈ S, b n, Finset.sum_nonneg (fun n _ => hb n), ?_⟩
  intro c ξ W J L k f hW hL hLT
  have hN : 0 ≤ weightNorm J W := weightNorm_nonneg hW J
  have hNbound (x : ℝ) : ‖W x‖ ≤ weightNorm J W := by
    simpa only [iteratedDeriv_zero] using
      norm_iteratedDeriv_le_weightNorm hW (Nat.zero_le J) x
  have heq : columnSum c ξ W L k f = ∑ n ∈ S, if SquarefreeOutside c.S n then
      coefficient ξ.val n * sexticSymbol n k *
        sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / L)
      else 0 := by
    unfold columnSum
    apply tsum_eq_sum
    intro n hn
    have hw : W (normIdeal n / L) = 0 := by
      by_contra hw
      have hupper := (div_le_iff₀ hL).mp (hW.2 hw).2
      apply hn
      apply (finite_normIdeal_le (I.hi * T)).mem_toFinset.mpr
      exact hupper.trans (mul_le_mul_of_nonneg_left hLT
        (I.lo_pos.trans_le I.ordered).le)
    simp only [hw, mul_zero, ite_self]
  rw [heq]
  calc
    ‖∑ n ∈ S, if SquarefreeOutside c.S n then
        coefficient ξ.val n * sexticSymbol n k *
          sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / L)
        else 0‖ ≤ ∑ n ∈ S, ‖if SquarefreeOutside c.S n then
        coefficient ξ.val n * sexticSymbol n k *
          sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / L)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, b n * weightNorm J W := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hns : SquarefreeOutside c.S n
      · simp only [if_pos hns, norm_mul, norm_pow]
        apply mul_le_mul _ (hNbound _) (norm_nonneg _) (hb n)
        exact mul_le_mul
          (mul_le_mul (norm_coefficient_le_fixed ξ.val n)
            (norm_sexticSymbol_le_symbolBound n k) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (pow_le_pow_left₀ (norm_nonneg _)
            (norm_sexticSymbol_le_symbolBound n (primaryGenerator f)) 4)
          (pow_nonneg (norm_nonneg _) _)
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (symbolBound_nonneg n))
      · simpa only [if_neg hns, norm_zero] using mul_nonneg (hb n) hN
    _ = (∑ n ∈ S, b n) * weightNorm J W := (Finset.sum_mul _ _ _).symm


/-- A common finite row window controls every smaller row cutoff. -/
theorem second_transfer_prmm_row_bound (column : O → ℂ) (H A B : ℝ)
    (hHA : H ≤ A) (hbound : ∀ k, ‖column k‖ ≤ B) :
    rowEnergy column H ≤ ((finite_normElement_le A).toFinset.card : ℝ) * B ^ 2 := by
  let S := (finite_normElement_le A).toFinset
  have heq : rowEnergy column H = ∑ k ∈ S,
      if 0 < normElement k ∧ normElement k ≤ H then ‖column k‖ ^ 2 else 0 := by
    apply tsum_eq_sum
    intro k hk
    exact if_neg (fun h => hk ((finite_normElement_le A).mem_toFinset.mpr
      (h.2.trans hHA)))
  rw [heq]
  calc
    _ ≤ ∑ _k ∈ S, B ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs
      · exact pow_le_pow_left₀ (norm_nonneg _) (hbound k) 2
      · exact sq_nonneg _
    _ = _ := by simp [S]

/-- Crude finite-window boundedness, with no arithmetic identity or estimate premise. -/
theorem second_transfer_prmm_energy_bounded (I : SupportInterval) (m : ℕ) (A T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ArithmeticContext) (ξ : RayCharacter c)
      (W : ℝ → ℂ) (H X F : ℝ), SmoothSupported I W → weightNorm m W ≤ 1 →
      H ≤ A → 1 ≤ X → X ≤ T → 1 ≤ F → F ≤ T →
      energy c ξ W H X F / (X * F) ≤ B := by
  obtain ⟨B, hB, hcolumns⟩ := second_transfer_prmm_column_bounded_scale I T
  let Q : ℝ := ((finite_normElement_le A).toFinset.card : ℝ) * B ^ 2
  let S := (finite_normIdeal_le (2 * T)).toFinset
  let E : ℝ := (S.card : ℝ) * Q
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hE : 0 ≤ E := mul_nonneg (Nat.cast_nonneg _) hQ
  refine ⟨E, hE, ?_⟩
  intro c ξ W H X F hW hnorm hHA hX hXT hF hFT
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hXF : 1 ≤ X * F := one_le_mul_of_one_le_of_one_le hX hF
  have hcolumn (f : Ideal O) (k : O) : ‖columnSum c ξ W X k f‖ ≤ B := by
    exact (hcolumns c ξ W m X k f hW hX0 hXT).trans
      (mul_le_of_le_one_right hB hnorm)
  have hrow (f : Ideal O) : rowEnergy (fun k => columnSum c ξ W X k f) H ≤ Q :=
    second_transfer_prmm_row_bound _ H A B hHA (hcolumn f)
  have heq : (∑' f : Ideal O,
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => columnSum c ξ W X k f) H else 0) =
      ∑ f ∈ S, if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => columnSum c ξ W X k f) H else 0 := by
    apply tsum_eq_sum
    intro f hf
    exact if_neg (fun h => hf ((finite_normIdeal_le (2 * T)).mem_toFinset.mpr
      (h.2.2.le.trans (by linarith))))
  have houter : (∑' f : Ideal O,
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => columnSum c ξ W X k f) H else 0) ≤ E := by
    rw [heq]
    calc
      _ ≤ ∑ _f ∈ S, Q := by
        apply Finset.sum_le_sum
        intro f hf
        split_ifs
        · exact hrow f
        · exact hQ
      _ = E := by simp [E]
  have henergy : energy c ξ W H X F ≤ E := by
    unfold energy
    exact (mul_le_mul_of_nonneg_left houter (inv_nonneg.mpr (mul_pos hX0 hF0).le)).trans
      (mul_le_of_le_one_left hE (inv_le_one_of_one_le₀ hXF))
  exact (div_le_self (energy_nonneg c ξ W H X F hX0.le hF0.le) hXF).trans henergy

/-- The literal child family is bounded, so totalized supremum pathologies do not occur. -/
theorem second_transfer_childValues_bddAbove (c : ArithmeticContext) (I : SupportInterval)
    (m : ℕ) (H L F Sigma : ℝ) : BddAbove (childValues c I m H L F Sigma) := by
  obtain ⟨B, hB, hbound⟩ := second_transfer_prmm_energy_bounded (enlarged I) m
    (H * L / (Sigma * F)) L
  refine ⟨B, ?_⟩
  rintro v ⟨H', X', F', ξ, W, hH', hX', hF', hHA, hratio, hprod, hW, hnorm, rfl⟩
  have hXT : X' ≤ L := (le_mul_of_one_le_right (zero_le_one.trans hX') hF').trans hprod
  have hFT : F' ≤ L := (le_mul_of_one_le_left (zero_le_one.trans hF') hX').trans hprod
  exact hbound c ξ W H' X' F' hW hnorm hHA hX' hXT hF' hFT

/-- Normalization gives the precise squared-norm child bound for every admissible scale. -/
theorem second_transfer_energy_le_childSup (c : ArithmeticContext) (I : SupportInterval)
    (m : ℕ) (H L F Sigma H' X' F' : ℝ) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (hW : SmoothSupported (enlarged I) W)
    (hH' : 1 ≤ H') (hX' : 1 ≤ X') (hF' : 1 ≤ F')
    (hHA : H' ≤ H * L / (Sigma * F))
    (hratio : H' / (X' * F') ≤ H / Sigma) (hprod : X' * F' ≤ L) :
    energy c ξ W H' X' F' ≤
      childSup c I m H L F Sigma * (X' * F') * weightNorm m W ^ 2 := by
  have hXF : 0 < X' * F' := mul_pos (zero_lt_one.trans_le hX') (zero_lt_one.trans_le hF')
  by_cases hz : weightNorm m W = 0
  · rw [energy_eq_zero_of_weightNorm_eq_zero hW m hz c ξ, hz]
    simp
  have hn : weightNorm m (normalizedWeight m W) ≤ 1 :=
    (weightNorm_normalizedWeight hW m hz).le
  have hmem : energy c ξ (normalizedWeight m W) H' X' F' / (X' * F') ∈
      childValues c I m H L F Sigma :=
    ⟨H', X', F', ξ, normalizedWeight m W, hH', hX', hF', hHA, hratio, hprod,
      hW.normalizedWeight m, hn, rfl⟩
  have hs := QRHLean3.le_supZero (second_transfer_childValues_bddAbove c I m H L F Sigma) hmem
  change energy c ξ (normalizedWeight m W) H' X' F' / (X' * F') ≤
    childSup c I m H L F Sigma at hs
  have he := (div_le_iff₀ hXF).mp hs
  rw [energy_eq_weightNorm_sq_mul_normalizedWeight hW m c ξ]
  nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg (weightNorm m W))]

end QRHShort
