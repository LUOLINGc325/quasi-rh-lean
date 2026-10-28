import QRHShort.FirstTransferPoissonPreMobiusDefinition

/-! The actual finite pre-Möbius zero contribution is bounded by the proved
weighted diagonal count.  Its support reduction is proved directly from the
literal summand and the explicit Poisson-zero premise. -/

noncomputable section

open Classical
open scoped BigOperators

namespace QRHShort

theorem first_transfer_preMobius_zero_symbol_norm_le_one (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O) : ‖sexticSymbol n z‖ ≤ 1 := by
  by_cases hz : IsUnit (Ideal.Quotient.mk n z)
  · exact (first_transfer_norm_sexticSymbol_of_unit c hn z hz).le
  · rw [firstTransferSexticSymbol_eq_zero_of_nonunit c hn z hz, norm_zero]
    exact zero_le_one

theorem first_transfer_preMobius_zero_energy_coefficient_norm_le
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (L : ℝ) (f : Ideal O) {n : Ideal O}
    (hn : SquarefreeOutside c.S n) :
    ‖firstTransferPoissonEnergyCoefficient c ξ W L f n‖ ≤ ‖W (normIdeal n / L)‖ := by
  rw [firstTransferPoissonEnergyCoefficient, ite_eq_left hn, norm_mul, norm_mul,
    norm_pow, first_transfer_poisson_coefficient_norm c hc ξ hn, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (first_transfer_preMobius_zero_symbol_norm_le_one c hn.1 _))

theorem first_transfer_preMobius_zeroTerm_eq_zero_of_nonunit_pair
    (hz : PoissonZeroStatement) (c : ArithmeticContext) (Φ : RowWeight)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) (f C a b : Ideal O)
    (hpair : ¬ (a = ⊤ ∧ b = ⊤)) :
    firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, a, b) = 0 := by
  unfold firstTransferPreMobiusZeroTerm
  split_ifs with ht
  · rw [first_transfer_paired_poissonZeroTerm_eq_zero hz c
      ht.2.1 ht.2.2.1 ht.2.2.2.2.2 hpair, mul_zero]
  · rfl

theorem first_transfer_preMobius_zeroTerm_diagonal_norm_le
    (hz : PoissonZeroStatement) (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ)
    {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (f : Ideal O) {C : Ideal O} (hC : SquarefreeOutside c.S C) :
    ‖firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, ⊤, ⊤)‖ ≤
      H / (L * F) * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ *
        ‖W (normIdeal C / L)‖ ^ 2 := by
  have hLF : 0 < L * F := mul_pos hL hF
  have hcoef := first_transfer_preMobius_zero_energy_coefficient_norm_le c hc ξ W L f hC
  have hcoefsq : ‖firstTransferPoissonEnergyCoefficient c ξ W L f C‖ ^ 2 ≤
      ‖W (normIdeal C / L)‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hcoef
  unfold firstTransferPreMobiusZeroTerm
  split_ifs with ht
  · simp only [Ideal.mul_top]
    have hzero := first_transfer_poissonZeroTerm_norm_le hz
      (firstTransferPrimitivePairedCharacter c ht.2.1 ht.2.2.1 ht.2.2.2.2.2)
      C hC.1.1 Φ H hH
    calc
      _ = (L * F)⁻¹ * ‖firstTransferPoissonEnergyCoefficient c ξ W L f C‖ ^ 2 *
          ‖poissonZeroTerm
            (firstTransferPrimitivePairedCharacter c ht.2.1 ht.2.2.1 ht.2.2.2.2.2)
            C (fun x => (Φ.value x : ℂ)) H‖ := by
        simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_of_pos hLF, pow_two, mul_assoc]
      _ ≤ (L * F)⁻¹ * ‖W (normIdeal C / L)‖ ^ 2 *
          (H * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoefsq (inv_nonneg.mpr hLF.le)) hzero
          (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hLF.le) (sq_nonneg _))
      _ = _ := by ring
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg hH.le hLF.le) (norm_nonneg _)) (sq_nonneg _)

theorem first_transfer_preMobius_zero_pair_sum_norm_le
    (hz : PoissonZeroStatement) (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ)
    {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (f : Ideal O) {C : Ideal O} (hC : SquarefreeOutside c.S C) :
    ‖∑ p ∈ firstTransferPreMobiusPairWindow I L C,
      firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2)‖ ≤
      H / (L * F) * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ *
        ‖W (normIdeal C / L)‖ ^ 2 := by
  calc
    _ ≤ ∑ p ∈ firstTransferPreMobiusPairWindow I L C,
        ‖firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2)‖ :=
      norm_sum_le _ _
    _ ≤ ‖firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, ⊤, ⊤)‖ := by
      by_cases hmem : (⊤, ⊤) ∈ firstTransferPreMobiusPairWindow I L C
      · apply le_of_eq
        apply Finset.sum_eq_single (⊤, ⊤)
        · intro p _ hp
          have hpair : ¬ (p.1 = ⊤ ∧ p.2 = ⊤) := by
            rintro ⟨ha, hb⟩
            exact hp (Prod.ext ha hb)
          rw [first_transfer_preMobius_zeroTerm_eq_zero_of_nonunit_pair
            hz c Φ ξ W H L F f C p.1 p.2 hpair, norm_zero]
        · intro hn
          exact (hn hmem).elim
      · have hzero : ∀ p ∈ firstTransferPreMobiusPairWindow I L C,
            ‖firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, p.1, p.2)‖ = 0 := by
          intro p hp
          have hpair : ¬ (p.1 = ⊤ ∧ p.2 = ⊤) := by
            rintro ⟨ha, hb⟩
            have hpTop : p = (⊤, ⊤) := Prod.ext ha hb
            exact hmem (hpTop ▸ hp)
          rw [first_transfer_preMobius_zeroTerm_eq_zero_of_nonunit_pair
            hz c Φ ξ W H L F f C p.1 p.2 hpair, norm_zero]
        rw [Finset.sum_eq_zero hzero]
        exact norm_nonneg _
    _ ≤ _ := first_transfer_preMobius_zeroTerm_diagonal_norm_le hz c hc Φ ξ W hH hL hF f hC

end QRHShort
