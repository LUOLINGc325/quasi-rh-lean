import QRHShort.Estimates
import QRHShort.WeightNorm
import QRHShort.EnergySupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
The initial scales are reduced to the actual canonical arithmetic energy.
A fixed dilation of the ambient parameter absorbs the constant in the initial
gap. A bounded dilation of the weight handles small column scales. Both
dilations affect the implied constant, while the derivative order remains
independent of the support interval and the initial gap constant.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- One fixed support interval contains every dilation with factor in `[1,R]`. -/
def dilationInterval (I : SupportInterval) (R : ℝ) (hR : 1 ≤ R) : SupportInterval where
  lo := I.lo / R
  hi := I.hi
  lo_pos := div_pos I.lo_pos (lt_of_lt_of_le zero_lt_one hR)
  ordered := (div_le_self I.lo_pos.le hR).trans I.ordered

theorem SmoothSupported.dilate {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {R lam : ℝ} (hR : 1 ≤ R)
    (hlam : 1 ≤ lam) (hlamR : lam ≤ R) :
    SmoothSupported (dilationInterval I R hR) (fun x => W (lam * x)) := by
  refine ⟨hW.1.comp (contDiff_const.mul contDiff_id), ?_⟩
  intro x hx
  have hs := hW.2 hx
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hxpos : 0 < x := by
    by_contra hx
    have hle := mul_nonpos_of_nonneg_of_nonpos hlampos.le (le_of_not_gt hx)
    linarith [I.lo_pos, hs.1]
  change I.lo / R ≤ x ∧ x ≤ I.hi
  constructor
  · apply (div_le_iff₀ hRpos).mpr
    calc
      I.lo ≤ lam * x := hs.1
      _ ≤ x * R := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlamR hxpos.le
  · exact (le_mul_of_one_le_left hxpos.le hlam).trans hs.2

theorem weightNorm_dilate_le {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (J : ℕ) {R lam : ℝ}
    (hR : 1 ≤ R) (hlam : 1 ≤ lam) (hlamR : lam ≤ R) :
    weightNorm J (fun x => W (lam * x)) ≤ R ^ J * weightNorm J W := by
  have hlam0 : 0 ≤ lam := le_trans zero_le_one hlam
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  apply QRHLean3.supZero_le (mul_nonneg (pow_nonneg hR0 _) (weightNorm_nonneg hW J))
  rintro r ⟨j, hj, x, rfl⟩
  have hdiff : ContDiff ℝ j W := hW.1.of_le (by simp)
  rw [iteratedDeriv_comp_const_smul hdiff, norm_smul, Real.norm_of_nonneg
    (pow_nonneg hlam0 _)]
  exact mul_le_mul ((pow_le_pow_left₀ hlam0 hlamR j).trans (pow_le_pow_right₀ hR hj))
    (norm_iteratedDeriv_le_weightNorm hW hj (lam * x)) (norm_nonneg _)
    (pow_nonneg hR0 _)

theorem columnSum_dilate (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X lam : ℝ) (k : O) (f : Ideal O) (hlam : lam ≠ 0) :
    columnSum c ξ (fun x => W (lam * x)) (lam * X) k f = columnSum c ξ W X k f := by
  have harg (a : ℝ) : lam * (a / (lam * X)) = a / X := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      lam * (a * (X⁻¹ * lam⁻¹)) = (lam * lam⁻¹) * (a * X⁻¹) := by ring
      _ = a * X⁻¹ := by simp [hlam]
  unfold columnSum
  apply tsum_congr
  intro n
  simp only [harg]

theorem energy_dilate (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (H X F lam : ℝ) (hlam : lam ≠ 0) :
    energy c ξ (fun x => W (lam * x)) H (lam * X) F =
      lam⁻¹ * energy c ξ W H X F := by
  unfold energy
  simp_rw [columnSum_dilate c ξ W X lam _ _ hlam]
  rw [show lam * X * F = lam * (X * F) by ring, mul_inv_rev]
  ring

theorem rowEnergy_eq_zero_of_lt_one (column : O → ℂ) {H : ℝ} (hH : H < 1) :
    rowEnergy column H = 0 := by
  unfold rowEnergy
  trans ∑' _ : O, (0 : ℝ)
  · apply tsum_congr
    intro k
    apply if_neg
    rintro ⟨hk0, hkH⟩
    change (0 : ℝ) < ((principal k).absNorm : ℝ) at hk0
    have hkNat : 0 < (principal k).absNorm := by
      exact_mod_cast hk0
    have hk1 : 1 ≤ normElement k := by
      change (1 : ℝ) ≤ ((principal k).absNorm : ℝ)
      exact_mod_cast (Nat.succ_le_iff.mpr hkNat)
    linarith
  · exact tsum_zero

theorem energy_eq_zero_of_row_lt_one (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X F : ℝ) {H : ℝ} (hH : H < 1) :
    energy c ξ W H X F = 0 := by
  simp [energy, rowEnergy_eq_zero_of_lt_one _ hH]

theorem columnSum_eq_zero_of_support_scale_lt_one {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (c : ArithmeticContext) (ξ : RayCharacter c)
    {X : ℝ} (hX : 0 < X) (hscale : I.hi * X < 1) (k : O) (f : Ideal O) :
    columnSum c ξ W X k f = 0 := by
  unfold columnSum
  trans ∑' _ : Ideal O, (0 : ℂ)
  · apply tsum_congr
    intro n
    by_cases hn : SquarefreeOutside c.S n
    · rw [if_pos hn]
      have hnorm : 1 ≤ normIdeal n := by
        have hnabs : n.absNorm ≠ 0 := fun h => hn.1.1 (Ideal.absNorm_eq_zero_iff.mp h)
        change (1 : ℝ) ≤ (n.absNorm : ℝ)
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnabs)
      have hweight : W (normIdeal n / X) = 0 := by
        by_contra hw
        have hs := hW.2 hw
        have hupper : normIdeal n ≤ I.hi * X := (div_le_iff₀ hX).mp hs.2
        linarith
      rw [hweight, mul_zero]
    · exact if_neg hn
  · exact tsum_zero

theorem energy_eq_zero_of_support_scale_lt_one {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (c : ArithmeticContext) (ξ : RayCharacter c)
    (H F : ℝ) {X : ℝ} (hX : 0 < X) (hscale : I.hi * X < 1) :
    energy c ξ W H X F = 0 := by
  simp [energy, rowEnergy, columnSum_eq_zero_of_support_scale_lt_one hW c ξ hX hscale]

/-- The initial row bound has the canonical positive gap up to its fixed constant. -/
theorem initial_scale_gap {θ C D B F H : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hH : H ≤ C * D ^ (2 : ℕ) / (D ^ (1 + θ) * B ^ (2 : ℕ))) :
    H ≤ C * ((D / (B * F)) * F) * D ^ (-θ) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hpow : D ^ (1 + θ) = D * D ^ θ := by
    rw [Real.rpow_add hD, Real.rpow_one]
  have hid : C * D ^ (2 : ℕ) / (D ^ (1 + θ) * B ^ (2 : ℕ)) =
      (C * ((D / (B * F)) * F) * D ^ (-θ)) / B := by
    rw [hpow, Real.rpow_neg hD.le]
    field_simp [hD.ne', hBpos.ne', hFpos.ne', (Real.rpow_pos_of_pos hD θ).ne']
    <;> ring
  rw [hid] at hH
  exact hH.trans (div_le_self (by positivity) hB)

private theorem inflated_parent_range {κ θ C D H X F A T : ℝ}
    (hθκ : κ ≤ θ) (hD : 2 ≤ D) (hH : 1 ≤ H) (hX : 0 < X)
    (hF : 1 ≤ F) (hA : 1 ≤ A) (hTA : A ≤ T)
    (hAX : 1 ≤ A * X) (hprod : X * F ≤ D)
    (hC : C ≤ T ^ (1 - κ)) (hgap : H ≤ C * (X * F) * D ^ (-θ)) :
    QRH.ParentRange (T * D) κ 2 H (T * max 1 X) F := by
  have hT : 1 ≤ T := hA.trans hTA
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hDpos : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hmax : max 1 X ≤ A * X := max_le hAX (le_mul_of_one_le_left hX.le hA)
  refine ⟨hH, ?_, hF, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hT (le_max_left _ _)
  · rw [Real.rpow_two]
    calc
      T * max 1 X * F ≤ T * (A * X) * F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hTpos.le) hFpos.le
      _ = (T * A) * (X * F) := by ring
      _ ≤ (T * A) * D := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ (T * T) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTA hTpos.le) hDpos.le
      _ ≤ (T * T) * D * D := le_mul_of_one_le_right (by positivity) hD1
      _ = (T * D) ^ (2 : ℕ) := by ring
  · have hpow : T ^ (1 - κ) = T * T ^ (-κ) := by
      rw [sub_eq_add_neg, Real.rpow_add hTpos, Real.rpow_one]
    calc
      H ≤ C * (X * F) * D ^ (-θ) := hgap
      _ ≤ T ^ (1 - κ) * (X * F) * D ^ (-θ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC (mul_nonneg hX.le hFpos.le)) (by positivity)
      _ ≤ T ^ (1 - κ) * (X * F) * D ^ (-κ) := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hD1 (neg_le_neg hθκ))
          (by positivity)
      _ = (T * X * F) * (T * D) ^ (-κ) := by
        rw [hpow, Real.mul_rpow hTpos.le hDpos.le]
        ring
      _ ≤ (T * max 1 X * F) * (T * D) ^ (-κ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right 1 X) hTpos.le) hFpos.le)
          (by positivity)

/-- The canonical estimate implies the manuscript's actual initial-scale estimate.
The fixed dilation absorbs the initial gap constant for every `D ≥ 2`, including
bounded `D`; no extra boundedness or arithmetic counting hypothesis is added. -/
theorem initial_energy_estimate_of_canonical (hcanonical : CanonicalEstimate)
    {θ : ℝ} (hθ : 0 < θ) (hθupper : θ ≤ (1 : ℝ) / 10) :
    InitialEnergyEstimate θ := by
  intro ε hε
  let κ : ℝ := θ / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  obtain ⟨J, hJ, hcanonicalJ⟩ := hcanonical κ 2 ε hκ (by norm_num) hε
  refine ⟨J, hJ, ?_⟩
  intro c I C hc hC
  let A : ℝ := max 1 I.hi
  let P : ℝ := max C A
  let T : ℝ := P ^ (2 : ℕ)
  let R : ℝ := T * A
  have hA : 1 ≤ A := le_max_left _ _
  have hIhi : I.hi ≤ A := le_max_right _ _
  have hCP : C ≤ P := le_max_left _ _
  have hAP : A ≤ P := le_max_right _ _
  have hP : 1 ≤ P := hC.trans hCP
  have hPT : P ≤ T := le_self_pow₀ hP (by decide : (2 : ℕ) ≠ 0)
  have hTA : A ≤ T := hAP.trans hPT
  have hT : 1 ≤ T := hA.trans hTA
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le hT hA
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hCpow : C ≤ T ^ (1 - κ) := by
    calc
      C ≤ P := hCP
      _ = P ^ (1 : ℝ) := (Real.rpow_one P).symm
      _ ≤ P ^ ((2 : ℝ) * (1 - κ)) :=
        Real.rpow_le_rpow_of_exponent_le hP (by dsimp [κ]; linarith)
      _ = T ^ (1 - κ) := by
        exact Real.rpow_natCast_mul (le_trans zero_le_one hP) 2 (1 - κ)
  let I' : SupportInterval := dilationInterval I R hR
  obtain ⟨K, hK, hbound⟩ := hcanonicalJ c I' hc
  have hconstant : 0 ≤ K * (R ^ J) ^ 2 * R ^ 2 * T ^ ε := by positivity
  refine ⟨K * (R ^ J) ^ 2 * R ^ 2 * T ^ ε, hconstant, ?_⟩
  intro ξ W D B F H hW hD hB hF hHpos hHbound
  have hDpos : 0 < D := by linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
  let X : ℝ := D / (B * F)
  have hX : 0 < X := by dsimp [X]; positivity
  have hXF : X * F = D / B := by
    dsimp [X]
    field_simp [hBpos.ne', hFpos.ne']
  have hprod : X * F ≤ D := by
    rw [hXF]
    exact div_le_self hDpos.le hB
  change energy c ξ W H X F ≤
    (K * (R ^ J) ^ 2 * R ^ 2 * T ^ ε) * weightNorm J W ^ 2 * D ^ ε * (D / B)
  by_cases hHsmall : H < 1
  · rw [energy_eq_zero_of_row_lt_one c ξ W X F hHsmall]
    positivity
  have hH : 1 ≤ H := le_of_not_gt hHsmall
  by_cases hsmall : A * X < 1
  · have hsupport : I.hi * X < 1 :=
      (mul_le_mul_of_nonneg_right hIhi hX.le).trans_lt hsmall
    rw [energy_eq_zero_of_support_scale_lt_one hW c ξ H F hX hsupport]
    positivity
  have hAX : 1 ≤ A * X := le_of_not_gt hsmall
  have hmax : max 1 X ≤ A * X := max_le hAX (le_mul_of_one_le_left hX.le hA)
  let lam : ℝ := T * max 1 X / X
  have hlamX : lam * X = T * max 1 X := by
    dsimp [lam]
    field_simp [hX.ne']
  have hTlam : T ≤ lam := by
    apply (le_div_iff₀ hX).mpr
    exact mul_le_mul_of_nonneg_left (le_max_right 1 X) hTpos.le
  have hlam : 1 ≤ lam := hT.trans hTlam
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hlamR : lam ≤ R := by
    apply (div_le_iff₀ hX).mpr
    calc
      T * max 1 X ≤ T * (A * X) := mul_le_mul_of_nonneg_left hmax hTpos.le
      _ = R * X := by dsimp [R]; ring
  have hU : SmoothSupported I' (fun x => W (lam * x)) := hW.dilate hR hlam hlamR
  have hnorm : weightNorm J (fun x => W (lam * x)) ≤ R ^ J * weightNorm J W :=
    weightNorm_dilate_le hW J hR hlam hlamR
  have hnormsq := pow_le_pow_left₀ (weightNorm_nonneg hU J) hnorm 2
  have hlamsq := pow_le_pow_left₀ hlampos.le hlamR 2
  have hgap : H ≤ C * (X * F) * D ^ (-θ) :=
    initial_scale_gap (le_trans zero_le_one hC) hDpos hB hF hHbound
  have hparent : QRH.ParentRange (T * D) κ 2 H (lam * X) F := by
    rw [hlamX]
    exact inflated_parent_range (by dsimp [κ]; linarith) hD hH hX hF hA hTA
      hAX hprod hCpow hgap
  have hTD : 2 ≤ T * D := hD.trans (le_mul_of_one_le_left hDpos.le hT)
  have hcanonicalBound := hbound ξ (fun x => W (lam * x)) (T * D) H (lam * X) F
    hU hTD hparent
  calc
    energy c ξ W H X F = lam * energy c ξ (fun x => W (lam * x)) H (lam * X) F := by
      rw [energy_dilate c ξ W H X F lam hlampos.ne']
      simp [← mul_assoc, hlampos.ne']
    _ ≤ lam * (K * weightNorm J (fun x => W (lam * x)) ^ 2 * (T * D) ^ ε *
        ((lam * X) * F)) := mul_le_mul_of_nonneg_left hcanonicalBound hlampos.le
    _ = (K * T ^ ε * D ^ ε * (X * F)) *
        (lam ^ 2 * weightNorm J (fun x => W (lam * x)) ^ 2) := by
      rw [Real.mul_rpow hTpos.le hDpos.le]
      ring
    _ ≤ (K * T ^ ε * D ^ ε * (X * F)) *
        (R ^ 2 * (R ^ J * weightNorm J W) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hlamsq hnormsq (sq_nonneg _) (sq_nonneg _)) (by positivity)
    _ = (K * (R ^ J) ^ 2 * R ^ 2 * T ^ ε) * weightNorm J W ^ 2 * D ^ ε * (D / B) := by
      rw [← hXF]
      ring

end QRHShort
