import QRHShort.FirstTransferPoissonKernelNormalization
import QRHShort.FirstTransferFiniteSupport

/-! Support alone bounds the global kernel parameter and the literal dual
frequency. It also removes every outer row beyond the manuscript cutoff. -/

noncomputable section

open Classical

namespace QRHShort

theorem first_transfer_kernel_parameter_le_of_ne_zero (I : SupportInterval)
    (Φ : RowWeight) (W : ℝ → ℂ) (hW : SmoothSupported I W)
    {a : ℝ} (ha : 0 ≤ a) {z : BoxSpace 2}
    (hz : firstTransferKernel Φ W a z ≠ 0) :
    a ≤ Φ.fourierCap * I.hi ^ 2 := by
  have hbox := firstTransferKernel_support I Φ W hW a hz
  have hz₀ : 0 < z 0 := I.lo_pos.trans_le (hbox 0).1
  have hz₁ : 0 < z 1 := I.lo_pos.trans_le (hbox 1).1
  have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
  have hprod : 0 < z 0 * z 1 := mul_pos hz₀ hz₁
  have hfourier : radialFourier (fun x => (Φ.value x : ℂ)) (a / (z 0 * z 1)) ≠ 0 := by
    intro hzero
    exact hz (by simp only [firstTransferKernel, hzero, mul_zero])
  have hcap := (Φ.fourier_support ⟨hfourier, div_nonneg ha hprod.le⟩).2
  have hprod_le : z 0 * z 1 ≤ I.hi ^ 2 := by
    calc
      z 0 * z 1 ≤ I.hi * I.hi := mul_le_mul (hbox 0).2 (hbox 1).2 hz₁.le hhi.le
      _ = I.hi ^ 2 := (pow_two _).symm
  exact ((div_le_iff₀ hprod).mp hcap).trans
    (mul_le_mul_of_nonneg_left hprod_le Φ.cap_pos.le)

theorem first_transfer_kernel_eq_zero_of_parameter_gt (I : SupportInterval)
    (Φ : RowWeight) (W : ℝ → ℂ) (hW : SmoothSupported I W)
    {a : ℝ} (ha : 0 ≤ a) (hbound : Φ.fourierCap * I.hi ^ 2 < a)
    (z : BoxSpace 2) : firstTransferKernel Φ W a z = 0 := by
  by_contra hz
  exact (not_le_of_gt hbound) (first_transfer_kernel_parameter_le_of_ne_zero I Φ W hW ha hz)

theorem first_transfer_frequency_le_of_kernel_ne_zero (I : SupportInterval)
    (Φ : RowWeight) (W : ℝ → ℂ) (hW : SmoothSupported I W)
    {H L NC Nd v : ℝ} (hH : 0 < H) (hL : 0 < L) (hNC : 0 < NC)
    (hNd : 0 < Nd) (hv : 0 ≤ v) {z : BoxSpace 2}
    (hz : firstTransferKernel Φ W (H * v * NC ^ 2 / (L ^ 2 * Nd)) z ≠ 0) :
    v ≤ Φ.fourierCap * I.hi ^ 2 * L ^ 2 * Nd / (H * NC ^ 2) := by
  have hden : 0 < L ^ 2 * Nd := mul_pos (sq_pos_of_pos hL) hNd
  have ha : 0 ≤ H * v * NC ^ 2 / (L ^ 2 * Nd) := by positivity
  have hparameter := first_transfer_kernel_parameter_le_of_ne_zero I Φ W hW ha hz
  apply (le_div_iff₀ (mul_pos hH (sq_pos_of_pos hNC))).mpr
  calc
    v * (H * NC ^ 2) =
        (H * v * NC ^ 2 / (L ^ 2 * Nd)) * (L ^ 2 * Nd) := by field_simp
    _ ≤ (Φ.fourierCap * I.hi ^ 2) * (L ^ 2 * Nd) :=
      mul_le_mul_of_nonneg_right hparameter hden.le
    _ = Φ.fourierCap * I.hi ^ 2 * L ^ 2 * Nd := by ring

theorem first_transfer_kernel_eq_zero_of_frequency_gt (I : SupportInterval)
    (Φ : RowWeight) (W : ℝ → ℂ) (hW : SmoothSupported I W)
    {H L NC Nd v : ℝ} (hH : 0 < H) (hL : 0 < L) (hNC : 0 < NC)
    (hNd : 0 < Nd) (hv : 0 ≤ v)
    (hbound : Φ.fourierCap * I.hi ^ 2 * L ^ 2 * Nd / (H * NC ^ 2) < v)
    (z : BoxSpace 2) :
    firstTransferKernel Φ W (H * v * NC ^ 2 / (L ^ 2 * Nd)) z = 0 := by
  by_contra hz
  exact (not_le_of_gt hbound)
    (first_transfer_frequency_le_of_kernel_ne_zero I Φ W hW hH hL hNC hNd hv hz)

theorem first_transfer_scaled_weight_eq_zero_of_outer_gt (I : SupportInterval)
    (W : ℝ → ℂ) (hW : SmoothSupported I W) {NC NT L x : ℝ}
    (hNC : 0 < NC) (hNT : 0 < NT) (hL : 0 < L) (hx : 1 ≤ x)
    (houter : I.hi * L < NC * NT) : W (x / (L / (NC * NT))) = 0 := by
  by_contra hzero
  have hprod : 0 < NC * NT := mul_pos hNC hNT
  have hell : 0 < L / (NC * NT) := div_pos hL hprod
  have hsupport := (hW.2 hzero).2
  have hxbound := (div_le_iff₀ hell).mp hsupport
  have hone : 1 ≤ I.hi * L / (NC * NT) := by
    simpa only [mul_div_assoc] using hx.trans hxbound
  have hbound : NC * NT ≤ I.hi * L := by
    simpa only [one_mul] using (le_div_iff₀ hprod).mp hone
  exact (not_le_of_gt houter) hbound

theorem first_transfer_scaled_weight_eq_zero_of_outer_cutoff (I : SupportInterval)
    (W : ℝ → ℂ) (hW : SmoothSupported I W) {NC NT L x : ℝ}
    (hNC : 0 < NC) (hNT : 0 < NT) (hL : 0 < L) (hx : 1 ≤ x)
    (houter : 2 * I.hi * L < NC * NT) : W (x / (L / (NC * NT))) = 0 := by
  apply first_transfer_scaled_weight_eq_zero_of_outer_gt I W hW hNC hNT hL hx
  have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
  exact (show I.hi * L ≤ 2 * I.hi * L by nlinarith [mul_pos hhi hL]).trans_lt houter

theorem first_transfer_firstColumn_eq_zero_of_outer_cutoff
    (c : ArithmeticContext) (ξ : RayCharacter c) (I : SupportInterval)
    (W : ℝ → ℂ) (hW : SmoothSupported I W) {C t : Ideal O}
    (hC : C ≠ ⊥) (ht : t ≠ ⊥) {L : ℝ} (hL : 0 < L)
    (houter : 2 * I.hi * L < normIdeal C * normIdeal t) (d : Ideal O) (y : O) :
    firstColumn c ξ C d t W (L / (normIdeal C * normIdeal t)) y = 0 := by
  rw [firstColumn_eq_firstTransferCoefficient]
  have hzero (n : Ideal O) : firstTransferCoefficient c ξ C d t y n *
      W (normIdeal n / (L / (normIdeal C * normIdeal t))) = 0 := by
    by_cases hn : n = ⊥
    · subst n
      simp only [firstTransferCoefficient, SquarefreeOutside, Outside, ne_eq, not_true_eq_false,
        false_and, ite_false, zero_mul]
    · rw [first_transfer_scaled_weight_eq_zero_of_outer_cutoff I W hW
        (normIdeal_pos hC) (normIdeal_pos ht) hL (first_transfer_one_le_normIdeal hn) houter,
        mul_zero]
  simp only [hzero, tsum_zero]

theorem first_transfer_poisson_kernel_normalization_ideals (Φ : RowWeight) (W : ℝ → ℂ)
    {C t d n₁ n₂ : Ideal O} (hC : C ≠ ⊥) (ht : t ≠ ⊥) (hd : d ≠ ⊥)
    (hn₁ : n₁ ≠ ⊥) (hn₂ : n₂ ≠ ⊥) {L F : ℝ} (hL : 0 < L) (hF : 0 < F)
    (H v : ℝ) :
    (((L * F)⁻¹ : ℝ) : ℂ) * (H : ℂ) /
        (Real.sqrt (normIdeal ((t * n₁) * (t * n₂))) : ℂ) / (normIdeal d : ℂ) *
        W (normIdeal n₁ / (L / (normIdeal C * normIdeal t))) *
        star (W (normIdeal n₂ / (L / (normIdeal C * normIdeal t)))) *
        radialFourier (fun x => (Φ.value x : ℂ))
          (H * v / (normIdeal d * normIdeal ((t * n₁) * (t * n₂)))) =
      ((H * normIdeal C / (normIdeal d * L ^ 2 * F) : ℝ) : ℂ) *
        firstTransferKernel Φ W (H * v * normIdeal C ^ 2 / (L ^ 2 * normIdeal d))
          ![normIdeal n₁ / (L / (normIdeal C * normIdeal t)),
            normIdeal n₂ / (L / (normIdeal C * normIdeal t))] := by
  simpa only [normIdeal_mul] using first_transfer_poisson_kernel_normalization Φ W
    (normIdeal_pos hC) (normIdeal_pos ht) (normIdeal_pos hd) hL hF
    (normIdeal_pos hn₁) (normIdeal_pos hn₂) H v

theorem first_transfer_kernel_eq_zero_of_ideal_frequency_gt (I : SupportInterval)
    (Φ : RowWeight) (W : ℝ → ℂ) (hW : SmoothSupported I W)
    {H L : ℝ} (hH : 0 < H) (hL : 0 < L) {C d : Ideal O}
    (hC : C ≠ ⊥) (hd : d ≠ ⊥) (h : O)
    (hbound : Φ.fourierCap * I.hi ^ 2 * L ^ 2 * normIdeal d /
      (H * normIdeal C ^ 2) < normElement h) (z : BoxSpace 2) :
    firstTransferKernel Φ W
      (H * normElement h * normIdeal C ^ 2 / (L ^ 2 * normIdeal d)) z = 0 :=
  first_transfer_kernel_eq_zero_of_frequency_gt I Φ W hW hH hL
    (normIdeal_pos hC) (normIdeal_pos hd) (Nat.cast_nonneg _) hbound z

end QRHShort
