import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Scalar identities and the child-range argument in `lem:second-transfer`.
These lemmas do not assume any arithmetic or analytic estimate. -/

namespace QRHShort

theorem second_transfer_length_identity {L C t g e w : ℝ}
    (hC : C ≠ 0) (ht : t ≠ 0) (hg : g ≠ 0) (he : e ≠ 0) (hw : w ≠ 0) :
    (L / (C * t)) / (g * w) = L / ((t * g / e) * (C * e * w)) := by
  field_simp
  <;> ring

theorem second_transfer_weight_identity {H L F Sigma cI C d t g e : ℝ}
    (hH : H ≠ 0) (hL : L ≠ 0) (hF : F ≠ 0) (hC : C ≠ 0)
    (hd : d ≠ 0) (ht : t ≠ 0) (he : e ≠ 0) :
    (H * C / (d * L ^ 2 * F)) *
        ((cI * Sigma * L * F * d / (H * C ^ 2)) * g / (e * (L / (C * t)))) =
      cI * Sigma * (t * g / e) / L ^ 2 := by
  field_simp
  <;> ring

theorem second_transfer_frequency_identity {H L F Sigma cI C d t g e h : ℝ}
    (hH : H ≠ 0) (hL : L ≠ 0) (hC : C ≠ 0) (ht : t ≠ 0) (he : e ≠ 0) :
    (cI * Sigma * L * F * d / (H * C ^ 2)) * h * g ^ 2 /
        (e * (L / (C * t)) ^ 2) =
      cI * Sigma * F * (d * e * h) * (t * g / e) ^ 2 / (H * L) := by
  field_simp
  <;> ring

/-- Local signed cancellation. The ideal-factorization bijection needed to use
this identity is a separate obligation; this lemma alone is not that bijection. -/
theorem second_transfer_prime_cancellation (P : Prop) [Decidable P] :
    (1 + (if P then (1 : ℤ) else 0)) - (if P then 1 else 0) -
        (if ¬ P then 1 else 0) = (if P then 1 else 0) := by
  by_cases h : P <;> simp [h]

theorem second_transfer_block_mass {Sigma L R : ℝ} (hL : L ≠ 0) (hR : R ≠ 0) :
    (Sigma * R / L ^ 2) * R * (L / R) ^ 2 = Sigma := by
  field_simp
  <;> ring

/-- The delicate lower bound survives every exclusion divisor `j | r`.
Here `r,j,F'` denote norms, and the active-row bound comes from `f' | k'`.
The conclusion is exactly the six scalar constraints in `childValues`. -/
theorem second_transfer_child_scales {H L F Sigma R F' r j : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hF : 1 ≤ F) (hSigma : 0 < Sigma)
    (hHS : H ≤ Sigma) (hR : 1 ≤ R) (hRr : R ≤ r)
    (hF' : 1 ≤ F') (hj : 1 ≤ j) (hjr : j ≤ r)
    (hactive : F' ≤ H * L / (Sigma * F * r ^ 2)) :
    1 ≤ H * L / (Sigma * F * R ^ 2) ∧
    1 ≤ (L / (R * F')) / j ∧
    1 ≤ F' * j ∧
    H * L / (Sigma * F * R ^ 2) ≤ H * L / (Sigma * F) ∧
    (H * L / (Sigma * F * R ^ 2)) / ((L / (R * F') / j) * (F' * j)) ≤
      H / Sigma ∧
    (L / (R * F') / j) * (F' * j) ≤ L := by
  have hF0 : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hr0 : 0 < r := lt_of_lt_of_le hR0 hRr
  have hF'0 : 0 < F' := lt_of_lt_of_le zero_lt_one hF'
  have hj0 : 0 < j := lt_of_lt_of_le zero_lt_one hj
  have hSF : 0 < Sigma * F := mul_pos hSigma hF0
  have hrr : R ^ 2 ≤ r ^ 2 := by nlinarith
  have hRj : R * j ≤ r ^ 2 := by
    calc
      R * j ≤ r * r := mul_le_mul hRr hjr hj0.le hr0.le
      _ = r ^ 2 := by ring
  have hHSF : H ≤ Sigma * F :=
    hHS.trans (le_mul_of_one_le_right hSigma.le hF)
  have hactive' : F' * (Sigma * F * r ^ 2) ≤ H * L :=
    (le_div_iff₀ (mul_pos hSF (sq_pos_of_pos hr0))).mp hactive
  have hscale : F' * (R * j) ≤ L := by
    apply (mul_le_mul_iff_left₀ hH).mp
    calc
      F' * (R * j) * H ≤ F' * r ^ 2 * H :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRj hF'0.le) hH.le
      _ ≤ F' * r ^ 2 * (Sigma * F) :=
        mul_le_mul_of_nonneg_left hHSF (mul_nonneg hF'0.le (sq_nonneg r))
      _ ≤ L * H := by nlinarith only [hactive']
  have hheight : 1 ≤ H * L / (Sigma * F * R ^ 2) := by
    apply hF'.trans
    apply hactive.trans
    exact div_le_div_of_nonneg_left (mul_pos hH hL).le
      (mul_pos hSF (sq_pos_of_pos hR0)) (mul_le_mul_of_nonneg_left hrr hSF.le)
  have hcolumn : 1 ≤ (L / (R * F')) / j := by
    apply (le_div_iff₀ hj0).mpr
    rw [one_mul]
    apply (le_div_iff₀ (mul_pos hR0 hF'0)).mpr
    nlinarith only [hscale]
  have hproduct : (L / (R * F') / j) * (F' * j) = L / R := by
    field_simp
    <;> ring
  have hratio : (H * L / (Sigma * F * R ^ 2)) /
      ((L / (R * F') / j) * (F' * j)) = H / (Sigma * F * R) := by
    rw [hproduct]
    field_simp
    <;> ring
  refine ⟨hheight, hcolumn, one_le_mul_of_one_le_of_one_le hF' hj, ?_, ?_, ?_⟩
  · apply div_le_div_of_nonneg_left (mul_pos hH hL).le hSF
    exact le_mul_of_one_le_right hSF.le (by nlinarith : 1 ≤ R ^ 2)
  · rw [hratio]
    apply div_le_div_of_nonneg_left hH.le hSigma
    exact (le_mul_of_one_le_right hSigma.le hF).trans
      (le_mul_of_one_le_right hSF.le hR)
  · rw [hproduct]
    exact div_le_self hL.le hR

end QRHShort
