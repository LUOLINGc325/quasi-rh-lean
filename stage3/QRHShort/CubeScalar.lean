import QRHShort.Recombination
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
open Classical
namespace QRHShort
/-- Every short cube scale lies in the range of the completed estimate. -/
theorem cube_short_scale_range {H X hc b : ℝ}
    (hX : 1 ≤ X) (hhc : 0 ≤ hc)
    (hcut : hc ^ (3 : ℕ) = min X (X ^ (2 : ℕ) / H ^ (2 : ℕ)))
    (hb : 1 ≤ b) (hbhc : b ≤ hc) :
    1 ≤ X / b ^ (3 : ℕ) ∧ X / b ^ (3 : ℕ) ≤ X := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hb3 : b ^ (3 : ℕ) ≤ X :=
    (pow_le_pow_left₀ (zero_le_one.trans hb) hbhc 3).trans
      (hcut.trans_le (min_le_left _ _))
  constructor
  · exact (le_div_iff₀ (pow_pos hbpos 3)).mpr (by simpa using hb3)
  · exact div_le_self (zero_le_one.trans hX) (one_le_pow₀ hb)

/-- The cutoff controls the completed-row loss uniformly over short indices. -/
theorem cube_short_completed_loss {H X F hc b nf : ℝ}
    (hH : 0 < H) (hX : 0 < X) (hF : 0 ≤ F) (hHX : H ≤ X * F)
    (hhc : 0 ≤ hc)
    (hcut : hc ^ (3 : ℕ) = min X (X ^ (2 : ℕ) / H ^ (2 : ℕ)))
    (hb : 0 ≤ b) (hbhc : b ≤ hc) (hnf : nf ≤ 2 * F) :
    H + H ^ (2 : ℕ) * nf / (X / b ^ (3 : ℕ)) ≤ 3 * (X * F) := by
  have hb3 : b ^ (3 : ℕ) ≤ hc ^ (3 : ℕ) := pow_le_pow_left₀ hb hbhc 3
  have hcut' : H ^ (2 : ℕ) * hc ^ (3 : ℕ) ≤ X ^ (2 : ℕ) := by
    have ht := hcut.trans_le (min_le_right _ _)
    simpa only [mul_comm] using (le_div_iff₀ (sq_pos_of_pos hH)).mp ht
  have hbound : H ^ (2 : ℕ) * b ^ (3 : ℕ) ≤ X ^ (2 : ℕ) :=
    (mul_le_mul_of_nonneg_left hb3 (sq_nonneg H)).trans hcut'
  have hmul := mul_le_mul_of_nonneg_right hbound (show 0 ≤ 2 * F by positivity)
  have hnf' := mul_le_mul_of_nonneg_left hnf
    (mul_nonneg (sq_nonneg H) (pow_nonneg hb 3))
  have hdiv : H ^ (2 : ℕ) * nf * b ^ (3 : ℕ) / X ≤ 2 * (X * F) := by
    apply (div_le_iff₀ hX).mpr
    nlinarith only [hmul, hnf']
  rw [div_div_eq_mul_div]
  linarith

/-- Keeping the two long cube indices separate still yields a logarithmic
fourth-power loss. No regrouping by ideal divisors is needed. -/
theorem cube_double_recombine {ι τ ρ : Type*}
    [Fintype ι] [Fintype τ] [Fintype ρ]
    (w : ρ → ℝ) (a : ι → ℝ) (b : τ → ℝ)
    (c : ι → ρ → ℂ) (d : ι → τ → ρ → ℂ)
    (V : ι → τ → ρ → ℂ)
    (hw : ∀ r, 0 ≤ w r) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hc : ∀ i r, ‖c i r‖ ≤ a i)
    (hd : ∀ i j r, ‖d i j r‖ ≤ b j)
    {M : ℝ} (hV : ∀ i j, (∑ r, w r * ‖V i j r‖ ^ 2) ≤ M) :
    (∑ r, w r * ‖∑ i, c i r * ∑ j, d i j r * V i j r‖ ^ 2) ≤
      (∑ i, a i) ^ 2 * (∑ j, b j) ^ 2 * M := by
  have hA : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
  have hB : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => hb j)
  have hinner (i : ι) :
      (∑ r, w r * ‖∑ j, d i j r * V i j r‖ ^ 2) ≤
        (∑ j, b j) ^ 2 * M := by
    calc
      _ ≤ (∑ j, b j) * ∑ j, b j * ∑ r, w r * ‖V i j r‖ ^ 2 :=
        recombine_sum w b (d i) (V i) hw hb (hd i)
      _ ≤ (∑ j, b j) * ∑ j, b j * M := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hV i j) (hb j))
      _ = (∑ j, b j) ^ 2 * M := by rw [← Finset.sum_mul]; ring
  calc
    _ ≤ (∑ i, a i) * ∑ i, a i *
        ∑ r, w r * ‖∑ j, d i j r * V i j r‖ ^ 2 :=
      recombine_sum w a c (fun i r => ∑ j, d i j r * V i j r) hw ha hc
    _ ≤ (∑ i, a i) * ∑ i, a i * ((∑ j, b j) ^ 2 * M) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hinner i) (ha i))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Explicit absorption of the harmonic fourth power and the completed-row loss. -/
theorem cube_loss_absorb {D ε A M t u B S E : ℝ}
    (hD : 1 ≤ D) (hε : 0 < ε) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hmass : M ≤ A * D ^ (ε / 8))
    (hE : E ≤ 2 * M ^ (2 : ℕ) * (t * D ^ (ε / 4) * B) +
      2 * M ^ (4 : ℕ) * (u * B + S)) :
    E ≤ (2 * A ^ (2 : ℕ) * t + 2 * A ^ (4 : ℕ) * (u + 1)) *
      D ^ ε * (B + S) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hM2 : M ^ (2 : ℕ) ≤ A ^ (2 : ℕ) * D ^ (ε / 4) := by
    calc
      M ^ (2 : ℕ) ≤ (A * D ^ (ε / 8)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hM hmass 2
      _ = A ^ (2 : ℕ) * D ^ (ε / 4) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hDpos.le]
        congr 1
        congr 1
        ring
  have hM4 : M ^ (4 : ℕ) ≤ A ^ (4 : ℕ) * D ^ (ε / 2) := by
    calc
      M ^ (4 : ℕ) ≤ (A * D ^ (ε / 8)) ^ (4 : ℕ) :=
        pow_le_pow_left₀ hM hmass 4
      _ = A ^ (4 : ℕ) * D ^ (ε / 2) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hDpos.le]
        congr 1
        congr 1
        ring
  have hp : D ^ (ε / 4) * D ^ (ε / 4) = D ^ (ε / 2) := by
    rw [← Real.rpow_add hDpos]
    congr 1
    ring
  have hshort : 2 * M ^ (2 : ℕ) * (t * D ^ (ε / 4) * B) ≤
      2 * A ^ (2 : ℕ) * t * D ^ (ε / 2) * B := by
    calc
      _ ≤ 2 * (A ^ (2 : ℕ) * D ^ (ε / 4)) * (t * D ^ (ε / 4) * B) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 (by norm_num))
          (by positivity)
      _ = 2 * A ^ (2 : ℕ) * t * (D ^ (ε / 4) * D ^ (ε / 4)) * B := by ring
      _ = _ := by rw [hp]
  have hlong : 2 * M ^ (4 : ℕ) * (u * B + S) ≤
      2 * A ^ (4 : ℕ) * D ^ (ε / 2) * (u * B + S) := by
    calc
      _ ≤ 2 * (A ^ (4 : ℕ) * D ^ (ε / 2)) * (u * B + S) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM4 (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hBS : B ≤ B + S := le_add_of_nonneg_right hS
  have hUS : u * B + S ≤ (u + 1) * (B + S) := by
    nlinarith [mul_nonneg hu hS]
  have hi : 2 * A ^ (2 : ℕ) * t * B + 2 * A ^ (4 : ℕ) * (u * B + S) ≤
      (2 * A ^ (2 : ℕ) * t + 2 * A ^ (4 : ℕ) * (u + 1)) * (B + S) := by
    have h₁ := mul_le_mul_of_nonneg_left hBS (show 0 ≤ 2 * A ^ (2 : ℕ) * t by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hUS (show 0 ≤ 2 * A ^ (4 : ℕ) by positivity)
    nlinarith only [h₁, h₂]
  calc
    E ≤ D ^ (ε / 2) *
        (2 * A ^ (2 : ℕ) * t * B + 2 * A ^ (4 : ℕ) * (u * B + S)) := by
      nlinarith only [hE, hshort, hlong]
    _ ≤ D ^ (ε / 2) *
        ((2 * A ^ (2 : ℕ) * t + 2 * A ^ (4 : ℕ) * (u + 1)) * (B + S)) :=
      mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hDpos.le _)
    _ ≤ D ^ ε *
        ((2 * A ^ (2 : ℕ) * t + 2 * A ^ (4 : ℕ) * (u + 1)) * (B + S)) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hD (by linarith)) (by positivity)
    _ = _ := by ring



end QRHShort
