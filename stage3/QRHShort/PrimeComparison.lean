import QRHShort.FiniteSupport
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
The sixth-power row difference is supported on ideals divisible by the selected
prime, once the two stated residue-symbol identities have been proved. This file
proves the coefficient bounds and the passage from those identities to the
actual finite sum and its cardinality bound. It does not assume the row error
estimate or prove the residue-symbol identities.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem norm_mobius_le_one (n : Ideal O) : ‖(mobius n : ℂ)‖ ≤ 1 := by
  by_cases hn : Squarefree n
  · simp [mobius, UniqueFactorizationMonoid.moebius, hn]
  · simp [mobius, UniqueFactorizationMonoid.moebius, hn]

theorem HeckeCharacter.norm_onElement_le_one (χ : HeckeCharacter) (a : O) :
    ‖χ.onElement a‖ ≤ 1 := by
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  by_cases ha : IsUnit (Ideal.Quotient.mk χ.modulus a)
  · obtain ⟨u, hu⟩ := ha
    have hnorm := Complex.norm_eq_one_of_mem_rootsOfUnity
      (χ.residue.apply_mem_rootsOfUnity u)
    have hnorm' : ‖χ.residue (u : O ⧸ χ.modulus)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using hnorm
    simpa only [HeckeCharacter.onElement, hu] using hnorm'.le
  · simp only [HeckeCharacter.onElement, χ.residue.map_nonunit ha, norm_zero, zero_le_one]

theorem HeckeCharacter.norm_onIdeal_le_one (χ : HeckeCharacter) (n : Ideal O) :
    ‖χ.onIdeal n‖ ≤ 1 := by
  by_cases hn : n = ⊥
  · simp only [HeckeCharacter.onIdeal, if_pos hn, norm_zero, zero_le_one]
  · simpa only [HeckeCharacter.onIdeal, if_neg hn] using
      χ.norm_onElement_le_one (idealGenerator n)

def boundedDivisibleIdeals (p : Ideal O) (X : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le X).toFinset.filter (fun n => p ∣ n ∧ n ≠ ⊥)

@[simp] theorem mem_boundedDivisibleIdeals {p n : Ideal O} {X : ℝ} :
    n ∈ boundedDivisibleIdeals p X ↔ normIdeal n ≤ X ∧ p ∣ n ∧ n ≠ ⊥ := by
  simp only [boundedDivisibleIdeals, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]

theorem originalSum_sub_sixth_eq_tsum (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D : ℝ} (hD : 0 < D) (p : Ideal O)
    (hone : ∀ n : Ideal O, Outside c.S n → sexticSymbol n 1 = 1)
    (hsixth : ∀ n : Ideal O, Outside c.S n →
      sexticSymbol n (primaryGenerator p ^ (6 : ℕ)) = if p ∣ n then 0 else 1) :
    originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ)) =
      ∑' n : Ideal O, if Outside c.S n ∧ p ∣ n then
        (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0 := by
  unfold originalSum
  rw [← (originalSum_summable c I hW hD 1).tsum_sub
    (originalSum_summable c I hW hD (primaryGenerator p ^ (6 : ℕ)))]
  apply tsum_congr
  intro n
  by_cases hn : Outside c.S n
  · by_cases hp : p ∣ n <;> simp [hn, hp, hone n hn, hsixth n hn]
  · simp [hn]

theorem originalSum_sub_sixth_eq_sum (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D : ℝ} (hD : 0 < D) (p : Ideal O)
    (hone : ∀ n : Ideal O, Outside c.S n → sexticSymbol n 1 = 1)
    (hsixth : ∀ n : Ideal O, Outside c.S n →
      sexticSymbol n (primaryGenerator p ^ (6 : ℕ)) = if p ∣ n then 0 else 1) :
    originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ)) =
      ∑ n ∈ boundedDivisibleIdeals p (I.hi * D), if Outside c.S n ∧ p ∣ n then
        (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0 := by
  rw [originalSum_sub_sixth_eq_tsum c I hW hD p hone hsixth]
  apply tsum_eq_sum
  intro n hn
  by_cases hc : Outside c.S n ∧ p ∣ n
  · rw [if_pos hc]
    have hzero : W (normIdeal n / D) = 0 := by
      by_contra hw
      have hupper : normIdeal n / D ≤ I.hi := (hW.2 hw).2
      exact hn (mem_boundedDivisibleIdeals.mpr
        ⟨(div_le_iff₀ hD).mp hupper, hc.2, hc.1.1⟩)
    simp only [hzero, mul_zero]
  · simp only [if_neg hc]

theorem originalSum_sub_sixth_norm_bound (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (hWbound : ∀ x : ℝ, ‖W x‖ ≤ B) (p : Ideal O)
    (hone : ∀ n : Ideal O, Outside c.S n → sexticSymbol n 1 = 1)
    (hsixth : ∀ n : Ideal O, Outside c.S n →
      sexticSymbol n (primaryGenerator p ^ (6 : ℕ)) = if p ∣ n then 0 else 1) :
    ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
      ((boundedDivisibleIdeals p (I.hi * D)).card : ℝ) * B := by
  rw [originalSum_sub_sixth_eq_sum c I hW hD p hone hsixth]
  calc
    ‖∑ n ∈ boundedDivisibleIdeals p (I.hi * D), if Outside c.S n ∧ p ∣ n then
        (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0‖ ≤
      ∑ n ∈ boundedDivisibleIdeals p (I.hi * D),
        ‖if Outside c.S n ∧ p ∣ n then
          (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ boundedDivisibleIdeals p (I.hi * D), B := by
      apply Finset.sum_le_sum
      intro n _
      split_ifs
      · have hcoeff : ‖(mobius n : ℂ) * c.nu.onIdeal n‖ ≤ 1 := by
          rw [norm_mul]
          simpa only [one_mul] using mul_le_mul (norm_mobius_le_one n)
            (c.nu.norm_onIdeal_le_one n) (norm_nonneg _) zero_le_one
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hcoeff (hWbound (normIdeal n / D))
          (norm_nonneg _) zero_le_one
      · simpa only [norm_zero] using hB
    _ = ((boundedDivisibleIdeals p (I.hi * D)).card : ℝ) * B := by
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem normIdeal_pos {p : Ideal O} (hp : p ≠ ⊥) : 0 < normIdeal p := by
  unfold normIdeal
  exact_mod_cast Nat.pos_of_ne_zero
    (fun h => hp (Ideal.absNorm_eq_zero_iff.mp h))

@[simp] theorem normIdeal_mul (a b : Ideal O) :
    normIdeal (a * b) = normIdeal a * normIdeal b := by
  simp only [normIdeal, map_mul, Nat.cast_mul]

/-- Multiplication by `p` covers all divisible ideals in the norm ball. -/
theorem card_boundedDivisibleIdeals_le {p : Ideal O} (hp : p ≠ ⊥) (X : ℝ) :
    (boundedDivisibleIdeals p X).card ≤
      (boundedDivisibleIdeals 1 (X / normIdeal p)).card := by
  apply Finset.card_le_card_of_surjOn (fun m : Ideal O => p * m)
  intro n hn
  rcases mem_boundedDivisibleIdeals.mp hn with ⟨hnX, ⟨m, hm⟩, hn0⟩
  refine ⟨m, mem_boundedDivisibleIdeals.mpr ⟨?_, one_dvd _, ?_⟩, hm.symm⟩
  · apply (le_div_iff₀ (normIdeal_pos hp)).mpr
    calc
      normIdeal m * normIdeal p = normIdeal (p * m) := by
        rw [normIdeal_mul, mul_comm]
      _ = normIdeal n := congrArg normIdeal hm.symm
      _ ≤ X := hnX
  · intro hm0
    apply hn0
    simp only [hm, hm0, Ideal.mul_bot]

theorem originalSum_sub_sixth_norm_le_div_norm (c : ArithmeticContext)
    (I : SupportInterval) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D B C : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (hWbound : ∀ x : ℝ, ‖W x‖ ≤ B)
    (hcount : ∀ X : ℝ, 0 < X →
      ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ C * X)
    {p : Ideal O} (hp : p ≠ ⊥)
    (hone : ∀ n : Ideal O, Outside c.S n → sexticSymbol n 1 = 1)
    (hsixth : ∀ n : Ideal O, Outside c.S n →
      sexticSymbol n (primaryGenerator p ^ (6 : ℕ)) = if p ∣ n then 0 else 1) :
    ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
      (C * B * I.hi) * D / normIdeal p := by
  have hI : 0 < I.hi := I.lo_pos.trans_le I.ordered
  have hcard : ((boundedDivisibleIdeals p (I.hi * D)).card : ℝ) ≤
      C * (I.hi * D / normIdeal p) := by
    have hcard' : ((boundedDivisibleIdeals p (I.hi * D)).card : ℝ) ≤
        ((boundedDivisibleIdeals 1 (I.hi * D / normIdeal p)).card : ℝ) := by
      exact_mod_cast card_boundedDivisibleIdeals_le hp (I.hi * D)
    exact hcard'.trans (hcount _ (div_pos (mul_pos hI hD) (normIdeal_pos hp)))
  calc
    ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
        ((boundedDivisibleIdeals p (I.hi * D)).card : ℝ) * B :=
      originalSum_sub_sixth_norm_bound c I hW hD hB hWbound p hone hsixth
    _ ≤ (C * (I.hi * D / normIdeal p)) * B := mul_le_mul_of_nonneg_right hcard hB
    _ = (C * B * I.hi) * D / normIdeal p := by ring

theorem originalSum_sub_sixth_norm_le_div_scale (c : ArithmeticContext)
    (I : SupportInterval) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D Y B C : ℝ} (hD : 0 < D) (hY : 0 < Y) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hWbound : ∀ x : ℝ, ‖W x‖ ≤ B)
    (hcount : ∀ X : ℝ, 0 < X →
      ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ C * X)
    {p : Ideal O} (hp : p ≠ ⊥) (hNp : Y ≤ normIdeal p)
    (hone : ∀ n : Ideal O, Outside c.S n → sexticSymbol n 1 = 1)
    (hsixth : ∀ n : Ideal O, Outside c.S n →
      sexticSymbol n (primaryGenerator p ^ (6 : ℕ)) = if p ∣ n then 0 else 1) :
    ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
      (C * B * I.hi) * D / Y := by
  apply (originalSum_sub_sixth_norm_le_div_norm c I hW hD hB hWbound hcount hp
    hone hsixth).trans
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg (mul_nonneg hC hB) (I.lo_pos.trans_le I.ordered).le) hD.le)
    hY hNp

end QRHShort
