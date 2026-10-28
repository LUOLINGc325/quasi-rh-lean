import QRHShort.FirstTransferReduction
import QRHShort.SmoothedSummability

/-!
Finite ranges and genuine convergence for child M. The ideal window is chosen
from the support interval and scale before the test function or row variable.
The Schwartz row weight is not compactly supported: convergence of its element
sum is proved separately, using `rowWeight_element_summable`.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_one_le_normIdeal {a : Ideal O} (ha : a ≠ ⊥) :
    1 ≤ normIdeal a := by
  have h : 1 ≤ a.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h => ha (Ideal.absNorm_eq_zero_iff.mp h))
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast h

theorem first_transfer_normIdeal_le_of_dvd {d C : Ideal O}
    (hC : C ≠ ⊥) (hd : d ∣ C) : normIdeal d ≤ normIdeal C := by
  have hpos : 0 < C.absNorm := Nat.pos_of_ne_zero
    (fun h => hC (Ideal.absNorm_eq_zero_iff.mp h))
  change (d.absNorm : ℝ) ≤ (C.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)

theorem first_transfer_divisors_finite {C : Ideal O} (hC : C ≠ ⊥) :
    {d : Ideal O | d ∣ C}.Finite :=
  (finite_normIdeal_le (normIdeal C)).subset
    (fun _ hd => first_transfer_normIdeal_le_of_dvd hC hd)

/-- Both outer ideal coordinates are bounded because nonzero ideal norms
are at least one. -/
theorem first_transfer_outer_ranges_finite (c : ArithmeticContext) (B : ℝ) :
    {p : Ideal O × Ideal O | SquarefreeOutside c.S p.1 ∧
      SquarefreeOutside c.S p.2 ∧ IsRelPrime p.1 p.2 ∧
        normIdeal p.1 * normIdeal p.2 ≤ B}.Finite := by
  apply ((finite_normIdeal_le B).prod (finite_normIdeal_le B)).subset
  rintro ⟨C, t⟩ ⟨hC, ht, _, hbound⟩
  have hC1 := first_transfer_one_le_normIdeal hC.1.1
  have ht1 := first_transfer_one_le_normIdeal ht.1.1
  exact ⟨(le_mul_of_one_le_right (zero_le_one.trans hC1) ht1).trans hbound,
    (le_mul_of_one_le_left (zero_le_one.trans ht1) hC1).trans hbound⟩

theorem first_transfer_middle_hasFiniteSupport (c : ArithmeticContext)
    (B : ℝ) (C : Ideal O) (v : Ideal O → ℝ) :
    Function.HasFiniteSupport (fun t : Ideal O =>
      if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ B then v t else 0) := by
  apply (finite_normIdeal_le B).subset
  intro t ht
  by_cases h : SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧
      IsRelPrime C t ∧ normIdeal C * normIdeal t ≤ B
  · exact (le_mul_of_one_le_left (normIdeal_pos h.2.1.1.1).le
      (first_transfer_one_le_normIdeal h.1.1.1)).trans h.2.2.2
  · exact False.elim (ht (if_neg h))

theorem first_transfer_outer_hasFiniteSupport (c : ArithmeticContext)
    (B : ℝ) (v : Ideal O → Ideal O → ℝ) :
    Function.HasFiniteSupport (fun C : Ideal O => ∑' t : Ideal O,
      if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ B then v C t else 0) := by
  apply (finite_normIdeal_le B).subset
  intro C hC
  by_contra hbound
  apply hC
  have hz (t : Ideal O) : (if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧
      IsRelPrime C t ∧ normIdeal C * normIdeal t ≤ B then v C t else 0) = 0 := by
    apply if_neg
    intro h
    apply hbound
    exact (le_mul_of_one_le_right (normIdeal_pos h.1.1.1).le
      (first_transfer_one_le_normIdeal h.2.1.1.1)).trans h.2.2.2
  simp only [hz, tsum_zero]

/-- A fixed finite ideal window, with zero excluded to ensure positive
sampling points. It does not depend on the test function or row variable. -/
def firstTransferIdealWindow (I : SupportInterval) (ell : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le (I.hi * ell)).toFinset.filter (fun n => n ≠ ⊥)

theorem mem_firstTransferIdealWindow {I : SupportInterval} {ell : ℝ} {n : Ideal O} :
    n ∈ firstTransferIdealWindow I ell ↔ normIdeal n ≤ I.hi * ell ∧ n ≠ ⊥ := by
  simp only [firstTransferIdealWindow, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]

theorem firstTransferIdealWindow_sample_pos {I : SupportInterval} {ell : ℝ}
    (hell : 0 < ell) {n : Ideal O} (hn : n ∈ firstTransferIdealWindow I ell) :
    0 < normIdeal n / ell :=
  div_pos (normIdeal_pos (mem_firstTransferIdealWindow.mp hn).2) hell

theorem firstTransferCoefficient_mul_eq_zero_of_not_mem
    (c : ArithmeticContext) (ξ : RayCharacter c) (C d t : Ideal O)
    {I : SupportInterval} {U : ℝ → ℂ} (hU : SmoothSupported I U)
    {ell : ℝ} (hell : 0 < ell) (y : O) (n : Ideal O)
    (hn : n ∉ firstTransferIdealWindow I ell) :
    firstTransferCoefficient c ξ C d t y n * U (normIdeal n / ell) = 0 := by
  by_cases hn0 : n = ⊥
  · subst n
    simp [firstTransferCoefficient, SquarefreeOutside, Outside]
  · have hU0 : U (normIdeal n / ell) = 0 := by
      by_contra hU0
      exact hn (mem_firstTransferIdealWindow.mpr
        ⟨(div_le_iff₀ hell).mp (hU.2 hU0).2, hn0⟩)
    simp only [hU0, mul_zero]

theorem firstColumn_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) {I : SupportInterval} {U : ℝ → ℂ}
    (hU : SmoothSupported I U) {ell : ℝ} (hell : 0 < ell) (y : O) :
    Function.HasFiniteSupport (fun n : Ideal O =>
      firstTransferCoefficient c ξ C d t y n * U (normIdeal n / ell)) :=
  weighted_ideal_hasFiniteSupport _ I hU.2 hell

theorem firstColumn_summable (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) {I : SupportInterval} {U : ℝ → ℂ}
    (hU : SmoothSupported I U) {ell : ℝ} (hell : 0 < ell) (y : O) :
    Summable (fun n : Ideal O =>
      firstTransferCoefficient c ξ C d t y n * U (normIdeal n / ell)) :=
  summable_of_hasFiniteSupport (firstColumn_hasFiniteSupport c ξ C d t hU hell y)

theorem firstColumn_eq_sum_window (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) {I : SupportInterval} {U : ℝ → ℂ}
    (hU : SmoothSupported I U) {ell : ℝ} (hell : 0 < ell) (y : O) :
    firstColumn c ξ C d t U ell y =
      ∑ n ∈ firstTransferIdealWindow I ell,
        firstTransferCoefficient c ξ C d t y n * U (normIdeal n / ell) := by
  rw [firstColumn_eq_firstTransferCoefficient]
  exact tsum_eq_sum (fun n hn =>
    firstTransferCoefficient_mul_eq_zero_of_not_mem c ξ C d t hU hell y n hn)

/-- A crude fixed-denominator bound suffices for convergence. This asserts
no sharp residue-symbol identity. -/
theorem first_transfer_sexticSymbol_uniform_bound (n : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : O, ‖sexticSymbol n y‖ ≤ B := by
  have hprime (P : Ideal O) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : O, ‖sexticAtPrime P y‖ ≤ B := by
    refine ⟨∑ j ∈ Finset.range 6, ‖embedding (rootSix ^ j)‖,
      Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
    intro y
    unfold sexticAtPrime
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (embedding (rootSix ^ j))
  have hprod (s : Multiset (Ideal O)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : O,
      ‖(s.map (fun P => sexticAtPrime P y)).prod‖ ≤ B := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, zero_le_one, by intro y; simp⟩
    | @cons P s ih =>
      obtain ⟨A, hA, hPA⟩ := hprime P
      obtain ⟨B, hB, hSB⟩ := ih
      refine ⟨A * B, mul_nonneg hA hB, ?_⟩
      intro y
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul (hPA y) (hSB y) (norm_nonneg _) hA
  by_cases hn : n = ⊥
  · exact ⟨0, le_rfl, by intro y; simp [sexticSymbol, hn]⟩
  · obtain ⟨B, hB, hbound⟩ := hprod (UniqueFactorizationMonoid.normalizedFactors n)
    exact ⟨B, hB, by intro y; simpa only [sexticSymbol, if_neg hn] using hbound y⟩

theorem firstTransferCoefficient_uniform_bound (c : ArithmeticContext)
    (ξ : RayCharacter c) (C d t n : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : O, ‖firstTransferCoefficient c ξ C d t y n‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := first_transfer_sexticSymbol_uniform_bound n
  refine ⟨‖(mobius n : ℂ) * rayValue ξ.val n‖ * B *
    ‖sexticSymbol n (primaryGenerator C) ^ (4 : ℕ) *
      sexticSymbol n (primaryGenerator d)‖, by positivity, ?_⟩
  intro y
  unfold firstTransferCoefficient
  split_ifs
  · rw [show (mobius n : ℂ) * rayValue ξ.val n * star (sexticSymbol n y) *
        sexticSymbol n (primaryGenerator C) ^ 4 * sexticSymbol n (primaryGenerator d) =
        ((mobius n : ℂ) * rayValue ξ.val n) * star (sexticSymbol n y) *
          (sexticSymbol n (primaryGenerator C) ^ 4 *
            sexticSymbol n (primaryGenerator d)) by ring]
    rw [norm_mul, norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _)) (norm_nonneg _)
  · simp only [norm_zero]
    positivity

/-- The bound is uniform in the element row variable. Its dependence on
the fixed test is harmless for proving convergence of the first form. -/
theorem firstColumn_uniform_bound (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) {I : SupportInterval} {U : ℝ → ℂ}
    (hU : SmoothSupported I U) {ell : ℝ} (hell : 0 < ell) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : O, ‖firstColumn c ξ C d t U ell y‖ ≤ B := by
  choose b hb0 hb using firstTransferCoefficient_uniform_bound c ξ C d t
  refine ⟨∑ n ∈ firstTransferIdealWindow I ell, b n * ‖U (normIdeal n / ell)‖,
    Finset.sum_nonneg (fun n _ => mul_nonneg (hb0 n) (norm_nonneg _)), ?_⟩
  intro y
  rw [firstColumn_eq_sum_window c ξ C d t hU hell y]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb n y) (norm_nonneg _)

/-- Genuine summability of the noncompact Schwartz-weighted element row. -/
theorem firstForm_row_summable (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (C d t : Ideal O) {I : SupportInterval} {U : ℝ → ℂ}
    (hU : SmoothSupported I U) {ell T : ℝ} (hell : 0 < ell) (hT : 0 < T) :
    Summable (fun y : O => Φ.value (normElement y / T) *
      ‖firstColumn c ξ C d t U ell y‖ ^ 2) := by
  obtain ⟨B, hB, hbound⟩ := firstColumn_uniform_bound c ξ C d t hU hell
  apply ((rowWeight_element_summable Φ hT).mul_right (B ^ 2)).of_nonneg_of_le
  · intro y
    exact mul_nonneg (Φ.nonnegative _ (by dsimp [normElement, normIdeal]; positivity))
      (sq_nonneg _)
  · intro y
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbound y) 2)
      (Φ.nonnegative _ (by dsimp [normElement, normIdeal]; positivity))

/-- The row scale appearing literally in `firstForm` is positive on every
admissible divisor fiber. Hence its element sum is genuinely convergent. -/
theorem firstForm_actual_row_summable (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (C d t : Ideal O) {I : SupportInterval} {U : ℝ → ℂ}
    (hU : SmoothSupported I U) (hC : C ≠ ⊥) (ht : t ≠ ⊥) (hd : d ∣ C)
    {cI H L F Sigma : ℝ} (hcI : 0 < cI) (hH : 0 < H) (hL : 0 < L)
    (hF : 0 < F) (hSigma : 0 < Sigma) :
    Summable (fun y : O => Φ.value (normElement y /
      (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))) *
      ‖firstColumn c ξ C d t U (L / (normIdeal C * normIdeal t)) y‖ ^ 2) := by
  apply firstForm_row_summable c ξ Φ C d t hU
  · exact div_pos hL (mul_pos (normIdeal_pos hC) (normIdeal_pos ht))
  · exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos hcI hSigma) hL) hF)
      (normIdeal_pos (ne_zero_of_dvd_ne_zero hC hd)))
      (mul_pos hH (pow_pos (normIdeal_pos hC) 2))

theorem first_transfer_divisor_summable (C : Ideal O) (hC : C ≠ ⊥)
    (v : Ideal O → ℝ) : Summable (fun d : Ideal O => if d ∣ C then v d else 0) := by
  apply summable_of_hasFiniteSupport
  apply (first_transfer_divisors_finite hC).subset
  intro d hd
  by_contra hnot
  exact hd (if_neg hnot)

/-- Summability of the two outer layers is established from their finite
ranges; this does not substitute for the separate Schwartz row proof above. -/
theorem firstForm_middle_summable (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (U : ℝ → ℂ)
    (cI H L F Sigma : ℝ) (C : Ideal O) :
    Summable (fun t : Ideal O =>
      if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L then
        ∑' d : Ideal O, if d ∣ C then
          (H * normIdeal C / (normIdeal d * L ^ 2 * F)) *
          ∑' y : O, Φ.value (normElement y /
            (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))) *
            ‖firstColumn c ξ C d t U (L / (normIdeal C * normIdeal t)) y‖ ^ 2
        else 0
      else 0) :=
  summable_of_hasFiniteSupport (first_transfer_middle_hasFiniteSupport c _ C _)

theorem firstForm_outer_summable (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (U : ℝ → ℂ)
    (cI H L F Sigma : ℝ) :
    Summable (fun C : Ideal O => ∑' t : Ideal O,
      if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L then
        ∑' d : Ideal O, if d ∣ C then
          (H * normIdeal C / (normIdeal d * L ^ 2 * F)) *
          ∑' y : O, Φ.value (normElement y /
            (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))) *
            ‖firstColumn c ξ C d t U (L / (normIdeal C * normIdeal t)) y‖ ^ 2
        else 0
      else 0) :=
  summable_of_hasFiniteSupport (first_transfer_outer_hasFiniteSupport c _ _)

end QRHShort
