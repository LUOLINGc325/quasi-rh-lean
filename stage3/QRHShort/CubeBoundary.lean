import QRHShort.IdealCounting
import QRHShort.ArithmeticBasics
import QRHShort.InitialEnergyBridge
import Mathlib.Data.Finset.Prod

/-! The small-column-scale boundary term in cube reduction. The constants are
uniform in the ray character, the row and ideal indices, and the smooth weight.
Only finitely many column ideals occur when the column scale is at most one. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- Counting nonzero elements costs only the finite unit group compared with
counting nonzero ideals. -/
theorem exists_element_norm_count_constant :
    ∃ A : ℝ, 0 < A ∧ ∀ H : ℝ, 0 < H →
      (((finite_normElement_le H).toFinset.filter
        (fun k => 0 < normElement k)).card : ℝ) ≤ A * H := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  let U : Finset Oˣ := finite_units.toFinset
  refine ⟨((U.card : ℝ) + 1) * C, mul_pos (by positivity) hC, ?_⟩
  intro H hH
  let S := (finite_normElement_le H).toFinset.filter (fun k => 0 < normElement k)
  let P := (boundedDivisibleIdeals 1 H) ×ˢ U
  have hsub : S ⊆ P.image (fun p => idealGenerator p.1 * (p.2 : O)) := by
    intro k hk
    obtain ⟨hkH, hkpos⟩ := Finset.mem_filter.mp hk
    have hkH' : normElement k ≤ H := (finite_normElement_le H).mem_toFinset.mp hkH
    have hk0 : principal k ≠ ⊥ := by
      intro he
      have hz : normElement k = 0 := by simp [normElement, normIdeal, he]
      exact (ne_of_gt hkpos) hz
    have hg : principal (idealGenerator (principal k)) = principal k :=
      Ideal.span_singleton_generator (principal k)
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hg
    apply Finset.mem_image.mpr
    refine ⟨(principal k, u), ?_, hu⟩
    apply Finset.mem_product.mpr
    exact ⟨mem_boundedDivisibleIdeals.mpr ⟨hkH', one_dvd _, hk0⟩,
      finite_units.mem_toFinset.mpr (Set.mem_univ u)⟩
  have hcard : S.card ≤ (boundedDivisibleIdeals 1 H).card * U.card := by
    calc
      S.card ≤ (P.image (fun p => idealGenerator p.1 * (p.2 : O))).card :=
        Finset.card_le_card hsub
      _ ≤ P.card := Finset.card_image_le
      _ = _ := Finset.card_product _ _
  have hcard' : (S.card : ℝ) ≤
      ((boundedDivisibleIdeals 1 H).card : ℝ) * (U.card : ℝ) := by
    exact_mod_cast hcard
  change (S.card : ℝ) ≤ _
  calc
    (S.card : ℝ) ≤ ((boundedDivisibleIdeals 1 H).card : ℝ) * (U.card : ℝ) := hcard'
    _ ≤ C * H * (U.card : ℝ) :=
      mul_le_mul_of_nonneg_right (hcount H hH) (Nat.cast_nonneg _)
    _ ≤ ((U.card : ℝ) + 1) * C * H := by nlinarith [mul_pos hC hH]

private def symbolBound (n : Ideal O) : ℝ :=
  6 ^ (UniqueFactorizationMonoid.normalizedFactors n).card

private theorem symbolBound_nonneg (n : Ideal O) : 0 ≤ symbolBound n := by
  unfold symbolBound
  positivity

private theorem norm_sexticAtPrime_le_six (P : Ideal O) (k : O) :
    ‖sexticAtPrime P k‖ ≤ 6 := by
  let z : ℕ → ℂ := fun j =>
    if Ideal.Quotient.mk P k ^ ((P.absNorm - 1) / 6) =
        Ideal.Quotient.mk P (rootSix ^ j)
    then embedding (rootSix ^ j) else 0
  change ‖∑ j ∈ Finset.range 6, z j‖ ≤ 6
  calc
    ‖∑ j ∈ Finset.range 6, z j‖ ≤
        ∑ j ∈ Finset.range 6, ‖z j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range 6, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      dsimp only [z]
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
  · simpa only [sexticSymbol, if_neg hn, symbolBound] using
      (hprod (UniqueFactorizationMonoid.normalizedFactors n))

private theorem norm_coefficient_le_fixed (ξ : HeckeCharacter) (n : Ideal O) :
    ‖coefficient ξ n‖ ≤ ‖alpha n‖ * ‖gauss 2 n‖ := by
  simp only [coefficient, norm_mul, norm_star]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (ξ.norm_onElement_le_one (primaryGenerator n))

/-- At scales at most one, only a fixed finite set of column ideals can occur. -/
theorem exists_column_small_scale_bound (I : SupportInterval) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ArithmeticContext) (ξ : RayCharacter c)
      (W : ℝ → ℂ) (J : ℕ) (L : ℝ) (k : O) (f : Ideal O),
      SmoothSupported I W → 0 < L → L ≤ 1 →
      ‖columnSum c ξ W L k f‖ ≤ B * weightNorm J W := by
  let S := (finite_normIdeal_le I.hi).toFinset
  let b (n : Ideal O) : ℝ :=
    ‖alpha n‖ * ‖gauss 2 n‖ * symbolBound n * symbolBound n ^ (4 : ℕ)
  have hb (n : Ideal O) : 0 ≤ b n := by
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (symbolBound_nonneg n))
      (pow_nonneg (symbolBound_nonneg n) _)
  refine ⟨∑ n ∈ S, b n, Finset.sum_nonneg (fun n _ => hb n), ?_⟩
  intro c ξ W J L k f hW hL hL1
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
      apply (finite_normIdeal_le I.hi).mem_toFinset.mpr
      exact hupper.trans (mul_le_of_le_one_right
        (I.lo_pos.trans_le I.ordered).le hL1)
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

private theorem rowEnergy_le_card_mul (column : O → ℂ) (H B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ k, ‖column k‖ ≤ B) :
    rowEnergy column H ≤ (((finite_normElement_le H).toFinset.filter
      (fun k => 0 < normElement k)).card : ℝ) * B ^ (2 : ℕ) := by
  let S := (finite_normElement_le H).toFinset.filter (fun k => 0 < normElement k)
  have heq : rowEnergy column H = ∑ k ∈ S, ‖column k‖ ^ (2 : ℕ) := by
    unfold rowEnergy
    have hts : (∑' k : O, if 0 < normElement k ∧ normElement k ≤ H then
        ‖column k‖ ^ (2 : ℕ) else 0) =
        ∑ k ∈ S, if 0 < normElement k ∧ normElement k ≤ H then
          ‖column k‖ ^ (2 : ℕ) else 0 := by
      apply tsum_eq_sum
      intro k hk
      have hnot : ¬ (0 < normElement k ∧ normElement k ≤ H) := by
        intro hk'
        exact hk (Finset.mem_filter.mpr
          ⟨(finite_normElement_le H).mem_toFinset.mpr hk'.2, hk'.1⟩)
      exact if_neg hnot
    rw [hts]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hkH, hkpos⟩ := Finset.mem_filter.mp hk
    exact if_pos ⟨hkpos, (finite_normElement_le H).mem_toFinset.mp hkH⟩
  rw [heq]
  calc
    (∑ k ∈ S, ‖column k‖ ^ (2 : ℕ)) ≤ ∑ _k ∈ S, B ^ (2 : ℕ) :=
      Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hbound k) 2)
    _ = (S.card : ℝ) * B ^ (2 : ℕ) := by simp

/-- The actual energy at a small column scale has the manuscript's `H / L` bound. -/
theorem exists_energy_small_scale_bound (I : SupportInterval) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ArithmeticContext) (ξ : RayCharacter c)
      (W : ℝ → ℂ) (J : ℕ) (H L F : ℝ), SmoothSupported I W →
      0 < H → 0 < L → L ≤ 1 → 0 < F →
      energy c ξ W H L F ≤ K * (H / L) * weightNorm J W ^ (2 : ℕ) := by
  obtain ⟨A, hA, hrows⟩ := exists_element_norm_count_constant
  obtain ⟨C, hC, hideals⟩ := exists_ideal_norm_count_constant
  obtain ⟨B, hB, hcolumns⟩ := exists_column_small_scale_bound I
  refine ⟨2 * C * A * B ^ (2 : ℕ), by positivity, ?_⟩
  intro c ξ W J H L F hW hH hL hL1 hF
  let N := weightNorm J W
  have hN : 0 ≤ N := weightNorm_nonneg hW J
  let V := A * H * (B * N) ^ (2 : ℕ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hrow (f : Ideal O) : rowEnergy (fun k => columnSum c ξ W L k f) H ≤ V := by
    calc
      rowEnergy (fun k => columnSum c ξ W L k f) H ≤
          (((finite_normElement_le H).toFinset.filter (fun k => 0 < normElement k)).card : ℝ) *
            (B * N) ^ (2 : ℕ) :=
        rowEnergy_le_card_mul _ H (B * N) (mul_nonneg hB hN)
          (fun k => hcolumns c ξ W J L k f hW hL hL1)
      _ ≤ V := mul_le_mul_of_nonneg_right (hrows H hH) (sq_nonneg _)
  let S := boundedDivisibleIdeals 1 (2 * F)
  have heq : (∑' f : Ideal O,
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => columnSum c ξ W L k f) H else 0) =
      ∑ f ∈ S, if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => columnSum c ξ W L k f) H else 0 := by
    apply tsum_eq_sum
    intro f hf
    have hnot : ¬ (SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F) := by
      intro hs
      exact hf (mem_boundedDivisibleIdeals.mpr ⟨hs.2.2.le, one_dvd _, hs.1.1.1⟩)
    exact if_neg hnot
  have houter : (∑' f : Ideal O,
      if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        rowEnergy (fun k => columnSum c ξ W L k f) H else 0) ≤ C * (2 * F) * V := by
    rw [heq]
    calc
      (∑ f ∈ S, if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
          rowEnergy (fun k => columnSum c ξ W L k f) H else 0) ≤ ∑ _f ∈ S, V := by
        apply Finset.sum_le_sum
        intro f hf
        split_ifs
        · exact hrow f
        · exact hV
      _ = (S.card : ℝ) * V := by simp
      _ ≤ C * (2 * F) * V :=
        mul_le_mul_of_nonneg_right (hideals (2 * F) (by positivity)) hV
  unfold energy
  calc
    (L * F)⁻¹ * _ ≤ (L * F)⁻¹ * (C * (2 * F) * V) :=
      mul_le_mul_of_nonneg_left houter (inv_nonneg.mpr (mul_nonneg hL.le hF.le))
    _ = (2 * C * A * B ^ (2 : ℕ)) * (H / L) * weightNorm J W ^ (2 : ℕ) := by
      dsimp [V, N]
      field_simp [ne_of_gt hL, ne_of_gt hF]
      <;> ring

/-- If the row height is at most `Sigma`, small column scales contribute only
the base term of cube reduction. Below the support threshold the energy is zero. -/
theorem exists_energy_small_scale_base_bound (I : SupportInterval) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ArithmeticContext) (ξ : RayCharacter c)
      (W : ℝ → ℂ) (J : ℕ) (H L F Sigma : ℝ), SmoothSupported I W →
      0 < H → 0 < L → L ≤ 1 → 0 < F → H ≤ Sigma →
      energy c ξ W H L F ≤ K * Sigma * weightNorm J W ^ (2 : ℕ) := by
  obtain ⟨K, hK, hbound⟩ := exists_energy_small_scale_bound I
  have hI : 0 < I.hi := I.lo_pos.trans_le I.ordered
  refine ⟨K * I.hi, mul_nonneg hK hI.le, ?_⟩
  intro c ξ W J H L F Sigma hW hH hL hL1 hF hSigma
  by_cases hzero : I.hi * L < 1
  · rw [energy_eq_zero_of_support_scale_lt_one hW c ξ H F hL hzero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK hI.le)
      (hH.le.trans hSigma)) (sq_nonneg _)
  · have hinv : 1 / L ≤ I.hi := (div_le_iff₀ hL).mpr (by nlinarith)
    have hHL : H / L ≤ Sigma * I.hi := by
      calc
        H / L = H * (1 / L) := by ring
        _ ≤ H * I.hi := mul_le_mul_of_nonneg_left hinv hH.le
        _ ≤ Sigma * I.hi := mul_le_mul_of_nonneg_right hSigma hI.le
    calc
      energy c ξ W H L F ≤ K * (H / L) * weightNorm J W ^ (2 : ℕ) :=
        hbound c ξ W J H L F hW hH hL hL1 hF
      _ ≤ K * (Sigma * I.hi) * weightNorm J W ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHL hK) (sq_nonneg _)
      _ = (K * I.hi) * Sigma * weightNorm J W ^ (2 : ℕ) := by ring

end QRHShort
