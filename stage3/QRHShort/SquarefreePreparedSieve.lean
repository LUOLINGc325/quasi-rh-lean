import QRHShort.SquarefreePreparedStatements
import QRHShort.SquarefreePreparedCounting

/-! The frozen quadratic estimate applied to arbitrary finite column masks.
Both infinite sums are converted using their actual finite support. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

theorem prepared_quadratic_finite_bound (hq : QuadraticEstimate)
    (S : Finset (Ideal O)) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (H U : ℝ) (columns : Finset (Ideal O))
      (β : Ideal O → ℂ), 1 ≤ H → 1 ≤ U →
      (∀ n ∈ columns, n ≠ ⊥ ∧ Squarefree n ∧
        IsRelPrime n (principal 3) ∧ U ≤ normIdeal n ∧ normIdeal n ≤ 2 * U) →
      (∑ k ∈ sieveRows S H,
        ‖∑ n ∈ columns, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2) ≤
          K * (H * U) ^ σ * (H + U) * ∑ n ∈ columns, ‖β n‖ ^ 2 := by
  obtain ⟨K, hK, hq⟩ := hq S σ 1 2 hσ zero_lt_one (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro H U columns β hH hU hcolumns
  let β' : Ideal O → ℂ := fun n => if n ∈ columns then β n else 0
  have hsupp : Function.support β' ⊆ {n | n ≠ ⊥ ∧ Squarefree n ∧
      IsRelPrime n (principal 3) ∧ 1 * U ≤ normIdeal n ∧ normIdeal n ≤ 2 * U} := by
    intro n hn
    have hncol : n ∈ columns := by
      by_contra hncol
      exact hn (by simp [β', hncol])
    simpa only [Set.mem_setOf_eq, one_mul] using hcolumns n hncol
  have hinner (k : Ideal O) :
      (∑' n : Ideal O, β' n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)) =
        ∑ n ∈ columns, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ) := by
    rw [tsum_eq_sum (s := columns) (fun n hn => by simp [β', hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [β', hn])
  have hnorm : (∑' n : Ideal O, ‖β' n‖ ^ 2) = ∑ n ∈ columns, ‖β n‖ ^ 2 := by
    rw [tsum_eq_sum (s := columns) (fun n hn => by simp [β', hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [β', hn])
  have houter :
      (∑' k : Ideal O, if SquarefreeOutside S k ∧ IsRelPrime k (principal 6) ∧
          normIdeal k ≤ H then
        ‖∑' n : Ideal O, β' n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2
        else 0) =
      ∑ k ∈ sieveRows S H,
        ‖∑' n : Ideal O, β' n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2 := by
    rw [tsum_eq_sum (s := sieveRows S H) (fun k hk =>
      if_neg (fun hk' => hk ((mem_sieveRows S H k).mpr hk')))]
    apply Finset.sum_congr rfl
    intro k hk
    exact if_pos ((mem_sieveRows S H k).mp hk)
  have hbound := hq H U β' hH hU hsupp
  rw [houter, hnorm] at hbound
  simpa only [hinner] using hbound

theorem prepared_quadratic_column_bound (hq : QuadraticEstimate)
    (S : Finset (Ideal O)) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (H U a : ℝ) (columns : Finset (Ideal O))
      (β : Ideal O → ℂ), 1 ≤ H → 1 ≤ U → 0 ≤ a →
      (∀ n ∈ columns, n ≠ ⊥ ∧ Squarefree n ∧
        IsRelPrime n (principal 3) ∧ U ≤ normIdeal n ∧ normIdeal n ≤ 2 * U) →
      (∀ n ∈ columns, ‖β n‖ ≤ a / Real.sqrt (normIdeal n)) →
      (∑ k ∈ sieveRows S H,
        ‖∑ n ∈ columns, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2) ≤
          K * a ^ 2 * (H * U) ^ σ * (H + U) := by
  obtain ⟨K, hK, hq⟩ := prepared_quadratic_finite_bound hq S hσ
  obtain ⟨B, hB, hinv⟩ := prepared_inverse_norm_bound
  refine ⟨K * B, mul_nonneg hK hB.le, ?_⟩
  intro H U a columns β hH hU ha hcolumns hβ
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hinv' := hinv U columns hUpos (fun n hn =>
    ⟨(hcolumns n hn).1, (hcolumns n hn).2.2.2⟩)
  have hnorm : (∑ n ∈ columns, ‖β n‖ ^ 2) ≤ a ^ 2 * B := by
    calc
      _ ≤ ∑ n ∈ columns, a ^ 2 * (normIdeal n)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos : 0 < normIdeal n := hUpos.trans_le (hcolumns n hn).2.2.2.1
        calc
          _ ≤ (a / Real.sqrt (normIdeal n)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hβ n hn) 2
          _ = a ^ 2 * (normIdeal n)⁻¹ := by
            rw [div_pow, Real.sq_sqrt hnpos.le, div_eq_mul_inv]
      _ = a ^ 2 * ∑ n ∈ columns, (normIdeal n)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ a ^ 2 * B := mul_le_mul_of_nonneg_left hinv' (sq_nonneg _)
  calc
    _ ≤ K * (H * U) ^ σ * (H + U) * ∑ n ∈ columns, ‖β n‖ ^ 2 :=
      hq H U columns β hH hU hcolumns
    _ ≤ K * (H * U) ^ σ * (H + U) * (a ^ 2 * B) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.prepared_quadratic_finite_bound
#print axioms QRHShort.SquarefreeAssembly.prepared_quadratic_column_bound
