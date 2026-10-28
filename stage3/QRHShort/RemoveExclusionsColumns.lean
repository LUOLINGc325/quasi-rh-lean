import QRHShort.RemoveExclusionsAssembly

/-!
Split the remaining column identity into a finite Möbius indicator identity and
one divisor's change of variables. Compact support justifies the interchange;
neither child is an axiom or an admitted theorem.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.RemoveExclusionsProof

def columnTerm (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (X : ℝ) (k : O) (f n : Ideal O) : ℂ :=
  coefficient ξ.val n * sexticSymbol n k *
    sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / X)

def divisibleColumnSum (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (d : Ideal O) (X : ℝ) (k : O) (f : Ideal O) : ℂ :=
  ∑' n : Ideal O, if SquarefreeOutside c.S n ∧ d ∣ n then columnTerm c ξ W X k f n else 0

/-- Finite inclusion-exclusion over the divisors of the radical outside `S`. -/
def MobiusIndicatorStatement : Prop :=
  ∀ (c : ArithmeticContext) (r n : Ideal O), r ≠ ⊥ → SquarefreeOutside c.S n →
    (∑ d ∈ radicalDivisors c.S r, if d ∣ n then (mobius d : ℂ) else 0) =
      if IsRelPrime n r then 1 else 0

/-- The `n = d m` change of variables, coefficient multiplicativity, and the
zero extension of sextic symbols, for one squarefree ideal outside `S`. -/
def DivisibleColumnStatement : Prop :=
  ∀ (c : ArithmeticContext), ArithmeticRelations c →
  ∀ (I : SupportInterval) (ξ : RayCharacter c) (W : ℝ → ℂ)
      (d : Ideal O) (X : ℝ) (k : O) (f : Ideal O),
    SmoothSupported I W → 0 < X → SquarefreeOutside c.S d → SquarefreeOutside c.S f →
    divisibleColumnSum c ξ W d X k f =
      if SquarefreeOutside c.S (d * f) then
        (coefficient ξ.val d * sexticSymbol d k * sexticSymbol d (primaryGenerator f) ^ 4) *
          columnSum c ξ W (X / normIdeal d) k (d * f)
      else 0

def boundedIdeals (I : SupportInterval) (X : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le (I.hi * X)).toFinset

theorem column_tsum_eq_finite (c : ArithmeticContext) (I : SupportInterval)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (X : ℝ) (k : O) (f : Ideal O)
    (P : Ideal O → Prop) [DecidablePred P] (hW : SmoothSupported I W) (hX : 0 < X) :
    (∑' n : Ideal O, if P n then columnTerm c ξ W X k f n else 0) =
      ∑ n ∈ boundedIdeals I X, if P n then columnTerm c ξ W X k f n else 0 := by
  apply tsum_eq_sum
  intro n hn
  by_cases hP : P n
  · rw [if_pos hP]
    have hzero : W (normIdeal n / X) = 0 := by
      by_contra hne
      have hle : normIdeal n ≤ I.hi * X := (div_le_iff₀ hX).mp (hW.2 hne).2
      exact hn (by simpa only [boundedIdeals, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq] using hle)
    simp only [columnTerm, hzero, mul_zero]
  · exact if_neg hP

/-- The finite Möbius identity can be moved through the column sum because
the weight restricts every participating series to the same finite ideal set. -/
theorem mobius_column_expansion (hmob : MobiusIndicatorStatement)
    (c : ArithmeticContext) (I : SupportInterval) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (r : Ideal O) (X : ℝ) (k : O) (f : Ideal O)
    (hr : r ≠ ⊥) (hW : SmoothSupported I W) (hX : 0 < X) :
    excludedColumnSum c ξ W r X k f =
      ∑ d ∈ radicalDivisors c.S r, (mobius d : ℂ) * divisibleColumnSum c ξ W d X k f := by
  calc
    _ = ∑ n ∈ boundedIdeals I X,
        if SquarefreeOutside c.S n ∧ IsRelPrime n r then
          columnTerm c ξ W X k f n else 0 :=
      column_tsum_eq_finite c I ξ W X k f
        (fun n => SquarefreeOutside c.S n ∧ IsRelPrime n r) hW hX
    _ = ∑ n ∈ boundedIdeals I X, ∑ d ∈ radicalDivisors c.S r,
        (mobius d : ℂ) *
          (if SquarefreeOutside c.S n ∧ d ∣ n then columnTerm c ξ W X k f n else 0) := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : SquarefreeOutside c.S n
      · calc
          _ = (if IsRelPrime n r then (1 : ℂ) else 0) * columnTerm c ξ W X k f n := by
            by_cases hnr : IsRelPrime n r <;> simp [hn, hnr]
          _ = (∑ d ∈ radicalDivisors c.S r, if d ∣ n then (mobius d : ℂ) else 0) *
              columnTerm c ξ W X k f n := by rw [hmob c r n hr hn]
          _ = _ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro d _
            by_cases hd : d ∣ n <;> simp [hn, hd]
      · simp [hn]
    _ = ∑ d ∈ radicalDivisors c.S r, (mobius d : ℂ) *
        ∑ n ∈ boundedIdeals I X,
          if SquarefreeOutside c.S n ∧ d ∣ n then columnTerm c ξ W X k f n else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      exact congrArg (fun z : ℂ => (mobius d : ℂ) * z)
        (column_tsum_eq_finite c I ξ W X k f
          (fun n => SquarefreeOutside c.S n ∧ d ∣ n) hW hX).symm

theorem column_expansion_of_components (hmob : MobiusIndicatorStatement)
    (hdiv : DivisibleColumnStatement) : ColumnExpansionStatement := by
  intro c hc I ξ W r X k f hr hW hX hf
  rw [mobius_column_expansion hmob c I ξ W r X k f hr hW hX]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hdiv c hc I ξ W d X k f hW hX (radicalDivisor_squarefreeOutside c hd) hf]
  split_ifs <;> simp only [exclusionMultiplier, mul_zero, mul_assoc]

/-- The original energy statement follows from the two strictly smaller,
explicit arithmetic children. -/
theorem remove_exclusions_step_of_arithmetic (ha : ArithmeticStatement)
    (hmob : MobiusIndicatorStatement) (hdiv : DivisibleColumnStatement) :
    RemoveExclusionsStatement :=
  remove_exclusions_step_of_column_expansion ha (column_expansion_of_components hmob hdiv)

end QRHShort.RemoveExclusionsProof
