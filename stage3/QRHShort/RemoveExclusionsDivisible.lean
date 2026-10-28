import QRHShort.RemoveExclusionsColumns
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! A single divisor's change of variables in the removal of exclusions. -/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.RemoveExclusionsProof
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites

theorem column_sexticSymbol_mul (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, sexticSymbol]
  by_cases hb : b = ⊥
  · simp [hb, sexticSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, if_neg ha, if_neg hb, if_neg hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

/-- Zero extension at a prime common to the denominator and the numerator ideal. -/
theorem column_symbol_zero (c : ArithmeticContext) {n a : Ideal O}
    (hn : Outside c.S n) (ha : Outside c.S a) (hrel : ¬ IsRelPrime n a) :
    sexticSymbol n (primaryGenerator a) = 0 := by
  by_contra hne
  apply hrel
  apply (isRelPrime_iff_no_prime_factors hn.1).mpr
  intro P hPn hPa hP
  have hmem : P ∈ normalizedFactors n :=
    (mem_normalizedFactors_iff hn.1).mpr ⟨hP, hPn⟩
  have hgen : primaryGenerator a ∈ P := by
    apply Ideal.dvd_span_singleton.mp
    change P ∣ principal (primaryGenerator a)
    rw [(primaryGenerator_spec_outside c ha).1]
    exact hPa
  have hz : sexticAtPrime P (primaryGenerator a) = 0 :=
    sexticAtPrime_zero_of_mem hP
      (outside_quotient_rootSix_isPrimitiveRoot c hP
        (outside_of_mem_normalizedFactors hn hmem)) hgen
  apply hne
  rw [sexticSymbol, if_neg hn.1]
  exact Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map.mpr ⟨P, hmem, hz⟩)

theorem column_squarefree_mul_iff (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) :
    SquarefreeOutside c.S (a * b) ↔ IsRelPrime a b := by
  exact ⟨fun h => (squarefree_mul_iff.mp h.2).1,
    fun h => ⟨ArithmeticProof.outside_mul c ha.1 hb.1,
      squarefree_mul_iff.mpr ⟨h, ha.2, hb.2⟩⟩⟩

/-- Injective ideal multiplication reindexes precisely the terms divisible by `d`. -/
theorem divisibleColumn_reindex (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (d : Ideal O) (X : ℝ) (k : O) (f : Ideal O) (hd : d ≠ ⊥) :
    divisibleColumnSum c ξ W d X k f =
      ∑' m : Ideal O, if SquarefreeOutside c.S (d * m) then
        columnTerm c ξ W X k f (d * m) else 0 := by
  have hinj : Function.Injective (fun m : Ideal O => d * m) := mul_right_injective₀ hd
  have heq := hinj.tsum_eq
    (f := fun n : Ideal O =>
      if SquarefreeOutside c.S n ∧ d ∣ n then columnTerm c ξ W X k f n else 0)
    (by
      intro n hn
      have hdn : d ∣ n := by
        by_contra h
        exact hn (if_neg (fun h' => h h'.2))
      obtain ⟨m, hm⟩ := hdn
      exact ⟨m, hm.symm⟩)
  unfold divisibleColumnSum
  rw [← heq]
  apply tsum_congr
  intro m
  simp only [dvd_mul_right, and_true]

/-- The coefficient formula and the two multiplicativities of the sextic symbol.
When `d m` is not squarefree, the extra numerator factor kills the right side. -/
theorem columnTerm_change_variables (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (d m : Ideal O) (X : ℝ) (k : O) (f : Ideal O)
    (hd : SquarefreeOutside c.S d) (hf : SquarefreeOutside c.S f) :
    (if SquarefreeOutside c.S (d * m) then columnTerm c ξ W X k f (d * m) else 0) =
      (coefficient ξ.val d * sexticSymbol d k * sexticSymbol d (primaryGenerator f) ^ 4) *
        (if SquarefreeOutside c.S m then
          columnTerm c ξ W (X / normIdeal d) k (d * f) m else 0) := by
  by_cases hdm : SquarefreeOutside c.S (d * m)
  · have hm : SquarefreeOutside c.S m :=
      squarefreeOutside_of_mul_left (by rw [mul_comm]; exact hdm)
    have hrel := (column_squarefree_mul_iff c hd hm).mp hdm
    obtain ⟨G, R, hG, hR, hs, hl, hr, hcoc, hrec, hg, hcoeff, hshift⟩ := hc
    rw [if_pos hdm, if_pos hm]
    have hscale : normIdeal (d * m) / X = normIdeal m / (X / normIdeal d) := by
      rw [normIdeal_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    simp only [columnTerm, hcoeff ξ d m hd hm hrel,
      column_sexticSymbol_mul, ArithmeticProof.primaryGenerator_mul c hd.1 hf.1,
      sexticSymbol_mul_numerator c hm.1, hscale, mul_pow]
    ring
  · rw [if_neg hdm]
    by_cases hm : SquarefreeOutside c.S m
    · rw [if_pos hm]
      have hrel : ¬ IsRelPrime m d := by
        intro h
        exact hdm ((column_squarefree_mul_iff c hd hm).mpr h.symm)
      have hz := column_symbol_zero c hm.1 hd.1 hrel
      simp only [columnTerm, ArithmeticProof.primaryGenerator_mul c hd.1 hf.1,
        sexticSymbol_mul_numerator c hm.1, hz, zero_mul, zero_pow (by decide : 4 ≠ 0),
        mul_zero]
    · rw [if_neg hm, mul_zero]

/-- Exact single-divisor identity, before discarding the zero multiplier. -/
theorem divisibleColumn_identity (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (d : Ideal O) (X : ℝ) (k : O) (f : Ideal O)
    (hd : SquarefreeOutside c.S d) (hf : SquarefreeOutside c.S f) :
    divisibleColumnSum c ξ W d X k f =
      (coefficient ξ.val d * sexticSymbol d k * sexticSymbol d (primaryGenerator f) ^ 4) *
        columnSum c ξ W (X / normIdeal d) k (d * f) := by
  rw [divisibleColumn_reindex c ξ W d X k f hd.1.1]
  calc
    _ = ∑' m : Ideal O,
        (coefficient ξ.val d * sexticSymbol d k * sexticSymbol d (primaryGenerator f) ^ 4) *
          (if SquarefreeOutside c.S m then
            columnTerm c ξ W (X / normIdeal d) k (d * f) m else 0) :=
      tsum_congr (fun m => columnTerm_change_variables c hc ξ W d m X k f hd hf)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The frozen statement, using only its explicit arithmetic-relation premise. -/
theorem divisibleColumn : DivisibleColumnStatement := by
  intro c hc I ξ W d X k f _hW _hX hd hf
  rw [divisibleColumn_identity c hc ξ W d X k f hd hf]
  by_cases hdf : SquarefreeOutside c.S (d * f)
  · exact (if_pos hdf).symm
  · rw [if_neg hdf]
    have hrel : ¬ IsRelPrime d f :=
      fun h => hdf ((column_squarefree_mul_iff c hd hf).mpr h)
    rw [column_symbol_zero c hd.1 hf.1 hrel]
    simp

end QRHShort.RemoveExclusionsProof
