import QRHShort.FirstTransferPoissonTruncation
import QRHShort.FirstTransferPoissonEnergyExpansion
import QRHShort.FirstTransferPairedCharacterPrimitivity
import QRHShort.FirstTransferSymbolIdentities

/-!
Poisson applied to the literal common-factor row. The common symbol supplies
the exclusion ideal, while the two residual symbols are the actual primitive
paired character. The Gauss factor remains that character's literal Gauss sum.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem first_transfer_outsideRadical_eq_self_of_squarefree {C : Ideal O}
    (hC : C ≠ ⊥) (hsq : Squarefree C) : outsideRadical ∅ C = C := by
  have hnodup := (squarefree_iff_nodup_normalizedFactors hC).mp hsq
  have hfilter : (primeFactors C).filter (fun P => P ∉ (∅ : Finset (Ideal O))) =
      primeFactors C := by simp
  unfold outsideRadical
  rw [hfilter]
  change ((normalizedFactors C).dedup.map (fun P => P)).prod = C
  rw [Multiset.map_id', Multiset.dedup_eq_self.mpr hnodup]
  exact Ideal.prod_normalizedFactors_eq_self hC

theorem first_transfer_poisson_divisors_eq_squarefree {C : Ideal O}
    (hC : C ≠ ⊥) (hsq : Squarefree C) :
    firstTransferPoissonDivisors C = (first_transfer_divisors_finite hC).toFinset := by
  ext d
  simp only [mem_firstTransferPoissonDivisors,
    first_transfer_outsideRadical_eq_self_of_squarefree hC hsq, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]

theorem first_transfer_poisson_divisor_generator (c : ArithmeticContext) {C d : Ideal O}
    (hC : Outside c.S C) (hd : d ∣ C) : chosenGenerator d = primaryGenerator d :=
  first_transfer_chosenGenerator_eq_primaryGenerator c (first_transfer_outside_of_dvd c hC hd)

theorem first_transfer_poisson_gcd_symbol_row (c : ArithmeticContext) {C a b : Ideal O}
    (hC : Outside c.S C) (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (k : O) :
    sexticSymbol (C * a) k * star (sexticSymbol (C * b) k) =
      if IsRelPrime (principal k) C then
        (firstTransferPrimitivePairedCharacter c ha hb hab).value k else 0 := by
  rw [first_transfer_sexticSymbol_mul, first_transfer_sexticSymbol_mul, star_mul]
  calc
    (sexticSymbol C k * sexticSymbol a k) * (star (sexticSymbol b k) * star (sexticSymbol C k)) =
        (sexticSymbol C k * star (sexticSymbol C k)) *
          (sexticSymbol a k * star (sexticSymbol b k)) := by ring
    _ = _ := by
      rw [first_transfer_sexticSymbol_mul_star c hC k,
        firstTransferPrimitivePairedCharacter_value]
      split_ifs <;> simp only [one_mul, zero_mul]

theorem first_transfer_poisson_gcd_row_eq (c : ArithmeticContext) {C a b : Ideal O}
    (hC : Outside c.S C) (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (Φ : RowWeight) (H : ℝ) :
    (∑' k : O, (Φ.value (normElement k / H) : ℂ) *
      sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) =
      ∑' k : O, if IsRelPrime (principal k) C then
        (firstTransferPrimitivePairedCharacter c ha hb hab).value k *
          (Φ.value (normElement k / H) : ℂ) else 0 := by
  apply tsum_congr
  intro k
  calc
    _ = (Φ.value (normElement k / H) : ℂ) *
        (sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) := by ring
    _ = _ := by
      rw [first_transfer_poisson_gcd_symbol_row c hC ha hb hab k]
      split_ifs
      · ring
      · simp only [mul_zero]

theorem first_transfer_poisson_gcd_row_summable (Φ : RowWeight) {H : ℝ} (hH : 0 < H)
    (C a b : Ideal O) : Summable (fun k : O =>
      (Φ.value (normElement k / H) : ℂ) *
        sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) :=
  first_transfer_poisson_character_row_summable Φ hH (C * a) (C * b)

theorem first_transfer_poisson_gcd_row_truncation (hp : PoissonStatement)
    (c : ArithmeticContext) {C a b : Ideal O} (hC : SquarefreeOutside c.S C)
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b)
    (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    let χ := firstTransferPrimitivePairedCharacter c ha hb hab
    (∑' k : O, (Φ.value (normElement k / H) : ℂ) *
      sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) =
      poissonZeroTerm χ C (fun x => (Φ.value x : ℂ)) H +
        H * χ.gauss / (Real.sqrt (normIdeal (a * b)) : ℂ) *
          ∑ d ∈ (first_transfer_divisors_finite hC.1.1).toFinset,
            ((mobius d : ℂ) * χ.value (primaryGenerator d) / (normIdeal d : ℂ)) *
              ∑ h ∈ (finite_normElement_le
                (Φ.fourierCap * normIdeal d * normIdeal (a * b) / H)).toFinset.erase 0,
                star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
                  (H * normElement h / (normIdeal d * normIdeal (a * b))) := by
  dsimp only
  rw [first_transfer_poisson_gcd_row_eq c hC.1 ha hb hab Φ H,
    first_transfer_poisson_truncation hp (firstTransferPrimitivePairedCharacter c ha hb hab)
      C Φ hC.1.1 hH,
    first_transfer_poisson_divisors_eq_squarefree hC.1.1 hC.2]
  congr 1
  unfold firstTransferPoissonDivisorCoefficient firstTransferPoissonFrequencies firstTransferPoissonDualTerm
  simp only [firstTransferPrimitivePairedCharacter_modulus]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdC : d ∣ C := (first_transfer_divisors_finite hC.1.1).mem_toFinset.mp hd
  rw [first_transfer_poisson_divisor_generator c hC.1 hdC]

end QRHShort
