import QRHShort.SixthPowerResidue
import QRHShort.MainStatements

/-!
Every finite Hecke character admits an arithmetic context. Thus the universal
context quantifier in the mean-square and pointwise statements is not vacuous.
The context here is sufficient for the original sums; the stronger reciprocity
relations and their enlarged ray modulus remain an independent obligation.
-/

noncomputable section
open Classical

namespace QRHShort

theorem principal_nat_ne_bot {n : ℕ} (hn : n ≠ 0) : principal (n : O) ≠ ⊥ := by
  intro h
  have hz : (n : O) = 0 := (Ideal.span_singleton_eq_bot).mp h
  exact hn (Nat.cast_eq_zero.mp hz)

/-- The finite set of primes above 2, 3, or the character modulus. -/
def HeckeCharacter.excludedPrimes (χ : HeckeCharacter) : Finset (Ideal O) :=
  (UniqueFactorizationMonoid.normalizedFactors (principal 2)).toFinset ∪
    (UniqueFactorizationMonoid.normalizedFactors (principal 3)).toFinset ∪
      (UniqueFactorizationMonoid.normalizedFactors χ.modulus).toFinset

theorem HeckeCharacter.mem_excludedPrimes (χ : HeckeCharacter) (P : Ideal O) :
    P ∈ χ.excludedPrimes ↔
      Prime P ∧ (P ∣ principal 2 ∨ P ∣ principal 3 ∨ P ∣ χ.modulus) := by
  have htwo : principal (2 : O) ≠ (0 : Ideal O) :=
    principal_nat_ne_bot (by decide : (2 : ℕ) ≠ 0)
  have hthree : principal (3 : O) ≠ (0 : Ideal O) :=
    principal_nat_ne_bot (by decide : (3 : ℕ) ≠ 0)
  simp only [HeckeCharacter.excludedPrimes, Finset.mem_union, Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff htwo,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff hthree,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff χ.modulus_ne_bot]
  tauto

/-- The original family needs no larger modulus than that of its fixed character. -/
def HeckeCharacter.context (χ : HeckeCharacter) : ArithmeticContext where
  nu := χ
  S := χ.excludedPrimes
  prime_S := fun P hP => (χ.mem_excludedPrimes P).mp hP |>.1
  above_two := fun P hP htwo => (χ.mem_excludedPrimes P).mpr ⟨hP, Or.inl htwo⟩
  above_three := fun P hP hthree =>
    (χ.mem_excludedPrimes P).mpr ⟨hP, Or.inr (Or.inl hthree)⟩
  conductor_S := fun P hP hmod =>
    (χ.mem_excludedPrimes P).mpr ⟨hP, Or.inr (Or.inr hmod)⟩
  rayModulus := χ.modulus
  rayModulus_ne_bot := χ.modulus_ne_bot
  ray_supported := fun P hP hmod =>
    (χ.mem_excludedPrimes P).mpr ⟨hP, Or.inr (Or.inr hmod)⟩
  nu_factors := le_rfl

theorem exists_context (χ : HeckeCharacter) :
    ∃ c : ArithmeticContext, c.nu = χ := ⟨χ.context, rfl⟩

/-- At the trivial row the actual sextic factor is one on every surviving ideal. -/
theorem originalSum_one_eq_mobius (c : ArithmeticContext) (W : ℝ → ℂ) (D : ℝ) :
    originalSum c W D 1 = ∑' n : Ideal O,
      if Outside c.S n then (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D)
      else 0 := by
  unfold originalSum
  apply tsum_congr
  intro n
  by_cases hn : Outside c.S n
  · simp only [if_pos hn, sexticSymbol_one_of_outside c hn, mul_one]
  · simp only [if_neg hn]

/-- The pointwise statement supplies the genuine smoothed Möbius sum for each
Hecke character, with the explicitly constructed finite excluded set. -/
theorem mobius_saving_of_pointwise (hp : PointwiseMobiusEstimate)
    (χ : HeckeCharacter) (I : SupportInterval) (W : ℝ → ℂ) (ε : ℝ)
    (hW : SmoothSupported I W) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℝ, 2 ≤ D →
      ‖∑' n : Ideal O, if Outside χ.excludedPrimes n then
        (mobius n : ℂ) * χ.onIdeal n * W (normIdeal n / D) else 0‖ ≤
          C * D ^ ((11 : ℝ) / 12 + ε) := by
  obtain ⟨C, hC, hbound⟩ := hp χ.context I W ε hW hε
  refine ⟨C, hC, ?_⟩
  intro D hD
  simpa only [originalSum_one_eq_mobius, HeckeCharacter.context] using hbound D hD

end QRHShort
