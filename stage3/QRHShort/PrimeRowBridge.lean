import QRHShort.FiniteSupport
import QRHShort.PrimeExtraction
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Finite row selection for the concrete mean square. The existence of primary
generators is an explicit input. The general selection lemma takes summability;
the concrete corollary obtains it from `FiniteSupport`. The prime-row comparison
estimate is separate.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem primaryGenerator_spec {a : Ideal O}
    (ha : ∃ z : O, principal z = a ∧ IsPrimary z) :
    principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) := by
  simp only [primaryGenerator, dif_pos ha]
  exact Classical.choose_spec ha

theorem principal_pow (z : O) (n : ℕ) : principal (z ^ n) = principal z ^ n := by
  exact (Ideal.span_singleton_pow z n).symm

theorem prime_ideal_eq_of_pow_eq {P Q : Ideal O} (hP : Prime P) (hQ : Prime Q)
    {n : ℕ} (hn : n ≠ 0) (heq : P ^ n = Q ^ n) : P = Q := by
  have hrad := congrArg Ideal.radical heq
  rw [Ideal.radical_pow P hn, Ideal.radical_pow Q hn,
    (Ideal.isPrime_of_prime hP).isRadical.radical,
    (Ideal.isPrime_of_prime hQ).isRadical.radical] at hrad
  exact hrad

theorem primaryGenerator_pow_injOn (P : Finset (Ideal O))
    (hprime : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, ∃ z : O, principal z = p ∧ IsPrimary z)
    {n : ℕ} (hn : n ≠ 0) :
    Set.InjOn (fun p : Ideal O => primaryGenerator p ^ n) (↑P : Set (Ideal O)) := by
  intro p hp q hq heq
  apply prime_ideal_eq_of_pow_eq (hprime p hp) (hprime q hq) hn
  have hideal := congrArg principal heq
  simpa only [principal_pow, (primaryGenerator_spec (hprimary p hp)).1,
    (primaryGenerator_spec (hprimary q hq)).1] using hideal

theorem normElement_primaryGenerator_pow {p : Ideal O}
    (hp : ∃ z : O, principal z = p ∧ IsPrimary z) (n : ℕ) :
    normElement (primaryGenerator p ^ n) = normIdeal p ^ n := by
  simp only [normElement, principal_pow, (primaryGenerator_spec hp).1, normIdeal,
    map_pow, Nat.cast_pow]

theorem finite_rows_le_originalMeanSquare {ι : Type*} (P : Finset ι) (row : ι → O)
    (hrow : Set.InjOn row (↑P : Set ι))
    (c : ArithmeticContext) (W : ℝ → ℂ) (D H : ℝ)
    (hsupport : ∀ p ∈ P, 0 < normElement (row p) ∧ normElement (row p) ≤ H)
    (hsum : Summable (fun u : O =>
      if 0 < normElement u ∧ normElement u ≤ H then ‖originalSum c W D u‖ ^ 2 else 0)) :
    (∑ p ∈ P, ‖originalSum c W D (row p)‖ ^ 2) ≤ originalMeanSquare c W D H := by
  let f : O → ℝ := fun u =>
    if 0 < normElement u ∧ normElement u ≤ H then ‖originalSum c W D u‖ ^ 2 else 0
  have hnonneg : ∀ u, 0 ≤ f u := by
    intro u
    dsimp only [f]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  calc
    (∑ p ∈ P, ‖originalSum c W D (row p)‖ ^ 2) = ∑ p ∈ P, f (row p) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [f, if_pos (hsupport p hp)]
    _ = ∑ u ∈ P.image row, f u := (Finset.sum_image hrow).symm
    _ ≤ ∑' u, f u := Summable.sum_le_tsum (P.image row) (fun u _ => hnonneg u) hsum
    _ = originalMeanSquare c W D H := rfl

theorem prime_sixth_rows_le_originalMeanSquare (P : Finset (Ideal O))
    (hprime : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, ∃ z : O, principal z = p ∧ IsPrimary z)
    (c : ArithmeticContext) (W : ℝ → ℂ) (D Y : ℝ)
    (hsize : ∀ p ∈ P, 0 < normIdeal p ∧ normIdeal p ≤ Y)
    (hsum : Summable (fun u : O =>
      if 0 < normElement u ∧ normElement u ≤ Y ^ (6 : ℕ)
      then ‖originalSum c W D u‖ ^ 2 else 0)) :
    (∑ p ∈ P, ‖originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ^ 2) ≤
      originalMeanSquare c W D (Y ^ (6 : ℕ)) := by
  apply finite_rows_le_originalMeanSquare P (fun p => primaryGenerator p ^ (6 : ℕ))
    (primaryGenerator_pow_injOn P hprime hprimary (by decide)) c W D (Y ^ (6 : ℕ))
    (hsum := hsum)
  intro p hp
  rw [normElement_primaryGenerator_pow (hprimary p hp)]
  exact ⟨pow_pos (hsize p hp).1 _, pow_le_pow_left₀ (hsize p hp).1.le (hsize p hp).2 _⟩

/-- The concrete mean square needs no additional summability hypothesis. -/
theorem prime_sixth_rows_le_meanSquare (P : Finset (Ideal O))
    (hprime : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, ∃ z : O, principal z = p ∧ IsPrimary z)
    (c : ArithmeticContext) (W : ℝ → ℂ) (D Y : ℝ)
    (hsize : ∀ p ∈ P, 0 < normIdeal p ∧ normIdeal p ≤ Y) :
    (∑ p ∈ P, ‖originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ^ 2) ≤
      originalMeanSquare c W D (Y ^ (6 : ℕ)) :=
  prime_sixth_rows_le_originalMeanSquare P hprime hprimary c W D Y hsize
    (originalMeanSquare_summable c W D (Y ^ (6 : ℕ)))

/-- Substitution of the actual arithmetic rows into the finite extraction lemma.
The comparison, mean-square estimate, and prime count are separate inputs. -/
theorem original_prime_rows_requested_loss (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, ∃ z : O, principal z = p ∧ IsPrimary z)
    (c : ArithmeticContext) (W : ℝ → ℂ) {D c₀ B K θ η ε : ℝ}
    (hD : 1 < D) (hc : 0 < c₀) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hθ : 0 ≤ θ) (hη : 0 < η) (hloss : 5 * θ / 12 + η ≤ ε)
    (hsize : ∀ p ∈ P, 0 < normIdeal p ∧ normIdeal p ≤ D ^ ((1 + θ) / 6))
    (herror : ∀ p ∈ P,
      ‖originalSum c W D 1 - originalSum c W D (primaryGenerator p ^ (6 : ℕ))‖ ≤
        B * D / D ^ ((1 + θ) / 6))
    (hmean : originalMeanSquare c W D (D ^ (1 + θ)) ≤ K * D ^ (2 + θ + η))
    (hcard : c₀ * D ^ ((1 + θ) / 6) / Real.log (D ^ ((1 + θ) / 6)) ≤
      (P.card : ℝ)) :
    ‖originalSum c W D 1‖ ≤
      Real.sqrt (2 * K * ((1 + θ) / (6 * η)) / c₀ + 2 * B ^ 2) *
        D ^ ((11 : ℝ) / 12 + ε) := by
  have hscale : (D ^ ((1 + θ) / 6)) ^ (6 : ℕ) = D ^ (1 + θ) := by
    rw [← Real.rpow_mul_natCast (zero_lt_one.trans hD).le]
    congr 1
    ring
  have hrows := prime_sixth_rows_le_meanSquare P hprime hprimary c W D
    (D ^ ((1 + θ) / 6)) hsize
  rw [hscale] at hrows
  exact prime_rows_requested_loss P hP (originalSum c W D 1)
    (fun p => originalSum c W D (primaryGenerator p ^ (6 : ℕ)))
    hD hc hB hK hθ hη hloss herror (hrows.trans hmean) hcard

end QRHShort
