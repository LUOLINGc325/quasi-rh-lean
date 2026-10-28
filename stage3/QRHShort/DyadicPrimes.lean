import QRHShort.FiniteSupport
import QRHShort.External
import Mathlib.Data.Fintype.Card

/-!
An actual finite enumeration of the dyadic prime ideals used in the Landau
input. Its cardinality is exactly the `Nat.card` in that input, and its
members satisfy the arithmetic exclusions required by the original sums.
-/

noncomputable section
open Classical

namespace QRHShort

def dyadicPrimeFinset (S : Finset (Ideal O)) (Y : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le Y).toFinset.filter
    (fun p => Prime p ∧ Y / 2 < normIdeal p ∧ p ∉ S)

@[simp] theorem mem_dyadicPrimeFinset {S : Finset (Ideal O)} {Y : ℝ} {p : Ideal O} :
    p ∈ dyadicPrimeFinset S Y ↔
      Prime p ∧ Y / 2 < normIdeal p ∧ normIdeal p ≤ Y ∧ p ∉ S := by
  simp only [dyadicPrimeFinset, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hupper, hprime, hlower, hS⟩
    exact ⟨hprime, hlower, hupper, hS⟩
  · rintro ⟨hprime, hlower, hupper, hS⟩
    exact ⟨hupper, hprime, hlower, hS⟩

def dyadicPrimeEquiv (S : Finset (Ideal O)) (Y : ℝ) :
    (dyadicPrimeFinset S Y) ≃ DyadicPrimeIdeals S Y where
  toFun p := ⟨p.1, mem_dyadicPrimeFinset.mp p.2⟩
  invFun p := ⟨p.1, mem_dyadicPrimeFinset.mpr p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_dyadicPrimeFinset (S : Finset (Ideal O)) (Y : ℝ) :
    (dyadicPrimeFinset S Y).card = Nat.card (DyadicPrimeIdeals S Y) := by
  calc
    (dyadicPrimeFinset S Y).card = Nat.card (dyadicPrimeFinset S Y) := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (DyadicPrimeIdeals S Y) := Nat.card_congr (dyadicPrimeEquiv S Y)

theorem dyadicPrimeFinset_nonempty {S : Finset (Ideal O)} {Y c : ℝ}
    (hY : 1 < Y) (hc : 0 < c)
    (hcard : c * Y / Real.log Y ≤ ((dyadicPrimeFinset S Y).card : ℝ)) :
    (dyadicPrimeFinset S Y).Nonempty := by
  have hpos : 0 < ((dyadicPrimeFinset S Y).card : ℝ) :=
    (div_pos (mul_pos hc (zero_lt_one.trans hY)) (Real.log_pos hY)).trans_le hcard
  exact Finset.card_pos.mp (Nat.cast_pos.mp hpos)

theorem dyadicPrimeFinset_outside (c : ArithmeticContext) {Y : ℝ} {p : Ideal O}
    (hp : p ∈ dyadicPrimeFinset c.S Y) : Outside c.S p := by
  obtain ⟨hprime, _, _, hS⟩ := mem_dyadicPrimeFinset.mp hp
  refine ⟨hprime.ne_zero, ?_⟩
  intro q hq hdiv
  have heq : q = p := (prime_dvd_prime_iff_eq (c.prime_S q hq) hprime).mp hdiv
  exact hS (heq ▸ hq)

end QRHShort
