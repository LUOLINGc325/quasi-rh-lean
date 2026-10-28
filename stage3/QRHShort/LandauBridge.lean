import QRHShort.DyadicPrimes

/-!
This file keeps the arithmetic part of the Landau bridge separate: it states
the explicit global interval-counting interface and proves the finite-deletion
and `Nat.card` bridges needed by the rest of the development.  The analytic
input is discharged in `APDyadicBridge` from the principal-ray OAI theorem.
-/

noncomputable section
open Classical

namespace QRHShort

/-- The dyadic prime ideals before removing a fixed finite set. -/
def allDyadicPrimeFinset (Y : ℝ) : Finset (Ideal O) :=
  dyadicPrimeFinset (∅ : Finset (Ideal O)) Y

@[simp] theorem mem_allDyadicPrimeFinset {Y : ℝ} {p : Ideal O} :
    p ∈ allDyadicPrimeFinset Y ↔
      Prime p ∧ Y / 2 < normIdeal p ∧ normIdeal p ≤ Y := by
  simpa [allDyadicPrimeFinset] using
    (mem_dyadicPrimeFinset (S := (∅ : Finset (Ideal O))) (Y := Y) (p := p))

theorem card_allDyadicPrimeFinset (Y : ℝ) :
    (allDyadicPrimeFinset Y).card =
      Nat.card (DyadicPrimeIdeals (∅ : Finset (Ideal O)) Y) := by
  simpa [allDyadicPrimeFinset] using
    (card_dyadicPrimeFinset (∅ : Finset (Ideal O)) Y)

/-! The elementary real bridge used when the analytic input is stated as a
dyadic prime-log mass. -/

def dyadicPrimeLogMass (S : Finset (Ideal O)) (Y : ℝ) : ℝ :=
  ∑ p ∈ dyadicPrimeFinset S Y, Real.log (normIdeal p)

private theorem prime_normIdeal_pos {p : Ideal O} (hp : Prime p) :
    0 < normIdeal p := by
  unfold normIdeal
  exact_mod_cast Nat.pos_of_ne_zero
    (fun h => hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))

theorem dyadicPrimeLogMass_le_card_mul_log
    {S : Finset (Ideal O)} {Y : ℝ} (hY : 1 < Y) :
    dyadicPrimeLogMass S Y ≤
      ((dyadicPrimeFinset S Y).card : ℝ) * Real.log Y := by
  unfold dyadicPrimeLogMass
  calc
    (∑ p ∈ dyadicPrimeFinset S Y, Real.log (normIdeal p)) ≤
        ∑ _p ∈ dyadicPrimeFinset S Y, Real.log Y := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hprime, _, hupper, _⟩ := mem_dyadicPrimeFinset.mp hp
      apply Real.log_le_log
      · exact prime_normIdeal_pos hprime
      · exact hupper
    _ = ((dyadicPrimeFinset S Y).card : ℝ) * Real.log Y := by
      simp

theorem dyadicPrime_card_lower_of_log_mass
    {S : Finset (Ideal O)} {Y M : ℝ} (hY : 1 < Y)
    (hM : M ≤ dyadicPrimeLogMass S Y) :
    M / Real.log Y ≤ ((dyadicPrimeFinset S Y).card : ℝ) := by
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hmass : M ≤ ((dyadicPrimeFinset S Y).card : ℝ) * Real.log Y :=
    hM.trans (dyadicPrimeLogMass_le_card_mul_log hY)
  exact (div_le_iff₀ hlog).2 (by simpa [mul_comm] using hmass)

/--
An explicit global prime-ideal interval-counting premise.  The parameter `A`
is arbitrary finite additive slack.  Thus this is a clean interface for the
usual prime-ideal asymptotic: after making `Y` large, its dyadic lower bound
dominates any prescribed finite deletion.

No theorem in this file asserts this premise.  A proof of it from Landau's
prime-ideal theorem may be supplied by a caller, while all finite combinatorics
below is unconditional.
-/
def GlobalPrimeIdealDyadicLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 ≤ A →
    ∃ Y₀ : ℝ, 1 < Y₀ ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        A + c * Y / Real.log Y ≤ ((allDyadicPrimeFinset Y).card : ℝ)

/-- Every prime in the undeleted dyadic set is either retained or deleted. -/
theorem allDyadicPrimeFinset_subset_union (S : Finset (Ideal O)) (Y : ℝ) :
    allDyadicPrimeFinset Y ⊆ dyadicPrimeFinset S Y ∪ S := by
  intro p hp
  by_cases hS : p ∈ S
  · exact Finset.mem_union.mpr (Or.inr hS)
  · apply Finset.mem_union.mpr
    left
    rw [mem_dyadicPrimeFinset]
    obtain ⟨hprime, hlow, hupp⟩ := mem_allDyadicPrimeFinset.mp hp
    exact ⟨hprime, hlow, hupp, hS⟩

/-- Deleting `S` costs at most `S.card` from the dyadic finite count. -/
theorem card_allDyadicPrimeFinset_le_add_deleted (S : Finset (Ideal O)) (Y : ℝ) :
    ((allDyadicPrimeFinset Y).card : ℝ) ≤
      ((dyadicPrimeFinset S Y).card : ℝ) + (S.card : ℝ) := by
  have hnat : (allDyadicPrimeFinset Y).card ≤
      (dyadicPrimeFinset S Y ∪ S).card :=
    Finset.card_le_card (allDyadicPrimeFinset_subset_union S Y)
  have hunion : (dyadicPrimeFinset S Y ∪ S).card ≤
      (dyadicPrimeFinset S Y).card + S.card :=
    Finset.card_union_le _ _
  have hnat' : (allDyadicPrimeFinset Y).card ≤
      (dyadicPrimeFinset S Y).card + S.card := hnat.trans hunion
  exact_mod_cast hnat'

/--
The global interval premise implies the desired finite-deletion lower bound,
with the existing `DyadicPrimeIdeals` subtype cardinality.  The only input
whose proof belongs to analytic number theory is the displayed premise
`hglobal`; the finite deletion, dyadic enumeration, and `Nat.card` conversion
are all proved here.
-/
theorem dyadicPrimeIdeals_lower_bound_of_global
    (hglobal : GlobalPrimeIdealDyadicLowerBound)
    (S : Finset (Ideal O)) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℝ, 1 < Y₀ ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        c * Y / Real.log Y ≤ (Nat.card (DyadicPrimeIdeals S Y) : ℝ) := by
  obtain ⟨c, hc, hglobal⟩ := hglobal
  obtain ⟨Y₀, hY₀, hcount⟩ := hglobal (S.card : ℝ) (Nat.cast_nonneg _)
  refine ⟨c, hc, Y₀, hY₀, ?_⟩
  intro Y hY
  have hglobalY := hcount Y hY
  have hdelete := card_allDyadicPrimeFinset_le_add_deleted S Y
  have hcard : c * Y / Real.log Y ≤ ((dyadicPrimeFinset S Y).card : ℝ) := by
    have : (S.card : ℝ) + c * Y / Real.log Y ≤
        ((dyadicPrimeFinset S Y).card : ℝ) + (S.card : ℝ) := by
      exact hglobalY.trans hdelete
    linarith
  simpa only [card_dyadicPrimeFinset] using hcard

/-- The same conclusion also supplies nonempty dyadic rows eventually. -/
theorem dyadicPrimeIdeals_eventually_nonempty_of_global
    (hglobal : GlobalPrimeIdealDyadicLowerBound)
    (S : Finset (Ideal O)) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℝ, 1 < Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      c * Y / Real.log Y ≤ (Nat.card (DyadicPrimeIdeals S Y) : ℝ) ∧
        (dyadicPrimeFinset S Y).Nonempty := by
  obtain ⟨c, hc, Y₀, hY₀, hcount⟩ :=
    dyadicPrimeIdeals_lower_bound_of_global hglobal S
  refine ⟨c, hc, Y₀, hY₀, ?_⟩
  intro Y hY
  have hcard := hcount Y hY
  have hcard' : c * Y / Real.log Y ≤ ((dyadicPrimeFinset S Y).card : ℝ) := by
    simpa only [card_dyadicPrimeFinset] using hcard
  exact ⟨hcard, dyadicPrimeFinset_nonempty (hY₀.trans_le hY) hc hcard'⟩

end QRHShort
