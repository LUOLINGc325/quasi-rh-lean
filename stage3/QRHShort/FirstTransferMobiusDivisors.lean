import QRHShort.FirstTransferMultiplicityBounds
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Finite Möbius cancellation for the literal ideals.  The zero ideal is excluded
before taking divisors, and the powerset argument uses the proved factorization
of squarefree ideal divisors.  No frozen cancellation module is imported.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

def firstTransferIdealDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) :=
  (first_transfer_divisors_finite hn).toFinset

@[simp] theorem mem_firstTransferIdealDivisors (n : Ideal O) (hn : n ≠ ⊥) (d : Ideal O) :
    d ∈ firstTransferIdealDivisors n hn ↔ d ∣ n := by
  simp only [firstTransferIdealDivisors, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem first_transfer_normalizedFactors_prime_product (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : normalizedFactors (∏ p ∈ s, p) = s.val := by
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
    (normalizedFactors_prod_of_prime (m := s.val) hp)

theorem first_transfer_prime_product_squarefree (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : Squarefree (∏ p ∈ s, p) := by
  have hzero : (∏ p ∈ s, p) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hzero).mpr
  rw [first_transfer_normalizedFactors_prime_product s hp]
  exact s.nodup

theorem first_transfer_prime_product_mobius (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : mobius (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  rw [mobius, (first_transfer_prime_product_squarefree s hp).moebius_eq,
    factors_eq_normalizedFactors, first_transfer_normalizedFactors_prime_product s hp]
  rfl

theorem first_transfer_sum_idealDivisors_mobius (n : Ideal O) (hn : n ≠ ⊥) :
    (∑ d ∈ firstTransferIdealDivisors n hn, mobius d) = if n = 1 then 1 else 0 := by
  let P := primeFactors n
  have hfilter : (∑ d ∈ firstTransferIdealDivisors n hn, mobius d) =
      ∑ d ∈ firstTransferSquarefreeDivisors n hn, mobius d := by
    rw [firstTransferSquarefreeDivisors, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hsq : Squarefree d
    · simp only [if_pos hsq]
    · simp only [if_neg hsq, mobius, moebius_of_not_squarefree hsq]
  have hsum : (∑ s ∈ P.powerset, (-1 : ℤ) ^ s.card) =
      ∑ d ∈ firstTransferSquarefreeDivisors n hn, mobius d := by
    apply Finset.sum_bij (fun s _ => ∏ p ∈ s, p)
    · intro s hs
      have hsP : s ⊆ primeFactors n := Finset.mem_powerset.mp hs
      apply (mem_firstTransferSquarefreeDivisors n hn _).mpr
      refine ⟨first_transfer_prime_subset_prod_dvd hn hsP, ?_⟩
      apply first_transfer_prime_product_squarefree
      intro p hp
      exact prime_of_normalized_factor p (Multiset.mem_toFinset.mp (hsP hp))
    · intro s hs t ht hprod
      have hps : ∀ p ∈ s, Prime p := fun p hp => prime_of_normalized_factor p
        (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp hs) hp))
      have hpt : ∀ p ∈ t, Prime p := fun p hp => prime_of_normalized_factor p
        (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp ht) hp))
      apply Finset.val_injective
      rw [← first_transfer_normalizedFactors_prime_product s hps,
        ← first_transfer_normalizedFactors_prime_product t hpt, hprod]
    · intro d hd
      obtain ⟨hdiv, hsq⟩ := (mem_firstTransferSquarefreeDivisors n hn d).mp hd
      obtain ⟨s, hs, hprod⟩ := first_transfer_squarefree_divisor_eq_prod hn hdiv hsq
      exact ⟨s, Finset.mem_powerset.mpr hs, hprod⟩
    · intro s hs
      symm
      apply first_transfer_prime_product_mobius
      intro p hp
      exact prime_of_normalized_factor p
        (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp hs) hp))
  have hprod : (∏ _p ∈ P, (0 : ℤ)) = ∑ s ∈ P.powerset, (-1 : ℤ) ^ s.card := by
    simpa only [sub_self, Finset.prod_const_one, mul_one] using
      (Finset.prod_sub (fun _ : Ideal O => (1 : ℤ)) (fun _ => 1) P)
  rw [hfilter, ← hsum, ← hprod]
  by_cases h1 : n = 1
  · subst n
    simp only [P, QRHShort.primeFactors, normalizedFactors_one, Multiset.toFinset_zero,
      Finset.prod_empty, ite_true]
  · rw [if_neg h1]
    have hP : P.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro h
      have hz : normalizedFactors n = 0 := Multiset.toFinset_eq_empty.mp h
      exact h1 ((normalizedFactors_eq_zero_iff hn).mp hz).eq_one
    obtain ⟨p, hp⟩ := hP
    exact Finset.prod_eq_zero_iff.mpr ⟨p, hp, rfl⟩

theorem first_transfer_sum_idealDivisors_mobius_complex (n : Ideal O) (hn : n ≠ ⊥) :
    (∑ d ∈ firstTransferIdealDivisors n hn, (mobius d : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (first_transfer_sum_idealDivisors_mobius n hn)
  simpa only [Int.cast_sum, apply_ite, Int.cast_one, Int.cast_zero] using h

/-- All common divisors are actual divisors of the nonzero ideal gcd. -/
def firstTransferCommonDivisors (a b : Ideal O) (ha : a ≠ ⊥) : Finset (Ideal O) :=
  firstTransferIdealDivisors (gcd a b) (ne_zero_of_dvd_ne_zero ha (gcd_dvd_left a b))

@[simp] theorem mem_firstTransferCommonDivisors (a b : Ideal O) (ha : a ≠ ⊥) (d : Ideal O) :
    d ∈ firstTransferCommonDivisors a b ha ↔ d ∣ a ∧ d ∣ b := by
  rw [firstTransferCommonDivisors, mem_firstTransferIdealDivisors, dvd_gcd_iff]

theorem first_transfer_sum_commonDivisors_mobius (a b : Ideal O) (ha : a ≠ ⊥) :
    (∑ d ∈ firstTransferCommonDivisors a b ha, (mobius d : ℂ)) =
      if IsRelPrime a b then 1 else 0 := by
  rw [firstTransferCommonDivisors, first_transfer_sum_idealDivisors_mobius_complex]
  have hiff : gcd a b = 1 ↔ IsRelPrime a b :=
    ⟨fun h => gcd_isUnit_iff_isRelPrime.mp (h.symm ▸ isUnit_one),
      fun h => (gcd_isUnit_iff_isRelPrime.mpr h).eq_one⟩
  simp only [hiff]

theorem first_transfer_commonDivisor_mobius_hasFiniteSupport (a b : Ideal O) (ha : a ≠ ⊥) :
    Function.HasFiniteSupport (fun d : Ideal O =>
      if d ∣ a ∧ d ∣ b then (mobius d : ℂ) else 0) := by
  apply (first_transfer_divisors_finite ha).subset
  intro d hd
  by_contra hnot
  change ¬ d ∣ a at hnot
  exact hd (if_neg (fun h => hnot h.1))

theorem first_transfer_tsum_commonDivisors_mobius (a b : Ideal O) (ha : a ≠ ⊥) :
    (∑' d : Ideal O, if d ∣ a ∧ d ∣ b then (mobius d : ℂ) else 0) =
      if IsRelPrime a b then 1 else 0 := by
  rw [tsum_eq_sum (s := firstTransferCommonDivisors a b ha) (fun d hd =>
    if_neg (fun h => hd ((mem_firstTransferCommonDivisors a b ha d).mpr h)))]
  calc
    _ = ∑ d ∈ firstTransferCommonDivisors a b ha, (mobius d : ℂ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact if_pos ((mem_firstTransferCommonDivisors a b ha d).mp hd)
    _ = _ := first_transfer_sum_commonDivisors_mobius a b ha

end QRHShort
