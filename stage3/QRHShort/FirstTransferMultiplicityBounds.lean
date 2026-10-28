import QRHShort.FirstTransferFiniteSupport
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
The multiplicity problem in child M involves squarefree ideal divisors only.
Their number is subpolynomial in the ideal norm: a fixed finite set absorbs
small prime ideals, while every remaining prime contributes at most its norm
to any prescribed positive real power. No divisor estimate is assumed.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

def firstTransferSquarefreeDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) :=
  (first_transfer_divisors_finite hn).toFinset.filter Squarefree

theorem mem_firstTransferSquarefreeDivisors (n : Ideal O) (hn : n ≠ ⊥)
    (d : Ideal O) : d ∈ firstTransferSquarefreeDivisors n hn ↔ d ∣ n ∧ Squarefree d := by
  simp only [firstTransferSquarefreeDivisors, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- A squarefree divisor is the product of its distinct prime ideal factors. -/
theorem first_transfer_squarefree_divisor_eq_prod {n d : Ideal O} (hn : n ≠ ⊥)
    (hd : d ∣ n) (hsq : Squarefree d) :
    ∃ s ⊆ primeFactors n, (∏ p ∈ s, p) = d := by
  have hn0 : n ≠ 0 := hn
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn0 hd
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn0).mp hd
  have hnodup := (squarefree_iff_nodup_normalizedFactors hd0).mp hsq
  refine ⟨(normalizedFactors d).toFinset, ?_, ?_⟩
  · intro p hp
    exact Multiset.mem_toFinset.mpr
      (Multiset.subset_of_le hle (Multiset.mem_toFinset.mp hp))
  · calc
      (∏ p ∈ (normalizedFactors d).toFinset, p) =
          (normalizedFactors d).toFinset.val.prod := by
        simp only [Finset.prod_eq_multiset_prod, Multiset.map_id']
      _ = (normalizedFactors d).prod := by
        rw [Multiset.toFinset_val, hnodup.dedup]
      _ = d := Ideal.prod_normalizedFactors_eq_self hd0

theorem first_transfer_squarefree_divisor_count_le (n : Ideal O) (hn : n ≠ ⊥) :
    (firstTransferSquarefreeDivisors n hn).card ≤ 2 ^ (primeFactors n).card := by
  calc
    (firstTransferSquarefreeDivisors n hn).card ≤
        (((primeFactors n).powerset).image (fun s => ∏ p ∈ s, p)).card := by
      apply Finset.card_le_card
      intro d hd
      obtain ⟨hdiv, hsq⟩ := (mem_firstTransferSquarefreeDivisors n hn d).mp hd
      obtain ⟨s, hs, hprod⟩ := first_transfer_squarefree_divisor_eq_prod hn hdiv hsq
      exact Finset.mem_image.mpr ⟨s, Finset.mem_powerset.mpr hs, hprod⟩
    _ ≤ ((primeFactors n).powerset).card := Finset.card_image_le
    _ = _ := Finset.card_powerset _

theorem first_transfer_prime_subset_prod_dvd {n : Ideal O} (hn : n ≠ ⊥)
    {s : Finset (Ideal O)} (hs : s ⊆ primeFactors n) : (∏ p ∈ s, p) ∣ n := by
  have hle : s.val ≤ normalizedFactors n := by
    apply (Multiset.le_iff_subset s.nodup).mpr
    intro p hp
    exact Multiset.mem_toFinset.mp (hs hp)
  have hdiv := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self (show n ≠ 0 from hn)] at hdiv
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using hdiv

theorem first_transfer_prime_subset_norm_prod_le {n : Ideal O} (hn : n ≠ ⊥)
    {s : Finset (Ideal O)} (hs : s ⊆ primeFactors n) :
    (∏ p ∈ s, normIdeal p) ≤ normIdeal n := by
  have h := first_transfer_normIdeal_le_of_dvd hn (first_transfer_prime_subset_prod_dvd hn hs)
  simpa only [normIdeal, map_prod, Nat.cast_prod] using h

/-- The number of subsets of the distinct prime support is bounded by every
positive power of the ideal norm, with a constant chosen before the ideal. -/
theorem first_transfer_prime_support_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : Ideal O), n ≠ ⊥ →
      (2 : ℝ) ^ (primeFactors n).card ≤ K * normIdeal n ^ ε := by
  let T : ℝ := (2 : ℝ) ^ ε⁻¹
  let small : Finset (Ideal O) := (finite_normIdeal_le T).toFinset
  refine ⟨(2 : ℝ) ^ small.card, pow_pos (by norm_num) _, ?_⟩
  intro n hn
  let P := primeFactors n
  let lo := P.filter (fun p => normIdeal p ≤ T)
  let hi := P.filter (fun p => ¬ normIdeal p ≤ T)
  have hlo : lo.card ≤ small.card := by
    apply Finset.card_le_card
    intro p hp
    exact (finite_normIdeal_le T).mem_toFinset.mpr (Finset.mem_filter.mp hp).2
  have hsplit : lo.card + hi.card = P.card :=
    Finset.card_filter_add_card_filter_not (fun p => normIdeal p ≤ T)
  have hlarge (p : Ideal O) (hp : p ∈ hi) : (2 : ℝ) ≤ normIdeal p ^ ε := by
    have hpT : T ≤ normIdeal p := (not_le.mp (Finset.mem_filter.mp hp).2).le
    calc
      (2 : ℝ) = T ^ ε := (Real.rpow_inv_rpow (by norm_num) hε.ne').symm
      _ ≤ normIdeal p ^ ε := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hpT hε.le
  have hhi : (2 : ℝ) ^ hi.card ≤ normIdeal n ^ ε := by
    calc
      (2 : ℝ) ^ hi.card = ∏ _p ∈ hi, (2 : ℝ) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ hi, normIdeal p ^ ε :=
        Finset.prod_le_prod₀ (fun _ _ => by norm_num) hlarge
      _ = (∏ p ∈ hi, normIdeal p) ^ ε :=
        Real.finsetProd_rpow hi normIdeal (fun p _ => Nat.cast_nonneg _) ε
      _ ≤ normIdeal n ^ ε := Real.rpow_le_rpow
        (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _))
        (first_transfer_prime_subset_norm_prod_le hn (Finset.filter_subset _ _)) hε.le
  calc
    (2 : ℝ) ^ (primeFactors n).card = (2 : ℝ) ^ (lo.card + hi.card) := by rw [hsplit]
    _ = (2 : ℝ) ^ lo.card * (2 : ℝ) ^ hi.card := pow_add _ _ _
    _ ≤ (2 : ℝ) ^ small.card * normIdeal n ^ ε :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) hlo) hhi (by positivity) (by positivity)

/-- The squarefree divisor bound needed by the first-transfer fibers. -/
theorem first_transfer_squarefree_divisors_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : Ideal O) (hn : n ≠ ⊥),
      ((firstTransferSquarefreeDivisors n hn).card : ℝ) ≤ K * normIdeal n ^ ε := by
  obtain ⟨K, hK, hbound⟩ := first_transfer_prime_support_subpolynomial ε hε
  refine ⟨K, hK, ?_⟩
  intro n hn
  have hcard : ((firstTransferSquarefreeDivisors n hn).card : ℝ) ≤
      (2 : ℝ) ^ (primeFactors n).card := by
    exact_mod_cast first_transfer_squarefree_divisor_count_le n hn
  exact hcard.trans (hbound n hn)

end QRHShort
