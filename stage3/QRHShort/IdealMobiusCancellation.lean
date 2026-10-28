import QRHShort.HeckeMultiplicative
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
Finite divisor cancellation for the actual ideals of the fixed cyclotomic field.
The finite divisor set is obtained from unique factorization; the zero ideal is
excluded because its divisor set is infinite. No analytic identity is assumed.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

/-- All ideal divisors of a nonzero ideal. -/
def idealDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) := by
  letI : Fintype {d : Ideal O // d ∣ n} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd n hn
  exact (Finset.univ : Finset {d : Ideal O // d ∣ n}).image Subtype.val

@[simp] theorem mem_idealDivisors (n : Ideal O) (hn : n ≠ ⊥) (d : Ideal O) :
    d ∈ idealDivisors n hn ↔ d ∣ n := by
  unfold idealDivisors
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hd
    exact ⟨⟨d, hd⟩, rfl⟩

private theorem normalizedFactors_finset_prod (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : normalizedFactors (∏ p ∈ s, p) = s.val := by
  calc
    normalizedFactors (∏ p ∈ s, p) = normalizedFactors s.val.prod :=
      congrArg normalizedFactors (Finset.prod_val s).symm
    _ = s.val := normalizedFactors_prod_of_prime (m := s.val) hp

private theorem prime_finset_prod_ne_zero (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : (∏ p ∈ s, p) ≠ (0 : Ideal O) := by
  exact Finset.prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)

private theorem prime_finset_prod_squarefree (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : Squarefree (∏ p ∈ s, p) := by
  apply (squarefree_iff_nodup_normalizedFactors
    (prime_finset_prod_ne_zero s hp)).mpr
  rw [normalizedFactors_finset_prod s hp]
  exact s.nodup

/-- A finite set of distinct prime ideals gives the usual Möbius sign. -/
theorem prime_finset_mobius (s : Finset (Ideal O)) (hp : ∀ p ∈ s, Prime p) :
    mobius (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  rw [mobius, (prime_finset_prod_squarefree s hp).moebius_eq,
    factors_eq_normalizedFactors, normalizedFactors_finset_prod s hp] <;> rfl

/-- Every squarefree divisor is the product of a subset of the prime support. -/
theorem squarefree_divisor_eq_prod {n d : Ideal O} (hn : n ≠ ⊥)
    (hd : d ∣ n) (hsq : Squarefree d) :
    ∃ t ⊆ (normalizedFactors n).toFinset, (∏ p ∈ t, p) = d := by
  have hd0 : d ≠ 0 := by
    intro h
    apply hn
    exact zero_dvd_iff.mp (h ▸ hd)
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn).mp hd
  have hnodup := (squarefree_iff_nodup_normalizedFactors hd0).mp hsq
  refine ⟨(normalizedFactors d).toFinset, ?_, ?_⟩
  · intro p hp
    exact Multiset.mem_toFinset.mpr
      (Multiset.subset_of_le hle (Multiset.mem_toFinset.mp hp))
  · calc
      (∏ p ∈ (normalizedFactors d).toFinset, p) =
          (normalizedFactors d).toFinset.val.prod :=
        (Finset.prod_val _).symm
      _ = (normalizedFactors d).prod := by
        rw [Multiset.toFinset_val, hnodup.dedup]
      _ = d := Ideal.prod_normalizedFactors_eq_self hd0

private theorem primeSubset_prod_properties {n : Ideal O} (hn : n ≠ ⊥)
    {t : Finset (Ideal O)} (ht : t ⊆ (normalizedFactors n).toFinset) :
    (∏ p ∈ t, p) ∣ n ∧ Squarefree (∏ p ∈ t, p) := by
  have hp : ∀ p ∈ t, Prime p := fun p h =>
    prime_of_normalized_factor p (Multiset.mem_toFinset.mp (ht h))
  refine ⟨?_, prime_finset_prod_squarefree t hp⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors
    (prime_finset_prod_ne_zero t hp) hn).mpr
  rw [normalizedFactors_finset_prod t hp]
  apply (Multiset.le_iff_subset t.nodup).mpr
  intro p h
  exact Multiset.mem_toFinset.mp (ht h)

private theorem primeSubset_prod_injective {n : Ideal O}
    {t u : Finset (Ideal O)} (ht : t ⊆ (normalizedFactors n).toFinset)
    (hu : u ⊆ (normalizedFactors n).toFinset)
    (h : (∏ p ∈ t, p) = ∏ p ∈ u, p) : t = u := by
  have hpt : ∀ p ∈ t, Prime p := fun p hp =>
    prime_of_normalized_factor p (Multiset.mem_toFinset.mp (ht hp))
  have hpu : ∀ p ∈ u, Prime p := fun p hp =>
    prime_of_normalized_factor p (Multiset.mem_toFinset.mp (hu hp))
  apply Finset.val_injective
  rw [← normalizedFactors_finset_prod t hpt, ← normalizedFactors_finset_prod u hpu]
  exact congrArg normalizedFactors h

/-- The actual finite ideal-divisor Möbius cancellation identity. -/
theorem sum_idealDivisors_mobius (n : Ideal O) (hn : n ≠ ⊥) :
    (∑ d ∈ idealDivisors n hn, mobius d) = if n = 1 then 1 else 0 := by
  let P := (normalizedFactors n).toFinset
  have hfilter : (∑ d ∈ idealDivisors n hn, mobius d) =
      ∑ d ∈ (idealDivisors n hn).filter Squarefree, mobius d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hsq : Squarefree d
    · simp only [hsq, if_pos]
    · simp only [hsq, if_false, mobius, moebius_of_not_squarefree hsq]
  have hsum : (∑ t ∈ P.powerset, (-1 : ℤ) ^ t.card) =
      ∑ d ∈ (idealDivisors n hn).filter Squarefree, mobius d := by
    apply Finset.sum_bij (fun t _ => ∏ p ∈ t, p)
    · intro t ht
      rcases primeSubset_prod_properties hn (Finset.mem_powerset.mp ht) with ⟨hd, hsq⟩
      exact Finset.mem_filter.mpr ⟨(mem_idealDivisors n hn _).mpr hd, hsq⟩
    · intro t ht u hu h
      exact primeSubset_prod_injective (Finset.mem_powerset.mp ht)
        (Finset.mem_powerset.mp hu) h
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hsq⟩
      obtain ⟨t, ht, hprod⟩ := squarefree_divisor_eq_prod hn
        ((mem_idealDivisors n hn d).mp hd) hsq
      exact ⟨t, Finset.mem_powerset.mpr ht, hprod⟩
    · intro t ht
      symm
      apply prime_finset_mobius
      intro p hp
      exact prime_of_normalized_factor p
        (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp ht) hp))
  have hprod : (∏ _p ∈ P, (0 : ℤ)) =
      ∑ t ∈ P.powerset, (-1 : ℤ) ^ t.card := by
    simpa only [sub_self, Finset.prod_const_one, mul_one] using
      (Finset.prod_sub (fun _ : Ideal O => (1 : ℤ)) (fun _ => 1) P)
  rw [hfilter, ← hsum, ← hprod]
  by_cases h1 : n = 1
  · subst n
    simp only [P, normalizedFactors_one, Multiset.toFinset_zero,
      Finset.prod_empty, if_true]
  · rw [if_neg h1]
    have hP : P.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro h
      have hz : normalizedFactors n = 0 := Multiset.toFinset_eq_empty.mp h
      have hu := (normalizedFactors_eq_zero_iff hn).mp hz
      exact h1 (by simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hu)
    obtain ⟨p, hp⟩ := hP
    exact Finset.prod_eq_zero_iff.mpr ⟨p, hp, rfl⟩

/-- Complex-valued form used when factoring ideal Dirichlet coefficients. -/
theorem sum_idealDivisors_mobius_complex (n : Ideal O) (hn : n ≠ ⊥) :
    (∑ d ∈ idealDivisors n hn, (mobius d : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_idealDivisors_mobius n hn)
  simpa only [Int.cast_sum, apply_ite, Int.cast_one, Int.cast_zero] using h

/-- Multiplicative weights turn finite Möbius divisor sums into Euler factors. -/
theorem sum_idealDivisors_mobius_mul (n : Ideal O) (hn : n ≠ ⊥)
    (f : Ideal O →* ℂ) :
    (∑ d ∈ idealDivisors n hn, (mobius d : ℂ) * f d) =
      ∏ p ∈ (normalizedFactors n).toFinset, (1 - f p) := by
  let P := (normalizedFactors n).toFinset
  have hfilter : (∑ d ∈ idealDivisors n hn, (mobius d : ℂ) * f d) =
      ∑ d ∈ (idealDivisors n hn).filter Squarefree, (mobius d : ℂ) * f d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hsq : Squarefree d
    · simp only [hsq, if_pos]
    · simp only [hsq, if_false, mobius, moebius_of_not_squarefree hsq,
        Int.cast_zero, zero_mul]
  have hsum : (∑ t ∈ P.powerset, (-1 : ℂ) ^ t.card * ∏ p ∈ t, f p) =
      ∑ d ∈ (idealDivisors n hn).filter Squarefree, (mobius d : ℂ) * f d := by
    apply Finset.sum_bij (fun t _ => ∏ p ∈ t, p)
    · intro t ht
      rcases primeSubset_prod_properties hn (Finset.mem_powerset.mp ht) with ⟨hd, hsq⟩
      exact Finset.mem_filter.mpr ⟨(mem_idealDivisors n hn _).mpr hd, hsq⟩
    · intro t ht u hu h
      exact primeSubset_prod_injective (Finset.mem_powerset.mp ht)
        (Finset.mem_powerset.mp hu) h
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hsq⟩
      obtain ⟨t, ht, hprod⟩ := squarefree_divisor_eq_prod hn
        ((mem_idealDivisors n hn d).mp hd) hsq
      exact ⟨t, Finset.mem_powerset.mpr ht, hprod⟩
    · intro t ht
      have hp : ∀ p ∈ t, Prime p := fun p h =>
        prime_of_normalized_factor p
          (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp ht) h))
      have hsign : (mobius (∏ p ∈ t, p) : ℂ) = (-1 : ℂ) ^ t.card := by
        exact_mod_cast prime_finset_mobius t hp
      rw [hsign, map_prod]
  have hprod : (∏ p ∈ P, (1 - f p)) =
      ∑ t ∈ P.powerset, (-1 : ℂ) ^ t.card * ∏ p ∈ t, f p := by
    simpa only [Finset.prod_const_one, mul_one] using
      (Finset.prod_sub (fun _ : Ideal O => (1 : ℂ)) f P)
  exact hfilter.trans (hsum.symm.trans hprod.symm)

/-- The squarefree ideal generated by a finite prime set has exactly these factors. -/
theorem sum_primeProductDivisors_mobius_mul (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hn : (∏ P ∈ S, P) ≠ ⊥) (f : Ideal O →* ℂ) :
    (∑ d ∈ idealDivisors (∏ P ∈ S, P) hn, (mobius d : ℂ) * f d) =
      ∏ P ∈ S, (1 - f P) := by
  simpa only [normalizedFactors_finset_prod S hS, Finset.val_toFinset] using
    sum_idealDivisors_mobius_mul (∏ P ∈ S, P) hn f

/-- Ideal-indexed form of the finite weighted divisor identity. -/
theorem tsum_ideal_dvd_mobius_mul (n : Ideal O) (hn : n ≠ ⊥)
    (f : Ideal O →* ℂ) :
    (∑' d : Ideal O, if d ∣ n then (mobius d : ℂ) * f d else 0) =
      ∏ p ∈ (normalizedFactors n).toFinset, (1 - f p) := by
  rw [tsum_eq_sum (s := idealDivisors n hn) (fun d hd =>
    if_neg (fun h => hd ((mem_idealDivisors n hn d).mpr h)))]
  calc
    (∑ d ∈ idealDivisors n hn, if d ∣ n then (mobius d : ℂ) * f d else 0) =
        ∑ d ∈ idealDivisors n hn, (mobius d : ℂ) * f d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact if_pos ((mem_idealDivisors n hn d).mp hd)
    _ = _ := sum_idealDivisors_mobius_mul n hn f

end QRHShort
