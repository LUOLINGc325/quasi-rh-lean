import QRHShort.PoissonAssembly
import QRHShort.SquarefreeNumeratorPowers
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
The finite inclusion--exclusion and lattice change of variables for the frozen
`CoprimeExpansionStatement`. The sole remaining analytic input is stated as
`RadialCharacterSummabilityStatement`; no unproved arithmetic input is used.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid
namespace QRHShort.PoissonProof.CoprimeExpansion

/-- All ideal divisors of a nonzero ideal. -/
def idealDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) := by
  letI : Fintype {d : Ideal O // d ∣ n} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd n hn
  exact Finset.univ.image (fun d : {d : Ideal O // d ∣ n} => d.1)

@[simp] theorem mem_idealDivisors (n : Ideal O) (hn : n ≠ ⊥) (d : Ideal O) :
    d ∈ idealDivisors n hn ↔ d ∣ n := by
  simp [idealDivisors]

private theorem normalizedFactors_finset_prod (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : normalizedFactors (∏ p ∈ s, p) = s.val := by
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
    (normalizedFactors_prod_of_prime (m := s.val) hp)

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
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
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
    · simp only [hsq, ite_false, mobius, moebius_of_not_squarefree hsq]
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
    rw [if_pos rfl]
    change (∏ _p ∈ (normalizedFactors (1 : Ideal O)).toFinset, (0 : ℤ)) = 1
    rw [normalizedFactors_one]
    rfl
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

theorem radical_dvd (r : Ideal O) (hr : r ≠ ⊥) : outsideRadical ∅ r ∣ r := by
  simpa [outsideRadical, primeFactors] using
    (primeSubset_prod_properties hr (Finset.Subset.refl
      (normalizedFactors r).toFinset)).1

theorem isRelPrime_radical_iff (r a : Ideal O) (hr : r ≠ ⊥) :
    IsRelPrime (outsideRadical ∅ r) a ↔ IsRelPrime r a := by
  constructor
  · intro h
    apply (isRelPrime_iff_no_prime_factors hr).mpr
    intro p hpr hpa hp
    have hmem : p ∈ primeFactors r :=
      Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hr).mpr ⟨hp, hpr⟩)
    have hpR : p ∣ outsideRadical ∅ r := by
      simpa [outsideRadical] using Finset.dvd_prod_of_mem id hmem
    exact hp.not_unit (h hpR hpa)
  · intro h d hd ha
    exact h (hd.trans (radical_dvd r hr)) ha

theorem gcd_eq_one_iff_relprime (a b : Ideal O) :
    gcd a b = 1 ↔ IsRelPrime a b := by
  constructor
  · intro h d ha hb
    exact isUnit_of_dvd_one (h ▸ dvd_gcd ha hb)
  · intro h
    simpa only [Ideal.isUnit_iff, Ideal.one_eq_top] using
      h (gcd_dvd_left a b) (gcd_dvd_right a b)

/-- The pointwise ideal Möbius indicator, including the lattice point zero. -/
theorem coprime_indicator (r : Ideal O) (hr : r ≠ ⊥) (a : Ideal O) :
    (∑ d ∈ idealDivisors (outsideRadical ∅ r) (radical_ne_bot r),
      if d ∣ a then (mobius d : ℂ) else 0) =
      if IsRelPrime a r then 1 else 0 := by
  let N := outsideRadical ∅ r
  have hN : N ≠ 0 := radical_ne_bot r
  have hg : gcd N a ≠ 0 := ne_zero_of_dvd_ne_zero hN (gcd_dvd_left N a)
  have heq :
      (∑ d ∈ idealDivisors N hN, if d ∣ a then (mobius d : ℂ) else 0) =
      ∑ d ∈ idealDivisors (gcd N a) hg, (mobius d : ℂ) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext d
      simp only [Finset.mem_filter, mem_idealDivisors, dvd_gcd_iff]
    · intro d _
      rfl
  rw [heq, sum_idealDivisors_mobius_complex]
  have hi : gcd N a = 1 ↔ IsRelPrime a r :=
    (gcd_eq_one_iff_relprime N a).trans
      ((isRelPrime_radical_iff r a hr).trans isRelPrime_comm)
  simp only [hi]

open SquarefreeReflection.RayValuePrerequisites

theorem prime_primary_generator (p : Ideal O) (hp : Prime p)
    (hrel : IsRelPrime p (principal 3)) : principal (primaryGenerator p) = p := by
  have hex : ∃ a : O, principal a = p ∧ IsPrimary a := by
    let a := idealGenerator p
    have hgen : principal a = p := Ideal.span_singleton_generator p
    have ha0 : a ≠ 0 := by
      intro ha
      apply hp.ne_zero
      rw [← hgen, ha]
      simp [principal]
    have haprime : Prime a := by
      apply (Ideal.span_singleton_prime ha0).mp
      change (principal a).IsPrime
      rw [hgen]
      exact Ideal.isPrime_of_prime hp
    have hnot : ¬ omega - 1 ∣ a := by
      intro hdiv
      have ha3 : a ∣ (3 : O) :=
        (omega_sub_one_prime.associated_of_dvd haprime hdiv).symm.dvd.trans
          omega_sub_one_dvd_three
      apply hp.not_unit
      apply hrel (dvd_refl p)
      apply Ideal.dvd_span_singleton.mpr
      rw [← hgen]
      exact Ideal.mem_span_singleton.mpr ha3
    obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd a hnot
    exact ⟨(u : O) * a, (Ideal.span_singleton_mul_left_unit u.isUnit a).trans hgen, hu⟩
  simpa only [primaryGenerator, dif_pos hex] using (Classical.choose_spec hex).1

/-- The exact generator in the frozen Poisson interface generates every nonzero ideal. -/
theorem chosenGenerator_spec {a : Ideal O} (ha : a ≠ ⊥) :
    principal (chosenGenerator a) = a := by
  have hprime (P : Ideal O) (hP : Prime P) :
      principal (if IsRelPrime P (principal 3) then primaryGenerator P
        else idealGenerator P) = P := by
    by_cases hrel : IsRelPrime P (principal 3)
    · rw [if_pos hrel]
      exact prime_primary_generator P hP hrel
    · rw [if_neg hrel]
      exact Ideal.span_singleton_generator P
  rw [chosenGenerator, if_neg ha, principal, ← Ideal.multiset_prod_span_singleton,
    Multiset.map_map]
  calc
    ((normalizedFactors a).map (fun P =>
        Ideal.span {if IsRelPrime P (principal 3) then primaryGenerator P
          else idealGenerator P})).prod = (normalizedFactors a).prod := by
      congr 1
      simpa only [principal, Multiset.map_id'] using
        (Multiset.map_congr rfl (fun P hP => hprime P (prime_of_normalized_factor P hP)))
    _ = a := Ideal.prod_normalizedFactors_eq_self ha

theorem normElement_mul (a b : O) :
    normElement (a * b) = normElement a * normElement b := by
  simp only [normElement, principal, ← Ideal.span_singleton_mul_span_singleton,
    normIdeal, map_mul, Nat.cast_mul]

theorem value_mul (χ : PrimitiveResidueCharacter) (a b : O) :
    χ.value (a * b) = χ.value a * χ.value b := by
  simp only [PrimitiveResidueCharacter.value, map_mul]

theorem divisor_iff_generator_dvd {d : Ideal O} (hd : d ≠ ⊥) (k : O) :
    d ∣ principal k ↔ chosenGenerator d ∣ k := by
  change d ∣ Ideal.span {k} ↔ chosenGenerator d ∣ k
  rw [Ideal.dvd_span_singleton]
  conv_lhs => rw [← chosenGenerator_spec hd]
  exact Ideal.mem_span_singleton (x := k) (y := chosenGenerator d)

/-- Reindex a lattice submodule by multiplication by its actual chosen generator.
No convergence hypothesis is needed for this injective reindexing. -/
theorem tsum_divisible (d : Ideal O) (hd : d ≠ ⊥) (f : O → ℂ) :
    (∑' k : O, if d ∣ principal k then f k else 0) =
      ∑' k : O, f (chosenGenerator d * k) := by
  have hg : chosenGenerator d ≠ 0 := by
    intro h
    apply hd
    rw [← chosenGenerator_spec hd, h]
    simp [principal]
  have hinj : Function.Injective (fun k : O => chosenGenerator d * k) :=
    mul_right_injective₀ hg
  have hreindex := hinj.tsum_eq (f := fun k : O => if d ∣ principal k then f k else 0)
    (by
      intro k hk
      have hdv : d ∣ principal k := by
        by_contra h
        exact hk (if_neg h)
      obtain ⟨l, hl⟩ := (divisor_iff_generator_dvd hd k).mp hdv
      exact ⟨l, hl.symm⟩)
  rw [← hreindex]
  apply tsum_congr
  intro k
  exact if_pos ((divisor_iff_generator_dvd hd _).mpr (dvd_mul_right _ _))

theorem tsum_scaled_divisible (χ : PrimitiveResidueCharacter) (d : Ideal O)
    (hd : d ≠ ⊥) (Φ : ℝ → ℂ) (H : ℝ) :
    (∑' k : O, if d ∣ principal k then χ.value k * Φ (normElement k / H) else 0) =
      χ.value (chosenGenerator d) *
        ∑' k : O, χ.value k * Φ (normElement k / (H / normIdeal d)) := by
  rw [tsum_divisible d hd, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [value_mul, normElement_mul]
  have hg : normElement (chosenGenerator d) = normIdeal d := by
    rw [normElement, chosenGenerator_spec hd]
  rw [hg]
  have hscale : normIdeal d * normElement k / H =
      normElement k / (H / normIdeal d) := by
    rw [div_div_eq_mul_div]
    ring
  rw [hscale]
  ring

end QRHShort.PoissonProof.CoprimeExpansion

namespace QRHShort.PoissonProof
open CoprimeExpansion

/-- The remaining analytic leaf: absolute convergence is required only to
interchange a finite divisor sum with the actual Schwartz lattice sum. -/
def RadialCharacterSummabilityStatement : Prop :=
  ∀ (χ : PrimitiveResidueCharacter) (Φ : ℝ → ℂ) (H : ℝ),
    0 < H → RadialSchwartz Φ →
      Summable (fun k : O => χ.value k * Φ (normElement k / H))

/-- All ideal inclusion--exclusion, generator arithmetic, character
multiplicativity and scale changes are discharged; only convergence remains. -/
theorem coprimeExpansion_of_radialCharacterSummability
    (hs : RadialCharacterSummabilityStatement) : CoprimeExpansionStatement := by
  intro χ r Φ H hr hH hΦ
  let D := idealDivisors (outsideRadical ∅ r) (radical_ne_bot r)
  let f : O → ℂ := fun k => χ.value k * Φ (normElement k / H)
  have hf : Summable f := hs χ Φ H hH hΦ
  have hpoint (k : O) :
      (if IsRelPrime (principal k) r then f k else 0) =
        ∑ d ∈ D, (mobius d : ℂ) * (if d ∣ principal k then f k else 0) := by
    have hi := coprime_indicator r hr (principal k)
    have hi' := congrArg (fun z : ℂ => z * f k) hi
    rw [Finset.sum_mul] at hi'
    simpa only [D, ite_mul, one_mul, zero_mul, mul_ite, mul_zero] using hi'.symm
  have hsum (d : Ideal O) : Summable (fun k : O =>
      (mobius d : ℂ) * (if d ∣ principal k then f k else 0)) := by
    have hi := hf.indicator {k | d ∣ principal k}
    simpa only [Set.indicator, Set.mem_setOf_eq] using hi.mul_left (mobius d : ℂ)
  calc
    (∑' k : O, if IsRelPrime (principal k) r then f k else 0) =
        ∑' k : O, ∑ d ∈ D, (mobius d : ℂ) *
          (if d ∣ principal k then f k else 0) := tsum_congr hpoint
    _ = ∑ d ∈ D, (mobius d : ℂ) *
        ∑' k : O, if d ∣ principal k then f k else 0 := by
      rw [Summable.tsum_finsetSum (fun d _ => hsum d)]
      apply Finset.sum_congr rfl
      intro d _
      exact tsum_mul_left
    _ = ∑ d ∈ D, (mobius d : ℂ) * χ.value (chosenGenerator d) *
        ∑' k : O, χ.value k * Φ (normElement k / (H / normIdeal d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 := ne_zero_of_dvd_ne_zero (radical_ne_bot r)
        ((mem_idealDivisors _ _ _).mp hd)
      rw [show (∑' k : O, if d ∣ principal k then f k else 0) =
          χ.value (chosenGenerator d) *
            ∑' k : O, χ.value k * Φ (normElement k / (H / normIdeal d)) from
          tsum_scaled_divisible χ d hd0 Φ H]
      ring
    _ = _ := by
      rw [tsum_eq_sum (s := D) (fun d hd =>
        if_neg (fun h => hd ((mem_idealDivisors _ _ _).mpr h)))]
      apply Finset.sum_congr rfl
      intro d hd
      exact (if_pos ((mem_idealDivisors _ _ _).mp hd)).symm

end QRHShort.PoissonProof
