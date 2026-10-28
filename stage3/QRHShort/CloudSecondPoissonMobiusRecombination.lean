import QRHShort.SecondPoissonAssembly
import QRHShort.SquarefreeNumeratorPowers
import QRHShort.QuotientSixthRoot
import QRHShort.PrimeComparison
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! Finite Möbius recombination for the literal second-Poisson columns.
The generic finite divisor reindexing is adapted from previously checked
first-transfer arguments, reproduced here without cross-branch imports. -/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch
open SecondPoissonProof

theorem second_mobius_divisors_finite {n : Ideal O} (hn : n ≠ ⊥) :
    {d : Ideal O | d ∣ n}.Finite := by
  apply (finite_normIdeal_le (normIdeal n)).subset
  intro d hd
  have hp : 0 < n.absNorm := Nat.pos_of_ne_zero
    (fun h => hn (Ideal.absNorm_eq_zero_iff.mp h))
  have h := Nat.le_of_dvd hp
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd))
  change (d.absNorm : ℝ) ≤ (n.absNorm : ℝ)
  exact_mod_cast h

theorem second_mobius_outside_mul_iff (c : ArithmeticContext) (a b : Ideal O) :
    Outside c.S (a * b) ↔ Outside c.S a ∧ Outside c.S b := by
  constructor
  · intro h
    constructor
    · refine ⟨?_, fun p hp hpa => h.2 p hp (dvd_mul_of_dvd_left hpa b)⟩
      intro ha
      exact h.1 (by rw [ha, Ideal.bot_mul])
    · refine ⟨?_, fun p hp hpb => h.2 p hp (dvd_mul_of_dvd_right hpb a)⟩
      intro hb
      exact h.1 (by rw [hb, Ideal.mul_bot])
  · rintro ⟨ha, hb⟩
    refine ⟨fun h => (Ideal.mul_eq_bot.mp h).elim ha.1 hb.1, ?_⟩
    intro p hp hdiv
    exact ((c.prime_S p hp).dvd_mul.mp hdiv).elim (ha.2 p hp) (hb.2 p hp)

theorem second_mobius_outside_of_dvd (c : ArithmeticContext) {a b : Ideal O}
    (hb : Outside c.S b) (hab : a ∣ b) : Outside c.S a := by
  refine ⟨?_, fun p hp hpa => hb.2 p hp (hpa.trans hab)⟩
  intro ha
  apply hb.1
  exact bot_unique (ha ▸ Ideal.dvd_iff_le.mp hab)

def secondMobiusGcdPairAdmissible (c : ArithmeticContext) (p : Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2

def secondMobiusSquarefreeDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) :=
  (second_mobius_divisors_finite hn).toFinset.filter Squarefree

theorem mem_secondMobiusSquarefreeDivisors (n : Ideal O) (hn : n ≠ ⊥)
    (d : Ideal O) : d ∈ secondMobiusSquarefreeDivisors n hn ↔ d ∣ n ∧ Squarefree d := by
  simp only [secondMobiusSquarefreeDivisors, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- A squarefree divisor is the product of its distinct prime ideal factors. -/
theorem second_mobius_squarefree_divisor_eq_prod {n d : Ideal O} (hn : n ≠ ⊥)
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

theorem second_mobius_prime_subset_prod_dvd {n : Ideal O} (hn : n ≠ ⊥)
    {s : Finset (Ideal O)} (hs : s ⊆ primeFactors n) : (∏ p ∈ s, p) ∣ n := by
  have hle : s.val ≤ normalizedFactors n := by
    apply (Multiset.le_iff_subset s.nodup).mpr
    intro p hp
    exact Multiset.mem_toFinset.mp (hs hp)
  have hdiv := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self (show n ≠ 0 from hn)] at hdiv
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using hdiv

def secondMobiusIdealDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) :=
  (second_mobius_divisors_finite hn).toFinset

@[simp] theorem mem_secondMobiusIdealDivisors (n : Ideal O) (hn : n ≠ ⊥) (d : Ideal O) :
    d ∈ secondMobiusIdealDivisors n hn ↔ d ∣ n := by
  simp only [secondMobiusIdealDivisors, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem second_mobius_normalizedFactors_prime_product (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : normalizedFactors (∏ p ∈ s, p) = s.val := by
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
    (normalizedFactors_prod_of_prime (m := s.val) hp)

theorem second_mobius_prime_product_squarefree (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : Squarefree (∏ p ∈ s, p) := by
  have hzero : (∏ p ∈ s, p) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hzero).mpr
  rw [second_mobius_normalizedFactors_prime_product s hp]
  exact s.nodup

theorem second_mobius_prime_product_mobius (s : Finset (Ideal O))
    (hp : ∀ p ∈ s, Prime p) : mobius (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  rw [mobius, (second_mobius_prime_product_squarefree s hp).moebius_eq,
    factors_eq_normalizedFactors, second_mobius_normalizedFactors_prime_product s hp]
  rfl

theorem second_mobius_sum_idealDivisors_mobius (n : Ideal O) (hn : n ≠ ⊥) :
    (∑ d ∈ secondMobiusIdealDivisors n hn, mobius d) = if n = 1 then 1 else 0 := by
  let P := primeFactors n
  have hfilter : (∑ d ∈ secondMobiusIdealDivisors n hn, mobius d) =
      ∑ d ∈ secondMobiusSquarefreeDivisors n hn, mobius d := by
    rw [secondMobiusSquarefreeDivisors, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hsq : Squarefree d
    · simp only [if_pos hsq]
    · simp only [if_neg hsq, mobius, moebius_of_not_squarefree hsq]
  have hsum : (∑ s ∈ P.powerset, (-1 : ℤ) ^ s.card) =
      ∑ d ∈ secondMobiusSquarefreeDivisors n hn, mobius d := by
    apply Finset.sum_bij (fun s _ => ∏ p ∈ s, p)
    · intro s hs
      have hsP : s ⊆ primeFactors n := Finset.mem_powerset.mp hs
      apply (mem_secondMobiusSquarefreeDivisors n hn _).mpr
      refine ⟨second_mobius_prime_subset_prod_dvd hn hsP, ?_⟩
      apply second_mobius_prime_product_squarefree
      intro p hp
      exact prime_of_normalized_factor p (Multiset.mem_toFinset.mp (hsP hp))
    · intro s hs t ht hprod
      have hps : ∀ p ∈ s, Prime p := fun p hp => prime_of_normalized_factor p
        (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp hs) hp))
      have hpt : ∀ p ∈ t, Prime p := fun p hp => prime_of_normalized_factor p
        (Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp ht) hp))
      apply Finset.val_injective
      rw [← second_mobius_normalizedFactors_prime_product s hps,
        ← second_mobius_normalizedFactors_prime_product t hpt, hprod]
    · intro d hd
      obtain ⟨hdiv, hsq⟩ := (mem_secondMobiusSquarefreeDivisors n hn d).mp hd
      obtain ⟨s, hs, hprod⟩ := second_mobius_squarefree_divisor_eq_prod hn hdiv hsq
      exact ⟨s, Finset.mem_powerset.mpr hs, hprod⟩
    · intro s hs
      symm
      apply second_mobius_prime_product_mobius
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

theorem second_mobius_sum_idealDivisors_mobius_complex (n : Ideal O) (hn : n ≠ ⊥) :
    (∑ d ∈ secondMobiusIdealDivisors n hn, (mobius d : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (second_mobius_sum_idealDivisors_mobius n hn)
  simpa only [Int.cast_sum, apply_ite, Int.cast_one, Int.cast_zero] using h

/-- All common divisors are actual divisors of the nonzero ideal gcd. -/
def secondMobiusCommonDivisors (a b : Ideal O) (ha : a ≠ ⊥) : Finset (Ideal O) :=
  secondMobiusIdealDivisors (gcd a b) (ne_zero_of_dvd_ne_zero ha (gcd_dvd_left a b))

@[simp] theorem mem_secondMobiusCommonDivisors (a b : Ideal O) (ha : a ≠ ⊥) (d : Ideal O) :
    d ∈ secondMobiusCommonDivisors a b ha ↔ d ∣ a ∧ d ∣ b := by
  rw [secondMobiusCommonDivisors, mem_secondMobiusIdealDivisors, dvd_gcd_iff]

theorem second_mobius_sum_commonDivisors_mobius (a b : Ideal O) (ha : a ≠ ⊥) :
    (∑ d ∈ secondMobiusCommonDivisors a b ha, (mobius d : ℂ)) =
      if IsRelPrime a b then 1 else 0 := by
  rw [secondMobiusCommonDivisors, second_mobius_sum_idealDivisors_mobius_complex]
  have hiff : gcd a b = 1 ↔ IsRelPrime a b :=
    ⟨fun h => gcd_isUnit_iff_isRelPrime.mp (h.symm ▸ isUnit_one),
      fun h => (gcd_isUnit_iff_isRelPrime.mpr h).eq_one⟩
  simp only [hiff]

theorem second_mobius_commonDivisor_mobius_hasFiniteSupport (a b : Ideal O) (ha : a ≠ ⊥) :
    Function.HasFiniteSupport (fun d : Ideal O =>
      if d ∣ a ∧ d ∣ b then (mobius d : ℂ) else 0) := by
  apply (second_mobius_divisors_finite ha).subset
  intro d hd
  by_contra hnot
  change ¬ d ∣ a at hnot
  exact hd (if_neg (fun h => hnot h.1))

theorem second_mobius_tsum_commonDivisors_mobius (a b : Ideal O) (ha : a ≠ ⊥) :
    (∑' d : Ideal O, if d ∣ a ∧ d ∣ b then (mobius d : ℂ) else 0) =
      if IsRelPrime a b then 1 else 0 := by
  rw [tsum_eq_sum (s := secondMobiusCommonDivisors a b ha) (fun d hd =>
    if_neg (fun h => hd ((mem_secondMobiusCommonDivisors a b ha d).mpr h)))]
  calc
    _ = ∑ d ∈ secondMobiusCommonDivisors a b ha, (mobius d : ℂ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact if_pos ((mem_secondMobiusCommonDivisors a b ha d).mp hd)
    _ = _ := second_mobius_sum_commonDivisors_mobius a b ha

def secondMobiusMobiusDivisorAdmissible (c : ArithmeticContext)
    (q : (Ideal O × Ideal O) × Ideal O) : Prop :=
  secondMobiusGcdPairAdmissible c q.1 ∧ q.2 ∣ q.1.1 ∧ q.2 ∣ q.1.2

def secondMobiusMobiusTripleAdmissible (c : ArithmeticContext)
    (t : Ideal O × Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧ SquarefreeOutside c.S t.2.2 ∧
    IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1

abbrev SecondMobiusMobiusDivisorIndices (c : ArithmeticContext) :=
  {q : (Ideal O × Ideal O) × Ideal O // secondMobiusMobiusDivisorAdmissible c q}

abbrev SecondMobiusMobiusTriples (c : ArithmeticContext) :=
  {t : Ideal O × Ideal O × Ideal O // secondMobiusMobiusTripleAdmissible c t}

def secondMobiusMobiusImage (t : Ideal O × Ideal O × Ideal O) :
    (Ideal O × Ideal O) × Ideal O := ((t.1 * t.2.1, t.1 * t.2.2), t.1)

theorem second_mobius_mobius_image_admissible (c : ArithmeticContext)
    {t : Ideal O × Ideal O × Ideal O} (ht : secondMobiusMobiusTripleAdmissible c t) :
    secondMobiusMobiusDivisorAdmissible c (secondMobiusMobiusImage t) := by
  refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _, dvd_mul_right _ _⟩
  · exact ⟨(second_mobius_outside_mul_iff c _ _).mpr ⟨ht.1.1, ht.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨ht.2.2.2.1.symm, ht.1.2, ht.2.1.2⟩⟩
  · exact ⟨(second_mobius_outside_mul_iff c _ _).mpr ⟨ht.1.1, ht.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨ht.2.2.2.2.symm, ht.1.2, ht.2.2.1.2⟩⟩

theorem second_mobius_mobius_image_injOn (c : ArithmeticContext) :
    Set.InjOn secondMobiusMobiusImage {t | secondMobiusMobiusTripleAdmissible c t} := by
  intro t ht s _hs h
  have ht0 : t.1 ≠ 0 := ht.1.1.1
  have hts : t.1 = s.1 := congrArg Prod.snd h
  have hp : (t.1 * t.2.1, t.1 * t.2.2) = (s.1 * s.2.1, s.1 * s.2.2) :=
    congrArg Prod.fst h
  apply Prod.ext hts
  apply Prod.ext
  · apply mul_left_cancel₀ ht0
    simpa only [hts] using congrArg Prod.fst hp
  · apply mul_left_cancel₀ ht0
    simpa only [hts] using congrArg Prod.snd hp

def secondMobiusMobiusReconstruct (c : ArithmeticContext) :
    SecondMobiusMobiusTriples c → SecondMobiusMobiusDivisorIndices c := fun t =>
  ⟨secondMobiusMobiusImage t.1, second_mobius_mobius_image_admissible c t.2⟩

theorem secondMobiusMobiusReconstruct_bijective (c : ArithmeticContext) :
    Function.Bijective (secondMobiusMobiusReconstruct c) := by
  constructor
  · intro t s h
    apply Subtype.ext
    exact second_mobius_mobius_image_injOn c t.2 s.2 (congrArg Subtype.val h)
  · intro q
    obtain ⟨x, hx⟩ := q.2.2.1
    obtain ⟨y, hy⟩ := q.2.2.2
    have ht : SquarefreeOutside c.S q.1.2 :=
      ⟨second_mobius_outside_of_dvd c q.2.1.1.1 q.2.2.1,
        q.2.1.1.2.squarefree_of_dvd q.2.2.1⟩
    have hxdvd : x ∣ q.1.1.1 := ⟨q.1.2, hx.trans (mul_comm _ _)⟩
    have hydvd : y ∣ q.1.1.2 := ⟨q.1.2, hy.trans (mul_comm _ _)⟩
    have hxout : SquarefreeOutside c.S x :=
      ⟨second_mobius_outside_of_dvd c q.2.1.1.1 hxdvd,
        q.2.1.1.2.squarefree_of_dvd hxdvd⟩
    have hyout : SquarefreeOutside c.S y :=
      ⟨second_mobius_outside_of_dvd c q.2.1.2.1 hydvd,
        q.2.1.2.2.squarefree_of_dvd hydvd⟩
    have hxt : IsRelPrime x q.1.2 := (IsRelPrime.of_squarefree_mul (hx ▸ q.2.1.1.2)).symm
    have hyt : IsRelPrime y q.1.2 := (IsRelPrime.of_squarefree_mul (hy ▸ q.2.1.2.2)).symm
    refine ⟨⟨(q.1.2, x, y), ht, hxout, hyout, hxt, hyt⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext (Prod.ext hx.symm hy.symm) rfl

def secondMobiusMobiusEquiv (c : ArithmeticContext) :
    SecondMobiusMobiusTriples c ≃ SecondMobiusMobiusDivisorIndices c :=
  Equiv.ofBijective (secondMobiusMobiusReconstruct c) (secondMobiusMobiusReconstruct_bijective c)

@[simp] theorem secondMobiusMobiusEquiv_apply (c : ArithmeticContext)
    (t : SecondMobiusMobiusTriples c) :
    (secondMobiusMobiusEquiv c t).1 = secondMobiusMobiusImage t.1 := rfl

theorem secondMobiusMobiusEquiv_symm_reconstruct (c : ArithmeticContext)
    (q : SecondMobiusMobiusDivisorIndices c) :
    let t := (secondMobiusMobiusEquiv c).symm q
    t.1.1 = q.1.2 ∧ q.1.1.1 = t.1.1 * t.1.2.1 ∧ q.1.1.2 = t.1.1 * t.1.2.2 := by
  have h := congrArg Subtype.val ((secondMobiusMobiusEquiv c).apply_symm_apply q)
  exact ⟨congrArg Prod.snd h, (congrArg (fun q : (Ideal O × Ideal O) × Ideal O => q.1.1) h).symm,
    (congrArg (fun q : (Ideal O × Ideal O) × Ideal O => q.1.2) h).symm⟩

def secondMobiusMobiusDivisorTerm (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (q : (Ideal O × Ideal O) × Ideal O) : ℂ :=
  if secondMobiusMobiusDivisorAdmissible c q then (mobius q.2 : ℂ) * F q.1 else 0

def secondMobiusMobiusTripleTerm (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if secondMobiusMobiusTripleAdmissible c t then
    (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0

theorem second_mobius_mobius_tripleTerm_eq (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (t : Ideal O × Ideal O × Ideal O) :
    secondMobiusMobiusTripleTerm c F t =
      if SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧
          SquarefreeOutside c.S t.2.2 ∧ IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1
      then (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
  unfold secondMobiusMobiusTripleTerm
  by_cases ht : secondMobiusMobiusTripleAdmissible c t
  · rw [if_pos ht]
    unfold secondMobiusMobiusTripleAdmissible at ht
    rw [if_pos ht]
  · rw [if_neg ht]
    unfold secondMobiusMobiusTripleAdmissible at ht
    rw [if_neg ht]

theorem second_mobius_mobius_divisorTerm_hasFiniteSupport (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (secondMobiusMobiusDivisorTerm c F) := by
  let S := {p : Ideal O × Ideal O | secondMobiusGcdPairAdmissible c p ∧ F p ≠ 0}
  have hS : S.Finite := hF.subset (fun _ hp => hp.2)
  have hfin : (⋃ p ∈ S, ({p} : Set (Ideal O × Ideal O)) ×ˢ
      {d : Ideal O | d ∣ p.1}).Finite := by
    apply hS.biUnion
    intro p hp
    exact (Set.finite_singleton p).prod (second_mobius_divisors_finite hp.1.1.1.1)
  apply hfin.subset
  intro q hq
  have hadm : secondMobiusMobiusDivisorAdmissible c q := by
    by_contra h
    exact hq (if_neg h)
  have hFq : F q.1 ≠ 0 := by
    intro h
    exact hq (by simp only [secondMobiusMobiusDivisorTerm, if_pos hadm, h, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨q.1, ⟨hadm.1, hFq⟩, rfl, hadm.2.1⟩

theorem second_mobius_mobius_divisorTerm_image (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) {t : Ideal O × Ideal O × Ideal O}
    (ht : secondMobiusMobiusTripleAdmissible c t) :
    secondMobiusMobiusDivisorTerm c F (secondMobiusMobiusImage t) =
      secondMobiusMobiusTripleTerm c F t := by
  rw [secondMobiusMobiusDivisorTerm,
    if_pos (second_mobius_mobius_image_admissible c ht),
    secondMobiusMobiusTripleTerm, if_pos ht]
  rfl

theorem second_mobius_mobius_tripleTerm_hasFiniteSupport (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (secondMobiusMobiusTripleTerm c F) := by
  have hadm : ∀ t ∈ Function.support (secondMobiusMobiusTripleTerm c F),
      secondMobiusMobiusTripleAdmissible c t := by
    intro t ht
    by_contra h
    exact ht (if_neg h)
  apply Set.Finite.of_injOn (f := secondMobiusMobiusImage)
    (t := Function.support (secondMobiusMobiusDivisorTerm c F))
  · intro t ht
    rw [Function.mem_support, second_mobius_mobius_divisorTerm_image c F (hadm t ht)]
    exact ht
  · intro t ht s hs h
    exact second_mobius_mobius_image_injOn c (hadm t ht) (hadm s hs) h
  · exact second_mobius_mobius_divisorTerm_hasFiniteSupport c F hF

theorem second_mobius_mobius_divisor_triple_reindex (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) :
    (∑' q : (Ideal O × Ideal O) × Ideal O, secondMobiusMobiusDivisorTerm c F q) =
      ∑' t : Ideal O × Ideal O × Ideal O, secondMobiusMobiusTripleTerm c F t := by
  have hdivIndicator : ({q | secondMobiusMobiusDivisorAdmissible c q}.indicator
      (fun q : (Ideal O × Ideal O) × Ideal O => (mobius q.2 : ℂ) * F q.1)) =
      secondMobiusMobiusDivisorTerm c F := by
    funext q
    exact Set.indicator_apply _ _ _
  have htripleIndicator : ({t | secondMobiusMobiusTripleAdmissible c t}.indicator
      (fun t : Ideal O × Ideal O × Ideal O =>
        (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2))) =
      secondMobiusMobiusTripleTerm c F := by
    funext t
    exact Set.indicator_apply _ _ _
  have hd : (∑' q : SecondMobiusMobiusDivisorIndices c, (mobius q.1.2 : ℂ) * F q.1.1) =
      ∑' q : (Ideal O × Ideal O) × Ideal O, secondMobiusMobiusDivisorTerm c F q := by
    have h := tsum_subtype {q | secondMobiusMobiusDivisorAdmissible c q}
      (fun q : (Ideal O × Ideal O) × Ideal O => (mobius q.2 : ℂ) * F q.1)
    simp_rw [hdivIndicator] at h
    exact h
  have ht : (∑' t : SecondMobiusMobiusTriples c,
      (mobius t.1.1 : ℂ) * F (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2)) =
      ∑' t : Ideal O × Ideal O × Ideal O, secondMobiusMobiusTripleTerm c F t := by
    have h := tsum_subtype {t | secondMobiusMobiusTripleAdmissible c t}
      (fun t : Ideal O × Ideal O × Ideal O =>
        (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2))
    simp_rw [htripleIndicator] at h
    exact h
  exact hd.symm.trans (((secondMobiusMobiusEquiv c).tsum_eq
    (fun q : SecondMobiusMobiusDivisorIndices c => (mobius q.1.2 : ℂ) * F q.1.1)).symm.trans ht)

theorem second_mobius_mobius_remove_pair_coprimality (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    (∑' p : Ideal O × Ideal O,
      if SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧ IsRelPrime p.1 p.2
      then F p else 0) =
    ∑' t : Ideal O × Ideal O × Ideal O,
      if SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧
          SquarefreeOutside c.S t.2.2 ∧ IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1
      then (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
  suffices h : (∑' p : Ideal O × Ideal O,
      if SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧ IsRelPrime p.1 p.2
      then F p else 0) = ∑' t, secondMobiusMobiusTripleTerm c F t by
    simpa only [second_mobius_mobius_tripleTerm_eq] using h
  rw [← second_mobius_mobius_divisor_triple_reindex]
  have hsum : Summable (secondMobiusMobiusDivisorTerm c F) := summable_of_hasFiniteSupport
    (second_mobius_mobius_divisorTerm_hasFiniteSupport c F hF)
  rw [hsum.tsum_prod]
  apply tsum_congr
  intro p
  by_cases hp : secondMobiusGcdPairAdmissible c p
  · have hterm : (fun d : Ideal O => secondMobiusMobiusDivisorTerm c F (p, d)) =
        fun d => (if d ∣ p.1 ∧ d ∣ p.2 then (mobius d : ℂ) else 0) * F p := by
      funext d
      by_cases hd : d ∣ p.1 ∧ d ∣ p.2
      · simp only [secondMobiusMobiusDivisorTerm, secondMobiusMobiusDivisorAdmissible,
          hp, hd, and_self, if_true]
      · simp only [secondMobiusMobiusDivisorTerm, secondMobiusMobiusDivisorAdmissible,
          hp, hd, and_false, if_false, zero_mul]
    rw [hterm, tsum_mul_right, second_mobius_tsum_commonDivisors_mobius p.1 p.2 hp.1.1.1]
    by_cases hrel : IsRelPrime p.1 p.2
    · simp only [hp.1, hp.2, hrel, and_self, if_true, one_mul]
    · simp only [hrel, and_false, if_false, zero_mul]
  · have hnot : ¬ (SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧
        IsRelPrime p.1 p.2) := fun h => hp ⟨h.1, h.2.1⟩
    rw [if_neg hnot]
    simp only [secondMobiusMobiusDivisorTerm, secondMobiusMobiusDivisorAdmissible,
      hp, false_and, ite_false, tsum_zero]

/-- The reindexed series is genuinely finite and hence summable, including
when the original finite support contains a zero ideal. -/
theorem second_mobius_mobius_removed_hasFiniteSupport (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (fun t : Ideal O × Ideal O × Ideal O =>
      if SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧
          SquarefreeOutside c.S t.2.2 ∧ IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1
      then (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0) := by
  have heq := funext (second_mobius_mobius_tripleTerm_eq c F)
  rw [← heq]
  exact second_mobius_mobius_tripleTerm_hasFiniteSupport c F hF

theorem second_mobius_mobius_removed_summable (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Summable (fun t : Ideal O × Ideal O × Ideal O =>
      if SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧
          SquarefreeOutside c.S t.2.2 ∧ IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1
      then (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0) :=
  summable_of_hasFiniteSupport (second_mobius_mobius_removed_hasFiniteSupport c F hF)


def secondMobiusPairKernel (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (U : ℝ → ℂ) (C d g e : Ideal O) (Y ell : ℝ) (h : O)
    (p : Ideal O × Ideal O) : ℂ :=
  coprimeCoefficient c ξ C d e h p.1 * star (coprimeCoefficient c ξ C d e h p.2) *
    secondPoissonKernel Φ U Y ell g e h
      (normIdeal p.1 / (ell / normIdeal g)) (normIdeal p.2 / (ell / normIdeal g))

theorem second_mobius_pairKernel_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {U : ℝ → ℂ} (hU : SmoothSupported I U) (C d g e : Ideal O)
    (Y : ℝ) {ell : ℝ} (hell : 0 < ell) (hg : 0 < normIdeal g) (h : O) :
    Function.HasFiniteSupport (secondMobiusPairKernel c ξ Φ U C d g e Y ell h) := by
  apply ((finite_normIdeal_le (I.hi * (ell / normIdeal g))).prod
    (finite_normIdeal_le (I.hi * (ell / normIdeal g)))).subset
  intro p hp
  have hker : secondPoissonKernel Φ U Y ell g e h
      (normIdeal p.1 / (ell / normIdeal g))
      (normIdeal p.2 / (ell / normIdeal g)) ≠ 0 := by
    intro hz
    exact hp (by simp only [secondMobiusPairKernel, hz, mul_zero])
  have hu1 : U (normIdeal p.1 / (ell / normIdeal g)) ≠ 0 := by
    intro hz
    exact hker (by simp only [secondPoissonKernel, hz, mul_zero, zero_mul])
  have hu2 : U (normIdeal p.2 / (ell / normIdeal g)) ≠ 0 := by
    intro hz
    exact hker (by simp only [secondPoissonKernel, hz, mul_zero, star_zero, zero_mul])
  exact ⟨(div_le_iff₀ (div_pos hell hg)).mp (hU.2 hu1).2,
    (div_le_iff₀ (div_pos hell hg)).mp (hU.2 hu2).2⟩

def secondMobiusRestrictedPair (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (U : ℝ → ℂ) (C d t g e : Ideal O) (Y ell : ℝ) (h : O)
    (p : Ideal O × Ideal O) : ℂ :=
  if IsRelPrime p.1 (g * C * t) ∧ IsRelPrime p.2 (g * C * t) then
    secondMobiusPairKernel c ξ Φ U C d g e Y ell h p else 0

theorem second_mobius_restrictedPair_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {U : ℝ → ℂ} (hU : SmoothSupported I U) (C d t g e : Ideal O)
    (Y : ℝ) {ell : ℝ} (hell : 0 < ell) (hg : 0 < normIdeal g) (h : O) :
    Function.HasFiniteSupport (secondMobiusRestrictedPair c ξ Φ U C d t g e Y ell h) := by
  apply (second_mobius_pairKernel_hasFiniteSupport c ξ I Φ hU C d g e Y hell hg h).subset
  intro p hp hz
  exact hp (by simp only [secondMobiusRestrictedPair, hz, ite_self])

/-- Exact actual-column Möbius insertion and z_i=w*n_i, with genuine finite
support on both the original pair and the new triple before rearrangement. -/
theorem second_mobius_coprime_columns_reindex (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {U : ℝ → ℂ} (hU : SmoothSupported I U) (C d t g e : Ideal O)
    (Y : ℝ) {ell : ℝ} (hell : 0 < ell) (hg : 0 < normIdeal g) (h : O) :
    (∑' n₁ : Ideal O, if SquarefreeOutside c.S n₁ ∧ IsRelPrime n₁ (g * C * t) then
      ∑' n₂ : Ideal O, if SquarefreeOutside c.S n₂ ∧ IsRelPrime n₂ (g * C * t) ∧
          IsRelPrime n₁ n₂ then
        secondMobiusPairKernel c ξ Φ U C d g e Y ell h (n₁,n₂) else 0 else 0) =
    ∑' w : Ideal O, ∑' x : Ideal O, ∑' y : Ideal O,
      if SquarefreeOutside c.S w ∧ SquarefreeOutside c.S x ∧
          SquarefreeOutside c.S y ∧ IsRelPrime x w ∧ IsRelPrime y w then
        (mobius w : ℂ) * secondMobiusRestrictedPair c ξ Φ U C d t g e Y ell h
          (w * x, w * y) else 0 := by
  let P := secondMobiusRestrictedPair c ξ Φ U C d t g e Y ell h
  have hP := second_mobius_restrictedPair_hasFiniteSupport c ξ I Φ hU C d t g e Y hell hg h
  have hleft : Function.HasFiniteSupport (fun p : Ideal O × Ideal O =>
      if SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧ IsRelPrime p.1 p.2
      then P p else 0) := by
    apply hP.subset
    intro p hp hz
    change P p = 0 at hz
    exact hp (by simp only [hz, ite_self])
  have hl := (summable_of_hasFiniteSupport hleft).tsum_prod
  have heq : (∑' n₁ : Ideal O, if SquarefreeOutside c.S n₁ ∧ IsRelPrime n₁ (g * C * t) then
      ∑' n₂ : Ideal O, if SquarefreeOutside c.S n₂ ∧ IsRelPrime n₂ (g * C * t) ∧
          IsRelPrime n₁ n₂ then
        secondMobiusPairKernel c ξ Φ U C d g e Y ell h (n₁,n₂) else 0 else 0) =
      ∑' p : Ideal O × Ideal O,
        if SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧ IsRelPrime p.1 p.2
        then P p else 0 := by
    have hpoint (x y : Ideal O) :
        (if SquarefreeOutside c.S x ∧ SquarefreeOutside c.S y ∧ IsRelPrime x y
          then P (x,y) else 0) =
        if SquarefreeOutside c.S x ∧ IsRelPrime x (g * C * t) then
          (if SquarefreeOutside c.S y ∧ IsRelPrime y (g * C * t) ∧ IsRelPrime x y then
            secondMobiusPairKernel c ξ Φ U C d g e Y ell h (x,y) else 0) else 0 := by
      dsimp only [P, secondMobiusRestrictedPair]
      by_cases px : SquarefreeOutside c.S x <;>
        by_cases py : SquarefreeOutside c.S y <;>
        by_cases rx : IsRelPrime x (g * C * t) <;>
        by_cases ry : IsRelPrime y (g * C * t) <;> by_cases xy : IsRelPrime x y <;>
        simp only [px,py,rx,ry,xy,and_true,and_false,true_and,false_and,ite_true,ite_false]
    rw [hl]
    simp_rw [hpoint]
    apply tsum_congr
    intro x
    by_cases hx : SquarefreeOutside c.S x ∧ IsRelPrime x (g * C * t)
    · simp only [if_pos hx]
    · simp only [if_neg hx, tsum_zero]
  rw [heq, second_mobius_mobius_remove_pair_coprimality c P hP]
  have hs := second_mobius_mobius_removed_summable c P hP
  rw [hs.tsum_prod]
  apply tsum_congr
  intro w
  exact (hs.prod_factor w).tsum_prod


theorem secondMobiusSexticSymbol_eq_zero_of_nonunit (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (a : O)
    (ha : ¬ IsUnit (Ideal.Quotient.mk n a)) : sexticSymbol n a = 0 := by
  have hproper : principal a ⊔ n ≠ ⊤ := by
    intro htop
    have hone : (1 : O) ∈ principal a ⊔ n := htop ▸ Submodule.mem_top
    obtain ⟨u, b, hb, heq⟩ := Ideal.mem_span_singleton_sup.mp hone
    apply ha
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk n u, ?_⟩
    have heq' := congrArg (Ideal.Quotient.mk n) heq
    simpa only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero] using heq'
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal (principal a ⊔ n) hproper
  have hnP : n ≤ P := le_trans le_sup_right hle
  have hPzero : P ≠ ⊥ := by
    intro hP
    apply hn.1
    exact le_antisymm (hP ▸ hnP) bot_le
  have hP : Prime P := Ideal.prime_of_isPrime hPzero hPmax.isPrime
  have hPmem : P ∈ normalizedFactors n :=
    (mem_normalizedFactors_iff hn.1).mpr ⟨hP, Ideal.dvd_iff_le.mpr hnP⟩
  have haP : a ∈ P := (le_trans le_sup_left hle) (Ideal.mem_span_singleton_self a)
  simp only [sexticSymbol, ite_eq_right hn.1]
  apply Multiset.prod_eq_zero
  apply Multiset.mem_map.mpr
  refine ⟨P, hPmem, ?_⟩
  exact SquarefreeReflection.sexticAtPrime_zero_of_mem hP
    (SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
      c hP (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors
        hn hPmem)) haP

theorem second_mobius_isUnit_mk_iff_isRelPrime (n : Ideal O) (z : O) :
    IsUnit (Ideal.Quotient.mk n z) ↔ IsRelPrime (principal z) n := by
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hz
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hmem : z * t - 1 ∈ n := Ideal.Quotient.eq.mp (by
      simpa only [map_mul, map_one] using hv)
    have hzt : z * t ∈ principal z :=
      (principal z).mul_mem_right t (Ideal.mem_span_singleton_self z)
    have hone : (1 : O) ∈ principal z ⊔ n := by
      have h := (principal z ⊔ n).sub_mem
        ((show principal z ≤ principal z ⊔ n from le_sup_left) hzt)
        ((show n ≤ principal z ⊔ n from le_sup_right) hmem)
      convert h using 1 <;> ring
    exact (Ideal.isCoprime_iff_sup_eq.mpr ((Ideal.eq_top_iff_one _).mpr hone)).isRelPrime
  · intro hrel
    have hcop : IsCoprime (principal z) n := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      exact Ideal.isUnit_iff.mp (hrel
        (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hx
    have h := congrArg (Ideal.Quotient.mk n) hxy
    simp only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] at h
    exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk n t, h⟩

theorem second_mobius_sexticSymbol_zero_of_not_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : ¬ IsRelPrime (principal z) n) : sexticSymbol n z = 0 := by
  apply secondMobiusSexticSymbol_eq_zero_of_nonunit c hn z
  exact fun h => hz ((second_mobius_isUnit_mk_iff_isRelPrime n z).mp h)

theorem second_mobius_sexticAtPrime_pow_six_of_not_mem (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) (z : O) (hz : z ∉ P) :
    sexticAtPrime P z ^ (6 : ℕ) = 1 := by
  have hζ := SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
    c hP hout
  obtain ⟨j, hj, htest⟩ := SquarefreeReflection.sexticAtPrime_index hP hζ hz
  rw [SquarefreeReflection.RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj htest,
    embedding_pow, ← pow_mul, Nat.mul_comm j 6, pow_mul,
    ← embedding_pow, rootSix_pow_six, embedding_one, one_pow]

theorem second_mobius_sexticSymbol_pow_six_of_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : IsRelPrime (principal z) n) : sexticSymbol n z ^ (6 : ℕ) = 1 := by
  simp only [sexticSymbol, ite_eq_right hn.1]
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro w hw
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hw
  have hprime := prime_of_normalized_factor P hP
  have hzP : z ∉ P := by
    intro hzP
    exact hprime.not_isUnit (hz (Ideal.dvd_span_singleton.mpr hzP)
      (dvd_of_mem_normalizedFactors hP))
  exact second_mobius_sexticAtPrime_pow_six_of_not_mem c hprime
    (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors hn hP) z hzP

theorem second_mobius_sexticSymbol_norm_of_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : IsRelPrime (principal z) n) : ‖sexticSymbol n z‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one
    (second_mobius_sexticSymbol_pow_six_of_isRelPrime c hn z hz) (by decide)

/-- The literal product with its complex conjugate is the exact coprimality
filter, including the modulus-one quotient. -/
theorem second_mobius_sexticSymbol_mul_star (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O) :
    sexticSymbol n z * star (sexticSymbol n z) =
      if IsRelPrime (principal z) n then 1 else 0 := by
  by_cases hz : IsRelPrime (principal z) n
  · rw [ite_eq_left hz]
    simpa only [starRingEnd_apply, second_mobius_sexticSymbol_norm_of_isRelPrime c hn z hz,
      one_pow, Complex.ofReal_one] using Complex.mul_conj' (sexticSymbol n z)
  · rw [ite_eq_right hz, second_mobius_sexticSymbol_zero_of_not_isRelPrime c hn z hz,
      star_zero, zero_mul]

theorem second_mobius_sexticSymbol_mul (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, sexticSymbol]
  by_cases hb : b = ⊥
  · simp [hb, sexticSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]



open SquarefreeReflection.RayValuePrerequisites

theorem second_mobius_primaryGenerator_spec_and_primary_outside (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) :
    principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) :=
  primaryGenerator_spec_outside c ha

theorem second_mobius_isPrimary_mul {a b : O} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  apply (isPrimary_iff_three_dvd _).mpr
  have h := dvd_add (dvd_mul_of_dvd_left ((isPrimary_iff_three_dvd a).mp ha) b)
    ((isPrimary_iff_three_dvd b).mp hb)
  convert h using 1 <;> ring

/-- The frozen primary condition removes every unit ambiguity. -/
theorem second_mobius_isPrimary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) :
    u = 1 := by
  have hthree := (isPrimary_iff_three_dvd (u : O)).mp hu
  have hlambda : (omega - 1) ^ (2 : ℕ) ∣ (3 : O) := by
    refine ⟨-omega ^ (2 : ℕ), ?_⟩
    rw [omega_sub_one_sq]
    calc
      (3 : O) = 3 * omega ^ (3 : ℕ) := by rw [omega_cube, mul_one]
      _ = -3 * omega * -omega ^ (2 : ℕ) := by ring
  have hcong : ∃ n : ℤ, (omega - 1) ^ (2 : ℕ) ∣ ((u : O) - n) :=
    ⟨1, by simpa only [Int.cast_one] using hlambda.trans hthree⟩
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u hcong with h | h
  · exact h
  · exfalso
    have hneg : omega - 1 ∣ (-1 : O) - 1 := by
      simpa only [h, Units.val_neg, Units.val_one] using
        omega_sub_one_dvd_three.trans hthree
    apply omega_sub_one_prime.not_dvd_one
    convert dvd_add omega_sub_one_dvd_three hneg using 1 <;> ring

theorem second_mobius_primary_eq_of_principal_eq {a b : O}
    (ha : IsPrimary a) (hb : IsPrimary b) (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [second_mobius_isPrimary_unit_eq_one u hup, Units.val_one, mul_one] using hu

@[simp] theorem second_mobius_primaryGenerator_one : primaryGenerator 1 = 1 := by
  have h : ∃ z : O, principal z = 1 ∧ IsPrimary z :=
    ⟨1, by simp [principal], by simp [IsPrimary]⟩
  have hs : principal (primaryGenerator 1) = 1 ∧ IsPrimary (primaryGenerator 1) := by
    simpa only [primaryGenerator, dite_eq_left h] using Classical.choose_spec h
  exact second_mobius_primary_eq_of_principal_eq hs.2 (by simp [IsPrimary])
    (hs.1.trans (by simp [principal]))

theorem second_mobius_primaryGenerator_mul_outside (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) :
    primaryGenerator (a * b) = primaryGenerator a * primaryGenerator b := by
  have ha' := second_mobius_primaryGenerator_spec_and_primary_outside c ha
  have hb' := second_mobius_primaryGenerator_spec_and_primary_outside c hb
  have hab' := second_mobius_primaryGenerator_spec_and_primary_outside c
    ((second_mobius_outside_mul_iff c a b).mpr ⟨ha, hb⟩)
  apply second_mobius_primary_eq_of_principal_eq hab'.2
    (second_mobius_isPrimary_mul ha'.2 hb'.2)
  rw [hab'.1]
  change a * b = Ideal.span {primaryGenerator a * primaryGenerator b}
  rw [← Ideal.span_singleton_mul_span_singleton]
  change a * b = principal (primaryGenerator a) * principal (primaryGenerator b)
  rw [ha'.1, hb'.1]

theorem second_mobius_primaryGenerator_ne_zero (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) : primaryGenerator n ≠ 0 := by
  intro hz
  apply hn.1
  rw [← (second_mobius_primaryGenerator_spec_and_primary_outside c hn).1, hz]
  simp [principal]

theorem second_mobius_norm_alpha_eq_one (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : ‖alpha n‖ = 1 := by
  have h : embedding (primaryGenerator n) ≠ 0 :=
    fun hz => second_mobius_primaryGenerator_ne_zero c hn (embedding_eq_zero.mp hz)
  simp only [alpha, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]

theorem second_mobius_mobius_sq {n : Ideal O} (hn : Squarefree n) :
    (mobius n : ℂ) ^ 2 = 1 := by
  simp [mobius, hn.moebius_eq, ← pow_mul, Nat.mul_comm]

theorem second_mobius_norm_mobius_eq_one {n : Ideal O} (hn : Squarefree n) :
    ‖(mobius n : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (second_mobius_mobius_sq hn) (by decide)

theorem second_mobius_norm_gauss_two (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {n : Ideal O} (hn : SquarefreeOutside c.S n) :
    ‖gauss 2 n‖ = 1 := by
  obtain ⟨G, R, _, _, _, _, _, _, _, hgauss, _, _⟩ := hc
  have h := congrArg norm (hgauss n hn).1
  rw [norm_pow, norm_mul, second_mobius_norm_mobius_eq_one hn.2,
    second_mobius_norm_alpha_eq_one c hn.1, mul_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    (h.trans (one_pow 3).symm)

theorem second_mobius_norm_rayValue (c : ArithmeticContext) (ξ : RayCharacter c)
    {n : Ideal O} (hn : Outside c.S n) : ‖rayValue ξ.val n‖ = 1 := by
  have hu : IsUnit (Ideal.Quotient.mk ξ.val.modulus (primaryGenerator n)) := by
    rw [ξ.property]
    exact SquarefreeReflection.primaryGenerator_unit_mod_supported c c.rayModulus
      c.rayModulus_ne_bot c.ray_supported hn
  letI : Finite (O ⧸ ξ.val.modulus) := Ring.HasFiniteQuotients.finiteQuotient ξ.val.modulus_ne_bot
  letI : Fintype (O ⧸ ξ.val.modulus) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hu
  have hnorm := Complex.norm_eq_one_of_mem_rootsOfUnity
    (ξ.val.residue.apply_mem_rootsOfUnity u)
  simpa only [MulChar.coe_equivToUnitHom, rayValue, HeckeCharacter.onElement, hu] using hnorm

theorem second_mobius_coefficient_mul_star (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {n : Ideal O}
    (hn : SquarefreeOutside c.S n) : coefficient ξ.val n * star (coefficient ξ.val n) = 1 := by
  have hnrm : ‖coefficient ξ.val n‖ = 1 := by
    simp only [coefficient, norm_mul, norm_star,
      second_mobius_norm_alpha_eq_one c hn.1, second_mobius_norm_gauss_two c hc hn,
      second_mobius_norm_rayValue c ξ hn.1, one_mul]
  simpa only [starRingEnd_apply, hnrm, one_pow, Complex.ofReal_one] using
    Complex.mul_conj' (coefficient ξ.val n)

/-- The literal column coefficient after splitting z=w*n, retaining the
common coefficient for its exact unit/zero cancellation. -/
theorem second_mobius_coprimeCoefficient_mul (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) (C d e : Ideal O) (h : O)
    {w n : Ideal O} (hw : SquarefreeOutside c.S w) (hn : SquarefreeOutside c.S n)
    (hwn : IsRelPrime w n) (hCe : Outside c.S (C * e)) :
    coprimeCoefficient c ξ C d e h (w * n) =
      coprimeCoefficient c ξ C d e h w *
        (coefficient ξ.val n * sexticSymbol n (primaryGenerator (d * e) * h) *
          sexticSymbol n (primaryGenerator (C * e * w)) ^ (4 : ℕ)) := by
  obtain ⟨G,R,hG,hR,hRs,hR1,hR2,hGm,hrec,hgauss,hcoeff,hother⟩ := hc
  simp only [coprimeCoefficient, hcoeff ξ w n hw hn hwn, second_mobius_sexticSymbol_mul,
    second_mobius_primaryGenerator_mul_outside c hCe hw.1,
    SquarefreeReflection.sexticSymbol_mul_numerator c hn.1, mul_pow]
  ring

theorem second_mobius_coprimeCoefficient_mul_star (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {C d t g e w : Ideal O}
    (hC : Outside c.S C) (hg : Outside c.S g) (hw : SquarefreeOutside c.S w)
    (hd : d ∣ C) (he : e ∣ g) (hwout : IsRelPrime w (g * C * t)) (h : O) :
    coprimeCoefficient c ξ C d e h w * star (coprimeCoefficient c ξ C d e h w) =
      if IsRelPrime (principal h) w then 1 else 0 := by
  have hdout := second_mobius_outside_of_dvd c hC hd
  have heout := second_mobius_outside_of_dvd c hg he
  have hde := (second_mobius_outside_mul_iff c d e).mpr ⟨hdout,heout⟩
  have hCe := (second_mobius_outside_mul_iff c C e).mpr ⟨hC,heout⟩
  have hwgc := (IsRelPrime.mul_right_iff.mp hwout).1
  have hwg := (IsRelPrime.mul_right_iff.mp hwgc).1
  have hwC := (IsRelPrime.mul_right_iff.mp hwgc).2
  have hwd := hwC.of_dvd_right hd
  have hwe := hwg.of_dvd_right he
  have hA : principal (primaryGenerator (d * e) * h) = d * e * principal h := by
    rw [show principal (primaryGenerator (d * e) * h) =
      principal (primaryGenerator (d * e)) * principal h from
        (Ideal.span_singleton_mul_span_singleton _ _).symm,
      (second_mobius_primaryGenerator_spec_and_primary_outside c hde).1]
  have hB := (second_mobius_primaryGenerator_spec_and_primary_outside c hCe).1
  have hrelA : IsRelPrime (principal (primaryGenerator (d * e) * h)) w ↔
      IsRelPrime (principal h) w := by
    rw [hA, IsRelPrime.mul_left_iff, IsRelPrime.mul_left_iff]
    simp only [hwd.symm, hwe.symm, true_and]
  have hrelB : IsRelPrime (principal (primaryGenerator (C * e))) w := by
    rw [hB]
    exact (hwC.mul_right hwe).symm
  simp only [coprimeCoefficient, star_mul, star_pow]
  calc
    _ = (coefficient ξ.val w * star (coefficient ξ.val w)) *
        (sexticSymbol w (primaryGenerator (d * e) * h) *
          star (sexticSymbol w (primaryGenerator (d * e) * h))) *
        (sexticSymbol w (primaryGenerator (C * e)) *
          star (sexticSymbol w (primaryGenerator (C * e)))) ^ (4 : ℕ) := by ring
    _ = _ := by
      rw [second_mobius_coefficient_mul_star c hc ξ hw,
        second_mobius_sexticSymbol_mul_star c hw.1,
        second_mobius_sexticSymbol_mul_star c hw.1,
        if_pos hrelB, hrelA]
      simp only [one_pow, one_mul, mul_one]

def secondMobiusRawCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d e w : Ideal O) (h : O) (n : Ideal O) : ℂ :=
  coefficient ξ.val n * sexticSymbol n (primaryGenerator (d * e) * h) *
    sexticSymbol n (primaryGenerator (C * e * w)) ^ (4 : ℕ)

/-- The numerator of the actual transformed coefficient enforces every
C,e,w exclusion that is absent from its explicit quotientIdeal filter. -/
theorem second_mobius_rawCoefficient_coprime (c : ArithmeticContext)
    (ξ : RayCharacter c) {C d e w n : Ideal O} (h : O)
    (hn : Outside c.S n) (hCew : Outside c.S (C * e * w))
    (hne : secondMobiusRawCoefficient c ξ C d e w h n ≠ 0) :
    IsRelPrime n (C * e * w) := by
  by_contra hr
  have hs : sexticSymbol n (primaryGenerator (C * e * w)) = 0 := by
    apply second_mobius_sexticSymbol_zero_of_not_isRelPrime c hn
    rw [(second_mobius_primaryGenerator_spec_and_primary_outside c hCew).1]
    exact fun hh => hr hh.symm
  exact hne (by simp only [secondMobiusRawCoefficient, hs, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero])

theorem second_mobius_quotientIdeal_spec {g e : Ideal O} (he : e ∣ g) :
    g = e * quotientIdeal g e := by
  simpa only [quotientIdeal, dif_pos he] using Classical.choose_spec he

/-- Precise replacement of all pre-Möbius column exclusions by the literal
post-Möbius quotientIdeal exclusion. -/
theorem second_mobius_rawCoefficient_filter (c : ArithmeticContext)
    (ξ : RayCharacter c) {C d t g e w n : Ideal O} (h : O)
    (hn : Outside c.S n) (hCew : Outside c.S (C * e * w)) (he : e ∣ g) :
    (if IsRelPrime n w ∧ IsRelPrime n (g * C * t) then
      secondMobiusRawCoefficient c ξ C d e w h n else 0) =
        secondPoissonCoefficient c ξ C d t g e w h n := by
  change (if IsRelPrime n w ∧ IsRelPrime n (g * C * t) then
      secondMobiusRawCoefficient c ξ C d e w h n else 0) =
    if IsRelPrime n (t * quotientIdeal g e) then
      secondMobiusRawCoefficient c ξ C d e w h n else 0
  by_cases hz : secondMobiusRawCoefficient c ξ C d e w h n = 0
  · simp only [hz, ite_self]
  have hc := second_mobius_rawCoefficient_coprime c ξ h hn hCew hz
  have hCe := (IsRelPrime.mul_right_iff.mp hc).1
  have hC := (IsRelPrime.mul_right_iff.mp hCe).1
  have he' := (IsRelPrime.mul_right_iff.mp hCe).2
  have hw := (IsRelPrime.mul_right_iff.mp hc).2
  have hi : (IsRelPrime n w ∧ IsRelPrime n (g * C * t)) ↔
      IsRelPrime n (t * quotientIdeal g e) := by
    conv_lhs => rw [second_mobius_quotientIdeal_spec he]
    simp only [IsRelPrime.mul_right_iff]
    simp only [hw, hC, he', true_and, and_true, and_comm]
  simp only [hi]

theorem second_mobius_kernel_sample_mul (Φ : RowWeight) (U : ℝ → ℂ)
    (C d g e w x y : Ideal O) (Y ell : ℝ) (h : O) :
    secondPoissonKernel Φ U Y ell g e h
      (normIdeal (w * x) / (ell / normIdeal g))
      (normIdeal (w * y) / (ell / normIdeal g)) =
    secondPoissonKernel Φ U Y ell g e h
      (normIdeal x / (ell / normIdeal (g * w)))
      (normIdeal y / (ell / normIdeal (g * w))) := by
  have hcoord (n : Ideal O) : normIdeal (w * n) / (ell / normIdeal g) =
      normIdeal n / (ell / normIdeal (g * w)) := by
    simp only [normIdeal_mul, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hcoord x,hcoord y]

/-- Pointwise cancellation at an inserted common squarefree ideal. -/
theorem second_mobius_pair_common_factor (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) (Φ : RowWeight) (U : ℝ → ℂ)
    {C d t g e w x y : Ideal O} (hC : Outside c.S C) (hg : Outside c.S g)
    (hw : SquarefreeOutside c.S w) (hx : SquarefreeOutside c.S x)
    (hy : SquarefreeOutside c.S y) (hd : d ∣ C) (he : e ∣ g)
    (Y ell : ℝ) (h : O) :
    (if IsRelPrime x w ∧ IsRelPrime y w then
      secondMobiusRestrictedPair c ξ Φ U C d t g e Y ell h (w * x,w * y) else 0) =
    if IsRelPrime w (g * C * t * principal h) then
      secondPoissonCoefficient c ξ C d t g e w h x *
        star (secondPoissonCoefficient c ξ C d t g e w h y) *
        secondPoissonKernel Φ U Y ell g e h
          (normIdeal x / (ell / normIdeal (g * w)))
          (normIdeal y / (ell / normIdeal (g * w))) else 0 := by
  have heout := second_mobius_outside_of_dvd c hg he
  have hCe := (second_mobius_outside_mul_iff c C e).mpr ⟨hC,heout⟩
  have hCew := (second_mobius_outside_mul_iff c (C * e) w).mpr ⟨hCe,hw.1⟩
  rw [← second_mobius_rawCoefficient_filter c ξ h hx.1 hCew he,
    ← second_mobius_rawCoefficient_filter c ξ h hy.1 hCew he]
  by_cases hwgt : IsRelPrime w (g * C * t)
  · by_cases hxw : IsRelPrime x w
    · by_cases hyw : IsRelPrime y w
      · by_cases hxgt : IsRelPrime x (g * C * t)
        · by_cases hygt : IsRelPrime y (g * C * t)
          · simp only [secondMobiusRestrictedPair, secondMobiusPairKernel,
              IsRelPrime.mul_left_iff, hwgt, hxgt, hygt, hxw, hyw, and_self,
              ite_true, second_mobius_coprimeCoefficient_mul c hc ξ C d e h hw hx hxw.symm hCe,
              second_mobius_coprimeCoefficient_mul c hc ξ C d e h hw hy hyw.symm hCe,
              star_mul]
            rw [second_mobius_kernel_sample_mul Φ U C d g e w x y Y ell h]
            have hcomm := second_mobius_coprimeCoefficient_mul_star c hc ξ hC hg hw hd he hwgt h
            have hr : IsRelPrime w (g * C * t * principal h) ↔ IsRelPrime (principal h) w := by
              rw [IsRelPrime.mul_right_iff]
              simp only [hwgt,true_and, isRelPrime_comm]
            rw [hr]
            calc
              _ = (coprimeCoefficient c ξ C d e h w * star (coprimeCoefficient c ξ C d e h w)) *
                (secondMobiusRawCoefficient c ξ C d e w h x *
                  star (secondMobiusRawCoefficient c ξ C d e w h y) *
                    secondPoissonKernel Φ U Y ell g e h
                      (normIdeal x / (ell / normIdeal (g * w)))
                      (normIdeal y / (ell / normIdeal (g * w)))) := by
                    simp only [secondMobiusRawCoefficient,star_mul]
                    ring
              _ = _ := by rw [hcomm]; split_ifs <;> simp only [one_mul, zero_mul]
          · simp only [secondMobiusRestrictedPair, IsRelPrime.mul_left_iff, hwgt,
              hxgt, hygt, hxw, hyw, and_self, and_true, and_false, false_and,
              ite_false, ite_true, star_zero, mul_zero, zero_mul, ite_self]
        · simp only [secondMobiusRestrictedPair, IsRelPrime.mul_left_iff, hwgt,
            hxgt, hxw, hyw, and_self, and_true, and_false, false_and,
            ite_false, ite_true, zero_mul, ite_self]
      · simp only [hyw, and_false, false_and, ite_false, star_zero, mul_zero, zero_mul, ite_self]
    · simp only [hxw, false_and, ite_false, zero_mul, ite_self]
  · have hnot : ¬ IsRelPrime w (g * C * t * principal h) :=
      fun hrel => hwgt (IsRelPrime.mul_right_iff.mp hrel).1
    rw [if_neg hnot]
    simp only [secondMobiusRestrictedPair, IsRelPrime.mul_left_iff,
      hwgt, false_and, ite_false, ite_self]

def secondMobiusDualColumns (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (U : ℝ → ℂ) (C d t g e w : Ideal O) (Y ell : ℝ) (h : O) : ℂ :=
  ∑' x : Ideal O, if SquarefreeOutside c.S x then
    ∑' y : Ideal O, if SquarefreeOutside c.S y then
      secondPoissonCoefficient c ξ C d t g e w h x *
        star (secondPoissonCoefficient c ξ C d t g e w h y) *
        secondPoissonKernel Φ U Y ell g e h
          (normIdeal x / (ell / normIdeal (g * w)))
          (normIdeal y / (ell / normIdeal (g * w))) else 0 else 0

/-- Exact Möbius substitution for the actual entire column pair, before the
outer w/h/character permutation and the Fourier cutoff. -/
theorem second_mobius_columns_eq (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {U : ℝ → ℂ} (hU : SmoothSupported I U) {C d t g e : Ideal O}
    (hC : Outside c.S C) (hg : Outside c.S g) (hd : d ∣ C) (he : e ∣ g)
    (Y : ℝ) {ell : ℝ} (hell : 0 < ell) (h : O) :
    (∑' n₁ : Ideal O, if SquarefreeOutside c.S n₁ ∧ IsRelPrime n₁ (g * C * t) then
      ∑' n₂ : Ideal O, if SquarefreeOutside c.S n₂ ∧ IsRelPrime n₂ (g * C * t) ∧
          IsRelPrime n₁ n₂ then
        secondMobiusPairKernel c ξ Φ U C d g e Y ell h (n₁,n₂) else 0 else 0) =
    ∑' w : Ideal O, if SquarefreeOutside c.S w ∧ IsRelPrime w (g * C * t * principal h) then
      (mobius w : ℂ) * secondMobiusDualColumns c ξ Φ U C d t g e w Y ell h else 0 := by
  rw [second_mobius_coprime_columns_reindex c ξ I Φ hU C d t g e Y hell (normIdeal_pos hg.1) h]
  apply tsum_congr
  intro w
  by_cases hw : SquarefreeOutside c.S w
  · have hpoint (x y : Ideal O) :
        (if SquarefreeOutside c.S w ∧ SquarefreeOutside c.S x ∧ SquarefreeOutside c.S y ∧
          IsRelPrime x w ∧ IsRelPrime y w then
            (mobius w : ℂ) * secondMobiusRestrictedPair c ξ Φ U C d t g e Y ell h
              (w*x,w*y) else 0) =
        if IsRelPrime w (g*C*t*principal h) then
          (mobius w : ℂ) * (if SquarefreeOutside c.S x then
            if SquarefreeOutside c.S y then
              secondPoissonCoefficient c ξ C d t g e w h x *
                star (secondPoissonCoefficient c ξ C d t g e w h y) *
                secondPoissonKernel Φ U Y ell g e h
                  (normIdeal x / (ell / normIdeal (g*w)))
                  (normIdeal y / (ell / normIdeal (g*w))) else 0 else 0) else 0 := by
      by_cases hx : SquarefreeOutside c.S x
      · by_cases hy : SquarefreeOutside c.S y
        · have hp := second_mobius_pair_common_factor c hc ξ Φ U (t := t) hC hg hw hx hy hd he Y ell h
          simpa only [hw,hx,hy,true_and,ite_true, mul_ite,mul_zero] using
            congrArg (fun z : ℂ => (mobius w : ℂ) * z) hp
        · simp only [hw,hx,hy,and_false,false_and,true_and,ite_false,mul_zero,ite_self]
      · simp only [hw,hx,false_and,true_and,ite_false,mul_zero,ite_self]
    simp_rw [hpoint]
    by_cases hrel : IsRelPrime w (g*C*t*principal h)
    · simp only [hw,hrel,and_self,ite_true, secondMobiusDualColumns, tsum_mul_left]
      congr 1
      apply tsum_congr
      intro x
      by_cases hx : SquarefreeOutside c.S x
      · simp only [if_pos hx]
      · simp only [if_neg hx,tsum_zero]
    · simp only [hw,hrel,and_false,ite_false,tsum_zero]
  · simp only [hw,false_and,ite_false,tsum_zero]

/-- Fourier support truncates every literal sampled kernel, with no convergence assumption. -/
theorem second_mobius_kernel_zero_of_frequency (I : SupportInterval) (Φ : RowWeight)
    {U : ℝ → ℂ} (hU : SmoothSupported I U) {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell)
    {g e : Ideal O} (hg : g ≠ ⊥) (he : e ≠ ⊥) (h : O) (x y : ℝ)
    (hh : Φ.fourierCap * I.hi ^ 2 * ell ^ 2 * normIdeal e /
      (Y * normIdeal g ^ 2) < normElement h) :
    secondPoissonKernel Φ U Y ell g e h x y = 0 := by
  by_cases hx : x ∈ Set.Icc I.lo I.hi
  · by_cases hy : y ∈ Set.Icc I.lo I.hi
    · exact secondPoissonKernel_eq_zero_of_frequency_gt I Φ U Y ell g e h x y hY hell
        (normIdeal_pos hg) (normIdeal_pos he) hx hy hh
    · exact secondPoissonKernel_eq_zero_of_x₂_not_mem I Φ U Y ell g e h x y hU hy
  · exact secondPoissonKernel_eq_zero_of_x₁_not_mem I Φ U Y ell g e h x y hU hx

theorem second_mobius_dualColumns_zero_of_frequency (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {U : ℝ → ℂ} (hU : SmoothSupported I U) (C d t w : Ideal O)
    {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) {g e : Ideal O}
    (hg : g ≠ ⊥) (he : e ≠ ⊥) (h : O)
    (hh : Φ.fourierCap * I.hi ^ 2 * ell ^ 2 * normIdeal e /
      (Y * normIdeal g ^ 2) < normElement h) :
    secondMobiusDualColumns c ξ Φ U C d t g e w Y ell h = 0 := by
  simp only [secondMobiusDualColumns,
    second_mobius_kernel_zero_of_frequency I Φ hU hY hell hg he h _ _ hh,
    mul_zero, ite_self, tsum_zero]

/-- A nonzero sampled column forces the exact common-ideal support cutoff. -/
theorem second_mobius_dualColumns_zero_of_outer (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {U : ℝ → ℂ} (hU : SmoothSupported I U) (C d t e : Ideal O)
    {Y ell : ℝ} (hell : 0 < ell) {g w : Ideal O}
    (hg : g ≠ ⊥) (hw : w ≠ ⊥) (h : O)
    (houter : I.hi * ell < normIdeal (g * w)) :
    secondMobiusDualColumns c ξ Φ U C d t g e w Y ell h = 0 := by
  have hgw : 0 < normIdeal (g*w) := by rw [normIdeal_mul]; exact mul_pos (normIdeal_pos hg) (normIdeal_pos hw)
  have hsample (x : Ideal O) (hx : SquarefreeOutside c.S x) :
      U (normIdeal x / (ell / normIdeal (g*w))) = 0 := by
    by_contra hu
    have hupper := (div_le_iff₀ (div_pos hell hgw)).mp (hU.2 hu).2
    have hxone : 1 ≤ normIdeal x := by
      change (1 : ℝ) ≤ (x.absNorm : ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun h => hx.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hb : 1 ≤ I.hi * ell / normIdeal (g*w) := by
      simpa only [mul_div_assoc] using hxone.trans hupper
    have hc := (le_div_iff₀ hgw).mp hb
    linarith
  unfold secondMobiusDualColumns
  calc
    _ = ∑' _x : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro x
      by_cases hx : SquarefreeOutside c.S x
      · simp only [if_pos hx,secondPoissonKernel,hsample x hx,mul_zero,zero_mul,ite_self,tsum_zero]
      · exact if_neg hx
    _ = 0 := tsum_zero

def secondMobiusJointTerm (c : ArithmeticContext) (coeffs : RayCharacter c → ℂ)
    (Φ : RowWeight) (U : ℝ → ℂ) (C d t g e : Ideal O) (Y ell : ℝ)
    (p : Ideal O × O × RayCharacter c) : ℂ :=
  if SquarefreeOutside c.S p.1 ∧ p.2.1 ≠ 0 ∧ IsRelPrime p.1 (g*C*t*principal p.2.1) then
    ((Y : ℂ) * (mobius e : ℂ) * coeffs p.2.2 * normIdeal g / ((normIdeal e : ℂ) * ell)) *
      (mobius p.1 : ℂ) * secondMobiusDualColumns c p.2.2 Φ U C d t g e p.1 Y ell p.2.1
  else 0

/-- Genuine joint finiteness in the three indices whose order changes. -/
theorem second_mobius_jointTerm_hasFiniteSupport (c : ArithmeticContext)
    (coeffs : RayCharacter c → ℂ) (hcoeff : (Function.support coeffs).Finite)
    (I : SupportInterval) (Φ : RowWeight) {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C d t : Ideal O) {g e : Ideal O} (hg : g ≠ ⊥) (he : e ≠ ⊥)
    {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    Function.HasFiniteSupport (secondMobiusJointTerm c coeffs Φ U C d t g e Y ell) := by
  let B := I.hi * ell / normIdeal g
  let A := Φ.fourierCap * I.hi ^ 2 * ell ^ 2 * normIdeal e / (Y * normIdeal g ^ 2)
  apply ((finite_normIdeal_le B).prod ((finite_normElement_le A).prod hcoeff)).subset
  intro p hp
  have hadm : SquarefreeOutside c.S p.1 ∧ p.2.1 ≠ 0 ∧
      IsRelPrime p.1 (g*C*t*principal p.2.1) := by
    by_contra hh
    exact hp (if_neg hh)
  have hcols : secondMobiusDualColumns c p.2.2 Φ U C d t g e p.1 Y ell p.2.1 ≠ 0 := by
    intro hz
    exact hp (by simp only [secondMobiusJointTerm,hz,mul_zero,ite_self])
  have hc : coeffs p.2.2 ≠ 0 := by
    intro hz
    exact hp (by simp only [secondMobiusJointTerm,hz,mul_zero,zero_mul,zero_div,ite_self])
  have hw : normIdeal (g*p.1) ≤ I.hi * ell := by
    by_contra hh
    exact hcols (second_mobius_dualColumns_zero_of_outer c p.2.2 I Φ hU C d t e hell
      hg hadm.1.1.1 p.2.1 (lt_of_not_ge hh))
  have hf : normElement p.2.1 ≤ A := by
    by_contra hh
    exact hcols (second_mobius_dualColumns_zero_of_frequency c p.2.2 I Φ hU C d t p.1
      hY hell hg he p.2.1 (lt_of_not_ge hh))
  refine ⟨?_,hf,hc⟩
  apply (le_div_iff₀ (normIdeal_pos hg)).mpr
  simpa only [normIdeal_mul,mul_comm] using hw

/-- Permute exactly the genuinely finite indices (w,h,character). -/
theorem second_mobius_jointTerm_reorder (c : ArithmeticContext)
    (coeffs : RayCharacter c → ℂ) (hcoeff : (Function.support coeffs).Finite)
    (I : SupportInterval) (Φ : RowWeight) {U : ℝ → ℂ} (hU : SmoothSupported I U)
    (C d t : Ideal O) {g e : Ideal O} (hg : g ≠ ⊥) (he : e ≠ ⊥)
    {Y ell : ℝ} (hY : 0 < Y) (hell : 0 < ell) :
    (∑' h : O, ∑' ξ : RayCharacter c, ∑' w : Ideal O,
      secondMobiusJointTerm c coeffs Φ U C d t g e Y ell (w,h,ξ)) =
    ∑' w : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c,
      secondMobiusJointTerm c coeffs Φ U C d t g e Y ell (w,h,ξ) := by
  let f := secondMobiusJointTerm c coeffs Φ U C d t g e Y ell
  have hs : Summable f := summable_of_hasFiniteSupport
    (second_mobius_jointTerm_hasFiniteSupport c coeffs hcoeff I Φ hU C d t hg he hY hell)
  calc
    _ = ∑' p : O × RayCharacter c, ∑' w : Ideal O, f (w,p) :=
      hs.prod_symm.prod.tsum_prod.symm
    _ = ∑' w : Ideal O, ∑' p : O × RayCharacter c, f (w,p) := Summable.tsum_comm (f := fun w p => f (w,p)) hs
    _ = _ := by
      apply tsum_congr
      intro w
      exact (hs.prod_factor w).tsum_prod

/-- The exact pinned Möbius recombination statement. All changed-order
indices have genuine joint finite support, independently of totalized sums. -/
theorem second_poisson_mobius_recombination_proved : MobiusRecombinationStatement := by
  intro c hc coeffs hcoeff I Φ U C d t Y ell hC ht hCt hd hY hell hU
  unfold coprimeDual secondPoissonDual
  apply tsum_congr
  intro g
  by_cases hg : SquarefreeOutside c.S g ∧ IsRelPrime g (C*t)
  · simp only [if_pos hg]
    apply tsum_congr
    intro e
    by_cases he : e ∣ g
    · simp only [if_pos he]
      have he0 : e ≠ ⊥ := ne_zero_of_dvd_ne_zero hg.1.1.1 he
      let f := secondMobiusJointTerm c coeffs Φ U C d t g e Y ell
      have hl : (∑' h : O, if h ≠ 0 then
          ∑' ξ : RayCharacter c,
            (Y : ℂ) * (mobius e : ℂ) * coeffs ξ * normIdeal g / ((normIdeal e : ℂ) * ell) *
              ∑' n₁ : Ideal O, if SquarefreeOutside c.S n₁ ∧ IsRelPrime n₁ (g*C*t) then
                ∑' n₂ : Ideal O, if SquarefreeOutside c.S n₂ ∧ IsRelPrime n₂ (g*C*t) ∧
                    IsRelPrime n₁ n₂ then
                  secondMobiusPairKernel c ξ Φ U C d g e Y ell h (n₁,n₂) else 0 else 0
          else 0) = ∑' h : O, ∑' ξ : RayCharacter c, ∑' w : Ideal O, f (w,h,ξ) := by
        apply tsum_congr
        intro h
        by_cases hh : h ≠ 0
        · rw [if_pos hh]
          apply tsum_congr
          intro ξ
          rw [second_mobius_columns_eq c hc ξ I Φ hU hC.1 hg.1.1 hd he Y hell h,
            ← tsum_mul_left]
          apply tsum_congr
          intro w
          by_cases hw : SquarefreeOutside c.S w ∧ IsRelPrime w (g*C*t*principal h)
          · simp only [if_pos hw]
            change _ = if SquarefreeOutside c.S w ∧ h ≠ 0 ∧ IsRelPrime w (g*C*t*principal h)
              then _ else 0
            rw [if_pos ⟨hw.1,hh,hw.2⟩]
            ring
          · have hn : ¬ (SquarefreeOutside c.S w ∧ h ≠ 0 ∧ IsRelPrime w (g*C*t*principal h)) :=
              fun hgate => hw ⟨hgate.1,hgate.2.2⟩
            simp only [if_neg hw,f,secondMobiusJointTerm,if_neg hn,mul_zero]
        · simp only [if_neg hh,f,secondMobiusJointTerm,hh,false_and,and_false,ite_false,tsum_zero]
      change (∑' h : O, if h ≠ 0 then
          ∑' ξ : RayCharacter c,
            (Y : ℂ) * (mobius e : ℂ) * coeffs ξ * normIdeal g / ((normIdeal e : ℂ) * ell) *
              ∑' n₁ : Ideal O, if SquarefreeOutside c.S n₁ ∧ IsRelPrime n₁ (g*C*t) then
                ∑' n₂ : Ideal O, if SquarefreeOutside c.S n₂ ∧ IsRelPrime n₂ (g*C*t) ∧
                    IsRelPrime n₁ n₂ then
                  secondMobiusPairKernel c ξ Φ U C d g e Y ell h (n₁,n₂) else 0 else 0
          else 0) = _
      rw [hl,second_mobius_jointTerm_reorder c coeffs hcoeff I Φ hU C d t hg.1.1.1 he0 hY hell]
      apply tsum_congr
      intro w
      by_cases hw : SquarefreeOutside c.S w ∧ normIdeal (g*w) ≤ I.hi * ell
      · rw [if_pos hw]
        apply tsum_congr
        intro h
        by_cases hh : h ≠ 0 ∧ IsRelPrime w (g*C*t*principal h) ∧
            normElement h ≤ Φ.fourierCap * I.hi ^ 2 * ell ^ 2 * normIdeal e /
              (Y * normIdeal g ^ 2)
        · rw [if_pos hh]
          apply tsum_congr
          intro ξ
          change (if SquarefreeOutside c.S w ∧ h ≠ 0 ∧ IsRelPrime w (g*C*t*principal h)
            then _ else 0) = _
          rw [if_pos ⟨hw.1,hh.1,hh.2.1⟩]
          dsimp only [secondMobiusDualColumns]
          ring
        · rw [if_neg hh]
          by_cases hn : h ≠ 0
          · by_cases hr : IsRelPrime w (g*C*t*principal h)
            · have hfreq : Φ.fourierCap * I.hi ^ 2 * ell ^ 2 * normIdeal e /
                (Y * normIdeal g ^ 2) < normElement h :=
                lt_of_not_ge (fun hb => hh ⟨hn,hr,hb⟩)
              have hz (ξ : RayCharacter c) := second_mobius_dualColumns_zero_of_frequency
                c ξ I Φ hU C d t w hY hell hg.1.1.1 he0 h hfreq
              simp only [f,secondMobiusJointTerm,hz,mul_zero,ite_self,tsum_zero]
            · simp only [f,secondMobiusJointTerm,hr,and_false,ite_false,tsum_zero]
          · simp only [f,secondMobiusJointTerm,hn,and_false,false_and,ite_false,tsum_zero]
      · rw [if_neg hw]
        by_cases hw' : SquarefreeOutside c.S w
        · have houter : I.hi * ell < normIdeal (g*w) :=
            lt_of_not_ge (fun hb => hw ⟨hw',hb⟩)
          have hz (h : O) (ξ : RayCharacter c) := second_mobius_dualColumns_zero_of_outer
            c ξ I Φ hU C d t e (Y := Y) hell hg.1.1.1 hw'.1.1 h houter
          simp only [f,secondMobiusJointTerm,hz,mul_zero,ite_self,tsum_zero]
        · simp only [f,secondMobiusJointTerm,hw',false_and,ite_false,tsum_zero]
    · simp only [if_neg he]
  · simp only [if_neg hg]

end QRHShort.CloudBatch
