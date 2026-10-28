import QRHShort.SecondTransferReduction
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem second_transfer_prmr_quotient_spec {g e : Ideal O} (h : e ∣ g) :
    e * quotientIdeal g e = g := by
  unfold quotientIdeal
  rw [dif_pos h]
  exact (Classical.choose_spec h).symm

theorem second_transfer_prmr_quotient_unique {g e q : Ideal O}
    (he : e ≠ ⊥) (h : e * q = g) : quotientIdeal g e = q := by
  apply mul_left_cancel₀ he
  exact (second_transfer_prmr_quotient_spec ⟨q, h.symm⟩).trans h.symm

/-- The actual ideal preimages of the excluded factor; no factorization is assumed. -/
def secondTransferPRMRDivisorFactorEquiv (r : Ideal O) (hr : r ≠ ⊥) :
    {t : Ideal O // t ∣ r} ≃ {p : Ideal O × Ideal O // p.1 * p.2 = r} where
  toFun t := ⟨(t.1, quotientIdeal r t.1), second_transfer_prmr_quotient_spec t.2⟩
  invFun p := ⟨p.1.1, ⟨p.1.2, p.2.symm⟩⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    change (p.val.1, quotientIdeal r p.val.1) = p.val
    apply Prod.ext
    · rfl
    · exact second_transfer_prmr_quotient_unique
        (ne_zero_of_dvd_ne_zero hr ⟨p.1.2, p.2.symm⟩) p.2

theorem second_transfer_prmr_factor_fiber_finite (r : Ideal O) (hr : r ≠ ⊥) :
    Finite {p : Ideal O × Ideal O // p.1 * p.2 = r} := by
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd r hr
  exact Finite.of_equiv _ (secondTransferPRMRDivisorFactorEquiv r hr)

theorem second_transfer_prmr_factor_fiber_sum (r : Ideal O) (hr : r ≠ ⊥) (z : ℂ) :
    (∑' _p : {p : Ideal O × Ideal O // p.1 * p.2 = r}, z) =
      (divisorCount r : ℂ) * z := by
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd r hr
  rw [← (secondTransferPRMRDivisorFactorEquiv r hr).tsum_eq (fun _ => z), tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, divisorCount,
    Nat.card_eq_fintype_card]

theorem second_transfer_prmr_squarefree_dvd_iff {f k : Ideal O} (hf : Squarefree f) :
    f ∣ k ↔ ∀ p : (primeFactors f), (p : Ideal O) ∣ k := by
  constructor
  · intro h p
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp p.2)).trans h
  · intro h
    by_cases hk : k = 0
    · rw [hk]; exact dvd_zero _
    apply (dvd_iff_normalizedFactors_le_normalizedFactors hf.ne_zero hk).mpr
    apply (Multiset.le_iff_subset ((squarefree_iff_nodup_normalizedFactors hf.ne_zero).mp hf)).mpr
    intro p hp
    exact (mem_normalizedFactors_iff hk).mpr
      ⟨prime_of_normalized_factor p hp, h ⟨p, Multiset.mem_toFinset.mpr hp⟩⟩

/-- The four choices are C without d, C with d, e, and w, respectively. -/
def secondTransferPRMRLocalSign (P : Prop) [Decidable P] (i : Fin 4) : ℤ :=
  if i = 0 then 1 else if i = 1 then (if P then 1 else 0)
  else if i = 2 then (if P then -1 else 0) else (if P then 0 else -1)

theorem second_transfer_prmr_localSign_sum (P : Prop) [Decidable P] :
    (∑ i : Fin 4, secondTransferPRMRLocalSign P i) = if P then 1 else 0 := by
  by_cases h : P <;> simp [Fin.sum_univ_four, secondTransferPRMRLocalSign, h]

/-- Signed cancellation simultaneously at every actual prime ideal of f.
The additional identification of these colorings with the complete literal
Poisson preimage fiber is a separate obligation. -/
theorem second_transfer_prmr_prime_fiber_cancellation (f k : Ideal O)
    (hf : Squarefree f) :
    (∑ v : (primeFactors f) → Fin 4,
      ∏ p : (primeFactors f), secondTransferPRMRLocalSign ((p : Ideal O) ∣ k) (v p)) =
      if f ∣ k then 1 else 0 := by
  rw [← Fintype.prod_sum]
  simp_rw [second_transfer_prmr_localSign_sum]
  by_cases h : f ∣ k
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro p _
    exact if_pos ((second_transfer_prmr_squarefree_dvd_iff hf).mp h p)
  · rw [if_neg h]
    have hn : ¬ ∀ p : (primeFactors f), (p : Ideal O) ∣ k :=
      fun hh => h ((second_transfer_prmr_squarefree_dvd_iff hf).mpr hh)
    push_neg at hn
    obtain ⟨p, hp⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

end QRHShort
