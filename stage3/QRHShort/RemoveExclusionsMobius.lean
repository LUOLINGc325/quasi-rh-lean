import QRHShort.RemoveExclusionsColumns
import QRHShort.PoissonCoprimeExpansion

/-! The finite Möbius indicator outside the excluded prime set. -/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.RemoveExclusionsProof

theorem outsideRadical_dvd (S : Finset (Ideal O)) (r : Ideal O) (hr : r ≠ ⊥) :
    outsideRadical S r ∣ r := by
  have hsub : outsideRadical S r ∣ outsideRadical ∅ r := by
    simpa only [outsideRadical, Finset.notMem_empty, not_false_eq_true,
      Finset.filter_true] using
      Finset.prod_dvd_prod_of_subset ((primeFactors r).filter (fun P => P ∉ S))
        (primeFactors r) (fun P => P) (Finset.filter_subset _ _)
  exact hsub.trans (PoissonProof.CoprimeExpansion.radical_dvd r hr)

/-- A nonzero ideal outside `S` cannot share any of the deleted prime factors. -/
theorem isRelPrime_outsideRadical_iff (S : Finset (Ideal O)) (r n : Ideal O)
    (hr : r ≠ ⊥) (hn : Outside S n) :
    IsRelPrime (outsideRadical S r) n ↔ IsRelPrime r n := by
  constructor
  · intro h
    apply (isRelPrime_iff_no_prime_factors hr).mpr
    intro P hPr hPn hP
    have hnot : P ∉ S := fun hPS => hn.2 P hPS hPn
    have hmem : P ∈ (primeFactors r).filter (fun Q => Q ∉ S) :=
      Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hr).mpr ⟨hP, hPr⟩),
          hnot⟩
    have hrad : P ∣ outsideRadical S r := Finset.dvd_prod_of_mem id hmem
    exact hP.not_isUnit (h hrad hPn)
  · intro h d hd hn'
    exact h (hd.trans (outsideRadical_dvd S r hr)) hn'

/-- The frozen finite inclusion-exclusion statement, with no unproved inputs. -/
theorem mobiusIndicator : MobiusIndicatorStatement := by
  intro c r n hr hn
  let R := outsideRadical c.S r
  have hR : R ≠ 0 := outsideRadical_ne_bot c.S r
  have hg : gcd R n ≠ 0 := ne_zero_of_dvd_ne_zero hR (gcd_dvd_left R n)
  have heq :
      (∑ d ∈ radicalDivisors c.S r, if d ∣ n then (mobius d : ℂ) else 0) =
      ∑ d ∈ PoissonProof.CoprimeExpansion.idealDivisors (gcd R n) hg,
        (mobius d : ℂ) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext d
      simp only [Finset.mem_filter, mem_radicalDivisors,
        PoissonProof.CoprimeExpansion.mem_idealDivisors, dvd_gcd_iff, R]
    · intro d _
      rfl
  rw [heq, PoissonProof.CoprimeExpansion.sum_idealDivisors_mobius_complex]
  have hi : gcd R n = 1 ↔ IsRelPrime n r :=
    (PoissonProof.CoprimeExpansion.gcd_eq_one_iff_relprime R n).trans
      ((isRelPrime_outsideRadical_iff c.S r n hr hn.1).trans isRelPrime_comm)
  simp only [hi]

end QRHShort.RemoveExclusionsProof
