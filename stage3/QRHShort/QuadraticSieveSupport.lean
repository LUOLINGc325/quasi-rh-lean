import QRHShort.QuadraticSieveTransfer
import Mathlib.Algebra.Order.Floor.Ring

/-! Finite ideal support and the exact factorization at primes above two. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def quadraticSieveIndices (F : QuadraticHeckeFamily) (X : ℝ) : Finset (Ideal O) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := O) ⌈X⌉₊).subset
    (show {n : Ideal O | normIdeal n ≤ X} ⊆ {n | n.absNorm ≤ ⌈X⌉₊} from
      fun n hn => Nat.cast_le.mp (hn.trans (Nat.le_ceil X)))).toFinset.filter
    (fun n => FamilyIdeal F.modulus n ∧ Squarefree n)

@[simp] theorem mem_quadraticSieveIndices (F : QuadraticHeckeFamily) (X : ℝ)
    (n : Ideal O) : n ∈ quadraticSieveIndices F X ↔
      FamilyIdeal F.modulus n ∧ Squarefree n ∧ normIdeal n ≤ X := by
  simp only [quadraticSieveIndices, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  tauto

theorem quadraticSieve_tsum {E : Type*} [NormedAddCommGroup E]
    (F : QuadraticHeckeFamily) (X : ℝ) (f : Ideal O → E) :
    (∑' n : Ideal O, if FamilyIdeal F.modulus n ∧ Squarefree n ∧ normIdeal n ≤ X
      then f n else 0) = ∑ n ∈ quadraticSieveIndices F X, f n := by
  calc
    _ = ∑ n ∈ quadraticSieveIndices F X,
        if FamilyIdeal F.modulus n ∧ Squarefree n ∧ normIdeal n ≤ X
          then f n else 0 := by
      apply tsum_eq_sum
      intro n hn
      exact if_neg (fun h => hn ((mem_quadraticSieveIndices F X n).mpr h))
    _ = _ := Finset.sum_congr rfl (fun n hn =>
      if_pos ((mem_quadraticSieveIndices F X n).mp hn))

theorem quadratic_twoPrime_factorization (n : Ideal O) (hn : n ≠ ⊥)
    (hsq : Squarefree n) (hthree : IsRelPrime n (principal 3)) :
    ∃ d m : Ideal O, d ∣ principal 2 ∧ d ≠ ⊥ ∧
      FamilyIdeal (principal 6) m ∧ Squarefree d ∧ Squarefree m ∧ n = d * m := by
  let d := gcd n (principal 2)
  obtain ⟨m, hm⟩ := gcd_dvd_left n (principal 2)
  change n = d * m at hm
  have hd0 : d ≠ ⊥ := fun hd => hn (by rw [hm, hd, Ideal.bot_mul])
  have hm0 : m ≠ ⊥ := fun hz => hn (by rw [hm, hz, Ideal.mul_bot])
  have hsqdm : Squarefree (d * m) := hm ▸ hsq
  have hdm : IsRelPrime d m := IsRelPrime.of_squarefree_mul hsqdm
  have hm2 : IsRelPrime m (principal 2) := by
    intro a ham ha2
    apply hdm _ ham
    change a ∣ gcd n (principal 2)
    apply dvd_gcd _ ha2
    rw [hm]
    exact dvd_mul_of_dvd_right ham d
  have hm3 : IsRelPrime m (principal 3) :=
    hthree.of_dvd_left (hm.symm ▸ dvd_mul_left m d)
  have hsix : principal (6 : O) = principal 2 * principal 3 := by
    change Ideal.span {(6 : O)} = Ideal.span {(2 : O)} * Ideal.span {(3 : O)}
    rw [Ideal.span_singleton_mul_span_singleton]
    norm_num
  refine ⟨d, m, gcd_dvd_right _ _, hd0, ⟨hm0, ?_⟩,
    hsqdm.of_mul_left, hsqdm.of_mul_right, hm⟩
  rw [hsix]
  exact hm2.mul_right hm3

/-- There are only finitely many possible bad factors, uniformly in U. -/
theorem quadratic_twoPrime_finite_badFactors :
    {d : Ideal O | d ∣ principal 2}.Finite := by
  have htwo : principal (2 : O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hfinite := Ideal.finite_setOfPred_absNorm_le (S := O) (principal (2 : O)).absNorm
  apply hfinite.subset
  intro d hd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr htwo))
    (map_dvd Ideal.absNorm hd)

end QRHShort

#print axioms QRHShort.quadratic_twoPrime_factorization
#print axioms QRHShort.quadratic_twoPrime_finite_badFactors
