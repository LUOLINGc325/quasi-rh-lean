import QRHShort.ThetaStatements

/-!
Uniformity follows from the fixed finite pool in `ReflectionStatement`.
Every prime of the varying ideal has exponent one and hence is active.
Removing these forced primes gives the required indexing by subsets of the
fixed prime set. The pool index can consequently be chosen constant in the
varying ideal, so the unit ideal suffices for the ray modulus.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ReflectionUniformityProof

theorem primeTwistSet_union_factors {c : ArithmeticContext}
    {P : Finset (Ideal O)} (hP : PrimeTwistSet c.S P)
    {k : Ideal O} (hk : SquarefreeOutside c.S k) :
    PrimeTwistSet c.S (P ∪ primeFactors k) := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact hP p hp
  · have hf : p ∈ UniqueFactorizationMonoid.normalizedFactors k :=
      Multiset.mem_toFinset.mp hp
    refine ⟨UniqueFactorizationMonoid.prime_of_normalized_factor p hf, ?_⟩
    intro hpS
    exact hk.1.2 p hpS (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hf)

theorem disjoint_primeFactors_of_relPrime {P : Finset (Ideal O)} {k : Ideal O}
    (hk : IsRelPrime k (∏ p ∈ P, p)) : Disjoint P (primeFactors k) := by
  apply Finset.disjoint_left.mpr
  intro p hpP hpk
  have hf : p ∈ UniqueFactorizationMonoid.normalizedFactors k :=
    Multiset.mem_toFinset.mp hpk
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor p hf).not_isUnit
    (hk (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hf)
      (Finset.dvd_prod_of_mem (fun p : Ideal O => p) hpP))

theorem admissible_union_iff {P Q A : Finset (Ideal O)}
    (hPQ : Disjoint P Q) (hA : A ⊆ P) (j : Ideal O → Fin 6) :
    AdmissibleActive (P ∪ Q) (variableTwistExponents P j) (A ∪ Q) ↔
      AdmissibleActive P j A := by
  constructor
  · intro h
    refine ⟨hA, ?_⟩
    intro p hpP hj
    have hp := h.2 p (Finset.mem_union_left Q hpP)
      (by simpa only [variableTwistExponents, ite_eq_left hpP] using hj)
    rcases Finset.mem_union.mp hp with hpA | hpQ
    · exact hpA
    · exact (Finset.disjoint_left.mp hPQ hpP hpQ).elim
  · intro h
    refine ⟨Finset.union_subset_union h.1 Finset.Subset.rfl, ?_⟩
    intro p hp hj
    rcases Finset.mem_union.mp hp with hpP | hpQ
    · exact Finset.mem_union_left Q (h.2 p hpP
        (by simpa only [variableTwistExponents, ite_eq_left hpP] using hj))
    · exact Finset.mem_union_right A hpQ

theorem forced_subset {P Q B : Finset (Ideal O)} (hPQ : Disjoint P Q)
    (j : Ideal O → Fin 6)
    (hB : AdmissibleActive (P ∪ Q) (variableTwistExponents P j) B) : Q ⊆ B := by
  intro p hpQ
  have hpP : p ∉ P := fun hpP => Finset.disjoint_left.mp hPQ hpP hpQ
  exact hB.2 p (Finset.mem_union_right P hpQ)
    (by simp [variableTwistExponents, hpP])

theorem sum_admissible_union (P Q : Finset (Ideal O))
    (j : Ideal O → Fin 6) (hPQ : Disjoint P Q) (F : Finset (Ideal O) → ℂ) :
    (∑ B ∈ (P ∪ Q).powerset,
      if AdmissibleActive (P ∪ Q) (variableTwistExponents P j) B then F B else 0) =
    ∑ A ∈ P.powerset, if AdmissibleActive P j A then F (A ∪ Q) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun A _ => A ∪ Q)
  · intro A hA
    have hA' := (Finset.mem_filter.mp hA).2
    have h := (admissible_union_iff hPQ hA'.1 j).mpr hA'
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h⟩
  · intro A hA B hB hAB
    have hAP := (Finset.mem_filter.mp hA).2.1
    have hBP := (Finset.mem_filter.mp hB).2.1
    apply Finset.Subset.antisymm
    · intro p hpA
      have hp : p ∈ B ∪ Q := hAB ▸ Finset.mem_union_left Q hpA
      exact (Finset.mem_union.mp hp).resolve_right
        (fun hpQ => Finset.disjoint_left.mp hPQ (hAP hpA) hpQ)
    · intro p hpB
      have hp : p ∈ A ∪ Q := hAB.symm ▸ Finset.mem_union_left Q hpB
      exact (Finset.mem_union.mp hp).resolve_right
        (fun hpQ => Finset.disjoint_left.mp hPQ (hBP hpB) hpQ)
  · intro B hB
    have hB' := (Finset.mem_filter.mp hB).2
    have hQB := forced_subset hPQ j hB'
    have heq : (B ∩ P) ∪ Q = B := by
      apply Finset.Subset.antisymm
      · exact Finset.union_subset Finset.inter_subset_left hQB
      · intro p hpB
        rcases Finset.mem_union.mp (hB'.1 hpB) with hpP | hpQ
        · exact Finset.mem_union_left Q (Finset.mem_inter.mpr ⟨hpB, hpP⟩)
        · exact Finset.mem_union_right (B ∩ P) hpQ
    refine ⟨B ∩ P, ?_, heq⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    apply (admissible_union_iff hPQ Finset.inter_subset_right j).mp
    simpa only [heq] using hB'
  · intro A _
    rfl

end QRHShort.ReflectionUniformityProof

namespace QRHShort
open ReflectionUniformityProof

theorem reflection_uniformity_of_reflection (hr : ReflectionStatement) :
    ReflectionUniformityStatement := by
  intro c ξ
  obtain ⟨N, pool, K, hK, hR⟩ := hr c ξ
  refine ⟨N, N, pool, K, hK, 1, one_ne_zero, ?_, ?_⟩
  · intro p hp hpd
    exact (hp.not_dvd_one hpd).elim
  · intro P j hP
    have hex : ∀ k : Ideal O, ∃ coeff : Fin N → Finset (Ideal O) → ℂ,
        SquarefreeOutside c.S k →
          (∀ h A, AdmissibleActive (P ∪ primeFactors k) (variableTwistExponents P j) A →
            ‖coeff h A‖ ≤ K) ∧
          ∀ (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ),
            SmoothSupported I W → 0 < X →
            completedSum c (productTwist c ξ (P ∪ primeFactors k)
              (variableTwistExponents P j)) W X =
              ∑ h : Fin N, ∑ A ∈ (P ∪ primeFactors k).powerset,
                if AdmissibleActive (P ∪ primeFactors k) (variableTwistExponents P j) A then
                  coeff h A * dualThetaSum (pool h) A (variableTwistExponents P j)
                    (fun x => (Real.sqrt x : ℂ) * W x) X
                else 0 := by
      intro k
      by_cases hk : SquarefreeOutside c.S k
      · obtain ⟨coeff, hb, he⟩ := hR (P ∪ primeFactors k) (variableTwistExponents P j)
          (primeTwistSet_union_factors hP hk)
        exact ⟨coeff, fun _ => ⟨hb, he⟩⟩
      · exact ⟨fun _ _ => 0, fun hk' => (hk hk').elim⟩
    choose coeff hcoeff using hex
    refine ⟨(fun _ h _ => h), (fun k h A => coeff k h (A ∪ primeFactors k)), ?_, ?_⟩
    · intro k l _ _ _ _ _ h A _
      rfl
    · intro k hk hkp
      obtain ⟨hb, he⟩ := hcoeff k hk
      have hPQ := disjoint_primeFactors_of_relPrime hkp
      refine ⟨?_, ?_⟩
      · intro h A hA
        exact hb h (A ∪ primeFactors k) ((admissible_union_iff hPQ hA.1 j).mpr hA)
      · intro I W X hW hX
        dsimp only
        rw [he I W X hW hX]
        apply Finset.sum_congr rfl
        intro h _
        exact sum_admissible_union P (primeFactors k) j hPQ
          (fun A => coeff k h A * dualThetaSum (pool h) A (variableTwistExponents P j)
            (fun x => (Real.sqrt x : ℂ) * W x) X)

end QRHShort
