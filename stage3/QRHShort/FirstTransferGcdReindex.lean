import QRHShort.FirstTransferGcd
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
Finite and summable reindexing by the genuine gcd equivalence.  The infinite
series API returns summability of the transformed series together with its
value identity, so no convergence is inferred from totalized tsum notation.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_gcd_sum_reindex {E : Type*} [AddCommMonoid E]
    (c : ArithmeticContext) (s : Finset (FirstTransferGcdPairs c))
    (f : FirstTransferGcdPairs c → E) :
    ∑ p ∈ s, f p =
      ∑ t ∈ s.map (firstTransferGcdEquiv c).symm.toEmbedding,
        f (firstTransferGcdReconstruct c t) := by
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  change f p = f (firstTransferGcdEquiv c ((firstTransferGcdEquiv c).symm p))
  rw [Equiv.apply_symm_apply]

theorem first_transfer_gcd_summable_iff {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : FirstTransferGcdPairs c → E) :
    Summable (fun t : FirstTransferGcdTriples c => f (firstTransferGcdReconstruct c t)) ↔
      Summable f :=
  (firstTransferGcdEquiv c).summable_iff

theorem first_transfer_gcd_summable_reindex {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : FirstTransferGcdPairs c → E) (hf : Summable f) :
    Summable (fun t : FirstTransferGcdTriples c => f (firstTransferGcdReconstruct c t)) ∧
      (∑' p, f p) = ∑' t : FirstTransferGcdTriples c, f (firstTransferGcdReconstruct c t) :=
  ⟨(first_transfer_gcd_summable_iff c f).mpr hf, ((firstTransferGcdEquiv c).tsum_eq f).symm⟩

/-- An unbundled form ready for literal ideal-pair expansions: both transformed
restrictions and all three coprimalities are exactly those of the gcd triple. -/
theorem first_transfer_gcd_indicator_reindex {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : Ideal O × Ideal O → E)
    (hf : Summable (fun p : Ideal O × Ideal O =>
      if firstTransferGcdPairAdmissible c p then f p else 0)) :
    Summable (fun t : Ideal O × Ideal O × Ideal O =>
      if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0) ∧
    (∑' p : Ideal O × Ideal O, if firstTransferGcdPairAdmissible c p then f p else 0) =
      ∑' t : Ideal O × Ideal O × Ideal O,
        if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
  have hpairIndicator : ({p | firstTransferGcdPairAdmissible c p}.indicator f) =
      (fun p => if firstTransferGcdPairAdmissible c p then f p else 0) := by
    funext p
    exact Set.indicator_apply _ _ _
  have htripleIndicator : ({t | firstTransferGcdTripleAdmissible c t}.indicator
      (fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))) =
      (fun t => if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2)
        else 0) := by
    funext t
    exact Set.indicator_apply _ _ _
  have hpair : Summable (fun p : FirstTransferGcdPairs c => f p.1) := by
    apply (summable_subtype_iff_indicator
      (s := {p | firstTransferGcdPairAdmissible c p}) (f := f)).mpr
    rw [hpairIndicator]
    exact hf
  obtain ⟨htriple, heq⟩ := first_transfer_gcd_summable_reindex c
    (fun p : FirstTransferGcdPairs c => f p.1) hpair
  have htriple' := (summable_subtype_iff_indicator
    (s := {t | firstTransferGcdTripleAdmissible c t})
    (f := fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))).mp htriple
  refine ⟨?_, ?_⟩
  · rw [htripleIndicator] at htriple'
    exact htriple'
  · have hp : (∑' p : FirstTransferGcdPairs c, f p.1) =
        ∑' p : Ideal O × Ideal O, if firstTransferGcdPairAdmissible c p then f p else 0 := by
      have h := tsum_subtype {p | firstTransferGcdPairAdmissible c p} f
      simp_rw [hpairIndicator] at h
      exact h
    have ht : (∑' t : FirstTransferGcdTriples c, f (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2)) =
        ∑' t : Ideal O × Ideal O × Ideal O,
          if firstTransferGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
      have h := tsum_subtype {t | firstTransferGcdTripleAdmissible c t}
        (fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))
      simp_rw [htripleIndicator] at h
      exact h
    exact hp.symm.trans (heq.trans ht)

end QRHShort
