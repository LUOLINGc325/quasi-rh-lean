import QRHShort.FirstTransferMobiusDivisors
import QRHShort.FirstTransferMobiusSubstitution
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
Möbius removal of pair coprimality for a genuinely finitely supported complex
function.  Both the common-divisor expansion and its (t,x,y) substitution have
finite support before the product series is rearranged.  The residual pair x,y
has no coprimality restriction.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def firstTransferMobiusDivisorTerm (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (q : (Ideal O × Ideal O) × Ideal O) : ℂ :=
  if firstTransferMobiusDivisorAdmissible c q then (mobius q.2 : ℂ) * F q.1 else 0

def firstTransferMobiusTripleTerm (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if firstTransferMobiusTripleAdmissible c t then
    (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0

theorem first_transfer_mobius_tripleTerm_eq (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (t : Ideal O × Ideal O × Ideal O) :
    firstTransferMobiusTripleTerm c F t =
      if SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧
          SquarefreeOutside c.S t.2.2 ∧ IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1
      then (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
  unfold firstTransferMobiusTripleTerm
  by_cases ht : firstTransferMobiusTripleAdmissible c t
  · rw [if_pos ht]
    unfold firstTransferMobiusTripleAdmissible at ht
    rw [if_pos ht]
  · rw [if_neg ht]
    unfold firstTransferMobiusTripleAdmissible at ht
    rw [if_neg ht]

theorem first_transfer_mobius_divisorTerm_hasFiniteSupport (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (firstTransferMobiusDivisorTerm c F) := by
  let S := {p : Ideal O × Ideal O | firstTransferGcdPairAdmissible c p ∧ F p ≠ 0}
  have hS : S.Finite := hF.subset (fun _ hp => hp.2)
  have hfin : (⋃ p ∈ S, ({p} : Set (Ideal O × Ideal O)) ×ˢ
      {d : Ideal O | d ∣ p.1}).Finite := by
    apply hS.biUnion
    intro p hp
    exact (Set.finite_singleton p).prod (first_transfer_divisors_finite hp.1.1.1.1)
  apply hfin.subset
  intro q hq
  have hadm : firstTransferMobiusDivisorAdmissible c q := by
    by_contra h
    exact hq (if_neg h)
  have hFq : F q.1 ≠ 0 := by
    intro h
    exact hq (by simp only [firstTransferMobiusDivisorTerm, if_pos hadm, h, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨q.1, ⟨hadm.1, hFq⟩, rfl, hadm.2.1⟩

theorem first_transfer_mobius_divisorTerm_image (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) {t : Ideal O × Ideal O × Ideal O}
    (ht : firstTransferMobiusTripleAdmissible c t) :
    firstTransferMobiusDivisorTerm c F (firstTransferMobiusImage t) =
      firstTransferMobiusTripleTerm c F t := by
  rw [firstTransferMobiusDivisorTerm,
    if_pos (first_transfer_mobius_image_admissible c ht),
    firstTransferMobiusTripleTerm, if_pos ht]
  rfl

theorem first_transfer_mobius_tripleTerm_hasFiniteSupport (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (firstTransferMobiusTripleTerm c F) := by
  have hadm : ∀ t ∈ Function.support (firstTransferMobiusTripleTerm c F),
      firstTransferMobiusTripleAdmissible c t := by
    intro t ht
    by_contra h
    exact ht (if_neg h)
  apply Set.Finite.of_injOn (f := firstTransferMobiusImage)
    (t := Function.support (firstTransferMobiusDivisorTerm c F))
  · intro t ht
    rw [Function.mem_support, first_transfer_mobius_divisorTerm_image c F (hadm t ht)]
    exact ht
  · intro t ht s hs h
    exact first_transfer_mobius_image_injOn c (hadm t ht) (hadm s hs) h
  · exact first_transfer_mobius_divisorTerm_hasFiniteSupport c F hF

theorem first_transfer_mobius_divisor_triple_reindex (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) :
    (∑' q : (Ideal O × Ideal O) × Ideal O, firstTransferMobiusDivisorTerm c F q) =
      ∑' t : Ideal O × Ideal O × Ideal O, firstTransferMobiusTripleTerm c F t := by
  have hdivIndicator : ({q | firstTransferMobiusDivisorAdmissible c q}.indicator
      (fun q : (Ideal O × Ideal O) × Ideal O => (mobius q.2 : ℂ) * F q.1)) =
      firstTransferMobiusDivisorTerm c F := by
    funext q
    exact Set.indicator_apply _ _ _
  have htripleIndicator : ({t | firstTransferMobiusTripleAdmissible c t}.indicator
      (fun t : Ideal O × Ideal O × Ideal O =>
        (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2))) =
      firstTransferMobiusTripleTerm c F := by
    funext t
    exact Set.indicator_apply _ _ _
  have hd : (∑' q : FirstTransferMobiusDivisorIndices c, (mobius q.1.2 : ℂ) * F q.1.1) =
      ∑' q : (Ideal O × Ideal O) × Ideal O, firstTransferMobiusDivisorTerm c F q := by
    have h := tsum_subtype {q | firstTransferMobiusDivisorAdmissible c q}
      (fun q : (Ideal O × Ideal O) × Ideal O => (mobius q.2 : ℂ) * F q.1)
    simp_rw [hdivIndicator] at h
    exact h
  have ht : (∑' t : FirstTransferMobiusTriples c,
      (mobius t.1.1 : ℂ) * F (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2)) =
      ∑' t : Ideal O × Ideal O × Ideal O, firstTransferMobiusTripleTerm c F t := by
    have h := tsum_subtype {t | firstTransferMobiusTripleAdmissible c t}
      (fun t : Ideal O × Ideal O × Ideal O =>
        (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2))
    simp_rw [htripleIndicator] at h
    exact h
  exact hd.symm.trans (((firstTransferMobiusEquiv c).tsum_eq
    (fun q : FirstTransferMobiusDivisorIndices c => (mobius q.1.2 : ℂ) * F q.1.1)).symm.trans ht)

theorem first_transfer_mobius_remove_pair_coprimality (c : ArithmeticContext)
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
      then F p else 0) = ∑' t, firstTransferMobiusTripleTerm c F t by
    simpa only [first_transfer_mobius_tripleTerm_eq] using h
  rw [← first_transfer_mobius_divisor_triple_reindex]
  have hsum : Summable (firstTransferMobiusDivisorTerm c F) := summable_of_hasFiniteSupport
    (first_transfer_mobius_divisorTerm_hasFiniteSupport c F hF)
  rw [hsum.tsum_prod]
  apply tsum_congr
  intro p
  by_cases hp : firstTransferGcdPairAdmissible c p
  · have hterm : (fun d : Ideal O => firstTransferMobiusDivisorTerm c F (p, d)) =
        fun d => (if d ∣ p.1 ∧ d ∣ p.2 then (mobius d : ℂ) else 0) * F p := by
      funext d
      by_cases hd : d ∣ p.1 ∧ d ∣ p.2
      · simp only [firstTransferMobiusDivisorTerm, firstTransferMobiusDivisorAdmissible,
          hp, hd, and_self, if_true]
      · simp only [firstTransferMobiusDivisorTerm, firstTransferMobiusDivisorAdmissible,
          hp, hd, and_false, if_false, zero_mul]
    rw [hterm, tsum_mul_right, first_transfer_tsum_commonDivisors_mobius p.1 p.2 hp.1.1.1]
    by_cases hrel : IsRelPrime p.1 p.2
    · simp only [hp.1, hp.2, hrel, and_self, if_true, one_mul]
    · simp only [hrel, and_false, if_false, zero_mul]
  · have hnot : ¬ (SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2 ∧
        IsRelPrime p.1 p.2) := fun h => hp ⟨h.1, h.2.1⟩
    rw [if_neg hnot]
    simp only [firstTransferMobiusDivisorTerm, firstTransferMobiusDivisorAdmissible,
      hp, false_and, ite_false, tsum_zero]

/-- The reindexed series is genuinely finite and hence summable, including
when the original finite support contains a zero ideal. -/
theorem first_transfer_mobius_removed_hasFiniteSupport (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (fun t : Ideal O × Ideal O × Ideal O =>
      if SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧
          SquarefreeOutside c.S t.2.2 ∧ IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1
      then (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0) := by
  have heq := funext (first_transfer_mobius_tripleTerm_eq c F)
  rw [← heq]
  exact first_transfer_mobius_tripleTerm_hasFiniteSupport c F hF

theorem first_transfer_mobius_removed_summable (c : ArithmeticContext)
    (F : Ideal O × Ideal O → ℂ) (hF : Function.HasFiniteSupport F) :
    Summable (fun t : Ideal O × Ideal O × Ideal O =>
      if SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧
          SquarefreeOutside c.S t.2.2 ∧ IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1
      then (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) else 0) :=
  summable_of_hasFiniteSupport (first_transfer_mobius_removed_hasFiniteSupport c F hF)

end QRHShort
