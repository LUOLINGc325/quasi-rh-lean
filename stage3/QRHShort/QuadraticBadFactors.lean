import QRHShort.QuadraticSieveTransfer
import QRHShort.FiniteSupport
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
The frozen `SquarefreeOutside S` predicate includes global squarefreeness.
Its row set is therefore a subset of the squarefree row set, for every S.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- Restricting the nonnegative row sum preserves the squarefree bound and
even allows its constant to be chosen independently of the excluded set. -/
theorem quadraticFiniteBadFactors : QuadraticFiniteBadFactorsStatement := by
  classical
  intro hs S ε a b hε ha hab
  obtain ⟨K, hK0, hK⟩ := hs ε a b hε ha hab
  refine ⟨K, hK0, ?_⟩
  intro H U β hH hU hβ
  let F : Ideal O → ℝ := fun k =>
    ‖∑' n : Ideal O, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2
  have hsum (P : Ideal O → Prop) (hP : ∀ k, P k → normIdeal k ≤ H) :
      Summable (fun k => if P k then F k else 0) := by
    apply summable_of_hasFiniteSupport
    apply (finite_normIdeal_le H).subset
    intro k hk
    by_contra hkH
    exact hk (if_neg (fun hPk => hkH (hP k hPk)))
  have hmono :
      (∑' k : Ideal O, if SquarefreeOutside S k ∧ IsRelPrime k (principal 6) ∧
          normIdeal k ≤ H then F k else 0) ≤
      ∑' k : Ideal O, if Squarefree k ∧ IsRelPrime k (principal 6) ∧
          normIdeal k ≤ H then F k else 0 := by
    refine Summable.tsum_le_tsum ?_
      ((hsum (fun k => SquarefreeOutside S k ∧ IsRelPrime k (principal 6) ∧
        normIdeal k ≤ H) (fun _ hk => hk.2.2)).congr
          (fun k => by split_ifs <;> rfl))
      ((hsum (fun k => Squarefree k ∧ IsRelPrime k (principal 6) ∧
        normIdeal k ≤ H) (fun _ hk => hk.2.2)).congr
          (fun k => by split_ifs <;> rfl))
    intro k
    by_cases hk : SquarefreeOutside S k ∧ IsRelPrime k (principal 6) ∧
        normIdeal k ≤ H
    · rw [if_pos hk, if_pos ⟨hk.1.2, hk.2⟩]
    · rw [if_neg hk]
      exact ite_nonneg (sq_nonneg _) le_rfl
  exact hmono.trans (hK H U β hH hU hβ)

end QRHShort

#print axioms QRHShort.quadraticFiniteBadFactors
