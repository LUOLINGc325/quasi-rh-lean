import QRHShort.QuadraticFamilyAssembly
import QRHShort.Estimates

/-!
The remaining analytic child has the original `QuadraticEstimate` as its
conclusion. It must account for the reversed family indices, coefficients
whose ideals may lie above two, and repeated factors at the finite set S.
The external family sieve alone has none of those extensions in its type.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The intermediate estimate has squarefree row ideals. Coefficients still
have exactly the support allowed by the frozen endpoint, including above two. -/
def QuadraticSquarefreeEstimate : Prop :=
  ∀ (ε a b : ℝ), 0 < ε → 0 < a → a ≤ b →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (H U : ℝ) (β : Ideal O → ℂ), 1 ≤ H → 1 ≤ U →
      Function.support β ⊆ {n | n ≠ ⊥ ∧ Squarefree n ∧
        IsRelPrime n (principal 3) ∧ a * U ≤ normIdeal n ∧ normIdeal n ≤ b * U} →
      (∑' k : Ideal O, if Squarefree k ∧ IsRelPrime k (principal 6) ∧
          normIdeal k ≤ H then
        ‖∑' n : Ideal O, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2
        else 0) ≤ K * (H * U) ^ ε * (H + U) * ∑' n : Ideal O, ‖β n‖ ^ 2

/-- Reciprocity, index interchange and the fixed prime above two are needed
here; all coefficient and scale quantifiers are retained. -/
def QuadraticSquarefreeSieveTransferStatement : Prop :=
  ∀ h : QuadraticRayClassInvariantStatement,
    QuadraticFamilySieve (concreteQuadraticFamily h) → QuadraticSquarefreeEstimate

/-- Extend squarefree rows to rows squarefree outside an arbitrary finite S.
The resulting constants may depend on S exactly as in the frozen endpoint. -/
def QuadraticFiniteBadFactorsStatement : Prop :=
  QuadraticSquarefreeEstimate → QuadraticEstimate

/-- Internal transfer from the concrete family sieve to the frozen endpoint.
No assertion of this proposition is made here. -/
def QuadraticSieveTransferStatement : Prop :=
  ∀ h : QuadraticRayClassInvariantStatement,
    QuadraticFamilySieve (concreteQuadraticFamily h) → QuadraticEstimate

theorem quadraticSieveTransfer_of_squarefree_and_badFactors
    (hs : QuadraticSquarefreeSieveTransferStatement)
    (hb : QuadraticFiniteBadFactorsStatement) : QuadraticSieveTransferStatement :=
  fun hi hf => hb (hs hi hf)

theorem quadratic_of_classInvariant_and_transfer
    (hi : QuadraticRayClassInvariantStatement) (ht : QuadraticSieveTransferStatement)
    (hf : QuadraticFamilySieve (concreteQuadraticFamily hi)) :
    QuadraticEstimate :=
  ht hi hf

theorem quadratic_of_primeReciprocity_and_transfer
    (hr : QuadraticPrimeRayReciprocityStatement) (ht : QuadraticSieveTransferStatement)
    (hf : QuadraticFamilySieve
      (concreteQuadraticFamily
        (quadraticRayClassInvariant_of_primeRayReciprocity hr))) :
    QuadraticEstimate :=
  quadratic_of_classInvariant_and_transfer
    (quadraticRayClassInvariant_of_primeRayReciprocity hr) ht hf

theorem quadratic_of_three_inputs (hr : QuadraticPrimeRayReciprocityStatement)
    (hs : QuadraticSquarefreeSieveTransferStatement)
    (hb : QuadraticFiniteBadFactorsStatement)
    (hf : QuadraticFamilySieve
      (concreteQuadraticFamily
        (quadraticRayClassInvariant_of_primeRayReciprocity hr))) :
    QuadraticEstimate :=
  quadratic_of_primeReciprocity_and_transfer hr
    (quadraticSieveTransfer_of_squarefree_and_badFactors hs hb) hf

end QRHShort

#print axioms QRHShort.quadratic_of_primeReciprocity_and_transfer
#print axioms QRHShort.quadratic_of_three_inputs
