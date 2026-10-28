import QRHShort.SquarefreeCharacterUniformity
import QRHShort.FiniteSupport

/-! Shared row set, separated from the independent quadratic-column draft.
The frozen definitions are copied verbatim from par/V-squarefree@9b3ecfa. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

def sieveRows (S : Finset (Ideal O)) (H : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le H).toFinset.filter
    (fun k => SquarefreeOutside S k ∧ IsRelPrime k (principal 6))

@[simp] theorem mem_sieveRows (S : Finset (Ideal O)) (H : ℝ) (k : Ideal O) :
    k ∈ sieveRows S H ↔ SquarefreeOutside S k ∧ IsRelPrime k (principal 6) ∧
      normIdeal k ≤ H := by
  simp [sieveRows, and_assoc, and_left_comm, and_comm]

end QRHShort.SquarefreeAssembly
