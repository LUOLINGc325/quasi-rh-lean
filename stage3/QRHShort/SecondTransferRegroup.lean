import QRHShort.SecondTransferPRMRComplete

namespace QRHShort

/-- Pending child R: the signed preimage-factorization identity and finite
reindexing into `(character,r,f',k')` with `f' | k'`. Use the scalar identities
in SecondTransferScalar; their local prime identity does not supply this
factorization bijection or the convergence/truncation proofs. -/
theorem second_transfer_regroup : SecondTransferRegroupStatement := by
  exact second_transfer_regroup_proved

end QRHShort
