import QRHShort.SecondTransferPoisson
import QRHShort.SecondTransferRegroup
import QRHShort.SecondTransferMeanSquare
import QRHShort.SecondTransferKernel

namespace QRHShort.Manuscript

/-- Complete conditional second transfer from the four proved internal children,
retaining exactly the original three upstream premises. -/
theorem second_transfer_step_from_children (_hp : SecondPoissonStatement)
    (_he : RemoveExclusionsStatement) (_hs : SmoothMeanSquareStatement) : SecondTransferEstimate := by
  exact second_transfer_of_components (second_transfer_poisson_bound _hp)
    second_transfer_regroup (second_transfer_mean_square _he) second_transfer_kernel_bound _hs

end QRHShort.Manuscript
