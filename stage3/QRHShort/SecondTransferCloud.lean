import QRHShort.SecondTransferStep

namespace QRHShort

/-- The original conditional endpoint, with exactly its three upstream premises. -/
theorem second_transfer_step_cloud (_hp : SecondPoissonStatement)
    (_he : RemoveExclusionsStatement) (_hs : SmoothMeanSquareStatement) :
    SecondTransferEstimate := by
  exact Manuscript.second_transfer_step_from_children _hp _he _hs

end QRHShort
