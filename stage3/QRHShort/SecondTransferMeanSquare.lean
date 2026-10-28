import QRHShort.SecondTransferPRMMComplete

namespace QRHShort

/-- Complete child M from the finite arithmetic blocks and the full dyadic sum. -/
theorem second_transfer_mean_square (_he : RemoveExclusionsStatement) :
    SecondTransferMeanSquareStatement := by
  exact second_transfer_mean_square_proved _he

end QRHShort
