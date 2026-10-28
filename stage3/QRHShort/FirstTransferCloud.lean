import QRHShort.FirstTransferPoisson
import QRHShort.FirstTransferMultiplicity
import QRHShort.FirstTransferKernel

/-! The first-transfer edge with exactly the four upstream premises allowed
by the assigned task. Each concrete component is proved in its own module. -/

namespace QRHShort

theorem first_transfer_step_cloud (_ha : ArithmeticStatement) (_hp : PoissonStatement)
    (_hz : PoissonZeroStatement) (_hs : SmoothMeanSquareStatement) : FirstTransferEstimate :=
  first_transfer_of_components (first_transfer_poisson_bound _ha _hp _hz)
    first_transfer_finite_reduction first_transfer_kernel_bound _hs

end QRHShort
