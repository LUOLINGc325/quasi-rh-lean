import QRHShort.ThetaBoundsReduction
import QRHShort.CloudThetaBoundsGauss
import QRHShort.CloudThetaBoundsCubeScale
import QRHShort.CloudThetaBoundsMellinShift
import QRHShort.CloudThetaBoundsMellinKernel

namespace QRHShort.Shared

theorem theta_bounds_assembled : QRHShort.ThetaBoundsStatement := by
  exact QRHShort.ThetaBoundsProof.theta_bounds_of_inputs
    QRHShort.CloudBatch.theta_bounds_gauss_proved
    QRHShort.CloudBatch.theta_bounds_cube_scale_proved
    QRHShort.CloudBatch.theta_bounds_mellin_shift_proved
    QRHShort.CloudBatch.theta_bounds_mellin_kernel_proved

end QRHShort.Shared
