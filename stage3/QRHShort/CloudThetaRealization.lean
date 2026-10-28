import QRHShort.ThetaTauSlice
import QRHShort.ThetaGaussLambda
import QRHShort.CloudThetaRealizationFourierInversion
import QRHShort.CloudThetaRealizationSummability

namespace QRHShort.CloudBatch

/-- Deterministic assembly of the original endpoint from its proved inputs. -/
theorem theta_realization_step_proved (ha : ArithmeticStatement) :
    ThetaRealizationStatement :=
  ThetaRealizationProof.theta_realization_step_of_components ha
    (ThetaRealizationProof.coefficientBridge_of_children
      ThetaRealizationProof.tauCubeSliceUniqueness
      ThetaRealizationProof.cubicGaussLambdaNormalization)
    theta_realization_fourier_inversion_proved
    theta_realization_summability_proved

end QRHShort.CloudBatch
