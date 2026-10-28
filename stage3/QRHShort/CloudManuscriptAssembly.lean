import QRHShort.CloudSecondPoisson
import QRHShort.CloudThetaRealization
import QRHShort.SharedThetaBoundsAssembly
import QRHShort.PoissonReduction
import QRHShort.SharedVsquarefreepreparedfinite

/-!
  Exact conditional edges for the frozen manuscript chain.

  These wrappers keep every unresolved upstream proposition explicit.  They
  are intended for the final assembly and do not replace the manuscript
  endpoints or import `QRHShort.Manuscript`.
-/

namespace QRHShort.CloudBatch

theorem arithmetic_poisson_of_components
    (ha : ArithmeticStatement) (hp : PoissonStatement) :
    SecondPoissonStatement :=
  arithmetic_poisson_step_proved ha hp

theorem theta_realization_of_arithmetic
    (ha : ArithmeticStatement) : ThetaRealizationStatement :=
  theta_realization_step_proved ha

theorem theta_bounds_of_components : ThetaBoundsStatement :=
  QRHShort.Shared.theta_bounds_assembled

theorem squarefree_completed_of_components
    (hr : ReflectionStatement) (hu : ReflectionUniformityStatement)
    (hb : ThetaBoundsStatement) (hq : QuadraticEstimate)
    (hs : SmoothSeparationStatement) (hc : RecombinationStatement) :
    SquarefreeCompletedEstimate :=
  squarefree_completed_step_proved hr hu hb hq hs hc

theorem poisson_reduction_of_components
    (ha : ArithmeticStatement) (hp : PoissonStatement)
    (hz : PoissonZeroStatement) (he : RemoveExclusionsStatement)
    (hs : SmoothMeanSquareStatement)
    (hexp : PoissonReductionProof.PoissonDyadicExpansionInput)
    (hblock : PoissonReductionProof.PoissonDyadicBlockInput) :
    PoissonReductionStatement :=
  QRHShort.PoissonReductionProof.poisson_reduction_step_of_components
    ha hp hz he hs hexp hblock

end QRHShort.CloudBatch
