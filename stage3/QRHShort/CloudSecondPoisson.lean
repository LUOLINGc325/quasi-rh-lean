import QRHShort.CloudSecondPoissonRayExpansion
import QRHShort.CloudSecondPoissonCoprimePoisson
import QRHShort.CloudSecondPoissonMobiusRecombination

/-! Exact assembly of the arithmetic Poisson step. The original arithmetic
and primitive Poisson premises remain explicit; all three internal obligations
are supplied by their independently proved statements. -/

namespace QRHShort.CloudBatch

/-- The frozen arithmetic Poisson step, with precisely its two upstream premises. -/
theorem arithmetic_poisson_step_proved (ha : ArithmeticStatement)
    (hp : PoissonStatement) : SecondPoissonStatement :=
  SecondPoissonProof.arithmetic_poisson_step_of_components ha hp
    second_poisson_ray_expansion_proved second_poisson_coprime_poisson_proved
    second_poisson_mobius_recombination_proved

end QRHShort.CloudBatch
