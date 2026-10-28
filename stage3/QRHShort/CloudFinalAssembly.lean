import QRHShort.ArithmeticReduction
import QRHShort.ArithmeticPrimaryClasses
import QRHShort.ArithmeticCubicFour
import QRHShort.ArithmeticQuadraticGauss
import QRHShort.ArithmeticSexticReciprocity
import QRHShort.ArithmeticMinusOne
import QRHShort.CubicGaussEvaluation
import QRHShort.MixedGaussExtension
import QRHShort.InverseGaussEvaluation
import QRHShort.CloudArithmeticInverseSexticPrimitive
import QRHShort.CloudArithmeticInverseAdditivePrimitive
import QRHShort.PoissonAssembly
import QRHShort.PoissonRadialSummability
import QRHShort.PoissonResidue
import QRHShort.PrimitiveGauss
import QRHShort.PoissonPrincipalZero
import QRHShort.FirstTransferCloud
import QRHShort.CloudSecondPoisson
import QRHShort.CloudThetaRealization
import QRHShort.SharedThetaBoundsAssembly
import QRHShort.CloudReflectionMellinTransfer
import QRHShort.CloudReflectionFunctionalEquation
import QRHShort.ReflectionReduction
import QRHShort.QuadraticPrimeReciprocity
import QRHShort.QuadraticSquarefreeTransferProof
import QRHShort.QuadraticBadFactors
import QRHShort.QuadraticSieveTransfer
import QRHShort.QuadraticGLAssembly
import QRHShort.CloudPoissonReductionDyadicExpansion
import QRHShort.CloudPoissonReductionDyadicBlock
import QRHShort.PoissonReduction
import QRHShort.DirichletBaseChange
import QRHShort.CloudPrimesAP
import QRHShort.HeckeNonvanishing

namespace QRHShort.CloudBatch

/-- The five accepted arithmetic children close the original arithmetic node. -/
theorem arithmetic_proved : ArithmeticStatement := by
  apply ArithmeticProof.arithmetic_of_inputs
  · apply ArithmeticProof.Ray.rayReciprocity_of_local_inputs
    · exact ArithmeticProof.Ray.primarySquareClassRay
    · exact ArithmeticProof.Ray.cubicFourRayCharacter
    · exact ArithmeticProof.Ray.quadraticGaussSquareClass
    · exact ArithmeticProof.Ray.sexticSquareClassReciprocity
    · exact ArithmeticProof.Ray.sexticMinusOneSquareClass
  · exact ArithmeticProof.CubicGauss.cubicGaussEvaluation_of_crt
      ArithmeticProof.MixedGauss.cubicGaussCRT
  · exact ArithmeticProof.MixedGauss.mixedGaussEvaluation
  · exact ArithmeticProof.InverseGauss.inverseGaussEvaluation_of_primitivity
      arithmetic_inverse_sextic_primitive_proved
      arithmetic_inverse_additive_primitive_proved
  · exact ArithmeticProof.MixedGauss.cubicGaussCRT

/-- The accepted residue, primitive, and radial Poisson children close Poisson. -/
theorem poisson_proved : ArithmeticStatement →
    PoissonStatement ∧ PoissonZeroStatement := by
  intro ha
  exact PoissonProof.poisson_step_of_components ha
    PoissonProof.coprimeExpansion
    PoissonProof.Residue.residueClassPoisson
    PoissonProof.PrimitiveGauss.primitiveGauss
    PoissonProof.principalZero

/-- The accepted theta assembly retains exactly its arithmetic premise. -/
theorem theta_realization_proved (ha : ArithmeticStatement) :
    ThetaRealizationStatement := theta_realization_step_proved ha

theorem theta_bounds_proved : ThetaBoundsStatement :=
  QRHShort.Shared.theta_bounds_assembled

/-- The accepted reflection children retain exactly the theta premise. -/
theorem reflection_proved (ht : ThetaRealizationStatement) : ReflectionStatement :=
  ReflectionProof.reflection_step_of_components
    reflection_functional_equation_proved
    reflection_mellin_transfer_proved ht

/-- The accepted quadratic children close the frozen estimate. -/
theorem quadratic_proved : QuadraticEstimate := by
  exact quadraticFiniteBadFactors
    (quadraticSquarefreeSieveTransfer
      (quadraticRayClassInvariant_of_primeRayReciprocity
        quadraticPrimeRayReciprocity)
      concreteQuadraticFamily_sieve_closed)

/-- The accepted first transfer retains its four original upstream premises. -/
theorem first_transfer_proved (ha : ArithmeticStatement) (hp : PoissonStatement)
    (hz : PoissonZeroStatement) (hs : SmoothMeanSquareStatement) :
    FirstTransferEstimate :=
  first_transfer_step_cloud ha hp hz hs

/-- The accepted second-Poisson parent retains arithmetic and Poisson premises. -/
theorem arithmetic_poisson_proved (ha : ArithmeticStatement)
    (hp : PoissonStatement) : SecondPoissonStatement :=
  arithmetic_poisson_step_proved ha hp

/-- The two accepted Poisson-reduction children are internal and exact. -/
theorem poisson_reduction_proved (ha : ArithmeticStatement) (hp : PoissonStatement)
    (hz : PoissonZeroStatement) (he : RemoveExclusionsStatement)
    (hs : SmoothMeanSquareStatement) : PoissonReductionStatement :=
  PoissonReductionProof.poisson_reduction_step_of_components ha hp hz he hs
    poisson_reduction_dyadic_expansion_proved
    poisson_reduction_dyadic_block_proved

/-- The pointwise-to-main edge uses the proven reciprocal-series identity and
keeps only the original pointwise estimate as premise. -/
theorem main_of_pointwise_proved (hp : PointwiseMobiusEstimate) : MainStatement := by
  exact main_of_hecke_zeroFree (heckeZeroFree_of_pointwise hp)

theorem prime_ap_proved (hm : MainStatement) : PrimeAPStatement :=
  primes_ap_step_proved hm

end QRHShort.CloudBatch
