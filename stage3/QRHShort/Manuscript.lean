import QRHShort.Estimates
import QRHShort.ThetaStatements
import QRHShort.ReflectionUniformity
import QRHShort.SecondPoissonStatements
import QRHShort.SmoothingStatements
import QRHShort.SmoothMeanSquareAssembly
import QRHShort.MainStatements
import QRHShort.RecombinationStatement
import QRHShort.TransferAssembly
import QRHShort.InitialEnergyBridge
import QRHShort.SmoothedSummability
import QRHShort.PointwiseAssembly
import QRHShort.CompletedAssembly
import QRHShort.CubeReductionAssembly
import QRHShort.RemoveExclusionsMobius
import QRHShort.RemoveExclusionsDivisible
import QRHShort.CloudFinalAssembly
import QRHShort.CloudManuscriptAssembly
import QRHShort.SmoothSeparationCandidate3
import QRHShort.SecondTransferCloud
import QRHLean3

/-!
The complete labelled dependency chain of the short 11/12 manuscript, frozen
against paper2.tex at source revision 1581d4cbdd69a0faf34b2089614fe2a814316a6a.

The dependency arrows below are the original manuscript statements. Their
external literature inputs remain explicit in `External.lean`; the endpoint
theorems are checked by the kernel against those inputs.
The `*_step` declarations expose the intended dependency arrows; the named
manuscript endpoints apply these steps without hiding their assumptions.
-/

namespace QRHShort.Manuscript

/-- `lem:arithmetic`, line 823. Reciprocity and a sufficiently large ray modulus. -/
theorem arithmetic : ArithmeticStatement := by
  exact QRHShort.CloudBatch.arithmetic_proved

/-- `lem:recombine`, line 3621. Both finite and integral formulations. -/
theorem recombine : RecombinationStatement := recombination_statement

/-- `lem:smooth`, line 3491. Mellin separation and weighted Fourier decay. -/
theorem smooth : SmoothSeparationStatement := by
  exact smooth_separation_statement_candidate

theorem smooth_mean_square_step
    (_hs : SmoothSeparationStatement) : SmoothMeanSquareStatement := by
  exact smooth_mean_square_of_separation _hs

/-- `lem:smooth-mean-square`, line 3566. -/
theorem smooth_mean_square : SmoothMeanSquareStatement := smooth_mean_square_step smooth

theorem poisson_step (_ha : ArithmeticStatement) :
    PoissonStatement ∧ PoissonZeroStatement := by
  exact QRHShort.CloudBatch.poisson_proved _ha

/-- `lem:poisson`, line 875, including its zero-frequency assertion. -/
theorem poisson : PoissonStatement ∧ PoissonZeroStatement := poisson_step arithmetic

theorem remove_exclusions_step (_ha : ArithmeticStatement) : RemoveExclusionsStatement := by
  exact QRHShort.RemoveExclusionsProof.remove_exclusions_step_of_arithmetic _ha
    QRHShort.RemoveExclusionsProof.mobiusIndicator
    QRHShort.RemoveExclusionsProof.divisibleColumn

/-- `lem:remove-exclusions`, line 962. -/
theorem remove_exclusions : RemoveExclusionsStatement := remove_exclusions_step arithmetic

theorem theta_realization_step (_ha : ArithmeticStatement) : ThetaRealizationStatement := by
  exact QRHShort.CloudBatch.theta_realization_proved _ha

/-- `lem:theta-realization`, line 1686. -/
theorem theta_realization : ThetaRealizationStatement := theta_realization_step arithmetic

theorem reflection_step (_ht : ThetaRealizationStatement) : ReflectionStatement := by
  exact QRHShort.CloudBatch.reflection_proved _ht

/-- `lem:reflection`, line 1805. -/
theorem reflection : ReflectionStatement := reflection_step theta_realization

theorem reflection_uniformity_step (_hr : ReflectionStatement) : ReflectionUniformityStatement := by
  exact reflection_uniformity_of_reflection _hr

/-- `lem:reflection-uniformity`, line 1847. -/
theorem reflection_uniformity : ReflectionUniformityStatement := reflection_uniformity_step reflection

/-- `lem:theta-bounds`, line 1859. Explicit coefficients and Mellin decay. -/
theorem theta_bounds : ThetaBoundsStatement := by
  exact QRHShort.CloudBatch.theta_bounds_proved

/-- `lem:quadratic`, line 1886. The concrete sextic-cube family still has to be
verified against the hypotheses of the external quadratic-family sieve. -/
theorem quadratic : QuadraticEstimate := by
  exact QRHShort.CloudBatch.quadratic_proved

theorem squarefree_completed_step (_hr : ReflectionStatement)
    (_hu : ReflectionUniformityStatement) (_hb : ThetaBoundsStatement)
    (_hq : QuadraticEstimate) (_hs : SmoothSeparationStatement)
    (_hc : RecombinationStatement) : SquarefreeCompletedEstimate := by
  exact QRHShort.CloudBatch.squarefree_completed_of_components _hr _hu _hb _hq _hs _hc

/-- `lem:squarefree-completed`, line 1923. -/
theorem squarefree_completed : SquarefreeCompletedEstimate :=
  squarefree_completed_step reflection reflection_uniformity theta_bounds quadratic smooth recombine

theorem completed_step (_hs : SquarefreeCompletedEstimate) : CompletedEstimate := by
  exact completed_of_squarefree _hs

/-- `prop:R`, line 1317. Completed mean square. -/
theorem completed : CompletedEstimate := completed_step squarefree_completed

theorem cube_reduction_step (_ha : ArithmeticStatement)
    (_hr : CompletedEstimate) : CubeEstimate :=
  cube_estimate_of_arithmetic_completed _ha _hr

/-- `lem:cube-reduction`, line 1341. -/
theorem cube_reduction : CubeEstimate := cube_reduction_step arithmetic completed

theorem first_transfer_step (_ha : ArithmeticStatement) (_hp : PoissonStatement)
    (_hz : PoissonZeroStatement) (_hs : SmoothMeanSquareStatement) : FirstTransferEstimate := by
  exact QRHShort.CloudBatch.first_transfer_proved _ha _hp _hz _hs

/-- `lem:first-transfer`, line 2263. -/
theorem first_transfer : FirstTransferEstimate :=
  first_transfer_step arithmetic poisson.1 poisson.2 smooth_mean_square

theorem arithmetic_poisson_step (_ha : ArithmeticStatement)
    (_hp : PoissonStatement) : SecondPoissonStatement := by
  exact QRHShort.CloudBatch.arithmetic_poisson_proved _ha _hp

/-- `lem:arithmetic-poisson`, line 2407. -/
theorem arithmetic_poisson : SecondPoissonStatement := arithmetic_poisson_step arithmetic poisson.1

theorem second_transfer_step (_hp : SecondPoissonStatement)
    (_he : RemoveExclusionsStatement) (_hs : SmoothMeanSquareStatement) : SecondTransferEstimate := by
  exact QRHShort.second_transfer_step_cloud _hp _he _hs

/-- `lem:second-transfer`, line 2496. -/
theorem second_transfer : SecondTransferEstimate :=
  second_transfer_step arithmetic_poisson remove_exclusions smooth_mean_square

theorem transfer_step (h₁ : FirstTransferEstimate)
    (h₂ : SecondTransferEstimate) : TransferEstimate :=
  transfer_estimate_of_first_second h₁ h₂

/-- `prop:transfer`, line 1487. -/
theorem transfer : TransferEstimate := transfer_step first_transfer second_transfer

theorem canonical_step (hc : CubeEstimate) (ht : TransferEstimate) : CanonicalEstimate :=
  canonical_estimate_of_cube_transfer hc ht

/-- `prop:canonical`, line 1261, using the actual energy induction and the
constructed smooth row weight. -/
theorem canonical : CanonicalEstimate := canonical_step cube_reduction transfer

theorem poisson_reduction_step (_ha : ArithmeticStatement)
    (_hp : PoissonStatement) (_hz : PoissonZeroStatement)
    (_he : RemoveExclusionsStatement) (_hs : SmoothMeanSquareStatement) :
    PoissonReductionStatement := by
  exact QRHShort.CloudBatch.poisson_reduction_proved _ha _hp _hz _he _hs

/-- `prop:poisson-reduction`, line 1000. -/
theorem poisson_reduction : PoissonReductionStatement :=
  poisson_reduction_step arithmetic poisson.1 poisson.2 remove_exclusions smooth_mean_square

/-- Unlabelled specialization of the canonical range used in `thm:ms`. -/
theorem initial_energy_of_canonical (hc : CanonicalEstimate) :
    ∀ θ : ℝ, 0 < θ → θ ≤ (1 : ℝ) / 10 → InitialEnergyEstimate θ := by
  intro θ hθ hθupper
  exact initial_energy_estimate_of_canonical hc hθ hθupper

/-- `thm:ms`, line 679. -/
theorem mean_square : MeanSquareEstimate := by
  intro θ ε hθ hθmax hε
  exact poisson_reduction θ hθ hθmax
    (initial_energy_of_canonical canonical θ hθ hθmax) ε hε

/-- Unlabelled prime-sixth-power extraction in the proof of `thm:main`. -/
theorem pointwise_of_mean_square (hm : MeanSquareEstimate) : PointwiseMobiusEstimate :=
  pointwise_of_meanSquare hm

/-- The Mellin reciprocal identity and the Dirichlet base-change step are
internal obligations, not implicit extra axioms. -/
theorem main_of_pointwise (_hp : PointwiseMobiusEstimate) : MainStatement := by
  exact QRHShort.CloudBatch.main_of_pointwise_proved _hp

/-- `thm:main`, line 73: actual Hecke and Dirichlet L-functions. -/
theorem main : MainStatement := main_of_pointwise (pointwise_of_mean_square mean_square)

theorem primes_ap_step (_hm : MainStatement) : PrimeAPStatement := by
  exact QRHShort.CloudBatch.prime_ap_proved _hm

/-- `cor:primes-ap`, line 84. -/
theorem primes_ap : PrimeAPStatement := primes_ap_step main

end QRHShort.Manuscript
