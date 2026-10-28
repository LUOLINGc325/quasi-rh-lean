import QRHShort.Manuscript

/-! Source coverage for all 23 labelled assertions. `dependencies` records the
intended mathematical arrows and their named source declarations. Proof
completion is determined by the kernel axiom audit, never by this table. -/

namespace QRHShort

structure ManuscriptEntry where
  label : String
  line : Nat
  declaration : Lean.Name
  dependencies : Array Lean.Name

def manuscriptEntries : Array ManuscriptEntry := #[
  ⟨"thm:main", 73, `QRHShort.Manuscript.main,
    #[`QRHShort.Manuscript.mean_square]⟩,
  ⟨"cor:primes-ap", 84, `QRHShort.Manuscript.primes_ap,
    #[`QRHShort.Manuscript.main]⟩,
  ⟨"thm:ms", 679, `QRHShort.Manuscript.mean_square,
    #[`QRHShort.Manuscript.poisson_reduction, `QRHShort.Manuscript.canonical]⟩,
  ⟨"lem:arithmetic", 823, `QRHShort.Manuscript.arithmetic, #[]⟩,
  ⟨"lem:poisson", 875, `QRHShort.Manuscript.poisson,
    #[`QRHShort.Manuscript.arithmetic]⟩,
  ⟨"lem:remove-exclusions", 962, `QRHShort.Manuscript.remove_exclusions,
    #[`QRHShort.Manuscript.arithmetic]⟩,
  ⟨"prop:poisson-reduction", 1000, `QRHShort.Manuscript.poisson_reduction,
    #[`QRHShort.Manuscript.arithmetic, `QRHShort.Manuscript.poisson,
      `QRHShort.Manuscript.remove_exclusions, `QRHShort.Manuscript.smooth_mean_square]⟩,
  ⟨"prop:canonical", 1261, `QRHShort.Manuscript.canonical,
    #[`QRHShort.Manuscript.cube_reduction, `QRHShort.Manuscript.transfer]⟩,
  ⟨"prop:R", 1317, `QRHShort.Manuscript.completed,
    #[`QRHShort.Manuscript.squarefree_completed]⟩,
  ⟨"lem:cube-reduction", 1341, `QRHShort.Manuscript.cube_reduction,
    #[`QRHShort.Manuscript.completed, `QRHShort.Manuscript.arithmetic]⟩,
  ⟨"prop:transfer", 1487, `QRHShort.Manuscript.transfer,
    #[`QRHShort.Manuscript.first_transfer, `QRHShort.Manuscript.second_transfer]⟩,
  ⟨"lem:theta-realization", 1686, `QRHShort.Manuscript.theta_realization,
    #[`QRHShort.Manuscript.arithmetic]⟩,
  ⟨"lem:reflection", 1805, `QRHShort.Manuscript.reflection,
    #[`QRHShort.Manuscript.theta_realization]⟩,
  ⟨"lem:reflection-uniformity", 1847, `QRHShort.Manuscript.reflection_uniformity,
    #[`QRHShort.Manuscript.reflection]⟩,
  ⟨"lem:theta-bounds", 1859, `QRHShort.Manuscript.theta_bounds, #[]⟩,
  ⟨"lem:quadratic", 1886, `QRHShort.Manuscript.quadratic,
    #[`QRHShort.concreteQuadraticFamily_sieve_closed]⟩,
  ⟨"lem:squarefree-completed", 1923, `QRHShort.Manuscript.squarefree_completed,
    #[`QRHShort.Manuscript.reflection, `QRHShort.Manuscript.reflection_uniformity,
      `QRHShort.Manuscript.theta_bounds, `QRHShort.Manuscript.quadratic,
      `QRHShort.Manuscript.smooth, `QRHShort.Manuscript.recombine]⟩,
  ⟨"lem:first-transfer", 2263, `QRHShort.Manuscript.first_transfer,
    #[`QRHShort.Manuscript.poisson, `QRHShort.Manuscript.arithmetic,
      `QRHShort.Manuscript.smooth_mean_square]⟩,
  ⟨"lem:arithmetic-poisson", 2407, `QRHShort.Manuscript.arithmetic_poisson,
    #[`QRHShort.Manuscript.poisson, `QRHShort.Manuscript.arithmetic]⟩,
  ⟨"lem:second-transfer", 2496, `QRHShort.Manuscript.second_transfer,
    #[`QRHShort.Manuscript.arithmetic_poisson, `QRHShort.Manuscript.remove_exclusions,
      `QRHShort.Manuscript.smooth_mean_square]⟩,
  ⟨"lem:smooth", 3491, `QRHShort.Manuscript.smooth, #[]⟩,
  ⟨"lem:smooth-mean-square", 3566, `QRHShort.Manuscript.smooth_mean_square,
    #[`QRHShort.Manuscript.smooth]⟩,
  ⟨"lem:recombine", 3621, `QRHShort.Manuscript.recombine, #[]⟩
]

end QRHShort
