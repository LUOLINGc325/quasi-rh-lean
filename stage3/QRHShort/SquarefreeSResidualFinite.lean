import QRHShort.SquarefreeUnitResidualCharacters

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort.SquarefreeReflection

theorem SResidueIndex_finite (c : ArithmeticContext) : Finite (SResidueIndex c) := by
  have finite_units : (Set.univ : Set Oˣ).Finite := by
    let η : Oˣ :=
      ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
        (by decide)).unit
    apply (List.finite_toSet [1, -1, η, -η, η ^ 2, -η ^ 2]).subset
    intro u _
    exact IsCyclotomicExtension.Rat.Three.Units.mem
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
  letI : Fintype Oˣ := Set.fintypeOfFiniteUniv finite_units
  infer_instance

theorem SResidual_finite (c : ArithmeticContext) : Set.Finite (Set.range (SResidual c)) := by
  letI : Finite (SResidueIndex c) := SResidueIndex_finite c
  exact Set.finite_range _

end QRHShort.SquarefreeReflection

set_option pp.fullNames true
#print axioms QRHShort.SquarefreeReflection.SResidueIndex_finite
#print axioms QRHShort.SquarefreeReflection.SResidual_finite
