import QRHShort.Arithmetic

/-! The frozen sextic symbol at a prime ideal denominator. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.SquarefreeReflection

theorem sexticSymbol_prime {p : Ideal O} (hp : Prime p) (x : O) :
    sexticSymbol p x = sexticAtPrime p x := by
  have hp_ne_bot : p ≠ ⊥ := hp.ne_zero
  have hfac : normalizedFactors p = {p} := by
    simpa using (normalizedFactors_prod_of_prime (m := {p}) (by simpa using hp))
  simp only [sexticSymbol, if_neg hp_ne_bot, hfac,
    Multiset.map_singleton, Multiset.prod_singleton]

end QRHShort.SquarefreeReflection

#print axioms QRHShort.SquarefreeReflection.sexticSymbol_prime
