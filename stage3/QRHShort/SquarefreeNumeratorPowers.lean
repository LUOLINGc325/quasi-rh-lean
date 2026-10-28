import QRHShort.SquarefreeNumeratorProducts

/-! Natural powers in the numerator of the frozen sextic symbol. -/

noncomputable section
namespace QRHShort.SquarefreeReflection

theorem sexticSymbol_pow_numerator (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (a : O) (m : ℕ) :
    sexticSymbol n (a ^ m) = sexticSymbol n a ^ m := by
  induction m with
  | zero => simpa only [pow_zero] using sexticSymbol_one_of_outside c hn
  | succ m ih =>
    rw [pow_succ, sexticSymbol_mul_numerator c hn, ih, pow_succ]

end QRHShort.SquarefreeReflection

#print axioms QRHShort.SquarefreeReflection.sexticSymbol_pow_numerator
