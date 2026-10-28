import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-!
The four-element calculation in paper2.tex:2820--2837.  The coordinates stand
for the square classes of `(-1)^e * (1 + 2 * omega)^f` modulo 4.  This module
proves the finite calculation only; identifying these coordinates with actual
Eisenstein residues is a separate arithmetic obligation.
-/

noncomputable section
set_option autoImplicit false

namespace QRHShort.ArithmeticProof.Ray

abbrev LocalClass := Multiplicative (ZMod 2 × ZMod 2)

/-- Values at `1, -1, lambda, -lambda` are `1, 1, I, -I`. -/
def gamma (x : LocalClass) : ℂ :=
  if x.toAdd.2 = 0 then 1 else if x.toAdd.1 = 0 then Complex.I else -Complex.I

/-- The polar form `(-1)^(e*h + f*g + f*h)`. -/
def correction (x y : LocalClass) : ℂ :=
  if x.toAdd.1 * y.toAdd.2 + x.toAdd.2 * y.toAdd.1 + x.toAdd.2 * y.toAdd.2 = 0
  then 1 else -1

theorem norm_gamma (x : LocalClass) : ‖gamma x‖ = 1 := by
  unfold gamma
  split_ifs <;> simp

theorem correction_sign (x y : LocalClass) :
    correction x y = 1 ∨ correction x y = -1 := by
  unfold correction
  split_ifs <;> simp

theorem correction_symm (x y : LocalClass) : correction x y = correction y x := by
  unfold correction
  congr 1
  simp only [mul_comm, add_comm]

theorem correction_mul_left (x y z : LocalClass) :
    correction (x * y) z = correction x z * correction y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp +decide [correction]

theorem correction_mul_right (x y z : LocalClass) :
    correction x (y * z) = correction x y * correction x z := by
  rw [correction_symm x (y * z), correction_mul_left,
    correction_symm y x, correction_symm z x]

theorem gamma_mul (x y : LocalClass) :
    gamma (x * y) = gamma x * gamma y * correction x y := by
  fin_cases x <;> fin_cases y <;> simp +decide [gamma, correction]

theorem correction_diagonal (x : LocalClass) :
    correction x x = if x.toAdd.2 = 0 then 1 else -1 := by
  fin_cases x <;> simp +decide [correction]

/-- Twisting by a cubic character preserves the polar form and unit norm. -/
def twistedGamma {A : Type*} [Monoid A]
    (k : A →* LocalClass) (t : A →* ℂ) (x : A) : ℂ := t x * gamma (k x)

theorem norm_twistedGamma {A : Type*} [Monoid A]
    (k : A →* LocalClass) (t : A →* ℂ) (ht : ∀ x, t x ^ (3 : ℕ) = 1) (x : A) :
    ‖twistedGamma k t x‖ = 1 := by
  rw [twistedGamma, norm_mul,
    Complex.norm_eq_one_of_pow_eq_one (ht x) (by decide), norm_gamma, mul_one]

theorem twistedGamma_mul {A : Type*} [Monoid A]
    (k : A →* LocalClass) (t : A →* ℂ) (x y : A) :
    twistedGamma k t (x * y) =
      twistedGamma k t x * twistedGamma k t y * correction (k x) (k y) := by
  simp only [twistedGamma, map_mul, gamma_mul]
  ac_rfl

end QRHShort.ArithmeticProof.Ray

#print axioms QRHShort.ArithmeticProof.Ray.correction_mul_left
#print axioms QRHShort.ArithmeticProof.Ray.gamma_mul
#print axioms QRHShort.ArithmeticProof.Ray.correction_diagonal
#print axioms QRHShort.ArithmeticProof.Ray.norm_twistedGamma
#print axioms QRHShort.ArithmeticProof.Ray.twistedGamma_mul
