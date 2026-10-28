import QRHShort.QuotientSixthRoot
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The actual Eisenstein integral basis and its positive determinant norm.
The coordinate decomposition is shared by the norm-lift and Poisson proofs. -/

noncomputable section
namespace QRHShort
open Module

def eisensteinPowerBasis : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

theorem eisensteinPowerBasis_dim : eisensteinPowerBasis.dim = 2 := by
  change (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

def eisensteinBasis : Basis (Fin 2) ℤ O :=
  eisensteinPowerBasis.basis.reindex (finCongr eisensteinPowerBasis_dim)

theorem eisensteinBasis_zero : eisensteinBasis 0 = 1 := by
  simp [eisensteinBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast]

theorem eisensteinBasis_one : eisensteinBasis 1 = omega := by
  have hgen : eisensteinPowerBasis.gen = omega :=
    IsPrimitiveRoot.integralPowerBasis_gen (IsCyclotomicExtension.zeta_spec 3 ℚ K)
  rw [eisensteinBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply_coe]
  simpa only [Fin.val_one, pow_one] using hgen

theorem eisenstein_coords (a : O) :
    a = (eisensteinBasis.repr a 0 : O) + (eisensteinBasis.repr a 1 : O) * omega := by
  simpa [Fin.sum_univ_two, eisensteinBasis_zero, eisensteinBasis_one,
    Algebra.smul_def] using
    (eisensteinBasis.sum_repr a).symm

theorem eisenstein_repr_pair (x y : ℤ) :
    (eisensteinBasis.repr ((x : O) + (y : O) * omega) : Fin 2 → ℤ) = ![x, y] := by
  have h : (x : O) + (y : O) * omega =
      x • eisensteinBasis 0 + y • eisensteinBasis 1 := by
    simp [eisensteinBasis_zero, eisensteinBasis_one, Algebra.smul_def]
  rw [h, map_add, map_smul, map_smul]
  ext i
  fin_cases i <;> simp [Basis.repr_self_apply]

/-- In this integral basis the determinant norm is the positive definite
Eisenstein quadratic form, including at zero. -/
theorem eisenstein_norm (a : O) :
    Algebra.norm ℤ a = eisensteinBasis.repr a 0 ^ 2 -
      eisensteinBasis.repr a 0 * eisensteinBasis.repr a 1 +
      eisensteinBasis.repr a 1 ^ 2 := by
  let x := eisensteinBasis.repr a 0
  let y := eisensteinBasis.repr a 1
  have ha : a = (x : O) + (y : O) * omega := eisenstein_coords a
  have hmul : a * omega = ((-y : ℤ) : O) + ((x - y : ℤ) : O) * omega := by
    rw [ha]
    push_cast
    calc
      ((x : O) + (y : O) * omega) * omega =
          -(y : O) + ((x : O) - (y : O)) * omega +
            (y : O) * (omega ^ 2 + omega + 1) := by ring
      _ = _ := by rw [omega_sq_add_omega_add_one]; ring
  have hmatrix : Algebra.leftMulMatrix eisensteinBasis a = !![x, -y; y, x - y] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases j
    · change (eisensteinBasis.repr (a * eisensteinBasis 0)) i =
        (![![x, -y], ![y, x - y]] : Fin 2 → Fin 2 → ℤ) i 0
      rw [eisensteinBasis_zero, mul_one,
        ha, eisenstein_repr_pair]
      fin_cases i <;> rfl
    · change (eisensteinBasis.repr (a * eisensteinBasis 1)) i =
        (![![x, -y], ![y, x - y]] : Fin 2 → Fin 2 → ℤ) i 1
      rw [eisensteinBasis_one, hmul,
        eisenstein_repr_pair]
      fin_cases i <;> rfl
  rw [Algebra.norm_eq_matrix_det eisensteinBasis, hmatrix, Matrix.det_fin_two]
  dsimp [x, y]
  ring

theorem eisenstein_norm_nonneg (a : O) : 0 ≤ Algebra.norm ℤ a := by
  rw [eisenstein_norm]
  have h₁ := sq_nonneg (2 * eisensteinBasis.repr a 0 - eisensteinBasis.repr a 1)
  have h₂ := sq_nonneg (eisensteinBasis.repr a 1)
  nlinarith

theorem principal_absNorm_int (a : O) :
    ((principal a).absNorm : ℤ) = Algebra.norm ℤ a := by
  rw [principal, Ideal.absNorm_span_singleton, Int.natCast_natAbs,
    abs_of_nonneg (eisenstein_norm_nonneg a)]

end QRHShort
