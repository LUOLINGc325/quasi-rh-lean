import QRHShort.QuotientSixthRoot
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

/-!
The lattice-triviality and representative invariance needed by the Gauss CRT
calculation. These use the actual integral power basis and selected embedding.
The frozen EisensteinBasis/AdditiveCharacter files are not changed.
-/

noncomputable section
open Classical

namespace QRHShort

def first_transfer_eisensteinPowerBasis : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

theorem first_transfer_eisensteinPowerBasis_dim : first_transfer_eisensteinPowerBasis.dim = 2 := by
  change (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

def first_transfer_eisensteinBasis : Module.Basis (Fin 2) ℤ O :=
  first_transfer_eisensteinPowerBasis.basis.reindex (finCongr first_transfer_eisensteinPowerBasis_dim)

theorem first_transfer_eisensteinBasis_zero : first_transfer_eisensteinBasis 0 = 1 := by
  rw [first_transfer_eisensteinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change first_transfer_eisensteinPowerBasis.gen ^ (0 : ℕ) = 1
  exact pow_zero _

theorem first_transfer_eisensteinBasis_one : first_transfer_eisensteinBasis 1 = omega := by
  rw [first_transfer_eisensteinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change first_transfer_eisensteinPowerBasis.gen ^ (1 : ℕ) = omega
  rw [pow_one]
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

theorem first_transfer_eisenstein_coords (a : O) :
    a = (first_transfer_eisensteinBasis.repr a 0 : O) + (first_transfer_eisensteinBasis.repr a 1 : O) * omega := by
  simpa [Fin.sum_univ_two, first_transfer_eisensteinBasis_zero, first_transfer_eisensteinBasis_one,
    Algebra.smul_def] using (first_transfer_eisensteinBasis.sum_repr a).symm

@[simp] theorem first_transfer_embedding_intCast (x : ℤ) : embedding (x : O) = (x : ℂ) := by
  simpa only [embeddingHom_apply] using map_intCast embeddingHom x

theorem first_transfer_embedding_omega_im : (embedding omega).im = Real.sqrt 3 / 2 := by
  let w := embedding omega
  have hp : w ^ 2 + w + 1 = 0 := by
    simpa only [embedding_add, embedding_pow, embedding_one, embedding_zero] using
      congrArg embedding omega_sq_add_omega_add_one
  have hr : w.re ^ 2 - w.im ^ 2 + w.re + 1 = 0 := by
    simpa only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
      Complex.zero_re] using congrArg Complex.re hp
  have hi : 2 * w.re * w.im + w.im = 0 := by
    have h := congrArg Complex.im hp
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im,
      Complex.zero_im] at h
    nlinarith
  have hne : w.im ≠ 0 := by
    intro h
    rw [h] at hr
    nlinarith [sq_nonneg (w.re + (1 : ℝ) / 2)]
  have hre : w.re = -(1 : ℝ) / 2 := by
    have hf : (2 * w.re + 1) * w.im = 0 := by nlinarith
    have hz := (mul_eq_zero.mp hf).resolve_right hne
    linarith
  have hnonneg : 0 ≤ w.im := by
    dsimp [w, embedding]
    split_ifs with h
    · exact h.le
    · simpa only [Complex.star_def, Complex.conj_im] using
        neg_nonneg.mpr (le_of_not_gt h)
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : w.im ^ 2 = (3 : ℝ) / 4 := by nlinarith
  change w.im = _
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

theorem first_transfer_additiveCharacter_add (z w : ℂ) :
    additiveCharacter (z + w) = additiveCharacter z * additiveCharacter w := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_im]
  push_cast
  ring

@[simp] theorem first_transfer_additiveCharacter_embedding (a : O) :
    additiveCharacter (embedding a) = 1 := by
  let y : ℤ := first_transfer_eisensteinBasis.repr a 1
  have him : (embedding a).im = (y : ℝ) * Real.sqrt 3 / 2 := by
    rw [first_transfer_eisenstein_coords a, embedding_add, embedding_mul,
      first_transfer_embedding_intCast, first_transfer_embedding_intCast]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, zero_add, add_zero, first_transfer_embedding_omega_im]
    dsimp [y]
    ring
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hexp : 4 * Real.pi * (embedding a).im / Real.sqrt 3 =
      (y : ℝ) * (2 * Real.pi) := by
    rw [him]
    field_simp [hs]
    <;> ring
  rw [additiveCharacter, hexp]
  push_cast
  simpa only [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I y

theorem first_transfer_additiveCharacter_add_embedding (z : ℂ) (a : O) :
    additiveCharacter (z + embedding a) = additiveCharacter z := by
  rw [first_transfer_additiveCharacter_add, first_transfer_additiveCharacter_embedding, mul_one]

@[simp] theorem first_transfer_additiveCharacter_zero : additiveCharacter 0 = 1 := by
  simp [additiveCharacter]

/-- The additive phase is unchanged by any change of integral representative
modulo its nonzero principal denominator. -/
theorem first_transfer_gauss_additive_div_congr {g x y : O} (hg : g ≠ 0)
    (hxy : Ideal.Quotient.mk (principal g) x = Ideal.Quotient.mk (principal g) y) :
    additiveCharacter (embedding x / embedding g) =
      additiveCharacter (embedding y / embedding g) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hxy)
  have hx : x = y + g * z := by linear_combination hz
  have hg' : embedding g ≠ 0 := fun h => hg (embedding_eq_zero.mp h)
  have harg : embedding x / embedding g = embedding y / embedding g + embedding z := by
    rw [hx, embedding_add, embedding_mul]
    field_simp [hg']
  rw [harg, first_transfer_additiveCharacter_add_embedding]

end QRHShort
