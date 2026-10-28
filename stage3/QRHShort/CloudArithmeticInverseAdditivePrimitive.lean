import QRHShort.InverseGaussEvaluation
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Primitivity for the literal additive phase at the chosen primary generator.
The trace tests prove nondegeneracy over every principal quotient directly. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch.InverseAdditive
open ArithmeticProof
open SquarefreeReflection.RayValuePrerequisites

private def integralPB : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

private theorem integralPB_dim : integralPB.dim = 2 := by
  change (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

private def integralBasis : Module.Basis (Fin 2) ℤ O :=
  integralPB.basis.reindex (finCongr integralPB_dim)

private theorem integralBasis_zero : integralBasis 0 = 1 := by
  rw [integralBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change integralPB.gen ^ (0 : ℕ) = 1
  exact pow_zero _

private theorem integralBasis_one : integralBasis 1 = omega := by
  rw [integralBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change integralPB.gen ^ (1 : ℕ) = omega
  rw [pow_one]
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

private theorem integral_coords (a : O) :
    a = (integralBasis.repr a 0 : O) + (integralBasis.repr a 1 : O) * omega := by
  simpa [Fin.sum_univ_two, integralBasis_zero, integralBasis_one, Algebra.smul_def] using
    (integralBasis.sum_repr a).symm

private theorem emb_add (a b : O) : embedding (a + b) = embedding a + embedding b := by
  simpa only [embeddingHom_apply] using map_add embeddingHom a b

private theorem emb_int (a : ℤ) : embedding (a : O) = (a : ℂ) := by
  simpa only [embeddingHom_apply] using map_intCast embeddingHom a

private theorem emb_zero : embedding (0 : O) = 0 := by
  simpa only [embeddingHom_apply] using map_zero embeddingHom

private theorem emb_omega_parts :
    (embedding omega).re = -(1 : ℝ) / 2 ∧
      (embedding omega).im = Real.sqrt 3 / 2 := by
  let w := embedding omega
  have hp : w ^ 2 + w + 1 = 0 := by
    simpa only [emb_add, embedding_pow, embedding_one, emb_zero] using
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
  refine ⟨hre, ?_⟩
  change w.im = _
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

private theorem emb_omega_re : (embedding omega).re = -(1 : ℝ) / 2 :=
  emb_omega_parts.1

private theorem emb_omega_im : (embedding omega).im = Real.sqrt 3 / 2 :=
  emb_omega_parts.2

private theorem phase_add (z w : ℂ) :
    additiveCharacter (z + w) = additiveCharacter z * additiveCharacter w := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_im]
  push_cast
  ring

private theorem phase_zero : additiveCharacter 0 = 1 := by simp [additiveCharacter]

private theorem phase_embedding (a : O) : additiveCharacter (embedding a) = 1 := by
  let y : ℤ := integralBasis.repr a 1
  have him : (embedding a).im = (y : ℝ) * Real.sqrt 3 / 2 := by
    rw [integral_coords a, emb_add, embedding_mul, emb_int, emb_int]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, zero_add, add_zero, emb_omega_im]
    dsimp only [y]
    ring
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hexp : 4 * Real.pi * (embedding a).im / Real.sqrt 3 = (y : ℝ) * (2 * Real.pi) := by
    rw [him]
    field_simp [hs]
    ring
  rw [additiveCharacter, hexp]
  push_cast
  simpa only [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I y

private theorem phase_add_embedding (z : ℂ) (a : O) :
    additiveCharacter (z + embedding a) = additiveCharacter z := by
  rw [phase_add, phase_embedding, mul_one]

private theorem phase_one_im (z : ℂ) (hz : additiveCharacter z = 1) :
    ∃ n : ℤ, 2 * z.im / Real.sqrt 3 = (n : ℝ) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz
  have hi := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, Complex.intCast_re,
    Complex.intCast_im, zero_mul, zero_add] at hi
  norm_num [Complex.mul_re] at hi
  refine ⟨n, ?_⟩
  apply mul_right_cancel₀ (show 2 * Real.pi ≠ 0 by positivity)
  calc
    (2 * z.im / Real.sqrt 3) * (2 * Real.pi) = 4 * Real.pi * z.im / Real.sqrt 3 := by ring
    _ = (n : ℝ) * (2 * Real.pi) := hi

/-- The two literal trace tests recover both integral Eisenstein coordinates. -/
private theorem phase_pair_integral (z : ℂ)
    (h1 : additiveCharacter z = 1) (hw : additiveCharacter (z * embedding omega) = 1) :
    ∃ a : O, z = embedding a := by
  obtain ⟨y, hy⟩ := phase_one_im z h1
  obtain ⟨k, hk⟩ := phase_one_im (z * embedding omega) hw
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hy' : 2 * z.im = (y : ℝ) * Real.sqrt 3 := (div_eq_iff hs).mp hy
  have hk' : 2 * (z * embedding omega).im = (k : ℝ) * Real.sqrt 3 := (div_eq_iff hs).mp hk
  simp only [Complex.mul_im, emb_omega_re, emb_omega_im] at hk'
  have hre : z.re = (k : ℝ) + (y : ℝ) / 2 := by
    apply mul_right_cancel₀ hs
    nlinarith [hy', hk']
  refine ⟨((k + y : ℤ) : O) + (y : O) * omega, ?_⟩
  rw [emb_add, embedding_mul, emb_int, emb_int]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      emb_omega_re, zero_mul, sub_zero, Int.cast_add]
    linarith [hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      emb_omega_im, zero_mul, add_zero, zero_add]
    linarith [hy']

private theorem emb_sub (a b : O) : embedding (a - b) = embedding a - embedding b := by
  simpa only [embeddingHom_apply] using map_sub embeddingHom a b

private theorem lift_spec (n : Ideal O) (x : O ⧸ n) :
    Ideal.Quotient.mk n (residueLift n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

private theorem phase_div_congr {q x y : O} (hq : q ≠ 0)
    (hxy : Ideal.Quotient.mk (principal q) x = Ideal.Quotient.mk (principal q) y) :
    additiveCharacter (embedding x / embedding q) =
      additiveCharacter (embedding y / embedding q) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hxy)
  have hx : x = y + q * z := by linear_combination hz
  have harg : embedding x / embedding q = embedding y / embedding q + embedding z := by
    rw [hx, emb_add, embedding_mul]
    field_simp [embedding_ne_zero hq]
  rw [harg, phase_add_embedding]

private def pairingChar (q : O) (hq : q ≠ 0) (m : O) :
    AddChar (O ⧸ principal q) ℂ where
  toFun x := additiveCharacter (embedding (m * residueLift (principal q) x) / embedding q)
  map_zero_eq_one' := by
    have heq : Ideal.Quotient.mk (principal q) (m * residueLift (principal q) 0) =
        Ideal.Quotient.mk (principal q) 0 := by
      rw [map_mul, lift_spec, mul_zero, map_zero]
    rw [phase_div_congr hq heq, emb_zero, zero_div, phase_zero]
  map_add_eq_mul' x y := by
    have heq : Ideal.Quotient.mk (principal q) (m * residueLift (principal q) (x + y)) =
        Ideal.Quotient.mk (principal q)
          (m * residueLift (principal q) x + m * residueLift (principal q) y) := by
      simp only [map_mul, map_add, lift_spec, mul_add]
    rw [phase_div_congr hq heq, emb_add, add_div, phase_add]

private theorem pairingChar_mk (q : O) (hq : q ≠ 0) (m x : O) :
    pairingChar q hq m (Ideal.Quotient.mk (principal q) x) =
      additiveCharacter (embedding (m * x) / embedding q) := by
  apply phase_div_congr hq
  simp only [map_mul, lift_spec]

/-- Nondegeneracy for the literal quotient pairing, including a unit modulus. -/
private theorem pairingChar_eq_zero_iff (q : O) (hq : q ≠ 0) (m : O) :
    pairingChar q hq m = 0 ↔ Ideal.Quotient.mk (principal q) m = 0 := by
  constructor
  · intro hchar
    have h1 := congrArg (fun χ : AddChar (O ⧸ principal q) ℂ =>
      χ (Ideal.Quotient.mk (principal q) 1)) hchar
    have hw := congrArg (fun χ : AddChar (O ⧸ principal q) ℂ =>
      χ (Ideal.Quotient.mk (principal q) omega)) hchar
    simp only [pairingChar_mk, mul_one, AddChar.zero_apply] at h1
    simp only [pairingChar_mk, AddChar.zero_apply, embedding_mul] at hw
    have hw' : additiveCharacter ((embedding m / embedding q) * embedding omega) = 1 := by
      convert hw using 1
      congr 1
      ring
    obtain ⟨a, ha⟩ := phase_pair_integral (embedding m / embedding q) h1 hw'
    have hemb : embedding m = embedding (q * a) := by
      rw [embedding_mul, ← ha]
      field_simp [embedding_ne_zero hq]
    have hm : m = q * a := by
      apply sub_eq_zero.mp
      by_contra hne
      apply embedding_ne_zero hne
      rw [emb_sub, hemb, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨a, hm⟩)
  · intro hm
    ext x
    change additiveCharacter (embedding (m * residueLift (principal q) x) / embedding q) = 1
    have heq : Ideal.Quotient.mk (principal q) (m * residueLift (principal q) x) =
        Ideal.Quotient.mk (principal q) 0 := by
      rw [map_mul, hm, zero_mul, map_zero]
    rw [phase_div_congr hq heq, emb_zero, zero_div, phase_zero]

/-- Primitivity of the actual exponential pairing on every nonzero
principal quotient, including the quotient by a unit. -/
private theorem pairingChar_primitive (q : O) (hq : q ≠ 0) :
    (pairingChar q hq 1).IsPrimitive := by
  intro x hx htrivial
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hshift : AddChar.mulShift (pairingChar q hq 1) (Ideal.Quotient.mk (principal q) m) =
      pairingChar q hq m := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [AddChar.mulShift_apply, ← map_mul, pairingChar_mk, one_mul]
  have hz : pairingChar q hq m = 0 := by
    rw [← hshift, htrivial]
    rfl
  exact hx ((pairingChar_eq_zero_iff q hq m).mp hz)

private theorem primitive_of_generator (n : Ideal O) (q : O) (hq : q ≠ 0)
    (hqn : principal q = n) :
    ∃ ψ : AddChar (O ⧸ n) ℂ, ψ.IsPrimitive ∧
      ∀ a : O, ψ (Ideal.Quotient.mk n a) = additiveCharacter (embedding a / embedding q) := by
  subst n
  refine ⟨pairingChar q hq 1, pairingChar_primitive q hq, ?_⟩
  intro a
  simpa only [one_mul] using pairingChar_mk q hq 1 a

/-- The exact dispatched additive-primitivity obligation. -/
theorem proved :
    ArithmeticProof.InverseGauss.AdditivePrimitivityStatement := by
  intro c n hn
  have hgen : principal (primaryGenerator n) = n := (primaryGenerator_spec_outside c hn).1
  have hq : primaryGenerator n ≠ 0 := by
    intro hz
    apply hn.1
    rw [← hgen, hz]
    simp only [principal, Ideal.span_singleton_zero]
  exact primitive_of_generator n (primaryGenerator n) hq hgen

end QRHShort.CloudBatch.InverseAdditive

namespace QRHShort.CloudBatch

theorem arithmetic_inverse_additive_primitive_proved :
    ArithmeticProof.InverseGauss.AdditivePrimitivityStatement :=
  InverseAdditive.proved

end QRHShort.CloudBatch
