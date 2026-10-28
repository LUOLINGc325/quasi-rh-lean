import QRHShort.PoissonAssembly
import QRHShort.EisensteinBasis
import QRHShort.PrimaryGenerator
import OAI.NumberTheory.DirichletL.CharacterTransport
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The primitive Gauss transform for the actual frozen representatives.
Primitivity is transported from the stated conductor condition on units;
no nonunit vanishing or generator property is assumed. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.PoissonProof.PrimitiveGauss
open OAI.SevenEighths

@[simp] theorem embedding_intCast (x : ℤ) : embedding (x : O) = (x : ℂ) := by
  simpa only [embeddingHom_apply] using map_intCast embeddingHom x

theorem embedding_omega_im : (embedding omega).im = Real.sqrt 3 / 2 := by
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

theorem additiveCharacter_add (z w : ℂ) :
    additiveCharacter (z + w) = additiveCharacter z * additiveCharacter w := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_im]
  push_cast
  ring

@[simp] theorem additiveCharacter_zero : additiveCharacter 0 = 1 := by
  simp [additiveCharacter]

/-- The chosen additive character is trivial on every Eisenstein integer. -/
@[simp] theorem additiveCharacter_embedding (a : O) :
    additiveCharacter (embedding a) = 1 := by
  let y : ℤ := eisensteinBasis.repr a 1
  have him : (embedding a).im = (y : ℝ) * Real.sqrt 3 / 2 := by
    rw [eisenstein_coords a, embedding_add, embedding_mul,
      embedding_intCast, embedding_intCast]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, zero_add, add_zero, embedding_omega_im]
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


theorem primary_generator_spec {a : Ideal O}
    (h : ∃ z : O, principal z = a ∧ IsPrimary z) :
    principal (primaryGenerator a) = a := by
  simpa only [primaryGenerator, dif_pos h] using (Classical.choose_spec h).1

theorem prime_generator_spec {P : Ideal O} (hP : Prime P) :
    principal (if IsRelPrime P (principal 3) then primaryGenerator P
      else idealGenerator P) = P := by
  by_cases hrel : IsRelPrime P (principal 3)
  · rw [if_pos hrel]
    apply primary_generator_spec
    apply exists_primary_generator_of_prime hP
    intro hthree
    exact hP.not_unit (hrel (dvd_refl P) hthree)
  · rw [if_neg hrel]
    exact Ideal.span_singleton_generator P

theorem chosen_generator_spec {a : Ideal O} (ha : a ≠ ⊥) :
    principal (chosenGenerator a) = a := by
  rw [chosenGenerator, if_neg ha, principal, ← Ideal.multiset_prod_span_singleton,
    Multiset.map_map]
  calc
    ((UniqueFactorizationMonoid.normalizedFactors a).map (fun P =>
        Ideal.span {if IsRelPrime P (principal 3) then primaryGenerator P
          else idealGenerator P})).prod =
        (UniqueFactorizationMonoid.normalizedFactors a).prod := by
      congr 1
      simpa only [principal, Multiset.map_id'] using
        (Multiset.map_congr rfl (fun P hP =>
          prime_generator_spec (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)))
    _ = a := Ideal.prod_normalizedFactors_eq_self ha

theorem generator_embedding_ne_zero (χ : PrimitiveResidueCharacter) :
    embedding (chosenGenerator χ.modulus) ≠ 0 := by
  rw [ne_eq, embedding_eq_zero]
  intro h
  apply χ.modulus_ne_bot
  rw [← chosen_generator_spec χ.modulus_ne_bot, h]
  simp [principal]

@[simp] theorem mk_residueLift (n : Ideal O) (x : O ⧸ n) :
    Ideal.Quotient.mk n (residueLift n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

/-- Periodicity includes every frequency and every choice of lift. -/
theorem phase_congr (χ : PrimitiveResidueCharacter) (a b h : O)
    (hab : Ideal.Quotient.mk χ.modulus a = Ideal.Quotient.mk χ.modulus b) :
    additiveCharacter (embedding a * embedding h / embedding (chosenGenerator χ.modulus)) =
      additiveCharacter (embedding b * embedding h / embedding (chosenGenerator χ.modulus)) := by
  have hmem : a - b ∈ principal (chosenGenerator χ.modulus) := by
    rw [chosen_generator_spec χ.modulus_ne_bot]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have ha : a = b + chosenGenerator χ.modulus * c := by
    linear_combination hc
  have he : embedding a * embedding h / embedding (chosenGenerator χ.modulus) =
      embedding b * embedding h / embedding (chosenGenerator χ.modulus) + embedding (c * h) := by
    rw [ha, embedding_add, embedding_mul, embedding_mul]
    field_simp [generator_embedding_ne_zero χ]
    <;> ring
  rw [he, additiveCharacter_add, additiveCharacter_embedding, mul_one]

/-- The additive character on the quotient, built from its actual chosen lifts. -/
def quotientAddChar (χ : PrimitiveResidueCharacter) : AddChar (O ⧸ χ.modulus) ℂ where
  toFun x := additiveCharacter
    (embedding (residueLift χ.modulus x) / embedding (chosenGenerator χ.modulus))
  map_zero_eq_one' := by
    have he := phase_congr χ (residueLift χ.modulus 0) 0 1 (by simp)
    simpa using he.trans (by simp)
  map_add_eq_mul' x y := by
    have he := phase_congr χ (residueLift χ.modulus (x + y))
      (residueLift χ.modulus x + residueLift χ.modulus y) 1 (by simp)
    simpa only [embedding_one, mul_one, embedding_add, add_div, additiveCharacter_add] using he

@[simp] theorem quotientAddChar_mk (χ : PrimitiveResidueCharacter) (a : O) :
    quotientAddChar χ (Ideal.Quotient.mk χ.modulus a) =
      additiveCharacter (embedding a / embedding (chosenGenerator χ.modulus)) := by
  change additiveCharacter (embedding (residueLift χ.modulus
    (Ideal.Quotient.mk χ.modulus a)) / embedding (chosenGenerator χ.modulus)) = _
  simpa only [embedding_one, mul_one] using
    phase_congr χ (residueLift χ.modulus (Ideal.Quotient.mk χ.modulus a)) a 1 (by simp)

/-- The manuscript's conductor minimality implies ideal primitivity on the quotient. -/
theorem primitive_on_ideals (χ : PrimitiveResidueCharacter) :
    FiniteFourier.IsPrimitiveOnIdeals χ.character := by
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  apply (FiniteConductor.primitiveOnIdeals_iff_no_descent χ.character).mpr
  intro I hI hdesc
  obtain ⟨ψ, hψ⟩ := hdesc
  let d : Ideal O := I.comap (Ideal.Quotient.mk χ.modulus)
  have hmd : χ.modulus ≤ d := by
    intro a ha
    change Ideal.Quotient.mk χ.modulus a ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact I.zero_mem
  have hd : d ≠ ⊥ := by
    intro hz
    exact χ.modulus_ne_bot (le_bot_iff.mp (hz ▸ hmd))
  let e : O ⧸ d ≃+* (O ⧸ χ.modulus) ⧸ I :=
    RingEquiv.ofBijective (Ideal.quotientMap I (Ideal.Quotient.mk χ.modulus) le_rfl)
      ⟨Ideal.quotientMap_injective,
        Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
  have hdm : d = χ.modulus := by
    apply χ.primitive d hd hmd
    refine ⟨CharacterTransport.pullback e ψ, ?_⟩
    intro a ha
    have hv := FiniteConductor.factorization_with_source_mask χ.character I ψ hψ
      (Ideal.Quotient.mk χ.modulus a)
    rw [CharacterTransport.pullback_apply]
    have he : e (Ideal.Quotient.mk d a) =
        Ideal.Quotient.mk I (Ideal.Quotient.mk χ.modulus a) := rfl
    rw [he]
    simpa only [ha, ite_true] using hv
  apply hI
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change a ∈ χ.modulus
  rw [← hdm]
  exact hx

/-- Identify the concrete finite transform with the usual Gauss sum. -/
theorem finiteFourier_eq_gaussSum (χ : PrimitiveResidueCharacter) (h : O) :
    finiteFourier χ h =
      letI : Finite (O ⧸ χ.modulus) :=
        Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
      letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
      gaussSum χ.character ((quotientAddChar χ).mulShift (Ideal.Quotient.mk χ.modulus h)) := by
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  unfold finiteFourier gaussSum
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change _ = quotientAddChar χ (Ideal.Quotient.mk χ.modulus h * x)
  have hx : Ideal.Quotient.mk χ.modulus (h * residueLift χ.modulus x) =
      Ideal.Quotient.mk χ.modulus h * x := by simp
  rw [← hx, quotientAddChar_mk, embedding_mul, mul_comm]

/-- The frozen primitive Gauss statement, with no pending proof hypotheses. -/
theorem primitiveGauss : PrimitiveGaussStatement := by
  intro χ h
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  have hf := FiniteFourier.primitive_gaussSum_mulShift χ.character
    (primitive_on_ideals χ) (quotientAddChar χ) (Ideal.Quotient.mk χ.modulus h)
  have hbase := finiteFourier_eq_gaussSum χ 1
  simp only [map_one, AddChar.mulShift_one] at hbase
  rw [finiteFourier_eq_gaussSum, hf, ← hbase, finiteFourier_one,
    ← MulChar.star_apply']
  change star (χ.value h) * _ = _
  exact mul_comm _ _

end QRHShort.PoissonProof.PrimitiveGauss
