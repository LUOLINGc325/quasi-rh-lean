import QRHShort.PoissonCoprimeExpansion
import QRHShort.EisensteinBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The principal zero-frequency term, with the actual lattice character and
the finite Euler product over the prime ideals of the exclusion modulus. -/

noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.PoissonProof.PrincipalZero

theorem embedding_intCast (x : ℤ) : embedding (x : O) = (x : ℂ) := by
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

/-- The chosen representatives of the modulus-one quotient may be arbitrary
lattice points, so their additive characters must be evaluated on the lattice. -/
theorem additiveCharacter_embedding (a : O) :
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

theorem value_of_modulus_top (χ : PrimitiveResidueCharacter)
    (hmod : χ.modulus = ⊤) (a : O) : χ.value a = 1 := by
  letI : Subsingleton (O ⧸ χ.modulus) := Ideal.Quotient.subsingleton_iff.mpr hmod
  have hmk : Ideal.Quotient.mk χ.modulus a = 1 := Subsingleton.elim _ _
  simp only [PrimitiveResidueCharacter.value, hmk, map_one]

theorem gauss_of_modulus_top (χ : PrimitiveResidueCharacter)
    (hmod : χ.modulus = ⊤) : χ.gauss = 1 := by
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  letI : Subsingleton (O ⧸ χ.modulus) := Ideal.Quotient.subsingleton_iff.mpr hmod
  letI : Unique (O ⧸ χ.modulus) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  have hnorm : normIdeal χ.modulus = 1 := by simp [hmod, normIdeal]
  have hgen : embedding (chosenGenerator χ.modulus) = 1 := by
    rw [hmod]
    have htop : chosenGenerator (⊤ : Ideal O) = 1 := by
      rw [← Ideal.one_eq_top, chosenGenerator,
        if_neg (show (1 : Ideal O) ≠ ⊥ by simp), normalizedFactors_one]
      rfl
    rw [htop, embedding_one]
  have hvalue (x : O ⧸ χ.modulus) : χ.character x = 1 := by
    have hx : x = 1 := Subsingleton.elim _ _
    rw [hx, map_one]
  simp [PrimitiveResidueCharacter.gauss, hnorm, hgen, hvalue,
    additiveCharacter_embedding]

private theorem factors_prime_product (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
    (normalizedFactors_prod_of_prime (m := S.val) hS)

/-- A weighted finite divisor identity, obtained by enumerating the subsets
of a set of distinct prime ideals. -/
theorem sum_prime_product_divisors (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (f : Ideal O →* ℂ) :
    (∑ d ∈ CoprimeExpansion.idealDivisors (∏ P ∈ S, P)
      (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)),
      (mobius d : ℂ) * f d) = ∏ P ∈ S, (1 - f P) := by
  have hn : (∏ P ∈ S, P) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
  have hsq : Squarefree (∏ P ∈ S, P) := by
    apply (squarefree_iff_nodup_normalizedFactors hn).mpr
    rw [factors_prime_product S hS]
    exact S.nodup
  have hsum : (∑ t ∈ S.powerset, (-1 : ℂ) ^ t.card * ∏ P ∈ t, f P) =
      ∑ d ∈ CoprimeExpansion.idealDivisors (∏ P ∈ S, P) hn,
        (mobius d : ℂ) * f d := by
    apply Finset.sum_bij (fun t _ => ∏ P ∈ t, P)
    · intro t ht
      exact (CoprimeExpansion.mem_idealDivisors _ hn _).mpr
        (Finset.prod_dvd_prod_of_subset t S id (Finset.mem_powerset.mp ht))
    · intro t ht u hu h
      have hpt : ∀ P ∈ t, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp ht) hP)
      have hpu : ∀ P ∈ u, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hu) hP)
      apply Finset.val_injective
      rw [← factors_prime_product t hpt, ← factors_prime_product u hpu]
      exact congrArg normalizedFactors h
    · intro d hd
      have hdvd := (CoprimeExpansion.mem_idealDivisors _ hn d).mp hd
      obtain ⟨t, ht, hprod⟩ := CoprimeExpansion.squarefree_divisor_eq_prod hn hdvd
        (hsq.squarefree_of_dvd hdvd)
      rw [factors_prime_product S hS, Finset.val_toFinset] at ht
      exact ⟨t, Finset.mem_powerset.mpr ht, hprod⟩
    · intro t ht
      have hp : ∀ P ∈ t, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp ht) hP)
      have hsign : (mobius (∏ P ∈ t, P) : ℂ) = (-1 : ℂ) ^ t.card := by
        exact_mod_cast CoprimeExpansion.prime_finset_mobius t hp
      rw [hsign, map_prod]
  have hprod : (∏ P ∈ S, (1 - f P)) =
      ∑ t ∈ S.powerset, (-1 : ℂ) ^ t.card * ∏ P ∈ t, f P := by
    simpa only [Finset.prod_const_one, mul_one] using
      (Finset.prod_sub (fun _ : Ideal O => (1 : ℂ)) f S)
  exact hsum.symm.trans hprod.symm

def reciprocalIdealNorm : Ideal O →* ℂ where
  toFun d := (normIdeal d : ℂ)⁻¹
  map_one' := by simp [normIdeal]
  map_mul' := by
    intro a b
    simp [normIdeal, map_mul, mul_inv_rev, mul_comm]

theorem reciprocalIdealNorm_apply (d : Ideal O) :
    reciprocalIdealNorm d = (normIdeal d : ℂ)⁻¹ := rfl

theorem tsum_radical_mobius_div_norm (r : Ideal O) :
    (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
      (mobius d : ℂ) / (normIdeal d : ℂ) else 0) =
        ∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹) := by
  have hS : ∀ P ∈ primeFactors r, Prime P := fun P hP =>
    prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hprod : outsideRadical ∅ r = ∏ P ∈ primeFactors r, P := by
    simp [outsideRadical]
  have hsum := sum_prime_product_divisors (primeFactors r) hS reciprocalIdealNorm
  have hn := radical_ne_bot r
  rw [tsum_eq_sum (s := CoprimeExpansion.idealDivisors (outsideRadical ∅ r) hn)
    (fun d hd => if_neg (fun h => hd ((CoprimeExpansion.mem_idealDivisors _ hn d).mpr h)))]
  calc
    _ = ∑ d ∈ CoprimeExpansion.idealDivisors (outsideRadical ∅ r) hn,
        (mobius d : ℂ) * reciprocalIdealNorm d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [if_pos ((CoprimeExpansion.mem_idealDivisors _ hn d).mp hd)]
      rfl
    _ = _ := by simpa only [hprod, reciprocalIdealNorm_apply] using hsum

theorem poissonZeroTerm_eq_euler (χ : PrimitiveResidueCharacter)
    (hmod : χ.modulus = ⊤) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) :
    poissonZeroTerm χ r Φ H = H * radialFourier Φ 0 *
      ∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹) := by
  have hnorm : normIdeal χ.modulus = 1 := by simp [hmod, normIdeal]
  have hval := value_of_modulus_top χ hmod
  unfold poissonZeroTerm
  rw [gauss_of_modulus_top χ hmod, hnorm]
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one, div_one, hval,
    star_one, mul_one]
  have htsum : (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
      (mobius d : ℂ) / (normIdeal d : ℂ) * radialFourier Φ 0 else 0) =
      (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
        (mobius d : ℂ) / (normIdeal d : ℂ) else 0) * radialFourier Φ 0 := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro d
    split_ifs <;> simp
  rw [htsum, tsum_radical_mobius_div_norm]
  ring

end QRHShort.PoissonProof.PrincipalZero

namespace QRHShort.PoissonProof

/-- The frozen principal zero-frequency statement, without any unproved input. -/
theorem principalZero : PrincipalZeroStatement := by
  intro χ r Φ H _hχ hmod _hr _hH _hΦ
  exact PrincipalZero.poissonZeroTerm_eq_euler χ hmod r Φ H

end QRHShort.PoissonProof
