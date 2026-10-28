import QRHShort.ThetaCoefficientBridge

/-! The unramified cube slice of the concrete TauFormula has a unique value.
Multiplying by lambda cubed makes every branch integral; primary elements have
zero valuation at the prime above three, forcing the second branch with k = 0.
The checked primary cube decomposition then identifies the two coefficient data. -/

noncomputable section
open Classical

namespace QRHShort.ThetaRealizationProof
open ArithmeticProof SquarefreeReflection.RayValuePrerequisites

theorem primary_not_dvd_ramified {a : O} (ha : IsPrimary a) :
    ¬ omega - 1 ∣ a := by
  intro h
  apply omega_sub_one_prime.not_dvd_one
  have hd := omega_sub_one_dvd_three.trans ((isPrimary_iff_three_dvd a).mp ha)
  convert dvd_sub h hd using 1 <;> ring

theorem ramified_dvd_lambda : omega - 1 ∣ lambda := by
  refine ⟨-omega, ?_⟩
  unfold lambda
  linear_combination omega_sq_add_omega_add_one

theorem lambda_ne_zero_tau : lambda ≠ 0 := by
  intro h
  have he := embedding_lambda
  rw [h, embedding_zero] at he
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))
  exact (mul_ne_zero hs Complex.I_ne_zero) he.symm

theorem frequency_shift_integral (m m' t : O) (e : ℕ)
    (h : -frequency m = embedding t *
      embedding lambda ^ ((e : ℤ) - 3) * embedding m') :
    -m = t * lambda ^ e * m' := by
  have hl := embedding_ne_zero lambda_ne_zero_tau
  have hc : embedding lambda ^ ((e : ℤ) - 3) =
      embedding lambda ^ e * embedding lambda ^ (-3 : ℤ) := by
    rw [sub_eq_add_neg, zpow_add₀ hl, zpow_natCast]
  rw [hc, frequency] at h
  have hi : Function.Injective embeddingHom := by
    unfold embeddingHom
    split_ifs
    · exact rawEmbedding.toRingHom.injective.comp NumberField.RingOfIntegers.coe_injective
    · exact (starRingEnd ℂ).injective.comp
        (rawEmbedding.toRingHom.injective.comp NumberField.RingOfIntegers.coe_injective)
  apply hi
  simp only [embeddingHom_apply, embedding_neg, ArithmeticProof.embedding_mul, embedding_pow]
  apply (mul_right_inj' (zpow_ne_zero (-3 : ℤ) hl)).mp
  calc
    embedding lambda ^ (-3 : ℤ) * -embedding m =
        -(embedding lambda ^ (-3 : ℤ) * embedding m) := by ring
    _ = embedding t * (embedding lambda ^ e *
        embedding lambda ^ (-3 : ℤ)) * embedding m' := h
    _ = embedding lambda ^ (-3 : ℤ) *
        (embedding t * embedding lambda ^ e * embedding m') := by ring

theorem frequency_shift_exponent_zero (m m' t : O) (e : ℕ)
    (hm : IsPrimary m)
    (h : -frequency m = embedding t *
      embedding lambda ^ ((e : ℤ) - 3) * embedding m') : e = 0 := by
  by_contra he
  have hd : omega - 1 ∣ t * lambda ^ e * m' :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
      (ramified_dvd_lambda.trans (dvd_pow_self lambda he)) t) m'
  rw [← frequency_shift_integral m m' t e h] at hd
  exact primary_not_dvd_ramified hm (dvd_neg.mp hd)

theorem tauCubeSliceUniqueness : TauCubeSliceUniquenessStatement := by
  intro n b hnb v hv
  rcases hv with ⟨n', b', hnb', s, hs, hcase⟩
  have hm : IsPrimary (n * b ^ 3) := primary_mul hnb.2.2.1 (primary_cube hnb.2.2.2.1)
  rcases hs with rfl | rfl
  all_goals rcases hcase with hcase | hcase
  · rcases hcase with ⟨k, j, hk, hell, _⟩
    have hexp : ((3 * k - 1 : ℕ) : ℤ) - 3 = (3 : ℤ) * k - 4 := by omega
    have hshift : -frequency (n * b ^ 3) = embedding (omega ^ j.val) *
        embedding lambda ^ (((3 * k - 1 : ℕ) : ℤ) - 3) * embedding (n' * b' ^ 3) := by
      simpa only [one_mul, embedding_pow, hexp] using hell
    have hz := frequency_shift_exponent_zero _ _ _ _ hm hshift
    omega
  · rcases hcase with ⟨k, hell, hv⟩
    have hshift : -frequency (n * b ^ 3) = embedding (1 : O) *
        embedding lambda ^ (((3 * k : ℕ) : ℤ) - 3) * embedding (n' * b' ^ 3) := by
      simpa only [embedding_one, Nat.cast_mul, Nat.cast_ofNat] using hell
    have hz := frequency_shift_exponent_zero _ _ _ _ hm hshift
    have hk : k = 0 := by omega
    subst k
    have he := frequency_shift_integral _ _ _ _ hshift
    simp only [Nat.mul_zero, pow_zero, mul_one, one_mul] at he
    have hi : principal (n * b ^ 3) = principal (n' * b' ^ 3) := by
      simpa only [one_mul, principal, Ideal.span_singleton_neg] using congrArg principal he
    have heq := primary_unique hm
      (primary_mul hnb'.2.2.1 (primary_cube hnb'.2.2.2.1)) hi
    obtain ⟨rfl, rfl⟩ := primaryCubeData_injective hnb hnb' heq
    simpa [cubeSliceValue] using hv
  · rcases hcase with ⟨k, j, hk, hell, _⟩
    have hexp : ((3 * k - 1 : ℕ) : ℤ) - 3 = (3 : ℤ) * k - 4 := by omega
    have hshift : -frequency (n * b ^ 3) = embedding (-(omega ^ j.val)) *
        embedding lambda ^ (((3 * k - 1 : ℕ) : ℤ) - 3) * embedding (n' * b' ^ 3) := by
      simpa only [neg_one_mul, embedding_neg, embedding_pow, hexp] using hell
    have hz := frequency_shift_exponent_zero _ _ _ _ hm hshift
    omega
  · rcases hcase with ⟨k, hell, hv⟩
    have hshift : -frequency (n * b ^ 3) = embedding (-1 : O) *
        embedding lambda ^ (((3 * k : ℕ) : ℤ) - 3) * embedding (n' * b' ^ 3) := by
      simpa only [embedding_neg, embedding_one, Nat.cast_mul, Nat.cast_ofNat] using hell
    have hz := frequency_shift_exponent_zero _ _ _ _ hm hshift
    have hk : k = 0 := by omega
    subst k
    have he := frequency_shift_integral _ _ _ _ hshift
    simp only [Nat.mul_zero, pow_zero, mul_one, one_mul] at he
    have hi : principal (n * b ^ 3) = principal (n' * b' ^ 3) := by
      exact congrArg principal (neg_injective (by simpa only [neg_one_mul] using he))
    have heq := primary_unique hm
      (primary_mul hnb'.2.2.1 (primary_cube hnb'.2.2.2.1)) hi
    obtain ⟨rfl, rfl⟩ := primaryCubeData_injective hnb hnb' heq
    simpa [cubeSliceValue] using hv

#print axioms tauCubeSliceUniqueness

end QRHShort.ThetaRealizationProof
