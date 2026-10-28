import QRHShort.ThetaBoundsReduction
import QRHShort.PrimaryGenerator

/-! Uniqueness of the literal primary cube scale. The ramified exponent is
separated by divisibility in O before applying ideal cube-factor uniqueness. -/

noncomputable section
open Classical

namespace QRHShort.CloudBatch
open ThetaBoundsProof

private theorem cube_lambda_factor : lambda = (omega - 1) * (-omega) := by
  unfold lambda
  linear_combination omega_sq_add_omega_add_one

private theorem cube_lambda_sq : lambda ^ (2 : ℕ) = -3 := by
  unfold lambda
  linear_combination 4 * omega_sq_add_omega_add_one

private theorem cube_lambda_ne_zero : lambda ≠ 0 := by
  intro h
  have hs := cube_lambda_sq
  rw [h, zero_pow (by decide)] at hs
  norm_num at hs

private theorem cube_embedding_lambda_ne_zero : embedding lambda ≠ 0 :=
  embedding_eq_zero.not.mpr cube_lambda_ne_zero

private theorem cube_primary_not_dvd {a : O} (ha : IsPrimary a) :
    ¬ omega - 1 ∣ a := by
  intro hd
  have hsub : omega - 1 ∣ a - 1 :=
    omega_sub_one_dvd_three.trans ((isPrimary_iff_three_dvd a).mp ha)
  apply omega_sub_one_prime.not_dvd_one
  convert dvd_sub hd hsub using 1 <;> ring

private theorem cube_unit_primary_product_not_dvd (u : Oˣ) {n b : O}
    (hn : PrimaryCubeData n b) : ¬ omega - 1 ∣ (u : O) * (n * b ^ (3 : ℕ)) := by
  intro h
  rcases omega_sub_one_prime.dvd_mul.mp h with hu | hnb
  · exact omega_sub_one_prime.irreducible.not_dvd_isUnit u.isUnit hu
  · rcases omega_sub_one_prime.dvd_mul.mp hnb with hn' | hb'
    · exact cube_primary_not_dvd hn.2.2.1 hn'
    · exact cube_primary_not_dvd hn.2.2.2.1 (omega_sub_one_prime.dvd_of_dvd_pow hb')

private theorem cube_exponent_eq_of_le (u u' : Oˣ) (m m' : ℤ)
    (n b n' b' : O) (hn : PrimaryCubeData n b) (_hn' : PrimaryCubeData n' b')
    (he : embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3) =
      embedding (u' : O) * embedding lambda ^ m' * embedding (n' * b' ^ 3))
    (hle : m ≤ m') : m = m' := by
  let k : ℕ := (m' - m).toNat
  have hk : m' = m + (k : ℤ) := by dsimp [k]; omega
  rw [hk, zpow_add₀ cube_embedding_lambda_ne_zero, zpow_natCast] at he
  have hi : (u : O) * (n * b ^ 3) =
      (u' : O) * (lambda ^ k * (n' * b' ^ 3)) := by
    apply embedding_injective
    apply mul_left_cancel₀ (zpow_ne_zero m cube_embedding_lambda_ne_zero)
    calc
      embedding lambda ^ m * embedding ((u : O) * (n * b ^ 3)) =
          embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3) := by
        rw [embedding_mul]
        ring
      _ = _ := he
      _ = embedding lambda ^ m * embedding ((u' : O) * (lambda ^ k * (n' * b' ^ 3))) := by
        simp only [embedding_mul, embedding_pow]
        ring
  have hkzero : k = 0 := by
    by_contra hkzero
    have hpi : omega - 1 ∣ lambda := ⟨-omega, cube_lambda_factor⟩
    have hpow : omega - 1 ∣ lambda ^ k := dvd_pow hpi hkzero
    have hright : omega - 1 ∣ (u' : O) * (lambda ^ k * (n' * b' ^ 3)) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpow _) _
    exact cube_unit_primary_product_not_dvd u hn (hi.symm ▸ hright)
  omega

private theorem cube_primary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) : u = 1 := by
  have hthree := (isPrimary_iff_three_dvd (u : O)).mp hu
  have hlambda : (omega - 1) ^ (2 : ℕ) ∣ (3 : O) := by
    refine ⟨-omega ^ (2 : ℕ), ?_⟩
    rw [omega_sub_one_sq]
    calc
      (3 : O) = 3 * omega ^ (3 : ℕ) := by rw [omega_cube, mul_one]
      _ = -3 * omega * -omega ^ (2 : ℕ) := by ring
  have hcong : ∃ k : ℤ, (omega - 1) ^ (2 : ℕ) ∣ ((u : O) - k) :=
    ⟨1, by simpa only [Int.cast_one] using hlambda.trans hthree⟩
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u hcong with h | h
  · exact h
  · exfalso
    have hneg : omega - 1 ∣ (-1 : O) - 1 := by
      simpa only [h, Units.val_neg, Units.val_one] using
        omega_sub_one_dvd_three.trans hthree
    apply omega_sub_one_prime.not_dvd_one
    convert dvd_add omega_sub_one_dvd_three hneg using 1 <;> ring

private theorem cube_primary_eq_of_principal_eq {a b : O}
    (ha : IsPrimary a) (hb : IsPrimary b) (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [cube_primary_unit_eq_one u hup, Units.val_one, mul_one] using hu

theorem theta_bounds_cube_scale_proved : PrimaryCubeScaleStatement := by
  intro u u' m m' n b n' b' hn hn' he
  have hm : m = m' := by
    rcases le_total m m' with hle | hle
    · exact cube_exponent_eq_of_le u u' m m' n b n' b' hn hn' he hle
    · exact (cube_exponent_eq_of_le u' u m' m n' b' n b hn' hn he.symm hle).symm
  subst m'
  have hi : (u : O) * (n * b ^ 3) = (u' : O) * (n' * b' ^ 3) := by
    apply embedding_injective
    apply mul_right_cancel₀ (zpow_ne_zero m cube_embedding_lambda_ne_zero)
    calc
      embedding ((u : O) * (n * b ^ 3)) * embedding lambda ^ m =
          embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3) := by
        simp only [embedding_mul]
        ring
      _ = _ := he
      _ = embedding ((u' : O) * (n' * b' ^ 3)) * embedding lambda ^ m := by
        simp only [embedding_mul]
        ring
  have hideal : principal n * principal b ^ (3 : ℕ) =
      principal n' * principal b' ^ (3 : ℕ) := by
    have h := congrArg principal hi
    rw [show principal ((u : O) * (n * b ^ 3)) = principal (n * b ^ 3) from
      Ideal.span_singleton_mul_left_unit u.isUnit _,
      show principal ((u' : O) * (n' * b' ^ 3)) = principal (n' * b' ^ 3) from
      Ideal.span_singleton_mul_left_unit u'.isUnit _] at h
    simpa only [principal, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_pow] using h
  have hb : principal b ≠ 0 := by
    intro h
    exact hn.2.1 (Ideal.span_singleton_eq_bot.mp h)
  have hb' : principal b' ≠ 0 := by
    intro h
    exact hn'.2.1 (Ideal.span_singleton_eq_bot.mp h)
  have hbideal := (squarefree_cube_decomposition_unique hb hb'
    hn.2.2.2.2 hn'.2.2.2.2 hideal).2
  have hbb' : b = b' := cube_primary_eq_of_principal_eq hn.2.2.2.1 hn'.2.2.2.1 hbideal
  rw [hbb']

end QRHShort.CloudBatch

#print axioms QRHShort.CloudBatch.theta_bounds_cube_scale_proved
