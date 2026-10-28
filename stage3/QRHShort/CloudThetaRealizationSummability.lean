import QRHShort.ThetaRealizationReduction
import QRHShort.ArithmeticBasics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import QRHShort.IdealCounting
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Bounds for the literal theta series, without a theta-bounds premise. -/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace QRHShort.CloudBatch

private theorem theta_breve_norm (z : ℂ) : ‖breve z‖ = 1 := by
  simp [breve, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem theta_ninth_norm (j : Fin 3) : ‖ninthPhase j‖ = 1 := by
  unfold ninthPhase
  split_ifs <;> simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem theta_cubicAtPrime_bound (P : Ideal O) (a : O) :
    ‖cubicAtPrime P a‖ ≤ 3 := by
  let f : ℕ → ℂ := fun j =>
    if Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3) = Ideal.Quotient.mk P (omega ^ j)
    then embedding (omega ^ j) else 0
  change ‖∑ j ∈ Finset.range 3, f j‖ ≤ 3
  calc
    _ ≤ ∑ j ∈ Finset.range 3, ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range 3, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      dsimp only [f]
      split_ifs
      · rw [embedding_pow, norm_pow, norm_embedding_omega, one_pow]
      · simp
    _ = 3 := by simp

private def theta_idealNormHom : Ideal O →* ℝ :=
  (Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom

private theorem theta_idealNormHom_apply (I : Ideal O) :
    theta_idealNormHom I = normIdeal I := rfl

private theorem theta_cubicAtPrime_norm_bound {P : Ideal O} (hP : Prime P) (a : O) :
    ‖cubicAtPrime P a‖ ≤ normIdeal P ^ 2 := by
  have h0 : P.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero
  have h1 : P.absNorm ≠ 1 := by
    intro h
    exact hP.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  have h2 : (2 : ℝ) ≤ normIdeal P := by
    change (2 : ℝ) ≤ (P.absNorm : ℝ)
    exact_mod_cast (show 2 ≤ P.absNorm by omega)
  exact (theta_cubicAtPrime_bound P a).trans (by nlinarith)

private theorem theta_cubic_product_bound (s : Multiset (Ideal O))
    (hs : ∀ P ∈ s, Prime P) (a : O) :
    ‖(s.map (fun P => cubicAtPrime P a)).prod‖ ≤ ((s.map normIdeal).prod) ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons P s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_pow]
    exact mul_le_mul (theta_cubicAtPrime_norm_bound (hs P (by simp)) a)
      (ih (fun Q hQ => hs Q (by simp [hQ]))) (norm_nonneg _) (sq_nonneg _)

private theorem theta_cubicSymbol_bound (I : Ideal O) (hI : I ≠ ⊥) (a : O) :
    ‖cubicSymbol I a‖ ≤ normIdeal I ^ 2 := by
  have hprod : ((UniqueFactorizationMonoid.normalizedFactors I).map normIdeal).prod =
      normIdeal I := by
    change ((UniqueFactorizationMonoid.normalizedFactors I).map theta_idealNormHom).prod =
      theta_idealNormHom I
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
  have h := theta_cubic_product_bound (UniqueFactorizationMonoid.normalizedFactors I)
    (fun P hP => UniqueFactorizationMonoid.prime_of_normalized_factor P hP) a
  rw [hprod] at h
  simpa only [cubicSymbol, ite_eq_right hI] using h

private theorem theta_cubicGauss_bound (r n : O) (hn : n ≠ 0) :
    ‖cubicGauss r n‖ ≤ normElement n ^ 3 := by
  have hI : principal n ≠ ⊥ := by
    intro h
    exact hn (Ideal.span_singleton_eq_bot.mp h)
  letI : Finite (O ⧸ principal n) := Ring.HasFiniteQuotients.finiteQuotient hI
  letI : Fintype (O ⧸ principal n) := Fintype.ofFinite _
  have hcard : (Fintype.card (O ⧸ principal n) : ℝ) = normElement n := by
    simp only [normElement, normIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_eq_fintype_card]
  rw [cubicGauss, dite_eq_left hI]
  calc
    _ ≤ ∑ x : O ⧸ principal n,
        ‖cubicSymbol (principal n) (residueLift (principal n) x) *
          breve (embedding (r * residueLift (principal n) x) / embedding n)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : O ⧸ principal n, normElement n ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, theta_breve_norm, mul_one]
      exact theta_cubicSymbol_bound (principal n) hI _
    _ = normElement n ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      ring

private def theta_integralPB : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

private theorem theta_integralPB_dim : theta_integralPB.dim = 2 := by
  change (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

private def theta_integralBasis : Module.Basis (Fin 2) ℤ O :=
  theta_integralPB.basis.reindex (finCongr theta_integralPB_dim)

private theorem theta_basis_zero : theta_integralBasis 0 = 1 := by
  rw [theta_integralBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change theta_integralPB.gen ^ (0 : ℕ) = 1
  exact pow_zero _

private theorem theta_basis_one : theta_integralBasis 1 = omega := by
  rw [theta_integralBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change theta_integralPB.gen ^ (1 : ℕ) = omega
  rw [pow_one]
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

private theorem theta_integral_coords (a : O) :
    a = (theta_integralBasis.repr a 0 : O) + (theta_integralBasis.repr a 1 : O) * omega := by
  simpa [Fin.sum_univ_two, theta_basis_zero, theta_basis_one, Algebra.smul_def] using
    (theta_integralBasis.sum_repr a).symm

private theorem theta_repr_pair (x y : ℤ) (i : Fin 2) :
    theta_integralBasis.repr ((x : O) + (y : O) * omega) i = ![x, y] i := by
  have h : (x : O) + (y : O) * omega =
      x • theta_integralBasis 0 + y • theta_integralBasis 1 := by
    simp [theta_basis_zero, theta_basis_one, Algebra.smul_def]
  rw [h, map_add, map_smul, map_smul]
  fin_cases i <;> simp [Module.Basis.repr_self_apply]

private theorem theta_algebra_norm (a : O) :
    Algebra.norm ℤ a = theta_integralBasis.repr a 0 ^ 2 -
      theta_integralBasis.repr a 0 * theta_integralBasis.repr a 1 +
      theta_integralBasis.repr a 1 ^ 2 := by
  let x := theta_integralBasis.repr a 0
  let y := theta_integralBasis.repr a 1
  have ha : a = (x : O) + (y : O) * omega := theta_integral_coords a
  have hmul : a * omega = ((-y : ℤ) : O) + ((x - y : ℤ) : O) * omega := by
    rw [ha]
    push_cast
    calc
      ((x : O) + (y : O) * omega) * omega =
          -(y : O) + ((x : O) - (y : O)) * omega +
            (y : O) * (omega ^ 2 + omega + 1) := by ring
      _ = _ := by rw [SquarefreeReflection.RayValuePrerequisites.omega_sq_add_omega_add_one]; ring
  have hmatrix : Algebra.leftMulMatrix theta_integralBasis a = !![x, -y; y, x - y] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j
    · change theta_integralBasis.repr (a * theta_integralBasis 0) 0 = x
      rw [theta_basis_zero, mul_one]
    · change theta_integralBasis.repr (a * theta_integralBasis 1) 0 = -y
      rw [theta_basis_one, hmul, theta_repr_pair]
      rfl
    · change theta_integralBasis.repr (a * theta_integralBasis 0) 1 = y
      rw [theta_basis_zero, mul_one]
    · change theta_integralBasis.repr (a * theta_integralBasis 1) 1 = x - y
      rw [theta_basis_one, hmul, theta_repr_pair]
      rfl
  rw [Algebra.norm_eq_matrix_det theta_integralBasis, hmatrix, Matrix.det_fin_two]
  dsimp [x, y]
  ring

private theorem theta_embedding_int (x : ℤ) : embedding (x : O) = (x : ℂ) := by
  simpa only [embeddingHom_apply] using map_intCast embeddingHom x

private theorem theta_omega_re : (embedding omega).re = -(1 : ℝ) / 2 := by
  have h := congrArg Complex.re ThetaRealizationProof.embedding_lambda
  simp only [lambda, embedding_add, embedding_mul, embedding_one] at h
  have htwo : embedding (2 : O) = 2 := by
    simpa only [embeddingHom_apply] using map_ofNat embeddingHom 2
  simp only [htwo, Complex.add_re, Complex.mul_re, Complex.one_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one] at h
  norm_num at h
  linarith

private theorem theta_omega_im : (embedding omega).im = Real.sqrt 3 / 2 := by
  have h := congrArg Complex.im ThetaRealizationProof.embedding_lambda
  simp only [lambda, embedding_add, embedding_mul, embedding_one] at h
  have htwo : embedding (2 : O) = 2 := by
    simpa only [embeddingHom_apply] using map_ofNat embeddingHom 2
  simp only [htwo, Complex.add_im, Complex.mul_im, Complex.one_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, zero_add,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero] at h
  norm_num at h
  linarith

private theorem theta_embedding_norm_sq (a : O) :
    ‖embedding a‖ ^ 2 = (theta_integralBasis.repr a 0 : ℝ) ^ 2 -
      (theta_integralBasis.repr a 0 : ℝ) * (theta_integralBasis.repr a 1 : ℝ) +
      (theta_integralBasis.repr a 1 : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  conv_lhs => rw [theta_integral_coords a, embedding_add,
    embedding_mul, theta_embedding_int, theta_embedding_int]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, theta_omega_re,
    theta_omega_im, zero_mul, sub_zero, add_zero, zero_add]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

private theorem theta_normElement_eq_sq (a : O) : normElement a = ‖embedding a‖ ^ 2 := by
  have hnonneg : 0 ≤ Algebra.norm ℤ a := by
    rw [theta_algebra_norm]
    nlinarith [sq_nonneg (2 * theta_integralBasis.repr a 0 - theta_integralBasis.repr a 1),
      sq_nonneg (theta_integralBasis.repr a 1)]
  have hnorm : ((principal a).absNorm : ℤ) = Algebra.norm ℤ a := by
    rw [principal, Ideal.absNorm_span_singleton, Int.natCast_natAbs, abs_of_nonneg hnonneg]
  have hreal := congrArg (fun x : ℤ => (x : ℝ)) hnorm
  simp only [Int.cast_natCast, theta_algebra_norm, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow] at hreal
  rw [normElement, normIdeal, theta_embedding_norm_sq]
  exact hreal

private theorem theta_embedding_norm_one_le {a : O} (ha : a ≠ 0) : 1 ≤ ‖embedding a‖ := by
  have hN : (1 : ℝ) ≤ normElement a := by
    change (1 : ℝ) ≤ ((principal a).absNorm : ℝ)
    have hz : (principal a).absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr
      (fun h => ha (Ideal.span_singleton_eq_bot.mp h))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  rw [theta_normElement_eq_sq] at hN
  nlinarith [norm_nonneg (embedding a)]

private theorem theta_lambda_norm_power (m : ℤ) :
    ‖embedding lambda‖ ^ m = (3 : ℝ) ^ ((m : ℝ) / 2) := by
  have hn : ‖embedding lambda‖ = Real.sqrt 3 := by
    rw [ThetaRealizationProof.embedding_lambda, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_I, mul_one]
  rw [hn, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

private theorem theta_gauss_ratio_bound (r : O) {n b : O} (hn : n ≠ 0) :
    ‖star (cubicGauss r n) * (‖embedding b / embedding n‖ : ℂ)‖ ≤
      ‖embedding n‖ ^ 5 * ‖embedding b‖ := by
  have hnpos : 0 < ‖embedding n‖ :=
    norm_pos_iff.mpr (embedding_eq_zero.not.mpr hn)
  calc
    _ = ‖cubicGauss r n‖ * (‖embedding b‖ / ‖embedding n‖) := by
      simp [norm_mul, norm_div]
    _ ≤ (‖embedding n‖ ^ 2) ^ 3 * (‖embedding b‖ / ‖embedding n‖) := by
      rw [← theta_normElement_eq_sq]
      exact mul_le_mul_of_nonneg_right (theta_cubicGauss_bound r n hn)
        (div_nonneg (norm_nonneg _) hnpos.le)
    _ = _ := by field_simp [hnpos.ne']

private theorem theta_representation_growth {ell value w : ℂ} {m : ℤ} {n b : O} {a : ℝ}
    (hw : ‖w‖ = 1) (hm : -4 ≤ m) (hn : n ≠ 0) (hb : b ≠ 0)
    (ha : a ≤ 3 + (m : ℝ) / 6)
    (he : ell = w * embedding lambda ^ m * embedding (n * b ^ 3))
    (hv : ‖value‖ ≤ (‖embedding n‖ ^ 5 * ‖embedding b‖) * (3 : ℝ) ^ a) :
    ‖value‖ ≤ (3 : ℝ) ^ (13 : ℕ) * ‖ell‖ ^ (5 : ℕ) := by
  have hmr : (-4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (13 : ℕ) *
      ((3 : ℝ) ^ ((m : ℝ) / 2)) ^ (5 : ℕ) := by
    calc
      _ ≤ (3 : ℝ) ^ ((13 : ℕ) + ((m : ℝ) / 2) * (5 : ℕ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = _ := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast,
          Real.rpow_mul_natCast (by norm_num)]
  have hB : ‖embedding b‖ ≤ ‖embedding b‖ ^ (15 : ℕ) :=
    le_self_pow₀ (theta_embedding_norm_one_le hb) (by decide)
  have hnorm : ‖ell‖ = (3 : ℝ) ^ ((m : ℝ) / 2) *
      ‖embedding n‖ * ‖embedding b‖ ^ (3 : ℕ) := by
    rw [he, norm_mul, norm_mul, hw, one_mul, norm_zpow, theta_lambda_norm_power,
      embedding_mul, norm_mul, embedding_pow, norm_pow]
    ring
  calc
    _ ≤ (‖embedding n‖ ^ 5 * ‖embedding b‖ ^ 15) *
        ((3 : ℝ) ^ 13 * ((3 : ℝ) ^ ((m : ℝ) / 2)) ^ 5) :=
      hv.trans (mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) hpow
        (Real.rpow_nonneg (by norm_num) _) (by positivity))
    _ = _ := by rw [hnorm]; ring

private theorem theta_tau_growth (ell : ℂ) :
    ‖tau ell‖ ≤ (3 : ℝ) ^ (13 : ℕ) * ‖ell‖ ^ (5 : ℕ) := by
  by_cases ht : tau ell = 0
  · rw [ht, norm_zero]
    positivity
  have hform : TauFormula ell (tau ell) := by
    by_cases h : ∃ value, TauFormula ell value
    · simpa only [tau, dite_eq_left h] using Classical.choose_spec h
    · exact (ht (by simp only [tau, dite_eq_right h])).elim
  rcases hform with ⟨n, b, hn, s, hs, h⟩
  have hsNorm : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  rcases h with ⟨k, j, hk, he, hv⟩ | ⟨k, he, hv⟩
  · apply theta_representation_growth (w := s * embedding omega ^ j.val)
      (m := 3 * (k : ℤ) - 4) (n := n) (b := b) (a := (k : ℝ) / 2 + 2)
      (by rw [norm_mul, hsNorm, norm_pow, norm_embedding_omega, one_pow, mul_one])
      (by omega) hn.1 hn.2.1 (by push_cast; linarith) he
    calc
      _ = ‖star (cubicGauss (omega ^ j.val * lambda ^ 2) n) *
          (‖embedding b / embedding n‖ : ℂ)‖ * (3 : ℝ) ^ ((k : ℝ) / 2 + 2) := by
        rw [hv]
        simp [norm_mul, theta_ninth_norm, Real.rpow_nonneg]
      _ ≤ _ := mul_le_mul_of_nonneg_right (theta_gauss_ratio_bound _ hn.1)
        (Real.rpow_nonneg (by norm_num) _)
  · apply theta_representation_growth (w := s) (m := 3 * (k : ℤ) - 3)
      (n := n) (b := b) (a := (k : ℝ) / 2 + 5 / 2) hsNorm (by omega)
      hn.1 hn.2.1 (by push_cast; linarith) he
    calc
      _ = ‖star (cubicGauss 1 n) * (‖embedding b / embedding n‖ : ℂ)‖ *
          (3 : ℝ) ^ ((k : ℝ) / 2 + 5 / 2) := by
        rw [hv]
        simp [norm_mul, Real.rpow_nonneg]
      _ ≤ _ := mul_le_mul_of_nonneg_right (theta_gauss_ratio_bound _ hn.1)
        (Real.rpow_nonneg (by norm_num) _)

private theorem theta_ideal_norm_fiber_bound {C : ℝ}
    (hcount : ∀ X : ℝ, 0 < X → ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ C * X)
    {m : ℕ} (hm : 0 < m) :
    (Nat.card {I : Ideal O // I.absNorm = m} : ℝ) ≤ C * (m : ℝ) := by
  let target := boundedDivisibleIdeals 1 (m : ℝ)
  let ι : {I : Ideal O // I.absNorm = m} → {I // I ∈ target} := fun I =>
    ⟨I.1, mem_boundedDivisibleIdeals.mpr ⟨by change (I.1.absNorm : ℝ) ≤ m; rw [I.2],
      one_dvd _, fun hI => (Nat.ne_of_gt hm)
        (I.2.symm.trans (Ideal.absNorm_eq_zero_iff.mpr hI))⟩⟩
  have hι : Function.Injective ι := by
    intro I J h
    apply Subtype.ext
    change (ι I).1 = (ι J).1
    exact congrArg Subtype.val h
  have hc := Nat.card_le_card_of_injective ι hι
  have hc' : (Nat.card {I : Ideal O // I.absNorm = m} : ℝ) ≤
      ((boundedDivisibleIdeals 1 (m : ℝ)).card : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc)
  exact hc'.trans (hcount m (by exact_mod_cast hm))

private theorem theta_ideal_inverse_cube_summable :
    Summable (fun I : Ideal O => 1 / normIdeal I ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  let coeff : ℕ → ℝ := fun m =>
    (Nat.card {I : Ideal O // I.absNorm = m} : ℝ) / (m : ℝ) ^ (3 : ℕ)
  have hc0 (m : ℕ) : 0 ≤ coeff m := by dsimp [coeff]; positivity
  have hp : Summable (fun m : ℕ => 1 / (m : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hmajor : Summable (fun m : ℕ => C / ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    simpa only [div_eq_mul_inv, one_mul] using ((summable_nat_add_iff 1).mpr hp).mul_left C
  have hc : Summable coeff := by
    apply (summable_nat_add_iff 1).mp
    apply hmajor.of_nonneg_of_le (fun m => hc0 (m + 1))
    intro m
    have hm : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    calc
      coeff (m + 1) ≤ (C * ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (theta_ideal_norm_fiber_bound hcount (Nat.succ_pos m))
          (pow_nonneg hm.le _)
      _ = _ := by field_simp [hm.ne']
  apply (summable_partition (fun I : Ideal O => by
    change 0 ≤ 1 / (I.absNorm : ℝ) ^ (3 : ℕ)
    positivity) (s := fun m : ℕ => {I : Ideal O | I.absNorm = m})
      (fun I => ⟨I.absNorm, rfl, fun m hm => hm.symm⟩)).mpr
  constructor
  · intro m
    letI := (Ideal.finite_setOfPred_absNorm_eq (S := O) m).fintype
    exact Summable.of_finite
  · apply hc.congr
    intro m
    letI := (Ideal.finite_setOfPred_absNorm_eq (S := O) m).fintype
    symm
    calc
      (∑' I : {I : Ideal O | I.absNorm = m}, 1 / normIdeal I.1 ^ (3 : ℕ)) =
          ∑' _I : {I : Ideal O | I.absNorm = m}, 1 / (m : ℝ) ^ (3 : ℕ) := by
        apply tsum_congr
        intro I
        change 1 / (I.1.absNorm : ℝ) ^ (3 : ℕ) = 1 / (m : ℝ) ^ (3 : ℕ)
        rw [I.2]
      _ = coeff m := by
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_eq_nat_card, coeff, div_eq_mul_inv, one_mul]
        rfl

private theorem theta_summable_principal_pullback {g : Ideal O → ℝ}
    (hg0 : ∀ I, 0 ≤ g I) (hg : Summable g) : Summable (fun a : O => g (principal a)) := by
  letI : Fintype Oˣ := Set.fintypeOfFiniteUniv finite_units
  have hu (a : O) : ∃ u : Oˣ, idealGenerator (principal a) * (u : O) = a := by
    exact Ideal.span_singleton_eq_span_singleton.mp (Ideal.span_singleton_generator (principal a))
  let u (a : O) : Oˣ := Classical.choose (hu a)
  have hurepr (a : O) : idealGenerator (principal a) * (u a : O) = a := Classical.choose_spec (hu a)
  let ι : O → Ideal O × Oˣ := fun a => (principal a, u a)
  have hι : Function.Injective ι := by
    intro a b h
    have hp : principal a = principal b := congrArg Prod.fst h
    have hu' : u a = u b := congrArg Prod.snd h
    calc
      a = idealGenerator (principal a) * (u a : O) := (hurepr a).symm
      _ = idealGenerator (principal b) * (u b : O) := by rw [hp, hu']
      _ = b := hurepr b
  have hprod : Summable (fun p : Ideal O × Oˣ => g p.1) := by
    apply (summable_prod_of_nonneg (fun p => hg0 p.1)).mpr
    constructor
    · intro I
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        hg.mul_left (Fintype.card Oˣ : ℝ)
  exact hprod.comp_injective hι

private theorem theta_element_inverse_cube_summable :
    Summable (fun a : O => 1 / normElement a ^ (3 : ℕ)) :=
  theta_summable_principal_pullback (fun I => by change 0 ≤ 1 / (I.absNorm : ℝ) ^ (3 : ℕ); positivity)
    theta_ideal_inverse_cube_summable

private theorem theta_poly_exp_bound {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    s ^ (5 : ℕ) * Real.exp (-a * s) ≤
      ((Nat.factorial 11 : ℝ) / a ^ (11 : ℕ)) / s ^ (6 : ℕ) := by
  have hp := Real.pow_div_factorial_le_exp (a * s) (mul_pos ha hs).le 11
  have hrecip := one_div_le_one_div_of_le (by positivity :
    0 < (a * s) ^ (11 : ℕ) / (Nat.factorial 11 : ℝ)) hp
  rw [one_div, ← Real.exp_neg] at hrecip
  calc
    _ ≤ s ^ (5 : ℕ) * ((a * s) ^ (11 : ℕ) / (Nat.factorial 11 : ℝ))⁻¹ := by
      simpa only [neg_mul, one_div] using mul_le_mul_of_nonneg_left hrecip (pow_nonneg hs.le 5)
    _ = _ := by field_simp [ha.ne', hs.ne']

private theorem theta_cosh_lower (t : ℝ) (ht : 0 ≤ t) :
    (1 : ℝ) / 2 + t ^ 2 / 8 ≤ Real.cosh t := by
  have hp := Real.pow_div_factorial_le_exp t ht 2
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hp
  have hc := Real.cosh_eq t
  have he := (Real.exp_pos (-t)).le
  have h1 := Real.one_le_cosh t
  nlinarith

private theorem theta_cosh_upper (t : ℝ) (ht : 0 ≤ t) :
    Real.cosh t ≤ Real.exp t := by
  have he : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  rw [Real.cosh_eq]
  linarith

private theorem theta_bessel_density_bound {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-x * Real.cosh t) * Real.cosh ((1 / 3 : ℝ) * t) ≤
      Real.exp (-x / 2 + 16 / δ) * Real.exp (-t) := by
  have hquad : -δ * t ^ 2 / 8 + t / 3 ≤ 16 / δ - t := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    have hi : (16 / δ) * δ = 16 := div_mul_cancel₀ _ hδ.ne'
    nlinarith [sq_nonneg (δ * t - 8)]
  have hc := theta_cosh_lower t ht
  have hxc : x / 2 + δ * t ^ 2 / 8 ≤ x * Real.cosh t := by
    have hmul := mul_le_mul_of_nonneg_left hc (hδ.trans_le hx).le
    have hmul' := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ t ^ 2 / 8)
    nlinarith
  calc
    _ ≤ Real.exp (-x * Real.cosh t) * Real.exp ((1 / 3 : ℝ) * t) :=
      mul_le_mul_of_nonneg_left (theta_cosh_upper _ (by positivity)) (Real.exp_pos _).le
    _ = Real.exp (-x * Real.cosh t + (1 / 3 : ℝ) * t) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-x / 2 + 16 / δ + -t) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_add _ _

private theorem theta_bessel_bound {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖besselK (1 / 3) x‖ ≤ Real.exp (16 / δ) * Real.exp (-x / 2) := by
  let g : ℝ → ℝ := fun t => Real.exp (-x / 2 + 16 / δ) * Real.exp (-t)
  have hg : IntegrableOn g (Set.Ioi 0) := by
    have h := (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul
      (Real.exp (-x / 2 + 16 / δ))
    change Integrable g (volume.restrict (Set.Ioi 0))
    convert h using 1
    funext t
    simp only [g, neg_one_mul]
  have hfmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-x * Real.cosh t) * Real.cosh ((1 / 3 : ℝ) * t))
      (volume.restrict (Set.Ioi 0)) := by
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi 0),
      ‖Real.exp (-x * Real.cosh t) * Real.cosh ((1 / 3 : ℝ) * t)‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact theta_bessel_density_bound hδ hx t ht.le
  have hf : IntegrableOn
      (fun t : ℝ => Real.exp (-x * Real.cosh t) * Real.cosh ((1 / 3 : ℝ) * t))
      (Set.Ioi 0) := hg.mono' hfmeas hbound
  have hint := norm_integral_le_of_norm_le hg hbound
  have hgi : (∫ t in Set.Ioi (0 : ℝ), g t) = Real.exp (-x / 2 + 16 / δ) := by
    rw [show g = fun t : ℝ => Real.exp (-x / 2 + 16 / δ) * Real.exp ((-1) * t) by
      funext t; simp only [g, neg_one_mul], integral_const_mul,
      integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0]
    norm_num
  change ‖∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-x * Real.cosh t) * Real.cosh ((1 / 3 : ℝ) * t)‖ ≤ _
  rw [hgi] at hint
  convert hint using 1 <;> rw [Real.exp_add] <;> ring

theorem theta_realization_summability_proved : ThetaRealizationProof.ThetaSummabilityStatement := by
  intro z v hv
  have hLambda : embedding lambda ≠ 0 := by
    rw [ThetaRealizationProof.embedding_lambda]
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (by norm_num : (0 : ℝ) < 3)))) Complex.I_ne_zero
  let κ : ℝ := ‖embedding lambda ^ (-3 : ℤ)‖
  have hκ : 0 < κ := norm_pos_iff.mpr (zpow_ne_zero _ hLambda)
  let δ : ℝ := 4 * Real.pi * κ * v
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let a : ℝ := 2 * Real.pi * κ * v
  have ha : 0 < a := by dsimp [a]; positivity
  let A : ℝ := (3 : ℝ) ^ (13 : ℕ) * κ ^ (5 : ℕ) * v * Real.exp (16 / δ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let K : ℝ := A * ((Nat.factorial 11 : ℝ) / a ^ (11 : ℕ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply Summable.of_norm
  apply (theta_element_inverse_cube_summable.mul_left K).of_nonneg_of_le (fun m => norm_nonneg _)
  intro m
  by_cases hm : m = 0
  · rw [ThetaRealizationProof.conjugateTerm, ite_eq_left hm, norm_zero]
    exact mul_nonneg hK (by change 0 ≤ 1 / ((principal m).absNorm : ℝ) ^ (3 : ℕ); positivity)
  have hs : 0 < ‖embedding m‖ := norm_pos_iff.mpr (embedding_eq_zero.not.mpr hm)
  have hfreq : ‖ThetaRealizationProof.frequency m‖ = κ * ‖embedding m‖ := by
    simp only [ThetaRealizationProof.frequency, norm_mul, κ]
  have hfreqLower : κ ≤ ‖ThetaRealizationProof.frequency m‖ := by
    rw [hfreq]
    exact le_mul_of_one_le_right hκ.le (theta_embedding_norm_one_le hm)
  have hx : δ ≤ 4 * Real.pi * ‖ThetaRealizationProof.frequency m‖ * v := by
    dsimp [δ]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfreqLower (by positivity)) hv.le
  have hc : ‖cuspCoefficient .zero (ThetaRealizationProof.frequency m)‖ ≤
      (3 : ℝ) ^ (13 : ℕ) * ‖ThetaRealizationProof.frequency m‖ ^ (5 : ℕ) := by
    simpa only [cuspCoefficient, norm_star, norm_neg] using
      theta_tau_growth (-ThetaRealizationProof.frequency m)
  have hmode : ‖thetaMode (ThetaRealizationProof.frequency m) z v‖ =
      v * ‖besselK (1 / 3) (4 * Real.pi * ‖ThetaRealizationProof.frequency m‖ * v)‖ := by
    simp only [thetaMode, norm_mul, theta_breve_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos hv]
  rw [ThetaRealizationProof.conjugateTerm, ite_eq_right hm, norm_mul, hmode]
  calc
    _ ≤ ((3 : ℝ) ^ (13 : ℕ) * ‖ThetaRealizationProof.frequency m‖ ^ (5 : ℕ)) *
        (v * (Real.exp (16 / δ) *
          Real.exp (-(4 * Real.pi * ‖ThetaRealizationProof.frequency m‖ * v) / 2))) :=
      mul_le_mul hc (mul_le_mul_of_nonneg_left (theta_bessel_bound hδ hx) hv.le)
        (by positivity) (by positivity)
    _ = A * (‖embedding m‖ ^ (5 : ℕ) * Real.exp (-a * ‖embedding m‖)) := by
      have hexp : -(4 * Real.pi * ‖ThetaRealizationProof.frequency m‖ * v) / 2 =
          -a * ‖embedding m‖ := by rw [hfreq]; dsimp [a]; ring
      rw [hexp, hfreq, mul_pow]
      dsimp [A]
      ring
    _ ≤ A * (((Nat.factorial 11 : ℝ) / a ^ (11 : ℕ)) / ‖embedding m‖ ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_left (theta_poly_exp_bound ha hs) hA
    _ = K * (1 / normElement m ^ (3 : ℕ)) := by
      rw [theta_normElement_eq_sq]
      dsimp [K]
      ring

end QRHShort.CloudBatch

#print axioms QRHShort.CloudBatch.theta_realization_summability_proved
