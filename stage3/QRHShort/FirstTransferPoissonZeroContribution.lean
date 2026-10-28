import QRHShort.PoissonStatements

/-! The actual Poisson zero term has only a principal contribution.  Its
Euler product has norm at most one.  The Poisson-zero statement is retained
as an explicit permitted premise; no additive-character theorem is imported. -/

noncomputable section

open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort

theorem first_transfer_primitive_character_eq_one_iff (χ : PrimitiveResidueCharacter) :
    χ.character = 1 ↔ χ.modulus = ⊤ := by
  constructor
  · intro hχ
    apply Eq.symm
    apply χ.primitive ⊤ top_ne_bot le_top
    refine ⟨1, ?_⟩
    intro a ha
    rw [hχ, MulChar.one_apply ha]
    let : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have hx : Ideal.Quotient.mk (⊤ : Ideal O) a = 1 := Subsingleton.elim _ _
    rw [hx, map_one]
  · intro hmod
    let : Subsingleton (O ⧸ χ.modulus) := Ideal.Quotient.subsingleton_iff.mpr hmod
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    simp only [hx, Units.val_one, map_one]

theorem first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal
    (hz : PoissonZeroStatement) (χ : PrimitiveResidueCharacter) (hχ : χ.character ≠ 1)
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) : poissonZeroTerm χ r Φ H = 0 := by
  unfold poissonZeroTerm
  simp only [hz.1 χ hχ, mul_zero, zero_mul, ite_self, tsum_zero]

theorem first_transfer_poissonZeroTerm_eq_zero_of_modulus_ne_top
    (hz : PoissonZeroStatement) (χ : PrimitiveResidueCharacter) (hχ : χ.modulus ≠ ⊤)
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) : poissonZeroTerm χ r Φ H = 0 :=
  first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal hz χ
    (mt (first_transfer_primitive_character_eq_one_iff χ).mp hχ) r Φ H

theorem first_transfer_zero_contribution_one_le_normIdeal {a : Ideal O} (ha : a ≠ ⊥) :
    1 ≤ normIdeal a := by
  let : Finite (O ⧸ a) := Ring.HasFiniteQuotients.finiteQuotient ha
  have hN : a.absNorm ≠ 0 := (Ideal.absNorm_ne_zero_iff a).mpr inferInstance
  have hNat : 1 ≤ a.absNorm := Nat.one_le_iff_ne_zero.mpr hN
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast hNat

theorem first_transfer_zero_euler_factor_norm_le_one {P : Ideal O} (hP : P ≠ ⊥) :
    ‖(1 : ℂ) - (normIdeal P : ℂ)⁻¹‖ ≤ 1 := by
  have hN := first_transfer_zero_contribution_one_le_normIdeal hP
  have hN0 : 0 ≤ normIdeal P := le_trans zero_le_one hN
  have hi0 : 0 ≤ (normIdeal P)⁻¹ := inv_nonneg.mpr hN0
  have hi1 : (normIdeal P)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have hsub : 0 ≤ 1 - (normIdeal P)⁻¹ := sub_nonneg.mpr hi1
  have hcast : (1 : ℂ) - (normIdeal P : ℂ)⁻¹ =
      ((1 - (normIdeal P)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsub]
  exact sub_le_self _ hi0

theorem first_transfer_zero_euler_product_norm_le_one (r : Ideal O) :
    ‖∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  have hp : Prime P := prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  exact first_transfer_zero_euler_factor_norm_le_one hp.ne_zero

theorem first_transfer_poissonZeroTerm_norm_le (hz : PoissonZeroStatement)
    (χ : PrimitiveResidueCharacter) (r : Ideal O) (hr : r ≠ ⊥)
    (Φ : RowWeight) (H : ℝ) (hH : 0 < H) :
    ‖poissonZeroTerm χ r (fun x => (Φ.value x : ℂ)) H‖ ≤
      H * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ := by
  by_cases hχ : χ.character = 1
  · rw [hz.2 χ r (fun x => (Φ.value x : ℂ)) H hχ
      ((first_transfer_primitive_character_eq_one_iff χ).mp hχ) hr hH Φ.schwartz]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    exact mul_le_of_le_one_right (mul_nonneg hH.le (norm_nonneg _))
      (first_transfer_zero_euler_product_norm_le_one r)
  · rw [first_transfer_poissonZeroTerm_eq_zero_of_nonprincipal hz χ hχ, norm_zero]
    exact mul_nonneg hH.le (norm_nonneg _)

end QRHShort
