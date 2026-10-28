import QRHShort.FirstTransferPairedGaussRayExpansion
import QRHShort.FirstTransferPoissonEnergyExpansion
import QRHShort.FirstTransferSymbolIdentities

/-!
Pointwise coefficient algebra for the Poisson-transformed energy. These
identities use the frozen literal coefficients and character values; no
interchange of a sum with an integral or another infinite sum occurs here.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

/-- Every allowed original coefficient has unit norm. -/
theorem first_transfer_poisson_coefficient_norm (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {n : Ideal O}
    (hn : SquarefreeOutside c.S n) : ‖coefficient ξ.val n‖ = 1 := by
  have hray : ‖rayValue ξ.val n‖ = 1 := by
    rw [FirstTransferRayFourier.rayValue_eq_rayClassCharacter c ξ hn.1]
    exact FirstTransferRayFourier.norm_rayClassCharacter c ξ _
  simp only [coefficient, norm_mul, norm_star, first_transfer_norm_alpha_eq_one c hn.1,
    first_transfer_norm_gauss_two c hc hn, hray, one_mul]

theorem first_transfer_poisson_coefficient_mul_star (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {n : Ideal O}
    (hn : SquarefreeOutside c.S n) : coefficient ξ.val n * star (coefficient ξ.val n) = 1 := by
  simpa only [starRingEnd_apply, first_transfer_poisson_coefficient_norm c hc ξ hn,
    one_pow, Complex.ofReal_one] using Complex.mul_conj' (coefficient ξ.val n)

/-- The common ideal is split using precisely the coefficient product law
contained in the permitted arithmetic premise. -/
theorem first_transfer_poisson_energy_coefficient_mul (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) (W : ℝ → ℂ) (L : ℝ)
    (f : Ideal O) {C a : Ideal O} (hC : SquarefreeOutside c.S C)
    (ha : SquarefreeOutside c.S a) (hCa : IsRelPrime C a) :
    firstTransferPoissonEnergyCoefficient c ξ W L f (C * a) =
      coefficient ξ.val C * coefficient ξ.val a *
        sexticSymbol a (primaryGenerator C) ^ (4 : ℕ) *
        sexticSymbol C (primaryGenerator f) ^ (4 : ℕ) *
        sexticSymbol a (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal (C * a) / L) := by
  have hCaout : SquarefreeOutside c.S (C * a) :=
    ⟨(first_transfer_outside_mul_iff c C a).mpr ⟨hC.1, ha.1⟩,
      squarefree_mul_iff.mpr ⟨hCa, hC.2, ha.2⟩⟩
  obtain ⟨G, R, hG, hsign, hsym, hRleft, hRright, hGmul, hrec, hgauss,
    hcoeff, hquot⟩ := hc
  rw [firstTransferPoissonEnergyCoefficient, ite_eq_left hCaout,
    hcoeff ξ C a hC ha hCa, first_transfer_sexticSymbol_mul, mul_pow]
  ring

/-- All remaining sextic factors combine into the literal first-transfer
numerator. This includes the zero extensions at nonunits. -/
theorem first_transfer_poisson_symbol_coefficient_product (c : ArithmeticContext)
    (η : RayCharacter c) (C d f : Ideal O) (h : O) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) :
    ((mobius a : ℂ) * (mobius b : ℂ) * rayValue η.val a * star (rayValue η.val b)) *
      (sexticSymbol a (primaryGenerator C) ^ (4 : ℕ) *
        star (sexticSymbol b (primaryGenerator C) ^ (4 : ℕ))) *
      (sexticSymbol a (primaryGenerator f) ^ (4 : ℕ) *
        star (sexticSymbol b (primaryGenerator f) ^ (4 : ℕ))) *
      (sexticSymbol a (primaryGenerator d) * star (sexticSymbol b (primaryGenerator d))) *
      (star (sexticSymbol a h) * sexticSymbol b h) =
        firstTransferCoefficient c η C d 1 (h * primaryGenerator f ^ 2) a *
          star (firstTransferCoefficient c η C d 1 (h * primaryGenerator f ^ 2) b) := by
  have haz := (first_transfer_sexticSymbol_fourth_mul_star c ha.1 (primaryGenerator f) h).symm
  have hbz : sexticSymbol b (h * primaryGenerator f ^ 2) =
      star (sexticSymbol b (primaryGenerator f) ^ (4 : ℕ)) * sexticSymbol b h := by
    simpa only [star_mul, star_star, mul_comm] using
      (congrArg star (first_transfer_sexticSymbol_fourth_mul_star c hb.1
        (primaryGenerator f) h)).symm
  simp only [firstTransferCoefficient,
    ite_eq_left (show SquarefreeOutside c.S a ∧ IsRelPrime a 1 from
      ⟨ha, isRelPrime_one_right⟩),
    ite_eq_left (show SquarefreeOutside c.S b ∧ IsRelPrime b 1 from
      ⟨hb, isRelPrime_one_right⟩), star_mul, star_star, star_pow, star_intCast]
  rw [haz, hbz]
  simp only [star_pow]
  ring

end QRHShort
