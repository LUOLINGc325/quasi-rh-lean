import QRHShort.FirstTransferPoissonCoefficientExpansionAlgebra

/-!
One uniformly bounded ray expansion simultaneously gives the pointwise
Poisson coefficient identity for every common ideal, pair, numerator,
weight, and scale. This is finite algebra and does not exchange sums.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort
open FirstTransferRayFourier

/-- Uniform pointwise coefficient expansion for the actual paired primitive
Gauss sum. B is chosen before the original ray character and l before every
row/column parameter. The numerator ideals f,d and the weight/scale are
arbitrary; the application may impose their additional restrictions later. -/
theorem first_transfer_poisson_coefficient_uniform_expansion
    (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : RayCharacter c,
      ∃ l : RayFourierIndex c → ℂ,
        (∑ ψ : RayFourierIndex c, ‖l ψ‖) ≤ B ∧
        ∀ (C a b f d : Ideal O) (h : O) (W : ℝ → ℂ) (L : ℝ)
          (hC : SquarefreeOutside c.S C) (ha : SquarefreeOutside c.S a)
          (hb : SquarefreeOutside c.S b) (hCa : IsRelPrime C a)
          (hCb : IsRelPrime C b) (hab : IsRelPrime a b),
          firstTransferPoissonEnergyCoefficient c ξ W L f (C * a) *
            star (firstTransferPoissonEnergyCoefficient c ξ W L f (C * b)) *
            (firstTransferPrimitivePairedCharacter c ha hb hab).gauss *
            (firstTransferPrimitivePairedCharacter c ha hb hab).value (primaryGenerator d) *
            star ((firstTransferPrimitivePairedCharacter c ha hb hab).value h) =
              (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ) *
                star (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ))) *
                W (normIdeal (C * a) / L) * star (W (normIdeal (C * b) / L)) *
                ∑ ψ : RayFourierIndex c, l ψ *
                  (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
                    (h * primaryGenerator f ^ 2) a *
                    star (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
                      (h * primaryGenerator f ^ 2) b)) := by
  obtain ⟨B, hB, hexp⟩ := first_transfer_primitive_paired_gauss_uniform_ray_expansion c hc
  refine ⟨B, hB, ?_⟩
  intro ξ
  obtain ⟨l, hl, hidentity⟩ := hexp ξ
  refine ⟨l, hl, ?_⟩
  intro C a b f d h W L hC ha hb hCa hCb hab
  let P : ℂ := (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ) *
      star (sexticSymbol C (primaryGenerator f) ^ (4 : ℕ))) *
      W (normIdeal (C * a) / L) * star (W (normIdeal (C * b) / L))
  let K : ℂ :=
    (sexticSymbol a (primaryGenerator C) ^ (4 : ℕ) *
      star (sexticSymbol b (primaryGenerator C) ^ (4 : ℕ))) *
    (sexticSymbol a (primaryGenerator f) ^ (4 : ℕ) *
      star (sexticSymbol b (primaryGenerator f) ^ (4 : ℕ))) *
    (sexticSymbol a (primaryGenerator d) * star (sexticSymbol b (primaryGenerator d))) *
    (star (sexticSymbol a h) * sexticSymbol b h)
  have hK (η : RayCharacter c) :
      ((mobius a : ℂ) * (mobius b : ℂ) * rayValue η.val a * star (rayValue η.val b)) * K =
        firstTransferCoefficient c η C d 1 (h * primaryGenerator f ^ 2) a *
          star (firstTransferCoefficient c η C d 1 (h * primaryGenerator f ^ 2) b) := by
    simpa only [K, mul_assoc] using
      first_transfer_poisson_symbol_coefficient_product c η C d f h ha hb
  have hraw :
      firstTransferPoissonEnergyCoefficient c ξ W L f (C * a) *
        star (firstTransferPoissonEnergyCoefficient c ξ W L f (C * b)) *
        (firstTransferPrimitivePairedCharacter c ha hb hab).gauss *
        (firstTransferPrimitivePairedCharacter c ha hb hab).value (primaryGenerator d) *
        star ((firstTransferPrimitivePairedCharacter c ha hb hab).value h) =
      P * ((coefficient ξ.val a * star (coefficient ξ.val b) *
        (firstTransferPrimitivePairedCharacter c ha hb hab).gauss) * K) := by
    rw [first_transfer_poisson_energy_coefficient_mul c hc ξ W L f hC ha hCa,
      first_transfer_poisson_energy_coefficient_mul c hc ξ W L f hC hb hCb]
    simp only [firstTransferPrimitivePairedCharacter_value, star_mul, star_star, star_pow]
    calc
      _ = (coefficient ξ.val C * star (coefficient ξ.val C)) *
          (P * ((coefficient ξ.val a * star (coefficient ξ.val b) *
            (firstTransferPrimitivePairedCharacter c ha hb hab).gauss) * K)) := by
        simp only [P, K, star_pow]
        ring
      _ = _ := by
        rw [first_transfer_poisson_coefficient_mul_star c hc ξ hC, one_mul]
  rw [hraw, hidentity a b ha hb hab]
  change P * ((∑ ψ : RayFourierIndex c, l ψ *
      ((mobius a : ℂ) * (mobius b : ℂ) * rayValue (rayFourierCharacter c ψ).val a *
        star (rayValue (rayFourierCharacter c ψ).val b))) * K) = P * _
  apply congrArg (fun z : ℂ => P * z)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ψ _
  rw [mul_assoc, hK]

end QRHShort
