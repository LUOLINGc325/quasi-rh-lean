import QRHShort.FirstTransferPoissonPreMobiusNormalization

/-! The actual normalized Poisson row, with its literal zero term and the
uniform ray expansion of its finitely many nonzero frequencies. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort
open FirstTransferRayFourier

theorem first_transfer_preMobius_poisson_row (hp : PoissonStatement)
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {H L F : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    {C a b : Ideal O} (hC : SquarefreeOutside c.S C)
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hCa : IsRelPrime C a) (hCb : IsRelPrime C b) (hab : IsRelPrime a b)
    (f : Ideal O) (l : RayFourierIndex c → ℂ)
    (hpoint : ∀ (d : Ideal O) (h : O),
      firstTransferPoissonEnergyCoefficient c ξ W L f (C * a) *
        star (firstTransferPoissonEnergyCoefficient c ξ W L f (C * b)) *
        (firstTransferPrimitivePairedCharacter c ha hb hab).gauss *
        (firstTransferPrimitivePairedCharacter c ha hb hab).value (primaryGenerator d) *
        star ((firstTransferPrimitivePairedCharacter c ha hb hab).value h) =
      firstTransferOffDiagonalLead C f * W (normIdeal (C * a) / L) *
        star (W (normIdeal (C * b) / L)) *
        ∑ ψ : RayFourierIndex c, l ψ *
          (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
            (h * primaryGenerator f ^ 2) a *
            star (firstTransferCoefficient c (rayFourierCharacter c ψ) C d 1
              (h * primaryGenerator f ^ 2) b))) :
    (((L * F)⁻¹ : ℝ) : ℂ) * firstTransferPoissonEnergyGcdTerm c ξ Φ W H L f (C, a, b) =
      firstTransferPreMobiusZeroTerm c Φ ξ W H L F f (C, a, b) +
        ∑ ψ : RayFourierIndex c, l ψ *
          (∑ d ∈ firstTransferPoissonDivisors C,
            ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
              firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h (a, b)) := by
  let χ := firstTransferPrimitivePairedCharacter c ha hb hab
  let A : ℂ := firstTransferPoissonEnergyCoefficient c ξ W L f (C * a) *
    star (firstTransferPoissonEnergyCoefficient c ξ W L f (C * b))
  let S : ℂ := (((L * F)⁻¹ : ℝ) : ℂ) * A *
    ((H : ℂ) * χ.gauss / (Real.sqrt (normIdeal (a * b)) : ℂ))
  have hadm : firstTransferGcdTripleAdmissible c (C, a, b) := ⟨hC, ha, hb, hCa, hCb, hab⟩
  have hfreq (d : Ideal O) (hd : d ∈ firstTransferPoissonDivisors C) :
      (∑ h ∈ firstTransferPreMobiusOldFrequencies Φ H d a b,
        S * (((mobius d : ℂ) * χ.value (primaryGenerator d) / (normIdeal d : ℂ)) *
          (star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
            (H * normElement h / (normIdeal d * normIdeal (a * b)))))) =
      ∑ ψ : RayFourierIndex c, l ψ *
        (∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
          firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h (a, b)) := by
    have hdC : d ∣ C := by
      have h := mem_firstTransferPoissonDivisors.mp hd
      rwa [first_transfer_outsideRadical_eq_self_of_squarefree hC.1.1 hC.2] at h
    have hd0 : d ≠ ⊥ := ne_zero_of_dvd_ne_zero hC.1.1 hdC
    calc
      _ = ∑ h ∈ firstTransferPreMobiusOldFrequencies Φ H d a b,
          ∑ ψ : RayFourierIndex c, l ψ *
            firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h (a, b) := by
        apply Finset.sum_congr rfl
        intro h hh
        calc
          _ = (mobius d : ℂ) *
              ((((L * F)⁻¹ : ℝ) : ℂ) * (H : ℂ) /
                (Real.sqrt (normIdeal (a * b)) : ℂ) / (normIdeal d : ℂ)) *
              (A * χ.gauss * χ.value (primaryGenerator d) * star (χ.value h)) *
              radialFourier (fun x => (Φ.value x : ℂ))
                (H * normElement h / (normIdeal d * normIdeal (a * b))) := by
            dsimp only [S]
            ring
          _ = _ := first_transfer_preMobius_normalize_ray_expansion c Φ W hL hF H
            hC.1.1 hd0 ha.1.1 hb.1.1 f h l _ (hpoint d h)
      _ = ∑ ψ : RayFourierIndex c, l ψ *
          (∑ h ∈ firstTransferPreMobiusOldFrequencies Φ H d a b,
            firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h (a, b)) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ψ hψ
        rw [first_transfer_preMobius_kernelTerm_frequency_sums c I Φ
          (rayFourierCharacter c ψ) hW hH hL F hC.1.1 hd0 ha.1.1 hb.1.1 f]
  have hoff :
      S * (∑ d ∈ firstTransferPoissonDivisors C,
        ((mobius d : ℂ) * χ.value (primaryGenerator d) / (normIdeal d : ℂ)) *
          ∑ h ∈ firstTransferPreMobiusOldFrequencies Φ H d a b,
            star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
              (H * normElement h / (normIdeal d * normIdeal (a * b)))) =
      ∑ ψ : RayFourierIndex c, l ψ *
        (∑ d ∈ firstTransferPoissonDivisors C,
          ∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
            firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h (a, b)) := by
    simp only [Finset.mul_sum]
    calc
      _ = ∑ d ∈ firstTransferPoissonDivisors C, ∑ ψ : RayFourierIndex c, l ψ *
          (∑ h ∈ firstTransferPreMobiusFrequencies I Φ H L C d,
            firstTransferPreMobiusKernelTerm c Φ (rayFourierCharacter c ψ) W H L F C d f h (a, b)) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hfreq d hd
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
  have hrow := first_transfer_poisson_gcd_row_truncation hp c hC ha hb hab Φ hH
  rw [← first_transfer_poisson_divisors_eq_squarefree hC.1.1 hC.2] at hrow
  change (∑' k : O, (Φ.value (normElement k / H) : ℂ) *
    sexticSymbol (C * a) k * star (sexticSymbol (C * b) k)) =
    poissonZeroTerm χ C (fun x => (Φ.value x : ℂ)) H +
      (H : ℂ) * χ.gauss / (Real.sqrt (normIdeal (a * b)) : ℂ) *
        ∑ d ∈ firstTransferPoissonDivisors C,
          ((mobius d : ℂ) * χ.value (primaryGenerator d) / (normIdeal d : ℂ)) *
            ∑ h ∈ firstTransferPreMobiusOldFrequencies Φ H d a b,
              star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
                (H * normElement h / (normIdeal d * normIdeal (a * b))) at hrow
  rw [firstTransferPoissonEnergyGcdTerm, ite_eq_left hadm]
  simp only [firstTransferPoissonEnergyCharacterRow]
  rw [hrow, firstTransferPreMobiusZeroTerm, dite_eq_left hadm, ← hoff]
  dsimp only [S, A, χ]
  ring

end QRHShort
