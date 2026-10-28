import QRHShort.FixedFieldPNT
import OAI.NumberTheory.DirichletL.PrimeCounting.LandauAnnularBridge

/-!
An explicit proof layer for the analytic Landau boundary.

The AP/PNT side is represented by `FixedFieldDyadicPrimeMassLowerBound`:
this is the dyadic logarithmic mass estimate obtained after applying the
residue-class or ray-prime theorem.  The theorems below keep that analytic
input separate from the finite deletion and cardinality arguments.  Thus a
future OAI `primeLogMass_ratio_tendsto` proof can be plugged in here without
changing the downstream `DyadicPrimeIdeals` interface.
-/

noncomputable section
open Classical
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.PNT
open OAI.SevenEighths.PNT.AnnularPrimeMass
open OAI.SevenEighths.HeckeRayPrimes
open OAI.SevenEighths.HeckeFamily

namespace QRHShort

/-- AP/ray prime input in the exact form needed by the finite Landau bridge.

The intended instantiation is the principal ray (`M = 1`) of the
Eisenstein field; the residue-class theorem supplies this estimate after the
usual finite-fibre and dyadic partial-summation step. -/
def APDyadicPrimeMassInput : Prop :=
  FixedFieldDyadicPrimeMassLowerBound

theorem globalPrimeIdealDyadicLowerBound_of_APMass
    (hAP : APDyadicPrimeMassInput) :
    GlobalPrimeIdealDyadicLowerBound :=
  globalPrimeIdealDyadicLowerBound_of_fixedFieldMass hAP

/-! The closed principal-ray proof exposes the same finite-support conclusion
as the former Landau interface, without retaining an external premise. -/
theorem landau_prime_ideal_dyadic_lower_bound_from_AP
    (hAP : APDyadicPrimeMassInput) (S : Finset (Ideal O)) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℝ, 1 < Y₀ ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        c * Y / Real.log Y ≤ (Nat.card (DyadicPrimeIdeals S Y) : ℝ) :=
  dyadicPrimeIdeals_lower_bound_of_global
    (globalPrimeIdealDyadicLowerBound_of_APMass hAP) S

theorem dyadicPrimeFinset_eventually_many_of_AP
    (hAP : APDyadicPrimeMassInput) (S : Finset (Ideal O)) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℝ, 1 < Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      c * Y / Real.log Y ≤ ((dyadicPrimeFinset S Y).card : ℝ) ∧
        (dyadicPrimeFinset S Y).Nonempty := by
  obtain ⟨c, hc, Y₀, hY₀, hcount⟩ :=
    landau_prime_ideal_dyadic_lower_bound_from_AP hAP S
  refine ⟨c, hc, Y₀, hY₀, ?_⟩
  intro Y hY
  have hcard : c * Y / Real.log Y ≤ ((dyadicPrimeFinset S Y).card : ℝ) := by
    simpa only [card_dyadicPrimeFinset] using hcount Y hY
  exact ⟨hcard, dyadicPrimeFinset_nonempty (hY₀.trans_le hY) hc hcard⟩


/-- The principal ray at unit modulus is exactly the set of nonzero ideals. -/
theorem annularPrincipalPrimeIdeals_eq_dyadic (Y : ℝ) :
    annularPrimeIdeals (RayOrthogonality.principalIdeals (1 : Ideal O))
      (1 / 2 : ℝ) 1 Y = allDyadicPrimeFinset Y := by
  classical
  ext P
  rw [mem_annularPrimeIdeals, mem_allDyadicPrimeFinset]
  constructor
  · rintro ⟨hC, hprime, hlo, hhi⟩
    have hnorm : 0 < normIdeal P := by
      unfold normIdeal
      exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
        hprime.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    refine ⟨hprime, ?_, ?_⟩
    · by_cases hY : 0 ≤ Y / 2
      · rw [show Y * (1 / 2 : ℝ) = Y / 2 by ring, Nat.floor_lt hY] at hlo
        exact hlo
      · have hf : ⌊Y / 2⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        rw [show Y * (1 / 2 : ℝ) = Y / 2 by ring, hf] at hlo
        linarith
    · by_cases hY : 0 ≤ Y
      · rw [show Y * (1 : ℝ) = Y by ring, Nat.le_floor_iff hY] at hhi
        exact hhi
      · have hf : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        rw [show Y * (1 : ℝ) = Y by ring, hf] at hhi
        exfalso
        linarith
  · rintro ⟨hprime, hlo, hhi⟩
    have hnorm : 0 < normIdeal P := by
      unfold normIdeal
      exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
        hprime.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    refine ⟨?_, hprime, ?_, ?_⟩
    · apply (principalIdeals_one).2
      intro hbot
      exact hprime.ne_zero (by simpa [hbot])
    · by_cases hY : 0 ≤ Y / 2
      · rw [show Y * (1 / 2 : ℝ) = Y / 2 by ring, Nat.floor_lt hY]
        exact hlo
      · rw [show Y * (1 / 2 : ℝ) = Y / 2 by ring,
          Nat.floor_eq_zero.mpr (by linarith)]
        have hnormNat : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (fun hz =>
          hprime.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
        exact_mod_cast hnormNat
    · by_cases hY : 0 ≤ Y
      · rw [show Y * (1 : ℝ) = Y by ring, Nat.le_floor_iff hY]
        exact hhi
      · exfalso
        linarith

/-- The cutoff weighted logarithmic mass is bounded by the raw dyadic mass. -/
theorem dyadicCutoff_weighted_le_raw (Y : ℝ) (hY : 0 < Y) :
    (∑ P ∈ annularPrimeIdeals (RayOrthogonality.principalIdeals (1 : Ideal O))
        (1 / 2 : ℝ) 1 Y,
      Real.log (Ideal.absNorm P) * dyadicCutoff (Ideal.absNorm P / Y))
      ≤ dyadicPrimeLogMass (∅ : Finset (Ideal O)) Y := by
  rw [annularPrincipalPrimeIdeals_eq_dyadic]
  unfold dyadicPrimeLogMass
  apply Finset.sum_le_sum
  intro P hP
  have hmem := (mem_allDyadicPrimeFinset.mp hP)
  have hratio : Ideal.absNorm P / Y ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hY).2
      change (1 / 2 : ℝ) * Y ≤ (Ideal.absNorm P : ℝ)
      have h := hmem.2.1.le
      change Y / 2 ≤ (Ideal.absNorm P : ℝ) at h
      linarith
    · apply (div_le_iff₀ hY).2
      change (Ideal.absNorm P : ℝ) ≤ 1 * Y
      have h := hmem.2.2
      change (Ideal.absNorm P : ℝ) ≤ Y at h
      linarith
  have hcut0 := dyadicCutoff_nonneg hratio
  have hcut1 := dyadicCutoff_le_one hratio
  have hlog : 0 ≤ Real.log (Ideal.absNorm P) := by
    apply Real.log_nonneg
    have hnorm : 0 < Ideal.absNorm P := by
      exact Nat.pos_of_ne_zero (fun hz =>
        hmem.1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnorm.ne')
  calc
    Real.log (Ideal.absNorm P) * dyadicCutoff (Ideal.absNorm P / Y)
        ≤ Real.log (Ideal.absNorm P) * 1 :=
      mul_le_mul_of_nonneg_left hcut1 hlog
    _ = Real.log (Ideal.absNorm P) := by ring

/-- The principal-ray annular theorem gives a positive linear lower bound for
raw dyadic prime-log mass. -/
theorem dyadicPrimeLogMass_linear_lower_from_ray :
    GenericMass.LinearMassLowerBound
      (dyadicPrimeLogMass (∅ : Finset (Ideal O))) := by
  let φ : ℝ → ℝ := dyadicCutoff
  have hφ : Differentiable ℝ φ := by
    intro x
    unfold φ dyadicCutoff
    fun_prop
  have hφ' : Continuous (deriv φ) := by
    unfold φ dyadicCutoff
    fun_prop
  have hI : 0 < ∫ y in (1 / 2 : ℝ)..1, φ y := by
    simpa [φ] using dyadicCutoff_integral
  obtain ⟨d, hd, Y₀, hY₀⟩ :=
    principalRay_primeLogAnnular_eventually_linear (M := (1 : Ideal O))
      φ hφ hφ' (by norm_num) (by norm_num)
        (by norm_num [φ, dyadicCutoff]) (by norm_num [φ, dyadicCutoff]) hI
  let Y₁ : ℝ := max Y₀ 2
  have hY₁ : 1 < Y₁ := by
    dsimp [Y₁]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨d, hd, Y₁, hY₁, ?_⟩
  intro Y hY
  have hYpos : 0 < Y := (lt_trans zero_lt_one hY₁).trans_le hY
  have hcomp := dyadicCutoff_weighted_le_raw Y hYpos
  have hlin := hY₀ Y ((le_max_left _ _).trans hY)
  have hlin' : d * Y ≤
      (∑ P ∈ annularPrimeIdeals (RayOrthogonality.principalIdeals (1 : Ideal O))
        (1 / 2 : ℝ) 1 Y,
        Real.log (Ideal.absNorm P) * dyadicCutoff (Ideal.absNorm P / Y)) := by
    simpa [φ, primeLogAnnularSum] using hlin
  exact hlin'.trans hcomp

/-- The fixed-field input and all finite-deletion counting follow from the
principal-ray annular prime theorem. -/
theorem fixedFieldDyadicPrimeMassLowerBound_from_ray :
    FixedFieldDyadicPrimeMassLowerBound :=
  fixedFieldDyadicPrimeMassLowerBound_of_linear
    dyadicPrimeLogMass_linear_lower_from_ray

/-- Eventual many-prime conclusion with the analytic input supplied by the
principal ray, retaining the original finite-set interface. -/
theorem dyadicPrimeFinset_eventually_many_from_ray (S : Finset (Ideal O)) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℝ, 1 < Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      c * Y / Real.log Y ≤ ((dyadicPrimeFinset S Y).card : ℝ) ∧
        (dyadicPrimeFinset S Y).Nonempty := by
  exact dyadicPrimeFinset_eventually_many_of_AP
    fixedFieldDyadicPrimeMassLowerBound_from_ray S

end QRHShort
