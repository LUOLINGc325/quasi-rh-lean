import QRHShort.FirstTransferFiniteSupport
import QRHShort.PoissonStatements

/-!
Finite support and the exact zero/nonzero-frequency split of the literal
Poisson right-hand side. The original row equality is used only through the
explicit PoissonStatement premise. No zero-frequency evaluation is assumed.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_poisson_outsideRadical_ne_bot (S : Finset (Ideal O)) (r : Ideal O) :
    outsideRadical S r ≠ ⊥ := by
  unfold outsideRadical
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  apply UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
  have hp := (Finset.mem_filter.mp hP).1
  simpa only [primeFactors, Multiset.mem_toFinset] using hp

def firstTransferPoissonDivisors (r : Ideal O) : Finset (Ideal O) :=
  (first_transfer_divisors_finite (first_transfer_poisson_outsideRadical_ne_bot ∅ r)).toFinset

theorem mem_firstTransferPoissonDivisors {r d : Ideal O} :
    d ∈ firstTransferPoissonDivisors r ↔ d ∣ outsideRadical ∅ r := by
  simp only [firstTransferPoissonDivisors, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

def firstTransferPoissonDivisorCoefficient (χ : PrimitiveResidueCharacter) (d : Ideal O) : ℂ :=
  (mobius d : ℂ) * χ.value (chosenGenerator d) / (normIdeal d : ℂ)

def firstTransferPoissonDualTerm (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    (H : ℝ) (d : Ideal O) (h : O) : ℂ :=
  star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
    (H * normElement h / (normIdeal d * normIdeal χ.modulus))

def firstTransferPoissonFrequencies (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    (H : ℝ) (d : Ideal O) : Finset O :=
  (finite_normElement_le (Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H)).toFinset.erase 0

theorem mem_firstTransferPoissonFrequencies {χ : PrimitiveResidueCharacter} {Φ : RowWeight}
    {H : ℝ} {d : Ideal O} {h : O} :
    h ∈ firstTransferPoissonFrequencies χ Φ H d ↔
      h ≠ 0 ∧ normElement h ≤ Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H := by
  simp only [firstTransferPoissonFrequencies, Finset.mem_erase, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, ne_eq]

theorem first_transfer_poisson_dual_support (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    Function.support (firstTransferPoissonDualTerm χ Φ H d) ⊆
      {h : O | normElement h ≤ Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H} := by
  intro h hh
  have hden : 0 < normIdeal d * normIdeal χ.modulus :=
    mul_pos (normIdeal_pos hd) (normIdeal_pos χ.modulus_ne_bot)
  have hfourier : radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal d * normIdeal χ.modulus)) ≠ 0 := by
    intro hz
    exact hh (by simp only [firstTransferPoissonDualTerm, hz, mul_zero])
  have hx : 0 ≤ H * normElement h / (normIdeal d * normIdeal χ.modulus) :=
    div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _)) hden.le
  have hcap := (Φ.fourier_support ⟨hfourier, hx⟩).2
  apply (le_div_iff₀ hH).mpr
  calc
    normElement h * H = H * normElement h := mul_comm _ _
    _ ≤ Φ.fourierCap * (normIdeal d * normIdeal χ.modulus) := (div_le_iff₀ hden).mp hcap
    _ = Φ.fourierCap * normIdeal d * normIdeal χ.modulus := by ring

theorem first_transfer_poisson_dual_hasFiniteSupport (χ : PrimitiveResidueCharacter)
    (Φ : RowWeight) {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    Function.HasFiniteSupport (firstTransferPoissonDualTerm χ Φ H d) :=
  (finite_normElement_le (Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H)).subset
    (first_transfer_poisson_dual_support χ Φ hH hd)

theorem first_transfer_poisson_dual_summable (χ : PrimitiveResidueCharacter)
    (Φ : RowWeight) {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    Summable (firstTransferPoissonDualTerm χ Φ H d) :=
  summable_of_hasFiniteSupport (first_transfer_poisson_dual_hasFiniteSupport χ Φ hH hd)

theorem first_transfer_poisson_dual_zero (χ : PrimitiveResidueCharacter)
    (Φ : RowWeight) (H : ℝ) (d : Ideal O) :
    firstTransferPoissonDualTerm χ Φ H d 0 =
      star (χ.value 0) * radialFourier (fun x => (Φ.value x : ℂ)) 0 := by
  simp only [firstTransferPoissonDualTerm, normElement, principal, Ideal.span_singleton_zero,
    normIdeal, Ideal.absNorm_bot, Nat.cast_zero, mul_zero, zero_div]

theorem first_transfer_poisson_dual_split (χ : PrimitiveResidueCharacter) (Φ : RowWeight)
    {H : ℝ} (hH : 0 < H) {d : Ideal O} (hd : d ≠ ⊥) :
    (∑' h : O, firstTransferPoissonDualTerm χ Φ H d h) =
      star (χ.value 0) * radialFourier (fun x => (Φ.value x : ℂ)) 0 +
        ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d,
          firstTransferPoissonDualTerm χ Φ H d h := by
  have hs := first_transfer_poisson_dual_summable χ Φ hH hd
  have hzero (h : O) (hh : h ∉ firstTransferPoissonFrequencies χ Φ H d) :
      (if h = 0 then 0 else firstTransferPoissonDualTerm χ Φ H d h) = 0 := by
    by_cases hh0 : h = 0
    · rw [if_pos hh0]
    · rw [if_neg hh0]
      by_contra hne
      exact hh (mem_firstTransferPoissonFrequencies.mpr
        ⟨hh0, first_transfer_poisson_dual_support χ Φ hH hd hne⟩)
  have htail : (∑' h : O, if h = 0 then 0 else firstTransferPoissonDualTerm χ Φ H d h) =
      ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d, firstTransferPoissonDualTerm χ Φ H d h := by
    rw [tsum_eq_sum hzero]
    apply Finset.sum_congr rfl
    intro h hh
    rw [if_neg (mem_firstTransferPoissonFrequencies.mp hh).1]
  rw [hs.tsum_eq_add_tsum_ite 0, first_transfer_poisson_dual_zero, htail]

theorem first_transfer_poisson_divisor_hasFiniteSupport (r : Ideal O) (v : Ideal O → ℂ) :
    Function.HasFiniteSupport (fun d : Ideal O =>
      if d ∣ outsideRadical ∅ r then v d else 0) := by
  apply (firstTransferPoissonDivisors r).finite_toSet.subset
  intro d hd
  by_cases hdiv : d ∣ outsideRadical ∅ r
  · exact mem_firstTransferPoissonDivisors.mpr hdiv
  · exact False.elim (hd (if_neg hdiv))

theorem first_transfer_poisson_divisor_tsum_eq_sum (r : Ideal O) (v : Ideal O → ℂ) :
    (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then v d else 0) =
      ∑ d ∈ firstTransferPoissonDivisors r, v d := by
  have hzero (d : Ideal O) (hd : d ∉ firstTransferPoissonDivisors r) :
      (if d ∣ outsideRadical ∅ r then v d else 0) = 0 := by
    apply if_neg
    exact fun hdiv => hd (mem_firstTransferPoissonDivisors.mpr hdiv)
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro d hd
  rw [if_pos (mem_firstTransferPoissonDivisors.mp hd)]

theorem first_transfer_poisson_dual_joint_hasFiniteSupport (χ : PrimitiveResidueCharacter)
    (r : Ideal O) (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    Function.HasFiniteSupport (fun p : Ideal O × O =>
      if p.1 ∣ outsideRadical ∅ r then
        firstTransferPoissonDivisorCoefficient χ p.1 * firstTransferPoissonDualTerm χ Φ H p.1 p.2
      else 0) := by
  have hfinite := (first_transfer_divisors_finite
    (first_transfer_poisson_outsideRadical_ne_bot ∅ r)).biUnion (fun d _ =>
      (finite_normElement_le (Φ.fourierCap * normIdeal d * normIdeal χ.modulus / H)).image
        (fun h => (d, h)))
  apply hfinite.subset
  rintro ⟨d, h⟩ hp
  have hd : d ∣ outsideRadical ∅ r := by
    by_contra hnot
    exact hp (if_neg hnot)
  have hd0 : d ≠ ⊥ := ne_zero_of_dvd_ne_zero
    (first_transfer_poisson_outsideRadical_ne_bot ∅ r) hd
  have hdual : firstTransferPoissonDualTerm χ Φ H d h ≠ 0 := by
    intro hz
    exact hp (by simp only [if_pos hd, hz, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨d, hd, ⟨h,
    first_transfer_poisson_dual_support χ Φ hH hd0 hdual, rfl⟩⟩

theorem first_transfer_poisson_dual_joint_summable (χ : PrimitiveResidueCharacter)
    (r : Ideal O) (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    Summable (fun p : Ideal O × O =>
      if p.1 ∣ outsideRadical ∅ r then
        firstTransferPoissonDivisorCoefficient χ p.1 * firstTransferPoissonDualTerm χ Φ H p.1 p.2
      else 0) :=
  summable_of_hasFiniteSupport (first_transfer_poisson_dual_joint_hasFiniteSupport χ r Φ hH)

theorem first_transfer_poisson_truncation (hp : PoissonStatement)
    (χ : PrimitiveResidueCharacter) (r : Ideal O) (Φ : RowWeight)
    {H : ℝ} (hr : r ≠ ⊥) (hH : 0 < H) :
    (∑' k : O, if IsRelPrime (principal k) r then
      χ.value k * (Φ.value (normElement k / H) : ℂ) else 0) =
      poissonZeroTerm χ r (fun x => (Φ.value x : ℂ)) H +
        H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
          ∑ d ∈ firstTransferPoissonDivisors r,
            firstTransferPoissonDivisorCoefficient χ d *
              ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d,
                firstTransferPoissonDualTerm χ Φ H d h := by
  rw [hp χ r (fun x => (Φ.value x : ℂ)) H hr hH Φ.schwartz]
  change H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
      (∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
        firstTransferPoissonDivisorCoefficient χ d * ∑' h : O, firstTransferPoissonDualTerm χ Φ H d h
        else 0) = _
  rw [first_transfer_poisson_divisor_tsum_eq_sum]
  have hsplit : (∑ d ∈ firstTransferPoissonDivisors r,
      firstTransferPoissonDivisorCoefficient χ d * ∑' h : O, firstTransferPoissonDualTerm χ Φ H d h) =
      (∑ d ∈ firstTransferPoissonDivisors r, firstTransferPoissonDivisorCoefficient χ d *
        (star (χ.value 0) * radialFourier (fun x => (Φ.value x : ℂ)) 0)) +
      ∑ d ∈ firstTransferPoissonDivisors r, firstTransferPoissonDivisorCoefficient χ d *
        ∑ h ∈ firstTransferPoissonFrequencies χ Φ H d, firstTransferPoissonDualTerm χ Φ H d h := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [first_transfer_poisson_dual_split χ Φ hH (ne_zero_of_dvd_ne_zero
      (first_transfer_poisson_outsideRadical_ne_bot ∅ r) (mem_firstTransferPoissonDivisors.mp hd)), mul_add]
  rw [hsplit, mul_add]
  congr 1
  unfold poissonZeroTerm
  rw [first_transfer_poisson_divisor_tsum_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  unfold firstTransferPoissonDivisorCoefficient
  ring

end QRHShort
