import QRHShort.SecondTransferPRMMChild

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem second_transfer_prmm_norm_one_le {r : Ideal O} (hr : r ≠ ⊥) :
    1 ≤ normIdeal r := by
  change (1 : ℝ) ≤ (r.absNorm : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
    (fun h => hr (Ideal.absNorm_eq_zero_iff.mp h)))

theorem second_transfer_prmm_divisor_ne_bot {r d : Ideal O} (hr : r ≠ ⊥)
    (hd : d ∣ r) : d ≠ ⊥ := by
  intro h
  exact hr (bot_unique (h ▸ Ideal.dvd_iff_le.mp hd))

theorem second_transfer_prmm_divisor_norm_le {r d : Ideal O} (hr : r ≠ ⊥)
    (hd : d ∣ r) : normIdeal d ≤ normIdeal r := by
  have hp : 0 < r.absNorm := Nat.pos_of_ne_zero
    (fun h => hr (Ideal.absNorm_eq_zero_iff.mp h))
  have h := Nat.le_of_dvd hp
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd))
  change (d.absNorm : ℝ) ≤ (r.absNorm : ℝ)
  exact_mod_cast h

theorem second_transfer_prmm_divisors_finite {r : Ideal O} (hr : r ≠ ⊥) :
    {d : Ideal O | d ∣ r}.Finite := by
  exact (finite_normIdeal_le (normIdeal r)).subset
    (fun d hd => second_transfer_prmm_divisor_norm_le hr hd)

def secondTransferPRMMDivisors (r : Ideal O) (hr : r ≠ ⊥) : Finset (Ideal O) :=
  (second_transfer_prmm_divisors_finite hr).toFinset

@[simp] theorem mem_secondTransferPRMMDivisors (r : Ideal O) (hr : r ≠ ⊥) (d : Ideal O) :
    d ∈ secondTransferPRMMDivisors r hr ↔ d ∣ r := by
  simp [secondTransferPRMMDivisors]

theorem second_transfer_prmm_divisors_card (r : Ideal O) (hr : r ≠ ⊥) :
    (secondTransferPRMMDivisors r hr).card = divisorCount r := by
  exact (Nat.subtype_card (secondTransferPRMMDivisors r hr)
    (mem_secondTransferPRMMDivisors r hr)).symm

theorem second_transfer_prmm_outsideRadical_eq (c : ArithmeticContext) {r : Ideal O}
    (hr : SquarefreeOutside c.S r) : outsideRadical c.S r = r := by
  have hf : (primeFactors r).filter (fun P => P ∉ c.S) = primeFactors r := by
    apply Finset.filter_eq_self.mpr
    intro P hP hPS
    exact hr.1.2 P hPS (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))
  unfold outsideRadical
  rw [hf]
  change ((normalizedFactors r).dedup.map (fun P => P)).prod = r
  rw [Multiset.map_id', Multiset.dedup_eq_self.mpr
    ((squarefree_iff_nodup_normalizedFactors hr.1.1).mp hr.2)]
  exact Ideal.prod_normalizedFactors_eq_self hr.1.1

/-- Exclusion removal on the complete column, with every divisor's child
scale verified and the normalized supremum genuinely bounded. -/
theorem second_transfer_prmm_excludedEnergy_bound (he : RemoveExclusionsStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (I : SupportInterval) (m : ℕ)
    (ξ : RayCharacter c) (V : ℝ → ℂ) (hV : SmoothSupported (enlarged I) V)
    {H L F Sigma R F' : ℝ} {r : Ideal O} (hr : SquarefreeOutside c.S r)
    (hH : 0 < H) (hL : 0 < L) (hF : 1 ≤ F) (hSigma : 0 < Sigma)
    (hHS : H ≤ Sigma) (hR : 1 ≤ R) (hRr : R ≤ normIdeal r) (hF' : 1 ≤ F')
    (hactive : F' ≤ H * L / (Sigma * F * normIdeal r ^ 2)) :
    excludedEnergy c ξ V r (H * L / (Sigma * F * R ^ 2)) (L / (R * F')) F' ≤
      (divisorCount r : ℝ) ^ 2 * childSup c I m H L F Sigma *
        (L / R) * weightNorm m V ^ 2 := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hF'0 : 0 < F' := zero_lt_one.trans_le hF'
  have hheight : 0 < H * L / (Sigma * F * R ^ 2) := by positivity
  have hcolumn : 0 < L / (R * F') := by positivity
  have hremove := he c hc (enlarged I) ξ V r
    (H * L / (Sigma * F * R ^ 2)) (L / (R * F')) F' hr.1.1 hV hheight hcolumn hF'
  rw [second_transfer_prmm_outsideRadical_eq c hr] at hremove
  let S := secondTransferPRMMDivisors r hr.1.1
  have heq : (∑' d : Ideal O, if d ∣ r then
      energy c ξ V (H * L / (Sigma * F * R ^ 2))
        (L / (R * F') / normIdeal d) (F' * normIdeal d) else 0) =
      ∑ d ∈ S, energy c ξ V (H * L / (Sigma * F * R ^ 2))
        (L / (R * F') / normIdeal d) (F' * normIdeal d) := by
    rw [tsum_eq_sum (s := S) (fun d hd => if_neg
      (fun h => hd ((mem_secondTransferPRMMDivisors r hr.1.1 d).mpr h)))]
    apply Finset.sum_congr rfl
    intro d hd
    exact if_pos ((mem_secondTransferPRMMDivisors r hr.1.1 d).mp hd)
  rw [heq] at hremove
  let B := childSup c I m H L F Sigma * (L / R) * weightNorm m V ^ 2
  have hsum : (∑ d ∈ S, energy c ξ V (H * L / (Sigma * F * R ^ 2))
      (L / (R * F') / normIdeal d) (F' * normIdeal d)) ≤ (divisorCount r : ℝ) * B := by
    calc
      _ ≤ ∑ _d ∈ S, B := by
        apply Finset.sum_le_sum
        intro d hd
        have hdv := (mem_secondTransferPRMMDivisors r hr.1.1 d).mp hd
        have hd0 := second_transfer_prmm_divisor_ne_bot hr.1.1 hdv
        have hj := second_transfer_prmm_norm_one_le hd0
        have hjr := second_transfer_prmm_divisor_norm_le hr.1.1 hdv
        obtain ⟨h1,h2,h3,h4,h5,h6⟩ := second_transfer_child_scales
          hH hL hF hSigma hHS hR hRr hF' hj hjr hactive
        have hb := second_transfer_energy_le_childSup c I m H L F Sigma _ _ _ ξ V hV
          h1 h2 h3 h4 h5 h6
        have hp : (L / (R * F') / normIdeal d) * (F' * normIdeal d) = L / R := by
          field_simp [hR0.ne', hF'0.ne', (normIdeal_pos hd0).ne']
        simpa only [hp] using hb
      _ = _ := by simp [S, second_transfer_prmm_divisors_card]
  calc
    _ ≤ (divisorCount r : ℝ) * ((divisorCount r : ℝ) * B) :=
      hremove.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    _ = _ := by dsimp [B]; ring

end QRHShort
