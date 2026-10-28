import QRHShort.SecondTransferPRMRFactorization

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

def secondTransferPRMRColorFactor (f : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) : Ideal O :=
  ∏ p ∈ (Finset.univ.filter fun p : (primeFactors f) => v p = i), (p : Ideal O)

theorem second_transfer_prmr_colorFactor_normalizedFactors (f : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) :
    normalizedFactors (secondTransferPRMRColorFactor f v i) =
      ((Finset.univ.filter fun p : (primeFactors f) => v p = i).val.map
        (fun p : (primeFactors f) => (p : Ideal O))) := by
  unfold secondTransferPRMRColorFactor
  rw [Finset.prod_eq_multiset_prod]
  apply normalizedFactors_prod_of_prime
  intro p hp
  obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
  exact prime_of_normalized_factor q.1 (Multiset.mem_toFinset.mp q.2)

theorem second_transfer_prmr_colorFactor_ne_zero (f : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) :
    secondTransferPRMRColorFactor f v i ≠ ⊥ := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact (prime_of_normalized_factor p.1 (Multiset.mem_toFinset.mp p.2)).ne_zero

theorem second_transfer_prmr_colorFactor_squarefree (f : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) :
    Squarefree (secondTransferPRMRColorFactor f v i) := by
  apply (squarefree_iff_nodup_normalizedFactors
    (second_transfer_prmr_colorFactor_ne_zero f v i)).mpr
  rw [second_transfer_prmr_colorFactor_normalizedFactors]
  exact Multiset.Nodup.map Subtype.val_injective (Finset.nodup _)

theorem second_transfer_prmr_colorFactor_mobius (f : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) :
    mobius (secondTransferPRMRColorFactor f v i) =
      (-1 : ℤ) ^ (Finset.univ.filter fun p : (primeFactors f) => v p = i).card := by
  rw [mobius, (second_transfer_prmr_colorFactor_squarefree f v i).moebius_eq,
    factors_eq_normalizedFactors, second_transfer_prmr_colorFactor_normalizedFactors,
    Multiset.card_map]
  rfl

theorem second_transfer_prmr_colorFactor_prime_dvd (f : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) (p : (primeFactors f)) :
    (p : Ideal O) ∣ secondTransferPRMRColorFactor f v i ↔ v p = i := by
  have hp := prime_of_normalized_factor p.1 (Multiset.mem_toFinset.mp p.2)
  have heq : (p : Ideal O) ∈ normalizedFactors (secondTransferPRMRColorFactor f v i) ↔
      v p = i := by
    rw [second_transfer_prmr_colorFactor_normalizedFactors]
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, heq⟩
      have : q = p := Subtype.ext heq
      simpa only [this] using hq
    · intro h
      exact ⟨p, h, rfl⟩
  exact ⟨fun h => heq.mp ((mem_normalizedFactors_iff
    (second_transfer_prmr_colorFactor_ne_zero f v i)).mpr ⟨hp, h⟩),
    fun h => ((mem_normalizedFactors_iff
      (second_transfer_prmr_colorFactor_ne_zero f v i)).mp (heq.mpr h)).2⟩

theorem second_transfer_prmr_colorFactor_injective (f : Ideal O) :
    Function.Injective (secondTransferPRMRColorFactor f) := by
  intro v w h
  funext p
  have hp : (p : Ideal O) ∣ secondTransferPRMRColorFactor f v (v p) :=
    (second_transfer_prmr_colorFactor_prime_dvd f v (v p) p).mpr rfl
  rw [congrFun h (v p)] at hp
  exact ((second_transfer_prmr_colorFactor_prime_dvd f w (v p) p).mp hp).symm

end QRHShort
