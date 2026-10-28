import QRHShort.QuadraticSieveSupport
import QRHShort.QuadraticSieveDuality
import Mathlib.NumberTheory.MulChar.Lemmas

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort
namespace QuadraticTransfer

theorem norm_onIdeal_le_one (χ : HeckeCharacter) (n : Ideal O) :
    ‖χ.onIdeal n‖ ≤ 1 := by
  by_cases hn : n = ⊥
  · simp only [HeckeCharacter.onIdeal, if_pos hn, norm_zero, zero_le_one]
  · simp only [HeckeCharacter.onIdeal, if_neg hn]
    letI : Finite (O ⧸ χ.modulus) :=
      Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
    letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
    by_cases ha : IsUnit (Ideal.Quotient.mk χ.modulus (idealGenerator n))
    · obtain ⟨u, hu⟩ := ha
      have hnorm := Complex.norm_eq_one_of_mem_rootsOfUnity
        (χ.residue.apply_mem_rootsOfUnity u)
      have hnorm' : ‖χ.residue (u : O ⧸ χ.modulus)‖ = 1 := by
        simpa only [MulChar.coe_equivToUnitHom] using hnorm
      simpa only [HeckeCharacter.onElement, hu] using hnorm'.le
    · simp only [HeckeCharacter.onElement, χ.residue.map_nonunit ha,
        norm_zero, zero_le_one]

def extendedIndices (X : ℝ) : Finset (Ideal O) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := O) ⌈X⌉₊).subset
    (show {n : Ideal O | normIdeal n ≤ X} ⊆ {n | n.absNorm ≤ ⌈X⌉₊} from
      fun n hn => Nat.cast_le.mp (hn.trans (Nat.le_ceil X)))).toFinset.filter
    (fun n => n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3))

@[simp] theorem mem_extendedIndices (X : ℝ) (n : Ideal O) :
    n ∈ extendedIndices X ↔ n ≠ ⊥ ∧ Squarefree n ∧
      IsRelPrime n (principal 3) ∧ normIdeal n ≤ X := by
  simp only [extendedIndices, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  tauto

def badFactors : Finset (Ideal O) := quadratic_twoPrime_finite_badFactors.toFinset

theorem extendedIndices_subset (hi : QuadraticRayClassInvariantStatement) (N : ℝ) :
    extendedIndices N ⊆ (badFactors ×ˢ quadraticSieveIndices (concreteQuadraticFamily hi) N).image
      (fun p => p.1 * p.2) := by
  intro n hn
  obtain ⟨hn0, hsq, h3, hN⟩ := (mem_extendedIndices N n).mp hn
  obtain ⟨d, m, hd, hd0, hm, hsd, hsm, hdm⟩ :=
    quadratic_twoPrime_factorization n hn0 hsq h3
  have hmn : m ∣ n := hdm.symm ▸ dvd_mul_left m d
  have hnorm : normIdeal m ≤ normIdeal n := by
    change (m.absNorm : ℝ) ≤ (n.absNorm : ℝ)
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn0))
      (map_dvd Ideal.absNorm hmn)
  apply Finset.mem_image.mpr
  refine ⟨(d, m), Finset.mem_product.mpr ⟨?_, ?_⟩, hdm.symm⟩
  · exact (quadratic_twoPrime_finite_badFactors.mem_toFinset).mpr hd
  · exact (mem_quadraticSieveIndices _ _ _).mpr ⟨hm, hsm, hnorm.trans hN⟩

/-- First extend the output index of the primal sieve. This avoids regrouping
the coefficients of the desired inequality. The sole loss is the fixed number
of divisors of (2). -/
theorem extended_primal (hi : QuadraticRayClassInvariantStatement)
    (M N B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x : Ideal O → ℂ,
      (∑ n ∈ quadraticSieveIndices (concreteQuadraticFamily hi) N,
        ‖∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M,
          x k * (quadraticCharacter k).onIdeal n‖ ^ 2) ≤
      B * ∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M, ‖x k‖ ^ 2)
    (x : Ideal O → ℂ) :
    (∑ n ∈ extendedIndices N,
      ‖∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M,
        x k * (quadraticCharacter k).onIdeal n‖ ^ 2) ≤
    (badFactors.card : ℝ) * B *
      ∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M, ‖x k‖ ^ 2 := by
  let f : Ideal O → ℝ := fun n =>
    ‖∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M,
      x k * (quadraticCharacter k).onIdeal n‖ ^ 2
  have hd (d : Ideal O) :
      (∑ m ∈ quadraticSieveIndices (concreteQuadraticFamily hi) N, f (d * m)) ≤
      B * ∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M, ‖x k‖ ^ 2 := by
    have h := hb (fun k => x k * (quadraticCharacter k).onIdeal d)
    have heq (m : Ideal O) : f (d * m) =
        ‖∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M,
          (x k * (quadraticCharacter k).onIdeal d) * (quadraticCharacter k).onIdeal m‖ ^ 2 := by
      simp only [f, HeckeCharacter.onIdeal_mul, mul_assoc]
    simp_rw [heq]
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) hB)
    intro k hk
    have hn : ‖x k * (quadraticCharacter k).onIdeal d‖ ≤ ‖x k‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_onIdeal_le_one _ _)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
  calc
    _ ≤ ∑ n ∈ (badFactors ×ˢ quadraticSieveIndices (concreteQuadraticFamily hi) N).image
          (fun p => p.1 * p.2), f n :=
      Finset.sum_le_sum_of_subset_of_nonneg (extendedIndices_subset hi N)
        (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ p ∈ badFactors ×ˢ quadraticSieveIndices (concreteQuadraticFamily hi) N,
        f (p.1 * p.2) :=
      Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
    _ = ∑ d ∈ badFactors,
        ∑ m ∈ quadraticSieveIndices (concreteQuadraticFamily hi) N, f (d * m) :=
      Finset.sum_product _ _ _
    _ ≤ ∑ d ∈ badFactors, B *
        ∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M, ‖x k‖ ^ 2 :=
      Finset.sum_le_sum (fun d _ => hd d)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Transpose the extended primal inequality. Both support sets are finite,
so no summability assumption or limiting interchange is needed. -/
theorem extended_dual (hi : QuadraticRayClassInvariantStatement)
    (hf : QuadraticFamilySieve (concreteQuadraticFamily hi))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N : ℝ) (β : Ideal O → ℂ), 1 ≤ M → 1 ≤ N →
      (∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M,
        ‖∑ n ∈ extendedIndices N, β n * (quadraticCharacter k).onIdeal n‖ ^ 2) ≤
      C * (M * N) ^ ε * (M + N) * ∑ n ∈ extendedIndices N, ‖β n‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := hf ε hε
  refine ⟨(badFactors.card : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro M N β hM hN
  let B := C * (M * N) ^ ε * (M + N)
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)) (by linarith)
  have hb (x : Ideal O → ℂ) :
      (∑ n ∈ quadraticSieveIndices (concreteQuadraticFamily hi) N,
        ‖∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M,
          x k * (quadraticCharacter k).onIdeal n‖ ^ 2) ≤
      B * ∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) M, ‖x k‖ ^ 2 := by
    have h := hbound N M x hN hM
    simp_rw [quadraticSieve_tsum] at h
    simpa only [B, concreteQuadraticFamily, mul_comm N M, add_comm N M] using h
  have h := quadratic_finite_transpose_bound (extendedIndices N)
    (quadraticSieveIndices (concreteQuadraticFamily hi) M)
    (fun n k => (quadraticCharacter k).onIdeal n)
    (mul_nonneg (Nat.cast_nonneg badFactors.card) hB)
    (fun x => extended_primal hi M N B hB hb x) β
  convert h using 1 <;> dsimp [B] <;> ring

end QuadraticTransfer

/-- Transfer of the unchanged external family sieve to the entire squarefree
symbol estimate, including coefficients divisible by primes above two. -/
theorem quadraticSquarefreeSieveTransfer : QuadraticSquarefreeSieveTransferStatement := by
  intro hi hf ε a b hε ha hab
  obtain ⟨C, hC, hbound⟩ := QuadraticTransfer.extended_dual hi hf ε hε
  let c : ℝ := max 1 b
  have hc : 1 ≤ c := le_max_left _ _
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  refine ⟨C * c ^ ε * c, mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hc0 _)) hc0, ?_⟩
  intro H U β hH hU hβ
  have hN : 1 ≤ c * U := le_trans hU (le_mul_of_one_le_left (by linarith) hc)
  have hs (n : Ideal O) (hn : β n ≠ 0) :
      n ∈ QuadraticTransfer.extendedIndices (c * U) := by
    have hn' := hβ hn
    exact (QuadraticTransfer.mem_extendedIndices _ _).mpr
      ⟨hn'.1, hn'.2.1, hn'.2.2.1,
        hn'.2.2.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) (by linarith))⟩
  have hinner (k : Ideal O) (hk : FamilyIdeal (principal 6) k) (hsk : Squarefree k) :
      (∑ n ∈ QuadraticTransfer.extendedIndices (c * U),
        β n * (quadraticCharacter k).onIdeal n) =
      ∑' n : Ideal O, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ) := by
    calc
      _ = ∑ n ∈ QuadraticTransfer.extendedIndices (c * U),
          β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := (QuadraticTransfer.mem_extendedIndices _ _).mp hn
        rw [quadraticCharacter_onIdeal k hk hsk n hn'.1 hn'.2.2.1]
      _ = _ := by
        symm
        apply tsum_eq_sum
        intro n hn
        have hz : β n = 0 := by
          by_contra hne
          exact hn (hs n hne)
        rw [hz, zero_mul]
  have henergy :
      (∑ n ∈ QuadraticTransfer.extendedIndices (c * U), ‖β n‖ ^ 2) =
      ∑' n : Ideal O, ‖β n‖ ^ 2 := by
    symm
    apply tsum_eq_sum
    intro n hn
    have hz : β n = 0 := by
      by_contra hne
      exact hn (hs n hne)
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have h := hbound H (c * U) β hH hN
  rw [henergy] at h
  have hrows :
      (∑' k : Ideal O, if Squarefree k ∧ IsRelPrime k (principal 6) ∧
          normIdeal k ≤ H then
        ‖∑' n : Ideal O, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2
        else 0) =
      ∑ k ∈ quadraticSieveIndices (concreteQuadraticFamily hi) H,
        ‖∑ n ∈ QuadraticTransfer.extendedIndices (c * U),
          β n * (quadraticCharacter k).onIdeal n‖ ^ 2 := by
    rw [← quadraticSieve_tsum]
    apply tsum_congr
    intro k
    by_cases hk0 : k = ⊥
    · simp [hk0, concreteQuadraticFamily, FamilyIdeal, sexticSymbol]
    · by_cases hk : Squarefree k ∧ IsRelPrime k (principal 6) ∧ normIdeal k ≤ H
      · rw [if_pos hk, if_pos ⟨⟨hk0, hk.2.1⟩, hk.1, hk.2.2⟩,
          hinner k ⟨hk0, hk.2.1⟩ hk.1]
      · rw [if_neg hk, if_neg (fun h => hk ⟨h.2.1, h.1.2, h.2.2⟩)]
  rw [hrows]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (tsum_nonneg (fun _ => sq_nonneg _)))
  have hscale : H + c * U ≤ c * (H + U) := by
    calc
      H + c * U ≤ c * H + c * U :=
        add_le_add (le_mul_of_one_le_left (zero_le_one.trans hH) hc) le_rfl
      _ = c * (H + U) := by ring
  calc
    C * (H * (c * U)) ^ ε * (H + c * U) ≤
        C * (H * (c * U)) ^ ε * (c * (H + U)) :=
      mul_le_mul_of_nonneg_left hscale
        (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    _ = (C * c ^ ε * c) * (H * U) ^ ε * (H + U) := by
      rw [show H * (c * U) = c * (H * U) by ring,
        Real.mul_rpow hc0 (by positivity)]
      ring

end QRHShort

#print axioms QRHShort.QuadraticTransfer.extended_dual
#print axioms QRHShort.quadraticSquarefreeSieveTransfer
