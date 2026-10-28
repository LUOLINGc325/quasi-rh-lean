import QRHShort.IdealMobiusProduct
import QRHShort.ActualEulerFactors

/-!
Restoring a finite exceptional set in the actual Möbius ideal series. A single
prime is removed by separating ideals divisible by that prime; the finite-set
identity then follows by induction. All sums are used only for Re s > 1.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

private def outsideMobiusTerm (χ : HeckeCharacter) (S : Finset (Ideal O))
    (s : ℂ) (n : Ideal O) : ℂ :=
  if Outside S n then fullMobiusSeriesTerm χ s n else 0

private def outsideMobiusSum (χ : HeckeCharacter) (S : Finset (Ideal O)) (s : ℂ) : ℂ :=
  ∑' n : Ideal O, outsideMobiusTerm χ S s n

private theorem outsideMobiusTerm_summable (χ : HeckeCharacter) (S : Finset (Ideal O))
    (s : ℂ) (hs : 1 < s.re) : Summable (outsideMobiusTerm χ S s) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) (fullMobiusSeriesTerm_norm_summable χ s hs)
  by_cases h : Outside S n
  · simp only [outsideMobiusTerm, if_pos h, le_refl]
  · simp only [outsideMobiusTerm, if_neg h, norm_zero, norm_nonneg]

private theorem outside_insert_iff (S : Finset (Ideal O)) (P n : Ideal O) :
    Outside (insert P S) n ↔ Outside S n ∧ ¬ P ∣ n := by
  constructor
  · intro h
    exact ⟨⟨h.1, fun Q hQ => h.2 Q (Finset.mem_insert_of_mem hQ)⟩,
      h.2 P (Finset.mem_insert_self P S)⟩
  · rintro ⟨h, hP⟩
    refine ⟨h.1, ?_⟩
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact hP
    · exact h.2 Q hQ

private theorem outside_mul_prime_iff (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Prime P) (hPS : P ∉ S) (hS : ∀ Q ∈ S, Prime Q) (a : Ideal O) :
    Outside S (P * a) ↔ Outside S a := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ha
      exact h.1 (by rw [ha, Ideal.mul_bot])
    · intro Q hQ hQa
      exact h.2 Q hQ (dvd_mul_of_dvd_right hQa P)
  · intro h
    refine ⟨mul_ne_zero hP.ne_zero h.1, ?_⟩
    intro Q hQ hQPa
    rcases (hS Q hQ).dvd_mul.mp hQPa with hQP | hQa
    · have heq : Q = P := associated_iff_eq.mp ((hS Q hQ).associated_of_dvd hP hQP)
      exact hPS (heq ▸ hQ)
    · exact h.2 Q hQ hQa

private theorem outsideMobiusTerm_prime_mul (χ : HeckeCharacter)
    (S : Finset (Ideal O)) (s : ℂ) {P : Ideal O} (hP : Prime P)
    (hPS : P ∉ S) (hS : ∀ Q ∈ S, Prime Q) (a : Ideal O) :
    outsideMobiusTerm χ S s (P * a) =
      -(heckeSeriesTerm χ s P * outsideMobiusTerm χ (insert P S) s a) := by
  by_cases ha : Outside S a
  · have hPa : Outside S (P * a) := (outside_mul_prime_iff S hP hPS hS a).mpr ha
    by_cases hdiv : P ∣ a
    · have hsq : ¬ Squarefree (P * a) := by
        intro h
        apply hP.not_isUnit
        exact h P (mul_dvd_mul (dvd_refl P) hdiv)
      have hmu : mobius (P * a) = 0 :=
        UniqueFactorizationMonoid.moebius_of_not_squarefree hsq
      have hnot : ¬ Outside (insert P S) a := fun h =>
        ((outside_insert_iff S P a).mp h).2 hdiv
      simp only [outsideMobiusTerm, if_pos hPa, if_neg hnot, fullMobiusSeriesTerm,
        hmu, Int.cast_zero, zero_mul, mul_zero, neg_zero]
    · have hins : Outside (insert P S) a := (outside_insert_iff S P a).mpr ⟨ha, hdiv⟩
      have hmu : mobius (P * a) = -mobius a := by
        unfold mobius
        rw [(hP.irreducible.isRelPrime_iff_not_dvd.mpr hdiv).moebius_mul,
          hP.irreducible.moebius_eq, neg_one_mul]
      rw [outsideMobiusTerm, if_pos hPa, outsideMobiusTerm, if_pos hins,
        fullMobiusSeriesTerm, hmu, Int.cast_neg, heckeSeriesTerm_mul,
        fullMobiusSeriesTerm]
      ring
  · have hPa : ¬ Outside S (P * a) := fun h =>
      ha ((outside_mul_prime_iff S hP hPS hS a).mp h)
    have hins : ¬ Outside (insert P S) a := fun h =>
      ha ((outside_insert_iff S P a).mp h).1
    simp only [outsideMobiusTerm, if_neg hPa, if_neg hins, mul_zero, neg_zero]

private theorem outsideMobiusSum_insert (χ : HeckeCharacter) (S : Finset (Ideal O))
    (s : ℂ) (hs : 1 < s.re) {P : Ideal O} (hP : Prime P) (hPS : P ∉ S)
    (hS : ∀ Q ∈ S, Prime Q) :
    outsideMobiusSum χ S s =
      (1 - heckeSeriesTerm χ s P) * outsideMobiusSum χ (insert P S) s := by
  let F := outsideMobiusTerm χ S s
  let G := outsideMobiusTerm χ (insert P S) s
  let D := fun n => F n - G n
  have hsupp : Function.support D ⊆ Set.range (fun a : Ideal O => P * a) := by
    intro n hn
    by_contra hnr
    have hndiv : ¬ P ∣ n := by
      rintro ⟨a, ha⟩
      exact hnr ⟨a, ha.symm⟩
    have hout : Outside (insert P S) n ↔ Outside S n := by
      rw [outside_insert_iff]
      exact and_iff_left hndiv
    have hz : D n = 0 := by
      simp only [D, F, G, outsideMobiusTerm, hout, sub_self]
    exact hn hz
  have hDmul (a : Ideal O) : D (P * a) = -(heckeSeriesTerm χ s P) * G a := by
    have hnot : ¬ Outside (insert P S) (P * a) := fun h =>
      ((outside_insert_iff S P (P * a)).mp h).2 (dvd_mul_right P a)
    change outsideMobiusTerm χ S s (P * a) -
      outsideMobiusTerm χ (insert P S) s (P * a) = _
    rw [outsideMobiusTerm_prime_mul χ S s hP hPS hS a]
    simp only [outsideMobiusTerm, if_neg hnot, sub_zero, neg_mul] <;> rfl
  have hreindex : (∑' a : Ideal O, D (P * a)) = ∑' n : Ideal O, D n :=
    (mul_right_injective₀ hP.ne_zero).tsum_eq hsupp
  have hsum : outsideMobiusSum χ S s - outsideMobiusSum χ (insert P S) s =
      -(heckeSeriesTerm χ s P) * outsideMobiusSum χ (insert P S) s := by
    calc
      outsideMobiusSum χ S s - outsideMobiusSum χ (insert P S) s =
          ∑' n : Ideal O, D n :=
        ((outsideMobiusTerm_summable χ S s hs).tsum_sub
          (outsideMobiusTerm_summable χ (insert P S) s hs)).symm
      _ = ∑' a : Ideal O, D (P * a) := hreindex.symm
      _ = ∑' a : Ideal O, -(heckeSeriesTerm χ s P) * G a :=
        tsum_congr hDmul
      _ = -(heckeSeriesTerm χ s P) * outsideMobiusSum χ (insert P S) s :=
        tsum_mul_left
  linear_combination hsum

private theorem fullMobiusSeries_eq_finiteFactors (χ : HeckeCharacter) (s : ℂ)
    (hs : 1 < s.re) (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    fullMobiusSeries χ s =
      (∏ P ∈ S, (1 - heckeSeriesTerm χ s P)) * outsideMobiusSum χ S s := by
  revert hS
  induction S using Finset.induction_on with
  | empty =>
      intro _
      rw [Finset.prod_empty, one_mul]
      apply tsum_congr
      intro n
      by_cases hn : n = ⊥
      · simp only [hn, outsideMobiusTerm, Outside, ne_eq, not_true_eq_false,
          false_and, if_false, fullMobiusSeriesTerm, heckeSeriesTerm_bot, mul_zero]
      · have hout : Outside ∅ n := ⟨hn, by simp⟩
        simp only [outsideMobiusTerm, if_pos hout]
  | @insert P S hPS ih =>
      intro hS
      have hP := hS P (Finset.mem_insert_self P S)
      have hrest : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
      rw [Finset.prod_insert hPS, ih hrest,
        outsideMobiusSum_insert χ S s hs hP hPS hrest]
      ring

/-- The omitted finite Euler factors recover the full Möbius ideal series. -/
theorem fullMobiusSeries_eq_omitted_mul (c : ArithmeticContext) (s : ℂ)
    (hs : 1 < s.re) :
    fullMobiusSeries c.nu s = omittedEulerProduct c s * mobiusSeries c s := by
  have h := fullMobiusSeries_eq_finiteFactors c.nu s hs c.S c.prime_S
  have hfactors : (∏ P ∈ c.S, (1 - heckeSeriesTerm c.nu s P)) =
      omittedEulerProduct c s := by
    unfold omittedEulerProduct
    apply Finset.prod_congr rfl
    intro P hP
    rw [heckeSeriesTerm, if_neg (by simpa using (c.prime_S P hP).ne_zero),
      Complex.cpow_neg, div_eq_mul_inv]
  have hterm : outsideMobiusTerm c.nu c.S s = mobiusSeriesTerm c s := by
    funext n
    by_cases hn : Outside c.S n
    · rw [outsideMobiusTerm, if_pos hn, mobiusSeriesTerm, if_pos hn,
        fullMobiusSeriesTerm, heckeSeriesTerm, if_neg hn.1,
        Complex.cpow_neg, div_eq_mul_inv, mul_assoc]
    · simp only [outsideMobiusTerm, mobiusSeriesTerm, if_neg hn]
  rw [hfactors] at h
  simpa only [outsideMobiusSum, hterm, mobiusSeries] using h

/-- The actual finite-S Euler–Möbius identity, proved in its absolute convergence domain. -/
theorem heckeL_mul_mobiusSeries_mul_omittedEulerProduct (c : ArithmeticContext)
    (s : ℂ) (hs : 1 < s.re) :
    HeckeL c.nu s * mobiusSeries c s * omittedEulerProduct c s = 1 := by
  have h := heckeL_mul_fullMobiusSeries c.nu s hs
  rw [fullMobiusSeries_eq_omitted_mul c s hs] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end QRHShort
