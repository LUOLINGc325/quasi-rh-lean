import QRHShort.IdealCounting
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import QRHShort.AnalyticObjects
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
Reciprocal ideal-norm sums from the actual linear ideal-counting bound.
The divisor weight is the existing `divisorCount`, including every ideal divisor.
The restriction `R ≥ 1` keeps `log (2 * R)` positive and uniform at the unit ideal.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.SecondTransferPRMPHarmonic

def idealDivisors (n : Ideal O) (hn : n ≠ ⊥) : Finset (Ideal O) := by
  letI : Fintype {d : Ideal O // d ∣ n} := UniqueFactorizationMonoid.fintypeSubtypeDvd n hn
  exact (Finset.univ : Finset {d : Ideal O // d ∣ n}).image Subtype.val

@[simp] theorem mem_idealDivisors (n : Ideal O) (hn : n ≠ ⊥) (d : Ideal O) :
    d ∈ idealDivisors n hn ↔ d ∣ n := by
  simp [idealDivisors]

private theorem normIdeal_one_le {b : Ideal O} (hb : b ≠ ⊥) :
    1 ≤ normIdeal b := by
  have h : 1 ≤ b.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h => hb (Ideal.absNorm_eq_zero_iff.mp h))
  change (1 : ℝ) ≤ (b.absNorm : ℝ)
  exact_mod_cast h

private theorem sum_weighted_le_of_partial_sum_le (a b f : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i, 0 ≤ f i) (hanti : Antitone f)
    (hpartial : ∀ m ≤ n, (∑ i ∈ Finset.range m, a i) ≤
      ∑ i ∈ Finset.range m, b i) :
    (∑ i ∈ Finset.range n, f i * a i) ≤ ∑ i ∈ Finset.range n, f i * b i := by
  have ha := Finset.sum_range_by_parts f a n
  have hb := Finset.sum_range_by_parts f b n
  simp only [smul_eq_mul] at ha hb
  rw [ha, hb]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) (hf _)
  · apply Finset.sum_le_sum
    intro i hi
    have hi' : i + 1 ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    exact mul_le_mul_of_nonpos_left (hpartial (i + 1) hi')
      (sub_nonpos.mpr (hanti (Nat.le_succ i)))

private theorem ideal_harmonic_le_count_harmonic (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ X : ℝ, 0 < X →
      ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ C * X)
    (R : ℝ) (hR : 1 ≤ R) :
    (∑ b ∈ boundedDivisibleIdeals 1 R, (normIdeal b)⁻¹) ≤
      C * (harmonic ⌊R⌋₊ : ℝ) := by
  let B := boundedDivisibleIdeals 1 R
  let a : ℕ → ℝ := fun i => ((B.filter (fun b => b.absNorm - 1 = i)).card : ℝ)
  let w : ℕ → ℝ := fun i => ((i + 1 : ℕ) : ℝ)⁻¹
  have hnorm : ∀ b ∈ B, 0 < b.absNorm := by
    intro b hb
    exact Nat.pos_of_ne_zero (fun h => (mem_boundedDivisibleIdeals.mp hb).2.2
      (Ideal.absNorm_eq_zero_iff.mp h))
  have hpartial : ∀ m, (∑ i ∈ Finset.range m, a i) ≤ C * m := by
    intro m
    have hsum : (∑ i ∈ Finset.range m, a i) =
        ((B.filter (fun b => b.absNorm - 1 ∈ Finset.range m)).card : ℝ) := by
      dsimp only [a]
      exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter B
        (Finset.range m) (fun b => b.absNorm - 1)
    rw [hsum]
    by_cases hm : m = 0
    · simp [hm]
    · have hsub : B.filter (fun b => b.absNorm - 1 ∈ Finset.range m) ⊆
          boundedDivisibleIdeals 1 (m : ℝ) := by
        intro b hb
        obtain ⟨hbB, hbM⟩ := Finset.mem_filter.mp hb
        have hbPos := hnorm b hbB
        have hbLe : b.absNorm ≤ m := by
          have := Finset.mem_range.mp hbM
          omega
        refine mem_boundedDivisibleIdeals.mpr ⟨?_, one_dvd _,
          (mem_boundedDivisibleIdeals.mp hbB).2.2⟩
        change (b.absNorm : ℝ) ≤ (m : ℝ)
        exact_mod_cast hbLe
      have hcard : ((B.filter (fun b => b.absNorm - 1 ∈ Finset.range m)).card : ℝ) ≤
          ((boundedDivisibleIdeals 1 (m : ℝ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (hcount m (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)))
  have hmap : ∀ b ∈ B, b.absNorm - 1 ∈ Finset.range ⌊R⌋₊ := by
    intro b hb
    have hbPos := hnorm b hb
    have hbLe : b.absNorm ≤ ⌊R⌋₊ :=
      (Nat.le_floor_iff (zero_le_one.trans hR)).mpr
        (mem_boundedDivisibleIdeals.mp hb).1
    exact Finset.mem_range.mpr (by omega)
  have hsplit := Finset.sum_fiberwise_of_maps_to hmap
    (fun b : Ideal O => (normIdeal b)⁻¹)
  have hterm : ∀ i : ℕ,
      (∑ b ∈ B.filter (fun b => b.absNorm - 1 = i), (normIdeal b)⁻¹) = w i * a i := by
    intro i
    calc
      (∑ b ∈ B.filter (fun b => b.absNorm - 1 = i), (normIdeal b)⁻¹) =
          ∑ _b ∈ B.filter (fun b => b.absNorm - 1 = i), w i := by
        apply Finset.sum_congr rfl
        intro b hb
        obtain ⟨hbB, hbI⟩ := Finset.mem_filter.mp hb
        have hbPos := hnorm b hbB
        have heq : b.absNorm = i + 1 := by omega
        change (b.absNorm : ℝ)⁻¹ = ((i + 1 : ℕ) : ℝ)⁻¹
        rw [heq]
      _ = w i * a i := by simp [a, mul_comm]
  rw [← hsplit]
  simp_rw [hterm]
  have hmajor := sum_weighted_le_of_partial_sum_le a (fun _ => C) w ⌊R⌋₊
    (fun i => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by
      intro i j hij
      exact inv_anti₀ (Nat.cast_pos.mpr (Nat.succ_pos i))
        (Nat.cast_le.mpr (Nat.add_le_add_right hij 1)))
    (fun m _ => by simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_comm] using hpartial m)
  refine hmajor.trans_eq ?_
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Finset.mul_sum, w, mul_comm]

/-- Reciprocal norms of nonzero ideals have logarithmic partial sums. -/
theorem exists_ideal_harmonic_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      (∑ b ∈ boundedDivisibleIdeals 1 R, (normIdeal b)⁻¹) ≤ C * Real.log (2 * R) := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C * (1 + (Real.log 2)⁻¹), mul_pos hC
    (add_pos_of_pos_of_nonneg zero_lt_one (inv_nonneg.mpr hlog.le)), ?_⟩
  intro R hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hscale : 1 + Real.log R ≤ (1 + (Real.log 2)⁻¹) * Real.log (2 * R) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRpos.ne']
    have hcancel : (Real.log 2)⁻¹ * Real.log 2 = 1 := inv_mul_cancel₀ hlog.ne'
    have hnonneg : 0 ≤ (Real.log 2)⁻¹ * Real.log R :=
      mul_nonneg (inv_nonneg.mpr hlog.le) hlogR
    nlinarith
  calc
    (∑ b ∈ boundedDivisibleIdeals 1 R, (normIdeal b)⁻¹) ≤
        C * (harmonic ⌊R⌋₊ : ℝ) := ideal_harmonic_le_count_harmonic C hC.le hcount R hR
    _ ≤ C * (1 + Real.log R) :=
      mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log R hR) hC.le
    _ ≤ C * ((1 + (Real.log 2)⁻¹) * Real.log (2 * R)) :=
      mul_le_mul_of_nonneg_left hscale hC.le
    _ = _ := by ring

private theorem divisorCount_eq_card (n : Ideal O) (hn : n ≠ ⊥) :
    divisorCount n = (idealDivisors n hn).card := by
  exact Nat.subtype_card (idealDivisors n hn) (mem_idealDivisors n hn)

private theorem factors_mem_norm_ball {R : ℝ} {n a b : Ideal O}
    (hn : n ∈ boundedDivisibleIdeals 1 R) (hab : a * b = n) :
    a ∈ boundedDivisibleIdeals 1 R ∧ b ∈ boundedDivisibleIdeals 1 R := by
  obtain ⟨hnR, _, hn0⟩ := mem_boundedDivisibleIdeals.mp hn
  have ha0 : a ≠ ⊥ := by
    intro h
    apply hn0
    simpa only [h, Ideal.bot_mul] using hab.symm
  have hb0 : b ≠ ⊥ := by
    intro h
    apply hn0
    simpa only [h, Ideal.mul_bot] using hab.symm
  have hprod : normIdeal a * normIdeal b = normIdeal n := by
    rw [← normIdeal_mul, hab]
  have haLe : normIdeal a ≤ normIdeal n := by
    rw [← hprod]
    exact le_mul_of_one_le_right (normIdeal_pos ha0).le (normIdeal_one_le hb0)
  have hbLe : normIdeal b ≤ normIdeal n := by
    rw [← hprod]
    exact le_mul_of_one_le_left (normIdeal_pos hb0).le (normIdeal_one_le ha0)
  exact ⟨mem_boundedDivisibleIdeals.mpr ⟨haLe.trans hnR, one_dvd _, ha0⟩,
    mem_boundedDivisibleIdeals.mpr ⟨hbLe.trans hnR, one_dvd _, hb0⟩⟩

private theorem factorPairs_card {R : ℝ} {n : Ideal O}
    (hn : n ∈ boundedDivisibleIdeals 1 R) :
    (((boundedDivisibleIdeals 1 R) ×ˢ (boundedDivisibleIdeals 1 R)).filter
      (fun ab => ab.1 * ab.2 = n)).card = divisorCount n := by
  have hn0 := (mem_boundedDivisibleIdeals.mp hn).2.2
  rw [divisorCount_eq_card n hn0]
  apply Finset.card_bij (fun ab _ => ab.1)
  · intro ab hab
    exact (mem_idealDivisors n hn0 _).mpr
      ⟨ab.2, (Finset.mem_filter.mp hab).2.symm⟩
  · intro ab hab cd hcd heq
    apply Prod.ext heq
    have ha0 := (mem_boundedDivisibleIdeals.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1).2.2
    apply mul_left_cancel₀ ha0
    calc
      ab.1 * ab.2 = n := (Finset.mem_filter.mp hab).2
      _ = cd.1 * cd.2 := (Finset.mem_filter.mp hcd).2.symm
      _ = ab.1 * cd.2 := by rw [heq]
  · intro d hd
    obtain ⟨e, hde⟩ := (mem_idealDivisors n hn0 d).mp hd
    have hmem := factors_mem_norm_ball hn hde.symm
    exact ⟨(d, e), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr hmem, hde.symm⟩, rfl⟩

private theorem ideal_divisor_harmonic_le_sq (R : ℝ) :
    (∑ n ∈ boundedDivisibleIdeals 1 R, (divisorCount n : ℝ) / normIdeal n) ≤
      (∑ n ∈ boundedDivisibleIdeals 1 R, (normIdeal n)⁻¹) ^ 2 := by
  let B := boundedDivisibleIdeals 1 R
  let w : Ideal O × Ideal O → ℝ := fun ab =>
    (normIdeal ab.1)⁻¹ * (normIdeal ab.2)⁻¹
  have hterm : ∀ n ∈ B,
      (∑ ab ∈ (B ×ˢ B).filter (fun ab => ab.1 * ab.2 = n), w ab) =
        (divisorCount n : ℝ) / normIdeal n := by
    intro n hn
    calc
      (∑ ab ∈ (B ×ˢ B).filter (fun ab => ab.1 * ab.2 = n), w ab) =
          ∑ _ab ∈ (B ×ˢ B).filter (fun ab => ab.1 * ab.2 = n), (normIdeal n)⁻¹ := by
        apply Finset.sum_congr rfl
        intro ab hab
        dsimp only [w]
        rw [← mul_inv, ← normIdeal_mul, (Finset.mem_filter.mp hab).2]
      _ = (divisorCount n : ℝ) / normIdeal n := by
        simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
        congr 1
        exact_mod_cast factorPairs_card hn
  calc
    (∑ n ∈ B, (divisorCount n : ℝ) / normIdeal n) =
        ∑ n ∈ B, ∑ ab ∈ (B ×ˢ B).filter (fun ab => ab.1 * ab.2 = n), w ab := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hterm n hn).symm
    _ = ∑ ab ∈ (B ×ˢ B).filter (fun ab => ab.1 * ab.2 ∈ B), w ab :=
      Finset.sum_fiberwise_eq_sum_filter (B ×ˢ B) B (fun ab => ab.1 * ab.2) w
    _ ≤ ∑ ab ∈ B ×ˢ B, w ab := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ab hab _
      exact mul_nonneg (inv_nonneg.mpr (normIdeal_pos
        (mem_boundedDivisibleIdeals.mp (Finset.mem_product.mp hab).1).2.2).le)
        (inv_nonneg.mpr (normIdeal_pos
          (mem_boundedDivisibleIdeals.mp (Finset.mem_product.mp hab).2).2.2).le)
    _ = (∑ n ∈ B, (normIdeal n)⁻¹) ^ 2 := by
      rw [Finset.sum_product, sq, Finset.sum_mul_sum]

/-- Divisor-weighted reciprocal norms have squared-logarithmic partial sums. -/
theorem exists_ideal_divisor_harmonic_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      (∑ b ∈ boundedDivisibleIdeals 1 R, (divisorCount b : ℝ) / normIdeal b) ≤
        C * (Real.log (2 * R)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_ideal_harmonic_constant
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro R hR
  have hsum : 0 ≤ ∑ b ∈ boundedDivisibleIdeals 1 R, (normIdeal b)⁻¹ := by
    apply Finset.sum_nonneg
    intro b hb
    exact inv_nonneg.mpr (normIdeal_pos (mem_boundedDivisibleIdeals.mp hb).2.2).le
  have hlarge := hbound R hR
  calc
    (∑ b ∈ boundedDivisibleIdeals 1 R, (divisorCount b : ℝ) / normIdeal b) ≤
        (∑ b ∈ boundedDivisibleIdeals 1 R, (normIdeal b)⁻¹) ^ 2 :=
      ideal_divisor_harmonic_le_sq R
    _ ≤ (C * Real.log (2 * R)) ^ 2 := by nlinarith
    _ = C ^ 2 * Real.log (2 * R) ^ 2 := by ring

end QRHShort.SecondTransferPRMPHarmonic
