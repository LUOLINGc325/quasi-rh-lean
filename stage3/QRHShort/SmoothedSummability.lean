import QRHShort.CanonicalAssembly
import QRHShort.RowWeightExistence
import QRHShort.IdealCounting
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
Convergence of the literal smoothed row sums. Rapid decay is read from the
radial Schwartz function at the positive real square root; ideal counting and
the finite unit group then give summability on the Eisenstein integers.
The residue-symbol bounds below are deliberately crude finite-sum bounds and
do not assume unproved reciprocity or unit-modulus identities.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

private theorem rowWeight_cubic_decay (Φ : RowWeight) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 ≤ x → x ^ (3 : ℕ) * Φ.value x ≤ A := by
  obtain ⟨f, hf⟩ := Φ.schwartz
  obtain ⟨A, hA, hdecay⟩ := f.decay 6 0
  refine ⟨A, hA, ?_⟩
  intro x hx
  let z : ℂ := (Real.sqrt x : ℂ)
  have hsq : ‖z‖ ^ (2 : ℕ) = x := by
    rw [Complex.sq_norm]
    exact (Complex.normSq_ofReal _).trans (Real.mul_self_sqrt hx)
  have hval : ‖f z‖ = Φ.value x := by
    rw [hf z, ← Complex.sq_norm, hsq, Complex.norm_real,
      Real.norm_of_nonneg (Φ.nonnegative x hx)]
  have hd := hdecay z
  rw [norm_iteratedFDeriv_zero] at hd
  calc
    x ^ (3 : ℕ) * Φ.value x = (‖z‖ ^ (2 : ℕ)) ^ (3 : ℕ) * ‖f z‖ := by rw [hsq, hval]
    _ = ‖z‖ ^ (6 : ℕ) * ‖f z‖ := by ring
    _ ≤ A := hd

private theorem rowWeight_scaled_cubic_bound (Φ : RowWeight) {A H x : ℝ}
    (hdecay : ∀ y : ℝ, 0 ≤ y → y ^ (3 : ℕ) * Φ.value y ≤ A)
    (hH : 0 < H) (hx : 0 < x) :
    Φ.value (x / H) ≤ A * H ^ (3 : ℕ) / x ^ (3 : ℕ) := by
  apply (le_div_iff₀ (pow_pos hx 3)).mpr
  calc
    Φ.value (x / H) * x ^ (3 : ℕ) =
        ((x / H) ^ (3 : ℕ) * Φ.value (x / H)) * H ^ (3 : ℕ) := by
      field_simp [hH.ne']
      <;> ring
    _ ≤ A * H ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right (hdecay (x / H) (div_pos hx hH).le) (pow_nonneg hH.le _)

private theorem ideal_norm_fiber_card_bound {C : ℝ}
    (hcount : ∀ X : ℝ, 0 < X → ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ C * X)
    {m : ℕ} (hm : 0 < m) :
    (Nat.card {a : Ideal O // a.absNorm = m} : ℝ) ≤ C * (m : ℝ) := by
  let target := boundedDivisibleIdeals 1 (m : ℝ)
  let ι : {a : Ideal O // a.absNorm = m} → {a // a ∈ target} := fun a =>
    ⟨a.1, mem_boundedDivisibleIdeals.mpr ⟨by
      change (a.1.absNorm : ℝ) ≤ (m : ℝ)
      rw [a.2],
      one_dvd _, fun ha => (Nat.ne_of_gt hm)
        (a.2.symm.trans (Ideal.absNorm_eq_zero_iff.mpr ha))⟩⟩
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (congrArg (fun x : {a // a ∈ target} => x.1) h)
  have hc := Nat.card_le_card_of_injective ι hι
  have hc' : (Nat.card {a : Ideal O // a.absNorm = m} : ℝ) ≤
      ((boundedDivisibleIdeals 1 (m : ℝ)).card : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc)
  exact hc'.trans (hcount m (by exact_mod_cast hm))

/-- A Schwartz row weight is genuinely summable over all integral ideals. -/
theorem rowWeight_ideal_summable (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    Summable (fun a : Ideal O => Φ.value (normIdeal a / H)) := by
  obtain ⟨A, hA, hdecay⟩ := rowWeight_cubic_decay Φ
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  let coefficient : ℕ → ℝ := fun m =>
    (Nat.card {a : Ideal O // a.absNorm = m} : ℝ) * Φ.value ((m : ℝ) / H)
  have hcoeff0 (m : ℕ) : 0 ≤ coefficient m :=
    mul_nonneg (Nat.cast_nonneg _) (Φ.nonnegative _ (div_nonneg (Nat.cast_nonneg _) hH.le))
  have hp : Summable (fun m : ℕ => 1 / (m : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hmajor : Summable (fun m : ℕ =>
      (C * A * H ^ (3 : ℕ)) / ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      ((summable_nat_add_iff 1).mpr hp).mul_left (C * A * H ^ (3 : ℕ))
  have hcoeff : Summable coefficient := by
    apply (summable_nat_add_iff 1).mp
    apply hmajor.of_nonneg_of_le (fun m => hcoeff0 (m + 1))
    intro m
    have hm : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    have hphi0 : 0 ≤ Φ.value (((m + 1 : ℕ) : ℝ) / H) :=
      Φ.nonnegative _ (div_pos hm hH).le
    calc
      coefficient (m + 1) ≤
          (C * ((m + 1 : ℕ) : ℝ)) * (A * H ^ (3 : ℕ) / ((m + 1 : ℕ) : ℝ) ^ (3 : ℕ)) :=
        mul_le_mul (ideal_norm_fiber_card_bound hcount (Nat.succ_pos m))
          (rowWeight_scaled_cubic_bound Φ hdecay hH hm) hphi0 (mul_nonneg hC.le hm.le)
      _ = (C * A * H ^ (3 : ℕ)) / ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
        field_simp [ne_of_gt hm]
        <;> ring
  apply (summable_partition (fun a => Φ.nonnegative _ (by
    change 0 ≤ (a.absNorm : ℝ) / H
    positivity)) (s := fun m : ℕ => {a : Ideal O | a.absNorm = m})
      (fun a => ⟨a.absNorm, rfl, fun m hm => hm.symm⟩)).mpr
  constructor
  · intro m
    letI := (Ideal.finite_setOfPred_absNorm_eq (S := O) m).fintype
    exact (hasSum_fintype _).summable
  · apply hcoeff.congr
    intro m
    letI := (Ideal.finite_setOfPred_absNorm_eq (S := O) m).fintype
    symm
    calc
      (∑' a : {a : Ideal O | a.absNorm = m}, Φ.value (normIdeal a.1 / H)) =
          ∑' _a : {a : Ideal O | a.absNorm = m}, Φ.value ((m : ℝ) / H) := by
        apply tsum_congr
        intro a
        change Φ.value ((a.1.absNorm : ℝ) / H) = Φ.value ((m : ℝ) / H)
        rw [a.2]
      _ = coefficient m := by
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          coefficient]
        have hcard : Nat.card {a : Ideal O | a.absNorm = m} =
            Nat.card {a : Ideal O // a.absNorm = m} := by
          apply Nat.card_congr
          exact
            { toFun := fun a => ⟨a.1, a.2⟩
              invFun := fun a => ⟨a.1, a.2⟩
              left_inv := by intro a; rfl
              right_inv := by intro a; rfl }
        rw [← Nat.card_eq_fintype_card, hcard]

private theorem summable_principal_pullback {g : Ideal O → ℝ}
    (hg0 : ∀ a, 0 ≤ g a) (hg : Summable g) :
    Summable (fun z : O => g (principal z)) := by
  letI : Fintype Oˣ := Set.fintypeOfFiniteUniv finite_units
  have hu (z : O) : ∃ u : Oˣ, idealGenerator (principal z) * (u : O) = z := by
    have hspan : principal (idealGenerator (principal z)) = principal z :=
      Ideal.span_singleton_generator (principal z)
    exact Ideal.span_singleton_eq_span_singleton.mp hspan
  let u (z : O) : Oˣ := Classical.choose (hu z)
  have hurepr (z : O) : idealGenerator (principal z) * (u z : O) = z :=
    Classical.choose_spec (hu z)
  let ι : O → Ideal O × Oˣ := fun z => (principal z, u z)
  have hι : Function.Injective ι := by
    intro z w h
    have hp : principal z = principal w := congrArg Prod.fst h
    have hu' : u z = u w := congrArg Prod.snd h
    calc
      z = idealGenerator (principal z) * (u z : O) := (hurepr z).symm
      _ = idealGenerator (principal w) * (u w : O) := by rw [hp, hu']
      _ = w := hurepr w
  have hprod : Summable (fun p : Ideal O × Oˣ => g p.1) := by
    apply (summable_prod_of_nonneg (fun p => hg0 p.1)).mpr
    constructor
    · intro a
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        hg.mul_left (Fintype.card Oˣ : ℝ)
  exact hprod.comp_injective hι

/-- Summability on elements follows from summability on ideals and the finite
unit group, including the zero element. -/
theorem rowWeight_element_summable (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    Summable (fun k : O => Φ.value (normElement k / H)) := by
  exact summable_principal_pullback
    (fun a => Φ.nonnegative _ (by dsimp [normIdeal]; positivity))
    (rowWeight_ideal_summable Φ hH)

private theorem sexticAtPrime_uniform_bound (P : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : O, ‖sexticAtPrime P k‖ ≤ B := by
  refine ⟨∑ j ∈ Finset.range 6, ‖embedding (rootSix ^ j)‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro k
  unfold sexticAtPrime
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (embedding (rootSix ^ j))

private theorem sexticSymbol_uniform_bound (n : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : O, ‖sexticSymbol n k‖ ≤ B := by
  have hprod (s : Multiset (Ideal O)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : O,
      ‖(s.map (fun P => sexticAtPrime P k)).prod‖ ≤ B := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, zero_le_one, by intro k; simp⟩
    | @cons P s ih =>
      obtain ⟨A, hA, hPA⟩ := sexticAtPrime_uniform_bound P
      obtain ⟨B, hB, hSB⟩ := ih
      refine ⟨A * B, mul_nonneg hA hB, ?_⟩
      intro k
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul (hPA k) (hSB k) (norm_nonneg _) hA
  by_cases hn : n = ⊥
  · exact ⟨0, le_rfl, by intro k; simp only [sexticSymbol, if_pos hn, norm_zero, le_refl]⟩
  · obtain ⟨B, hB, hbound⟩ := hprod (UniqueFactorizationMonoid.normalizedFactors n)
    exact ⟨B, hB, by intro k; simpa only [sexticSymbol, if_neg hn] using hbound k⟩

/-- Compact support makes a column uniformly bounded in its row variable. This
requires no reciprocity, Gauss-sum evaluation, or sharp residue-symbol bound. -/
theorem columnSum_uniform_bound (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) (f : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : O, ‖columnSum c ξ W X k f‖ ≤ B := by
  let b (n : Ideal O) : ℝ := Classical.choose (sexticSymbol_uniform_bound n)
  have hb0 (n : Ideal O) : 0 ≤ b n := (Classical.choose_spec (sexticSymbol_uniform_bound n)).1
  have hbk (n : Ideal O) (k : O) : ‖sexticSymbol n k‖ ≤ b n :=
    (Classical.choose_spec (sexticSymbol_uniform_bound n)).2 k
  let major (n : Ideal O) : ℝ := if SquarefreeOutside c.S n then
    ‖coefficient ξ.val n‖ * b n * ‖sexticSymbol n (primaryGenerator f)‖ ^ (4 : ℕ) *
      ‖W (normIdeal n / X)‖ else 0
  have hmajor0 (n : Ideal O) : 0 ≤ major n := by
    dsimp [major]
    split_ifs
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (norm_nonneg (coefficient ξ.val n)) (hb0 n))
          (pow_nonneg (norm_nonneg (sexticSymbol n (primaryGenerator f))) (4 : ℕ)))
        (norm_nonneg (W (normIdeal n / X)))
    · exact le_rfl
  have hfinite : Function.HasFiniteSupport major := by
    apply (finite_normIdeal_le (I.hi * X)).subset
    intro n hn
    by_contra hnot
    have hw : W (normIdeal n / X) = 0 := by
      by_contra hw
      exact hnot ((div_le_iff₀ hX).mp (hW.2 hw).2)
    exact hn (by simp only [major, hw, norm_zero, mul_zero, ite_self])
  have hs : Summable major := summable_of_hasFiniteSupport hfinite
  refine ⟨∑' n, major n, tsum_nonneg hmajor0, ?_⟩
  intro k
  unfold columnSum
  apply tsum_of_norm_bounded hs.hasSum
  intro n
  by_cases hn : SquarefreeOutside c.S n
  · simp only [if_pos hn, major, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbk n k) (norm_nonneg _))
        (pow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
  · simp only [if_neg hn, norm_zero, major, le_refl]

/-- The convergence premise needed by the sharp-to-smoothed comparison follows
from the existing Schwartz, compact support, and arithmetic definitions. -/
theorem rowWeight_smoothedRowSummability (Φ : RowWeight) : SmoothedRowSummability Φ := by
  intro c I _ ξ W H X f hW hH hX
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  obtain ⟨B, hB, hbound⟩ := columnSum_uniform_bound c ξ hW hXpos f
  have hs := (rowWeight_element_summable Φ hHpos).mul_right (B ^ (2 : ℕ))
  apply hs.of_nonneg_of_le
  · intro k
    exact mul_nonneg (Φ.nonnegative _ (by dsimp [normElement, normIdeal]; positivity)) (sq_nonneg _)
  · intro k
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbound k) 2)
      (Φ.nonnegative _ (by dsimp [normElement, normIdeal]; positivity))

/-- The only remaining smoothing input to the actual canonical assembly is the
existence of a row weight; convergence is proved above. -/
theorem canonical_estimate_of_cube_transfer_and_weight
    (hcube : CubeEstimate) (htransfer : TransferEstimate) (Φ : RowWeight) : CanonicalEstimate :=
  canonical_estimate_of_cube_transfer_and_rows hcube htransfer Φ
    (rowWeight_smoothedRowSummability Φ)

/-- The actual canonical estimate follows from the two manuscript reductions;
the row weight and the convergence of its smoothed rows are constructed above. -/
theorem canonical_estimate_of_cube_transfer
    (hcube : CubeEstimate) (htransfer : TransferEstimate) : CanonicalEstimate := by
  obtain ⟨Φ⟩ := rowWeight_nonempty
  exact canonical_estimate_of_cube_transfer_and_weight hcube htransfer Φ

end QRHShort
