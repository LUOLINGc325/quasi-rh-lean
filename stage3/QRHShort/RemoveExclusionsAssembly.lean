import QRHShort.PoissonStatements
import QRHShort.EnergySupport
import QRHShort.RemoveExclusionsNorms
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Finite-sum assembly of the removal-of-exclusions estimate (paper2.tex, Lemma
`removeexclusions`).  The arithmetic column expansion and its multiplier bound
are explicit propositions, separate from the proved energy transport below.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.RemoveExclusionsProof

theorem normIdeal_pos {d : Ideal O} (hd : d ≠ ⊥) : 0 < normIdeal d := by
  have hn : d.absNorm ≠ 0 := fun h => hd (Ideal.absNorm_eq_zero_iff.mp h)
  change 0 < (d.absNorm : ℝ)
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem normIdeal_mul (d f : Ideal O) :
    normIdeal (d * f) = normIdeal d * normIdeal f := by
  simp only [normIdeal, map_mul, Nat.cast_mul]

theorem outsideRadical_ne_bot (S : Finset (Ideal O)) (r : Ideal O) :
    outsideRadical S r ≠ ⊥ := by
  change (∏ P ∈ (primeFactors r).filter (fun P => P ∉ S), P) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero

theorem finite_radical_divisors (S : Finset (Ideal O)) (r : Ideal O) :
    {d : Ideal O | d ∣ outsideRadical S r}.Finite := by
  apply (finite_normIdeal_le (normIdeal (outsideRadical S r))).subset
  intro d hd
  have hn : (outsideRadical S r).absNorm ≠ 0 :=
    fun h => outsideRadical_ne_bot S r (Ideal.absNorm_eq_zero_iff.mp h)
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (map_dvd Ideal.absNorm hd)
  change (d.absNorm : ℝ) ≤ ((outsideRadical S r).absNorm : ℝ)
  exact_mod_cast hle

def radicalDivisors (S : Finset (Ideal O)) (r : Ideal O) : Finset (Ideal O) :=
  (finite_radical_divisors S r).toFinset

@[simp] theorem mem_radicalDivisors (S : Finset (Ideal O)) (r d : Ideal O) :
    d ∈ radicalDivisors S r ↔ d ∣ outsideRadical S r := by
  simp [radicalDivisors]

theorem radicalDivisors_card (S : Finset (Ideal O)) (r : Ideal O) :
    (radicalDivisors S r).card = divisorCount (outsideRadical S r) := by
  letI := Fintype.subtype (radicalDivisors S r) (mem_radicalDivisors S r)
  rw [divisorCount, Nat.card_eq_fintype_card,
    Fintype.card_of_subtype (radicalDivisors S r) (mem_radicalDivisors S r)]

theorem radicalDivisor_ne_bot {S : Finset (Ideal O)} {r d : Ideal O}
    (hd : d ∈ radicalDivisors S r) : d ≠ ⊥ :=
  ne_zero_of_dvd_ne_zero (outsideRadical_ne_bot S r) (mem_radicalDivisors S r d |>.mp hd)

theorem outsideRadical_squarefreeOutside (c : ArithmeticContext) (r : Ideal O) :
    SquarefreeOutside c.S (outsideRadical c.S r) := by
  let s := (primeFactors r).filter (fun P => P ∉ c.S)
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)
  refine ⟨⟨outsideRadical_ne_bot c.S r, ?_⟩, ?_⟩
  · intro P hP hdiv
    change P ∣ ∏ Q ∈ s, Q at hdiv
    obtain ⟨Q, hQ, hPQ⟩ := (c.prime_S P hP).exists_mem_finset_dvd hdiv
    have heq : P = Q := (prime_dvd_prime_iff_eq (c.prime_S P hP) (hprime Q hQ)).mp hPQ
    exact (Finset.mem_filter.mp hQ).2 (heq ▸ hP)
  · change Squarefree (∏ P ∈ s, P)
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro P hP Q hQ hne
      apply (hprime P hP).irreducible.isRelPrime_iff_not_dvd.mpr
      exact fun hd => hne ((prime_dvd_prime_iff_eq (hprime P hP) (hprime Q hQ)).mp hd)
    · exact fun P hP => (hprime P hP).squarefree

theorem radicalDivisor_squarefreeOutside (c : ArithmeticContext) {r d : Ideal O}
    (hd : d ∈ radicalDivisors c.S r) : SquarefreeOutside c.S d := by
  have hrad := outsideRadical_squarefreeOutside c r
  have hdiv := (mem_radicalDivisors c.S r d).mp hd
  refine ⟨⟨radicalDivisor_ne_bot hd, ?_⟩, hrad.2.squarefree_of_dvd hdiv⟩
  exact fun P hP hPd => hrad.1.2 P hP (hPd.trans hdiv)

theorem radical_tsum_eq_sum (S : Finset (Ideal O)) (r : Ideal O)
    (v : Ideal O → ℝ) :
    (∑' d : Ideal O, if d ∣ outsideRadical S r then v d else 0) =
      ∑ d ∈ radicalDivisors S r, v d := by
  rw [tsum_eq_sum (s := radicalDivisors S r) (fun d hd =>
    if_neg (fun h => hd ((mem_radicalDivisors S r d).mpr h)))]
  exact Finset.sum_congr rfl (fun d hd => if_pos ((mem_radicalDivisors S r d).mp hd))

def rowBall (H : ℝ) : Finset O :=
  (finite_normElement_le H).toFinset.filter (fun k => 0 < normElement k)

@[simp] theorem mem_rowBall (H : ℝ) (k : O) :
    k ∈ rowBall H ↔ 0 < normElement k ∧ normElement k ≤ H := by
  simp [rowBall, and_comm]

def idealBand (S : Finset (Ideal O)) (F : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le (2 * F)).toFinset.filter
    (fun f => SquarefreeOutside S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F)

@[simp] theorem mem_idealBand (S : Finset (Ideal O)) (F : ℝ) (f : Ideal O) :
    f ∈ idealBand S F ↔
      SquarefreeOutside S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F := by
  simp only [idealBand, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨And.right, fun h => ⟨h.2.2.le, h⟩⟩

theorem rowEnergy_eq_sum (column : O → ℂ) (H : ℝ) :
    rowEnergy column H = ∑ k ∈ rowBall H, ‖column k‖ ^ 2 := by
  unfold rowEnergy
  rw [tsum_eq_sum (s := rowBall H) (fun k hk =>
    if_neg (fun h => hk ((mem_rowBall H k).mpr h)))]
  exact Finset.sum_congr rfl (fun k hk => if_pos ((mem_rowBall H k).mp hk))

theorem band_tsum_eq_sum (S : Finset (Ideal O)) (F : ℝ) (v : Ideal O → ℝ) :
    (∑' f : Ideal O,
      if SquarefreeOutside S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then v f else 0) =
        ∑ f ∈ idealBand S F, v f := by
  rw [tsum_eq_sum (s := idealBand S F) (fun f hf =>
    if_neg (fun h => hf ((mem_idealBand S F f).mpr h)))]
  exact Finset.sum_congr rfl (fun f hf => if_pos ((mem_idealBand S F f).mp hf))

theorem energy_eq_sum (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (H X F : ℝ) : energy c ξ W H X F =
      (X * F)⁻¹ * ∑ f ∈ idealBand c.S F, rowEnergy (fun k => columnSum c ξ W X k f) H := by
  rw [energy, band_tsum_eq_sum]

theorem excludedEnergy_eq_sum (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (r : Ideal O) (H X F : ℝ) : excludedEnergy c ξ W r H X F =
      (X * F)⁻¹ * ∑ f ∈ idealBand c.S F,
        rowEnergy (fun k => excludedColumnSum c ξ W r X k f) H := by
  rw [excludedEnergy, band_tsum_eq_sum]

def exclusionMultiplier {c : ArithmeticContext} (ξ : RayCharacter c)
    (d : Ideal O) (k : O) (f : Ideal O) : ℂ :=
  (mobius d : ℂ) * coefficient ξ.val d * sexticSymbol d k *
    sexticSymbol d (primaryGenerator f) ^ (4 : ℕ)

/-- Arithmetic child: Möbius inversion and the `n = d m` reindexing, including
the vanishing terms when `d f` is not squarefree outside `S`. -/
def ColumnExpansionStatement : Prop :=
  ∀ (c : ArithmeticContext), ArithmeticRelations c →
  ∀ (I : SupportInterval) (ξ : RayCharacter c) (W : ℝ → ℂ)
      (r : Ideal O) (X : ℝ) (k : O) (f : Ideal O),
    r ≠ ⊥ → SmoothSupported I W → 0 < X → SquarefreeOutside c.S f →
    excludedColumnSum c ξ W r X k f =
      ∑ d ∈ radicalDivisors c.S r,
        if SquarefreeOutside c.S (d * f) then
          exclusionMultiplier ξ d k f * columnSum c ξ W (X / normIdeal d) k (d * f)
        else 0

/-- Pointwise arithmetic bound, with no assertion about infinite sums. -/
def MultiplierBoundStatement : Prop :=
  ∀ (c : ArithmeticContext), ArithmeticRelations c →
  ∀ (ξ : RayCharacter c) (d : Ideal O) (k : O) (f : Ideal O),
    SquarefreeOutside c.S d → ‖exclusionMultiplier ξ d k f‖ ≤ 1

theorem multiplier_bound : MultiplierBoundStatement := by
  intro c hc ξ d k f hd
  exact norm_removal_product_le_one c hc ξ d k f hd

theorem squarefreeOutside_of_mul_left {S : Finset (Ideal O)} {d f : Ideal O}
    (h : SquarefreeOutside S (d * f)) : SquarefreeOutside S d := by
  refine ⟨⟨?_, ?_⟩, h.2.of_mul_left⟩
  · exact ne_zero_of_dvd_ne_zero h.1.1 (dvd_mul_right d f)
  · intro P hP hd
    exact h.1.2 P hP (hd.trans (dvd_mul_right d f))

theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (z : ι → ℂ) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hz : ∀ i ∈ s, ‖z i‖ ^ 2 ≤ b i) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, b i := by
  calc
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (∑ _i ∈ s, (1 : ℝ)) * ∑ i ∈ s, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (fun _ _ => zero_le_one) hb (fun i hi => by simpa using hz i hi)
    _ = _ := by simp

theorem column_sq_bound (hexp : ColumnExpansionStatement) (hmult : MultiplierBoundStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (I : SupportInterval)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (r : Ideal O) (X : ℝ) (k : O) (f : Ideal O)
    (hr : r ≠ ⊥) (hW : SmoothSupported I W) (hX : 0 < X)
    (hf : SquarefreeOutside c.S f) :
    ‖excludedColumnSum c ξ W r X k f‖ ^ 2 ≤
      ((radicalDivisors c.S r).card : ℝ) *
        ∑ d ∈ radicalDivisors c.S r, if SquarefreeOutside c.S (d * f) then
          ‖columnSum c ξ W (X / normIdeal d) k (d * f)‖ ^ 2 else 0 := by
  rw [hexp c hc I ξ W r X k f hr hW hX hf]
  apply norm_sum_sq_le_card
  · intro d _
    split_ifs <;> positivity
  · intro d _
    split_ifs with hdf
    · rw [norm_mul, mul_pow]
      have h := pow_le_pow_left₀ (norm_nonneg _) (hmult c hc ξ d k f
        (squarefreeOutside_of_mul_left hdf)) 2
      simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right h
        (sq_nonneg ‖columnSum c ξ W (X / normIdeal d) k (d * f)‖)
    · simp

theorem row_bound (hexp : ColumnExpansionStatement) (hmult : MultiplierBoundStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (I : SupportInterval)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (r : Ideal O) (H X : ℝ) (f : Ideal O)
    (hr : r ≠ ⊥) (hW : SmoothSupported I W) (hX : 0 < X)
    (hf : SquarefreeOutside c.S f) :
    rowEnergy (fun k => excludedColumnSum c ξ W r X k f) H ≤
      ((radicalDivisors c.S r).card : ℝ) *
        ∑ d ∈ radicalDivisors c.S r, if SquarefreeOutside c.S (d * f) then
          rowEnergy (fun k => columnSum c ξ W (X / normIdeal d) k (d * f)) H else 0 := by
  rw [rowEnergy_eq_sum]
  calc
    _ ≤ ∑ k ∈ rowBall H, ((radicalDivisors c.S r).card : ℝ) *
        ∑ d ∈ radicalDivisors c.S r, if SquarefreeOutside c.S (d * f) then
          ‖columnSum c ξ W (X / normIdeal d) k (d * f)‖ ^ 2 else 0 := by
      exact Finset.sum_le_sum (fun k _ => column_sq_bound hexp hmult c hc I ξ W r X k f
        hr hW hX hf)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      split_ifs with hdf
      · simp only [hdf, if_true, rowEnergy_eq_sum]
      · simp only [hdf, if_false, Finset.sum_const_zero]

/-- Multiplication by a nonzero ideal embeds the active squarefree dyadic band
in the enlarged band. The unused terms of the enlarged band are nonnegative. -/
theorem band_transport (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (d : Ideal O) (H X F : ℝ) (hd : d ≠ ⊥) :
    (∑ f ∈ idealBand c.S F, if SquarefreeOutside c.S (d * f) then
      rowEnergy (fun k => columnSum c ξ W (X / normIdeal d) k (d * f)) H else 0) ≤
      ∑ g ∈ idealBand c.S (F * normIdeal d),
        rowEnergy (fun k => columnSum c ξ W (X / normIdeal d) k g) H := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_injOn (fun f => d * f)
  · intro a _ b _ hab
    exact mul_left_cancel₀ hd hab
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hfband, hdf⟩ := Finset.mem_filter.mp hf
    obtain ⟨_, hlo, hhi⟩ := (mem_idealBand c.S F f).mp hfband
    apply (mem_idealBand c.S (F * normIdeal d) (d * f)).mpr
    refine ⟨hdf, ?_, ?_⟩
    · rw [normIdeal_mul, mul_comm (normIdeal d)]
      exact mul_le_mul_of_nonneg_right hlo (normIdeal_pos hd).le
    · rw [normIdeal_mul, mul_comm (normIdeal d)]
      calc
        normIdeal f * normIdeal d < (2 * F) * normIdeal d :=
          mul_lt_mul_of_pos_right hhi (normIdeal_pos hd)
        _ = 2 * (F * normIdeal d) := by ring
  · intro f _
    exact le_rfl
  · intro g _ _
    exact rowEnergy_nonneg _ H

/-- The energy conclusion with both arithmetic children explicitly supplied.
The original `Manuscript.remove_exclusions_step` statement is unchanged. -/
theorem remove_exclusions_step_of_components (_ha : ArithmeticStatement)
    (hexp : ColumnExpansionStatement) (hmult : MultiplierBoundStatement) :
    RemoveExclusionsStatement := by
  intro c hc I ξ W r H X F hr hW _hH hX hF
  have hXF : 0 ≤ (X * F)⁻¹ := inv_nonneg.mpr (mul_nonneg hX.le (by linarith))
  rw [excludedEnergy_eq_sum, radical_tsum_eq_sum, ← radicalDivisors_card]
  calc
    _ ≤ (X * F)⁻¹ *
        ∑ f ∈ idealBand c.S F, ((radicalDivisors c.S r).card : ℝ) *
          ∑ d ∈ radicalDivisors c.S r, if SquarefreeOutside c.S (d * f) then
            rowEnergy (fun k => columnSum c ξ W (X / normIdeal d) k (d * f)) H else 0 := by
      apply mul_le_mul_of_nonneg_left _ hXF
      exact Finset.sum_le_sum (fun f hf => row_bound hexp hmult c hc I ξ W r H X f
        hr hW hX ((mem_idealBand c.S F f).mp hf).1)
    _ = ((radicalDivisors c.S r).card : ℝ) *
        ∑ d ∈ radicalDivisors c.S r, (X * F)⁻¹ *
          ∑ f ∈ idealBand c.S F, if SquarefreeOutside c.S (d * f) then
            rowEnergy (fun k => columnSum c ξ W (X / normIdeal d) k (d * f)) H else 0 := by
      rw [← Finset.mul_sum, mul_left_comm, Finset.sum_comm, Finset.mul_sum]
    _ ≤ ((radicalDivisors c.S r).card : ℝ) *
        ∑ d ∈ radicalDivisors c.S r, energy c ξ W H (X / normIdeal d) (F * normIdeal d) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro d hd
      have hd0 := radicalDivisor_ne_bot hd
      have hnorm : (X / normIdeal d) * (F * normIdeal d) = X * F := by
        field_simp [(normIdeal_pos hd0).ne'] <;> ring
      rw [energy_eq_sum, hnorm]
      exact mul_le_mul_of_nonneg_left (band_transport c ξ W d H X F hd0) hXF

/-- Only the arithmetic column identity remains as an explicit input. -/
theorem remove_exclusions_step_of_column_expansion (ha : ArithmeticStatement)
    (hexp : ColumnExpansionStatement) : RemoveExclusionsStatement :=
  remove_exclusions_step_of_components ha hexp multiplier_bound

end QRHShort.RemoveExclusionsProof
