import QRHShort.Estimates
import QRHShort.CompletedScalar
import QRHShort.CompletedArithmeticSupport
import QRHShort.External
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The square-factor assembly in the proof of `prop:R` (paper2.tex:2189--2224).
The analytic squarefree estimate is an explicit upstream hypothesis.  The
arithmetic lemmas below concern the concrete symbols, including their zero
extensions; they do not assume a reciprocity theorem.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort
namespace CompletedAssembly
open SquarefreeReflection
open SquarefreeReflection.RayValuePrerequisites
open SquarefreeReflection.NumeratorPrerequisites

/-- The eighth and second powers agree, also when the local symbol is zero. -/
theorem sexticAtPrime_pow_eight {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a : O) :
    sexticAtPrime P a ^ 8 = sexticAtPrime P a ^ 2 := by
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hP hζ ha]
    norm_num
  obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hP hζ ha
  rw [sexticAtPrime_eq_of_test hζ hj ht]
  have hz : embedding (rootSix ^ j) ^ 6 = 1 := by
    rw [← embedding_pow, ← pow_mul, Nat.mul_comm, pow_mul,
      rootSix_pow_six, one_pow, embedding_one]
  calc
    embedding (rootSix ^ j) ^ 8 =
      embedding (rootSix ^ j) ^ 6 * embedding (rootSix ^ j) ^ 2 := by ring
    _ = embedding (rootSix ^ j) ^ 2 := by rw [hz, one_mul]

theorem sexticSymbol_pow_eight (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (a : O) :
    sexticSymbol n a ^ 8 = sexticSymbol n a ^ 2 := by
  simp only [sexticSymbol, if_neg hn.1, ← Multiset.prod_map_pow]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  exact sexticAtPrime_pow_eight (prime_of_normalized_factor P hP)
    (outside_quotient_rootSix_isPrimitiveRoot c (prime_of_normalized_factor P hP)
      (outside_of_mem_normalizedFactors hn hP)) a

/-- Equation immediately after `k = u₀ s v²` in the proof of `prop:R`. -/
theorem completedTwistElement_square_shift (c : ArithmeticContext)
    (ξ : RayCharacter c) (k g v : O) :
    completedTwistElement c ξ (k * v ^ 2) g =
      completedTwistElement c ξ k (g * v ^ 2) := by
  funext n
  by_cases hn : Outside c.S n
  · simp only [completedTwistElement, if_pos hn,
      sexticSymbol_mul_numerator c hn, sexticSymbol_pow_numerator c hn, mul_pow]
    rw [← pow_mul, show 2 * 4 = 8 from rfl, sexticSymbol_pow_eight c hn]
    ring
  · simp only [completedTwistElement, if_neg hn]

theorem completedRowElement_square_shift (c : ArithmeticContext)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (X : ℝ) (k g v : O) :
    completedRowElement c ξ W X (k * v ^ 2) g =
      completedRowElement c ξ W X k (g * v ^ 2) := by
  unfold completedRowElement
  rw [completedTwistElement_square_shift]

theorem completedRow_square_shift (c : ArithmeticContext)
    (ξ : RayCharacter c) (W : ℝ → ℂ) (X : ℝ) (k v : O) (f : Ideal O) :
    completedRow c ξ W X (k * v ^ 2) f =
      completedRowElement c ξ W X k (primaryGenerator f * v ^ 2) := by
  exact completedRowElement_square_shift c ξ W X k (primaryGenerator f) v

@[simp] theorem principal_mul (a b : O) :
    principal (a * b) = principal a * principal b :=
  (Ideal.span_singleton_mul_span_singleton a b).symm

@[simp] theorem principal_pow (a : O) (m : ℕ) :
    principal (a ^ m) = principal a ^ m :=
  (Ideal.span_singleton_pow a m).symm

@[simp] theorem normIdeal_mul (a b : Ideal O) :
    normIdeal (a * b) = normIdeal a * normIdeal b := by
  simp only [normIdeal, map_mul, Nat.cast_mul]

@[simp] theorem normIdeal_pow (a : Ideal O) (m : ℕ) :
    normIdeal (a ^ m) = normIdeal a ^ m := by
  simp only [normIdeal, map_pow, Nat.cast_pow]

@[simp] theorem normElement_mul (a b : O) :
    normElement (a * b) = normElement a * normElement b := by
  simp only [normElement, principal_mul, normIdeal_mul]

@[simp] theorem normElement_pow (a : O) (m : ℕ) :
    normElement (a ^ m) = normElement a ^ m := by
  simp only [normElement, principal_pow, normIdeal_pow]

theorem one_le_normIdeal {a : Ideal O} (ha : a ≠ ⊥) : 1 ≤ normIdeal a := by
  have h : 1 ≤ a.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun hz => ha (Ideal.absNorm_eq_zero_iff.mp hz))
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast h

theorem principal_ne_bot {a : O} (ha : a ≠ 0) : principal a ≠ ⊥ := by
  intro h
  exact ha (Ideal.span_singleton_eq_bot.mp h)

theorem normElement_pos {a : O} (ha : a ≠ 0) : 0 < normElement a :=
  zero_lt_one.trans_le (one_le_normIdeal (principal_ne_bot ha))

theorem primaryGenerator_spec_of_exists {a : Ideal O}
    (h : ∃ z : O, principal z = a ∧ IsPrimary z) :
    principal (primaryGenerator a) = a := by
  simpa only [primaryGenerator, dif_pos h] using (Classical.choose_spec h).1

theorem prime_generator_spec {P : Ideal O} (hP : Prime P) :
    principal (if IsRelPrime P (principal 3) then primaryGenerator P
      else idealGenerator P) = P := by
  by_cases hrel : IsRelPrime P (principal 3)
  · rw [if_pos hrel]
    apply primaryGenerator_spec_of_exists
    apply exists_primary_generator_of_prime hP
    intro hthree
    exact hP.not_unit (hrel (dvd_refl P) hthree)
  · rw [if_neg hrel]
    exact Ideal.span_singleton_generator P

/-- The manuscript's fixed prime-generator product really generates its ideal. -/
theorem chosenGenerator_spec {a : Ideal O} (ha : a ≠ ⊥) :
    principal (chosenGenerator a) = a := by
  rw [chosenGenerator, if_neg ha, principal, ← Ideal.multiset_prod_span_singleton,
    Multiset.map_map]
  calc
    ((normalizedFactors a).map (fun P =>
        Ideal.span {if IsRelPrime P (principal 3) then primaryGenerator P
          else idealGenerator P})).prod = (normalizedFactors a).prod := by
      congr 1
      simpa only [principal, Multiset.map_id'] using
        (Multiset.map_congr rfl (fun P hP =>
          prime_generator_spec (prime_of_normalized_factor P hP)))
    _ = a := Ideal.prod_normalizedFactors_eq_self ha

@[simp] theorem norm_chosenGenerator {a : Ideal O} (ha : a ≠ ⊥) :
    normElement (chosenGenerator a) = normIdeal a := by
  rw [normElement, chosenGenerator_spec ha]

@[simp] theorem norm_unit (u : Oˣ) : normElement (u : O) = 1 := by
  rw [normElement, principal, Ideal.span_singleton_eq_top.mpr u.isUnit]
  simp [normIdeal]

/-- Existence suffices for a nonnegative-sum bound; no coprimality of `s,v` is used. -/
theorem exists_unit_squarefree_square {k : O} (hk : k ≠ 0) :
    ∃ (u : Oˣ) (s v : Ideal O), s ≠ ⊥ ∧ v ≠ ⊥ ∧ Squarefree s ∧
      k = (u : O) * chosenGenerator s * chosenGenerator v ^ 2 := by
  obtain ⟨v, s, hvs, hs⟩ := exists_sq_mul_squarefree (principal k)
  have hv : v ≠ ⊥ := by
    intro h
    apply principal_ne_bot hk
    rw [← hvs, h]
    simp
  have hs0 : s ≠ ⊥ := by
    intro h
    apply principal_ne_bot hk
    rw [← hvs, h]
    simp
  have hp : principal (chosenGenerator s * chosenGenerator v ^ 2) = principal k := by
    rw [principal_mul, principal_pow, chosenGenerator_spec hs0,
      chosenGenerator_spec hv, mul_comm, hvs]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hp
  refine ⟨u, s, v, hs0, hv, hs, ?_⟩
  rw [← hu]
  ring

theorem primaryGenerator_spec_outside (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : principal (primaryGenerator a) = a := by
  apply primaryGenerator_spec_of_exists
  let z := idealGenerator a
  have hz : principal z = a := Ideal.span_singleton_generator a
  have hp : Prime (principal (omega - 1)) :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have hthree : principal (omega - 1) ∣ principal 3 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three
  have hnot : ¬ omega - 1 ∣ z := by
    intro hdiv
    apply ha.2 _ (c.above_three _ hp hthree)
    rw [← hz]
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr hdiv
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  exact ⟨(u : O) * z, (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz, hu⟩

/-- The principal Hecke character with modulus the unit ideal. -/
def trivialHeckeCharacter : HeckeCharacter where
  modulus := ⊤
  modulus_ne_bot := top_ne_bot
  residue := 1
  unit_trivial u := MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk ⊤))

theorem trivialHeckeCharacter_onIdeal {a : Ideal O} (ha : a ≠ ⊥) :
    trivialHeckeCharacter.onIdeal a = 1 := by
  rw [HeckeCharacter.onIdeal, if_neg ha]
  apply MulChar.one_apply
  have heq : Ideal.Quotient.mk (⊤ : Ideal O) (idealGenerator a) = 1 :=
    Subsingleton.elim _ _
  change IsUnit (Ideal.Quotient.mk (⊤ : Ideal O) (idealGenerator a))
  rw [heq]
  exact isUnit_one

/-- The convergent `ζ_K(2)` factor uses only the existing Hecke continuation input. -/
theorem summable_inverse_norm_sq :
    Summable (fun v : Ideal O => (normIdeal v ^ 2)⁻¹) := by
  apply Complex.summable_ofReal.mp
  have hs := (HeckeL_hasSum trivialHeckeCharacter (2 : ℂ) (by norm_num)).summable
  apply hs.congr
  intro v
  by_cases hv : v = ⊥
  · simp [heckeSeriesTerm, hv, normIdeal]
  · rw [heckeSeriesTerm, if_neg hv, trivialHeckeCharacter_onIdeal hv]
    simp only [Complex.cpow_ofNat, one_div, Complex.ofReal_inv, Complex.ofReal_pow]

def unitFinset : Finset Oˣ := finite_units.toFinset

def idealNormBall (H : ℝ) : Finset (Ideal O) := (finite_normIdeal_le H).toFinset

def positiveRowBall (H : ℝ) : Finset O :=
  (finite_normElement_le H).toFinset.filter (fun k => 0 < normElement k)

def squareDivisors (H : ℝ) : Finset (Ideal O) :=
  (idealNormBall H).filter (fun v => v ≠ ⊥ ∧ normIdeal v ^ 2 ≤ H)

@[simp] theorem mem_unitFinset (u : Oˣ) : u ∈ unitFinset := by
  simp [unitFinset]

@[simp] theorem mem_idealNormBall (H : ℝ) (a : Ideal O) :
    a ∈ idealNormBall H ↔ normIdeal a ≤ H := by
  simp [idealNormBall]

@[simp] theorem mem_positiveRowBall (H : ℝ) (k : O) :
    k ∈ positiveRowBall H ↔ 0 < normElement k ∧ normElement k ≤ H := by
  simp [positiveRowBall, and_comm]

@[simp] theorem mem_squareDivisors (H : ℝ) (v : Ideal O) :
    v ∈ squareDivisors H ↔ v ≠ ⊥ ∧ normIdeal v ^ 2 ≤ H := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    rw [mem_idealNormBall]
    have hv := one_le_normIdeal h.1
    nlinarith [sq_nonneg (normIdeal v - 1)]

def squarefreeRowTerm (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X H : ℝ) (g : O) (u : Oˣ) (s : Ideal O) : ℝ :=
  if s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ H then
    ‖completedRowElement c ξ W X ((u : O) * chosenGenerator s) g‖ ^ 2 else 0

theorem squarefreeRowTerm_nonneg (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X H : ℝ) (g : O) (u : Oˣ) (s : Ideal O) :
    0 ≤ squarefreeRowTerm c ξ W X H g u s := by
  unfold squarefreeRowTerm
  split_ifs <;> positivity

theorem squarefreeRowTerm_summable (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X H : ℝ) (g : O) (u : Oˣ) :
    Summable (squarefreeRowTerm c ξ W X H g u) := by
  apply summable_of_hasFiniteSupport
  apply (finite_normIdeal_le H).subset
  intro s hs
  by_contra h
  apply hs
  exact if_neg (fun hs => h hs.2.2)

theorem rowEnergy_eq_sum (column : O → ℂ) (H : ℝ) :
    rowEnergy column H = ∑ k ∈ positiveRowBall H, ‖column k‖ ^ 2 := by
  unfold rowEnergy
  rw [tsum_eq_sum (s := positiveRowBall H) (fun k hk =>
    if_neg (fun h => hk ((mem_positiveRowBall H k).mpr h)))]
  apply Finset.sum_congr rfl
  intro k hk
  exact if_pos ((mem_positiveRowBall H k).mp hk)

theorem rowEnergy_mono (column : O → ℂ) {H B : ℝ} (hHB : H ≤ B) :
    rowEnergy column H ≤ rowEnergy column B := by
  apply Summable.tsum_le_tsum _ (rowEnergy_summable column H)
    (rowEnergy_summable column B)
  intro k
  by_cases hk : 0 < normElement k ∧ normElement k ≤ H
  · rw [if_pos hk, if_pos ⟨hk.1, hk.2.trans hHB⟩]
  · rw [if_neg hk]
    split_ifs <;> positivity

theorem nonnegative_sum_le_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (e : β → α) (F : α → ℝ)
    (hF : ∀ a, 0 ≤ F a) (hcover : ∀ a ∈ s, ∃ b ∈ t, e b = a) :
    ∑ a ∈ s, F a ≤ ∑ b ∈ t, F (e b) := by
  have hsub : s ⊆ t.image e := by
    intro a ha
    obtain ⟨b, hb, he⟩ := hcover a ha
    exact Finset.mem_image.mpr ⟨b, hb, he⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hF a)).trans
    (Finset.sum_image_le_of_nonneg (fun a _ => hF a))

/-- The exact nonnegative row regrouping required by `prop:R`.
Only a cover is needed: uniqueness of squarefree decomposition is not assumed. -/
theorem rowEnergy_le_squarefree_rows (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (X B : ℝ) (f : Ideal O) :
    rowEnergy (fun k => completedRow c ξ W X k f) B ≤
      ∑ v ∈ squareDivisors B, ∑ u ∈ unitFinset,
        ∑' s : Ideal O, squarefreeRowTerm c ξ W X (B / normIdeal v ^ 2)
          (primaryGenerator f * chosenGenerator v ^ 2) u s := by
  let ind : Finset (Ideal O × (Oˣ × Ideal O)) :=
    ((squareDivisors B).product (unitFinset.product (idealNormBall B))).filter
      (fun p => p.2.2 ≠ ⊥ ∧ Squarefree p.2.2 ∧
        normIdeal p.2.2 ≤ B / normIdeal p.1 ^ 2)
  let value : Ideal O × (Oˣ × Ideal O) → O :=
    fun p => (p.2.1 : O) * chosenGenerator p.2.2 * chosenGenerator p.1 ^ 2
  have hcover : ∀ k ∈ positiveRowBall B, ∃ p ∈ ind, value p = k := by
    intro k hk
    obtain ⟨hkpos, hkB⟩ := (mem_positiveRowBall B k).mp hk
    have hk0 : k ≠ 0 := by
      intro h
      simpa [h, normElement, principal, normIdeal] using hkpos
    obtain ⟨u, s, v, hs0, hv0, hs, heq⟩ := exists_unit_squarefree_square hk0
    have hknorm : normElement k = normIdeal s * normIdeal v ^ 2 := by
      rw [heq, normElement_mul, normElement_mul, norm_unit, one_mul,
        normElement_pow, norm_chosenGenerator hs0, norm_chosenGenerator hv0]
    have hNs := one_le_normIdeal hs0
    have hNv := one_le_normIdeal hv0
    have hv2 : 0 < normIdeal v ^ 2 := pow_pos (zero_lt_one.trans_le hNv) _
    have hprodB : normIdeal s * normIdeal v ^ 2 ≤ B := hknorm ▸ hkB
    have hvB : normIdeal v ^ 2 ≤ B := by
      exact (le_mul_of_one_le_left hv2.le hNs).trans hprodB
    have hsB : normIdeal s ≤ B := by
      have hv21 : 1 ≤ normIdeal v ^ 2 := one_le_pow₀ hNv
      exact (le_mul_of_one_le_right (zero_le_one.trans hNs) hv21).trans hprodB
    have hscut : normIdeal s ≤ B / normIdeal v ^ 2 := by
      apply (le_div_iff₀ hv2).mpr
      rwa [← hknorm]
    refine ⟨(v, u, s), ?_, heq.symm⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨(mem_squareDivisors B v).mpr ⟨hv0, hvB⟩,
      Finset.mem_product.mpr ⟨mem_unitFinset u, (mem_idealNormBall B s).mpr hsB⟩⟩,
      hs0, hs, hscut⟩
  rw [rowEnergy_eq_sum]
  calc
    (∑ k ∈ positiveRowBall B, ‖completedRow c ξ W X k f‖ ^ 2) ≤
        ∑ p ∈ ind, ‖completedRow c ξ W X (value p) f‖ ^ 2 :=
      nonnegative_sum_le_cover _ _ _ _ (fun _ => sq_nonneg _) hcover
    _ ≤ ∑ v ∈ squareDivisors B, ∑ u ∈ unitFinset,
        ∑' s : Ideal O, squarefreeRowTerm c ξ W X (B / normIdeal v ^ 2)
          (primaryGenerator f * chosenGenerator v ^ 2) u s := by
      simp only [ind, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro u _
      have heq : (∑ s ∈ idealNormBall B,
          if s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ B / normIdeal v ^ 2 then
            ‖completedRow c ξ W X (value (v, u, s)) f‖ ^ 2 else 0) =
          ∑ s ∈ idealNormBall B, squarefreeRowTerm c ξ W X
            (B / normIdeal v ^ 2) (primaryGenerator f * chosenGenerator v ^ 2) u s := by
        apply Finset.sum_congr rfl
        intro s _
        simp only [value, squarefreeRowTerm, completedRow_square_shift]
      rw [heq]
      apply Summable.sum_le_tsum
      · exact fun s _ => squarefreeRowTerm_nonneg c ξ W X _ _ u s
      · exact squarefreeRowTerm_summable c ξ W X _ _ u

theorem squareDivisors_sum_bound (B M : ℝ) (hM : 0 ≤ M) :
    (∑ v ∈ squareDivisors B, ∑ _u ∈ unitFinset, M / normIdeal v ^ 2) ≤
      (unitFinset.card : ℝ) * M * ∑' v : Ideal O, (normIdeal v ^ 2)⁻¹ := by
  have hs : (∑ v ∈ squareDivisors B, (normIdeal v ^ 2)⁻¹) ≤
      ∑' v : Ideal O, (normIdeal v ^ 2)⁻¹ := by
    apply Summable.sum_le_tsum
    · exact fun v _ => inv_nonneg.mpr (sq_nonneg _)
    · exact summable_inverse_norm_sq
  calc
    (∑ v ∈ squareDivisors B, ∑ _u ∈ unitFinset, M / normIdeal v ^ 2) =
        (unitFinset.card : ℝ) * M *
          ∑ v ∈ squareDivisors B, (normIdeal v ^ 2)⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      simp only [← mul_assoc, ← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg (Nat.cast_nonneg _) hM)

end CompletedAssembly

/-- Conditional square-factor assembly of `prop:R`: the only upstream estimate
is the explicit squarefree-completed hypothesis `hs`. -/
theorem completed_of_squarefree (hs : SquarefreeCompletedEstimate) : CompletedEstimate := by
  intro ε C hε hC
  obtain ⟨J, hJ, hsq⟩ := hs ε (2 * C) hε (by linarith)
  refine ⟨J, hJ, ?_⟩
  intro c I A hc hA
  obtain ⟨K, hK, hrows⟩ := hsq c I hc
  let a : ℝ := max 1 A
  let Z : ℝ := ∑' v : Ideal O, (normIdeal v ^ 2)⁻¹
  have ha : 1 ≤ a := le_max_left _ _
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hZ : 0 ≤ Z := tsum_nonneg (fun v => inv_nonneg.mpr (sq_nonneg _))
  refine ⟨(CompletedAssembly.unitFinset.card : ℝ) * Z * K * a ^ ε * a ^ (2 : ℕ),
    by positivity, ?_⟩
  intro ξ W D H X f hW hD hf hH hHmax hX hXmax hF hFmax
  have hD0 : 0 ≤ D := by linarith
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hF0 : 0 ≤ normIdeal f := zero_le_one.trans hF
  have hB0 : 0 ≤ a * H := mul_nonneg ha0 hH0
  obtain ⟨haD, hBmax, hDXmax, hFBmax⟩ :=
    CompletedAssembly.enlarged_ranges ha hD hC hH hHmax hF hFmax
  have hfgen : normElement (primaryGenerator f) = normIdeal f := by
    unfold normElement
    rw [CompletedAssembly.primaryGenerator_spec_outside c hf.1]
  let M : ℝ := K * (a * D) ^ ε * weightNorm J W ^ 2 *
    (a * H + (a * H) ^ (2 : ℕ) * normIdeal f / X)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (mul_nonneg ha0 hD0) _))
        (sq_nonneg _))
      (add_nonneg hB0 (div_nonneg (mul_nonneg (sq_nonneg _) hF0) hX0))
  have hrow : ∀ v ∈ CompletedAssembly.squareDivisors (a * H),
      ∀ u ∈ CompletedAssembly.unitFinset,
      (∑' s : Ideal O, CompletedAssembly.squarefreeRowTerm c ξ W X
        (a * H / normIdeal v ^ 2) (primaryGenerator f * chosenGenerator v ^ 2) u s) ≤
          M / normIdeal v ^ 2 := by
    intro v hv u _
    obtain ⟨hv0, hvB⟩ := (CompletedAssembly.mem_squareDivisors (a * H) v).mp hv
    have hNv := CompletedAssembly.one_le_normIdeal hv0
    have hNv0 : 0 < normIdeal v := zero_lt_one.trans_le hNv
    have hv21 : 1 ≤ normIdeal v ^ (2 : ℕ) := one_le_pow₀ hNv
    have hv2 : 0 < normIdeal v ^ (2 : ℕ) := pow_pos hNv0 _
    have hcut : 1 ≤ a * H / normIdeal v ^ 2 :=
      (le_div_iff₀ hv2).mpr (by simpa only [one_mul] using hvB)
    have hcutmax : a * H / normIdeal v ^ 2 ≤ (a * D) ^ (2 * C) := by
      apply le_trans _ hBmax
      exact (div_le_iff₀ hv2).mpr (le_mul_of_one_le_right hB0 hv21)
    have hg : normElement (primaryGenerator f * chosenGenerator v ^ 2) =
        normIdeal f * normIdeal v ^ 2 := by
      rw [CompletedAssembly.normElement_mul, CompletedAssembly.normElement_pow,
        CompletedAssembly.norm_chosenGenerator hv0, hfgen]
    have hg1 : 1 ≤ normElement (primaryGenerator f * chosenGenerator v ^ 2) := by
      rw [hg]
      exact one_le_mul_of_one_le_of_one_le hF hv21
    have hgmax : normElement (primaryGenerator f * chosenGenerator v ^ 2) ≤
        (a * D) ^ (2 * C) := by
      rw [hg]
      exact (mul_le_mul_of_nonneg_left hvB hF0).trans hFBmax
    have h := hrows ξ W (a * D) (a * H / normIdeal v ^ 2) X
      (primaryGenerator f * chosenGenerator v ^ 2) u hW haD hcut hcutmax
      hX (hXmax.trans hDXmax) hg1 hgmax
    change (∑' s : Ideal O, CompletedAssembly.squarefreeRowTerm c ξ W X
      (a * H / normIdeal v ^ 2) (primaryGenerator f * chosenGenerator v ^ 2) u s) ≤ _ at h
    rw [hg, CompletedAssembly.square_shift_bound_identity _ _ _ _ hNv0.ne'] at h
    simpa only [M, mul_div_assoc] using h
  calc
    rowEnergy (fun k => completedRow c ξ W X k f) (A * H) ≤
        rowEnergy (fun k => completedRow c ξ W X k f) (a * H) :=
      CompletedAssembly.rowEnergy_mono _
        (mul_le_mul_of_nonneg_right (le_max_right 1 A) hH0)
    _ ≤ ∑ v ∈ CompletedAssembly.squareDivisors (a * H),
        ∑ u ∈ CompletedAssembly.unitFinset,
          ∑' s : Ideal O, CompletedAssembly.squarefreeRowTerm c ξ W X
            (a * H / normIdeal v ^ 2) (primaryGenerator f * chosenGenerator v ^ 2) u s :=
      CompletedAssembly.rowEnergy_le_squarefree_rows c ξ W X (a * H) f
    _ ≤ ∑ v ∈ CompletedAssembly.squareDivisors (a * H),
        ∑ _u ∈ CompletedAssembly.unitFinset, M / normIdeal v ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.sum_le_sum (fun u hu => hrow v hv u hu)
    _ ≤ (CompletedAssembly.unitFinset.card : ℝ) * M * Z :=
      CompletedAssembly.squareDivisors_sum_bound (a * H) M hM
    _ ≤ (CompletedAssembly.unitFinset.card : ℝ) *
        (K * (a * D) ^ ε * weightNorm J W ^ 2 *
          (a ^ (2 : ℕ) * (H + H ^ (2 : ℕ) * normIdeal f / X))) * Z := by
      apply mul_le_mul_of_nonneg_right _ hZ
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left
        (CompletedAssembly.radius_polynomial_bound ha hH0 hF0 hX0)
      exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (mul_nonneg ha0 hD0) _))
        (sq_nonneg _)
    _ = ((CompletedAssembly.unitFinset.card : ℝ) * Z * K * a ^ ε * a ^ (2 : ℕ)) *
        D ^ ε * weightNorm J W ^ 2 * (H + H ^ (2 : ℕ) * normIdeal f / X) := by
      rw [Real.mul_rpow ha0 hD0]
      ring

end QRHShort

#print axioms QRHShort.CompletedAssembly.completedRow_square_shift
#print axioms QRHShort.CompletedAssembly.square_shift_bound_identity
#print axioms QRHShort.completed_of_squarefree
