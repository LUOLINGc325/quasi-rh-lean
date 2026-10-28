import QRHShort.CompletedSupport
import QRHShort.InitialEnergyBridge
import QRHShort.PrimaryGenerator
import QRHShort.PrimeComparison
import QRHShort.IdealMobiusCancellation
import Mathlib.Tactic.LinearCombination

/-! The arithmetic and finite divisor identities behind actual cube completion.
All generators, twists and weights in this file are the manuscript definitions.
-/

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

@[simp] theorem outside_one (c : ArithmeticContext) : Outside c.S 1 := by
  refine ⟨by simp, ?_⟩
  intro p hp
  exact (c.prime_S p hp).not_dvd_one

theorem outside_mul_iff (c : ArithmeticContext) (a b : Ideal O) :
    Outside c.S (a * b) ↔ Outside c.S a ∧ Outside c.S b := by
  constructor
  · intro h
    constructor
    · refine ⟨?_, fun p hp hpa => h.2 p hp (dvd_mul_of_dvd_left hpa b)⟩
      intro ha
      exact h.1 (by rw [ha, Ideal.bot_mul])
    · refine ⟨?_, fun p hp hpb => h.2 p hp (dvd_mul_of_dvd_right hpb a)⟩
      intro hb
      exact h.1 (by rw [hb, Ideal.mul_bot])
  · rintro ⟨ha, hb⟩
    refine ⟨fun h => (Ideal.mul_eq_bot.mp h).elim ha.1 hb.1, ?_⟩
    intro p hp hdiv
    exact ((c.prime_S p hp).dvd_mul.mp hdiv).elim (ha.2 p hp) (hb.2 p hp)

theorem outside_of_dvd (c : ArithmeticContext) {a b : Ideal O}
    (hb : Outside c.S b) (hab : a ∣ b) : Outside c.S a := by
  refine ⟨?_, fun p hp hpa => hb.2 p hp (hpa.trans hab)⟩
  intro ha
  apply hb.1
  have ha0 : a = 0 := ha
  have hb0 : b = 0 := zero_dvd_iff.mp (ha0 ▸ hab)
  exact hb0

/-- Excluding the prime above three gives a primary generator for every ideal,
not only for a prime ideal. -/
theorem exists_primary_generator_outside (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : ∃ z : O, principal z = a ∧ IsPrimary z := by
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
  refine ⟨(u : O) * z, ?_, hu⟩
  exact (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz

theorem primaryGenerator_spec_outside (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) :
    principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) := by
  have h := exists_primary_generator_outside c ha
  simpa only [primaryGenerator, dif_pos h] using Classical.choose_spec h

theorem isPrimary_mul {a b : O} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  apply (isPrimary_iff_three_dvd _).mpr
  have h := dvd_add (dvd_mul_of_dvd_left ((isPrimary_iff_three_dvd a).mp ha) b)
    ((isPrimary_iff_three_dvd b).mp hb)
  convert h using 1 <;> ring

/-- A unit congruent to one modulo three is one. -/
theorem isPrimary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) : u = 1 := by
  have hthree := (isPrimary_iff_three_dvd (u : O)).mp hu
  have hlambda : (omega - 1) ^ (2 : ℕ) ∣ (3 : O) := by
    refine ⟨-omega ^ (2 : ℕ), ?_⟩
    rw [omega_sub_one_sq]
    calc
      (3 : O) = 3 * omega ^ (3 : ℕ) := by rw [omega_cube, mul_one]
      _ = -3 * omega * -omega ^ (2 : ℕ) := by ring
  have hcong : ∃ n : ℤ, (omega - 1) ^ (2 : ℕ) ∣ ((u : O) - n) :=
    ⟨1, by simpa only [Int.cast_one] using hlambda.trans hthree⟩
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u hcong with h | h
  · exact h
  · exfalso
    have hneg : omega - 1 ∣ (-1 : O) - 1 := by
      simpa only [h, Units.val_neg, Units.val_one] using
        omega_sub_one_dvd_three.trans hthree
    apply omega_sub_one_prime.not_dvd_one
    convert dvd_add omega_sub_one_dvd_three hneg using 1 <;> ring

/-- Primary generators of the same ideal coincide. -/
theorem primary_eq_of_principal_eq {a b : O} (ha : IsPrimary a) (hb : IsPrimary b)
    (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [isPrimary_unit_eq_one u hup, Units.val_one, mul_one] using hu

@[simp] theorem primaryGenerator_one : primaryGenerator 1 = 1 := by
  have h : ∃ z : O, principal z = 1 ∧ IsPrimary z :=
    ⟨1, by simp [principal], by simp [IsPrimary]⟩
  have hs : principal (primaryGenerator 1) = 1 ∧ IsPrimary (primaryGenerator 1) := by
    simpa only [primaryGenerator, dif_pos h] using Classical.choose_spec h
  exact primary_eq_of_principal_eq hs.2 (by simp [IsPrimary])
    (hs.1.trans (by simp [principal]))

theorem primaryGenerator_mul_outside (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    primaryGenerator (a * b) = primaryGenerator a * primaryGenerator b := by
  have ha' := primaryGenerator_spec_outside c ha
  have hb' := primaryGenerator_spec_outside c hb
  have hab' := primaryGenerator_spec_outside c ((outside_mul_iff c a b).mpr ⟨ha, hb⟩)
  apply primary_eq_of_principal_eq hab'.2 (isPrimary_mul ha'.2 hb'.2)
  rw [hab'.1]
  change a * b = Ideal.span {primaryGenerator a * primaryGenerator b}
  rw [← Ideal.span_singleton_mul_span_singleton]
  change a * b = principal (primaryGenerator a) * principal (primaryGenerator b)
  rw [ha'.1, hb'.1]

@[simp] theorem alpha_one : alpha 1 = 1 := by
  simp only [alpha, primaryGenerator_one, embedding_one, norm_one, Complex.ofReal_one, div_one]

theorem alpha_mul_outside (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) : alpha (a * b) = alpha a * alpha b := by
  simp only [alpha, primaryGenerator_mul_outside c ha hb, embedding_mul,
    norm_mul, Complex.ofReal_mul]
  exact mul_div_mul_comm _ _ _ _

theorem rayValue_eq_onIdeal_outside (c : ArithmeticContext) (χ : HeckeCharacter)
    {a : Ideal O} (ha : Outside c.S a) : rayValue χ a = χ.onIdeal a :=
  (χ.onIdeal_of_generator ha.1 (primaryGenerator_spec_outside c ha).1).symm

@[simp] theorem rayValue_one (χ : HeckeCharacter) : rayValue χ 1 = 1 := by
  simp only [rayValue, primaryGenerator_one, χ.onElement_one]

theorem rayValue_mul_outside (c : ArithmeticContext) (χ : HeckeCharacter)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) :
    rayValue χ (a * b) = rayValue χ a * rayValue χ b := by
  rw [rayValue_eq_onIdeal_outside c χ ((outside_mul_iff c a b).mpr ⟨ha, hb⟩),
    χ.onIdeal_mul, ← rayValue_eq_onIdeal_outside c χ ha,
    ← rayValue_eq_onIdeal_outside c χ hb]

@[simp] theorem sexticSymbol_unit_ideal (z : O) : sexticSymbol 1 z = 1 := by
  simp only [sexticSymbol, show (1 : Ideal O) ≠ ⊥ from one_ne_zero, if_false, normalizedFactors_one,
    Multiset.map_zero, Multiset.prod_zero]

theorem sexticSymbol_mul (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp only [ha, Ideal.bot_mul, sexticSymbol, ite_true, zero_mul]
  by_cases hb : b = ⊥
  · simp only [hb, Ideal.mul_bot, sexticSymbol, ite_true, mul_zero]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, if_neg ha, if_neg hb, if_neg hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

@[simp] theorem completedTwist_one (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) : completedTwist c ξ k f 1 = 1 := by
  simp only [completedTwist, outside_one c, if_true, rayValue_one,
    sexticSymbol_unit_ideal, one_pow, mul_one]

theorem completedTwist_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f a b : Ideal O) :
    completedTwist c ξ k f (a * b) =
      completedTwist c ξ k f a * completedTwist c ξ k f b := by
  by_cases ha : Outside c.S a
  · by_cases hb : Outside c.S b
    · simp only [completedTwist, if_pos ha, if_pos hb,
        if_pos ((outside_mul_iff c a b).mpr ⟨ha, hb⟩),
        rayValue_mul_outside c ξ.val ha hb, sexticSymbol_mul, mul_pow]
      ring
    · have hab : ¬ Outside c.S (a * b) := fun h => hb ((outside_mul_iff c a b).mp h).2
      simp only [completedTwist, if_neg hab, if_neg hb, mul_zero]
  · have hab : ¬ Outside c.S (a * b) := fun h => ha ((outside_mul_iff c a b).mp h).1
    simp only [completedTwist, if_neg hab, if_neg ha, zero_mul]

/-- The coefficient of the cube-divided column in actual completion. -/
def cubeWeight (c : ArithmeticContext) (ξ : RayCharacter c) (k : O)
    (f b : Ideal O) : ℂ :=
  if Outside c.S b then
    star (alpha b) ^ (3 : ℕ) * completedTwist c ξ k f b ^ (3 : ℕ) / (normIdeal b : ℂ)
  else 0

@[simp] theorem cubeWeight_bot (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) : cubeWeight c ξ k f ⊥ = 0 := by
  simp only [cubeWeight, Outside, ne_eq, not_true_eq_false, false_and, if_false]

@[simp] theorem cubeWeight_one (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f : Ideal O) : cubeWeight c ξ k f 1 = 1 := by
  simp only [cubeWeight, outside_one c, if_true, alpha_one, star_one, one_pow,
    completedTwist_one, mul_one, normIdeal, map_one, Nat.cast_one,
    Complex.ofReal_one, div_one]

theorem cubeWeight_mul (c : ArithmeticContext) (ξ : RayCharacter c)
    (k : O) (f a b : Ideal O) :
    cubeWeight c ξ k f (a * b) = cubeWeight c ξ k f a * cubeWeight c ξ k f b := by
  by_cases ha : Outside c.S a
  · by_cases hb : Outside c.S b
    · simp only [cubeWeight, if_pos ha, if_pos hb,
        if_pos ((outside_mul_iff c a b).mpr ⟨ha, hb⟩), alpha_mul_outside c ha hb,
        completedTwist_mul, star_mul, mul_pow, normIdeal_mul, Complex.ofReal_mul,
        div_eq_mul_inv, mul_inv_rev]
      ring
    · have hab : ¬ Outside c.S (a * b) := fun h => hb ((outside_mul_iff c a b).mp h).2
      simp only [cubeWeight, if_neg hab, if_neg hb, mul_zero]
  · have hab : ¬ Outside c.S (a * b) := fun h => ha ((outside_mul_iff c a b).mp h).1
    simp only [cubeWeight, if_neg hab, if_neg ha, zero_mul]

private def cubeDivisorFactorEquiv (n : Ideal O) (hn : n ≠ ⊥) :
    {d : Ideal O // d ∈ idealDivisors n hn} ≃
      {ab : Ideal O × Ideal O // ab.1 * ab.2 = n} where
  toFun d :=
    ⟨(d.val, Classical.choose ((mem_idealDivisors n hn d.val).mp d.property)),
      (Classical.choose_spec ((mem_idealDivisors n hn d.val).mp d.property)).symm⟩
  invFun ab :=
    ⟨ab.val.1, (mem_idealDivisors n hn ab.val.1).mpr
      ⟨ab.val.2, ab.property.symm⟩⟩
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv ab := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    have ha : ab.val.1 ≠ 0 := by
      intro h
      apply hn
      change n = (0 : Ideal O)
      rw [← ab.property, h, zero_mul]
    apply mul_left_cancel₀ ha
    exact (Classical.choose_spec
      ((mem_idealDivisors n hn ab.val.1).mp
        ((mem_idealDivisors n hn ab.val.1).mpr ⟨ab.val.2, ab.property.symm⟩))).symm.trans
      ab.property.symm

private theorem finite_ideal_factor_pairs {n : Ideal O} (hn : n ≠ ⊥) :
    {ab : Ideal O × Ideal O | ab.1 * ab.2 = n}.Finite := by
  apply ((idealDivisors n hn).finite_toSet.prod (idealDivisors n hn).finite_toSet).subset
  rintro ⟨a, b⟩ hab
  exact ⟨(mem_idealDivisors n hn a).mpr ⟨b, hab.symm⟩,
    (mem_idealDivisors n hn b).mpr ⟨a, by simpa only [mul_comm] using hab.symm⟩⟩

private theorem mobius_factor_fiber (g : Ideal O → ℂ) (hg0 : g ⊥ = 0)
    (n : Ideal O) :
    (∑' ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = n},
      (mobius ab.val.1 : ℂ) * g (ab.val.1 * ab.val.2)) =
        if n = 1 then g 1 else 0 := by
  by_cases hn : n = ⊥
  · subst n
    rw [if_neg (by simp)]
    calc
      _ = ∑' _ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = ⊥}, (0 : ℂ) := by
        apply tsum_congr
        intro ab
        rw [ab.property, hg0, mul_zero]
      _ = 0 := tsum_zero
  let e := cubeDivisorFactorEquiv n hn
  calc
    (∑' ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = n},
        (mobius ab.val.1 : ℂ) * g (ab.val.1 * ab.val.2)) =
      ∑' d : {d : Ideal O // d ∈ idealDivisors n hn},
        (mobius (e d).val.1 : ℂ) * g ((e d).val.1 * (e d).val.2) :=
      (e.tsum_eq _).symm
    _ = ∑' d : {d : Ideal O // d ∈ idealDivisors n hn},
        (mobius d.val : ℂ) * g n := by
      apply tsum_congr
      intro d
      exact congrArg (fun z => (mobius d.val : ℂ) * g z) (e d).property
    _ = (∑ d ∈ idealDivisors n hn, (mobius d : ℂ)) * g n := by
      rw [tsum_mul_right]
      exact congrArg (fun z : ℂ => z * g n)
        (Finset.tsum_subtype (idealDivisors n hn) (fun d => (mobius d : ℂ)))
    _ = if n = 1 then g 1 else 0 := by
      rw [sum_idealDivisors_mobius_complex]
      split_ifs with h
      · subst n
        rw [one_mul]
      · rw [zero_mul]

/-- Finite ideal Möbius cancellation, with all factor pairs genuinely summable. -/
theorem ideal_mobius_factor_sum (g : Ideal O → ℂ)
    (hg : Function.HasFiniteSupport g) (hg0 : g ⊥ = 0) :
    (∑' a : Ideal O, ∑' b : Ideal O, (mobius a : ℂ) * g (a * b)) = g 1 := by
  have hfinite : Function.HasFiniteSupport (fun ab : Ideal O × Ideal O =>
      (mobius ab.1 : ℂ) * g (ab.1 * ab.2)) := by
    have hfib : ∀ n ∈ Function.support g,
        {ab : Ideal O × Ideal O | ab.1 * ab.2 = n}.Finite := by
      intro n hn
      apply finite_ideal_factor_pairs
      intro hn0
      exact hn (hn0 ▸ hg0)
    apply (hg.biUnion hfib).subset
    rintro ⟨a, b⟩ hab
    have hnonzero : g (a * b) ≠ 0 := by
      intro hzero
      exact hab (by simp only [hzero, mul_zero])
    exact Set.mem_iUnion₂.mpr ⟨a * b, hnonzero, rfl⟩
  have hs : Summable (fun ab : Ideal O × Ideal O =>
      (mobius ab.1 : ℂ) * g (ab.1 * ab.2)) := summable_of_hasFiniteSupport hfinite
  have hgroup := hs.hasSum.tsum_fiberwise
    (fun ab : Ideal O × Ideal O => ab.1 * ab.2)
  change HasSum (fun n : Ideal O =>
    ∑' ab : {ab : Ideal O × Ideal O // ab.1 * ab.2 = n},
      (mobius ab.val.1 : ℂ) * g (ab.val.1 * ab.val.2))
    (∑' ab : Ideal O × Ideal O, (mobius ab.1 : ℂ) * g (ab.1 * ab.2)) at hgroup
  simp_rw [mobius_factor_fiber g hg0] at hgroup
  exact hs.tsum_prod.symm.trans (hgroup.unique (hasSum_ite_eq (1 : Ideal O) (g 1)))

/-- Completion expressed using the actual multiplicative cube coefficient. -/
theorem completedRow_eq_cubeWeight_sum (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) (k : O) (f : Ideal O) :
    completedRow c ξ W X k f = ∑' b : Ideal O,
      cubeWeight c ξ k f b * (Real.sqrt (X / normIdeal b ^ (3 : ℕ)) : ℂ)⁻¹ *
        columnSum c ξ W (X / normIdeal b ^ (3 : ℕ)) k f := by
  rw [completedRow_eq_cube_columns c ξ hW hX k f]
  apply tsum_congr
  intro b
  by_cases hb : Outside c.S b
  · simp only [cubeWeight, if_pos hb]
  · simp only [cubeWeight, if_neg hb, zero_mul]

private theorem cubeColumn_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) (k : O) (f : Ideal O) :
    Function.HasFiniteSupport (fun b : Ideal O =>
      cubeWeight c ξ k f b * (Real.sqrt (X / normIdeal b ^ (3 : ℕ)) : ℂ)⁻¹ *
        columnSum c ξ W (X / normIdeal b ^ (3 : ℕ)) k f) := by
  apply (finite_normIdeal_le (max 1 (I.hi * X))).subset
  intro b hnonzero
  have hb : Outside c.S b := by
    by_contra hb
    exact hnonzero (by simp only [cubeWeight, if_neg hb, zero_mul])
  have hbpos := normIdeal_pos hb.1
  by_contra hbound
  have hlarge : max 1 (I.hi * X) < normIdeal b := lt_of_not_ge hbound
  have hb1 : 1 ≤ normIdeal b := (le_max_left _ _).trans hlarge.le
  have hbcube : normIdeal b ≤ normIdeal b ^ (3 : ℕ) := by
    calc
      normIdeal b = normIdeal b * 1 := (mul_one _).symm
      _ ≤ normIdeal b * normIdeal b ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hb1) hbpos.le
      _ = normIdeal b ^ (3 : ℕ) := by ring
  have hscale : I.hi * (X / normIdeal b ^ (3 : ℕ)) < 1 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (pow_pos hbpos _)).mpr
    rw [one_mul]
    exact ((le_max_right _ _).trans_lt hlarge).trans_le hbcube
  have hzero := columnSum_eq_zero_of_support_scale_lt_one hW c ξ
    (div_pos hX (pow_pos hbpos _)) hscale k f
  exact hnonzero (by simp only [hzero, mul_zero])

/-- The actual cube-completion Möbius inverse, including zeros of the twist.
Compact support supplies all required finite-support and change-of-order facts. -/
theorem columnSum_eq_mobius_completedRow (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X : ℝ} (hX : 0 < X) (k : O) (f : Ideal O) :
    (Real.sqrt X : ℂ)⁻¹ * columnSum c ξ W X k f =
      ∑' h : Ideal O, (mobius h : ℂ) * cubeWeight c ξ k f h *
        completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f := by
  let g : Ideal O → ℂ := fun b =>
    cubeWeight c ξ k f b * (Real.sqrt (X / normIdeal b ^ (3 : ℕ)) : ℂ)⁻¹ *
      columnSum c ξ W (X / normIdeal b ^ (3 : ℕ)) k f
  have hg : Function.HasFiniteSupport g := cubeColumn_hasFiniteSupport c ξ hW hX k f
  have hg0 : g ⊥ = 0 := by simp only [g, cubeWeight_bot, zero_mul]
  have hg1 : g 1 = (Real.sqrt X : ℂ)⁻¹ * columnSum c ξ W X k f := by
    simp only [g, cubeWeight_one, one_mul, normIdeal, map_one, Nat.cast_one,
      one_pow, div_one]
  rw [← hg1, ← ideal_mobius_factor_sum g hg hg0]
  apply tsum_congr
  intro h
  by_cases hh : Outside c.S h
  · have hL : 0 < X / normIdeal h ^ (3 : ℕ) :=
      div_pos hX (pow_pos (normIdeal_pos hh.1) _)
    rw [completedRow_eq_cubeWeight_sum c ξ hW hL k f, ← tsum_mul_left]
    apply tsum_congr
    intro b
    have hscale : X / normIdeal (h * b) ^ (3 : ℕ) =
        (X / normIdeal h ^ (3 : ℕ)) / normIdeal b ^ (3 : ℕ) := by
      rw [normIdeal_mul, mul_pow, div_div]
    simp only [g, cubeWeight_mul, hscale]
    ring
  · have hweight : cubeWeight c ξ k f h = 0 := by
      simp only [cubeWeight, if_neg hh]
    rw [hweight, mul_zero, zero_mul]
    calc
      _ = ∑' _b : Ideal O, (0 : ℂ) := by
        apply tsum_congr
        intro b
        simp only [g, cubeWeight_mul, hweight, zero_mul, mul_zero]
      _ = 0 := tsum_zero

end QRHShort
