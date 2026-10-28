import QRHShort.CloudSfSprimeRamifiedLocal
import QRHShort.CloudSfSprimeOrdinaryLocal
import QRHShort.SquarefreeUnitResidualCharacters
import QRHShort.SquarefreeReflectionPackets
import QRHShort.SquarefreeThetaSummability
import QRHShort.ArithmeticBasics
import QRHShort.SquarefreeRayDescent
import QRHShort.SquarefreeNumeratorPowers
import QRHShort.SquarefreePrimeSymbol
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Data.Fin.Embedding

/-! Exact exceptional-prime substitutions for the frozen prepared columns. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly.PacketConstruction

/-- The two ideal coordinates in the literal prepared-theta support. -/
structure ThetaPair where
  n : Ideal O
  b : Ideal O
  n_ne_bot : n ≠ ⊥
  n_squarefree : Squarefree n
  n_three : IsRelPrime n (principal 3)
  b_ne_bot : b ≠ ⊥
  b_three : IsRelPrime b (principal 3)

theorem thetaPair_ext {x y : ThetaPair} (hn : x.n = y.n) (hb : x.b = y.b) : x = y := by
  cases x
  cases y
  dsimp only at hn hb
  subst_vars
  rfl

abbrev UnramifiedPair (p : Ideal O) := {q : ThetaPair // IsRelPrime p q.n}
abbrev NumeratorDivisiblePair (p : Ideal O) := {q : ThetaPair // p ∣ q.n}
abbrev CubeDivisiblePair (p : Ideal O) :=
  {q : ThetaPair // IsRelPrime p q.n ∧ p ∣ q.b}

def numeratorMap {p : Ideal O} (hp : Prime p) (h3 : IsRelPrime p (principal 3))
    (q : UnramifiedPair p) : NumeratorDivisiblePair p :=
  ⟨{ n := p * q.1.n
     b := q.1.b
     n_ne_bot := mul_ne_zero hp.ne_zero q.1.n_ne_bot
     n_squarefree := squarefree_mul_iff.mpr ⟨q.2, hp.squarefree, q.1.n_squarefree⟩
     n_three := h3.mul_left q.1.n_three
     b_ne_bot := q.1.b_ne_bot
     b_three := q.1.b_three }, ⟨q.1.n, rfl⟩⟩

theorem numeratorMap_bijective {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) : Function.Bijective (numeratorMap hp h3) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply thetaPair_ext
    · exact mul_left_cancel₀ hp.ne_zero
        (congrArg (fun q : NumeratorDivisiblePair p => q.1.n) h)
    · exact congrArg (fun q : NumeratorDivisiblePair p => q.1.b) h
  · rintro ⟨q, hq⟩
    obtain ⟨n, hn⟩ := hq
    have hs : Squarefree (p * n) := hn ▸ q.n_squarefree
    have hc : IsRelPrime (p * n) (principal 3) := hn ▸ q.n_three
    have hn0 : n ≠ ⊥ := by
      intro hz
      apply q.n_ne_bot
      rw [hn, hz, Ideal.mul_bot]
    let x : UnramifiedPair p :=
      ⟨{ n := n
         b := q.b
         n_ne_bot := hn0
         n_squarefree := hs.of_mul_right
         n_three := hc.of_mul_left_right
         b_ne_bot := q.b_ne_bot
         b_three := q.b_three }, IsRelPrime.of_squarefree_mul hs⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact thetaPair_ext hn.symm rfl

def numeratorEquiv {p : Ideal O} (hp : Prime p) (h3 : IsRelPrime p (principal 3)) :
    UnramifiedPair p ≃ NumeratorDivisiblePair p :=
  Equiv.ofBijective (numeratorMap hp h3) (numeratorMap_bijective hp h3)

@[simp] theorem numeratorEquiv_n {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (q : UnramifiedPair p) :
    (numeratorEquiv hp h3 q).1.n = p * q.1.n := rfl

@[simp] theorem numeratorEquiv_b {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (q : UnramifiedPair p) :
    (numeratorEquiv hp h3 q).1.b = q.1.b := rfl

def cubeMap {p : Ideal O} (hp : Prime p) (h3 : IsRelPrime p (principal 3))
    (q : UnramifiedPair p) : CubeDivisiblePair p :=
  ⟨{ n := q.1.n
     b := p * q.1.b
     n_ne_bot := q.1.n_ne_bot
     n_squarefree := q.1.n_squarefree
     n_three := q.1.n_three
     b_ne_bot := mul_ne_zero hp.ne_zero q.1.b_ne_bot
     b_three := h3.mul_left q.1.b_three }, q.2, ⟨q.1.b, rfl⟩⟩

theorem cubeMap_bijective {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) : Function.Bijective (cubeMap hp h3) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply thetaPair_ext
    · exact congrArg (fun q : CubeDivisiblePair p => q.1.n) h
    · exact mul_left_cancel₀ hp.ne_zero
        (congrArg (fun q : CubeDivisiblePair p => q.1.b) h)
  · rintro ⟨q, hcop, hq⟩
    obtain ⟨b, hb⟩ := hq
    have hc : IsRelPrime (p * b) (principal 3) := hb ▸ q.b_three
    have hb0 : b ≠ ⊥ := by
      intro hz
      apply q.b_ne_bot
      rw [hb, hz, Ideal.mul_bot]
    let x : UnramifiedPair p :=
      ⟨{ n := q.n
         b := b
         n_ne_bot := q.n_ne_bot
         n_squarefree := q.n_squarefree
         n_three := q.n_three
         b_ne_bot := hb0
         b_three := hc.of_mul_left_right }, hcop⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact thetaPair_ext rfl hb.symm

def cubeEquiv {p : Ideal O} (hp : Prime p) (h3 : IsRelPrime p (principal 3)) :
    UnramifiedPair p ≃ CubeDivisiblePair p :=
  Equiv.ofBijective (cubeMap hp h3) (cubeMap_bijective hp h3)

@[simp] theorem cubeEquiv_n {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (q : UnramifiedPair p) :
    (cubeEquiv hp h3 q).1.n = q.1.n := rfl

@[simp] theorem cubeEquiv_b {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (q : UnramifiedPair p) :
    (cubeEquiv hp h3 q).1.b = p * q.1.b := rfl

theorem numerator_substitution {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (F : ThetaPair → ℂ) :
    (∑' q : NumeratorDivisiblePair p, F q.1) =
      ∑' q : UnramifiedPair p, F (numeratorMap hp h3 q).1 :=
  ((numeratorEquiv hp h3).tsum_eq (fun q : NumeratorDivisiblePair p => F q.1)).symm

theorem cube_substitution {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (F : ThetaPair → ℂ) :
    (∑' q : CubeDivisiblePair p, F q.1) =
      ∑' q : UnramifiedPair p, F (cubeMap hp h3 q).1 :=
  ((cubeEquiv hp h3).tsum_eq (fun q : CubeDivisiblePair p => F q.1)).symm

theorem numerator_substitution_summable {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (F : ThetaPair → ℂ)
    (hF : Summable (fun q => ‖F q‖)) :
    Summable (fun q : UnramifiedPair p => ‖F (numeratorMap hp h3 q).1‖) :=
  (numeratorEquiv hp h3).summable_iff.mpr (hF.subtype (fun q => p ∣ q.n))

theorem cube_substitution_summable {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (F : ThetaPair → ℂ)
    (hF : Summable (fun q => ‖F q‖)) :
    Summable (fun q : UnramifiedPair p => ‖F (cubeMap hp h3 q).1‖) :=
  (cubeEquiv hp h3).summable_iff.mpr
    (hF.subtype (fun q => IsRelPrime p q.n ∧ p ∣ q.b))

/-- The divisor indicators are disjoint after the numerator branch is
removed, so there is no extra restriction on the new cube coordinate. -/
def exceptionalMultiplier (p : Ideal O) (q : ThetaPair) : ℂ :=
  -(Real.sqrt (normIdeal p) : ℂ)⁻¹ +
    if p ∣ q.n ∨ p ∣ q.b then (Real.sqrt (normIdeal p) : ℂ) else 0

theorem exceptionalMultiplier_split {p : Ideal O} (hp : Prime p) (q : ThetaPair) :
    exceptionalMultiplier p q = -(Real.sqrt (normIdeal p) : ℂ)⁻¹ +
      (if p ∣ q.n then (Real.sqrt (normIdeal p) : ℂ) else 0) +
      (if IsRelPrime p q.n ∧ p ∣ q.b then (Real.sqrt (normIdeal p) : ℂ) else 0) := by
  have hcop : IsRelPrime p q.n ↔ ¬ p ∣ q.n := hp.irreducible.isRelPrime_iff_not_dvd
  by_cases hn : p ∣ q.n <;> by_cases hb : p ∣ q.b <;>
    simp [exceptionalMultiplier, hcop, hn, hb]

/-- The complete three-branch reindexing is used only with genuine absolute
summability. In particular the two positive branches are disjoint. -/
theorem exceptional_substitution {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (F : ThetaPair → ℂ)
    (hF : Summable (fun q => ‖F q‖)) :
    (∑' q : ThetaPair, exceptionalMultiplier p q * F q) =
      -(Real.sqrt (normIdeal p) : ℂ)⁻¹ * (∑' q : ThetaPair, F q) +
      (Real.sqrt (normIdeal p) : ℂ) *
        (∑' q : UnramifiedPair p, F (numeratorMap hp h3 q).1) +
      (Real.sqrt (normIdeal p) : ℂ) *
        (∑' q : UnramifiedPair p, F (cubeMap hp h3 q).1) := by
  let f₁ : ThetaPair → ℂ := fun q => if p ∣ q.n then F q else 0
  let f₂ : ThetaPair → ℂ := fun q =>
    if IsRelPrime p q.n ∧ p ∣ q.b then F q else 0
  have hind₁ : ({q : ThetaPair | p ∣ q.n}.indicator F) = f₁ := by
    funext q
    exact Set.indicator_apply _ _ _
  have hind₂ : ({q : ThetaPair | IsRelPrime p q.n ∧ p ∣ q.b}.indicator F) = f₂ := by
    funext q
    exact Set.indicator_apply _ _ _
  have hs₁ : Summable f₁ := by
    rw [← hind₁]
    exact hF.of_norm.indicator {q | p ∣ q.n}
  have hs₂ : Summable f₂ := by
    rw [← hind₂]
    exact hF.of_norm.indicator {q | IsRelPrime p q.n ∧ p ∣ q.b}
  have hsum₁ : (∑' q, f₁ q) = ∑' q : UnramifiedPair p, F (numeratorMap hp h3 q).1 := by
    rw [← numerator_substitution hp h3 F]
    have h := tsum_subtype {q : ThetaPair | p ∣ q.n} F
    simp_rw [hind₁] at h
    exact h.symm
  have hsum₂ : (∑' q, f₂ q) = ∑' q : UnramifiedPair p, F (cubeMap hp h3 q).1 := by
    rw [← cube_substitution hp h3 F]
    have h := tsum_subtype {q : ThetaPair | IsRelPrime p q.n ∧ p ∣ q.b} F
    simp_rw [hind₂] at h
    exact h.symm
  calc
    _ = ∑' q : ThetaPair,
        ((-(Real.sqrt (normIdeal p) : ℂ)⁻¹ * F q +
          (Real.sqrt (normIdeal p) : ℂ) * f₁ q) +
          (Real.sqrt (normIdeal p) : ℂ) * f₂ q) := by
      apply tsum_congr
      intro q
      rw [exceptionalMultiplier_split hp]
      dsimp only [f₁, f₂]
      split_ifs <;> ring
    _ = _ := by
      rw [((hF.of_norm.mul_left _).add (hs₁.mul_left _)).tsum_add (hs₂.mul_left _),
        (hF.of_norm.mul_left _).tsum_add (hs₁.mul_left _),
        tsum_mul_left, tsum_mul_left, tsum_mul_left, hsum₁, hsum₂]


/-! The following selection is made from the literal cusp support. It has no
row ideal, character, test function, or analytic scale as a parameter. -/

open SquarefreeReflection.RayValuePrerequisites in
theorem primary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) : u = 1 := by
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

open SquarefreeReflection.RayValuePrerequisites in
theorem primary_eq_of_principal_eq {a b : O}
    (ha : IsPrimary a) (hb : IsPrimary b) (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [primary_unit_eq_one u hup, Units.val_one, mul_one] using hu

theorem primaryGenerator_principal {n : O} (hn : IsPrimary n) :
    primaryGenerator (principal n) = n := by
  have hex : ∃ z : O, principal z = principal n ∧ IsPrimary z := ⟨n, rfl, hn⟩
  have hs : principal (primaryGenerator (principal n)) = principal n ∧
      IsPrimary (primaryGenerator (principal n)) := by
    simpa only [primaryGenerator, dite_eq_left hex] using Classical.choose_spec hex
  exact primary_eq_of_principal_eq hs.2 hn hs.1

open SquarefreeReflection.RayValuePrerequisites in
theorem primary_principal_three {n : O} (hn : IsPrimary n) :
    IsRelPrime (principal n) (principal 3) := by
  apply IsCoprime.isRelPrime
  apply (Ideal.isCoprime_span_singleton_iff n (3 : O)).mpr
  obtain ⟨t, ht⟩ := (isPrimary_iff_three_dvd n).mp hn
  refine ⟨1, -t, ?_⟩
  linear_combination ht

def primaryPair (n b : O) (h : PrimaryCubeData n b) : ThetaPair where
  n := principal n
  b := principal b
  n_ne_bot := fun hz => h.1 (Ideal.span_singleton_eq_bot.mp hz)
  n_squarefree := h.2.2.2.2
  n_three := primary_principal_three h.2.2.1
  b_ne_bot := fun hz => h.2.1 (Ideal.span_singleton_eq_bot.mp hz)
  b_three := primary_principal_three h.2.2.2.1

def omegaUnit : Oˣ :=
  ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
    (by decide)).unit

def unitSlot (i : Fin 6) : Oˣ :=
  ![1, -1, omegaUnit, -omegaUnit, omegaUnit ^ 2, -omegaUnit ^ 2] i

theorem unitSlot_surjective : Function.Surjective unitSlot := by
  intro u
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem
    (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
  change u ∈ [1, -1, omegaUnit, -omegaUnit, omegaUnit ^ 2, -omegaUnit ^ 2] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩
  · exact ⟨3, h.symm⟩
  · exact ⟨4, h.symm⟩
  · exact ⟨5, h.symm⟩

theorem lambda_ne_zero : lambda ≠ 0 := by
  have hs : lambda ^ 2 = (-3 : O) := by
    unfold lambda
    linear_combination 4 * SquarefreeReflection.RayValuePrerequisites.omega_sq_add_omega_add_one
  intro hz
  rw [hz] at hs
  norm_num at hs

abbrev ThetaIndex := Fin 6 × ℕ × ThetaPair

def indexMode (i : ThetaIndex) : O :=
  (unitSlot i.1 : O) * lambda ^ i.2.1 *
    (primaryGenerator i.2.2.n * primaryGenerator i.2.2.b ^ 3)

def latticeFrequency (z : O) : ℂ := embedding lambda ^ (-4 : ℤ) * embedding z

abbrev CuspSupport (σ : ThetaCusp) :=
  {z : O // z ≠ 0 ∧ cuspCoefficient σ (latticeFrequency z) ≠ 0}

/-- Every actual supported lattice mode has an ideal-indexed representation
with one of the six unit slots and the frozen lower exponent shift. -/
theorem indexMode_surjective_on_support (hB : ThetaBoundsStatement) (σ : ThetaCusp)
    (z : CuspSupport σ) : ∃ i : ThetaIndex, indexMode i = z.1 := by
  obtain ⟨u, m, n, b, hm, hnb, he⟩ := hB.1 σ (latticeFrequency z.1) z.2.2
  obtain ⟨j, hj⟩ := unitSlot_surjective u
  let r : ℕ := (m + 4).toNat
  have hr : (r : ℤ) = m + 4 := Int.toNat_of_nonneg (by omega)
  have hm' : m = (r : ℤ) - 4 := by omega
  refine ⟨(j, r, primaryPair n b hnb), ?_⟩
  have hLam : embedding lambda ≠ 0 := embedding_eq_zero.not.mpr lambda_ne_zero
  apply embedding_injective
  have him : embedding (indexMode (j, r, primaryPair n b hnb)) =
      embedding (u : O) * embedding lambda ^ r * embedding (n * b ^ 3) := by
    simp only [indexMode, primaryPair, hj, primaryGenerator_principal hnb.2.2.1,
      primaryGenerator_principal hnb.2.2.2.1, embedding_mul, embedding_pow]
  rw [him]
  unfold latticeFrequency at he
  simp only [hm', zpow_sub₀ hLam, zpow_natCast, zpow_ofNat, zpow_neg] at he
  apply mul_right_cancel₀ (inv_ne_zero (pow_ne_zero 4 hLam))
  calc
    (embedding (u : O) * embedding lambda ^ r * embedding (n * b ^ 3)) *
        (embedding lambda ^ 4)⁻¹ =
        embedding (u : O) * (embedding lambda ^ r / embedding lambda ^ 4) *
          embedding (n * b ^ 3) := by ring
    _ = (embedding lambda ^ 4)⁻¹ * embedding z.1 := he.symm
    _ = embedding z.1 * (embedding lambda ^ 4)⁻¹ := mul_comm _ _

/-- This choice is independent of every row ideal and of every test function. -/
def supportLabel (hB : ThetaBoundsStatement) (σ : ThetaCusp)
    (z : CuspSupport σ) : ThetaIndex :=
  Classical.choose (indexMode_surjective_on_support hB σ z)

@[simp] theorem indexMode_supportLabel (hB : ThetaBoundsStatement) (σ : ThetaCusp)
    (z : CuspSupport σ) : indexMode (supportLabel hB σ z) = z.1 :=
  Classical.choose_spec (indexMode_surjective_on_support hB σ z)

theorem supportLabel_injective (hB : ThetaBoundsStatement) (σ : ThetaCusp) :
    Function.Injective (supportLabel hB σ) := by
  intro x y h
  apply Subtype.ext
  simpa only [indexMode_supportLabel] using congrArg indexMode h

def selectedIndices (hB : ThetaBoundsStatement) (σ : ThetaCusp) : Set ThetaIndex :=
  Set.range (supportLabel hB σ)

def supportEquivSelected (hB : ThetaBoundsStatement) (σ : ThetaCusp) :
    CuspSupport σ ≃ selectedIndices hB σ :=
  Equiv.ofInjective (supportLabel hB σ) (supportLabel_injective hB σ)

theorem selectedIndices_iff (hB : ThetaBoundsStatement) (σ : ThetaCusp)
    (i : ThetaIndex) : i ∈ selectedIndices hB σ ↔
      ∃ h : indexMode i ≠ 0 ∧ cuspCoefficient σ (latticeFrequency (indexMode i)) ≠ 0,
        supportLabel hB σ ⟨indexMode i, h⟩ = i := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨by simpa only [indexMode_supportLabel] using z.2, ?_⟩
    congr 1
    exact Subtype.ext (indexMode_supportLabel hB σ z)
  · rintro ⟨h, hi⟩
    exact ⟨⟨indexMode i, h⟩, hi⟩

/-- The mask keeps one representative of every nonzero cusp-supported mode;
its definition has no dependence on a row ideal. This is a bijective transport,
not a rearrangement of a conditionally convergent family. -/
theorem support_tsum_eq_selected (hB : ThetaBoundsStatement) (σ : ThetaCusp)
    (F : O → ℂ) :
    (∑' z : CuspSupport σ, F z.1) =
      ∑' i : ThetaIndex, if i ∈ selectedIndices hB σ then F (indexMode i) else 0 := by
  calc
    _ = ∑' i : selectedIndices hB σ, F (indexMode i.1) := by
      have h := tsum_range (fun i : ThetaIndex => F (indexMode i))
        (supportLabel_injective hB σ)
      simp only [indexMode_supportLabel] at h
      exact h.symm
    _ = _ := by
      have h := tsum_subtype (selectedIndices hB σ) (fun i : ThetaIndex => F (indexMode i))
      exact h.trans (tsum_congr (fun i => Set.indicator_apply _ _ _))

theorem support_summable_selected (hB : ThetaBoundsStatement) (σ : ThetaCusp)
    (F : O → ℂ) (hF : Summable (fun z : CuspSupport σ => ‖F z.1‖)) :
    Summable (fun i : ThetaIndex =>
      if i ∈ selectedIndices hB σ then ‖F (indexMode i)‖ else 0) := by
  have hs : Summable (fun i : selectedIndices hB σ => ‖F (indexMode i.1)‖) := by
    apply (supportEquivSelected hB σ).summable_iff.mp
    change Summable (fun z : CuspSupport σ => ‖F (indexMode (supportLabel hB σ z))‖)
    simpa only [indexMode_supportLabel] using hF
  have hi : Summable ((selectedIndices hB σ).indicator
      (fun i : ThetaIndex => ‖F (indexMode i)‖)) :=
    summable_subtype_iff_indicator.mp hs
  exact hi.congr (fun i => Set.indicator_apply _ _ _)



/-! Literal norm and primary-generator identities used by the row-independent
column amplitudes. -/

theorem norm_embedding_sq (a : O) : ‖embedding a‖ ^ 2 = normElement a := by
  open NumberField NumberField.InfinitePlace
    IsCyclotomicExtension.Rat in
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces,
      nrRealPlaces_eq_zero (n := 3) K (by decide), zero_add,
      nrComplexPlaces_eq_totient_div_two (n := 3)]
    rfl
  letI : Subsingleton (NumberField.InfinitePlace K) :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  letI : NumberField.IsTotallyComplex K :=
    IsCyclotomicExtension.Rat.isTotallyComplex K (n := 3) (by decide)
  let w := NumberField.InfinitePlace.mk rawEmbedding.toRingHom
  have hw : NumberField.InfinitePlace.mult w = 2 :=
    (NumberField.IsTotallyComplex.isComplex w).mult_eq_two
  have hnorm := NumberField.InfinitePlace.prod_eq_abs_norm (a : K)
  rw [Fintype.prod_subsingleton _ w, hw] at hnorm
  have he : ‖embedding a‖ = w (a : K) := by
    unfold embedding w
    split_ifs <;> simp [NumberField.InfinitePlace.apply]
  rw [he, hnorm]
  simp only [normElement, normIdeal, principal, Ideal.absNorm_span_singleton,
    ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast, Nat.cast_natAbs, Int.cast_abs]

open SquarefreeReflection.RayValuePrerequisites in
theorem primaryGenerator_spec_three {a : Ideal O}
    (h3 : IsRelPrime a (principal 3)) :
    principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) := by
  let z : O := idealGenerator a
  have hz : principal z = a := Ideal.span_singleton_generator a
  have hnot : ¬ omega - 1 ∣ z := by
    intro hd
    have hda : principal (omega - 1) ∣ a := by
      rw [← hz]
      exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hd
    have hd3 : principal (omega - 1) ∣ principal 3 :=
      Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr omega_sub_one_dvd_three
    have hi : principal (omega - 1) = ⊤ := Ideal.isUnit_iff.mp (h3 hda hd3)
    exact omega_sub_one_prime.not_unit (Ideal.span_singleton_eq_top.mp hi)
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  have hex : ∃ v : O, principal v = a ∧ IsPrimary v := by
    refine ⟨(u : O) * z, ?_, hu⟩
    change Ideal.span {(u : O) * z} = a
    rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit]
    simpa only [Ideal.top_mul, principal] using hz
  simpa only [primaryGenerator, dite_eq_left hex] using Classical.choose_spec hex

open SquarefreeReflection.RayValuePrerequisites in
theorem primary_mul {a b : O} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  apply (isPrimary_iff_three_dvd _).mpr
  have h := dvd_add (dvd_mul_of_dvd_left ((isPrimary_iff_three_dvd a).mp ha) b)
    ((isPrimary_iff_three_dvd b).mp hb)
  convert h using 1 <;> ring

theorem primaryGenerator_mul_three {a b : Ideal O}
    (ha : IsRelPrime a (principal 3)) (hb : IsRelPrime b (principal 3)) :
    primaryGenerator (a * b) = primaryGenerator a * primaryGenerator b := by
  have ha' := primaryGenerator_spec_three ha
  have hb' := primaryGenerator_spec_three hb
  have hab' := primaryGenerator_spec_three (ha.mul_left hb)
  apply primary_eq_of_principal_eq hab'.2 (primary_mul ha'.2 hb'.2)
  rw [hab'.1]
  change a * b = Ideal.span {primaryGenerator a * primaryGenerator b}
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact congrArg₂ (· * ·) ha'.1.symm hb'.1.symm

theorem norm_primaryGenerator (q : ThetaPair) :
    ‖embedding (primaryGenerator q.n)‖ = Real.sqrt (normIdeal q.n) ∧
    ‖embedding (primaryGenerator q.b)‖ = Real.sqrt (normIdeal q.b) := by
  constructor
  · rw [← Real.sqrt_sq (norm_nonneg (embedding (primaryGenerator q.n))), norm_embedding_sq]
    congr 1
    exact congrArg normIdeal (primaryGenerator_spec_three q.n_three).1
  · rw [← Real.sqrt_sq (norm_nonneg (embedding (primaryGenerator q.b))), norm_embedding_sq]
    congr 1
    exact congrArg normIdeal (primaryGenerator_spec_three q.b_three).1

theorem index_primary_data (q : ThetaPair) :
    PrimaryCubeData (primaryGenerator q.n) (primaryGenerator q.b) := by
  have hn := primaryGenerator_spec_three q.n_three
  have hb := primaryGenerator_spec_three q.b_three
  refine ⟨?_, ?_, hn.2, hb.2, ?_⟩
  · intro h
    apply q.n_ne_bot
    rw [← hn.1, h]
    simp [principal]
  · intro h
    apply q.b_ne_bot
    rw [← hb.1, h]
    simp [principal]
  · rw [hn.1]
    exact q.n_squarefree

theorem norm_unitSlot (j : Fin 6) : ‖embedding (unitSlot j : O)‖ = 1 := by
  have hω : (omegaUnit : O) = omega := IsUnit.unit_spec _
  fin_cases j <;>
    simp [unitSlot, hω, embedding_neg, embedding_one, embedding_pow, norm_embedding_omega]

theorem norm_embedding_lambda : ‖embedding lambda‖ = Real.sqrt 3 := by
  have hs : lambda ^ 2 = (-3 : O) := by
    unfold lambda
    linear_combination 4 * SquarefreeReflection.RayValuePrerequisites.omega_sq_add_omega_add_one
  have hc := congrArg (fun a : O => ‖embedding a‖) hs
  have hm : embedding (-3 : O) = (-3 : ℂ) := by
    simpa only [map_ofNat, embeddingHom_apply] using map_neg embeddingHom (3 : O)
  rw [embedding_pow, norm_pow, hm] at hc
  norm_num at hc
  rw [← Real.sqrt_sq (norm_nonneg (embedding lambda)), hc]

theorem latticeFrequency_indexMode (i : ThetaIndex) :
    latticeFrequency (indexMode i) =
      embedding (unitSlot i.1 : O) * embedding lambda ^ ((i.2.1 : ℤ) - 4) *
        embedding (primaryGenerator i.2.2.n * primaryGenerator i.2.2.b ^ 3) := by
  have hLam : embedding lambda ≠ 0 := embedding_eq_zero.not.mpr lambda_ne_zero
  simp only [latticeFrequency, indexMode, embedding_mul, embedding_pow,
    zpow_sub₀ hLam, zpow_natCast, zpow_ofNat, zpow_neg, div_eq_mul_inv]
  ring

theorem cusp_bound_indexMode (hB : ThetaBoundsStatement) (σ : ThetaCusp)
    (i : ThetaIndex) :
    ‖cuspCoefficient σ (latticeFrequency (indexMode i))‖ ≤
      27 * (3 : ℝ) ^ ((((i.2.1 : ℤ) - 4 : ℤ) : ℝ) / 6) *
        Real.sqrt (normIdeal i.2.2.b) := by
  rw [latticeFrequency_indexMode]
  simpa only [(norm_primaryGenerator i.2.2).2] using
    hB.2.1 σ (unitSlot i.1) ((i.2.1 : ℤ) - 4)
      (primaryGenerator i.2.2.n) (primaryGenerator i.2.2.b)
      (by omega) (index_primary_data i.2.2)

theorem normIdeal_pos {a : Ideal O} (ha : a ≠ ⊥) : 0 < normIdeal a := by
  change (0 : ℝ) < (a.absNorm : ℝ)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ha)

theorem norm_latticeFrequency_indexMode (i : ThetaIndex) :
    ‖latticeFrequency (indexMode i)‖ =
      (3 : ℝ) ^ ((((i.2.1 : ℤ) - 4 : ℤ) : ℝ) / 2) *
        Real.sqrt (normIdeal i.2.2.n) * Real.sqrt (normIdeal i.2.2.b) ^ 3 := by
  rw [latticeFrequency_indexMode, norm_mul, norm_mul, norm_unitSlot, one_mul,
    norm_zpow, norm_embedding_lambda, embedding_mul, embedding_pow, norm_mul, norm_pow,
    (norm_primaryGenerator i.2.2).1, (norm_primaryGenerator i.2.2).2,
    ← Real.rpow_intCast, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have he : (1 / (2 : ℝ)) * (((i.2.1 : ℤ) - 4 : ℤ) : ℝ) =
      ((((i.2.1 : ℤ) - 4 : ℤ) : ℝ) / 2) := by ring
  rw [he]
  ring

theorem norm_latticeFrequency_pos (i : ThetaIndex) :
    0 < ‖latticeFrequency (indexMode i)‖ := by
  rw [norm_latticeFrequency_indexMode]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.sqrt_pos.mpr (normIdeal_pos i.2.2.n_ne_bot)))
    (pow_pos (Real.sqrt_pos.mpr (normIdeal_pos i.2.2.b_ne_bot)) _)

def columnDenominator (i : ThetaIndex) : ℝ :=
  (3 : ℝ) ^ ((((i.2.1 : ℤ) - 4 : ℤ) : ℝ) / 3) *
    Real.sqrt (normIdeal i.2.2.n) * normIdeal i.2.2.b

theorem columnDenominator_pos (i : ThetaIndex) : 0 < columnDenominator i := by
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.sqrt_pos.mpr (normIdeal_pos i.2.2.n_ne_bot)))
    (normIdeal_pos i.2.2.b_ne_bot)

/-- The actual cusp coefficient, angular factor and datum phase, expressed in
exactly the denominator used by the frozen prepared series. -/
def normalizedCuspColumn (d : ReflectionDatum) (i : ThetaIndex) : ℂ :=
  (columnDenominator i : ℂ) * cuspCoefficient d.cusp (latticeFrequency (indexMode i)) *
    (latticeFrequency (indexMode i) / (‖latticeFrequency (indexMode i)‖ : ℂ)) /
      (‖latticeFrequency (indexMode i)‖ : ℂ) * d.phase (indexMode i)

theorem normalizedCuspColumn_norm_le (hB : ThetaBoundsStatement)
    (d : ReflectionDatum) (i : ThetaIndex) : ‖normalizedCuspColumn d i‖ ≤ 27 := by
  have hden := columnDenominator_pos i
  have hell := norm_latticeFrequency_pos i
  have hnorm : ‖normalizedCuspColumn d i‖ =
      columnDenominator i * ‖cuspCoefficient d.cusp (latticeFrequency (indexMode i))‖ /
        ‖latticeFrequency (indexMode i)‖ := by
    simp only [normalizedCuspColumn, norm_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hden.le, abs_of_nonneg (norm_nonneg _),
      div_self hell.ne', mul_one, d.phase_norm]
  rw [hnorm, div_le_iff₀ hell]
  calc
    _ ≤ columnDenominator i *
        (27 * (3 : ℝ) ^ ((((i.2.1 : ℤ) - 4 : ℤ) : ℝ) / 6) *
          Real.sqrt (normIdeal i.2.2.b)) :=
      mul_le_mul_of_nonneg_left (cusp_bound_indexMode hB d.cusp i) hden.le
    _ = 27 * ‖latticeFrequency (indexMode i)‖ := by
      rw [norm_latticeFrequency_indexMode]
      let m : ℝ := (((i.2.1 : ℤ) - 4 : ℤ) : ℝ)
      have hp : (3 : ℝ) ^ (m / 3) * 3 ^ (m / 6) = 3 ^ (m / 2) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
      have hsq := Real.sq_sqrt (normIdeal_pos i.2.2.b_ne_bot).le
      change (3 ^ (m / 3) * Real.sqrt (normIdeal i.2.2.n) * normIdeal i.2.2.b) *
        (27 * 3 ^ (m / 6) * Real.sqrt (normIdeal i.2.2.b)) = _
      calc
        _ = 27 * (3 ^ (m / 3) * 3 ^ (m / 6)) *
            Real.sqrt (normIdeal i.2.2.n) * Real.sqrt (normIdeal i.2.2.b) ^ 3 := by
          nth_rw 1 [← hsq]
          ring
        _ = _ := by rw [hp]; ring

theorem normalizedCuspColumn_div (d : ReflectionDatum) (i : ThetaIndex) :
    normalizedCuspColumn d i / (columnDenominator i : ℂ) =
      cuspCoefficient d.cusp (latticeFrequency (indexMode i)) *
        (latticeFrequency (indexMode i) / (‖latticeFrequency (indexMode i)‖ : ℂ)) /
          (‖latticeFrequency (indexMode i)‖ : ℂ) * d.phase (indexMode i) := by
  have hd : (columnDenominator i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (columnDenominator_pos i).ne'
  unfold normalizedCuspColumn
  field_simp
  <;> ring

theorem normSq_latticeFrequency_indexMode (i : ThetaIndex) :
    Complex.normSq (latticeFrequency (indexMode i)) =
      (3 : ℝ) ^ ((((i.2.1 : ℤ) - 4 : ℤ) : ℝ)) *
        normIdeal i.2.2.n * normIdeal i.2.2.b ^ 3 := by
  rw [Complex.normSq_eq_norm_sq, norm_latticeFrequency_indexMode]
  let m : ℝ := (((i.2.1 : ℤ) - 4 : ℤ) : ℝ)
  have hp : ((3 : ℝ) ^ (m / 2)) ^ (2 : ℕ) = 3 ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    norm_num
  calc
    _ = (3 ^ (m / 2)) ^ 2 * Real.sqrt (normIdeal i.2.2.n) ^ 2 *
        (Real.sqrt (normIdeal i.2.2.b) ^ 2) ^ 3 := by ring
    _ = _ := by
      rw [hp, Real.sq_sqrt (normIdeal_pos i.2.2.n_ne_bot).le,
        Real.sq_sqrt (normIdeal_pos i.2.2.b_ne_bot).le]

theorem normElement_mul (a b : O) :
    normElement (a * b) = normElement a * normElement b := by
  simp only [normElement, principal, ← Ideal.span_singleton_mul_span_singleton,
    normIdeal, map_mul, Nat.cast_mul]

theorem normElement_prod {ι : Type*} (s : Finset ι) (f : ι → O) :
    normElement (∏ i ∈ s, f i) = ∏ i ∈ s, normElement (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normElement, principal, normIdeal]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, normElement_mul, ih]

theorem normElement_reflectionDenominator (d : ReflectionDatum)
    (A : Finset (Ideal O)) (hA : ∀ a ∈ A, IsRelPrime a (principal 3)) :
    normElement (reflectionDenominator d A) =
      normElement d.denominator * ∏ a ∈ A, normIdeal a := by
  rw [reflectionDenominator, normElement_mul, normElement_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  exact congrArg normIdeal (primaryGenerator_spec_three (hA a ha)).1

/-- The literal scale change used before the exceptional-prime substitutions. -/
theorem dual_scale_identity (v N A H X Nk : ℝ)
    (hN : N ≠ 0) (hA : A ≠ 0) (hH : H ≠ 0) (hX : X ≠ 0) :
    v * X / (N * A * Nk) ^ 2 =
      v * H ^ 2 / ((N ^ 2 * H ^ 2 / X * A ^ 2) * Nk ^ 2) := by
  by_cases hk : Nk = 0
  · simp [hk]
  · field_simp
    <;> ring


theorem indexMode_ne_zero (i : ThetaIndex) : indexMode i ≠ 0 := by
  intro hz
  have h := norm_latticeFrequency_pos i
  simp only [latticeFrequency, hz, embedding_zero, mul_zero, norm_zero] at h
  exact lt_irrefl _ h

def indexedDualTerm (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (V : ℝ → ℂ) (X : ℝ) (i : ThetaIndex) : ℂ :=
  normalizedCuspColumn d i / (columnDenominator i : ℂ) *
    (∏ p ∈ A, thetaLocalFactor p (j p) (indexMode i)) *
    thetaWeight V (Complex.normSq (latticeFrequency (indexMode i)) * X /
      normElement (reflectionDenominator d A) ^ 2)

/-- An exact bijection on the nonzero support of the literal dual theta sum.
The choice of the retained index depends only on the cusp and the mode. -/
theorem dualThetaSum_eq_selected (hB : ThetaBoundsStatement)
    (d : ReflectionDatum) (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (V : ℝ → ℂ) (X : ℝ) :
    dualThetaSum d A j V X =
      ∑' i : ThetaIndex, if i ∈ selectedIndices hB d.cusp then
        indexedDualTerm d A j V X i else 0 := by
  let F : O → ℂ := fun z => if z = 0 then 0 else
    cuspCoefficient d.cusp (latticeFrequency z) *
      (latticeFrequency z / (‖latticeFrequency z‖ : ℂ)) /
        (‖latticeFrequency z‖ : ℂ) * d.phase z *
      (∏ p ∈ A, thetaLocalFactor p (j p) z) *
      thetaWeight V (Complex.normSq (latticeFrequency z) * X /
        normElement (reflectionDenominator d A) ^ 2)
  have hsup : Function.support F ⊆
      {z | z ≠ 0 ∧ cuspCoefficient d.cusp (latticeFrequency z) ≠ 0} := by
    intro z hz
    constructor
    · intro hz0
      exact hz (by simp [F, hz0])
    · intro hc0
      exact hz (by simp [F, hc0])
  calc
    _ = ∑' z : CuspSupport d.cusp, F z.1 :=
      (tsum_subtype_eq_of_support_subset hsup).symm
    _ = ∑' i : ThetaIndex, if i ∈ selectedIndices hB d.cusp then
        F (indexMode i) else 0 := support_tsum_eq_selected hB d.cusp F
    _ = _ := by
      apply tsum_congr
      intro i
      by_cases hi : i ∈ selectedIndices hB d.cusp
      · simp only [hi, ite_true, F, indexMode_ne_zero, ite_false,
          indexedDualTerm, normalizedCuspColumn_div]
      · simp only [hi, ite_false]

abbrev SubstitutedPair (D E : Ideal O) :=
  {q : ThetaPair // IsRelPrime D q.n ∧ IsRelPrime E q.n}
abbrev DivisiblePair (D E : Ideal O) :=
  {q : ThetaPair // D ∣ q.n ∧ E ∣ q.b ∧ IsRelPrime E q.n}

/-- All numerator and cube branches can be applied simultaneously. Distinct
exceptional primes give the required relative primeness of D and E. -/
def pairSubstitution {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) (q : SubstitutedPair D E) : DivisiblePair D E :=
  ⟨{ n := D * q.1.n
     b := E * q.1.b
     n_ne_bot := mul_ne_zero hD0 q.1.n_ne_bot
     n_squarefree := squarefree_mul_iff.mpr ⟨q.2.1, hD, q.1.n_squarefree⟩
     n_three := hD3.mul_left q.1.n_three
     b_ne_bot := mul_ne_zero hE0 q.1.b_ne_bot
     b_three := hE3.mul_left q.1.b_three },
   ⟨⟨q.1.n, rfl⟩, ⟨q.1.b, rfl⟩, hED.mul_right q.2.2⟩⟩

theorem pairSubstitution_bijective {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) :
    Function.Bijective (pairSubstitution hD hD0 hE0 hD3 hE3 hED) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply thetaPair_ext
    · exact mul_left_cancel₀ hD0
        (congrArg (fun q : DivisiblePair D E => q.1.n) h)
    · exact mul_left_cancel₀ hE0
        (congrArg (fun q : DivisiblePair D E => q.1.b) h)
  · rintro ⟨q, hDn, hEb, hEn⟩
    obtain ⟨n, hn⟩ := hDn
    obtain ⟨b, hb⟩ := hEb
    have hs : Squarefree (D * n) := hn ▸ q.n_squarefree
    have hn3 : IsRelPrime (D * n) (principal 3) := hn ▸ q.n_three
    have hb3 : IsRelPrime (E * b) (principal 3) := hb ▸ q.b_three
    have hn0 : n ≠ ⊥ := by
      intro hz
      apply q.n_ne_bot
      rw [hn, hz, Ideal.mul_bot]
    have hb0 : b ≠ ⊥ := by
      intro hz
      apply q.b_ne_bot
      rw [hb, hz, Ideal.mul_bot]
    let x : SubstitutedPair D E :=
      ⟨{ n := n
         b := b
         n_ne_bot := hn0
         n_squarefree := (squarefree_mul_iff.mp hs).2.2
         n_three := hn3.of_mul_left_right
         b_ne_bot := hb0
         b_three := hb3.of_mul_left_right },
       ⟨(squarefree_mul_iff.mp hs).1, (hn ▸ hEn).of_mul_right_right⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact thetaPair_ext hn.symm hb.symm

def pairSubstitutionEquiv {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) : SubstitutedPair D E ≃ DivisiblePair D E :=
  Equiv.ofBijective (pairSubstitution hD hD0 hE0 hD3 hE3 hED)
    (pairSubstitution_bijective hD hD0 hE0 hD3 hE3 hED)

theorem pair_substitution_tsum {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) (F : ThetaPair → ℂ) :
    (∑' q : DivisiblePair D E, F q.1) =
      ∑' q : SubstitutedPair D E,
        F (pairSubstitution hD hD0 hE0 hD3 hE3 hED q).1 :=
  ((pairSubstitutionEquiv hD hD0 hE0 hD3 hE3 hED).tsum_eq
    (fun q : DivisiblePair D E => F q.1)).symm

theorem pair_substitution_summable {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) (F : ThetaPair → ℂ)
    (hF : Summable (fun q => ‖F q‖)) :
    Summable (fun q : SubstitutedPair D E =>
      ‖F (pairSubstitution hD hD0 hE0 hD3 hE3 hED q).1‖) :=
  (pairSubstitutionEquiv hD hD0 hE0 hD3 hE3 hED).summable_iff.mpr
    (hF.subtype (fun q => D ∣ q.n ∧ E ∣ q.b ∧ IsRelPrime E q.n))


/-! Finite expansion of all exceptional local factors. -/

def exceptionalBranch (p : Ideal O) (b : Fin 3) (q : ThetaPair) : ℂ :=
  if b = 0 then -(Real.sqrt (normIdeal p) : ℂ)⁻¹ else
  if b = 1 then
    if p ∣ q.n then (Real.sqrt (normIdeal p) : ℂ) else 0
  else if IsRelPrime p q.n ∧ p ∣ q.b then (Real.sqrt (normIdeal p) : ℂ) else 0

theorem exceptionalBranch_sum {p : Ideal O} (hp : Prime p) (q : ThetaPair) :
    (∑ b : Fin 3, exceptionalBranch p b q) = exceptionalMultiplier p q := by
  rw [Fin.sum_univ_three, exceptionalMultiplier_split hp]
  simp [exceptionalBranch]

theorem exceptional_product_expansion (P : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (q : ThetaPair) :
    (∏ p ∈ P, exceptionalMultiplier p q) =
      ∑ b : P → Fin 3, ∏ p : P, exceptionalBranch p.1 (b p) q := by
  rw [← Finset.prod_coe_sort P (fun p => exceptionalMultiplier p q)]
  calc
    _ = ∏ p : P, ∑ b : Fin 3, exceptionalBranch p.1 b q := by
      apply Finset.prod_congr rfl
      intro p _
      exact (exceptionalBranch_sum (hP p.1 p.2) q).symm
    _ = _ := Fintype.prod_sum _

def branchNumeratorSet (P : Finset (Ideal O)) (b : P → Fin 3) : Finset (Ideal O) :=
  P.attach.filter (fun p => b p = 1) |>.image Subtype.val

def branchCubeSet (P : Finset (Ideal O)) (b : P → Fin 3) : Finset (Ideal O) :=
  P.attach.filter (fun p => b p = 2) |>.image Subtype.val

def branchNumerator (P : Finset (Ideal O)) (b : P → Fin 3) : Ideal O :=
  ∏ p ∈ branchNumeratorSet P b, p

def branchCube (P : Finset (Ideal O)) (b : P → Fin 3) : Ideal O :=
  ∏ p ∈ branchCubeSet P b, p

theorem mem_branchNumeratorSet (P : Finset (Ideal O)) (b : P → Fin 3)
    (p : Ideal O) : p ∈ branchNumeratorSet P b ↔ ∃ hp : p ∈ P, b ⟨p, hp⟩ = 1 := by
  simp only [branchNumeratorSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  · rintro ⟨hp, hb⟩
    exact ⟨⟨p, hp⟩, hb, rfl⟩

theorem mem_branchCubeSet (P : Finset (Ideal O)) (b : P → Fin 3)
    (p : Ideal O) : p ∈ branchCubeSet P b ↔ ∃ hp : p ∈ P, b ⟨p, hp⟩ = 2 := by
  simp only [branchCubeSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  · rintro ⟨hp, hb⟩
    exact ⟨⟨p, hp⟩, hb, rfl⟩

theorem branchSets_disjoint (P : Finset (Ideal O)) (b : P → Fin 3) :
    Disjoint (branchNumeratorSet P b) (branchCubeSet P b) := by
  apply Finset.disjoint_left.mpr
  intro p hn hc
  obtain ⟨hnP, hn⟩ := (mem_branchNumeratorSet P b p).mp hn
  obtain ⟨hcP, hc⟩ := (mem_branchCubeSet P b p).mp hc
  exact (by decide : (1 : Fin 3) ≠ 2) (hn.symm.trans hc)

theorem prime_ideal_relPrime {p q : Ideal O} (hp : Prime p) (hq : Prime q)
    (hpq : p ≠ q) : IsRelPrime p q := by
  apply hp.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hpq (associated_iff_eq.mp (hp.associated_of_dvd hq hd))

theorem prime_set_squarefree (P : Finset (Ideal O)) (hP : ∀ p ∈ P, Prime p) :
    Squarefree (∏ p ∈ P, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact prime_ideal_relPrime (hP p hp) (hP q hq) hpq
  · intro p hp
    exact (hP p hp).squarefree

theorem prime_set_relPrime (P Q : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (hQ : ∀ q ∈ Q, Prime q) (hPQ : Disjoint P Q) :
    IsRelPrime (∏ p ∈ P, p) (∏ q ∈ Q, q) := by
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  apply prime_ideal_relPrime (hP p hp) (hQ q hq)
  intro h
  exact Finset.disjoint_left.mp hPQ hp (h.symm ▸ hq)

theorem prime_set_dvd_iff (P : Finset (Ideal O)) (hP : ∀ p ∈ P, Prime p)
    (n : Ideal O) : (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p => p) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hpq
    exact prime_ideal_relPrime (hP p hp) (hP q hq) hpq

def branchCoefficient (P : Finset (Ideal O)) (b : P → Fin 3) : ℂ :=
  ∏ p : P, if b p = 0 then -(Real.sqrt (normIdeal p.1) : ℂ)⁻¹ else
    (Real.sqrt (normIdeal p.1) : ℂ)

def branchCondition (P : Finset (Ideal O)) (b : P → Fin 3) (q : ThetaPair) : Prop :=
  ∀ p : P, (b p = 1 → p.1 ∣ q.n) ∧
    (b p = 2 → IsRelPrime p.1 q.n ∧ p.1 ∣ q.b)

theorem exceptional_product_branch (P : Finset (Ideal O)) (b : P → Fin 3)
    (q : ThetaPair) :
    (∏ p : P, exceptionalBranch p.1 (b p) q) =
      if branchCondition P b q then branchCoefficient P b else 0 := by
  by_cases h : branchCondition P b q
  · rw [if_pos h]
    unfold branchCoefficient
    apply Finset.prod_congr rfl
    intro p _
    have hp := h p
    have hb : b p = 0 ∨ b p = 1 ∨ b p = 2 := by omega
    rcases hb with h0 | h1 | h2
    · simp [exceptionalBranch, h0]
    · simp [exceptionalBranch, h1, hp.1 h1]
    · simp [exceptionalBranch, h2, hp.2 h2]
  · rw [if_neg h]
    have hex : ∃ p : P,
        ¬ ((b p = 1 → p.1 ∣ q.n) ∧ (b p = 2 → IsRelPrime p.1 q.n ∧ p.1 ∣ q.b)) := by
      simpa only [branchCondition, not_forall] using h
    obtain ⟨p, hp⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    have hb : b p = 0 ∨ b p = 1 ∨ b p = 2 := by omega
    rcases hb with h0 | h1 | h2
    · simp [h0] at hp
    · simp [h1] at hp
      simp [exceptionalBranch, h1, hp]
    · simp [h2] at hp
      have hn : ¬ (IsRelPrime p.1 q.n ∧ p.1 ∣ q.b) := fun h => hp h.1 h.2
      simp [exceptionalBranch, h2, hn]

theorem branchCondition_iff (P : Finset (Ideal O)) (hP : ∀ p ∈ P, Prime p)
    (b : P → Fin 3) (q : ThetaPair) : branchCondition P b q ↔
      branchNumerator P b ∣ q.n ∧ branchCube P b ∣ q.b ∧
        IsRelPrime (branchCube P b) q.n := by
  have hnP : ∀ p ∈ branchNumeratorSet P b, Prime p := by
    intro p hp
    exact hP p ((mem_branchNumeratorSet P b p).mp hp).choose
  have hcP : ∀ p ∈ branchCubeSet P b, Prime p := by
    intro p hp
    exact hP p ((mem_branchCubeSet P b p).mp hp).choose
  rw [branchNumerator, branchCube, prime_set_dvd_iff _ hnP,
    prime_set_dvd_iff _ hcP, IsRelPrime.prod_left_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨hpP, hb⟩ := (mem_branchNumeratorSet P b p).mp hp
      exact (h ⟨p, hpP⟩).1 hb
    · intro p hp
      obtain ⟨hpP, hb⟩ := (mem_branchCubeSet P b p).mp hp
      exact ((h ⟨p, hpP⟩).2 hb).2
    · intro p hp
      obtain ⟨hpP, hb⟩ := (mem_branchCubeSet P b p).mp hp
      exact ((h ⟨p, hpP⟩).2 hb).1
  · rintro ⟨hn, hc, he⟩ p
    constructor
    · intro hb
      exact hn p.1 ((mem_branchNumeratorSet P b p.1).mpr ⟨p.2, hb⟩)
    · intro hb
      have hm := (mem_branchCubeSet P b p.1).mpr ⟨p.2, hb⟩
      exact ⟨he p.1 hm, hc p.1 hm⟩

theorem branch_substitution_data (P : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (h3 : ∀ p ∈ P, IsRelPrime p (principal 3))
    (b : P → Fin 3) :
    Squarefree (branchNumerator P b) ∧ branchNumerator P b ≠ ⊥ ∧
      branchCube P b ≠ ⊥ ∧ IsRelPrime (branchNumerator P b) (principal 3) ∧
      IsRelPrime (branchCube P b) (principal 3) ∧
      IsRelPrime (branchCube P b) (branchNumerator P b) := by
  have hnP : ∀ p ∈ branchNumeratorSet P b, p ∈ P := by
    intro p hp
    exact ((mem_branchNumeratorSet P b p).mp hp).choose
  have hcP : ∀ p ∈ branchCubeSet P b, p ∈ P := by
    intro p hp
    exact ((mem_branchCubeSet P b p).mp hp).choose
  refine ⟨prime_set_squarefree _ (fun p hp => hP p (hnP p hp)), ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hP p (hnP p hp)).ne_zero)
  · exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hP p (hcP p hp)).ne_zero)
  · exact IsRelPrime.prod_left (fun p hp => h3 p (hnP p hp))
  · exact IsRelPrime.prod_left (fun p hp => h3 p (hcP p hp))
  · exact prime_set_relPrime _ _ (fun p hp => hP p (hcP p hp))
      (fun p hp => hP p (hnP p hp)) (branchSets_disjoint P b).symm

def branchSubstitution (P : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (h3 : ∀ p ∈ P, IsRelPrime p (principal 3))
    (b : P → Fin 3) :
    SubstitutedPair (branchNumerator P b) (branchCube P b) →
      DivisiblePair (branchNumerator P b) (branchCube P b) :=
  let h := branch_substitution_data P hP h3 b
  pairSubstitution h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- Genuine absolute summability permits the finite local expansion to pass
through the series. The branch map is the proved ideal-coordinate bijection. -/
theorem exceptional_product_substitution (P : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (h3 : ∀ p ∈ P, IsRelPrime p (principal 3))
    (F : ThetaPair → ℂ) (hF : Summable (fun q => ‖F q‖)) :
    (∑' q : ThetaPair, (∏ p ∈ P, exceptionalMultiplier p q) * F q) =
      ∑ b : P → Fin 3, branchCoefficient P b *
        ∑' q : SubstitutedPair (branchNumerator P b) (branchCube P b),
          F (branchSubstitution P hP h3 b q).1 := by
  let G : (P → Fin 3) → ThetaPair → ℂ := fun b q =>
    branchCoefficient P b * (if branchCondition P b q then F q else 0)
  have hs : ∀ b, Summable (G b) := by
    intro b
    have hi := hF.of_norm.indicator {q | branchCondition P b q}
    have he : ({q | branchCondition P b q}.indicator F) =
        (fun q => if branchCondition P b q then F q else 0) := by
      funext q
      exact Set.indicator_apply _ _ _
    rw [he] at hi
    exact hi.mul_left _
  have hpw : ∀ q : ThetaPair, (∏ p ∈ P, exceptionalMultiplier p q) * F q =
      ∑ b : P → Fin 3, G b q := by
    intro q
    rw [exceptional_product_expansion P hP q, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [exceptional_product_branch]
    by_cases hb : branchCondition P b q <;> simp [G, hb]
  calc
    _ = ∑' q : ThetaPair, ∑ b : P → Fin 3, G b q := tsum_congr hpw
    _ = ∑ b : P → Fin 3, ∑' q : ThetaPair, G b q :=
      Summable.tsum_finsetSum (fun b _ => hs b)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [G]
      rw [tsum_mul_left]
      congr 1
      have h := branch_substitution_data P hP h3 b
      change (∑' q : ThetaPair, if branchCondition P b q then F q else 0) =
        ∑' q : SubstitutedPair (branchNumerator P b) (branchCube P b),
          F (pairSubstitution h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 q).1
      rw [← pair_substitution_tsum h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 F]
      have ht := tsum_subtype {q : ThetaPair |
        branchNumerator P b ∣ q.n ∧ branchCube P b ∣ q.b ∧
          IsRelPrime (branchCube P b) q.n} F
      apply Eq.trans _ ht.symm
      apply tsum_congr
      intro q
      simp only [Set.indicator_apply, Set.mem_setOf_eq, ← branchCondition_iff P hP b q]



/-- The exact support test appearing in the frozen prepared summand. -/
def pairCondition (n b : Ideal O) : Prop :=
  n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3) ∧
    b ≠ ⊥ ∧ IsRelPrime b (principal 3)

def thetaPairOfCondition {n b : Ideal O} (h : pairCondition n b) : ThetaPair :=
  ⟨n, b, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem thetaPair_condition (q : ThetaPair) : pairCondition q.n q.b :=
  ⟨q.n_ne_bot, q.n_squarefree, q.n_three, q.b_ne_bot, q.b_three⟩

def preparedCoordinates : (ℕ × ThetaPair) ≃
    {q : ℕ × Ideal O × Ideal O // pairCondition q.2.1 q.2.2} where
  toFun q := ⟨(q.1, q.2.n, q.2.b), thetaPair_condition q.2⟩
  invFun q := (q.1.1, thetaPairOfCondition q.2)
  left_inv := by
    rintro ⟨r, q⟩
    congr 1
  right_inv := by
    rintro ⟨⟨r, n, b⟩, h⟩
    rfl

/-- Only the zero support test is removed; no infinite regrouping occurs. -/
theorem preparedThetaRow_eq_supported (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k : Ideal O) :
    preparedThetaRow W H Y A coeff k =
      ∑' q : ℕ × ThetaPair, preparedThetaTerm W H Y A coeff k (q.1, q.2.n, q.2.b) := by
  have hs : Function.support (preparedThetaTerm W H Y A coeff k) ⊆
      {q : ℕ × Ideal O × Ideal O | pairCondition q.2.1 q.2.2} := by
    intro q hq
    by_contra h
    exact hq (if_neg h)
  have ht := tsum_subtype_eq_of_support_subset hs
  have he := preparedCoordinates.tsum_eq
    (fun q : {q : ℕ × Ideal O × Ideal O // pairCondition q.2.1 q.2.2} =>
      preparedThetaTerm W H Y A coeff k q.1)
  exact ht.symm.trans he.symm

set_option maxHeartbeats 400000 in
theorem preparedThetaTerm_summable_supported (hb : ThetaBoundsStatement)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    (H Y a : ℝ) (hH : 0 < H) (hY : 0 < Y) (ha : 0 ≤ a)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k : Ideal O) (hk : k ≠ ⊥)
    (hA : ∀ r n b, ‖A r n b‖ ≤ a) (hc : ∀ r, ‖coeff r k‖ ≤ 1) :
    Summable (fun q : ℕ × ThetaPair =>
      ‖preparedThetaTerm W H Y A coeff k (q.1, q.2.n, q.2.b)‖) := by
  have hs : Summable (fun q : ℕ × Ideal O × Ideal O =>
      ‖preparedThetaTerm W H Y A coeff k q‖) :=
    preparedThetaTerm_summable_of_thetaBounds hb hW H Y a hH hY ha A coeff k hk hA hc
  let f : {q : ℕ × Ideal O × Ideal O // pairCondition q.2.1 q.2.2} → ℝ :=
    fun q => ‖preparedThetaTerm W H Y A coeff k q.1‖
  have ht : Summable f := hs.subtype (fun q => pairCondition q.2.1 q.2.2)
  change Summable (f ∘ preparedCoordinates)
  exact preparedCoordinates.summable_iff.mpr ht

def arrayOfIndex (u : Fin 6) (A : ThetaIndex → ℂ)
    (r : ℕ) (n b : Ideal O) : ℂ :=
  if h : pairCondition n b then A (u, r, thetaPairOfCondition h) else 0

@[simp] theorem arrayOfIndex_apply (u : Fin 6) (A : ThetaIndex → ℂ)
    (r : ℕ) (q : ThetaPair) : arrayOfIndex u A r q.n q.b = A (u, r, q) := by
  rw [arrayOfIndex, dif_pos (thetaPair_condition q)]
  congr 2

theorem arrayOfIndex_bound (u : Fin 6) (A : ThetaIndex → ℂ)
    (a : ℝ) (ha : 0 ≤ a) (hA : ∀ i, ‖A i‖ ≤ a) :
    ∀ r n b, ‖arrayOfIndex u A r n b‖ ≤ a := by
  intro r n b
  dsimp only [arrayOfIndex]
  split_ifs
  · exact hA _
  · simpa only [norm_zero] using ha

def maskedCuspColumn (hB : ThetaBoundsStatement) (d : ReflectionDatum)
    (i : ThetaIndex) : ℂ :=
  if i ∈ selectedIndices hB d.cusp then normalizedCuspColumn d i else 0

theorem maskedCuspColumn_norm_le (hB : ThetaBoundsStatement) (d : ReflectionDatum)
    (i : ThetaIndex) : ‖maskedCuspColumn hB d i‖ ≤ 27 := by
  dsimp only [maskedCuspColumn]
  split_ifs
  · exact normalizedCuspColumn_norm_le hB d i
  · norm_num

theorem maskedCuspColumn_mul_norm_le (hB : ThetaBoundsStatement) (d : ReflectionDatum)
    (M : ThetaIndex → ℂ) (B : ℝ) (hB0 : 0 ≤ B) (hM : ∀ i, ‖M i‖ ≤ B)
    (i : ThetaIndex) : ‖maskedCuspColumn hB d i * M i‖ ≤ 27 * B := by
  rw [norm_mul]
  exact mul_le_mul (maskedCuspColumn_norm_le hB d i) (hM i) (norm_nonneg _) (by norm_num)

/-- The simultaneous ideal substitution acts on the literal mode by the
expected scalar, before any character or norm is applied. -/
theorem pairSubstitution_indexMode {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) (u : Fin 6) (r : ℕ) (q : SubstitutedPair D E) :
    indexMode (u, r, (pairSubstitution hD hD0 hE0 hD3 hE3 hED q).1) =
      ((unitSlot u : O) * lambda ^ r * primaryGenerator D * primaryGenerator E ^ 3) *
        (primaryGenerator q.1.n * primaryGenerator q.1.b ^ 3) := by
  change (unitSlot u : O) * lambda ^ r *
    (primaryGenerator (D * q.1.n) * primaryGenerator (E * q.1.b) ^ 3) = _
  rw [primaryGenerator_mul_three hD3 q.1.n_three,
    primaryGenerator_mul_three hE3 q.1.b_three]
  ring

theorem pairSubstitution_columnDenominator {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) (u : Fin 6) (r : ℕ) (q : SubstitutedPair D E) :
    columnDenominator (u, r, (pairSubstitution hD hD0 hE0 hD3 hE3 hED q).1) =
      columnDenominator (u, r, q.1) * Real.sqrt (normIdeal D) * normIdeal E := by
  change (3 : ℝ) ^ ((((r : ℤ) - 4 : ℤ) : ℝ) / 3) *
    Real.sqrt (normIdeal (D * q.1.n)) * normIdeal (E * q.1.b) = _
  have hN (a b : Ideal O) : normIdeal (a * b) = normIdeal a * normIdeal b := by
    simp only [normIdeal, map_mul, Nat.cast_mul]
  rw [hN, hN, Real.sqrt_mul (normIdeal_pos hD0).le]
  unfold columnDenominator
  ring

theorem pairSubstitution_frequency_normSq {D E : Ideal O} (hD : Squarefree D)
    (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) (u : Fin 6) (r : ℕ) (q : SubstitutedPair D E) :
    Complex.normSq (latticeFrequency (indexMode
      (u, r, (pairSubstitution hD hD0 hE0 hD3 hE3 hED q).1))) =
      Complex.normSq (latticeFrequency (indexMode (u, r, q.1))) *
        normIdeal D * normIdeal E ^ 3 := by
  rw [normSq_latticeFrequency_indexMode, normSq_latticeFrequency_indexMode]
  change (3 : ℝ) ^ ((((r : ℤ) - 4 : ℤ) : ℝ)) *
    normIdeal (D * q.1.n) * normIdeal (E * q.1.b) ^ 3 = _
  simp only [normIdeal, map_mul, Nat.cast_mul]
  ring

/-- The n and b branches rescale Y by ND and NE³ respectively. -/
theorem pairSubstitution_scale (v Y ND NE H Nk : ℝ)
    (hND : ND ≠ 0) (hNE : NE ≠ 0) :
    (v * ND * NE ^ 3) * H ^ 2 / (Y * Nk ^ 2) =
      v * H ^ 2 / ((Y / (ND * NE ^ 3)) * Nk ^ 2) := by
  by_cases hY : Y = 0
  · simp [hY]
  by_cases hk : Nk = 0
  · simp [hk]
  field_simp
  <;> ring



theorem exceptionalMultiplier_norm_le (p : Ideal O) (q : ThetaPair) :
    ‖exceptionalMultiplier p q‖ ≤ (Real.sqrt (normIdeal p))⁻¹ + Real.sqrt (normIdeal p) := by
  have hs : 0 ≤ Real.sqrt (normIdeal p) := Real.sqrt_nonneg _
  have hh : ‖(if p ∣ q.n ∨ p ∣ q.b then (Real.sqrt (normIdeal p) : ℂ) else 0)‖ ≤
      Real.sqrt (normIdeal p) := by
    split_ifs <;> simp [Real.norm_of_nonneg hs, hs]
  unfold exceptionalMultiplier
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs]
  exact add_le_add le_rfl hh

/-- The simultaneous exceptional substitutions commute with an additional
parameter series using the original joint absolute convergence. -/
theorem exceptional_product_substitution_with_parameter {T : Type*}
    (P : Finset (Ideal O)) (hP : ∀ p ∈ P, Prime p)
    (h3 : ∀ p ∈ P, IsRelPrime p (principal 3))
    (F : T × ThetaPair → ℂ) (hF : Summable (fun q => ‖F q‖)) :
    (∑' q : T × ThetaPair, (∏ p ∈ P, exceptionalMultiplier p q.2) * F q) =
      ∑ b : P → Fin 3, branchCoefficient P b *
        ∑' q : T × SubstitutedPair (branchNumerator P b) (branchCube P b),
          F (q.1, (branchSubstitution P hP h3 b q.2).1) := by
  let B : ℝ := ∏ p ∈ P, ((Real.sqrt (normIdeal p))⁻¹ + Real.sqrt (normIdeal p))
  have hleft : Summable (fun q : T × ThetaPair =>
      ‖(∏ p ∈ P, exceptionalMultiplier p q.2) * F q‖) := by
    apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ (hF.mul_left B)
    intro q
    rw [norm_mul, norm_prod]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Finset.prod_le_prod₀ (fun p hp => norm_nonneg _)
      (fun p hp => exceptionalMultiplier_norm_le p q.2)
  have hbranch : ∀ b : P → Fin 3,
      Summable (fun q : T × SubstitutedPair (branchNumerator P b) (branchCube P b) =>
        ‖F (q.1, (branchSubstitution P hP h3 b q.2).1)‖) := by
    intro b
    have h := branch_substitution_data P hP h3 b
    have hi : Function.Injective (fun q : SubstitutedPair (branchNumerator P b) (branchCube P b) =>
        (branchSubstitution P hP h3 b q).1) :=
      Subtype.val_injective.comp
        (pairSubstitution_bijective h.1 h.2.1 h.2.2.1 h.2.2.2.1
          h.2.2.2.2.1 h.2.2.2.2.2).1
    apply hF.comp_injective
    intro q q' hq
    have ht : q.1 = q'.1 := congrArg (fun a : T × ThetaPair => a.1) hq
    have hp := congrArg (fun a : T × ThetaPair => a.2) hq
    exact Prod.ext ht (hi hp)
  calc
    _ = ∑' t : T, ∑' q : ThetaPair, (∏ p ∈ P, exceptionalMultiplier p q) * F (t, q) :=
      hleft.of_norm.tsum_prod
    _ = ∑' t : T, ∑ b : P → Fin 3, branchCoefficient P b *
        ∑' q : SubstitutedPair (branchNumerator P b) (branchCube P b),
          F (t, (branchSubstitution P hP h3 b q).1) := by
      apply tsum_congr
      intro t
      exact exceptional_product_substitution P hP h3 (fun q => F (t, q)) (hF.prod_factor t)
    _ = ∑ b : P → Fin 3, ∑' t : T, branchCoefficient P b *
        ∑' q : SubstitutedPair (branchNumerator P b) (branchCube P b),
          F (t, (branchSubstitution P hP h3 b q).1) :=
      Summable.tsum_finsetSum (fun b _ => (hbranch b).of_norm.prod.mul_left _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [tsum_mul_left, ← (hbranch b).of_norm.tsum_prod]

theorem prime_lambda_not_mem {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) : lambda ∉ p := by
  intro h
  have hs : lambda ^ 2 = (-3 : O) := by
    unfold lambda
    linear_combination 4 * SquarefreeReflection.RayValuePrerequisites.omega_sq_add_omega_add_one
  have hm := p.pow_mem_of_mem h 2 (by decide)
  rw [hs] at hm
  have hthree : (3 : O) ∈ p := by simpa only [neg_neg] using p.neg_mem hm
  exact hp.not_isUnit (h3 dvd_rfl (Ideal.dvd_span_singleton.mpr hthree))

theorem thetaLocalFactor_four_indexMode {p : Ideal O} (hp : Prime p)
    (h3 : IsRelPrime p (principal 3)) (i : ThetaIndex) :
    thetaLocalFactor p 4 (indexMode i) = exceptionalMultiplier p i.2.2 := by
  have hprime := Ideal.isPrime_of_prime hp
  have hu : (unitSlot i.1 : O) ∉ p := fun h =>
    hprime.ne_top (p.eq_top_of_isUnit_mem h (unitSlot i.1).isUnit)
  have hl : lambda ^ i.2.1 ∉ p := fun h =>
    prime_lambda_not_mem hp h3 (hprime.mem_of_pow_mem _ h)
  have ha : (unitSlot i.1 : O) * lambda ^ i.2.1 ∉ p :=
    hprime.mul_notMem hu hl
  have hn : primaryGenerator i.2.2.n ∈ p ↔ p ∣ i.2.2.n := by
    calc
      _ ↔ p ∣ principal (primaryGenerator i.2.2.n) := Ideal.dvd_span_singleton.symm
      _ ↔ _ := by rw [(primaryGenerator_spec_three i.2.2.n_three).1]
  have hb : primaryGenerator i.2.2.b ∈ p ↔ p ∣ i.2.2.b := by
    calc
      _ ↔ p ∣ principal (primaryGenerator i.2.2.b) := Ideal.dvd_span_singleton.symm
      _ ↔ _ := by rw [(primaryGenerator_spec_three i.2.2.b_three).1]
  have hcop : IsRelPrime p i.2.2.n ↔ ¬ p ∣ i.2.2.n :=
    hp.irreducible.isRelPrime_iff_not_dvd
  unfold indexMode
  rw [← mul_assoc, thetaLocalFactor_four_split hp _ _ _ ha,
    exceptionalMultiplier_split hp]
  simp only [hn, hb, hcop]

def exceptionalPrimes (A : Finset (Ideal O)) (j : Ideal O → Fin 6) :
    Finset (Ideal O) := A.filter (fun p => j p = 4)

def ordinaryLocalProduct (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (i : ThetaIndex) : ℂ :=
  ∏ p ∈ A.filter (fun p => j p ≠ 4), thetaLocalFactor p (j p) (indexMode i)

theorem active_local_product_split (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hA : ∀ p ∈ A, Prime p) (h3 : ∀ p ∈ A, IsRelPrime p (principal 3))
    (i : ThetaIndex) :
    (∏ p ∈ A, thetaLocalFactor p (j p) (indexMode i)) =
      ordinaryLocalProduct A j i *
        ∏ p ∈ exceptionalPrimes A j, exceptionalMultiplier p i.2.2 := by
  rw [← Finset.prod_filter_not_mul_prod_filter A (fun p => j p = 4)]
  unfold ordinaryLocalProduct exceptionalPrimes
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hm := Finset.mem_filter.mp hp
  rw [hm.2, thetaLocalFactor_four_indexMode (hA p hm.1) (h3 p hm.1)]


def branchCode (b : Fin 3) : ReflectionLocalBranch :=
  if b = 0 then .unchanged else if b = 1 then .numerator else .cube

def localBranchDenominator (q : ℝ) (b : Fin 3) : ℝ :=
  (if b = 1 then Real.sqrt q else 1) * (if b = 2 then q else 1)

def localBranchScalar (q : ℝ) (b : Fin 3) : ℂ :=
  if b = 0 then -(Real.sqrt q : ℂ)⁻¹ else (Real.sqrt q : ℂ)

theorem localBranchDenominator_pos {q : ℝ} (hq : 0 < q) (b : Fin 3) :
    0 < localBranchDenominator q b := by
  have hs := Real.sqrt_pos.mpr hq
  fin_cases b <;> simp [localBranchDenominator, hs, hq]

theorem localBranchScalar_norm_sq {q : ℝ} (hq : 0 < q) (b : Fin 3) :
    ‖localBranchScalar q b / (localBranchDenominator q b : ℂ)‖ ^ 2 =
      reflectionLocalWeight q 4 (branchCode b) := by
  have hs := Real.sqrt_pos.mpr hq
  have hsq := Real.sq_sqrt hq.le
  fin_cases b
  · simp [localBranchScalar, localBranchDenominator, branchCode,
      reflectionLocalWeight, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le,
      inv_pow, hsq]
  · simp [localBranchScalar, localBranchDenominator, branchCode,
      reflectionLocalWeight, hs.ne']
  · have hh : ‖(Real.sqrt q : ℂ) / (q : ℂ)‖ ^ 2 = q⁻¹ := by
      rw [norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hq.le, div_pow, hsq]
      field_simp [hq.ne']
    simpa [localBranchScalar, localBranchDenominator, branchCode,
      reflectionLocalWeight] using hh


theorem localBranchScalar_norm {q : ℝ} (hq : 0 < q) (b : Fin 3) :
    ‖localBranchScalar q b / (localBranchDenominator q b : ℂ)‖ =
      Real.sqrt (reflectionLocalWeight q 4 (branchCode b)) := by
  rw [← localBranchScalar_norm_sq hq b, Real.sqrt_sq (norm_nonneg _)]

theorem localBranchScale {q : ℝ} (hq : 0 < q) (b : Fin 3) :
    q ^ 2 / ((if b = 1 then q else 1) * (if b = 2 then q ^ 3 else 1)) =
      reflectionLocalScale q 4 (branchCode b) := by
  fin_cases b <;> simp [branchCode, reflectionLocalScale] <;>
    field_simp [hq.ne'] <;> ring

theorem branchNumerator_norm_prod (P : Finset (Ideal O)) (b : P → Fin 3) :
    normIdeal (branchNumerator P b) = ∏ p : P, if b p = 1 then normIdeal p.1 else 1 := by
  simp only [branchNumerator, branchNumeratorSet, normIdeal, map_prod, Nat.cast_prod]
  rw [Finset.prod_image (fun x hx y hy h => Subtype.ext h)]
  simp only [Finset.prod_filter]
  rfl

theorem branchCube_norm_prod (P : Finset (Ideal O)) (b : P → Fin 3) :
    normIdeal (branchCube P b) = ∏ p : P, if b p = 2 then normIdeal p.1 else 1 := by
  simp only [branchCube, branchCubeSet, normIdeal, map_prod, Nat.cast_prod]
  rw [Finset.prod_image (fun x hx y hy h => Subtype.ext h)]
  simp only [Finset.prod_filter]
  rfl

theorem branch_denominator_prod (P : Finset (Ideal O)) (b : P → Fin 3) :
    Real.sqrt (normIdeal (branchNumerator P b)) * normIdeal (branchCube P b) =
      ∏ p : P, localBranchDenominator (normIdeal p.1) (b p) := by
  rw [branchNumerator_norm_prod, branchCube_norm_prod,
    Real.sqrt_prod _ (fun p _ => by
      split_ifs
      · exact Nat.cast_nonneg _
      · exact zero_le_one)]
  simp only [localBranchDenominator, Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  split_ifs <;> simp

theorem branchCoefficient_norm (P : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (b : P → Fin 3) :
    ‖branchCoefficient P b /
      ((Real.sqrt (normIdeal (branchNumerator P b)) * normIdeal (branchCube P b) : ℝ) : ℂ)‖ =
      Real.sqrt (∏ p : P, reflectionLocalWeight (normIdeal p.1) 4 (branchCode (b p))) := by
  rw [branch_denominator_prod, Complex.ofReal_prod]
  change ‖(∏ p : P, localBranchScalar (normIdeal p.1) (b p)) /
    (∏ p : P, (localBranchDenominator (normIdeal p.1) (b p) : ℂ))‖ = _
  rw [← Finset.prod_div_distrib, norm_prod]
  calc
    _ = ∏ p : P, Real.sqrt (reflectionLocalWeight (normIdeal p.1) 4 (branchCode (b p))) := by
      apply Finset.prod_congr rfl
      intro p _
      exact localBranchScalar_norm (normIdeal_pos (hP p.1 p.2).ne_zero) (b p)
    _ = _ := by
      apply (Real.sqrt_prod _ _).symm
      intro p _
      exact (reflection_local_update (by
        change (1 : ℝ) ≤ ((p.1).absNorm : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Ideal.absNorm_eq_zero_iff.not.mpr (hP p.1 p.2).ne_zero)) 4 (branchCode (b p))).1

end QRHShort.SquarefreeAssembly.PacketConstruction

namespace QRHShort.SquarefreeAssembly.PacketCharacters
open UniqueFactorizationMonoid
open QRHShort.SquarefreeReflection

theorem prime_outside (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hnot : p ∉ c.S) : Outside c.S p := by
  refine ⟨hp.ne_zero, ?_⟩
  intro q hq hqp
  have heq : q = p := associated_iff_eq.mp
    ((c.prime_S q hq).associated_of_dvd hp hqp)
  exact hnot (heq ▸ hq)

theorem outside_prime_relPrime_three (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hout : Outside c.S p) : IsRelPrime p (principal 3) := by
  apply hp.irreducible.isRelPrime_iff_not_dvd.mpr
  intro h3
  exact hout.2 p (c.above_three p hp h3) (dvd_refl p)

theorem primeFactors_prime {k p : Ideal O} (hp : p ∈ primeFactors k) : Prime p :=
  prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)

theorem primeFactors_dvd {k p : Ideal O} (hp : p ∈ primeFactors k) : p ∣ k :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)

theorem primeFactors_prod {k : Ideal O} (hk : k ≠ ⊥) (hs : Squarefree k) :
    (∏ p ∈ primeFactors k, p) = k := by
  have hn := (squarefree_iff_nodup_normalizedFactors hk).mp hs
  unfold primeFactors
  rw [← Multiset.toFinset_eq hn]
  simpa only [Finset.prod_mk, Multiset.map_id'] using
    (Ideal.prod_normalizedFactors_eq_self hk)

theorem sexticAtPrime_zero_or_sixth (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hout : Outside c.S p) (z : O) :
    sexticAtPrime p z = 0 ∨ sexticAtPrime p z ^ (6 : ℕ) = 1 := by
  have hζ := RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot c hp hout
  by_cases hz : z ∈ p
  · exact Or.inl (sexticAtPrime_zero_of_mem hp hζ hz)
  · obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ hz
    right
    rw [RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj ht,
      ← QRHShort.embedding_pow, ← pow_mul, Nat.mul_comm j 6, pow_mul,
      QRHShort.rootSix_pow_six, one_pow, QRHShort.embedding_one]

theorem zero_or_sixth_prod (s : Multiset ℂ)
    (hs : ∀ z ∈ s, z = 0 ∨ z ^ (6 : ℕ) = 1) :
    s.prod = 0 ∨ s.prod ^ (6 : ℕ) = 1 := by
  revert hs
  induction s using Multiset.induction_on with
  | empty => intro _; exact Or.inr (by simp)
  | @cons z s ih =>
    intro hs
    have hz := hs z (by simp)
    have ht := ih (fun w hw => hs w (Multiset.mem_cons_of_mem hw))
    rcases hz with hz | hz
    · exact Or.inl (by simp [hz])
    rcases ht with ht | ht
    · exact Or.inl (by simp [ht])
    · exact Or.inr (by simp only [Multiset.prod_cons, mul_pow, hz, ht, one_mul])

theorem sexticSymbol_zero_or_sixth (c : ArithmeticContext) {k : Ideal O}
    (hk : Outside c.S k) (z : O) :
    sexticSymbol k z = 0 ∨ sexticSymbol k z ^ (6 : ℕ) = 1 := by
  simp only [sexticSymbol, if_neg hk.1]
  apply zero_or_sixth_prod
  intro w hw
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
  exact sexticAtPrime_zero_or_sixth c (prime_of_normalized_factor p hp)
    (RayValuePrerequisites.outside_of_mem_normalizedFactors hk hp) z

theorem sexticSymbol_norm_le_one (c : ArithmeticContext) {k : Ideal O}
    (hk : Outside c.S k) (z : O) : ‖sexticSymbol k z‖ ≤ 1 := by
  rcases sexticSymbol_zero_or_sixth c hk z with hz | h6
  · simp [hz]
  · exact (Complex.norm_eq_one_of_pow_eq_one h6 (by decide)).le

theorem ninth_eq_cube {z : ℂ} (hz : z = 0 ∨ z ^ (6 : ℕ) = 1) :
    z ^ (9 : ℕ) = z ^ (3 : ℕ) := by
  rcases hz with rfl | h6
  · simp
  · calc
      z ^ (9 : ℕ) = z ^ (6 : ℕ) * z ^ (3 : ℕ) := by ring
      _ = _ := by rw [h6, one_mul]

theorem sexticSymbol_cubic_factor (c : ArithmeticContext) {k : Ideal O}
    (hk : Outside c.S k) (a n b : O) :
    sexticSymbol k (a * n * b ^ (3 : ℕ)) ^ (3 : ℕ) =
      sexticSymbol k a ^ (3 : ℕ) * sexticSymbol k (n * b) ^ (3 : ℕ) := by
  rw [sexticSymbol_mul_numerator c hk, sexticSymbol_mul_numerator c hk,
    sexticSymbol_pow_numerator c hk, sexticSymbol_mul_numerator c hk,
    mul_pow, mul_pow, mul_pow, ← pow_mul]
  rw [ninth_eq_cube (sexticSymbol_zero_or_sixth c hk b)]
  ring

theorem neg_three_eq_cube {z : ℂ} (h6 : z ^ (6 : ℕ) = 1) :
    z ^ (-3 : ℤ) = z ^ (3 : ℕ) := by
  have h3 : z ^ (3 : ℕ) * z ^ (3 : ℕ) = 1 := by
    simpa only [← pow_add] using h6
  rw [show (-3 : ℤ) = -(3 : ℤ) by rfl, zpow_neg]
  exact inv_eq_of_mul_eq_one_right h3

theorem thetaLocalFactor_one (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hout : Outside c.S p) (z : O) :
    thetaLocalFactor p 1 z = sexticAtPrime p z ^ (3 : ℕ) := by
  have hζ := RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot c hp hout
  change (if z ∈ p then 0 else sexticSymbol p z ^ (-3 : ℤ)) = _
  rw [sexticSymbol_prime hp]
  by_cases hz : z ∈ p
  · rw [if_pos hz, sexticAtPrime_zero_of_mem hp hζ hz, zero_pow (by decide)]
  · rw [if_neg hz]
    obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ hz
    apply neg_three_eq_cube
    rw [RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj ht,
      ← QRHShort.embedding_pow, ← pow_mul, Nat.mul_comm j 6, pow_mul,
      QRHShort.rootSix_pow_six, one_pow, QRHShort.embedding_one]

theorem thetaLocalFactor_primeFactors (c : ArithmeticContext) {k : Ideal O}
    (hk : SquarefreeOutside c.S k) (z : O) :
    (∏ p ∈ primeFactors k, thetaLocalFactor p 1 z) =
      sexticSymbol k z ^ (3 : ℕ) := by
  have hn := (squarefree_iff_nodup_normalizedFactors hk.1.1).mp hk.2
  calc
    _ = ∏ p ∈ primeFactors k, sexticAtPrime p z ^ (3 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact thetaLocalFactor_one c (primeFactors_prime hp)
        (RayValuePrerequisites.outside_of_mem_normalizedFactors hk.1
          (Multiset.mem_toFinset.mp hp)) z
    _ = sexticSymbol k z ^ (3 : ℕ) := by
      simp only [sexticSymbol, if_neg hk.1.1, primeFactors]
      rw [← Multiset.toFinset_eq hn]
      exact Multiset.prod_map_pow

theorem primeFactors_disjoint {k : Ideal O} {A : Finset (Ideal O)}
    (hA : ∀ p ∈ A, Prime p) (hcop : IsRelPrime k (∏ p ∈ A, p)) :
    Disjoint A (primeFactors k) := by
  apply Finset.disjoint_left.mpr
  intro p hpA hpk
  exact (hA p hpA).not_isUnit
    (hcop (primeFactors_dvd hpk) (Finset.dvd_prod_of_mem (fun p => p) hpA))

theorem thetaLocalFactor_union (c : ArithmeticContext) {k : Ideal O}
    (hk : SquarefreeOutside c.S k) (A : Finset (Ideal O))
    (hA : PrimeTwistSet c.S A) (hcop : IsRelPrime k (∏ p ∈ A, p))
    (j : Ideal O → Fin 6) (z : O) :
    (∏ p ∈ A ∪ primeFactors k, thetaLocalFactor p (variableTwistExponents A j p) z) =
      (∏ p ∈ A, thetaLocalFactor p (j p) z) * sexticSymbol k z ^ (3 : ℕ) := by
  have hd := primeFactors_disjoint (fun p hp => (hA p hp).1) hcop
  rw [Finset.prod_union hd]
  have hfirst : (∏ p ∈ A, thetaLocalFactor p (variableTwistExponents A j p) z) =
      ∏ p ∈ A, thetaLocalFactor p (j p) z := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [variableTwistExponents, if_pos hp]
  have hsecond : (∏ p ∈ primeFactors k,
      thetaLocalFactor p (variableTwistExponents A j p) z) =
      ∏ p ∈ primeFactors k, thetaLocalFactor p 1 z := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [variableTwistExponents, if_neg (fun h => Finset.disjoint_left.mp hd h hp)]
  rw [hfirst, hsecond, thetaLocalFactor_primeFactors c hk]

theorem norm_zpow_le_one_of_zero_or_sixth {z : ℂ}
    (hz : z = 0 ∨ z ^ (6 : ℕ) = 1) (t : ℤ) (ht : t ≠ 0) : ‖z ^ t‖ ≤ 1 := by
  rcases hz with rfl | h6
  · simp [zero_zpow t ht]
  · rw [norm_zpow, Complex.norm_eq_one_of_pow_eq_one h6 (by decide), one_zpow]

theorem localCharacterPower_norm_le_one (c : ArithmeticContext) {p : Ideal O}
    (hout : Outside c.S p) (t : ℤ) (ht : t ≠ 0) (z : O) :
    ‖localCharacterPower p t z‖ ≤ 1 := by
  unfold localCharacterPower
  split_ifs with hz
  · simp
  · exact norm_zpow_le_one_of_zero_or_sixth (sexticSymbol_zero_or_sixth c hout z) t ht

theorem thetaLocalFactor_norm_le_one (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hout : Outside c.S p) (j : Fin 6)
    (h0 : j ≠ 0) (h4 : j ≠ 4) (z : O) : ‖thetaLocalFactor p j z‖ ≤ 1 := by
  have hv0 : j.val ≠ 0 := by exact fun h => h0 (Fin.ext h)
  have hv4 : j.val ≠ 4 := by exact fun h => h4 (Fin.ext h)
  simp only [thetaLocalFactor, if_neg hv0, if_neg hv4]
  apply localCharacterPower_norm_le_one c hout
  omega

theorem thetaLocalFactor_norm_le_weight (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hout : Outside c.S p) (j : Fin 6) (h4 : j ≠ 4) (z : O) :
    ‖thetaLocalFactor p j z‖ ≤
      if j = 0 then (Real.sqrt (normIdeal p))⁻¹ else 1 := by
  by_cases h0 : j = 0
  · subst j
    change ‖(Real.sqrt (normIdeal p) : ℂ)⁻¹ * localCharacterPower p (-2) z‖ ≤
      (Real.sqrt (normIdeal p))⁻¹
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (localCharacterPower_norm_le_one c hout (-2) (by decide) z)
  · rw [if_neg h0]
    exact thetaLocalFactor_norm_le_one c hp hout j h0 h4 z

end QRHShort.SquarefreeAssembly.PacketCharacters

namespace QRHShort.SquarefreeAssembly.PacketConstruction


def packetBranchAssignment (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (b : exceptionalPrimes A j → Fin 3) (p : Ideal O) : ReflectionLocalBranch :=
  if hp : p ∈ exceptionalPrimes A j then branchCode (b ⟨p, hp⟩) else .unchanged

def packetBranchWeight (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (b : exceptionalPrimes A j → Fin 3) : ℝ :=
  ∏ p ∈ A, reflectionLocalWeight (normIdeal p) (j p) (packetBranchAssignment A j b p)

def packetBranchScale (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (b : exceptionalPrimes A j → Fin 3) : ℝ :=
  ∏ p ∈ A, reflectionLocalScale (normIdeal p) (j p) (packetBranchAssignment A j b p)

theorem primeTwist_three (c : ArithmeticContext) {A : Finset (Ideal O)}
    (hA : PrimeTwistSet c.S A) {p : Ideal O} (hp : p ∈ A) :
    IsRelPrime p (principal 3) :=
  PacketCharacters.outside_prime_relPrime_three c (hA p hp).1
    (PacketCharacters.prime_outside c (hA p hp).1 (hA p hp).2)

def reflectedBranchArray (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (u : Fin 6) (b : exceptionalPrimes p.active p.exponent → Fin 3)
    (r : ℕ) (n d : Ideal O) : ℂ :=
  let P := exceptionalPrimes p.active p.exponent
  let D := branchNumerator P b
  let E := branchCube P b
  if h : pairCondition n d ∧ IsRelPrime D n ∧ IsRelPrime E n then
    let q : SubstitutedPair D E := ⟨thetaPairOfCondition h.1, h.2⟩
    let i : ThetaIndex := (u, r,
      (branchSubstitution P (fun a ha => (hA a (Finset.mem_filter.mp ha).1).1)
        (fun a ha => primeTwist_three c hA (Finset.mem_filter.mp ha).1) b q).1)
    (p.amplitude : ℂ) *
      (branchCoefficient P b / ((Real.sqrt (normIdeal D) * normIdeal E : ℝ) : ℂ)) *
      maskedCuspColumn hB p.datum i * ordinaryLocalProduct p.active p.exponent i
  else 0

def reflectedBranchCoeff (p : RawReflectionPacket) (u : Fin 6)
    (b : exceptionalPrimes p.active p.exponent → Fin 3)
    (r : ℕ) (k : Ideal O) : ℂ :=
  let P := exceptionalPrimes p.active p.exponent
  p.coeff k * sexticSymbol k ((unitSlot u : O) * lambda ^ r *
    primaryGenerator (branchNumerator P b) * primaryGenerator (branchCube P b) ^ 3) ^ 3

/-- Every component is literal: the chosen cusp column is evaluated at the
original pair, and the variable-row character is kept solely in `coeff`. -/
def reflectedBranchPacket (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active) (X : ℝ)
    (u : Fin 6) (b : exceptionalPrimes p.active p.exponent → Fin 3) : ReflectionPacket where
  H := p.H
  Y := rawReflectionScale X p * packetBranchScale p.active p.exponent b
  amplitude := 27 * p.amplitude * Real.sqrt (packetBranchWeight p.active p.exponent b)
  A := reflectedBranchArray hB c p hA u b
  coeff := reflectedBranchCoeff p u b

theorem reflectedBranchCoeff_norm_le (c : ArithmeticContext)
    (p : RawReflectionPacket) (u : Fin 6)
    (b : exceptionalPrimes p.active p.exponent → Fin 3)
    (hc : ∀ k ∈ sieveRows c.S p.H, ‖p.coeff k‖ ≤ 1)
    (r : ℕ) (k : Ideal O) (hk : k ∈ sieveRows c.S p.H) :
    ‖reflectedBranchCoeff p u b r k‖ ≤ 1 := by
  rw [reflectedBranchCoeff, norm_mul, norm_pow]
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (PacketCharacters.sexticSymbol_norm_le_one c ((mem_sieveRows _ _ _).mp hk).1.1
      ((unitSlot u : O) * lambda ^ r *
        primaryGenerator (branchNumerator (exceptionalPrimes p.active p.exponent) b) *
        primaryGenerator (branchCube (exceptionalPrimes p.active p.exponent) b) ^ 3)) 3
  simpa only [one_pow, one_mul] using mul_le_mul (hc k hk) hh
    (pow_nonneg (norm_nonneg _) _) zero_le_one

theorem primeTwist_norm_one_le (c : ArithmeticContext) {A : Finset (Ideal O)}
    (hA : PrimeTwistSet c.S A) : ∀ p ∈ A, 1 ≤ normIdeal p := by
  intro p hp
  change (1 : ℝ) ≤ (p.absNorm : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hA p hp).1.ne_zero)

theorem reflectedBranch_shape (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q)
    (u : Fin 6) (b : exceptionalPrimes p.active p.exponent → Fin 3) :
    let t := reflectedBranchPacket hB c p hA X u b
    1 ≤ t.H ∧ t.H ≤ D ^ C ∧ 0 < t.Y ∧ t.Y ≤ L * D ^ C ∧
      0 ≤ t.amplitude ∧ t.H = p.H ∧
      t.amplitude ^ 2 * (t.H + t.Y) ≤
        729 * (p.amplitude ^ 2 * (p.H + rawReflectionScale X p * rawReflectionCost p)) := by
  obtain ⟨hH, hHC, hY, hYB, ha, _, _, _, _⟩ := hp
  have hu := reflection_local_product p.active normIdeal p.exponent
    (packetBranchAssignment p.active p.exponent b) (primeTwist_norm_one_le c hA)
  have hw : 0 ≤ packetBranchWeight p.active p.exponent b := hu.1
  have hs : 0 < packetBranchScale p.active p.exponent b := hu.2.2.1
  refine ⟨hH, hHC, mul_pos hY hs, ?_, ?_, rfl, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hu.2.2.2.1 hY.le).trans hYB
  · exact mul_nonneg (mul_nonneg (by norm_num) ha) (Real.sqrt_nonneg _)
  · have hc := reflection_local_product_budget p.active normIdeal p.exponent
      (packetBranchAssignment p.active p.exponent b) (primeTwist_norm_one_le c hA)
      (p.amplitude ^ 2) p.H (rawReflectionScale X p) (sq_nonneg _)
      (zero_le_one.trans hH) hY.le
    change (27 * p.amplitude * Real.sqrt (packetBranchWeight p.active p.exponent b)) ^ 2 *
      (p.H + rawReflectionScale X p * packetBranchScale p.active p.exponent b) ≤ _
    rw [mul_pow, mul_pow, Real.sq_sqrt hw]
    convert mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 729) using 1 <;>
      dsimp only [packetBranchWeight, packetBranchScale, rawReflectionCost] <;> ring

theorem packetBranchWeight_split (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (b : exceptionalPrimes A j → Fin 3) :
    packetBranchWeight A j b =
      (∏ p ∈ A.filter (fun p => j p ≠ 4),
        reflectionLocalWeight (normIdeal p) (j p) .unchanged) *
      ∏ p : exceptionalPrimes A j,
        reflectionLocalWeight (normIdeal p.1) 4 (branchCode (b p)) := by
  unfold packetBranchWeight
  rw [← Finset.prod_filter_not_mul_prod_filter A (fun p => j p = 4)]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hn : p ∉ exceptionalPrimes A j := by
      simp only [exceptionalPrimes, Finset.mem_filter]
      exact fun h => (Finset.mem_filter.mp hp).2 h.2
    simp only [packetBranchAssignment, dif_neg hn]
  · change (∏ p ∈ exceptionalPrimes A j,
      reflectionLocalWeight (normIdeal p) (j p) (packetBranchAssignment A j b p)) = _
    rw [← Finset.prod_coe_sort (exceptionalPrimes A j)
      (fun p => reflectionLocalWeight (normIdeal p) (j p) (packetBranchAssignment A j b p))]
    apply Finset.prod_congr rfl
    intro p _
    have hj := (Finset.mem_filter.mp p.2).2
    simp only [packetBranchAssignment, dif_pos p.2, hj]

theorem ordinaryLocalProduct_norm_le (c : ArithmeticContext)
    (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hA : PrimeTwistSet c.S A) (i : ThetaIndex) :
    ‖ordinaryLocalProduct A j i‖ ≤
      Real.sqrt (∏ p ∈ A.filter (fun p => j p ≠ 4),
        reflectionLocalWeight (normIdeal p) (j p) .unchanged) := by
  rw [ordinaryLocalProduct, norm_prod]
  calc
    _ ≤ ∏ p ∈ A.filter (fun p => j p ≠ 4),
        Real.sqrt (reflectionLocalWeight (normIdeal p) (j p) .unchanged) := by
      apply Finset.prod_le_prod₀ (fun p hp => norm_nonneg _)
      intro p hp
      obtain ⟨hpA, hj4⟩ := Finset.mem_filter.mp hp
      have hl := PacketCharacters.thetaLocalFactor_norm_le_weight c (hA p hpA).1
        (PacketCharacters.prime_outside c (hA p hpA).1 (hA p hpA).2) (j p) hj4 (indexMode i)
      by_cases hj0 : j p = 0
      · simpa [reflectionLocalWeight, hj0, Real.sqrt_inv] using hl
      · simpa [reflectionLocalWeight, hj0, hj4] using hl
    _ = _ := by
      apply (Real.sqrt_prod _ _).symm
      intro p hp
      exact (reflection_local_update (primeTwist_norm_one_le c hA p (Finset.mem_filter.mp hp).1)
        (j p) .unchanged).1

theorem reflectedBranchArray_norm_le (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (ha : 0 ≤ p.amplitude) (u : Fin 6)
    (b : exceptionalPrimes p.active p.exponent → Fin 3)
    (r : ℕ) (n d : Ideal O) :
    ‖reflectedBranchArray hB c p hA u b r n d‖ ≤
      27 * p.amplitude * Real.sqrt (packetBranchWeight p.active p.exponent b) := by
  let P := exceptionalPrimes p.active p.exponent
  let WN := ∏ a ∈ p.active.filter (fun a => p.exponent a ≠ 4),
    reflectionLocalWeight (normIdeal a) (p.exponent a) .unchanged
  let WE := ∏ a : P, reflectionLocalWeight (normIdeal a.1) 4 (branchCode (b a))
  have hn : 0 ≤ WN := Finset.prod_nonneg (fun a ha' =>
    (reflection_local_update (primeTwist_norm_one_le c hA a (Finset.mem_filter.mp ha').1)
      (p.exponent a) .unchanged).1)
  have hc := branchCoefficient_norm P (fun a ha' => (hA a (Finset.mem_filter.mp ha').1).1) b
  dsimp only [reflectedBranchArray]
  split_ifs with h
  · let q : SubstitutedPair (branchNumerator P b) (branchCube P b) :=
      ⟨thetaPairOfCondition h.1, h.2⟩
    let i : ThetaIndex := (u, r,
      (branchSubstitution P (fun a ha' => (hA a (Finset.mem_filter.mp ha').1).1)
        (fun a ha' => primeTwist_three c hA (Finset.mem_filter.mp ha').1) b q).1)
    change ‖(p.amplitude : ℂ) *
      (branchCoefficient P b /
        ((Real.sqrt (normIdeal (branchNumerator P b)) * normIdeal (branchCube P b) : ℝ) : ℂ)) *
      maskedCuspColumn hB p.datum i * ordinaryLocalProduct p.active p.exponent i‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha, hc]
    calc
      _ ≤ (p.amplitude * Real.sqrt WE * 27) * Real.sqrt WN :=
        mul_le_mul (mul_le_mul_of_nonneg_left (maskedCuspColumn_norm_le hB p.datum i)
          (mul_nonneg ha (Real.sqrt_nonneg _)))
          (ordinaryLocalProduct_norm_le c p.active p.exponent hA i)
          (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [packetBranchWeight_split, Real.sqrt_mul hn]
        ring
  · simpa only [norm_zero] using mul_nonneg (mul_nonneg (by norm_num) ha) (Real.sqrt_nonneg _)

theorem reflectedBranchPacket_valid (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q)
    (u : Fin 6) (b : exceptionalPrimes p.active p.exponent → Fin 3) :
    (reflectedBranchPacket hB c p hA X u b).Valid c.S D C L := by
  have hs := reflectedBranch_shape hB c p hA D C L X Q hp u b
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, ?_, ?_⟩
  · exact reflectedBranchArray_norm_le hB c p hA hp.2.2.2.2.1 u b
  · exact reflectedBranchCoeff_norm_le c p u b hp.2.2.2.2.2.2.1

theorem branch_frequency_denominator_prod (P : Finset (Ideal O)) (b : P → Fin 3) :
    normIdeal (branchNumerator P b) * normIdeal (branchCube P b) ^ 3 =
      ∏ p : P, ((if b p = 1 then normIdeal p.1 else 1) *
        (if b p = 2 then normIdeal p.1 ^ 3 else 1)) := by
  rw [branchNumerator_norm_prod, branchCube_norm_prod, ← Finset.prod_pow,
    Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : b p = 2 <;> simp [hp]

theorem branchScale_prod (P : Finset (Ideal O)) (hP : ∀ p ∈ P, Prime p)
    (b : P → Fin 3) :
    (∏ p : P, reflectionLocalScale (normIdeal p.1) 4 (branchCode (b p))) =
      (∏ p : P, normIdeal p.1 ^ 2) /
        (normIdeal (branchNumerator P b) * normIdeal (branchCube P b) ^ 3) := by
  rw [branch_frequency_denominator_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  exact (localBranchScale (normIdeal_pos (hP p.1 p.2).ne_zero) (b p)).symm

theorem packetBranchScale_split (A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hA : ∀ p ∈ A, Prime p) (b : exceptionalPrimes A j → Fin 3) :
    packetBranchScale A j b = (∏ p ∈ A, normIdeal p ^ 2) /
      (normIdeal (branchNumerator (exceptionalPrimes A j) b) *
        normIdeal (branchCube (exceptionalPrimes A j) b) ^ 3) := by
  have hsplit : packetBranchScale A j b =
      (∏ p ∈ A.filter (fun p => j p ≠ 4), normIdeal p ^ 2) *
        ∏ p : exceptionalPrimes A j,
          reflectionLocalScale (normIdeal p.1) 4 (branchCode (b p)) := by
    unfold packetBranchScale
    rw [← Finset.prod_filter_not_mul_prod_filter A (fun p => j p = 4)]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      simp only [reflectionLocalScale, if_neg (Finset.mem_filter.mp hp).2]
    · change (∏ p ∈ exceptionalPrimes A j,
        reflectionLocalScale (normIdeal p) (j p) (packetBranchAssignment A j b p)) = _
      rw [← Finset.prod_coe_sort (exceptionalPrimes A j)
        (fun p => reflectionLocalScale (normIdeal p) (j p) (packetBranchAssignment A j b p))]
      apply Finset.prod_congr rfl
      intro p _
      simp only [packetBranchAssignment, dif_pos p.2, (Finset.mem_filter.mp p.2).2]
  rw [hsplit]
  calc
    _ = (∏ p ∈ A.filter (fun p => j p ≠ 4), normIdeal p ^ 2) *
        ((∏ p : exceptionalPrimes A j, normIdeal p.1 ^ 2) /
          (normIdeal (branchNumerator (exceptionalPrimes A j) b) *
            normIdeal (branchCube (exceptionalPrimes A j) b) ^ 3)) :=
      congrArg (fun z : ℝ => (∏ p ∈ A.filter (fun p => j p ≠ 4), normIdeal p ^ 2) * z)
        (branchScale_prod (exceptionalPrimes A j)
          (fun p hp => hA p (Finset.mem_filter.mp hp).1) b)
    _ = _ := by
      rw [← mul_div_assoc]
      congr 1
      exact (congrArg
        (fun z : ℝ => (∏ p ∈ A.filter (fun p => j p ≠ 4), normIdeal p ^ 2) * z)
        (Finset.prod_coe_sort (exceptionalPrimes A j) (fun p : Ideal O => normIdeal p ^ 2))).trans
          (Finset.prod_filter_not_mul_prod_filter A (fun p => j p = 4)
            (fun p : Ideal O => normIdeal p ^ 2))

theorem normElement_reflectionDenominator_union (c : ArithmeticContext)
    (d : ReflectionDatum) (A : Finset (Ideal O)) (hA : PrimeTwistSet c.S A)
    {k : Ideal O} (hk : SquarefreeOutside c.S k) (hcop : IsRelPrime k (∏ p ∈ A, p)) :
    normElement (reflectionDenominator d (A ∪ primeFactors k)) =
      normElement d.denominator * (∏ p ∈ A, normIdeal p) * normIdeal k := by
  have hd := PacketCharacters.primeFactors_disjoint (fun p hp => (hA p hp).1) hcop
  rw [normElement_reflectionDenominator d _ (by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact primeTwist_three c hA hp
    · exact PacketCharacters.outside_prime_relPrime_three c
        (PacketCharacters.primeFactors_prime hp)
        (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors hk.1
          (Multiset.mem_toFinset.mp hp))), Finset.prod_union hd]
  have hkN : (∏ p ∈ primeFactors k, normIdeal p) = normIdeal k := by
    calc
      _ = normIdeal (∏ p ∈ primeFactors k, p) := by
        simp only [normIdeal, map_prod, Nat.cast_prod]
      _ = _ := congrArg normIdeal (PacketCharacters.primeFactors_prod hk.1.1 hk.2)
  rw [hkN]
  ring


def initialScale (X : ℝ) (p : RawReflectionPacket) : ℝ :=
  rawReflectionScale X p * ∏ a ∈ p.active, normIdeal a ^ 2

def initialCoeff (p : RawReflectionPacket) (u : Fin 6)
    (r : ℕ) (k : Ideal O) : ℂ :=
  p.coeff k * sexticSymbol k ((unitSlot u : O) * lambda ^ r) ^ 3

def initialArray (hB : ThetaBoundsStatement) (p : RawReflectionPacket)
    (u : Fin 6) : ℕ → Ideal O → Ideal O → ℂ :=
  arrayOfIndex u (fun i =>
    (p.amplitude : ℂ) * maskedCuspColumn hB p.datum i * ordinaryLocalProduct p.active p.exponent i)

def initialTerm (hB : ThetaBoundsStatement) (p : RawReflectionPacket)
    (W : ℝ → ℂ) (X : ℝ) (u : Fin 6) (k : Ideal O) (q : ℕ × ThetaPair) : ℂ :=
  preparedThetaTerm W p.H (initialScale X p) (initialArray hB p u) (initialCoeff p u)
    k (q.1, q.2.n, q.2.b)

theorem initialCoeff_norm_le (c : ArithmeticContext) (p : RawReflectionPacket)
    (u : Fin 6) (r : ℕ) (k : Ideal O) (hk : Outside c.S k) (hc : ‖p.coeff k‖ ≤ 1) :
    ‖initialCoeff p u r k‖ ≤ 1 := by
  rw [initialCoeff, norm_mul, norm_pow]
  have hs := pow_le_pow_left₀ (norm_nonneg _)
    (PacketCharacters.sexticSymbol_norm_le_one c hk ((unitSlot u : O) * lambda ^ r)) 3
  simpa only [one_pow, one_mul] using mul_le_mul hc hs
    (pow_nonneg (norm_nonneg _) _) zero_le_one

theorem initialArray_norm_le (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (ha : 0 ≤ p.amplitude) (u : Fin 6) :
    ∀ r n b, ‖initialArray hB p u r n b‖ ≤
      27 * p.amplitude * Real.sqrt
        (∏ a ∈ p.active.filter (fun a => p.exponent a ≠ 4),
          reflectionLocalWeight (normIdeal a) (p.exponent a) .unchanged) := by
  apply arrayOfIndex_bound
  · exact mul_nonneg (mul_nonneg (by norm_num) ha) (Real.sqrt_nonneg _)
  · intro i
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
    calc
      _ ≤ (p.amplitude * 27) * Real.sqrt
          (∏ a ∈ p.active.filter (fun a => p.exponent a ≠ 4),
            reflectionLocalWeight (normIdeal a) (p.exponent a) .unchanged) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (maskedCuspColumn_norm_le hB p.datum i) ha)
          (ordinaryLocalProduct_norm_le c p.active p.exponent hA i)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem initialScale_pos (c : ArithmeticContext) (p : RawReflectionPacket)
    (hA : PrimeTwistSet c.S p.active) (X : ℝ) (hX : 0 < rawReflectionScale X p) :
    0 < initialScale X p := by
  apply mul_pos hX
  exact Finset.prod_pos (fun a ha => sq_pos_of_pos (normIdeal_pos (hA a ha).1.ne_zero))

theorem initialTerm_summable (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (I : SupportInterval) (W : ℝ → ℂ)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q)
    (hW : SmoothSupported I W) (u : Fin 6)
    (k : Ideal O) (hk : k ∈ sieveRows c.S p.H) :
    Summable (fun q : ℕ × ThetaPair => ‖initialTerm hB p W X u k q‖) := by
  obtain ⟨hH, hHC, hY, hYB, ha, hA, hc, hz, hcount⟩ := hp
  have hk' := (mem_sieveRows _ _ _).mp hk
  exact preparedThetaTerm_summable_supported hB hW p.H (initialScale X p) _
    (zero_lt_one.trans_le hH) (initialScale_pos c p hA X hY)
    (mul_nonneg (mul_nonneg (by norm_num) ha) (Real.sqrt_nonneg _))
    (initialArray hB p u) (initialCoeff p u) k hk'.1.1.1
    (initialArray_norm_le hB c p hA ha u)
    (fun r => initialCoeff_norm_le c p u r k hk'.1.1 (hc k hk))

theorem initialTerm_joint_summable (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (I : SupportInterval) (W : ℝ → ℂ)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q)
    (hW : SmoothSupported I W) (k : Ideal O) (hk : k ∈ sieveRows c.S p.H) :
    Summable (fun i : ThetaIndex => ‖initialTerm hB p W X i.1 k i.2‖) := by
  apply (summable_prod_of_nonneg (fun i => norm_nonneg _)).mpr
  exact ⟨fun u => initialTerm_summable hB c p I W D C L X Q hp hW u k hk,
    (hasSum_fintype _).summable⟩

theorem indexMode_cubic_factor (c : ArithmeticContext) {k : Ideal O}
    (hk : Outside c.S k) (i : ThetaIndex) :
    sexticSymbol k (indexMode i) ^ 3 =
      sexticSymbol k ((unitSlot i.1 : O) * lambda ^ i.2.1) ^ 3 *
        sexticSymbol k (primaryGenerator i.2.2.n * primaryGenerator i.2.2.b) ^ 3 := by
  unfold indexMode
  rw [← mul_assoc]
  exact PacketCharacters.sexticSymbol_cubic_factor c hk _ _ _

theorem pairSubstitution_cubic_factor (c : ArithmeticContext) {k D E : Ideal O}
    (hk : Outside c.S k) (hD : Squarefree D) (hD0 : D ≠ ⊥) (hE0 : E ≠ ⊥)
    (hD3 : IsRelPrime D (principal 3)) (hE3 : IsRelPrime E (principal 3))
    (hED : IsRelPrime E D) (u : Fin 6) (r : ℕ) (q : SubstitutedPair D E) :
    sexticSymbol k ((unitSlot u : O) * lambda ^ r) ^ 3 *
      sexticSymbol k (primaryGenerator (D * q.1.n) * primaryGenerator (E * q.1.b)) ^ 3 =
        sexticSymbol k ((unitSlot u : O) * lambda ^ r * primaryGenerator D * primaryGenerator E ^ 3) ^ 3 *
          sexticSymbol k (primaryGenerator q.1.n * primaryGenerator q.1.b) ^ 3 := by
  have hi := indexMode_cubic_factor c hk
    (u, r, (pairSubstitution hD hD0 hE0 hD3 hE3 hED q).1)
  change sexticSymbol k (indexMode (u, r, (pairSubstitution hD hD0 hE0 hD3 hE3 hED q).1)) ^ 3 =
    sexticSymbol k ((unitSlot u : O) * lambda ^ r) ^ 3 *
      sexticSymbol k (primaryGenerator (D * q.1.n) * primaryGenerator (E * q.1.b)) ^ 3 at hi
  rw [← hi, pairSubstitution_indexMode]
  rw [← mul_assoc]
  exact PacketCharacters.sexticSymbol_cubic_factor c hk _ _ _



theorem preparedThetaTerm_indexed (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k : Ideal O) (u : Fin 6) (r : ℕ) (q : ThetaPair) :
    preparedThetaTerm W H Y A coeff k (r, q.n, q.b) =
      coeff r k * A r q.n q.b *
        sexticSymbol k (primaryGenerator q.n * primaryGenerator q.b) ^ 3 /
          (columnDenominator (u, r, q) : ℂ) *
        thetaWeight (fun x => (Real.sqrt x : ℂ) * W x)
          (Complex.normSq (latticeFrequency (indexMode (u, r, q))) * H ^ 2 /
            (Y * normIdeal k ^ 2)) := by
  rw [normSq_latticeFrequency_indexMode]
  exact if_pos (thetaPair_condition q)

theorem raw_argument_eq_initial (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (X : ℝ) (hX : 0 < X) (hH : 0 < p.H)
    {k : Ideal O} (hk : SquarefreeOutside c.S k)
    (hcop : IsRelPrime k (∏ a ∈ p.active, a)) (i : ThetaIndex) :
    Complex.normSq (latticeFrequency (indexMode i)) * X /
        normElement (reflectionDenominator p.datum (p.active ∪ primeFactors k)) ^ 2 =
      Complex.normSq (latticeFrequency (indexMode i)) * p.H ^ 2 /
        (initialScale X p * normIdeal k ^ 2) := by
  have hd0 : principal p.datum.denominator ≠ ⊥ := fun h =>
    p.datum.denominator_ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have hd : normElement p.datum.denominator ≠ 0 := (normIdeal_pos hd0).ne'
  have hA0 : (∏ a ∈ p.active, normIdeal a) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a ha => (normIdeal_pos (hA a ha).1.ne_zero).ne')
  rw [normElement_reflectionDenominator_union c p.datum p.active hA hk hcop]
  rw [initialScale, rawReflectionScale, Finset.prod_pow]
  exact dual_scale_identity _ _ _ _ _ _ hd hA0 hH.ne' hX.ne'

theorem raw_indexed_term_eq_initial (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (hH : 0 < p.H)
    {k : Ideal O} (hk : SquarefreeOutside c.S k)
    (hcop : IsRelPrime k (∏ a ∈ p.active, a)) (i : ThetaIndex) :
    (p.amplitude : ℂ) * p.coeff k *
      (if i ∈ selectedIndices hB p.datum.cusp then
        indexedDualTerm p.datum (p.active ∪ primeFactors k)
          (variableTwistExponents p.active p.exponent)
          (fun x => (Real.sqrt x : ℂ) * W x) X i else 0) =
      (∏ a ∈ exceptionalPrimes p.active p.exponent, exceptionalMultiplier a i.2.2) *
        initialTerm hB p W X i.1 k i.2 := by
  rw [initialTerm, preparedThetaTerm_indexed W p.H (initialScale X p)
    (initialArray hB p i.1) (initialCoeff p i.1) k i.1 i.2.1 i.2.2,
    initialArray, arrayOfIndex_apply, initialCoeff]
  by_cases hi : i ∈ selectedIndices hB p.datum.cusp
  · rw [if_pos hi, indexedDualTerm,
      PacketCharacters.thetaLocalFactor_union c hk p.active hA hcop,
      active_local_product_split p.active p.exponent
        (fun a ha => (hA a ha).1) (fun a ha => primeTwist_three c hA ha),
      indexMode_cubic_factor c hk.1,
      raw_argument_eq_initial c p hA X hX hH hk hcop]
    simp only [maskedCuspColumn, if_pos hi]
    ring
  · simp only [if_neg hi, maskedCuspColumn, if_neg hi, mul_zero, zero_mul, zero_div]

theorem raw_row_eq_initial_joint (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (hH : 0 < p.H)
    {k : Ideal O} (hk : SquarefreeOutside c.S k)
    (hcop : IsRelPrime k (∏ a ∈ p.active, a)) :
    rawReflectionRow W X p k =
      ∑' i : ThetaIndex,
        (∏ a ∈ exceptionalPrimes p.active p.exponent, exceptionalMultiplier a i.2.2) *
          initialTerm hB p W X i.1 k i.2 := by
  rw [rawReflectionRow, dualThetaSum_eq_selected hB, ← tsum_mul_left]
  apply tsum_congr
  exact raw_indexed_term_eq_initial hB c p hA W X hX hH hk hcop

set_option maxHeartbeats 800000 in
theorem raw_row_eq_branches (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (I : SupportInterval) (W : ℝ → ℂ)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q)
    (hW : SmoothSupported I W) (hX : 0 < X)
    (k : Ideal O) (hk : k ∈ sieveRows c.S p.H)
    (hcop : IsRelPrime k (∏ a ∈ p.active, a)) :
    let P := exceptionalPrimes p.active p.exponent
    let hA := hp.2.2.2.2.2.1
    let hP : ∀ a ∈ P, Prime a := fun a ha => (hA a (Finset.mem_filter.mp ha).1).1
    let h3 : ∀ a ∈ P, IsRelPrime a (principal 3) :=
      fun a ha => primeTwist_three c hA (Finset.mem_filter.mp ha).1
    rawReflectionRow W X p k =
      ∑ b : P → Fin 3, branchCoefficient P b *
        ∑' q : (Fin 6 × ℕ) × SubstitutedPair (branchNumerator P b) (branchCube P b),
          initialTerm hB p W X q.1.1 k
            (q.1.2, (branchSubstitution P hP h3 b q.2).1) := by
  dsimp only
  let e := Equiv.prodAssoc (Fin 6) ℕ ThetaPair
  have hs := initialTerm_joint_summable hB c p I W D C L X Q hp hW k hk
  have he : Summable (fun q : (Fin 6 × ℕ) × ThetaPair =>
      ‖initialTerm hB p W X q.1.1 k (q.1.2, q.2)‖) := e.summable_iff.mpr hs
  rw [raw_row_eq_initial_joint hB c p hp.2.2.2.2.2.1 W X hX
    (zero_lt_one.trans_le hp.1) ((mem_sieveRows _ _ _).mp hk).1 hcop]
  rw [← e.tsum_eq (fun i : ThetaIndex =>
    (∏ a ∈ exceptionalPrimes p.active p.exponent, exceptionalMultiplier a i.2.2) *
      initialTerm hB p W X i.1 k i.2)]
  exact exceptional_product_substitution_with_parameter
    (exceptionalPrimes p.active p.exponent)
    (fun a ha => (hp.2.2.2.2.2.1 a (Finset.mem_filter.mp ha).1).1)
    (fun a ha => primeTwist_three c hp.2.2.2.2.2.1 (Finset.mem_filter.mp ha).1)
    (fun q : (Fin 6 × ℕ) × ThetaPair => initialTerm hB p W X q.1.1 k (q.1.2, q.2)) he


theorem branch_column_algebra (c a B m o u v s w d e t : ℂ)
    (hχ : u * v = s * w) :
    B * ((c * u) * (a * m * o) * v / (d * e) * t) =
      (c * s) * (a * (B / e) * m * o) * w / d * t := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (c * a * B * m * o * d⁻¹ * e⁻¹ * t) * (u * v) := by ring
    _ = _ := by rw [hχ]; ring

theorem reflectedBranchArray_apply (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (u : Fin 6) (b : exceptionalPrimes p.active p.exponent → Fin 3) (r : ℕ)
    (q : SubstitutedPair (branchNumerator (exceptionalPrimes p.active p.exponent) b)
      (branchCube (exceptionalPrimes p.active p.exponent) b)) :
    let P := exceptionalPrimes p.active p.exponent
    let hP : ∀ a ∈ P, Prime a := fun a ha => (hA a (Finset.mem_filter.mp ha).1).1
    let h3 : ∀ a ∈ P, IsRelPrime a (principal 3) :=
      fun a ha => primeTwist_three c hA (Finset.mem_filter.mp ha).1
    let i : ThetaIndex := (u, r, (branchSubstitution P hP h3 b q).1)
    reflectedBranchArray hB c p hA u b r q.1.n q.1.b =
      (p.amplitude : ℂ) *
        (branchCoefficient P b /
          ((Real.sqrt (normIdeal (branchNumerator P b)) * normIdeal (branchCube P b) : ℝ) : ℂ)) *
        maskedCuspColumn hB p.datum i * ordinaryLocalProduct p.active p.exponent i := by
  dsimp only
  rw [reflectedBranchArray, dif_pos ⟨thetaPair_condition q.1, q.2⟩]
  have he : (⟨thetaPairOfCondition (thetaPair_condition q.1), q.2⟩ :
      SubstitutedPair (branchNumerator (exceptionalPrimes p.active p.exponent) b)
        (branchCube (exceptionalPrimes p.active p.exponent) b)) = q := by
    apply Subtype.ext
    exact thetaPair_ext rfl rfl
  dsimp only
  rw [he]

theorem branchY_eq_initial (p : RawReflectionPacket)
    (hA : ∀ a ∈ p.active, Prime a) (X : ℝ)
    (b : exceptionalPrimes p.active p.exponent → Fin 3) :
    rawReflectionScale X p * packetBranchScale p.active p.exponent b =
      initialScale X p /
        (normIdeal (branchNumerator (exceptionalPrimes p.active p.exponent) b) *
          normIdeal (branchCube (exceptionalPrimes p.active p.exponent) b) ^ 3) := by
  rw [packetBranchScale_split p.active p.exponent hA, initialScale, ← mul_div_assoc]

theorem initialTerm_branch_eq_prepared (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (W : ℝ → ℂ) (X : ℝ) (u : Fin 6)
    (b : exceptionalPrimes p.active p.exponent → Fin 3)
    (r : ℕ) (k : Ideal O) (hk : Outside c.S k)
    (q : SubstitutedPair (branchNumerator (exceptionalPrimes p.active p.exponent) b)
      (branchCube (exceptionalPrimes p.active p.exponent) b)) :
    let P := exceptionalPrimes p.active p.exponent
    let hP : ∀ a ∈ P, Prime a := fun a ha => (hA a (Finset.mem_filter.mp ha).1).1
    let h3 : ∀ a ∈ P, IsRelPrime a (principal 3) :=
      fun a ha => primeTwist_three c hA (Finset.mem_filter.mp ha).1
    branchCoefficient P b * initialTerm hB p W X u k
      (r, (branchSubstitution P hP h3 b q).1) =
        preparedThetaTerm W p.H
          (rawReflectionScale X p * packetBranchScale p.active p.exponent b)
          (reflectedBranchArray hB c p hA u b) (reflectedBranchCoeff p u b)
          k (r, q.1.n, q.1.b) := by
  dsimp only
  let P := exceptionalPrimes p.active p.exponent
  let hP : ∀ a ∈ P, Prime a := fun a ha => (hA a (Finset.mem_filter.mp ha).1).1
  let h3 : ∀ a ∈ P, IsRelPrime a (principal 3) :=
      fun a ha => primeTwist_three c hA (Finset.mem_filter.mp ha).1
  let z := branch_substitution_data P hP h3 b
  let q' := (branchSubstitution P hP h3 b q).1
  have hχ := pairSubstitution_cubic_factor c hk z.1 z.2.1 z.2.2.1 z.2.2.2.1
    z.2.2.2.2.1 z.2.2.2.2.2 u r q
  have hden := pairSubstitution_columnDenominator z.1 z.2.1 z.2.2.1 z.2.2.2.1
    z.2.2.2.2.1 z.2.2.2.2.2 u r q
  have hfreq := pairSubstitution_frequency_normSq z.1 z.2.1 z.2.2.1 z.2.2.2.1
    z.2.2.2.2.1 z.2.2.2.2.2 u r q
  change columnDenominator (u, r, q') =
    columnDenominator (u, r, q.1) * Real.sqrt (normIdeal (branchNumerator P b)) *
      normIdeal (branchCube P b) at hden
  change Complex.normSq (latticeFrequency (indexMode (u, r, q'))) =
    Complex.normSq (latticeFrequency (indexMode (u, r, q.1))) *
      normIdeal (branchNumerator P b) * normIdeal (branchCube P b) ^ 3 at hfreq
  rw [initialTerm, preparedThetaTerm_indexed W p.H (initialScale X p)
    (initialArray hB p u) (initialCoeff p u) k u r q',
    initialArray, arrayOfIndex_apply, initialCoeff,
    preparedThetaTerm_indexed W p.H _ _ _ k u r q.1,
    reflectedBranchArray_apply, reflectedBranchCoeff,
    hden, hfreq, branchY_eq_initial p (fun a ha => (hA a ha).1)]
  rw [pairSubstitution_scale _ _ _ _ _ _
    (normIdeal_pos z.2.1).ne' (normIdeal_pos z.2.2.1).ne']
  have hdenC : ((columnDenominator (u, r, q.1) *
      Real.sqrt (normIdeal (branchNumerator P b)) * normIdeal (branchCube P b) : ℝ) : ℂ) =
      (columnDenominator (u, r, q.1) : ℂ) *
        ((Real.sqrt (normIdeal (branchNumerator P b)) * normIdeal (branchCube P b) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdenC]
  exact branch_column_algebra _ _ _ _ _ _ _ _ _ _ _ _ hχ

theorem reflectedBranchArray_zero (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (u : Fin 6) (b : exceptionalPrimes p.active p.exponent → Fin 3) (r : ℕ)
    (q : ThetaPair)
    (hq : ¬ (IsRelPrime (branchNumerator (exceptionalPrimes p.active p.exponent) b) q.n ∧
      IsRelPrime (branchCube (exceptionalPrimes p.active p.exponent) b) q.n)) :
    reflectedBranchArray hB c p hA u b r q.n q.b = 0 := by
  exact dif_neg (fun h => hq h.2)

theorem prepared_branch_row_eq_restricted (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (hA : PrimeTwistSet c.S p.active)
    (W : ℝ → ℂ) (X : ℝ) (u : Fin 6)
    (b : exceptionalPrimes p.active p.exponent → Fin 3) (k : Ideal O) :
    let t := reflectedBranchPacket hB c p hA X u b
    preparedThetaRow W t.H t.Y t.A t.coeff k =
      ∑' q : ℕ × SubstitutedPair (branchNumerator (exceptionalPrimes p.active p.exponent) b)
        (branchCube (exceptionalPrimes p.active p.exponent) b),
        preparedThetaTerm W t.H t.Y t.A t.coeff k (q.1, q.2.1.n, q.2.1.b) := by
  dsimp only
  rw [preparedThetaRow_eq_supported]
  let g := fun q : ℕ × SubstitutedPair
      (branchNumerator (exceptionalPrimes p.active p.exponent) b)
      (branchCube (exceptionalPrimes p.active p.exponent) b) => (q.1, q.2.1)
  have hg : Function.Injective g := by
    intro x y h
    have hr := congrArg (fun z : ℕ × ThetaPair => z.1) h
    have hq := congrArg (fun z : ℕ × ThetaPair => z.2) h
    exact Prod.ext hr (Subtype.ext hq)
  apply (hg.tsum_eq _).symm
  intro q hq
  by_cases h : IsRelPrime (branchNumerator (exceptionalPrimes p.active p.exponent) b) q.2.n ∧
      IsRelPrime (branchCube (exceptionalPrimes p.active p.exponent) b) q.2.n
  · exact ⟨(q.1, ⟨q.2, h⟩), rfl⟩
  · exfalso
    apply hq
    dsimp only [reflectedBranchPacket]
    rw [preparedThetaTerm_indexed W _ _ _ _ k u q.1 q.2]
    change _ * reflectedBranchArray hB c p hA u b q.1 q.2.n q.2.b * _ / _ * _ = 0
    rw [reflectedBranchArray_zero hB c p hA u b q.1 q.2 h]
    simp only [mul_zero, zero_mul, zero_div]

theorem tsum_finite_units {S : Type*} (F : (Fin 6 × ℕ) × S → ℂ)
    (hF : Summable F) :
    (∑' q, F q) = ∑ u : Fin 6, ∑' q : ℕ × S, F ((u, q.1), q.2) := by
  let e := Equiv.prodAssoc (Fin 6) ℕ S
  calc
    _ = ∑' q : Fin 6 × (ℕ × S), F ((q.1, q.2.1), q.2.2) :=
      (e.symm.tsum_eq F).symm
    _ = _ := by
      have h : Summable (fun q : Fin 6 × (ℕ × S) => F ((q.1, q.2.1), q.2.2)) :=
        e.symm.summable_iff.mpr hF
      exact h.tsum_prod.trans (tsum_fintype _)



theorem branch_original_index_injective (P : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (h3 : ∀ p ∈ P, IsRelPrime p (principal 3))
    (b : P → Fin 3) :
    Function.Injective (fun q : (Fin 6 × ℕ) ×
      SubstitutedPair (branchNumerator P b) (branchCube P b) =>
        ((q.1.1, q.1.2, (branchSubstitution P hP h3 b q.2).1) : ThetaIndex)) := by
  have h := branch_substitution_data P hP h3 b
  have hi := Subtype.val_injective.comp
    (pairSubstitution_bijective h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2).1
  intro x y hxy
  have hu := congrArg (fun i : ThetaIndex => i.1) hxy
  have hr := congrArg (fun i : ThetaIndex => i.2.1) hxy
  have hq := congrArg (fun i : ThetaIndex => i.2.2) hxy
  exact Prod.ext (Prod.ext hu hr) (hi hq)

theorem summable_norm_mul_comp {ι κ : Type*} (F : ι → ℂ) (a : ℂ)
    (e : κ → ι) (he : Function.Injective e) (hF : Summable (fun i => ‖F i‖)) :
    Summable (fun j => ‖a * F (e j)‖) := by
  have h : Summable (fun j => ‖F (e j)‖) := hF.comp_injective he
  simpa only [norm_mul] using h.mul_left ‖a‖

theorem initialTerm_branch_summable (P : Finset (Ideal O))
    (hP : ∀ p ∈ P, Prime p) (h3 : ∀ p ∈ P, IsRelPrime p (principal 3))
    (b : P → Fin 3) (F : ThetaIndex → ℂ) (hF : Summable F) :
    Summable (fun q : (Fin 6 × ℕ) ×
      SubstitutedPair (branchNumerator P b) (branchCube P b) =>
        branchCoefficient P b * F (q.1.1, q.1.2, (branchSubstitution P hP h3 b q.2).1)) := by
  have h : Summable (fun q : (Fin 6 × ℕ) ×
      SubstitutedPair (branchNumerator P b) (branchCube P b) =>
        F (q.1.1, q.1.2, (branchSubstitution P hP h3 b q.2).1)) :=
    hF.comp_injective (branch_original_index_injective P hP h3 b)
  exact h.mul_left (branchCoefficient P b)

set_option maxHeartbeats 800000 in
theorem branch_sum_eq_prepared (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (I : SupportInterval) (W : ℝ → ℂ)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q)
    (hW : SmoothSupported I W) (k : Ideal O) (hk : k ∈ sieveRows c.S p.H)
    (b : exceptionalPrimes p.active p.exponent → Fin 3) :
    let P := exceptionalPrimes p.active p.exponent
    let hA := hp.2.2.2.2.2.1
    let hP : ∀ a ∈ P, Prime a := fun a ha => (hA a (Finset.mem_filter.mp ha).1).1
    let h3 : ∀ a ∈ P, IsRelPrime a (principal 3) :=
      fun a ha => primeTwist_three c hA (Finset.mem_filter.mp ha).1
    branchCoefficient P b *
      (∑' q : (Fin 6 × ℕ) × SubstitutedPair (branchNumerator P b) (branchCube P b),
        initialTerm hB p W X q.1.1 k (q.1.2, (branchSubstitution P hP h3 b q.2).1)) =
      ∑ u : Fin 6,
        let t := reflectedBranchPacket hB c p hA X u b
        preparedThetaRow W t.H t.Y t.A t.coeff k := by
  dsimp only
  rw [← tsum_mul_left]
  rw [tsum_finite_units _ (initialTerm_branch_summable
    (exceptionalPrimes p.active p.exponent)
    (fun a ha => (hp.2.2.2.2.2.1 a (Finset.mem_filter.mp ha).1).1)
    (fun a ha => primeTwist_three c hp.2.2.2.2.2.1 (Finset.mem_filter.mp ha).1) b
    (fun i : ThetaIndex => initialTerm hB p W X i.1 k i.2)
    (initialTerm_joint_summable hB c p I W D C L X Q hp hW k hk).of_norm)]
  apply Finset.sum_congr rfl
  intro u _
  rw [prepared_branch_row_eq_restricted]
  apply tsum_congr
  intro q
  exact initialTerm_branch_eq_prepared hB c p hp.2.2.2.2.2.1 W X u b q.1 k
    ((mem_sieveRows _ _ _).mp hk).1.1 q.2

theorem preparedThetaRow_zero_of_coeff (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k : Ideal O) (hc : ∀ r, coeff r k = 0) :
    preparedThetaRow W H Y A coeff k = 0 := by
  simp only [preparedThetaRow, preparedThetaTerm, hc, zero_mul, zero_div, ite_self, tsum_zero]

set_option maxHeartbeats 800000 in
theorem raw_row_eq_branch_packets (hB : ThetaBoundsStatement) (c : ArithmeticContext)
    (p : RawReflectionPacket) (I : SupportInterval) (W : ℝ → ℂ)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q)
    (hW : SmoothSupported I W) (hX : 0 < X)
    (k : Ideal O) (hk : k ∈ sieveRows c.S p.H) :
    rawReflectionRow W X p k =
      ∑ b : exceptionalPrimes p.active p.exponent → Fin 3, ∑ u : Fin 6,
        let t := reflectedBranchPacket hB c p hp.2.2.2.2.2.1 X u b
        preparedThetaRow W t.H t.Y t.A t.coeff k := by
  by_cases hcop : IsRelPrime k (∏ a ∈ p.active, a)
  · rw [raw_row_eq_branches hB c p I W D C L X Q hp hW hX k hk hcop]
    apply Finset.sum_congr rfl
    intro b _
    exact branch_sum_eq_prepared hB c p I W D C L X Q hp hW k hk b
  · have hzero := hp.2.2.2.2.2.2.2.1 k hk hcop
    have hz : ∀ b : exceptionalPrimes p.active p.exponent → Fin 3, ∀ u : Fin 6,
        let t := reflectedBranchPacket hB c p hp.2.2.2.2.2.1 X u b
        preparedThetaRow W t.H t.Y t.A t.coeff k = 0 := by
      intro b u
      apply preparedThetaRow_zero_of_coeff
      intro r
      simp only [reflectedBranchPacket, reflectedBranchCoeff, hzero, zero_mul]
    simp only [rawReflectionRow, hzero, mul_zero, zero_mul, hz, Finset.sum_const_zero]


def finiteFamilyExtend {ι κ α : Type*} (e : ι ↪ κ) (f : ι → α) (z : α)
    (j : κ) : α :=
  if h : ∃ i, e i = j then f (Classical.choose h) else z

theorem finiteFamilyExtend_apply {ι κ α : Type*} (e : ι ↪ κ) (f : ι → α)
    (z : α) (i : ι) : finiteFamilyExtend e f z (e i) = f i := by
  let h : ∃ a, e a = e i := ⟨i, rfl⟩
  rw [finiteFamilyExtend, dif_pos h]
  exact congrArg f (e.injective (Classical.choose_spec h))

theorem finiteFamilyExtend_property {ι κ α : Type*} (e : ι ↪ κ) (f : ι → α)
    (z : α) (P : α → Prop) (hf : ∀ i, P (f i)) (hz : P z) (j : κ) :
    P (finiteFamilyExtend e f z j) := by
  unfold finiteFamilyExtend
  split_ifs with h
  · exact hf _
  · exact hz

theorem finiteFamilyExtend_sum {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (f : ι → α) (z : α) (g : α → ℂ) (hz : g z = 0) :
    (∑ j : κ, g (finiteFamilyExtend e f z j)) = ∑ i : ι, g (f i) := by
  calc
    _ = ∑ j ∈ Finset.univ.map e, g (finiteFamilyExtend e f z j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hn : ¬ ∃ i, e i = j := by
        rintro ⟨i, hi⟩
        exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [finiteFamilyExtend, dif_neg hn, hz]
    _ = _ := by
      rw [Finset.sum_map]
      simp only [finiteFamilyExtend_apply]

abbrev ReflectedBranchIndex (p : RawReflectionPacket) :=
  (exceptionalPrimes p.active p.exponent → Fin 3) × Fin 6

theorem reflectedBranchIndex_card_le (p : RawReflectionPacket) (Q : ℕ)
    (hQ : 6 * 3 ^ p.active.card ≤ Q) : Fintype.card (ReflectedBranchIndex p) ≤ Q := by
  simp only [ReflectedBranchIndex, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_coe]
  calc
    _ = 6 * 3 ^ (exceptionalPrimes p.active p.exponent).card := Nat.mul_comm _ _
    _ ≤ 6 * 3 ^ p.active.card := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (Finset.card_filter_le _ _))
    _ ≤ Q := hQ

def zeroReflectionPacket (p : RawReflectionPacket) (X : ℝ) : ReflectionPacket where
  H := p.H
  Y := initialScale X p
  amplitude := 0
  A := fun _ _ _ => 0
  coeff := fun _ _ => 0

theorem zeroReflectionPacket_valid (c : ArithmeticContext) (p : RawReflectionPacket)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q) :
    (zeroReflectionPacket p X).Valid c.S D C L := by
  refine ⟨hp.1, hp.2.1,
    initialScale_pos c p hp.2.2.2.2.2.1 X hp.2.2.1,
    hp.2.2.2.1, le_rfl, ?_, ?_⟩
  · intro r n b
    simp only [zeroReflectionPacket, norm_zero, le_refl]
  · intro r k hk
    simp only [zeroReflectionPacket, norm_zero, zero_le_one]

theorem rawReflectionCost_nonneg (p : RawReflectionPacket) : 0 ≤ rawReflectionCost p := by
  apply Finset.prod_nonneg
  intro a ha
  unfold reflectionLocalCost
  split_ifs
  · exact Nat.cast_nonneg _
  · exact sq_nonneg _

theorem zeroReflectionPacket_property (c : ArithmeticContext) (p : RawReflectionPacket)
    (D C L X : ℝ) (Q : ℕ) (hp : p.Valid c.S D C L X Q) :
    (zeroReflectionPacket p X).Valid c.S D C L ∧
      (zeroReflectionPacket p X).H = p.H ∧
      (zeroReflectionPacket p X).amplitude ^ 2 *
          ((zeroReflectionPacket p X).H + (zeroReflectionPacket p X).Y) ≤
        729 * (p.amplitude ^ 2 *
          (p.H + rawReflectionScale X p * rawReflectionCost p)) := by
  refine ⟨zeroReflectionPacket_valid c p D C L X Q hp, rfl, ?_⟩
  change 0 ^ 2 * (p.H + initialScale X p) ≤ _
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
  exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
    (add_nonneg (zero_le_one.trans hp.1)
      (mul_nonneg hp.2.2.1.le (rawReflectionCost_nonneg p))))

theorem zeroReflectionPacket_row (p : RawReflectionPacket) (W : ℝ → ℂ)
    (X : ℝ) (k : Ideal O) :
    preparedThetaRow W (zeroReflectionPacket p X).H (zeroReflectionPacket p X).Y
      (zeroReflectionPacket p X).A (zeroReflectionPacket p X).coeff k = 0 :=
  preparedThetaRow_zero_of_coeff W _ _ _ _ k (fun _ => rfl)

set_option maxHeartbeats 800000 in
/-- The full literal single-column identity, with the required common finite
index set and coefficients independent of the row variable. -/
theorem dual_theta_packet_identity_proved : DualThetaPacketIdentityStep := by
  intro hB c I W D C L X Q p hW hD hC hL hX hp
  let hA := hp.2.2.2.2.2.1
  let family : ReflectedBranchIndex p → ReflectionPacket := fun i =>
    reflectedBranchPacket hB c p hA X i.2 i.1
  have hcard := reflectedBranchIndex_card_le p Q hp.2.2.2.2.2.2.2.2
  let e : ReflectedBranchIndex p ↪ Fin Q :=
    (Fintype.equivFin (ReflectedBranchIndex p)).toEmbedding.trans (Fin.castLEEmb hcard)
  let packet := finiteFamilyExtend e family (zeroReflectionPacket p X)
  refine ⟨packet, ?_, ?_⟩
  · intro j
    refine finiteFamilyExtend_property e family (zeroReflectionPacket p X)
      (fun t => t.Valid c.S D C L ∧ t.H = p.H ∧
        t.amplitude ^ 2 * (t.H + t.Y) ≤
          729 * (p.amplitude ^ 2 * (p.H + rawReflectionScale X p * rawReflectionCost p)))
      ?_ ?_ j
    · intro i
      have hv := reflectedBranchPacket_valid hB c p hA D C L X Q hp i.2 i.1
      have hs := reflectedBranch_shape hB c p hA D C L X Q hp i.2 i.1
      exact ⟨hv, rfl, hs.2.2.2.2.2.2⟩
    · exact zeroReflectionPacket_property c p D C L X Q hp
  · intro k hk
    change rawReflectionRow W X p k =
      ∑ j : Fin Q, preparedThetaRow W (packet j).H (packet j).Y
        (packet j).A (packet j).coeff k
    rw [finiteFamilyExtend_sum e family (zeroReflectionPacket p X)
      (fun t => preparedThetaRow W t.H t.Y t.A t.coeff k)
      (zeroReflectionPacket_row p W X k)]
    rw [Fintype.sum_prod_type]
    exact raw_row_eq_branch_packets hB c p I W D C L X Q hp hW hX k hk

theorem dual_theta_packet_step_proved : DualThetaPacketStep :=
  dual_theta_packet_step_of_identity dual_theta_packet_identity_proved

end QRHShort.SquarefreeAssembly.PacketConstruction

namespace QRHShort.SquarefreeAssembly.PacketResidualCharacters
open QRHShort.SquarefreeReflection

theorem mulChar_pow_apply_of_isUnit {R : Type*} [CommMonoid R]
    (χ : MulChar R ℂ) (e : ℕ) {x : R} (hx : IsUnit x) :
    (χ ^ e) x = χ x ^ e := by
  simpa only [hx.unit_spec] using MulChar.pow_apply_coe χ e hx.unit

theorem mulChar_prod_apply_of_isUnit {R ι : Type*} [CommMonoid R]
    (s : Finset ι) (χ : ι → MulChar R ℂ) {x : R} (hx : IsUnit x) :
    (∏ i ∈ s, χ i) x = ∏ i ∈ s, χ i x := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using MulChar.one_apply hx
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, MulChar.mul_apply, ih]

theorem refine_rayValue_outside (c : ArithmeticContext) (χ : HeckeCharacter)
    (M : Ideal O) (hM : M ≠ ⊥)
    (hS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S)
    (hle : M ≤ χ.modulus) {n : Ideal O} (hn : Outside c.S n) :
    rayValue (refineHeckeCharacter χ M hM hle) n = rayValue χ n :=
  refineHeckeCharacter_onElement χ M hM hle
    (primaryGenerator_unit_mod_supported c M hM hS hn)

/-- Pure finite assembly: the generator-character premise is exactly the
expanded SPrimeGeneratorRayTarget; the conclusion is exactly the expanded
SResidualRayTarget. No supplementary reciprocity input is asserted here. -/
theorem residual_characters_of_generator_characters
    (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (hprime : ∃ Mp : Ideal O, Mp ≠ ⊥ ∧ Mp ≤ c.rayModulus ∧
      (∀ p : Ideal O, Prime p → p ∣ Mp → p ∈ c.S) ∧
      ∀ p : c.S, ∃ χ : HeckeCharacter, χ.modulus = Mp ∧
        ∀ n : Ideal O, Outside c.S n →
          rayValue χ n = sexticSymbol n (idealGenerator p.val)) :
    ∃ M : Ideal O, M ≠ ⊥ ∧ M ≤ c.rayModulus ∧
      (∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) ∧
      ∀ r : SResidueIndex c, ∃ χ : HeckeCharacter, χ.modulus = M ∧
        ∀ n : Ideal O, Outside c.S n → rayValue χ n = SResidual c r n := by
  obtain ⟨Mp, hMp, hMpRay, hMpS, hprime⟩ := hprime
  obtain ⟨Mu, hMu, hMuRay, hMuS, hunit⟩ :=
    exists_all_unit_residual_characters c hc
  choose χp hχpM hχpval using hprime
  choose χu hχuM hχuval using hunit
  let M : Ideal O := Mu * Mp
  have hM : M ≠ ⊥ := mul_ne_zero hMu hMp
  have hMRay : M ≤ c.rayModulus := Ideal.mul_le_left.trans hMuRay
  have hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S := by
    intro p hp hpM
    rcases hp.dvd_mul.mp hpM with hpu | hpp
    · exact hMuS p hp hpu
    · exact hMpS p hp hpp
  have hχuValue (u : Oˣ) {n : Ideal O} (hn : Outside c.S n) :
      rayValue (χu u) n = sexticSymbol n (u : O) := by
    simpa only [SResidual, SRepresentative, SProduct, Fin.val_zero, pow_zero,
      Finset.prod_const_one, mul_one] using hχuval u n hn
  refine ⟨M, hM, hMRay, hMS, ?_⟩
  intro r
  have hleu : M ≤ (χu r.1).modulus := by
    rw [hχuM r.1]
    exact Ideal.mul_le_left
  have hlep (p : c.S) : M ≤ (χp p).modulus := by
    rw [hχpM p]
    exact Ideal.mul_le_right
  let unitChar := refineHeckeCharacter (χu r.1) M hM hleu
  let primeChar (p : c.S) := refineHeckeCharacter (χp p) M hM (hlep p)
  let unitResidue : MulChar (O ⧸ M) ℂ := unitChar.residue
  let primeResidue (p : c.S) : MulChar (O ⧸ M) ℂ := (primeChar p).residue
  let χ : HeckeCharacter :=
    { modulus := M
      modulus_ne_bot := hM
      residue := unitResidue * ∏ p : c.S, primeResidue p ^ (r.2 p).val
      unit_trivial := by
        intro u
        have hu : IsUnit (Ideal.Quotient.mk M (u : O)) :=
          u.isUnit.map (Ideal.Quotient.mk M)
        rw [MulChar.mul_apply, mulChar_prod_apply_of_isUnit _ _ hu]
        change unitChar.onElement (u : O) *
          (∏ p : c.S, (primeResidue p ^ (r.2 p).val)
            (Ideal.Quotient.mk M (u : O))) = 1
        rw [show unitChar.onElement (u : O) = 1 from unitChar.unit_trivial u, one_mul]
        apply Finset.prod_eq_one
        intro p _
        rw [mulChar_pow_apply_of_isUnit _ _ hu]
        change (primeChar p).onElement (u : O) ^ (r.2 p).val = 1
        rw [show (primeChar p).onElement (u : O) = 1 from (primeChar p).unit_trivial u,
          one_pow] }
  refine ⟨χ, rfl, ?_⟩
  intro n hn
  have hx : IsUnit (Ideal.Quotient.mk M (primaryGenerator n)) :=
    primaryGenerator_unit_mod_supported c M hM hMS hn
  have hunitValue : unitChar.onElement (primaryGenerator n) = sexticSymbol n (r.1 : O) :=
    (refine_rayValue_outside c (χu r.1) M hM hMS hleu hn).trans (hχuValue r.1 hn)
  have hprimeValue (p : c.S) :
      (primeChar p).onElement (primaryGenerator n) = sexticSymbol n (idealGenerator p.val) :=
    (refine_rayValue_outside c (χp p) M hM hMS (hlep p) hn).trans (hχpval p n hn)
  change (unitResidue * ∏ p : c.S, primeResidue p ^ (r.2 p).val)
    (Ideal.Quotient.mk M (primaryGenerator n)) = _
  rw [MulChar.mul_apply, mulChar_prod_apply_of_isUnit _ _ hx]
  change unitChar.onElement (primaryGenerator n) *
    (∏ p : c.S, (primeResidue p ^ (r.2 p).val)
      (Ideal.Quotient.mk M (primaryGenerator n))) = _
  calc
    _ = sexticSymbol n (r.1 : O) *
        ∏ p : c.S, sexticSymbol n (idealGenerator p.val) ^ (r.2 p).val := by
      rw [hunitValue]
      congr 1
      apply Finset.prod_congr rfl
      intro p _
      rw [mulChar_pow_apply_of_isUnit _ _ hx]
      exact congrArg (fun z : ℂ => z ^ (r.2 p).val) (hprimeValue p)
    _ = SResidual c r n := by
      rw [SResidual, SRepresentative, SProduct, sexticSymbol_mul_numerator c hn,
        sexticSymbol_prod_numerator c hn]
      simp only [sexticSymbol_pow_numerator c hn]

end QRHShort.SquarefreeAssembly.PacketResidualCharacters


namespace QRHShort.SquarefreeAssembly
theorem supplementary_reciprocity_proved : SquarefreeReflection.SupplementaryReciprocityStatement := by
  intro c hc
  exact PacketResidualCharacters.residual_characters_of_generator_characters c hc
    ((SquarefreeReflection.sPrimeGeneratorReciprocity_of_local_inputs
      CloudBatch.sf_sprime_ramified_local_proved CloudBatch.sf_sprime_ordinary_local_proved) c hc)
end QRHShort.SquarefreeAssembly

namespace QRHShort.SquarefreeAssembly.PacketConstruction

/-- The part of a squarefree row supported on a fixed finite prime set. -/
def rowFixedPrimes (B : Finset (Ideal O)) (s : Ideal O) : Finset (Ideal O) :=
  primeFactors s ∩ B

def rowFixedPart (B : Finset (Ideal O)) (s : Ideal O) : Ideal O :=
  ∏ p ∈ rowFixedPrimes B s, p

def rowFreePart (B : Finset (Ideal O)) (s : Ideal O) : Ideal O :=
  ∏ p ∈ primeFactors s \ B, p

theorem rowFixedPrimes_subset (B : Finset (Ideal O)) (s : Ideal O) :
    rowFixedPrimes B s ⊆ B := Finset.inter_subset_right

theorem row_fixed_free_product (B : Finset (Ideal O)) {s : Ideal O}
    (hs0 : s ≠ ⊥) (hs : Squarefree s) :
    rowFixedPart B s * rowFreePart B s = s := by
  exact (Finset.prod_inter_mul_prod_sdiff (primeFactors s) B (fun p : Ideal O => p)).trans
    (PacketCharacters.primeFactors_prod hs0 hs)

theorem rowFixedPart_ne_bot (B : Finset (Ideal O)) (s : Ideal O) :
    rowFixedPart B s ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
    (PacketCharacters.primeFactors_prime (Finset.mem_inter.mp hp).1).ne_zero)

theorem rowFreePart_ne_bot (B : Finset (Ideal O)) (s : Ideal O) :
    rowFreePart B s ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
    (PacketCharacters.primeFactors_prime (Finset.mem_sdiff.mp hp).1).ne_zero)

theorem rowFixedPart_squarefree (B : Finset (Ideal O)) (s : Ideal O) :
    Squarefree (rowFixedPart B s) :=
  prime_set_squarefree _ (fun p hp =>
    PacketCharacters.primeFactors_prime (Finset.mem_inter.mp hp).1)

theorem rowFreePart_squarefree (B : Finset (Ideal O)) (s : Ideal O) :
    Squarefree (rowFreePart B s) :=
  prime_set_squarefree _ (fun p hp =>
    PacketCharacters.primeFactors_prime (Finset.mem_sdiff.mp hp).1)

theorem rowFreePart_coprime (B : Finset (Ideal O))
    (hB : ∀ p ∈ B, Prime p) (s : Ideal O) :
    IsRelPrime (rowFreePart B s) (∏ p ∈ B, p) := by
  apply prime_set_relPrime _ _
    (fun p hp => PacketCharacters.primeFactors_prime (Finset.mem_sdiff.mp hp).1) hB
  exact Finset.disjoint_left.mpr (fun p hp hpb => (Finset.mem_sdiff.mp hp).2 hpb)

theorem rowFreePart_squarefree_outside (c : ArithmeticContext) (B : Finset (Ideal O))
    (hB : ∀ p ∈ B, Prime p) (hS : c.S ⊆ B) (s : Ideal O) :
    SquarefreeOutside c.S (rowFreePart B s) := by
  refine ⟨⟨rowFreePart_ne_bot B s, ?_⟩, rowFreePart_squarefree B s⟩
  intro p hp hpk
  exact (c.prime_S p hp).not_isUnit
    (rowFreePart_coprime B hB s hpk (Finset.dvd_prod_of_mem (fun p => p) (hS hp)))

theorem rowFreePart_norm_le_iff (B : Finset (Ideal O)) {s : Ideal O}
    (hs0 : s ≠ ⊥) (hs : Squarefree s) (H : ℝ) :
    normIdeal (rowFreePart B s) ≤ H / normIdeal (rowFixedPart B s) ↔ normIdeal s ≤ H := by
  have hp : normIdeal (rowFixedPart B s) * normIdeal (rowFreePart B s) = normIdeal s := by
    simpa only [normIdeal, map_mul, Nat.cast_mul] using
      congrArg normIdeal (row_fixed_free_product B hs0 hs)
  rw [le_div_iff₀ (normIdeal_pos (rowFixedPart_ne_bot B s)), mul_comm, hp]

theorem rowParts_injective (B : Finset (Ideal O)) :
    Function.Injective (fun s : {s : Ideal O // s ≠ ⊥ ∧ Squarefree s} =>
      (rowFixedPrimes B s.1, rowFreePart B s.1)) := by
  intro s t h
  apply Subtype.ext
  have hT := congrArg (fun q : Finset (Ideal O) × Ideal O => ∏ p ∈ q.1, p) h
  have hk := congrArg Prod.snd h
  calc
    s.1 = rowFixedPart B s.1 * rowFreePart B s.1 :=
      (row_fixed_free_product B s.2.1 s.2.2).symm
    _ = rowFixedPart B t.1 * rowFreePart B t.1 := congrArg₂ (· * ·) hT hk
    _ = t.1 := row_fixed_free_product B t.2.1 t.2.2


theorem idealNorm_le_of_dvd {a b : Ideal O} (hb : b ≠ ⊥) (hab : a ∣ b) :
    normIdeal a ≤ normIdeal b := by
  change (a.absNorm : ℝ) ≤ (b.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb))
    (map_dvd Ideal.absNorm hab)

open UniqueFactorizationMonoid in
theorem primeFactors_product_dvd {s : Ideal O} (hs : s ≠ ⊥) :
    (∏ p ∈ primeFactors s, p) ∣ s := by
  have h := Multiset.toFinset_prod_dvd_prod (normalizedFactors s)
  rw [Ideal.prod_normalizedFactors_eq_self hs] at h
  exact h

def auxiliaryPrimes (c : ArithmeticContext) (g : O) : Finset (Ideal O) :=
  primeFactors (principal g) \ c.S

theorem auxiliaryPrimes_primeTwist (c : ArithmeticContext) (g : O) :
    PrimeTwistSet c.S (auxiliaryPrimes c g) := by
  intro p hp
  exact ⟨PacketCharacters.primeFactors_prime (Finset.mem_sdiff.mp hp).1,
    (Finset.mem_sdiff.mp hp).2⟩

theorem auxiliaryPrimes_product_dvd (c : ArithmeticContext) {g : O} (hg : g ≠ 0) :
    (∏ p ∈ auxiliaryPrimes c g, p) ∣ principal g := by
  have hs : principal g ≠ ⊥ := fun h => hg (Ideal.span_singleton_eq_bot.mp h)
  exact (Finset.prod_dvd_prod_of_subset (auxiliaryPrimes c g) (primeFactors (principal g))
    (fun p : Ideal O => p) Finset.sdiff_subset).trans (primeFactors_product_dvd hs)

theorem auxiliaryPrimes_norm_product_le (c : ArithmeticContext) {g : O} (hg : g ≠ 0) :
    (∏ p ∈ auxiliaryPrimes c g, normIdeal p) ≤ normElement g := by
  have hs : principal g ≠ ⊥ := fun h => hg (Ideal.span_singleton_eq_bot.mp h)
  have h := idealNorm_le_of_dvd hs (auxiliaryPrimes_product_dvd c hg)
  simpa only [normIdeal, normElement, map_prod, Nat.cast_prod] using h

/-- The exponent is chosen before the context; only the fixed scalar B depends
on the prescribed per-prime number of choices and the requested small power. -/
theorem auxiliary_choices_uniform (a δ C : ℝ) (ha : 1 ≤ a) (hδ : 0 < δ) (hC : 1 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (c : ArithmeticContext) (g : O) (D : ℝ),
      g ≠ 0 → 2 ≤ D → normElement g ≤ D ^ C →
      a ^ (auxiliaryPrimes c g).card ≤ B * D ^ δ := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hδC : 0 < δ / C := div_pos hδ hC0
  obtain ⟨B, hB, hcount⟩ := reflection_choices_small_power a (δ / C) ha hδC
  refine ⟨B, hB, ?_⟩
  intro c g D hg hD hgD
  have hP := auxiliaryPrimes_primeTwist c g
  have hnorm := primeTwist_norm_one_le c hP
  have hn0 : 0 ≤ ∏ p ∈ auxiliaryPrimes c g, normIdeal p :=
    Finset.prod_nonneg (fun p hp => zero_le_one.trans (hnorm p hp))
  have hpow := Real.rpow_le_rpow hn0
    ((auxiliaryPrimes_norm_product_le c hg).trans hgD) hδC.le
  have he : C * (δ / C) = δ := by field_simp [hC0.ne']
  rw [← Real.rpow_mul (by linarith : 0 ≤ D), he] at hpow
  exact (hcount (auxiliaryPrimes c g) hnorm).trans
    (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hB))

end QRHShort.SquarefreeAssembly.PacketConstruction

open UniqueFactorizationMonoid

namespace QRHShort.SquarefreeAssembly.PacketReciprocity
open QRHShort.SquarefreeReflection

theorem sexticSymbol_eq_zero_of_not_relPrime (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) (z : O) (hnot : ¬ IsRelPrime a (principal z)) :
    sexticSymbol a z = 0 := by
  by_contra hvalue
  apply hnot
  apply (isRelPrime_iff_no_prime_factors ha.1).mpr
  intro p hpa hpz hp
  apply hvalue
  rw [sexticSymbol, if_neg ha.1]
  apply Multiset.prod_eq_zero
  have hmem : p ∈ normalizedFactors a :=
    (mem_normalizedFactors_iff ha.1).mpr ⟨hp, hpa⟩
  refine Multiset.mem_map.mpr ⟨p, hmem, ?_⟩
  exact sexticAtPrime_zero_of_mem hp
    (RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot c hp
      (RayValuePrerequisites.outside_of_mem_normalizedFactors ha hmem))
    (Ideal.dvd_span_singleton.mp hpz)

theorem sexticSymbol_sixth_eq_one_of_relPrime (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) (z : O) (hrel : IsRelPrime a (principal z)) :
    sexticSymbol a z ^ (6 : ℕ) = 1 := by
  rw [sexticSymbol, if_neg ha.1, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro w hw
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hw
  have hprime := prime_of_normalized_factor p hp
  have hout := RayValuePrerequisites.outside_of_mem_normalizedFactors ha hp
  have hζ := RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot c hprime hout
  have hz : z ∉ p := by
    intro hz
    exact hprime.not_isUnit
      (hrel (dvd_of_mem_normalizedFactors hp) (Ideal.dvd_span_singleton.mpr hz))
  obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hprime hζ hz
  rw [RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj ht,
    ← RayValuePrerequisites.embedding_pow, ← pow_mul, Nat.mul_comm j 6, pow_mul,
    RayValuePrerequisites.rootSix_pow_six, one_pow, RayValuePrerequisites.embedding_one]

theorem sexticSymbol_norm_eq_one_of_relPrime (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) (z : O) (hrel : IsRelPrime a (principal z)) :
    ‖sexticSymbol a z‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one
    (sexticSymbol_sixth_eq_one_of_relPrime c ha z hrel) (by decide)

theorem sexticSymbol_eq_zero_iff_not_relPrime (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) (z : O) :
    sexticSymbol a z = 0 ↔ ¬ IsRelPrime a (principal z) := by
  constructor
  · intro hz hrel
    have hnorm := sexticSymbol_norm_eq_one_of_relPrime c ha z hrel
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · exact sexticSymbol_eq_zero_of_not_relPrime c ha z

theorem sexticSymbol_ne_zero_iff_relPrime (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) (z : O) :
    sexticSymbol a z ≠ 0 ↔ IsRelPrime a (principal z) := by
  rw [ne_eq, sexticSymbol_eq_zero_iff_not_relPrime c ha z, not_not]

/-- Only the coprime branch uses the supplied reciprocity law. In the other
branch both literal residue symbols vanish at a common prime divisor. -/
theorem reciprocity_outside (c : ArithmeticContext) (d : ReciprocityData c)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) :
    sexticSymbol b (primaryGenerator a) =
      d.value (idealClass c a) (idealClass c b) * sexticSymbol a (primaryGenerator b) := by
  by_cases hcop : IsRelPrime a b
  · exact d.reciprocity a b ha hb hcop
  · have haGen := (RayValuePrerequisites.primaryGenerator_spec_outside c ha).1
    have hbGen := (RayValuePrerequisites.primaryGenerator_spec_outside c hb).1
    have hba : ¬ IsRelPrime b (principal (primaryGenerator a)) := by
      rw [haGen]
      exact fun h => hcop h.symm
    have hab : ¬ IsRelPrime a (principal (primaryGenerator b)) := by
      rw [hbGen]
      exact hcop
    rw [sexticSymbol_eq_zero_of_not_relPrime c hb _ hba,
      sexticSymbol_eq_zero_of_not_relPrime c ha _ hab, mul_zero]

end QRHShort.SquarefreeAssembly.PacketReciprocity

open UniqueFactorizationMonoid

namespace QRHShort.SquarefreeAssembly.PacketTwistProduct
open QRHShort.SquarefreeReflection

theorem sexticSymbol_one_denominator (z : O) : sexticSymbol (1 : Ideal O) z = 1 := by
  have h1 : (1 : Ideal O) ≠ ⊥ := one_ne_zero
  rw [sexticSymbol, if_neg h1]
  change ((normalizedFactors (1 : Ideal O)).map (fun p => sexticAtPrime p z)).prod = 1
  rw [normalizedFactors_one]
  rfl

theorem sexticSymbol_mul_denominator {a b : Ideal O}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  have hab : a * b ≠ ⊥ := by
    intro h
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact ha h
    · exact hb h
  simp only [sexticSymbol, if_neg hab, if_neg ha, if_neg hb,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

theorem sexticSymbol_pow_denominator {a : Ideal O} (ha : a ≠ ⊥) (e : ℕ) (z : O) :
    sexticSymbol (a ^ e) z = sexticSymbol a z ^ e := by
  induction e with
  | zero => simp only [pow_zero, sexticSymbol_one_denominator]
  | succ e ih =>
    rw [pow_succ, sexticSymbol_mul_denominator (pow_ne_zero e ha) ha z, ih, pow_succ]

theorem sexticSymbol_prod_denominator {ι : Type*} (s : Finset ι) (f : ι → Ideal O)
    (hf : ∀ i ∈ s, f i ≠ ⊥) (z : O) :
    sexticSymbol (∏ i ∈ s, f i) z = ∏ i ∈ s, sexticSymbol (f i) z := by
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp only [Finset.prod_empty, sexticSymbol_one_denominator]
  | @insert i s hi ih =>
    intro hf
    have hs : ∀ j ∈ s, f j ≠ ⊥ := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      sexticSymbol_mul_denominator (hf i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr hs) z, ih hs]

theorem pow_mod_six {w : ℂ} (hw : w ^ (6 : ℕ) = 1) (e : ℕ) :
    w ^ (e % 6) = w ^ e := by
  conv_rhs =>
    rw [← Nat.mod_add_div e 6, pow_add, pow_mul, hw, one_pow, mul_one]

/-- Exponent reduction retains the zero extension even when e mod 6 is zero. -/
theorem localCharacterPower_mod_six (c : ArithmeticContext) {p : Ideal O}
    (hp : Prime p) (hout : Outside c.S p) (e : ℕ) (z : O) :
    localCharacterPower p (e : ℤ) z = localCharacterPower p ((e % 6 : ℕ) : ℤ) z := by
  unfold localCharacterPower
  by_cases hz : z ∈ p
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    change sexticSymbol p z ^ e = sexticSymbol p z ^ (e % 6)
    apply (pow_mod_six _ e).symm
    apply PacketReciprocity.sexticSymbol_sixth_eq_one_of_relPrime c hout z
    apply hp.irreducible.isRelPrime_iff_not_dvd.mpr
    exact fun h => hz (Ideal.dvd_span_singleton.mp h)

theorem sexticSymbol_prime_pow_eq_localCharacterPower (c : ArithmeticContext)
    {p : Ideal O} (hp : Prime p) (hout : Outside c.S p)
    (e : ℕ) (he : 0 < e) (z : O) :
    sexticSymbol p z ^ e = localCharacterPower p (e : ℤ) z := by
  by_cases hz : z ∈ p
  · have hzero : sexticSymbol p z = 0 :=
      PacketReciprocity.sexticSymbol_eq_zero_of_not_relPrime c hout z
        (fun h => hp.not_isUnit (h (dvd_refl p) (Ideal.dvd_span_singleton.mpr hz)))
    simp only [hzero, zero_pow (Nat.ne_of_gt he), localCharacterPower, if_pos hz]
  · simp only [localCharacterPower, if_neg hz, zpow_natCast]

theorem sexticSymbol_prime_pow_eq_localCharacterPower_mod_six (c : ArithmeticContext)
    {p : Ideal O} (hp : Prime p) (hout : Outside c.S p)
    (e : ℕ) (he : 0 < e) (z : O) :
    sexticSymbol p z ^ e = localCharacterPower p ((e % 6 : ℕ) : ℤ) z :=
  (sexticSymbol_prime_pow_eq_localCharacterPower c hp hout e he z).trans
    (localCharacterPower_mod_six c hp hout e z)

theorem sexticSymbol_squarefree_product (c : ArithmeticContext) {k : Ideal O}
    (hk : SquarefreeOutside c.S k) (z : O) :
    sexticSymbol k z = ∏ p ∈ primeFactors k, sexticSymbol p z := by
  calc
    _ = sexticSymbol (∏ p ∈ primeFactors k, p) z :=
      congrArg (fun n : Ideal O => sexticSymbol n z)
        (PacketCharacters.primeFactors_prod hk.1.1 hk.2).symm
    _ = _ := sexticSymbol_prod_denominator _ (fun p => p)
      (fun p hp => (PacketCharacters.primeFactors_prime hp).ne_zero) z

theorem subset_character_prod (P T : Finset (Ideal O)) (hTP : T ⊆ P) (z : O) :
    (∏ p ∈ T, sexticSymbol p z) =
      ∏ p ∈ P, if p ∈ T then sexticSymbol p z else 1 := by
  have hfilter : P.filter (fun p => p ∈ T) = T := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hTP h, h⟩⟩
  symm
  rw [← Finset.prod_filter]
  exact congrArg (fun U : Finset (Ideal O) => ∏ p ∈ U, sexticSymbol p z) hfilter

theorem combine_character_products (P T : Finset (Ideal O)) (hTP : T ⊆ P)
    (v : Ideal O → ℕ) (z : O) :
    (∏ p ∈ T, sexticSymbol p z) * (∏ p ∈ P, sexticSymbol p z ^ (4 * v p)) =
      ∏ p ∈ P, sexticSymbol p z ^ (4 * v p + if p ∈ T then 1 else 0) := by
  rw [subset_character_prod P T hTP z, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  by_cases ht : p ∈ T
  · simp only [ht, ↓reduceIte, pow_add, pow_one]
    exact mul_comm _ _
  · simp [ht]

/-- The finite product for the actual outside auxiliary ideal and squarefree
row factor. The right exponent is the literal expanded exponent used by
productTwist; no coprimality with the numerator z is required. -/
theorem sexticSymbol_auxiliary_product (c : ArithmeticContext)
    (P T : Finset (Ideal O)) (hP : PrimeTwistSet c.S P) (hTP : T ⊆ P)
    (v : Ideal O → ℕ) (hv : ∀ p ∈ P, 0 < v p)
    {k : Ideal O} (hk : SquarefreeOutside c.S k)
    (hcop : IsRelPrime k (∏ p ∈ P, p)) (z : O) :
    sexticSymbol ((∏ p ∈ T, p) * k) z *
        sexticSymbol (∏ p ∈ P, p ^ v p) z ^ (4 : ℕ) =
      ∏ p ∈ P ∪ primeFactors k,
        localCharacterPower p
          ((if p ∈ P then (4 * v p + if p ∈ T then 1 else 0) % 6 else 1 : ℕ) : ℤ) z := by
  have hT0 : (∏ p ∈ T, p) ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (hP p (hTP hp)).1.ne_zero)
  have hTval : sexticSymbol (∏ p ∈ T, p) z = ∏ p ∈ T, sexticSymbol p z :=
    sexticSymbol_prod_denominator T (fun p => p)
      (fun p hp => (hP p (hTP hp)).1.ne_zero) z
  have hPval : sexticSymbol (∏ p ∈ P, p ^ v p) z =
      ∏ p ∈ P, sexticSymbol p z ^ v p := by
    rw [sexticSymbol_prod_denominator P (fun p => p ^ v p)
      (fun p hp => pow_ne_zero _ (hP p hp).1.ne_zero) z]
    apply Finset.prod_congr rfl
    intro p hp
    exact sexticSymbol_pow_denominator (hP p hp).1.ne_zero (v p) z
  have hPfour : sexticSymbol (∏ p ∈ P, p ^ v p) z ^ (4 : ℕ) =
      ∏ p ∈ P, sexticSymbol p z ^ (4 * v p) := by
    rw [hPval, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p _
    rw [← pow_mul, Nat.mul_comm (v p) 4]
  have hPmod : (∏ p ∈ P,
      sexticSymbol p z ^ (4 * v p + if p ∈ T then 1 else 0)) =
      ∏ p ∈ P, localCharacterPower p
        (((4 * v p + if p ∈ T then 1 else 0) % 6 : ℕ) : ℤ) z := by
    apply Finset.prod_congr rfl
    intro p hp
    have hvp := hv p hp
    exact sexticSymbol_prime_pow_eq_localCharacterPower_mod_six c (hP p hp).1
      (PacketCharacters.prime_outside c (hP p hp).1 (hP p hp).2) _ (by omega) z
  have hKval : (∏ p ∈ primeFactors k, sexticSymbol p z) =
      ∏ p ∈ primeFactors k, localCharacterPower p 1 z := by
    apply Finset.prod_congr rfl
    intro p hp
    simpa only [pow_one, Nat.cast_one] using
      sexticSymbol_prime_pow_eq_localCharacterPower c (PacketCharacters.primeFactors_prime hp)
        (RayValuePrerequisites.outside_of_mem_normalizedFactors hk.1
          (Multiset.mem_toFinset.mp hp)) 1 (by decide) z
  have hd := PacketCharacters.primeFactors_disjoint (fun p hp => (hP p hp).1) hcop
  have hunion : (∏ p ∈ P ∪ primeFactors k,
      localCharacterPower p
        ((if p ∈ P then (4 * v p + if p ∈ T then 1 else 0) % 6 else 1 : ℕ) : ℤ) z) =
      (∏ p ∈ P, localCharacterPower p
        (((4 * v p + if p ∈ T then 1 else 0) % 6 : ℕ) : ℤ) z) *
      ∏ p ∈ primeFactors k, localCharacterPower p 1 z := by
    rw [Finset.prod_union hd]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      rw [if_pos hp]
    · apply Finset.prod_congr rfl
      intro p hp
      rw [if_neg (fun h => Finset.disjoint_left.mp hd h hp)]
      simp only [Nat.cast_one]
  rw [sexticSymbol_mul_denominator hT0 hk.1.1 z, hTval,
    sexticSymbol_squarefree_product c hk z, hPfour]
  calc
    _ = ((∏ p ∈ T, sexticSymbol p z) * (∏ p ∈ P, sexticSymbol p z ^ (4 * v p))) *
        ∏ p ∈ primeFactors k, sexticSymbol p z := by ring
    _ = _ := by rw [combine_character_products P T hTP v z, hPmod, hKval, hunion]

end QRHShort.SquarefreeAssembly.PacketTwistProduct

namespace QRHShort.SquarefreeAssembly.PacketConstruction


open UniqueFactorizationMonoid

def supportedExponents (c : ArithmeticContext) (a : Ideal O) (p : c.S) : ℕ :=
  (normalizedFactors a).count p.1

def outsideIdealPart (c : ArithmeticContext) (a : Ideal O) : Ideal O :=
  ((normalizedFactors a).filter (fun p => p ∉ c.S)).prod

theorem outsideIdealPart_outside (c : ArithmeticContext) (a : Ideal O) :
    Outside c.S (outsideIdealPart c a) := by
  refine ⟨Multiset.prod_ne_zero_of_prime _ (fun p hp =>
    prime_of_normalized_factor p (Multiset.mem_filter.mp hp).1), ?_⟩
  intro p hp hpa
  obtain ⟨q, hq, hpq⟩ := (c.prime_S p hp).exists_mem_multiset_dvd hpa
  obtain ⟨hqN, hqS⟩ := Multiset.mem_filter.mp hq
  have he : p = q := associated_iff_eq.mp
    ((c.prime_S p hp).associated_of_dvd (prime_of_normalized_factor q hqN) hpq)
  exact hqS (he ▸ hp)

theorem supported_factor_product (c : ArithmeticContext) {a : Ideal O} (ha : a ≠ ⊥) :
    (∏ p : c.S, p.1 ^ supportedExponents c a p) * outsideIdealPart c a = a := by
  have hs : ((normalizedFactors a).filter (fun p => p ∈ c.S)).prod =
      ∏ p ∈ c.S, p ^ (normalizedFactors a).count p := by
    rw [Finset.prod_multiset_count_of_subset _ c.S (by
      intro p hp
      exact (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hp)).2)]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Multiset.count_filter_of_pos hp]
  change (∏ p : c.S, p.1 ^ (normalizedFactors a).count p.1) *
    ((normalizedFactors a).filter (fun p => p ∉ c.S)).prod = a
  rw [Finset.prod_coe_sort c.S (fun p : Ideal O => p ^ (normalizedFactors a).count p),
    ← hs, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self ha

def principalMulHom : O →* Ideal O where
  toFun := principal
  map_one' := by simp [principal]
  map_mul' a b := (Ideal.span_singleton_mul_span_singleton a b).symm

theorem principal_SProduct (c : ArithmeticContext) (e : c.S → ℕ) :
    principal (SquarefreeReflection.SProduct c e) = ∏ p : c.S, p.1 ^ e p := by
  change principalMulHom (∏ p : c.S, idealGenerator p.1 ^ e p) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p _
  rw [map_pow]
  change principal (idealGenerator p.1) ^ e p = _
  rw [show principal (idealGenerator p.1) = p.1 from Ideal.span_singleton_generator p.1]

theorem element_supported_outside_factor (c : ArithmeticContext) {g : O} (hg : g ≠ 0) :
    ∃ u : Oˣ, g = (u : O) *
      SquarefreeReflection.SProduct c (supportedExponents c (principal g)) *
      primaryGenerator (outsideIdealPart c (principal g)) := by
  have hga : principal g ≠ ⊥ := fun h => hg (Ideal.span_singleton_eq_bot.mp h)
  have hpg := SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c
    (outsideIdealPart_outside c (principal g))
  have hp : principal (SquarefreeReflection.SProduct c (supportedExponents c (principal g)) *
      primaryGenerator (outsideIdealPart c (principal g))) = principal g := by
    change principalMulHom (_ * _) = _
    rw [map_mul]
    change principal (SquarefreeReflection.SProduct c (supportedExponents c (principal g))) *
      principal (primaryGenerator (outsideIdealPart c (principal g))) = _
    rw [principal_SProduct, hpg.1]
    exact supported_factor_product c hga
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hp
  refine ⟨u, ?_⟩
  calc
    g = (SquarefreeReflection.SProduct c (supportedExponents c (principal g)) *
        primaryGenerator (outsideIdealPart c (principal g))) * (u : O) := hu.symm
    _ = _ := by ring


open UniqueFactorizationMonoid

theorem outsideIdealPart_eq_count_product (c : ArithmeticContext) (a : Ideal O) :
    outsideIdealPart c a = ∏ p ∈ primeFactors a \ c.S, p ^ (normalizedFactors a).count p := by
  unfold outsideIdealPart
  rw [Finset.prod_multiset_count_of_subset _ (primeFactors a \ c.S) (by
    intro p hp
    obtain ⟨hpN, hpS⟩ := Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hp)
    exact Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr hpN, hpS⟩)]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Multiset.count_filter_of_pos (p := fun q : Ideal O => q ∉ c.S)
    (a := p) (s := normalizedFactors a) (Finset.mem_sdiff.mp hp).2]

theorem outsideIdealPart_dvd (c : ArithmeticContext) {a : Ideal O} (ha : a ≠ ⊥) :
    outsideIdealPart c a ∣ a :=
  ⟨∏ p : c.S, p.1 ^ supportedExponents c a p,
    by rw [mul_comm]; exact (supported_factor_product c ha).symm⟩

theorem outsideIdealPart_norm_product (c : ArithmeticContext) (a : Ideal O) :
    normIdeal (outsideIdealPart c a) =
      ∏ p ∈ primeFactors a \ c.S, normIdeal p ^ (normalizedFactors a).count p := by
  rw [outsideIdealPart_eq_count_product]
  simp only [normIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]

theorem auxiliaryPrimes_multiplicity_pos (c : ArithmeticContext) (g : O)
    {p : Ideal O} (hp : p ∈ auxiliaryPrimes c g) :
    1 ≤ (normalizedFactors (principal g)).count p := by
  exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hp).1)

theorem auxiliaryPrimes_weighted_norm_le (c : ArithmeticContext) {g : O} (hg : g ≠ 0) :
    (∏ p ∈ auxiliaryPrimes c g, normIdeal p ^ (normalizedFactors (principal g)).count p) ≤
      normElement g := by
  have hga : principal g ≠ ⊥ := fun h => hg (Ideal.span_singleton_eq_bot.mp h)
  unfold auxiliaryPrimes
  rw [← outsideIdealPart_norm_product c (principal g)]
  exact idealNorm_le_of_dvd hga (outsideIdealPart_dvd c hga)

theorem outsideIdealPart_squarefree_product (c : ArithmeticContext) {a : Ideal O}
    (ha0 : a ≠ ⊥) (ha : Squarefree a) :
    outsideIdealPart c a = ∏ p ∈ primeFactors a \ c.S, p := by
  have hn := (squarefree_iff_nodup_normalizedFactors ha0).mp ha
  have hfilter : (normalizedFactors a).toFinset \ c.S =
      ((normalizedFactors a).filter (fun p => p ∉ c.S)).toFinset := by
    ext p
    simp only [Finset.mem_sdiff, Multiset.mem_toFinset, Multiset.mem_filter]
  change ((normalizedFactors a).filter (fun p => p ∉ c.S)).prod =
    ∏ p ∈ (normalizedFactors a).toFinset \ c.S, p
  rw [hfilter, ← Multiset.toFinset_eq (hn.filter _)]
  simp only [Finset.prod_mk, Multiset.map_id']

theorem outsideIdealPart_row_split (c : ArithmeticContext) (B : Finset (Ideal O))
    (hSB : c.S ⊆ B) {s : Ideal O} (hs0 : s ≠ ⊥) (hs : Squarefree s) :
    outsideIdealPart c s =
      (∏ p ∈ rowFixedPrimes B s \ c.S, p) * rowFreePart B s := by
  rw [outsideIdealPart_squarefree_product c hs0 hs]
  have he : primeFactors s \ c.S =
      (rowFixedPrimes B s \ c.S) ∪ (primeFactors s \ B) := by
    ext p
    simp only [rowFixedPrimes, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hp, hpS⟩
      by_cases hpB : p ∈ B
      · exact Or.inl ⟨⟨hp, hpB⟩, hpS⟩
      · exact Or.inr ⟨hp, hpB⟩
    · rintro (⟨⟨hp, hpB⟩, hpS⟩ | ⟨hp, hpB⟩)
      · exact ⟨hp, hpS⟩
      · exact ⟨hp, fun hpS => hpB (hSB hpS)⟩
  have hd : Disjoint (rowFixedPrimes B s \ c.S) (primeFactors s \ B) := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    exact (Finset.mem_sdiff.mp hp').2
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp hp).1).2
  rw [he, Finset.prod_union hd]
  rfl

theorem chosenGenerator_generates {a : Ideal O} (ha : a ≠ ⊥) :
    principal (chosenGenerator a) = a := by
  rw [chosenGenerator, if_neg ha, principal, ← Ideal.multiset_prod_span_singleton,
    Multiset.map_map]
  calc
    ((normalizedFactors a).map (fun p =>
        Ideal.span {if IsRelPrime p (principal 3) then primaryGenerator p
          else idealGenerator p})).prod = (normalizedFactors a).prod := by
      congr 1
      apply (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
      intro p hp
      by_cases hp3 : IsRelPrime p (principal 3)
      · rw [if_pos hp3]
        exact (primaryGenerator_spec_three hp3).1
      · rw [if_neg hp3]
        exact Ideal.span_singleton_generator p
    _ = a := Ideal.prod_normalizedFactors_eq_self ha

theorem chosenGenerator_unit_generates (u : Oˣ) {a : Ideal O} (ha : a ≠ ⊥) :
    principal ((u : O) * chosenGenerator a) = a := by
  change Ideal.span {((u : O) * chosenGenerator a)} = a
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  exact chosenGenerator_generates ha


def refineArithmeticContext (c : ArithmeticContext) (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus) :
    ArithmeticContext where
  nu := c.nu
  S := c.S
  prime_S := c.prime_S
  above_two := c.above_two
  above_three := c.above_three
  conductor_S := c.conductor_S
  rayModulus := M
  rayModulus_ne_bot := hM
  ray_supported := hMS
  nu_factors := hMR.trans c.nu_factors

theorem completedSum_refine_context (c : ArithmeticContext) (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus)
    (Ψ : Ideal O → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    completedSum (refineArithmeticContext c M hM hMS hMR) Ψ W X =
      completedSum c Ψ W X := rfl

def refineRayCharacter (c : ArithmeticContext) (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus)
    (ξ : RayCharacter c) : RayCharacter (refineArithmeticContext c M hM hMS hMR) :=
  ⟨SquarefreeReflection.refineHeckeCharacter ξ.1 M hM (by rw [ξ.2]; exact hMR), rfl⟩

theorem refineRayCharacter_value (c : ArithmeticContext) (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus)
    (ξ : RayCharacter c) {n : Ideal O} (hn : Outside c.S n) :
    rayValue (refineRayCharacter c M hM hMS hMR ξ).1 n = rayValue ξ.1 n :=
  PacketResidualCharacters.refine_rayValue_outside c ξ.1 M hM hMS _ hn

theorem rayResidue_onElement (c : ArithmeticContext) (ξ : RayCharacter c) (z : O) :
    rayResidue c ξ (Ideal.Quotient.mk c.rayModulus z) = ξ.1.onElement z := by
  rcases ξ with ⟨⟨M, hM, χ, hu⟩, h⟩
  dsimp only at h
  subst M
  rfl

def rayCharacterProduct (c : ArithmeticContext) (ξ η : RayCharacter c) : RayCharacter c :=
  ⟨{ modulus := c.rayModulus
     modulus_ne_bot := c.rayModulus_ne_bot
     residue := rayResidue c ξ * rayResidue c η
     unit_trivial := by
       intro u
       have hξ : ξ.1.onElement (u : O) = 1 := ξ.1.unit_trivial u
       have hη : η.1.onElement (u : O) = 1 := η.1.unit_trivial u
       rw [MulChar.mul_apply, rayResidue_onElement, rayResidue_onElement,
         hξ, hη, one_mul] }, rfl⟩

theorem rayCharacterProduct_value (c : ArithmeticContext) (ξ η : RayCharacter c)
    (n : Ideal O) :
    rayValue (rayCharacterProduct c ξ η).1 n = rayValue ξ.1 n * rayValue η.1 n := by
  change (rayResidue c ξ * rayResidue c η)
    (Ideal.Quotient.mk c.rayModulus (primaryGenerator n)) = _
  rw [MulChar.mul_apply, rayResidue_onElement, rayResidue_onElement]
  rfl

/-- A fixed common context supplies all residual row characters, together with
an exact lift of every original ray character. The context is chosen before
any varying element, weight, scale or row. -/
theorem exists_common_residual_context (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ M : Ideal O, ∃ hM : M ≠ ⊥,
      ∃ hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S,
      ∃ hMR : M ≤ c.rayModulus,
        ∃ χ : SquarefreeReflection.SResidueIndex c →
          RayCharacter (refineArithmeticContext c M hM hMS hMR),
          ∀ r n, Outside c.S n → rayValue (χ r).1 n = SquarefreeReflection.SResidual c r n := by
  obtain ⟨M, hM, hMR, hMS, hχ⟩ := supplementary_reciprocity_proved c hc
  choose χ hχM hχValue using hχ
  exact ⟨M, hM, hMS, hMR, (fun r => ⟨χ r, hχM r⟩), hχValue⟩

theorem reciprocitySection_value (c : ArithmeticContext)
    (d : SquarefreeReflection.ReciprocityData c) (a : Ideal O)
    {n : Ideal O} (hn : Outside c.S n) :
    rayValue (SquarefreeReflection.rayCharacterOfHom c
      (SquarefreeReflection.reciprocitySection d (idealClass c a))).1 n =
        d.value (idealClass c a) (idealClass c n) := by
  rw [SquarefreeReflection.rayCharacterOfHom_rayValue c _ hn]
  exact d.symmetric _ _


def rayCharacterPower (c : ArithmeticContext) (ξ : RayCharacter c) (e : ℕ) : RayCharacter c :=
  ⟨{ modulus := c.rayModulus
     modulus_ne_bot := c.rayModulus_ne_bot
     residue := rayResidue c ξ ^ e
     unit_trivial := by
       intro u
       have hξ : ξ.1.onElement (u : O) = 1 := ξ.1.unit_trivial u
       rw [PacketResidualCharacters.mulChar_pow_apply_of_isUnit _ _
         (u.isUnit.map (Ideal.Quotient.mk c.rayModulus)), rayResidue_onElement,
         hξ, one_pow] }, rfl⟩

theorem rayCharacterPower_value (c : ArithmeticContext) (ξ : RayCharacter c) (e : ℕ)
    {n : Ideal O} (hn : Outside c.S n) :
    rayValue (rayCharacterPower c ξ e).1 n = rayValue ξ.1 n ^ e := by
  change (rayResidue c ξ ^ e) (Ideal.Quotient.mk c.rayModulus (primaryGenerator n)) = _
  rw [PacketResidualCharacters.mulChar_pow_apply_of_isUnit _ _
    (SquarefreeReflection.primaryGenerator_unit_mod_supported c c.rayModulus
      c.rayModulus_ne_bot c.ray_supported hn), rayResidue_onElement]
  rfl

def rayCharacterFiniteProduct (c : ArithmeticContext) {ι : Type*} (S : Finset ι)
    (ξ : ι → RayCharacter c) : RayCharacter c :=
  ⟨{ modulus := c.rayModulus
     modulus_ne_bot := c.rayModulus_ne_bot
     residue := ∏ i ∈ S, rayResidue c (ξ i)
     unit_trivial := by
       intro u
       rw [PacketResidualCharacters.mulChar_prod_apply_of_isUnit _ _
         (u.isUnit.map (Ideal.Quotient.mk c.rayModulus))]
       exact Finset.prod_eq_one (fun i hi =>
         (rayResidue_onElement c (ξ i) (u : O)).trans ((ξ i).1.unit_trivial u)) }, rfl⟩

theorem rayCharacterFiniteProduct_value (c : ArithmeticContext) {ι : Type*} (S : Finset ι)
    (ξ : ι → RayCharacter c) {n : Ideal O} (hn : Outside c.S n) :
    rayValue (rayCharacterFiniteProduct c S ξ).1 n = ∏ i ∈ S, rayValue (ξ i).1 n := by
  change (∏ i ∈ S, rayResidue c (ξ i))
    (Ideal.Quotient.mk c.rayModulus (primaryGenerator n)) = _
  rw [PacketResidualCharacters.mulChar_prod_apply_of_isUnit _ _
    (SquarefreeReflection.primaryGenerator_unit_mod_supported c c.rayModulus
      c.rayModulus_ne_bot c.ray_supported hn)]
  exact Finset.prod_congr rfl (fun i hi => rayResidue_onElement c (ξ i) _)

theorem SRepresentative_prime (c : ArithmeticContext) (p : c.S) :
    SquarefreeReflection.SRepresentative c (1, fun q => if q = p then 1 else 0) =
      idealGenerator p.1 := by
  simp only [SquarefreeReflection.SRepresentative, Units.val_one, one_mul,
    SquarefreeReflection.SProduct]
  calc
    _ = ∏ q : c.S, if q = p then idealGenerator q.1 else 1 := by
      apply Finset.prod_congr rfl
      intro q hq
      by_cases h : q = p <;> simp only [h, ↓reduceIte, Fin.val_one, Fin.val_zero,
        pow_one, pow_zero]
    _ = _ := Fintype.prod_ite_eq' p _

/-- Arbitrary natural exponents use powers in one fixed residue character
space; the common modulus is independent of the varying exponents. -/
theorem exists_common_supported_context (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ M : Ideal O, ∃ hM : M ≠ ⊥,
      ∃ hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S,
      ∃ hMR : M ≤ c.rayModulus,
        ∀ (u : Oˣ) (e : c.S → ℕ),
          ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
            ∀ n, Outside c.S n → rayValue χ.1 n =
              sexticSymbol n ((u : O) * SquarefreeReflection.SProduct c e) := by
  obtain ⟨M, hM, hMS, hMR, χ, hχ⟩ := exists_common_residual_context c hc
  let c' := refineArithmeticContext c M hM hMS hMR
  refine ⟨M, hM, hMS, hMR, ?_⟩
  intro u e
  let η : c.S → RayCharacter c' := fun p => χ (1, fun q => if q = p then 1 else 0)
  refine ⟨rayCharacterProduct c' (χ (u, fun _ => 0))
    (rayCharacterFiniteProduct c' Finset.univ (fun p => rayCharacterPower c' (η p) (e p))), ?_⟩
  intro n hn
  have hn' : Outside c'.S n := hn
  have hu : rayValue (χ (u, fun _ => 0)).1 n = sexticSymbol n (u : O) := by
    simpa only [SquarefreeReflection.SResidual, SquarefreeReflection.SRepresentative,
      SquarefreeReflection.SProduct, Fin.val_zero, pow_zero, Finset.prod_const_one, mul_one]
      using hχ (u, fun _ => 0) n hn
  have hp (p : c.S) : rayValue (η p).1 n = sexticSymbol n (idealGenerator p.1) := by
    simpa only [SquarefreeReflection.SResidual, SRepresentative_prime, η]
      using hχ (1, fun q => if q = p then 1 else 0) n hn
  rw [rayCharacterProduct_value, hu, rayCharacterFiniteProduct_value c' _ _ hn',
    SquarefreeReflection.sexticSymbol_mul_numerator c hn,
    SquarefreeReflection.SProduct, SquarefreeReflection.sexticSymbol_prod_numerator c hn]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  rw [rayCharacterPower_value c' _ _ hn', hp,
    SquarefreeReflection.sexticSymbol_pow_numerator c hn]


theorem reciprocityData_nonempty (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    Nonempty (SquarefreeReflection.ReciprocityData c) := by
  obtain ⟨G, R, hG, hsign, hsym, hleft, hright, hGmul, hrec,
    hgauss, hcoeff, hquot⟩ := hc
  exact ⟨⟨R, hsign, hsym, hleft, hright, hrec⟩⟩

theorem reciprocity_four (c : ArithmeticContext) (d : SquarefreeReflection.ReciprocityData c)
    (a b : RayClass c) : d.value a b ^ (4 : ℕ) = 1 := by
  rcases d.sign a b with h | h <;> norm_num [h]

/-- The auxiliary fourth power eliminates its reciprocity sign; no division
by a potentially vanishing residue symbol occurs. -/
theorem symbol_reversal_algebra (r s x y a b R S : ℂ)
    (hr : r = x * R * a) (hs : s = y * S * b) (hS : S ^ (4 : ℕ) = 1) :
    r * s ^ (4 : ℕ) = (x * y ^ (4 : ℕ) * R) * a * b ^ (4 : ℕ) := by
  rw [hr, hs, mul_pow, mul_pow, hS]
  ring


/-- The fixed common character space absorbs every unit and every S-supported
factor of an actual nonzero numerator. -/
theorem supported_element_character_factor (c : ArithmeticContext)
    (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus)
    (hchar : ∀ (u : Oˣ) (e : c.S → ℕ),
      ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
        ∀ n, Outside c.S n → rayValue χ.1 n =
          sexticSymbol n ((u : O) * SquarefreeReflection.SProduct c e))
    {x : O} (hx : x ≠ 0) :
    ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
      ∀ n, Outside c.S n → sexticSymbol n x = rayValue χ.1 n *
        sexticSymbol n (primaryGenerator (outsideIdealPart c (principal x))) := by
  obtain ⟨u, hu⟩ := element_supported_outside_factor c hx
  obtain ⟨χ, hχ⟩ := hchar u (supportedExponents c (principal x))
  refine ⟨χ, ?_⟩
  intro n hn
  calc
    sexticSymbol n x = sexticSymbol n
        (((u : O) * SquarefreeReflection.SProduct c (supportedExponents c (principal x))) *
          primaryGenerator (outsideIdealPart c (principal x))) := congrArg (sexticSymbol n) hu
    _ = _ := by
      rw [SquarefreeReflection.sexticSymbol_mul_numerator c hn, hχ n hn]

/-- Exact reversal of the two actual row numerators. Both non-coprime cases
are included; the fourth power removes its sign and all remaining signs
are characters in the same fixed finite ray space. -/
theorem exists_reversed_twist_character (c : ArithmeticContext)
    (d : SquarefreeReflection.ReciprocityData c) (ξ : RayCharacter c)
    (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus)
    (hchar : ∀ (u : Oˣ) (e : c.S → ℕ),
      ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
        ∀ n, Outside c.S n → rayValue χ.1 n =
          sexticSymbol n ((u : O) * SquarefreeReflection.SProduct c e))
    {x g : O} (hx : x ≠ 0) (hg : g ≠ 0) :
    ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
      ∀ n, Outside c.S n →
        rayValue ξ.1 n * sexticSymbol n x * sexticSymbol n g ^ (4 : ℕ) =
          rayValue χ.1 n *
            sexticSymbol (outsideIdealPart c (principal x)) (primaryGenerator n) *
            sexticSymbol (outsideIdealPart c (principal g)) (primaryGenerator n) ^ (4 : ℕ) := by
  let c' := refineArithmeticContext c M hM hMS hMR
  obtain ⟨η, hη⟩ := supported_element_character_factor c M hM hMS hMR hchar hx
  obtain ⟨ζ, hζ⟩ := supported_element_character_factor c M hM hMS hMR hchar hg
  let a := outsideIdealPart c (principal x)
  let b := outsideIdealPart c (principal g)
  let ρ := SquarefreeReflection.rayCharacterOfHom c
    (SquarefreeReflection.reciprocitySection d (idealClass c a))
  let χ := rayCharacterProduct c' (refineRayCharacter c M hM hMS hMR ξ)
    (rayCharacterProduct c' η (rayCharacterProduct c' (rayCharacterPower c' ζ 4)
      (refineRayCharacter c M hM hMS hMR ρ)))
  refine ⟨χ, ?_⟩
  intro n hn
  have hn' : Outside c'.S n := hn
  have hρ : rayValue ρ.1 n = d.value (idealClass c a) (idealClass c n) :=
    reciprocitySection_value c d a hn
  have hχ : rayValue χ.1 n = rayValue ξ.1 n *
      (rayValue η.1 n * (rayValue ζ.1 n ^ (4 : ℕ) *
        d.value (idealClass c a) (idealClass c n))) := by
    simp only [χ, rayCharacterProduct_value]
    rw [rayCharacterPower_value c' _ _ hn',
      refineRayCharacter_value c M hM hMS hMR ξ hn,
      refineRayCharacter_value c M hM hMS hMR ρ hn, hρ]
  rw [hχ, hη n hn, hζ n hn,
    PacketReciprocity.reciprocity_outside c d (outsideIdealPart_outside c _) hn,
    PacketReciprocity.reciprocity_outside c d (outsideIdealPart_outside c _) hn]
  rw [mul_pow, mul_pow, reciprocity_four c d]
  ring


def rowAuxiliaryExponent {ι : Type*} (v : ι → ℕ) (T : Finset ι) (p : ι) : Fin 6 :=
  ⟨(4 * v p + if p ∈ T then 1 else 0) % 6, Nat.mod_lt _ (by decide)⟩

theorem reflectionLocalCost_one_le {q : ℝ} (hq : 1 ≤ q) (j : Fin 6) :
    1 ≤ reflectionLocalCost q j := by
  unfold reflectionLocalCost
  split_ifs
  · exact hq
  · exact one_le_pow₀ hq

theorem rowAuxiliaryLocalCost_bound {ι : Type*} (v : ι → ℕ) (T : Finset ι)
    (p : ι) (q : ℝ) (hq : 1 ≤ q) (hv : 1 ≤ v p) :
    reflectionLocalCost q (rowAuxiliaryExponent v T p) ≤
      (if p ∈ T then q ^ 2 else 1) * q ^ v p := by
  by_cases hp : p ∈ T
  · have he : rowAuxiliaryExponent v T p =
        (⟨(1 + 4 * v p) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) := by
      simp only [rowAuxiliaryExponent, if_pos hp, Nat.add_comm]
    rw [he, reflection_row_prime_cost, if_pos hp]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hq)
  · have he : rowAuxiliaryExponent v T p =
        (⟨(4 * v p) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) := by
      simp only [rowAuxiliaryExponent, if_neg hp, Nat.add_zero]
    rw [he, if_neg hp, one_mul]
    exact reflection_auxiliary_prime_cost hq (v p) hv

theorem rowAuxiliaryCost_product_bound {ι : Type*} (P T A : Finset ι)
    (q : ι → ℝ) (v : ι → ℕ) (hT : T ⊆ P) (hA : A ⊆ P)
    (hq : ∀ p ∈ P, 1 ≤ q p) (hv : ∀ p ∈ P, 1 ≤ v p) :
    (∏ p ∈ A, reflectionLocalCost (q p) (rowAuxiliaryExponent v T p)) ≤
      (∏ p ∈ T, q p) ^ 2 * ∏ p ∈ P, q p ^ v p := by
  have hsub := Finset.prod_le_prod_of_subset_of_one_le₀ hA
    (fun p hp => zero_le_one.trans (reflectionLocalCost_one_le (hq p (hA hp)) _))
    (fun p hp _ => reflectionLocalCost_one_le (hq p hp) (rowAuxiliaryExponent v T p))
  have hprod : (∏ p ∈ P, reflectionLocalCost (q p) (rowAuxiliaryExponent v T p)) ≤
      ∏ p ∈ P, (if p ∈ T then q p ^ 2 else 1) * q p ^ v p :=
    Finset.prod_le_prod₀
      (fun p hp => zero_le_one.trans (reflectionLocalCost_one_le (hq p hp) _))
      (fun p hp => rowAuxiliaryLocalCost_bound v T p (q p) (hq p hp) (hv p hp))
  have hTprod : (∏ p ∈ P, if p ∈ T then q p ^ 2 else 1) = ∏ p ∈ T, q p ^ 2 := by
    calc
      _ = ∏ p ∈ T, if p ∈ T then q p ^ 2 else 1 :=
        (Finset.prod_subset hT (fun p hp hpT => if_neg hpT)).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [if_pos hp]
  exact hsub.trans (hprod.trans_eq (by
    rw [Finset.prod_mul_distrib, hTprod, Finset.prod_pow]))

theorem raw_scaled_cost_bound (H Nt Ng X Nd L A cost : ℝ)
    (hH : 0 ≤ H) (hNt : 1 ≤ Nt) (hNg : 0 ≤ Ng) (hX : 0 < X)
    (hL : 1 ≤ L) (hNd : Nd ^ 2 ≤ L) (hcost : cost ≤ Nt ^ 2 * Ng) :
    A ^ 2 * (H / Nt + (Nd ^ 2 * (H / Nt) ^ 2 / X) * cost) ≤
      (A ^ 2 * L) * (H + H ^ 2 * Ng / X) := by
  have hNt0 : 0 < Nt := zero_lt_one.trans_le hNt
  have hQ : 0 ≤ H ^ 2 * Ng / X := div_nonneg (mul_nonneg (sq_nonneg _) hNg) hX.le
  have hy : 0 ≤ Nd ^ 2 * (H / Nt) ^ 2 / X := by positivity
  have hc : (Nd ^ 2 * (H / Nt) ^ 2 / X) * cost ≤ Nd ^ 2 * (H ^ 2 * Ng / X) := by
    calc
      _ ≤ (Nd ^ 2 * (H / Nt) ^ 2 / X) * (Nt ^ 2 * Ng) :=
        mul_le_mul_of_nonneg_left hcost hy
      _ = _ := by field_simp [hNt0.ne', hX.ne']
  have hh : H / Nt ≤ H := div_le_self hH hNt
  have hb : H / Nt + (Nd ^ 2 * (H / Nt) ^ 2 / X) * cost ≤
      L * (H + H ^ 2 * Ng / X) := by
    calc
      _ ≤ H + Nd ^ 2 * (H ^ 2 * Ng / X) := add_le_add hh hc
      _ ≤ L * H + L * (H ^ 2 * Ng / X) :=
        add_le_add (le_mul_of_one_le_left hH hL) (mul_le_mul_of_nonneg_right hNd hQ)
      _ = _ := by ring
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (sq_nonneg A)


def rawRowHeight (H : ℝ) (t : Ideal O) : ℝ := max 1 (H / normIdeal t)

theorem normIdeal_one_le_of_ne_bot {a : Ideal O} (ha : a ≠ ⊥) : 1 ≤ normIdeal a := by
  have h : 1 ≤ a.absNorm := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ha)
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast h

theorem rawRowHeight_bounds {H : ℝ} (hH : 1 ≤ H) {t : Ideal O} (ht : t ≠ ⊥) :
    1 ≤ rawRowHeight H t ∧ rawRowHeight H t ≤ H := by
  exact ⟨le_max_left _ _, max_le hH (div_le_self (zero_le_one.trans hH)
    (normIdeal_one_le_of_ne_bot ht))⟩

theorem rawRowHeight_of_norm_le {H : ℝ} {t : Ideal O} (ht : t ≠ ⊥)
    (hHt : normIdeal t ≤ H) : rawRowHeight H t = H / normIdeal t := by
  exact max_eq_right ((one_le_div (normIdeal_pos ht)).mpr hHt)

theorem rawRowHeight_div_le (H : ℝ) (t : Ideal O) :
    H / normIdeal t ≤ rawRowHeight H t := le_max_right _ _

theorem raw_fourth_scale_bound (D C X H Ng Nd L : ℝ)
    (hD : 2 ≤ D) (hH : 0 ≤ H) (hHC : H ≤ D ^ C)
    (hNg : 0 ≤ Ng) (hNgC : Ng ≤ D ^ C) (hX : 1 ≤ X)
    (hL : 0 ≤ L) (hNd : Nd ^ 2 ≤ L) :
    (Nd ^ 2 * H ^ 2 / X) * Ng ^ 2 ≤ L * D ^ (4 * C) := by
  have hD0 : 0 ≤ D := by linarith
  have hp : 0 ≤ D ^ C := Real.rpow_nonneg hD0 _
  have hH2 : H ^ 2 ≤ (D ^ C) ^ (2 : ℕ) := pow_le_pow_left₀ hH hHC _
  have hNg2 : Ng ^ 2 ≤ (D ^ C) ^ (2 : ℕ) := pow_le_pow_left₀ hNg hNgC _
  have hE : (D ^ C) ^ (4 : ℕ) = D ^ (4 * C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]
    congr 1
    ring
  calc
    _ ≤ (Nd ^ 2 * H ^ 2) * Ng ^ 2 :=
      mul_le_mul_of_nonneg_right (div_le_self (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hX)
        (sq_nonneg _)
    _ ≤ (L * (D ^ C) ^ (2 : ℕ)) * (D ^ C) ^ (2 : ℕ) :=
      mul_le_mul (mul_le_mul hNd hH2 (sq_nonneg _) hL) hNg2 (sq_nonneg _)
        (mul_nonneg hL (sq_nonneg _))
    _ = L * (D ^ C) ^ (4 : ℕ) := by ring
    _ = _ := by rw [hE]


theorem fixedSubset_primes (c : ArithmeticContext) {P T : Finset (Ideal O)}
    (hP : PrimeTwistSet c.S P) (hT : T ⊆ c.S ∪ P) : ∀ p ∈ T, Prime p := by
  intro p hp
  obtain hpS | hpP := Finset.mem_union.mp (hT hp)
  · exact c.prime_S p hpS
  · exact (hP p hpP).1

theorem fixedSubset_outside_subset (c : ArithmeticContext) {P T : Finset (Ideal O)}
    (hT : T ⊆ c.S ∪ P) : T \ c.S ⊆ P := by
  intro p hp
  obtain ⟨hpT, hpS⟩ := Finset.mem_sdiff.mp hp
  exact (Finset.mem_union.mp (hT hpT)).resolve_left hpS

theorem fixedSubset_product_ne_bot (c : ArithmeticContext) {P T : Finset (Ideal O)}
    (hP : PrimeTwistSet c.S P) (hT : T ⊆ c.S ∪ P) : (∏ p ∈ T, p) ≠ ⊥ :=
  Finset.prod_ne_zero_iff.mpr (fun p hp => (fixedSubset_primes c hP hT p hp).ne_zero)

theorem fixedSubset_norm (T : Finset (Ideal O)) :
    normIdeal (∏ p ∈ T, p) = ∏ p ∈ T, normIdeal p := by
  simp only [normIdeal, map_prod, Nat.cast_prod]

theorem fixedSubset_local_cost (c : ArithmeticContext) {P T A : Finset (Ideal O)}
    (hP : PrimeTwistSet c.S P) (hT : T ⊆ c.S ∪ P) (hA : A ⊆ P)
    (v : Ideal O → ℕ) (hv : ∀ p ∈ P, 1 ≤ v p) (Ng : ℝ)
    (hNg : 0 ≤ Ng) (hw : (∏ p ∈ P, normIdeal p ^ v p) ≤ Ng) :
    (∏ p ∈ A, reflectionLocalCost (normIdeal p) (rowAuxiliaryExponent v (T \ c.S) p)) ≤
      normIdeal (∏ p ∈ T, p) ^ 2 * Ng := by
  have hprime := fixedSubset_primes c hP hT
  have hq : ∀ p ∈ T, 1 ≤ normIdeal p :=
    fun p hp => normIdeal_one_le_of_ne_bot (hprime p hp).ne_zero
  have hsub : (∏ p ∈ T \ c.S, normIdeal p) ≤ normIdeal (∏ p ∈ T, p) := by
    rw [fixedSubset_norm]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ Finset.sdiff_subset
      (fun p hp => zero_le_one.trans (hq p (Finset.mem_sdiff.mp hp).1))
      (fun p hp _ => hq p hp)
  have hsub0 : 0 ≤ ∏ p ∈ T \ c.S, normIdeal p :=
    Finset.prod_nonneg (fun p hp => zero_le_one.trans (hq p (Finset.mem_sdiff.mp hp).1))
  have hw0 : 0 ≤ ∏ p ∈ P, normIdeal p ^ v p :=
    Finset.prod_nonneg (fun p hp => pow_nonneg (zero_le_one.trans
      (primeTwist_norm_one_le c hP p hp)) _)
  exact (rowAuxiliaryCost_product_bound P (T \ c.S) A normIdeal v
    (fixedSubset_outside_subset c hT) hA (primeTwist_norm_one_le c hP) hv).trans
      (mul_le_mul (pow_le_pow_left₀ hsub0 hsub 2) hw hw0 (sq_nonneg _))


def rawAuxiliaryExponents (c : ArithmeticContext) (g : O) (T : Finset (Ideal O)) :
    Ideal O → Fin 6 :=
  rowAuxiliaryExponent (fun p => (UniqueFactorizationMonoid.normalizedFactors (principal g)).count p)
    (T \ c.S)

theorem raw_twist_character_exists (c : ArithmeticContext)
    (d : SquarefreeReflection.ReciprocityData c) (ξ : RayCharacter c)
    (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus)
    (hchar : ∀ (u : Oˣ) (e : c.S → ℕ),
      ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
        ∀ n, Outside c.S n → rayValue χ.1 n =
          sexticSymbol n ((u : O) * SquarefreeReflection.SProduct c e))
    {g : O} (hg : g ≠ 0) (u : Oˣ) {s : Ideal O} (hs0 : s ≠ ⊥) (hs : Squarefree s) :
    ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
      completedTwistElement c ξ ((u : O) * chosenGenerator s) g =
        productTwist (refineArithmeticContext c M hM hMS hMR) χ
          (auxiliaryPrimes c g ∪ primeFactors (rowFreePart (c.S ∪ auxiliaryPrimes c g) s))
          (variableTwistExponents (auxiliaryPrimes c g)
            (rawAuxiliaryExponents c g (rowFixedPrimes (c.S ∪ auxiliaryPrimes c g) s))) := by
  let P := auxiliaryPrimes c g
  let B := c.S ∪ P
  let k := rowFreePart B s
  let T := rowFixedPrimes B s
  have hP := auxiliaryPrimes_primeTwist c g
  have hB : ∀ p ∈ B, Prime p := fixedSubset_primes c hP (fun _ hp => hp)
  have hSB : c.S ⊆ B := Finset.subset_union_left
  have hPB : P ⊆ B := Finset.subset_union_right
  have hk : SquarefreeOutside c.S k := rowFreePart_squarefree_outside c B hB hSB s
  have hcopB := rowFreePart_coprime B hB s
  have hcop : IsRelPrime k (∏ p ∈ P, p) := by
    intro q hqk hqP
    exact hcopB hqk (hqP.trans (Finset.prod_dvd_prod_of_subset P B (fun p => p) hPB))
  have hT : T \ c.S ⊆ P := fixedSubset_outside_subset c (rowFixedPrimes_subset B s)
  have hx : (u : O) * chosenGenerator s ≠ 0 := by
    intro hz
    have he := chosenGenerator_unit_generates u hs0
    rw [hz] at he
    exact hs0 (by simpa only [principal, Ideal.span_singleton_zero] using he.symm)
  obtain ⟨χ, hχ⟩ := exists_reversed_twist_character c d ξ M hM hMS hMR hchar hx hg
  refine ⟨χ, ?_⟩
  funext n
  by_cases hn : Outside c.S n
  · have hn' : Outside (refineArithmeticContext c M hM hMS hMR).S n := hn
    simp only [completedTwistElement, productTwist, if_pos hn, if_pos hn']
    rw [hχ n hn, chosenGenerator_unit_generates u hs0,
      outsideIdealPart_row_split c B hSB hs0 hs,
      outsideIdealPart_eq_count_product c (principal g)]
    rw [mul_assoc]
    congr 1
    have hp := PacketTwistProduct.sexticSymbol_auxiliary_product c P (T \ c.S)
      hP hT (fun p => (UniqueFactorizationMonoid.normalizedFactors (principal g)).count p)
      (fun p hp => auxiliaryPrimes_multiplicity_pos c g hp) hk hcop (primaryGenerator n)
    refine hp.trans ?_
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hpP : p ∈ auxiliaryPrimes c g <;>
      by_cases hpT : p ∈ rowFixedPrimes (c.S ∪ auxiliaryPrimes c g) s \ c.S <;>
      simp only [P, T, B, rawAuxiliaryExponents, rowAuxiliaryExponent, variableTwistExponents,
        hpP, hpT, ↓reduceIte, Fin.val_mk, Fin.val_one]
  · have hn' : ¬ Outside (refineArithmeticContext c M hM hMS hMR).S n := hn
    simp only [completedTwistElement, productTwist, if_neg hn, if_neg hn']

/-- One choice of row character works for all weights and scales. Its range
lies in the common finite ray space chosen before g and the row ideal. -/
theorem raw_twist_character_family (c : ArithmeticContext)
    (d : SquarefreeReflection.ReciprocityData c) (ξ : RayCharacter c)
    (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) (hMR : M ≤ c.rayModulus)
    (hchar : ∀ (u : Oˣ) (e : c.S → ℕ),
      ∃ χ : RayCharacter (refineArithmeticContext c M hM hMS hMR),
        ∀ n, Outside c.S n → rayValue χ.1 n =
          sexticSymbol n ((u : O) * SquarefreeReflection.SProduct c e))
    {g : O} (hg : g ≠ 0) (u : Oˣ) :
    ∃ select : Ideal O → RayCharacter (refineArithmeticContext c M hM hMS hMR),
      ∀ s : Ideal O, s ≠ ⊥ → Squarefree s →
        completedTwistElement c ξ ((u : O) * chosenGenerator s) g =
          productTwist (refineArithmeticContext c M hM hMS hMR) (select s)
            (auxiliaryPrimes c g ∪ primeFactors (rowFreePart (c.S ∪ auxiliaryPrimes c g) s))
            (variableTwistExponents (auxiliaryPrimes c g)
              (rawAuxiliaryExponents c g (rowFixedPrimes (c.S ∪ auxiliaryPrimes c g) s))) := by
  let select := fun s : Ideal O => if hs : s ≠ ⊥ ∧ Squarefree s then
    Classical.choose (raw_twist_character_exists c d ξ M hM hMS hMR hchar hg u hs.1 hs.2)
    else refineRayCharacter c M hM hMS hMR ξ
  refine ⟨select, ?_⟩
  intro s hs0 hs
  dsimp only [select]
  rw [dif_pos ⟨hs0, hs⟩]
  exact Classical.choose_spec (raw_twist_character_exists c d ξ M hM hMS hMR hchar hg u hs0 hs)


theorem norm_fintype_sum_sq_le {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ‖∑ i, z i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
  calc
    _ ≤ (∑ i, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ _ := by
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _i : ι => (1 : ℝ)) (fun i : ι => ‖z i‖))

/-- Finite Cauchy and injection of each fixed row part into its literal free
ideal window. The tag restriction is retained before applying injectivity. -/
theorem finite_row_cover {α τ κ ι : Type*} [Fintype ι]
    (R : Finset α) (tag : α → τ) (key : α → κ) (packetTag : ι → τ)
    (window : ι → Finset κ) (F : α → ℂ) (G : ι → κ → ℂ)
    (hinj : Set.InjOn (fun a => (tag a, key a)) R)
    (hmem : ∀ a ∈ R, ∀ i, tag a = packetTag i → key a ∈ window i)
    (heq : ∀ a ∈ R, F a = ∑ i, if tag a = packetTag i then G i (key a) else 0) :
    (∑ a ∈ R, ‖F a‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * ∑ i, ∑ k ∈ window i, ‖G i k‖ ^ 2 := by
  have hcol (i : ι) :
      (∑ a ∈ R, ‖if tag a = packetTag i then G i (key a) else 0‖ ^ 2) ≤
        ∑ k ∈ window i, ‖G i k‖ ^ 2 := by
    let S := R.filter (fun a => tag a = packetTag i)
    have hi : Set.InjOn key S := by
      intro a ha b hb h
      obtain ⟨haR, hat⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbR, hbt⟩ := Finset.mem_filter.mp hb
      exact hinj haR hbR (Prod.ext (hat.trans hbt.symm) h)
    have hm : S.image key ⊆ window i := by
      intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      exact hmem a (Finset.mem_filter.mp ha).1 i (Finset.mem_filter.mp ha).2
    calc
      _ = ∑ a ∈ S, ‖G i (key a)‖ ^ 2 := by
        simp only [S, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        split_ifs <;> simp
      _ = ∑ k ∈ S.image key, ‖G i k‖ ^ 2 :=
        (Finset.sum_image (f := fun k => ‖G i k‖ ^ 2) hi).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hm (fun k hk hkS => sq_nonneg _)
  calc
    _ ≤ ∑ a ∈ R, (Fintype.card ι : ℝ) *
        ∑ i, ‖if tag a = packetTag i then G i (key a) else 0‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      rw [heq a ha]
      exact norm_fintype_sum_sq_le _
    _ = (Fintype.card ι : ℝ) *
        ∑ i, ∑ a ∈ R, ‖if tag a = packetTag i then G i (key a) else 0‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi => hcol i))
      (Nat.cast_nonneg _)


def rawOriginalRows (H : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le H).toFinset.filter (fun s => s ≠ ⊥ ∧ Squarefree s)

theorem mem_rawOriginalRows (H : ℝ) (s : Ideal O) :
    s ∈ rawOriginalRows H ↔ s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ H := by
  simp only [rawOriginalRows, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  tauto

theorem rawOriginalRows_tsum (H : ℝ) (F : Ideal O → ℝ) :
    (∑' s : Ideal O, if s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ H then F s else 0) =
      ∑ s ∈ rawOriginalRows H, F s := by
  rw [tsum_eq_sum (s := rawOriginalRows H) (fun s hs =>
    if_neg (fun h => hs ((mem_rawOriginalRows H s).mpr h)))]
  exact Finset.sum_congr rfl (fun s hs => if_pos ((mem_rawOriginalRows H s).mp hs))

theorem rowParts_injOn_originalRows (B : Finset (Ideal O)) (H : ℝ) :
    Set.InjOn (fun s => (rowFixedPrimes B s, rowFreePart B s)) (rawOriginalRows H) := by
  intro s hs t ht he
  have hs' := (mem_rawOriginalRows H s).mp hs
  have ht' := (mem_rawOriginalRows H t).mp ht
  have hst : (⟨s, hs'.1, hs'.2.1⟩ : {a : Ideal O // a ≠ ⊥ ∧ Squarefree a}) =
      ⟨t, ht'.1, ht'.2.1⟩ := rowParts_injective B he
  exact congrArg Subtype.val hst

theorem rowFixedPart_norm_le_original (B : Finset (Ideal O)) (H : ℝ)
    {s : Ideal O} (hs : s ∈ rawOriginalRows H) : normIdeal (rowFixedPart B s) ≤ H := by
  have hs' := (mem_rawOriginalRows H s).mp hs
  exact (idealNorm_le_of_dvd hs'.1
    ⟨rowFreePart B s, (row_fixed_free_product B hs'.1 hs'.2.1).symm⟩).trans hs'.2.2

theorem rowFreePart_mem_sieveRows (c : ArithmeticContext) (B : Finset (Ideal O))
    (hB : ∀ p ∈ B, Prime p) (hS : c.S ⊆ B) (H : ℝ)
    {s : Ideal O} (hs : s ∈ rawOriginalRows H) :
    rowFreePart B s ∈ sieveRows c.S (rawRowHeight H (rowFixedPart B s)) := by
  have hs' := (mem_rawOriginalRows H s).mp hs
  have hout := rowFreePart_squarefree_outside c B hB hS s
  have hcop : IsRelPrime (rowFreePart B s) (principal 6) := by
    apply (isRelPrime_iff_no_prime_factors hout.1.1).mpr
    intro p hpk hp6 hp
    have h6 : principal (6 : O) = principal 2 * principal 3 := by
      simp only [principal, Ideal.span_singleton_mul_span_singleton]
      norm_num
    rw [h6] at hp6
    rcases hp.dvd_mul.mp hp6 with hp2 | hp3
    · exact hout.1.2 p (c.above_two p hp hp2) hpk
    · exact hout.1.2 p (c.above_three p hp hp3) hpk
  apply (mem_sieveRows _ _ _).mpr
  exact ⟨hout, hcop,
    ((rowFreePart_norm_le_iff B hs'.1 hs'.2.1 H).mpr hs'.2.2).trans
      (rawRowHeight_div_le H _)⟩


/-- The actual finite data supplied by reflection uniformity. The pool and
coefficient bound are fixed before the varying prime set and free ideal. -/
structure RawUniformData (c : ArithmeticContext) (ξ : RayCharacter c) where
  N : ℕ
  H : ℕ
  pool : Fin N → ReflectionDatum
  K : ℝ
  K_nonneg : 0 ≤ K
  pick : ∀ (P : Finset (Ideal O)) (j : Ideal O → Fin 6), PrimeTwistSet c.S P →
    Ideal O → Fin H → Finset (Ideal O) → Fin N
  coeff : ∀ (P : Finset (Ideal O)) (j : Ideal O → Fin 6), PrimeTwistSet c.S P →
    Ideal O → Fin H → Finset (Ideal O) → ℂ
  bound : ∀ P j hP k, SquarefreeOutside c.S k → IsRelPrime k (∏ p ∈ P, p) →
    ∀ h A, AdmissibleActive P j A → ‖coeff P j hP k h A‖ ≤ K
  identity : ∀ P j hP k, SquarefreeOutside c.S k → IsRelPrime k (∏ p ∈ P, p) →
    ∀ (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ),
      SmoothSupported I W → 0 < X →
      completedSum c (productTwist c ξ (P ∪ primeFactors k) (variableTwistExponents P j)) W X =
        ∑ h : Fin H, ∑ A ∈ P.powerset,
          if AdmissibleActive P j A then coeff P j hP k h A *
            dualThetaSum (pool (pick P j hP k h A)) (A ∪ primeFactors k)
              (variableTwistExponents P j) (fun x => (Real.sqrt x : ℂ) * W x) X
          else 0

theorem rawUniformData_nonempty (hR : ReflectionUniformityStatement)
    (c : ArithmeticContext) (ξ : RayCharacter c) : Nonempty (RawUniformData c ξ) := by
  obtain ⟨N, H, pool, K, hK, M, hM, hMS, h⟩ := hR c ξ
  choose pick coeff hcoh h using h
  exact ⟨{ N := N, H := H, pool := pool, K := K, K_nonneg := hK
           pick := pick, coeff := coeff
           bound := fun P j hP k hk hcop => (h P j hP k hk hcop).1
           identity := fun P j hP k hk hcop => (h P j hP k hk hcop).2 }⟩

def rawUniformData (hR : ReflectionUniformityStatement)
    (c : ArithmeticContext) (ξ : RayCharacter c) : RawUniformData c ξ :=
  Classical.choice (rawUniformData_nonempty hR c ξ)

/-- Separating the selected datum into its fixed finite pool changes no row
and leaves every coefficient bound unchanged. -/
theorem RawUniformData.identity_pool (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) {k : Ideal O} (hk : SquarefreeOutside c.S k)
    (hcop : IsRelPrime k (∏ p ∈ P, p))
    (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ) (hW : SmoothSupported I W) (hX : 0 < X) :
    completedSum c (productTwist c ξ (P ∪ primeFactors k) (variableTwistExponents P j)) W X =
      ∑ n : Fin d.N, ∑ h : Fin d.H, ∑ A ∈ P.powerset,
        if AdmissibleActive P j A ∧ d.pick P j hP k h A = n then
          d.coeff P j hP k h A * dualThetaSum (d.pool n) (A ∪ primeFactors k)
            (variableTwistExponents P j) (fun x => (Real.sqrt x : ℂ) * W x) X
        else 0 := by
  rw [d.identity P j hP k hk hcop I W X hW hX]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases ha : AdmissibleActive P j A
  · simp only [ha, true_and, ↓reduceIte]
    simpa only [↓reduceIte] using (Finset.sum_eq_single (s := Finset.univ)
      (f := fun n : Fin d.N => if d.pick P j hP k h A = n then
        d.coeff P j hP k h A * dualThetaSum (d.pool n) (A ∪ primeFactors k)
          (variableTwistExponents P j) (fun x => (Real.sqrt x : ℂ) * W x) X else 0)
      (d.pick P j hP k h A)
      (fun n hn hne => if_neg (Ne.symm hne)) (by simp)).symm
  · simp only [ha, false_and, ↓reduceIte, Finset.sum_const_zero]


theorem dualThetaSum_congr_exponents (d : ReflectionDatum) (A : Finset (Ideal O))
    (j j' : Ideal O → Fin 6) (V : ℝ → ℂ) (X : ℝ)
    (hj : ∀ p ∈ A, j p = j' p) :
    dualThetaSum d A j V X = dualThetaSum d A j' V X := by
  have hp (m : O) : (∏ p ∈ A, thetaLocalFactor p (j p) m) =
      ∏ p ∈ A, thetaLocalFactor p (j' p) m :=
    Finset.prod_congr rfl (fun p hp => congrArg (fun e => thetaLocalFactor p e m) (hj p hp))
  unfold dualThetaSum
  simp_rw [hp]

theorem variable_exponents_active (P A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : ∀ p ∈ P, Prime p) (hA : A ⊆ P) {k : Ideal O}
    (hcop : IsRelPrime k (∏ p ∈ P, p)) {p : Ideal O}
    (hp : p ∈ A ∪ primeFactors k) :
    variableTwistExponents P j p = variableTwistExponents A j p := by
  obtain hpA | hpk := Finset.mem_union.mp hp
  · simp only [variableTwistExponents, if_pos hpA, if_pos (hA hpA)]
  · have hpP : p ∉ P := fun h =>
      Finset.disjoint_left.mp (PacketCharacters.primeFactors_disjoint hP hcop) h hpk
    have hpA : p ∉ A := fun h => hpP (hA h)
    simp only [variableTwistExponents, if_neg hpP, if_neg hpA]

theorem dualThetaSum_variable_active (d : ReflectionDatum) (P A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (hP : ∀ p ∈ P, Prime p) (hA : A ⊆ P)
    {k : Ideal O} (hcop : IsRelPrime k (∏ p ∈ P, p)) (V : ℝ → ℂ) (X : ℝ) :
    dualThetaSum d (A ∪ primeFactors k) (variableTwistExponents P j) V X =
      dualThetaSum d (A ∪ primeFactors k) (variableTwistExponents A j) V X :=
  dualThetaSum_congr_exponents d _ _ _ V X
    (fun p hp => variable_exponents_active P A j hP hA hcop hp)


def rawCoefficientCondition (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (k : Ideal O) : Prop :=
  SquarefreeOutside c.S k ∧ IsRelPrime k (∏ p ∈ P, p) ∧
    select (t * k) = ξ ∧ d.pick P j hP k h A = n ∧ AdmissibleActive P j A

def rawMaskedCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (k : Ideal O) : ℂ :=
  if rawCoefficientCondition c ξ d P j hP t select n h A k then
    d.coeff P j hP k h A / ((d.K + 1 : ℝ) : ℂ) else 0

def rawMaskedPacket (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (H : ℝ) : RawReflectionPacket where
  H := rawRowHeight H t
  amplitude := if normIdeal t ≤ H then d.K + 1 else 0
  datum := d.pool n
  active := A
  exponent := j
  coeff := rawMaskedCoefficient c ξ d P j hP t select n h A

theorem rawMaskedCoefficient_norm_le (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (k : Ideal O) :
    ‖rawMaskedCoefficient c ξ d P j hP t select n h A k‖ ≤ 1 := by
  unfold rawMaskedCoefficient
  split_ifs with hk
  · have hα : 0 < d.K + 1 := by linarith [d.K_nonneg]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
    exact (div_le_iff₀ hα).mpr
      ((d.bound P j hP k hk.1 hk.2.1 h A hk.2.2.2.2).trans (by linarith))
  · simp

theorem coprime_subprod {P A : Finset (Ideal O)} (hA : A ⊆ P) {k : Ideal O}
    (hk : IsRelPrime k (∏ p ∈ P, p)) : IsRelPrime k (∏ p ∈ A, p) := by
  intro q hqk hqA
  exact hk hqk (hqA.trans (Finset.prod_dvd_prod_of_subset A P (fun p : Ideal O => p) hA))

theorem rawMaskedCoefficient_zero (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (hA : A ⊆ P) (k : Ideal O)
    (hk : ¬ IsRelPrime k (∏ p ∈ A, p)) :
    rawMaskedCoefficient c ξ d P j hP t select n h A k = 0 := by
  apply if_neg
  intro hc
  exact hk (coprime_subprod hA hc.2.1)

theorem rawMaskedPacket_amplitude_nonneg (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (H : ℝ) :
    0 ≤ (rawMaskedPacket c ξ d P j hP t select n h A H).amplitude := by
  change 0 ≤ if normIdeal t ≤ H then d.K + 1 else 0
  split_ifs <;> linarith [d.K_nonneg]

theorem rawMaskedPacket_row (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (H : ℝ)
    (W : ℝ → ℂ) (X : ℝ) (k : Ideal O) (hH : normIdeal t ≤ H) :
    rawReflectionRow W X (rawMaskedPacket c ξ d P j hP t select n h A H) k =
      if rawCoefficientCondition c ξ d P j hP t select n h A k then
        d.coeff P j hP k h A * dualThetaSum (d.pool n) (A ∪ primeFactors k)
          (variableTwistExponents A j) (fun x => (Real.sqrt x : ℂ) * W x) X
      else 0 := by
  have hα : ((d.K + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [d.K_nonneg])
  unfold rawReflectionRow rawMaskedPacket rawMaskedCoefficient
  simp only [if_pos hH]
  split_ifs
  · have hcancel : ((d.K + 1 : ℝ) : ℂ) *
        (d.coeff P j hP k h A / ((d.K + 1 : ℝ) : ℂ)) = d.coeff P j hP k h A := by
      field_simp [hα]
    rw [hcancel]
  · simp only [mul_zero, zero_mul]

/-- The square of the full active conductor has the universal exponent 4C;
this scale bound is separate from the sharper local cost bound. -/
theorem rawMaskedPacket_valid (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (ht : t ≠ ⊥)
    (select : Ideal O → RayCharacter c) (n : Fin d.N) (h : Fin d.H)
    (A : Finset (Ideal O)) (hA : A ⊆ P) (D C L X H Ng : ℝ)
    (hD : 2 ≤ D) (hC : 1 ≤ C) (hH : 1 ≤ H) (hHC : H ≤ D ^ C) (hX : 1 ≤ X)
    (hL : 1 ≤ L) (hNd : normElement (d.pool n).denominator ^ 2 ≤ L)
    (hNg : 0 ≤ Ng) (hNgC : Ng ≤ D ^ C)
    (hprod : (∏ p ∈ P, normIdeal p) ≤ Ng) :
    (rawMaskedPacket c ξ d P j hP t select n h A H).Valid c.S D (4 * C) L X
      (6 * 3 ^ P.card) := by
  have hheight := rawRowHeight_bounds hH ht
  have hHA : 0 ≤ rawRowHeight H t := zero_le_one.trans hheight.1
  have hHX : 0 < X := zero_lt_one.trans_le hX
  have hN0 : 0 < normElement (d.pool n).denominator := normIdeal_pos
    (fun hz => (d.pool n).denominator_ne_zero (Ideal.span_singleton_eq_bot.mp hz))
  have hAp : PrimeTwistSet c.S A := fun p hp => hP p (hA hp)
  have hAP : (∏ p ∈ A, normIdeal p) ≤ ∏ p ∈ P, normIdeal p :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hA
      (fun p hp => zero_le_one.trans (primeTwist_norm_one_le c hP p (hA hp)))
      (fun p hp hpA => primeTwist_norm_one_le c hP p hp)
  have hAn : 0 ≤ ∏ p ∈ A, normIdeal p :=
    Finset.prod_nonneg (fun p hp => (normIdeal_pos (hAp p hp).1.ne_zero).le)
  have hscale := raw_fourth_scale_bound D C X (rawRowHeight H t)
    (∏ p ∈ A, normIdeal p) (normElement (d.pool n).denominator) L
    hD hHA (hheight.2.trans hHC) hAn ((hAP.trans hprod).trans hNgC) hX
    (zero_le_one.trans hL) hNd
  refine ⟨hheight.1, ?_, ?_, ?_,
    rawMaskedPacket_amplitude_nonneg c ξ d P j hP t select n h A H,
    hAp, ?_, ?_, ?_⟩
  · exact (hheight.2.trans hHC).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  · change 0 < normElement (d.pool n).denominator ^ 2 * (rawRowHeight H t) ^ 2 / X
    exact div_pos (mul_pos (sq_pos_of_pos hN0)
      (sq_pos_of_pos (zero_lt_one.trans_le hheight.1))) hHX
  · change (normElement (d.pool n).denominator ^ 2 * (rawRowHeight H t) ^ 2 / X) *
      (∏ p ∈ A, normIdeal p ^ 2) ≤ L * D ^ (4 * C)
    simpa only [Finset.prod_pow] using hscale
  · intro k hk
    exact rawMaskedCoefficient_norm_le c ξ d P j hP t select n h A k
  · intro k hk hcop
    exact rawMaskedCoefficient_zero c ξ d P j hP t select n h A hA k hcop
  · exact Nat.mul_le_mul_left 6 (Nat.pow_le_pow_right (by decide) (Finset.card_le_card hA))

theorem rawMaskedPacket_budget (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (ht : t ≠ ⊥)
    (select : Ideal O → RayCharacter c) (n : Fin d.N) (h : Fin d.H)
    (A : Finset (Ideal O)) (H X Ng L B : ℝ)
    (hH : 1 ≤ H) (hX : 0 < X) (hNg : 0 ≤ Ng) (hL : 1 ≤ L)
    (hNd : normElement (d.pool n).denominator ^ 2 ≤ L) (hB : d.K + 1 ≤ B)
    (hcost : (∏ p ∈ A, reflectionLocalCost (normIdeal p) (j p)) ≤ normIdeal t ^ 2 * Ng) :
    let p := rawMaskedPacket c ξ d P j hP t select n h A H
    p.amplitude ^ 2 * (p.H + rawReflectionScale X p * rawReflectionCost p) ≤
      (B ^ 2 * L) * (H + H ^ 2 * Ng / X) := by
  have hpoly : 0 ≤ H + H ^ 2 * Ng / X := by positivity
  have hB0 : 0 ≤ B := (by linarith [d.K_nonneg] : 0 ≤ d.K + 1).trans hB
  dsimp only
  by_cases hHt : normIdeal t ≤ H
  · change (if normIdeal t ≤ H then d.K + 1 else 0) ^ 2 *
      (rawRowHeight H t +
        (normElement (d.pool n).denominator ^ 2 * (rawRowHeight H t) ^ 2 / X) *
          (∏ p ∈ A, reflectionLocalCost (normIdeal p) (j p))) ≤ _
    rw [if_pos hHt, rawRowHeight_of_norm_le ht hHt]
    have hc := raw_scaled_cost_bound H (normIdeal t) Ng X
      (normElement (d.pool n).denominator) L (d.K + 1) _
      (zero_le_one.trans hH) (normIdeal_one_le_of_ne_bot ht) hNg hX hL hNd hcost
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [d.K_nonneg]) hB 2)
        (zero_le_one.trans hL)) hpoly)
  · change (if normIdeal t ≤ H then d.K + 1 else 0) ^ 2 * _ ≤ _
    rw [if_neg hHt]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (zero_le_one.trans hL)) hpoly


theorem rawMaskedPacket_row_zero_character (c : ArithmeticContext) (ξ : RayCharacter c)
    (d : RawUniformData c ξ) (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hP : PrimeTwistSet c.S P) (t : Ideal O) (select : Ideal O → RayCharacter c)
    (n : Fin d.N) (h : Fin d.H) (A : Finset (Ideal O)) (H : ℝ)
    (W : ℝ → ℂ) (X : ℝ) (k : Ideal O) (hξ : select (t * k) ≠ ξ) :
    rawReflectionRow W X (rawMaskedPacket c ξ d P j hP t select n h A H) k = 0 := by
  have hz : rawMaskedCoefficient c ξ d P j hP t select n h A k = 0 :=
    if_neg (fun hc => hξ hc.2.2.1)
  change _ * rawMaskedCoefficient c ξ d P j hP t select n h A k * _ = 0
  rw [hz, mul_zero, zero_mul]

/-- The pool separation is an exact finite identity with a fixed index set.
The selected character and selected datum occur only inside coefficients. -/
theorem rawMaskedPacket_pool_sum (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ)
    (P : Finset (Ideal O)) (j : Ideal O → Fin 6) (hP : PrimeTwistSet c.S P)
    (t : Ideal O) (select : Ideal O → RayCharacter c) (H : ℝ) (hH : normIdeal t ≤ H)
    (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ) (hW : SmoothSupported I W) (hX : 0 < X)
    {k : Ideal O} (hk : SquarefreeOutside c.S k) (hcop : IsRelPrime k (∏ p ∈ P, p)) :
    completedSum c
      (productTwist c (select (t * k)) (P ∪ primeFactors k) (variableTwistExponents P j)) W X =
      ∑ ξ : RayCharacter c, ∑ n : Fin (d ξ).N, ∑ h : Fin (d ξ).H,
        ∑ A : P.powerset,
          rawReflectionRow W X (rawMaskedPacket c ξ (d ξ) P j hP t select n h A.1 H) k := by
  let ξ₀ := select (t * k)
  have hs : completedSum c
      (productTwist c ξ₀ (P ∪ primeFactors k) (variableTwistExponents P j)) W X =
        ∑ n : Fin (d ξ₀).N, ∑ h : Fin (d ξ₀).H,
          ∑ A : P.powerset,
            rawReflectionRow W X (rawMaskedPacket c ξ₀ (d ξ₀) P j hP t select n h A.1 H) k := by
    rw [RawUniformData.identity_pool c ξ₀ (d ξ₀) P j hP hk hcop I W X hW hX]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_coe_sort P.powerset (fun A =>
      rawReflectionRow W X (rawMaskedPacket c ξ₀ (d ξ₀) P j hP t select n h A H) k)]
    apply Finset.sum_congr rfl
    intro A hA
    rw [rawMaskedPacket_row c ξ₀ (d ξ₀) P j hP t select n h A H W X k hH]
    by_cases ha : AdmissibleActive P j A
    · by_cases hn' : (d ξ₀).pick P j hP k h A = n
      · simp only [rawCoefficientCondition, hk, hcop, ξ₀, ha, hn',
          true_and, and_self, ↓reduceIte]
        rw [dualThetaSum_variable_active ((d ξ₀).pool n) P A j
          (fun p hp => (hP p hp).1) ha.1 hcop]
      · simp only [rawCoefficientCondition, hk, hcop, ξ₀, ha, hn',
          true_and, false_and, and_false, ↓reduceIte]
    · simp only [rawCoefficientCondition, hk, hcop, ξ₀, ha,
        true_and, false_and, and_false, ↓reduceIte]
  refine hs.trans (Finset.sum_eq_single (s := Finset.univ)
    (f := fun ξ : RayCharacter c => ∑ n : Fin (d ξ).N, ∑ h : Fin (d ξ).H,
      ∑ A : P.powerset,
        rawReflectionRow W X (rawMaskedPacket c ξ (d ξ) P j hP t select n h A.1 H) k)
    ξ₀ ?_ (by simp)).symm
  intro ξ hξ hne
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro h hh
  apply Finset.sum_eq_zero
  intro A hA
  exact rawMaskedPacket_row_zero_character c ξ (d ξ) P j hP t select n h A.1 H W X k
    (Ne.symm hne)


abbrev RawSplitIndex (S P : Finset (Ideal O)) (ι : Type*) :=
  {T : Finset (Ideal O) // T ∈ (S ∪ P).powerset} ×
    {A : Finset (Ideal O) // A ∈ P.powerset} × ι

theorem rawSplitIndex_card_budget (S P : Finset (Ideal O)) (hSP : Disjoint S P)
    (ι : Type*) [Fintype ι] :
    Fintype.card (RawSplitIndex S P ι) * (6 * 3 ^ P.card) =
      (6 * Fintype.card ι * 2 ^ S.card) * 12 ^ P.card := by
  simp only [RawSplitIndex, Fintype.card_prod, Fintype.card_coe, Finset.card_powerset,
    Finset.card_union_of_disjoint hSP, pow_add]
  have hp : (12 : ℕ) ^ P.card = 2 ^ P.card * 2 ^ P.card * 3 ^ P.card := by
    rw [show (12 : ℕ) = 2 * 2 * 3 by rfl, mul_pow, mul_pow]
  rw [hp]
  ring

/-- One divisor exponent pays for both fixed-row subsets, the active subsets,
and all three exceptional branches, with no second small-power loss. -/
theorem rawSplitIndex_count_uniform (c : ArithmeticContext) (ι : Type*) [Fintype ι]
    (δ C : ℝ) (hδ : 0 < δ) (hC : 1 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (g : O) (D : ℝ), g ≠ 0 → 2 ≤ D →
      normElement g ≤ D ^ C →
      ((Fintype.card (RawSplitIndex c.S (auxiliaryPrimes c g) ι) *
          (6 * 3 ^ (auxiliaryPrimes c g).card) : ℕ) : ℝ) ≤ B * D ^ δ := by
  obtain ⟨B, hB, hb⟩ := auxiliary_choices_uniform 12 δ C (by norm_num) hδ hC
  let K : ℝ := ((6 * Fintype.card ι * 2 ^ c.S.card : ℕ) : ℝ)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  refine ⟨1 + K * B, le_add_of_nonneg_right (mul_nonneg hK (zero_le_one.trans hB)), ?_⟩
  intro g D hg hD hgD
  have hd : Disjoint c.S (auxiliaryPrimes c g) :=
    Finset.disjoint_left.mpr (fun p hp hp' => (Finset.mem_sdiff.mp hp').2 hp)
  rw [rawSplitIndex_card_budget c.S (auxiliaryPrimes c g) hd ι,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    K * 12 ^ (auxiliaryPrimes c g).card ≤ K * (B * D ^ δ) :=
      mul_le_mul_of_nonneg_left (hb c g D hg hD hgD) hK
    _ ≤ (1 + K * B) * D ^ δ := by
      have hp : 0 ≤ D ^ δ := Real.rpow_nonneg (by linarith) _
      nlinarith


abbrev RawUniformIndex (c : ArithmeticContext) (d : ∀ ξ : RayCharacter c, RawUniformData c ξ) :=
  Σ ξ : RayCharacter c, Fin (d ξ).N × Fin (d ξ).H

def rawUniformAmplitude (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ) : ℝ :=
  1 + ∑ ξ : RayCharacter c, (d ξ).K

def rawUniformConductor (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ) : ℝ :=
  1 + ∑ ξ : RayCharacter c, ∑ n : Fin (d ξ).N, normElement ((d ξ).pool n).denominator ^ 2

theorem rawUniformAmplitude_one_le (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ) : 1 ≤ rawUniformAmplitude c d := by
  have h := Finset.sum_nonneg (fun ξ (_ : ξ ∈ Finset.univ) => (d ξ).K_nonneg)
  change 1 ≤ 1 + _
  linarith

theorem rawUniformAmplitude_bound (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ) (ξ : RayCharacter c) :
    (d ξ).K + 1 ≤ rawUniformAmplitude c d := by
  have h : (d ξ).K ≤ ∑ η : RayCharacter c, (d η).K :=
    Finset.single_le_sum (fun η _ => (d η).K_nonneg) (Finset.mem_univ ξ)
  change _ ≤ 1 + _
  linarith

theorem rawUniformConductor_one_le (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ) : 1 ≤ rawUniformConductor c d := by
  have h : 0 ≤ ∑ ξ : RayCharacter c, ∑ n : Fin (d ξ).N,
      normElement ((d ξ).pool n).denominator ^ 2 :=
    Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun n _ => sq_nonneg _))
  change 1 ≤ 1 + _
  linarith

theorem rawUniformConductor_bound (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ)
    (ξ : RayCharacter c) (n : Fin (d ξ).N) :
    normElement ((d ξ).pool n).denominator ^ 2 ≤ rawUniformConductor c d := by
  have h₁ : normElement ((d ξ).pool n).denominator ^ 2 ≤
      ∑ m : Fin (d ξ).N, normElement ((d ξ).pool m).denominator ^ 2 :=
    Finset.single_le_sum
      (f := fun m : Fin (d ξ).N => normElement ((d ξ).pool m).denominator ^ 2)
      (fun m _ => sq_nonneg _) (Finset.mem_univ n)
  have h₂ : (∑ m : Fin (d ξ).N, normElement ((d ξ).pool m).denominator ^ 2) ≤
      ∑ η : RayCharacter c, ∑ m : Fin (d η).N, normElement ((d η).pool m).denominator ^ 2 :=
    Finset.single_le_sum
      (f := fun η : RayCharacter c =>
        ∑ m : Fin (d η).N, normElement ((d η).pool m).denominator ^ 2)
      (fun η _ => Finset.sum_nonneg (fun m _ => sq_nonneg _))
      (Finset.mem_univ ξ)
  change _ ≤ 1 + _
  linarith


def rawPacketFamily (c : ArithmeticContext) (d : ∀ ξ : RayCharacter c, RawUniformData c ξ)
    (P : Finset (Ideal O)) (hP : PrimeTwistSet c.S P)
    (j : Finset (Ideal O) → Ideal O → Fin 6) (select : Ideal O → RayCharacter c)
    (H : ℝ) (i : RawSplitIndex c.S P (RawUniformIndex c d)) : RawReflectionPacket :=
  rawMaskedPacket c i.2.2.1 (d i.2.2.1) P (j i.1.1) hP
    (∏ p ∈ i.1.1, p) select i.2.2.2.1 i.2.2.2.2 i.2.1.1 H

theorem rawSplitIndex_sum_tag {ι : Type*} [Fintype ι] (S P : Finset (Ideal O))
    (T : (S ∪ P).powerset) (F : RawSplitIndex S P ι → ℂ) :
    (∑ i : RawSplitIndex S P ι, if T.1 = i.1.1 then F i else 0) =
      ∑ A : P.powerset, ∑ j : ι, F (T, A, j) := by
  simp only [RawSplitIndex, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single T]
  · simp only [ite_true]
  · intro U hU hUT
    have hv : T.1 ≠ U.1 := fun h => hUT (Subtype.ext h.symm)
    simp only [if_neg hv, Finset.sum_const_zero]
  · simp

theorem rawSplitIndex_uniform_sum_tag (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ) (P : Finset (Ideal O))
    (T : (c.S ∪ P).powerset) (F : RawSplitIndex c.S P (RawUniformIndex c d) → ℂ) :
    (∑ i : RawSplitIndex c.S P (RawUniformIndex c d), if T.1 = i.1.1 then F i else 0) =
      ∑ ξ : RayCharacter c, ∑ n : Fin (d ξ).N, ∑ h : Fin (d ξ).H,
        ∑ A : P.powerset, F (T, A, ⟨ξ, (n, h)⟩) := by
  rw [rawSplitIndex_sum_tag]
  simp only [RawUniformIndex, Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]


theorem rawPacketFamily_valid (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ)
    (P : Finset (Ideal O)) (hP : PrimeTwistSet c.S P)
    (j : Finset (Ideal O) → Ideal O → Fin 6) (select : Ideal O → RayCharacter c)
    (D C H X Ng : ℝ) (hD : 2 ≤ D) (hC : 1 ≤ C) (hH : 1 ≤ H)
    (hHC : H ≤ D ^ C) (hX : 1 ≤ X) (hNg : 0 ≤ Ng) (hNgC : Ng ≤ D ^ C)
    (hprod : (∏ p ∈ P, normIdeal p) ≤ Ng)
    (i : RawSplitIndex c.S P (RawUniformIndex c d)) :
    (rawPacketFamily c d P hP j select H i).Valid c.S D (4 * C)
      (rawUniformConductor c d) X (6 * 3 ^ P.card) := by
  exact rawMaskedPacket_valid c i.2.2.1 (d i.2.2.1) P (j i.1.1) hP
    (∏ p ∈ i.1.1, p) (fixedSubset_product_ne_bot c hP (Finset.mem_powerset.mp i.1.2))
    select i.2.2.2.1 i.2.2.2.2 i.2.1.1 (Finset.mem_powerset.mp i.2.1.2)
    D C (rawUniformConductor c d) X H Ng hD hC hH hHC hX
    (rawUniformConductor_one_le c d) (rawUniformConductor_bound c d _ _) hNg hNgC hprod

theorem rawPacketFamily_budget (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ)
    (P : Finset (Ideal O)) (hP : PrimeTwistSet c.S P)
    (v : Ideal O → ℕ) (hv : ∀ p ∈ P, 1 ≤ v p)
    (select : Ideal O → RayCharacter c) (H X Ng : ℝ)
    (hH : 1 ≤ H) (hX : 0 < X) (hNg : 0 ≤ Ng)
    (hw : (∏ p ∈ P, normIdeal p ^ v p) ≤ Ng)
    (i : RawSplitIndex c.S P (RawUniformIndex c d)) :
    let p := rawPacketFamily c d P hP (fun T => rowAuxiliaryExponent v (T \ c.S)) select H i
    p.amplitude ^ 2 * (p.H + rawReflectionScale X p * rawReflectionCost p) ≤
      (rawUniformAmplitude c d ^ 2 * rawUniformConductor c d) *
        (H + H ^ 2 * Ng / X) := by
  exact rawMaskedPacket_budget c i.2.2.1 (d i.2.2.1) P
    (rowAuxiliaryExponent v (i.1.1 \ c.S)) hP (∏ p ∈ i.1.1, p)
    (fixedSubset_product_ne_bot c hP (Finset.mem_powerset.mp i.1.2))
    select i.2.2.2.1 i.2.2.2.2 i.2.1.1 H X Ng
    (rawUniformConductor c d) (rawUniformAmplitude c d) hH hX hNg
    (rawUniformConductor_one_le c d) (rawUniformConductor_bound c d _ _)
    (rawUniformAmplitude_bound c d _)
    (fixedSubset_local_cost c hP (Finset.mem_powerset.mp i.1.2)
      (Finset.mem_powerset.mp i.2.1.2) v hv Ng hNg hw)


/-- The remaining outer regrouping is finite: each original row is injected
by its fixed prime subset and its actual free ideal. -/
theorem rawPacketFamily_energy_cover (c : ArithmeticContext) [Fintype (RayCharacter c)]
    (d : ∀ ξ : RayCharacter c, RawUniformData c ξ)
    (P : Finset (Ideal O)) (hP : PrimeTwistSet c.S P)
    (j : Finset (Ideal O) → Ideal O → Fin 6) (select : Ideal O → RayCharacter c)
    (H : ℝ) (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ)
    (hW : SmoothSupported I W) (hX : 0 < X) (F : Ideal O → ℂ)
    (hF : ∀ s ∈ rawOriginalRows H, F s =
      completedSum c (productTwist c (select s)
        (P ∪ primeFactors (rowFreePart (c.S ∪ P) s))
        (variableTwistExponents P (j (rowFixedPrimes (c.S ∪ P) s)))) W X) :
    (∑ s ∈ rawOriginalRows H, ‖F s‖ ^ 2) ≤
      (Fintype.card (RawSplitIndex c.S P (RawUniformIndex c d)) : ℝ) *
        ∑ i : RawSplitIndex c.S P (RawUniformIndex c d),
          rawReflectionEnergy c.S W X (rawPacketFamily c d P hP j select H i) := by
  let B := c.S ∪ P
  have hB : ∀ p ∈ B, Prime p := fixedSubset_primes c hP (fun _ hp => hp)
  have hS : c.S ⊆ B := Finset.subset_union_left
  have hrow (s : Ideal O) (hs : s ∈ rawOriginalRows H) :
      F s = ∑ i : RawSplitIndex c.S P (RawUniformIndex c d),
        if rowFixedPrimes B s = i.1.1 then
          rawReflectionRow W X (rawPacketFamily c d P hP j select H i) (rowFreePart B s)
        else 0 := by
    let T : B.powerset := ⟨rowFixedPrimes B s, Finset.mem_powerset.mpr (rowFixedPrimes_subset B s)⟩
    have hs' := (mem_rawOriginalRows H s).mp hs
    have hk := rowFreePart_squarefree_outside c B hB hS s
    have hcop : IsRelPrime (rowFreePart B s) (∏ p ∈ P, p) := by
      intro q hqk hqP
      exact rowFreePart_coprime B hB s hqk
        (hqP.trans (Finset.prod_dvd_prod_of_subset P B (fun p => p) Finset.subset_union_right))
    have hp := rawMaskedPacket_pool_sum c d P (j T.1) hP
      (rowFixedPart B s) select H (rowFixedPart_norm_le_original B H hs)
      I W X hW hX hk hcop
    rw [row_fixed_free_product B hs'.1 hs'.2.1] at hp
    rw [hF s hs]
    refine hp.trans ?_
    have hflat := rawSplitIndex_uniform_sum_tag c d P T
      (fun i => rawReflectionRow W X (rawPacketFamily c d P hP j select H i) (rowFreePart B s))
    exact hflat.symm
  have hmem : ∀ s ∈ rawOriginalRows H,
      ∀ i : RawSplitIndex c.S P (RawUniformIndex c d), rowFixedPrimes B s = i.1.1 →
        rowFreePart B s ∈ sieveRows c.S (rawPacketFamily c d P hP j select H i).H := by
    intro s hs i hi
    change rowFreePart B s ∈ sieveRows c.S (rawRowHeight H (∏ p ∈ i.1.1, p))
    rw [← hi]
    exact rowFreePart_mem_sieveRows c B hB hS H hs
  exact finite_row_cover (rawOriginalRows H) (rowFixedPrimes B) (rowFreePart B)
    (fun i : RawSplitIndex c.S P (RawUniformIndex c d) => i.1.1)
    (fun i => sieveRows c.S (rawPacketFamily c d P hP j select H i).H) F
    (fun i k => rawReflectionRow W X (rawPacketFamily c d P hP j select H i) k)
    (rowParts_injOn_originalRows B H) hmem (fun s hs => by
      refine (hrow s hs).trans ?_
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : rowFixedPrimes B s = i.1.1 <;> simp only [h, ↓reduceIte])


/-- Actual finite reflection packets for every squarefree row, including the
rows meeting S. All constants and the finite ray space precede W,D,H,X,g,u. -/
theorem squarefree_raw_reflection_step_proved : SquarefreeRawReflectionStep := by
  intro hr hu δ C hδ hC
  refine ⟨4 * C, by linarith, ?_⟩
  intro c I hc ξ
  obtain ⟨M, hM, hMS, hMR, hchar⟩ := exists_common_supported_context c hc
  let c' := refineArithmeticContext c M hM hMS hMR
  let reciprocity : SquarefreeReflection.ReciprocityData c :=
    Classical.choice (reciprocityData_nonempty c hc)
  letI : Finite (RayCharacter c') := rayCharacter_finite c'
  letI : Fintype (RayCharacter c') := Fintype.ofFinite _
  let data : ∀ χ : RayCharacter c', RawUniformData c' χ := fun χ => rawUniformData hu c' χ
  let L := rawUniformConductor c' data
  let A₀ := rawUniformAmplitude c' data
  have hL : 1 ≤ L := rawUniformConductor_one_le c' data
  have hA₀ : 1 ≤ A₀ := rawUniformAmplitude_one_le c' data
  obtain ⟨B₀, hB₀, hcount⟩ := rawSplitIndex_count_uniform c' (RawUniformIndex c' data) δ C hδ hC
  let B := B₀ + A₀ ^ 2 * L
  have hB₀B : B₀ ≤ B := le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg _) (zero_le_one.trans hL))
  have hcostB : A₀ ^ 2 * L ≤ B := le_add_of_nonneg_left (zero_le_one.trans hB₀)
  refine ⟨L, B, hL, hB₀.trans hB₀B, ?_⟩
  intro W D H X g u hW hD hH hHC hX hXC hg hgC
  have hg0 : g ≠ 0 := by
    intro he
    subst g
    norm_num [normElement, principal, normIdeal] at hg
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hNg0 : 0 ≤ normElement g := zero_le_one.trans hg
  obtain ⟨select, hselect⟩ := raw_twist_character_family c reciprocity ξ M hM hMS hMR hchar hg0 u
  let P := auxiliaryPrimes c' g
  let hP : PrimeTwistSet c'.S P := auxiliaryPrimes_primeTwist c' g
  let j := rawAuxiliaryExponents c' g
  let R := RawSplitIndex c'.S P (RawUniformIndex c' data)
  let family : R → RawReflectionPacket := rawPacketFamily c' data P hP j select H
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let packet : Fin (Fintype.card R) → RawReflectionPacket := fun i => family (e.symm i)
  refine ⟨Fintype.card R, 6 * 3 ^ P.card, packet, ?_, ?_, ?_, ?_⟩
  · intro i
    exact rawPacketFamily_valid c' data P hP j select D C H X (normElement g)
      hD hC hH hHC hX hNg0 hgC (auxiliaryPrimes_norm_product_le c' hg0) (e.symm i)
  · exact (hcount g D hg0 hD hgC).trans
      (mul_le_mul_of_nonneg_right hB₀B (Real.rpow_nonneg (by linarith) _))
  · intro i
    have hv : ∀ p ∈ P,
        1 ≤ (UniqueFactorizationMonoid.normalizedFactors (principal g)).count p :=
      fun p hp => auxiliaryPrimes_multiplicity_pos c' g hp
    have hbudget := rawPacketFamily_budget c' data P hP
      (fun p => (UniqueFactorizationMonoid.normalizedFactors (principal g)).count p)
      hv select H X (normElement g) hH hX0 hNg0
      (auxiliaryPrimes_weighted_norm_le c' hg0) (e.symm i)
    exact hbudget.trans (mul_le_mul_of_nonneg_right hcostB (by positivity))
  · rw [rawOriginalRows_tsum]
    have hrow : ∀ s ∈ rawOriginalRows H,
        completedRowElement c ξ W X ((u : O) * chosenGenerator s) g =
          completedSum c' (productTwist c' (select s)
            (P ∪ primeFactors (rowFreePart (c'.S ∪ P) s))
            (variableTwistExponents P (j (rowFixedPrimes (c'.S ∪ P) s)))) W X := by
      intro s hs
      have hs' := (mem_rawOriginalRows H s).mp hs
      unfold completedRowElement
      rw [hselect s hs'.1 hs'.2.1]
      exact (completedSum_refine_context c M hM hMS hMR _ W X).symm
    have he := rawPacketFamily_energy_cover c' data P hP j select H I W X hW hX0
      (fun s => completedRowElement c ξ W X ((u : O) * chosenGenerator s) g) hrow
    have hsum : (∑ i : Fin (Fintype.card R), rawReflectionEnergy c.S W X (packet i)) =
        ∑ i : R, rawReflectionEnergy c.S W X (family i) :=
      e.symm.sum_comp (fun i : R => rawReflectionEnergy c.S W X (family i))
    rw [hsum]
    exact he

theorem squarefree_reflection_packet_step_proved : SquarefreeReflectionPacketStep :=
  squarefree_reflection_packet_step_of_children
    squarefree_raw_reflection_step_proved dual_theta_packet_step_proved

end QRHShort.SquarefreeAssembly.PacketConstruction
