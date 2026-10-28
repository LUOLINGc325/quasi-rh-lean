import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic

import QRHShort.PoissonReduction
import QRHShort.IdealMobiusCancellation
import QRHShort.PrimaryGenerator
import QRHShort.SmoothedSummability
import QRHShort.HeckeMultiplicative
import QRHShort.SquarefreeNumeratorProducts
import QRHShort.SquarefreePrimeSymbol
import QRHShort.QuotientSixthRoot
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Squarefree.Basic

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch

theorem expansion_outside_mul (c : ArithmeticContext) (a b : Ideal O) :
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

theorem expansion_outside_of_dvd (c : ArithmeticContext) {a b : Ideal O}
    (hb : Outside c.S b) (hab : a ∣ b) : Outside c.S a := by
  refine ⟨ne_zero_of_dvd_ne_zero hb.1 hab, fun p hp hpa => hb.2 p hp (hpa.trans hab)⟩

theorem expansion_primary_spec (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : principal (primaryGenerator a) = a := by
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
  have hex : ∃ w : O, principal w = a ∧ IsPrimary w :=
    ⟨(u : O) * z, (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz, hu⟩
  exact (show principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) by
    simpa only [primaryGenerator, dite_eq_left hex] using Classical.choose_spec hex).1

theorem expansion_primary_ne_zero (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : primaryGenerator a ≠ 0 := by
  intro h
  apply ha.1
  rw [← expansion_primary_spec c ha, h]
  simp [principal]

theorem expansion_principal_mul (a b : O) : principal (a * b) = principal a * principal b := by
  unfold principal
  rw [Ideal.span_singleton_mul_span_singleton]

/-- The source indices after writing the genuine ideal quotient g/e as b. -/
def ExpansionSplitAdmissible (c : ArithmeticContext)
    (p : Ideal O × Ideal O × Ideal O × O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2.1 ∧
    SquarefreeOutside c.S p.2.2.1 ∧ IsRelPrime p.1 p.2.1 ∧
    IsRelPrime p.1 p.2.2.1 ∧ IsRelPrime p.2.1 p.2.2.1 ∧
    p.2.2.2 ≠ 0 ∧ IsRelPrime p.2.2.1 (principal p.2.2.2)

def ExpansionOutputAdmissible (c : ArithmeticContext)
    (p : Ideal O × Ideal O × O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2.1 ∧
    IsRelPrime p.1 p.2.1 ∧ p.2.2 ≠ 0

abbrev ExpansionSplit (c : ArithmeticContext) :=
  {p : Ideal O × Ideal O × Ideal O × O // ExpansionSplitAdmissible c p}

abbrev ExpansionOutput (c : ArithmeticContext) :=
  {p : Ideal O × Ideal O × O // ExpansionOutputAdmissible c p}

def expansionRecombine (c : ArithmeticContext) : ExpansionSplit c → ExpansionOutput c :=
  fun p => ⟨(p.1.1, p.1.2.1 * p.1.2.2.1, primaryGenerator p.1.2.1 * p.1.2.2.2),
    p.2.1,
    ⟨(expansion_outside_mul c _ _).mpr ⟨p.2.2.1.1, p.2.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨p.2.2.2.2.2.2.1, p.2.2.1.2, p.2.2.2.1.2⟩⟩,
    p.2.2.2.2.1.mul_right p.2.2.2.2.2.1,
    mul_ne_zero (expansion_primary_ne_zero c p.2.2.1.1) p.2.2.2.2.2.2.2.1⟩

theorem expansionRecombine_gcd (c : ArithmeticContext) (p : ExpansionSplit c) :
    gcd (expansionRecombine c p).1.2.1 (principal (expansionRecombine c p).1.2.2) =
      p.1.2.1 := by
  change gcd (p.1.2.1 * p.1.2.2.1) (principal (primaryGenerator p.1.2.1 * p.1.2.2.2)) = _
  rw [expansion_principal_mul, expansion_primary_spec c p.2.2.1.1,
    gcd_mul_left, normalize_eq]
  have hg : gcd p.1.2.2.1 (principal p.1.2.2.2) = 1 :=
    (gcd_isUnit_iff_isRelPrime.mpr p.2.2.2.2.2.2.2.2).eq_one
  rw [hg, mul_one]

theorem expansionRecombine_injective (c : ArithmeticContext) :
    Function.Injective (expansionRecombine c) := by
  intro p q hpq
  have hb : p.1.1 = q.1.1 := congrArg (fun x : ExpansionOutput c => x.1.1) hpq
  have he : p.1.2.1 = q.1.2.1 := by
    rw [← expansionRecombine_gcd c p, ← expansionRecombine_gcd c q, hpq]
  have hf : p.1.2.1 * p.1.2.2.1 = q.1.2.1 * q.1.2.2.1 :=
    congrArg (fun x : ExpansionOutput c => x.1.2.1) hpq
  have hk : primaryGenerator p.1.2.1 * p.1.2.2.2 =
      primaryGenerator q.1.2.1 * q.1.2.2.2 :=
    congrArg (fun x : ExpansionOutput c => x.1.2.2) hpq
  have hv : p.1.2.2.1 = q.1.2.2.1 := by
    apply mul_left_cancel₀ p.2.2.1.1.1
    simpa only [he] using hf
  have hh : p.1.2.2.2 = q.1.2.2.2 := by
    apply mul_left_cancel₀ (expansion_primary_ne_zero c p.2.2.1.1)
    simpa only [he] using hk
  exact Subtype.ext (Prod.ext hb (Prod.ext he (Prod.ext hv hh)))

theorem expansionRecombine_surjective (c : ArithmeticContext) :
    Function.Surjective (expansionRecombine c) := by
  intro p
  let e := gcd p.1.2.1 (principal p.1.2.2)
  obtain ⟨v, q, hv, hq, hvq⟩ := extract_gcd p.1.2.1 (principal p.1.2.2)
  have hediv : e ∣ p.1.2.1 := gcd_dvd_left _ _
  have hek : e ∣ principal p.1.2.2 := gcd_dvd_right _ _
  have he : SquarefreeOutside c.S e :=
    ⟨expansion_outside_of_dvd c p.2.2.1.1 hediv, p.2.2.1.2.squarefree_of_dvd hediv⟩
  have hvdiv : v ∣ p.1.2.1 := ⟨e, hv.trans (mul_comm _ _)⟩
  have hvS : SquarefreeOutside c.S v :=
    ⟨expansion_outside_of_dvd c p.2.2.1.1 hvdiv, p.2.2.1.2.squarefree_of_dvd hvdiv⟩
  have hgen : primaryGenerator e ∣ p.1.2.2 := by
    apply Ideal.mem_span_singleton.mp
    change p.1.2.2 ∈ principal (primaryGenerator e)
    rw [expansion_primary_spec c he.1]
    exact Ideal.dvd_span_singleton.mp hek
  obtain ⟨h, hh⟩ := hgen
  have h0 : h ≠ 0 := by
    intro hz
    exact p.2.2.2.2 (by rw [hh, hz, mul_zero])
  have hprincipal : principal h = q := by
    apply mul_left_cancel₀ he.1.1
    calc
      e * principal h = principal p.1.2.2 := by
        rw [hh, expansion_principal_mul, expansion_primary_spec c he.1]
      _ = e * q := hq
  have hev : IsRelPrime e v := IsRelPrime.of_squarefree_mul (hv ▸ p.2.2.1.2)
  have hbe : IsRelPrime p.1.1 e := p.2.2.2.1.of_dvd_right hediv
  have hbv : IsRelPrime p.1.1 v := p.2.2.2.1.of_dvd_right hvdiv
  have hvh : IsRelPrime v (principal h) := by
    rw [hprincipal]
    exact gcd_isUnit_iff_isRelPrime.mp hvq
  refine ⟨⟨(p.1.1, e, v, h), p.2.1, he, hvS, hbe, hbv, hev, h0, hvh⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext rfl (Prod.ext hv.symm hh.symm)

def expansionSplitEquiv (c : ArithmeticContext) : ExpansionSplit c ≃ ExpansionOutput c :=
  Equiv.ofBijective (expansionRecombine c)
    ⟨expansionRecombine_injective c, expansionRecombine_surjective c⟩

def expansionQuotient (g e : Ideal O) : Ideal O :=
  if h : e ∣ g then Classical.choose h else 1

theorem expansionQuotient_spec {g e : Ideal O} (h : e ∣ g) :
    e * expansionQuotient g e = g := by
  unfold expansionQuotient
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).symm

theorem expansionQuotient_unique {g e b : Ideal O} (he : e ≠ ⊥)
    (h : e * b = g) : expansionQuotient g e = b := by
  apply mul_left_cancel₀ he
  exact (expansionQuotient_spec ⟨b, h.symm⟩).trans h.symm

/-- Exactly the (g,e,v,h) arithmetic domain before the manuscript substitution. -/
def ExpansionRawAdmissible (c : ArithmeticContext)
    (p : Ideal O × Ideal O × Ideal O × O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2.2.1 ∧
    IsRelPrime p.1 p.2.2.1 ∧ p.2.1 ∣ p.1 ∧
    p.2.2.2 ≠ 0 ∧ IsRelPrime p.2.2.1 (principal p.2.2.2)

abbrev ExpansionRaw (c : ArithmeticContext) :=
  {p : Ideal O × Ideal O × Ideal O × O // ExpansionRawAdmissible c p}

def expansionToSplit (c : ArithmeticContext) (p : ExpansionRaw c) : ExpansionSplit c := by
  let b := expansionQuotient p.1.1 p.1.2.1
  have hediv : p.1.2.1 ∣ p.1.1 := p.2.2.2.2.1
  have hspec : p.1.2.1 * b = p.1.1 := expansionQuotient_spec hediv
  have hbdiv : b ∣ p.1.1 := ⟨p.1.2.1, hspec.symm.trans (mul_comm _ _)⟩
  have he : SquarefreeOutside c.S p.1.2.1 :=
    ⟨expansion_outside_of_dvd c p.2.1.1 hediv, p.2.1.2.squarefree_of_dvd hediv⟩
  have hb : SquarefreeOutside c.S b :=
    ⟨expansion_outside_of_dvd c p.2.1.1 hbdiv, p.2.1.2.squarefree_of_dvd hbdiv⟩
  have heb : IsRelPrime p.1.2.1 b :=
    IsRelPrime.of_squarefree_mul (hspec.symm ▸ p.2.1.2)
  exact ⟨(b, p.1.2.1, p.1.2.2.1, p.1.2.2.2), hb, he, p.2.2.1, heb.symm,
    p.2.2.2.1.of_dvd_left hbdiv, p.2.2.2.1.of_dvd_left hediv,
    p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩

def expansionFromSplit (c : ArithmeticContext) (p : ExpansionSplit c) : ExpansionRaw c :=
  ⟨(p.1.1 * p.1.2.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2),
    ⟨(expansion_outside_mul c _ _).mpr ⟨p.2.1.1, p.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨p.2.2.2.2.1, p.2.1.2, p.2.2.1.2⟩⟩,
    p.2.2.2.1, p.2.2.2.2.2.1.mul_left p.2.2.2.2.2.2.1,
    ⟨p.1.1, mul_comm _ _⟩, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩

theorem expansionFromSplit_toSplit (c : ArithmeticContext) (p : ExpansionRaw c) :
    expansionFromSplit c (expansionToSplit c p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change expansionQuotient p.1.1 p.1.2.1 * p.1.2.1 = p.1.1
    rw [mul_comm]
    exact expansionQuotient_spec p.2.2.2.2.1
  · rfl

theorem expansionToSplit_fromSplit (c : ArithmeticContext) (p : ExpansionSplit c) :
    expansionToSplit c (expansionFromSplit c p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change expansionQuotient (p.1.1 * p.1.2.1) p.1.2.1 = p.1.1
    exact expansionQuotient_unique p.2.2.1.1.1 (mul_comm _ _)
  · rfl

def expansionRawSplitEquiv (c : ArithmeticContext) : ExpansionRaw c ≃ ExpansionSplit c where
  toFun := expansionToSplit c
  invFun := expansionFromSplit c
  left_inv := expansionFromSplit_toSplit c
  right_inv := expansionToSplit_fromSplit c

/-- Genuine reindexing (g,e,v,h) ↔ (b,f,k), including element frequencies. -/
def expansionRawEquiv (c : ArithmeticContext) : ExpansionRaw c ≃ ExpansionOutput c :=
  (expansionRawSplitEquiv c).trans (expansionSplitEquiv c)

theorem expansionRawEquiv_apply (c : ArithmeticContext) (p : ExpansionRaw c) :
    (expansionRawEquiv c p).1 =
      (expansionQuotient p.1.1 p.1.2.1, p.1.2.1 * p.1.2.2.1,
        primaryGenerator p.1.2.1 * p.1.2.2.2) := rfl

theorem expansionRawEquiv_inverse_gcd (c : ArithmeticContext) (p : ExpansionOutput c) :
    ((expansionRawEquiv c).symm p).1.2.1 = gcd p.1.2.1 (principal p.1.2.2) := by
  have h := expansionRecombine_gcd c
    (expansionToSplit c ((expansionRawEquiv c).symm p))
  change gcd (expansionRawEquiv c ((expansionRawEquiv c).symm p)).1.2.1
    (principal (expansionRawEquiv c ((expansionRawEquiv c).symm p)).1.2.2) =
      ((expansionRawEquiv c).symm p).1.2.1 at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem expansionRawEquiv_summable_iff (c : ArithmeticContext)
    (F : ExpansionOutput c → ℂ) :
    Summable (fun p => F (expansionRawEquiv c p)) ↔ Summable F :=
  (expansionRawEquiv c).summable_iff

theorem expansionRawEquiv_tsum (c : ArithmeticContext)
    (F : ExpansionOutput c → ℂ) (hF : Summable F) :
    (∑' p : ExpansionRaw c, F (expansionRawEquiv c p)) = ∑' q : ExpansionOutput c, F q :=
  (expansionRawEquiv c).tsum_eq F

open PoissonReductionProof

def ExpansionBlockRow (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (D H B F : ℝ) (p : Ideal O × Ideal O × O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ B ≤ normIdeal p.1 ∧ normIdeal p.1 < 2 * B ∧
    SquarefreeOutside c.S p.2.1 ∧ F ≤ normIdeal p.2.1 ∧ normIdeal p.2.1 < 2 * F ∧
    IsRelPrime p.1 p.2.1 ∧ 0 < normElement p.2.2 ∧
    normElement p.2.2 ≤ initialHeight I Φ D H B

theorem expansion_block_rows_finite (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (D H B F : ℝ) :
    {p : Ideal O × Ideal O × O | ExpansionBlockRow c I Φ D H B F p}.Finite := by
  apply ((finite_normIdeal_le (2 * B)).prod
    ((finite_normIdeal_le (2 * F)).prod
      (finite_normElement_le (initialHeight I Φ D H B)))).subset
  intro p hp
  exact ⟨hp.2.2.1.le, hp.2.2.2.2.2.1.le, hp.2.2.2.2.2.2.2.2⟩

def expansionBlockJoint (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (D H B F : ℝ)
    (p : (Ideal O × Ideal O × O) × (Ideal O × Ideal O)) : ℂ :=
  if ExpansionBlockRow c I Φ D H B F p.1 then
    (normIdeal p.1.1 : ℂ) * (mobius p.1.2.1 : ℂ) *
      initialPairedTerm c ξ Φ W D H B F p.1.1 p.1.2.1 p.1.2.2 p.2
  else 0

theorem expansion_block_joint_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    Function.HasFiniteSupport (expansionBlockJoint c ξ I Φ W D H B F) := by
  have hpair (p : Ideal O × Ideal O × O)
      (hp : ExpansionBlockRow c I Φ D H B F p) :
      (Function.support (initialPairedTerm c ξ Φ W D H B F p.1 p.2.1 p.2.2)).Finite :=
    initial_pair_finiteSupport c I Φ ξ W D H B F p.1 p.2.1 p.2.2 hW hD hB hF
      hp.1.1.1 hp.2.2.2.1.1.1
  apply ((expansion_block_rows_finite c I Φ D H B F).biUnion
    (fun p hp => (hpair p hp).image (fun n : Ideal O × Ideal O => (p, n)))).subset
  intro p hp
  have hr : ExpansionBlockRow c I Φ D H B F p.1 := by
    by_contra h
    exact hp (by simp only [expansionBlockJoint, ite_eq_right h])
  have hn : initialPairedTerm c ξ Φ W D H B F p.1.1 p.1.2.1 p.1.2.2 p.2 ≠ 0 := by
    intro h
    exact hp (by simp only [expansionBlockJoint, ite_eq_left hr, h, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨p.1, hr, ⟨p.2, hn, rfl⟩⟩

theorem expansion_block_joint_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    Summable (expansionBlockJoint c ξ I Φ W D H B F) :=
  summable_of_hasFiniteSupport
    (expansion_block_joint_hasFiniteSupport c ξ I Φ hW hD hB hF H)

theorem expansion_pairedTerm_scale_invariant (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ)
    {D B F : ℝ} (hD : D ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (H : ℝ) (b f : Ideal O) (k : O) (n : Ideal O × Ideal O) :
    initialPairedTerm c ξ Φ W D H B F b f k n =
      initialAtom c ξ b f k n.1 * star (initialAtom c ξ b f k n.2) *
        (initialWeight W (normIdeal b * normIdeal f * normIdeal n.1 / D) *
          star (initialWeight W (normIdeal b * normIdeal f * normIdeal n.2 / D)) *
          radialFourier (fun t => (Φ.value t : ℂ))
            (H * normElement k / (normIdeal f ^ 2 * normIdeal n.1 * normIdeal n.2))) := by
  have harg (t : ℝ) : normIdeal b * normIdeal f / (B * F) * (t / (D / (B * F))) =
      normIdeal b * normIdeal f * t / D := by
    field_simp
  have hfourier : (H * normElement k / (normIdeal f ^ 2 * (D / (B * F)) ^ 2)) /
      ((normIdeal n.1 / (D / (B * F))) * (normIdeal n.2 / (D / (B * F)))) =
        H * normElement k / (normIdeal f ^ 2 * normIdeal n.1 * normIdeal n.2) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
    field_simp
  simp only [initialPairedTerm, initialKernel, Matrix.cons_val_zero,
    Matrix.cons_val_one, harg, hfourier]

theorem expansion_primary_isPrimary (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : IsPrimary (primaryGenerator a) := by
  by_cases h : ∃ z : O, principal z = a ∧ IsPrimary z
  · simpa only [primaryGenerator, dite_eq_left h] using (Classical.choose_spec h).2
  · exact False.elim (expansion_primary_ne_zero c ha
      (by simp only [primaryGenerator, dite_eq_right h]))

theorem expansion_isPrimary_mul {a b : O} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  apply (isPrimary_iff_three_dvd _).mpr
  have h := dvd_add (dvd_mul_of_dvd_left ((isPrimary_iff_three_dvd a).mp ha) b)
    ((isPrimary_iff_three_dvd b).mp hb)
  convert h using 1 <;> ring

theorem expansion_isPrimary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) : u = 1 := by
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

theorem expansion_primary_unique {a b : O} (ha : IsPrimary a) (hb : IsPrimary b)
    (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [expansion_isPrimary_unit_eq_one u hup, Units.val_one, mul_one] using hu

theorem expansion_primary_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    primaryGenerator (a * b) = primaryGenerator a * primaryGenerator b := by
  have hab := (expansion_outside_mul c a b).mpr ⟨ha, hb⟩
  apply expansion_primary_unique (expansion_primary_isPrimary c hab)
    (expansion_isPrimary_mul (expansion_primary_isPrimary c ha) (expansion_primary_isPrimary c hb))
  rw [expansion_primary_spec c hab, expansion_principal_mul,
    expansion_primary_spec c ha, expansion_primary_spec c hb]

theorem expansion_normIdeal_mul (a b : Ideal O) :
    normIdeal (a * b) = normIdeal a * normIdeal b := by
  simp only [normIdeal, map_mul, Nat.cast_mul]

theorem expansion_normElement_mul (a b : O) :
    normElement (a * b) = normElement a * normElement b := by
  simp only [normElement, expansion_principal_mul, expansion_normIdeal_mul]

theorem expansionRawEquiv_norm_frequency (c : ArithmeticContext) (p : ExpansionRaw c) :
    normElement (expansionRawEquiv c p).1.2.2 = normIdeal p.1.2.1 * normElement p.1.2.2.2 := by
  change normElement (primaryGenerator p.1.2.1 * p.1.2.2.2) = _
  rw [expansion_normElement_mul]
  change normIdeal (principal (primaryGenerator p.1.2.1)) * _ = _
  rw [expansion_primary_spec c (expansion_outside_of_dvd c p.2.1.1 p.2.2.2.2.1)]

theorem expansionRawEquiv_product (c : ArithmeticContext) (p : ExpansionRaw c) :
    p.1.1 * p.1.2.2.1 = (expansionRawEquiv c p).1.1 * (expansionRawEquiv c p).1.2.1 := by
  change p.1.1 * p.1.2.2.1 = expansionQuotient p.1.1 p.1.2.1 * (p.1.2.1 * p.1.2.2.1)
  calc
    _ = (p.1.2.1 * expansionQuotient p.1.1 p.1.2.1) * p.1.2.2.1 :=
      congrArg (fun a : Ideal O => a * p.1.2.2.1) (expansionQuotient_spec p.2.2.2.2.1).symm
    _ = _ := by ac_rfl

theorem expansionRawEquiv_mobius (c : ArithmeticContext) (p : ExpansionRaw c) :
    mobius p.1.2.1 * mobius p.1.2.2.1 = mobius (expansionRawEquiv c p).1.2.1 := by
  change mobius p.1.2.1 * mobius p.1.2.2.1 = mobius (p.1.2.1 * p.1.2.2.1)
  exact (p.2.2.2.1.of_dvd_left p.2.2.2.2.1).moebius_mul.symm

theorem expansionRawEquiv_twist (c : ArithmeticContext) (p : ExpansionRaw c) :
    p.1.2.2.2 * primaryGenerator p.1.2.1 ^ 5 * primaryGenerator p.1.2.2.1 ^ 4 =
      (expansionRawEquiv c p).1.2.2 * primaryGenerator (expansionRawEquiv c p).1.2.1 ^ 4 := by
  change p.1.2.2.2 * primaryGenerator p.1.2.1 ^ 5 * primaryGenerator p.1.2.2.1 ^ 4 =
    (primaryGenerator p.1.2.1 * p.1.2.2.2) * primaryGenerator (p.1.2.1 * p.1.2.2.1) ^ 4
  rw [expansion_primary_mul c (expansion_outside_of_dvd c p.2.1.1 p.2.2.2.2.1) p.2.2.1.1]
  ring

theorem expansion_initialDyadicBlock_eq_joint (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    initialDyadicBlock c ξ I Φ W D H B F =
      (H / D ^ 2 : ℝ) * ∑' p, expansionBlockJoint c ξ I Φ W D H B F p := by
  have hs := expansion_block_joint_summable c ξ I Φ hW hD hB hF H
  have hflat : (∑' p, expansionBlockJoint c ξ I Φ W D H B F p) =
      ∑' b : Ideal O, ∑' f : Ideal O, ∑' k : O,
        ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
          expansionBlockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) := by
    rw [hs.tsum_prod, hs.prod.tsum_prod]
    apply tsum_congr
    intro b
    rw [(hs.prod.prod_factor b).tsum_prod]
    apply tsum_congr
    intro f
    apply tsum_congr
    intro k
    exact (hs.prod_factor (b, f, k)).tsum_prod
  rw [initialDyadicBlock, hflat]
  congr 1
  apply tsum_congr
  intro b
  by_cases hb : SquarefreeOutside c.S b ∧ B ≤ normIdeal b ∧ normIdeal b < 2 * B
  · rw [ite_eq_left hb, ← tsum_mul_left]
    apply tsum_congr
    intro f
    by_cases hf : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧
        normIdeal f < 2 * F ∧ IsRelPrime b f
    · rw [ite_eq_left hf]
      simp only [← tsum_mul_left]
      apply tsum_congr
      intro k
      by_cases hk : 0 < normElement k ∧ normElement k ≤ initialHeight I Φ D H B
      · rw [ite_eq_left hk]
        simp only [← tsum_mul_left]
        apply tsum_congr
        intro n₁
        apply tsum_congr
        intro n₂
        have hr : ExpansionBlockRow c I Φ D H B F (b, f, k) :=
          ⟨hb.1, hb.2.1, hb.2.2, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hk.1, hk.2⟩
        simp only [expansionBlockJoint, ite_eq_left hr]
        ring
      · have hz (n₁ n₂ : Ideal O) :
            expansionBlockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) = 0 := by
          apply ite_eq_right
          intro hr
          exact hk ⟨hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2⟩
        simp only [ite_eq_right hk, mul_zero, hz, tsum_zero]
    · have hz (k : O) (n₁ n₂ : Ideal O) :
          expansionBlockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) = 0 := by
        apply ite_eq_right
        intro hr
        exact hf ⟨hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩
      simp only [ite_eq_right hf, mul_zero, hz, tsum_zero]
  · have hz (f : Ideal O) (k : O) (n₁ n₂ : Ideal O) :
        expansionBlockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) = 0 := by
      apply ite_eq_right
      intro hr
      exact hb ⟨hr.1, hr.2.1, hr.2.2.1⟩
    simp only [ite_eq_right hb, hz, tsum_zero]

theorem expansion_block_support_output (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (D H B F : ℝ) :
    Function.support (fun r : Ideal O × Ideal O × O =>
      ∑' n : Ideal O × Ideal O, expansionBlockJoint c ξ I Φ W D H B F (r, n)) ⊆
      {r | ExpansionOutputAdmissible c r} := by
  intro r hr
  by_contra hout
  have hnot : ¬ ExpansionBlockRow c I Φ D H B F r := by
    intro h
    apply hout
    refine ⟨h.1, h.2.2.2.1, h.2.2.2.2.2.2.1, ?_⟩
    intro hk
    have hn := h.2.2.2.2.2.2.2.1
    simpa only [hk, normElement, principal, Ideal.span_singleton_zero,
      normIdeal, Ideal.absNorm_bot, Nat.cast_zero, lt_self_iff_false] using hn
  exact hr (by simp only [expansionBlockJoint, ite_eq_right hnot, tsum_zero])

theorem expansion_raw_block_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    Function.HasFiniteSupport (fun p : ExpansionRaw c × (Ideal O × Ideal O) =>
      expansionBlockJoint c ξ I Φ W D H B F ((expansionRawEquiv c p.1).1, p.2)) := by
  let map : ExpansionRaw c × (Ideal O × Ideal O) →
      (Ideal O × Ideal O × O) × (Ideal O × Ideal O) :=
    fun p => ((expansionRawEquiv c p.1).1, p.2)
  have hinj : Function.Injective map := by
    intro p q h
    apply Prod.ext
    · apply (expansionRawEquiv c).injective
      exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun x : (Ideal O × Ideal O × O) × (Ideal O × Ideal O) => x.2) h
  exact (expansion_block_joint_hasFiniteSupport c ξ I Φ hW hD hB hF H).preimage hinj.injOn

/-- The literal bounded block is reindexed by the arithmetic variables before
this regrouping. All the displayed series have finite joint support. -/
theorem expansion_initialDyadicBlock_eq_raw (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    initialDyadicBlock c ξ I Φ W D H B F =
      (H / D ^ 2 : ℝ) * ∑' p : ExpansionRaw c,
        ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
          expansionBlockJoint c ξ I Φ W D H B F
            ((expansionRawEquiv c p).1, (n₁, n₂)) := by
  rw [expansion_initialDyadicBlock_eq_joint c ξ I Φ hW hD hB hF H]
  congr 1
  have hs := expansion_block_joint_summable c ξ I Φ hW hD hB hF H
  rw [hs.tsum_prod, ← tsum_subtype_eq_of_support_subset
    (expansion_block_support_output c ξ I Φ W D H B F)]
  change (∑' x : ExpansionOutput c, ∑' n : Ideal O × Ideal O,
    expansionBlockJoint c ξ I Φ W D H B F (x.1, n)) = _
  rw [← (expansionRawEquiv c).tsum_eq (fun x : ExpansionOutput c =>
    ∑' n : Ideal O × Ideal O, expansionBlockJoint c ξ I Φ W D H B F (x.1, n))]
  apply tsum_congr
  intro p
  exact (hs.prod_factor ((expansionRawEquiv c p).1)).tsum_prod

theorem expansionRawEquiv_norm_weight (c : ArithmeticContext) (p : ExpansionRaw c) :
    normIdeal p.1.1 / normIdeal p.1.2.1 = normIdeal (expansionRawEquiv c p).1.1 := by
  have he : p.1.2.1 ≠ ⊥ := ne_zero_of_dvd_ne_zero p.2.1.1.1 p.2.2.2.2.1
  have hNe : normIdeal p.1.2.1 ≠ 0 := ne_of_gt
    (zero_lt_one.trans_le (PoissonReductionProof.normIdeal_one_le he))
  change normIdeal p.1.1 / normIdeal p.1.2.1 = normIdeal (expansionQuotient p.1.1 p.1.2.1)
  have hN := congrArg normIdeal (expansionQuotient_spec p.2.2.2.2.1)
  rw [expansion_normIdeal_mul] at hN
  rw [← hN]
  field_simp

theorem expansionRawEquiv_fourier_parameter (c : ArithmeticContext) (p : ExpansionRaw c)
    (H x y : ℝ) :
    H * normElement (expansionRawEquiv c p).1.2.2 /
        (normIdeal (expansionRawEquiv c p).1.2.1 ^ 2 * x * y) =
      H * normElement p.1.2.2.2 / (normIdeal p.1.2.1 * normIdeal p.1.2.2.1 ^ 2 * x * y) := by
  have he : p.1.2.1 ≠ ⊥ := ne_zero_of_dvd_ne_zero p.2.1.1.1 p.2.2.2.2.1
  have hNe : normIdeal p.1.2.1 ≠ 0 := ne_of_gt
    (zero_lt_one.trans_le (PoissonReductionProof.normIdeal_one_le he))
  rw [expansionRawEquiv_norm_frequency]
  change H * (normIdeal p.1.2.1 * normElement p.1.2.2.2) /
    (normIdeal (p.1.2.1 * p.1.2.2.1) ^ 2 * x * y) = _
  rw [expansion_normIdeal_mul]
  field_simp

theorem expansion_dyadic_unique {x : ℝ} {j l : ℕ}
    (hj : (2 : ℝ) ^ j ≤ x ∧ x < 2 * (2 : ℝ) ^ j)
    (hl : (2 : ℝ) ^ l ≤ x ∧ x < 2 * (2 : ℝ) ^ l) : j = l := by
  have not_lt {a b : ℕ}
      (ha : (2 : ℝ) ^ a ≤ x ∧ x < 2 * (2 : ℝ) ^ a)
      (hb : (2 : ℝ) ^ b ≤ x ∧ x < 2 * (2 : ℝ) ^ b) : ¬ a < b := by
    intro h
    have hp : (2 : ℝ) ^ (a + 1) ≤ (2 : ℝ) ^ b :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_iff.mpr h)
    rw [pow_succ, mul_comm] at hp
    exact (not_lt_of_ge hb.1) (ha.2.trans_le hp)
  exact le_antisymm (Nat.le_of_not_gt (not_lt hl hj)) (Nat.le_of_not_gt (not_lt hj hl))

theorem expansion_initialDepth_covers (I : SupportInterval) (D x : ℝ)
    (hx : 1 ≤ x) (hbound : x ≤ I.hi * D) :
    ∃! j : ℕ, j ∈ Finset.range (initialDepth I D) ∧
      (2 : ℝ) ^ j ≤ x ∧ x < 2 * (2 : ℝ) ^ j := by
  obtain ⟨j, hj, hjupper⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjlog : (j : ℝ) ≤ Real.log (max 1 (I.hi * D)) / Real.log 2 := by
    apply (le_div_iff₀ hlog).mpr
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (hj.trans (hbound.trans (le_max_right _ _)))
  have hjceil : j ≤ ⌈Real.log (max 1 (I.hi * D)) / Real.log 2⌉₊ :=
    (Nat.cast_le (α := ℝ)).mp (hjlog.trans (Nat.le_ceil _))
  have hjrange : j ∈ Finset.range (initialDepth I D) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hjceil)
  have hjup : x < 2 * (2 : ℝ) ^ j := by simpa only [pow_succ, mul_comm] using hjupper
  refine ⟨j, ⟨hjrange, hj, hjup⟩, ?_⟩
  intro l hl
  exact expansion_dyadic_unique hl.2 ⟨hj, hjup⟩

theorem expansion_initialKernel_parameter (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (x : BoxSpace 2) (hx : initialKernel Φ W r a x ≠ 0) :
    a * r ^ 2 ≤ Φ.fourierCap * I.hi ^ 2 := by
  have hW0 : W (r * x 0) ≠ 0 := by
    intro h
    exact hx (by simp only [initialKernel, initialWeight, h, star_zero, mul_zero, zero_mul])
  have hW1 : W (r * x 1) ≠ 0 := by
    intro h
    exact hx (by simp only [initialKernel, initialWeight, h, star_zero, mul_zero, zero_mul])
  have h0 := hW.2 hW0
  have h1 := hW.2 hW1
  have hx0 : 0 < x 0 := (mul_pos_iff_of_pos_left hr).mp (I.lo_pos.trans_le h0.1)
  have hx1 : 0 < x 1 := (mul_pos_iff_of_pos_left hr).mp (I.lo_pos.trans_le h1.1)
  have hF : radialFourier (fun t => (Φ.value t : ℂ)) (a / (x 0 * x 1)) ≠ 0 := by
    intro h
    exact hx (by simp only [initialKernel, h, mul_zero])
  have hcap := (Φ.fourier_support ⟨hF, div_nonneg ha (mul_pos hx0 hx1).le⟩).2
  have hparam : a ≤ Φ.fourierCap * (x 0 * x 1) :=
    (div_le_iff₀ (mul_pos hx0 hx1)).mp hcap
  have hprod : (r * x 0) * (r * x 1) ≤ I.hi ^ 2 := by
    calc
      _ ≤ I.hi * I.hi := mul_le_mul h0.2 h1.2 (mul_pos hr hx1).le
        (I.lo_pos.le.trans I.ordered)
      _ = _ := (pow_two _).symm
  calc
    a * r ^ 2 ≤ (Φ.fourierCap * (x 0 * x 1)) * r ^ 2 :=
      mul_le_mul_of_nonneg_right hparam (sq_nonneg r)
    _ = Φ.fourierCap * ((r * x 0) * (r * x 1)) := by ring
    _ ≤ Φ.fourierCap * I.hi ^ 2 := mul_le_mul_of_nonneg_left hprod Φ.cap_pos.le

theorem expansion_pairedTerm_frequency_bound (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D H B F : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hB : 0 < B) (hF : 0 < F)
    (b f : Ideal O) (hb : b ≠ ⊥) (hf : f ≠ ⊥) (k : O)
    (n : Ideal O × Ideal O) (hn : initialPairedTerm c ξ Φ W D H B F b f k n ≠ 0) :
    normElement k ≤ Φ.fourierCap * I.hi ^ 2 * D ^ 2 / (H * normIdeal b ^ 2) := by
  have hNb : 0 < normIdeal b := zero_lt_one.trans_le (normIdeal_one_le hb)
  have hNf : 0 < normIdeal f := zero_lt_one.trans_le (normIdeal_one_le hf)
  have hX : 0 < D / (B * F) := div_pos hD (mul_pos hB hF)
  have hr : 0 < normIdeal b * normIdeal f / (B * F) :=
    div_pos (mul_pos hNb hNf) (mul_pos hB hF)
  have ha : 0 ≤ H * normElement k / (normIdeal f ^ 2 * (D / (B * F)) ^ 2) := by
    apply div_nonneg
    · exact mul_nonneg hH.le (Nat.cast_nonneg _)
    · positivity
  have hk : initialKernel Φ W (normIdeal b * normIdeal f / (B * F))
      (H * normElement k / (normIdeal f ^ 2 * (D / (B * F)) ^ 2))
      ![normIdeal n.1 / (D / (B * F)), normIdeal n.2 / (D / (B * F))] ≠ 0 :=
    (mul_ne_zero_iff.mp hn).2
  have hp := expansion_initialKernel_parameter I Φ hW hr ha _ hk
  have heq : (H * normElement k / (normIdeal f ^ 2 * (D / (B * F)) ^ 2)) *
      (normIdeal b * normIdeal f / (B * F)) ^ 2 = H * normElement k * normIdeal b ^ 2 / D ^ 2 := by
    field_simp
  rw [heq] at hp
  apply (le_div_iff₀ (mul_pos hH (sq_pos_of_pos hNb))).mpr
  have h := (div_le_iff₀ (sq_pos_of_pos hD)).mp hp
  nlinarith only [h]

theorem expansion_pairedTerm_height_bound (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D H B F : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hB : 0 < B) (hF : 0 < F)
    (b f : Ideal O) (hb : b ≠ ⊥) (hf : f ≠ ⊥) (hBN : B ≤ normIdeal b) (k : O)
    (n : Ideal O × Ideal O) (hn : initialPairedTerm c ξ Φ W D H B F b f k n ≠ 0) :
    normElement k ≤ initialHeight I Φ D H B := by
  have hNb : 0 < normIdeal b := zero_lt_one.trans_le (normIdeal_one_le hb)
  have hparam := expansion_pairedTerm_frequency_bound c ξ I Φ hW hD hH hB hF b f hb hf k n hn
  apply hparam.trans
  calc
    Φ.fourierCap * I.hi ^ 2 * D ^ 2 / (H * normIdeal b ^ 2) ≤
        Φ.fourierCap * I.hi ^ 2 * D ^ 2 / (H * B ^ 2) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg Φ.cap_pos.le (sq_nonneg I.hi)) (sq_nonneg D))
        (mul_pos hH (sq_pos_of_pos hB))
      apply mul_le_mul_of_nonneg_left _ hH.le
      exact pow_le_pow_left₀ hB.le hBN 2
    _ ≤ initialHeight I Φ D H B := by
      apply div_le_div_of_nonneg_right _ (mul_pos hH (sq_pos_of_pos hB)).le
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg D)

theorem expansion_pairedTerm_norm_product_bound (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : B ≠ 0) (hF : F ≠ 0) (H : ℝ)
    (b f : Ideal O) (k : O) (n : Ideal O × Ideal O)
    (hn : initialPairedTerm c ξ Φ W D H B F b f k n ≠ 0) :
    normIdeal b * normIdeal f ≤ I.hi * D := by
  have hatom : initialAtom c ξ b f k n.1 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  have hnS : SquarefreeOutside c.S n.1 ∧ IsRelPrime n.1 b := by
    by_contra h
    exact hatom (by simp only [initialAtom, ite_eq_right h])
  have hnorm := normIdeal_one_le hnS.1.1.1
  have hw : W (normIdeal b * normIdeal f * normIdeal n.1 / D) ≠ 0 := by
    intro hz
    apply hn
    rw [expansion_pairedTerm_scale_invariant c ξ Φ W hD.ne' hB hF]
    simp only [initialWeight, hz, star_zero, mul_zero, zero_mul]
  have hb := (div_le_iff₀ hD).mp (hW.2 hw).2
  exact (le_mul_of_one_le_right
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hnorm).trans hb

theorem expansion_pairedTerm_dyadic_cover (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : B ≠ 0) (hF : F ≠ 0) (H : ℝ)
    (b f : Ideal O) (hb : b ≠ ⊥) (hf : f ≠ ⊥) (k : O) (n : Ideal O × Ideal O)
    (hn : initialPairedTerm c ξ Φ W D H B F b f k n ≠ 0) :
    (∃! j : ℕ, j ∈ Finset.range (initialDepth I D) ∧
      (2 : ℝ) ^ j ≤ normIdeal b ∧ normIdeal b < 2 * (2 : ℝ) ^ j) ∧
    (∃! l : ℕ, l ∈ Finset.range (initialDepth I D) ∧
      (2 : ℝ) ^ l ≤ normIdeal f ∧ normIdeal f < 2 * (2 : ℝ) ^ l) := by
  have hprod := expansion_pairedTerm_norm_product_bound c ξ I Φ hW hD hB hF H b f k n hn
  have hb1 := normIdeal_one_le hb
  have hf1 := normIdeal_one_le hf
  exact ⟨expansion_initialDepth_covers I D _ hb1
      ((le_mul_of_one_le_right (zero_le_one.trans hb1) hf1).trans hprod),
    expansion_initialDepth_covers I D _ hf1
      ((le_mul_of_one_le_left (zero_le_one.trans hf1) hb1).trans hprod)⟩


instance expansion_rayClassFinite (c : ArithmeticContext) : Finite (RayClass c) := by
  let : Finite (O ⧸ c.rayModulus) :=
    Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  infer_instance

instance expansion_rayClassFintype (c : ArithmeticContext) : Fintype (RayClass c) :=
  Fintype.ofFinite _

abbrev expansion_RayFourierIndex (c : ArithmeticContext) := AddChar (Additive (RayClass c)) ℂ

instance expansion_rayFourierIndexFintype (c : ArithmeticContext) : Fintype (expansion_RayFourierIndex c) := by
  letI : Fintype (RayClass c) := expansion_rayClassFintype c
  exact AddChar.instFintype (Additive (RayClass c)) ℂ

/-- A character of the additive type tag is a multiplicative group character. -/
def expansion_characterHom {G : Type*} [CommGroup G] (ψ : AddChar (Additive G) ℂ) : G →* ℂ where
  toFun x := ψ (Additive.ofMul x)
  map_one' := ψ.map_zero_eq_one
  map_mul' x y := ψ.map_add_eq_mul (Additive.ofMul x) (Additive.ofMul y)

/-- Descend a character from residue units modulo global units and extend it
by zero at nonunits, exactly as in the frozen Hecke-character definition. -/
def expansion_rayCharacterFromHom (c : ArithmeticContext) (f : RayClass c →* ℂ) :
    RayCharacter c :=
  ⟨{ modulus := c.rayModulus
     modulus_ne_bot := c.rayModulus_ne_bot
     residue := MulChar.ofUnitHom
       (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c)))
     unit_trivial := by
       intro u
       let v : (O ⧸ c.rayModulus)ˣ :=
         Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u
       have hv : (QuotientGroup.mk' (globalUnitImage c)) v = 1 :=
         (QuotientGroup.eq_one_iff v).mpr ⟨u, rfl⟩
       change MulChar.ofUnitHom
         (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c)))
         (v : O ⧸ c.rayModulus) = 1
       rw [MulChar.ofUnitHom_coe]
       simp only [MonoidHom.comp_apply, hv, map_one, Units.val_one] }, rfl⟩

theorem expansion_rayCharacterFromHom_onElement (c : ArithmeticContext)
    (f : RayClass c →* ℂ) {x : O}
    (hx : IsUnit (Ideal.Quotient.mk c.rayModulus x)) :
    (expansion_rayCharacterFromHom c f).val.onElement x = f (rayClass c x) := by
  unfold HeckeCharacter.onElement expansion_rayCharacterFromHom rayClass
  rw [dite_eq_left hx]
  have h := MulChar.ofUnitHom_coe
    (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c))) hx.unit
  simpa only [hx.unit_spec, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits,
    QuotientGroup.mk'_apply] using h

theorem expansion_primaryGenerator_unit_rayModulus (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) :
    IsUnit (Ideal.Quotient.mk c.rayModulus (primaryGenerator a)) := by
  have hcoprime : IsCoprime a c.rayModulus := by
    apply Ideal.coprime_of_no_prime_ge
    intro p hap hmp hp
    have hp₀ : p ≠ ⊥ := by
      intro h
      exact c.rayModulus_ne_bot (le_bot_iff.mp (h ▸ hmp))
    have hp' := Ideal.prime_of_isPrime hp₀ hp
    exact ha.2 p (c.ray_supported p hp' (Ideal.dvd_iff_le.mpr hmp))
      (Ideal.dvd_iff_le.mpr hap)
  obtain ⟨i, hi, j, hj, hij⟩ := hcoprime.exists
  rw [← expansion_primary_spec c ha] at hi
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hi
  have h := congrArg (Ideal.Quotient.mk c.rayModulus) hij
  have hj₀ := Ideal.Quotient.eq_zero_iff_mem.mpr hj
  simp only [map_add, map_mul, hj₀, add_zero, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk c.rayModulus b, h⟩

theorem expansion_rayCharacterFromHom_rayValue (c : ArithmeticContext)
    (f : RayClass c →* ℂ) {a : Ideal O} (ha : Outside c.S a) :
    rayValue (expansion_rayCharacterFromHom c f).val a = f (idealClass c a) :=
  expansion_rayCharacterFromHom_onElement c f (expansion_primaryGenerator_unit_rayModulus c ha)

/-- The fixed finite family used for every bounded function at this modulus. -/
def expansion_rayFourierCharacter (c : ArithmeticContext) (ψ : expansion_RayFourierIndex c) : RayCharacter c :=
  expansion_rayCharacterFromHom c (expansion_characterHom (G := RayClass c) ψ)

theorem expansion_rayFourierCharacter_rayValue (c : ArithmeticContext) (ψ : expansion_RayFourierIndex c)
    {a : Ideal O} (ha : Outside c.S a) :
    rayValue (expansion_rayFourierCharacter c ψ).val a = ψ (Additive.ofMul (idealClass c a)) :=
  expansion_rayCharacterFromHom_rayValue c (expansion_characterHom (G := RayClass c) ψ) ha

/-- Transport the residue character along its specified modulus equality. -/
def expansion_residueAtRayModulus (c : ArithmeticContext) (ξ : RayCharacter c) :
    MulChar (O ⧸ c.rayModulus) ℂ :=
  ξ.property ▸ ξ.val.residue

theorem expansion_residueAtRayModulus_onElement (c : ArithmeticContext) (ξ : RayCharacter c)
    (x : O) :
    expansion_residueAtRayModulus c ξ (Ideal.Quotient.mk c.rayModulus x) = ξ.val.onElement x := by
  rcases ξ with ⟨⟨M, hM, r, hu⟩, h⟩
  change M = c.rayModulus at h
  subst M
  rfl

theorem expansion_residueAtRayModulus_unit_trivial (c : ArithmeticContext) (ξ : RayCharacter c)
    (u : Oˣ) :
    expansion_residueAtRayModulus c ξ (Ideal.Quotient.mk c.rayModulus (u : O)) = 1 := by
  rw [expansion_residueAtRayModulus_onElement]
  exact ξ.val.unit_trivial u

def expansion_rayUnitHom (c : ArithmeticContext) (ξ : RayCharacter c) :
    (O ⧸ c.rayModulus)ˣ →* ℂ where
  toFun u := expansion_residueAtRayModulus c ξ (u : O ⧸ c.rayModulus)
  map_one' := (expansion_residueAtRayModulus c ξ).map_one
  map_mul' u v := (expansion_residueAtRayModulus c ξ).map_mul u v

theorem expansion_globalUnitImage_le_rayUnitHom_ker (c : ArithmeticContext) (ξ : RayCharacter c) :
    globalUnitImage c ≤ (expansion_rayUnitHom c ξ).ker := by
  rintro u ⟨v, rfl⟩
  exact expansion_residueAtRayModulus_unit_trivial c ξ v

/-- The actual ray character descended to the quotient by global units. -/
def expansion_rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c) : RayClass c →* ℂ :=
  QuotientGroup.lift (globalUnitImage c) (expansion_rayUnitHom c ξ)
    (expansion_globalUnitImage_le_rayUnitHom_ker c ξ)

theorem expansion_rayClassCharacter_rayClass (c : ArithmeticContext) (ξ : RayCharacter c)
    {x : O} (hx : IsUnit (Ideal.Quotient.mk c.rayModulus x)) :
    expansion_rayClassCharacter c ξ (rayClass c x) = ξ.val.onElement x := by
  unfold rayClass expansion_rayClassCharacter
  rw [dite_eq_left hx, QuotientGroup.lift_mk']
  change expansion_residueAtRayModulus c ξ (hx.unit : O ⧸ c.rayModulus) = _
  rw [hx.unit_spec, expansion_residueAtRayModulus_onElement]

theorem expansion_rayValue_eq_rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c)
    {a : Ideal O} (ha : Outside c.S a) :
    rayValue ξ.val a = expansion_rayClassCharacter c ξ (idealClass c a) :=
  (expansion_rayClassCharacter_rayClass c ξ (expansion_primaryGenerator_unit_rayModulus c ha)).symm

/-- Expand any function of the actual ray class as a finitely supported
linear combination of actual ray characters. Equal output characters are
combined by mapDomain, so no injectivity of the indexing map is assumed. -/
theorem expansion_class_function_ray_expansion (c : ArithmeticContext) (g : RayClass c → ℂ) :
    ∃ coeffs : RayCharacter c → ℂ, (Function.support coeffs).Finite ∧
      ∀ a : Ideal O, Outside c.S a →
        g (idealClass c a) = ∑' ξ : RayCharacter c, coeffs ξ * rayValue ξ.val a := by
  let : Fintype (RayClass c) := expansion_rayClassFintype c
  let l : expansion_RayFourierIndex c →₀ ℂ :=
    (AddChar.complexBasis (Additive (RayClass c))).repr (fun x => g x.toMul)
  let m : RayCharacter c →₀ ℂ := l.mapDomain (expansion_rayFourierCharacter c)
  refine ⟨(m : RayCharacter c → ℂ), m.hasFiniteSupport, ?_⟩
  intro a ha
  have hb := congr_fun
    ((AddChar.complexBasis (Additive (RayClass c))).linearCombination_repr
      (fun x => g x.toMul)) (Additive.ofMul (idealClass c a))
  have hb' : l.sum (fun ψ v => v * ψ (Additive.ofMul (idealClass c a))) =
      g (idealClass c a) := by
    simpa [l, Finsupp.linearCombination_apply, Finsupp.sum] using hb
  calc
    g (idealClass c a) = l.sum (fun ψ v => v * ψ (Additive.ofMul (idealClass c a))) := hb'.symm
    _ = l.sum (fun ψ v => v * rayValue (expansion_rayFourierCharacter c ψ).val a) := by
      apply Finsupp.sum_congr
      intro ψ _
      rw [expansion_rayFourierCharacter_rayValue c ψ ha]
    _ = m.sum (fun ξ v => v * rayValue ξ.val a) := by
      exact (Finsupp.sum_mapDomain_index (f := expansion_rayFourierCharacter c) (s := l)
        (h := fun (ξ : RayCharacter c) (v : ℂ) => v * rayValue ξ.val a)
        (fun (ξ : RayCharacter c) => zero_mul (rayValue ξ.val a))
        (fun (ξ : RayCharacter c) (u v : ℂ) => add_mul u v (rayValue ξ.val a))).symm
    _ = ∑' ξ : RayCharacter c, m ξ * rayValue ξ.val a := by
      symm
      apply tsum_eq_sum
      intro ξ hξ
      rw [Finsupp.notMem_support_iff.mp hξ, zero_mul]



/-- The original Hecke character evaluated on residue units at the fixed ray modulus. -/
def expansionNuUnitHom (c : ArithmeticContext) : (O ⧸ c.rayModulus)ˣ →* ℂ where
  toFun u := c.nu.residue (Ideal.Quotient.factor c.nu_factors (u : O ⧸ c.rayModulus))
  map_one' := by simp only [Units.val_one, map_one]
  map_mul' u v := by simp only [Units.val_mul, map_mul]

theorem expansion_nuUnitHom_unit_trivial (c : ArithmeticContext) (u : Oˣ) :
    expansionNuUnitHom c (Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u) = 1 := by
  exact c.nu.unit_trivial u

def expansionNuRayHom (c : ArithmeticContext) : RayClass c →* ℂ :=
  QuotientGroup.lift (globalUnitImage c) (expansionNuUnitHom c) (by
    rintro u ⟨v, rfl⟩
    exact expansion_nuUnitHom_unit_trivial c v)

theorem expansion_nuRayHom_onIdeal (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : expansionNuRayHom c (idealClass c a) = c.nu.onIdeal a := by
  have hx := expansion_primaryGenerator_unit_rayModulus c ha
  unfold idealClass rayClass expansionNuRayHom
  rw [dite_eq_left hx, QuotientGroup.lift_mk']
  change c.nu.residue (Ideal.Quotient.factor c.nu_factors
    (hx.unit : O ⧸ c.rayModulus)) = _
  rw [hx.unit_spec, Ideal.Quotient.factor_mk]
  exact (c.nu.onIdeal_of_generator ha.1 (expansion_primary_spec c ha)).symm

/-- A fixed finite family expands the literal inverse ray-class factor on any pair
of outside ideals. Its coefficients are chosen before every test and scale. -/
theorem expansion_paired_ray_expansion (c : ArithmeticContext) (g : RayClass c → ℂ) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ),
      ∀ (a b : Ideal O), Outside c.S a → Outside c.S b →
        g (idealClass c a * (idealClass c b)⁻¹) =
          ∑ ξ ∈ Ξ, coeffs ξ * rayValue ξ.val a * star (rayValue ξ.val b) := by
  let l : expansion_RayFourierIndex c →₀ ℂ :=
    (AddChar.complexBasis (Additive (RayClass c))).repr (fun x => g x.toMul)
  let m : RayCharacter c →₀ ℂ := l.mapDomain (expansion_rayFourierCharacter c)
  refine ⟨m.support, m, ?_⟩
  intro a b ha hb
  have hrepr := congr_fun
    ((AddChar.complexBasis (Additive (RayClass c))).linearCombination_repr
      (fun x => g x.toMul))
    (Additive.ofMul (idealClass c a * (idealClass c b)⁻¹))
  have hrepr' : l.sum (fun ψ v =>
      v * ψ (Additive.ofMul (idealClass c a * (idealClass c b)⁻¹))) =
      g (idealClass c a * (idealClass c b)⁻¹) := by
    simpa [l, Finsupp.linearCombination_apply, Finsupp.sum] using hrepr
  have hpair (ψ : expansion_RayFourierIndex c) :
      ψ (Additive.ofMul (idealClass c a * (idealClass c b)⁻¹)) =
        rayValue (expansion_rayFourierCharacter c ψ).val a *
          star (rayValue (expansion_rayFourierCharacter c ψ).val b) := by
    rw [expansion_rayFourierCharacter_rayValue c ψ ha,
      expansion_rayFourierCharacter_rayValue c ψ hb]
    change ψ (Additive.ofMul (idealClass c a) + -Additive.ofMul (idealClass c b)) = _
    rw [ψ.map_add_eq_mul]
    congr 1
    exact AddChar.map_neg_eq_conj (G := Additive (RayClass c)) (K := ℂ) ψ
      (Additive.ofMul (idealClass c b))
  calc
    _ = l.sum (fun ψ v =>
        v * ψ (Additive.ofMul (idealClass c a * (idealClass c b)⁻¹))) := hrepr'.symm
    _ = l.sum (fun ψ v => v * rayValue (expansion_rayFourierCharacter c ψ).val a *
        star (rayValue (expansion_rayFourierCharacter c ψ).val b)) := by
      apply Finsupp.sum_congr
      intro ψ _
      rw [hpair ψ, mul_assoc]
    _ = m.sum (fun ξ v => v * rayValue ξ.val a * star (rayValue ξ.val b)) := by
      exact (Finsupp.sum_mapDomain_index
        (f := expansion_rayFourierCharacter c) (s := l)
        (h := fun (ξ : RayCharacter c) (v : ℂ) =>
          v * rayValue ξ.val a * star (rayValue ξ.val b))
        (fun ξ => by simp only [zero_mul])
        (fun ξ u v => by simp only [add_mul])).symm
    _ = _ := rfl

/-- The precise fixed ray-class function in the initial Poisson reduction. -/
theorem expansion_initial_ray_expansion (c : ArithmeticContext)
    (hc : ArithmeticRelations c) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ),
      ∀ (a b : Ideal O), Outside c.S a → Outside c.S b →
        star (expansionNuRayHom c (idealClass c a * (idealClass c b)⁻¹)) *
          reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) =
          ∑ ξ ∈ Ξ, coeffs ξ * rayValue ξ.val a * star (rayValue ξ.val b) := by
  obtain ⟨Ξ, coeffs, h⟩ := expansion_paired_ray_expansion c
    (fun t => star (expansionNuRayHom c t) * reciprocityG c hc t⁻¹)
  refine ⟨Ξ, coeffs, ?_⟩
  intro a b ha hb
  have hi : (idealClass c a * (idealClass c b)⁻¹)⁻¹ =
      idealClass c b * (idealClass c a)⁻¹ := by
    calc
      _ = ((idealClass c b)⁻¹)⁻¹ * (idealClass c a)⁻¹ := mul_inv_rev _ _
      _ = _ := congrArg (fun z : RayClass c => z * (idealClass c a)⁻¹)
        (inv_inv (idealClass c b))
  simpa only [hi] using h a b ha hb


theorem expansion_sexticAtPrime_uniform_bound (P : Ideal O) :
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

theorem expansion_sexticSymbol_uniform_bound (n : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : O, ‖sexticSymbol n k‖ ≤ B := by
  have hprod (s : Multiset (Ideal O)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : O,
      ‖(s.map (fun P => sexticAtPrime P k)).prod‖ ≤ B := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, zero_le_one, by intro k; simp⟩
    | @cons P s ih =>
      obtain ⟨A, hA, hPA⟩ := expansion_sexticAtPrime_uniform_bound P
      obtain ⟨B, hB, hSB⟩ := ih
      refine ⟨A * B, mul_nonneg hA hB, ?_⟩
      intro k
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul (hPA k) (hSB k) (norm_nonneg _) hA
  by_cases hn : n = ⊥
  · exact ⟨0, le_rfl, by intro k; simp only [sexticSymbol, if_pos hn, norm_zero, le_refl]⟩
  · obtain ⟨B, hB, hbound⟩ := hprod (UniqueFactorizationMonoid.normalizedFactors n)
    exact ⟨B, hB, by intro k; simpa only [sexticSymbol, if_neg hn] using hbound k⟩


def expansionOriginalCoefficient (c : ArithmeticContext) (W : ℝ → ℂ) (D : ℝ)
    (n : Ideal O) : ℂ :=
  if Outside c.S n then (mobius n : ℂ) * c.nu.onIdeal n * W (normIdeal n / D) else 0

def expansionOriginalWindow (I : SupportInterval) (D : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le (I.hi * D)).toFinset

def expansionOriginalPair (c : ArithmeticContext) (W : ℝ → ℂ) (D : ℝ)
    (p : Ideal O × Ideal O) (u : O) : ℂ :=
  star (expansionOriginalCoefficient c W D p.1) * expansionOriginalCoefficient c W D p.2 *
    star (sexticSymbol p.1 u) * sexticSymbol p.2 u

def expansionOriginalCharacterRow (Φ : RowWeight) (H : ℝ)
    (a b : Ideal O) (u : O) : ℂ :=
  (Φ.value (normElement u / H) : ℂ) * star (sexticSymbol a u) * sexticSymbol b u

def expansionOriginalTerm (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D H : ℝ) (p : Ideal O × Ideal O) (u : O) : ℂ :=
  (Φ.value (normElement u / H) : ℂ) * expansionOriginalPair c W D p u

def expansionSmoothedEnergy (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D H : ℝ) : ℝ :=
  D⁻¹ * ∑' u : O, Φ.value (normElement u / H) * ‖originalSum c W D u‖ ^ 2

theorem expansion_originalCoefficient_support (c : ArithmeticContext)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) :
    Function.support (expansionOriginalCoefficient c W D) ⊆
      (expansionOriginalWindow I D : Set (Ideal O)) := by
  intro n hn
  have hw : W (normIdeal n / D) ≠ 0 := by
    intro hw
    exact hn (by simp only [expansionOriginalCoefficient, hw, mul_zero, ite_self])
  exact (finite_normIdeal_le _).mem_toFinset.mpr ((div_le_iff₀ hD).mp (hW.2 hw).2)

theorem expansion_originalSum_eq_finite (c : ArithmeticContext)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (u : O) :
    originalSum c W D u = ∑ n ∈ expansionOriginalWindow I D,
      expansionOriginalCoefficient c W D n * sexticSymbol n u := by
  have h : originalSum c W D u = ∑' n : Ideal O,
      expansionOriginalCoefficient c W D n * sexticSymbol n u := by
    unfold originalSum
    apply tsum_congr
    intro n
    by_cases hn : Outside c.S n
    · simp only [expansionOriginalCoefficient, if_pos hn]
      ring
    · simp only [expansionOriginalCoefficient, if_neg hn, zero_mul]
  rw [h]
  apply tsum_eq_sum
  intro n hn
  have hz : expansionOriginalCoefficient c W D n = 0 := by
    by_contra hz
    exact hn (expansion_originalCoefficient_support c hW hD hz)
  rw [hz, zero_mul]

theorem expansion_originalPair_support (c : ArithmeticContext)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (u : O) :
    Function.support (fun p => expansionOriginalPair c W D p u) ⊆
      ((expansionOriginalWindow I D).product (expansionOriginalWindow I D) :
        Set (Ideal O × Ideal O)) := by
  intro p hp
  have h1 : expansionOriginalCoefficient c W D p.1 ≠ 0 := by
    intro hz
    exact hp (by simp only [expansionOriginalPair, hz, star_zero, zero_mul])
  have h2 : expansionOriginalCoefficient c W D p.2 ≠ 0 := by
    intro hz
    exact hp (by simp only [expansionOriginalPair, hz, mul_zero, zero_mul])
  exact Finset.mem_product.mpr ⟨expansion_originalCoefficient_support c hW hD h1,
    expansion_originalCoefficient_support c hW hD h2⟩

theorem expansion_originalSum_square (c : ArithmeticContext)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (u : O) :
    ((‖originalSum c W D u‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : Ideal O × Ideal O, expansionOriginalPair c W D p u := by
  let s := expansionOriginalWindow I D
  have hz (p : Ideal O × Ideal O) (hp : p ∉ s.product s) :
      expansionOriginalPair c W D p u = 0 := by
    by_contra hne
    exact hp (expansion_originalPair_support c hW hD u hne)
  calc
    _ = star (originalSum c W D u) * originalSum c W D u := by
      simpa only [Complex.ofReal_pow, starRingEnd_apply, mul_comm] using
        (Complex.mul_conj' (originalSum c W D u)).symm
    _ = star (∑ n ∈ s, expansionOriginalCoefficient c W D n * sexticSymbol n u) *
        (∑ n ∈ s, expansionOriginalCoefficient c W D n * sexticSymbol n u) := by
      rw [expansion_originalSum_eq_finite c hW hD u]
    _ = ∑ p ∈ s.product s, expansionOriginalPair c W D p u := by
      rw [Finset.product_eq_sprod, Finset.sum_product, star_sum, Finset.sum_mul]
      simp only [star_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      unfold expansionOriginalPair
      ring
    _ = _ := (tsum_eq_sum hz).symm

theorem expansion_originalCharacterRow_summable (Φ : RowWeight) {H : ℝ}
    (hH : 0 < H) (a b : Ideal O) : Summable (expansionOriginalCharacterRow Φ H a b) := by
  obtain ⟨A, hA, ha⟩ := expansion_sexticSymbol_uniform_bound a
  obtain ⟨B, hB, hb⟩ := expansion_sexticSymbol_uniform_bound b
  apply Summable.of_norm_bounded (((rowWeight_element_summable Φ hH).mul_right A).mul_right B)
  intro u
  have hphi : 0 ≤ Φ.value (normElement u / H) :=
    Φ.nonnegative _ (div_nonneg (Nat.cast_nonneg _) hH.le)
  simp only [expansionOriginalCharacterRow, norm_mul, norm_star, Complex.norm_real,
    Real.norm_of_nonneg hphi]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (ha u) hphi) (hb u) (norm_nonneg _)
    (mul_nonneg hphi hA)

theorem expansion_originalTerm_row_summable (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D : ℝ) {H : ℝ} (hH : 0 < H) (p : Ideal O × Ideal O) :
    Summable (expansionOriginalTerm c Φ W D H p) := by
  apply ((expansion_originalCharacterRow_summable Φ hH p.1 p.2).mul_left
    (star (expansionOriginalCoefficient c W D p.1) *
      expansionOriginalCoefficient c W D p.2)).congr
  intro u
  unfold expansionOriginalTerm expansionOriginalPair expansionOriginalCharacterRow
  ring

theorem expansion_finite_rows_summable {α : Type*} (s : Finset α)
    (g : α → O → ℂ) (hzero : ∀ a ∉ s, ∀ u, g a u = 0)
    (hrow : ∀ a, Summable (g a)) : Summable (fun p : α × O => g p.1 p.2) := by
  apply summable_norm_iff.mp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro a
    exact (hrow a).norm
  · apply summable_of_hasFiniteSupport
    apply s.finite_toSet.subset
    intro a ha
    by_contra hnot
    exact ha (by simp only [hzero a hnot, norm_zero, tsum_zero])

theorem expansion_originalTerm_joint_summable (c : ArithmeticContext) (Φ : RowWeight)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Summable (fun p : (Ideal O × Ideal O) × O => expansionOriginalTerm c Φ W D H p.1 p.2) := by
  apply expansion_finite_rows_summable
    ((expansionOriginalWindow I D).product (expansionOriginalWindow I D))
  · intro p hp u
    have hz : expansionOriginalPair c W D p u = 0 := by
      by_contra hz
      exact hp (expansion_originalPair_support c hW hD u hz)
    simp only [expansionOriginalTerm, hz, mul_zero]
  · exact expansion_originalTerm_row_summable c Φ W D hH

theorem expansion_smoothed_original_summable (c : ArithmeticContext) (Φ : RowWeight)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Summable (fun u : O => Φ.value (normElement u / H) * ‖originalSum c W D u‖ ^ 2) := by
  have hs := (expansion_originalTerm_joint_summable c Φ hW hD hH).prod_symm.prod
  have hpoint (u : O) : (∑' p : Ideal O × Ideal O, expansionOriginalTerm c Φ W D H p u) =
      ((Φ.value (normElement u / H) * ‖originalSum c W D u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, expansion_originalSum_square c hW hD u, ← tsum_mul_left]
    rfl
  have hs' : Summable (fun u : O =>
      ((Φ.value (normElement u / H) * ‖originalSum c W D u‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [Prod.swap, hpoint] using hs
  exact Complex.summable_ofReal.mp hs'

theorem expansion_originalMeanSquare_le_smoothed (c : ArithmeticContext) (Φ : RowWeight)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    originalMeanSquare c W D H ≤ D * expansionSmoothedEnergy c Φ W D H := by
  have hs := expansion_smoothed_original_summable c Φ hW hD hH
  have hmajor (u : O) :
      (if 0 < normElement u ∧ normElement u ≤ H then ‖originalSum c W D u‖ ^ 2 else 0) ≤
        Φ.value (normElement u / H) * ‖originalSum c W D u‖ ^ 2 := by
    split_ifs with hu
    · exact le_mul_of_one_le_left (sq_nonneg _) (Φ.majorant _
        ⟨(div_pos hu.1 hH).le, (div_le_one hH).mpr hu.2⟩)
    · exact mul_nonneg (Φ.nonnegative _ (div_nonneg (Nat.cast_nonneg _) hH.le)) (sq_nonneg _)
  have h := (originalMeanSquare_summable c W D H).tsum_le_tsum hmajor hs
  simpa only [expansionSmoothedEnergy, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul,
    originalMeanSquare] using h

set_option maxHeartbeats 800000 in
theorem expansion_original_energy_expansion (c : ArithmeticContext) (Φ : RowWeight)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    ((expansionSmoothedEnergy c Φ W D H : ℝ) : ℂ) =
      (D⁻¹ : ℂ) * ∑' a : Ideal O, ∑' b : Ideal O,
        star (expansionOriginalCoefficient c W D a) * expansionOriginalCoefficient c W D b *
          ∑' u : O, expansionOriginalCharacterRow Φ H a b u := by
  have hs := expansion_originalTerm_joint_summable c Φ hW hD hH
  unfold expansionSmoothedEnergy
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_tsum]
  congr 1
  have hpoint (u : O) :
      ((Φ.value (normElement u / H) * ‖originalSum c W D u‖ ^ 2 : ℝ) : ℂ) =
        ∑' p : Ideal O × Ideal O, expansionOriginalTerm c Φ W D H p u := by
    rw [Complex.ofReal_mul, expansion_originalSum_square c hW hD u, ← tsum_mul_left]
    rfl
  simp_rw [hpoint]
  rw [hs.tsum_comm, hs.prod.tsum_prod]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  rw [← tsum_mul_left]
  apply tsum_congr
  intro u
  unfold expansionOriginalTerm expansionOriginalPair expansionOriginalCharacterRow
  ring

/-- The single row weight works simultaneously for every test and positive scale. -/
theorem expansion_uniform_sharp_to_schwartz (c : ArithmeticContext) (I : SupportInterval) :
    ∃ Φ : RowWeight, ∀ (W : ℝ → ℂ) (D H : ℝ), SmoothSupported I W → 2 ≤ D → 0 < H →
      originalMeanSquare c W D H ≤ D * expansionSmoothedEnergy c Φ W D H := by
  obtain ⟨Φ⟩ := rowWeight_nonempty
  refine ⟨Φ, ?_⟩
  intro W D H hW hD hH
  exact expansion_originalMeanSquare_le_smoothed c Φ hW (lt_of_lt_of_le (by norm_num) hD) hH


def expansionGcdPairAdmissible (c : ArithmeticContext) (p : Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2

def expansionGcdTripleAdmissible (c : ArithmeticContext)
    (t : Ideal O × Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧ SquarefreeOutside c.S t.2.2 ∧
    IsRelPrime t.1 t.2.1 ∧ IsRelPrime t.1 t.2.2 ∧ IsRelPrime t.2.1 t.2.2

abbrev ExpansionGcdPairs (c : ArithmeticContext) :=
  {p : Ideal O × Ideal O // expansionGcdPairAdmissible c p}

abbrev ExpansionGcdTriples (c : ArithmeticContext) :=
  {t : Ideal O × Ideal O × Ideal O // expansionGcdTripleAdmissible c t}

/-- Reconstruction multiplies both residual ideals by their common factor. -/
def expansionGcdReconstruct (c : ArithmeticContext) :
    ExpansionGcdTriples c → ExpansionGcdPairs c := fun t =>
  ⟨(t.1.1 * t.1.2.1, t.1.1 * t.1.2.2),
    ⟨(expansion_outside_mul c _ _).mpr ⟨t.2.1.1, t.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨t.2.2.2.2.1, t.2.1.2, t.2.2.1.2⟩⟩,
    ⟨(expansion_outside_mul c _ _).mpr ⟨t.2.1.1, t.2.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨t.2.2.2.2.2.1, t.2.1.2, t.2.2.2.1.2⟩⟩⟩

@[simp] theorem expansionGcdReconstruct_val (c : ArithmeticContext)
    (t : ExpansionGcdTriples c) :
    (expansionGcdReconstruct c t).1 = (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2) := rfl

/-- The reconstructed pair has exactly C as its actual ideal gcd. -/
theorem expansionGcdReconstruct_gcd (c : ArithmeticContext) (t : ExpansionGcdTriples c) :
    gcd (expansionGcdReconstruct c t).1.1 (expansionGcdReconstruct c t).1.2 = t.1.1 := by
  have hunit : gcd t.1.2.1 t.1.2.2 = 1 :=
    (gcd_isUnit_iff_isRelPrime.mpr t.2.2.2.2.2.2).eq_one
  change gcd (t.1.1 * t.1.2.1) (t.1.1 * t.1.2.2) = t.1.1
  rw [gcd_mul_left, normalize_eq, hunit, mul_one]

theorem expansionGcdReconstruct_injective (c : ArithmeticContext) :
    Function.Injective (expansionGcdReconstruct c) := by
  intro t s h
  have hC : t.1.1 = s.1.1 := by
    calc
      t.1.1 = gcd (expansionGcdReconstruct c t).1.1
          (expansionGcdReconstruct c t).1.2 := (expansionGcdReconstruct_gcd c t).symm
      _ = gcd (expansionGcdReconstruct c s).1.1
          (expansionGcdReconstruct c s).1.2 :=
        congrArg (fun p : ExpansionGcdPairs c => gcd p.1.1 p.1.2) h
      _ = s.1.1 := expansionGcdReconstruct_gcd c s
  have hpair : (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2) =
      (s.1.1 * s.1.2.1, s.1.1 * s.1.2.2) := congrArg Subtype.val h
  apply Subtype.ext
  apply Prod.ext hC
  apply Prod.ext
  · apply mul_left_cancel₀ t.2.1.1.1
    simpa only [hC] using congrArg Prod.fst hpair
  · apply mul_left_cancel₀ t.2.1.1.1
    simpa only [hC] using congrArg Prod.snd hpair

/-- Extraction starts with Mathlib's literal gcd factorization; squarefreeness
forces each residual factor to be coprime to the common factor as well. -/
theorem expansionGcdReconstruct_surjective (c : ArithmeticContext) :
    Function.Surjective (expansionGcdReconstruct c) := by
  intro p
  obtain ⟨u, v, hu, hv, huv⟩ := extract_gcd p.1.1 p.1.2
  let C := gcd p.1.1 p.1.2
  have hC : SquarefreeOutside c.S C :=
    ⟨expansion_outside_of_dvd c p.2.1.1 (gcd_dvd_left _ _),
      p.2.1.2.squarefree_of_dvd (gcd_dvd_left _ _)⟩
  have hudiv : u ∣ p.1.1 := ⟨C, hu.trans (mul_comm _ _)⟩
  have hvdiv : v ∣ p.1.2 := ⟨C, hv.trans (mul_comm _ _)⟩
  have huout : SquarefreeOutside c.S u :=
    ⟨expansion_outside_of_dvd c p.2.1.1 hudiv, p.2.1.2.squarefree_of_dvd hudiv⟩
  have hvout : SquarefreeOutside c.S v :=
    ⟨expansion_outside_of_dvd c p.2.2.1 hvdiv, p.2.2.2.squarefree_of_dvd hvdiv⟩
  have hCu : IsRelPrime C u := IsRelPrime.of_squarefree_mul (hu ▸ p.2.1.2)
  have hCv : IsRelPrime C v := IsRelPrime.of_squarefree_mul (hv ▸ p.2.2.2)
  have huv' : IsRelPrime u v := gcd_isUnit_iff_isRelPrime.mp huv
  refine ⟨⟨(C, u, v), hC, huout, hvout, hCu, hCv, huv'⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hu.symm hv.symm

theorem expansionGcdReconstruct_bijective (c : ArithmeticContext) :
    Function.Bijective (expansionGcdReconstruct c) :=
  ⟨expansionGcdReconstruct_injective c, expansionGcdReconstruct_surjective c⟩

/-- The forward map reconstructs the pair; the inverse is its unique gcd triple. -/
def expansionGcdEquiv (c : ArithmeticContext) :
    ExpansionGcdTriples c ≃ ExpansionGcdPairs c :=
  Equiv.ofBijective (expansionGcdReconstruct c) (expansionGcdReconstruct_bijective c)

@[simp] theorem expansionGcdEquiv_apply (c : ArithmeticContext) (t : ExpansionGcdTriples c) :
    expansionGcdEquiv c t = expansionGcdReconstruct c t := rfl

theorem expansionGcdEquiv_symm_gcd (c : ArithmeticContext) (p : ExpansionGcdPairs c) :
    ((expansionGcdEquiv c).symm p).1.1 = gcd p.1.1 p.1.2 := by
  have h := expansionGcdReconstruct_gcd c ((expansionGcdEquiv c).symm p)
  change gcd (expansionGcdEquiv c ((expansionGcdEquiv c).symm p)).1.1
    (expansionGcdEquiv c ((expansionGcdEquiv c).symm p)).1.2 = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem expansionGcdEquiv_symm_reconstruct (c : ArithmeticContext) (p : ExpansionGcdPairs c) :
    let t := (expansionGcdEquiv c).symm p
    p.1.1 = t.1.1 * t.1.2.1 ∧ p.1.2 = t.1.1 * t.1.2.2 := by
  have h := congrArg Subtype.val ((expansionGcdEquiv c).apply_symm_apply p)
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem expansion_gcd_summable_iff {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : ExpansionGcdPairs c → E) :
    Summable (fun t : ExpansionGcdTriples c => f (expansionGcdReconstruct c t)) ↔
      Summable f :=
  (expansionGcdEquiv c).summable_iff

theorem expansion_gcd_summable_reindex {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : ExpansionGcdPairs c → E) (hf : Summable f) :
    Summable (fun t : ExpansionGcdTriples c => f (expansionGcdReconstruct c t)) ∧
      (∑' p, f p) = ∑' t : ExpansionGcdTriples c, f (expansionGcdReconstruct c t) :=
  ⟨(expansion_gcd_summable_iff c f).mpr hf, ((expansionGcdEquiv c).tsum_eq f).symm⟩

/-- An unbundled form ready for literal ideal-pair expansions: both transformed
restrictions and all three coprimalities are exactly those of the gcd triple. -/
theorem expansion_gcd_indicator_reindex {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (c : ArithmeticContext) (f : Ideal O × Ideal O → E)
    (hf : Summable (fun p : Ideal O × Ideal O =>
      if expansionGcdPairAdmissible c p then f p else 0)) :
    Summable (fun t : Ideal O × Ideal O × Ideal O =>
      if expansionGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0) ∧
    (∑' p : Ideal O × Ideal O, if expansionGcdPairAdmissible c p then f p else 0) =
      ∑' t : Ideal O × Ideal O × Ideal O,
        if expansionGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
  have hpairIndicator : ({p | expansionGcdPairAdmissible c p}.indicator f) =
      (fun p => if expansionGcdPairAdmissible c p then f p else 0) := by
    funext p
    exact Set.indicator_apply _ _ _
  have htripleIndicator : ({t | expansionGcdTripleAdmissible c t}.indicator
      (fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))) =
      (fun t => if expansionGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2)
        else 0) := by
    funext t
    exact Set.indicator_apply _ _ _
  have hpair : Summable (fun p : ExpansionGcdPairs c => f p.1) := by
    apply (summable_subtype_iff_indicator
      (s := {p | expansionGcdPairAdmissible c p}) (f := f)).mpr
    rw [hpairIndicator]
    exact hf
  obtain ⟨htriple, heq⟩ := expansion_gcd_summable_reindex c
    (fun p : ExpansionGcdPairs c => f p.1) hpair
  have htriple' := (summable_subtype_iff_indicator
    (s := {t | expansionGcdTripleAdmissible c t})
    (f := fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))).mp htriple
  refine ⟨?_, ?_⟩
  · rw [htripleIndicator] at htriple'
    exact htriple'
  · have hp : (∑' p : ExpansionGcdPairs c, f p.1) =
        ∑' p : Ideal O × Ideal O, if expansionGcdPairAdmissible c p then f p else 0 := by
      have h := tsum_subtype {p | expansionGcdPairAdmissible c p} f
      simp_rw [hpairIndicator] at h
      exact h
    have ht : (∑' t : ExpansionGcdTriples c, f (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2)) =
        ∑' t : Ideal O × Ideal O × Ideal O,
          if expansionGcdTripleAdmissible c t then f (t.1 * t.2.1, t.1 * t.2.2) else 0 := by
      have h := tsum_subtype {t | expansionGcdTripleAdmissible c t}
        (fun t : Ideal O × Ideal O × Ideal O => f (t.1 * t.2.1, t.1 * t.2.2))
      simp_rw [htripleIndicator] at h
      exact h
    exact hp.symm.trans (heq.trans ht)

theorem expansion_originalCoefficient_zero_of_not_squarefree (c : ArithmeticContext)
    (W : ℝ → ℂ) (D : ℝ) {a : Ideal O} (ha : ¬ SquarefreeOutside c.S a) :
    expansionOriginalCoefficient c W D a = 0 := by
  by_cases hout : Outside c.S a
  · have hsq : ¬ Squarefree a := fun h => ha ⟨hout, h⟩
    simp only [expansionOriginalCoefficient, if_pos hout, mobius,
      UniqueFactorizationMonoid.moebius_of_not_squarefree hsq, Int.cast_zero, zero_mul]
  · simp only [expansionOriginalCoefficient, if_neg hout]

def expansionOriginalGcdTerm (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D H : ℝ) (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if expansionGcdTripleAdmissible c t then
    star (expansionOriginalCoefficient c W D (t.1 * t.2.1)) *
      expansionOriginalCoefficient c W D (t.1 * t.2.2) *
        ∑' u : O, expansionOriginalCharacterRow Φ H (t.1 * t.2.1) (t.1 * t.2.2) u
  else 0

theorem expansion_original_energy_gcd_row (c : ArithmeticContext) (Φ : RowWeight)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (H : ℝ) :
    Summable (expansionOriginalGcdTerm c Φ W D H) ∧
      (∑' a : Ideal O, ∑' b : Ideal O,
        star (expansionOriginalCoefficient c W D a) * expansionOriginalCoefficient c W D b *
          ∑' u : O, expansionOriginalCharacterRow Φ H a b u) =
        ∑' t : Ideal O × Ideal O × Ideal O, expansionOriginalGcdTerm c Φ W D H t := by
  let g : Ideal O × Ideal O → ℂ := fun p =>
    star (expansionOriginalCoefficient c W D p.1) * expansionOriginalCoefficient c W D p.2 *
      ∑' u : O, expansionOriginalCharacterRow Φ H p.1 p.2 u
  have hfinite : Function.HasFiniteSupport g := by
    apply ((expansionOriginalWindow I D).finite_toSet.prod
      (expansionOriginalWindow I D).finite_toSet).subset
    intro p hp
    constructor
    · apply expansion_originalCoefficient_support c hW hD
      intro hz
      exact hp (by simp only [g, hz, star_zero, zero_mul])
    · apply expansion_originalCoefficient_support c hW hD
      intro hz
      exact hp (by simp only [g, hz, mul_zero, zero_mul])
  have hrestrict : (fun p : Ideal O × Ideal O =>
      if expansionGcdPairAdmissible c p then g p else 0) = g := by
    funext p
    by_cases ha : SquarefreeOutside c.S p.1
    · by_cases hb : SquarefreeOutside c.S p.2
      · rw [if_pos (show expansionGcdPairAdmissible c p from ⟨ha, hb⟩)]
      · simp only [expansionGcdPairAdmissible, ha, hb, and_false, if_false,
          g, expansion_originalCoefficient_zero_of_not_squarefree c W D hb, mul_zero, zero_mul]
    · simp only [expansionGcdPairAdmissible, ha, false_and, if_false,
        g, expansion_originalCoefficient_zero_of_not_squarefree c W D ha, star_zero, zero_mul]
  have hs : Summable g := summable_of_hasFiniteSupport hfinite
  have hrestricted : Summable (fun p => if expansionGcdPairAdmissible c p then g p else 0) := by
    rw [hrestrict]
    exact hs
  obtain ⟨ht, heq⟩ := expansion_gcd_indicator_reindex c g hrestricted
  refine ⟨ht, ?_⟩
  rw [hrestrict] at heq
  exact hs.tsum_prod.symm.trans heq

/-- The actual original smoothed energy, indexed by its genuine common ideal gcd. -/
theorem expansion_original_energy_gcd (c : ArithmeticContext) (Φ : RowWeight)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    (expansionSmoothedEnergy c Φ W D H : ℂ) =
      (D⁻¹ : ℂ) * ∑' t : Ideal O × Ideal O × Ideal O,
        expansionOriginalGcdTerm c Φ W D H t := by
  rw [expansion_original_energy_expansion c Φ hW hD hH,
    (expansion_original_energy_gcd_row c Φ hW hD H).2]


def expansionNuRayAddChar (c : ArithmeticContext) : AddChar (Additive (RayClass c)) ℂ where
  toFun t := expansionNuRayHom c t.toMul
  map_zero_eq_one' := (expansionNuRayHom c).map_one
  map_add_eq_mul' a b := (expansionNuRayHom c).map_mul a.toMul b.toMul

theorem expansion_nuRayHom_inv (c : ArithmeticContext) (t : RayClass c) :
    expansionNuRayHom c t⁻¹ = star (expansionNuRayHom c t) := by
  exact AddChar.map_neg_eq_conj (G := Additive (RayClass c)) (K := ℂ)
    (expansionNuRayAddChar c) (Additive.ofMul t)

/-- Literal original Hecke coefficients, rather than only abstract class evaluations. -/
theorem expansion_initial_ray_expansion_onIdeals (c : ArithmeticContext)
    (hc : ArithmeticRelations c) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ),
      ∀ (a b : Ideal O), Outside c.S a → Outside c.S b →
        star (c.nu.onIdeal a) * c.nu.onIdeal b *
          reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) =
          ∑ ξ ∈ Ξ, coeffs ξ * rayValue ξ.val a * star (rayValue ξ.val b) := by
  obtain ⟨Ξ, coeffs, h⟩ := expansion_initial_ray_expansion c hc
  refine ⟨Ξ, coeffs, ?_⟩
  intro a b ha hb
  simpa only [map_mul, expansion_nuRayHom_inv, star_mul, star_star,
    expansion_nuRayHom_onIdeal c ha, expansion_nuRayHom_onIdeal c hb, mul_comm] using h a b ha hb

/-- The coefficient bound is fixed with the ray family, before any row or test. -/
theorem expansion_initial_ray_expansion_uniform (c : ArithmeticContext)
    (hc : ArithmeticRelations c) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ) (A : ℝ),
      0 ≤ A ∧
      (∀ (a b : Ideal O), Outside c.S a → Outside c.S b →
        star (c.nu.onIdeal a) * c.nu.onIdeal b *
          reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) =
          ∑ ξ ∈ Ξ, coeffs ξ * rayValue ξ.val a * star (rayValue ξ.val b)) ∧
      ∀ S : RayCharacter c → ℂ, ‖∑ ξ ∈ Ξ, coeffs ξ * S ξ‖ ≤ A * ∑ ξ ∈ Ξ, ‖S ξ‖ := by
  obtain ⟨Ξ, coeffs, h⟩ := expansion_initial_ray_expansion_onIdeals c hc
  let A := ∑ ξ ∈ Ξ, ‖coeffs ξ‖
  refine ⟨Ξ, coeffs, A, Finset.sum_nonneg (fun _ _ => norm_nonneg _), h, ?_⟩
  intro S
  calc
    _ ≤ ∑ ξ ∈ Ξ, ‖coeffs ξ * S ξ‖ := norm_sum_le _ _
    _ ≤ ∑ ξ ∈ Ξ, A * ‖S ξ‖ := by
      apply Finset.sum_le_sum
      intro ξ hξ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun ζ _ => norm_nonneg (coeffs ζ)) hξ) (norm_nonneg _)
    _ = _ := (Finset.mul_sum Ξ _ _).symm

theorem expansion_primitive_character_eq_one_iff (χ : PrimitiveResidueCharacter) :
    χ.character = 1 ↔ χ.modulus = ⊤ := by
  constructor
  · intro hχ
    apply Eq.symm
    apply χ.primitive ⊤ top_ne_bot le_top
    refine ⟨1, ?_⟩
    intro a ha
    rw [hχ, MulChar.one_apply ha]
    let : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have hx : Ideal.Quotient.mk (⊤ : Ideal O) a = 1 := Subsingleton.elim _ _
    rw [hx, map_one]
  · intro hmod
    let : Subsingleton (O ⧸ χ.modulus) := Ideal.Quotient.subsingleton_iff.mpr hmod
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    simp only [hx, Units.val_one, map_one]

theorem expansion_poissonZeroTerm_eq_zero_of_nonprincipal
    (hz : PoissonZeroStatement) (χ : PrimitiveResidueCharacter) (hχ : χ.character ≠ 1)
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) : poissonZeroTerm χ r Φ H = 0 := by
  unfold poissonZeroTerm
  simp only [hz.1 χ hχ, mul_zero, zero_mul, ite_self, tsum_zero]

theorem expansion_poissonZeroTerm_eq_zero_of_modulus_ne_top
    (hz : PoissonZeroStatement) (χ : PrimitiveResidueCharacter) (hχ : χ.modulus ≠ ⊤)
    (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ) : poissonZeroTerm χ r Φ H = 0 :=
  expansion_poissonZeroTerm_eq_zero_of_nonprincipal hz χ
    (mt (expansion_primitive_character_eq_one_iff χ).mp hχ) r Φ H

theorem expansion_zero_contribution_one_le_normIdeal {a : Ideal O} (ha : a ≠ ⊥) :
    1 ≤ normIdeal a := by
  let : Finite (O ⧸ a) := Ring.HasFiniteQuotients.finiteQuotient ha
  have hN : a.absNorm ≠ 0 := (Ideal.absNorm_ne_zero_iff a).mpr inferInstance
  have hNat : 1 ≤ a.absNorm := Nat.one_le_iff_ne_zero.mpr hN
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast hNat

theorem expansion_zero_euler_factor_norm_le_one {P : Ideal O} (hP : P ≠ ⊥) :
    ‖(1 : ℂ) - (normIdeal P : ℂ)⁻¹‖ ≤ 1 := by
  have hN := expansion_zero_contribution_one_le_normIdeal hP
  have hN0 : 0 ≤ normIdeal P := le_trans zero_le_one hN
  have hi0 : 0 ≤ (normIdeal P)⁻¹ := inv_nonneg.mpr hN0
  have hi1 : (normIdeal P)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have hsub : 0 ≤ 1 - (normIdeal P)⁻¹ := sub_nonneg.mpr hi1
  have hcast : (1 : ℂ) - (normIdeal P : ℂ)⁻¹ =
      ((1 - (normIdeal P)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsub]
  exact sub_le_self _ hi0

theorem expansion_zero_euler_product_norm_le_one (r : Ideal O) :
    ‖∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  exact expansion_zero_euler_factor_norm_le_one hp.ne_zero

theorem expansion_poissonZeroTerm_norm_le (hz : PoissonZeroStatement)
    (χ : PrimitiveResidueCharacter) (r : Ideal O) (hr : r ≠ ⊥)
    (Φ : RowWeight) (H : ℝ) (hH : 0 < H) :
    ‖poissonZeroTerm χ r (fun x => (Φ.value x : ℂ)) H‖ ≤
      H * ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖ := by
  by_cases hχ : χ.character = 1
  · rw [hz.2 χ r (fun x => (Φ.value x : ℂ)) H hχ
      ((expansion_primitive_character_eq_one_iff χ).mp hχ) hr hH Φ.schwartz]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    exact mul_le_of_le_one_right (mul_nonneg hH.le (norm_nonneg _))
      (expansion_zero_euler_product_norm_le_one r)
  · rw [expansion_poissonZeroTerm_eq_zero_of_nonprincipal hz χ hχ, norm_zero]
    exact mul_nonneg hH.le (norm_nonneg _)

/-- The diagonal expression produced by the principal Poisson character. -/
def expansionOriginalDiagonal (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D H : ℝ) : ℂ :=
  (H / D : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
    ∑' g : Ideal O, ((‖expansionOriginalCoefficient c W D g‖ ^ 2 : ℝ) : ℂ) *
      ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)

theorem expansion_originalCoefficient_norm_le (c : ArithmeticContext)
    (W : ℝ → ℂ) (D : ℝ) (a : Ideal O) :
    ‖expansionOriginalCoefficient c W D a‖ ≤ ‖W (normIdeal a / D)‖ := by
  unfold expansionOriginalCoefficient
  split_ifs
  · rw [norm_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (mul_le_one₀ (norm_mobius_le_one a) (norm_nonneg _) (c.nu.norm_onIdeal_le_one a))
  · exact (norm_zero : ‖(0 : ℂ)‖ = 0).le.trans (norm_nonneg _)

theorem expansion_originalDiagonal_eq_finite (c : ArithmeticContext) (Φ : RowWeight)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (H : ℝ) :
    expansionOriginalDiagonal c Φ W D H =
      (H / D : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
        ∑ g ∈ boundedDivisibleIdeals 1 (I.hi * D),
          ((‖expansionOriginalCoefficient c W D g‖ ^ 2 : ℝ) : ℂ) *
            ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹) := by
  unfold expansionOriginalDiagonal
  congr 1
  apply tsum_eq_sum
  intro g hg
  have hz : expansionOriginalCoefficient c W D g = 0 := by
    by_contra hne
    have hw : W (normIdeal g / D) ≠ 0 := by
      intro hw
      exact hne (by simp only [expansionOriginalCoefficient, hw, mul_zero, ite_self])
    have hout : Outside c.S g := by
      by_contra hout
      exact hne (by simp only [expansionOriginalCoefficient, if_neg hout])
    exact hg (mem_boundedDivisibleIdeals.mpr
      ⟨(div_le_iff₀ hD).mp (hW.2 hw).2, one_dvd _, hout.1⟩)
  simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.ofReal_zero, zero_mul]

/-- A uniform zero-frequency bound with no restriction H ≥ 1. -/
theorem expansion_originalDiagonal_uniform_bound (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ (W : ℝ → ℂ) (D H : ℝ), SmoothSupported I W → 0 < D → 0 < H →
      ‖expansionOriginalDiagonal c Φ W D H‖ ≤ Z * weightNorm 0 W ^ 2 * H := by
  obtain ⟨C, hC, hcount⟩ := exists_ideal_norm_count_constant
  let T := ‖radialFourier (fun x => (Φ.value x : ℂ)) 0‖
  have hI : 0 < I.hi := I.lo_pos.trans_le I.ordered
  refine ⟨C * I.hi * T, mul_nonneg (mul_nonneg hC.le hI.le) (norm_nonneg _), ?_⟩
  intro W D H hW hD hH
  rw [expansion_originalDiagonal_eq_finite c Φ hW hD H, norm_mul, norm_mul,
    norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hH.le,
    Real.norm_of_nonneg hD.le]
  have hterm (g : Ideal O) :
      ‖((‖expansionOriginalCoefficient c W D g‖ ^ 2 : ℝ) : ℂ) *
        ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)‖ ≤ weightNorm 0 W ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have hWg : ‖W (normIdeal g / D)‖ ≤ weightNorm 0 W := by
      simpa only [iteratedDeriv_zero] using
        norm_iteratedDeriv_le_weightNorm hW (le_refl 0) (normIdeal g / D)
    exact (mul_le_of_le_one_right (sq_nonneg _)
      (expansion_zero_euler_product_norm_le_one g)).trans
      (pow_le_pow_left₀ (norm_nonneg _) ((expansion_originalCoefficient_norm_le c W D g).trans hWg) 2)
  have hsum : ‖∑ g ∈ boundedDivisibleIdeals 1 (I.hi * D),
      ((‖expansionOriginalCoefficient c W D g‖ ^ 2 : ℝ) : ℂ) *
        ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)‖ ≤
      C * (I.hi * D) * weightNorm 0 W ^ 2 := by
    calc
      _ ≤ ∑ g ∈ boundedDivisibleIdeals 1 (I.hi * D), weightNorm 0 W ^ 2 :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => hterm g)
      _ = ((boundedDivisibleIdeals 1 (I.hi * D)).card : ℝ) * weightNorm 0 W ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcount _ (mul_pos hI hD)) (sq_nonneg _)
  calc
    _ ≤ H / D * T * (C * (I.hi * D) * weightNorm 0 W ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (div_nonneg hH.le hD.le) (norm_nonneg _))
    _ = _ := by dsimp [T]; field_simp [hD.ne'] <;> ring


open UniqueFactorizationMonoid



theorem expansionResidueLift_spec (n : Ideal O) (x : O ⧸ n) :
    Ideal.Quotient.mk n (residueLift n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

/-- Every local factor in the frozen symbol depends only on the residue modulo
the full denominator, including when that denominator has repeated factors. -/
theorem expansionSexticSymbol_congr {n : Ideal O} {a b : O}
    (hab : Ideal.Quotient.mk n a = Ideal.Quotient.mk n b) :
    sexticSymbol n a = sexticSymbol n b := by
  by_cases hn : n = ⊥
  · simp only [sexticSymbol, ite_eq_left hn]
  simp only [sexticSymbol, ite_eq_right hn]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hnP : n ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
  have habP : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b :=
    Ideal.Quotient.eq.mpr (hnP (Ideal.Quotient.eq.mp hab))
  simp only [sexticAtPrime, habP]

def expansionResidueValue (n : Ideal O) (x : O ⧸ n) : ℂ :=
  sexticSymbol n (residueLift n x)

@[simp] theorem expansionResidueValue_apply_mk (n : Ideal O) (a : O) :
    expansionResidueValue n (Ideal.Quotient.mk n a) = sexticSymbol n a :=
  expansionSexticSymbol_congr (expansionResidueLift_spec n _)

/-- A nonunit in the residue ring lies in a prime factor of the denominator,
so one of the actual local sextic factors is zero. -/
theorem expansionSexticSymbol_eq_zero_of_nonunit (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (a : O)
    (ha : ¬ IsUnit (Ideal.Quotient.mk n a)) : sexticSymbol n a = 0 := by
  have hproper : principal a ⊔ n ≠ ⊤ := by
    intro htop
    have hone : (1 : O) ∈ principal a ⊔ n := htop ▸ Submodule.mem_top
    obtain ⟨u, b, hb, heq⟩ := Ideal.mem_span_singleton_sup.mp hone
    apply ha
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk n u, ?_⟩
    have heq' := congrArg (Ideal.Quotient.mk n) heq
    simpa only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero] using heq'
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal (principal a ⊔ n) hproper
  have hnP : n ≤ P := le_trans le_sup_right hle
  have hPzero : P ≠ ⊥ := by
    intro hP
    apply hn.1
    exact le_antisymm (hP ▸ hnP) bot_le
  have hP : Prime P := Ideal.prime_of_isPrime hPzero hPmax.isPrime
  have hPmem : P ∈ normalizedFactors n :=
    (mem_normalizedFactors_iff hn.1).mpr ⟨hP, Ideal.dvd_iff_le.mpr hnP⟩
  have haP : a ∈ P := (le_trans le_sup_left hle) (Ideal.mem_span_singleton_self a)
  simp only [sexticSymbol, ite_eq_right hn.1]
  apply Multiset.prod_eq_zero
  apply Multiset.mem_map.mpr
  refine ⟨P, hPmem, ?_⟩
  exact SquarefreeReflection.sexticAtPrime_zero_of_mem hP
    (SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
      c hP (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors
        hn hPmem)) haP

/-- The literal sextic character of the actual quotient ring, without a
nontriviality assumption on that ring. -/
def expansionResidueCharacter (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : MulChar (O ⧸ n) ℂ where
  toFun := expansionResidueValue n
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk n), expansionResidueValue_apply_mk]
    exact SquarefreeReflection.sexticSymbol_one_of_outside c hn
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, expansionResidueValue_apply_mk,
      expansionResidueValue_apply_mk, expansionResidueValue_apply_mk]
    exact SquarefreeReflection.sexticSymbol_mul_numerator c hn a b
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [expansionResidueValue_apply_mk]
    exact expansionSexticSymbol_eq_zero_of_nonunit c hn a hx

@[simp] theorem expansionResidueCharacter_apply (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O ⧸ n) :
    expansionResidueCharacter c hn x = sexticSymbol n (residueLift n x) := rfl

@[simp] theorem expansionResidueCharacter_apply_mk (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (a : O) :
    expansionResidueCharacter c hn (Ideal.Quotient.mk n a) = sexticSymbol n a :=
  expansionResidueValue_apply_mk n a



/-- In a finite field containing a primitive m-th root, the usual power
test reaches every m-th root on a nonzero field element. -/
theorem expansion_finiteField_power_test_surjective {F : Type*}
    [Field F] [Fintype F] {m : ℕ} (hm : m ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) {w : F} (hw : w ^ m = 1) :
    ∃ a : F, a ≠ 0 ∧ a ^ ((Fintype.card F - 1) / m) = w := by
  letI : NeZero m := ⟨hm⟩
  have hMpos : 0 < Fintype.card F - 1 := by
    have hcard : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hdiv : m ∣ Fintype.card F - 1 :=
    (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero hm))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hgen : IsPrimitiveRoot (g : F) (Fintype.card F - 1) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have htest : IsPrimitiveRoot ((g : F) ^ ((Fintype.card F - 1) / m)) m :=
    hgen.pow hMpos (Nat.div_mul_cancel hdiv).symm
  obtain ⟨j, _, hj⟩ := htest.eq_pow_of_pow_eq_one hw
  refine ⟨(g : F) ^ j, pow_ne_zero j g.ne_zero, ?_⟩
  simpa only [← pow_mul, Nat.mul_comm] using hj

/-- Each of the six literal complex root values occurs at a residue unit. -/
theorem expansion_sexticAtPrime_surjective (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) (j : ℕ) (hj : j < 6) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      sexticAtPrime P a = embedding (rootSix ^ j) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hP hout
  have hroot : (Ideal.Quotient.mk P rootSix ^ j) ^ (6 : ℕ) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨x, hx, htest⟩ := expansion_finiteField_power_test_surjective
    (by decide : (6 : ℕ) ≠ 0) hζ hroot
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨a, ?_, ?_⟩
  · rw [ha]
    exact isUnit_iff_ne_zero.mpr hx
  · have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    apply SquarefreeReflection.RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj
    simpa only [hcard, ha, map_pow] using htest

theorem expansion_sexticAtPrime_hits_rootSix (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      sexticAtPrime P a = embedding rootSix := by
  simpa only [pow_one] using expansion_sexticAtPrime_surjective c hP hout 1 (by decide)

theorem expansion_embedding_rootSix_ne_one : embedding rootSix ≠ 1 := by
  intro h
  have hc : embedding rootSix ^ 3 = (-1 : ℂ) := by
    rw [← embedding_pow, rootSix_cube, embedding_neg, embedding_one]
  rw [h] at hc
  norm_num at hc

/-- A unit witness proves genuine nontriviality, independently of how a
multiplicative character on the residue ring is bundled. -/



theorem expansion_prime_character_hits_rootSix (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ a : O, IsUnit (Ideal.Quotient.mk P a) ∧
      expansionResidueCharacter c hout (Ideal.Quotient.mk P a) = embedding rootSix := by
  obtain ⟨a, ha, hv⟩ := expansion_sexticAtPrime_hits_rootSix c hP hout
  refine ⟨a, ha, ?_⟩
  rw [expansionResidueCharacter_apply_mk, SquarefreeReflection.sexticSymbol_prime hP]
  exact hv




theorem expansion_ideal_isCoprime_of_isRelPrime {a b : Ideal O}
    (hab : IsRelPrime a b) : IsCoprime a b := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp (hab
    (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

theorem expansion_quotient_mul_isUnit_iff (a b : Ideal O) (hab : IsCoprime a b)
    (x : O ⧸ (a * b)) :
    IsUnit x ↔ IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x) ∧
      IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  rw [← isUnit_map_iff e x, Prod.isUnit_iff]
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

/-- A prescribed unit in one factor and 1 in the other lift to a unit of the
actual product quotient. No nontriviality of either quotient is required. -/
theorem expansion_crt_unit_lift (a b : Ideal O) (hab : IsCoprime a b)
    (u : O) (hu : IsUnit (Ideal.Quotient.mk a u)) :
    ∃ x : O, Ideal.Quotient.mk a x = Ideal.Quotient.mk a u ∧
      Ideal.Quotient.mk b x = 1 ∧ IsUnit (Ideal.Quotient.mk (a * b) x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (e.symm (Ideal.Quotient.mk a u, (1 : O ⧸ b)))
  have heq : e (Ideal.Quotient.mk (a * b) x) = (Ideal.Quotient.mk a u, (1 : O ⧸ b)) := by
    rw [hx, e.apply_symm_apply]
  have hxa : Ideal.Quotient.mk a x = Ideal.Quotient.mk a u := by
    simpa only [e, Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
      using congrArg Prod.fst heq
  have hxb : Ideal.Quotient.mk b x = 1 := by
    simpa only [e, Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
      using congrArg Prod.snd heq
  refine ⟨x, hxa, hxb, ?_⟩
  apply (expansion_quotient_mul_isUnit_iff a b hab _).mpr
  simpa only [Ideal.Quotient.factor_mk, hxa, hxb] using And.intro hu isUnit_one

/-- The quotient character has exactly the manuscript's sextic factor and
conjugate sextic factor, with zero extension on every nonunit. -/
def expansionPairedResidueCharacter (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b) :
    MulChar (O ⧸ (a * b)) ℂ where
  toFun x := expansionResidueCharacter c ha (Ideal.Quotient.factor Ideal.mul_le_left x) *
    star (expansionResidueCharacter c hb (Ideal.Quotient.factor Ideal.mul_le_right x))
  map_one' := by simp only [map_one, star_one, mul_one]
  map_mul' := by
    intro x y
    simp only [map_mul, star_mul]
    ring
  map_nonunit' := by
    intro x hx
    have hnot := mt (expansion_quotient_mul_isUnit_iff a b
      (expansion_ideal_isCoprime_of_isRelPrime hab) x).mpr hx
    by_cases hxa : IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x)
    · have hxb : ¬ IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) :=
        fun h => hnot ⟨hxa, h⟩
      rw [(expansionResidueCharacter c hb).map_nonunit hxb, star_zero, mul_zero]
    · rw [(expansionResidueCharacter c ha).map_nonunit hxa, zero_mul]

@[simp] theorem expansionPairedResidueCharacter_apply_mk (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (x : O) :
    expansionPairedResidueCharacter c ha hb hab (Ideal.Quotient.mk (a * b) x) =
      sexticSymbol a x * star (sexticSymbol b x) := by
  change expansionResidueCharacter c ha
      (Ideal.Quotient.factor Ideal.mul_le_left (Ideal.Quotient.mk (a * b) x)) *
    star (expansionResidueCharacter c hb
      (Ideal.Quotient.factor Ideal.mul_le_right (Ideal.Quotient.mk (a * b) x))) = _
  simp only [Ideal.Quotient.factor_mk, expansionResidueCharacter_apply_mk]

theorem expansion_sexticSymbol_eq_one_of_mk_eq_one (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) {x : O} (hx : Ideal.Quotient.mk a x = 1) :
    sexticSymbol a x = 1 := by
  rw [← expansionResidueCharacter_apply_mk c ha, hx, map_one]

theorem expansion_sexticSymbol_mul (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, sexticSymbol]
  by_cases hb : b = ⊥
  · simp [hb, sexticSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]



theorem expansion_squarefree_dvd_of_prime_dvd {n J : Ideal O}
    (hn : n ≠ ⊥) (hJ : J ≠ ⊥) (hsq : Squarefree n)
    (hprime : ∀ P : Ideal O, Prime P → P ∣ n → P ∣ J) : n ∣ J := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hn hJ).mpr
  apply (Multiset.le_iff_subset ((squarefree_iff_nodup_normalizedFactors hn).mp hsq)).mpr
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact (mem_normalizedFactors_iff hJ).mpr ⟨hp, hprime P hp (dvd_of_mem_normalizedFactors hP)⟩

/-- Missing a prime factor of the left denominator produces a unit witness
whose paired literal value is nontrivial, while its residue modulo J is 1. -/
theorem expansion_paired_left_missing_prime_witness (c : ArithmeticContext)
    {a b J P : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hP : Prime P) (hPa : P ∣ a)
    (hmod : a * b ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
      Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
  obtain ⟨A, hA⟩ := hPa
  have hPa' : P ∣ a := ⟨A, hA⟩
  have hAa : A ∣ a := ⟨P, hA.trans (mul_comm _ _)⟩
  have hPout := expansion_outside_of_dvd c ha.1 hPa'
  have hAout := expansion_outside_of_dvd c ha.1 hAa
  have hsq : Squarefree (P * (A * b)) := by
    rw [← mul_assoc, ← hA]
    exact squarefree_mul_iff.mpr ⟨hab, ha.2, hb.2⟩
  have hcop : IsCoprime P (A * b) :=
    expansion_ideal_isCoprime_of_isRelPrime (IsRelPrime.of_squarefree_mul hsq)
  have hJdiv : J ∣ P * (A * b) := by
    rw [← mul_assoc, ← hA]
    exact Ideal.dvd_iff_le.mpr hmod
  have hJrest : J ∣ A * b :=
    ((hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot).symm).dvd_of_dvd_mul_left hJdiv
  obtain ⟨u, hu, hζ⟩ := expansion_prime_character_hits_rootSix c hP hPout
  obtain ⟨x, hxP, hxrest, hxunit⟩ := expansion_crt_unit_lift P (A * b) hcop u hu
  have hxJ : Ideal.Quotient.mk J x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (Ideal.le_of_dvd hJrest)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxA : Ideal.Quotient.mk A x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (show A * b ≤ A from Ideal.mul_le_left)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxb : Ideal.Quotient.mk b x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (show A * b ≤ b from Ideal.mul_le_right)) hxrest
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxPvalue : sexticSymbol P x = embedding rootSix := by
    apply (expansionSexticSymbol_congr hxP).trans
    simpa only [expansionResidueCharacter_apply_mk] using hζ
  have hxvalue : sexticSymbol a x * star (sexticSymbol b x) = embedding rootSix := by
    rw [hA, expansion_sexticSymbol_mul,
      expansion_sexticSymbol_eq_one_of_mk_eq_one c hAout hxA,
      expansion_sexticSymbol_eq_one_of_mk_eq_one c hb.1 hxb, hxPvalue]
    simp only [star_one, mul_one]
  refine ⟨x, ?_, hxJ, ?_⟩
  · rw [hA, mul_assoc]
    exact hxunit
  · rw [hxvalue]
    exact expansion_embedding_rootSix_ne_one

theorem expansion_paired_right_missing_prime_witness (c : ArithmeticContext)
    {a b J P : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (hP : Prime P) (hPb : P ∣ b)
    (hmod : a * b ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
      Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
  obtain ⟨x, hxunit, hxJ, hxvalue⟩ := expansion_paired_left_missing_prime_witness c
    hb ha hab.symm hP hPb (by simpa only [mul_comm] using hmod) hnot
  refine ⟨x, ?_, hxJ, ?_⟩
  · rw [mul_comm a b]
    exact hxunit
  · intro h
    apply hxvalue
    have hh := congrArg star h
    simpa only [star_mul, star_star, star_one, mul_comm] using hh

/-- The exact unit-agreement condition required by PrimitiveResidueCharacter. -/
theorem expansionPairedResidueCharacter_primitive (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (J : Ideal O) (hJ : J ≠ ⊥) (hmod : a * b ≤ J)
    (ψ : MulChar (O ⧸ J) ℂ)
    (hagrees : ∀ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) →
      expansionPairedResidueCharacter c ha.1 hb.1 hab (Ideal.Quotient.mk (a * b) x) =
        ψ (Ideal.Quotient.mk J x)) : J = a * b := by
  have hab0 : a * b ≠ ⊥ := mul_ne_zero ha.1.1 hb.1.1
  have hsq : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨hab, ha.2, hb.2⟩
  have hdiv : a * b ∣ J := expansion_squarefree_dvd_of_prime_dvd hab0 hJ hsq (by
    intro P hP hPab
    by_contra hnot
    have hex : ∃ x : O, IsUnit (Ideal.Quotient.mk (a * b) x) ∧
        Ideal.Quotient.mk J x = 1 ∧ sexticSymbol a x * star (sexticSymbol b x) ≠ 1 := by
      rcases hP.dvd_mul.mp hPab with hPa | hPb
      · exact expansion_paired_left_missing_prime_witness c ha hb hab hP hPa hmod hnot
      · exact expansion_paired_right_missing_prime_witness c ha hb hab hP hPb hmod hnot
    obtain ⟨x, hxunit, hxJ, hxvalue⟩ := hex
    apply hxvalue
    have h := hagrees x hxunit
    simpa only [expansionPairedResidueCharacter_apply_mk, hxJ, map_one] using h)
  exact le_antisymm (Ideal.le_of_dvd hdiv) hmod

/-- A primitive character for the literal paired sextic row, including the
principal character when both denominator ideals are the unit ideal. -/
def expansionPrimitivePairedCharacter (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b) :
    PrimitiveResidueCharacter where
  modulus := a * b
  modulus_ne_bot := mul_ne_zero ha.1.1 hb.1.1
  character := expansionPairedResidueCharacter c ha.1 hb.1 hab
  primitive := by
    intro J hJ hmod hfactor
    obtain ⟨ψ, hagrees⟩ := hfactor
    exact expansionPairedResidueCharacter_primitive c ha hb hab J hJ hmod ψ hagrees

@[simp] theorem expansionPrimitivePairedCharacter_modulus (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) : (expansionPrimitivePairedCharacter c ha hb hab).modulus = a * b := rfl

@[simp] theorem expansionPrimitivePairedCharacter_value (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) (x : O) :
    (expansionPrimitivePairedCharacter c ha hb hab).value x =
      sexticSymbol a x * star (sexticSymbol b x) :=
  expansionPairedResidueCharacter_apply_mk c ha.1 hb.1 hab x

/-- The inverse paired character needed by the conjugated original square. -/
def expansionInversePairedCharacter (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b) :
    PrimitiveResidueCharacter := expansionPrimitivePairedCharacter c hb ha hab.symm

theorem expansion_inversePairedCharacter_modulus (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b) :
    (expansionInversePairedCharacter c ha hb hab).modulus = a * b := mul_comm b a

theorem expansion_inversePairedCharacter_value (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b)
    (u : O) : (expansionInversePairedCharacter c ha hb hab).value u =
      star (sexticSymbol a u) * sexticSymbol b u := by
  rw [expansionInversePairedCharacter, expansionPrimitivePairedCharacter_value, mul_comm]

/-- The actual inverse paired row satisfies the permitted Poisson identity.
The Gauss factor here is still its literal normalized quotient-ring sum. -/
theorem expansion_inverse_paired_poisson (hp : PoissonStatement)
    (c : ArithmeticContext) (Φ : RowWeight) {a b g : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b)
    (hg : g ≠ ⊥) {H : ℝ} (hH : 0 < H) :
    (∑' u : O, if IsRelPrime (principal u) g then
      star (sexticSymbol a u) * sexticSymbol b u * (Φ.value (normElement u / H) : ℂ) else 0) =
      (H : ℂ) * (expansionInversePairedCharacter c ha hb hab).gauss /
        (Real.sqrt (normIdeal a * normIdeal b) : ℂ) *
        ∑' d : Ideal O, if d ∣ outsideRadical ∅ g then
          (mobius d : ℂ) * (star (sexticSymbol a (chosenGenerator d)) *
            sexticSymbol b (chosenGenerator d)) / (normIdeal d : ℂ) *
            ∑' h : O, (sexticSymbol a h * star (sexticSymbol b h)) *
              radialFourier (fun x => (Φ.value x : ℂ))
                (H * normElement h / (normIdeal d * (normIdeal a * normIdeal b)))
        else 0 := by
  have h := hp (expansionInversePairedCharacter c ha hb hab) g
    (fun x => (Φ.value x : ℂ)) H hg hH Φ.schwartz
  simpa only [expansion_inversePairedCharacter_value, expansion_inversePairedCharacter_modulus,
    expansion_normIdeal_mul, star_mul, star_star, mul_comm] using h


/-- Fourier support makes each literal dual frequency row finite. -/
theorem expansion_fourier_frequency_hasFiniteSupport (Φ : RowWeight)
    {H M : ℝ} (hH : 0 < H) (hM : 0 < M) :
    Function.HasFiniteSupport (fun h : O =>
      radialFourier (fun x => (Φ.value x : ℂ)) (H * normElement h / M)) := by
  apply (finite_normElement_le (Φ.fourierCap * M / H)).subset
  intro h hh
  have hx0 : 0 ≤ H * normElement h / M :=
    div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _)) hM.le
  have hcap := (Φ.fourier_support ⟨hh, hx0⟩).2
  have hmul : H * normElement h ≤ Φ.fourierCap * M := (div_le_iff₀ hM).mp hcap
  exact (le_div_iff₀ hH).mpr (by simpa only [mul_comm] using hmul)

theorem expansion_divisors_finite {g : Ideal O} (hg : g ≠ ⊥) :
    {d : Ideal O | d ∣ g}.Finite := by
  apply (finite_normIdeal_le (normIdeal g)).subset
  intro d hd
  have hpos : 0 < g.absNorm := Nat.pos_of_ne_zero
    (fun h => hg (Ideal.absNorm_eq_zero_iff.mp h))
  change (d.absNorm : ℝ) ≤ (g.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)

theorem expansion_outsideRadical_ne_bot (S : Finset (Ideal O)) (g : Ideal O) :
    outsideRadical S g ≠ ⊥ := by
  unfold outsideRadical
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact (prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero

/-- All dual divisor/frequency terms are jointly finite, independently of
which arithmetic coefficient is attached to them. -/
theorem expansion_poisson_dual_joint_hasFiniteSupport (Φ : RowWeight)
    {H : ℝ} (hH : 0 < H) {a b : Ideal O} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (g : Ideal O) (A : Ideal O × O → ℂ) :
    Function.HasFiniteSupport (fun p : Ideal O × O =>
      if p.1 ∣ outsideRadical ∅ g then A p *
        radialFourier (fun x => (Φ.value x : ℂ))
          (H * normElement p.2 / (normIdeal p.1 * (normIdeal a * normIdeal b))) else 0) := by
  have hr := expansion_outsideRadical_ne_bot ∅ g
  have hrow (d : Ideal O) (hd : d ∣ outsideRadical ∅ g) :
      Function.HasFiniteSupport (fun h : O =>
        radialFourier (fun x => (Φ.value x : ℂ))
          (H * normElement h / (normIdeal d * (normIdeal a * normIdeal b)))) := by
    apply expansion_fourier_frequency_hasFiniteSupport Φ hH
    exact mul_pos (lt_of_lt_of_le zero_lt_one
      (normIdeal_one_le (ne_zero_of_dvd_ne_zero hr hd)))
      (mul_pos (lt_of_lt_of_le zero_lt_one (normIdeal_one_le ha))
        (lt_of_lt_of_le zero_lt_one (normIdeal_one_le hb)))
  apply ((expansion_divisors_finite hr).biUnion
    (fun d hd => (hrow d hd).image (fun h : O => (d, h)))).subset
  intro p hp
  have hd : p.1 ∣ outsideRadical ∅ g := by
    by_contra hd
    exact hp (by simp only [if_neg hd])
  have hh : radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement p.2 / (normIdeal p.1 * (normIdeal a * normIdeal b))) ≠ 0 := by
    intro hh
    exact hp (by simp only [if_pos hd, hh, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨p.1, hd, ⟨p.2, hh, rfl⟩⟩

theorem expansion_inverse_paired_row_summable (Φ : RowWeight) {H : ℝ} (hH : 0 < H)
    (a b g : Ideal O) : Summable (fun u : O => if IsRelPrime (principal u) g then
      star (sexticSymbol a u) * sexticSymbol b u * (Φ.value (normElement u / H) : ℂ) else 0) := by
  apply ((expansion_originalCharacterRow_summable Φ hH a b).indicator
    {u | IsRelPrime (principal u) g}).congr
  intro u
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  split_ifs
  · unfold expansionOriginalCharacterRow
    ring
  · rfl


theorem expansion_isUnit_mk_iff_isRelPrime (n : Ideal O) (z : O) :
    IsUnit (Ideal.Quotient.mk n z) ↔ IsRelPrime (principal z) n := by
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hz
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hmem : z * t - 1 ∈ n := Ideal.Quotient.eq.mp (by
      simpa only [map_mul, map_one] using hv)
    have hzt : z * t ∈ principal z :=
      (principal z).mul_mem_right t (Ideal.mem_span_singleton_self z)
    have hone : (1 : O) ∈ principal z ⊔ n := by
      have h := (principal z ⊔ n).sub_mem
        ((show principal z ≤ principal z ⊔ n from le_sup_left) hzt)
        ((show n ≤ principal z ⊔ n from le_sup_right) hmem)
      convert h using 1 <;> ring
    exact (Ideal.isCoprime_iff_sup_eq.mpr ((Ideal.eq_top_iff_one _).mpr hone)).isRelPrime
  · intro hrel
    have hcop : IsCoprime (principal z) n := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      exact Ideal.isUnit_iff.mp (hrel
        (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hx
    have h := congrArg (Ideal.Quotient.mk n) hxy
    simp only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] at h
    exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk n t, h⟩

theorem expansion_sexticSymbol_zero_of_not_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : ¬ IsRelPrime (principal z) n) : sexticSymbol n z = 0 := by
  apply expansionSexticSymbol_eq_zero_of_nonunit c hn z
  exact fun h => hz ((expansion_isUnit_mk_iff_isRelPrime n z).mp h)


theorem expansion_sexticSymbol_norm_of_isRelPrime (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (u : O)
    (hu : IsRelPrime (principal u) n) : ‖sexticSymbol n u‖ = 1 := by
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1
  letI : Fintype (O ⧸ n) := Fintype.ofFinite _
  obtain ⟨v, hv⟩ := (expansion_isUnit_mk_iff_isRelPrime n u).mpr hu
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity
    ((expansionResidueCharacter c hn).apply_mem_rootsOfUnity v)
  simpa only [MulChar.coe_equivToUnitHom, hv, expansionResidueCharacter_apply_mk] using h

theorem expansion_sexticSymbol_mul_star (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (u : O) :
    sexticSymbol n u * star (sexticSymbol n u) =
      if IsRelPrime (principal u) n then 1 else 0 := by
  by_cases hu : IsRelPrime (principal u) n
  · rw [if_pos hu]
    simpa only [starRingEnd_apply, expansion_sexticSymbol_norm_of_isRelPrime c hn u hu,
      one_pow, Complex.ofReal_one] using Complex.mul_conj' (sexticSymbol n u)
  · rw [if_neg hu, expansion_sexticSymbol_zero_of_not_isRelPrime c hn u hu,
      star_zero, zero_mul]

theorem expansion_original_gcd_symbol_row (c : ArithmeticContext) {g a b : Ideal O}
    (hg : Outside c.S g) (u : O) :
    star (sexticSymbol (g * a) u) * sexticSymbol (g * b) u =
      if IsRelPrime (principal u) g then star (sexticSymbol a u) * sexticSymbol b u else 0 := by
  rw [expansion_sexticSymbol_mul, expansion_sexticSymbol_mul, star_mul]
  calc
    _ = (sexticSymbol g u * star (sexticSymbol g u)) *
        (star (sexticSymbol a u) * sexticSymbol b u) := by ring
    _ = _ := by
      rw [expansion_sexticSymbol_mul_star c hg u]
      split_ifs <;> simp only [one_mul, zero_mul]

theorem expansion_original_gcd_character_row (c : ArithmeticContext) (Φ : RowWeight)
    (H : ℝ) {g a b : Ideal O} (hg : Outside c.S g) :
    (∑' u : O, expansionOriginalCharacterRow Φ H (g * a) (g * b) u) =
      ∑' u : O, if IsRelPrime (principal u) g then
        star (sexticSymbol a u) * sexticSymbol b u * (Φ.value (normElement u / H) : ℂ) else 0 := by
  apply tsum_congr
  intro u
  unfold expansionOriginalCharacterRow
  rw [mul_assoc, expansion_original_gcd_symbol_row c hg]
  split_ifs
  · ring
  · rw [mul_zero]

/-- Poisson now applies to the actual gcd row of the original mean square. -/
theorem expansion_original_gcd_poisson_row (hp : PoissonStatement)
    (c : ArithmeticContext) (Φ : RowWeight) {a b g : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b)
    (hg : Outside c.S g) {H : ℝ} (hH : 0 < H) :
    (∑' u : O, expansionOriginalCharacterRow Φ H (g * a) (g * b) u) =
      (H : ℂ) * (expansionInversePairedCharacter c ha hb hab).gauss /
        (Real.sqrt (normIdeal a * normIdeal b) : ℂ) *
        ∑' d : Ideal O, if d ∣ outsideRadical ∅ g then
          (mobius d : ℂ) * (star (sexticSymbol a (chosenGenerator d)) *
            sexticSymbol b (chosenGenerator d)) / (normIdeal d : ℂ) *
            ∑' h : O, (sexticSymbol a h * star (sexticSymbol b h)) *
              radialFourier (fun x => (Φ.value x : ℂ))
                (H * normElement h / (normIdeal d * (normIdeal a * normIdeal b)))
        else 0 := by
  rw [expansion_original_gcd_character_row c Φ H hg]
  exact expansion_inverse_paired_poisson hp c Φ ha hb hab hg.1 hH


/-- The literal right side of the permitted Poisson identity. -/
def expansionPoissonDual (χ : PrimitiveResidueCharacter) (g : Ideal O)
    (Φ : RowWeight) (H : ℝ) : ℂ :=
  H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
    ∑' d : Ideal O, if d ∣ outsideRadical ∅ g then
      (mobius d : ℂ) * χ.value (chosenGenerator d) / (normIdeal d : ℂ) *
        ∑' h : O, star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
          (H * normElement h / (normIdeal d * normIdeal χ.modulus))
    else 0

def expansionOriginalPoissonTerm (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D H : ℝ) (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if ht : expansionGcdTripleAdmissible c t then
    star (expansionOriginalCoefficient c W D (t.1 * t.2.1)) *
      expansionOriginalCoefficient c W D (t.1 * t.2.2) *
        expansionPoissonDual (expansionInversePairedCharacter c ht.2.1 ht.2.2.1
          ht.2.2.2.2.2) t.1 Φ H
  else 0

theorem expansion_originalPoissonTerm_eq (hp : PoissonStatement)
    (c : ArithmeticContext) (Φ : RowWeight) (W : ℝ → ℂ) (D : ℝ)
    {H : ℝ} (hH : 0 < H) (t : Ideal O × Ideal O × Ideal O) :
    expansionOriginalPoissonTerm c Φ W D H t = expansionOriginalGcdTerm c Φ W D H t := by
  by_cases ht : expansionGcdTripleAdmissible c t
  · rw [expansionOriginalPoissonTerm, dif_pos ht, expansionOriginalGcdTerm, if_pos ht]
    congr 1
    rw [expansion_original_gcd_character_row c Φ H ht.1.1]
    exact (show (∑' u : O, if IsRelPrime (principal u) t.1 then
        star (sexticSymbol t.2.1 u) * sexticSymbol t.2.2 u *
          (Φ.value (normElement u / H) : ℂ) else 0) =
      expansionPoissonDual (expansionInversePairedCharacter c ht.2.1 ht.2.2.1 ht.2.2.2.2.2)
        t.1 Φ H from by
      simpa only [expansionPoissonDual, expansion_inversePairedCharacter_value] using
        hp (expansionInversePairedCharacter c ht.2.1 ht.2.2.1 ht.2.2.2.2.2) t.1
          (fun x => (Φ.value x : ℂ)) H ht.1.1.1 hH Φ.schwartz).symm
  · simp only [expansionOriginalPoissonTerm, dif_neg ht, expansionOriginalGcdTerm, if_neg ht]

theorem expansion_originalPoissonTerm_summable (hp : PoissonStatement)
    (c : ArithmeticContext) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Summable (expansionOriginalPoissonTerm c Φ W D H) := by
  apply (expansion_original_energy_gcd_row c Φ hW hD H).1.congr
  intro t
  exact (expansion_originalPoissonTerm_eq hp c Φ W D hH t).symm

/-- Genuine first Poisson expansion of the original smoothed mean square.
Only the original Poisson input is assumed; the finite ray and arithmetic
conversion of its Gauss factors remain separate obligations. -/
theorem expansion_original_energy_poisson (hp : PoissonStatement)
    (c : ArithmeticContext) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    (expansionSmoothedEnergy c Φ W D H : ℂ) =
      (D⁻¹ : ℂ) * ∑' t : Ideal O × Ideal O × Ideal O,
        expansionOriginalPoissonTerm c Φ W D H t := by
  rw [expansion_original_energy_gcd c Φ hW hD hH]
  congr 1
  apply tsum_congr
  intro t
  exact (expansion_originalPoissonTerm_eq hp c Φ W D hH t).symm


theorem expansion_primary_spec_and_primary (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : principal (primaryGenerator a) = a ∧ IsPrimary (primaryGenerator a) :=
  ⟨expansion_primary_spec c ha, expansion_primary_isPrimary c ha⟩

theorem expansion_prime_isRelPrime_three (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    IsRelPrime P (principal 3) := by
  apply hP.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hthree
  exact hout.2 P (c.above_three P hP hthree) (dvd_refl P)

theorem expansion_chosenGenerator_eq_prod (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) :
    chosenGenerator n = ((normalizedFactors n).map primaryGenerator).prod := by
  rw [chosenGenerator, ite_eq_right hn.1]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  exact ite_eq_left (expansion_prime_isRelPrime_three c
    (prime_of_normalized_factor P hP) (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors hn hP))

theorem expansion_isPrimary_multiset_prod (s : Multiset O)
    (hs : ∀ a ∈ s, IsPrimary a) : IsPrimary s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp [IsPrimary]
  | @cons a s ih =>
    rw [Multiset.prod_cons]
    exact expansion_isPrimary_mul (hs a (by simp))
      (ih (fun b hb => hs b (by simp [hb])))

/-- The fixed product of prime generators generates the full ideal and is
primary for every denominator outside S, including the empty product. -/
theorem expansion_chosenGenerator_spec_outside (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) :
    principal (chosenGenerator n) = n ∧ IsPrimary (chosenGenerator n) := by
  rw [expansion_chosenGenerator_eq_prod c hn]
  constructor
  · rw [principal, ← Ideal.multiset_prod_span_singleton, Multiset.map_map]
    calc
      ((normalizedFactors n).map (fun P =>
          Ideal.span {primaryGenerator P})).prod = (normalizedFactors n).prod := by
        apply congrArg Multiset.prod
        simpa only [principal, Multiset.map_id'] using
          (Multiset.map_congr rfl (fun P hP =>
            (expansion_primary_spec_and_primary c
              (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors hn hP)).1))
      _ = n := Ideal.prod_normalizedFactors_eq_self hn.1
  · apply expansion_isPrimary_multiset_prod
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    exact (expansion_primary_spec_and_primary c
      (SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors hn hP)).2

/-- The Poisson and frozen Gauss definitions use exactly the same generator
on the actual denominators outside S. -/
theorem expansion_chosenGenerator_eq_primaryGenerator (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) : chosenGenerator n = primaryGenerator n := by
  have hc := expansion_chosenGenerator_spec_outside c hn
  have hp := expansion_primary_spec_and_primary c hn
  exact expansion_primary_unique hc.2 hp.2 (hc.1.trans hp.1.symm)




def expansion_eisensteinPowerBasis : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

theorem expansion_eisensteinPowerBasis_dim : expansion_eisensteinPowerBasis.dim = 2 := by
  change (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

def expansion_eisensteinBasis : Module.Basis (Fin 2) ℤ O :=
  expansion_eisensteinPowerBasis.basis.reindex (finCongr expansion_eisensteinPowerBasis_dim)

theorem expansion_eisensteinBasis_zero : expansion_eisensteinBasis 0 = 1 := by
  rw [expansion_eisensteinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change expansion_eisensteinPowerBasis.gen ^ (0 : ℕ) = 1
  exact pow_zero _

theorem expansion_eisensteinBasis_one : expansion_eisensteinBasis 1 = omega := by
  rw [expansion_eisensteinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change expansion_eisensteinPowerBasis.gen ^ (1 : ℕ) = omega
  rw [pow_one]
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

theorem expansion_eisenstein_coords (a : O) :
    a = (expansion_eisensteinBasis.repr a 0 : O) + (expansion_eisensteinBasis.repr a 1 : O) * omega := by
  simpa [Fin.sum_univ_two, expansion_eisensteinBasis_zero, expansion_eisensteinBasis_one,
    Algebra.smul_def] using (expansion_eisensteinBasis.sum_repr a).symm

@[simp] theorem expansion_embedding_intCast (x : ℤ) : embedding (x : O) = (x : ℂ) := by
  simpa only [embeddingHom_apply] using map_intCast embeddingHom x

theorem expansion_embedding_omega_im : (embedding omega).im = Real.sqrt 3 / 2 := by
  let w := embedding omega
  have hp : w ^ 2 + w + 1 = 0 := by
    simpa only [embedding_add, embedding_pow, embedding_one, embedding_zero] using
      congrArg embedding omega_sq_add_omega_add_one
  have hr : w.re ^ 2 - w.im ^ 2 + w.re + 1 = 0 := by
    simpa only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
      Complex.zero_re] using congrArg Complex.re hp
  have hi : 2 * w.re * w.im + w.im = 0 := by
    have h := congrArg Complex.im hp
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im,
      Complex.zero_im] at h
    nlinarith
  have hne : w.im ≠ 0 := by
    intro h
    rw [h] at hr
    nlinarith [sq_nonneg (w.re + (1 : ℝ) / 2)]
  have hre : w.re = -(1 : ℝ) / 2 := by
    have hf : (2 * w.re + 1) * w.im = 0 := by nlinarith
    have hz := (mul_eq_zero.mp hf).resolve_right hne
    linarith
  have hnonneg : 0 ≤ w.im := by
    dsimp [w, embedding]
    split_ifs with h
    · exact h.le
    · simpa only [Complex.star_def, Complex.conj_im] using
        neg_nonneg.mpr (le_of_not_gt h)
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : w.im ^ 2 = (3 : ℝ) / 4 := by nlinarith
  change w.im = _
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

theorem expansion_additiveCharacter_add (z w : ℂ) :
    additiveCharacter (z + w) = additiveCharacter z * additiveCharacter w := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_im]
  push_cast
  ring

@[simp] theorem expansion_additiveCharacter_embedding (a : O) :
    additiveCharacter (embedding a) = 1 := by
  let y : ℤ := expansion_eisensteinBasis.repr a 1
  have him : (embedding a).im = (y : ℝ) * Real.sqrt 3 / 2 := by
    rw [expansion_eisenstein_coords a, embedding_add, embedding_mul,
      expansion_embedding_intCast, expansion_embedding_intCast]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, zero_add, add_zero, expansion_embedding_omega_im]
    dsimp [y]
    ring
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hexp : 4 * Real.pi * (embedding a).im / Real.sqrt 3 =
      (y : ℝ) * (2 * Real.pi) := by
    rw [him]
    field_simp [hs]
    <;> ring
  rw [additiveCharacter, hexp]
  push_cast
  simpa only [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I y

theorem expansion_additiveCharacter_add_embedding (z : ℂ) (a : O) :
    additiveCharacter (z + embedding a) = additiveCharacter z := by
  rw [expansion_additiveCharacter_add, expansion_additiveCharacter_embedding, mul_one]

@[simp] theorem expansion_additiveCharacter_zero : additiveCharacter 0 = 1 := by
  simp [additiveCharacter]

/-- The additive phase is unchanged by any change of integral representative
modulo its nonzero principal denominator. -/
theorem expansion_gauss_additive_div_congr {g x y : O} (hg : g ≠ 0)
    (hxy : Ideal.Quotient.mk (principal g) x = Ideal.Quotient.mk (principal g) y) :
    additiveCharacter (embedding x / embedding g) =
      additiveCharacter (embedding y / embedding g) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hxy)
  have hx : x = y + g * z := by linear_combination hz
  have hg' : embedding g ≠ 0 := fun h => hg (embedding_eq_zero.mp h)
  have harg : embedding x / embedding g = embedding y / embedding g + embedding z := by
    rw [hx, embedding_add, embedding_mul]
    field_simp [hg']
  rw [harg, expansion_additiveCharacter_add_embedding]



theorem expansion_gauss_crt_generator_isUnit (a b : Ideal O)
    (hab : IsCoprime a b) (B : O) (hB : principal B = b) :
    IsUnit (Ideal.Quotient.mk a B) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hab.exists
  rw [← hB] at hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hy
  have h := congrArg (Ideal.Quotient.mk a) hxy
  simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    zero_add, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk a t, h⟩

/-- Reindexing by the actual Chinese-remainder bijection after multiplying
the two quotient coordinates by the opposite generators. -/
theorem expansion_gauss_crt_reindex (a b : Ideal O) (hab : IsCoprime a b)
    (A B : O) (hA : principal A = a) (hB : principal B = b)
    [Fintype (O ⧸ a)] [Fintype (O ⧸ b)] [Fintype (O ⧸ (a * b))]
    (f : O ⧸ (a * b) → ℂ) :
    (∑ x : O ⧸ (a * b), f x) =
      ∑ u : O ⧸ a, ∑ v : O ⧸ b,
        f (Ideal.Quotient.mk (a * b) (B * residueLift a u + A * residueLift b v)) := by
  let hBa := expansion_gauss_crt_generator_isUnit a b hab B hB
  let hAb := expansion_gauss_crt_generator_isUnit b a hab.symm A hA
  let base := Ideal.quotientMulEquivQuotientProd a b hab
  let e : (O ⧸ a) × (O ⧸ b) ≃ O ⧸ (a * b) :=
    (hBa.unit.mulLeft.prodCongr hAb.unit.mulLeft).trans base.toEquiv.symm
  have hAzero : Ideal.Quotient.mk a A = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hA]
    exact Ideal.mem_span_singleton_self A
  have hBzero : Ideal.Quotient.mk b B = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hB]
    exact Ideal.mem_span_singleton_self B
  have he (u : O ⧸ a) (v : O ⧸ b) : e (u, v) =
      Ideal.Quotient.mk (a * b) (B * residueLift a u + A * residueLift b v) := by
    apply base.injective
    change base (base.symm (hBa.unit * u, hAb.unit * v)) = _
    rw [base.apply_symm_apply]
    apply Prod.ext
    · change hBa.unit * u = (Ideal.quotientMulEquivQuotientProd a b hab
        (Ideal.Quotient.mk (a * b) _)).1
      rw [Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
      simp only [map_add, map_mul, hAzero, zero_mul, add_zero,
        expansionResidueLift_spec, IsUnit.unit_spec]
    · change hAb.unit * v = (Ideal.quotientMulEquivQuotientProd a b hab
        (Ideal.Quotient.mk (a * b) _)).2
      rw [Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
      simp only [map_add, map_mul, hBzero, zero_mul, zero_add,
        expansionResidueLift_spec, IsUnit.unit_spec]
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [he]

theorem expansion_gauss_crt_paired_value (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (u v : O) :
    expansionPairedResidueCharacter c ha hb hab
      (Ideal.Quotient.mk (a * b)
        (primaryGenerator b * u + primaryGenerator a * v)) =
      (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) *
        (sexticSymbol a u * star (sexticSymbol b v)) := by
  have hAzero : Ideal.Quotient.mk a (primaryGenerator a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : primaryGenerator a ∈ principal (primaryGenerator a) :=
      Ideal.mem_span_singleton_self _
    rw [(expansion_primary_spec_and_primary c ha).1] at hm
    exact hm
  have hBzero : Ideal.Quotient.mk b (primaryGenerator b) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : primaryGenerator b ∈ principal (primaryGenerator b) :=
      Ideal.mem_span_singleton_self _
    rw [(expansion_primary_spec_and_primary c hb).1] at hm
    exact hm
  have hleft : sexticSymbol a (primaryGenerator b * u + primaryGenerator a * v) =
      sexticSymbol a (primaryGenerator b) * sexticSymbol a u := by
    rw [← expansionResidueCharacter_apply_mk c ha]
    simp only [map_add, map_mul, hAzero, zero_mul, add_zero,
      expansionResidueCharacter_apply_mk]
  have hright : sexticSymbol b (primaryGenerator b * u + primaryGenerator a * v) =
      sexticSymbol b (primaryGenerator a) * sexticSymbol b v := by
    rw [← expansionResidueCharacter_apply_mk c hb]
    simp only [map_add, map_mul, hBzero, zero_mul, zero_add,
      expansionResidueCharacter_apply_mk]
  rw [expansionPairedResidueCharacter_apply_mk, hleft, hright, star_mul]
  ring

/-- Complex conjugation is exactly the frozen negative first power,
including the zero extension at nonunits. -/
theorem expansion_gauss_sextic_star_eq_neg_one (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O) :
    star (sexticSymbol n x) = sexticSymbol n x ^ (-1 : ℤ) := by
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1
  rw [← expansionResidueCharacter_apply_mk c hn,
    MulChar.star_apply', MulChar.inv_apply_eq_inv', zpow_neg_one]



/-- The additive factor appearing in the frozen ideal Gauss sums. -/
def expansionGaussPhase (n : Ideal O) (x : O ⧸ n) : ℂ :=
  additiveCharacter (embedding (residueLift n x) / embedding (primaryGenerator n))

theorem expansion_gauss_phase_apply_mk (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O) :
    expansionGaussPhase n (Ideal.Quotient.mk n x) =
      additiveCharacter (embedding x / embedding (primaryGenerator n)) := by
  have hgen := (expansion_primary_spec_and_primary c hn).1
  have hne : primaryGenerator n ≠ 0 := by
    intro h
    apply hn.1
    rw [← hgen, h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  apply expansion_gauss_additive_div_congr hne
  rw [hgen]
  exact expansionResidueLift_spec n _

theorem expansion_gauss_phase_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (u v : O) :
    expansionGaussPhase (a * b) (Ideal.Quotient.mk (a * b)
      (primaryGenerator b * u + primaryGenerator a * v)) =
      additiveCharacter (embedding u / embedding (primaryGenerator a)) *
        additiveCharacter (embedding v / embedding (primaryGenerator b)) := by
  have hab := (expansion_outside_mul c a b).mpr ⟨ha, hb⟩
  have hne (n : Ideal O) (hn : Outside c.S n) : embedding (primaryGenerator n) ≠ 0 := by
    intro h
    apply hn.1
    rw [← (expansion_primary_spec_and_primary c hn).1,
      embedding_eq_zero.mp h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  rw [expansion_gauss_phase_apply_mk c hab,
    expansion_primary_mul c ha hb,
    embedding_add, embedding_mul, embedding_mul, embedding_mul]
  have harg :
      (embedding (primaryGenerator b) * embedding u +
        embedding (primaryGenerator a) * embedding v) /
        (embedding (primaryGenerator a) * embedding (primaryGenerator b)) =
      embedding u / embedding (primaryGenerator a) +
        embedding v / embedding (primaryGenerator b) := by
    field_simp [hne a ha, hne b hb]
  rw [harg, expansion_additiveCharacter_add]

/-- Exact factorization before normalizing, valid also for unit-ideal
quotients and for any chosen finite enumerations of the quotients. -/
theorem expansion_paired_gauss_crt_sum (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    [Fintype (O ⧸ a)] [Fintype (O ⧸ b)] [Fintype (O ⧸ (a * b))] :
    (∑ x : O ⧸ (a * b), expansionPairedResidueCharacter c ha hb hab x *
      expansionGaussPhase (a * b) x) =
      (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) *
        (∑ u : O ⧸ a, sexticSymbol a (residueLift a u) * expansionGaussPhase a u) *
        (∑ v : O ⧸ b, star (sexticSymbol b (residueLift b v)) * expansionGaussPhase b v) := by
  rw [expansion_gauss_crt_reindex a b
    (expansion_ideal_isCoprime_of_isRelPrime hab)
    (primaryGenerator a) (primaryGenerator b)
    (expansion_primary_spec_and_primary c ha).1
    (expansion_primary_spec_and_primary c hb).1]
  simp_rw [expansion_gauss_crt_paired_value c ha hb hab,
    expansion_gauss_phase_crt c ha hb]
  simp only [expansionGaussPhase, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring



theorem expansion_gauss_sqrt_norm_inv_mul (a b : Ideal O) :
    (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ =
      (Real.sqrt (normIdeal a) : ℂ)⁻¹ * (Real.sqrt (normIdeal b) : ℂ)⁻¹ := by
  simp only [normIdeal, map_mul, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, mul_inv]

/-- The exact normalized CRT identity for the literal paired character.
No primitivity or nontriviality assumption on the quotient is needed. -/
theorem expansion_paired_gauss_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    [Fintype (O ⧸ (a * b))] :
    (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ *
      (∑ x : O ⧸ (a * b), expansionPairedResidueCharacter c ha hb hab x *
        additiveCharacter (embedding (residueLift (a * b) x) /
          embedding (chosenGenerator (a * b)))) =
      sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
        gauss 1 a * gauss (-1) b := by
  letI : Finite (O ⧸ a) := Ring.HasFiniteQuotients.finiteQuotient ha.1
  letI : Finite (O ⧸ b) := Ring.HasFiniteQuotients.finiteQuotient hb.1
  letI : Fintype (O ⧸ a) := Fintype.ofFinite _
  letI : Fintype (O ⧸ b) := Fintype.ofFinite _
  have hout := (expansion_outside_mul c a b).mpr ⟨ha, hb⟩
  rw [expansion_chosenGenerator_eq_primaryGenerator c hout]
  change (Real.sqrt (normIdeal (a * b)) : ℂ)⁻¹ *
    (∑ x : O ⧸ (a * b), expansionPairedResidueCharacter c ha hb hab x *
      expansionGaussPhase (a * b) x) = _
  rw [expansion_paired_gauss_crt_sum c ha hb hab,
    expansion_gauss_sqrt_norm_inv_mul]
  simp_rw [expansion_gauss_sextic_star_eq_neg_one c hb]
  simp only [gauss, dif_pos ha.1, dif_pos hb.1, zpow_one, expansionGaussPhase]
  ring

/-- The preceding finite-sum formula is precisely the Gauss sum attached
to the concrete primitive character for a squarefree coprime pair. -/
theorem expansion_primitive_paired_gauss_crt (c : ArithmeticContext)
    {a b : Ideal O} (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    (expansionPrimitivePairedCharacter c ha hb hab).gauss =
      sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
        gauss 1 a * gauss (-1) b := by
  letI : Finite (O ⧸ (a * b)) :=
    Ring.HasFiniteQuotients.finiteQuotient (mul_ne_zero ha.1.1 hb.1.1)
  letI : Fintype (O ⧸ (a * b)) := Fintype.ofFinite _
  exact expansion_paired_gauss_crt c ha.1 hb.1 hab

/-- Exact CRT factorization of the literal inverse paired Gauss sum used in
`expansion_original_energy_poisson`, including unit-ideal denominators. -/
theorem expansion_inverse_paired_gauss_crt (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b) :
    (expansionInversePairedCharacter c ha hb hab).gauss =
      sexticSymbol b (primaryGenerator a) * star (sexticSymbol a (primaryGenerator b)) *
        gauss 1 b * gauss (-1) a :=
  expansion_primitive_paired_gauss_crt c hb ha hab.symm


theorem expansion_norm_alpha_eq_one (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : ‖alpha n‖ = 1 := by
  have h : embedding (primaryGenerator n) ≠ 0 :=
    fun hz => expansion_primary_ne_zero c hn (embedding_eq_zero.mp hz)
  simp only [alpha, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]

theorem expansion_mobius_sq {n : Ideal O} (hn : Squarefree n) :
    (mobius n : ℂ) ^ 2 = 1 := by
  simp [mobius, hn.moebius_eq, ← pow_mul, Nat.mul_comm]

theorem expansion_norm_mobius_eq_one {n : Ideal O} (hn : Squarefree n) :
    ‖(mobius n : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (expansion_mobius_sq hn) (by decide)

theorem expansion_norm_sexticSymbol_of_unit (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk n z)) : ‖sexticSymbol n z‖ = 1 := by
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1
  letI : Fintype (O ⧸ n) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hz
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity
    ((expansionResidueCharacter c hn).apply_mem_rootsOfUnity u)
  simpa only [MulChar.coe_equivToUnitHom, hu,
    expansionResidueCharacter_apply_mk] using h

theorem expansion_primaryGenerator_unit_of_isRelPrime (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b)
    (hab : IsRelPrime a b) : IsUnit (Ideal.Quotient.mk a (primaryGenerator b)) := by
  have hcop : IsCoprime a b := by
    apply Ideal.coprime_of_no_prime_ge
    intro p hap hbp hp
    have hp0 : p ≠ ⊥ := by
      intro h
      exact ha.1 (le_bot_iff.mp (h ▸ hap))
    exact (Ideal.prime_of_isPrime hp0 hp).not_unit
      (hab (Ideal.dvd_iff_le.mpr hap) (Ideal.dvd_iff_le.mpr hbp))
  obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
  rw [← expansion_primary_spec c hb] at hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hy
  have h := congrArg (Ideal.Quotient.mk a) hxy
  simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    zero_add, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk a t, h⟩

theorem expansion_norm_gauss_two (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {n : Ideal O} (hn : SquarefreeOutside c.S n) :
    ‖gauss 2 n‖ = 1 := by
  obtain ⟨G, R, _, _, _, _, _, _, _, hgauss, _, _⟩ := hc
  have h := congrArg norm (hgauss n hn).1
  rw [norm_pow, norm_mul, expansion_norm_mobius_eq_one hn.2,
    expansion_norm_alpha_eq_one c hn.1, mul_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    (h.trans (one_pow 3).symm)

/-- The explicit expression that the separate CRT Gauss calculation must
identify with the normalized Gauss sum of the paired primitive character. -/
def expansionPairedGaussFactor (a b : Ideal O) : ℂ :=
  sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
    gauss 1 a * gauss (-1) b

theorem expansion_coefficient_pairedGaussFactor (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    coefficient ξ.val a * star (coefficient ξ.val b) * expansionPairedGaussFactor a b =
      (mobius a : ℂ) * (mobius b : ℂ) *
        (rayValue ξ.val a * star (rayValue ξ.val b)) *
          reciprocityG c hc (idealClass c a * (idealClass c b)⁻¹) := by
  obtain ⟨R, hG, hsign, hsym, _, _, _, hrec, hgauss, _, hquot⟩ := Classical.choose_spec hc
  let G := reciprocityG c hc
  have hcross : sexticSymbol a (primaryGenerator b) *
      star (sexticSymbol b (primaryGenerator a)) = R (idealClass c a) (idealClass c b) := by
    rw [hrec a b ha.1 hb.1 hab, star_mul]
    have hn : ‖sexticSymbol a (primaryGenerator b)‖ = 1 :=
      expansion_norm_sexticSymbol_of_unit c ha.1 _
        (expansion_primaryGenerator_unit_of_isRelPrime c ha.1 hb.1 hab)
    have hunit : sexticSymbol a (primaryGenerator b) *
        star (sexticSymbol a (primaryGenerator b)) = 1 := by
      simpa only [starRingEnd_apply, hn, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (sexticSymbol a (primaryGenerator b))
    rcases hsign (idealClass c a) (idealClass c b) with h | h <;>
      simp only [h, star_one, star_neg, one_mul, mul_one, mul_neg] <;> simpa using hunit
  have hα : star (alpha b) * alpha b = 1 := by
    simpa only [starRingEnd_apply, expansion_norm_alpha_eq_one c hb.1,
      one_pow, Complex.ofReal_one] using Complex.conj_mul' (alpha b)
  have hg₂ : gauss 2 b * star (gauss 2 b) = 1 := by
    simpa only [starRingEnd_apply, expansion_norm_gauss_two c hc hb,
      one_pow, Complex.ofReal_one] using Complex.mul_conj' (gauss 2 b)
  have hGb : (G (idealClass c b))⁻¹ = star (G (idealClass c b)) :=
    Complex.inv_eq_conj (hG (idealClass c b))
  have hbminus : alpha b * star (gauss 2 b) * gauss (-1) b =
      (mobius b : ℂ) * sexticSymbol b (-1) * star (G (idealClass c b)) := by
    calc
      _ = (mobius b : ℂ) * ((mobius b : ℂ) * gauss (-1) b) *
          (alpha b * star (gauss 2 b)) := by
        rw [show (mobius b : ℂ) * ((mobius b : ℂ) * gauss (-1) b) =
          (mobius b : ℂ) ^ 2 * gauss (-1) b by ring,
          expansion_mobius_sq hb.2, one_mul]
        ring
      _ = (mobius b : ℂ) *
          (sexticSymbol b (-1) * (G (idealClass c b))⁻¹ * star (alpha b) * gauss 2 b) *
          (alpha b * star (gauss 2 b)) := by
        rw [(hgauss b hb).2.2.2.2.2]
        rfl
      _ = ((mobius b : ℂ) * sexticSymbol b (-1) * star (G (idealClass c b))) *
          (star (alpha b) * alpha b) * (gauss 2 b * star (gauss 2 b)) := by
        rw [hGb]
        ring
      _ = _ := by rw [hα, hg₂, mul_one, mul_one]
  have hga : star (alpha a) * gauss 2 a * gauss 1 a =
      (mobius a : ℂ) * G (idealClass c a) := (hgauss a ha).2.2.2.2.1
  have hq : sexticSymbol b (-1) * star (G (idealClass c b)) * G (idealClass c a) *
      R (idealClass c a) (idealClass c b) =
        G (idealClass c a * (idealClass c b)⁻¹) := by
    rw [hsym (idealClass c a) (idealClass c b)]
    exact hquot b a hb.1 ha.1
  unfold coefficient expansionPairedGaussFactor
  rw [star_mul, star_mul, star_star]
  calc
    _ = (star (alpha a) * gauss 2 a * gauss 1 a) *
        (alpha b * star (gauss 2 b) * gauss (-1) b) *
        (rayValue ξ.val a * star (rayValue ξ.val b)) *
        (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) := by ring
    _ = ((mobius a : ℂ) * G (idealClass c a)) *
        ((mobius b : ℂ) * sexticSymbol b (-1) * star (G (idealClass c b))) *
        (rayValue ξ.val a * star (rayValue ξ.val b)) * R (idealClass c a) (idealClass c b) := by
      rw [hga, hbminus, hcross]
    _ = (mobius a : ℂ) * (mobius b : ℂ) * (rayValue ξ.val a * star (rayValue ξ.val b)) *
        (sexticSymbol b (-1) * star (G (idealClass c b)) * G (idealClass c a) *
          R (idealClass c a) (idealClass c b)) := by ring
    _ = _ := by rw [hq]

def expansionBaseCoefficient (n : Ideal O) : ℂ := star (alpha n) * gauss 2 n

theorem expansion_baseCoefficient_norm (c : ArithmeticContext) (hc : ArithmeticRelations c)
    {n : Ideal O} (hn : SquarefreeOutside c.S n) : ‖expansionBaseCoefficient n‖ = 1 := by
  rw [expansionBaseCoefficient, norm_mul, norm_star,
    expansion_norm_alpha_eq_one c hn.1, expansion_norm_gauss_two c hc hn, mul_one]

/-- Arithmetic conversion of the actual inverse paired Gauss sum, after CRT. -/
theorem expansion_inverse_gauss_baseCoefficient (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b) (hab : IsRelPrime a b) :
    (mobius a : ℂ) * (mobius b : ℂ) * (expansionInversePairedCharacter c ha hb hab).gauss =
      expansionBaseCoefficient a * star (expansionBaseCoefficient b) *
        reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) := by
  let ξ := expansion_rayCharacterFromHom c (1 : RayClass c →* ℂ)
  have hξ (n : Ideal O) (hn : Outside c.S n) : rayValue ξ.val n = 1 := by
    exact expansion_rayCharacterFromHom_rayValue c (1 : RayClass c →* ℂ) hn
  have h := expansion_coefficient_pairedGaussFactor c hc ξ hb ha hab.symm
  simp only [coefficient, hξ a ha.1, hξ b hb.1, mul_one, star_one, one_mul] at h
  change expansionBaseCoefficient b * star (expansionBaseCoefficient a) *
      expansionPairedGaussFactor b a = (mobius b : ℂ) * (mobius a : ℂ) *
        reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹) at h
  have hA : expansionBaseCoefficient a * star (expansionBaseCoefficient a) = 1 := by
    simpa only [starRingEnd_apply, expansion_baseCoefficient_norm c hc ha,
      one_pow, Complex.ofReal_one] using Complex.mul_conj' (expansionBaseCoefficient a)
  have hB : star (expansionBaseCoefficient b) * expansionBaseCoefficient b = 1 := by
    simpa only [starRingEnd_apply, expansion_baseCoefficient_norm c hc hb,
      one_pow, Complex.ofReal_one] using Complex.conj_mul' (expansionBaseCoefficient b)
  rw [expansion_inverse_paired_gauss_crt]
  change (mobius a : ℂ) * (mobius b : ℂ) * expansionPairedGaussFactor b a = _
  calc
    _ = (expansionBaseCoefficient a * star (expansionBaseCoefficient b)) *
        (expansionBaseCoefficient b * star (expansionBaseCoefficient a) *
          expansionPairedGaussFactor b a) * ((mobius a : ℂ) * (mobius b : ℂ)) := by
      calc
        _ = ((mobius a : ℂ) * (mobius b : ℂ)) * expansionPairedGaussFactor b a *
            (expansionBaseCoefficient a * star (expansionBaseCoefficient a)) *
            (star (expansionBaseCoefficient b) * expansionBaseCoefficient b) := by rw [hA, hB, mul_one, mul_one]
        _ = _ := by ring
    _ = _ := by
      rw [h]
      have hm : (mobius a : ℂ) * (mobius b : ℂ) *
          ((mobius b : ℂ) * (mobius a : ℂ)) = 1 := by
        calc
          _ = (mobius a : ℂ) ^ 2 * (mobius b : ℂ) ^ 2 := by ring
          _ = 1 := by rw [expansion_mobius_sq ha.2, expansion_mobius_sq hb.2, mul_one]
      calc
        _ = (expansionBaseCoefficient a * star (expansionBaseCoefficient b) *
            reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹)) *
              ((mobius a : ℂ) * (mobius b : ℂ) * ((mobius b : ℂ) * (mobius a : ℂ))) := by ring
        _ = _ := by rw [hm, mul_one]

/-- The precise paired Gauss identity of the initial Poisson reduction, with
one actual finite ray family fixed before all tests, scales, and ideal pairs. -/
theorem expansion_initial_paired_gauss_identity (c : ArithmeticContext)
    (hc : ArithmeticRelations c) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ),
      ∀ (a b : Ideal O) (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
        (hab : IsRelPrime a b),
        (mobius a : ℂ) * (mobius b : ℂ) * star (c.nu.onIdeal a) * c.nu.onIdeal b *
          (expansionInversePairedCharacter c ha hb hab).gauss =
          ∑ ξ ∈ Ξ, coeffs ξ * coefficient ξ.val a * star (coefficient ξ.val b) := by
  obtain ⟨Ξ, coeffs, h⟩ := expansion_initial_ray_expansion_onIdeals c hc
  refine ⟨Ξ, coeffs, ?_⟩
  intro a b ha hb hab
  calc
    _ = ((mobius a : ℂ) * (mobius b : ℂ) *
        (expansionInversePairedCharacter c ha hb hab).gauss) *
          (star (c.nu.onIdeal a) * c.nu.onIdeal b) := by ring
    _ = (expansionBaseCoefficient a * star (expansionBaseCoefficient b)) *
        (star (c.nu.onIdeal a) * c.nu.onIdeal b *
          reciprocityG c hc (idealClass c b * (idealClass c a)⁻¹)) := by
      rw [expansion_inverse_gauss_baseCoefficient c hc ha hb hab]
      ring
    _ = _ := by
      rw [h a b ha.1 hb.1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ hξ
      unfold expansionBaseCoefficient coefficient
      simp only [star_mul]
      ring

end QRHShort.CloudBatch

section
/- Frozen original Poisson expansion fragment PoissonExpansionCommonCoefficients.lean SHA256 b0d454007a2b5aeb235acbb5ed2576db59f3f1e48d08aeaf590400ff85294e8e -/


noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.CloudBatch
open PoissonReductionProof

theorem expansion_rayValue_norm_one (c : ArithmeticContext) (ξ : RayCharacter c)
    {a : Ideal O} (ha : Outside c.S a) : ‖rayValue ξ.val a‖ = 1 := by
  letI : Finite (O ⧸ c.rayModulus) := Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  letI : Fintype (O ⧸ c.rayModulus) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := expansion_primaryGenerator_unit_rayModulus c ha
  have hn := Complex.norm_eq_one_of_mem_rootsOfUnity
    ((expansion_residueAtRayModulus c ξ).apply_mem_rootsOfUnity u)
  simpa only [MulChar.coe_equivToUnitHom, hu,
    expansion_residueAtRayModulus_onElement, rayValue] using hn

theorem expansion_coefficient_norm_one (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) {a : Ideal O} (ha : SquarefreeOutside c.S a) :
    ‖coefficient ξ.val a‖ = 1 := by
  change ‖expansionBaseCoefficient a * rayValue ξ.val a‖ = 1
  rw [norm_mul, expansion_baseCoefficient_norm c hc ha,
    expansion_rayValue_norm_one c ξ ha.1, mul_one]

theorem expansion_sextic_six (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (x : O) (hx : IsRelPrime (principal x) n) :
    sexticSymbol n x ^ (6 : ℕ) = 1 := by
  unfold sexticSymbol
  rw [if_neg hn.1, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  have hp : Prime P := prime_of_normalized_factor P hP
  have hout := SquarefreeReflection.RayValuePrerequisites.outside_of_mem_normalizedFactors hn hP
  have hζ := SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
    c hp hout
  have hxP : x ∉ P := fun h => hp.not_unit
    (hx (Ideal.dvd_span_singleton.mpr h) (dvd_of_mem_normalizedFactors hP))
  obtain ⟨j, hj, he⟩ := SquarefreeReflection.sexticAtPrime_index hp hζ hxP
  rw [SquarefreeReflection.RayValuePrerequisites.sexticAtPrime_eq_of_test hζ hj he]
  rw [← embedding_pow, ← pow_mul, Nat.mul_comm j 6, pow_mul, rootSix_pow_six,
    one_pow, embedding_one]

theorem expansion_sextic_star_five (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) (x : O) :
    star (sexticSymbol n x) = sexticSymbol n x ^ (5 : ℕ) := by
  by_cases hx : IsRelPrime (principal x) n
  · have h6 := expansion_sextic_six c hn x hx
    have hu : sexticSymbol n x * star (sexticSymbol n x) = 1 := by
      rw [expansion_sexticSymbol_mul_star c hn, if_pos hx]
    calc
      _ = star (sexticSymbol n x) * sexticSymbol n x ^ 6 := by rw [h6, mul_one]
      _ = (sexticSymbol n x * star (sexticSymbol n x)) * sexticSymbol n x ^ 5 := by ring
      _ = _ := by rw [hu, one_mul]
  · rw [expansion_sexticSymbol_zero_of_not_isRelPrime c hn x hx]
    simp

/-- The literal column after the paired Gauss conversion and before
coprimality inversion. Its squarefree and common-gcd exclusions are retained. -/
def expansionPreColumn (c : ArithmeticContext) (ξ : RayCharacter c)
    (g e : Ideal O) (h : O) (n : Ideal O) : ℂ :=
  if SquarefreeOutside c.S n ∧ IsRelPrime n g then
    coefficient ξ.val n * star (sexticSymbol n (primaryGenerator e)) * sexticSymbol n h
  else 0

def expansionCommonColumnScalar (c : ArithmeticContext) (ξ : RayCharacter c)
    (e v : Ideal O) (h : O) : ℂ :=
  coefficient ξ.val v * star (sexticSymbol v (primaryGenerator e)) * sexticSymbol v h

/-- Common-factor extraction with every exclusion proved, including when a
remaining column meets e or v. Those forbidden columns vanish in the original
initialAtom through the actual zero extension of the sextic symbol. -/
theorem expansion_preColumn_common_factor (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) {b e v : Ideal O}
    (hb : SquarefreeOutside c.S b) (he : SquarefreeOutside c.S e)
    (hv : SquarefreeOutside c.S v) (hbe : IsRelPrime b e)
    (hbv : IsRelPrime b v) (hev : IsRelPrime e v) (h : O) (n : Ideal O) :
    expansionPreColumn c ξ (e * b) e h (v * n) =
      expansionCommonColumnScalar c ξ e v h *
        initialAtom c ξ b (e * v) (primaryGenerator e * h) n := by
  obtain ⟨G, R, hG, hR, hRs, hRl, hRr, hGm, hrec, hgauss, hcoeff, hquot⟩ := hc
  by_cases hs : SquarefreeOutside c.S (v * n) ∧ IsRelPrime (v * n) (e * b)
  · have hndiv : n ∣ v * n := ⟨v, mul_comm _ _⟩
    have hn : SquarefreeOutside c.S n :=
      ⟨expansion_outside_of_dvd c hs.1.1 hndiv, hs.1.2.squarefree_of_dvd hndiv⟩
    have hvn : IsRelPrime v n := IsRelPrime.of_squarefree_mul hs.1.2
    have hnbe : IsRelPrime n (e * b) := hs.2.of_dvd_left hndiv
    have hnb : IsRelPrime n b := hnbe.of_dvd_right ⟨e, mul_comm _ _⟩
    rw [expansionPreColumn, if_pos hs, initialAtom, if_pos ⟨hn, hnb⟩,
      hcoeff ξ v n hv hn hvn, expansion_sexticSymbol_mul, expansion_sexticSymbol_mul,
      star_mul, expansion_primary_mul c he.1 hv.1,
      SquarefreeReflection.sexticSymbol_mul_numerator c hn.1,
      SquarefreeReflection.sexticSymbol_mul_numerator c hn.1,
      expansion_sextic_star_five c hn.1]
    unfold expansionCommonColumnScalar
    ring
  · rw [expansionPreColumn, if_neg hs]
    by_cases hn : SquarefreeOutside c.S n
    · by_cases hnb : IsRelPrime n b
      · have hnf : ¬ IsRelPrime n (e * v) := by
          intro hnf
          have hne : IsRelPrime n e := hnf.of_dvd_right ⟨v, rfl⟩
          have hnv : IsRelPrime n v := hnf.of_dvd_right ⟨e, mul_comm _ _⟩
          apply hs
          exact ⟨⟨(expansion_outside_mul c v n).mpr ⟨hv.1, hn.1⟩,
            squarefree_mul_iff.mpr ⟨hnv.symm, hv.2, hn.2⟩⟩,
            (hev.symm.mul_right hbv.symm).mul_left (hne.mul_right hnb)⟩
        have hzero : sexticSymbol n (primaryGenerator (e * v)) = 0 := by
          apply expansion_sexticSymbol_zero_of_not_isRelPrime c hn.1
          rw [expansion_primary_spec c ((expansion_outside_mul c e v).mpr ⟨he.1, hv.1⟩)]
          exact fun hh => hnf hh.symm
        rw [initialAtom, if_pos (show SquarefreeOutside c.S n ∧ IsRelPrime n b from ⟨hn, hnb⟩), hzero]
        simp only [zero_pow (by decide : 4 ≠ 0), mul_zero]
      · simp only [initialAtom, hn, hnb, and_false, if_false, mul_zero]
    · simp only [initialAtom, hn, false_and, if_false, mul_zero]

theorem expansion_commonColumnScalar_mul_star (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {e v : Ideal O}
    (he : SquarefreeOutside c.S e) (hv : SquarefreeOutside c.S v)
    (hev : IsRelPrime e v) (h : O) :
    expansionCommonColumnScalar c ξ e v h * star (expansionCommonColumnScalar c ξ e v h) =
      if IsRelPrime v (principal h) then 1 else 0 := by
  have hC : coefficient ξ.val v * star (coefficient ξ.val v) = 1 := by
    simpa only [starRingEnd_apply, expansion_coefficient_norm_one c hc ξ hv,
      one_pow, Complex.ofReal_one] using Complex.mul_conj' (coefficient ξ.val v)
  have hrel : IsRelPrime (principal (primaryGenerator e)) v := by
    rw [expansion_primary_spec c he.1]
    exact hev
  calc
    _ = (coefficient ξ.val v * star (coefficient ξ.val v)) *
        (sexticSymbol v (primaryGenerator e) * star (sexticSymbol v (primaryGenerator e))) *
        (sexticSymbol v h * star (sexticSymbol v h)) := by
      simp only [expansionCommonColumnScalar, star_mul, star_star]
      ring
    _ = if IsRelPrime (principal h) v then 1 else 0 := by
      rw [hC, expansion_sexticSymbol_mul_star c hv.1, if_pos hrel,
        expansion_sexticSymbol_mul_star c hv.1, one_mul, one_mul]
    _ = _ := by
      by_cases hh : IsRelPrime v (principal h)
      · rw [if_pos hh, if_pos hh.symm]
      · rw [if_neg hh, if_neg (fun hh' => hh hh'.symm)]

/-- Exact cancellation of the common coefficient and common character in
the genuine paired column. The surviving coprimality is exactly the one in
ExpansionRawAdmissible, and both output columns are the frozen initialAtom. -/
theorem expansion_paired_common_factor (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) {b e v : Ideal O}
    (hb : SquarefreeOutside c.S b) (he : SquarefreeOutside c.S e)
    (hv : SquarefreeOutside c.S v) (hbe : IsRelPrime b e)
    (hbv : IsRelPrime b v) (hev : IsRelPrime e v) (h : O) (n₁ n₂ : Ideal O) :
    expansionPreColumn c ξ (e * b) e h (v * n₁) *
      star (expansionPreColumn c ξ (e * b) e h (v * n₂)) =
      if IsRelPrime v (principal h) then
        initialAtom c ξ b (e * v) (primaryGenerator e * h) n₁ *
          star (initialAtom c ξ b (e * v) (primaryGenerator e * h) n₂)
      else 0 := by
  rw [expansion_preColumn_common_factor c hc ξ hb he hv hbe hbv hev,
    expansion_preColumn_common_factor c hc ξ hb he hv hbe hbv hev, star_mul]
  calc
    _ = (expansionCommonColumnScalar c ξ e v h * star (expansionCommonColumnScalar c ξ e v h)) *
        (initialAtom c ξ b (e * v) (primaryGenerator e * h) n₁ *
          star (initialAtom c ξ b (e * v) (primaryGenerator e * h) n₂)) := by ring
    _ = _ := by
      rw [expansion_commonColumnScalar_mul_star c hc ξ he hv hev]
      split_ifs <;> simp only [one_mul, zero_mul]

end QRHShort.CloudBatch








end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionGcdCoefficients.lean SHA256 f95c19af2003b843fe3c90764a3effefdcb24e7862bdc469fac82bf4c7b811b7 -/


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch

/-- The actual Hecke value is unitary outside the fixed bad primes. The
ray-class realization already includes the quotient factor to nu.modulus. -/
theorem expansion_nu_star_mul (c : ArithmeticContext) {g : Ideal O}
    (hg : Outside c.S g) : star (c.nu.onIdeal g) * c.nu.onIdeal g = 1 := by
  rw [← expansion_nuRayHom_onIdeal c hg, ← expansion_nuRayHom_inv c,
    ← map_mul, inv_mul_cancel, map_one]

theorem expansion_nu_norm_one (c : ArithmeticContext) {g : Ideal O}
    (hg : Outside c.S g) : ‖c.nu.onIdeal g‖ = 1 := by
  have he := congrArg norm (expansion_nu_star_mul c hg)
  simp only [norm_mul, norm_star, norm_one] at he
  nlinarith [norm_nonneg (c.nu.onIdeal g)]

/-- Exact common-gcd cancellation in the original source coefficients. -/
theorem expansion_originalCoefficient_gcd_pair (c : ArithmeticContext)
    (W : ℝ → ℂ) (D : ℝ) {g a b : Ideal O}
    (hg : SquarefreeOutside c.S g) (ha : SquarefreeOutside c.S a)
    (hb : SquarefreeOutside c.S b) (hga : IsRelPrime g a) (hgb : IsRelPrime g b) :
    star (expansionOriginalCoefficient c W D (g * a)) *
        expansionOriginalCoefficient c W D (g * b) =
      (mobius a : ℂ) * (mobius b : ℂ) * star (c.nu.onIdeal a) * c.nu.onIdeal b *
        star (W (normIdeal g * normIdeal a / D)) * W (normIdeal g * normIdeal b / D) := by
  have hgaO := (expansion_outside_mul c g a).mpr ⟨hg.1, ha.1⟩
  have hgbO := (expansion_outside_mul c g b).mpr ⟨hg.1, hb.1⟩
  have hma : (mobius (g * a) : ℂ) = (mobius g : ℂ) * (mobius a : ℂ) := by
    simp only [mobius, hga.moebius_mul, Int.cast_mul]
  have hmb : (mobius (g * b) : ℂ) = (mobius g : ℂ) * (mobius b : ℂ) := by
    simp only [mobius, hgb.moebius_mul, Int.cast_mul]
  simp only [expansionOriginalCoefficient, if_pos hgaO, if_pos hgbO, expansion_normIdeal_mul,
    hma, hmb, HeckeCharacter.onIdeal_mul, star_mul, star_intCast]
  calc
    _ = ((mobius g : ℂ) ^ 2 * (star (c.nu.onIdeal g) * c.nu.onIdeal g)) *
        ((mobius a : ℂ) * (mobius b : ℂ) * star (c.nu.onIdeal a) * c.nu.onIdeal b *
          star (W (normIdeal g * normIdeal a / D)) * W (normIdeal g * normIdeal b / D)) := by ring
    _ = _ := by rw [expansion_mobius_sq hg.2, expansion_nu_star_mul c hg.1, one_mul, one_mul]

/-- A single genuine ray family expands the original weighted gcd pair
and its inverse paired Gauss sum, before any weight, scale or gcd triple. -/
theorem expansion_original_gcd_paired_gauss_identity (c : ArithmeticContext)
    (hc : ArithmeticRelations c) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ),
      ∀ (W : ℝ → ℂ) (D : ℝ) (g a b : Ideal O)
        (hg : SquarefreeOutside c.S g) (ha : SquarefreeOutside c.S a)
        (hb : SquarefreeOutside c.S b) (hga : IsRelPrime g a) (hgb : IsRelPrime g b)
        (hab : IsRelPrime a b),
        star (expansionOriginalCoefficient c W D (g * a)) *
          expansionOriginalCoefficient c W D (g * b) *
            (expansionInversePairedCharacter c ha hb hab).gauss =
          ∑ ξ ∈ Ξ, coeffs ξ * coefficient ξ.val a * star (coefficient ξ.val b) *
            star (W (normIdeal g * normIdeal a / D)) * W (normIdeal g * normIdeal b / D) := by
  obtain ⟨Ξ, coeffs, he⟩ := expansion_initial_paired_gauss_identity c hc
  refine ⟨Ξ, coeffs, ?_⟩
  intro W D g a b hg ha hb hga hgb hab
  rw [expansion_originalCoefficient_gcd_pair c W D hg ha hb hga hgb]
  calc
    _ = ((mobius a : ℂ) * (mobius b : ℂ) * star (c.nu.onIdeal a) * c.nu.onIdeal b *
        (expansionInversePairedCharacter c ha hb hab).gauss) *
          star (W (normIdeal g * normIdeal a / D)) * W (normIdeal g * normIdeal b / D) := by ring
    _ = _ := by rw [he a b ha hb hab, Finset.sum_mul, Finset.sum_mul]

end QRHShort.CloudBatch





end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionMobius.lean SHA256 6c42108973c70d9a12c103459d39e19c7cd39ae37a150acafffcae7834e76c38 -/



noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch

abbrev ExpansionCommonFactorFiber (a b : Ideal O) :=
  {t : Ideal O × Ideal O × Ideal O // t.1 * t.2.1 = a ∧ t.1 * t.2.2 = b}

theorem expansion_gcd_ne_zero {a b : Ideal O} (ha : a ≠ ⊥) : gcd a b ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot] at ha ⊢
  intro hz
  apply ha
  simpa only [hz, zero_dvd_iff] using gcd_dvd_left a b

/-- The actual common divisors, with their two uniquely determined ideal
quotients, parameterize the whole common-factor fiber. -/
def expansionCommonFactorEquiv (a b : Ideal O) (ha : a ≠ ⊥) :
    {d : Ideal O // d ∈ idealDivisors (gcd a b) (expansion_gcd_ne_zero ha)} ≃
      ExpansionCommonFactorFiber a b where
  toFun d := by
    have hd := (mem_idealDivisors _ _ d.val).mp d.property
    have hda : d.val ∣ a := hd.trans (gcd_dvd_left a b)
    have hdb : d.val ∣ b := hd.trans (gcd_dvd_right a b)
    exact ⟨(d.val, Classical.choose hda, Classical.choose hdb),
      (Classical.choose_spec hda).symm, (Classical.choose_spec hdb).symm⟩
  invFun t := ⟨t.val.1, (mem_idealDivisors _ _ _).mpr
    (dvd_gcd ⟨t.val.2.1, t.property.1.symm⟩ ⟨t.val.2.2, t.property.2.symm⟩)⟩
  left_inv d := by apply Subtype.ext; rfl
  right_inv t := by
    apply Subtype.ext
    have hv : t.val.1 ≠ 0 := by
      intro hz
      exact ha (by rw [← t.property.1, hz, zero_mul]; exact Ideal.zero_eq_bot)
    let hda : t.val.1 ∣ a :=
      (dvd_gcd ⟨t.val.2.1, t.property.1.symm⟩ ⟨t.val.2.2, t.property.2.symm⟩).trans (gcd_dvd_left a b)
    let hdb : t.val.1 ∣ b :=
      (dvd_gcd ⟨t.val.2.1, t.property.1.symm⟩ ⟨t.val.2.2, t.property.2.symm⟩).trans (gcd_dvd_right a b)
    change (t.val.1, Classical.choose hda, Classical.choose hdb) = t.val
    refine Prod.ext rfl ?_
    apply Prod.ext
    · apply mul_left_cancel₀ hv
      exact (Classical.choose_spec
        ((dvd_gcd ⟨t.val.2.1, t.property.1.symm⟩
          ⟨t.val.2.2, t.property.2.symm⟩).trans (gcd_dvd_left a b))).symm.trans
            t.property.1.symm
    · apply mul_left_cancel₀ hv
      exact (Classical.choose_spec
        ((dvd_gcd ⟨t.val.2.1, t.property.1.symm⟩
          ⟨t.val.2.2, t.property.2.symm⟩).trans (gcd_dvd_right a b))).symm.trans
            t.property.2.symm

theorem expansion_common_factor_fiber_finite {a b : Ideal O}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    {t : Ideal O × Ideal O × Ideal O | t.1 * t.2.1 = a ∧ t.1 * t.2.2 = b}.Finite := by
  apply ((idealDivisors a ha).finite_toSet.prod
    ((idealDivisors a ha).finite_toSet.prod (idealDivisors b hb).finite_toSet)).subset
  rintro ⟨v, x, y⟩ ⟨hax, hby⟩
  exact ⟨(mem_idealDivisors a ha v).mpr ⟨x, hax.symm⟩,
    (mem_idealDivisors a ha x).mpr ⟨v, by simpa only [mul_comm] using hax.symm⟩,
    (mem_idealDivisors b hb y).mpr ⟨v, by simpa only [mul_comm] using hby.symm⟩⟩

theorem expansion_common_factor_mobius_fiber
    (F : Ideal O × Ideal O → ℂ)
    (hF0 : ∀ a, F (⊥, a) = 0) (a b : Ideal O) :
    (∑' t : ExpansionCommonFactorFiber a b,
      (mobius t.val.1 : ℂ) * F (t.val.1 * t.val.2.1, t.val.1 * t.val.2.2)) =
        if IsRelPrime a b then F (a, b) else 0 := by
  by_cases ha : a = ⊥
  · subst a
    have hz : (∑' t : ExpansionCommonFactorFiber ⊥ b,
        (mobius t.val.1 : ℂ) * F (t.val.1 * t.val.2.1, t.val.1 * t.val.2.2)) = 0 := by
      have hterm (t : ExpansionCommonFactorFiber ⊥ b) :
          (mobius t.val.1 : ℂ) * F (t.val.1 * t.val.2.1, t.val.1 * t.val.2.2) = 0 := by
        rw [t.property.1, t.property.2, hF0, mul_zero]
      simp_rw [hterm, tsum_zero]
    rw [hz, hF0]
    simp
  let e := expansionCommonFactorEquiv a b ha
  calc
    _ = ∑' d : {d : Ideal O // d ∈ idealDivisors (gcd a b) (expansion_gcd_ne_zero ha)},
        (mobius (e d).val.1 : ℂ) * F ((e d).val.1 * (e d).val.2.1,
          (e d).val.1 * (e d).val.2.2) := (e.tsum_eq _).symm
    _ = ∑' d : {d : Ideal O // d ∈ idealDivisors (gcd a b) (expansion_gcd_ne_zero ha)},
        (mobius d.val : ℂ) * F (a, b) := by
      apply tsum_congr
      intro d
      rw [(e d).property.1, (e d).property.2]
      rfl
    _ = (∑ d ∈ idealDivisors (gcd a b) (expansion_gcd_ne_zero ha), (mobius d : ℂ)) *
        F (a, b) := by
      rw [tsum_mul_right]
      congr 1
      exact Finset.tsum_subtype (idealDivisors (gcd a b) (expansion_gcd_ne_zero ha))
        (fun d : Ideal O => (mobius d : ℂ))
    _ = if IsRelPrime a b then F (a, b) else 0 := by
      rw [sum_idealDivisors_mobius_complex]
      by_cases hab : IsRelPrime a b
      · rw [if_pos ((gcd_isUnit_iff_isRelPrime.mpr hab).eq_one), if_pos hab, one_mul]
      · have hne : gcd a b ≠ 1 := by
          intro he
          apply hab
          apply gcd_isUnit_iff_isRelPrime.mp
          rw [he]
          exact isUnit_one
        rw [if_neg hne, if_neg hab, zero_mul]

/-- Joint finiteness is proved before changing the order of any actual
Möbius sum. Zero ideals are excluded by the source itself. -/
theorem expansion_common_mobius_hasFiniteSupport (F : Ideal O × Ideal O → ℂ)
    (hF : Function.HasFiniteSupport F)
    (hF0 : ∀ a, F (⊥, a) = 0) (hF0' : ∀ a, F (a, ⊥) = 0) :
    Function.HasFiniteSupport (fun t : Ideal O × Ideal O × Ideal O =>
      (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2)) := by
  have hfib : ∀ p ∈ Function.support F,
      {t : Ideal O × Ideal O × Ideal O | t.1 * t.2.1 = p.1 ∧ t.1 * t.2.2 = p.2}.Finite := by
    intro p hp
    apply expansion_common_factor_fiber_finite
    · intro hz
      exact hp (by rw [show p = (p.1, p.2) from rfl, hz, hF0])
    · intro hz
      exact hp (by rw [show p = (p.1, p.2) from rfl, hz, hF0'])
  apply (hF.biUnion hfib).subset
  intro t ht
  have hn : F (t.1 * t.2.1, t.1 * t.2.2) ≠ 0 := by
    intro hz
    exact ht (by change (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) = 0; rw [hz, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨(t.1 * t.2.1, t.1 * t.2.2), hn, rfl, rfl⟩

/-- Exact two-column coprimality inversion on the actual ideal monoid,
with the finite joint support and all order exchanges justified. -/
theorem expansion_common_divisor_mobius (F : Ideal O × Ideal O → ℂ)
    (hF : Function.HasFiniteSupport F)
    (hF0 : ∀ a, F (⊥, a) = 0) (hF0' : ∀ a, F (a, ⊥) = 0) :
    (∑' v : Ideal O, ∑' a : Ideal O, ∑' b : Ideal O,
      (mobius v : ℂ) * F (v * a, v * b)) =
        ∑' p : Ideal O × Ideal O, if IsRelPrime p.1 p.2 then F p else 0 := by
  have hs := summable_of_hasFiniteSupport (L := .unconditional _)
    (expansion_common_mobius_hasFiniteSupport F hF hF0 hF0')
  have hgroup := hs.hasSum.tsum_fiberwise
    (fun t : Ideal O × Ideal O × Ideal O => (t.1 * t.2.1, t.1 * t.2.2))
  have hfiber (p : Ideal O × Ideal O) :
      (∑' t : {t : Ideal O × Ideal O × Ideal O //
          (t.1 * t.2.1, t.1 * t.2.2) = p},
        (mobius t.val.1 : ℂ) * F (t.val.1 * t.val.2.1, t.val.1 * t.val.2.2)) =
          if IsRelPrime p.1 p.2 then F p else 0 := by
    let e : {t : Ideal O × Ideal O × Ideal O //
        (t.1 * t.2.1, t.1 * t.2.2) = p} ≃ ExpansionCommonFactorFiber p.1 p.2 :=
      Equiv.subtypeEquivRight (fun t => Prod.ext_iff)
    exact (e.tsum_eq (fun t =>
      (mobius t.val.1 : ℂ) * F (t.val.1 * t.val.2.1, t.val.1 * t.val.2.2))).trans
        (expansion_common_factor_mobius_fiber F hF0 p.1 p.2)
  have hgroup' : HasSum (fun p : Ideal O × Ideal O => if IsRelPrime p.1 p.2 then F p else 0)
      (∑' t : Ideal O × Ideal O × Ideal O, (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2)) := by
    convert hgroup using 1
    funext p
    exact (hfiber p).symm
  calc
    _ = ∑' v : Ideal O, ∑' p : Ideal O × Ideal O,
        (mobius v : ℂ) * F (v * p.1, v * p.2) := by
      apply tsum_congr
      intro v
      exact (hs.prod_factor v).tsum_prod.symm
    _ = ∑' t : Ideal O × Ideal O × Ideal O,
        (mobius t.1 : ℂ) * F (t.1 * t.2.1, t.1 * t.2.2) := hs.tsum_prod.symm
    _ = _ := hgroup'.tsum_eq.symm

end QRHShort.CloudBatch






end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionPrePairs.lean SHA256 ecd1b7c0cac6f0eae508896b2230774e1db1ad25d27f1bd75ae73a78fa70f906 -/



noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch

/-- The literal paired kernel before common-factor Möbius inversion. -/
def expansionPrePairedTerm (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (g e : Ideal O) (h : O)
    (p : Ideal O × Ideal O) : ℂ :=
  expansionPreColumn c ξ g e h p.1 * star (expansionPreColumn c ξ g e h p.2) *
    (((Real.sqrt (normIdeal p.1 * normIdeal p.2) : ℝ) : ℂ)⁻¹ *
      (star (W (normIdeal g * normIdeal p.1 / D)) * W (normIdeal g * normIdeal p.2 / D))) *
    radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal e * (normIdeal p.1 * normIdeal p.2)))

theorem expansion_preColumn_bot (c : ArithmeticContext) (ξ : RayCharacter c)
    (g e : Ideal O) (h : O) : expansionPreColumn c ξ g e h ⊥ = 0 := by
  unfold expansionPreColumn
  apply if_neg
  intro hs
  exact hs.1.1.1 rfl

theorem expansion_prePaired_bot_left (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (g e : Ideal O) (h : O) (a : Ideal O) :
    expansionPrePairedTerm c ξ Φ W D H g e h (⊥, a) = 0 := by
  simp only [expansionPrePairedTerm, expansion_preColumn_bot, zero_mul]

theorem expansion_prePaired_bot_right (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (g e : Ideal O) (h : O) (a : Ideal O) :
    expansionPrePairedTerm c ξ Φ W D H g e h (a, ⊥) = 0 := by
  simp only [expansionPrePairedTerm, expansion_preColumn_bot, star_zero, mul_zero, zero_mul]

theorem expansion_prePaired_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (H : ℝ) {g : Ideal O} (hg : g ≠ ⊥) (e : Ideal O) (h : O) :
    Function.HasFiniteSupport (expansionPrePairedTerm c ξ Φ W D H g e h) := by
  have hNg : 0 < normIdeal g := normIdeal_pos hg
  apply ((finite_normIdeal_le (I.hi * D / normIdeal g)).prod
    (finite_normIdeal_le (I.hi * D / normIdeal g))).subset
  intro p hp
  have hw1 : W (normIdeal g * normIdeal p.1 / D) ≠ 0 := by
    intro hz
    exact hp (by simp only [expansionPrePairedTerm, hz, star_zero, zero_mul, mul_zero])
  have hw2 : W (normIdeal g * normIdeal p.2 / D) ≠ 0 := by
    intro hz
    exact hp (by simp only [expansionPrePairedTerm, hz, star_zero, zero_mul, mul_zero])
  constructor
  · apply (le_div_iff₀ hNg).mpr
    have hu := (div_le_iff₀ hD).mp (hW.2 hw1).2
    nlinarith
  · apply (le_div_iff₀ hNg).mpr
    have hu := (div_le_iff₀ hD).mp (hW.2 hw2).2
    nlinarith

/-- Exact inversion for the literal paired kernel; every reordered series
has genuine finite joint support. -/
theorem expansion_prePaired_common_divisor (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (H : ℝ) {g : Ideal O} (hg : g ≠ ⊥) (e : Ideal O) (h : O) :
    (∑' v : Ideal O, ∑' a : Ideal O, ∑' b : Ideal O,
      (mobius v : ℂ) * expansionPrePairedTerm c ξ Φ W D H g e h (v * a, v * b)) =
        ∑' p : Ideal O × Ideal O, if IsRelPrime p.1 p.2 then
          expansionPrePairedTerm c ξ Φ W D H g e h p else 0 := by
  exact expansion_common_divisor_mobius (expansionPrePairedTerm c ξ Φ W D H g e h)
    (expansion_prePaired_hasFiniteSupport c ξ I Φ hW hD H hg e h)
    (expansion_prePaired_bot_left c ξ Φ W D H g e h)
    (expansion_prePaired_bot_right c ξ Φ W D H g e h)

end QRHShort.CloudBatch






end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionRayIntegrand.lean SHA256 a4bf31c5e3ec68226d3eaea1c6a30d224682994e649a576b837f7d8af1171ebd -/



noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch

/-- The inverse-character factors are precisely the two literal columns,
including their original squarefree and common-gcd exclusions. -/
theorem expansion_prePaired_character_factor (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) {g a b e : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hga : IsRelPrime g a) (hgb : IsRelPrime g b) (hab : IsRelPrime a b)
    (he : Outside c.S e) (h : O) :
    expansionPrePairedTerm c ξ Φ W D H g e h (a, b) =
      coefficient ξ.val a * star (coefficient ξ.val b) *
        star (W (normIdeal g * normIdeal a / D)) * W (normIdeal g * normIdeal b / D) *
        ((expansionInversePairedCharacter c ha hb hab).value (chosenGenerator e) *
          star ((expansionInversePairedCharacter c ha hb hab).value h)) *
        (((Real.sqrt (normIdeal a * normIdeal b) : ℝ) : ℂ)⁻¹) *
        radialFourier (fun x => (Φ.value x : ℂ))
          (H * normElement h / (normIdeal e * (normIdeal a * normIdeal b))) := by
  have hca : SquarefreeOutside c.S a ∧ IsRelPrime a g := ⟨ha, hga.symm⟩
  have hcb : SquarefreeOutside c.S b ∧ IsRelPrime b g := ⟨hb, hgb.symm⟩
  simp only [expansionPrePairedTerm, expansionPreColumn, if_pos hca,
    if_pos hcb, expansion_inversePairedCharacter_value,
    expansion_chosenGenerator_eq_primaryGenerator c he, star_mul, star_star]
  ring

/-- One ray family converts each actual original Poisson integrand into
literal pre-paired kernels. No infinite sum is exchanged in this lemma. -/
theorem expansion_original_ray_integrand (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ),
      ∀ (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (g a b e : Ideal O) (h : O)
        (hg : SquarefreeOutside c.S g) (ha : SquarefreeOutside c.S a)
        (hb : SquarefreeOutside c.S b) (hga : IsRelPrime g a) (hgb : IsRelPrime g b)
        (hab : IsRelPrime a b) (he : Outside c.S e),
        star (expansionOriginalCoefficient c W D (g * a)) *
          expansionOriginalCoefficient c W D (g * b) *
            (expansionInversePairedCharacter c ha hb hab).gauss *
            ((expansionInversePairedCharacter c ha hb hab).value (chosenGenerator e) *
              star ((expansionInversePairedCharacter c ha hb hab).value h)) *
            (((Real.sqrt (normIdeal a * normIdeal b) : ℝ) : ℂ)⁻¹) *
            radialFourier (fun x => (Φ.value x : ℂ))
              (H * normElement h / (normIdeal e * (normIdeal a * normIdeal b))) =
          ∑ ξ ∈ Ξ, coeffs ξ * expansionPrePairedTerm c ξ Φ W D H g e h (a, b) := by
  obtain ⟨Ξ, coeffs, hbase⟩ := expansion_original_gcd_paired_gauss_identity c hc
  refine ⟨Ξ, coeffs, ?_⟩
  intro Φ W D H g a b e h hg ha hb hga hgb hab he
  rw [hbase W D g a b hg ha hb hga hgb hab]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [expansion_prePaired_character_factor c ξ Φ W D H ha hb hga hgb hab he h]
  ring

end QRHShort.CloudBatch



end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionZero.lean SHA256 6f23b53265ddc7ab6df1ef7ad15c0d7a72f2527b759425aa2d9ce281a70d5331 -/


noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch.PoissonExpansionZero

def actualZeroTerm (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D H : ℝ) (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if ht : expansionGcdTripleAdmissible c t then
    star (expansionOriginalCoefficient c W D (t.1 * t.2.1)) *
      expansionOriginalCoefficient c W D (t.1 * t.2.2) *
        poissonZeroTerm (expansionInversePairedCharacter c ht.2.1 ht.2.2.1
          ht.2.2.2.2.2) t.1 (fun x => (Φ.value x : ℂ)) H
  else 0

theorem ideal_mul_eq_top_iff (a b : Ideal O) :
    a * b = ⊤ ↔ a = 1 ∧ b = 1 := by
  rw [← Ideal.isUnit_iff, IsUnit.mul_iff]
  simp only [Ideal.isUnit_iff, Ideal.one_eq_top]

theorem squarefreeOutside_one (c : ArithmeticContext) :
    SquarefreeOutside c.S (1 : Ideal O) := by
  refine ⟨⟨one_ne_zero, ?_⟩, squarefree_one⟩
  intro p hp hd
  exact (c.prime_S p hp).not_unit (isUnit_of_dvd_one hd)

theorem gcdTriple_one_iff (c : ArithmeticContext) (g : Ideal O) :
    expansionGcdTripleAdmissible c (g, 1, 1) ↔ SquarefreeOutside c.S g := by
  simp only [expansionGcdTripleAdmissible, squarefreeOutside_one c,
    isRelPrime_one_right, and_true, true_and]

theorem actualZeroTerm_eq (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (Φ : RowWeight) (W : ℝ → ℂ) (D : ℝ)
    {H : ℝ} (hH : 0 < H) (t : Ideal O × Ideal O × Ideal O) :
    actualZeroTerm c Φ W D H t =
      if t.2.1 = 1 ∧ t.2.2 = 1 then
        if SquarefreeOutside c.S t.1 then
          ((‖expansionOriginalCoefficient c W D t.1‖ ^ 2 : ℝ) : ℂ) *
            (∏ P ∈ primeFactors t.1, (1 - (normIdeal P : ℂ)⁻¹)) *
            (H : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0
        else 0
      else 0 := by
  rcases t with ⟨g, a, b⟩
  by_cases hab : a = 1 ∧ b = 1
  · rcases hab with ⟨rfl, rfl⟩
    by_cases hg : SquarefreeOutside c.S g
    · have ht := (gcdTriple_one_iff c g).mpr hg
      have hm : (expansionInversePairedCharacter c ht.2.1 ht.2.2.1
          ht.2.2.2.2.2).modulus = ⊤ := by
        rw [expansion_inversePairedCharacter_modulus, mul_one, Ideal.one_eq_top]
      rw [actualZeroTerm, dif_pos ht,
        hz.2 _ g (fun x => (Φ.value x : ℂ)) H
          ((expansion_primitive_character_eq_one_iff _).mpr hm) hm hg.1.1 hH Φ.schwartz]
      simp only [mul_one, and_self, if_true, if_pos hg]
      have hc : star (expansionOriginalCoefficient c W D g) *
          expansionOriginalCoefficient c W D g =
          ((‖expansionOriginalCoefficient c W D g‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [Complex.ofReal_pow, starRingEnd_apply, mul_comm] using
          Complex.mul_conj' (expansionOriginalCoefficient c W D g)
      rw [hc]
      ring
    · have ht : ¬ expansionGcdTripleAdmissible c (g, 1, 1) :=
        fun h => hg ((gcdTriple_one_iff c g).mp h)
      simp only [actualZeroTerm, dif_neg ht, and_self, if_true, if_neg hg]
  · by_cases ht : expansionGcdTripleAdmissible c (g, a, b)
    · have hm : (expansionInversePairedCharacter c ht.2.1 ht.2.2.1
          ht.2.2.2.2.2).modulus ≠ ⊤ := by
        rw [expansion_inversePairedCharacter_modulus]
        exact mt (ideal_mul_eq_top_iff a b).mp hab
      rw [actualZeroTerm, dif_pos ht,
        expansion_poissonZeroTerm_eq_zero_of_modulus_ne_top hz _ hm]
      simp only [mul_zero, if_neg hab]
    · simp only [actualZeroTerm, dif_neg ht, if_neg hab]

theorem actualZeroTerm_diagonal (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (Φ : RowWeight) (W : ℝ → ℂ) (D : ℝ)
    {H : ℝ} (hH : 0 < H) (g : Ideal O) :
    actualZeroTerm c Φ W D H (g, 1, 1) =
      ((‖expansionOriginalCoefficient c W D g‖ ^ 2 : ℝ) : ℂ) *
        (∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹)) *
        (H : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 := by
  rw [actualZeroTerm_eq hz c Φ W D hH]
  simp only [and_self, if_true]
  split_ifs with hg
  · rfl
  · rw [expansion_originalCoefficient_zero_of_not_squarefree c W D hg]
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero, zero_mul]

theorem actualZeroTerm_tsum (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (Φ : RowWeight) (W : ℝ → ℂ) (D : ℝ)
    {H : ℝ} (hH : 0 < H) :
    (∑' t : Ideal O × Ideal O × Ideal O, actualZeroTerm c Φ W D H t) =
      (H : ℂ) * radialFourier (fun x => (Φ.value x : ℂ)) 0 *
        ∑' g : Ideal O, ((‖expansionOriginalCoefficient c W D g‖ ^ 2 : ℝ) : ℂ) *
          ∏ P ∈ primeFactors g, (1 - (normIdeal P : ℂ)⁻¹) := by
  have hi : Function.Injective (fun g : Ideal O => (g, (1 : Ideal O), (1 : Ideal O))) :=
    fun g g' h => congrArg Prod.fst h
  have hs : Function.support (actualZeroTerm c Φ W D H) ⊆
      Set.range (fun g : Ideal O => (g, (1 : Ideal O), (1 : Ideal O))) := by
    rintro ⟨g, a, b⟩ h
    by_cases hab : a = 1 ∧ b = 1
    · rcases hab with ⟨rfl, rfl⟩
      exact ⟨g, rfl⟩
    · exact False.elim (h (by rw [actualZeroTerm_eq hz c Φ W D hH, if_neg hab]))
  rw [← hi.tsum_eq hs]
  simp_rw [actualZeroTerm_diagonal hz c Φ W D hH]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro g
  ring

theorem actualZeroTerm_tsum_eq_originalDiagonal (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (Φ : RowWeight) (W : ℝ → ℂ) {D H : ℝ}
    (hD : 0 < D) (hH : 0 < H) :
    (∑' t : Ideal O × Ideal O × Ideal O, actualZeroTerm c Φ W D H t) =
      (D : ℂ) * expansionOriginalDiagonal c Φ W D H := by
  rw [actualZeroTerm_tsum hz c Φ W D hH, expansionOriginalDiagonal]
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  field_simp

end QRHShort.CloudBatch.PoissonExpansionZero








end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionNonzeroSplit.lean SHA256 3d4820076e9252de9aff08d227a98f66f65822a4864daef4e26768d9e9ac8836 -/


noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.CloudBatch.PoissonExpansionZero

def actualNonzeroDual (χ : PrimitiveResidueCharacter) (g : Ideal O)
    (Φ : RowWeight) (H : ℝ) : ℂ :=
  H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
    ∑' d : Ideal O, if d ∣ outsideRadical ∅ g then
      (mobius d : ℂ) * χ.value (chosenGenerator d) / (normIdeal d : ℂ) *
        ∑' h : O, if h ≠ 0 then star (χ.value h) *
          radialFourier (fun x => (Φ.value x : ℂ))
            (H * normElement h / (normIdeal d * normIdeal χ.modulus)) else 0
    else 0

def actualNonzeroTerm (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D H : ℝ) (t : Ideal O × Ideal O × Ideal O) : ℂ :=
  if ht : expansionGcdTripleAdmissible c t then
    star (expansionOriginalCoefficient c W D (t.1 * t.2.1)) *
      expansionOriginalCoefficient c W D (t.1 * t.2.2) *
        actualNonzeroDual (expansionInversePairedCharacter c ht.2.1 ht.2.2.1
          ht.2.2.2.2.2) t.1 Φ H
  else 0

theorem actualDual_frequency_split (χ : PrimitiveResidueCharacter)
    (g : Ideal O) (Φ : RowWeight) {H : ℝ} (hH : 0 < H)
    {d : Ideal O} (hd : d ∣ outsideRadical ∅ g) :
    (∑' h : O, star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal d * normIdeal χ.modulus))) =
      star (χ.value 0) * radialFourier (fun x => (Φ.value x : ℂ)) 0 +
        ∑' h : O, if h ≠ 0 then star (χ.value h) *
          radialFourier (fun x => (Φ.value x : ℂ))
            (H * normElement h / (normIdeal d * normIdeal χ.modulus)) else 0 := by
  have hM : 0 < normIdeal d * normIdeal χ.modulus :=
    mul_pos (zero_lt_one.trans_le (expansion_zero_contribution_one_le_normIdeal
      (ne_zero_of_dvd_ne_zero (expansion_outsideRadical_ne_bot ∅ g) hd)))
      (zero_lt_one.trans_le (expansion_zero_contribution_one_le_normIdeal χ.modulus_ne_bot))
  have hf : Function.HasFiniteSupport (fun h : O => star (χ.value h) *
      radialFourier (fun x => (Φ.value x : ℂ))
        (H * normElement h / (normIdeal d * normIdeal χ.modulus))) := by
    apply (expansion_fourier_frequency_hasFiniteSupport Φ hH hM).subset
    intro h hh hz
    change radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal d * normIdeal χ.modulus)) = 0 at hz
    change star (χ.value h) * radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal d * normIdeal χ.modulus)) ≠ 0 at hh
    exact hh (by rw [hz, mul_zero])
  have hz : normElement (0 : O) = 0 := by
    simp [normElement, principal, normIdeal]
  simpa only [hz, mul_zero, zero_div, ite_not] using
    (summable_of_hasFiniteSupport hf).tsum_eq_add_tsum_ite (0 : O)

theorem actualPoissonDual_split (χ : PrimitiveResidueCharacter)
    (g : Ideal O) (Φ : RowWeight) {H : ℝ} (hH : 0 < H) :
    expansionPoissonDual χ g Φ H =
      poissonZeroTerm χ g (fun x => (Φ.value x : ℂ)) H +
        actualNonzeroDual χ g Φ H := by
  have hfinite := expansion_divisors_finite (expansion_outsideRadical_ne_bot ∅ g)
  have hs (f : Ideal O → ℂ) : Summable (fun d =>
      if d ∣ outsideRadical ∅ g then f d else 0) := by
    apply summable_of_hasFiniteSupport
    apply hfinite.subset
    intro d hd
    by_contra hnd
    change ¬ d ∣ outsideRadical ∅ g at hnd
    change (if d ∣ outsideRadical ∅ g then f d else 0) ≠ 0 at hd
    exact hd (by rw [if_neg hnd])
  unfold expansionPoissonDual poissonZeroTerm actualNonzeroDual
  rw [← mul_add, ← (hs _).tsum_add (hs _)]
  congr 1
  apply tsum_congr
  intro d
  by_cases hd : d ∣ outsideRadical ∅ g
  · simp only [if_pos hd]
    rw [actualDual_frequency_split χ g Φ hH hd]
    ring
  · simp only [if_neg hd, add_zero]

theorem actualOriginalPoissonTerm_split (c : ArithmeticContext) (Φ : RowWeight)
    (W : ℝ → ℂ) (D : ℝ) {H : ℝ} (hH : 0 < H)
    (t : Ideal O × Ideal O × Ideal O) :
    expansionOriginalPoissonTerm c Φ W D H t =
      actualZeroTerm c Φ W D H t + actualNonzeroTerm c Φ W D H t := by
  by_cases ht : expansionGcdTripleAdmissible c t
  · rw [expansionOriginalPoissonTerm, actualZeroTerm, actualNonzeroTerm,
      dif_pos ht, dif_pos ht, dif_pos ht, actualPoissonDual_split _ _ _ hH, mul_add]
  · simp only [expansionOriginalPoissonTerm, actualZeroTerm, actualNonzeroTerm,
      dif_neg ht, add_zero]

theorem actualZeroTerm_hasFiniteSupport (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Function.HasFiniteSupport (actualZeroTerm c Φ W D H) := by
  apply ((expansionOriginalWindow I D).finite_toSet.image
    (fun g : Ideal O => (g, (1 : Ideal O), (1 : Ideal O)))).subset
  rintro ⟨g, a, b⟩ ht
  have hab : a = 1 ∧ b = 1 := by
    by_contra hab
    exact ht (by rw [actualZeroTerm_eq hz c Φ W D hH, if_neg hab])
  rcases hab with ⟨rfl, rfl⟩
  refine ⟨g, ?_, rfl⟩
  apply expansion_originalCoefficient_support c hW hD
  intro hc
  exact ht (by rw [actualZeroTerm_diagonal hz c Φ W D hH, hc]; simp)

theorem actualNonzeroTerm_summable (hp : PoissonStatement) (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Summable (actualNonzeroTerm c Φ W D H) := by
  apply ((expansion_originalPoissonTerm_summable hp c Φ hW hD hH).sub
    (summable_of_hasFiniteSupport
      (actualZeroTerm_hasFiniteSupport hz c Φ hW hD hH))).congr
  intro t
  rw [actualOriginalPoissonTerm_split c Φ W D hH]
  ring

theorem actual_energy_zero_nonzero (hp : PoissonStatement) (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (Φ : RowWeight) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    (expansionSmoothedEnergy c Φ W D H : ℂ) =
      expansionOriginalDiagonal c Φ W D H +
        (D⁻¹ : ℂ) * ∑' t : Ideal O × Ideal O × Ideal O,
          actualNonzeroTerm c Φ W D H t := by
  rw [expansion_original_energy_poisson hp c Φ hW hD hH]
  simp_rw [actualOriginalPoissonTerm_split c Φ W D hH]
  rw [(summable_of_hasFiniteSupport
    (actualZeroTerm_hasFiniteSupport hz c Φ hW hD hH)).tsum_add
      (actualNonzeroTerm_summable hp hz c Φ hW hD hH),
    actualZeroTerm_tsum_eq_originalDiagonal hz c Φ W hD hH, mul_add]
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  simp only [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hDc, one_mul]

end QRHShort.CloudBatch.PoissonExpansionZero







end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionRaySupport.lean SHA256 ea8feebf8f3f2157c70f05cb4aea426df633a73e95952a2b3f56748ae8bb0d1c -/



noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.CloudBatch

def expansionRayJoint (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ)
    (t : Ideal O × Ideal O × O × (Ideal O × Ideal O)) : ℂ :=
  if SquarefreeOutside c.S t.1 ∧ t.2.1 ∣ t.1 ∧ t.2.2.1 ≠ 0 then
    (mobius t.2.1 : ℂ) / (normIdeal t.2.1 : ℂ) *
      expansionPrePairedTerm c ξ Φ W D H t.1 t.2.1 t.2.2.1 t.2.2.2
  else 0

theorem expansion_normIdeal_le_of_dvd {a b : Ideal O} (hb : b ≠ ⊥)
    (hab : a ∣ b) : normIdeal a ≤ normIdeal b := by
  have hpos : 0 < b.absNorm := Nat.pos_of_ne_zero
    (fun h => hb (Ideal.absNorm_eq_zero_iff.mp h))
  change (a.absNorm : ℝ) ≤ (b.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hab)

theorem expansion_primeFactors_prod {g : Ideal O} (hg : g ≠ ⊥)
    (hsq : Squarefree g) : (∏ p ∈ primeFactors g, p) = g := by
  have hnodup := (squarefree_iff_nodup_normalizedFactors hg).mp hsq
  unfold primeFactors
  calc
    _ = (normalizedFactors g).toFinset.val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors g).prod := by rw [Multiset.toFinset_val, hnodup.dedup]
    _ = g := Ideal.prod_normalizedFactors_eq_self hg

theorem expansion_outsideRadical_empty_eq {g : Ideal O} (hg : g ≠ ⊥)
    (hsq : Squarefree g) : outsideRadical ∅ g = g := by
  simpa [outsideRadical] using expansion_primeFactors_prod hg hsq

theorem expansion_prePaired_joint_norm_bounds (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) {g e : Ideal O} (hg : g ≠ ⊥)
    (he : e ∣ g) {h : O} {p : Ideal O × Ideal O}
    (hp : expansionPrePairedTerm c ξ Φ W D H g e h p ≠ 0) :
    normIdeal g ≤ max 1 (I.hi * D) ∧ normIdeal e ≤ max 1 (I.hi * D) ∧
      normElement h ≤ Φ.fourierCap * (max 1 (I.hi * D)) ^ 3 / H ∧
      normIdeal p.1 ≤ max 1 (I.hi * D) ∧ normIdeal p.2 ≤ max 1 (I.hi * D) := by
  have hsf1 : SquarefreeOutside c.S p.1 := by
    by_contra hs
    exact hp (by simp [expansionPrePairedTerm, expansionPreColumn, hs])
  have hsf2 : SquarefreeOutside c.S p.2 := by
    by_contra hs
    exact hp (by simp [expansionPrePairedTerm, expansionPreColumn, hs])
  have hw1 : W (normIdeal g * normIdeal p.1 / D) ≠ 0 := by
    intro hz
    exact hp (by simp only [expansionPrePairedTerm, hz, star_zero, zero_mul, mul_zero])
  have hw2 : W (normIdeal g * normIdeal p.2 / D) ≠ 0 := by
    intro hz
    exact hp (by simp only [expansionPrePairedTerm, hz, mul_zero, zero_mul])
  have hfour : radialFourier (fun x => (Φ.value x : ℂ))
      (H * normElement h / (normIdeal e * (normIdeal p.1 * normIdeal p.2))) ≠ 0 := by
    intro hz
    exact hp (by simp only [expansionPrePairedTerm, hz, mul_zero])
  have hga := (div_le_iff₀ hD).mp (hW.2 hw1).2
  have hgb := (div_le_iff₀ hD).mp (hW.2 hw2).2
  have hNg := expansion_zero_contribution_one_le_normIdeal hg
  have hNa := expansion_zero_contribution_one_le_normIdeal hsf1.1.1
  have hNb := expansion_zero_contribution_one_le_normIdeal hsf2.1.1
  have hNe := expansion_zero_contribution_one_le_normIdeal
    (ne_zero_of_dvd_ne_zero hg he)
  have hT : 0 ≤ max 1 (I.hi * D) := zero_le_one.trans (le_max_left _ _)
  have hgT : normIdeal g ≤ max 1 (I.hi * D) :=
    (le_mul_of_one_le_right (zero_le_one.trans hNg) hNa).trans
      (hga.trans (le_max_right _ _))
  have haT : normIdeal p.1 ≤ max 1 (I.hi * D) :=
    (le_mul_of_one_le_left (zero_le_one.trans hNa) hNg).trans
      (hga.trans (le_max_right _ _))
  have hbT : normIdeal p.2 ≤ max 1 (I.hi * D) :=
    (le_mul_of_one_le_left (zero_le_one.trans hNb) hNg).trans
      (hgb.trans (le_max_right _ _))
  have heT := (expansion_normIdeal_le_of_dvd hg he).trans hgT
  have hdenpos : 0 < normIdeal e * (normIdeal p.1 * normIdeal p.2) :=
    mul_pos (zero_lt_one.trans_le hNe)
      (mul_pos (zero_lt_one.trans_le hNa) (zero_lt_one.trans_le hNb))
  have hden : normIdeal e * (normIdeal p.1 * normIdeal p.2) ≤
      (max 1 (I.hi * D)) ^ 3 := by
    calc
      _ ≤ max 1 (I.hi * D) * (max 1 (I.hi * D) * max 1 (I.hi * D)) :=
        mul_le_mul heT (mul_le_mul haT hbT (zero_le_one.trans hNb) hT)
          (mul_nonneg (zero_le_one.trans hNa) (zero_le_one.trans hNb)) hT
      _ = _ := by ring
  have hx0 : 0 ≤ H * normElement h /
      (normIdeal e * (normIdeal p.1 * normIdeal p.2)) :=
    div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _)) hdenpos.le
  have hcap := (Φ.fourier_support ⟨hfour, hx0⟩).2
  refine ⟨hgT, heT, ?_, haT, hbT⟩
  apply (le_div_iff₀ hH).mpr
  have hh := (div_le_iff₀ hdenpos).mp hcap
  have hc := mul_le_mul_of_nonneg_left hden Φ.cap_pos.le
  nlinarith

theorem expansion_rayJoint_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Function.HasFiniteSupport (expansionRayJoint c ξ Φ W D H) := by
  let T := max 1 (I.hi * D)
  apply ((finite_normIdeal_le T).prod ((finite_normIdeal_le T).prod
    ((finite_normElement_le (Φ.fourierCap * T ^ 3 / H)).prod
      ((finite_normIdeal_le T).prod (finite_normIdeal_le T))))).subset
  intro t ht
  have hguard : SquarefreeOutside c.S t.1 ∧ t.2.1 ∣ t.1 ∧ t.2.2.1 ≠ 0 := by
    by_contra hn
    exact ht (by simp only [expansionRayJoint, if_neg hn])
  have hp : expansionPrePairedTerm c ξ Φ W D H t.1 t.2.1 t.2.2.1 t.2.2.2 ≠ 0 := by
    intro hz
    exact ht (by simp only [expansionRayJoint, if_pos hguard, hz, mul_zero])
  obtain ⟨hg, he, hh, ha, hb⟩ := expansion_prePaired_joint_norm_bounds c ξ I Φ
    hW hD hH hguard.1.1.1 hguard.2.1 hp
  exact ⟨hg, he, hh, ha, hb⟩

end QRHShort.CloudBatch






end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionRayEnergy.lean SHA256 505f2a4987b8e8245cced0eb5bb8ae49f5cca923fff19cdbda828c07e19e7000 -/



noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch
open PoissonExpansionZero

abbrev ExpansionRayIndex := Ideal O × Ideal O × O × (Ideal O × Ideal O)
abbrev ExpansionRayGroupedIndex := (Ideal O × Ideal O × Ideal O) × (Ideal O × O)

def expansionRayTranspose : ExpansionRayGroupedIndex ≃ ExpansionRayIndex where
  toFun x := (x.1.1, x.2.1, x.2.2, x.1.2.1, x.1.2.2)
  invFun x := ((x.1, x.2.2.2.1, x.2.2.2.2), (x.2.1, x.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def expansionCoprimeRayJoint (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (t : ExpansionRayIndex) : ℂ :=
  if IsRelPrime t.2.2.2.1 t.2.2.2.2 then expansionRayJoint c ξ Φ W D H t else 0

theorem expansion_coprimeRayJoint_summable (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Summable (expansionCoprimeRayJoint c ξ Φ W D H) := by
  apply summable_of_hasFiniteSupport
  apply (expansion_rayJoint_hasFiniteSupport c ξ I Φ hW hD hH).subset
  intro t ht hz
  exact ht (by simp only [expansionCoprimeRayJoint, hz, ite_self])

theorem expansion_coprimeRayJoint_zero_of_not_admissible (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ)
    (g a b e : Ideal O) (h : O)
    (hbad : ¬ expansionGcdTripleAdmissible c (g, a, b)) :
    expansionCoprimeRayJoint c ξ Φ W D H (g, e, h, a, b) = 0 := by
  by_cases hab : IsRelPrime a b
  · rw [expansionCoprimeRayJoint, if_pos hab]
    by_cases hg : SquarefreeOutside c.S g ∧ e ∣ g ∧ h ≠ 0
    · by_cases ha : SquarefreeOutside c.S a ∧ IsRelPrime a g
      · by_cases hb : SquarefreeOutside c.S b ∧ IsRelPrime b g
        · exact False.elim (hbad ⟨hg.1, ha.1, hb.1, ha.2.symm, hb.2.symm, hab⟩)
        · simp only [expansionRayJoint, if_pos hg, expansionPrePairedTerm,
            expansionPreColumn, if_neg hb, star_zero, mul_zero, zero_mul]
      · simp only [expansionRayJoint, if_pos hg, expansionPrePairedTerm,
          expansionPreColumn, if_neg ha, zero_mul, mul_zero]
    · exact if_neg hg
  · exact if_neg hab

theorem expansion_scaled_nonzeroDual (χ : PrimitiveResidueCharacter)
    (g : Ideal O) (Φ : RowWeight) (H : ℝ) (A : ℂ) :
    A * actualNonzeroDual χ g Φ H =
      (H : ℂ) * ∑' e : Ideal O, ∑' h : O,
        if e ∣ outsideRadical ∅ g ∧ h ≠ 0 then
          (mobius e : ℂ) / (normIdeal e : ℂ) *
            (A * χ.gauss * (χ.value (chosenGenerator e) * star (χ.value h)) *
              ((Real.sqrt (normIdeal χ.modulus) : ℂ)⁻¹) *
              radialFourier (fun x => (Φ.value x : ℂ))
                (H * normElement h / (normIdeal e * normIdeal χ.modulus))) else 0 := by
  unfold actualNonzeroDual
  simp only [← mul_assoc, ← tsum_mul_left, mul_ite, mul_zero]
  apply tsum_congr
  intro e
  by_cases he : e ∣ outsideRadical ∅ g
  · simp only [he, true_and, ite_true, ← tsum_mul_left]
    apply tsum_congr
    intro h
    by_cases hh : h ≠ 0
    · simp only [if_pos hh]
      ring
    · simp only [if_neg hh, mul_zero]
  · simp only [he, false_and, ite_false, tsum_zero, mul_zero]

theorem expansion_original_energy_ray (hp : PoissonStatement) (hz : PoissonZeroStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ (Ξ : Finset (RayCharacter c)) (coeffs : RayCharacter c → ℂ),
      ∀ (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ),
        SmoothSupported I W → 0 < D → 0 < H →
        (expansionSmoothedEnergy c Φ W D H : ℂ) =
          expansionOriginalDiagonal c Φ W D H + (H / D : ℂ) *
            ∑ ξ ∈ Ξ, coeffs ξ * ∑' t : ExpansionRayIndex,
              if IsRelPrime t.2.2.2.1 t.2.2.2.2 then
                expansionRayJoint c ξ Φ W D H t else 0 := by
  obtain ⟨Ξ, coeffs, hconv⟩ := expansion_original_ray_integrand c hc
  refine ⟨Ξ, coeffs, ?_⟩
  intro I Φ W D H hW hD hH
  let R (ξ : RayCharacter c) := expansionCoprimeRayJoint c ξ Φ W D H
  have hs (ξ : RayCharacter c) : Summable (fun x : ExpansionRayGroupedIndex =>
      R ξ (expansionRayTranspose x)) :=
    expansionRayTranspose.summable_iff.mpr
      (expansion_coprimeRayJoint_summable c ξ I Φ hW hD hH)
  have hpoint (t : Ideal O × Ideal O × Ideal O) :
      actualNonzeroTerm c Φ W D H t = (H : ℂ) *
        ∑' e : Ideal O, ∑' h : O, ∑ ξ ∈ Ξ, coeffs ξ * R ξ
          (t.1, e, h, t.2.1, t.2.2) := by
    rcases t with ⟨g, a, b⟩
    by_cases ht : expansionGcdTripleAdmissible c (g, a, b)
    · rw [actualNonzeroTerm, dif_pos ht,
        expansion_scaled_nonzeroDual, expansion_outsideRadical_empty_eq ht.1.1.1 ht.1.2]
      congr 1
      apply tsum_congr
      intro e
      apply tsum_congr
      intro h
      by_cases he : e ∣ g ∧ h ≠ 0
      · rw [if_pos he, expansion_inversePairedCharacter_modulus, expansion_normIdeal_mul]
        rw [hconv Φ W D H g a b e h ht.1 ht.2.1 ht.2.2.1
          ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2
          (expansion_outside_of_dvd c ht.1.1 he.1), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ hξ
        have hguard : SquarefreeOutside c.S g ∧ e ∣ g ∧ h ≠ 0 := ⟨ht.1, he⟩
        simp only [R, expansionCoprimeRayJoint, if_pos ht.2.2.2.2.2,
          expansionRayJoint, if_pos hguard]
        ring
      · simp only [if_neg he]
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro ξ hξ
        have hguard : ¬ (SquarefreeOutside c.S g ∧ e ∣ g ∧ h ≠ 0) :=
          fun hg => he hg.2
        simp only [R, expansionCoprimeRayJoint, if_pos ht.2.2.2.2.2,
          expansionRayJoint, if_neg hguard, mul_zero]
    · rw [actualNonzeroTerm, dif_neg ht]
      have hz' (e : Ideal O) (h : O) (ξ : RayCharacter c) :
          R ξ (g, e, h, a, b) = 0 :=
        expansion_coprimeRayJoint_zero_of_not_admissible c ξ Φ W D H g a b e h ht
      simp only [hz', mul_zero, Finset.sum_const_zero, tsum_zero]
  have hswap (t : Ideal O × Ideal O × Ideal O) :
      (∑' e : Ideal O, ∑' h : O, ∑ ξ ∈ Ξ, coeffs ξ *
        R ξ (t.1, e, h, t.2.1, t.2.2)) =
          ∑ ξ ∈ Ξ, coeffs ξ * ∑' r : Ideal O × O,
            R ξ (expansionRayTranspose (t, r)) := by
    have hrows (ξ : RayCharacter c) : Summable (fun r : Ideal O × O =>
        coeffs ξ * R ξ (expansionRayTranspose (t, r))) :=
      ((hs ξ).prod_factor t).mul_left _
    have hsum : Summable (fun r : Ideal O × O => ∑ ξ ∈ Ξ,
        coeffs ξ * R ξ (expansionRayTranspose (t, r))) :=
      (hasSum_sum (fun ξ _ => (hrows ξ).hasSum)).summable
    calc
      _ = ∑' r : Ideal O × O, ∑ ξ ∈ Ξ,
          coeffs ξ * R ξ (expansionRayTranspose (t, r)) := hsum.tsum_prod.symm
      _ = ∑ ξ ∈ Ξ, ∑' r : Ideal O × O,
          coeffs ξ * R ξ (expansionRayTranspose (t, r)) :=
        Summable.tsum_finsetSum (fun ξ _ => hrows ξ)
      _ = _ := by simp only [tsum_mul_left]
  have htotal : (∑' t : Ideal O × Ideal O × Ideal O, actualNonzeroTerm c Φ W D H t) =
      (H : ℂ) * ∑ ξ ∈ Ξ, coeffs ξ * ∑' t : ExpansionRayIndex, R ξ t := by
    simp_rw [hpoint, hswap]
    rw [tsum_mul_left, Summable.tsum_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [tsum_mul_left, ← (hs ξ).tsum_prod, expansionRayTranspose.tsum_eq]
    · intro ξ hξ
      exact (hs ξ).prod.mul_left _
  rw [actual_energy_zero_nonzero hp hz c Φ hW hD hH, htotal]
  change expansionOriginalDiagonal c Φ W D H + _ =
    expansionOriginalDiagonal c Φ W D H + _
  congr 1
  dsimp only [R, expansionCoprimeRayJoint]
  simp only [div_eq_mul_inv]
  ring

end QRHShort.CloudBatch





end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionParametricMobius.lean SHA256 c01320b4e94a357e97ab9fd9611f61ee93df326bb32a791ded59e53337a9f13a -/


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch

def expansionParametricMobius {α : Type*} (F : α × (Ideal O × Ideal O) → ℂ)
    (u : α × (Ideal O × Ideal O × Ideal O)) : ℂ :=
  (mobius u.2.1 : ℂ) * F (u.1, (u.2.1 * u.2.2.1, u.2.1 * u.2.2.2))

theorem expansion_parametric_mobius_hasFiniteSupport {α : Type*}
    (F : α × (Ideal O × Ideal O) → ℂ) (hF : Function.HasFiniteSupport F)
    (hF0 : ∀ t a, F (t, (⊥, a)) = 0) (hF0' : ∀ t a, F (t, (a, ⊥)) = 0) :
    Function.HasFiniteSupport (expansionParametricMobius F) := by
  have hfib : ∀ p ∈ Function.support F,
      (({p.1} : Set α) ×ˢ {v : Ideal O × Ideal O × Ideal O |
        v.1 * v.2.1 = p.2.1 ∧ v.1 * v.2.2 = p.2.2}).Finite := by
    intro p hp
    apply (Set.finite_singleton p.1).prod
    apply expansion_common_factor_fiber_finite
    · intro hz
      exact hp (by rw [show p = (p.1, (p.2.1, p.2.2)) from rfl, hz, hF0])
    · intro hz
      exact hp (by rw [show p = (p.1, (p.2.1, p.2.2)) from rfl, hz, hF0'])
  apply (hF.biUnion hfib).subset
  intro u hu
  have hn : F (u.1, (u.2.1 * u.2.2.1, u.2.1 * u.2.2.2)) ≠ 0 := by
    intro hz
    exact hu (by simp only [expansionParametricMobius, hz, mul_zero])
  exact Set.mem_iUnion₂.mpr
    ⟨(u.1, (u.2.1 * u.2.2.1, u.2.1 * u.2.2.2)), hn, ⟨rfl, rfl, rfl⟩⟩

theorem expansion_parametric_mobius_summable {α : Type*}
    (F : α × (Ideal O × Ideal O) → ℂ) (hF : Function.HasFiniteSupport F)
    (hF0 : ∀ t a, F (t, (⊥, a)) = 0) (hF0' : ∀ t a, F (t, (a, ⊥)) = 0) :
    Summable (expansionParametricMobius F) :=
  summable_of_hasFiniteSupport (expansion_parametric_mobius_hasFiniteSupport F hF hF0 hF0')

theorem expansion_parametric_common_divisor_mobius {α : Type*}
    (F : α × (Ideal O × Ideal O) → ℂ) (hF : Function.HasFiniteSupport F)
    (hF0 : ∀ t a, F (t, (⊥, a)) = 0) (hF0' : ∀ t a, F (t, (a, ⊥)) = 0) :
    (∑' t : α, ∑' v : Ideal O, ∑' a : Ideal O, ∑' b : Ideal O,
      (mobius v : ℂ) * F (t, (v * a, v * b))) =
        ∑' t : α, ∑' p : Ideal O × Ideal O,
          if IsRelPrime p.1 p.2 then F (t, p) else 0 := by
  apply tsum_congr
  intro t
  apply expansion_common_divisor_mobius (fun p => F (t, p))
  · exact hF.preimage (fun _ _ _ _ h => congrArg Prod.snd h)
  · exact hF0 t
  · exact hF0' t

theorem expansion_parametric_mobius_joint_tsum {α : Type*}
    (F : α × (Ideal O × Ideal O) → ℂ) (hF : Function.HasFiniteSupport F)
    (hF0 : ∀ t a, F (t, (⊥, a)) = 0) (hF0' : ∀ t a, F (t, (a, ⊥)) = 0) :
    (∑' u : α × (Ideal O × Ideal O × Ideal O), expansionParametricMobius F u) =
      ∑' t : α, ∑' v : Ideal O, ∑' a : Ideal O, ∑' b : Ideal O,
        (mobius v : ℂ) * F (t, (v * a, v * b)) := by
  have hs := expansion_parametric_mobius_summable F hF hF0 hF0'
  rw [hs.tsum_prod]
  apply tsum_congr
  intro t
  rw [(hs.prod_factor t).tsum_prod]
  apply tsum_congr
  intro v
  exact ((hs.prod_factor t).prod_factor v).tsum_prod

end QRHShort.CloudBatch





end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionKernelBridge.lean SHA256 61ca4ee3a1763395c8af5d1f7952dd1d2c4f094b37daf69dbc057e8c0f1c2969 -/


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch
open PoissonReductionProof

theorem expansion_initialWeight_pair_scale (W : ℝ → ℂ) {M D a b : ℝ}
    (hM : 0 < M) (hD : 0 < D) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt (a * b) : ℂ)⁻¹ * (star (W (M * a / D)) * W (M * b / D)) =
      (M / D : ℂ) *
        (initialWeight W (M * a / D) * star (initialWeight W (M * b / D))) := by
  have hscale : Real.sqrt (M * a / D) * Real.sqrt (M * b / D) =
      (M / D) * Real.sqrt (a * b) := by
    rw [show M * a / D = (M / D) * a by ring,
      show M * b / D = (M / D) * b by ring,
      Real.sqrt_mul (div_nonneg hM.le hD.le), Real.sqrt_mul (div_nonneg hM.le hD.le)]
    calc
      _ = (Real.sqrt (M / D)) ^ 2 * (Real.sqrt a * Real.sqrt b) := by ring
      _ = _ := by rw [Real.sq_sqrt (div_nonneg hM.le hD.le), ← Real.sqrt_mul ha]
  have hcast : (Real.sqrt (M * a / D) : ℂ) * (Real.sqrt (M * b / D) : ℂ) =
      (M / D : ℂ) * (Real.sqrt (a * b) : ℂ) := by
    exact_mod_cast hscale
  have hMD : (M / D : ℂ) ≠ 0 := div_ne_zero
    (Complex.ofReal_ne_zero.mpr hM.ne') (Complex.ofReal_ne_zero.mpr hD.ne')
  calc
    _ = (M / D : ℂ) * ((M / D : ℂ) * (Real.sqrt (a * b) : ℂ))⁻¹ *
        (star (W (M * a / D)) * W (M * b / D)) := by
      rw [mul_inv_rev]
      calc
        _ = (M / D : ℂ) * (M / D : ℂ)⁻¹ *
            ((Real.sqrt (a * b) : ℂ)⁻¹ *
              (star (W (M * a / D)) * W (M * b / D))) := by rw [mul_inv_cancel₀ hMD, one_mul]
        _ = _ := by ring
    _ = (M / D : ℂ) *
        (((Real.sqrt (M * a / D) : ℂ) * (Real.sqrt (M * b / D) : ℂ))⁻¹ *
          (star (W (M * a / D)) * W (M * b / D))) := by rw [hcast]; ring
    _ = _ := by
      simp [initialWeight, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

theorem expansion_initialAtom_bot (c : ArithmeticContext) (ξ : RayCharacter c)
    (b f : Ideal O) (k : O) : initialAtom c ξ b f k ⊥ = 0 := by
  unfold initialAtom
  apply if_neg
  intro hs
  exact hs.1.1.1 rfl

/-- The physical kernel and its square-root normalization transform with
the exact scalar Ng/D. All ideal columns, including zero columns, are covered. -/
theorem expansion_prePaired_kernel_bridge (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) {D : ℝ} (hD : 0 < D) (H : ℝ)
    {b e v : Ideal O} (hb : SquarefreeOutside c.S b) (he : SquarefreeOutside c.S e)
    (hv : SquarefreeOutside c.S v) (hbe : IsRelPrime b e)
    (hbv : IsRelPrime b v) (hev : IsRelPrime e v) (h : O) (n₁ n₂ : Ideal O) :
    expansionPrePairedTerm c ξ Φ W D H (e * b) e h (v * n₁, v * n₂) =
      if IsRelPrime v (principal h) then
        (normIdeal (e * b) / D : ℂ) *
          initialPairedTerm c ξ Φ W D H 1 1 b (e * v) (primaryGenerator e * h) (n₁, n₂)
      else 0 := by
  by_cases hn₁ : n₁ = ⊥
  · subst n₁
    simp only [Ideal.mul_bot, expansion_prePaired_bot_left, initialPairedTerm,
      expansion_initialAtom_bot, zero_mul, mul_zero, ite_self]
  by_cases hn₂ : n₂ = ⊥
  · subst n₂
    simp only [Ideal.mul_bot, expansion_prePaired_bot_right, initialPairedTerm,
      expansion_initialAtom_bot, star_zero, mul_zero, zero_mul, ite_self]
  have hNg : 0 < normIdeal (e * b) := normIdeal_pos (mul_ne_zero he.1.1 hb.1.1)
  have hNe : 0 < normIdeal e := normIdeal_pos he.1.1
  have hNv : 0 < normIdeal v := normIdeal_pos hv.1.1
  have hN₁ : 0 < normIdeal n₁ := normIdeal_pos hn₁
  have hN₂ : 0 < normIdeal n₂ := normIdeal_pos hn₂
  have hprim : normElement (primaryGenerator e) = normIdeal e := by
    change normIdeal (principal (primaryGenerator e)) = normIdeal e
    rw [expansion_primary_spec c he.1]
  have harg (n : Ideal O) :
      normIdeal (e * b) * normIdeal (v * n) / D =
        normIdeal b * normIdeal (e * v) * normIdeal n / D := by
    simp only [expansion_normIdeal_mul]
    ring
  have hf : H * normElement h / (normIdeal e * (normIdeal (v * n₁) * normIdeal (v * n₂))) =
      H * normElement (primaryGenerator e * h) /
        (normIdeal (e * v) ^ 2 * normIdeal n₁ * normIdeal n₂) := by
    rw [expansion_normElement_mul, hprim]
    simp only [expansion_normIdeal_mul]
    field_simp
  rw [expansionPrePairedTerm, expansion_paired_common_factor c hc ξ hb he hv hbe hbv hev]
  by_cases hh : IsRelPrime v (principal h)
  · rw [if_pos hh, if_pos hh,
      expansion_initialWeight_pair_scale W hNg hD
        (normIdeal_pos (mul_ne_zero hv.1.1 hn₁)).le
        (normIdeal_pos (mul_ne_zero hv.1.1 hn₂)).le,
      harg n₁, harg n₂, hf,
      expansion_pairedTerm_scale_invariant c ξ Φ W hD.ne' one_ne_zero one_ne_zero]
    ring
  · rw [if_neg hh, if_neg hh, zero_mul, zero_mul]

end QRHShort.CloudBatch




end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionRawKernel.lean SHA256 174ba1df8e8d5b1de749797ac40afaf65cc88c1a206a74d2c52711f2bc8ab282 -/


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch
open PoissonReductionProof

theorem expansion_preColumn_zero_bad_common (c : ArithmeticContext) (ξ : RayCharacter c)
    (g e v : Ideal O) (h : O) (n : Ideal O)
    (hv : ¬ (SquarefreeOutside c.S v ∧ IsRelPrime g v)) :
    expansionPreColumn c ξ g e h (v * n) = 0 := by
  unfold expansionPreColumn
  apply if_neg
  intro hs
  apply hv
  have hd : v ∣ v * n := ⟨n, rfl⟩
  exact ⟨⟨expansion_outside_of_dvd c hs.1.1 hd,
    hs.1.2.squarefree_of_dvd hd⟩, (hs.2.of_dvd_left hd).symm⟩

theorem expansion_prePaired_zero_bad_common (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (g e v : Ideal O) (h : O)
    (n₁ n₂ : Ideal O) (hv : ¬ (SquarefreeOutside c.S v ∧ IsRelPrime g v)) :
    expansionPrePairedTerm c ξ Φ W D H g e h (v * n₁, v * n₂) = 0 := by
  simp only [expansionPrePairedTerm, expansion_preColumn_zero_bad_common c ξ g e v h n₁ hv,
    zero_mul]

/-- On every genuine raw index the whole scalar, character, square-root
weight and physical Fourier kernel equal the original output integrand. -/
theorem expansion_raw_kernel_weight (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) {D : ℝ} (hD : 0 < D) (H : ℝ)
    (p : ExpansionRaw c) (n₁ n₂ : Ideal O) :
    (H / D : ℂ) * ((mobius p.val.2.1 : ℂ) / (normIdeal p.val.2.1 : ℂ)) *
      (mobius p.val.2.2.1 : ℂ) *
        expansionPrePairedTerm c ξ Φ W D H p.val.1 p.val.2.1 p.val.2.2.2
          (p.val.2.2.1 * n₁, p.val.2.2.1 * n₂) =
      (H / D ^ 2 : ℂ) * (normIdeal (expansionRawEquiv c p).val.1 : ℂ) *
        (mobius (expansionRawEquiv c p).val.2.1 : ℂ) *
          initialPairedTerm c ξ Φ W D H 1 1 (expansionRawEquiv c p).val.1
            (expansionRawEquiv c p).val.2.1 (expansionRawEquiv c p).val.2.2 (n₁, n₂) := by
  let s := expansionToSplit c p
  obtain ⟨hb, he, hv, hbe, hbv, hev, hh, hvh⟩ := s.property
  have hk := expansion_prePaired_kernel_bridge c hc ξ Φ W hD H hb he hv hbe hbv hev
    s.val.2.2.2 n₁ n₂
  rw [if_pos hvh] at hk
  change expansionPrePairedTerm c ξ Φ W D H
      (p.val.2.1 * expansionQuotient p.val.1 p.val.2.1) p.val.2.1 p.val.2.2.2
      (p.val.2.2.1 * n₁, p.val.2.2.1 * n₂) =
    (normIdeal (p.val.2.1 * expansionQuotient p.val.1 p.val.2.1) / D : ℂ) *
      initialPairedTerm c ξ Φ W D H 1 1 (expansionRawEquiv c p).val.1
        (expansionRawEquiv c p).val.2.1 (expansionRawEquiv c p).val.2.2 (n₁, n₂) at hk
  rw [expansionQuotient_spec p.property.2.2.2.1] at hk
  have hN : (normIdeal p.val.1 : ℂ) / (normIdeal p.val.2.1 : ℂ) =
      (normIdeal (expansionRawEquiv c p).val.1 : ℂ) := by
    exact_mod_cast expansionRawEquiv_norm_weight c p
  have hμ : (mobius p.val.2.1 : ℂ) * (mobius p.val.2.2.1 : ℂ) =
      (mobius (expansionRawEquiv c p).val.2.1 : ℂ) := by
    exact_mod_cast expansionRawEquiv_mobius c p
  rw [hk]
  calc
    _ = (H / D ^ 2 : ℂ) *
        ((normIdeal p.val.1 : ℂ) / (normIdeal p.val.2.1 : ℂ)) *
        ((mobius p.val.2.1 : ℂ) * (mobius p.val.2.2.1 : ℂ)) *
          initialPairedTerm c ξ Φ W D H 1 1 (expansionRawEquiv c p).val.1
            (expansionRawEquiv c p).val.2.1 (expansionRawEquiv c p).val.2.2 (n₁, n₂) := by
      simp only [div_eq_mul_inv, inv_pow]
      ring
    _ = _ := by rw [hN, hμ]

end QRHShort.CloudBatch




end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionDyadicPartition.lean SHA256 89a9096c8960d435764ed9059fde2db35d07efd6984c4eb6517d1c3489665974 -/


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch
open PoissonReductionProof

def expansionOutputJoint (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ)
    (p : ExpansionOutput c × (Ideal O × Ideal O)) : ℂ :=
  (H / D ^ 2 : ℝ) * (normIdeal p.1.val.1 : ℂ) * (mobius p.1.val.2.1 : ℂ) *
    initialPairedTerm c ξ Φ W D H 1 1 p.1.val.1 p.1.val.2.1 p.1.val.2.2 p.2

def expansionOutputBand (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (j l : ℕ)
    (p : ExpansionOutput c × (Ideal O × Ideal O)) : ℂ :=
  (H / D ^ 2 : ℝ) * expansionBlockJoint c ξ I Φ W D H (2 ^ j) (2 ^ l) (p.1.val, p.2)

theorem expansion_outputBand_eq_indicator (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) {D : ℝ} (hD : D ≠ 0)
    (H : ℝ) (j l : ℕ) (p : ExpansionOutput c × (Ideal O × Ideal O)) :
    expansionOutputBand c ξ I Φ W D H j l p =
      if ExpansionBlockRow c I Φ D H (2 ^ j) (2 ^ l) p.1.val then
        expansionOutputJoint c ξ Φ W D H p else 0 := by
  have hscale : initialPairedTerm c ξ Φ W D H (2 ^ j) (2 ^ l)
      p.1.val.1 p.1.val.2.1 p.1.val.2.2 p.2 =
      initialPairedTerm c ξ Φ W D H 1 1 p.1.val.1 p.1.val.2.1 p.1.val.2.2 p.2 := by
    rw [expansion_pairedTerm_scale_invariant c ξ Φ W hD (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num)),
      expansion_pairedTerm_scale_invariant c ξ Φ W hD one_ne_zero one_ne_zero]
  unfold expansionOutputBand expansionBlockJoint
  split_ifs with hr
  · rw [hscale]
    simp only [expansionOutputJoint, mul_assoc]
  · exact mul_zero _

theorem expansion_outputJoint_pointwise_partition (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H)
    (p : ExpansionOutput c × (Ideal O × Ideal O)) :
    expansionOutputJoint c ξ Φ W D H p =
      ∑ j ∈ Finset.range (initialDepth I D), ∑ l ∈ Finset.range (initialDepth I D),
        expansionOutputBand c ξ I Φ W D H j l p := by
  simp_rw [expansion_outputBand_eq_indicator c ξ I Φ W hD.ne']
  by_cases hz : expansionOutputJoint c ξ Φ W D H p = 0
  · simp only [hz, ite_self, Finset.sum_const_zero]
  have hpair : initialPairedTerm c ξ Φ W D H 1 1
      p.1.val.1 p.1.val.2.1 p.1.val.2.2 p.2 ≠ 0 := by
    intro hn
    exact hz (by simp only [expansionOutputJoint, hn, mul_zero])
  obtain ⟨⟨j₀, hj, hjuniq⟩, ⟨l₀, hl, hluniq⟩⟩ :=
    expansion_pairedTerm_dyadic_cover c ξ I Φ hW hD one_ne_zero one_ne_zero H
      p.1.val.1 p.1.val.2.1 p.1.property.1.1.1 p.1.property.2.1.1.1
      p.1.val.2.2 p.2 hpair
  have hheight := expansion_pairedTerm_height_bound c ξ I Φ hW hD hH
    (pow_pos (by norm_num : (0 : ℝ) < 2) j₀) (pow_pos (by norm_num : (0 : ℝ) < 2) l₀)
    p.1.val.1 p.1.val.2.1 p.1.property.1.1.1 p.1.property.2.1.1.1 hj.2.1 p.1.val.2.2 p.2
    (by
      rw [expansion_pairedTerm_scale_invariant c ξ Φ W hD.ne'
        (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))]
      rw [expansion_pairedTerm_scale_invariant c ξ Φ W hD.ne' one_ne_zero one_ne_zero] at hpair
      exact hpair)
  have hkpos : 0 < normElement p.1.val.2.2 := by
    apply normIdeal_pos
    intro hz
    apply p.1.property.2.2.2
    exact Ideal.span_singleton_eq_bot.mp hz
  have hr : ExpansionBlockRow c I Φ D H (2 ^ j₀) (2 ^ l₀) p.1.val :=
    ⟨p.1.property.1, hj.2.1, hj.2.2, p.1.property.2.1, hl.2.1, hl.2.2,
      p.1.property.2.2.1, hkpos, hheight⟩
  symm
  rw [Finset.sum_eq_single j₀]
  · rw [Finset.sum_eq_single l₀]
    · exact if_pos hr
    · intro l hll hlj
      apply if_neg
      intro hrow
      exact hlj (expansion_dyadic_unique ⟨hrow.2.2.2.2.1, hrow.2.2.2.2.2.1⟩ hl.2)
    · intro hnot
      exact (hnot hl.1).elim
  · intro j hjj hjn
    apply Finset.sum_eq_zero
    intro l hll
    apply if_neg
    intro hrow
    exact hjn (expansion_dyadic_unique ⟨hrow.2.1, hrow.2.2.1⟩ hj.2)
  · intro hnot
    exact (hnot hj.1).elim

theorem expansion_outputBand_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (H : ℝ) (j l : ℕ) :
    Function.HasFiniteSupport (expansionOutputBand c ξ I Φ W D H j l) := by
  have hinj : Function.Injective (fun p : ExpansionOutput c × (Ideal O × Ideal O) => (p.1.val, p.2)) := by
    intro p q he
    have hfirst : p.1.val = q.1.val := congrArg (fun x : (Ideal O × Ideal O × O) × (Ideal O × Ideal O) => x.1) he
    have hsecond : p.2 = q.2 := congrArg (fun x : (Ideal O × Ideal O × O) × (Ideal O × Ideal O) => x.2) he
    exact Prod.ext (Subtype.ext hfirst) hsecond
  have hf : Function.HasFiniteSupport (fun p : ExpansionOutput c × (Ideal O × Ideal O) =>
      expansionBlockJoint c ξ I Φ W D H (2 ^ j) (2 ^ l) (p.1.val, p.2)) :=
    (expansion_block_joint_hasFiniteSupport c ξ I Φ hW (B := (2 : ℝ) ^ j) (F := (2 : ℝ) ^ l) hD
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) H).preimage hinj.injOn
  apply hf.subset
  intro p hp
  intro hz
  exact hp (by simp only [expansionOutputBand, hz, mul_zero])

theorem expansion_outputJoint_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Function.HasFiniteSupport (expansionOutputJoint c ξ Φ W D H) := by
  let J := Finset.range (initialDepth I D)
  have hfinite : (⋃ j ∈ J, ⋃ l ∈ J,
      Function.support (expansionOutputBand c ξ I Φ W D H j l)).Finite :=
    J.finite_toSet.biUnion (fun j hj => J.finite_toSet.biUnion
      (fun l hl => expansion_outputBand_hasFiniteSupport c ξ I Φ hW hD H j l))
  apply hfinite.subset
  intro p hp
  by_contra hn
  apply hp
  rw [expansion_outputJoint_pointwise_partition c ξ I Φ hW hD hH p]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro l hl
  by_contra hz
  exact hn (Set.mem_iUnion₂.mpr ⟨j, hj, Set.mem_iUnion₂.mpr ⟨l, hl, hz⟩⟩)

theorem expansion_outputBand_tsum (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D : ℝ} (hD : 0 < D) (H : ℝ) (j l : ℕ) :
    (∑' p : ExpansionOutput c × (Ideal O × Ideal O), expansionOutputBand c ξ I Φ W D H j l p) =
      initialDyadicBlock c ξ I Φ W D H (2 ^ j) (2 ^ l) := by
  let f := expansionBlockJoint c ξ I Φ W D H (2 ^ j) (2 ^ l)
  have hs : Summable f := expansion_block_joint_summable c ξ I Φ hW hD
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) H
  have hinj : Function.Injective (fun p : ExpansionOutput c × (Ideal O × Ideal O) => (p.1.val, p.2)) := by
    intro p q he
    have hfirst : p.1.val = q.1.val := congrArg (fun x : (Ideal O × Ideal O × O) × (Ideal O × Ideal O) => x.1) he
    have hsecond : p.2 = q.2 := congrArg (fun x : (Ideal O × Ideal O × O) × (Ideal O × Ideal O) => x.2) he
    exact Prod.ext (Subtype.ext hfirst) hsecond
  have hs' := hs.comp_injective hinj
  calc
    _ = (H / D ^ 2 : ℝ) * ∑' p : ExpansionOutput c × (Ideal O × Ideal O), f (p.1.val, p.2) :=
      tsum_mul_left
    _ = (H / D ^ 2 : ℝ) * ∑' p : ExpansionOutput c, ∑' n : Ideal O × Ideal O, f (p.val, n) := by
      congr 1
      exact hs'.tsum_prod
    _ = _ := by
      symm
      rw [expansion_initialDyadicBlock_eq_joint c ξ I Φ hW hD
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) H,
        hs.tsum_prod, ← tsum_subtype_eq_of_support_subset
          (expansion_block_support_output c ξ I Φ W D H (2 ^ j) (2 ^ l))]
      rfl

theorem expansion_outputJoint_dyadic_partition (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 2 ≤ D) (hH : 0 < H) :
    (∑' p : ExpansionOutput c × (Ideal O × Ideal O), expansionOutputJoint c ξ Φ W D H p) =
      ∑ j ∈ Finset.range (initialDepth I D), ∑ l ∈ Finset.range (initialDepth I D),
        initialDyadicBlock c ξ I Φ W D H (2 ^ j) (2 ^ l) := by
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hs (j l : ℕ) : Summable (expansionOutputBand c ξ I Φ W D H j l) :=
    summable_of_hasFiniteSupport (L := .unconditional _)
      (expansion_outputBand_hasFiniteSupport c ξ I Φ hW hDpos H j l)
  calc
    _ = ∑' p : ExpansionOutput c × (Ideal O × Ideal O),
        ∑ j ∈ Finset.range (initialDepth I D), ∑ l ∈ Finset.range (initialDepth I D),
          expansionOutputBand c ξ I Φ W D H j l p :=
      tsum_congr (expansion_outputJoint_pointwise_partition c ξ I Φ hW hDpos hH)
    _ = ∑ j ∈ Finset.range (initialDepth I D), ∑' p : ExpansionOutput c × (Ideal O × Ideal O),
        ∑ l ∈ Finset.range (initialDepth I D), expansionOutputBand c ξ I Φ W D H j l p :=
      Summable.tsum_finsetSum (fun j hj => summable_sum (fun l hl => hs j l))
    _ = ∑ j ∈ Finset.range (initialDepth I D), ∑ l ∈ Finset.range (initialDepth I D),
        ∑' p : ExpansionOutput c × (Ideal O × Ideal O), expansionOutputBand c ξ I Φ W D H j l p := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun l hl => hs j l)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      exact expansion_outputBand_tsum c ξ I Φ hW hDpos H j l

end QRHShort.CloudBatch







end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionRawSupport.lean SHA256 3831c2648286b40a0762cd460b5c913645ad19a8132b14cf33d63057ea2b4c70 -/



noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch

theorem expansion_preColumn_zero_bad_frequency (c : ArithmeticContext) (ξ : RayCharacter c)
    (g e : Ideal O) {v : Ideal O} (hv : Outside c.S v) (h : O) (n : Ideal O)
    (hh : ¬ IsRelPrime v (principal h)) :
    expansionPreColumn c ξ g e h (v * n) = 0 := by
  have hz : sexticSymbol v h = 0 :=
    expansion_sexticSymbol_zero_of_not_isRelPrime c hv h (fun he => hh he.symm)
  unfold expansionPreColumn
  split_ifs
  · rw [expansion_sexticSymbol_mul v n h, hz, zero_mul, mul_zero]
  · rfl

theorem expansion_prePaired_zero_bad_frequency (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (g e : Ideal O) {v : Ideal O}
    (hv : Outside c.S v) (h : O) (n₁ n₂ : Ideal O)
    (hh : ¬ IsRelPrime v (principal h)) :
    expansionPrePairedTerm c ξ Φ W D H g e h (v * n₁, v * n₂) = 0 := by
  simp only [expansionPrePairedTerm,
    expansion_preColumn_zero_bad_frequency c ξ g e hv h n₁ hh, zero_mul]

/-- The full six-index integrand after genuine common-divisor inversion. -/
def expansionAllRawWeight (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ)
    (p : Ideal O × Ideal O × Ideal O × O) (n : Ideal O × Ideal O) : ℂ :=
  if SquarefreeOutside c.S p.1 ∧ p.2.1 ∣ p.1 ∧ p.2.2.2 ≠ 0 then
    (H / D : ℂ) * ((mobius p.2.1 : ℂ) / (normIdeal p.2.1 : ℂ)) *
      (mobius p.2.2.1 : ℂ) *
        expansionPrePairedTerm c ξ Φ W D H p.1 p.2.1 p.2.2.2
          (p.2.2.1 * n.1, p.2.2.1 * n.2)
  else 0

/-- No raw-index restriction is imposed without proof: every excluded
common factor or frequency makes the genuine column itself vanish. -/
theorem expansion_allRawWeight_zero_of_not_admissible (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ)
    (p : Ideal O × Ideal O × Ideal O × O) (n : Ideal O × Ideal O)
    (hp : ¬ ExpansionRawAdmissible c p) : expansionAllRawWeight c ξ Φ W D H p n = 0 := by
  unfold expansionAllRawWeight
  split_ifs with hs
  · by_cases hv : SquarefreeOutside c.S p.2.2.1 ∧ IsRelPrime p.1 p.2.2.1
    · have hh : ¬ IsRelPrime p.2.2.1 (principal p.2.2.2) := by
        intro hh
        exact hp ⟨hs.1, hv.1, hv.2, hs.2.1, hs.2.2, hh⟩
      rw [expansion_prePaired_zero_bad_frequency c ξ Φ W D H p.1 p.2.1 hv.1.1
        p.2.2.2 n.1 n.2 hh, mul_zero]
    · rw [expansion_prePaired_zero_bad_common c ξ Φ W D H p.1 p.2.1 p.2.2.1
        p.2.2.2 n.1 n.2 hv, mul_zero]
  · rfl

/-- The surviving raw integrand is exactly the frozen global output
integrand under the genuine (g,e,v,h) ↔ (b,f,k) equivalence. -/
theorem expansion_allRawWeight_eq_output (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ) {D : ℝ} (hD : 0 < D) (H : ℝ)
    (p : ExpansionRaw c) (n : Ideal O × Ideal O) :
    expansionAllRawWeight c ξ Φ W D H p.val n =
      expansionOutputJoint c ξ Φ W D H (expansionRawEquiv c p, n) := by
  have hs : SquarefreeOutside c.S p.val.1 ∧ p.val.2.1 ∣ p.val.1 ∧ p.val.2.2.2 ≠ 0 :=
    ⟨p.property.1, p.property.2.2.2.1, p.property.2.2.2.2.1⟩
  rw [expansionAllRawWeight, if_pos hs]
  simpa only [expansionOutputJoint, Complex.ofReal_div, Complex.ofReal_pow,
    Prod.mk.eta] using expansion_raw_kernel_weight c hc ξ Φ W hD H p n.1 n.2

end QRHShort.CloudBatch





end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionRayOutput.lean SHA256 7e030fc535d6e19b4e48b46e15522821814c49639547fe3cf02d5348dcf09f36 -/




noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch

def expansionRayPairEquiv :
    ((Ideal O × Ideal O × O) × (Ideal O × Ideal O)) ≃
      (Ideal O × Ideal O × O × (Ideal O × Ideal O)) where
  toFun p := (p.1.1, p.1.2.1, p.1.2.2, p.2)
  invFun p := ((p.1, p.2.1, p.2.2.1), p.2.2.2)
  left_inv p := by rcases p with ⟨⟨g, e, h⟩, n⟩; rfl
  right_inv p := by rcases p with ⟨g, e, h, n⟩; rfl

def expansionRawMobiusEquiv :
    ((Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O)) ≃
      ((Ideal O × Ideal O × O) × (Ideal O × Ideal O × Ideal O)) where
  toFun p := ((p.1.1, p.1.2.1, p.1.2.2.2), (p.1.2.2.1, p.2.1, p.2.2))
  invFun p := ((p.1.1, p.1.2.1, p.2.1, p.1.2.2), (p.2.2.1, p.2.2.2))
  left_inv p := by rcases p with ⟨⟨g, e, v, h⟩, a, b⟩; rfl
  right_inv p := by rcases p with ⟨⟨g, e, h⟩, v, a, b⟩; rfl

def expansionRawPairSubtypeEquiv (c : ArithmeticContext) :
    (ExpansionRaw c × (Ideal O × Ideal O)) ≃
      {p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O) // ExpansionRawAdmissible c p.1} where
  toFun p := ⟨(p.1.val, p.2), p.1.property⟩
  invFun p := (⟨p.val.1, p.property⟩, p.val.2)
  left_inv p := by rcases p with ⟨⟨p, hp⟩, n⟩; rfl
  right_inv p := by rcases p with ⟨⟨p, n⟩, hp⟩; rfl

def expansionRayAsPair (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ)
    (p : (Ideal O × Ideal O × O) × (Ideal O × Ideal O)) : ℂ :=
  expansionRayJoint c ξ Φ W D H (expansionRayPairEquiv p)

theorem expansion_rayAsPair_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Function.HasFiniteSupport (expansionRayAsPair c ξ Φ W D H) :=
  (expansion_rayJoint_hasFiniteSupport c ξ I Φ hW hD hH).preimage
    expansionRayPairEquiv.injective.injOn

theorem expansion_rayAsPair_bot_left (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (t : Ideal O × Ideal O × O) (a : Ideal O) :
    expansionRayAsPair c ξ Φ W D H (t, (⊥, a)) = 0 := by
  change (if SquarefreeOutside c.S t.1 ∧ t.2.1 ∣ t.1 ∧ t.2.2 ≠ 0 then
    (mobius t.2.1 : ℂ) / (normIdeal t.2.1 : ℂ) *
      expansionPrePairedTerm c ξ Φ W D H t.1 t.2.1 t.2.2 (⊥, a) else 0) = 0
  simp only [expansion_prePaired_bot_left, mul_zero, ite_self]

theorem expansion_rayAsPair_bot_right (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ) (t : Ideal O × Ideal O × O) (a : Ideal O) :
    expansionRayAsPair c ξ Φ W D H (t, (a, ⊥)) = 0 := by
  change (if SquarefreeOutside c.S t.1 ∧ t.2.1 ∣ t.1 ∧ t.2.2 ≠ 0 then
    (mobius t.2.1 : ℂ) / (normIdeal t.2.1 : ℂ) *
      expansionPrePairedTerm c ξ Φ W D H t.1 t.2.1 t.2.2 (a, ⊥) else 0) = 0
  simp only [expansion_prePaired_bot_right, mul_zero, ite_self]

theorem expansion_parametric_raw_weight (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H : ℝ)
    (p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O)) :
    (H / D : ℂ) * expansionParametricMobius (expansionRayAsPair c ξ Φ W D H)
      (expansionRawMobiusEquiv p) = expansionAllRawWeight c ξ Φ W D H p.1 p.2 := by
  change (H / D : ℂ) * ((mobius p.1.2.2.1 : ℂ) *
    expansionRayJoint c ξ Φ W D H (p.1.1, p.1.2.1, p.1.2.2.2,
      (p.1.2.2.1 * p.2.1, p.1.2.2.1 * p.2.2))) = _
  unfold expansionRayJoint expansionAllRawWeight
  split_ifs <;> ring

theorem expansion_allRawWeight_hasFiniteSupport (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    Function.HasFiniteSupport (fun p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O) =>
      expansionAllRawWeight c ξ Φ W D H p.1 p.2) := by
  have hF := expansion_rayAsPair_hasFiniteSupport c ξ I Φ hW hD hH
  have hG := expansion_parametric_mobius_hasFiniteSupport (expansionRayAsPair c ξ Φ W D H) hF
    (expansion_rayAsPair_bot_left c ξ Φ W D H) (expansion_rayAsPair_bot_right c ξ Φ W D H)
  have hpre : Function.HasFiniteSupport (fun p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O) =>
      expansionParametricMobius (expansionRayAsPair c ξ Φ W D H) (expansionRawMobiusEquiv p)) :=
    hG.preimage expansionRawMobiusEquiv.injective.injOn
  apply hpre.subset
  intro p hp
  intro hz
  exact hp (by
    change expansionAllRawWeight c ξ Φ W D H p.1 p.2 = 0
    rw [← expansion_parametric_raw_weight c ξ Φ W D H p]
    exact mul_eq_zero_of_right _ hz)

/-- Exact finite-support passage from the ray integrand to the original
output variables. All restrictions and index permutations are proved. -/
theorem expansion_ray_joint_eq_output (c : ArithmeticContext) (hc : ArithmeticRelations c)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {D H : ℝ} (hD : 0 < D) (hH : 0 < H) :
    (H / D : ℂ) * (∑' t : Ideal O × Ideal O × O × (Ideal O × Ideal O),
      if IsRelPrime t.2.2.2.1 t.2.2.2.2 then expansionRayJoint c ξ Φ W D H t else 0) =
        ∑' p : ExpansionOutput c × (Ideal O × Ideal O), expansionOutputJoint c ξ Φ W D H p := by
  let F := expansionRayAsPair c ξ Φ W D H
  have hF : Function.HasFiniteSupport F := expansion_rayAsPair_hasFiniteSupport c ξ I Φ hW hD hH
  have hF0 := expansion_rayAsPair_bot_left c ξ Φ W D H
  have hF0' := expansion_rayAsPair_bot_right c ξ Φ W D H
  have hfiltered : Function.HasFiniteSupport (fun p : (Ideal O × Ideal O × O) × (Ideal O × Ideal O) =>
      if IsRelPrime p.2.1 p.2.2 then F p else 0) := by
    apply hF.subset
    intro p hp
    intro hz
    exact hp (by
      change (if IsRelPrime p.2.1 p.2.2 then F p else 0) = 0
      rw [hz]
      simp)
  have hsfiltered : Summable (fun p : (Ideal O × Ideal O × O) × (Ideal O × Ideal O) =>
      if IsRelPrime p.2.1 p.2.2 then F p else 0) :=
    summable_of_hasFiniteSupport (L := .unconditional _) hfiltered
  have hm := expansion_parametric_common_divisor_mobius F hF hF0 hF0'
  have hj := expansion_parametric_mobius_joint_tsum F hF hF0 hF0'
  have hG := expansion_parametric_mobius_hasFiniteSupport F hF hF0 hF0'
  let fraw := fun p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O) =>
    expansionAllRawWeight c ξ Φ W D H p.1 p.2
  have hrestrict : Function.support fraw ⊆
      {p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O) | ExpansionRawAdmissible c p.1} := by
    intro p hp
    by_contra hn
    exact hp (expansion_allRawWeight_zero_of_not_admissible c ξ Φ W D H p.1 p.2 hn)
  calc
    _ = (H / D : ℂ) * ∑' p : (Ideal O × Ideal O × O) × (Ideal O × Ideal O),
        if IsRelPrime p.2.1 p.2.2 then F p else 0 := by
      congr 1
      exact (expansionRayPairEquiv.tsum_eq (fun t : Ideal O × Ideal O × O × (Ideal O × Ideal O) =>
        if IsRelPrime t.2.2.2.1 t.2.2.2.2 then expansionRayJoint c ξ Φ W D H t else 0)).symm
    _ = (H / D : ℂ) * ∑' u : (Ideal O × Ideal O × O) × (Ideal O × Ideal O × Ideal O),
        expansionParametricMobius F u := by rw [hsfiltered.tsum_prod, ← hm, ← hj]
    _ = (H / D : ℂ) * ∑' p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O),
        expansionParametricMobius F (expansionRawMobiusEquiv p) := by
      rw [expansionRawMobiusEquiv.tsum_eq]
    _ = ∑' p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O), fraw p := by
      rw [← tsum_mul_left]
      apply tsum_congr
      exact expansion_parametric_raw_weight c ξ Φ W D H
    _ = ∑' p : {p : (Ideal O × Ideal O × Ideal O × O) × (Ideal O × Ideal O) //
        ExpansionRawAdmissible c p.1}, fraw p.val :=
      (tsum_subtype_eq_of_support_subset hrestrict).symm
    _ = ∑' p : ExpansionRaw c × (Ideal O × Ideal O), fraw (p.1.val, p.2) :=
      ((expansionRawPairSubtypeEquiv c).tsum_eq (fun p => fraw p.val)).symm
    _ = ∑' p : ExpansionRaw c × (Ideal O × Ideal O),
        expansionOutputJoint c ξ Φ W D H (expansionRawEquiv c p.1, p.2) := by
      apply tsum_congr
      intro p
      exact expansion_allRawWeight_eq_output c hc ξ Φ W hD H p.1 p.2
    _ = _ := (Equiv.prodCongr (expansionRawEquiv c) (Equiv.refl (Ideal O × Ideal O))).tsum_eq _

end QRHShort.CloudBatch







end
end

section
/- Frozen original Poisson expansion fragment PoissonExpansionComplete.lean SHA256 9caaa719922b70701e0331113065adbec976c28cf1a69a378a0331c973cd5f7d -/




noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.CloudBatch
open PoissonReductionProof

theorem expansion_finite_block_norm_le {α : Type*} (Ξ : Finset α) (a : α → ℂ)
    (J : Finset ℕ) (B : α → ℕ → ℕ → ℂ) :
    ‖∑ ξ ∈ Ξ, a ξ * ∑ j ∈ J, ∑ l ∈ J, B ξ j l‖ ≤
      (∑ ξ ∈ Ξ, ‖a ξ‖) * ∑ ξ ∈ Ξ, ∑ j ∈ J, ∑ l ∈ J, ‖B ξ j l‖ := by
  calc
    _ ≤ ∑ ξ ∈ Ξ, ‖a ξ * ∑ j ∈ J, ∑ l ∈ J, B ξ j l‖ := norm_sum_le _ _
    _ ≤ ∑ ξ ∈ Ξ, ‖a ξ‖ * ∑ j ∈ J, ∑ l ∈ J, ‖B ξ j l‖ := by
      apply Finset.sum_le_sum
      intro ξ hξ
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
    _ ≤ ∑ ξ ∈ Ξ, (∑ η ∈ Ξ, ‖a η‖) * ∑ j ∈ J, ∑ l ∈ J, ‖B ξ j l‖ := by
      apply Finset.sum_le_sum
      intro ξ hξ
      apply mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun η _ => norm_nonneg (a η)) hξ)
      exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem poisson_reduction_dyadic_expansion_proved : PoissonDyadicExpansionInput := by
  intro hp hz c I hc
  obtain ⟨Φ, hsharp⟩ := expansion_uniform_sharp_to_schwartz c I
  obtain ⟨Ξ, coeffs, henergy⟩ := expansion_original_energy_ray hp hz c hc
  obtain ⟨Z, hZ, hdiag⟩ := expansion_originalDiagonal_uniform_bound c I Φ
  let A : ℝ := ∑ ξ ∈ Ξ, ‖coeffs ξ‖
  refine ⟨Φ, Ξ, A, Z, Finset.sum_nonneg (fun ξ _ => norm_nonneg _), hZ, ?_⟩
  intro W D H hW hD hH
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have heq : (expansionSmoothedEnergy c Φ W D H : ℂ) =
      expansionOriginalDiagonal c Φ W D H +
        ∑ ξ ∈ Ξ, coeffs ξ * ∑ j ∈ Finset.range (initialDepth I D),
          ∑ l ∈ Finset.range (initialDepth I D),
            initialDyadicBlock c ξ I Φ W D H ((2 : ℝ) ^ j) ((2 : ℝ) ^ l) := by
    rw [henergy I Φ W D H hW hDpos hH, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [mul_left_comm (H / D : ℂ) (coeffs ξ),
      expansion_ray_joint_eq_output c hc ξ I Φ hW hDpos hH,
      expansion_outputJoint_dyadic_partition c ξ I Φ hW hD hH]
  have hE : expansionSmoothedEnergy c Φ W D H ≤
      ‖(expansionSmoothedEnergy c Φ W D H : ℂ)‖ := by
    simpa only [Complex.ofReal_re] using
      Complex.re_le_norm (expansionSmoothedEnergy c Φ W D H : ℂ)
  have hnorm : ‖(expansionSmoothedEnergy c Φ W D H : ℂ)‖ ≤
      Z * weightNorm 0 W ^ 2 * H + A *
        ∑ ξ ∈ Ξ, ∑ j ∈ Finset.range (initialDepth I D),
          ∑ l ∈ Finset.range (initialDepth I D),
            ‖initialDyadicBlock c ξ I Φ W D H ((2 : ℝ) ^ j) ((2 : ℝ) ^ l)‖ := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (hdiag W D H hW hDpos hH)
      (expansion_finite_block_norm_le Ξ coeffs (Finset.range (initialDepth I D))
        (fun ξ j l => initialDyadicBlock c ξ I Φ W D H ((2 : ℝ) ^ j) ((2 : ℝ) ^ l))))
  exact (hsharp W D H hW hD hH).trans
    (mul_le_mul_of_nonneg_left (hE.trans hnorm) hDpos.le)

example : QRHShort.PoissonReductionProof.PoissonDyadicExpansionInput :=
  QRHShort.CloudBatch.poisson_reduction_dyadic_expansion_proved

example :
    QRHShort.PoissonStatement → QRHShort.PoissonZeroStatement →
    ∀ (c : QRHShort.ArithmeticContext) (I : QRHShort.SupportInterval),
      QRHShort.ArithmeticRelations c →
      ∃ (Φ : QRHShort.RowWeight) (Ξ : Finset (QRHShort.RayCharacter c)) (A Z : ℝ),
        0 ≤ A ∧ 0 ≤ Z ∧ ∀ (W : ℝ → ℂ) (D H : ℝ),
          QRHShort.SmoothSupported I W → 2 ≤ D → 0 < H →
          QRHShort.originalMeanSquare c W D H ≤
            D * (Z * QRHShort.weightNorm 0 W ^ 2 * H + A *
              ∑ ξ ∈ Ξ, ∑ j ∈ Finset.range (QRHShort.PoissonReductionProof.initialDepth I D),
                ∑ l ∈ Finset.range (QRHShort.PoissonReductionProof.initialDepth I D),
                  ‖QRHShort.PoissonReductionProof.initialDyadicBlock c ξ I Φ W D H
                    ((2 : ℝ) ^ j) ((2 : ℝ) ^ l)‖) :=
  QRHShort.CloudBatch.poisson_reduction_dyadic_expansion_proved

end QRHShort.CloudBatch



end
end
