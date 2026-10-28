import QRHShort.MixedGaussEvaluation

/-! Exact squarefree extension of the mixed identity. The prime evaluation is
combined with the general-exponent CRT formula proved below, yielding the
original statement without additional hypotheses. -/

noncomputable section
open Classical

namespace QRHShort.ArithmeticProof.MixedGauss
open SquarefreeReflection
open SquarefreeReflection.RayValuePrerequisites

/-- The odd-exponent part of CRT, isolated from the already routed cubic CRT
statement. Both twists are present; no reciprocity assertion is assumed. -/
def OddGaussCRTStatement : Prop :=
  ∀ (c : ArithmeticContext) (a b : Ideal O),
    SquarefreeOutside c.S a → SquarefreeOutside c.S b → IsRelPrime a b →
    ∀ j : ℕ, (j = 1 ∨ j = 3) →
      gauss (j : ℤ) (a * b) = gauss (j : ℤ) a * gauss (j : ℤ) b *
        (sexticSymbol a (primaryGenerator b) *
          sexticSymbol b (primaryGenerator a)) ^ j

theorem sexticSymbol_mul_denominator {a b : Ideal O}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (x : O) :
    sexticSymbol (a * b) x = sexticSymbol a x * sexticSymbol b x := by
  have hab : a * b ≠ ⊥ := mul_ne_zero ha hb
  simp only [sexticSymbol, if_neg ha, if_neg hb, if_neg hab,
    UniqueFactorizationMonoid.normalizedFactors_mul ha hb,
    Multiset.map_add, Multiset.prod_add]

theorem sexticSymbol_one_denominator (x : O) : sexticSymbol 1 x = 1 := by
  simp only [sexticSymbol, if_neg (show (1 : Ideal O) ≠ ⊥ from one_ne_zero),
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

theorem gauss_one (j : ℤ) : gauss j 1 = 1 := by
  have hne : (1 : Ideal O) ≠ ⊥ := one_ne_zero
  unfold gauss
  rw [dif_pos hne]
  simp only [sexticSymbol_one_denominator, one_zpow, primaryGenerator_one,
    embedding_one, div_one, additiveCharacter_embedding, mul_one]
  simp [normIdeal]

/-- The two sides of the local identity acquire the same CRT twist, because
its sixth power is one. This is independent of any cubic Gauss evaluation. -/
theorem mixed_scalar_mul {a₁ a₂ a₃ b₁ b₂ b₃ u v t : ℂ}
    (ha : a₁ * a₂ = a₂ ^ (3 : ℕ) * (star u * a₃))
    (hb : b₁ * b₂ = b₂ ^ (3 : ℕ) * (star v * b₃))
    (ht : t ^ (6 : ℕ) = 1) :
    (a₁ * b₁ * t) * (a₂ * b₂ * t ^ (2 : ℕ)) =
      (a₂ * b₂ * t ^ (2 : ℕ)) ^ (3 : ℕ) *
        (star (u * v) * (a₃ * b₃ * t ^ (3 : ℕ))) := by
  have hcube : (a₂ * b₂ * t ^ (2 : ℕ)) ^ (3 : ℕ) =
      a₂ ^ (3 : ℕ) * b₂ ^ (3 : ℕ) := by
    rw [mul_pow, mul_pow, ← pow_mul, ht, mul_one]
  rw [hcube, star_mul]
  calc
    (a₁ * b₁ * t) * (a₂ * b₂ * t ^ (2 : ℕ)) =
        (a₁ * a₂) * (b₁ * b₂) * t ^ (3 : ℕ) := by ring
    _ = _ := by rw [ha, hb]; ring

theorem mixed_mul (hodd : OddGaussCRTStatement) (hcrt : CubicGaussCRTStatement)
    (c : ArithmeticContext) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b)
    (hma : gauss 1 a * gauss 2 a =
      gauss 2 a ^ (3 : ℕ) * (star (sexticSymbol a 4) * gauss 3 a))
    (hmb : gauss 1 b * gauss 2 b =
      gauss 2 b ^ (3 : ℕ) * (star (sexticSymbol b 4) * gauss 3 b)) :
    gauss 1 (a * b) * gauss 2 (a * b) =
      gauss 2 (a * b) ^ (3 : ℕ) *
        (star (sexticSymbol (a * b) 4) * gauss 3 (a * b)) := by
  let t := sexticSymbol a (primaryGenerator b) * sexticSymbol b (primaryGenerator a)
  have ht : t ^ (6 : ℕ) = 1 := by
    have hab' : IsRelPrime a (principal (primaryGenerator b)) := by
      rw [(primaryGenerator_spec_outside c hb.1).1]
      exact hab
    have hba' : IsRelPrime b (principal (primaryGenerator a)) := by
      rw [(primaryGenerator_spec_outside c ha.1).1]
      exact hab.symm
    dsimp only [t]
    rw [mul_pow, symbol_sixth c ha.1 _ hab', symbol_sixth c hb.1 _ hba', mul_one]
  have hg2 : gauss 2 (a * b) = gauss 2 a * gauss 2 b * t ^ (2 : ℕ) := by
    rw [hcrt c a b ha hb hab]
    simp only [t, mul_pow]
    ring
  have hg1 := hodd c a b ha hb hab 1 (Or.inl rfl)
  have hg3 := hodd c a b ha hb hab 3 (Or.inr rfl)
  simp only [Nat.cast_one, Nat.cast_ofNat, pow_one] at hg1 hg3
  rw [hg1, hg3, hg2, sexticSymbol_mul_denominator ha.1.1 hb.1.1]
  simpa only [Nat.cast_one, Nat.cast_ofNat, pow_one, t] using mixed_scalar_mul hma hmb ht

/-- This concludes exactly the frozen target from the odd CRT child and the
existing cubic CRT predecessor. Both dependencies are explicit propositions;
there is no dependence on the cubic evaluation or on ray reciprocity. -/
theorem mixedGaussEvaluation_of_crt (hodd : OddGaussCRTStatement)
    (hcrt : CubicGaussCRTStatement) : MixedGaussEvaluationStatement := by
  intro c n hn
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun a : Ideal O => SquarefreeOutside c.S a →
      gauss 1 a * gauss 2 a =
        gauss 2 a ^ (3 : ℕ) * (star (sexticSymbol a 4) * gauss 3 a)) n ?_ ?_ ?_ hn
  · intro h
    exact (h.1.1 rfl).elim
  · intro a ha _
    have he : a = 1 := isUnit_iff_eq_one.mp ha
    subst a
    simp only [gauss_one, sexticSymbol_one_denominator, one_pow, star_one, mul_one]
  · intro a P _ hp ih h
    have hfac := squarefree_mul_iff.mp h.2
    have hP : SquarefreeOutside c.S P :=
      ⟨outside_of_dvd h.1 (dvd_mul_right P a), hfac.2.1⟩
    have ha : SquarefreeOutside c.S a :=
      ⟨outside_of_dvd h.1 (dvd_mul_left a P), hfac.2.2⟩
    exact mixed_mul hodd hcrt c hP ha hfac.1 (prime_mixed c hp hP.1) (ih ha)

end QRHShort.ArithmeticProof.MixedGauss

#print axioms QRHShort.ArithmeticProof.MixedGauss.gauss_one
#print axioms QRHShort.ArithmeticProof.MixedGauss.mixedGaussEvaluation_of_crt

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations := (← getEnv).checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof.MixedGauss).isPrefixOf name then
        entries.push (name, info)
      else entries) (#[] : Array (Name × ConstantInfo))
  let mut checked : Nat := 0
  for (name, ci) in declarations do
    match ci with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Mixed Gauss extension depends on forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Mixed Gauss extension declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No mixed Gauss declarations audited"
  logInfo m!"MIXED_GAUSS_EXTENSION_AUDIT declarations={checked} forbidden=0 conditional_inputs=odd_CRT,cubic_CRT"


/-! General-exponent extension of the existing arithmetic CRT candidate.
The weighted CRT map and additive splitting are reused from ArithmeticGaussCRT;
only the character exponent is generalized. -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ArithmeticProof.MixedGauss.CRT
open QRHShort.ArithmeticProof.MixedGauss
@[simp] theorem lift_spec (n : Ideal O) (x : O ⧸ n) :
    Ideal.Quotient.mk n (residueLift n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

theorem symbol_congr {n : Ideal O} {a b : O}
    (hab : Ideal.Quotient.mk n a = Ideal.Quotient.mk n b) :
    sexticSymbol n a = sexticSymbol n b := by
  by_cases hn : n = ⊥
  · simp [sexticSymbol, hn]
  simp only [sexticSymbol, if_neg hn]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hnP : n ≤ P := Ideal.dvd_iff_le.mp
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
  have habP : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr
      (hnP ((Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab))
  simp only [sexticAtPrime, habP]

theorem symbol_mul_denominator {a b : Ideal O} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (x : O) : sexticSymbol (a * b) x = sexticSymbol a x * sexticSymbol b x := by
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, if_neg ha, if_neg hb, if_neg hab,
    UniqueFactorizationMonoid.normalizedFactors_mul ha hb,
    Multiset.map_add, Multiset.prod_add]

theorem ideals_coprime {a b : Ideal O} (h : IsRelPrime a b) : IsCoprime a b := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp
    (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

theorem generator_quotient_zero (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : Ideal.Quotient.mk n (primaryGenerator n) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hm : primaryGenerator n ∈ principal (primaryGenerator n) :=
    Ideal.subset_span (by simp)
  rwa [(SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c hn).1]
    at hm

theorem generator_unit (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b) :
    IsUnit (Ideal.Quotient.mk a (primaryGenerator b)) := by
  have hg : IsCoprime (primaryGenerator b) (primaryGenerator a) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    change IsCoprime (principal (primaryGenerator b)) (principal (primaryGenerator a))
    rw [(SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c hb).1,
      (SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c ha).1]
    exact (ideals_coprime hab).symm
  have hz := generator_quotient_zero c ha
  exact isCoprime_zero_right.mp (by
    simpa only [hz] using hg.map (Ideal.Quotient.mk a))

/-- Weighted CRT: the representative is b*x + a*y, so the additive
character splits without introducing inverses into the residue-symbol factors.
The construction also covers the ideal 1 and its one-element quotient. -/
def weightedCRT (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b) :
    (O ⧸ a) × (O ⧸ b) ≃ O ⧸ (a * b) :=
  (Equiv.prodCongr (generator_unit c ha hb hab).unit.mulLeft
    (generator_unit c hb ha hab.symm).unit.mulLeft).trans
    (Ideal.quotientMulEquivQuotientProd a b (ideals_coprime hab)).toEquiv.symm

theorem weightedCRT_repr (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (x : O ⧸ a) (y : O ⧸ b) :
    weightedCRT c ha hb hab (x, y) =
      Ideal.Quotient.mk (a * b)
        (primaryGenerator b * residueLift a x + primaryGenerator a * residueLift b y) := by
  have hza := generator_quotient_zero c ha
  have hzb := generator_quotient_zero c hb
  apply (Ideal.quotientMulEquivQuotientProd a b (ideals_coprime hab)).injective
  change (Ideal.quotientMulEquivQuotientProd a b (ideals_coprime hab))
    ((Ideal.quotientMulEquivQuotientProd a b (ideals_coprime hab)).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  apply Prod.ext
  · simp [Equiv.prodCongr, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk, map_add, map_mul, lift_spec, hza,
      IsUnit.unit_spec]
  · simp [Equiv.prodCongr, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk, map_add, map_mul, lift_spec, hzb,
      IsUnit.unit_spec]

private theorem embedding_add (a b : O) :
    embedding (a + b) = embedding a + embedding b := by
  simpa only [SquarefreeReflection.RayValuePrerequisites.embeddingHom_apply] using
    map_add SquarefreeReflection.RayValuePrerequisites.embeddingHom a b

theorem additive_add (z w : ℂ) :
    additiveCharacter (z + w) = additiveCharacter z * additiveCharacter w := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_im]
  push_cast
  ring

def phase (n : Ideal O) (a : O) : ℂ :=
  additiveCharacter (embedding a / embedding (primaryGenerator n))

theorem generator_ne_zero (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : primaryGenerator n ≠ 0 := by
  intro hz
  apply hn.1
  rw [← (SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c hn).1,
    hz]
  simp [principal]

theorem phase_congr (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) {a b : O}
    (hab : Ideal.Quotient.mk n a = Ideal.Quotient.mk n b) : phase n a = phase n b := by
  have hmem := (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab
  rw [← (SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c hn).1]
    at hmem
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
  have ha : a = b + primaryGenerator n * t := by
    linear_combination ht
  have he := ArithmeticProof.embedding_ne_zero (generator_ne_zero c hn)
  calc
    phase n a = additiveCharacter
        (embedding b / embedding (primaryGenerator n) + embedding t) := by
      unfold phase
      rw [ha, embedding_add, ArithmeticProof.embedding_mul]
      congr 1
      field_simp [he]
      <;> ring
    _ = phase n b := by simp only [phase, additive_add, additiveCharacter_embedding, mul_one]

theorem phase_weighted (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (x y : O) :
    phase (a * b) (primaryGenerator b * x + primaryGenerator a * y) =
      phase a x * phase b y := by
  have hea := ArithmeticProof.embedding_ne_zero (generator_ne_zero c ha)
  have heb := ArithmeticProof.embedding_ne_zero (generator_ne_zero c hb)
  unfold phase
  rw [primaryGenerator_mul c ha hb, embedding_add,
    ArithmeticProof.embedding_mul, ArithmeticProof.embedding_mul, ArithmeticProof.embedding_mul]
  have hdiv : (embedding (primaryGenerator b) * embedding x +
      embedding (primaryGenerator a) * embedding y) /
        (embedding (primaryGenerator a) * embedding (primaryGenerator b)) =
      embedding x / embedding (primaryGenerator a) +
        embedding y / embedding (primaryGenerator b) := by
    field_simp [hea, heb]
    <;> ring
  rw [hdiv, additive_add]

def term (j : ℕ) (n : Ideal O) (x : O ⧸ n) : ℂ :=
  sexticSymbol n (residueLift n x) ^ j * phase n (residueLift n x)

theorem term_weighted (j : ℕ) (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (x : O ⧸ a) (y : O ⧸ b) :
    term j (a * b) (weightedCRT c ha hb hab (x, y)) =
      term j a x * term j b y * sexticSymbol a (primaryGenerator b) ^ j *
        sexticSymbol b (primaryGenerator a) ^ j := by
  let t := primaryGenerator b * residueLift a x + primaryGenerator a * residueLift b y
  have ht : Ideal.Quotient.mk (a * b)
      (residueLift (a * b) (weightedCRT c ha hb hab (x, y))) =
      Ideal.Quotient.mk (a * b) t := by
    simpa only [lift_spec] using weightedCRT_repr c ha hb hab x y
  have hza := generator_quotient_zero c ha
  have hzb := generator_quotient_zero c hb
  have hta : Ideal.Quotient.mk a t =
      Ideal.Quotient.mk a (primaryGenerator b * residueLift a x) := by
    simp [t, map_add, map_mul, hza]
  have htb : Ideal.Quotient.mk b t =
      Ideal.Quotient.mk b (primaryGenerator a * residueLift b y) := by
    simp [t, map_add, map_mul, hzb]
  unfold term
  rw [symbol_congr ht, phase_congr c (outside_mul c ha hb) ht,
    symbol_mul_denominator ha.1 hb.1, symbol_congr hta, symbol_congr htb,
    SquarefreeReflection.sexticSymbol_mul_numerator c ha,
    SquarefreeReflection.sexticSymbol_mul_numerator c hb]
  change (_ * _) ^ j *
    phase (a * b) (primaryGenerator b * residueLift a x +
      primaryGenerator a * residueLift b y) = _
  rw [phase_weighted c ha hb]
  simp only [mul_pow]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem gauss_eq_sum (j : ℕ) (n : Ideal O) (hn : n ≠ ⊥) [Fintype (O ⧸ n)] :
    gauss (j : ℤ) n = (Real.sqrt (normIdeal n) : ℂ)⁻¹ * ∑ x : O ⧸ n, term j n x := by
  simp only [gauss, dif_pos hn, term, phase, zpow_natCast]
  congr 1 <;> exact Finset.sum_congr (by ext x; simp) (fun x _ => rfl)

theorem norm_mul (a b : Ideal O) : normIdeal (a * b) = normIdeal a * normIdeal b := by
  simp only [normIdeal, map_mul, Nat.cast_mul]

theorem sqrt_norm_mul (a b : Ideal O) :
    (Real.sqrt (normIdeal (a * b)) : ℂ) =
      (Real.sqrt (normIdeal a) : ℂ) * (Real.sqrt (normIdeal b) : ℂ) := by
  have hn : 0 ≤ normIdeal a := by unfold normIdeal; positivity
  rw [norm_mul, Real.sqrt_mul hn]
  exact Complex.ofReal_mul _ _

/-- The CRT formula for every natural character exponent. -/
theorem gauss_crt (j : ℕ) (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b) :
    gauss (j : ℤ) (a * b) = gauss (j : ℤ) a * gauss (j : ℤ) b *
      sexticSymbol a (primaryGenerator b) ^ j *
      sexticSymbol b (primaryGenerator a) ^ j := by
  letI : Finite (O ⧸ a) := Ring.HasFiniteQuotients.finiteQuotient ha.1
  letI : Fintype (O ⧸ a) := Fintype.ofFinite _
  letI : Finite (O ⧸ b) := Ring.HasFiniteQuotients.finiteQuotient hb.1
  letI : Fintype (O ⧸ b) := Fintype.ofFinite _
  have hab0 := (outside_mul c ha hb).1
  letI : Finite (O ⧸ (a * b)) := Ring.HasFiniteQuotients.finiteQuotient hab0
  letI : Fintype (O ⧸ (a * b)) := Fintype.ofFinite _
  have hsum : (∑ z : O ⧸ (a * b), term j (a * b) z) =
      (∑ x : O ⧸ a, term j a x) * (∑ y : O ⧸ b, term j b y) *
        sexticSymbol a (primaryGenerator b) ^ j *
        sexticSymbol b (primaryGenerator a) ^ j := by
    rw [← (weightedCRT c ha hb hab).sum_comp (term j (a * b))]
    rw [Fintype.sum_prod_type]
    simp_rw [term_weighted j c ha hb hab]
    rw [Fintype.sum_mul_sum]
    simp only [Finset.sum_mul]
  rw [gauss_eq_sum j (a * b) hab0, gauss_eq_sum j a ha.1, gauss_eq_sum j b hb.1,
    hsum, sqrt_norm_mul, mul_inv_rev]
  ring


end QRHShort.ArithmeticProof.MixedGauss.CRT

#print axioms QRHShort.ArithmeticProof.MixedGauss.CRT.gauss_crt

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof.MixedGauss.CRT).isPrefixOf name then
        entries.push (name, info)
      else entries) (#[] : Array (Name × ConstantInfo))
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Mixed Gauss CRT depends on forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Mixed Gauss CRT declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No mixed Gauss CRT declarations audited"
  logInfo m!"MIXED_GAUSS_CRT_AUDIT declarations={checked} forbidden=0"


/-! Close the original mixed evaluation using the general-exponent CRT formula. -/

noncomputable section
open Classical

namespace QRHShort.ArithmeticProof.MixedGauss

theorem oddGaussCRT : OddGaussCRTStatement := by
  intro c a b ha hb hab j _
  simpa only [mul_pow, mul_assoc] using CRT.gauss_crt j c ha.1 hb.1 hab

theorem cubicGaussCRT : CubicGaussCRTStatement := by
  intro c a b ha hb hab
  exact CRT.gauss_crt 2 c ha.1 hb.1 hab

/-- The frozen statement, with no outstanding proposition parameters. -/
theorem mixedGaussEvaluation : MixedGaussEvaluationStatement :=
  mixedGaussEvaluation_of_crt oddGaussCRT cubicGaussCRT

example : MixedGaussEvaluationStatement := mixedGaussEvaluation

end QRHShort.ArithmeticProof.MixedGauss

#print axioms QRHShort.ArithmeticProof.MixedGauss.mixedGaussEvaluation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let names := #[`QRHShort.ArithmeticProof.MixedGauss.oddGaussCRT,
    `QRHShort.ArithmeticProof.MixedGauss.cubicGaussCRT,
    `QRHShort.ArithmeticProof.MixedGauss.mixedGaussEvaluation]
  for name in names do
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "Mixed Gauss completion depends on forbidden axiom {ax} in {name}"
  logInfo m!"MIXED_GAUSS_COMPLETION_AUDIT declarations={names.size} forbidden=0 pending_inputs=0"
