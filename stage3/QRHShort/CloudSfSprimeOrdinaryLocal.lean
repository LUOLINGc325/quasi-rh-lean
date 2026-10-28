import QRHShort.SquarefreeSPrimeReciprocity
import QRHShort.SquarefreeNumeratorProducts
import QRHShort.ArithmeticBasics
import QRHShort.PrimaryGenerator
import OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
import OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization

/-! Direct finite-residue prerequisites for an excluded ordinary prime.
These do not identify the two orders of the sextic residue symbol. -/

noncomputable section
open Classical

namespace QRHShort.CloudBatch.SPrimeOrdinary
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites

/-- An excluded prime is genuinely outside the domain of the supplied
`ArithmeticRelations` reciprocity formula. -/
theorem excluded_prime_not_outside (c : ArithmeticContext) (p : c.S) :
    ¬ Outside c.S p.val := by
  intro hp
  exact hp.2 p.val p.property (dvd_refl p.val)

theorem ordinary_quotient_rootSix (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) :
    IsPrimitiveRoot (Ideal.Quotient.mk p.val rootSix) 6 := by
  have h := mt (sPrime_dvd_six_iff c p).mpr hp
  exact quotient_rootSix_isPrimitiveRoot p.val
    (fun htwo => h (Or.inl htwo)) (fun hthree => h (Or.inr hthree))

theorem ordinary_absNorm_mod_six (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) : p.val.absNorm % 6 = 1 :=
  prime_absNorm_mod_six (c.prime_S p.val p.property)
    (ordinary_quotient_rootSix c p hp)

theorem outside_relPrime_excluded (c : ArithmeticContext) (p : c.S)
    {q : Ideal O} (hq : Outside c.S q) : IsRelPrime p.val q :=
  (c.prime_S p.val p.property).irreducible.isRelPrime_iff_not_dvd.mpr
    (hq.2 p.val p.property)

theorem primaryGenerator_unit_mod_excluded (c : ArithmeticContext) (p : c.S)
    {q : Ideal O} (hq : Outside c.S q) :
    IsUnit (Ideal.Quotient.mk p.val (primaryGenerator q)) := by
  letI : p.val.IsMaximal :=
    (Ideal.isPrime_of_prime (c.prime_S p.val p.property)).isMaximal
      (c.prime_S p.val p.property).ne_zero
  letI : Field (O ⧸ p.val) := Ideal.Quotient.field p.val
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply hq.2 p.val p.property
  rw [← (primaryGenerator_spec_outside c hq).1]
  exact Ideal.dvd_span_singleton.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem prime_symbol_congr (P : Ideal O) {a b : O}
    (hab : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) :
    sexticAtPrime P a = sexticAtPrime P b := by
  simp only [sexticAtPrime, hab]

private theorem lift_spec (P : Ideal O) (x : O ⧸ P) :
    Ideal.Quotient.mk P (residueLift P x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

/-- The opposite-order symbol is an actual character on the quotient by p.
No `Outside c.S p` premise is used. This character has not been asserted to
be trivial on the global units. -/
def ordinaryResidueCharacter (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) : MulChar (O ⧸ p.val) ℂ := by
  let hζ := ordinary_quotient_rootSix c p hp
  let hP := c.prime_S p.val p.property
  letI : p.val.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ p.val) := Ideal.Quotient.field p.val
  refine
    { toFun := fun x => sexticAtPrime p.val (residueLift p.val x)
      map_one' := ?_
      map_mul' := ?_
      map_nonunit' := ?_ }
  · rw [prime_symbol_congr p.val (show Ideal.Quotient.mk p.val
        (residueLift p.val 1) = Ideal.Quotient.mk p.val 1 by
          rw [lift_spec, map_one])]
    have ht : Ideal.Quotient.mk p.val (1 : O) ^ ((p.val.absNorm - 1) / 6) =
        Ideal.Quotient.mk p.val (rootSix ^ (0 : ℕ)) := by simp
    simpa only [pow_zero, embedding_one] using
      sexticAtPrime_eq_of_test hζ (by decide : (0 : ℕ) < 6) ht
  · intro x y
    rw [prime_symbol_congr p.val (show Ideal.Quotient.mk p.val
        (residueLift p.val (x * y)) = Ideal.Quotient.mk p.val
        (residueLift p.val x * residueLift p.val y) by
          rw [map_mul, lift_spec, lift_spec, lift_spec])]
    exact sexticAtPrime_mul hP hζ _ _
  · intro x hx
    have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hx
    apply sexticAtPrime_zero_of_mem hP hζ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [lift_spec, hx0]

@[simp] theorem ordinaryResidueCharacter_mk (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) (a : O) :
    ordinaryResidueCharacter c p hp (Ideal.Quotient.mk p.val a) =
      sexticAtPrime p.val a := by
  apply prime_symbol_congr
  exact lift_spec _ _


/-- The only primary global unit is one. -/
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

def unitReductionThree : Oˣ →* (O ⧸ principal (3 : O))ˣ :=
  Units.map (Ideal.Quotient.mk (principal (3 : O))).toMonoidHom

theorem unitReductionThree_injective : Function.Injective unitReductionThree := by
  apply (injective_iff_map_eq_one unitReductionThree).mpr
  intro u hu
  apply primary_unit_eq_one
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hval := congrArg Units.val hu
  change Ideal.Quotient.mk (principal (3 : O)) (u : O) = 1 at hval
  change Ideal.Quotient.mk (principal (3 : O)) ((u : O) - 1) = 0
  rw [map_sub, map_one, hval, sub_self]

theorem unitReductionThree_surjective : Function.Surjective unitReductionThree := by
  intro x
  let a := residueLift (principal (3 : O)) (x : O ⧸ principal (3 : O))
  let b := residueLift (principal (3 : O)) ((x⁻¹ : (O ⧸ principal (3 : O))ˣ) :
    O ⧸ principal (3 : O))
  have ha : Ideal.Quotient.mk (principal (3 : O)) a = (x : O ⧸ principal (3 : O)) :=
    lift_spec _ _
  have hb : Ideal.Quotient.mk (principal (3 : O)) b =
      ((x⁻¹ : (O ⧸ principal (3 : O))ˣ) : O ⧸ principal (3 : O)) := lift_spec _ _
  have hthree : (3 : O) ∣ a * b - 1 := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (principal (3 : O)) (a * b - 1) = 0
    rw [map_sub, map_mul, map_one, ha, hb, Units.mul_inv, sub_self]
  have hnot : ¬ omega - 1 ∣ a := by
    intro hdiv
    apply omega_sub_one_prime.not_dvd_one
    convert dvd_sub (dvd_mul_of_dvd_left hdiv b)
      (omega_sub_one_dvd_three.trans hthree) using 1 <;> ring
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd a hnot
  have hux : unitReductionThree u * x = 1 := by
    apply Units.ext
    change Ideal.Quotient.mk (principal (3 : O)) (u : O) *
      (x : O ⧸ principal (3 : O)) = 1
    rw [← ha, ← map_mul]
    have h : Ideal.Quotient.mk (principal (3 : O)) ((u : O) * a - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hu
    rw [map_sub, map_one] at h
    exact sub_eq_zero.mp h
  refine ⟨u⁻¹, ?_⟩
  apply mul_left_cancel (a := unitReductionThree u)
  rw [← map_mul, mul_inv_cancel, map_one, hux]

def unitLiftThree : (O ⧸ principal (3 : O))ˣ ≃* Oˣ :=
  (MulEquiv.ofBijective unitReductionThree
    ⟨unitReductionThree_injective, unitReductionThree_surjective⟩).symm

@[simp] theorem unitLiftThree_reduction (u : Oˣ) :
    unitLiftThree (unitReductionThree u) = u :=
  (MulEquiv.ofBijective unitReductionThree
    ⟨unitReductionThree_injective, unitReductionThree_surjective⟩).symm_apply_apply u

/-- Normalize a quotient unit by its unique global unit modulo three. -/
def primaryUnitCorrection (P : Ideal O) : (O ⧸ principal (3 : O) * P)ˣ →* Oˣ :=
  unitLiftThree.toMonoidHom.comp
    (Units.map (Ideal.Quotient.factor (show principal (3 : O) * P ≤ principal (3 : O)
      from Ideal.mul_le_left)).toMonoidHom)

@[simp] theorem primaryUnitCorrection_global (P : Ideal O) (u : Oˣ) :
    primaryUnitCorrection P
      (Units.map (Ideal.Quotient.mk (principal (3 : O) * P)).toMonoidHom u) = u := by
  change unitLiftThree (unitReductionThree u) = u
  exact unitLiftThree_reduction u

theorem primaryUnitCorrection_primary (P : Ideal O) (a : O)
    (ha : IsPrimary a) (hu : IsUnit (Ideal.Quotient.mk (principal (3 : O) * P) a)) :
    primaryUnitCorrection P hu.unit = 1 := by
  have hv : Units.map
      (Ideal.Quotient.factor (show principal (3 : O) * P ≤ principal (3 : O)
        from Ideal.mul_le_left)).toMonoidHom hu.unit = 1 := by
    apply Units.ext
    change Ideal.Quotient.factor _ (hu.unit : O ⧸ principal (3 : O) * P) = 1
    rw [hu.unit_spec, Ideal.Quotient.factor_mk]
    have h : Ideal.Quotient.mk (principal (3 : O)) (a - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [map_sub, map_one] at h
    exact sub_eq_zero.mp h
  change unitLiftThree _ = 1
  rw [hv, map_one]

/-- Unit-normalized extension of an arbitrary finite residue character. -/
def primaryExtensionHom (P : Ideal O) (χ : MulChar (O ⧸ P) ℂ) :
    (O ⧸ principal (3 : O) * P)ˣ →* ℂˣ :=
  χ.toUnitHom.comp
      (Units.map (Ideal.Quotient.factor (show principal (3 : O) * P ≤ P
        from Ideal.mul_le_right)).toMonoidHom) *
    (χ.toUnitHom.comp ((Units.map (Ideal.Quotient.mk P).toMonoidHom).comp
      (primaryUnitCorrection P)))⁻¹

theorem primaryExtensionHom_global (P : Ideal O) (χ : MulChar (O ⧸ P) ℂ) (u : Oˣ) :
    primaryExtensionHom P χ
      (Units.map (Ideal.Quotient.mk (principal (3 : O) * P)).toMonoidHom u) = 1 := by
  simp only [primaryExtensionHom, MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.comp_apply, primaryUnitCorrection_global]
  change χ.toUnitHom (Units.map (Ideal.Quotient.mk P).toMonoidHom u) *
    (χ.toUnitHom (Units.map (Ideal.Quotient.mk P).toMonoidHom u))⁻¹ = 1
  exact mul_inv_cancel _

def primaryHeckeExtension (P : Ideal O) (hP : P ≠ ⊥)
    (χ : MulChar (O ⧸ P) ℂ) : HeckeCharacter where
  modulus := principal (3 : O) * P
  modulus_ne_bot := mul_ne_zero
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (3 : O) ≠ 0)) hP
  residue := MulChar.ofUnitHom (primaryExtensionHom P χ)
  unit_trivial := by
    intro u
    change MulChar.ofUnitHom (primaryExtensionHom P χ)
      ((Units.map (Ideal.Quotient.mk (principal (3 : O) * P)).toMonoidHom u :
        (O ⧸ principal (3 : O) * P)ˣ) : O ⧸ principal (3 : O) * P) = 1
    rw [MulChar.ofUnitHom_coe, primaryExtensionHom_global, Units.val_one]

theorem primaryHeckeExtension_primary (P : Ideal O) (hP : P ≠ ⊥)
    (χ : MulChar (O ⧸ P) ℂ) (a : O) (ha : IsPrimary a)
    (hu : IsUnit (Ideal.Quotient.mk (principal (3 : O) * P) a)) :
    (primaryHeckeExtension P hP χ).onElement a = χ (Ideal.Quotient.mk P a) := by
  change MulChar.ofUnitHom (primaryExtensionHom P χ)
    (Ideal.Quotient.mk (principal (3 : O) * P) a) = χ (Ideal.Quotient.mk P a)
  rw [← hu.unit_spec, MulChar.ofUnitHom_coe]
  simp only [primaryExtensionHom, MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.comp_apply, primaryUnitCorrection_primary P a ha hu,
    map_one, inv_one, mul_one]
  change χ (Ideal.Quotient.factor _ (hu.unit : O ⧸ principal (3 : O) * P)) = _
  rw [hu.unit_spec, Ideal.Quotient.factor_mk]

def ordinaryPrimaryHeckeCharacter (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) : HeckeCharacter :=
  primaryHeckeExtension p.val (c.prime_S p.val p.property).ne_zero
    (ordinaryResidueCharacter c p hp)

theorem ordinaryPrimaryHeckeCharacter_supported (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) :
    ∀ q : Ideal O, Prime q → q ∣ (ordinaryPrimaryHeckeCharacter c p hp).modulus →
      q ∈ c.S := by
  intro q hq hdiv
  change q ∣ principal (3 : O) * p.val at hdiv
  rcases hq.dvd_mul.mp hdiv with h | h
  · exact c.above_three q hq h
  · have he : q = p.val := associated_iff_eq.mp
      (hq.associated_of_dvd (c.prime_S p.val p.property) h)
    simpa only [he] using p.property

/-- This is an actual globally unit-trivial Hecke character, with the opposite
order of the symbol. The reciprocity identification is still separate. -/
theorem ordinaryPrimaryHeckeCharacter_rayValue (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) {q : Ideal O} (hq : Outside c.S q) :
    rayValue (ordinaryPrimaryHeckeCharacter c p hp) q =
      sexticAtPrime p.val (primaryGenerator q) := by
  have hu := primaryGenerator_unit_mod_supported c
    (ordinaryPrimaryHeckeCharacter c p hp).modulus
    (ordinaryPrimaryHeckeCharacter c p hp).modulus_ne_bot
    (ordinaryPrimaryHeckeCharacter_supported c p hp) hq
  change (primaryHeckeExtension p.val (c.prime_S p.val p.property).ne_zero
    (ordinaryResidueCharacter c p hp)).onElement (primaryGenerator q) = _
  rw [primaryHeckeExtension_primary _ _ _ _ (primaryGenerator_spec_outside c hq).2 hu,
    ordinaryResidueCharacter_mk]


/-- The defining residue test identifies any sixth root, independently of its
chosen exponent among the six roots. -/
theorem sexticAtPrime_eq_of_sixth_root_test {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) {a v : O}
    (hv : v ^ (6 : ℕ) = 1)
    (ht : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) = Ideal.Quotient.mk P v) :
    sexticAtPrime P a = embedding v := by
  have hr : IsPrimitiveRoot rootSix 6 := by
    refine ⟨rootSix_pow_six, ?_⟩
    intro k hk
    apply hζ.dvd_of_pow_eq_one k
    simpa only [map_pow, map_one] using congrArg (Ideal.Quotient.mk P) hk
  obtain ⟨j, hj, rfl⟩ := hr.eq_pow_of_pow_eq_one hv
  exact sexticAtPrime_eq_of_test hζ hj ht


theorem selected_embedding_omega_im : (embedding omega).im = Real.sqrt 3 / 2 := by
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

theorem embedding_omega_explicit :
    QRHShort.embedding omega = ((-1 : ℂ) + (Real.sqrt 3 : ℂ) * Complex.I) / 2 := by
  have hp : QRHShort.embedding omega ^ 2 + QRHShort.embedding omega + 1 = 0 := by
    simpa only [QRHShort.embedding_add, QRHShort.embedding_pow,
      QRHShort.embedding_one, QRHShort.embedding_zero] using
      congrArg QRHShort.embedding QRHShort.omega_sq_add_omega_add_one
  have hi : (2 * (QRHShort.embedding omega).re + 1) *
      (QRHShort.embedding omega).im = 0 := by
    have h := congrArg Complex.im hp
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im,
      Complex.zero_im] at h
    nlinarith
  have him : (QRHShort.embedding omega).im ≠ 0 := by
    rw [selected_embedding_omega_im]
    exact div_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (by norm_num)
  have hre : (QRHShort.embedding omega).re = -(1 : ℝ) / 2 := by
    have h := (mul_eq_zero.mp hi).resolve_right him
    linarith
  apply Complex.ext
  · simp [hre, Complex.div_re]
  · simp [selected_embedding_omega_im, Complex.div_im]

/-- The upstream concrete positive embedding agrees with the frozen selected
embedding, rather than merely being an unspecified conjugate embedding. -/
theorem oai_embedding_eq (a : O) :
    OAI.ConcreteTraceCRT.eisEmbedding a = QRHShort.embedding a := by
  have hg : OAI.EisensteinEmbedding.pb.gen = omega := by
    simp [OAI.EisensteinEmbedding.pb, QRHShort.omega]
  have hi (z : ℤ) : QRHShort.embedding (z : O) = (z : ℂ) := by
    simpa only [QRHShort.embeddingHom_apply] using map_intCast QRHShort.embeddingHom z
  obtain ⟨x, y, rfl⟩ := OAI.EisensteinEmbedding.exists_ab a
  change OAI.EisensteinEmbedding.embedding _ _ _ = _
  rw [OAI.EisensteinEmbedding.embedding_apply_ab, hg, QRHShort.embedding_add,
    QRHShort.embedding_mul, hi, hi, embedding_omega_explicit]
  rfl

/-- Exact identification of the actual upstream sextic character with the
frozen finite six-term residue-symbol definition. -/
theorem canonicalSextic_eq_literal (P : Ideal O) [P.IsMaximal] (hP : Prime P)
    (hg : OAI.ActualEisensteinCubic.lambda ∉ P)
    (hc : ringChar (O ⧸ P) ≠ 2)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6) (a : O) :
    OAI.ActualEisensteinCubic.canonicalSextic P hg (Ideal.Quotient.mk P a) =
      sexticAtPrime P a := by
  by_cases ha : Ideal.Quotient.mk P a = 0
  · rw [ha, MulChar.map_zero]
    exact (sexticAtPrime_zero_of_mem hP hζ
      (Ideal.Quotient.eq_zero_iff_mem.mp ha)).symm
  · have hu : IsUnit (Ideal.Quotient.mk P a) := isUnit_iff_ne_zero.mpr ha
    have hv : OAI.ActualEisensteinCubic.sexticChar P hg
        (Ideal.Quotient.mk P a) ^ (6 : ℕ) = 1 := by
      rw [← MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0),
        (OAI.ActualEisensteinCubic.sexticChar_powers P hg).2.2,
        MulChar.one_apply hu]
    have ht := OAI.ActualEisensteinCubic.sexticChar_reduce_unit P hg hc hu.unit
    rw [hu.unit_spec] at ht
    have ht' : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) =
        Ideal.Quotient.mk P (OAI.ActualEisensteinCubic.sexticChar P hg
          (Ideal.Quotient.mk P a)) := ht.symm
    rw [sexticAtPrime_eq_of_sixth_root_test hζ hv ht']
    exact oai_embedding_eq _


theorem prime_good_data {P : Ideal O} (hP : Prime P)
    (h2 : ¬ P ∣ principal (2 : O)) (h3 : ¬ P ∣ principal (3 : O)) :
    OAI.ActualEisensteinCubic.lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  constructor
  · intro h
    exact h3 (Ideal.dvd_span_singleton.mpr
      (P.mem_of_dvd omega_sub_one_dvd_three h))
  · apply OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P
    intro h
    exact h2 (Ideal.dvd_span_singleton.mpr h)

theorem primary_compat {a : O} (ha : IsPrimary a) :
    OAI.ActualEisensteinCubic.lambda ^ (2 : ℕ) ∣ a - 1 :=
  OAI.ActualEisensteinCubic.lambda_sq_dvd_three.trans
    ((isPrimary_iff_three_dvd a).mp ha)

/-- Genuine ordinary reciprocity for the cubic part of the literal sextic
symbol, including an excluded ordinary prime on either side. -/
theorem literal_square_reciprocity {P Q : Ideal O} (hP : Prime P) (hQ : Prime Q)
    (hP2 : ¬ P ∣ principal (2 : O)) (hP3 : ¬ P ∣ principal (3 : O))
    (hQ2 : ¬ Q ∣ principal (2 : O)) (hQ3 : ¬ Q ∣ principal (3 : O))
    (a b : O) (ha : principal a = P) (hb : principal b = Q)
    (hpa : IsPrimary a) (hpb : IsPrimary b) :
    sexticAtPrime P b ^ (2 : ℕ) = sexticAtPrime Q a ^ (2 : ℕ) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Q.IsMaximal := (Ideal.isPrime_of_prime hQ).isMaximal hQ.ne_zero
  obtain ⟨hPg, hPc⟩ := prime_good_data hP hP2 hP3
  obtain ⟨hQg, hQc⟩ := prime_good_data hQ hQ2 hQ3
  rw [← canonicalSextic_eq_literal P hP hPg hPc
      (quotient_rootSix_isPrimitiveRoot P hP2 hP3) b,
    ← canonicalSextic_eq_literal Q hQ hQg hQc
      (quotient_rootSix_isPrimitiveRoot Q hQ2 hQ3) a]
  exact OAI.ActualEisensteinCubic.canonicalSextic_sq_reciprocity_primary
    P Q hPg hQg a b ha.symm hb.symm (primary_compat hpa) (primary_compat hpb)

theorem prime_primary_spec {P : Ideal O} (hP : Prime P)
    (h3 : ¬ P ∣ principal (3 : O)) :
    principal (primaryGenerator P) = P ∧ IsPrimary (primaryGenerator P) := by
  have h := QRHShort.exists_primary_generator_of_prime hP h3
  simpa only [primaryGenerator, dif_pos h] using Classical.choose_spec h

def ordinaryCubicHeckeCharacter (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) : HeckeCharacter :=
  primaryHeckeExtension p.val (c.prime_S p.val p.property).ne_zero
    (ordinaryResidueCharacter c p hp ^ (2 : ℕ))

theorem ordinaryCubicHeckeCharacter_supported (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) :
    ∀ q : Ideal O, Prime q → q ∣ (ordinaryCubicHeckeCharacter c p hp).modulus →
      q ∈ c.S := ordinaryPrimaryHeckeCharacter_supported c p hp

/-- The cubic part now has the required fixed-numerator/varying-denominator
orientation, with a genuinely unit-trivial Hecke character. -/
theorem ordinaryCubicHeckeCharacter_rayValue (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) {q : Ideal O} (hq : Prime q)
    (hout : Outside c.S q) :
    rayValue (ordinaryCubicHeckeCharacter c p hp) q =
      sexticAtPrime q (primaryGenerator p.val) ^ (2 : ℕ) := by
  have hp23 := mt (sPrime_dvd_six_iff c p).mpr hp
  have hp2 : ¬ p.val ∣ principal (2 : O) := fun h => hp23 (Or.inl h)
  have hp3 : ¬ p.val ∣ principal (3 : O) := fun h => hp23 (Or.inr h)
  have hq2 : ¬ q ∣ principal (2 : O) :=
    fun h => hout.2 q (c.above_two q hq h) (dvd_refl q)
  have hq3 : ¬ q ∣ principal (3 : O) :=
    fun h => hout.2 q (c.above_three q hq h) (dvd_refl q)
  have hu := primaryGenerator_unit_mod_supported c
    (ordinaryCubicHeckeCharacter c p hp).modulus
    (ordinaryCubicHeckeCharacter c p hp).modulus_ne_bot
    (ordinaryCubicHeckeCharacter_supported c p hp) hout
  change (primaryHeckeExtension p.val (c.prime_S p.val p.property).ne_zero
    (ordinaryResidueCharacter c p hp ^ (2 : ℕ))).onElement (primaryGenerator q) = _
  rw [primaryHeckeExtension_primary _ _ _ _ (primaryGenerator_spec_outside c hout).2 hu,
    MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), ordinaryResidueCharacter_mk]
  exact literal_square_reciprocity (c.prime_S p.val p.property) hq hp2 hp3 hq2 hq3
    (primaryGenerator p.val) (primaryGenerator q)
    (prime_primary_spec (c.prime_S p.val p.property) hp3).1
    (primaryGenerator_spec_outside c hout).1
    (prime_primary_spec (c.prime_S p.val p.property) hp3).2
    (primaryGenerator_spec_outside c hout).2


/-- Descent of a genuinely periodic multiplicative function to the ideal
quotient; no unit-triviality premise is needed at this stage. -/
def periodicQuotientMonoid (M : Ideal O) (G : O →* ℂ)
    (hG : ∀ x y : O, x - y ∈ M → G x = G y) : (O ⧸ M) →* ℂ where
  toFun x := Quotient.liftOn' x G (fun a b hab => hG a b (M.quotientRel_def.mp hab))
  map_one' := G.map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    exact G.map_mul

/-- Primary normalization supplies global-unit triviality automatically. -/
def primaryPeriodicHeckeCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : ∀ x y : O, x - y ∈ M → G x = G y) : HeckeCharacter :=
  primaryHeckeExtension M hM
    (MulChar.ofUnitHom (Units.map (periodicQuotientMonoid M G hG)))

theorem primaryPeriodicHeckeCharacter_primary (M : Ideal O) (hM : M ≠ ⊥)
    (G : O →* ℂ) (hG : ∀ x y : O, x - y ∈ M → G x = G y)
    (a : O) (ha : IsPrimary a)
    (hu : IsUnit (Ideal.Quotient.mk (principal (3 : O) * M) a)) :
    (primaryPeriodicHeckeCharacter M hM G hG).onElement a = G a := by
  have huM : IsUnit (Ideal.Quotient.mk M a) := by
    simpa only [Ideal.Quotient.factor_mk] using
      hu.map (Ideal.Quotient.factor (show principal (3 : O) * M ≤ M
        from Ideal.mul_le_right))
  change (primaryHeckeExtension M hM
    (MulChar.ofUnitHom (Units.map (periodicQuotientMonoid M G hG)))).onElement a = _
  rw [primaryHeckeExtension_primary M hM _ a ha hu,
    ← huM.unit_spec, MulChar.ofUnitHom_coe]
  change periodicQuotientMonoid M G hG (huM.unit : O ⧸ M) = G a
  rw [huM.unit_spec]
  rfl


/-! The finite quadratic CRT proof is self-contained here. Its inputs are
already compiled finite Gauss/trace theorems; no later analytic row-completion
module or reciprocity premise is imported. -/
namespace QuadraticBridge
open OAI OAI.ActualEisensteinCubic OAI.QuadraticGaussRay
open OAI.ActualEisensteinCoordinates OAI.FiniteGaussPhase
open OAI.ConcreteTraceCRT
open OAI.EisensteinEPrimaryPhase (Coord odd)
open scoped BigOperators

def character (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : MulChar (ActualEisensteinCubic.O⧸P) ℂ := by
  letI : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  letI : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  exact (quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ℂ)

theorem normalized_prime_eq_square_sum (p : ActualEisensteinCubic.O) (hp : p≠0)
    [(Ideal.span {p}).IsMaximal] (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2) :
    ConcreteBreveE.normalizedTraceGauss p hp (character (Ideal.span {p}))=
      quadraticGammaO p hp := by
  let : Field (ActualEisensteinCubic.O⧸Ideal.span {p}):=Ideal.Quotient.field _
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p}):=Fintype.ofFinite _
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates p hp
  have hψ:ψ≠1:=by
    have hprim:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
    simpa only [AddChar.mulShift_one] using hprim (a:=1) one_ne_zero
  change gaussSum (character (Ideal.span {p})) ψ/(‖eisEmbedding p‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {p},ψ (x^2))/(‖eisEmbedding p‖:ℂ)
  congr 1
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase ψ hc hψ

theorem normalized_product_eq_square_sum {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    normalizedProductTraceGauss p hp hcop (fun i=>character (Ideal.span {p i}))=
      quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) := by
  let c:=∏i,p i
  have hc0:c≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {c}):=finite_quotient_span hc0
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {c}):=Fintype.ofFinite _
  let (i:ι) : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Fintype.ofFinite _
  let (i:ι) : Field (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Ideal.Quotient.field _
  let e:=productElementCRT p hcop
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},(∏i,character (Ideal.span {p i}) (e x i))*ψ x)/(‖eisEmbedding c‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},ψ (x^2))/(‖eisEmbedding c‖:ℂ)
  congr 1
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i=>ActualEisensteinCubic.O⧸Ideal.span {p i}) e ψ (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hc

theorem quadraticGamma_product {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))=
      ∏i,character (Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i))*
        quadraticGammaO (p i) (hp i) := by
  rw [←normalized_product_eq_square_sum p hp hcop hc,normalizedProductTraceGauss_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalized_prime_eq_square_sum _ _ (hc i)]


theorem quadratic_ray_cross (a b : ActualEisensteinCubic.O) (ha : a≠0) (hb : b≠0)
    [(Ideal.span {a}).IsMaximal] [(Ideal.span {b}).IsMaximal]
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (hca : ringChar (ActualEisensteinCubic.O⧸Ideal.span {a})≠2)
    (hcb : ringChar (ActualEisensteinCubic.O⧸Ideal.span {b})≠2) :
    quadraticRayValue (residue (a*b))=
      character (Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)*
      character (Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) a)*
      quadraticRayValue (residue a)*quadraticRayValue (residue b) := by
  let p : Bool→ActualEisensteinCubic.O:=fun i=>if i then a else b
  have hp : ∀i,p i≠0:=by
    intro i
    cases i
    · exact hb
    · exact ha
  let (i : Bool) : (Ideal.span {p i}).IsMaximal := by
    cases i <;> dsimp [p] <;> infer_instance
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [p,Function.onFun,isCoprime_comm]
  have hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2 := by
    intro i
    cases i
    · exact hcb
    · exact hca
  have h:=quadraticGamma_product p hp hcop hc
  simp only [quadraticGammaO_eq_rayValue] at h
  have ht : cofactor p true=b:=by
    apply mul_left_cancel₀ ha
    simpa [p] using prime_mul_cofactor p true
  have hf : cofactor p false=a:=by
    apply mul_left_cancel₀ hb
    simpa [p,mul_comm] using prime_mul_cofactor p false
  simp only [Fintype.prod_bool,ht,hf] at h
  simpa [p,mul_comm,mul_left_comm,mul_assoc] using h

theorem quadraticRayValue_ne_zero_of_odd (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : quadraticRayValue r≠0 := by
  rcases r with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      zpow_neg,Complex.I_sq,Complex.I_pow_three,Complex.inv_I,ZMod.val] at * <;>
      intro h <;> solve | (have hh:=congrArg Complex.re h; norm_num at hh) | (have hh:=congrArg Complex.im h; norm_num at hh)


def quadraticRayExponent (r : Coord) : ZMod 4 :=
  if r∈({(0,1),(0,3),(1,0),(1,1),(3,0),(3,3)} : Finset Coord) then 0
  else if r∈({(1,2),(1,3),(2,3)} : Finset Coord) then 1 else 3

def fourthRoot (a : ZMod 4) : ℂ := Complex.I^(a.val:ℤ)

lemma fourthRoot_add (a b : ZMod 4) : fourthRoot (a+b)=fourthRoot a*fourthRoot b := by
  unfold fourthRoot
  rw [←zpow_add₀ Complex.I_ne_zero]
  apply I_zpow_eq_of_mod_four
  push_cast
  simp

lemma quadraticRayValue_eq_fourthRoot (r : Coord) (hr : odd r) :
    quadraticRayValue r=fourthRoot (quadraticRayExponent r) := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases r with ⟨a,b⟩
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [quadraticRayExponent,fourthRoot,EisensteinEPrimaryPhase.odd,
      quadraticRayValue,breveGaussianFourTerms_formula,Prod.mk.injEq,hcmp,
      ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf

def quadraticRaySign (r s : Coord) : ℤ :=
  if odd r ∧ odd s then
    if quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s then 1 else -1
  else 0

lemma quadraticRaySign_mul_left (r s t : Coord) :
    quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
      quadraticRaySign r t*quadraticRaySign s t := by
  have h : ∀r s t : Coord,
      quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
        quadraticRaySign r t*quadraticRaySign s t := by decide
  exact h r s t

lemma quadraticRaySign_mul_right (r s t : Coord) :
    quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
      quadraticRaySign r s*quadraticRaySign r t := by
  have h : ∀r s t : Coord,
      quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
        quadraticRaySign r s*quadraticRaySign r t := by decide
  exact h r s t

lemma quadraticRaySign_symm (r s : Coord) : quadraticRaySign r s=quadraticRaySign s r := by
  have h : ∀r s : Coord,quadraticRaySign r s=quadraticRaySign s r := by decide
  exact h r s

lemma quadraticRaySign_sq (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRaySign r s^2=1 := by
  unfold quadraticRaySign
  rw [ite_eq_left ⟨hr,hs⟩]
  split_ifs <;> norm_num

lemma quadraticRaySign_exponent (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by
  have h : ∀r s : Coord,odd r → odd s →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
        (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by decide
  exact h r s hr hs

lemma quadraticRaySign_root (r s : Coord) (hr : odd r) (hs : odd s) :
    fourthRoot (if quadraticRaySign r s=1 then 0 else 2)=(quadraticRaySign r s:ℂ) := by
  by_cases he : quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]

lemma odd_mul (r s : Coord) (hr : odd r) (hs : odd s) : odd (EisensteinEPrimaryPhase.mul r s) := by
  have h : ∀r s : Coord,odd r → odd s → odd (EisensteinEPrimaryPhase.mul r s) := by decide
  exact h r s hr hs

theorem quadraticRayValue_mul (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul r s)=
      (quadraticRaySign r s:ℂ)*quadraticRayValue r*quadraticRayValue s := by
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul r s hr hs),quadraticRaySign_exponent r s hr hs,
    fourthRoot_add,fourthRoot_add,quadraticRaySign_root r s hr hs,
    quadraticRayValue_eq_fourthRoot r hr,quadraticRayValue_eq_fourthRoot s hs]



theorem prime_residue_odd (a : QRHShort.O) (ha : Prime a)
    (h2 : ¬ QRHShort.principal a ∣ QRHShort.principal (2 : QRHShort.O)) :
    odd (residue a) := by
  apply (odd_residue_iff_not_two_dvd a).mpr
  intro hdiv
  have ht : Prime (2 : QRHShort.O) := by
    apply (Ideal.span_singleton_prime (by norm_num : (2 : QRHShort.O) ≠ 0)).mp
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using
      cubicTwoIdeal_isMaximal.isPrime
  have ha2 : a ∣ (2 : QRHShort.O) := (ht.associated_of_dvd ha hdiv).symm.dvd
  exact h2 (Ideal.dvd_span_singleton.mpr (Ideal.mem_span_singleton.mpr ha2))

theorem literal_cube_character (P : Ideal QRHShort.O) [P.IsMaximal] (hP : Prime P)
    (hg : OAI.ActualEisensteinCubic.lambda ∉ P)
    (hc : ringChar (QRHShort.O ⧸ P) ≠ 2)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P QRHShort.rootSix) 6) (a : QRHShort.O) :
    QRHShort.sexticAtPrime P a ^ (3 : ℕ) = character P (Ideal.Quotient.mk P a) := by
  rw [← canonicalSextic_eq_literal P hP hg hc hζ a,
    ← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
    canonicalSextic_pow_three_quadratic]
  rfl

/-- Full reciprocity for the frozen literal sextic symbols at ordinary prime
primary generators. Its finite sign is explicitly multiplicative modulo four. -/
theorem literal_prime_reciprocity (a b : QRHShort.O) (ha : Prime a) (hb : Prime b)
    (hpa : QRHShort.IsPrimary a) (hpb : QRHShort.IsPrimary b)
    (ha2 : ¬ QRHShort.principal a ∣ QRHShort.principal (2 : QRHShort.O))
    (ha3 : ¬ QRHShort.principal a ∣ QRHShort.principal (3 : QRHShort.O))
    (hb2 : ¬ QRHShort.principal b ∣ QRHShort.principal (2 : QRHShort.O))
    (hb3 : ¬ QRHShort.principal b ∣ QRHShort.principal (3 : QRHShort.O)) :
    QRHShort.sexticAtPrime (QRHShort.principal a) b =
      (quadraticRaySign (residue a) (residue b) : ℂ) *
        QRHShort.sexticAtPrime (QRHShort.principal b) a := by
  letI : (Ideal.span {a}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
  letI : (Ideal.span {b}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hb.irreducible
  letI : (QRHShort.principal a).IsMaximal := by
    change (Ideal.span {a}).IsMaximal
    infer_instance
  letI : (QRHShort.principal b).IsMaximal := by
    change (Ideal.span {b}).IsMaximal
    infer_instance
  letI : Field (QRHShort.O ⧸ QRHShort.principal a) := Ideal.Quotient.field _
  letI : Field (QRHShort.O ⧸ QRHShort.principal b) := Ideal.Quotient.field _
  have hA : Prime (QRHShort.principal a) := Ideal.prime_span_singleton_iff.mpr ha
  have hB : Prime (QRHShort.principal b) := Ideal.prime_span_singleton_iff.mpr hb
  obtain ⟨hag, hac⟩ := prime_good_data hA ha2 ha3
  obtain ⟨hbg, hbc⟩ := prime_good_data hB hb2 hb3
  have hζa := QRHShort.quotient_rootSix_isPrimitiveRoot (QRHShort.principal a) ha2 ha3
  have hζb := QRHShort.quotient_rootSix_isPrimitiveRoot (QRHShort.principal b) hb2 hb3
  by_cases he : QRHShort.principal a = QRHShort.principal b
  · have hba : b ∈ QRHShort.principal a := by rw [he]; exact Ideal.subset_span (by simp)
    have hab : a ∈ QRHShort.principal b := by rw [← he]; exact Ideal.subset_span (by simp)
    rw [sexticAtPrime_zero_of_mem hA hζa hba, sexticAtPrime_zero_of_mem hB hζb hab,
      mul_zero]
  · have hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}) :=
      Ideal.isCoprime_of_isMaximal he
    have hba : b ∉ QRHShort.principal a := by
      intro hm
      apply he
      exact ((inferInstance : (Ideal.span {b} : Ideal QRHShort.O).IsMaximal).eq_of_le
        (Ideal.IsMaximal.ne_top inferInstance)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm))).symm
    have hu : IsUnit (Ideal.Quotient.mk (QRHShort.principal a) b) :=
      isUnit_iff_ne_zero.mpr (fun hz => hba (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    have h6 : QRHShort.sexticAtPrime (QRHShort.principal a) b ^ (6 : ℕ) = 1 := by
      rw [← canonicalSextic_eq_literal _ hA hag hac hζa b,
        ← MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), canonicalSextic_pow_six,
        MulChar.one_apply hu]
    have h2 := literal_square_reciprocity hA hB ha2 ha3 hb2 hb3 a b rfl rfl hpa hpb
    have hoA := prime_residue_odd a ha ha2
    have hoB := prime_residue_odd b hb hb2
    have hcross := quadratic_ray_cross a b ha.ne_zero hb.ne_zero hcop hac hbc
    rw [residue_mul, quadraticRayValue_mul _ _ hoA hoB] at hcross
    have h3 : QRHShort.sexticAtPrime (QRHShort.principal a) b ^ (3 : ℕ) *
        QRHShort.sexticAtPrime (QRHShort.principal b) a ^ (3 : ℕ) =
          (quadraticRaySign (residue a) (residue b) : ℂ) := by
      change QRHShort.sexticAtPrime (Ideal.span {a}) b ^ (3 : ℕ) *
        QRHShort.sexticAtPrime (Ideal.span {b}) a ^ (3 : ℕ) = _
      rw [literal_cube_character (Ideal.span {a}) hA hag hac hζa b,
        literal_cube_character (Ideal.span {b}) hB hbg hbc hζb a]
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ hoA)
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ hoB)
      simpa only [QRHShort.principal, mul_assoc, mul_left_comm, mul_comm] using hcross.symm
    calc
      _ = QRHShort.sexticAtPrime (QRHShort.principal a) b *
          QRHShort.sexticAtPrime (QRHShort.principal a) b ^ (6 : ℕ) := by rw [h6, mul_one]
      _ = QRHShort.sexticAtPrime (QRHShort.principal a) b ^ (3 : ℕ) *
          (QRHShort.sexticAtPrime (QRHShort.principal a) b ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = QRHShort.sexticAtPrime (QRHShort.principal a) b ^ (3 : ℕ) *
          (QRHShort.sexticAtPrime (QRHShort.principal b) a ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [h2]
      _ = (QRHShort.sexticAtPrime (QRHShort.principal a) b ^ (3 : ℕ) *
          QRHShort.sexticAtPrime (QRHShort.principal b) a ^ (3 : ℕ)) *
          QRHShort.sexticAtPrime (QRHShort.principal b) a := by ring
      _ = _ := by rw [h3]

end QuadraticBridge


open OAI.ActualEisensteinCoordinates

/-- The fixed ordinary numerator contributes a genuine character modulo four. -/
def ordinaryPhaseHom (a : O) (ha : OAI.EisensteinEPrimaryPhase.odd (residue a)) :
    O →* ℂ where
  toFun n := (QuadraticBridge.quadraticRaySign (residue a) (residue n) : ℂ)
  map_one' := by
    have h1 : residue (1 : O) = ((1 : ZMod 4), 0) := by
      have h : (1 : O) = eval 1 0 := by simp [eval]
      rw [h, residue_eval]
      norm_num
    have ht : ∀ r : OAI.EisensteinEPrimaryPhase.Coord,
        OAI.EisensteinEPrimaryPhase.odd r →
        QuadraticBridge.quadraticRaySign r ((1 : ZMod 4), 0) = 1 := by decide
    rw [h1, ht _ ha, Int.cast_one]
  map_mul' x y := by
    rw [residue_mul, QuadraticBridge.quadraticRaySign_mul_right, Int.cast_mul]

def ordinaryReciprocalHom (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) (a : O)
    (ha : OAI.EisensteinEPrimaryPhase.odd (residue a)) : O →* ℂ :=
  ordinaryPhaseHom a ha *
    ((ordinaryResidueCharacter c p hp).toMonoidHom.comp
      (Ideal.Quotient.mk p.val).toMonoidHom)

theorem ordinaryReciprocalHom_apply (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) (a : O)
    (ha : OAI.EisensteinEPrimaryPhase.odd (residue a)) (n : O) :
    ordinaryReciprocalHom c p hp a ha n =
      (QuadraticBridge.quadraticRaySign (residue a) (residue n) : ℂ) *
        sexticAtPrime p.val n := by
  change _ * ordinaryResidueCharacter c p hp (Ideal.Quotient.mk p.val n) = _
  rw [ordinaryResidueCharacter_mk]
  rfl

theorem ordinaryReciprocalHom_periodic (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) (a : O)
    (ha : OAI.EisensteinEPrimaryPhase.odd (residue a)) (x y : O)
    (hxy : x - y ∈ principal (4 : O) * p.val) :
    ordinaryReciprocalHom c p hp a ha x = ordinaryReciprocalHom c p hp a ha y := by
  rw [ordinaryReciprocalHom_apply, ordinaryReciprocalHom_apply]
  have hr := OAI.QuadraticGaussRay.residue_eq_of_four_dvd_sub x y
    (Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy))
  rw [hr, prime_symbol_congr p.val (Ideal.Quotient.eq.mpr (Ideal.mul_le_right hxy))]

theorem ordinary_modulus_supported (c : ArithmeticContext) (p : c.S) :
    ∀ q : Ideal O, Prime q → q ∣ principal (3 : O) * (principal (4 : O) * p.val) →
      q ∈ c.S := by
  intro q hq hdiv
  rcases hq.dvd_mul.mp hdiv with h | h
  · exact c.above_three q hq h
  · rcases hq.dvd_mul.mp h with h | h
    · have hfour : principal (4 : O) = principal (2 : O) ^ (2 : ℕ) := by
        rw [pow_two]
        simp only [principal, Ideal.span_singleton_mul_span_singleton]
        norm_num
      rw [hfour] at h
      exact c.above_two q hq (hq.dvd_of_dvd_pow h)
    · have he : q = p.val := associated_iff_eq.mp
        (hq.associated_of_dvd (c.prime_S p.val p.property) h)
      simpa only [he] using p.property

/-- The exact prime-value target for a fixed element, before selecting a
principal generator. -/
def NumeratorCharacter (c : ArithmeticContext) (a : O) : Prop :=
  ∃ χ : HeckeCharacter,
    (∀ q : Ideal O, Prime q → q ∣ χ.modulus → q ∈ c.S) ∧
    ∀ q : Ideal O, Prime q → Outside c.S q → rayValue χ q = sexticAtPrime q a

theorem primary_numerator_character (c : ArithmeticContext) (p : c.S)
    (hp : ¬ p.val ∣ principal (6 : O)) (a : O) (ha : principal a = p.val)
    (hpa : IsPrimary a) : NumeratorCharacter c a := by
  have hp23 := mt (sPrime_dvd_six_iff c p).mpr hp
  have hp2 : ¬ p.val ∣ principal (2 : O) := fun h => hp23 (Or.inl h)
  have hp3 : ¬ p.val ∣ principal (3 : O) := fun h => hp23 (Or.inr h)
  have hap : Prime a := Ideal.prime_span_singleton_iff.mp
    (show Prime (principal a) by rw [ha]; exact c.prime_S p.val p.property)
  have ha2 : ¬ principal a ∣ principal (2 : O) := by simpa only [ha] using hp2
  have ha3 : ¬ principal a ∣ principal (3 : O) := by simpa only [ha] using hp3
  have hoa := QuadraticBridge.prime_residue_odd a hap ha2
  let M := principal (4 : O) * p.val
  have hM : M ≠ ⊥ := mul_ne_zero
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (4 : O) ≠ 0))
    (c.prime_S p.val p.property).ne_zero
  let G := ordinaryReciprocalHom c p hp a hoa
  let hG := ordinaryReciprocalHom_periodic c p hp a hoa
  let χ := primaryPeriodicHeckeCharacter M hM G hG
  have hS : ∀ q : Ideal O, Prime q → q ∣ χ.modulus → q ∈ c.S :=
    ordinary_modulus_supported c p
  refine ⟨χ, hS, ?_⟩
  intro q hq hout
  have hqgen := primaryGenerator_spec_outside c hout
  have hqp : Prime (primaryGenerator q) := Ideal.prime_span_singleton_iff.mp
    (show Prime (principal (primaryGenerator q)) by rw [hqgen.1]; exact hq)
  have hq2 : ¬ q ∣ principal (2 : O) :=
    fun h => hout.2 q (c.above_two q hq h) (dvd_refl q)
  have hq3 : ¬ q ∣ principal (3 : O) :=
    fun h => hout.2 q (c.above_three q hq h) (dvd_refl q)
  have hb2 : ¬ principal (primaryGenerator q) ∣ principal (2 : O) := by simpa only [hqgen.1] using hq2
  have hb3 : ¬ principal (primaryGenerator q) ∣ principal (3 : O) := by simpa only [hqgen.1] using hq3
  have hu := primaryGenerator_unit_mod_supported c χ.modulus χ.modulus_ne_bot hS hout
  change χ.onElement (primaryGenerator q) = _
  rw [primaryPeriodicHeckeCharacter_primary M hM G hG _ hqgen.2 hu]
  rw [ordinaryReciprocalHom_apply]
  have hrec := QuadraticBridge.literal_prime_reciprocity (primaryGenerator q) a
    hqp hap hqgen.2 hpa hb2 hb3 ha2 ha3
  simpa only [ha, hqgen.1, QuadraticBridge.quadraticRaySign_symm
    (residue (primaryGenerator q)) (residue a)] using hrec.symm

/-- Unit multiplication of the numerator is already covered by the verified
unit supplementary characters; it introduces no local reciprocity premise. -/
theorem numeratorCharacter_unit_mul (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {a : O} (ha : NumeratorCharacter c a) (u : Oˣ) :
    NumeratorCharacter c ((u : O) * a) := by
  obtain ⟨χ, hχS, hχ⟩ := ha
  obtain ⟨M₀, hM₀, _, hM₀S, hunit⟩ := exists_all_unit_residual_characters c hc
  obtain ⟨η, hηM, hη⟩ := hunit u
  have hηS : ∀ q : Ideal O, Prime q → q ∣ η.modulus → q ∈ c.S := by
    intro q hq hdiv
    exact hM₀S q hq (hηM ▸ hdiv)
  let M : Ideal O := χ.modulus * η.modulus
  have hM : M ≠ ⊥ := mul_ne_zero χ.modulus_ne_bot η.modulus_ne_bot
  have hMS : ∀ q : Ideal O, Prime q → q ∣ M → q ∈ c.S := by
    intro q hq hdiv
    rcases hq.dvd_mul.mp hdiv with h | h
    · exact hχS q hq h
    · exact hηS q hq h
  let χ' := refineHeckeCharacter χ M hM Ideal.mul_le_left
  let η' := refineHeckeCharacter η M hM Ideal.mul_le_right
  let ηR : MulChar (O ⧸ M) ℂ := η'.residue
  let χR : MulChar (O ⧸ M) ℂ := χ'.residue
  let ρ : HeckeCharacter :=
    { modulus := M
      modulus_ne_bot := hM
      residue := ηR * χR
      unit_trivial := by
        intro v
        rw [MulChar.mul_apply]
        change η'.onElement (v : O) * χ'.onElement (v : O) = 1
        rw [show η'.onElement (v : O) = 1 from η'.unit_trivial v,
          show χ'.onElement (v : O) = 1 from χ'.unit_trivial v, mul_one] }
  refine ⟨ρ, hMS, ?_⟩
  intro q hq hout
  have hx := primaryGenerator_unit_mod_supported c M hM hMS hout
  have hηvalue : η.onElement (primaryGenerator q) = sexticAtPrime q (u : O) := by
    have h := hη q hout
    simpa only [SResidual, SRepresentative, SProduct, Fin.val_zero, pow_zero,
      Finset.prod_const_one, mul_one, sexticSymbol_prime hq, rayValue] using h
  change (ηR * χR) (Ideal.Quotient.mk M (primaryGenerator q)) = _
  rw [MulChar.mul_apply]
  change η'.onElement (primaryGenerator q) * χ'.onElement (primaryGenerator q) = _
  rw [refineHeckeCharacter_onElement η M hM Ideal.mul_le_right hx,
    refineHeckeCharacter_onElement χ M hM Ideal.mul_le_left hx,
    hηvalue, show χ.onElement (primaryGenerator q) = sexticAtPrime q a from hχ q hq hout,
    sexticAtPrime_mul hq (outside_quotient_rootSix_isPrimitiveRoot c hq hout)]

/-- This is independent of the arbitrary principal-generator choice. -/
theorem numeratorCharacter_of_associated (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {a b : O} (ha : NumeratorCharacter c a)
    (hab : Associated a b) : NumeratorCharacter c b := by
  obtain ⟨u, rfl⟩ := hab
  simpa only [mul_comm a (u : O)] using numeratorCharacter_unit_mul c hc ha u


end QRHShort.CloudBatch.SPrimeOrdinary


namespace QRHShort.CloudBatch

/-- The original ordinary S-prime local reciprocity obligation, with its
literal generator and every original quantifier unchanged. -/
theorem sf_sprime_ordinary_local_proved :
    SquarefreeReflection.SPrimeOrdinaryLocalReciprocityStatement := by
  intro c hc p hp
  have h3 : ¬ p.val ∣ principal (3 : O) := by
    intro h
    exact hp ((SquarefreeReflection.sPrime_dvd_six_iff c p).mpr (Or.inr h))
  obtain ⟨a, ha, hpa⟩ := exists_primary_generator_of_prime
    (c.prime_S p.val p.property) h3
  change SPrimeOrdinary.NumeratorCharacter c (idealGenerator p.val)
  apply SPrimeOrdinary.numeratorCharacter_of_associated c hc
    (SPrimeOrdinary.primary_numerator_character c p hp a ha hpa)
  apply Ideal.span_singleton_eq_span_singleton.mp
  exact ha.trans (Ideal.span_singleton_generator p.val).symm

end QRHShort.CloudBatch
