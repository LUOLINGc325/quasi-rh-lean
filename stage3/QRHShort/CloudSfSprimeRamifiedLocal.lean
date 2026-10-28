import QRHShort.SquarefreeSPrimeReciprocity
import QRHShort.SquarefreeNumeratorProducts
import QRHShort.PrimaryGenerator
import OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
import OAI.NumberTheory.DirichletL.Fourier.TupleWeights
import OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
import OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization

noncomputable section
open Classical

namespace QRHShort.CloudBatch.RamifiedLocal
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites

/-- The actual prime values required for a fixed numerator. -/
def NumeratorCharacter (c : ArithmeticContext) (a : O) : Prop :=
  ∃ χ : HeckeCharacter,
    (∀ q : Ideal O, Prime q → q ∣ χ.modulus → q ∈ c.S) ∧
    ∀ q : Ideal O, Prime q → Outside c.S q →
      rayValue χ q = sexticAtPrime q a

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

/-- Every prime divisor of three has the same generator up to an actual unit. -/
theorem generator_associated_omega_sub_one {p : Ideal O}
    (hp : Prime p) (hp3 : p ∣ principal (3 : O)) :
    Associated (omega - 1) (idealGenerator p) := by
  have hgen : principal (idealGenerator p) = p := Ideal.span_singleton_generator p
  have ha0 : idealGenerator p ≠ 0 := by
    intro ha
    apply hp.ne_zero
    rw [← hgen, ha]
    simp [principal]
  have ha : Prime (idealGenerator p) := by
    apply (Ideal.span_singleton_prime ha0).mp
    change (principal (idealGenerator p)).IsPrime
    rw [hgen]
    exact Ideal.isPrime_of_prime hp
  have ha3 : idealGenerator p ∣ (3 : O) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hgen] at hp3
    exact Ideal.dvd_span_singleton.mp hp3
  have had : idealGenerator p ∣ (omega - 1) ^ (2 : ℕ) := by
    rw [omega_sub_one_sq]
    exact dvd_mul_of_dvd_left (dvd_neg.mpr ha3) omega
  exact (ha.associated_of_dvd omega_sub_one_prime (ha.dvd_of_dvd_pow had)).symm

/-- The above-three part needs only the fixed nonunit numerator omega-1. -/
theorem localCharacter_of_above_three (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (p : c.S) (hp3 : p.val ∣ principal (3 : O))
    (hlambda : NumeratorCharacter c (omega - 1)) : SPrimeLocalCharacter c p := by
  exact numeratorCharacter_of_associated c hc hlambda
    (generator_associated_omega_sub_one (c.prime_S p.val p.property) hp3)

/-- A periodic multiplicative function descends to the actual ideal quotient. -/
def quotientMonoid (M : Ideal O) (G : O →* ℂ)
    (hG : ∀ x y : O, x - y ∈ M → G x = G y) : (O ⧸ M) →* ℂ where
  toFun x := Quotient.liftOn' x G (fun a b hab => hG a b (M.quotientRel_def.mp hab))
  map_one' := G.map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    exact G.map_mul

/-- Restriction to residue units followed by extension by zero. -/
def periodicHeckeCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : ∀ x y : O, x - y ∈ M → G x = G y)
    (hu : ∀ u : Oˣ, G (u : O) = 1) : HeckeCharacter where
  modulus := M
  modulus_ne_bot := hM
  residue := MulChar.ofUnitHom (Units.map (quotientMonoid M G hG))
  unit_trivial := by
    intro u
    let v : (O ⧸ M)ˣ := Units.map (Ideal.Quotient.mk M).toMonoidHom u
    change MulChar.ofUnitHom (Units.map (quotientMonoid M G hG)) (v : O ⧸ M) = 1
    rw [MulChar.ofUnitHom_coe]
    exact hu u

theorem periodicHeckeCharacter_onElement (M : Ideal O) (hM : M ≠ ⊥)
    (G : O →* ℂ) (hG : ∀ x y : O, x - y ∈ M → G x = G y)
    (hu : ∀ u : Oˣ, G (u : O) = 1) {x : O}
    (hx : IsUnit (Ideal.Quotient.mk M x)) :
    (periodicHeckeCharacter M hM G hG hu).onElement x = G x := by
  change MulChar.ofUnitHom (Units.map (quotientMonoid M G hG))
    (Ideal.Quotient.mk M x) = G x
  rw [← hx.unit_spec, MulChar.ofUnitHom_coe]
  change quotientMonoid M G hG (hx.unit : O ⧸ M) = G x
  rw [hx.unit_spec]
  rfl

/-- To construct the required genuine Hecke character it suffices to prove
periodicity and global-unit invariance of the literal multiplicative row. -/
theorem numeratorCharacter_of_periodic_monoid (c : ArithmeticContext) (a : O)
    (M : Ideal O) (hM : M ≠ ⊥)
    (hMS : ∀ q : Ideal O, Prime q → q ∣ M → q ∈ c.S)
    (G : O →* ℂ) (hG : ∀ x y : O, x - y ∈ M → G x = G y)
    (hu : ∀ u : Oˣ, G (u : O) = 1)
    (hvalue : ∀ q : Ideal O, Prime q → Outside c.S q →
      G (primaryGenerator q) = sexticAtPrime q a) :
    NumeratorCharacter c a := by
  refine ⟨periodicHeckeCharacter M hM G hG hu, hMS, ?_⟩
  intro q hq hout
  change (periodicHeckeCharacter M hM G hG hu).onElement (primaryGenerator q) = _
  rw [periodicHeckeCharacter_onElement M hM G hG hu
    (primaryGenerator_unit_mod_supported c M hM hMS hout)]
  exact hvalue q hq hout

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
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
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

namespace OAIInput

open OAI
open OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.CanonicalQuadraticSieve
open OAI.ConcreteTraceCRT
open scoped BigOperators
open UniqueFactorizationMonoid
local notation "Eis" => OAI.ActualEisensteinCubic.O
local notation "lam" => OAI.ActualEisensteinCubic.lambda

/-- The canonical finite character itself, with no later completion import. -/
abbrev actualSextic := OAI.ActualEisensteinCubic.canonicalSextic

/-! Only finite arithmetic from the frozen upstream sources is reproduced below.
The unavailable later analytic import is not used. -/

def primeValueHom (w : Ideal ActualEisensteinCubic.O → ℂ) : Ideal ActualEisensteinCubic.O →*₀ ℂ where
  toFun I := if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map w).prod
  map_zero' := by simp
  map_one' := by
    rw [ite_eq_right one_ne_zero,UniqueFactorizationMonoid.normalizedFactors_one]
    rfl
  map_mul' I J := by
    by_cases hI : I=0
    · simp [hI]
    by_cases hJ : J=0
    · simp [hJ]
    simp only [ite_eq_right hI,ite_eq_right hJ,ite_eq_right (mul_ne_zero hI hJ),
      UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,Multiset.map_add,Multiset.prod_add]

theorem primeValueHom_prime (w : Ideal ActualEisensteinCubic.O → ℂ) (P : Ideal ActualEisensteinCubic.O) (hP : Prime P) :
    primeValueHom w P = w P := by
  change (if P=0 then 0 else _) = w P
  rw [ite_eq_right hP.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible]
  simp only [normalize_eq,Multiset.map_singleton,Multiset.prod_singleton]

def localRowValue (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) : ℂ :=
  if h : P.IsMaximal ∧ lam∉P then
    letI : P.IsMaximal := h.1
    actualSextic P h.2 (Ideal.Quotient.mk P x)
  else 0

theorem localRowValue_good (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lam∉P) :
    localRowValue x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  simp only [localRowValue,dite_eq_left (show P.IsMaximal ∧ lam∉P from ⟨inferInstance,hg⟩)]

def idealRowHom (x : ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O →*₀ ℂ := primeValueHom (localRowValue x)

theorem idealRowHom_prime (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lam∉P) :
    idealRowHom x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  rw [idealRowHom,primeValueHom_prime _ P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance),localRowValue_good]

open OAI.QuadraticGaussRay OAI.ActualEisensteinCoordinates OAI.FiniteGaussPhase
open OAI.EisensteinEPrimaryPhase (Coord odd)

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


local instance : (Ideal.span {lam} : Ideal ActualEisensteinCubic.O).IsMaximal:=lambdaIdeal_maximal

lemma lambda_odd : ringChar (ActualEisensteinCubic.O⧸Ideal.span {lam})≠2:=
  ActualEisensteinSieve.lambda_residue_odd

lemma lambda_residue : residue lam=((3:ZMod 4),(1:ZMod 4)) := by
  have h : lam=eval (-1) 1 := by
    change (ActualEisensteinCubic.omega-1:ActualEisensteinCubic.O)=((-1:ℤ):ActualEisensteinCubic.O)+((1:ℤ):ActualEisensteinCubic.O)*ActualEisensteinCubic.omega
    push_cast
    ring
  rw [h,residue_eval]
  decide

lemma lambda_quadratic_ray_ne_zero : quadraticRayValue (residue lam)≠0 := by
  apply quadraticRayValue_ne_zero_of_odd
  rw [lambda_residue]
  decide

lemma character_lambda_primary (p : ActualEisensteinCubic.O) (hp : lam^2∣p-1) :
    character (Ideal.span {lam}) (Ideal.Quotient.mk (Ideal.span {lam}) p)=1 := by
  have hm : Ideal.Quotient.mk (Ideal.span {lam}) p=Ideal.Quotient.mk (Ideal.span {lam}) (1:ActualEisensteinCubic.O) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self lam (by decide : (2:ℕ)≠0)).trans hp))
  rw [hm,map_one,map_one]

def lambdaQuadraticRay (r : EisensteinEPrimaryPhase.Coord) : ℂ:=
  quadraticRayValue (EisensteinEPrimaryPhase.mul (residue lam) r)/
    (quadraticRayValue (residue lam)*quadraticRayValue r)

theorem character_lambda_eq_ray (p : ActualEisensteinCubic.O) (hp : p≠0) [(Ideal.span {p}).IsMaximal]
    (hg : lam∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2)
    (hprimary : lam^2∣p-1) (hodd : EisensteinEPrimaryPhase.odd (residue p)) :
    character (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) lam)=
      lambdaQuadraticRay (residue p) := by
  have hcop : IsCoprime (Ideal.span {lam} : Ideal ActualEisensteinCubic.O) (Ideal.span {p}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro he
    apply hg
    rw [←he]
    exact Ideal.subset_span (by simp)
  have h:=quadratic_ray_cross lam p PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero hp hcop lambda_odd hc
  rw [character_lambda_primary p hprimary,one_mul] at h
  unfold lambdaQuadraticRay
  rw [←residue_mul]
  apply (eq_div_iff (mul_ne_zero lambda_quadratic_ray_ne_zero (quadraticRayValue_ne_zero_of_odd _ hodd))).mpr
  simpa only [mul_assoc] using h.symm


open ActualEisensteinCubic
open OAI.QuadraticGaussRay hiding O
open OAI.ActualEisensteinCoordinates hiding O omega

def lambdaQuadraticTable (r : EisensteinEPrimaryPhase.Coord) : ℤ :=
  if ¬EisensteinEPrimaryPhase.odd r then 0
  else if r∈({(0,1),(1,0),(1,2),(1,3),(2,3),(3,3)} : Finset EisensteinEPrimaryPhase.Coord)
    then 1 else -1

lemma lambdaQuadraticTable_mul (r s : EisensteinEPrimaryPhase.Coord) :
    lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
      lambdaQuadraticTable r*lambdaQuadraticTable s := by
  have h : ∀r s : EisensteinEPrimaryPhase.Coord,
      lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
        lambdaQuadraticTable r*lambdaQuadraticTable s := by decide
  exact h r s

lemma lambdaQuadraticTable_eq_ray (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    (lambdaQuadraticTable r:ℂ)=lambdaQuadraticRay r := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hn3 : (-3 : ZMod 4) = 1 := by decide
  rcases r with ⟨a,b⟩
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [lambdaQuadraticTable,lambdaQuadraticRay,lambda_residue,EisensteinEPrimaryPhase.mul,
      EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      Prod.mk.injEq,hcmp,hn3,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      ZMod.val_neg_one,ZMod.val_mul,ZMod.val_add,ZMod.val_sub,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_three]
  all_goals
    field_simp [Complex.I_ne_zero]
    change (-2 : ℂ) = Complex.I * (Complex.I ^ (1 : ℤ) + Complex.I ^ (2 - 1 : ℤ))
    norm_num [Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]

def lambdaQuadraticCharacter : ActualEisensteinCubic.O→*ℂ where
  toFun n:=(lambdaQuadraticTable (residue n):ℂ)
  map_one' := by
    have h : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0):=by
      have h1 : (1:ActualEisensteinCubic.O)=eval 1 0:=by simp [eval]
      rw [h1,residue_eval]
      norm_num
    rw [h]
    exact_mod_cast (show lambdaQuadraticTable ((1:ZMod 4),0)=1 from by decide)
  map_mul' x y := by
    rw [residue_mul,lambdaQuadraticTable_mul]
    push_cast
    rfl

lemma lambdaQuadraticCharacter_periodic (x y : ActualEisensteinCubic.O) (h : (4:ActualEisensteinCubic.O)∣x-y) :
    lambdaQuadraticCharacter x=lambdaQuadraticCharacter y := by
  change (lambdaQuadraticTable (residue x):ℂ)=(lambdaQuadraticTable (residue y):ℂ)
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y h]


open OAI.CubicJacobiGlobal hiding O
lemma localRowValue_square (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue x P^2=eisEmbedding (primeValue P x) := by
  unfold localRowValue primeValue
  split_ifs with h
  · let : P.IsMaximal:=h.1
    change (actualSextic P h.2 (Ideal.Quotient.mk P x))^2=_
    rw [←MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),canonicalSextic_pow_two]
    rfl
  · simp

theorem idealRowHom_square (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom x I^2=eisEmbedding (idealSymbol I x) := by
  have hm (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue x)).prod^2=eisEmbedding ((s.map (fun P=>primeValue P x)).prod) := by
    induction s using Multiset.induction_on with
    | empty=>simp
    | @cons P s ih=>
      simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow,map_mul,localRowValue_square,ih]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,idealSymbol_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · change (if I=0 then 0 else _)^2=eisEmbedding (if I=0 then 0 else _)
    simp only [ite_eq_right hI]
    exact hm _

lemma actualSextic_cube_quadratic (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lam∉P) :
    actualSextic P hg^3=character P := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ,hχ3⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧
      χ^3=(quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ActualEisensteinCubic.O) :=
    ⟨_,rfl,(sexticChar_powers P hg).2.1⟩
  rw [hχ,MulChar.ringHomComp_pow,hχ3]
  ext x
  change eisEmbedding ((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ActualEisensteinCubic.O)=((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ℂ)
  simp

lemma idealRowHom_lambda_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : lam^2∣p-1) (hs : Supported (Ideal.span {p})) :
    idealRowHom lam (Ideal.span {p})^3=lambdaQuadraticCharacter p := by
  let : (Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p}∈normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩
  obtain ⟨hg,hc⟩:=hs.2 _ hmem
  rw [idealRowHom_prime lam _ hg]
  change (actualSextic _ hg (Ideal.Quotient.mk _ lam))^3=_
  rw [←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
  have he:=character_lambda_eq_ray p hp.ne_zero hg hc hprimary
    ((ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p).mpr ((supported_span_iff p).mp hs).2)
  have ho:=ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p
  have hs' := (supported_span_iff p).mp hs
  change character _ (Ideal.Quotient.mk _ lam)=_
  rw [he]
  exact (lambdaQuadraticTable_eq_ray _ (ho.mpr hs'.2)).symm

theorem idealRowHom_lambda_cube (y : ActualEisensteinCubic.O) (hy : lam^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lam (Ideal.span {y})^3=lambdaQuadraticCharacter y := by
  have hy0 : y≠0:=by
    intro he
    apply hs.1
    simp [he]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization y hy0 hy
  rw [←hprod] at hs ⊢
  clear hprod hy hy0 y
  induction s using Multiset.induction_on with
  | empty=>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_pow]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀q∈s,Prime q ∧ lam^2∣q-1:=
      fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,mul_pow,
      idealRowHom_lambda_prime_cube p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

theorem idealRowHom_lambda_formula (y : ActualEisensteinCubic.O) (hy : lam^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lam (Ideal.span {y})=
      eisEmbedding (CubicRamified.linearRay 1 0 y)^2*lambdaQuadraticCharacter y := by
  have htwo:=idealRowHom_square lam (Ideal.span {y})
  change idealRowHom lam (Ideal.span {y})^2=eisEmbedding (symbol lam y) at htwo
  rw [CubicRamified.symbol_lambda_eq_linearRay y hy] at htwo
  have hthree:=idealRowHom_lambda_cube y hy hs
  have hq : lambdaQuadraticCharacter y^2=1 := by
    change (lambdaQuadraticTable (ActualEisensteinCoordinates.residue y):ℂ)^2=1
    have ho := ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd y |>.mpr ((supported_span_iff y).mp hs).2
    unfold lambdaQuadraticTable
    rw [ite_eq_right (not_not.mpr ho)]
    split_ifs <;> norm_num
  have hsix : idealRowHom lam (Ideal.span {y})^6=1 := by
    calc
      _ = (idealRowHom lam (Ideal.span {y})^3)^2:=by ring
      _ = 1:=by rw [hthree,hq]
  calc
    _ = (idealRowHom lam (Ideal.span {y})^2)^2*(idealRowHom lam (Ideal.span {y})^3):=by
      calc
        _ = idealRowHom lam (Ideal.span {y})*idealRowHom lam (Ideal.span {y})^6:=by rw [hsix,mul_one]
        _ = _:=by ring
    _ = _:=by rw [htwo,hthree]

theorem idealRowHom_lambda_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hx : lam^2∣x-1) (hy : lam^2∣y-1)
    (hsx : Supported (Ideal.span {x})) (hsy : Supported (Ideal.span {y}))
    (hxy : (36:ActualEisensteinCubic.O)∣x-y) :
    idealRowHom lam (Ideal.span {x})=idealRowHom lam (Ideal.span {y}) := by
  rw [idealRowHom_lambda_formula x hx hsx,idealRowHom_lambda_formula y hy hsy,
    CubicRamified.linearRay_congr_mod_nine 1 0 x y hx hy ((show (9:ActualEisensteinCubic.O)∣36 from ⟨4,by norm_num⟩).trans hxy),
    lambdaQuadraticCharacter_periodic x y ((show (4:ActualEisensteinCubic.O)∣36 from ⟨9,by norm_num⟩).trans hxy)]


open OAI.ShortDraftLatticeCount (qNat qO_nonneg coords_eval)
lemma norm_eval_mod (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

theorem normCharacter_periodic {m : ℕ} (χ : DirichletCharacter ℂ m) :
    ∀ x y : ActualEisensteinCubic.O, x-y∈Ideal.span {(m : ActualEisensteinCubic.O)} →
      InitialMeanSquare.normCharacter χ x = InitialMeanSquare.normCharacter χ y := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp

lemma supported_span_congruent_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(36:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    Supported (Ideal.span {x})↔Supported (Ideal.span {y}) := by
  have h36:(36:ActualEisensteinCubic.O)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have hlam : lam∣(36:ActualEisensteinCubic.O):=
    ((dvd_pow_self lam (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three).trans ⟨12,by norm_num⟩
  have htwo : (2:ActualEisensteinCubic.O)∣(36:ActualEisensteinCubic.O):=⟨18,by norm_num⟩
  have he (a : ActualEisensteinCubic.O) (ha : a∣x-y) : a∣x↔a∣y := by
    constructor
    · intro hx
      convert dvd_sub hx ha using 1 ; ring
    · intro hy
      convert dvd_add ha hy using 1 ; ring
  rw [supported_span_iff,supported_span_iff,he lam (hlam.trans h36),he 2 (htwo.trans h36)]

lemma supported_prime_data (p : ActualEisensteinCubic.O) (hp : Prime p) (hs : Supported (Ideal.span {p})) :
    lam∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) ∧ ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩)


/-- The two developments use the same integer ring and primary congruence. -/
theorem primary_compat {x : O} (hx : IsPrimary x) : lam ^ 2 ∣ x - 1 :=
  OAI.ActualEisensteinCubic.lambda_sq_dvd_three.trans
    ((isPrimary_iff_three_dvd x).mp hx)

/-- The manuscript exclusions imply the literal support predicate of the
independently defined canonical sextic characters. -/
theorem outside_supported (c : ArithmeticContext) {I : Ideal O}
    (hI : Outside c.S I) : Supported I := by
  refine ⟨hI.1, ?_⟩
  intro P hP
  have hp := prime_of_normalized_factor P hP
  have hout := outside_of_mem_normalizedFactors hI hP
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  constructor
  · intro hlam
    have hthree : P ∣ principal (3 : O) :=
      Ideal.dvd_span_singleton.mpr (P.mem_of_dvd omega_sub_one_dvd_three hlam)
    exact hout.2 P (c.above_three P hp hthree) (dvd_refl P)
  · apply OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P
    intro htwo
    exact hout.2 P (c.above_two P hp (Ideal.dvd_span_singleton.mpr htwo)) (dvd_refl P)

def cubicTwoSupplement : Eis →* ℂ where
  toFun n := (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
    (Ideal.Quotient.mk cubicTwoIdeal n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]

def quadraticTwoSupplement : Eis →* ℂ :=
  InitialMeanSquare.normCharacter (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))

def twoSupplement : Eis →* ℂ := cubicTwoSupplement ^ 2 * quadraticTwoSupplement

theorem cubicTwoSupplement_periodic (x y : Eis)
    (hxy : x - y ∈ Ideal.span {(8 : Eis)}) :
    cubicTwoSupplement x = cubicTwoSupplement y := by
  have h2 : x - y ∈ cubicTwoIdeal := by
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-4 * k, ?_⟩
    change x - y = (-2 : Eis) * (-4 * k)
    rw [hk]
    ring
  change (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
    (Ideal.Quotient.mk cubicTwoIdeal x) =
    (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
      (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

theorem twoSupplement_periodic (x y : Eis)
    (hxy : x - y ∈ Ideal.span {(8 : Eis)}) :
    twoSupplement x = twoSupplement y := by
  change cubicTwoSupplement x ^ 2 * quadraticTwoSupplement x =
    cubicTwoSupplement y ^ 2 * quadraticTwoSupplement y
  rw [cubicTwoSupplement_periodic x y hxy]
  congr 1
  exact normCharacter_periodic _ x y hxy

/-- The two prime factors of a sextic value are computed by actual cubic
reciprocity and the finite-field quadratic supplement at two. -/
theorem idealRowHom_two_prime (p : Eis) (hp : Prime p)
    (hprimary : lam ^ 2 ∣ p - 1) (hs : Supported (Ideal.span {p})) :
    idealRowHom (2 : Eis) (Ideal.span {p}) = twoSupplement p := by
  letI : (Ideal.span {p}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : Field (Eis ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Fintype (Eis ⧸ Ideal.span {p}) := Fintype.ofFinite _
  obtain ⟨hg, hc⟩ := supported_prime_data p hp hs
  have h2 : idealRowHom (2 : Eis) (Ideal.span {p}) ^ 2 = cubicTwoSupplement p := by
    rw [idealRowHom_prime _ _ hg]
    have he := canonicalSextic_four_eq_fixed_two (Ideal.span {p}) hg p rfl hprimary
    have hfour : Ideal.Quotient.mk (Ideal.span {p}) (4 : Eis) =
        (Ideal.Quotient.mk (Ideal.span {p}) (2 : Eis)) ^ 2 := by
      norm_num [map_ofNat]
    rw [hfour, map_pow] at he
    change actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ 2) ^ 2 =
      (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal p)
    rw [canonicalSextic_pow_two]
    exact he
  have h3 : idealRowHom (2 : Eis) (Ideal.span {p}) ^ 3 = quadraticTwoSupplement p := by
    rw [idealRowHom_prime _ _ hg, ← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
      actualSextic_cube_quadratic]
    change ((quadraticChar (Eis ⧸ Ideal.span {p})
      (Ideal.Quotient.mk _ (2 : Eis)) : ℤ) : ℂ) = _
    simp only [map_ofNat]
    rw [quadraticChar_two hc]
    have hn : Ideal.absNorm (Ideal.span {p}) = Fintype.card (Eis ⧸ Ideal.span {p}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    change ((ZMod.χ₈ (Fintype.card (Eis ⧸ Ideal.span {p})) : ℤ) : ℂ) =
      ((ZMod.χ₈ (Ideal.absNorm (Ideal.span {p})) : ℤ) : ℂ)
    rw [hn]
  have hn2 : (2 : Eis) ∉ Ideal.span {p} := by
    intro hz
    have he : (2 : Eis ⧸ Ideal.span {p}) = 0 := by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hz
    exact Ring.two_ne_zero hc he
  have h6 : idealRowHom (2 : Eis) (Ideal.span {p}) ^ 6 = 1 := by
    rw [idealRowHom_prime _ _ hg]
    have he := canonicalSextic_sixth_power_mask (Ideal.span {p}) hg (2 : Eis)
    change actualSextic _ hg (Ideal.Quotient.mk _ ((2 : Eis) ^ 6)) = _ at he
    simpa only [map_pow, ite_eq_right hn2] using he
  calc
    _ = idealRowHom (2 : Eis) (Ideal.span {p}) *
        idealRowHom (2 : Eis) (Ideal.span {p}) ^ 6 := by rw [h6, mul_one]
    _ = idealRowHom (2 : Eis) (Ideal.span {p}) ^ 3 *
        (idealRowHom (2 : Eis) (Ideal.span {p}) ^ 2) ^ 2 := by ring
    _ = twoSupplement p := by
      rw [h2, h3]
      change quadraticTwoSupplement p * cubicTwoSupplement p ^ 2 =
        cubicTwoSupplement p ^ 2 * quadraticTwoSupplement p
      ring

theorem idealRowHom_two_formula (n : Eis) (hn : lam ^ 2 ∣ n - 1)
    (hs : Supported (Ideal.span {n})) :
    idealRowHom (2 : Eis) (Ideal.span {n}) = twoSupplement n := by
  have hn0 : n ≠ 0 := by intro hz; apply hs.1; simp [hz]
  obtain ⟨s, hprod, hfactors⟩ := OAI.ActualEisensteinCubic.exists_primary_prime_factorization n hn0 hn
  rw [← hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty =>
      simp only [Multiset.prod_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one]
  | @cons p s ih =>
      have hp := hfactors p (Multiset.mem_cons_self _ _)
      have htail : ∀ q ∈ s, Prime q ∧ lam ^ 2 ∣ q - 1 :=
        fun q hq => hfactors q (Multiset.mem_cons_of_mem hq)
      have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
        simpa only [Multiset.prod_cons, ← Ideal.span_singleton_mul_span_singleton,
          supported_mul_iff] using hs
      rw [Multiset.prod_cons, ← Ideal.span_singleton_mul_span_singleton, map_mul,
        idealRowHom_two_prime p hp.1 hp.2 hsplit.1, ih hsplit.2 htail, map_mul]

/-- This row is invariant under every global unit because it is evaluated
on the actual principal ideal, before taking residue classes. -/
def supportedRow (a : Eis) : Eis →* ℂ where
  toFun n := if Supported (Ideal.span {n}) then idealRowHom a (Ideal.span {n}) else 0
  map_one' := by
    have hs : Supported (1 : Ideal Eis) := ⟨one_ne_zero, by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1 : Eis)} = (1 : Ideal Eis) by
      simp only [Ideal.span_singleton_one, Ideal.one_eq_top], ite_eq_left hs, map_one]
  map_mul' x y := by
    rw [← Ideal.span_singleton_mul_span_singleton, supported_mul_iff, map_mul]
    by_cases hx : Supported (Ideal.span {x}) <;>
      by_cases hy : Supported (Ideal.span {y}) <;> simp [hx, hy]

theorem supportedRow_unit (a : Eis) (u : Eisˣ) : supportedRow a (u : Eis) = 1 := by
  calc
    supportedRow a (u : Eis) = supportedRow a 1 := by
      change (if Supported (Ideal.span {(u : Eis)}) then _ else 0) =
        (if Supported (Ideal.span {(1 : Eis)}) then _ else 0)
      rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.span_singleton_one]
    _ = 1 := map_one _

theorem supportedRow_apply (a n : Eis) (hs : Supported (Ideal.span {n})) :
    supportedRow a n = idealRowHom a (Ideal.span {n}) := if_pos hs

theorem exists_supported_primary_unit (x : Eis) (hx : Supported (Ideal.span {x})) :
    ∃ u : Eisˣ, lam ^ 2 ∣ (u : Eis) * x - 1 := by
  have hnot := ((supported_span_iff x).mp hx).1
  obtain ⟨u, hu⟩ := QRHShort.exists_primary_unit_of_not_dvd x hnot
  exact ⟨u, primary_compat hu⟩

theorem supportedRow_lambda_periodic (x y : Eis)
    (hxy : x - y ∈ Ideal.span {(36 : Eis)}) :
    supportedRow lam x = supportedRow lam y := by
  have hs := supported_span_congruent_mod_thirty_six x y hxy
  change (if Supported (Ideal.span {x}) then _ else 0) =
    (if Supported (Ideal.span {y}) then _ else 0)
  by_cases hx : Supported (Ideal.span {x})
  · have hy := hs.mp hx
    rw [ite_eq_left hx, ite_eq_left hy]
    obtain ⟨u, hux⟩ := exists_supported_primary_unit x hx
    have h36 : (36 : Eis) ∣ (u : Eis) * x - (u : Eis) * y := by
      convert dvd_mul_of_dvd_right (Ideal.mem_span_singleton.mp hxy) (u : Eis) using 1
      ring
    have hl : lam ^ 2 ∣ (u : Eis) * x - (u : Eis) * y :=
      lambda_sq_dvd_three.trans ((show (3 : Eis) ∣ 36 from ⟨12, by norm_num⟩).trans h36)
    have huy : lam ^ 2 ∣ (u : Eis) * y - 1 := by
      convert dvd_sub hux hl using 1
      ring
    have hsp (z : Eis) : Ideal.span {(u : Eis) * z} = Ideal.span {z} :=
      Ideal.span_singleton_mul_left_unit u.isUnit z
    have he := idealRowHom_lambda_mod_thirty_six ((u : Eis) * x) ((u : Eis) * y)
      hux huy (by rwa [hsp]) (by rwa [hsp]) h36
    simpa only [hsp] using he
  · rw [ite_eq_right hx, ite_eq_right (fun hy => hx (hs.mpr hy))]

theorem supportedRow_two_periodic (x y : Eis)
    (hxy : x - y ∈ principal (72 : O)) :
    supportedRow (2 : Eis) x = supportedRow (2 : Eis) y := by
  have h72 : (72 : Eis) ∣ x - y := Ideal.mem_span_singleton.mp hxy
  have h36 : x - y ∈ Ideal.span {(36 : Eis)} :=
    Ideal.mem_span_singleton.mpr ((show (36 : Eis) ∣ 72 from ⟨2, by norm_num⟩).trans h72)
  have hs := supported_span_congruent_mod_thirty_six x y h36
  change (if Supported (Ideal.span {x}) then _ else 0) =
    (if Supported (Ideal.span {y}) then _ else 0)
  by_cases hx : Supported (Ideal.span {x})
  · have hy := hs.mp hx
    rw [ite_eq_left hx, ite_eq_left hy]
    obtain ⟨u, hux⟩ := exists_supported_primary_unit x hx
    have hu72 : (72 : Eis) ∣ (u : Eis) * x - (u : Eis) * y := by
      convert dvd_mul_of_dvd_right h72 (u : Eis) using 1
      ring
    have hl : lam ^ 2 ∣ (u : Eis) * x - (u : Eis) * y :=
      lambda_sq_dvd_three.trans ((show (3 : Eis) ∣ 72 from ⟨24, by norm_num⟩).trans hu72)
    have huy : lam ^ 2 ∣ (u : Eis) * y - 1 := by
      convert dvd_sub hux hl using 1
      ring
    have hsp (z : Eis) : Ideal.span {(u : Eis) * z} = Ideal.span {z} :=
      Ideal.span_singleton_mul_left_unit u.isUnit z
    calc
      _ = idealRowHom (2 : Eis) (Ideal.span {(u : Eis) * x}) := by rw [hsp]
      _ = twoSupplement ((u : Eis) * x) :=
        idealRowHom_two_formula _ hux (by rwa [hsp])
      _ = twoSupplement ((u : Eis) * y) :=
        twoSupplement_periodic _ _ (Ideal.mem_span_singleton.mpr
          ((show (8 : Eis) ∣ 72 from ⟨9, by norm_num⟩).trans hu72))
      _ = idealRowHom (2 : Eis) (Ideal.span {(u : Eis) * y}) :=
        (idealRowHom_two_formula _ huy (by rwa [hsp])).symm
      _ = _ := by rw [hsp]
  · rw [ite_eq_right hx, ite_eq_right (fun hy => hx (hs.mpr hy))]

theorem modulus72_ne_bot : principal (72 : O) ≠ ⊥ := by
  exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

theorem modulus72_supported (c : ArithmeticContext) :
    ∀ q : Ideal O, Prime q → q ∣ principal (72 : O) → q ∈ c.S := by
  intro q hq hdiv
  have hmem : (2 : O) ^ 3 * (3 : O) ^ 2 ∈ q := by
    convert Ideal.dvd_span_singleton.mp hdiv using 1 <;> norm_num
  have hp := Ideal.isPrime_of_prime hq
  rcases hp.mem_or_mem hmem with htwo | hthree
  · exact c.above_two q hq (Ideal.dvd_span_singleton.mpr (hp.mem_of_pow_mem 3 htwo))
  · exact c.above_three q hq (Ideal.dvd_span_singleton.mpr (hp.mem_of_pow_mem 2 hthree))

theorem supportedRow_lambda_periodic72 (x y : Eis)
    (hxy : x - y ∈ principal (72 : O)) :
    supportedRow lam x = supportedRow lam y :=
  supportedRow_lambda_periodic x y (Ideal.mem_span_singleton.mpr
    ((show (36 : Eis) ∣ 72 from ⟨2, by norm_num⟩).trans (Ideal.mem_span_singleton.mp hxy)))

/-- One fixed modulus, supported only above two and three, works for the
literal canonical row with numerator two. -/
def twoHeckeCharacter : HeckeCharacter :=
  periodicHeckeCharacter (principal (72 : O)) modulus72_ne_bot
    (supportedRow 2) supportedRow_two_periodic (supportedRow_unit 2)

/-- The same modulus also carries the canonical row with numerator omega-1. -/
def lambdaHeckeCharacter : HeckeCharacter :=
  periodicHeckeCharacter (principal (72 : O)) modulus72_ne_bot
    (supportedRow lam) supportedRow_lambda_periodic72 (supportedRow_unit lam)

theorem twoHeckeCharacter_rayValue (c : ArithmeticContext) {I : Ideal O}
    (hI : Outside c.S I) :
    rayValue twoHeckeCharacter I = idealRowHom (2 : Eis) I := by
  have hgen := (SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c hI).1
  have hs : Supported (Ideal.span {QRHShort.primaryGenerator I}) := by
    change Supported (principal (QRHShort.primaryGenerator I))
    rw [hgen]
    exact outside_supported c hI
  change (periodicHeckeCharacter (principal (72 : O)) modulus72_ne_bot
    (supportedRow 2) supportedRow_two_periodic (supportedRow_unit 2)).onElement
      (QRHShort.primaryGenerator I) = _
  rw [periodicHeckeCharacter_onElement _ _ _ _ _
    (primaryGenerator_unit_mod_supported c _ modulus72_ne_bot (modulus72_supported c) hI),
    supportedRow_apply _ _ hs]
  change idealRowHom (2 : Eis) (principal (QRHShort.primaryGenerator I)) = _
  rw [hgen]

theorem lambdaHeckeCharacter_rayValue (c : ArithmeticContext) {I : Ideal O}
    (hI : Outside c.S I) :
    rayValue lambdaHeckeCharacter I = idealRowHom lam I := by
  have hgen := (SquarefreeReflection.RayValuePrerequisites.primaryGenerator_spec_outside c hI).1
  have hs : Supported (Ideal.span {QRHShort.primaryGenerator I}) := by
    change Supported (principal (QRHShort.primaryGenerator I))
    rw [hgen]
    exact outside_supported c hI
  change (periodicHeckeCharacter (principal (72 : O)) modulus72_ne_bot
    (supportedRow lam) supportedRow_lambda_periodic72 (supportedRow_unit lam)).onElement
      (QRHShort.primaryGenerator I) = _
  rw [periodicHeckeCharacter_onElement _ _ _ _ _
    (primaryGenerator_unit_mod_supported c _ modulus72_ne_bot (modulus72_supported c) hI),
    supportedRow_apply _ _ hs]
  change idealRowHom lam (principal (QRHShort.primaryGenerator I)) = _
  rw [hgen]

theorem generator_associated_two {p : Ideal O}
    (hp : Prime p) (hp2 : p ∣ principal (2 : O)) :
    Associated (2 : O) (idealGenerator p) := by
  have hgen : principal (idealGenerator p) = p := Ideal.span_singleton_generator p
  have ha0 : idealGenerator p ≠ 0 := by
    intro ha
    apply hp.ne_zero
    rw [← hgen, ha]
    simp [principal]
  have ha : Prime (idealGenerator p) := by
    apply (Ideal.span_singleton_prime ha0).mp
    change (principal (idealGenerator p)).IsPrime
    rw [hgen]
    exact Ideal.isPrime_of_prime hp
  have ha2 : idealGenerator p ∣ (2 : O) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hgen] at hp2
    exact Ideal.dvd_span_singleton.mp hp2
  have htwo : Prime (2 : O) :=
    (Ideal.span_singleton_prime (by norm_num : (2 : O) ≠ 0)).mp
      OAI.CanonicalQuadraticSieve.twoIdeal_maximal.isPrime
  exact (ha.associated_of_dvd htwo ha2).symm

/-- Both row definitions have the same actual finite-field value, with the
positive complex embeddings explicitly identified above. -/
theorem idealRowHom_prime_literal (c : ArithmeticContext) {P : Ideal O}
    (hP : Prime P) (hout : Outside c.S P) (a : O) :
    idealRowHom a P = sexticAtPrime P a := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hs := outside_supported c hout
  have hm : P ∈ normalizedFactors P :=
    (Ideal.mem_normalizedFactors_iff hout.1).mpr ⟨inferInstance, le_rfl⟩
  obtain ⟨hg, hc⟩ := hs.2 P hm
  rw [idealRowHom_prime a P hg]
  exact canonicalSextic_eq_literal P hP hg hc
    (SquarefreeReflection.RayValuePrerequisites.outside_quotient_rootSix_isPrimitiveRoot
      c hP hout) a

theorem numeratorCharacter_two (c : ArithmeticContext) : NumeratorCharacter c (2 : O) := by
  refine ⟨twoHeckeCharacter, modulus72_supported c, ?_⟩
  intro P hP hout
  rw [twoHeckeCharacter_rayValue c hout]
  exact idealRowHom_prime_literal c hP hout 2

theorem numeratorCharacter_lambda (c : ArithmeticContext) :
    NumeratorCharacter c (QRHShort.omega - 1) := by
  refine ⟨lambdaHeckeCharacter, modulus72_supported c, ?_⟩
  intro P hP hout
  rw [lambdaHeckeCharacter_rayValue c hout]
  exact idealRowHom_prime_literal c hP hout lam

end OAIInput

end QRHShort.CloudBatch.RamifiedLocal

namespace QRHShort.CloudBatch

theorem sf_sprime_ramified_local_proved :
    SquarefreeReflection.SPrimeRamifiedLocalReciprocityStatement := by
  intro c hc p hp
  rcases (SquarefreeReflection.sPrime_dvd_six_iff c p).mp hp with hp2 | hp3
  · exact RamifiedLocal.numeratorCharacter_of_associated c hc
      (RamifiedLocal.OAIInput.numeratorCharacter_two c)
      (RamifiedLocal.OAIInput.generator_associated_two (c.prime_S p.val p.property) hp2)
  · exact RamifiedLocal.localCharacter_of_above_three c hc p hp3
      (RamifiedLocal.OAIInput.numeratorCharacter_lambda c)

end QRHShort.CloudBatch
