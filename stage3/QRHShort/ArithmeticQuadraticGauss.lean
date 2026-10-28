import QRHShort.ArithmeticQuadraticGaussLocal
import QRHShort.CubicGaussEvaluation
import OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius

noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators

namespace QRHShort.ArithmeticProof.Ray.QuadraticGauss
open SquarefreeReflection SquarefreeReflection.RayValuePrerequisites
open CubicGauss
open OAI.ConcreteTraceCRT (eisEmbedding eisTraceModChar)
open OAI.QuadraticGaussRay
open OAI.ActualEisensteinCoordinates hiding O omega

theorem prime_char_ne_two (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] : ringChar (O ⧸ P) ≠ 2 := by
  apply OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem
  intro htwo
  exact hn.2 P (c.above_two P hp (Ideal.dvd_span_singleton.mpr htwo)) (dvd_refl P)

theorem sixth_root_lift_injective {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P rootSix) 6)
    {a b : O} (ha : a ^ (6 : ℕ) = 1) (hb : b ^ (6 : ℕ) = 1)
    (hab : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) : a = b := by
  have hroot : IsPrimitiveRoot rootSix 6 := by
    refine ⟨rootSix_pow_six, ?_⟩
    intro l hl
    exact hζ.dvd_of_pow_eq_one l (by rw [← map_pow, hl, map_one])
  obtain ⟨i, hi, hie⟩ := hroot.eq_pow_of_pow_eq_one ha
  obtain ⟨j, hj, hje⟩ := hroot.eq_pow_of_pow_eq_one hb
  rw [← hie, ← hje, map_pow, map_pow] at hab
  have hij := hζ.pow_inj hi hj hab
  subst j
  exact hie.symm.trans hje

/-- Identify the actual sixth-power-residue definition with the upstream
multiplicative character, including its zero value. -/
theorem prime_sextic_symbol (c : ArithmeticContext) {P : Ideal O} (hp : Prime P)
    (hn : Outside c.S P) [P.IsMaximal] (a : O) :
    sexticSymbol P a = OAI.ActualEisensteinCubic.canonicalSextic P
      (prime_good c hp hn) (Ideal.Quotient.mk P a) := by
  let χ := OAI.ActualEisensteinCubic.sexticChar P (prime_good c hp hn)
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hp hn
  rw [sexticSymbol_prime hp]
  by_cases ha : a ∈ P
  · rw [sexticAtPrime_zero_of_mem hp hζ ha,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, MulChar.map_zero]
  have hunit : IsUnit (Ideal.Quotient.mk P a) :=
    isUnit_iff_ne_zero.mpr (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hχpow : χ (Ideal.Quotient.mk P a) ^ (6 : ℕ) = 1 := by
    rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
      (OAI.ActualEisensteinCubic.sexticChar_powers P (prime_good c hp hn)).2.2]
    exact MulChar.one_apply hunit
  obtain ⟨j, hj, ht⟩ := sexticAtPrime_index hp hζ ha
  have hpow : (rootSix ^ j) ^ (6 : ℕ) = 1 := by
    rw [← pow_mul, Nat.mul_comm j 6, pow_mul, rootSix_pow_six, one_pow]
  have hreduce : Ideal.Quotient.mk P (χ (Ideal.Quotient.mk P a)) =
      Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 6) := by
    have hu := OAI.ActualEisensteinCubic.sexticChar_reduce_unit P
      (prime_good c hp hn) (prime_char_ne_two c hp hn) hunit.unit
    simpa only [IsUnit.unit_spec, Ideal.absNorm_apply, Submodule.cardQuot_apply, χ] using hu
  have he : rootSix ^ j = χ (Ideal.Quotient.mk P a) :=
    sixth_root_lift_injective hζ hpow hχpow (ht.symm.trans hreduce.symm)
  rw [sexticAtPrime_eq_of_test hζ hj ht, he, embedding_eq_eisEmbedding]
  rfl


/-- The QRH normalization uses the absolute norm of the principal ideal. -/
theorem sqrt_norm_span (z : O) :
    Real.sqrt (normIdeal (principal z)) = ‖eisEmbedding z‖ := by
  rw [normIdeal, principal, ← OAI.ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]

set_option maxHeartbeats 2000000 in
/-- Transport the full squarefree CRT sum, with the actual residue-symbol and
additive-character conventions, into the upstream canonical product. -/
theorem gauss_product (c : ArithmeticContext) {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hout : ∀ i, Outside c.S (principal (p i)))
    (hgen : primaryGenerator (principal (∏ i, p i)) = ∏ i, p i) :
    gauss 3 (principal (∏ i, p i)) =
      OAI.FiniteGaussPhase.canonicalProductGauss p hp hcop
        (fun i => prime_good c
          (Ideal.prime_of_isPrime (by
            intro h
            exact hp i (Ideal.span_singleton_eq_bot.mp h)) inferInstance) (hout i))
        (fun _ => 3) := by
  letI (i : ι) : (principal (p i)).IsMaximal :=
    inferInstanceAs ((Ideal.span {p i}).IsMaximal)
  have hprime (i : ι) : Prime (principal (p i)) :=
    Ideal.prime_of_isPrime (by
      intro h
      exact hp i (Ideal.span_singleton_eq_bot.mp h)) inferInstance
  have hgood (i : ι) : OAI.ActualEisensteinCubic.lambda ∉ Ideal.span {p i} :=
    prime_good c (hprime i) (hout i)
  have hn : principal (∏ i, p i) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hfac : UniqueFactorizationMonoid.normalizedFactors (principal (∏ i, p i)) =
      Finset.univ.val.map (fun i => principal (p i)) := by
    have hf := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
      (m := Finset.univ.val.map (fun i => principal (p i))) (by
        intro P hP
        obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hP
        exact hprime i)
    have he : (Finset.univ.val.map (fun i => principal (p i))).prod =
        principal (∏ i, p i) := (OAI.FiniteGaussPhase.span_finset_prod Finset.univ p).symm
    rwa [he] at hf
  have hs (a : O) : sexticSymbol (principal (∏ i, p i)) a =
      ∏ i, OAI.ActualEisensteinCubic.canonicalSextic (Ideal.span {p i})
        (hgood i) (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
    rw [sexticSymbol, if_neg hn, hfac, Multiset.map_map]
    change (∏ i, sexticAtPrime (principal (p i)) a) = _
    apply Finset.prod_congr rfl
    intro i _
    exact (sexticSymbol_prime (hprime i) a).symm.trans
      (prime_sextic_symbol c (hprime i) (hout i) a)
  letI : Finite (O ⧸ Ideal.span {∏ i, p i}) :=
    Ring.HasFiniteQuotients.finiteQuotient (show Ideal.span {∏ i, p i} ≠ ⊥ from hn)
  letI : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  rw [gauss, dif_pos hn, sqrt_norm_span, hgen]
  change (‖eisEmbedding (∏ i, p i)‖ : ℂ)⁻¹ * (∑ x : O ⧸ Ideal.span {∏ i, p i},
      sexticSymbol (principal (∏ i, p i)) (residueLift _ x) ^ (3 : ℤ) *
        additiveCharacter (embedding (residueLift _ x) / embedding (∏ i, p i))) =
    (∑ x : O ⧸ Ideal.span {∏ i, p i},
      (∏ i, (OAI.ActualEisensteinCubic.canonicalSextic (Ideal.span {p i})
        (hgood i) ^ 3)
        (OAI.FiniteGaussPhase.productElementCRT p hcop x i)) *
      eisTraceModChar OAI.ShortDraftTrace.breveE OAI.ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) x) /
      (‖eisEmbedding (∏ i, p i)‖ : ℂ)
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hx : Ideal.Quotient.mk (Ideal.span {∏ i, p i}) (residueLift _ x) = x :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective x)
  have hcoord (i : ι) : OAI.FiniteGaussPhase.productElementCRT p hcop x i =
      Ideal.Quotient.mk (Ideal.span {p i}) (residueLift _ x) := by
    simpa only [hx] using
      OAI.FiniteGaussPhase.productElementCRT_mk p hcop (residueLift _ x) i
  have ht :
      eisTraceModChar OAI.ShortDraftTrace.breveE OAI.ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) x =
      additiveCharacter (embedding (residueLift _ x) / embedding (∏ i, p i)) :=
    (congrArg (fun y : O ⧸ Ideal.span {∏ i, p i} =>
      eisTraceModChar OAI.ShortDraftTrace.breveE OAI.ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) y) hx.symm).trans
      (trace_char_mk (P := Ideal.span {∏ i, p i}) (∏ i, p i)
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) rfl (residueLift _ x))
  apply congrArg₂ (fun a b : ℂ => a * b)
  · rw [hs]
    simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), hcoord,
      Finset.prod_pow, zpow_ofNat]
  · exact ht.symm

/-- Upstream quadratic evaluation for every actual squarefree outside ideal. -/
theorem gauss_three_eq_rayValue (c : ArithmeticContext) (n : Ideal O)
    (hn : SquarefreeOutside c.S n) :
    gauss 3 n = quadraticRayValue (residue (primaryGenerator n)) := by
  let s := (UniqueFactorizationMonoid.normalizedFactors n).toFinset
  let p : s → O := fun P => primaryGenerator P.val
  have hprime (P : s) : Prime P.val :=
    UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_toFinset.mp P.property)
  have hout (P : s) : Outside c.S P.val :=
    outside_of_mem_normalizedFactors hn.1 (Multiset.mem_toFinset.mp P.property)
  have hspan (P : s) : principal (p P) = P.val :=
    (primaryGenerator_spec_outside c (hout P)).1
  have hp (P : s) : p P ≠ 0 := by
    intro hz
    have he := hspan P
    rw [hz] at he
    exact (hprime P).ne_zero (by simpa [principal] using he.symm)
  letI (P : s) : (Ideal.span {p P}).IsMaximal := by
    change (principal (p P)).IsMaximal
    rw [hspan]
    exact (Ideal.isPrime_of_prime (hprime P)).isMaximal (hprime P).ne_zero
  have hcop : Pairwise (Function.onFun IsCoprime (fun P => Ideal.span {p P})) := by
    intro P Q hne
    apply Ideal.isCoprime_of_isMaximal
    change principal (p P) ≠ principal (p Q)
    rw [hspan, hspan]
    exact fun h => hne (Subtype.ext h)
  have hspanAll : principal (∏ P, p P) = n := by
    rw [principal, OAI.FiniteGaussPhase.span_finset_prod]
    change (∏ P : s, principal (p P)) = n
    simp_rw [hspan]
    exact (Finset.prod_coe_sort s (fun P : Ideal O => P)).trans
      (OAI.IdealMobiusDivisorSum.squarefree_support_product_self hn.2)
  have hprimary : IsPrimary (∏ P, p P) := by
    have h (t : Finset s) : IsPrimary (∏ P ∈ t, p P) := by
      induction t using Finset.induction_on with
      | empty => simp [IsPrimary]
      | @insert P t hP ih =>
        rw [Finset.prod_insert hP]
        exact primary_mul (primaryGenerator_spec_outside c (hout P)).2 ih
    exact h Finset.univ
  have hgen : primaryGenerator n = ∏ P, p P :=
    primary_unique (primaryGenerator_spec_outside c hn.1).2 hprimary
      ((primaryGenerator_spec_outside c hn.1).1.trans hspanAll.symm)
  have hg (P : s) : Outside c.S (principal (p P)) := by rw [hspan]; exact hout P
  have hprod := gauss_product c p hp hcop hg (by rw [hspanAll]; exact hgen)
  rw [hspanAll] at hprod
  rw [hprod, canonicalProductGauss_three_eq_quadraticGamma,
    quadraticGammaO_eq_rayValue, ← hgen]
  intro P
  change ringChar (O ⧸ principal (p P)) ≠ 2
  rw [hspan]
  letI : P.val.IsMaximal :=
    (Ideal.isPrime_of_prime (hprime P)).isMaximal (hprime P).ne_zero
  exact prime_char_ne_two c (hprime P) (hout P)

end QRHShort.ArithmeticProof.Ray.QuadraticGauss

namespace QRHShort.ArithmeticProof.Ray
/-- The original frozen squarefree quadratic Gauss statement, without extra inputs. -/
theorem quadraticGaussSquareClass : QuadraticGaussSquareClassStatement := by
  intro c n hn x hx
  rw [QuadraticGauss.gauss_three_eq_rayValue c n hn]
  exact QuadraticGauss.rayValue_of_hasLocalClass hx
end QRHShort.ArithmeticProof.Ray

#print axioms OAI.QuadraticGaussRay.canonicalProductGauss_three_eq_quadraticGamma
#print axioms OAI.QuadraticGaussRay.quadraticGammaO_eq_rayValue
#print axioms QRHShort.ArithmeticProof.Ray.QuadraticGauss.gauss_product
#print axioms QRHShort.ArithmeticProof.Ray.QuadraticGauss.gauss_three_eq_rayValue
#print axioms QRHShort.ArithmeticProof.Ray.quadraticGaussSquareClass

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.checked.get.constants.toList do
    if (`QRHShort.ArithmeticProof.Ray.QuadraticGauss).isPrefixOf name ||
        name == `QRHShort.ArithmeticProof.Ray.quadraticGaussSquareClass then
      match info with
      | .thmInfo _ | .defnInfo _ =>
        checked := checked + 1
        for ax in (← collectAxioms name) do
          unless allowed.contains ax do
            throwError "Quadratic Gauss: forbidden axiom {ax} in {name}"
      | .axiomInfo _ => throwError "Quadratic Gauss declares axiom {name}"
      | _ => pure ()
  if checked == 0 then throwError "No quadratic Gauss declarations audited"
  logInfo m!"QUADRATIC_GAUSS_AUDIT declarations={checked} forbidden=0"
