import QRHShort.InverseGaussEvaluation
import QRHShort.QuotientSixthRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Squarefree.Basic

/-! Ideal-wise primitivity of the literal sextic residue character. A missing
prime of an inducing ideal is detected by a unit lifted through actual CRT. -/

noncomputable section
open Classical UniqueFactorizationMonoid

namespace QRHShort.CloudBatch
open ArithmeticProof.InverseGauss
open SquarefreeReflection.RayValuePrerequisites

private theorem inverse_outside_of_dvd (c : ArithmeticContext) {a b : Ideal O}
    (hb : Outside c.S b) (hab : a ∣ b) : Outside c.S a := by
  refine ⟨?_, fun P hP hPa => hb.2 P hP (hPa.trans hab)⟩
  intro ha
  exact hb.1 (bot_unique (ha ▸ Ideal.dvd_iff_le.mp hab))

private theorem inverse_symbol_mul (a b : Ideal O) (z : O) :
    sexticSymbol (a * b) z = sexticSymbol a z * sexticSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, sexticSymbol]
  by_cases hb : b = ⊥
  · simp [hb, sexticSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [sexticSymbol, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

private theorem inverse_symbol_prime {P : Ideal O} (hP : Prime P) (x : O) :
    sexticSymbol P x = sexticAtPrime P x := by
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := {P}) (by simpa using hP))
  simp only [sexticSymbol, ite_eq_right hP0, hf,
    Multiset.map_singleton, Multiset.prod_singleton]

private theorem inverse_symbol_one_of_residue_one (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) {x : O} (hx : Ideal.Quotient.mk n x = 1) :
    sexticSymbol n x = 1 := by
  rw [← sexticResidueCharacter_mk c n hn, hx, map_one]

private theorem inverse_finiteField_power_test_surjective {F : Type*}
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

private theorem inverse_prime_hits_rootSix (c : ArithmeticContext)
    {P : Ideal O} (hP : Prime P) (hout : Outside c.S P) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk P x) ∧ sexticSymbol P x = embedding rootSix := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := outside_quotient_rootSix_isPrimitiveRoot c hP hout
  obtain ⟨y, hy, htest⟩ := inverse_finiteField_power_test_surjective
    (by decide : (6 : ℕ) ≠ 0) hζ hζ.pow_eq_one
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨x, ?_, ?_⟩
  · rw [hx]
    exact isUnit_iff_ne_zero.mpr hy
  · rw [inverse_symbol_prime hP]
    have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have htest' : Ideal.Quotient.mk P x ^ ((P.absNorm - 1) / 6) =
        Ideal.Quotient.mk P (rootSix ^ (1 : ℕ)) := by
      simpa only [hcard, hx, pow_one] using htest
    simpa only [pow_one] using sexticAtPrime_eq_of_test hζ (by decide : 1 < 6) htest'

private theorem inverse_rootSix_ne_one : embedding rootSix ≠ 1 := by
  intro h
  have hc : embedding rootSix ^ 3 = (-1 : ℂ) := by
    rw [← embedding_pow, rootSix_cube, embedding_neg, embedding_one]
  rw [h] at hc
  norm_num at hc

private theorem inverse_ideal_isCoprime_of_isRelPrime {a b : Ideal O}
    (hab : IsRelPrime a b) : IsCoprime a b := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp (hab
    (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

private theorem inverse_quotient_mul_isUnit_iff (a b : Ideal O) (hab : IsCoprime a b)
    (x : O ⧸ (a * b)) :
    IsUnit x ↔ IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x) ∧
      IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  rw [← isUnit_map_iff e x, Prod.isUnit_iff]
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

private theorem inverse_crt_unit_lift (a b : Ideal O) (hab : IsCoprime a b)
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
  apply (inverse_quotient_mul_isUnit_iff a b hab _).mpr
  simpa only [Ideal.Quotient.factor_mk, hxa, hxb] using And.intro hu isUnit_one

private theorem inverse_squarefree_dvd_of_prime_dvd {n J : Ideal O}
    (hn : n ≠ ⊥) (hJ : J ≠ ⊥) (hsq : Squarefree n)
    (hprime : ∀ P : Ideal O, Prime P → P ∣ n → P ∣ J) : n ∣ J := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hn hJ).mpr
  apply (Multiset.le_iff_subset ((squarefree_iff_nodup_normalizedFactors hn).mp hsq)).mpr
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact (mem_normalizedFactors_iff hJ).mpr ⟨hp, hprime P hp (dvd_of_mem_normalizedFactors hP)⟩

private theorem inverse_missing_prime_witness (c : ArithmeticContext)
    {n J P : Ideal O} (hn : SquarefreeOutside c.S n) (hP : Prime P) (hPn : P ∣ n)
    (hnJ : n ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk n x) ∧
      Ideal.Quotient.mk J x = 1 ∧ sexticSymbol n x ≠ 1 := by
  obtain ⟨A, hA⟩ := hPn
  have hPout := inverse_outside_of_dvd c hn.1 (show P ∣ n from ⟨A, hA⟩)
  have hAout := inverse_outside_of_dvd c hn.1 (show A ∣ n from ⟨P, hA.trans (mul_comm _ _)⟩)
  have hcop : IsCoprime P A := inverse_ideal_isCoprime_of_isRelPrime
    (IsRelPrime.of_squarefree_mul (hA ▸ hn.2))
  have hJdiv : J ∣ P * A := by
    rw [← hA]
    exact Ideal.dvd_iff_le.mpr hnJ
  have hJA : J ∣ A :=
    ((hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot).symm).dvd_of_dvd_mul_left hJdiv
  obtain ⟨u, hu, hζ⟩ := inverse_prime_hits_rootSix c hP hPout
  obtain ⟨x, hxP, hxA, hxunit⟩ := inverse_crt_unit_lift P A hcop u hu
  have hxJ : Ideal.Quotient.mk J x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (Ideal.le_of_dvd hJA)) hxA
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxPvalue : sexticSymbol P x = embedding rootSix :=
    (sexticSymbol_congr c hPout hxP).trans hζ
  have hxvalue : sexticSymbol n x = embedding rootSix := by
    rw [hA, inverse_symbol_mul, inverse_symbol_one_of_residue_one c hAout hxA,
      hxPvalue, mul_one]
  refine ⟨x, ?_, hxJ, ?_⟩
  · rwa [hA]
  · rw [hxvalue]
    exact inverse_rootSix_ne_one

theorem arithmetic_inverse_sextic_primitive_proved :
    ArithmeticProof.InverseGauss.SexticPrimitivityStatement := by
  intro c n hn I hI
  let J : Ideal O := Ideal.comap (Ideal.Quotient.mk n) I
  have hnJ : n ≤ J := by
    intro a ha
    change Ideal.Quotient.mk n a ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact I.zero_mem
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    exact hn.1.1 (bot_unique (hJ ▸ hnJ))
  have hJne : J ≠ n := by
    intro hJn
    apply hI
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk n a = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have ha : a ∈ J := hx
    simpa only [hJn] using ha
  have hmissing : ∃ P : Ideal O, Prime P ∧ P ∣ n ∧ ¬ P ∣ J := by
    by_contra! hnone
    have hdiv : n ∣ J := inverse_squarefree_dvd_of_prime_dvd hn.1.1 hJ0 hn.2 hnone
    exact hJne (le_antisymm (Ideal.le_of_dvd hdiv) hnJ)
  obtain ⟨P, hP, hPn, hnot⟩ := hmissing
  obtain ⟨x, hxunit, hxJ, hxvalue⟩ := inverse_missing_prime_witness c hn hP hPn hnJ hnot
  refine ⟨hxunit.unit, ?_, ?_⟩
  · rw [hxunit.unit_spec]
    have hsub : x - 1 ∈ J := (Ideal.Quotient.mk_eq_one_iff_sub_mem x).mp hxJ
    have hmem : Ideal.Quotient.mk n (x - 1) ∈ I := hsub
    simpa only [map_sub, map_one] using hmem
  · rw [hxunit.unit_spec, sexticResidueCharacter_mk]
    exact hxvalue

end QRHShort.CloudBatch

#print axioms QRHShort.CloudBatch.arithmetic_inverse_sextic_primitive_proved
