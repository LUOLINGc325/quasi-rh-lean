import QRHShort.ThetaBoundsReduction
import QRHShort.PrimaryGenerator
import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-! A finite-ring Gauss bound for the literal cubic character and trace phase. -/

noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.CloudBatch.ThetaGauss

private theorem finiteField_third_power_test {F : Type*} [Field F] [Fintype F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ 3) (a : F) :
    (a ^ (3 : ℕ)) ^ ((Fintype.card F - 1) / 3) = if a = 0 then 0 else 1 := by
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  have hdvd : 3 ∣ Fintype.card F - 1 :=
    (hζ.pow_eq_one_iff_dvd _).mp
      (FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero (by decide)))
  have hpos : 0 < (Fintype.card F - 1) / 3 :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by decide)
  by_cases ha : a = 0
  · simp [ha, Nat.ne_of_gt hpos]
  · rw [if_neg ha, ← pow_mul, Nat.mul_div_cancel' hdvd]
    exact FiniteField.pow_card_sub_one_eq_one a ha


private theorem omega_pow_mod (m : ℕ) : omega ^ (m % 3) = omega ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, omega_cube,
    one_pow, mul_one]


private theorem cubicAtPrime_eq_of_test {P : Ideal O}
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3)
    {a : O} {j : ℕ} (hj : j < 3)
    (ht : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3) =
      Ideal.Quotient.mk P (omega ^ j)) :
    cubicAtPrime P a = embedding (omega ^ j) := by
  unfold cubicAtPrime
  rw [Finset.sum_eq_single j]
  · exact if_pos ht
  · intro i hi hij
    apply if_neg
    intro hiTest
    apply hij
    apply hζ.pow_inj (Finset.mem_range.mp hi) hj
    simpa only [map_pow] using hiTest.symm.trans ht
  · exact fun h => (h (Finset.mem_range.mpr hj)).elim


private theorem cubicAtPrime_zero_of_mem {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3)
    {a : O} (ha : a ∈ P) : cubicAtPrime P a = 0 := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have ht6 := finiteField_third_power_test hζ (Ideal.Quotient.mk P a)
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr ha)] at ht6
  have ht : Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 3)
    simpa only [← pow_mul, Nat.mul_comm, hcard] using ht6
  unfold cubicAtPrime
  apply Finset.sum_eq_zero
  intro j _
  apply if_neg
  rw [ht, map_pow]
  exact (pow_ne_zero j (hζ.ne_zero (by decide))).symm

private theorem cubicAtPrime_index {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3)
    {a : O} (ha : a ∉ P) :
    ∃ j < 3, Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3) =
      Ideal.Quotient.mk P (omega ^ j) := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have ht6 := finiteField_third_power_test hζ (Ideal.Quotient.mk P a)
  rw [if_neg (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))] at ht6
  have ht : (Ideal.Quotient.mk P a ^ ((P.absNorm - 1) / 3)) ^ 3 = 1 := by
    simpa only [← pow_mul, Nat.mul_comm, hcard] using ht6
  obtain ⟨j, hj, heq⟩ := hζ.eq_pow_of_pow_eq_one ht
  exact ⟨j, hj, by simpa only [map_pow] using heq.symm⟩

/-- Multiplicativity in the numerator, with no coprimality restriction. -/
private theorem cubicAtPrime_mul {P : Ideal O} (hP : Prime P)
    (hζ : IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3) (a b : O) :
    cubicAtPrime P (a * b) = cubicAtPrime P a * cubicAtPrime P b := by
  by_cases ha : a ∈ P
  · rw [cubicAtPrime_zero_of_mem hP hζ (P.mul_mem_right b ha),
      cubicAtPrime_zero_of_mem hP hζ ha, zero_mul]
  by_cases hb : b ∈ P
  · rw [cubicAtPrime_zero_of_mem hP hζ (P.mul_mem_left a hb),
      cubicAtPrime_zero_of_mem hP hζ hb, mul_zero]
  obtain ⟨i, hi, hit⟩ := cubicAtPrime_index hP hζ ha
  obtain ⟨j, hj, hjt⟩ := cubicAtPrime_index hP hζ hb
  have hij : Ideal.Quotient.mk P (a * b) ^ ((P.absNorm - 1) / 3) =
      Ideal.Quotient.mk P (omega ^ ((i + j) % 3)) := by
    rw [omega_pow_mod, map_mul, mul_pow, hit, hjt, ← map_mul, ← pow_add]
  rw [cubicAtPrime_eq_of_test hζ (Nat.mod_lt _ (by decide)) hij,
    cubicAtPrime_eq_of_test hζ hi hit, cubicAtPrime_eq_of_test hζ hj hjt,
    omega_pow_mod, pow_add, embedding_mul]


private def Good (I : Ideal O) : Prop :=
  I ≠ ⊥ ∧ ∀ P : Ideal O, Prime P → P ∣ I → ¬ P ∣ principal 3

private theorem good_of_primary {n : O} (hn : n ≠ 0) (hprimary : IsPrimary n) :
    Good (principal n) := by
  refine ⟨fun h => hn (Ideal.span_singleton_eq_bot.mp h), ?_⟩
  intro P hP hPn hP3
  have hnP : n ∈ P := Ideal.dvd_span_singleton.mp hPn
  have h3P : (3 : O) ∈ P := Ideal.dvd_span_singleton.mp hP3
  have hsub : n - 1 ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr h3P hprimary
  have hone : (1 : O) ∈ P := by convert P.sub_mem hnP hsub using 1 <;> ring
  exact (Ideal.isPrime_of_prime hP).ne_top ((Ideal.eq_top_iff_one P).mpr hone)

private theorem good_of_dvd {I J : Ideal O} (hJ : Good J) (hIJ : I ∣ J) : Good I := by
  refine ⟨?_, fun P hP hPI => hJ.2 P hP (hPI.trans hIJ)⟩
  intro hI
  exact hJ.1 (bot_unique (hI ▸ Ideal.dvd_iff_le.mp hIJ))

private theorem cubicSymbol_congr {I : Ideal O} (hI : Good I) {a b : O}
    (hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b) :
    cubicSymbol I a = cubicSymbol I b := by
  simp only [cubicSymbol, ite_eq_right hI.1]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hIP : I ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
  have habP : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b :=
    Ideal.Quotient.eq.mpr (hIP (Ideal.Quotient.eq.mp hab))
  simp only [cubicAtPrime, habP]

private theorem cubicSymbol_one {I : Ideal O} (hI : Good I) : cubicSymbol I 1 = 1 := by
  simp only [cubicSymbol, ite_eq_right hI.1]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  have hζ := quotient_omega_isPrimitiveRoot P
    (hI.2 P (prime_of_normalized_factor P hP) (dvd_of_mem_normalizedFactors hP))
  have ht : Ideal.Quotient.mk P 1 ^ ((P.absNorm - 1) / 3) =
      Ideal.Quotient.mk P (omega ^ (0 : ℕ)) := by simp
  simpa only [pow_zero, embedding_one] using cubicAtPrime_eq_of_test hζ (by decide : 0 < 3) ht

private theorem cubicSymbol_mul_numerator {I : Ideal O} (hI : Good I) (a b : O) :
    cubicSymbol I (a * b) = cubicSymbol I a * cubicSymbol I b := by
  simp only [cubicSymbol, ite_eq_right hI.1]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact cubicAtPrime_mul hp
    (quotient_omega_isPrimitiveRoot P (hI.2 P hp (dvd_of_mem_normalizedFactors hP))) a b

private theorem cubicSymbol_zero_of_nonunit {I : Ideal O} (hI : Good I) (a : O)
    (ha : ¬ IsUnit (Ideal.Quotient.mk I a)) : cubicSymbol I a = 0 := by
  by_contra hzero
  have hcop : IsCoprime I (principal a) := by
    apply Ideal.coprime_of_no_prime_ge
    intro P hIP haP hP
    have hP0 : P ≠ ⊥ := fun h => hI.1 (le_bot_iff.mp (h ▸ hIP))
    have hp : Prime P := Ideal.prime_of_isPrime hP0 hP
    have hmem : P ∈ normalizedFactors I :=
      (mem_normalizedFactors_iff hI.1).mpr ⟨hp, Ideal.dvd_iff_le.mpr hIP⟩
    apply hzero
    rw [cubicSymbol, ite_eq_right hI.1]
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.mpr ⟨P, hmem, ?_⟩
    exact cubicAtPrime_zero_of_mem hp
      (quotient_omega_isPrimitiveRoot P (hI.2 P hp (dvd_of_mem_normalizedFactors hmem)))
      ((Ideal.span_singleton_le_iff_mem P).mp haP)
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp hcop
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hy
  apply ha
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk I b, ?_⟩
  have h := congrArg (Ideal.Quotient.mk I) hxy
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_add, map_one] at h
  simpa only [hb, map_mul] using h

private theorem lift_spec (I : Ideal O) (x : O ⧸ I) :
    Ideal.Quotient.mk I (residueLift I x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

private def cubicChar (I : Ideal O) (hI : Good I) : MulChar (O ⧸ I) ℂ where
  toFun x := cubicSymbol I (residueLift I x)
  map_one' := by
    rw [cubicSymbol_congr hI (by simp only [lift_spec, map_one] :
      Ideal.Quotient.mk I (residueLift I 1) = Ideal.Quotient.mk I 1)]
    exact cubicSymbol_one hI
  map_mul' x y := by
    rw [cubicSymbol_congr hI (by simp only [lift_spec, map_mul] :
      Ideal.Quotient.mk I (residueLift I (x * y)) =
        Ideal.Quotient.mk I (residueLift I x * residueLift I y))]
    exact cubicSymbol_mul_numerator hI _ _
  map_nonunit' x hx := cubicSymbol_zero_of_nonunit hI _ (by
    simpa only [lift_spec] using hx)

private theorem cubicChar_mk (I : Ideal O) (hI : Good I) (a : O) :
    cubicChar I hI (Ideal.Quotient.mk I a) = cubicSymbol I a :=
  cubicSymbol_congr hI (lift_spec _ _)


private theorem symbol_mul (a b : Ideal O) (z : O) :
    cubicSymbol (a * b) z = cubicSymbol a z * cubicSymbol b z := by
  by_cases ha : a = ⊥
  · simp [ha, cubicSymbol]
  by_cases hb : b = ⊥
  · simp [hb, cubicSymbol]
  have hab : a * b ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim ha hb
  simp only [cubicSymbol, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab,
    normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

private theorem symbol_prime {P : Ideal O} (hP : Prime P) (x : O) :
    cubicSymbol P x = cubicAtPrime P x := by
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := {P}) (by simpa using hP))
  simp only [cubicSymbol, ite_eq_right hP0, hf,
    Multiset.map_singleton, Multiset.prod_singleton]

private theorem symbol_one_of_residue_one {n : Ideal O}
    (hn : Good n) {x : O} (hx : Ideal.Quotient.mk n x = 1) :
    cubicSymbol n x = 1 := by
  rw [← cubicChar_mk n hn, hx, map_one]

private theorem finiteField_power_test_surjective {F : Type*}
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


private theorem prime_hits_omega {P : Ideal O} (hP : Prime P) (hout : Good P) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk P x) ∧ cubicSymbol P x = embedding omega := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Finite (O ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP.ne_zero
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hζ := quotient_omega_isPrimitiveRoot P (hout.2 P hP (dvd_refl P))
  obtain ⟨y, hy, htest⟩ := finiteField_power_test_surjective
    (by decide : (3 : ℕ) ≠ 0) hζ hζ.pow_eq_one
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨x, ?_, ?_⟩
  · rw [hx]
    exact isUnit_iff_ne_zero.mpr hy
  · rw [symbol_prime hP]
    have hcard : P.absNorm = Fintype.card (O ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have htest' : Ideal.Quotient.mk P x ^ ((P.absNorm - 1) / 3) =
        Ideal.Quotient.mk P (omega ^ (1 : ℕ)) := by
      simpa only [hcard, hx, pow_one] using htest
    simpa only [pow_one] using cubicAtPrime_eq_of_test hζ (by decide : 1 < 3) htest'

private theorem omega_ne_one : embedding omega ≠ 1 := by
  intro h
  have hc : embedding omega ^ 2 + embedding omega + 1 = (0 : ℂ) := by
    simpa only [embedding_add, embedding_pow, embedding_one, embedding_zero] using
      congrArg embedding omega_sq_add_omega_add_one
  rw [h] at hc
  norm_num at hc
private theorem ideal_isCoprime_of_isRelPrime {a b : Ideal O}
    (hab : IsRelPrime a b) : IsCoprime a b := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp (hab
    (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

private theorem quotient_mul_isUnit_iff (a b : Ideal O) (hab : IsCoprime a b)
    (x : O ⧸ (a * b)) :
    IsUnit x ↔ IsUnit (Ideal.Quotient.factor Ideal.mul_le_left x) ∧
      IsUnit (Ideal.Quotient.factor Ideal.mul_le_right x) := by
  let e := Ideal.quotientMulEquivQuotientProd a b hab
  rw [← isUnit_map_iff e x, Prod.isUnit_iff]
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

private theorem crt_unit_lift (a b : Ideal O) (hab : IsCoprime a b)
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
  apply (quotient_mul_isUnit_iff a b hab _).mpr
  simpa only [Ideal.Quotient.factor_mk, hxa, hxb] using And.intro hu isUnit_one

private theorem squarefree_dvd_of_prime_dvd {n J : Ideal O}
    (hn : n ≠ ⊥) (hJ : J ≠ ⊥) (hsq : Squarefree n)
    (hprime : ∀ P : Ideal O, Prime P → P ∣ n → P ∣ J) : n ∣ J := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hn hJ).mpr
  apply (Multiset.le_iff_subset ((squarefree_iff_nodup_normalizedFactors hn).mp hsq)).mpr
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact (mem_normalizedFactors_iff hJ).mpr ⟨hp, hprime P hp (dvd_of_mem_normalizedFactors hP)⟩

private theorem missing_prime_witness
    {n J P : Ideal O} (hn : Good n) (hsq : Squarefree n) (hP : Prime P) (hPn : P ∣ n)
    (hnJ : n ≤ J) (hnot : ¬ P ∣ J) :
    ∃ x : O, IsUnit (Ideal.Quotient.mk n x) ∧
      Ideal.Quotient.mk J x = 1 ∧ cubicSymbol n x ≠ 1 := by
  obtain ⟨A, hA⟩ := hPn
  have hPout := good_of_dvd hn (show P ∣ n from ⟨A, hA⟩)
  have hAout := good_of_dvd hn (show A ∣ n from ⟨P, hA.trans (mul_comm _ _)⟩)
  have hcop : IsCoprime P A := ideal_isCoprime_of_isRelPrime
    (IsRelPrime.of_squarefree_mul (hA ▸ hsq))
  have hJdiv : J ∣ P * A := by
    rw [← hA]
    exact Ideal.dvd_iff_le.mpr hnJ
  have hJA : J ∣ A :=
    ((hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot).symm).dvd_of_dvd_mul_left hJdiv
  obtain ⟨u, hu, hζ⟩ := prime_hits_omega hP hPout
  obtain ⟨x, hxP, hxA, hxunit⟩ := crt_unit_lift P A hcop u hu
  have hxJ : Ideal.Quotient.mk J x = 1 := by
    have h := congrArg (Ideal.Quotient.factor (Ideal.le_of_dvd hJA)) hxA
    simpa only [Ideal.Quotient.factor_mk, map_one] using h
  have hxPvalue : cubicSymbol P x = embedding omega :=
    (cubicSymbol_congr hPout hxP).trans hζ
  have hxvalue : cubicSymbol n x = embedding omega := by
    rw [hA, symbol_mul, symbol_one_of_residue_one hAout hxA,
      hxPvalue, mul_one]
  refine ⟨x, ?_, hxJ, ?_⟩
  · rwa [hA]
  · rw [hxvalue]
    exact omega_ne_one


private def PrimitiveOnIdeals {R : Type*} [CommRing R] (χ : MulChar R ℂ) : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃ u : Rˣ, (u : R) - 1 ∈ I ∧ χ (u : R) ≠ 1

private theorem cubicChar_primitive {n : Ideal O} (hn : Good n) (hsq : Squarefree n) :
    PrimitiveOnIdeals (cubicChar n hn) := by
  intro I hI
  let J : Ideal O := Ideal.comap (Ideal.Quotient.mk n) I
  have hnJ : n ≤ J := by
    intro a ha
    change Ideal.Quotient.mk n a ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact I.zero_mem
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    exact hn.1 (bot_unique (hJ ▸ hnJ))
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
    have hdiv : n ∣ J := squarefree_dvd_of_prime_dvd hn.1 hJ0 hsq hnone
    exact hJne (le_antisymm (Ideal.le_of_dvd hdiv) hnJ)
  obtain ⟨P, hP, hPn, hnot⟩ := hmissing
  obtain ⟨x, hxunit, hxJ, hxvalue⟩ := missing_prime_witness hn hsq hP hPn hnJ hnot
  refine ⟨hxunit.unit, ?_, ?_⟩
  · rw [hxunit.unit_spec]
    have hsub : x - 1 ∈ J := (Ideal.Quotient.mk_eq_one_iff_sub_mem x).mp hxJ
    have hmem : Ideal.Quotient.mk n (x - 1) ∈ I := hsub
    simpa only [map_sub, map_one] using hmem
  · rw [hxunit.unit_spec, cubicChar_mk]
    exact hxvalue

section FiniteRing
variable {R : Type*} [CommRing R] [Fintype R]

private theorem exists_nonzero_annihilator {a : R} (ha : ¬ IsUnit a) :
    ∃ b : R, b ≠ 0 ∧ a * b = 0 := by
  by_contra! h
  apply ha
  apply IsLeftRegular.isUnit_of_finite
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro b hb
  by_contra hb0
  exact h b hb0 hb

private theorem exists_unit_stabilizer (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    {a : R} (ha : ¬ IsUnit a) :
    ∃ u : Rˣ, a * (u : R) = a ∧ χ (u : R) ≠ 1 := by
  obtain ⟨b, hb, hab⟩ := exists_nonzero_annihilator ha
  have hI : Ideal.span ({b} : Set R) ≠ ⊥ := by
    intro hI
    have hbI := Ideal.mem_span_singleton_self b
    rw [hI] at hbI
    exact hb hbI
  obtain ⟨u, hu, hχu⟩ := hχ _ hI
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hu
  refine ⟨u, ?_, hχu⟩
  have hzero : a * ((u : R) - 1) = 0 := by
    rw [hd, ← mul_assoc, hab, zero_mul]
  linear_combination hzero

private theorem gaussSum_nonunit_shift (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) {a : R} (ha : ¬ IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  obtain ⟨u, hu, hχu⟩ := exists_unit_stabilizer χ hχ ha
  have hshift : (ψ.mulShift a).mulShift (u : R) = ψ.mulShift a := by
    ext x
    simp only [AddChar.mulShift_apply, ← mul_assoc, hu]
  have heq := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hshift] at heq
  exact eq_zero_of_mul_eq_self_left hχu heq

private theorem gaussSum_shift (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa only [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [gaussSum_nonunit_shift χ hχ ψ ha, MulChar.map_nonunit _ ha, zero_mul]

private theorem fourier_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (x : R) :
    (∑ a : R, (∑ y : R, f y * ψ (a * y)) * ψ (-(a * x))) =
      (Fintype.card R : ℂ) * f x := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y : R, ∑ a : R, f y * ψ (a * y) * ψ (-(a * x))) =
        ∑ y : R, f y * ∑ a : R, ψ (a * (y - x)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (Fintype.card R : ℂ) * f x := by
      simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero]
      simp [mul_ite, mul_comm]

private theorem gaussSum_mul_conjugate (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by
  have hinv := fourier_inversion ψ hψ (fun x => χ x) 1
  change (∑ a : R, gaussSum χ (ψ.mulShift a) * ψ (-(a * 1))) = _ at hinv
  simp only [gaussSum_shift χ hχ, mul_one, map_one] at hinv
  rw [star_gaussSum_eq]
  calc
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ =
        ∑ a : R, (χ⁻¹ a * gaussSum χ ψ) * ψ (-a) := by
      change gaussSum χ ψ * (∑ a : R, χ⁻¹ a * ψ⁻¹ a) = _
      rw [Finset.mul_sum]
      simp only [AddChar.inv_apply]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (Fintype.card R : ℂ) := hinv


private theorem gaussSum_norm_le (χ : MulChar R ℂ) (hχ : PrimitiveOnIdeals χ)
    (ψ : AddChar R ℂ) : ‖gaussSum χ ψ‖ ≤ Real.sqrt (Fintype.card R) := by
  by_cases hψ : ψ.IsPrimitive
  · have h := congrArg Complex.re (gaussSum_mul_conjugate χ hχ ψ hψ)
    simp only [Complex.star_def] at h
    rw [Complex.mul_conj] at h
    simp only [Complex.ofReal_re, Complex.natCast_re] at h
    rw [Complex.normSq_eq_norm_sq] at h
    have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card R) : (0 : ℝ) ≤ _)
    nlinarith [norm_nonneg (gaussSum χ ψ), Real.sqrt_nonneg (Fintype.card R)]
  · have hnot : ∃ a : R, a ≠ 0 ∧ ψ.mulShift a = 1 := by
      by_contra! hh
      exact hψ (by intro a ha he; exact hh a ha he)
    obtain ⟨a, ha, hshift⟩ := hnot
    have hI : Ideal.span ({a} : Set R) ≠ ⊥ := by
      intro hI
      exact ha (Ideal.span_singleton_eq_bot.mp hI)
    obtain ⟨u, hu, hχu⟩ := hχ _ hI
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hu
    have hu' : (u : R) = 1 + a * d := by linear_combination hd
    have hψu : ψ.mulShift (u : R) = ψ := by
      ext x
      have ht := congrArg (fun η : AddChar R ℂ => η (d * x)) hshift
      simp only [AddChar.mulShift_apply, AddChar.one_apply] at ht
      change ψ ((u : R) * x) = ψ x
      rw [hu', add_mul, one_mul, mul_assoc, AddChar.map_add_eq_mul, ht, mul_one]
    have heq := gaussSum_mulShift χ ψ u
    rw [hψu] at heq
    have hz : gaussSum χ ψ = 0 := eq_zero_of_mul_eq_self_left hχu heq
    rw [hz, norm_zero]
    exact Real.sqrt_nonneg _

end FiniteRing


private def theta_integralPB : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

private theorem theta_integralPB_dim : theta_integralPB.dim = 2 := by
  change (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

private def theta_integralBasis : Module.Basis (Fin 2) ℤ O :=
  theta_integralPB.basis.reindex (finCongr theta_integralPB_dim)

private theorem theta_basis_zero : theta_integralBasis 0 = 1 := by
  rw [theta_integralBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change theta_integralPB.gen ^ (0 : ℕ) = 1
  exact pow_zero _

private theorem theta_basis_one : theta_integralBasis 1 = omega := by
  rw [theta_integralBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change theta_integralPB.gen ^ (1 : ℕ) = omega
  rw [pow_one]
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

private theorem theta_integral_coords (a : O) :
    a = (theta_integralBasis.repr a 0 : O) + (theta_integralBasis.repr a 1 : O) * omega := by
  simpa [Fin.sum_univ_two, theta_basis_zero, theta_basis_one, Algebra.smul_def] using
    (theta_integralBasis.sum_repr a).symm

private theorem theta_repr_pair (x y : ℤ) (i : Fin 2) :
    theta_integralBasis.repr ((x : O) + (y : O) * omega) i = ![x, y] i := by
  have h : (x : O) + (y : O) * omega =
      x • theta_integralBasis 0 + y • theta_integralBasis 1 := by
    simp [theta_basis_zero, theta_basis_one, Algebra.smul_def]
  rw [h, map_add, map_smul, map_smul]
  fin_cases i <;> simp [Module.Basis.repr_self_apply]

private theorem theta_algebra_norm (a : O) :
    Algebra.norm ℤ a = theta_integralBasis.repr a 0 ^ 2 -
      theta_integralBasis.repr a 0 * theta_integralBasis.repr a 1 +
      theta_integralBasis.repr a 1 ^ 2 := by
  let x := theta_integralBasis.repr a 0
  let y := theta_integralBasis.repr a 1
  have ha : a = (x : O) + (y : O) * omega := theta_integral_coords a
  have hmul : a * omega = ((-y : ℤ) : O) + ((x - y : ℤ) : O) * omega := by
    rw [ha]
    push_cast
    calc
      ((x : O) + (y : O) * omega) * omega =
          -(y : O) + ((x : O) - (y : O)) * omega +
            (y : O) * (omega ^ 2 + omega + 1) := by ring
      _ = _ := by rw [omega_sq_add_omega_add_one]; ring
  have hmatrix : Algebra.leftMulMatrix theta_integralBasis a = !![x, -y; y, x - y] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j
    · change theta_integralBasis.repr (a * theta_integralBasis 0) 0 = x
      rw [theta_basis_zero, mul_one]
    · change theta_integralBasis.repr (a * theta_integralBasis 1) 0 = -y
      rw [theta_basis_one, hmul, theta_repr_pair]
      rfl
    · change theta_integralBasis.repr (a * theta_integralBasis 0) 1 = y
      rw [theta_basis_zero, mul_one]
    · change theta_integralBasis.repr (a * theta_integralBasis 1) 1 = x - y
      rw [theta_basis_one, hmul, theta_repr_pair]
      rfl
  rw [Algebra.norm_eq_matrix_det theta_integralBasis, hmatrix, Matrix.det_fin_two]
  dsimp [x, y]
  ring

private theorem theta_embedding_int (x : ℤ) : embedding (x : O) = (x : ℂ) := by
  simpa only [embeddingHom_apply] using map_intCast embeddingHom x

private theorem theta_omega_parts :
    (embedding omega).re = -(1 : ℝ) / 2 ∧
      (embedding omega).im = Real.sqrt 3 / 2 := by
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
  refine ⟨hre, ?_⟩
  change w.im = _
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

private theorem theta_omega_re : (embedding omega).re = -(1 : ℝ) / 2 :=
  theta_omega_parts.1

private theorem theta_omega_im : (embedding omega).im = Real.sqrt 3 / 2 :=
  theta_omega_parts.2

private theorem theta_embedding_norm_sq (a : O) :
    ‖embedding a‖ ^ 2 = (theta_integralBasis.repr a 0 : ℝ) ^ 2 -
      (theta_integralBasis.repr a 0 : ℝ) * (theta_integralBasis.repr a 1 : ℝ) +
      (theta_integralBasis.repr a 1 : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  conv_lhs => rw [theta_integral_coords a, embedding_add,
    embedding_mul, theta_embedding_int, theta_embedding_int]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, theta_omega_re,
    theta_omega_im, zero_mul, sub_zero, add_zero, zero_add]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

private theorem theta_normElement_eq_sq (a : O) : normElement a = ‖embedding a‖ ^ 2 := by
  have hnonneg : 0 ≤ Algebra.norm ℤ a := by
    rw [theta_algebra_norm]
    nlinarith [sq_nonneg (2 * theta_integralBasis.repr a 0 - theta_integralBasis.repr a 1),
      sq_nonneg (theta_integralBasis.repr a 1)]
  have hnorm : ((principal a).absNorm : ℤ) = Algebra.norm ℤ a := by
    rw [principal, Ideal.absNorm_span_singleton, Int.natCast_natAbs, abs_of_nonneg hnonneg]
  have hreal := congrArg (fun x : ℤ => (x : ℝ)) hnorm
  simp only [Int.cast_natCast, theta_algebra_norm, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow] at hreal
  rw [normElement, normIdeal, theta_embedding_norm_sq]
  exact hreal


private theorem breve_add (z w : ℂ) : breve (z + w) = breve z * breve w := by
  unfold breve
  rw [← Complex.exp_add]
  congr 1
  simp only [star_add]
  ring

private theorem breve_zero : breve 0 = 1 := by simp [breve]

private theorem breve_embedding (a : O) : breve (embedding a) = 1 := by
  let x : ℤ := theta_integralBasis.repr a 0
  let y : ℤ := theta_integralBasis.repr a 1
  have hre : (embedding a).re = (x : ℝ) - (y : ℝ) / 2 := by
    rw [theta_integral_coords a, embedding_add, embedding_mul,
      theta_embedding_int, theta_embedding_int]
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, theta_omega_re, zero_mul, sub_zero]
    dsimp only [x, y]
    ring
  have htrace : embedding a + star (embedding a) = ((2 * x - y : ℤ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.star_def, Complex.conj_re,
        Complex.intCast_re]
      push_cast
      rw [hre]
      ring
    · simp
  have hexp : (2 * Real.pi : ℂ) * Complex.I *
      (embedding a + star (embedding a)) =
        ((2 * x - y : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [htrace]
    ring
  unfold breve
  push_cast
  rw [hexp, Complex.exp_int_mul_two_pi_mul_I]

private theorem breve_add_embedding (z : ℂ) (a : O) :
    breve (z + embedding a) = breve z := by
  rw [breve_add, breve_embedding, mul_one]

private theorem breve_div_congr {q x y : O} (hq : q ≠ 0)
    (hxy : Ideal.Quotient.mk (principal q) x = Ideal.Quotient.mk (principal q) y) :
    breve (embedding x / embedding q) = breve (embedding y / embedding q) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hxy)
  have hx : x = y + q * z := by linear_combination hz
  have harg : embedding x / embedding q = embedding y / embedding q + embedding z := by
    rw [hx, embedding_add, embedding_mul]
    field_simp [embedding_eq_zero.not.mpr hq]
  rw [harg, breve_add_embedding]

private def breveChar (q : O) (hq : q ≠ 0) (m : O) :
    AddChar (O ⧸ principal q) ℂ where
  toFun x := breve (embedding (m * residueLift (principal q) x) / embedding q)
  map_zero_eq_one' := by
    have heq : Ideal.Quotient.mk (principal q) (m * residueLift (principal q) 0) =
        Ideal.Quotient.mk (principal q) 0 := by
      rw [map_mul, lift_spec, mul_zero, map_zero]
    rw [breve_div_congr hq heq, embedding_zero, zero_div, breve_zero]
  map_add_eq_mul' x y := by
    have heq : Ideal.Quotient.mk (principal q) (m * residueLift (principal q) (x + y)) =
        Ideal.Quotient.mk (principal q)
          (m * residueLift (principal q) x + m * residueLift (principal q) y) := by
      simp only [map_mul, map_add, lift_spec, mul_add]
    rw [breve_div_congr hq heq, embedding_add, add_div, breve_add]

private theorem proved : ThetaBoundsProof.CubicGaussBoundStatement := by
  intro r n hn hprimary hsq
  have hg := good_of_primary hn hprimary
  letI : Finite (O ⧸ principal n) := Ring.HasFiniteQuotients.finiteQuotient hg.1
  letI : Fintype (O ⧸ principal n) := Fintype.ofFinite _
  have heq : cubicGauss r n = gaussSum (cubicChar (principal n) hg) (breveChar n hn r) := by
    rw [cubicGauss, dif_pos hg.1]
    rfl
  have hcard : (Fintype.card (O ⧸ principal n) : ℝ) = normElement n := by
    simp only [normElement, normIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_eq_fintype_card]
  rw [heq]
  have h := gaussSum_norm_le (cubicChar (principal n) hg)
    (cubicChar_primitive hg hsq) (breveChar n hn r)
  rw [hcard, theta_normElement_eq_sq, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

end QRHShort.CloudBatch.ThetaGauss

namespace QRHShort.CloudBatch

theorem theta_bounds_gauss_proved : ThetaBoundsProof.CubicGaussBoundStatement :=
  ThetaGauss.proved

end QRHShort.CloudBatch

#print axioms QRHShort.CloudBatch.theta_bounds_gauss_proved
