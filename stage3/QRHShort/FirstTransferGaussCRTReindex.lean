import QRHShort.FirstTransferPairedCharacter
import QRHShort.FirstTransferGeneratorNormalization
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
The actual CRT reindexing used in the paired Gauss sum. Multiplication by
the opposite generator gives permutations of the two quotient rings, so the
representatives B*u + A*v cover the product quotient exactly once. Quotients
by the unit ideal are included throughout.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_gauss_crt_generator_isUnit (a b : Ideal O)
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
theorem first_transfer_gauss_crt_reindex (a b : Ideal O) (hab : IsCoprime a b)
    (A B : O) (hA : principal A = a) (hB : principal B = b)
    [Fintype (O ⧸ a)] [Fintype (O ⧸ b)] [Fintype (O ⧸ (a * b))]
    (f : O ⧸ (a * b) → ℂ) :
    (∑ x : O ⧸ (a * b), f x) =
      ∑ u : O ⧸ a, ∑ v : O ⧸ b,
        f (Ideal.Quotient.mk (a * b) (B * residueLift a u + A * residueLift b v)) := by
  let hBa := first_transfer_gauss_crt_generator_isUnit a b hab B hB
  let hAb := first_transfer_gauss_crt_generator_isUnit b a hab.symm A hA
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
        firstTransferResidueLift_spec, IsUnit.unit_spec]
    · change hAb.unit * v = (Ideal.quotientMulEquivQuotientProd a b hab
        (Ideal.Quotient.mk (a * b) _)).2
      rw [Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
      simp only [map_add, map_mul, hBzero, zero_mul, zero_add,
        firstTransferResidueLift_spec, IsUnit.unit_spec]
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [he]

theorem first_transfer_gauss_crt_paired_value (c : ArithmeticContext)
    {a b : Ideal O} (ha : Outside c.S a) (hb : Outside c.S b) (hab : IsRelPrime a b)
    (u v : O) :
    firstTransferPairedResidueCharacter c ha hb hab
      (Ideal.Quotient.mk (a * b)
        (primaryGenerator b * u + primaryGenerator a * v)) =
      (sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a))) *
        (sexticSymbol a u * star (sexticSymbol b v)) := by
  have hAzero : Ideal.Quotient.mk a (primaryGenerator a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : primaryGenerator a ∈ principal (primaryGenerator a) :=
      Ideal.mem_span_singleton_self _
    rw [(first_transfer_primaryGenerator_spec_and_primary_outside c ha).1] at hm
    exact hm
  have hBzero : Ideal.Quotient.mk b (primaryGenerator b) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : primaryGenerator b ∈ principal (primaryGenerator b) :=
      Ideal.mem_span_singleton_self _
    rw [(first_transfer_primaryGenerator_spec_and_primary_outside c hb).1] at hm
    exact hm
  have hleft : sexticSymbol a (primaryGenerator b * u + primaryGenerator a * v) =
      sexticSymbol a (primaryGenerator b) * sexticSymbol a u := by
    rw [← firstTransferResidueCharacter_apply_mk c ha]
    simp only [map_add, map_mul, hAzero, zero_mul, add_zero,
      firstTransferResidueCharacter_apply_mk]
  have hright : sexticSymbol b (primaryGenerator b * u + primaryGenerator a * v) =
      sexticSymbol b (primaryGenerator a) * sexticSymbol b v := by
    rw [← firstTransferResidueCharacter_apply_mk c hb]
    simp only [map_add, map_mul, hBzero, zero_mul, zero_add,
      firstTransferResidueCharacter_apply_mk]
  rw [firstTransferPairedResidueCharacter_apply_mk, hleft, hright, star_mul]
  ring

/-- Complex conjugation is exactly the frozen negative first power,
including the zero extension at nonunits. -/
theorem first_transfer_gauss_sextic_star_eq_neg_one (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (x : O) :
    star (sexticSymbol n x) = sexticSymbol n x ^ (-1 : ℤ) := by
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1
  rw [← firstTransferResidueCharacter_apply_mk c hn,
    MulChar.star_apply', MulChar.inv_apply_eq_inv', zpow_neg_one]

end QRHShort
