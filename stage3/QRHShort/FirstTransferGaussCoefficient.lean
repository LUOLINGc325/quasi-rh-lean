import QRHShort.FirstTransferResidueCharacter
import QRHShort.FirstTransferMultiplicityBoundsFiber
import QRHShort.ArithmeticStatements
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
The arithmetic simplification of the explicit two-factor Gauss expression.
Its identification with the Gauss sum of the primitive paired character is a
separate CRT obligation. All symbols here are the frozen literal definitions.
-/

noncomputable section
open Classical

namespace QRHShort

theorem first_transfer_norm_alpha_eq_one (c : ArithmeticContext) {n : Ideal O}
    (hn : Outside c.S n) : ‖alpha n‖ = 1 := by
  have h : embedding (primaryGenerator n) ≠ 0 :=
    fun hz => first_transfer_primaryGenerator_ne_zero c hn (embedding_eq_zero.mp hz)
  simp only [alpha, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]

theorem first_transfer_mobius_sq {n : Ideal O} (hn : Squarefree n) :
    (mobius n : ℂ) ^ 2 = 1 := by
  simp [mobius, hn.moebius_eq, ← pow_mul, Nat.mul_comm]

theorem first_transfer_norm_mobius_eq_one {n : Ideal O} (hn : Squarefree n) :
    ‖(mobius n : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (first_transfer_mobius_sq hn) (by decide)

theorem first_transfer_norm_sexticSymbol_of_unit (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk n z)) : ‖sexticSymbol n z‖ = 1 := by
  letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn.1
  letI : Fintype (O ⧸ n) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hz
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity
    ((firstTransferResidueCharacter c hn).apply_mem_rootsOfUnity u)
  simpa only [MulChar.coe_equivToUnitHom, hu,
    firstTransferResidueCharacter_apply_mk] using h

theorem first_transfer_primaryGenerator_unit_of_isRelPrime (c : ArithmeticContext)
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
  rw [← first_transfer_primaryGenerator_spec_outside c hb] at hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hy
  have h := congrArg (Ideal.Quotient.mk a) hxy
  simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    zero_add, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk a t, h⟩

theorem first_transfer_norm_gauss_two (c : ArithmeticContext)
    (hc : ArithmeticRelations c) {n : Ideal O} (hn : SquarefreeOutside c.S n) :
    ‖gauss 2 n‖ = 1 := by
  obtain ⟨G, R, _, _, _, _, _, _, _, hgauss, _, _⟩ := hc
  have h := congrArg norm (hgauss n hn).1
  rw [norm_pow, norm_mul, first_transfer_norm_mobius_eq_one hn.2,
    first_transfer_norm_alpha_eq_one c hn.1, mul_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    (h.trans (one_pow 3).symm)

/-- The explicit expression that the separate CRT Gauss calculation must
identify with the normalized Gauss sum of the paired primitive character. -/
def firstTransferPairedGaussFactor (a b : Ideal O) : ℂ :=
  sexticSymbol a (primaryGenerator b) * star (sexticSymbol b (primaryGenerator a)) *
    gauss 1 a * gauss (-1) b

theorem first_transfer_coefficient_pairedGaussFactor (c : ArithmeticContext)
    (hc : ArithmeticRelations c) (ξ : RayCharacter c) {a b : Ideal O}
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    coefficient ξ.val a * star (coefficient ξ.val b) * firstTransferPairedGaussFactor a b =
      (mobius a : ℂ) * (mobius b : ℂ) *
        (rayValue ξ.val a * star (rayValue ξ.val b)) *
          reciprocityG c hc (idealClass c a * (idealClass c b)⁻¹) := by
  obtain ⟨R, hG, hsign, hsym, _, _, _, hrec, hgauss, _, hquot⟩ := Classical.choose_spec hc
  let G := reciprocityG c hc
  have hcross : sexticSymbol a (primaryGenerator b) *
      star (sexticSymbol b (primaryGenerator a)) = R (idealClass c a) (idealClass c b) := by
    rw [hrec a b ha.1 hb.1 hab, star_mul]
    have hn : ‖sexticSymbol a (primaryGenerator b)‖ = 1 :=
      first_transfer_norm_sexticSymbol_of_unit c ha.1 _
        (first_transfer_primaryGenerator_unit_of_isRelPrime c ha.1 hb.1 hab)
    have hunit : sexticSymbol a (primaryGenerator b) *
        star (sexticSymbol a (primaryGenerator b)) = 1 := by
      simpa only [starRingEnd_apply, hn, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (sexticSymbol a (primaryGenerator b))
    rcases hsign (idealClass c a) (idealClass c b) with h | h <;>
      simp only [h, star_one, star_neg, one_mul, mul_one, mul_neg] <;> simpa using hunit
  have hα : star (alpha b) * alpha b = 1 := by
    simpa only [starRingEnd_apply, first_transfer_norm_alpha_eq_one c hb.1,
      one_pow, Complex.ofReal_one] using Complex.conj_mul' (alpha b)
  have hg₂ : gauss 2 b * star (gauss 2 b) = 1 := by
    simpa only [starRingEnd_apply, first_transfer_norm_gauss_two c hc hb,
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
          first_transfer_mobius_sq hb.2, one_mul]
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
  unfold coefficient firstTransferPairedGaussFactor
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

end QRHShort
