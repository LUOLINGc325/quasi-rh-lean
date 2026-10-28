import QRHShort.QuadraticPrimitive
import QRHShort.PrimaryGenerator
import QRHShort.HeckeMultiplicative
import Mathlib.Data.Fintype.BigOperators

/-!
The unit correction for the concrete quadratic residue characters.  A single
quadratic factor at omega - 1 is adjoined exactly when the product takes -1
at -1.  Its value on every primary generator is one.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def quadraticLambdaIdeal : Ideal O := principal (omega - 1)

theorem quadraticLambdaIdeal_ne_bot : quadraticLambdaIdeal ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr omega_sub_one_prime.ne_zero

instance quadraticLambdaIdeal_maximal : quadraticLambdaIdeal.IsMaximal :=
  (Ideal.isPrime_span_singleton_of_prime omega_sub_one_prime).isMaximal
    quadraticLambdaIdeal_ne_bot

theorem quadraticLambda_card : Nat.card (O ⧸ quadraticLambdaIdeal) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [quadraticLambdaIdeal, principal, omega,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
      (by decide)]
  norm_num

theorem quadraticLambda_odd : ringChar (O ⧸ quadraticLambdaIdeal) ≠ 2 := by
  letI : Field (O ⧸ quadraticLambdaIdeal) := Ideal.Quotient.field _
  letI : Fintype (O ⧸ quadraticLambdaIdeal) := Fintype.ofFinite _
  intro h
  have heven := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card, quadraticLambda_card] at heven
  norm_num at heven

theorem quadraticLambda_neg_one :
    quadraticResidueChar quadraticLambdaIdeal
      (Ideal.Quotient.mk quadraticLambdaIdeal (-1 : O)) = -1 := by
  letI : Field (O ⧸ quadraticLambdaIdeal) := Ideal.Quotient.field _
  letI : Fintype (O ⧸ quadraticLambdaIdeal) := Fintype.ofFinite _
  have hv : quadraticChar (O ⧸ quadraticLambdaIdeal) (-1) = -1 := by
    rw [quadraticChar_neg_one quadraticLambda_odd,
      ← Nat.card_eq_fintype_card, quadraticLambda_card]
    rfl
  change ((quadraticChar (O ⧸ quadraticLambdaIdeal)
    (Ideal.Quotient.mk quadraticLambdaIdeal (-1 : O)) : ℤ) : ℂ) = -1
  rw [map_neg, map_one, hv]
  norm_num

theorem quadraticLambda_primary (x : O) (hx : IsPrimary x) :
    quadraticResidueChar quadraticLambdaIdeal
      (Ideal.Quotient.mk quadraticLambdaIdeal x) = 1 := by
  have hm : x - 1 ∈ quadraticLambdaIdeal := Ideal.mem_span_singleton.mpr
    (omega_sub_one_dvd_three.trans ((isPrimary_iff_three_dvd x).mp hx))
  have he : Ideal.Quotient.mk quadraticLambdaIdeal x = 1 := by
    simpa only [map_one] using Ideal.Quotient.eq.mpr hm
  rw [he, map_one]

def quadraticElementProduct {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] : O →* ℂ where
  toFun x := ∏ i, quadraticResidueChar (P i) (Ideal.Quotient.mk (P i) x)
  map_one' := by simp
  map_mul' := by intro x y; simp only [map_mul, Finset.prod_mul_distrib]

@[simp] theorem quadraticElementProduct_apply {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (x : O) :
    quadraticElementProduct P x =
      ∏ i, quadraticResidueChar (P i) (Ideal.Quotient.mk (P i) x) := rfl

theorem quadraticResidueChar_omega (P : Ideal O) [P.IsMaximal] :
    quadraticResidueChar P (Ideal.Quotient.mk P omega) = 1 := by
  have hu : IsUnit omega :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit (by decide)
  have h2 := quadraticResidueChar_sq P (Ideal.Quotient.mk P omega)
    (hu.map (Ideal.Quotient.mk P))
  have h3 : quadraticResidueChar P (Ideal.Quotient.mk P omega) ^ (3 : ℕ) = 1 := by
    rw [← map_pow, ← map_pow, omega_cube, map_one, map_one]
  calc
    quadraticResidueChar P (Ideal.Quotient.mk P omega) =
        quadraticResidueChar P (Ideal.Quotient.mk P omega) ^ (2 : ℕ) *
          quadraticResidueChar P (Ideal.Quotient.mk P omega) := by rw [h2, one_mul]
    _ = quadraticResidueChar P (Ideal.Quotient.mk P omega) ^ (3 : ℕ) := by ring
    _ = 1 := h3

theorem quadraticElementProduct_omega {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] : quadraticElementProduct P omega = 1 := by
  simp only [quadraticElementProduct_apply, quadraticResidueChar_omega, Finset.prod_const_one]

theorem quadraticElementProduct_neg_one_sq {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] :
    quadraticElementProduct P (-1) ^ (2 : ℕ) = 1 := by
  rw [← map_pow, neg_one_sq, map_one]

theorem eisensteinUnit_trivial_of_neg_one_omega (f : O →* ℂ)
    (hneg : f (-1) = 1) (homega : f omega = 1) (u : Oˣ) : f (u : O) = 1 := by
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := IsUnit.unit_spec _
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · subst u
    simp only [Units.val_one, map_one]
  · subst u
    simpa only [Units.val_neg, Units.val_one] using hneg
  · subst u
    change f (η : O) = 1
    rw [hη, homega]
  · subst u
    change f (-(η : O)) = 1
    rw [neg_eq_neg_one_mul, map_mul, hneg, hη, homega, one_mul]
  · subst u
    change f ((η : O) ^ (2 : ℕ)) = 1
    rw [map_pow, hη, homega, one_pow]
  · subst u
    change f (-((η : O) ^ (2 : ℕ))) = 1
    rw [neg_eq_neg_one_mul, map_mul, hneg, map_pow, hη, homega, one_pow, one_mul]

def quadraticAdjoinLambda {ι : Type*} (P : ι → Ideal O) : Option ι → Ideal O
  | none => quadraticLambdaIdeal
  | some i => P i

instance quadraticAdjoinLambda_maximal {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (i : Option ι) :
    (quadraticAdjoinLambda P i).IsMaximal := by
  cases i <;> dsimp [quadraticAdjoinLambda] <;> infer_instance

theorem quadraticAdjoinLambda_pairwise {ι : Type*}
    (P : ι → Ideal O) (hpair : Pairwise (Function.onFun IsCoprime P))
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i)) :
    Pairwise (Function.onFun IsCoprime (quadraticAdjoinLambda P)) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hlambda j
  | some i =>
      cases j with
      | none => exact (hlambda i).symm
      | some j => exact hpair (fun h => hij (congrArg some h))

theorem quadraticAdjoinLambda_prod {ι : Type*} [Fintype ι] (P : ι → Ideal O) :
    Finset.univ.prod (quadraticAdjoinLambda P) =
      quadraticLambdaIdeal * Finset.univ.prod P := by
  simp [Fintype.prod_option, quadraticAdjoinLambda]

theorem quadraticAdjoinLambda_element {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (x : O) :
    quadraticElementProduct (quadraticAdjoinLambda P) x =
      quadraticResidueChar quadraticLambdaIdeal (Ideal.Quotient.mk quadraticLambdaIdeal x) *
        quadraticElementProduct P x := by
  simp only [quadraticElementProduct_apply, Fintype.prod_option, quadraticAdjoinLambda] <;> rfl

/-- The actual unit-corrected product, with no unnecessary lambda factor. -/
def correctedQuadraticHecke {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i)) : HeckeCharacter :=
  if hs : quadraticElementProduct P (-1) = 1 then
    quadraticProductHecke P hpair hne
      (eisensteinUnit_trivial_of_neg_one_omega (quadraticElementProduct P) hs
        (quadraticElementProduct_omega P))
  else
    quadraticProductHecke (quadraticAdjoinLambda P)
      (quadraticAdjoinLambda_pairwise P hpair hlambda)
      (by rw [quadraticAdjoinLambda_prod]; exact mul_ne_zero quadraticLambdaIdeal_ne_bot hne)
      (eisensteinUnit_trivial_of_neg_one_omega
        (quadraticElementProduct (quadraticAdjoinLambda P))
        (by
          have hneg : quadraticElementProduct P (-1) = -1 :=
            (sq_eq_one_iff.mp (quadraticElementProduct_neg_one_sq P)).resolve_left hs
          rw [quadraticAdjoinLambda_element, quadraticLambda_neg_one, hneg]
          norm_num)
        (quadraticElementProduct_omega (quadraticAdjoinLambda P)))

theorem correctedQuadraticHecke_modulus {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i)) :
    (correctedQuadraticHecke P hpair hne hlambda).modulus =
      if quadraticElementProduct P (-1) = 1 then Finset.univ.prod P
      else quadraticLambdaIdeal * Finset.univ.prod P := by
  unfold correctedQuadraticHecke
  split_ifs with hs
  · rfl
  · exact quadraticAdjoinLambda_prod P

theorem correctedQuadraticHecke_onElement {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i)) (x : O) :
    (correctedQuadraticHecke P hpair hne hlambda).onElement x =
      if quadraticElementProduct P (-1) = 1 then quadraticElementProduct P x
      else quadraticElementProduct P x *
        quadraticResidueChar quadraticLambdaIdeal (Ideal.Quotient.mk quadraticLambdaIdeal x) := by
  unfold correctedQuadraticHecke
  split_ifs with hs
  · exact quadraticProductChar_mk P hpair x
  · change quadraticProductChar (quadraticAdjoinLambda P) _
      (Ideal.Quotient.mk _ x) = _
    rw [quadraticProductChar_mk]
    change quadraticElementProduct (quadraticAdjoinLambda P) x = _
    rw [quadraticAdjoinLambda_element, mul_comm]

theorem correctedQuadraticHecke_primary {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i))
    (x : O) (hx : IsPrimary x) :
    (correctedQuadraticHecke P hpair hne hlambda).onElement x = quadraticElementProduct P x := by
  rw [correctedQuadraticHecke_onElement, quadraticLambda_primary x hx, mul_one]
  split_ifs <;> rfl

theorem correctedQuadraticHecke_primitive {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    (correctedQuadraticHecke P hpair hne hlambda).IsPrimitive := by
  unfold correctedQuadraticHecke
  split_ifs
  · exact quadraticProductHecke_primitive _ _ _ _ hodd
  · apply quadraticProductHecke_primitive
    intro i
    cases i with
    | none => exact quadraticLambda_odd
    | some i => exact hodd i

theorem correctedQuadraticHecke_quadratic {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hlambda : ∀ i, IsCoprime quadraticLambdaIdeal (P i))
    (x : O) (hx : IsUnit (Ideal.Quotient.mk
      (correctedQuadraticHecke P hpair hne hlambda).modulus x)) :
    (correctedQuadraticHecke P hpair hne hlambda).onElement x ^ (2 : ℕ) = 1 := by
  by_cases hs : quadraticElementProduct P (-1) = 1
  · rw [correctedQuadraticHecke, dif_pos hs] at hx ⊢
    exact quadraticProductChar_sq _ _ _ hx
  · rw [correctedQuadraticHecke, dif_neg hs] at hx ⊢
    exact quadraticProductChar_sq _ _ _ hx

end QRHShort

#print axioms QRHShort.correctedQuadraticHecke_primitive
#print axioms QRHShort.correctedQuadraticHecke_primary
