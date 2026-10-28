import QRHShort.QuadraticAssembly
import QRHShort.HeckeFamily
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pi.Units

/-!
Primitivity on units for products of the actual residue-field quadratic
characters.  The CRT witness is a unit for the full modulus, so the result
has exactly the strength required by `HeckeCharacter.IsPrimitive`.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem quadraticResidueChar_sq (P : Ideal O) [P.IsMaximal]
    (z : O ⧸ P) (hz : IsUnit z) : quadraticResidueChar P z ^ (2 : ℕ) = 1 := by
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  change ((quadraticChar (O ⧸ P) z : ℤ) : ℂ) ^ (2 : ℕ) = 1
  exact_mod_cast (quadraticChar_sq_one (isUnit_iff_ne_zero.mp hz))

theorem quadraticResidueChar_exists_neg_one (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    ∃ u : (O ⧸ P)ˣ, quadraticResidueChar P (u : O ⧸ P) = -1 := by
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one' hodd
  refine ⟨u, ?_⟩
  change ((quadraticChar (O ⧸ P) (u : O ⧸ P) : ℤ) : ℂ) = -1
  rw [hu]
  norm_num

theorem quadraticProduct_eq_iInf {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hpair : Pairwise (Function.onFun IsCoprime P)) :
    Finset.univ.prod P = ⨅ i, P i := by
  have hpair' : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun IsCoprime P) := by
    intro i hi j hj hij
    exact hpair hij
  simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime hpair'

def quadraticProductCRT {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    (O ⧸ Finset.univ.prod P) ≃+* ((i : ι) → O ⧸ P i) :=
  (Ideal.quotEquivOfEq (quadraticProduct_eq_iInf P hpair)).trans
    (Ideal.quotientInfRingEquivPiQuotient P hpair)

@[simp] theorem quadraticProductCRT_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    quadraticProductCRT P hpair (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      fun i => Ideal.Quotient.mk (P i) x := by
  funext i
  simp only [quadraticProductCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

def quadraticPiChar {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : MulChar ((i : ι) → O ⧸ P i) ℂ where
  toFun z := ∏ i, quadraticResidueChar (P i) (z i)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro z hz
    by_contra hprod
    apply hz
    apply Pi.isUnit_iff.mpr
    intro i
    apply (MulChar.apply_ne_zero_iff (χ := quadraticResidueChar (P i))).mp
    intro hi
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hi)

def quadraticProductChar {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hpair : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ Finset.univ.prod P) ℂ where
  toFun z := quadraticPiChar P (quadraticProductCRT P hpair z)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_nonunit' := by
    intro z hz
    apply (quadraticPiChar P).map_nonunit
    intro hu
    apply hz
    simpa using hu.map (quadraticProductCRT P hpair).symm.toRingHom

@[simp] theorem quadraticProductChar_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    quadraticProductChar P hpair (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ i, quadraticResidueChar (P i) (Ideal.Quotient.mk (P i) x) := by
  change quadraticPiChar P
    (quadraticProductCRT P hpair (Ideal.Quotient.mk (Finset.univ.prod P) x)) = _
  rw [quadraticProductCRT_mk]
  rfl

theorem quadraticProductChar_sq {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (z : O ⧸ Finset.univ.prod P) (hz : IsUnit z) :
    quadraticProductChar P hpair z ^ (2 : ℕ) = 1 := by
  change (∏ i, quadraticResidueChar (P i) (quadraticProductCRT P hpair z i)) ^
      (2 : ℕ) = 1
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  exact quadraticResidueChar_sq (P i) _
    ((Pi.isUnit_iff.mp (hz.map (quadraticProductCRT P hpair).toRingHom)) i)

private theorem quadratic_crt_pair (I J : Ideal O) (h : IsCoprime I J)
    (a : O ⧸ I) (b : O ⧸ J) :
    ∃ x : O, Ideal.Quotient.mk I x = a ∧ Ideal.Quotient.mk J x = b := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (a, b))
  have he : e (Ideal.Quotient.mk (I * J) x) = (a, b) := by
    rw [hx, e.apply_symm_apply]
  refine ⟨x, ?_, ?_⟩
  · simpa [e] using congrArg Prod.fst he
  · simpa [e] using congrArg Prod.snd he

/-- A proper reduction of the modulus fails already on its units. -/
theorem quadraticProductChar_primitive_on_units {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (d : Ideal O) (hd : Finset.univ.prod P ≤ d)
    (hf : ∃ ψ : MulChar (O ⧸ d) ℂ, ∀ x : O,
      IsUnit (Ideal.Quotient.mk (Finset.univ.prod P) x) →
      quadraticProductChar P hpair (Ideal.Quotient.mk (Finset.univ.prod P) x) =
        ψ (Ideal.Quotient.mk d x)) : d = Finset.univ.prod P := by
  by_contra hne
  have hnot : ¬ d ≤ Finset.univ.prod P := fun h => hne (le_antisymm h hd)
  have hsome : ∃ i, ¬ d ≤ P i := by
    by_contra h
    push_neg at h
    apply hnot
    rw [quadraticProduct_eq_iInf P hpair]
    exact le_iInf h
  obtain ⟨i, hi⟩ := hsome
  have hcopd : IsCoprime (P i) d := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra htop
    have heq := (inferInstance : (P i).IsMaximal).eq_of_le htop
      (show P i ≤ P i ⊔ d from le_sup_left)
    exact hi (le_sup_right.trans heq.symm.le)
  let J : Ideal O := d * (Finset.univ.erase i).prod P
  have hcop : IsCoprime (P i) J := hcopd.mul_right (IsCoprime.prod_right (by
    intro j hj
    exact hpair (Finset.mem_erase.mp hj).1.symm))
  have hJd : J ≤ d := Ideal.mul_le_left
  have hJP (j : ι) (hj : j ≠ i) : J ≤ P j := by
    calc
      J ≤ (Finset.univ.erase i).prod P := Ideal.mul_le_right
      _ ≤ (Finset.univ.erase i).inf P := Ideal.prod_le_inf
      _ ≤ P j := Finset.inf_le (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  obtain ⟨u, hu⟩ := quadraticResidueChar_exists_neg_one (P i) (hodd i)
  obtain ⟨x, hxi, hxJ⟩ := quadratic_crt_pair (P i) J hcop (u : O ⧸ P i) 1
  have hxmem : x - 1 ∈ J := Ideal.Quotient.eq.mp (by simpa only [map_one] using hxJ)
  have hxd : Ideal.Quotient.mk d x = 1 := by
    simpa only [map_one] using Ideal.Quotient.eq.mpr (hJd hxmem)
  have hxj (j : ι) (hj : j ≠ i) : Ideal.Quotient.mk (P j) x = 1 := by
    simpa only [map_one] using Ideal.Quotient.eq.mpr (hJP j hj hxmem)
  have hxunit : IsUnit (Ideal.Quotient.mk (Finset.univ.prod P) x) := by
    have he : IsUnit (quadraticProductCRT P hpair
        (Ideal.Quotient.mk (Finset.univ.prod P) x)) := by
      rw [quadraticProductCRT_mk]
      apply Pi.isUnit_iff.mpr
      intro j
      by_cases hj : j = i
      · subst j
        rw [hxi]
        exact u.isUnit
      · rw [hxj j hj]
        exact isUnit_one
    exact (MulEquiv.isUnit_map (quadraticProductCRT P hpair)).mp he
  have hxvalue : quadraticProductChar P hpair
      (Ideal.Quotient.mk (Finset.univ.prod P) x) = -1 := by
    rw [quadraticProductChar_mk, Finset.prod_eq_single i]
    · rw [hxi, hu]
    · intro j _ hji
      rw [hxj j hji, map_one]
    · simp
  obtain ⟨ψ, hψ⟩ := hf
  have he := hψ x hxunit
  rw [hxvalue, hxd, map_one] at he
  norm_num at he

/-- Package the concrete product when its unit correction has been checked. -/
def quadraticProductHecke {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hunit : ∀ u : Oˣ,
      (∏ i, quadraticResidueChar (P i) (Ideal.Quotient.mk (P i) (u : O))) = 1) :
    HeckeCharacter where
  modulus := Finset.univ.prod P
  modulus_ne_bot := hne
  residue := quadraticProductChar P hpair
  unit_trivial := by intro u; rw [quadraticProductChar_mk]; exact hunit u

theorem quadraticProductHecke_primitive {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hne : Finset.univ.prod P ≠ ⊥)
    (hunit : ∀ u : Oˣ,
      (∏ i, quadraticResidueChar (P i) (Ideal.Quotient.mk (P i) (u : O))) = 1)
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    (quadraticProductHecke P hpair hne hunit).IsPrimitive := by
  intro d _ hd hf
  exact quadraticProductChar_primitive_on_units P hpair hodd d hd hf

end QRHShort

#print axioms QRHShort.quadraticProductChar_primitive_on_units
#print axioms QRHShort.quadraticProductHecke_primitive
