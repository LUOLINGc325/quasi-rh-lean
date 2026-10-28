import QRHShort.MainStatements
import QRHShort.HeckeMultiplicative
import QRHShort.EisensteinBasis
import QRHShort.NormLiftContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The quadratic base-change step in paper2.tex:759--772, for the actual
Mathlib Dirichlet L-function and the actual ideal Hecke L-function.

The norm lift keeps the modulus `(N)` and its imprimitive Euler factors.
The twist keeps level `lcm N 3`, rather than replacing it by its primitive
character. With these conventions the base-change identity is exact; no
unmentioned Euler factors occur. We exclude `s = 1`, where either chosen
continuation may have an arbitrary totalized value at a pole.

The norm character is constructed by
computing the determinant norm in the integral basis `1, omega`. The final implication
from Hecke zero-freeness to Dirichlet zero-freeness is proved, using Mathlib's
already proved Dirichlet nonvanishing theorem at 1.
-/

noncomputable section
open Classical

namespace QRHShort

/-- The nontrivial quadratic Dirichlet character modulo 3, with its actual
values on the three residue classes. -/
private def chiMinusThreeValue (a : ZMod 3) : ℂ :=
  if a = 1 then 1 else if a = 2 then -1 else 0

private theorem chiMinusThreeValue_eq_cached (a : ZMod 3) :
    chiMinusThreeValue a = OAI.ShortDraftHeckeBridge.chiMinusThree a := by
  fin_cases a
  · change chiMinusThreeValue (0 : ZMod 3) =
      OAI.ShortDraftHeckeBridge.chiMinusThree (0 : ZMod 3)
    have h0 : chiMinusThreeValue (0 : ZMod 3) = 0 := by
      have h02 : (0 : ZMod 3) ≠ 2 := by decide
      norm_num [chiMinusThreeValue, h02]
    have hb : OAI.ShortDraftHeckeBridge.chiMinusThree (0 : ZMod 3) = 0 :=
      OAI.ShortDraftHeckeBridge.chiMinusThree_mod_zero 0 (by decide)
    exact h0.trans hb.symm
  · change chiMinusThreeValue (1 : ZMod 3) =
      OAI.ShortDraftHeckeBridge.chiMinusThree (1 : ZMod 3)
    have h1 : chiMinusThreeValue (1 : ZMod 3) = 1 := by
      norm_num [chiMinusThreeValue]
    have hb : OAI.ShortDraftHeckeBridge.chiMinusThree (1 : ZMod 3) = 1 :=
      OAI.ShortDraftHeckeBridge.chiMinusThree_mod_one 1 (by decide)
    exact h1.trans hb.symm
  · change chiMinusThreeValue (2 : ZMod 3) =
      OAI.ShortDraftHeckeBridge.chiMinusThree (2 : ZMod 3)
    have h21 : (2 : ZMod 3) ≠ 1 := by decide
    have h2 : chiMinusThreeValue (2 : ZMod 3) = -1 := by
      norm_num [chiMinusThreeValue, h21]
    have hb : OAI.ShortDraftHeckeBridge.chiMinusThree (2 : ZMod 3) = -1 :=
      OAI.ShortDraftHeckeBridge.chiMinusThree_mod_two 2 (by decide)
    exact h2.trans hb.symm

def chiMinusThree : DirichletCharacter ℂ 3 where
  toFun a := if a = 1 then 1 else if a = 2 then -1 else 0
  map_one' := by
    change chiMinusThreeValue (1 : ZMod 3) = 1
    norm_num [chiMinusThreeValue]
  map_mul' := by
    intro a b
    change chiMinusThreeValue (a * b) = chiMinusThreeValue a * chiMinusThreeValue b
    rw [chiMinusThreeValue_eq_cached, chiMinusThreeValue_eq_cached,
      chiMinusThreeValue_eq_cached]
    exact map_mul _ _ _
  map_nonunit' := by
    intro a ha
    change chiMinusThreeValue a = 0
    rw [chiMinusThreeValue_eq_cached]
    exact OAI.ShortDraftHeckeBridge.chiMinusThree.map_nonunit' a ha

@[simp] theorem chiMinusThree_zero : chiMinusThree 0 = 0 := by
  change chiMinusThreeValue (0 : ZMod 3) = 0
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  norm_num [chiMinusThreeValue, h02]

@[simp] theorem chiMinusThree_one : chiMinusThree 1 = 1 := by
  change chiMinusThreeValue (1 : ZMod 3) = 1
  norm_num [chiMinusThreeValue]

@[simp] theorem chiMinusThree_two : chiMinusThree 2 = -1 := by
  change chiMinusThreeValue (2 : ZMod 3) = -1
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  norm_num [chiMinusThreeValue, h21]

theorem chiMinusThree_ne_one : chiMinusThree ≠ 1 := by
  intro h
  have hvalue := DFunLike.congr_fun h (2 : ZMod 3)
  have hu : IsUnit (2 : ZMod 3) := isUnit_iff_ne_zero.mpr (by decide)
  rw [chiMinusThree_two, MulChar.one_apply hu] at hvalue
  norm_num at hvalue

private theorem chiMinusThree_eq_cached :
    chiMinusThree = OAI.ShortDraftHeckeBridge.chiMinusThree := by
  ext x
  change chiMinusThreeValue x = OAI.ShortDraftHeckeBridge.chiMinusThree x
  exact chiMinusThreeValue_eq_cached x

/-- The ideal modulus `(N)` is retained, including for imprimitive characters. -/
def normLiftModulus (N : ℕ) : Ideal O := principal (N : O)

theorem normLiftModulus_ne_bot (N : ℕ) [NeZero N] : normLiftModulus N ≠ ⊥ := by
  intro h
  have hN : (N : O) = 0 := Ideal.span_singleton_eq_bot.mp h
  have hN' : N = 0 := by exact_mod_cast hN
  exact NeZero.ne N hN'

private theorem eisenstein_norm_mod_congr (N : ℕ) {a b : O}
    (h : Ideal.Quotient.mk (normLiftModulus N) a =
      Ideal.Quotient.mk (normLiftModulus N) b) :
    (Algebra.norm ℤ a : ZMod N) = (Algebra.norm ℤ b : ZMod N) := by
  have hmem : a - b ∈ principal (N : O) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have hcoord (i : Fin 2) : (eisensteinBasis.repr a i : ZMod N) =
      (eisensteinBasis.repr b i : ZMod N) := by
    have hmul : (N : O) * c = (N : ℤ) • c := by simp [Algebra.smul_def]
    have hh : eisensteinBasis.repr a i - eisensteinBasis.repr b i =
        (N : ℤ) * eisensteinBasis.repr c i := by
      simpa only [hmul, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] using
        congrArg (fun z : O => eisensteinBasis.repr z i) hc
    have hh' := congrArg (fun z : ℤ => (z : ZMod N)) hh
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul] at hh'
    exact sub_eq_zero.mp hh'
  rw [eisenstein_norm, eisenstein_norm]
  push_cast
  all_goals first | rw [hcoord 0, hcoord 1] | skip

private def eisensteinNormMod (N : ℕ) (x : O ⧸ normLiftModulus N) : ZMod N :=
  (Algebra.norm ℤ (Quotient.out x) : ZMod N)

private theorem eisensteinNormMod_mk (N : ℕ) (a : O) :
    eisensteinNormMod N (Ideal.Quotient.mk (normLiftModulus N) a) =
      (Algebra.norm ℤ a : ZMod N) :=
  eisenstein_norm_mod_congr N (Ideal.Quotient.mk_out _)

private def eisensteinNormModHom (N : ℕ) : (O ⧸ normLiftModulus N) →* ZMod N where
  toFun := eisensteinNormMod N
  map_one' := by
    change eisensteinNormMod N (Ideal.Quotient.mk (normLiftModulus N) 1) = 1
    rw [eisensteinNormMod_mk, map_one, Int.cast_one]
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, eisensteinNormMod_mk, eisensteinNormMod_mk, eisensteinNormMod_mk,
      map_mul, Int.cast_mul]

private theorem intCast_quotient_eq_of_zmod (N : ℕ) {a b : ℤ}
    (h : (a : ZMod N) = (b : ZMod N)) :
    (a : O ⧸ normLiftModulus N) = (b : O ⧸ normLiftModulus N) := by
  have hd : (N : ℤ) ∣ a - b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
    simpa only [Int.cast_sub] using sub_eq_zero.mpr h)
  obtain ⟨c, hc⟩ := hd
  have hN : (N : O ⧸ normLiftModulus N) = 0 := by
    change Ideal.Quotient.mk (normLiftModulus N) (N : O) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  apply sub_eq_zero.mp
  rw [← Int.cast_sub, hc, Int.cast_mul, Int.cast_natCast, hN, zero_mul]

private theorem eisensteinNormMod_reflects_units (N : ℕ)
    (x : O ⧸ normLiftModulus N) (hx : IsUnit (eisensteinNormModHom N x)) : IsUnit x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  let r := eisensteinBasis.repr a 0
  let t := eisensteinBasis.repr a 1
  let ac : O := ((r - t : ℤ) : O) - (t : O) * omega
  have hprod : a * ac = (Algebra.norm ℤ a : O) := by
    calc
      a * ac = ((r : O) + (t : O) * omega) * ac :=
        congrArg (fun z : O => z * ac) (eisenstein_coords a)
      _ = (r : O) ^ 2 - (r : O) * (t : O) + (t : O) ^ 2 -
          (t : O) ^ 2 * (omega ^ 2 + omega + 1) := by
        dsimp [ac]
        push_cast
        ring
      _ = ((r ^ 2 - r * t + t ^ 2 : ℤ) : O) := by
        rw [omega_sq_add_omega_add_one]
        push_cast
        ring
      _ = (Algebra.norm ℤ a : O) := by rw [eisenstein_norm]
  rcases hx with ⟨u, hu⟩
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective (↑(u⁻¹) : ZMod N)
  have hz : ((Algebra.norm ℤ a * v : ℤ) : ZMod N) = 1 := by
    rw [Int.cast_mul, hv]
    change (Algebra.norm ℤ a : ZMod N) * ↑(u⁻¹) = 1
    rw [← eisensteinNormMod_mk N a]
    change eisensteinNormModHom N (Ideal.Quotient.mk (normLiftModulus N) a) * ↑(u⁻¹) = 1
    rw [← hu]
    exact u.val_inv
  have hq := intCast_quotient_eq_of_zmod N (a := Algebra.norm ℤ a * v) (b := 1) (by
    simpa only [Int.cast_one] using hz)
  have hnunit : IsUnit (Algebra.norm ℤ a : O ⧸ normLiftModulus N) :=
    IsUnit.of_mul_eq_one (v : O ⧸ normLiftModulus N) (by
      simpa only [Int.cast_mul, Int.cast_one] using hq)
  apply isUnit_of_mul_isUnit_left (y := Ideal.Quotient.mk (normLiftModulus N) ac)
  simpa only [← map_mul, hprod, map_intCast] using hnunit

/-- The actual absolute-norm character descends modulo `(N)` and vanishes
on nonunits. This is an arithmetic construction, independent of L-functions. -/
theorem exists_normLiftResidue {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    ∃ ψ : MulChar (O ⧸ normLiftModulus N) ℂ,
      ∀ a : O, ψ (Ideal.Quotient.mk (normLiftModulus N) a) =
        χ (((principal a).absNorm : ℕ) : ZMod N) := by
  let f := eisensteinNormModHom N
  refine ⟨{ toMonoidHom := χ.toMonoidHom.comp f
            map_nonunit' := ?_ }, ?_⟩
  · intro x hx
    exact χ.map_nonunit (fun h => hx (eisensteinNormMod_reflects_units N x h))
  · intro a
    change χ (eisensteinNormMod N (Ideal.Quotient.mk (normLiftModulus N) a)) = _
    rw [eisensteinNormMod_mk]
    have h := congrArg (fun z : ℤ => (z : ZMod N)) (principal_absNorm_int a)
    simpa only [Int.cast_natCast] using congrArg χ h.symm

def normLiftResidue {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    MulChar (O ⧸ normLiftModulus N) ℂ :=
  Classical.choose (exists_normLiftResidue χ)

theorem normLiftResidue_spec {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a : O) :
    normLiftResidue χ (Ideal.Quotient.mk (normLiftModulus N) a) =
      χ (((principal a).absNorm : ℕ) : ZMod N) :=
  Classical.choose_spec (exists_normLiftResidue χ) a

/-- The finite-order, trivial-infinity-type Hecke character `χ ∘ N`.
The value on an element is specified by its actual principal-ideal norm. -/
def normLift {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : HeckeCharacter where
  modulus := normLiftModulus N
  modulus_ne_bot := normLiftModulus_ne_bot N
  residue := normLiftResidue χ
  unit_trivial := by
    intro u
    rw [normLiftResidue_spec]
    have hu : principal (u : O) = ⊤ := Ideal.span_singleton_eq_top.mpr u.isUnit
    rw [hu, Ideal.absNorm_top, Nat.cast_one, map_one]

@[simp] theorem normLift_onElement {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a : O) :
    (normLift χ).onElement a = χ (((principal a).absNorm : ℕ) : ZMod N) :=
  normLiftResidue_spec χ a

/-- At nonzero ideals the coefficients are exactly the norm-lift values.
The zero ideal is excluded, since the Hecke series assigns it zero even at
level 1, where the residue ring itself is the zero ring. -/
theorem normLift_onIdeal {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a : Ideal O) (ha : a ≠ ⊥) :
    (normLift χ).onIdeal a = χ ((a.absNorm : ℕ) : ZMod N) := by
  rw [(normLift χ).onIdeal_of_generator ha (Ideal.span_singleton_generator a),
    normLift_onElement]
  change χ (((Ideal.span {idealGenerator a}).absNorm : ℕ) : ZMod N) = _
  simpa only [idealGenerator, Ideal.span_singleton_generator]

/-- The actual imprimitive twist at common level `lcm N 3`.
Using `primitive_mul` here would require explicit finite Euler corrections. -/
def minusThreeTwist {N : ℕ} (χ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (Nat.lcm N 3) :=
  DirichletCharacter.mul χ chiMinusThree

private instance normLift_neZero_lcm {N : ℕ} [NeZero N] : NeZero (Nat.lcm N 3) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩

/-- Keeping the common imprimitive level preserves the product of the two
native coefficient functions, including integers not coprime to either level. -/
theorem minusThreeTwist_natCast {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (n : ℕ) :
    minusThreeTwist χ (n : ZMod (Nat.lcm N 3)) =
      χ (n : ZMod N) * chiMinusThree (n : ZMod 3) := by
  classical
  change (DirichletCharacter.changeLevel (Nat.dvd_lcm_left N 3) χ)
      (n : ZMod (Nat.lcm N 3)) *
    (DirichletCharacter.changeLevel (Nat.dvd_lcm_right N 3) chiMinusThree)
      (n : ZMod (Nat.lcm N 3)) = _
  by_cases hN : IsUnit (n : ZMod N)
  · by_cases h3 : IsUnit (n : ZMod 3)
    · have hnN := (ZMod.isUnit_iff_coprime n N).mp hN
      have hn3 := (ZMod.isUnit_iff_coprime n 3).mp h3
      have hnl : n.Coprime (Nat.lcm N 3) :=
        (hnN.mul_right hn3).coprime_dvd_right (Nat.lcm_dvd
          (dvd_mul_right N 3) (dvd_mul_left 3 N))
      let u := ZMod.unitOfCoprime n hnl
      have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd χ
        (Nat.dvd_lcm_left N 3) u
      have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd chiMinusThree
        (Nat.dvd_lcm_right N 3) u
      simpa only [u, ZMod.coe_unitOfCoprime, Nat.dvd_lcm_left, Nat.dvd_lcm_right,
        ZMod.cast_natCast] using
        congrArg₂ (fun x y : ℂ => x * y) hχ hψ
    · have hnl : ¬ IsUnit (n : ZMod (Nat.lcm N 3)) := by
        intro h
        apply h3
        exact (ZMod.isUnit_iff_coprime n 3).mpr
          (((ZMod.isUnit_iff_coprime n (Nat.lcm N 3)).mp h).coprime_dvd_right
            (Nat.dvd_lcm_right N 3))
      rw [(DirichletCharacter.changeLevel (Nat.dvd_lcm_right N 3)
        chiMinusThree).map_nonunit hnl, chiMinusThree.map_nonunit h3]
      simp
  · have hnl : ¬ IsUnit (n : ZMod (Nat.lcm N 3)) := by
      intro h
      apply hN
      exact (ZMod.isUnit_iff_coprime n N).mpr
        (((ZMod.isUnit_iff_coprime n (Nat.lcm N 3)).mp h).coprime_dvd_right
          (Nat.dvd_lcm_left N 3))
    rw [(DirichletCharacter.changeLevel (Nat.dvd_lcm_left N 3) χ).map_nonunit hnl,
      χ.map_nonunit hN]
    simp

private theorem prime_mod_three_ne_zero (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hp3 : p ≠ 3) : (p : ZMod 3) ≠ 0 := by
  intro hz
  have hd : 3 ∣ p := (ZMod.natCast_eq_zero_iff p 3).mp hz
  have h : 3 = p := ((Nat.dvd_prime hp.out).mp hd).resolve_left (by decide)
  exact hp3 h.symm

private theorem prime_not_dvd_three (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hp3 : p ≠ 3) : ¬ p ∣ 3 := by
  intro hd
  exact hp3 (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left
    hp.out.ne_one)

private theorem orderOf_prime_mod_three (p : ℕ) [Fact (Nat.Prime p)]
    (hp3 : p ≠ 3) :
    orderOf (p : ZMod 3) = if (p : ZMod 3) = 1 then 1 else 2 := by
  by_cases hp1 : (p : ZMod 3) = 1
  · simp [hp1]
  have hclasses (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hp2 : (p : ZMod 3) = 2 :=
    ((hclasses p).resolve_left (prime_mod_three_ne_zero p hp3)).resolve_left hp1
  rw [if_neg hp1, hp2]
  apply orderOf_eq_prime <;> decide

/-- Actual residue degrees in the quadratic cyclotomic field, including
the unique ramified rational prime. -/
theorem eisenstein_prime_inertiaDegree (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.inertiaDeg ℤ =
      if p = 3 then 1 else if (p : ZMod 3) = 1 then 1 else 2 := by
  by_cases hp3 : p = 3
  · subst p
    simpa using IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 3 K P
  · rw [if_neg hp3, IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K P
      (prime_not_dvd_three p hp3)]
    exact orderOf_prime_mod_three p hp3

theorem eisenstein_prime_ramificationDegree (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ = if p = 3 then 2 else 1 := by
  by_cases hp3 : p = 3
  · subst p
    simpa using IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime 3 K P
  · rw [if_neg hp3]
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P
      (prime_not_dvd_three p hp3)

/-- There are two primes of norm `p` in the split case, one of norm `p²`
in the inert case, and one of norm 3 over 3. -/
theorem eisenstein_primesOver_card (p : ℕ) [Fact (Nat.Prime p)] :
    Fintype.card ((Ideal.span {(p : ℤ)}).primesOver O) =
      if p = 3 then 1 else if (p : ZMod 3) = 1 then 2 else 1 := by
  have hdim : Module.finrank ℤ O = 2 := by
    simpa using Module.finrank_eq_card_basis eisensteinBasis
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (Ideal.span {(p : ℤ)}) O
  have hram (P : (Ideal.span {(p : ℤ)}).primesOver O) :
      P.val.ramificationIdx ℤ = if p = 3 then 2 else 1 :=
    eisenstein_prime_ramificationDegree p P.val
  have hinertia (P : (Ideal.span {(p : ℤ)}).primesOver O) :
      P.val.inertiaDeg ℤ =
        if p = 3 then 1 else if (p : ZMod 3) = 1 then 1 else 2 :=
    eisenstein_prime_inertiaDegree p P.val
  simp_rw [hram, hinertia] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, hdim] at hsum
  by_cases hp3 : p = 3
  · simp only [hp3, if_true, mul_one] at hsum ⊢
    omega
  · by_cases hp1 : (p : ZMod 3) = 1
    · simpa only [if_neg hp3, if_pos hp1, one_mul, mul_one] using hsum
    · simp only [if_neg hp3, if_neg hp1, one_mul] at hsum ⊢
      omega

theorem eisenstein_prime_absNorm (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.absNorm = p ^
      (if p = 3 then 1 else if (p : ZMod 3) = 1 then 1 else 2) := by
  rw [← Ideal.pow_inertiaDeg p P, eisenstein_prime_inertiaDegree p P]

/-- A finite local Euler denominator for the actual norm-lift coefficients.
No infinite Euler product is asserted by this definition. -/
def normLiftPrimeDenominator {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (p : ℕ) [Fact (Nat.Prime p)] (s : ℂ) : ℂ :=
  ∏ P : (Ideal.span {(p : ℤ)}).primesOver O,
    (1 - (normLift χ).onIdeal P.val * (P.val.absNorm : ℂ) ^ (-s))

/-- The exact local splitting identity, including omitted Euler factors at
primes dividing `N`, is proved directly for the two imprimitive characters. -/
theorem normLiftPrimeDenominator_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (p : ℕ) [hp : Fact (Nat.Prime p)] (s : ℂ) :
    normLiftPrimeDenominator χ p s =
      (1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)) *
        (1 - minusThreeTwist χ (p : ZMod (Nat.lcm N 3)) * (p : ℂ) ^ (-s)) := by
  let f : ℕ := if p = 3 then 1 else if (p : ZMod 3) = 1 then 1 else 2
  have hP (P : (Ideal.span {(p : ℤ)}).primesOver O) :
      (normLift χ).onIdeal P.val = χ (p : ZMod N) ^ f := by
    have hbase : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      simpa only [ne_eq, Ideal.span_singleton_eq_bot, Int.natCast_eq_zero] using hp.out.ne_zero
    rw [normLift_onIdeal χ P.val (Ideal.ne_bot_of_mem_primesOver hbase P.property),
      eisenstein_prime_absNorm p P.val, Nat.cast_pow, map_pow]
  have hnorm (P : (Ideal.span {(p : ℤ)}).primesOver O) :
      P.val.absNorm = p ^ f := eisenstein_prime_absNorm p P.val
  have hprod : normLiftPrimeDenominator χ p s =
      (1 - χ (p : ZMod N) ^ f * ((p ^ f : ℕ) : ℂ) ^ (-s)) ^
        Fintype.card ((Ideal.span {(p : ℤ)}).primesOver O) := by
    unfold normLiftPrimeDenominator
    simp_rw [hP, hnorm]
    simp only [Finset.prod_const, Finset.card_univ]
  rw [hprod, eisenstein_primesOver_card, minusThreeTwist_natCast]
  by_cases hp3 : p = 3
  · subst p
    have hchi3 : chiMinusThree (3 : ZMod 3) = 0 := by
      rw [chiMinusThree_eq_cached]
      exact OAI.ShortDraftHeckeBridge.chiMinusThree_mod_zero 3 (by decide)
    simp +decide [f, hchi3]
  · by_cases hp1 : (p : ZMod 3) = 1
    · simp [f, hp3, hp1, pow_two]
    · have hclasses (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
        fin_cases x
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have hp2 : (p : ZMod 3) = 2 :=
        ((hclasses p).resolve_left (prime_mod_three_ne_zero p hp3)).resolve_left hp1
      have hnatpow : (((p ^ 2 : ℕ) : ℂ) ^ (-s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
        rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
      have hpow : ((p : ℂ) ^ 2) ^ (-s) = ((p : ℂ) ^ (-s)) ^ 2 := by
        simpa only [Nat.cast_pow] using hnatpow
      simp +decide [f, hp3, hp1, hp2, chiMinusThree_two, hpow]
      ring

/-- The splitting of rational primes in
`Q(ζ₃)` gives this equality first for `Re s > 1`; analytic uniqueness then
extends it to `ℂ \ {1}`. The prime 3 is ramified: if `3 ∤ N`, its one Hecke
factor is retained by `χ` and omitted by the twist, so the formula remains
exact. Primes dividing `N` are omitted on both sides. -/
theorem normLift_LFunction_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1) :
    HeckeL (normLift χ) s =
      DirichletCharacter.LFunction χ s *
        DirichletCharacter.LFunction (minusThreeTwist χ) s := by
  refine HeckeL_eq_dirichlet_product_of_norm_coefficients χ (minusThreeTwist χ)
    (normLift χ) (normLift_onIdeal χ) ?_ s hs
  intro p
  rw [minusThreeTwist_natCast, chiMinusThree_eq_cached]

/-- The base-change consequence used by the manuscript. At 1 use the
existing Dirichlet theorem directly; no value at a Hecke pole is evaluated. -/
theorem dirichlet_zeroFree_of_hecke_zeroFree
    (hHecke : HeckeZeroFreeStatement) : DirichletZeroFreeStatement := by
  classical
  intro N _ χ s hs hpole
  by_cases hsone : s = 1
  · subst s
    exact DirichletCharacter.LFunction_apply_one_ne_zero
      (hpole.resolve_left (by simp))
  · have hnonzero := hHecke (normLift χ) s hs (.inl hsone)
    rw [normLift_LFunction_eq χ s hsone] at hnonzero
    exact (mul_ne_zero_iff.mp hnonzero).1

theorem main_of_hecke_zeroFree (hHecke : HeckeZeroFreeStatement) : MainStatement :=
  ⟨hHecke, dirichlet_zeroFree_of_hecke_zeroFree hHecke⟩

end QRHShort

#print axioms QRHShort.normLift_LFunction_eq
