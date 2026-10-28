import QRHShort.ArithmeticReduction
import QRHShort.ArithmeticRaySquareClass

/-!
An exact reduction of `RayReciprocityStatement` following Appendix A.1.

The finite square-class calculation is proved in `ArithmeticRaySquareClass`.
Here the context is constructed with modulus `nu.modulus * (12)`, preserving
the given excluded set.  Five explicit arithmetic propositions remain:
primary square-class descent, the cubic supplementary character at 4, the
quadratic Gauss evaluation, sextic reciprocity, and the supplementary law at
-1.  They are parameters of the assembly, never axioms or admitted theorems.

The two descent propositions apply to every context whose modulus is divisible
by (12).  This gives the two characters on the SAME context, without assuming
that independently chosen existential moduli or witnesses coincide.
-/

noncomputable section
set_option autoImplicit false
open Classical

namespace QRHShort.ArithmeticProof.Ray

/-- Representatives of the four square classes modulo 4. -/
def representative (x : LocalClass) : O :=
  (-1 : O) ^ x.toAdd.1.val * (1 + 2 * omega) ^ x.toAdd.2.val

/-- An actual congruence modulo (4), with a unit square as the multiplier. -/
def HasLocalClass (z : O) (x : LocalClass) : Prop :=
  ∃ u : (O ⧸ principal 4)ˣ,
    Ideal.Quotient.mk (principal 4) z =
      Ideal.Quotient.mk (principal 4) (representative x) * (u : O ⧸ principal 4) ^ 2

theorem representative_hasLocalClass (x : LocalClass) :
    HasLocalClass (representative x) x := by
  exact ⟨1, by simp⟩

theorem principal_twelve :
    principal (12 : O) = (principal 2 * principal 2) * principal 3 := by
  simp only [principal, Ideal.span_singleton_mul_span_singleton]
  norm_num

/-- Enlarging the modulus introduces only the already excluded primes 2 and 3. -/
def enlargedContext (ν : HeckeCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P)
    (h2 : ∀ P : Ideal O, Prime P → P ∣ principal 2 → P ∈ S)
    (h3 : ∀ P : Ideal O, Prime P → P ∣ principal 3 → P ∈ S)
    (hν : ∀ P : Ideal O, Prime P → P ∣ ν.modulus → P ∈ S) :
    ArithmeticContext where
  nu := ν
  S := S
  prime_S := hS
  above_two := h2
  above_three := h3
  conductor_S := hν
  rayModulus := ν.modulus * principal 12
  rayModulus_ne_bot := by
    apply mul_ne_zero ν.modulus_ne_bot
    exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  ray_supported := by
    intro P hP hdiv
    rcases hP.dvd_mul.mp hdiv with h | h
    · exact hν P hP h
    rw [principal_twelve] at h
    rcases hP.dvd_mul.mp h with h | h
    · rcases hP.dvd_mul.mp h with h | h
      · exact h2 P hP h
      · exact h2 P hP h
    · exact h3 P hP h
  nu_factors := Ideal.mul_le_left

theorem exists_enlargedContext (ν : HeckeCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P)
    (h2 : ∀ P : Ideal O, Prime P → P ∣ principal 2 → P ∈ S)
    (h3 : ∀ P : Ideal O, Prime P → P ∣ principal 3 → P ∈ S)
    (hν : ∀ P : Ideal O, Prime P → P ∣ ν.modulus → P ∈ S) :
    ∃ c : ArithmeticContext, c.nu = ν ∧ c.S = S ∧ c.rayModulus ≤ principal 12 := by
  exact ⟨enlargedContext ν S hS h2 h3 hν, rfl, rfl, Ideal.mul_le_right⟩

/-- Child 1: primary normalization descends modulo 12, followed by the
four-element square-class quotient modulo 4.  No Gauss sum is assumed. -/
def PrimarySquareClassRayStatement : Prop :=
  ∀ c : ArithmeticContext, c.rayModulus ≤ principal 12 →
    ∃ k : RayClass c →* LocalClass,
      ∀ a : Ideal O, Outside c.S a →
        HasLocalClass (primaryGenerator a) (k (idealClass c a))

/-- Child 2: the cubic supplementary law gives the conjugate symbol at 4 as
a ray character.  Its order divides 3 on the entire ray group. -/
def CubicFourRayCharacterStatement : Prop :=
  ∀ c : ArithmeticContext, c.rayModulus ≤ principal 12 →
    ∃ t : RayClass c →* ℂ,
      (∀ x, t x ^ (3 : ℕ) = 1) ∧
      ∀ a : Ideal O, Outside c.S a →
        t (idealClass c a) = star (sexticSymbol a 4)

/-- Child 3: the normalized quadratic Gauss sum is the explicit four-value
function, including its extension from primes to squarefree ideals. -/
def QuadraticGaussSquareClassStatement : Prop :=
  ∀ (c : ArithmeticContext) (n : Ideal O), SquarefreeOutside c.S n →
    ∀ x : LocalClass, HasLocalClass (primaryGenerator n) x → gauss 3 n = gamma x

/-- Child 4: the actual sextic symbols have the explicit local polar factor.
This is an identity for all coprime outside ideals, including prime powers. -/
def SexticSquareClassReciprocityStatement : Prop :=
  ∀ (c : ArithmeticContext) (a b : Ideal O),
    Outside c.S a → Outside c.S b → IsRelPrime a b →
    ∀ x y : LocalClass,
      HasLocalClass (primaryGenerator a) x →
      HasLocalClass (primaryGenerator b) y →
      sexticSymbol b (primaryGenerator a) =
        correction x y * sexticSymbol a (primaryGenerator b)

/-- Child 5: the supplementary law at -1 is the diagonal of the same polar
form.  This is separate from the coprime-pair reciprocity statement. -/
def SexticMinusOneSquareClassStatement : Prop :=
  ∀ (c : ArithmeticContext) (a : Ideal O), Outside c.S a →
    ∀ x : LocalClass, HasLocalClass (primaryGenerator a) x →
      sexticSymbol a (-1) = correction x x

/-- Assemble the frozen nine ray laws from concrete coordinates and three
arithmetic identities.  All group laws and norm statements are proved. -/
theorem laws_of_local_inputs (c : ArithmeticContext)
    (k : RayClass c →* LocalClass) (t : RayClass c →* ℂ)
    (hk : ∀ a : Ideal O, Outside c.S a →
      HasLocalClass (primaryGenerator a) (k (idealClass c a)))
    (ht : ∀ x, t x ^ (3 : ℕ) = 1)
    (htvalue : ∀ a : Ideal O, Outside c.S a →
      t (idealClass c a) = star (sexticSymbol a 4))
    (hgauss : QuadraticGaussSquareClassStatement)
    (hrecip : SexticSquareClassReciprocityStatement)
    (hminus : SexticMinusOneSquareClassStatement) :
    RayReciprocityLaws c (twistedGamma k t) (fun x y => correction (k x) (k y)) where
  norm_G := norm_twistedGamma k t ht
  sign_R := fun x y => correction_sign (k x) (k y)
  symm_R := fun x y => correction_symm (k x) (k y)
  mul_left_R := by
    intro x y z
    rw [map_mul, correction_mul_left]
  mul_right_R := by
    intro x y z
    rw [map_mul, correction_mul_right]
  mul_G := twistedGamma_mul k t
  reciprocity := by
    intro a b ha hb hab
    exact hrecip c a b ha hb hab _ _ (hk a ha) (hk b hb)
  quadratic := by
    intro n hn
    rw [twistedGamma, htvalue n hn.1, hgauss c n hn _ (hk n hn.1)]
  diagonal := by
    intro a ha
    exact (hminus c a ha _ (hk a ha)).symm

/-- Exact original target, with the five unresolved arithmetic leaves explicit.
There is no dependency on `Manuscript.arithmetic` or on the parent statement. -/
theorem rayReciprocity_of_local_inputs
    (hclass : PrimarySquareClassRayStatement)
    (hfour : CubicFourRayCharacterStatement)
    (hgauss : QuadraticGaussSquareClassStatement)
    (hrecip : SexticSquareClassReciprocityStatement)
    (hminus : SexticMinusOneSquareClassStatement) : RayReciprocityStatement := by
  intro ν S hS h2 h3 hν
  obtain ⟨c, hcν, hcS, hc12⟩ := exists_enlargedContext ν S hS h2 h3 hν
  obtain ⟨k, hk⟩ := hclass c hc12
  obtain ⟨t, ht, htvalue⟩ := hfour c hc12
  exact ⟨c, hcν, hcS, twistedGamma k t, (fun x y => correction (k x) (k y)),
    laws_of_local_inputs c k t hk ht htvalue hgauss hrecip hminus⟩

end QRHShort.ArithmeticProof.Ray

#print axioms QRHShort.ArithmeticProof.Ray.exists_enlargedContext
#print axioms QRHShort.ArithmeticProof.Ray.laws_of_local_inputs
#print axioms QRHShort.ArithmeticProof.Ray.rayReciprocity_of_local_inputs

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations : Array (Name × ConstantInfo) := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof.Ray).isPrefixOf name then entries.push (name, info)
      else entries) #[]
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Ray reciprocity reduction: forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Ray reciprocity reduction declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No ray reciprocity declarations audited"
  logInfo m!"RAY_RECIPROCITY_AUDIT declarations={checked} forbidden=0 pending_children=5"
