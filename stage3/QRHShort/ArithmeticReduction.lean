import QRHShort.ArithmeticStatements
import QRHShort.SquarefreeRayDescent
import Mathlib.Tactic.FieldSimp
import Lean.Util.CollectAxioms

/-!
Reduction of the frozen `ArithmeticStatement` to the arithmetic inputs in
paper2.tex, Appendix A.1 (2689--2877). All missing inputs are explicit proposition
parameters, not axioms or admitted theorems. The assembly proves exactly the
original statement; it does not prove any of the five input propositions.

The elementary primary-generator prerequisites are imported from the verified
ray-descent module. No manuscript endpoint is imported, so the dependency graph
does not loop through `Manuscript.arithmetic`.
-/

noncomputable section
open Classical

namespace QRHShort.ArithmeticProof
open SquarefreeReflection.RayValuePrerequisites

theorem outside_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) : Outside c.S (a * b) := by
  refine ⟨fun h => (Ideal.mul_eq_bot.mp h).elim ha.1 hb.1, ?_⟩
  intro P hP hdiv
  exact ((c.prime_S P hP).dvd_mul.mp hdiv).elim (ha.2 P hP) (hb.2 P hP)

theorem primary_mul {a b : O} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  apply (isPrimary_iff_three_dvd _).mpr
  have h := dvd_add (dvd_mul_of_dvd_left ((isPrimary_iff_three_dvd a).mp ha) b)
    ((isPrimary_iff_three_dvd b).mp hb)
  convert h using 1; ring

theorem primary_unit_eq_one (u : Oˣ) (hu : IsPrimary (u : O)) : u = 1 := by
  have hthree := (isPrimary_iff_three_dvd (u : O)).mp hu
  have hlambda : (omega - 1) ^ (2 : ℕ) ∣ (3 : O) := by
    refine ⟨-omega ^ (2 : ℕ), ?_⟩
    rw [omega_sub_one_sq]
    calc
      (3 : O) = 3 * omega ^ (3 : ℕ) := by rw [omega_cube, mul_one]
      _ = -3 * omega * -omega ^ (2 : ℕ) := by ring
  have hcong : ∃ n : ℤ, (omega - 1) ^ (2 : ℕ) ∣ ((u : O) - n) :=
    ⟨1, by simpa only [Int.cast_one] using hlambda.trans hthree⟩
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u hcong with h | h
  · exact h
  · exfalso
    have hneg : omega - 1 ∣ (-1 : O) - 1 := by
      simpa only [h, Units.val_neg, Units.val_one] using
        omega_sub_one_dvd_three.trans hthree
    apply omega_sub_one_prime.not_dvd_one
    convert dvd_add omega_sub_one_dvd_three hneg using 1; ring

theorem primary_unique {a b : O} (ha : IsPrimary a) (hb : IsPrimary b)
    (hab : principal a = principal b) : a = b := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  have hup : IsPrimary (u : O) := by
    apply (isPrimary_iff_three_dvd _).mpr
    obtain ⟨x, hx⟩ := (isPrimary_iff_three_dvd a).mp ha
    obtain ⟨y, hy⟩ := (isPrimary_iff_three_dvd b).mp hb
    refine ⟨y - (u : O) * x, ?_⟩
    linear_combination hy - (u : O) * hx + hu
  simpa only [primary_unit_eq_one u hup, Units.val_one, mul_one] using hu

theorem primaryGenerator_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    primaryGenerator (a * b) = primaryGenerator a * primaryGenerator b := by
  have ha' := primaryGenerator_spec_outside c ha
  have hb' := primaryGenerator_spec_outside c hb
  have hab' := primaryGenerator_spec_outside c (outside_mul c ha hb)
  apply primary_unique hab'.2 (primary_mul ha'.2 hb'.2)
  rw [hab'.1]
  change a * b = Ideal.span {primaryGenerator a * primaryGenerator b}
  rw [← Ideal.span_singleton_mul_span_singleton]
  change a * b = principal (primaryGenerator a) * principal (primaryGenerator b)
  rw [ha'.1, hb'.1]

theorem embedding_mul (a b : O) : embedding (a * b) = embedding a * embedding b := by
  simpa only [embeddingHom_apply] using map_mul embeddingHom a b

theorem embedding_ne_zero {z : O} (hz : z ≠ 0) : embedding z ≠ 0 := by
  have hi : Function.Injective embeddingHom := by
    unfold embeddingHom
    split_ifs
    · exact rawEmbedding.toRingHom.injective.comp NumberField.RingOfIntegers.coe_injective
    · exact (starRingEnd ℂ).injective.comp
        (rawEmbedding.toRingHom.injective.comp NumberField.RingOfIntegers.coe_injective)
  simpa only [embeddingHom_apply] using (map_ne_zero_iff embeddingHom hi).mpr hz

theorem alpha_norm (c : ArithmeticContext) {n : Ideal O} (hn : Outside c.S n) :
    ‖alpha n‖ = 1 := by
  have hz : primaryGenerator n ≠ 0 := by
    intro hz
    apply hn.1
    rw [← (primaryGenerator_spec_outside c hn).1, hz]
    simp [principal]
  have he := embedding_ne_zero hz
  rw [alpha, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr he)]

theorem alpha_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) : alpha (a * b) = alpha a * alpha b := by
  simp only [alpha, primaryGenerator_mul c ha hb, embedding_mul,
    norm_mul, Complex.ofReal_mul]
  exact mul_div_mul_comm _ _ _ _

theorem rayValue_mul (c : ArithmeticContext) (χ : HeckeCharacter) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) :
    rayValue χ (a * b) = rayValue χ a * rayValue χ b := by
  simp only [rayValue, HeckeCharacter.onElement, primaryGenerator_mul c ha hb, map_mul]

theorem star_mul_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  calc
    star z * z = (‖z‖ : ℂ) ^ 2 := Complex.conj_mul' z
    _ = 1 := by rw [hz]; norm_num

theorem ne_zero_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem sign_mul_self {z : ℂ} (hz : z = 1 ∨ z = -1) : z * z = 1 := by
  rcases hz with rfl | rfl <;> norm_num

theorem sign_ne_zero {z : ℂ} (hz : z = 1 ∨ z = -1) : z ≠ 0 := by
  rcases hz with rfl | rfl <;> norm_num

/-- The scalar implication giving (convert1), with no assumption on the Mobius value. -/
theorem convert_one {a g₁ g₂ m G : ℂ} (ha : ‖a‖ = 1)
    (h : g₁ * g₂ = m * a * G) : star a * g₂ * g₁ = m * G := by
  calc
    star a * g₂ * g₁ = star a * (g₁ * g₂) := by ring
    _ = star a * (m * a * G) := by rw [h]
    _ = (star a * a) * (m * G) := by ring
    _ = m * G := by rw [star_mul_of_norm_one ha, one_mul]

/-- (convert2) follows without dividing by either Gauss sum or the Mobius value. -/
theorem convert_two {a g₁ g₂ gm m G s : ℂ} (hG : G ≠ 0)
    (hc : star a * g₂ * g₁ = m * G) (hi : g₁ * gm = s) :
    m * gm = s * G⁻¹ * star a * g₂ := by
  calc
    m * gm = G⁻¹ * (m * G) * gm := by field_simp [hG]
    _ = G⁻¹ * (star a * g₂ * g₁) * gm := by rw [hc]
    _ = (g₁ * gm) * G⁻¹ * star a * g₂ := by ring
    _ = s * G⁻¹ * star a * g₂ := by rw [hi]

/-- The common ray functions required in Appendix A.1. The last two fields are
the quadratic evaluation and diagonal supplementary law used in that appendix. -/
structure RayReciprocityLaws (c : ArithmeticContext)
    (G : RayClass c → ℂ) (R : RayClass c → RayClass c → ℂ) : Prop where
  norm_G : ∀ a, ‖G a‖ = 1
  sign_R : ∀ a b, R a b = 1 ∨ R a b = -1
  symm_R : ∀ a b, R a b = R b a
  mul_left_R : ∀ a a' b, R (a * a') b = R a b * R a' b
  mul_right_R : ∀ a b b', R a (b * b') = R a b * R a b'
  mul_G : ∀ a b, G (a * b) = G a * G b * R a b
  reciprocity : ∀ a b : Ideal O, Outside c.S a → Outside c.S b → IsRelPrime a b →
    sexticSymbol b (primaryGenerator a) =
      R (idealClass c a) (idealClass c b) * sexticSymbol a (primaryGenerator b)
  quadratic : ∀ n : Ideal O, SquarefreeOutside c.S n →
    G (idealClass c n) = star (sexticSymbol n 4) * gauss 3 n
  diagonal : ∀ a : Ideal O, Outside c.S a →
    R (idealClass c a) (idealClass c a) = sexticSymbol a (-1)

namespace RayReciprocityLaws
variable {c : ArithmeticContext} {G : RayClass c → ℂ}
  {R : RayClass c → RayClass c → ℂ} (h : RayReciprocityLaws c G R)
include h

theorem R_one_left (b : RayClass c) : R 1 b = 1 := by
  apply mul_right_cancel₀ (sign_ne_zero (h.sign_R 1 b))
  calc
    R 1 b * R 1 b = R (1 * 1) b := (h.mul_left_R 1 1 b).symm
    _ = R 1 b := congrArg (fun x : RayClass c => R x b) (one_mul (1 : RayClass c))
    _ = 1 * R 1 b := (one_mul _).symm

theorem R_one_right (a : RayClass c) : R a 1 = 1 := by
  rw [h.symm_R, h.R_one_left]

theorem R_inv_right (a b : RayClass c) : R a b⁻¹ = R a b := by
  apply mul_left_cancel₀ (sign_ne_zero (h.sign_R a b))
  rw [← h.mul_right_R, mul_inv_cancel, h.R_one_right,
    sign_mul_self (h.sign_R a b)]

theorem G_one : G 1 = 1 := by
  apply mul_right_cancel₀ (ne_zero_of_norm_one (h.norm_G 1))
  calc
    G 1 * G 1 = G 1 * G 1 * R 1 1 := by rw [h.R_one_left, mul_one]
    _ = G (1 * 1) := (h.mul_G 1 1).symm
    _ = G 1 := congrArg G (one_mul (1 : RayClass c))
    _ = 1 * G 1 := (one_mul _).symm

theorem G_inv (a : RayClass c) : G a⁻¹ = R a a * star (G a) := by
  have hp : (G a * G a⁻¹) * R a a = 1 := by
    simpa only [mul_inv_cancel, h.G_one, h.R_inv_right] using (h.mul_G a a⁻¹).symm
  have hp' : G a * G a⁻¹ = R a a := by
    apply mul_right_cancel₀ (sign_ne_zero (h.sign_R a a))
    rw [hp, sign_mul_self (h.sign_R a a)]
  calc
    G a⁻¹ = (star (G a) * G a) * G a⁻¹ := by
      rw [star_mul_of_norm_one (h.norm_G a), one_mul]
    _ = star (G a) * (G a * G a⁻¹) := by ring
    _ = R a a * star (G a) := by rw [hp']; ring

theorem quotient (a b : Ideal O) (ha : Outside c.S a) :
    sexticSymbol a (-1) * star (G (idealClass c a)) * G (idealClass c b) *
      R (idealClass c a) (idealClass c b) =
        G (idealClass c b * (idealClass c a)⁻¹) := by
  rw [h.mul_G, h.G_inv, h.R_inv_right, h.diagonal a ha,
    h.symm_R (idealClass c b) (idealClass c a)]
  ring

theorem symbol_square (a b : Ideal O) (ha : Outside c.S a) (hb : Outside c.S b)
    (hab : IsRelPrime a b) :
    sexticSymbol b (primaryGenerator a) ^ (2 : ℕ) =
      sexticSymbol a (primaryGenerator b) ^ (2 : ℕ) := by
  rw [h.reciprocity a b ha hb hab, mul_pow, pow_two,
    sign_mul_self (h.sign_R _ _), one_mul]

end RayReciprocityLaws

/-- Child 1: simultaneous ray descent, sextic reciprocity and the normalized
quadratic Gauss sum; paper2.tex:2785--2851. The modulus is existential, exactly
as in the frozen statement, and all downstream children work for any context. -/
def RayReciprocityStatement : Prop :=
  ∀ (ν : HeckeCharacter) (S : Finset (Ideal O)),
    (∀ P ∈ S, Prime P) →
    (∀ P : Ideal O, Prime P → P ∣ principal 2 → P ∈ S) →
    (∀ P : Ideal O, Prime P → P ∣ principal 3 → P ∈ S) →
    (∀ P : Ideal O, Prime P → P ∣ ν.modulus → P ∈ S) →
    ∃ c : ArithmeticContext, c.nu = ν ∧ c.S = S ∧
      ∃ G : RayClass c → ℂ, ∃ R : RayClass c → RayClass c → ℂ,
        RayReciprocityLaws c G R

/-- Child 2: the primary cubic Jacobi evaluation and squarefree extension;
paper2.tex:2728--2772. -/
def CubicGaussEvaluationStatement : Prop :=
  ∀ (c : ArithmeticContext) (n : Ideal O), SquarefreeOutside c.S n →
    gauss 2 n ^ (3 : ℕ) = (mobius n : ℂ) * alpha n

/-- Child 3: the mixed sextic/cubic/quadratic Gauss--Jacobi relation before
substituting the cubic evaluation; paper2.tex:2696--2726,2770--2772. -/
def MixedGaussEvaluationStatement : Prop :=
  ∀ (c : ArithmeticContext) (n : Ideal O), SquarefreeOutside c.S n →
    gauss 1 n * gauss 2 n =
      gauss 2 n ^ (3 : ℕ) * (star (sexticSymbol n 4) * gauss 3 n)

/-- Child 4: primitive inverse-character Gauss sums over squarefree ideals;
paper2.tex:2717--2719,2865--2867. -/
def InverseGaussEvaluationStatement : Prop :=
  ∀ (c : ArithmeticContext) (n : Ideal O), SquarefreeOutside c.S n →
    gauss 1 n * gauss (-1) n = sexticSymbol n (-1)

/-- Child 5: the CRT identity before cubic reciprocity; paper2.tex:2774--2780.
Both numerator factors are retained so this child does not depend on Child 1. -/
def CubicGaussCRTStatement : Prop :=
  ∀ (c : ArithmeticContext) (a b : Ideal O),
    SquarefreeOutside c.S a → SquarefreeOutside c.S b → IsRelPrime a b →
    gauss 2 (a * b) = gauss 2 a * gauss 2 b *
      sexticSymbol a (primaryGenerator b) ^ (2 : ℕ) *
      sexticSymbol b (primaryGenerator a) ^ (2 : ℕ)

theorem coefficient_mul_of_crt {c : ArithmeticContext} {G : RayClass c → ℂ}
    {R : RayClass c → RayClass c → ℂ} (h : RayReciprocityLaws c G R)
    (hcrt : CubicGaussCRTStatement) (ξ : RayCharacter c) (a b : Ideal O)
    (ha : SquarefreeOutside c.S a) (hb : SquarefreeOutside c.S b)
    (hab : IsRelPrime a b) :
    coefficient ξ.val (a * b) = coefficient ξ.val a * coefficient ξ.val b *
      sexticSymbol b (primaryGenerator a) ^ (4 : ℕ) := by
  simp only [coefficient, alpha_mul c ha.1 hb.1, star_mul,
    rayValue_mul c ξ.val ha.1 hb.1, hcrt c a b ha hb hab]
  rw [← h.symbol_square a b ha.1 hb.1 hab]
  ring

/-- All six Gauss identities in the frozen conjunction, with only the three
explicit Gauss input statements and the common ray data as hypotheses. -/
theorem gauss_relations_of_evaluations {c : ArithmeticContext} {G : RayClass c → ℂ}
    {R : RayClass c → RayClass c → ℂ} (h : RayReciprocityLaws c G R)
    (hcubic : CubicGaussEvaluationStatement) (hmixed : MixedGaussEvaluationStatement)
    (hinverse : InverseGaussEvaluationStatement) (n : Ideal O)
    (hn : SquarefreeOutside c.S n) :
    gauss 2 n ^ (3 : ℕ) = (mobius n : ℂ) * alpha n ∧
    gauss 1 n * gauss 2 n = (mobius n : ℂ) * alpha n * G (idealClass c n) ∧
    G (idealClass c n) = star (sexticSymbol n 4) * gauss 3 n ∧
    gauss 1 n * gauss (-1) n = sexticSymbol n (-1) ∧
    star (alpha n) * gauss 2 n * gauss 1 n = (mobius n : ℂ) * G (idealClass c n) ∧
    (mobius n : ℂ) * gauss (-1) n =
      sexticSymbol n (-1) * (G (idealClass c n))⁻¹ * star (alpha n) * gauss 2 n := by
  have hm : gauss 1 n * gauss 2 n =
      (mobius n : ℂ) * alpha n * G (idealClass c n) := by
    rw [hmixed c n hn, hcubic c n hn, ← h.quadratic n hn]
  have hconv := convert_one (alpha_norm c hn.1) hm
  exact ⟨hcubic c n hn, hm, h.quadratic n hn, hinverse c n hn, hconv,
    convert_two (ne_zero_of_norm_one (h.norm_G _)) hconv (hinverse c n hn)⟩

theorem arithmeticRelations_of_inputs {c : ArithmeticContext} {G : RayClass c → ℂ}
    {R : RayClass c → RayClass c → ℂ} (h : RayReciprocityLaws c G R)
    (hcubic : CubicGaussEvaluationStatement) (hmixed : MixedGaussEvaluationStatement)
    (hinverse : InverseGaussEvaluationStatement) (hcrt : CubicGaussCRTStatement) :
    ArithmeticRelations c := by
  exact ⟨G, R, h.norm_G, h.sign_R, h.symm_R, h.mul_left_R, h.mul_right_R, h.mul_G,
    h.reciprocity, gauss_relations_of_evaluations h hcubic hmixed hinverse,
    coefficient_mul_of_crt h hcrt, fun a b ha _ => h.quotient a b ha⟩

/-- Exact assembly of `Manuscript.arithmetic` from the five frozen child
statements. This theorem does not assert that those children have been proved. -/
theorem arithmetic_of_inputs (hray : RayReciprocityStatement)
    (hcubic : CubicGaussEvaluationStatement) (hmixed : MixedGaussEvaluationStatement)
    (hinverse : InverseGaussEvaluationStatement) (hcrt : CubicGaussCRTStatement) :
    ArithmeticStatement := by
  intro ν S hS htwo hthree hnu
  obtain ⟨c, hcν, hcS, G, R, h⟩ := hray ν S hS htwo hthree hnu
  exact ⟨c, hcν, hcS, arithmeticRelations_of_inputs h hcubic hmixed hinverse hcrt⟩

end QRHShort.ArithmeticProof

/-! Audit this reduction and its recursive proof dependencies in the same
kernel invocation. The five pending statements remain explicit parameters. -/

#print axioms QRHShort.ArithmeticProof.primaryGenerator_mul
#print axioms QRHShort.ArithmeticProof.alpha_norm
#print axioms QRHShort.ArithmeticProof.RayReciprocityLaws.quotient
#print axioms QRHShort.ArithmeticProof.coefficient_mul_of_crt
#print axioms QRHShort.ArithmeticProof.gauss_relations_of_evaluations
#print axioms QRHShort.ArithmeticProof.arithmetic_of_inputs

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let declarations : Array (Name × ConstantInfo) := env.checked.get.constants.foldStage2
    (fun entries name info =>
      if (`QRHShort.ArithmeticProof).isPrefixOf name then entries.push (name, info)
      else entries) #[]
  let mut checked : Nat := 0
  for (name, info) in declarations do
    match info with
    | .thmInfo _ | .defnInfo _ =>
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Arithmetic reduction depends on forbidden axiom {ax} in {name}"
    | .axiomInfo _ => throwError "Arithmetic reduction declares an axiom: {name}"
    | _ => pure ()
  if checked == 0 then throwError "No arithmetic declarations audited"
  logInfo m!"ARITHMETIC_AUDIT declarations={checked} forbidden=0 pending_children=5"
