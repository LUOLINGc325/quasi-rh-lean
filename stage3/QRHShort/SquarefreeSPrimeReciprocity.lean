import QRHShort.SquarefreeSupplementaryTargets
import QRHShort.SquarefreePrimeSymbol
import QRHShort.HeckeMultiplicative

/-!
Exact reduction of the frozen S-prime-generator target to local reciprocity
at prime denominators. Each local character may initially have its own
S-supported modulus. Prime-factor expansion and a common refinement are
proved here; the two remaining arithmetic statements are explicit parameters.
-/

noncomputable section
set_option autoImplicit false
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.SquarefreeReflection

open RayValuePrerequisites

/-- A single generator needs only a character with the correct PRIME values.
No common modulus or evaluation at composite ideals is assumed here. -/
def SPrimeLocalCharacter (c : ArithmeticContext) (p : c.S) : Prop :=
  ∃ χ : HeckeCharacter,
    (∀ q : Ideal O, Prime q → q ∣ χ.modulus → q ∈ c.S) ∧
    ∀ q : Ideal O, Prime q → Outside c.S q →
      rayValue χ q = sexticAtPrime q (idealGenerator p.val)

/-- The supplementary laws at primes over two or three. -/
def SPrimeRamifiedLocalReciprocityStatement : Prop :=
  ∀ c : ArithmeticContext, ArithmeticRelations c →
    ∀ p : c.S, p.val ∣ principal (6 : O) → SPrimeLocalCharacter c p

/-- The reciprocity law at the other excluded prime generators. -/
def SPrimeOrdinaryLocalReciprocityStatement : Prop :=
  ∀ c : ArithmeticContext, ArithmeticRelations c →
    ∀ p : c.S, ¬ p.val ∣ principal (6 : O) → SPrimeLocalCharacter c p

theorem sPrime_dvd_six_iff (c : ArithmeticContext) (p : c.S) :
    p.val ∣ principal (6 : O) ↔
      p.val ∣ principal (2 : O) ∨ p.val ∣ principal (3 : O) := by
  have hsix : principal (6 : O) = principal (2 : O) * principal (3 : O) := by
    simp only [principal, Ideal.span_singleton_mul_span_singleton]
    norm_num
  rw [hsix]
  exact (c.prime_S p.val p.property).dvd_mul

theorem onIdeal_eq_rayValue_outside (χ : HeckeCharacter) (c : ArithmeticContext)
    {n : Ideal O} (hn : Outside c.S n) : χ.onIdeal n = rayValue χ n :=
  χ.onIdeal_of_generator hn.1 (primaryGenerator_spec_outside c hn).1

/-- Multiplicities in normalizedFactors retain every prime power. -/
theorem rayValue_eq_sexticSymbol_of_prime_values (χ : HeckeCharacter)
    (c : ArithmeticContext) (a : O)
    (hprime : ∀ q : Ideal O, Prime q → Outside c.S q →
      rayValue χ q = sexticAtPrime q a)
    {n : Ideal O} (hn : Outside c.S n) :
    rayValue χ n = sexticSymbol n a := by
  calc
    rayValue χ n = χ.onIdeal n := (onIdeal_eq_rayValue_outside χ c hn).symm
    _ = ((normalizedFactors n).map χ.onIdeal).prod := by
      have h := map_multiset_prod χ.onIdealHom (normalizedFactors n)
      change χ.onIdeal (normalizedFactors n).prod =
        ((normalizedFactors n).map χ.onIdeal).prod at h
      rw [Ideal.prod_normalizedFactors_eq_self hn.1] at h
      exact h
    _ = ((normalizedFactors n).map (fun q => sexticAtPrime q a)).prod := by
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro q hq
      have hqn := outside_of_mem_normalizedFactors hn hq
      exact (onIdeal_eq_rayValue_outside χ c hqn).trans
        (hprime q (prime_of_normalized_factor q hq) hqn)
    _ = sexticSymbol n a := by rw [sexticSymbol, if_neg hn.1]

/-- The product refines all local moduli and the ORIGINAL ray modulus. -/
def sPrimeCommonModulus (c : ArithmeticContext) (χ : c.S → HeckeCharacter) :
    Ideal O := c.rayModulus * ∏ p : c.S, (χ p).modulus

theorem sPrimeCommonModulus_ne_bot (c : ArithmeticContext)
    (χ : c.S → HeckeCharacter) : sPrimeCommonModulus c χ ≠ ⊥ := by
  exact mul_ne_zero c.rayModulus_ne_bot
    (Finset.prod_ne_zero_iff.mpr (fun p _ => (χ p).modulus_ne_bot))

theorem sPrimeCommonModulus_le_ray (c : ArithmeticContext)
    (χ : c.S → HeckeCharacter) : sPrimeCommonModulus c χ ≤ c.rayModulus :=
  Ideal.mul_le_left

theorem sPrimeCommonModulus_le_local (c : ArithmeticContext)
    (χ : c.S → HeckeCharacter) (p : c.S) :
    sPrimeCommonModulus c χ ≤ (χ p).modulus := by
  apply Ideal.mul_le_right.trans
  exact Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ p))

theorem sPrimeCommonModulus_supported (c : ArithmeticContext)
    (χ : c.S → HeckeCharacter)
    (hχ : ∀ p : c.S, ∀ q : Ideal O, Prime q → q ∣ (χ p).modulus → q ∈ c.S) :
    ∀ q : Ideal O, Prime q → q ∣ sPrimeCommonModulus c χ → q ∈ c.S := by
  intro q hq hdiv
  rcases hq.dvd_mul.mp hdiv with h | h
  · exact c.ray_supported q hq h
  · obtain ⟨p, _, hp⟩ := (hq.dvd_finsetProd_iff _).mp h
    exact hχ p q hq hp

/-- Local prime values suffice for the full target with all quantifiers intact. -/
theorem sPrimeGeneratorRayTarget_of_local (c : ArithmeticContext)
    (hlocal : ∀ p : c.S, SPrimeLocalCharacter c p) :
    SPrimeGeneratorRayTarget c := by
  choose χ hs heval using hlocal
  let M := sPrimeCommonModulus c χ
  have hM : M ≠ ⊥ := sPrimeCommonModulus_ne_bot c χ
  have hS : ∀ q : Ideal O, Prime q → q ∣ M → q ∈ c.S :=
    sPrimeCommonModulus_supported c χ hs
  refine ⟨M, hM, sPrimeCommonModulus_le_ray c χ, hS, ?_⟩
  intro p
  let hle := sPrimeCommonModulus_le_local c χ p
  refine ⟨refineHeckeCharacter (χ p) M hM hle, rfl, ?_⟩
  intro n hn
  change (refineHeckeCharacter (χ p) M hM hle).onElement (primaryGenerator n) = _
  calc
    _ = (χ p).onElement (primaryGenerator n) :=
      refineHeckeCharacter_onElement (χ p) M hM hle
        (primaryGenerator_unit_mod_supported c M hM hS hn)
    _ = sexticSymbol n (idealGenerator p.val) :=
      rayValue_eq_sexticSymbol_of_prime_values (χ p) c _ (heval p) hn

/-- The reduction is reversible: it neither strengthens nor weakens the target. -/
theorem sPrimeGeneratorRayTarget_iff_local (c : ArithmeticContext) :
    SPrimeGeneratorRayTarget c ↔ ∀ p : c.S, SPrimeLocalCharacter c p := by
  constructor
  · rintro ⟨M, _, _, hS, hχ⟩ p
    obtain ⟨χ, hχM, hval⟩ := hχ p
    refine ⟨χ, ?_, ?_⟩
    · intro q hq hdiv
      exact hS q hq (hχM ▸ hdiv)
    · intro q hq hqn
      exact (hval q hqn).trans (sexticSymbol_prime hq _)
  · exact sPrimeGeneratorRayTarget_of_local c

/-- Only the two named local arithmetic inputs remain unproved. -/
theorem sPrimeGeneratorReciprocity_of_local_inputs
    (hramified : SPrimeRamifiedLocalReciprocityStatement)
    (hordinary : SPrimeOrdinaryLocalReciprocityStatement) :
    SPrimeGeneratorReciprocityStatement := by
  intro c hc
  apply sPrimeGeneratorRayTarget_of_local c
  intro p
  by_cases hp : p.val ∣ principal (6 : O)
  · exact hramified c hc p hp
  · exact hordinary c hc p hp

theorem sPrimeGeneratorReciprocity_iff_local_inputs :
    SPrimeGeneratorReciprocityStatement ↔
      SPrimeRamifiedLocalReciprocityStatement ∧
        SPrimeOrdinaryLocalReciprocityStatement := by
  constructor
  · intro h
    constructor
    · intro c hc p _
      exact (sPrimeGeneratorRayTarget_iff_local c).mp (h c hc) p
    · intro c hc p _
      exact (sPrimeGeneratorRayTarget_iff_local c).mp (h c hc) p
  · rintro ⟨hramified, hordinary⟩
    exact sPrimeGeneratorReciprocity_of_local_inputs hramified hordinary

end QRHShort.SquarefreeReflection

set_option pp.fullNames true
#print axioms QRHShort.SquarefreeReflection.SPrimeLocalCharacter
#print axioms QRHShort.SquarefreeReflection.SPrimeRamifiedLocalReciprocityStatement
#print axioms QRHShort.SquarefreeReflection.SPrimeOrdinaryLocalReciprocityStatement
#print axioms QRHShort.SquarefreeReflection.sPrime_dvd_six_iff
#print axioms QRHShort.SquarefreeReflection.onIdeal_eq_rayValue_outside
#print axioms QRHShort.SquarefreeReflection.rayValue_eq_sexticSymbol_of_prime_values
#print axioms QRHShort.SquarefreeReflection.sPrimeCommonModulus
#print axioms QRHShort.SquarefreeReflection.sPrimeCommonModulus_ne_bot
#print axioms QRHShort.SquarefreeReflection.sPrimeCommonModulus_le_ray
#print axioms QRHShort.SquarefreeReflection.sPrimeCommonModulus_le_local
#print axioms QRHShort.SquarefreeReflection.sPrimeCommonModulus_supported
#print axioms QRHShort.SquarefreeReflection.sPrimeGeneratorRayTarget_of_local
#print axioms QRHShort.SquarefreeReflection.sPrimeGeneratorRayTarget_iff_local
#print axioms QRHShort.SquarefreeReflection.sPrimeGeneratorReciprocity_of_local_inputs
#print axioms QRHShort.SquarefreeReflection.sPrimeGeneratorReciprocity_iff_local_inputs
