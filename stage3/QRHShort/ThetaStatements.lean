import QRHShort.ThetaObjects
import QRHShort.ArithmeticStatements

/-! Statements of `lem:theta-realization`, `lem:reflection`,
`lem:reflection-uniformity`, and `lem:theta-bounds` in paper2.tex.
All coefficient sequences, local factors and integral transforms are concrete.
Existential constants and finite families precede the varying primes and scales. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

def ThetaRealizationStatement : Prop :=
  (∀ (c : ArithmeticContext), ArithmeticRelations c →
    ∀ (ξ : RayCharacter c) (I : SupportInterval) (W : ℝ → ℂ)
      (X : ℝ) (k : O) (f : Ideal O),
      SmoothSupported I W → 0 < X → Outside c.S f →
      completedRow c ξ W X k f =
        (((3 : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt X : ℝ) : ℂ)⁻¹ *
          ∑' n : O, if n ≠ 0 ∧ IsPrimary n ∧ Squarefree (principal n) ∧
              Outside c.S (principal n) then
            ∑' b : O, if b ≠ 0 ∧ IsPrimary b ∧ Outside c.S (principal b) then
              cuspCoefficient .zero (embedding lambda ^ (-3 : ℤ) * embedding (n * b ^ 3)) *
                thetaMultiplier c ξ k f (n * b ^ 3) *
                star (embedding (n * b ^ 3) / (‖embedding (n * b ^ 3)‖ : ℂ)) *
                W (normElement (n * b ^ 3) / X)
            else 0
          else 0)
  ∧ ∀ (c : ArithmeticContext) (ξ : RayCharacter c) (k : O) (f : Ideal O)
      (q : O), principal q ≠ ⊥ →
      (∀ a b : O, a - b ∈ principal q →
        thetaMultiplier c ξ k f a = thetaMultiplier c ξ k f b) →
      ∀ (z : ℂ) (v : ℝ), 0 < v →
      let φ := thetaMultiplier c ξ k f
      twistedTheta φ z v =
        ∑' h : O ⧸ principal q, finiteFourier φ q h *
          star (cubicTheta (z + embedding (lambda ^ 2 * residueLift (principal q) h) /
            embedding q) v)

def PrimeTwistSet (S P : Finset (Ideal O)) : Prop :=
  ∀ p ∈ P, Prime p ∧ p ∉ S

def AdmissibleActive (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (A : Finset (Ideal O)) : Prop :=
  A ⊆ P ∧ ∀ p ∈ P, (j p).val ≠ 0 → p ∈ A

def productTwist (c : ArithmeticContext) (ξ : RayCharacter c)
    (P : Finset (Ideal O)) (j : Ideal O → Fin 6) (n : Ideal O) : ℂ :=
  if Outside c.S n then rayValue ξ.val n *
    ∏ p ∈ P, localCharacterPower p ((j p).val : ℤ) (primaryGenerator n)
  else 0

structure ReflectionDatum where
  cusp : ThetaCusp
  phase : O → ℂ
  phase_add : ∀ a b, phase (a + b) = phase a * phase b
  phase_norm : ∀ a, ‖phase a‖ = 1
  denominator : O
  denominator_ne_zero : denominator ≠ 0

def reflectionDenominator (d : ReflectionDatum) (A : Finset (Ideal O)) : O :=
  d.denominator * ∏ p ∈ A, primaryGenerator p

def dualThetaSum (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' m : O, if m = 0 then 0 else
    let ell := embedding lambda ^ (-4 : ℤ) * embedding m
    cuspCoefficient d.cusp ell * (ell / (‖ell‖ : ℂ)) / (‖ell‖ : ℂ) *
      d.phase m * (∏ p ∈ A, thetaLocalFactor p (j p) m) *
      thetaWeight V (Complex.normSq ell * X /
        normElement (reflectionDenominator d A) ^ (2 : ℕ))

def ReflectionStatement : Prop :=
  ∀ (c : ArithmeticContext) (ξ : RayCharacter c),
    ∃ N : ℕ, ∃ data : Fin N → ReflectionDatum, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (P : Finset (Ideal O)) (j : Ideal O → Fin 6), PrimeTwistSet c.S P →
        ∃ coeff : Fin N → Finset (Ideal O) → ℂ,
          (∀ h A, AdmissibleActive P j A → ‖coeff h A‖ ≤ K) ∧
          ∀ (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ),
            SmoothSupported I W → 0 < X →
            completedSum c (productTwist c ξ P j) W X =
              ∑ h : Fin N, ∑ A ∈ P.powerset,
                if AdmissibleActive P j A then coeff h A *
                  dualThetaSum (data h) A j (fun x => (Real.sqrt x : ℂ) * W x) X
                else 0

def SameRayModulo (M : Ideal O) (a b : O) : Prop :=
  ∃ u : Oˣ, a - (u : O) * b ∈ M

def variableTwistExponents (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (p : Ideal O) : Fin 6 := if p ∈ P then j p else 1

/-- The common finite pool and index bound depend only on the fixed ray
character. The varying squarefree ideal enters the selected triple only
through a ray class modulo the single fixed S-supported ideal M. -/
def ReflectionUniformityStatement : Prop :=
  ∀ (c : ArithmeticContext) (ξ : RayCharacter c),
    ∃ N H : ℕ, ∃ pool : Fin N → ReflectionDatum, ∃ K : ℝ, 0 ≤ K ∧
      ∃ M : Ideal O, M ≠ ⊥ ∧
        (∀ p : Ideal O, Prime p → p ∣ M → p ∈ c.S) ∧
      ∀ (P : Finset (Ideal O)) (j : Ideal O → Fin 6), PrimeTwistSet c.S P →
        ∃ pick : Ideal O → Fin H → Finset (Ideal O) → Fin N,
        ∃ coeff : Ideal O → Fin H → Finset (Ideal O) → ℂ,
          (∀ k l, SquarefreeOutside c.S k → SquarefreeOutside c.S l →
            IsRelPrime k (∏ p ∈ P, p) → IsRelPrime l (∏ p ∈ P, p) →
            SameRayModulo M (primaryGenerator k) (primaryGenerator l) →
            ∀ h A, AdmissibleActive P j A → pick k h A = pick l h A) ∧
          ∀ k : Ideal O, SquarefreeOutside c.S k → IsRelPrime k (∏ p ∈ P, p) →
            (∀ h A, AdmissibleActive P j A → ‖coeff k h A‖ ≤ K) ∧
            ∀ (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ),
              SmoothSupported I W → 0 < X →
              let j' := variableTwistExponents P j
              completedSum c (productTwist c ξ (P ∪ primeFactors k) j') W X =
                ∑ h : Fin H, ∑ A ∈ P.powerset,
                  if AdmissibleActive P j A then coeff k h A *
                    dualThetaSum (pool (pick k h A)) (A ∪ primeFactors k) j'
                      (fun x => (Real.sqrt x : ℂ) * W x) X
                  else 0

def ThetaBoundsStatement : Prop :=
  (∀ (σ : ThetaCusp) (ell : ℂ), cuspCoefficient σ ell ≠ 0 →
    ∃ (u : Oˣ) (m : ℤ) (n b : O), -4 ≤ m ∧ PrimaryCubeData n b ∧
      ell = embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3)) ∧
  (∀ (σ : ThetaCusp) (u : Oˣ) (m : ℤ) (n b : O),
    -4 ≤ m → PrimaryCubeData n b →
      ‖cuspCoefficient σ (embedding (u : O) * embedding lambda ^ m * embedding (n * b ^ 3))‖ ≤
        27 * (3 : ℝ) ^ ((m : ℝ) / 6) * ‖embedding b‖) ∧
  (∀ (A : ℝ) (j : ℕ), 0 < A → ∃ J : ℕ, 1 ≤ J ∧
    ∀ I : SupportInterval, ∃ K : ℝ, 0 ≤ K ∧ ∀ (V : ℝ → ℂ),
      SmoothSupported I V → ∀ x : ℝ, 0 < x →
        ‖eulerDerivative j (thetaWeight V) x‖ ≤
          K * weightNorm J V * min (x ^ (1 / 4 : ℝ)) (x ^ (-A)))

end QRHShort
