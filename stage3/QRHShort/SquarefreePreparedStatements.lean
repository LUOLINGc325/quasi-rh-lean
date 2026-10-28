import QRHShort.SquarefreeSieveRows
import QRHShort.ThetaStatements
import QRHShort.SmoothingStatements
import QRHShort.RecombinationStatement

/-!
Two strictly internal children of `squarefree_completed_step`, following
paper2.tex:1951--2192. Neither child is asserted here. The prepared series is
an explicit series over ideals, not an alias for the completed row estimate.
Its summability is part of the analytic obligation, so regrouping cannot be
justified by the default value of a divergent `tsum`.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

/-- The `m = r - 4` summand in `eq:prepared-theta-sum`, with primary
elements indexed by their ideals. All column restrictions are explicit. -/
def preparedThetaTerm (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k : Ideal O) (q : ℕ × Ideal O × Ideal O) : ℂ :=
  let r := q.1
  let n := q.2.1
  let b := q.2.2
  let m : ℤ := (r : ℤ) - 4
  if n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3) ∧
      b ≠ ⊥ ∧ IsRelPrime b (principal 3) then
    coeff r k * A r n b *
      sexticSymbol k (primaryGenerator n * primaryGenerator b) ^ (3 : ℕ) /
        (((3 : ℝ) ^ ((m : ℝ) / 3) * Real.sqrt (normIdeal n) * normIdeal b : ℝ) : ℂ) *
      thetaWeight (fun x => (Real.sqrt x : ℂ) * W x)
        ((3 : ℝ) ^ (m : ℝ) * normIdeal n * normIdeal b ^ (3 : ℕ) * H ^ (2 : ℕ) /
          (Y * normIdeal k ^ (2 : ℕ)))
  else 0

def preparedThetaRow (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k : Ideal O) : ℂ :=
  ∑' q : ℕ × Ideal O × Ideal O, preparedThetaTerm W H Y A coeff k q

/-- Uniform analytic estimate for the prepared columns. `L` absorbs the
fixed reflection denominators and may depend on the arithmetic context;
the derivative order must be chosen before `S`, `I`, and `L`. -/
def PreparedThetaEstimate : Prop :=
  ∀ ε C : ℝ, 0 < ε → 1 ≤ C → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (S : Finset (Ideal O)) (I : SupportInterval) (L : ℝ), 1 ≤ L →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (D H Y a : ℝ)
        (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ),
        SmoothSupported I W → 2 ≤ D → 1 ≤ H → H ≤ D ^ C →
        0 < Y → Y ≤ L * D ^ C → 0 ≤ a →
        (∀ r n b, ‖A r n b‖ ≤ a) →
        (∀ r k, k ∈ sieveRows S H → ‖coeff r k‖ ≤ 1) →
        (∀ k ∈ sieveRows S H,
          Summable (fun q => ‖preparedThetaTerm W H Y A coeff k q‖)) ∧
        (∑ k ∈ sieveRows S H, ‖preparedThetaRow W H Y A coeff k‖ ^ 2) ≤
          K * D ^ ε * weightNorm J W ^ 2 * a ^ 2 * (H + Y)

/-- Child 1: Mellin separation, quadratic sieve, and the infinite dyadic
and `m` sums, including absolute convergence. -/
def PreparedThetaEstimateStep : Prop :=
  ThetaBoundsStatement → QuadraticEstimate → SmoothSeparationStatement →
    RecombinationStatement → PreparedThetaEstimate

/-- Child 2: split `s = t*k`, resolve the fixed ray characters, expand the
reflection, reindex the exceptional local factors, control the conductor
and number of columns, and sum the `t` and ray-class partitions. -/
def SquarefreeReflectionStep : Prop :=
  ReflectionStatement → ReflectionUniformityStatement → ThetaBoundsStatement →
    PreparedThetaEstimate → SquarefreeCompletedByCharacter

end QRHShort.SquarefreeAssembly
