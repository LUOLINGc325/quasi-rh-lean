import QRHShort.SecondPoissonStatements
import QRHShort.SmoothingStatements
import QRHShort.TransferAssembly
import QRHShort.SecondTransferScalar
import Mathlib.Tactic.FinCases

/-!
Decomposition of `Manuscript.second_transfer_step`, paper2.tex:2496--2670.
The four remaining interfaces isolate zero-frequency estimation, signed
regrouping, exclusion removal/counting, and the uniform smooth-kernel bound.
They concern the literal Poisson sums and arithmetic columns, not scalar
surrogates. The assembly below has the unchanged `SecondTransferEstimate`
as its conclusion; none of the four interfaces is asserted as an axiom.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The off-zero part obtained by applying the second Poisson identity to
each summand of `firstForm`, with exactly its original outer ranges. -/
def secondTransferDual (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ)
    (cI H L F Sigma : ℝ) : ℂ :=
  ∑' C : Ideal O, ∑' t : Ideal O,
    if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L then
      ∑' d : Ideal O, if d ∣ C then
        (H * normIdeal C / (normIdeal d * L ^ (2 : ℕ) * F) : ℝ) *
          secondPoissonDual c (halfEnlarged I) Φ U coeffs C d t
            (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ (2 : ℕ)))
            (L / (normIdeal C * normIdeal t))
      else 0
    else 0

def secondTransferInterval (I : SupportInterval) : SupportInterval where
  lo := I.lo / 8
  hi := 2 * I.hi
  lo_pos := div_pos I.lo_pos (by norm_num)
  ordered := by nlinarith [I.lo_pos, I.ordered]

/-- `rho = X'/X'_0`; `a` is the Fourier parameter after this dilation. -/
def secondTransferKernel (Φ : RowWeight) (U : ℝ → ℂ) (rho a : ℝ)
    (x : BoxSpace 2) : ℂ :=
  ((Real.sqrt (rho * x 0) : ℂ)⁻¹ * U (rho * x 0)) *
    star ((Real.sqrt (rho * x 1) : ℂ)⁻¹ * U (rho * x 1)) *
    radialFourier (fun y => (Φ.value y : ℂ)) (a / (x 0 * x 1))

/-- A row after signed regrouping. The two natural numbers select dyadic
blocks; their ranges below fix the blocks uniquely. -/
structure SecondTransferIndex (c : ArithmeticContext) where
  character : RayCharacter c
  excluded : Ideal O
  twist : Ideal O
  frequency : O
  rBlock : ℕ
  fBlock : ℕ

def SecondTransferIndex.columnScale {c : ArithmeticContext}
    (z : SecondTransferIndex c) (L : ℝ) : ℝ :=
  L / ((2 : ℝ) ^ z.rBlock * (2 : ℝ) ^ z.fBlock)

def SecondTransferIndex.dilation {c : ArithmeticContext}
    (z : SecondTransferIndex c) : ℝ :=
  normIdeal z.excluded * normIdeal z.twist /
    ((2 : ℝ) ^ z.rBlock * (2 : ℝ) ^ z.fBlock)

def SecondTransferIndex.parameter {c : ArithmeticContext}
    (z : SecondTransferIndex c) (cI H L F Sigma : ℝ) : ℝ :=
  cI * Sigma * F * normElement z.frequency * normIdeal z.excluded ^ (2 : ℕ) /
    (H * L * z.dilation ^ (2 : ℕ))

def SecondTransferIndex.phase {c : ArithmeticContext}
    (z : SecondTransferIndex c) (coeffs : RayCharacter c → ℂ)
    (cI L Sigma : ℝ) : ℂ :=
  (cI * Sigma / L ^ (2 : ℕ) * normIdeal z.excluded *
    (divisorCount z.excluded : ℝ) : ℝ) * coeffs z.character

def SecondTransferIndex.valid {c : ArithmeticContext} (z : SecondTransferIndex c)
    (I : SupportInterval) (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ) : Prop :=
  SquarefreeOutside c.S z.excluded ∧ SquarefreeOutside c.S z.twist ∧
  IsRelPrime z.excluded z.twist ∧ coeffs z.character ≠ 0 ∧
  z.frequency ≠ 0 ∧ 0 < normElement z.frequency ∧ z.twist ∣ principal z.frequency ∧
  normIdeal z.twist ≤ normElement z.frequency ∧
  normElement z.frequency ≤ H * L / (Sigma * F * normIdeal z.excluded ^ (2 : ℕ)) ∧
  normIdeal z.excluded * normIdeal z.twist ≤ 2 * I.hi * L ∧
  (2 : ℝ) ^ z.rBlock ≤ normIdeal z.excluded ∧
  normIdeal z.excluded < 2 * (2 : ℝ) ^ z.rBlock ∧
  (2 : ℝ) ^ z.fBlock ≤ normIdeal z.twist ∧
  normIdeal z.twist < 2 * (2 : ℝ) ^ z.fBlock

/-- Finite arithmetic arrays. `column_complete` is a truncation identity for
every supported test, so arbitrary partial sums cannot be used to infer a
mean-square bound for the full column. No estimate is a field of this type. -/
structure SecondTransferFiniteModel (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ) where
  R : ℕ
  N : ℕ
  row : Fin R → SecondTransferIndex c
  row_injective : Function.Injective row
  valid : ∀ r, (row r).valid I coeffs H L F Sigma
  a : Fin R → Fin N → ℂ
  x : Fin R → Fin N → ℝ
  x_pos : ∀ r n, 0 < x r n
  column_complete : ∀ (r : Fin R) (V : ℝ → ℂ), SmoothSupported (enlarged I) V →
    finiteTestSum a x r V =
      excludedColumnSum c (row r).character V (row r).excluded
        ((row r).columnScale L) (row r).frequency (row r).twist
  dilation_lower : ∀ r, 1 ≤ (row r).dilation
  dilation_upper : ∀ r, (row r).dilation ≤ 4
  parameter_nonneg : ∀ r, 0 ≤ (row r).parameter cI H L F Sigma

def SecondTransferFiniteModel.phase {c : ArithmeticContext} {I : SupportInterval}
    {coeffs : RayCharacter c → ℂ} {cI H L F Sigma : ℝ}
    (model : SecondTransferFiniteModel c I coeffs cI H L F Sigma) (r : Fin model.R) : ℂ :=
  (model.row r).phase coeffs cI L Sigma

def SecondTransferFiniteModel.weight {c : ArithmeticContext} {I : SupportInterval}
    {coeffs : RayCharacter c → ℂ} {cI H L F Sigma : ℝ}
    (model : SecondTransferFiniteModel c I coeffs cI H L F Sigma) (r : Fin model.R) : ℝ :=
  ‖model.phase r‖

def SecondTransferFiniteModel.kernel {c : ArithmeticContext} {I : SupportInterval}
    {coeffs : RayCharacter c → ℂ} {cI H L F Sigma : ℝ}
    (model : SecondTransferFiniteModel c I coeffs cI H L F Sigma)
    (Φ : RowWeight) (U : ℝ → ℂ) (r : Fin model.R) : BoxSpace 2 → ℂ :=
  secondTransferKernel Φ U (model.row r).dilation
    ((model.row r).parameter cI H L F Sigma)

/-- P: the actual Poisson expansion and the total zero-frequency bound.
The coefficient mass bound is uniform in the input ray character. -/
def SecondTransferPoissonBound : Prop :=
  ∀ (C ε : ℝ) (q : ℕ), 1 ≤ C → 0 < ε →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) (cI : ℝ),
      ArithmeticRelations c → max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (U : ℝ → ℂ)
        (D H L F Sigma : ℝ), SmoothSupported (halfEnlarged I) U → 2 ≤ D →
        TransferRange D C H L F Sigma →
        ∃ coeffs : RayCharacter c → ℂ, (Function.support coeffs).Finite ∧
          (∑' ξ', ‖coeffs ξ'‖) ≤ K ∧
          firstForm c I Φ ξ U cI H L F Sigma ≤
            K * D ^ ε * Sigma * weightNorm q U ^ 2 +
              ‖secondTransferDual c I Φ U coeffs cI H L F Sigma‖

/-- R: regroup with signs before taking absolute values. The exact phase
contains `N(r) tau(r)` and the surviving restriction is `f' | k'`.
All sums here are finite and the array is independent of the test U. -/
def SecondTransferRegroupStatement : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (cI : ℝ), ArithmeticRelations c →
    max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI →
    ∀ (D H L F Sigma : ℝ) (coeffs : RayCharacter c → ℂ),
      2 ≤ D → TransferRange D C H L F Sigma → (Function.support coeffs).Finite →
      ∃ model : SecondTransferFiniteModel c I coeffs cI H L F Sigma,
        ∀ U : ℝ → ℂ, SmoothSupported (halfEnlarged I) U →
          secondTransferDual c I Φ U coeffs cI H L F Sigma =
            ∑ r : Fin model.R, model.phase r *
              ∑ n₁ : Fin model.N, ∑ n₂ : Fin model.N,
                model.a r n₁ * star (model.a r n₂) *
                  model.kernel Φ U r ![model.x r n₁, model.x r n₂]

/-- M: use exclusion removal, child-scale admissibility and ideal counting.
The bound is universal over finite arithmetic models with no repeated rows.
It includes all dyadic blocks and the finite character coefficient mass. -/
def SecondTransferMeanSquareStatement : Prop :=
  ∀ (C ε : ℝ) (m : ℕ), 1 ≤ C → 0 < ε →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) (cI : ℝ),
      ArithmeticRelations c → max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (D H L F Sigma : ℝ) (coeffs : RayCharacter c → ℂ),
        2 ≤ D → TransferRange D C H L F Sigma → (Function.support coeffs).Finite →
        ∀ (model : SecondTransferFiniteModel c I coeffs cI H L F Sigma)
          (V : ℝ → ℂ), SmoothSupported (enlarged I) V →
          (∑ r : Fin model.R, model.weight r * ‖finiteTestSum model.a model.x r V‖ ^ 2) ≤
            K * D ^ ε * Sigma * (∑' ξ', ‖coeffs ξ'‖) *
              childSup c I m H L F Sigma * weightNorm m V ^ 2

/-- K: uniform Schwartz/chain-rule bounds after a dilation between 1 and 4.
The auxiliary interval is strictly inside the enlarged interval required by
the frozen smooth-mean-square lemma. -/
def SecondTransferKernelStatement : Prop :=
  ∀ (I : SupportInterval) (Φ : RowWeight) (q : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : ℝ → ℂ) (rho a : ℝ),
      SmoothSupported (halfEnlarged I) U → 1 ≤ rho → rho ≤ 4 → 0 ≤ a →
      SmoothBox (fun _ : Fin 2 => secondTransferInterval I)
        (secondTransferKernel Φ U rho a) ∧
      multiWeightNorm q (secondTransferKernel Φ U rho a) ≤ K * weightNorm q U ^ 2

theorem second_transfer_interval_interior (I : SupportInterval) :
    (enlarged I).lo < (secondTransferInterval I).lo ∧
    (secondTransferInterval I).hi < (enlarged I).hi := by
  dsimp [enlarged, secondTransferInterval]
  constructor <;> linarith [I.lo_pos, I.ordered]

/-- The kernel vanishes outside the rescaled compact box. Differentiability
and quantitative derivative bounds remain exactly child K. -/
theorem second_transfer_kernel_support (I : SupportInterval) (Φ : RowWeight)
    (U : ℝ → ℂ) (rho a : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hrho : 1 ≤ rho) (hrho4 : rho ≤ 4) :
    Function.support (secondTransferKernel Φ U rho a) ⊆
      {x | ∀ i, x i ∈ Set.Icc (secondTransferInterval I).lo
        (secondTransferInterval I).hi} := by
  intro x hx
  have hprod := (mul_ne_zero_iff.mp hx).1
  have hleft : U (rho * x 0) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).2
  have hright : U (rho * x 1) ≠ 0 := by
    have hstar := (mul_ne_zero_iff.mp hprod).2
    have hrightprod : (Real.sqrt (rho * x 1) : ℂ)⁻¹ * U (rho * x 1) ≠ 0 := by
      intro hz
      exact hstar (by rw [hz, star_zero])
    exact (mul_ne_zero_iff.mp hrightprod).2
  have bounds (i : Fin 2) (hi : U (rho * x i) ≠ 0) :
      x i ∈ Set.Icc (secondTransferInterval I).lo (secondTransferInterval I).hi := by
    obtain ⟨hlo, hhi⟩ := hU.2 hi
    change I.lo / 2 ≤ rho * x i at hlo
    change rho * x i ≤ 2 * I.hi at hhi
    have hxpos : 0 < x i := by
      have hmul : 0 < rho * x i := lt_of_lt_of_le (div_pos I.lo_pos (by norm_num)) hlo
      exact (mul_pos_iff_of_pos_left (lt_of_lt_of_le zero_lt_one hrho)).mp hmul
    change I.lo / 8 ≤ x i ∧ x i ≤ 2 * I.hi
    constructor <;> nlinarith
  intro i
  fin_cases i
  · exact bounds 0 hleft
  · exact bounds 1 hright

/-- Conditional assembly. Its conclusion is the entire frozen estimate,
including quantifier order, constants, test support and derivative order. -/
theorem second_transfer_of_components
    (hpoisson : SecondTransferPoissonBound) (hregroup : SecondTransferRegroupStatement)
    (hmean : SecondTransferMeanSquareStatement) (hkernel : SecondTransferKernelStatement)
    (hsmooth : SmoothMeanSquareStatement) : SecondTransferEstimate := by
  intro C ε m hC hε c I Φ cI hc hcI
  obtain ⟨Kp, hKp, hP⟩ := hpoisson C ε (2 * m + 4) hC hε c I Φ cI hc hcI
  obtain ⟨Km, hKm, hM⟩ := hmean C ε m hC hε c I Φ cI hc hcI
  obtain ⟨Kk, hKk, hK⟩ := hkernel I Φ (2 * m + 4)
  obtain ⟨hlo, hhi⟩ := second_transfer_interval_interior I
  obtain ⟨Ks, hKs, hS⟩ := hsmooth (secondTransferInterval I) (enlarged I) m hlo hhi
  let Kb : ℝ := Ks * Km * Kp * Kk
  have hKb : 0 ≤ Kb := mul_nonneg (mul_nonneg (mul_nonneg hKs hKm) hKp) hKk
  refine ⟨Kp + Kb, add_nonneg hKp hKb, ?_⟩
  intro ξ U D H L F Sigma hU hD hrange
  obtain ⟨coeffs, hfinite, hmass, hfirst⟩ := hP ξ U D H L F Sigma hU hD hrange
  obtain ⟨model, hexp⟩ := hregroup C hC c I Φ cI hc hcI D H L F Sigma coeffs
    hD hrange hfinite
  have hp : 0 ≤ D ^ ε := Real.rpow_nonneg (le_trans (by norm_num) hD) _
  have hSigma : 0 ≤ Sigma := le_trans zero_le_one hrange.2.2.2.2.2.2.1
  have hchild : 0 ≤ childSup c I m H L F Sigma := childSup_nonneg c I m H L F Sigma
  let M : ℝ := Km * D ^ ε * Sigma * Kp * childSup c I m H L F Sigma
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKm hp) hSigma) hKp) hchild
  have htest (V : ℝ → ℂ) (hV : SmoothSupported (enlarged I) V) :
      (∑ r : Fin model.R, model.weight r * ‖finiteTestSum model.a model.x r V‖ ^ 2) ≤
        M * weightNorm m V ^ 2 := by
    apply (hM D H L F Sigma coeffs hD hrange hfinite model V hV).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hchild
    exact mul_le_mul_of_nonneg_left hmass (mul_nonneg (mul_nonneg hKm hp) hSigma)
  have hk (r : Fin model.R) := hK U (model.row r).dilation
    ((model.row r).parameter cI H L F Sigma) hU
    (model.dilation_lower r) (model.dilation_upper r) (model.parameter_nonneg r)
  have hbound := hS model.R model.N model.N model.a model.a model.x model.x
    model.weight model.phase M M (model.kernel Φ U) model.x_pos model.x_pos
    (fun r => norm_nonneg _) (fun _ => le_rfl) hM0 hM0 htest htest (fun r => (hk r).1)
  rw [Real.sqrt_mul_self hM0] at hbound
  have hsup : QRHLean3.supZero
      {v | ∃ r : Fin model.R, v = multiWeightNorm (2 * m + 4) (model.kernel Φ U r)} ≤
        Kk * weightNorm (2 * m + 4) U ^ 2 := by
    apply QRHLean3.supZero_le (mul_nonneg hKk (sq_nonneg _))
    rintro v ⟨r, rfl⟩
    exact (hk r).2
  have hdual : ‖secondTransferDual c I Φ U coeffs cI H L F Sigma‖ ≤
      Kb * D ^ ε * Sigma * childSup c I m H L F Sigma * weightNorm (2 * m + 4) U ^ 2 := by
    calc
      _ ≤ Ks * M * QRHLean3.supZero
          {v | ∃ r : Fin model.R, v = multiWeightNorm (2 * m + 4) (model.kernel Φ U r)} := by
        rw [hexp U hU]
        exact hbound
      _ ≤ Ks * M * (Kk * weightNorm (2 * m + 4) U ^ 2) :=
        mul_le_mul_of_nonneg_left hsup (mul_nonneg hKs hM0)
      _ = _ := by dsimp only [M, Kb]; ring
  have hfinal : Kp + Kb * childSup c I m H L F Sigma ≤
      (Kp + Kb) * (1 + childSup c I m H L F Sigma) := by
    nlinarith [mul_nonneg hKp hchild]
  calc
    _ ≤ Kp * D ^ ε * Sigma * weightNorm (2 * m + 4) U ^ 2 +
        Kb * D ^ ε * Sigma * childSup c I m H L F Sigma * weightNorm (2 * m + 4) U ^ 2 :=
      hfirst.trans (add_le_add le_rfl hdual)
    _ = (Kp + Kb * childSup c I m H L F Sigma) *
        (D ^ ε * Sigma * weightNorm (2 * m + 4) U ^ 2) := by ring
    _ ≤ ((Kp + Kb) * (1 + childSup c I m H L F Sigma)) *
        (D ^ ε * Sigma * weightNorm (2 * m + 4) U ^ 2) :=
      mul_le_mul_of_nonneg_right hfinal (mul_nonneg (mul_nonneg hp hSigma) (sq_nonneg _))
    _ = _ := by ring

end QRHShort
