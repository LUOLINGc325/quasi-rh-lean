import QRHShort.AnalyticObjects
import QRHShort.ArithmeticStatements
import QRH.Definitions

/-! Quantified analytic statements from the 11/12 manuscript.
Derivative orders precede the support interval and every varying scale.
The constants below are nonnegative and uniform in tests and scales.
These propositions are the actual arithmetic estimates, not scalar surrogate bounds. -/

noncomputable section
open scoped BigOperators
namespace QRHShort
open Classical

def MeanSquareEstimate : Prop :=
  ∀ θ ε : ℝ, 0 < θ → θ ≤ (1 : ℝ) / 10 → 0 < ε →
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (c : ArithmeticContext) (I : SupportInterval),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (D : ℝ),
        SmoothSupported I W → 2 ≤ D →
        originalMeanSquare c W D (D ^ (1 + θ)) ≤
          K * weightNorm J W ^ 2 * D ^ (2 + θ + ε)

def InitialEnergyEstimate (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (c : ArithmeticContext) (I : SupportInterval) (C : ℝ), ArithmeticRelations c → 1 ≤ C →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
        (D B F H : ℝ), SmoothSupported I W → 2 ≤ D → 1 ≤ B → 1 ≤ F →
        0 < H → H ≤ C * D ^ (2 : ℕ) / (D ^ (1 + θ) * B ^ (2 : ℕ)) →
        energy c ξ W H (D / (B * F)) F ≤
          K * weightNorm J W ^ 2 * D ^ ε * (D / B)

/-- Proposition `prop:poisson-reduction`: the initial-scale estimate implies
the original arithmetic mean square, with the same fixed theta parameter. -/
def PoissonReductionStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ (1 : ℝ) / 10 → InitialEnergyEstimate θ →
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 1 ≤ J ∧
      ∀ (c : ArithmeticContext) (I : SupportInterval),
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (D : ℝ),
          SmoothSupported I W → 2 ≤ D →
          originalMeanSquare c W D (D ^ (1 + θ)) ≤
            K * weightNorm J W ^ 2 * D ^ (2 + θ + ε)

def CanonicalEstimate : Prop :=
  ∀ κ C ε : ℝ, 0 < κ → 1 ≤ C → 0 < ε →
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
        (D H X F : ℝ), SmoothSupported I W → 2 ≤ D →
        QRH.ParentRange D κ C H X F →
        energy c ξ W H X F ≤ K * weightNorm J W ^ 2 * D ^ ε * (X * F)

def CompletedEstimate : Prop :=
  ∀ ε C : ℝ, 0 < ε → 1 ≤ C → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (c : ArithmeticContext) (I : SupportInterval) (A : ℝ), ArithmeticRelations c → 0 < A →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
        (D H X : ℝ) (f : Ideal O), SmoothSupported I W → 2 ≤ D →
        SquarefreeOutside c.S f → 1 ≤ H → H ≤ D ^ C →
        1 ≤ X → X ≤ D ^ C → 1 ≤ normIdeal f → normIdeal f ≤ D ^ C →
        rowEnergy (fun k => completedRow c ξ W X k f) (A * H) ≤
          K * D ^ ε * weightNorm J W ^ 2 *
            (H + H ^ (2 : ℕ) * normIdeal f / X)

def CubeEstimate : Prop :=
  ∀ C ε : ℝ, 1 ≤ C → 0 < ε → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
        (D H X F hc : ℝ), SmoothSupported I W → 2 ≤ D →
        1 ≤ H → H ≤ D ^ C → 1 ≤ X → X ≤ D ^ C →
        1 ≤ F → F ≤ D ^ C → H ≤ X * F → 0 ≤ hc →
        hc ^ (3 : ℕ) = min X (X ^ (2 : ℕ) / H ^ (2 : ℕ)) →
        energy c ξ W H X F ≤ K * D ^ ε *
          (X * F * weightNorm J W ^ 2 + QRHLean3.supZero (cubeValues c ξ W H X F hc))

def TransferEstimate : Prop :=
  ∀ (C ε : ℝ) (m : ℕ), 1 ≤ C → 0 < ε →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight), ArithmeticRelations c →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
        (D H L F Sigma : ℝ), SmoothSupported I W → 2 ≤ D → TransferRange D C H L F Sigma →
        smoothedEnergy c ξ Φ.value W H L F ≤
          K * D ^ ε * Sigma * weightNorm (4 * m + 12) W ^ 2 *
            (1 + childSup c I m H L F Sigma)

def QuadraticEstimate : Prop :=
  ∀ (S : Finset (Ideal O)) (ε a b : ℝ), 0 < ε → 0 < a → a ≤ b →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (H U : ℝ) (β : Ideal O → ℂ), 1 ≤ H → 1 ≤ U →
      Function.support β ⊆ {n | n ≠ ⊥ ∧ Squarefree n ∧
        IsRelPrime n (principal 3) ∧ a * U ≤ normIdeal n ∧ normIdeal n ≤ b * U} →
      (∑' k : Ideal O, if SquarefreeOutside S k ∧ IsRelPrime k (principal 6) ∧
          normIdeal k ≤ H then
        ‖∑' n : Ideal O, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2
        else 0) ≤ K * (H * U) ^ ε * (H + U) * ∑' n : Ideal O, ‖β n‖ ^ 2

def SquarefreeCompletedEstimate : Prop :=
  ∀ ε C : ℝ, 0 < ε → 1 ≤ C → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
        (D H X : ℝ) (g : O) (u : Oˣ), SmoothSupported I W → 2 ≤ D →
        1 ≤ H → H ≤ D ^ C → 1 ≤ X → X ≤ D ^ C →
        1 ≤ normElement g → normElement g ≤ D ^ C →
        (∑' s : Ideal O, if s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ H then
          ‖completedRowElement c ξ W X ((u : O) * chosenGenerator s) g‖ ^ 2 else 0) ≤
          K * D ^ ε * weightNorm J W ^ 2 * (H + H ^ (2 : ℕ) * normElement g / X)

def FirstTransferEstimate : Prop :=
  ∀ (C ε : ℝ) (j : ℕ), 1 ≤ C → 0 < ε →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) (cI : ℝ),
      ArithmeticRelations c → max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
        (D H L F Sigma M : ℝ), SmoothSupported I W → 2 ≤ D →
        TransferRange D C H L F Sigma → 0 ≤ M →
        (∀ (ξ₁ : RayCharacter c) (U : ℝ → ℂ), SmoothSupported (halfEnlarged I) U →
          firstForm c I Φ ξ₁ U cI H L F Sigma ≤ M * weightNorm j U ^ 2) →
        smoothedEnergy c ξ Φ.value W H L F ≤
          K * D ^ ε * (Sigma + M) * weightNorm (2 * j + 4) W ^ 2

def SecondTransferEstimate : Prop :=
  ∀ (C ε : ℝ) (m : ℕ), 1 ≤ C → 0 < ε →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) (cI : ℝ),
      ArithmeticRelations c → max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ₁ : RayCharacter c) (U : ℝ → ℂ)
        (D H L F Sigma : ℝ), SmoothSupported (halfEnlarged I) U → 2 ≤ D →
        TransferRange D C H L F Sigma →
        firstForm c I Φ ξ₁ U cI H L F Sigma ≤
          K * D ^ ε * Sigma * (1 + childSup c I m H L F Sigma) *
            weightNorm (2 * m + 4) U ^ 2

end QRHShort
