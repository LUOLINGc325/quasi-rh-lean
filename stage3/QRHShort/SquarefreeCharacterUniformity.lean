import QRHShort.Estimates
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Tactic.Positivity

/-! The finite-character uniformization needed at the end of
`lem:squarefree-completed`.  No analytic estimate is assumed implicitly. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort
namespace SquarefreeAssembly

def rayResidue (c : ArithmeticContext) (ξ : RayCharacter c) :
    MulChar (O ⧸ c.rayModulus) ℂ :=
  Eq.mp (congrArg (fun M : Ideal O => MulChar (O ⧸ M) ℂ) ξ.property) ξ.val.residue

theorem rayResidue_injective (c : ArithmeticContext) :
    Function.Injective (rayResidue c) := by
  intro ξ η h
  rcases ξ with ⟨⟨M, hM, χ, hχ⟩, hξ⟩
  rcases η with ⟨⟨N, hN, ψ, hψ⟩, hη⟩
  dsimp only at hξ hη
  subst M
  subst N
  change χ = ψ at h
  cases h
  rfl

theorem rayCharacter_finite (c : ArithmeticContext) : Finite (RayCharacter c) := by
  letI : Finite (O ⧸ c.rayModulus) :=
    Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  exact Finite.of_injective (rayResidue c) (rayResidue_injective c)

/-- The same numerical estimate before the final finite-character
uniformization.  The derivative order already precedes the character. -/
def SquarefreeCompletedByCharacter : Prop :=
  ∀ ε C : ℝ, 0 < ε → 1 ≤ C → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
      ∀ ξ : RayCharacter c, ∃ K : ℝ, 0 ≤ K ∧
        ∀ (W : ℝ → ℂ) (D H X : ℝ) (g : O) (u : Oˣ),
        SmoothSupported I W → 2 ≤ D →
        1 ≤ H → H ≤ D ^ C → 1 ≤ X → X ≤ D ^ C →
        1 ≤ normElement g → normElement g ≤ D ^ C →
        (∑' s : Ideal O, if s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ H then
          ‖completedRowElement c ξ W X ((u : O) * chosenGenerator s) g‖ ^ 2 else 0) ≤
          K * D ^ ε * weightNorm J W ^ 2 *
            (H + H ^ (2 : ℕ) * normElement g / X)

theorem squarefree_completed_uniformize (h : SquarefreeCompletedByCharacter) :
    SquarefreeCompletedEstimate := by
  intro ε C hε hC
  obtain ⟨J, hJ, hξ⟩ := h ε C hε hC
  refine ⟨J, hJ, ?_⟩
  intro c I hc
  letI : Finite (RayCharacter c) := rayCharacter_finite c
  letI : Fintype (RayCharacter c) := Fintype.ofFinite _
  let K : RayCharacter c → ℝ := fun ξ => (hξ c I hc ξ).choose
  have hK : ∀ ξ, 0 ≤ K ξ := fun ξ => (hξ c I hc ξ).choose_spec.1
  refine ⟨∑ ξ, K ξ, Finset.sum_nonneg (fun ξ _ => hK ξ), ?_⟩
  intro ξ W D H X g u hW hD hH hHmax hX hXmax hg hgmax
  have hconst : K ξ ≤ ∑ η, K η :=
    Finset.single_le_sum (fun η _ => hK η) (Finset.mem_univ ξ)
  have hscale : 0 ≤ D ^ ε := Real.rpow_nonneg (by positivity) _
  have hpoly : 0 ≤ H + H ^ (2 : ℕ) * normElement g / X := by positivity
  exact ((hξ c I hc ξ).choose_spec.2 W D H X g u
    hW hD hH hHmax hX hXmax hg hgmax).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst hscale) (sq_nonneg _)) hpoly)

end SquarefreeAssembly
end QRHShort

#print axioms QRHShort.SquarefreeAssembly.rayCharacter_finite
#print axioms QRHShort.SquarefreeAssembly.squarefree_completed_uniformize
