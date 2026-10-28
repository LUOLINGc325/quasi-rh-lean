import QRHShort.SecondTransferReduction
import Mathlib.NumberTheory.MulChar.Duality

noncomputable section
open Classical

namespace QRHShort

def secondTransferPRMPResidue (c : ArithmeticContext) (ξ : RayCharacter c) :
    MulChar (O ⧸ c.rayModulus) ℂ := ξ.property ▸ ξ.val.residue

theorem second_transfer_prmp_residue_injective (c : ArithmeticContext) :
    Function.Injective (secondTransferPRMPResidue c) := by
  intro ξ η heq
  rcases ξ with ⟨⟨M, hM, r, hu⟩, hξ⟩
  rcases η with ⟨⟨N, hN, s, hv⟩, hη⟩
  change M = c.rayModulus at hξ
  change N = c.rayModulus at hη
  subst M
  subst N
  change r = s at heq
  subst s
  rfl

theorem second_transfer_prmp_rayCharacter_finite (c : ArithmeticContext) :
    Finite (RayCharacter c) := by
  let : Finite (O ⧸ c.rayModulus) :=
    Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  exact Finite.of_injective (secondTransferPRMPResidue c)
    (second_transfer_prmp_residue_injective c)

/-- Finiteness of the complete input family makes the coefficient mass bound
uniform in its input character. The exact row identities remain those of hp. -/
theorem second_transfer_prmp_uniform_coefficients (hp : SecondPoissonStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ₁ : RayCharacter c,
      ∃ coeffs : RayCharacter c → ℂ, (Function.support coeffs).Finite ∧
        (∑' ξ, ‖coeffs ξ‖) ≤ B ∧
        ∀ (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
          (C d t : Ideal O) (Y ell : ℝ),
          SquarefreeOutside c.S C → SquarefreeOutside c.S t → IsRelPrime C t → d ∣ C →
          0 < Y → 0 < ell → SmoothSupported I U →
          ((∑' y : O, Φ.value (normElement y / Y) *
            ‖firstColumn c ξ₁ C d t U ell y‖ ^ 2 : ℝ) : ℂ) =
              secondPoissonZero c Φ U C t Y ell +
                secondPoissonDual c I Φ U coeffs C d t Y ell := by
  let : Finite (RayCharacter c) := second_transfer_prmp_rayCharacter_finite c
  let f : RayCharacter c → RayCharacter c → ℂ := fun ξ => Classical.choose (hp.1 c hc ξ)
  have hf (ξ : RayCharacter c) := Classical.choose_spec (hp.1 c hc ξ)
  obtain ⟨B, hB⟩ := (Set.finite_range (fun ξ => ∑' η, ‖f ξ η‖)).bddAbove
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro ξ
  refine ⟨f ξ, (hf ξ).1, ?_, (hf ξ).2.2⟩
  exact (hB ⟨ξ, rfl⟩).trans (le_max_right _ _)

end QRHShort
