import QRHShort.FirstTransferReduction
import QRHShort.FirstTransferRayFourierInput
import Mathlib.NumberTheory.MulChar.Duality

/-! The full frozen family of ray characters at its fixed modulus is finite.
Consequently every fixed bilinear norm family has a genuine bounded supremum,
without assumptions on the test weight or scales. -/

noncomputable section
open Classical

namespace QRHShort
open FirstTransferRayFourier

/-- Transporting residues to the common ray modulus loses no character data.
The dependent modulus and proof fields of the frozen structure are preserved. -/
theorem first_transfer_residueAtRayModulus_injective (c : ArithmeticContext) :
    Function.Injective (residueAtRayModulus c) := by
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

/-- This instance concerns all frozen ray characters, not just the characters
selected by a Fourier expansion.  Complex-valued multiplicative characters of
a finite monoid are finite through their characters on its finite unit group. -/
instance first_transfer_rayCharacter_finite (c : ArithmeticContext) :
    Finite (RayCharacter c) := by
  letI : Finite (O ⧸ c.rayModulus) :=
    Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  exact Finite.of_injective (residueAtRayModulus c)
    (first_transfer_residueAtRayModulus_injective c)

theorem first_transfer_rayCharacter_range_finite (c : ArithmeticContext)
    {α : Type*} (f : RayCharacter c → α) : (Set.range f).Finite :=
  Set.finite_range f

theorem first_transfer_bilinear_norm_range_finite (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (H L F : ℝ) :
    {v : ℝ | ∃ ξ : RayCharacter c,
      v = ‖firstTransferBilinear c I Φ ξ W H L F‖}.Finite := by
  convert first_transfer_rayCharacter_range_finite c
    (fun ξ => ‖firstTransferBilinear c I Φ ξ W H L F‖) using 1
  ext v
  exact ⟨fun ⟨ξ, hξ⟩ => ⟨ξ, hξ.symm⟩, fun ⟨ξ, hξ⟩ => ⟨ξ, hξ.symm⟩⟩

theorem first_transfer_bilinear_norm_bddAbove (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (H L F : ℝ) :
    BddAbove {v : ℝ | ∃ ξ : RayCharacter c,
      v = ‖firstTransferBilinear c I Φ ξ W H L F‖} :=
  (first_transfer_bilinear_norm_range_finite c I Φ W H L F).bddAbove

theorem first_transfer_bilinear_norm_le_supZero (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (H L F : ℝ) :
    ‖firstTransferBilinear c I Φ ξ W H L F‖ ≤
      QRHLean3.supZero {v : ℝ | ∃ η : RayCharacter c,
        v = ‖firstTransferBilinear c I Φ η W H L F‖} :=
  QRHLean3.le_supZero (first_transfer_bilinear_norm_bddAbove c I Φ W H L F) ⟨ξ, rfl⟩

theorem first_transfer_bilinear_supZero_nonneg (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (H L F : ℝ) :
    0 ≤ QRHLean3.supZero {v : ℝ | ∃ ξ : RayCharacter c,
      v = ‖firstTransferBilinear c I Φ ξ W H L F‖} :=
  QRHLean3.supZero_nonneg (first_transfer_bilinear_norm_bddAbove c I Φ W H L F)

end QRHShort

#print axioms QRHShort.first_transfer_residueAtRayModulus_injective
#print axioms QRHShort.first_transfer_rayCharacter_finite
#print axioms QRHShort.first_transfer_bilinear_norm_bddAbove
#print axioms QRHShort.first_transfer_bilinear_norm_le_supZero
