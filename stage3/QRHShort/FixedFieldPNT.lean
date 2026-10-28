import QRHShort.LandauBridge
import QRHShort.LinearMassAbsorb

/-!
Fixed-field input boundary for the Landau bridge.

The analytic statement is intentionally a parameter: it is the dyadic
prime-log mass lower bound that a fixed-field PNT would provide.  Everything
after this boundary is elementary and uses only the finite-sum log-mass
estimate from `LandauBridge`.
-/

noncomputable section
open Classical

namespace QRHShort

/-- Fixed-field dyadic prime-log mass input, with enough additive slack to
survive deleting an arbitrary finite set of ideals. -/
def FixedFieldDyadicPrimeMassLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 ≤ A →
    ∃ Y₀ : ℝ, 1 < Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      A * Real.log Y + c * Y ≤ dyadicPrimeLogMass (∅ : Finset (Ideal O)) Y

/-- A positive linear lower bound for the undeleted dyadic prime mass is
enough for `FixedFieldDyadicPrimeMassLowerBound`: the generic real-variable
lemma absorbs each prescribed `A * log Y` term. -/
theorem fixedFieldDyadicPrimeMassLowerBound_of_linear
    (hlinear : GenericMass.LinearMassLowerBound
      (dyadicPrimeLogMass (∅ : Finset (Ideal O)))) :
    FixedFieldDyadicPrimeMassLowerBound := by
  obtain ⟨c, hc, hmass⟩ :=
    GenericMass.logMassLowerBound_of_linear hlinear
  exact ⟨c, hc, hmass⟩

/-- The fixed-field prime-log mass input implies the global interval-counting
interface consumed by finite deletion. -/
theorem globalPrimeIdealDyadicLowerBound_of_fixedFieldMass
    (hinput : FixedFieldDyadicPrimeMassLowerBound) :
    GlobalPrimeIdealDyadicLowerBound := by
  obtain ⟨c, hc, hmass⟩ := hinput
  refine ⟨c, hc, ?_⟩
  intro A hA
  obtain ⟨Y₀, hY₀, hcount⟩ := hmass A hA
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y hY
  have hlog : 0 < Real.log Y := Real.log_pos (hY₀.trans_le hY)
  have hcard := dyadicPrime_card_lower_of_log_mass (S := (∅ : Finset (Ideal O)))
    (Y := Y) (M := A * Real.log Y + c * Y) (hY₀.trans_le hY) (hcount Y hY)
  have hrewrite :
      A + c * Y / Real.log Y = (A * Real.log Y + c * Y) / Real.log Y := by
    field_simp
  rw [hrewrite]
  simpa only [allDyadicPrimeFinset] using hcard

end QRHShort

