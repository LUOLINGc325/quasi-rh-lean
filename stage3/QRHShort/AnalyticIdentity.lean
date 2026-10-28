import QRHShort.External
import Mathlib.Analysis.Analytic.Uniqueness

/-!
The identity-principle step in paper2.tex:750--757. Analyticity of the Mellin
integral and its transform, and their initial product identity, are explicit
inputs. No Mellin formula or nonvanishing assertion is introduced as an axiom.

The general result works on any preconnected set on whose neighbourhood the
functions are analytic, so in particular on a preconnected open domain. The
Hecke specialization restricts to the actual continuation domain and excludes
the totalized principal-character value at the possible pole.
-/

noncomputable section
open scoped Topology

namespace QRHShort

/-- A local identity between analytic products extends along a preconnected
domain. `F` may be the finite product of omitted Euler factors. -/
theorem analytic_product_identity {U : Set ℂ} {L F M G : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U) (hF : AnalyticOnNhd ℂ F U)
    (hM : AnalyticOnNhd ℂ M U) (hG : AnalyticOnNhd ℂ G U)
    (hU : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hlocal : (fun z => L z * F z * M z) =ᶠ[𝓝 z₀] G) :
    Set.EqOn (fun z => L z * F z * M z) G U :=
  ((hL.mul hF).mul hM).eqOn_of_preconnected_of_eventuallyEq hG hU hz₀ hlocal

/-- A nonzero product value forces its first factor to be nonzero. No
nonvanishing of the other two factors is required for this implication. -/
theorem left_factor_ne_zero_of_product_eq {l f m g : ℂ}
    (hproduct : l * f * m = g) (hg : g ≠ 0) : l ≠ 0 := by
  intro hl
  apply hg
  simpa only [hl, zero_mul] using hproduct.symm

/-- The identity principle followed by evaluation at a nonzero transform. -/
theorem analytic_left_factor_ne_zero {U : Set ℂ} {L F M G : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U) (hF : AnalyticOnNhd ℂ F U)
    (hM : AnalyticOnNhd ℂ M U) (hG : AnalyticOnNhd ℂ G U)
    (hU : IsPreconnected U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hlocal : (fun z => L z * F z * M z) =ᶠ[𝓝 z₀] G)
    {z : ℂ} (hz : z ∈ U) (hGz : G z ≠ 0) : L z ≠ 0 :=
  left_factor_ne_zero_of_product_eq
    (analytic_product_identity hL hF hM hG hU hz₀ hlocal hz) hGz

/-- Apply the identity principle to the selected continuation of the actual
ideal Dirichlet series. Mellin analyticity and the initial identity remain
explicit hypotheses. -/
theorem hecke_product_identity (χ : HeckeCharacter) {U : Set ℂ} {F M G : ℂ → ℂ}
    (hcontinuation : U ⊆ {s : ℂ | s ≠ 1 ∨ χ.residue ≠ 1})
    (hF : AnalyticOnNhd ℂ F U) (hM : AnalyticOnNhd ℂ M U)
    (hG : AnalyticOnNhd ℂ G U) (hU : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hlocal : (fun z => HeckeL χ z * F z * M z) =ᶠ[𝓝 z₀] G) :
    Set.EqOn (fun z => HeckeL χ z * F z * M z) G U :=
  analytic_product_identity ((HeckeL_analytic χ).mono hcontinuation)
    hF hM hG hU hz₀ hlocal

/-- Nonvanishing of the Mellin transform at a point rules out a zero of the
actual Hecke L-function there. The point must belong to the analytic domain;
the principal-character pole is never assigned analytic meaning. -/
theorem heckeL_ne_zero_of_analytic_product (χ : HeckeCharacter)
    {U : Set ℂ} {F M G : ℂ → ℂ}
    (hcontinuation : U ⊆ {s : ℂ | s ≠ 1 ∨ χ.residue ≠ 1})
    (hF : AnalyticOnNhd ℂ F U) (hM : AnalyticOnNhd ℂ M U)
    (hG : AnalyticOnNhd ℂ G U) (hU : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hlocal : (fun z => HeckeL χ z * F z * M z) =ᶠ[𝓝 z₀] G)
    {z : ℂ} (hz : z ∈ U) (hGz : G z ≠ 0) : HeckeL χ z ≠ 0 :=
  left_factor_ne_zero_of_product_eq
    (hecke_product_identity χ hcontinuation hF hM hG hU hz₀ hlocal hz) hGz

end QRHShort
