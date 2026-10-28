import QRHShort.HeckeContinuationBridge
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
The explicit external inputs used by the 11/12 manuscript.

All three former literature inputs are discharged by the imported OAI bridges
and the closed assemblies in this tree; this file retains only their shared
definitions and compatibility lemmas.
-/

noncomputable section

namespace QRHShort

/-- **External input 1 (Hecke analytic continuation).**
E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur
Verteilung der Primzahlen. Zweite Mitteilung*, Math. Z. 6 (1920), 11–51,
https://doi.org/10.1007/BF01202991 ; original scan:
https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0006/LOG_0008.pdf .
Section 6, p. 30, (29) defines the ideal series for `Re s > 1` and (31)
reduces imprimitive characters by a finite Euler product. The continuation
and its principal-character exception are the Hauptsatz on pp. 34–35,
following (40)–(44); the ordinary principal zeta case is explicitly included
as the previously known case on p. 34. This second paper treats general
number fields, including imaginary quadratic fields; the 1918 first paper
alone is not the appropriate source for this specialization.

This is only the finite-order, trivial-infinity-type specialization over the
fixed field `K`. Imprimitive characters are allowed. Nonvanishing at 1 is
deliberately not included in this continuation input. -/
theorem hecke_continuation (χ : HeckeCharacter) :
    ∃ L : ℂ → ℂ, HeckeContinuationSpec χ L :=
  HeckeContinuationBridge.hecke_continuation_from_oai χ

/-- A selected analytic continuation of the actual ideal Dirichlet series. -/
def HeckeL (χ : HeckeCharacter) : ℂ → ℂ :=
  Classical.choose (hecke_continuation χ)

theorem HeckeL_spec (χ : HeckeCharacter) : HeckeContinuationSpec χ (HeckeL χ) :=
  Classical.choose_spec (hecke_continuation χ)

theorem HeckeL_hasSum (χ : HeckeCharacter) (s : ℂ) (hs : 1 < s.re) :
    HasSum (heckeSeriesTerm χ s) (HeckeL χ s) :=
  (HeckeL_spec χ).1 s hs

theorem HeckeL_analytic (χ : HeckeCharacter) :
    AnalyticOnNhd ℂ (HeckeL χ) {s : ℂ | s ≠ 1 ∨ χ.residue ≠ 1} :=
  (HeckeL_spec χ).2

/-- The finite dyadic prime-ideal set, allowing removal of any fixed finite
set of ideals. `Nat.card` does not require a selected enumeration. -/
def DyadicPrimeIdeals (S : Finset (Ideal O)) (Y : ℝ) :=
  {P : Ideal O // Prime P ∧ Y / 2 < normIdeal P ∧ normIdeal P ≤ Y ∧ P ∉ S}

/- The Landau and Goldmakher--Louvel interfaces formerly declared here are
replaced by the closed OAI bridges in `APDyadicBridge` and
`QuadraticGLAssembly`; no unresolved external axiom remains in this module. -/

end QRHShort
