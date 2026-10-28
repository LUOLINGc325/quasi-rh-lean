import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Scalar bookkeeping for S10 `paper2.tex:1333–1355,1490–1512,1520–1608`,
source revision 1581d4cbdd69. Analytic cube/transfer inequalities remain
explicit hypotheses; these definitions do not assert them for arithmetic energy.
-/
namespace QRHLean3

/-- Supremum with the paper's empty-family convention for nonnegative energies.
Adding zero also makes the upper-bound lemmas valid for signed families. -/
noncomputable def supZero (s : Set ℝ) : ℝ := sSup (insert 0 s)

/-- `cubeOrder δ` is the cube-reduction derivative order at exponent δ.
Fixed κ,C₀ are implicit in this function; it is independent of D and I. -/
noncomputable def derivativeOrder (cubeOrder : ℝ → ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 1
  | j + 1, ε => max (cubeOrder (ε / 3)) (4 * derivativeOrder cubeOrder j (ε / 3) + 12)

end QRHLean3
