import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Algebraic parameters in paper2.tex, §4, equations `positive-gap`,
`cube-cutoff`, and `transfer-scales` (source revision 1581d4cbdd69).
The real variable `b` denotes the norm N(b) of a nonzero integral ideal.
The only arithmetic property used here is `1 ≤ b`.
The paper assumes ambient `D ≥ 2` (paper2.tex:198) and `C₀ ≥ 1`
(paper2.tex:1262). The algebraic power comparisons need only `D ≥ 1`,
and these parameter lemmas do not need the lower bound on `C₀`.
These structures record hypotheses; they do not postulate analytic estimates.
-/

namespace QRH

/-- The canonical cap and positive gap (paper2.tex:1263–1266).
With the separately supplied `1 ≤ D` and `0 < κ`, the gap implies `H ≤ X * F`;
the lower bounds then also give `H, X, F ≤ D ^ C` individually. -/
structure ParentRange (D κ C H X F : ℝ) : Prop where
  H_one_le : 1 ≤ H
  X_one_le : 1 ≤ X
  F_one_le : 1 ≤ F
  product_le : X * F ≤ D ^ C
  gap : H ≤ (X * F) * D ^ (-κ)

/-- The algebraic conditions in the cube-reduction supremum (paper2.tex:1337–1350).
For `1 ≤ H` and `1 ≤ X`, the cutoff equation already forces `0 ≤ hc`;
the explicit field records the intended nonnegative real cutoff. -/
structure LongBranch (H X hc b : ℝ) : Prop where
  hc_nonneg : 0 ≤ hc
  b_one_le : 1 ≤ b
  cutoff : hc ^ 3 = min X (X ^ 2 / H ^ 2)
  above_cutoff : hc < b
  column_gt_one : 1 < X / b ^ 3

structure TransferBounds (H X F b H' X' F' : ℝ) : Prop where
  H_one_le : 1 ≤ H'
  X_one_le : 1 ≤ X'
  F_one_le : 1 ≤ F'
  row_le : H' ≤ H * (X / b ^ 3) / ((X * F) * F)
  ratio_le : H' / (X' * F') ≤ H / (X * F)
  product_le : X' * F' ≤ X / b ^ 3

end QRH
