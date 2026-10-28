import QRHShort.Arithmetic
import QRHLean3.Supremum
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Concrete sums and uniformity conventions of the 11/12 manuscript.
Every infinite sum here has a separate finite-support or summability obligation in
the corresponding analytic proof. A totalized `tsum` is not used as a convergence proof. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

structure SupportInterval where
  lo : ℝ
  hi : ℝ
  lo_pos : 0 < lo
  ordered : lo ≤ hi

def SmoothSupported (I : SupportInterval) (W : ℝ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧ Function.support W ⊆ Set.Icc I.lo I.hi

def weightNorm (J : ℕ) (W : ℝ → ℂ) : ℝ :=
  QRHLean3.supZero {r | ∃ j : ℕ, j ≤ J ∧ ∃ x : ℝ, r = ‖iteratedDeriv j W x‖}

def enlarged (I : SupportInterval) : SupportInterval where
  lo := I.lo / 16
  hi := 4 * I.hi
  lo_pos := div_pos I.lo_pos (by norm_num)
  ordered := by nlinarith [I.lo_pos, I.ordered]

def halfEnlarged (I : SupportInterval) : SupportInterval where
  lo := I.lo / 2
  hi := 2 * I.hi
  lo_pos := div_pos I.lo_pos (by norm_num)
  ordered := by nlinarith [I.lo_pos, I.ordered]

def originalSum (c : ArithmeticContext) (W : ℝ → ℂ) (D : ℝ) (u : O) : ℂ :=
  ∑' n : Ideal O, if Outside c.S n then
    (mobius n : ℂ) * c.nu.onIdeal n * sexticSymbol n u * W (normIdeal n / D)
  else 0

def originalMeanSquare (c : ArithmeticContext) (W : ℝ → ℂ) (D H : ℝ) : ℝ :=
  ∑' u : O, if 0 < normElement u ∧ normElement u ≤ H then
    ‖originalSum c W D u‖ ^ 2 else 0

def columnSum (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (X : ℝ) (k : O) (f : Ideal O) : ℂ :=
  ∑' n : Ideal O, if SquarefreeOutside c.S n then
    coefficient ξ.val n * sexticSymbol n k *
      sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / X)
  else 0

def excludedColumnSum (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (r : Ideal O) (X : ℝ) (k : O) (f : Ideal O) : ℂ :=
  ∑' n : Ideal O, if SquarefreeOutside c.S n ∧ IsRelPrime n r then
    coefficient ξ.val n * sexticSymbol n k *
      sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) * W (normIdeal n / X)
  else 0

def rowEnergy (column : O → ℂ) (H : ℝ) : ℝ :=
  ∑' k : O, if 0 < normElement k ∧ normElement k ≤ H then ‖column k‖ ^ 2 else 0

def energy (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (H X F : ℝ) : ℝ :=
  (X * F)⁻¹ * ∑' f : Ideal O,
    if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
      rowEnergy (fun k => columnSum c ξ W X k f) H else 0

def excludedEnergy (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (r : Ideal O) (H X F : ℝ) : ℝ :=
  (X * F)⁻¹ * ∑' f : Ideal O,
    if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
      rowEnergy (fun k => excludedColumnSum c ξ W r X k f) H else 0

def completedTwist (c : ArithmeticContext) (ξ : RayCharacter c) (k : O)
    (f n : Ideal O) : ℂ :=
  if Outside c.S n then rayValue ξ.val n * sexticSymbol n k *
    sexticSymbol n (primaryGenerator f) ^ (4 : ℕ) else 0

/-- Equation (T), including the cube variable and the weight V_*(y)=sqrt(y) W(y). -/
def completedSum (c : ArithmeticContext) (Ψ : Ideal O → ℂ) (W : ℝ → ℂ)
    (X : ℝ) : ℂ :=
  ∑' n : Ideal O, if SquarefreeOutside c.S n then
    ∑' b : Ideal O, if Outside c.S b then
      (star (alpha n) * gauss 2 n * Ψ n * star (alpha b) ^ (3 : ℕ) * Ψ b ^ (3 : ℕ)) /
        ((Real.sqrt (normIdeal n) : ℂ) * (normIdeal b : ℂ)) *
        ((Real.sqrt (normIdeal n * normIdeal b ^ (3 : ℕ) / X) : ℂ) *
          W (normIdeal n * normIdeal b ^ (3 : ℕ) / X))
    else 0
  else 0

def completedRow (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (X : ℝ) (k : O) (f : Ideal O) : ℂ :=
  completedSum c (completedTwist c ξ k f) W X

/-- The auxiliary element in the squarefree-row lemma may meet S, including 3. -/
def completedTwistElement (c : ArithmeticContext) (ξ : RayCharacter c)
    (k g : O) (n : Ideal O) : ℂ :=
  if Outside c.S n then rayValue ξ.val n * sexticSymbol n k *
    sexticSymbol n g ^ (4 : ℕ) else 0

def completedRowElement (c : ArithmeticContext) (ξ : RayCharacter c) (W : ℝ → ℂ)
    (X : ℝ) (k g : O) : ℂ :=
  completedSum c (completedTwistElement c ξ k g) W X

def smoothedEnergy (c : ArithmeticContext) (ξ : RayCharacter c) (Φ : ℝ → ℝ)
    (W : ℝ → ℂ) (H L F : ℝ) : ℝ :=
  (L * F)⁻¹ * ∑' f : Ideal O,
    if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
      ∑' k : O, Φ (normElement k / H) * ‖columnSum c ξ W L k f‖ ^ 2
    else 0

def childValues (c : ArithmeticContext) (I : SupportInterval) (m : ℕ)
    (H L F Sigma : ℝ) : Set ℝ :=
  {v | ∃ H' X' F' : ℝ, ∃ ξ' : RayCharacter c, ∃ U : ℝ → ℂ,
    1 ≤ H' ∧ 1 ≤ X' ∧ 1 ≤ F' ∧ H' ≤ H * L / (Sigma * F) ∧
    H' / (X' * F') ≤ H / Sigma ∧ X' * F' ≤ L ∧
    SmoothSupported (enlarged I) U ∧ weightNorm m U ≤ 1 ∧
    v = energy c ξ' U H' X' F' / (X' * F')}

def childSup (c : ArithmeticContext) (I : SupportInterval) (m : ℕ)
    (H L F Sigma : ℝ) : ℝ := QRHLean3.supZero (childValues c I m H L F Sigma)

end QRHShort
