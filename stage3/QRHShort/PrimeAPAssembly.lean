import QRHShort.MainStatements
import Mathlib.NumberTheory.Chebyshev

/-!
Internal decomposition of `Manuscript.primes_ap_step`.

The four propositions `ZeroFreeTwistedStep`, `CharacterOrthogonalityStep`,
`LargeModulusPsiEstimate`, and `PartialSummationStep` below are UNPROVED
interfaces, not axioms. The conditional assembly takes their proofs explicitly.
In particular the existing qualitative PNT for each fixed modulus does not
supply the absolute constant required here. No manuscript endpoint is changed.
-/

noncomputable section
open Classical Finset
open scoped BigOperators

namespace QRHShort.PrimeAP

/-- The inclusive Mangoldt sum in one residue class. -/
def psi (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊,
    if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0

/-- The inclusive prime logarithm sum in the same residue class. -/
def theta (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊,
    if Nat.Prime n ∧ n % q = a % q then Real.log n else 0

def twistedPsi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n

/-- Includes imprimitive characters. The principal main term is `x`. -/
def TwistedMangoldtEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x → (q : ℝ) ≤ x →
      ‖twistedPsi χ x - if χ = 1 then (x : ℂ) else 0‖ ≤
        C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2

def SmallModulusPsiEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (q a : ℕ),
    2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → Nat.Coprime a q →
      |psi x q a - x / (Nat.totient q : ℝ)| ≤
        C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2

/-- Needed because Abel summation also samples `t < q`, even if `q ≤ x`. -/
def LargeModulusPsiEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (q a : ℕ),
    2 ≤ x → 1 ≤ q → x < (q : ℝ) → Nat.Coprime a q →
      |psi x q a - x / (Nat.totient q : ℝ)| ≤
        C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2

def PsiEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (q a : ℕ),
    2 ≤ x → 1 ≤ q → Nat.Coprime a q →
      |psi x q a - x / (Nat.totient q : ℝ)| ≤
        C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2

def ThetaEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (q a : ℕ),
    2 ≤ x → 1 ≤ q → Nat.Coprime a q →
      |theta x q a - x / (Nat.totient q : ℝ)| ≤
        C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2

/-- Same count, lower integration endpoint, and quantifiers as the frozen goal;
only the witness constant is real rather than natural. -/
def CountEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (q a : ℕ),
    2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → Nat.Coprime a q →
      |(primeAPCount x q a : ℝ) -
        (Nat.totient q : ℝ)⁻¹ * ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹| ≤
          C * x ^ ((11 : ℝ) / 12) * Real.log x

/-- Unproved analytic child: uniform quantitative explicit formula, including
zero counting and the treatment of imprimitive Euler factors. -/
def ZeroFreeTwistedStep : Prop :=
  DirichletZeroFreeStatement → TwistedMangoldtEstimate

/-- Unproved finite Fourier child: the number of characters cancels `φ(q)`.
This must retain the constant's independence of both `q` and `a`. -/
def CharacterOrthogonalityStep : Prop :=
  TwistedMangoldtEstimate → SmallModulusPsiEstimate

/-- Unproved calculus child: use `prime_count_partial_summation` below and
bound the error integral; the boundary contribution at 2 must be retained. -/
def PartialSummationStep : Prop := ThetaEstimate → CountEstimate

theorem psi_estimate_of_small_large
    (hs : SmallModulusPsiEstimate) (hl : LargeModulusPsiEstimate) : PsiEstimate := by
  obtain ⟨Cs, hCs, hs⟩ := hs
  obtain ⟨Cl, hCl, hl⟩ := hl
  refine ⟨max Cs Cl, le_trans hCs (le_max_left _ _), ?_⟩
  intro x q a hx hq ha
  have hx0 : 0 ≤ x := by linarith
  rcases le_or_gt (q : ℝ) x with hsmall | hlarge
  · calc
      _ ≤ Cs * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := hs x q a hx hq hsmall ha
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Cs Cl) (Real.rpow_nonneg hx0 _))
        (sq_nonneg _)
  · calc
      _ ≤ Cl * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := hl x q a hx hq hlarge ha
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right Cs Cl) (Real.rpow_nonneg hx0 _))
        (sq_nonneg _)

theorem psi_sub_theta_nonneg (x : ℝ) (q a : ℕ) : 0 ≤ psi x q a - theta x q a := by
  unfold psi theta
  rw [← sum_sub_distrib]
  refine sum_nonneg fun n _ => ?_
  by_cases hr : n % q = a % q
  · by_cases hp : Nat.Prime n
    · simp [hr, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simpa [hr, hp] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · simp [hr]

/-- Removing prime powers in a progression costs no more than removing them
from the complete set of natural numbers. -/
theorem psi_sub_theta_le_global (x : ℝ) (q a : ℕ) :
    psi x q a - theta x q a ≤ Chebyshev.psi x - Chebyshev.theta x := by
  rw [psi, theta, ← sum_sub_distrib, Chebyshev.psi_eq_sum_Icc,
    Chebyshev.theta_eq_sum_Icc, sum_filter, ← sum_sub_distrib]
  refine sum_le_sum fun n _ => ?_
  by_cases hr : n % q = a % q
  · simp [hr]
  · by_cases hp : Nat.Prime n
    · simp [hr, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simpa [hr, hp] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))

theorem abs_psi_sub_theta_le (x : ℝ) (q a : ℕ) (hx : 1 ≤ x) :
    |psi x q a - theta x q a| ≤ 2 * Real.sqrt x * Real.log x := by
  rw [abs_of_nonneg (psi_sub_theta_nonneg x q a)]
  exact (psi_sub_theta_le_global x q a).trans
    ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx))

theorem prime_power_error_absorbed (x : ℝ) (hx : 2 ≤ x) :
    2 * Real.sqrt x * Real.log x ≤
      (2 / Real.log 2) * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogx : 0 ≤ Real.log x := le_trans hlog2.le hlog
  have hx0 : 0 ≤ x := by linarith
  have hsqrt : Real.sqrt x ≤ x ^ ((11 : ℝ) / 12) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  calc
    _ ≤ 2 * x ^ ((11 : ℝ) / 12) * Real.log x := by gcongr
    _ = (2 / Real.log 2) * x ^ ((11 : ℝ) / 12) *
        (Real.log 2 * Real.log x) := by field_simp <;> ring
    _ ≤ _ := by gcongr <;> nlinarith

theorem theta_estimate_of_psi (h : PsiEstimate) : ThetaEstimate := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C + 2 / Real.log 2, add_nonneg hC (by positivity), ?_⟩
  intro x q a hx hq ha
  calc
    |theta x q a - x / (Nat.totient q : ℝ)| =
        |(psi x q a - x / (Nat.totient q : ℝ)) - (psi x q a - theta x q a)| := by
          congr 1; ring
    _ ≤ |psi x q a - x / (Nat.totient q : ℝ)| + |psi x q a - theta x q a| :=
      abs_sub _ _
    _ ≤ C * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 +
        (2 / Real.log 2) * x ^ ((11 : ℝ) / 12) * (Real.log x) ^ 2 :=
      add_le_add (h x q a hx hq ha)
        ((abs_psi_sub_theta_le x q a (by linarith)).trans (prime_power_error_absorbed x hx))
    _ = _ := by ring

/-- Exact Abel summation for the actual frozen counting function, including
the prime 2. It is valid for every modulus and residue, even non-coprime ones. -/
theorem prime_count_partial_summation (x : ℝ) (q a : ℕ) (hx : 2 ≤ x) :
    (primeAPCount x q a : ℝ) = theta x q a / Real.log x +
      ∫ t in (2 : ℝ)..x, theta t q a / (t * (Real.log t) ^ 2) := by
  unfold primeAPCount
  rw [card_eq_sum_ones, Nat.range_succ_eq_Icc_zero, sum_filter]
  push_cast
  let c : ℕ → ℝ := fun n =>
    if Nat.Prime n ∧ n % q = a % q then Real.log n else 0
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * c n
  · refine sum_congr rfl fun n _ => ?_
    by_cases hn : Nat.Prime n ∧ n % q = a % q
    · have hlog : Real.log (n : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hn.1.pos)
          (by exact_mod_cast hn.1.ne_one)
      simp [c, hn, hlog]
    · simp [c, hn]
  rw [sum_mul_eq_sub_integral_mul₁ c (f := fun t => (Real.log t)⁻¹)
    (by simp [c]) (by simp [c]), ← intervalIntegral.integral_of_le hx]
  · have hderiv (f : ℝ → ℝ) :
        (∫ u in (2 : ℝ)..x, deriv (fun t => (Real.log t)⁻¹) u * f u) =
        ∫ u in (2 : ℝ)..x, f u * -(u * (Real.log u) ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by simp [field]
    rw [hderiv]
    simp only [c, theta, mul_neg, neg_mul, intervalIntegral.integral_neg,
      sub_neg_eq_add, div_eq_mul_inv, mul_comm]
  · intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hzlog : Real.log z ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z hz => ContinuousWithinAt.congr ?_
      (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hzlog : (Real.log z) ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_) <;> linarith [hz.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)

theorem primeAPStatement_of_countEstimate (h : CountEstimate) : PrimeAPStatement := by
  obtain ⟨C, _, h⟩ := h
  obtain ⟨N, hN⟩ := exists_nat_ge C
  refine ⟨N, ?_⟩
  intro x q a hx hq hqx ha
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  calc
    _ ≤ C * x ^ ((11 : ℝ) / 12) * Real.log x := h x q a hx hq hqx ha
    _ ≤ _ := by gcongr

/-- The four explicit child premises are the complete remaining obligations.
The original `MainStatement` enters only through its Dirichlet component. -/
theorem primes_ap_step_of_children (hz : ZeroFreeTwistedStep)
    (ho : CharacterOrthogonalityStep) (hl : LargeModulusPsiEstimate)
    (hp : PartialSummationStep) (hm : MainStatement) : PrimeAPStatement :=
  primeAPStatement_of_countEstimate
    (hp (theta_estimate_of_psi (psi_estimate_of_small_large (ho (hz hm.2)) hl)))

end QRHShort.PrimeAP

#print axioms QRHShort.PrimeAP.psi_estimate_of_small_large
#print axioms QRHShort.PrimeAP.psi_sub_theta_nonneg
#print axioms QRHShort.PrimeAP.psi_sub_theta_le_global
#print axioms QRHShort.PrimeAP.abs_psi_sub_theta_le
#print axioms QRHShort.PrimeAP.prime_power_error_absorbed
#print axioms QRHShort.PrimeAP.theta_estimate_of_psi
#print axioms QRHShort.PrimeAP.prime_count_partial_summation
#print axioms QRHShort.PrimeAP.primeAPStatement_of_countEstimate
#print axioms QRHShort.PrimeAP.primes_ap_step_of_children
