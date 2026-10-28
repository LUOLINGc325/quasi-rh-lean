import QRHShort.PrimeComparison
import QRHShort.External
import QRHShort.EulerFactors

/-!
The actual finite Euler factors at the primes omitted by an arithmetic context.
Their entireness and nonvanishing use the ideal norms and the given finite-order
Hecke character. No identity with an infinite Euler product is assumed here.
-/

noncomputable section
open scoped BigOperators

namespace QRHShort

/-- The factors omitted from the Hecke series at the finite exceptional set. -/
def omittedEulerProduct (c : ArithmeticContext) (s : ℂ) : ℂ :=
  ∏ P ∈ c.S, (1 - c.nu.onIdeal P * (normIdeal P : ℂ) ^ (-s))

/-- Every nonzero prime ideal has absolute norm at least two. -/
theorem two_le_absNorm_of_prime {P : Ideal O} (hP : Prime P) : 2 ≤ P.absNorm := by
  have h0 : P.absNorm ≠ 0 := fun h => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : P.absNorm ≠ 1 := fun h =>
    (Ideal.isPrime_of_prime hP).ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- Restoring the finite exceptional Euler factors creates no zero for Re s > 0. -/
theorem omittedEulerProduct_ne_zero (c : ArithmeticContext) {s : ℂ} (hs : 0 < s.re) :
    omittedEulerProduct c s ≠ 0 := by
  simpa only [omittedEulerProduct, normIdeal, Complex.ofReal_natCast] using
    finite_euler_product_ne_zero c.S (fun P => P.absNorm) c.nu.onIdeal
      (fun P hP => two_le_absNorm_of_prime (c.prime_S P hP))
      (fun P _ => c.nu.norm_onIdeal_le_one P) hs

/-- The actual exceptional Euler product is analytic on the whole complex plane. -/
theorem omittedEulerProduct_analytic (c : ArithmeticContext) :
    AnalyticOnNhd ℂ (omittedEulerProduct c) Set.univ := by
  let h := finite_euler_product_analytic c.S (fun P => P.absNorm) c.nu.onIdeal
    (fun P hP => lt_of_lt_of_le (by decide : 0 < 2)
      (two_le_absNorm_of_prime (c.prime_S P hP)))
  change AnalyticOnNhd ℂ
    (fun s : ℂ => ∏ P ∈ c.S,
      (1 - c.nu.onIdeal P * (normIdeal P : ℂ) ^ (-s))) Set.univ
  simpa only [normIdeal, Complex.ofReal_natCast] using h

/-- The actual exceptional Euler product is complex differentiable everywhere. -/
theorem omittedEulerProduct_differentiable (c : ArithmeticContext) :
    Differentiable ℂ (omittedEulerProduct c) :=
  fun s => (omittedEulerProduct_analytic c s (Set.mem_univ s)).differentiableAt

end QRHShort
