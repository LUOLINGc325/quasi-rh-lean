import QRHShort.PoissonStatements
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Explicit internal obligations for `Manuscript.poisson_step` (paper2.tex:875--936).
The three nonzero-frequency obligations follow the three steps of the paper:
Möbius expansion, Poisson summation on residue classes, and the primitive finite
Fourier transform. They are propositions, not axioms or proved inputs.

The assembly below preserves the frozen `PoissonStatement` verbatim, including
all ideals, the actual `chosenGenerator`, and the normalization of `radialFourier`.
The principal zero-frequency obligation is separate; its existing candidate is
`PoissonZero.lean`. No theorem here claims to close any of these obligations.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.PoissonProof

/-- The finite transform with exactly the representatives and generator used
in `PrimitiveResidueCharacter.gauss`. -/
def finiteFourier (χ : PrimitiveResidueCharacter) (h : O) : ℂ :=
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  ∑ x : O ⧸ χ.modulus, χ.character x *
    additiveCharacter (embedding (residueLift χ.modulus x) * embedding h /
      embedding (chosenGenerator χ.modulus))

/-- Inclusion--exclusion and the change of lattice variable `k = d * l`.
The scale is changed rather than the Schwartz profile. A proof must justify
the finite/infinite interchange from the actual Schwartz hypothesis. -/
def CoprimeExpansionStatement : Prop :=
  ∀ (χ : PrimitiveResidueCharacter) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ),
    r ≠ ⊥ → 0 < H → RadialSchwartz Φ →
    (∑' k : O, if IsRelPrime (principal k) r then
      χ.value k * Φ (normElement k / H) else 0) =
      ∑' d : Ideal O, if d ∣ outsideRadical ∅ r then
        (mobius d : ℂ) * χ.value (chosenGenerator d) *
          ∑' k : O, χ.value k * Φ (normElement k / (H / normIdeal d))
        else 0

/-- Lattice Poisson before evaluating the finite character transform.
This is an obligation over the concrete cyclotomic integer ring, with the
manuscript's measure normalization `2 / sqrt 3`.
The upstream theorem `EisensteinSchwartzPoisson.actual_eisenstein_paper_poisson`
is a candidate input after identifying its embedding and squared norm with
`embedding` and `normElement`, and applying the radial scaling identity.
Use its complex Schwartz formulation: `RadialSchwartz` does not supply a
Schwartz function on the entire real line. -/
def ResidueClassPoissonStatement : Prop :=
  ∀ (χ : PrimitiveResidueCharacter) (Φ : ℝ → ℂ) (H : ℝ),
    0 < H → RadialSchwartz Φ →
    (∑' k : O, χ.value k * Φ (normElement k / H)) =
      (H : ℂ) / (normIdeal χ.modulus : ℂ) *
        ∑' h : O, finiteFourier χ h *
          radialFourier Φ (H * normElement h / normIdeal χ.modulus)

/-- Finite Fourier evaluation at every frequency, including frequencies
which are not units modulo the conductor. Primitivity on units must be used
to prove the nonunit case; the prime-field Gauss identity alone is insufficient. -/
def PrimitiveGaussStatement : Prop :=
  ∀ (χ : PrimitiveResidueCharacter) (h : O),
    finiteFourier χ h =
      (Real.sqrt (normIdeal χ.modulus) : ℂ) * χ.gauss * star (χ.value h)

/-- The principal part of the frozen zero-frequency assertion. -/
def PrincipalZeroStatement : Prop :=
  ∀ (χ : PrimitiveResidueCharacter) (r : Ideal O) (Φ : ℝ → ℂ) (H : ℝ),
    χ.character = 1 → χ.modulus = ⊤ → r ≠ ⊥ → 0 < H → RadialSchwartz Φ →
      poissonZeroTerm χ r Φ H = H * radialFourier Φ 0 *
        ∏ P ∈ primeFactors r, (1 - (normIdeal P : ℂ)⁻¹)

/-- Intermediate conclusion with no coprimality exclusion. -/
def PrimitivePoissonStatement : Prop :=
  ∀ (χ : PrimitiveResidueCharacter) (Φ : ℝ → ℂ) (H : ℝ),
    0 < H → RadialSchwartz Φ →
    (∑' k : O, χ.value k * Φ (normElement k / H)) =
      H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) *
        ∑' h : O, star (χ.value h) *
          radialFourier Φ (H * normElement h / normIdeal χ.modulus)

theorem normIdeal_pos {d : Ideal O} (hd : d ≠ ⊥) : 0 < normIdeal d := by
  have hn : d.absNorm ≠ 0 := fun h => hd (Ideal.absNorm_eq_zero_iff.mp h)
  change 0 < (d.absNorm : ℝ)
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem radical_ne_bot (r : Ideal O) : outsideRadical ∅ r ≠ ⊥ := by
  change (∏ P ∈ (primeFactors r).filter (fun P => P ∉ ∅), P) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero

theorem divisor_norm_pos {r d : Ideal O} (hd : d ∣ outsideRadical ∅ r) :
    0 < normIdeal d :=
  normIdeal_pos (ne_zero_of_dvd_ne_zero (radical_ne_bot r) hd)

/-- The normalization at frequency one follows directly from the definition,
with no primitive-character or lattice-Poisson input. -/
theorem finiteFourier_one (χ : PrimitiveResidueCharacter) :
    finiteFourier χ 1 = (Real.sqrt (normIdeal χ.modulus) : ℂ) * χ.gauss := by
  have hs : (Real.sqrt (normIdeal χ.modulus) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (normIdeal_pos χ.modulus_ne_bot))
  have he : embedding (1 : O) = 1 := by simp [embedding]
  dsimp only [finiteFourier, PrimitiveResidueCharacter.gauss]
  simp only [he, mul_one, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- This split makes the genuinely primitive, nonunit part explicit. -/
theorem primitiveGauss_of_unit_nonunit
    (hu : ∀ (χ : PrimitiveResidueCharacter) (h : O),
      IsUnit (Ideal.Quotient.mk χ.modulus h) →
      finiteFourier χ h = finiteFourier χ 1 * star (χ.value h))
    (hn : ∀ (χ : PrimitiveResidueCharacter) (h : O),
      ¬ IsUnit (Ideal.Quotient.mk χ.modulus h) → finiteFourier χ h = 0) :
    PrimitiveGaussStatement := by
  intro χ h
  by_cases hh : IsUnit (Ideal.Quotient.mk χ.modulus h)
  · rw [hu χ h hh, finiteFourier_one]
  · have hv : χ.value h = 0 := χ.character.map_nonunit hh
    rw [hn χ h hh, hv, star_zero, mul_zero]

/-- The nonprincipal zero-frequency assertion is independent of Poisson
summation, also when the quotient ring is a subsingleton. -/
theorem nonprincipal_zero (χ : PrimitiveResidueCharacter)
    (hχ : χ.character ≠ 1) : star (χ.value 0) = 0 := by
  rcases subsingleton_or_nontrivial (O ⧸ χ.modulus) with hsub | hnontrivial
  · have heq : χ.character = 1 := by
      ext x
      have hx : x = (1 : O ⧸ χ.modulus) := @Subsingleton.elim _ hsub x 1
      simp only [hx, map_one]
    exact (hχ heq).elim
  · letI := hnontrivial
    simp [PrimitiveResidueCharacter.value, MulChar.map_zero]

theorem poissonZero_of_principal (hz : PrincipalZeroStatement) : PoissonZeroStatement :=
  ⟨nonprincipal_zero, hz⟩

/-- Collapse the finite Fourier coefficients and the square-root normalization.
The operations on `tsum` here are exact identities in the complete field `ℂ`. -/
theorem primitivePoisson_of_residue_gauss
    (hl : ResidueClassPoissonStatement) (hg : PrimitiveGaussStatement) :
    PrimitivePoissonStatement := by
  intro χ Φ H hH hΦ
  have hn := normIdeal_pos χ.modulus_ne_bot
  have hs : (Real.sqrt (normIdeal χ.modulus) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hn)
  have hsq : (Real.sqrt (normIdeal χ.modulus) : ℂ) ^ 2 =
      (normIdeal χ.modulus : ℂ) := by
    exact_mod_cast Real.sq_sqrt hn.le
  have hcoef : (H : ℂ) / (normIdeal χ.modulus : ℂ) *
      ((Real.sqrt (normIdeal χ.modulus) : ℂ) * χ.gauss) =
      H * χ.gauss / (Real.sqrt (normIdeal χ.modulus) : ℂ) := by
    rw [← hsq]
    field_simp [hs]
  have hsum : (∑' h : O, finiteFourier χ h *
      radialFourier Φ (H * normElement h / normIdeal χ.modulus)) =
      ((Real.sqrt (normIdeal χ.modulus) : ℂ) * χ.gauss) *
        ∑' h : O, star (χ.value h) *
          radialFourier Φ (H * normElement h / normIdeal χ.modulus) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    rw [hg χ h]
    ring
  rw [hl χ Φ H hH hΦ, hsum, ← mul_assoc, hcoef]

/-- Reinsert the coprimality exclusion at the exact frozen scale. -/
theorem poisson_of_coprime_primitive
    (hc : CoprimeExpansionStatement) (hp : PrimitivePoissonStatement) :
    PoissonStatement := by
  intro χ r Φ H hr hH hΦ
  rw [hc χ r Φ H hr hH hΦ]
  conv_rhs => rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  by_cases hd : d ∣ outsideRadical ∅ r
  · simp only [if_pos hd]
    rw [hp χ Φ (H / normIdeal d) (div_pos hH (divisor_norm_pos hd)) hΦ]
    have hscale (h : O) : H / normIdeal d * normElement h / normIdeal χ.modulus =
        H * normElement h / (normIdeal d * normIdeal χ.modulus) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    simp_rw [hscale]
    push_cast
    ring
  · simp only [if_neg hd, mul_zero]

/-- The full nonzero-frequency conclusion, conditional on precisely the
three smaller internal proof obligations above. -/
theorem poisson_of_components (hc : CoprimeExpansionStatement)
    (hl : ResidueClassPoissonStatement) (hg : PrimitiveGaussStatement) :
    PoissonStatement :=
  poisson_of_coprime_primitive hc (primitivePoisson_of_residue_gauss hl hg)

/-- A conditional assembly of the frozen node, not a proof of its inputs.
`ArithmeticStatement` is retained explicitly as the original upstream premise. -/
theorem poisson_step_of_components (_ha : ArithmeticStatement)
    (hc : CoprimeExpansionStatement) (hl : ResidueClassPoissonStatement)
    (hg : PrimitiveGaussStatement) (hz : PrincipalZeroStatement) :
    PoissonStatement ∧ PoissonZeroStatement :=
  ⟨poisson_of_components hc hl hg, poissonZero_of_principal hz⟩

end QRHShort.PoissonProof
