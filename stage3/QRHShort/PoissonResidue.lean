import QRHShort.PoissonAssembly
import QRHShort.CubicGaussEvaluation
import OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

/-!
Residue-class Poisson summation for the frozen complex radial Schwartz hypothesis.
The upstream complex Schwartz theorem supplies both lattice rearrangements;
the lemmas below identify the generator, embedding, measure and radial scale.
No Schwartz extension of the profile to the negative real axis is assumed.
-/

noncomputable section
set_option autoImplicit false
open Classical MeasureTheory
open scoped BigOperators

namespace QRHShort.PoissonProof.Residue

open UniqueFactorizationMonoid
open SquarefreeReflection.RayValuePrerequisites
open ArithmeticProof.CubicGauss
open OAI.ConcreteTraceCRT (eisEmbedding)
open OAI.EisensteinSchwartzPoisson

theorem primaryGenerator_spec_of_coprime {a : Ideal O}
    (ha : IsRelPrime a (principal 3)) : principal (primaryGenerator a) = a := by
  let z := idealGenerator a
  have hz : principal z = a := Ideal.span_singleton_generator a
  have hp : Prime (principal (omega - 1)) :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have ht : principal (omega - 1) ∣ principal 3 :=
    Ideal.dvd_span_singleton.mpr (Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three)
  have hnot : ¬ omega - 1 ∣ z := by
    intro h
    have hd : principal (omega - 1) ∣ a := by
      rw [← hz]
      exact Ideal.dvd_span_singleton.mpr (Ideal.mem_span_singleton.mpr h)
    exact hp.not_isUnit (ha hd ht)
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  have hex : ∃ b : O, principal b = a ∧ IsPrimary b :=
    ⟨(u : O) * z, (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz, hu⟩
  simpa only [primaryGenerator, dif_pos hex] using (Classical.choose_spec hex).1

theorem chosenGenerator_spec {a : Ideal O} (ha : a ≠ ⊥) :
    principal (chosenGenerator a) = a := by
  have hgen (P : Ideal O) :
      principal (if IsRelPrime P (principal 3) then primaryGenerator P
        else idealGenerator P) = P := by
    by_cases hP : IsRelPrime P (principal 3)
    · rw [if_pos hP]
      exact primaryGenerator_spec_of_coprime hP
    · rw [if_neg hP]
      exact Ideal.span_singleton_generator P
  rw [chosenGenerator, if_neg ha, principal, ← Ideal.multiset_prod_span_singleton,
    Multiset.map_map]
  calc
    ((normalizedFactors a).map (fun P =>
        Ideal.span {if IsRelPrime P (principal 3) then primaryGenerator P
          else idealGenerator P})).prod = (normalizedFactors a).prod := by
      congr 1
      simpa only [principal, Multiset.map_id'] using
        (Multiset.map_congr (s := normalizedFactors a) (t := normalizedFactors a)
          rfl (fun P _ => hgen P))
    _ = a := Ideal.prod_normalizedFactors_eq_self ha

theorem chosenGenerator_ne_zero {a : Ideal O} (ha : a ≠ ⊥) :
    chosenGenerator a ≠ 0 := by
  intro hz
  have hg := chosenGenerator_spec ha
  rw [hz] at hg
  exact ha (by simpa [principal] using hg.symm)

theorem normElement_eq (a : O) : normElement a = ‖embedding a‖ ^ 2 := by
  rw [embedding_eq_eisEmbedding]
  exact (OAI.ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span a).symm

theorem additiveCharacter_eq_paperE (z : ℂ) : additiveCharacter z = paperE z :=
  additiveCharacter_eq_breveE z

theorem radialFourier_eq_paperRadialFourier (Φ : ℝ → ℂ) (t : ℝ) :
    radialFourier Φ t = paperRadialFourier Φ t := by
  unfold radialFourier paperRadialFourier paperFourier
  simp only [Algebra.smul_def, Complex.coe_algebraMap, Complex.ofReal_div, Complex.ofReal_ofNat]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [← Complex.sq_norm, additiveCharacter_eq_paperE]
    simp only [neg_mul, mul_comm]

/-- Positive radial dilation preserves the complex Schwartz hypothesis. -/
theorem scaled_radial_schwartz {Φ : ℝ → ℂ} (hΦ : RadialSchwartz Φ)
    {H : ℝ} (hH : 0 < H) :
    ∃ f : SchwartzMap ℂ ℂ, ∀ z : ℂ, f z = Φ (‖z‖ ^ 2 / H) := by
  obtain ⟨f, hf⟩ := hΦ
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (complexMulEquiv (Real.sqrt H : ℂ)⁻¹ (inverseSqrt_ne_zero H hH)) f, ?_⟩
  intro z
  change f ((Real.sqrt H : ℂ)⁻¹ * z) = _
  rw [hf, ← Complex.sq_norm, norm_mul, mul_pow, inverseSqrt_norm_sq H hH]
  congr 1
  ring

/-- The complex Schwartz Poisson formula transported to an arbitrary actual
principal ideal; quotient representatives agree definitionally. -/
theorem periodic_poisson (n : Ideal O) (hn : n ≠ ⊥) (c : O)
    (hc : principal c = n) (f : SchwartzMap ℂ ℂ) (P : O ⧸ n → ℂ) :
    letI : Finite (O ⧸ n) := Ring.HasFiniteQuotients.finiteQuotient hn
    letI : Fintype (O ⧸ n) := Fintype.ofFinite _
    (∑' k : O, P (Ideal.Quotient.mk n k) * f (embedding k)) =
      (normIdeal n : ℂ)⁻¹ * ∑' h : O,
        (∑ x : O ⧸ n, P x * additiveCharacter
          (embedding (residueLift n x) * embedding h / embedding c)) *
        paperFourier f (embedding h / embedding c) := by
  have hc0 : c ≠ 0 := by
    intro h
    apply hn
    rw [← hc, h]
    simp [principal]
  subst n
  have hp := actual_eisenstein_paper_poisson f c hc0 P
  convert hp using 1 <;>
    simp only [embedding_eq_eisEmbedding, additiveCharacter_eq_paperE,
      OAI.GaussianShiftedPartition.representative, residueLift, principal,
      normIdeal, OAI.ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
      Algebra.smul_def, Complex.coe_algebraMap, one_div, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  · apply tsum_congr
    intro k
    rfl
  · congr 1

/-- The frozen endpoint, with no extra analytic or arithmetic premise. -/
theorem residueClassPoisson : ResidueClassPoissonStatement := by
  intro χ Φ H hH hΦ
  obtain ⟨f, hf⟩ := scaled_radial_schwartz hΦ hH
  have hg := chosenGenerator_spec χ.modulus_ne_bot
  have hnorm : ‖embedding (chosenGenerator χ.modulus)‖ ^ 2 =
      normIdeal χ.modulus := by
    rw [← normElement_eq, normElement, hg]
  have hF (u : ℂ) : paperFourier f u =
      (H : ℂ) * radialFourier Φ (H * ‖u‖ ^ 2) := by
    have heq : (f : ℂ → ℂ) = fun z : ℂ => Φ (‖z‖ ^ 2 / H) := funext hf
    rw [heq, paperFourier_radial_scaled Φ H hH,
      radialFourier_eq_paperRadialFourier]
    rfl
  have hp := periodic_poisson χ.modulus χ.modulus_ne_bot
    (chosenGenerator χ.modulus) hg f χ.character
  simp only [hf, ← normElement_eq] at hp
  change (∑' k : O, χ.value k * Φ (normElement k / H)) =
    (normIdeal χ.modulus : ℂ)⁻¹ * ∑' h : O,
      finiteFourier χ h * paperFourier f
        (embedding h / embedding (chosenGenerator χ.modulus)) at hp
  simp_rw [hF, norm_div, div_pow, hnorm, ← normElement_eq, ← mul_div_assoc] at hp
  have hsum : (∑' h : O, finiteFourier χ h *
      ((H : ℂ) * radialFourier Φ (H * normElement h / normIdeal χ.modulus))) =
      (H : ℂ) * ∑' h : O, finiteFourier χ h *
        radialFourier Φ (H * normElement h / normIdeal χ.modulus) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hp, hsum]
  ring

end QRHShort.PoissonProof.Residue

#print axioms QRHShort.PoissonProof.Residue.residueClassPoisson

open Lean Elab Command in
run_cmd do
  let approved : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, ci) in (← getEnv).constants.toList do
    if name.toString.startsWith "QRHShort.PoissonProof.Residue." then
      match ci with
      | .thmInfo _ =>
        checked := checked + 1
        for ax in (← Lean.collectAxioms name) do
          unless approved.contains ax do
            throwError "Unapproved axiom {ax} in {name}"
      | .axiomInfo _ => throwError "Unexpected axiom {name}"
      | _ => pure ()
  logInfo m!"POISSON_RESIDUE_AUDIT_PASS declarations={checked}"
