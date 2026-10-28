import QRHShort.ThetaStatements
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Lean.Util.CollectAxioms

/-!
Reduction of `Manuscript.reflection_step`, paper2.tex:2904--3436.

The finite active/inactive expansion and its uniform coefficient bound are
proved here. Two explicit propositions remain: the theta functional equation
(including convergence and vertical growth), and Mellin inversion/contour
transfer for that equation. Neither proposition is an axiom or an admitted
theorem. The conditional assembly has exactly the frozen reflection conclusion;
it does not complete the manuscript endpoint.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.ReflectionProof

theorem admissible_iff_support_subset (P A : Finset (Ideal O))
    (j : Ideal O → Fin 6) :
    AdmissibleActive P j A ↔ A ⊆ P ∧ P.filter (fun p => (j p).val ≠ 0) ⊆ A := by
  constructor
  · intro h
    exact ⟨h.1, fun p hp => h.2 p (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hp).2⟩
  · rintro ⟨hA, hj⟩
    exact ⟨hA, fun p hp hn => hj (Finset.mem_filter.mpr ⟨hp, hn⟩)⟩

theorem admissible_full (P : Finset (Ideal O)) (j : Ideal O → Fin 6) :
    AdmissibleActive P j P := ⟨Finset.Subset.rfl, fun _ hp _ => hp⟩

theorem admissible_empty_iff (P : Finset (Ideal O)) (j : Ideal O → Fin 6) :
    AdmissibleActive P j ∅ ↔ ∀ p ∈ P, (j p).val = 0 := by
  constructor
  · intro h p hp
    by_contra hj
    exact Finset.notMem_empty p (h.2 p hp hj)
  · intro h
    exact ⟨Finset.empty_subset P, fun p hp hj => (hj (h p hp)).elim⟩

theorem admissible_iff_eq_full (P A : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (hj : ∀ p ∈ P, (j p).val ≠ 0) :
    AdmissibleActive P j A ↔ A = P := by
  constructor
  · intro h
    exact Finset.Subset.antisymm h.1 (fun p hp => h.2 p hp (hj p hp))
  · intro hAP
    subst A
    exact admissible_full P j

/-- The scalar left after selecting active and inactive local terms. -/
def localExpansionCoeff (P A : Finset (Ideal O)) (u v : Ideal O → ℂ) : ℂ :=
  (∏ p ∈ A, u p) * ∏ p ∈ P \ A, v p

theorem localExpansionCoeff_zero_of_not_admissible
    (P A : Finset (Ideal O)) (j : Ideal O → Fin 6) (u v : Ideal O → ℂ)
    (hA : A ⊆ P) (hv : ∀ p ∈ P, (j p).val ≠ 0 → v p = 0)
    (hbad : ¬ AdmissibleActive P j A) : localExpansionCoeff P A u v = 0 := by
  have hex : ∃ p, p ∈ P ∧ (j p).val ≠ 0 ∧ p ∉ A := by
    by_contra h
    apply hbad
    refine ⟨hA, ?_⟩
    intro p hp hj
    by_contra ha
    exact h ⟨p, hp, hj, ha⟩
  obtain ⟨p, hp, hj, ha⟩ := hex
  have hz : (∏ q ∈ P \ A, v q) = 0 :=
    Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hp, ha⟩) (hv p hp hj)
  simp only [localExpansionCoeff, hz, mul_zero]

/-- There are choices only at exponent-zero primes; all other inactive terms
vanish. This is the finite algebra behind the active-set indexing. -/
theorem prod_active_expansion (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (u v : Ideal O → ℂ) (hv : ∀ p ∈ P, (j p).val ≠ 0 → v p = 0) :
    (∏ p ∈ P, (u p + v p)) =
      ∑ A ∈ P.powerset, if AdmissibleActive P j A then
        localExpansionCoeff P A u v else 0 := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : AdmissibleActive P j A
  · simp only [h, if_true, localExpansionCoeff]
  · simpa only [h, if_false, localExpansionCoeff] using
      localExpansionCoeff_zero_of_not_admissible P A j u v
        (Finset.mem_powerset.mp hA) hv h

theorem admissible_count_le (P : Finset (Ideal O)) (j : Ideal O → Fin 6) :
    (P.powerset.filter (AdmissibleActive P j)).card ≤ 2 ^ P.card := by
  simpa only [Finset.card_powerset] using
    Finset.card_filter_le (s := P.powerset) (p := AdmissibleActive P j)

theorem norm_prod_le_one (A : Finset (Ideal O)) (u : Ideal O → ℂ)
    (hu : ∀ p ∈ A, ‖u p‖ ≤ 1) : ‖∏ p ∈ A, u p‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun p _ => norm_nonneg (u p)) hu

theorem norm_localExpansionCoeff_le_one (P A : Finset (Ideal O))
    (u v : Ideal O → ℂ) (hu : ∀ p ∈ A, ‖u p‖ ≤ 1)
    (hv : ∀ p ∈ P \ A, ‖v p‖ ≤ 1) : ‖localExpansionCoeff P A u v‖ ≤ 1 := by
  rw [localExpansionCoeff, norm_mul]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul (norm_prod_le_one A u hu)
      (norm_prod_le_one (P \ A) v hv) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- The bound is independent of the number of varying primes. -/
theorem norm_coefficient_le (P A : Finset (Ideal O)) (u v : Ideal O → ℂ)
    (base : ℂ) (K : ℝ) (hbase : ‖base‖ ≤ K)
    (hu : ∀ p ∈ A, ‖u p‖ ≤ 1) (hv : ∀ p ∈ P \ A, ‖v p‖ ≤ 1) :
    ‖base * localExpansionCoeff P A u v‖ ≤ K := by
  rw [norm_mul]
  calc
    _ ≤ ‖base‖ * 1 := mul_le_mul_of_nonneg_left
      (norm_localExpansionCoeff_le_one P A u v hu hv) (norm_nonneg base)
    _ = ‖base‖ := mul_one _
    _ ≤ K := hbase

theorem coefficients_uniformly_bounded {N : ℕ} (base : Fin N → ℂ)
    (u v : Fin N → Ideal O → ℂ) (P : Finset (Ideal O))
    (j : Ideal O → Fin 6) (K : ℝ) (hbase : ∀ h, ‖base h‖ ≤ K)
    (hu : ∀ h p, p ∈ P → ‖u h p‖ ≤ 1)
    (hv : ∀ h p, p ∈ P → ‖v h p‖ ≤ 1) :
    ∀ h A, AdmissibleActive P j A →
      ‖base h * localExpansionCoeff P A (u h) (v h)‖ ≤ K := by
  intro h A hA
  exact norm_coefficient_le P A (u h) (v h) (base h) K (hbase h)
    (fun p hp => hu h p (hA.1 hp))
    (fun p hp => hv h p (Finset.mem_sdiff.mp hp).1)

theorem reflectionDenominator_ne_zero (d : ReflectionDatum)
    (A : Finset (Ideal O)) (hA : ∀ p ∈ A, primaryGenerator p ≠ 0) :
    reflectionDenominator d A ≠ 0 := by
  exact mul_ne_zero d.denominator_ne_zero (Finset.prod_ne_zero_iff.mpr hA)

/-- The source Dirichlet coefficient in paper2.tex:3285--3298. The pair index
records absolute convergence before interchanging the two ideal sums. -/
def sourceDirichletTerm (c : ArithmeticContext) (Ψ : Ideal O → ℂ)
    (s : ℂ) (nb : Ideal O × Ideal O) : ℂ :=
  if SquarefreeOutside c.S nb.1 ∧ Outside c.S nb.2 then
    star (alpha nb.1) * gauss 2 nb.1 * Ψ nb.1 *
      star (alpha nb.2) ^ (3 : ℕ) * Ψ nb.2 ^ (3 : ℕ) *
      (normIdeal nb.1 : ℂ) ^ (-s) *
      (normIdeal nb.2 : ℂ) ^ (-(3 : ℂ) * s + 1 / 2)
  else 0

/-- Dual Dirichlet modes, before the Mellin weight is inserted. -/
def dualDirichletTerm (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (s : ℂ) (m : O) : ℂ :=
  if m = 0 then 0 else
    let ell := embedding lambda ^ (-4 : ℤ) * embedding m
    cuspCoefficient d.cusp ell * (ell / (‖ell‖ : ℂ)) * d.phase m *
      (∏ p ∈ A, thetaLocalFactor p (j p) m) *
      (Complex.normSq ell : ℂ) ^ (-s)

def dualDirichlet (d : ReflectionDatum) (A : Finset (Ideal O))
    (j : Ideal O → Fin 6) (s : ℂ) : ℂ :=
  ∑' m : O, dualDirichletTerm d A j s m

/-- The gamma factor after absorbing the scalar -i/81 into `coeff`.
The substitution t = 1/2 - s gives exactly `thetaWeight`. -/
def reflectionGammaFactor (s : ℂ) : ℂ :=
  (((2 * Real.pi) ^ (4 : ℕ) / 27 : ℝ) : ℂ) ^ (s - 1 / 2) *
    (Complex.Gamma (4 / 3 - s) * Complex.Gamma (5 / 3 - s) /
      (Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3)))

theorem reflectionGammaFactor_half_sub (t : ℂ) :
    reflectionGammaFactor (1 / 2 - t) =
      (((2 * Real.pi) ^ (4 : ℕ) / 27 : ℝ) : ℂ) ^ (-t) *
        (Complex.Gamma (7 / 6 + t) * Complex.Gamma (5 / 6 + t) /
          (Complex.Gamma (7 / 6 - t) * Complex.Gamma (5 / 6 - t))) := by
  have h0 : (1 / 2 - t) - 1 / 2 = -t := by ring
  have h1 : 4 / 3 - (1 / 2 - t) = 5 / 6 + t := by ring
  have h2 : 5 / 3 - (1 / 2 - t) = 7 / 6 + t := by ring
  have h3 : (1 / 2 - t) + 1 / 3 = 5 / 6 - t := by ring
  have h4 : (1 / 2 - t) + 2 / 3 = 7 / 6 - t := by ring
  simp only [reflectionGammaFactor, h0, h1, h2, h3, h4]
  ring

/-- Polynomial bounds on each closed vertical strip. -/
def StripPolynomialGrowth (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖F s‖ ≤ C * (1 + |s.im|) ^ B

def SourceContinuation (c : ArithmeticContext) (Ψ : Ideal O → ℂ)
    (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
    (∀ s : ℂ, 2 < s.re → HasSum (sourceDirichletTerm c Ψ s) (F s)) ∧
    StripPolynomialGrowth F

def DualDirichletConvergence {N : ℕ} (data : Fin N → ReflectionDatum)
    (P : Finset (Ideal O)) (j : Ideal O → Fin 6) : Prop :=
  ∀ h A, AdmissibleActive P j A → ∀ s : ℂ, 2 < s.re →
    Summable (dualDirichletTerm (data h) A j s)

/-- This equation is asserted only where the dual series converges. Entire
continuation and strip growth supply the other hypotheses for contour transfer.
The half-planes Re(s)>2 and Re(s)<-1 suffice; no boundary convergence is used. -/
def HasReflectionEquation {N : ℕ} (data : Fin N → ReflectionDatum)
    (P : Finset (Ideal O)) (j : Ideal O → Fin 6)
    (coeff : Fin N → Finset (Ideal O) → ℂ) (F : ℂ → ℂ) : Prop :=
  (∀ h A, AdmissibleActive P j A → reflectionDenominator (data h) A ≠ 0) ∧
  ∀ s : ℂ, s.re < -1 → F s = reflectionGammaFactor s *
    ∑ h : Fin N, ∑ A ∈ P.powerset,
      if AdmissibleActive P j A then coeff h A *
        (normElement (reflectionDenominator (data h) A) : ℂ) ^ (1 - 2 * s) *
        dualDirichlet (data h) A j (1 - s)
      else 0

/-- First remaining child: finite Fourier/cusp automorphy and local Gauss
transformation, with the fixed pool and coefficient bound chosen before P,j.
No manuscript endpoint or reflection proposition appears in the conclusion. -/
def ReflectionFunctionalEquationStatement : Prop :=
  ThetaRealizationStatement →
  ∀ (c : ArithmeticContext) (ξ : RayCharacter c),
    ∃ N : ℕ, ∃ data : Fin N → ReflectionDatum, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (P : Finset (Ideal O)) (j : Ideal O → Fin 6), PrimeTwistSet c.S P →
        ∃ coeff : Fin N → Finset (Ideal O) → ℂ,
          (∀ h A, AdmissibleActive P j A → ‖coeff h A‖ ≤ K) ∧
          ∃ F : ℂ → ℂ, SourceContinuation c (productTwist c ξ P j) F ∧
            DualDirichletConvergence data P j ∧ HasReflectionEquation data P j coeff F

/-- Second remaining child: Mellin inversion and the two contour shifts. This
is independent of theta automorphy and concerns an arbitrary source multiplier
and any finite family satisfying the displayed Dirichlet-series equation. -/
def ReflectionMellinTransferStatement : Prop :=
  ∀ (c : ArithmeticContext) (Ψ : Ideal O → ℂ) (N : ℕ)
    (data : Fin N → ReflectionDatum) (P : Finset (Ideal O))
    (j : Ideal O → Fin 6) (coeff : Fin N → Finset (Ideal O) → ℂ) (F : ℂ → ℂ),
    SourceContinuation c Ψ F → DualDirichletConvergence data P j →
    HasReflectionEquation data P j coeff F →
    ∀ (I : SupportInterval) (W : ℝ → ℂ) (X : ℝ), SmoothSupported I W → 0 < X →
      completedSum c Ψ W X =
        ∑ h : Fin N, ∑ A ∈ P.powerset,
          if AdmissibleActive P j A then coeff h A *
            dualThetaSum (data h) A j (fun x => (Real.sqrt x : ℂ) * W x) X
          else 0

theorem reflection_step_of_components
    (hfunctional : ReflectionFunctionalEquationStatement)
    (hmellin : ReflectionMellinTransferStatement)
    (ht : ThetaRealizationStatement) : ReflectionStatement := by
  intro c ξ
  obtain ⟨N, data, K, hK, hf⟩ := hfunctional ht c ξ
  refine ⟨N, data, K, hK, ?_⟩
  intro P j hP
  obtain ⟨coeff, hcoeff, F, hsource, hdual, heq⟩ := hf P j hP
  exact ⟨coeff, hcoeff, hmellin c (productTwist c ξ P j) N data P j coeff F
    hsource hdual heq⟩

end QRHShort.ReflectionProof

#print axioms QRHShort.ReflectionProof.prod_active_expansion
#print axioms QRHShort.ReflectionProof.coefficients_uniformly_bounded
#print axioms QRHShort.ReflectionProof.reflection_step_of_components
