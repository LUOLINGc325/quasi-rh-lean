import QRHShort.External
import QRHShort.NormLiftSeries
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! The analytic base-change step, with the arithmetic coefficient identities explicit. -/

noncomputable section

namespace QRHShort

theorem HeckeL_eq_dirichlet_product_of_norm_coefficients
    {N M : ℕ} [NeZero N] [NeZero M]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (η : HeckeCharacter)
    (hη : ∀ I : Ideal O, I ≠ ⊥ → η.onIdeal I = χ (I.absNorm : ZMod N))
    (hψ : ∀ p : Nat.Primes, ψ (p : ℕ) =
      χ (p : ℕ) * OAI.ShortDraftHeckeBridge.chiMinusThree (p : ℕ))
    (s : ℂ) (hs : s ≠ 1) :
    HeckeL η s = χ.LFunction s * ψ.LFunction s := by
  have hright (z : ℂ) (hz : 1 < z.re) :
      (OAI.ShortDraftHeckeBridge.baseChangeChar χ).LFunction z = ψ.LFunction z := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hz,
      DirichletCharacter.LFunction_eq_LSeries _ hz]
    have hp (p : Nat.Primes) :
        OAI.ShortDraftHeckeBridge.baseChangeChar χ (p : ℕ) = ψ (p : ℕ) := by
      rw [OAI.ShortDraftHeckeBridge.baseChangeChar_prime_apply χ p.property, hψ p]
    have h := DirichletCharacter.LSeries_eulerProduct_hasProd
      (OAI.ShortDraftHeckeBridge.baseChangeChar χ) hz
    simp_rw [hp] at h
    exact h.unique (DirichletCharacter.LSeries_eulerProduct_hasProd ψ hz)
  have hleft (z : ℂ) (hz : 1 < z.re) :
      HeckeL η z = χ.LFunction z * ψ.LFunction z := by
    have ht (I : Ideal O) : heckeSeriesTerm η z I =
        BaseChangeSeries.normPullback χ (Complex.ne_zero_of_one_lt_re hz) I := by
      by_cases hI : I = ⊥
      · subst I
        simp only [heckeSeriesTerm, if_pos rfl]
        exact (map_zero _).symm
      · rw [heckeSeriesTerm, if_neg hI, hη I hI,
          BaseChangeSeries.normPullback_apply]
        simp only [normIdeal, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
    have hh := HeckeL_hasSum η z hz
    rw [funext ht] at hh
    calc
      _ = ∑' I, BaseChangeSeries.normPullback χ (Complex.ne_zero_of_one_lt_re hz) I :=
        hh.tsum_eq.symm
      _ = χ.LFunction z * (OAI.ShortDraftHeckeBridge.baseChangeChar χ).LFunction z :=
        BaseChangeSeries.norm_sum_eq χ z hz hh.summable.norm
      _ = _ := by rw [hright z hz]
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have hne : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (g := fun z => χ.LFunction z * ψ.LFunction z) ?_ ?_ hpc hne ?_ hs
  · exact (HeckeL_analytic η).mono (fun _ hz => Or.inl hz)
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact ((DirichletCharacter.differentiableAt_LFunction χ z (.inl hz)).mul
      (DirichletCharacter.differentiableAt_LFunction ψ z (.inl hz))).differentiableWithinAt
  · refine Filter.eventually_of_mem ?_ (fun z (hz : 1 < z.re) => hleft z hz)
    exact (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by simp : 1 < (2 : ℂ).re)

end QRHShort

#print axioms QRHShort.HeckeL_eq_dirichlet_product_of_norm_coefficients
