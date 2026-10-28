import OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities
import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-! Absolute-convergence bridge from the ideal norm series to quadratic base change. -/

open scoped BigOperators
open Classical
open Complex
open OAI.CompletedGauss (MulFiber mulFiber_moebius_sum)
open OAI.ShortDraftHeckeBridge

#print axioms OAI.CompletedGauss.mulFiber_moebius_sum
#print axioms OAI.ShortDraftHeckeBridge.baseChangeChar_prime_apply
#print axioms OAI.ShortDraftHeckeBridge.chiMinusThree_mod_two

namespace QRHShort.BaseChangeSeries

local notation "O" => OAI.ShortDraftHeckeBridge.O

private theorem norm_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  by_cases hI : Squarefree I
  · simp [UniqueFactorizationMonoid.moebius, hI]
  · simp [UniqueFactorizationMonoid.moebius, hI]

private theorem inverse_summable_norm (f : Ideal O →*₀ ℂ)
    (hf : Summable (fun I => ‖f I‖)) :
    Summable (fun I => ‖(UniqueFactorizationMonoid.moebius I : ℂ) * f I‖) := by
  apply hf.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_le_one I)

private theorem inverse_mul_sum (f : Ideal O →*₀ ℂ)
    (hf : Summable (fun I => ‖f I‖)) :
    (∑' I, (UniqueFactorizationMonoid.moebius I : ℂ) * f I) * (∑' I, f I) = 1 := by
  let F : Ideal O × Ideal O → ℂ :=
    fun p => (UniqueFactorizationMonoid.moebius p.1 : ℂ) * f (p.1 * p.2)
  have hi := inverse_summable_norm f hf
  have hprod := hi.mul_norm hf
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.1) = if B = 1 then 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.1 = 0 := by
        simp only [F, p.2, map_zero, mul_zero]
      simp only [hz, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.1.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.2])
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B
            simp only [map_one, one_mul]
          · exact zero_mul _
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.1) (∑' p, F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p, F p) = 1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O,
        ((UniqueFactorizationMonoid.moebius p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm hi hf
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = 1 := hFone

noncomputable def normPullback {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 0) : Ideal O →*₀ ℂ :=
  (dirichletSummandHom χ hs).comp Ideal.absNorm

theorem normPullback_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 0) (I : Ideal O) :
    normPullback χ hs I = χ (I.absNorm : ZMod q) * (I.absNorm : ℂ) ^ (-s) := rfl

private theorem normFiber_tsum (a : Ideal O → ℂ) (n : ℕ) :
    (∑' I : {I : Ideal O // I.absNorm = n}, a I.val) = normFiberCoeff a n := by
  let : Fintype {I : Ideal O // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := O) n).fintype
  rw [tsum_fintype]
  symm
  exact Finset.sum_subtype _ (by intro I; simp) a

private theorem inverse_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 0)
    (hf : Summable (fun I => ‖normPullback χ hs I‖)) :
    (∑' I, (UniqueFactorizationMonoid.moebius I : ℂ) * normPullback χ hs I) =
      LSeries (normFiberCoeff (baseChangeWeight χ)) s := by
  have hfiber (n : ℕ) :
      (∑' I : {I : Ideal O // I.absNorm = n},
        (UniqueFactorizationMonoid.moebius I.val : ℂ) * normPullback χ hs I.val) =
        LSeries.term (normFiberCoeff (baseChangeWeight χ)) s n := by
    by_cases hn : n = 0
    · subst n
      have hz (I : {I : Ideal O // I.absNorm = 0}) : normPullback χ hs I.val = 0 := by
        have hI : I.val = 0 := Ideal.absNorm_eq_zero_iff.mp I.property
        simp only [hI, map_zero]
      simp only [hz, mul_zero, tsum_zero, LSeries.term_zero]
    · calc
        _ = ∑' I : {I : Ideal O // I.absNorm = n},
            baseChangeWeight χ I.val * (n : ℂ) ^ (-s) := by
          apply tsum_congr
          intro I
          rw [normPullback_apply]
          simp only [baseChangeWeight, I.property, mul_assoc]
        _ = _ := by
          rw [tsum_mul_right, normFiber_tsum, LSeries.term_of_ne_zero hn,
            Complex.cpow_neg, div_eq_mul_inv]
  have hh := (inverse_summable_norm _ hf).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // I.absNorm = n},
    (UniqueFactorizationMonoid.moebius I.val : ℂ) * normPullback χ hs I.val) _ at hh
  simp_rw [hfiber] at hh
  exact hh.tsum_eq.symm

theorem norm_sum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re)
    (hf : Summable (fun I => ‖normPullback χ (ne_zero_of_one_lt_re hs) I‖)) :
    (∑' I, normPullback χ (ne_zero_of_one_lt_re hs) I) =
      χ.LFunction s * (baseChangeChar χ).LFunction s := by
  let f := normPullback χ (ne_zero_of_one_lt_re hs)
  let M := ∑' I, (UniqueFactorizationMonoid.moebius I : ℂ) * f I
  have hleft : M * (∑' I, f I) = 1 := inverse_mul_sum f hf
  have hM : M = LSeries (pairInverseCoeff χ (baseChangeChar χ)) s := by
    exact (inverse_eq_LSeries χ _ hf).trans
      (normFiber_LSeries_eq_pair_inverse χ (baseChangeChar χ) (baseChangeWeight χ)
        (fun n hn => normFiberCoeff_baseChange_eq_pairInverseCoeff χ n hn) s)
  have hright : χ.LFunction s * (baseChangeChar χ).LFunction s * M = 1 := by
    rw [hM]
    exact pair_inverse_euler_identity χ (baseChangeChar χ) s hs
  have hne : M ≠ 0 := by
    intro h
    rw [h, zero_mul] at hleft
    exact zero_ne_one hleft
  apply mul_left_cancel₀ hne
  change M * (∑' I, f I) = _
  rw [hleft, mul_comm M]
  exact hright.symm

end QRHShort.BaseChangeSeries

#print axioms QRHShort.BaseChangeSeries.norm_sum_eq
