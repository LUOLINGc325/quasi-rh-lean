import QRHShort.MellinTermwise
import QRHShort.AnalyticIdentity
import QRHShort.ActualEulerFactors
import QRHShort.IdealMobiusEuler
import Mathlib.Analysis.Complex.Convex

/-!
The identity-principle conclusion of paper2.tex:728--757. The reciprocal-series
identity in Re(s)>1 is proved by ideal Möbius cancellation and the finite Euler
factor calculation; no internal analytic identity is introduced as an axiom.
-/

noncomputable section
open scoped Topology
open Classical Set Filter

namespace QRHShort

/-- The half-plane of interest with the possible principal pole removed. -/
def puncturedQRHHalfPlane : Set ℂ := {s | (11 : ℝ) / 12 < s.re ∧ s ≠ 1}

theorem puncturedQRHHalfPlane_isPreconnected : IsPreconnected puncturedQRHHalfPlane := by
  let A : Set ℂ := {z | (11 : ℝ) / 12 < z.re ∧ 0 < z.im}
  let B : Set ℂ := {z | (11 : ℝ) / 12 < z.re ∧ z.im < 0}
  let C : Set ℂ := {z | (11 : ℝ) / 12 < z.re ∧ z.re < 1}
  let D : Set ℂ := {z | 1 < z.re}
  have hA : IsPreconnected A :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)).isPreconnected
  have hB : IsPreconnected B :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _)).isPreconnected
  have hC : IsPreconnected C :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
  have hD : IsPreconnected D := (convex_halfSpace_re_gt _).isPreconnected
  have hAC : IsPreconnected (A ∪ C) :=
    IsPreconnected.union' ⟨(23 / 24 : ℂ) + Complex.I, by norm_num [A, C]⟩ hA hC
  have hACD : IsPreconnected ((A ∪ C) ∪ D) :=
    IsPreconnected.union' ⟨(2 : ℂ) + Complex.I, by norm_num [A, C, D]⟩ hAC hD
  have hall : IsPreconnected (((A ∪ C) ∪ D) ∪ B) :=
    IsPreconnected.union' ⟨(2 : ℂ) - Complex.I, by norm_num [A, B, C, D]⟩ hACD hB
  have heq : (((A ∪ C) ∪ D) ∪ B) = puncturedQRHHalfPlane := by
    ext z
    change (((_ ∧ _) ∨ (_ ∧ _)) ∨ _) ∨ (_ ∧ _) ↔ _ ∧ _
    constructor
    · rintro (((⟨hr, hi⟩ | ⟨hr, hr1⟩) | hr1) | ⟨hr, hi⟩)
      · exact ⟨hr, fun hz => by simpa [hz] using hi⟩
      · exact ⟨hr, fun hz => by simpa [hz] using hr1⟩
      · have hr1' : 1 < z.re := by simpa [D] using hr1
        refine ⟨by linarith, fun hz => ?_⟩
        simpa [hz] using hr1'
      · exact ⟨hr, fun hz => by simpa [hz] using hi⟩
    · rintro ⟨hr, hne⟩
      rcases lt_trichotomy z.im 0 with hi | hi | hi
      · exact Or.inr ⟨hr, hi⟩
      · rcases lt_trichotomy z.re 1 with hr1 | hr1 | hr1
        · exact Or.inl (Or.inl (Or.inr ⟨hr, hr1⟩))
        · exact (hne (Complex.ext (by simpa using hr1) (by simpa using hi))).elim
        · exact Or.inl (Or.inr hr1)
      · exact Or.inl (Or.inl (Or.inl ⟨hr, hi⟩))
  exact heq ▸ hall

/-- The initial reciprocal identity for the actual ideal series. -/
def HeckeReciprocalIdentity : Prop :=
  ∀ (c : ArithmeticContext) (s : ℂ), 1 < s.re →
    HeckeL c.nu s * omittedEulerProduct c s * mobiusSeries c s = 1

theorem hecke_reciprocal_identity : HeckeReciprocalIdentity := by
  intro c s hs
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    heckeL_mul_mobiusSeries_mul_omittedEulerProduct c s hs

/-- The actual Mellin integral supplies the analytic product identity near 2. -/
theorem hecke_mellin_product_eventually (hrec : HeckeReciprocalIdentity)
    (c : ArithmeticContext) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) :
    (fun s => HeckeL c.nu s * omittedEulerProduct c s * mobiusMellin c W s)
      =ᶠ[𝓝 (2 : ℂ)] mellin W := by
  have hnhds : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hnhds] with s hs
  rw [mobiusMellin_eq_mellin_mul_series c hW s hs]
  calc
    _ = (HeckeL c.nu s * omittedEulerProduct c s * mobiusSeries c s) * mellin W s := by ring
    _ = mellin W s := by rw [hrec c s hs, one_mul]

/-- Pointwise cancellation and the explicit reciprocal-series identity imply
the complete Hecke part of the main theorem, including nonprincipal s=1. -/
theorem heckeZeroFree_of_pointwise_of_reciprocal (hp : PointwiseMobiusEstimate)
    (hrec : HeckeReciprocalIdentity) : HeckeZeroFreeStatement := by
  intro χ s hs hpole
  obtain ⟨I, W, hW, hnonzero⟩ := exists_smoothSupported_mellin_ne_zero s
  let c := χ.context
  have hF := omittedEulerProduct_analytic c
  have hM := mobiusMellin_analyticOnNhd hp c I hW
  have hG := hW.mellin_analyticOnNhd
  have hlocal := hecke_mellin_product_eventually hrec c hW
  by_cases hχ : χ.residue = 1
  · have hsne : s ≠ 1 := hpole.resolve_right (not_ne_iff.mpr hχ)
    apply heckeL_ne_zero_of_analytic_product χ
      (U := puncturedQRHHalfPlane) (F := omittedEulerProduct c)
      (M := mobiusMellin c W) (G := mellin W)
      (fun _ hz => Or.inl hz.2) (hF.mono (subset_univ _))
      (hM.mono (fun _ hz => hz.1)) (hG.mono (subset_univ _))
      puncturedQRHHalfPlane_isPreconnected (z₀ := 2)
      (by norm_num [puncturedQRHHalfPlane]) hlocal ⟨hs, hsne⟩ hnonzero
  · apply heckeL_ne_zero_of_analytic_product χ
      (U := {z : ℂ | (11 : ℝ) / 12 < z.re}) (F := omittedEulerProduct c)
      (M := mobiusMellin c W) (G := mellin W)
      (fun _ _ => Or.inr hχ) (hF.mono (subset_univ _)) hM
      (hG.mono (subset_univ _)) (convex_halfSpace_re_gt _).isPreconnected
      (z₀ := 2) (by norm_num) hlocal hs hnonzero

/-- The complete Hecke conclusion, conditional only on the pointwise estimate. -/
theorem heckeZeroFree_of_pointwise (hp : PointwiseMobiusEstimate) :
    HeckeZeroFreeStatement :=
  heckeZeroFree_of_pointwise_of_reciprocal hp hecke_reciprocal_identity

end QRHShort
