import QRHShort.FirstTransferKernelRegularity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
A globally smooth extension of the Fourier amplitude, equal to the literal
amplitude on the support box.  Compactness bounds all its derivatives uniformly
in the square-root frequency parameter, before the test weight is chosen.
-/

noncomputable section
open scoped ContDiff

namespace QRHShort

/-- A positive smooth replacement for a coordinate, equal to it above `I.lo`. -/
def firstTransferPositiveCoordinate (I : SupportInterval) (x : ℝ) : ℝ :=
  I.lo / 2 + (x - I.lo / 2) *
    Real.smoothTransition ((x - I.lo / 2) / (I.lo / 2))

theorem first_transfer_positiveCoordinate_pos (I : SupportInterval) (x : ℝ) :
    0 < firstTransferPositiveCoordinate I x := by
  have hlo : 0 < I.lo / 2 := half_pos I.lo_pos
  unfold firstTransferPositiveCoordinate
  by_cases hx : x - I.lo / 2 ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hlo.le)]
    simpa using hlo
  · exact add_pos_of_pos_of_nonneg hlo
      (mul_nonneg (le_of_lt (lt_of_not_ge hx)) (Real.smoothTransition.nonneg _))

theorem first_transfer_positiveCoordinate_eq (I : SupportInterval) {x : ℝ}
    (hx : I.lo ≤ x) : firstTransferPositiveCoordinate I x = x := by
  unfold firstTransferPositiveCoordinate
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · apply (one_le_div (half_pos I.lo_pos)).2
    linarith

theorem first_transfer_positiveCoordinate_contDiff (I : SupportInterval) :
    ContDiff ℝ ∞ (firstTransferPositiveCoordinate I) := by
  unfold firstTransferPositiveCoordinate
  apply contDiff_const.add
  apply (contDiff_id.sub contDiff_const).mul
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- This amplitude agrees with the kernel's non-weight factor on the box. -/
def firstTransferAmplitude (I : SupportInterval) (Φ : RowWeight) (b : ℝ)
    (z : BoxSpace 2) : ℂ :=
  (Real.sqrt (firstTransferPositiveCoordinate I (z 0) *
    firstTransferPositiveCoordinate I (z 1)) : ℂ)⁻¹ *
  firstTransferFourierProfile Φ (b / Real.sqrt
    (firstTransferPositiveCoordinate I (z 0) * firstTransferPositiveCoordinate I (z 1)))

theorem first_transfer_amplitude_joint_contDiff (I : SupportInterval) (Φ : RowWeight) :
    ContDiff ℝ ∞ (fun p : ℝ × BoxSpace 2 => firstTransferAmplitude I Φ p.1 p.2) := by
  have hp0 : ContDiff ℝ ∞
      (fun p : ℝ × BoxSpace 2 => firstTransferPositiveCoordinate I (p.2 0)) :=
    (first_transfer_positiveCoordinate_contDiff I).comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd)
  have hp1 : ContDiff ℝ ∞
      (fun p : ℝ × BoxSpace 2 => firstTransferPositiveCoordinate I (p.2 1)) :=
    (first_transfer_positiveCoordinate_contDiff I).comp
      ((contDiff_apply ℝ ℝ 1).comp contDiff_snd)
  have hpos : ∀ p : ℝ × BoxSpace 2,
      0 < firstTransferPositiveCoordinate I (p.2 0) *
        firstTransferPositiveCoordinate I (p.2 1) := fun p =>
    mul_pos (first_transfer_positiveCoordinate_pos I _) (first_transfer_positiveCoordinate_pos I _)
  have hbase := (hp0.mul hp1).sqrt (fun p => ne_of_gt (hpos p))
  have hroot : ∀ p : ℝ × BoxSpace 2,
      Real.sqrt (firstTransferPositiveCoordinate I (p.2 0) *
        firstTransferPositiveCoordinate I (p.2 1)) ≠ 0 := fun p =>
    ne_of_gt (Real.sqrt_pos.mpr (hpos p))
  have hcomplex : ContDiff ℝ ∞ (fun p : ℝ × BoxSpace 2 =>
      (Real.sqrt (firstTransferPositiveCoordinate I (p.2 0) *
        firstTransferPositiveCoordinate I (p.2 1)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hbase
  have hinv := hcomplex.inv (fun p => by exact_mod_cast hroot p)
  exact hinv.mul ((first_transfer_fourierProfile_contDiff Φ).comp
    (contDiff_fst.div hbase hroot))

theorem first_transfer_amplitude_contDiff (I : SupportInterval) (Φ : RowWeight) (b : ℝ) :
    ContDiff ℝ ∞ (firstTransferAmplitude I Φ b) := by
  have hpair : ContDiff ℝ ∞ (fun z : BoxSpace 2 => (b, z)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using (first_transfer_amplitude_joint_contDiff I Φ).comp hpair

/-- Differentiating a parameter slice restricts the joint derivative to a
linear isometric inclusion, so its operator norm can only decrease. -/
theorem first_transfer_norm_iteratedFDeriv_slice_le
    (F : ℝ × BoxSpace 2 → ℂ) (hF : ContDiff ℝ ∞ F) (b : ℝ) (z : BoxSpace 2) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => F (b, y)) z‖ ≤ ‖iteratedFDeriv ℝ j F (b, z)‖ := by
  let L : BoxSpace 2 →L[ℝ] ℝ × BoxSpace 2 := ContinuousLinearMap.inr ℝ ℝ (BoxSpace 2)
  have hg : ContDiff ℝ ∞ (fun p : ℝ × BoxSpace 2 => F ((b, 0) + p)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have heq : (fun y => F (b, y)) = (fun p : ℝ × BoxSpace 2 => F ((b, 0) + p)) ∘ L := by
    funext y
    simp [L]
  rw [heq, L.iteratedFDeriv_comp_right hg z (by simp),
    iteratedFDeriv_comp_add_left]
  have hpoint : (b, (0 : BoxSpace 2)) + L z = (b, z) := by
    ext <;> simp [L]
  rw [hpoint]
  have hnorm : ‖L‖ = 1 := ContinuousLinearMap.norm_inr ℝ ℝ (BoxSpace 2)
  simpa only [hnorm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ j F (b, z)).norm_compContinuousLinearMap_le (fun _ => L)

/-- The bound depends on the fixed interval, row weight, order and compact
parameter interval only; it is independent of the eventual test weight. -/
theorem first_transfer_amplitude_uniform_bound (I : SupportInterval) (Φ : RowWeight)
    (q : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ), b ∈ Set.Icc 0 B →
      ∀ z ∈ Set.Icc (fun _ : Fin 2 => I.lo) (fun _ : Fin 2 => I.hi),
        ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℝ j (firstTransferAmplitude I Φ b) z‖ ≤ C := by
  let F : ℝ × BoxSpace 2 → ℂ := fun p => firstTransferAmplitude I Φ p.1 p.2
  have hF : ContDiff ℝ ∞ F := first_transfer_amplitude_joint_contDiff I Φ
  have hcompact : IsCompact (Set.Icc (0 : ℝ) B ×ˢ
      Set.Icc (fun _ : Fin 2 => I.lo) (fun _ : Fin 2 => I.hi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ), b ∈ Set.Icc 0 B →
      ∀ z ∈ Set.Icc (fun _ : Fin 2 => I.lo) (fun _ : Fin 2 => I.hi),
        ‖iteratedFDeriv ℝ j (firstTransferAmplitude I Φ b) z‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
      (hF.continuous_iteratedFDeriv (by simp)).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun b hb z hz => ?_⟩
    exact (first_transfer_norm_iteratedFDeriv_slice_le F hF b z j).trans
      ((hC (b, z) ⟨hb, hz⟩).trans (le_max_left _ _))
  induction q with
  | zero =>
    obtain ⟨C, hC, hboundC⟩ := hbound 0
    refine ⟨C, hC, fun b hb z hz j hj => ?_⟩
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact hboundC b hb z hz
  | succ q ih =>
    obtain ⟨C, hC, hboundC⟩ := ih
    obtain ⟨D, hD, hboundD⟩ := hbound (q + 1)
    refine ⟨max C D, hC.trans (le_max_left _ _), fun b hb z hz j hj => ?_⟩
    by_cases hjq : j ≤ q
    · exact (hboundC b hb z hz j hjq).trans (le_max_left _ _)
    · have hjeq : j = q + 1 := by omega
      subst j
      exact (hboundD b hb z hz).trans (le_max_right _ _)

/-- The global smooth extension reproduces the literal kernel because both
coordinate weights vanish whenever the positive replacement can differ. -/
theorem first_transfer_kernel_eq_amplitude (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (a : ℝ) (hW : SmoothSupported I W) (ha : 0 ≤ a) :
    firstTransferKernel Φ W a = fun z =>
      firstTransferAmplitude I Φ (Real.sqrt a) z * W (z 0) * star (W (z 1)) := by
  funext z
  by_cases h0 : W (z 0) = 0
  · simp [firstTransferKernel, h0]
  by_cases h1 : W (z 1) = 0
  · simp [firstTransferKernel, h1]
  have hz0 : I.lo ≤ z 0 := (hW.2 h0).1
  have hz1 : I.lo ≤ z 1 := (hW.2 h1).1
  simp only [firstTransferKernel, firstTransferAmplitude,
    first_transfer_positiveCoordinate_eq I hz0, first_transfer_positiveCoordinate_eq I hz1,
    first_transfer_radialFourier_eq_profile, Real.sqrt_div ha]
  ring

end QRHShort
