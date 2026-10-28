import QRHShort.SecondTransferKernelFourier
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
def secondTransferPositiveCoordinate (I : SupportInterval) (x : ℝ) : ℝ :=
  I.lo / 2 + (x - I.lo / 2) *
    Real.smoothTransition ((x - I.lo / 2) / (I.lo / 2))

theorem second_transfer_positiveCoordinate_pos (I : SupportInterval) (x : ℝ) :
    0 < secondTransferPositiveCoordinate I x := by
  have hlo : 0 < I.lo / 2 := half_pos I.lo_pos
  unfold secondTransferPositiveCoordinate
  by_cases hx : x - I.lo / 2 ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hlo.le)]
    simpa using hlo
  · exact add_pos_of_pos_of_nonneg hlo
      (mul_nonneg (le_of_lt (lt_of_not_ge hx)) (Real.smoothTransition.nonneg _))

theorem second_transfer_positiveCoordinate_eq (I : SupportInterval) {x : ℝ}
    (hx : I.lo ≤ x) : secondTransferPositiveCoordinate I x = x := by
  unfold secondTransferPositiveCoordinate
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · apply (one_le_div (half_pos I.lo_pos)).2
    linarith

theorem second_transfer_positiveCoordinate_contDiff (I : SupportInterval) :
    ContDiff ℝ ∞ (secondTransferPositiveCoordinate I) := by
  unfold secondTransferPositiveCoordinate
  apply contDiff_const.add
  apply (contDiff_id.sub contDiff_const).mul
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- This amplitude agrees with the kernel's non-weight factor on the box. -/
def secondTransferAmplitude (I : SupportInterval) (Φ : RowWeight) (b : ℝ)
    (z : BoxSpace 2) : ℂ :=
  (Real.sqrt (secondTransferPositiveCoordinate I (z 0) *
    secondTransferPositiveCoordinate I (z 1)) : ℂ)⁻¹ *
  secondTransferFourierProfile Φ (b / Real.sqrt
    (secondTransferPositiveCoordinate I (z 0) * secondTransferPositiveCoordinate I (z 1)))

theorem second_transfer_amplitude_joint_contDiff (I : SupportInterval) (Φ : RowWeight) :
    ContDiff ℝ ∞ (fun p : ℝ × BoxSpace 2 => secondTransferAmplitude I Φ p.1 p.2) := by
  have hp0 : ContDiff ℝ ∞
      (fun p : ℝ × BoxSpace 2 => secondTransferPositiveCoordinate I (p.2 0)) :=
    (second_transfer_positiveCoordinate_contDiff I).comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd)
  have hp1 : ContDiff ℝ ∞
      (fun p : ℝ × BoxSpace 2 => secondTransferPositiveCoordinate I (p.2 1)) :=
    (second_transfer_positiveCoordinate_contDiff I).comp
      ((contDiff_apply ℝ ℝ 1).comp contDiff_snd)
  have hpos : ∀ p : ℝ × BoxSpace 2,
      0 < secondTransferPositiveCoordinate I (p.2 0) *
        secondTransferPositiveCoordinate I (p.2 1) := fun p =>
    mul_pos (second_transfer_positiveCoordinate_pos I _) (second_transfer_positiveCoordinate_pos I _)
  have hbase := (hp0.mul hp1).sqrt (fun p => ne_of_gt (hpos p))
  have hroot : ∀ p : ℝ × BoxSpace 2,
      Real.sqrt (secondTransferPositiveCoordinate I (p.2 0) *
        secondTransferPositiveCoordinate I (p.2 1)) ≠ 0 := fun p =>
    ne_of_gt (Real.sqrt_pos.mpr (hpos p))
  have hcomplex : ContDiff ℝ ∞ (fun p : ℝ × BoxSpace 2 =>
      (Real.sqrt (secondTransferPositiveCoordinate I (p.2 0) *
        secondTransferPositiveCoordinate I (p.2 1)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hbase
  have hinv := hcomplex.inv (fun p => by exact_mod_cast hroot p)
  exact hinv.mul ((second_transfer_fourierProfile_contDiff Φ).comp
    (contDiff_fst.div hbase hroot))

theorem second_transfer_amplitude_contDiff (I : SupportInterval) (Φ : RowWeight) (b : ℝ) :
    ContDiff ℝ ∞ (secondTransferAmplitude I Φ b) := by
  have hpair : ContDiff ℝ ∞ (fun z : BoxSpace 2 => (b, z)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using (second_transfer_amplitude_joint_contDiff I Φ).comp hpair

/-- Differentiating a parameter slice restricts the joint derivative to a
linear isometric inclusion, so its operator norm can only decrease. -/
theorem second_transfer_norm_iteratedFDeriv_slice_le
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
theorem second_transfer_amplitude_uniform_bound (I : SupportInterval) (Φ : RowWeight)
    (q : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ), b ∈ Set.Icc 0 B →
      ∀ z ∈ Set.Icc (fun _ : Fin 2 => I.lo) (fun _ : Fin 2 => I.hi),
        ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℝ j (secondTransferAmplitude I Φ b) z‖ ≤ C := by
  let F : ℝ × BoxSpace 2 → ℂ := fun p => secondTransferAmplitude I Φ p.1 p.2
  have hF : ContDiff ℝ ∞ F := second_transfer_amplitude_joint_contDiff I Φ
  have hcompact : IsCompact (Set.Icc (0 : ℝ) B ×ˢ
      Set.Icc (fun _ : Fin 2 => I.lo) (fun _ : Fin 2 => I.hi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ), b ∈ Set.Icc 0 B →
      ∀ z ∈ Set.Icc (fun _ : Fin 2 => I.lo) (fun _ : Fin 2 => I.hi),
        ‖iteratedFDeriv ℝ j (secondTransferAmplitude I Φ b) z‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
      (hF.continuous_iteratedFDeriv (by simp)).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun b hb z hz => ?_⟩
    exact (second_transfer_norm_iteratedFDeriv_slice_le F hF b z j).trans
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

end QRHShort
