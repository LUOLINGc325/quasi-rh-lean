import QRHShort.FirstTransferFiniteModelExpansion
import Mathlib.Data.Fintype.EquivFin

/-!
A finite presentation of the literal first-transfer expression. Rows and the
common column window are chosen before the test. The weight of each row is the
norm of its explicit arithmetic coefficient; no divisor estimate is asserted.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_tsum_eq_sum_fin {α β : Type*} [NormedAddCommGroup β]
    (s : Finset α) (f : α → β)
    (hf : Function.support f ⊆ (s : Set α)) :
    ∑' a, f a = ∑ i : Fin s.card, f (s.equivFin.symm i) := by
  calc
    ∑' a, f a = ∑' a : (s : Set α), f a :=
      (tsum_subtype_eq_of_support_subset hf).symm
    _ = ∑ a : s, f a := tsum_fintype _
    _ = _ := (s.equivFin.symm.sum_comp (fun a : s => f a)).symm

theorem first_transfer_pair_tsum_eq_sum_fin {α : Type*} (s : Finset α)
    (f : α × α → ℂ) (hf : Function.support f ⊆ (s : Set α) ×ˢ (s : Set α)) :
    ∑' p, f p = ∑ i : Fin s.card, ∑ j : Fin s.card,
      f (s.equivFin.symm i, s.equivFin.symm j) := by
  have hfinite : Function.HasFiniteSupport f :=
    (s.finite_toSet.prod s.finite_toSet).subset hf
  have hs : Summable f := summable_of_hasFiniteSupport hfinite
  rw [hs.tsum_prod]
  have houter : Function.support (fun a => ∑' b, f (a, b)) ⊆ (s : Set α) := by
    intro a ha
    by_contra hnot
    apply ha
    have hz (b : α) : f (a, b) = 0 := by
      by_contra hab
      exact hnot (hf hab).1
    simp only [hz, tsum_zero]
  rw [first_transfer_tsum_eq_sum_fin s _ houter]
  apply Finset.sum_congr rfl
  intro i _
  apply first_transfer_tsum_eq_sum_fin
  intro b hb
  exact (hf hb).2

theorem first_transfer_kernel_pair_window_support (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) (a : ℝ) {ell L : ℝ}
    (hell : 0 < ell) (hle : ell ≤ L) :
    Function.support (fun p : Ideal O × Ideal O =>
      firstTransferKernel Φ W a ![normIdeal p.1 / ell, normIdeal p.2 / ell]) ⊆
        (firstTransferIdealWindow I L : Set (Ideal O)) ×ˢ
          (firstTransferIdealWindow I L : Set (Ideal O)) := by
  intro p hp
  have hbox := firstTransferKernel_support I Φ W hW a hp
  have hhi : 0 ≤ I.hi := I.lo_pos.le.trans I.ordered
  have hmem (n : Ideal O) (hn : normIdeal n / ell ∈ Set.Icc I.lo I.hi) :
      n ∈ firstTransferIdealWindow I L := by
    apply mem_firstTransferIdealWindow.mpr
    refine ⟨((div_le_iff₀ hell).mp hn.2).trans
      (mul_le_mul_of_nonneg_left hle hhi), ?_⟩
    intro hn0
    have hpos := I.lo_pos.trans_le hn.1
    simpa [hn0, normIdeal] using hpos
  exact ⟨hmem p.1 (by simpa using hbox 0), hmem p.2 (by simpa using hbox 1)⟩

def firstTransferModelRows (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (H L F : ℝ) : Finset FirstTransferRowIndex :=
  (first_transfer_bilinear_row_ranges_finite c I Φ H L F).toFinset

def firstTransferModelColumns (I : SupportInterval) (L : ℝ) : Finset (Ideal O) :=
  firstTransferIdealWindow (halfEnlarged I) L

def firstTransferModelScale (L : ℝ) (r : FirstTransferRowIndex) : ℝ :=
  L / (normIdeal r.1.1 * normIdeal r.1.2.1)

def firstTransferModelCoefficient (H L F : ℝ) (r : FirstTransferRowIndex) : ℂ :=
  (mobius r.1.2.2 : ℂ) * (mobius r.1.2.1 : ℂ) *
    (H * normIdeal r.1.1 / (normIdeal r.1.2.2 * L ^ 2 * F) : ℝ)

def firstTransferModelParameter (H L : ℝ) (r : FirstTransferRowIndex) : ℝ :=
  H * normElement r.2.2 * normIdeal r.1.1 ^ 2 / (L ^ 2 * normIdeal r.1.2.2)

def firstTransferModelColumn (c : ArithmeticContext) (ξ : RayCharacter c)
    (r : FirstTransferRowIndex) (n : Ideal O) : ℂ :=
  firstTransferCoefficient c ξ r.1.1 r.1.2.2 r.1.2.1
    (r.2.2 * primaryGenerator r.2.1 ^ 2) n

theorem first_transfer_model_scale_bounds (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (H F : ℝ) {L : ℝ} (hL : 0 < L) (r : FirstTransferRowIndex)
    (hr : firstTransferRowAdmissible c I Φ H L F r) :
    0 < firstTransferModelScale L r ∧ firstTransferModelScale L r ≤ L := by
  have hC := hr.1.1.1.1
  have ht := hr.1.2.1.1.1
  have hden : 0 < normIdeal r.1.1 * normIdeal r.1.2.1 :=
    mul_pos (normIdeal_pos hC) (normIdeal_pos ht)
  refine ⟨div_pos hL hden, ?_⟩
  have hone : 1 ≤ normIdeal r.1.1 * normIdeal r.1.2.1 :=
    one_le_mul_of_one_le_of_one_le (first_transfer_one_le_normIdeal hC)
      (first_transfer_one_le_normIdeal ht)
  exact (div_le_iff₀ hden).mpr (le_mul_of_one_le_right hL.le hone)

def firstTransferConcreteModel (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) :
    FirstTransferFiniteModel c I Φ ξ H L F := by
  let rows := firstTransferModelRows c I Φ H L F
  let cols := firstTransferModelColumns I L
  let row : Fin rows.card → FirstTransferRowIndex := fun r => rows.equivFin.symm r
  let col : Fin cols.card → Ideal O := fun n => cols.equivFin.symm n
  have hrow (r : Fin rows.card) : firstTransferRowAdmissible c I Φ H L F (row r) := by
    exact (first_transfer_bilinear_row_ranges_finite c I Φ H L F).mem_toFinset.mp
      (rows.equivFin.symm r).property
  have hcol (n : Fin cols.card) : col n ∈ firstTransferIdealWindow (halfEnlarged I) L :=
    (cols.equivFin.symm n).property
  have hscale (r : Fin rows.card) := first_transfer_model_scale_bounds c I Φ H F hL (row r) (hrow r)
  refine {
    R := rows.card
    N := cols.card
    a := fun r n => firstTransferModelColumn c ξ (row r) (col n)
    x := fun r n => normIdeal (col n) / firstTransferModelScale L (row r)
    w := fun r => ‖firstTransferModelCoefficient H L F (row r)‖
    coefficient := fun r => firstTransferModelCoefficient H L F (row r)
    parameter := fun r => firstTransferModelParameter H L (row r)
    x_pos := fun r n => div_pos
      (normIdeal_pos (mem_firstTransferIdealWindow.mp (hcol n)).2) (hscale r).1
    w_nonneg := fun _ => norm_nonneg _
    coefficient_le := fun _ => le_rfl
    parameter_nonneg := ?_
    parameter_le := ?_
    expansion := ?_ }
  · intro r
    unfold firstTransferModelParameter
    exact div_nonneg (mul_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _)) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  · intro r
    exact first_transfer_kernel_parameter_le hH hL (normIdeal_pos (hrow r).1.1.1.1)
      (normIdeal_pos (ne_zero_of_dvd_ne_zero (hrow r).1.1.1.1 (hrow r).1.2.2.2.2))
      (hrow r).2.2.2.2
  · intro W hW
    have hWstar : SmoothSupported (halfEnlarged I) W := by
      refine ⟨hW.1, fun x hx => ?_⟩
      have hxI := hW.2 hx
      dsimp [halfEnlarged]
      constructor <;> linarith [hxI.1, hxI.2, I.lo_pos, I.ordered]
    rw [firstTransferBilinear_eq_joint_tsum c I Φ ξ hW H F hL]
    have hs := firstTransferBilinear_joint_summable c I Φ ξ hW H F hL
    rw [hs.tsum_prod]
    have hrowsupport : Function.support (fun r => ∑' p : Ideal O × Ideal O,
        firstTransferBilinearSummand c I Φ ξ W H L F r p) ⊆ (rows : Set FirstTransferRowIndex) := by
      intro r hr
      by_contra hnot
      have hnotadm : ¬ firstTransferRowAdmissible c I Φ H L F r := by
        intro hadm
        exact hnot ((first_transfer_bilinear_row_ranges_finite c I Φ H L F).mem_toFinset.mpr hadm)
      exact hr (by simp only [firstTransferBilinearSummand, if_neg hnotadm, tsum_zero])
    rw [first_transfer_tsum_eq_sum_fin rows _ hrowsupport]
    apply Finset.sum_congr rfl
    intro r _
    have hpairsupport : Function.support (fun p : Ideal O × Ideal O =>
        firstTransferBilinearSummand c I Φ ξ W H L F (row r) p) ⊆
          (cols : Set (Ideal O)) ×ˢ (cols : Set (Ideal O)) := by
      intro p hp
      have hk : firstTransferKernel Φ W (firstTransferModelParameter H L (row r))
          ![normIdeal p.1 / firstTransferModelScale L (row r),
            normIdeal p.2 / firstTransferModelScale L (row r)] ≠ 0 := by
        intro hk
        exact hp (by simp only [firstTransferBilinearSummand, if_pos (hrow r),
          firstTransferModelParameter, firstTransferModelScale] at hk ⊢; rw [hk, mul_zero, mul_zero])
      exact first_transfer_kernel_pair_window_support (halfEnlarged I) Φ hWstar _
        (hscale r).1 (hscale r).2 hk
    rw [first_transfer_pair_tsum_eq_sum_fin cols _ hpairsupport]
    simp only [firstTransferBilinearSummand, if_pos (hrow r), firstTransferModelColumn,
      firstTransferModelCoefficient, firstTransferModelParameter, firstTransferModelScale,
      Finset.mul_sum, col]

theorem first_transfer_model_exists (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) :
    Nonempty (FirstTransferFiniteModel c I Φ ξ H L F) :=
  ⟨firstTransferConcreteModel c I Φ ξ hH hL⟩

theorem firstColumn_eq_sum_fin_larger_window (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) {J : SupportInterval} {U : ℝ → ℂ} (hU : SmoothSupported J U)
    {ell L : ℝ} (hell : 0 < ell) (hle : ell ≤ L) (y : O) :
    firstColumn c ξ C d t U ell y =
      ∑ n : Fin (firstTransferIdealWindow J L).card,
        firstTransferCoefficient c ξ C d t y ((firstTransferIdealWindow J L).equivFin.symm n) *
          U (normIdeal ((firstTransferIdealWindow J L).equivFin.symm n) / ell) := by
  rw [firstColumn_eq_firstTransferCoefficient]
  apply first_transfer_tsum_eq_sum_fin
  intro n hn
  have hmem : n ∈ firstTransferIdealWindow J ell := by
    by_contra hnot
    exact hn (firstTransferCoefficient_mul_eq_zero_of_not_mem c ξ C d t hU hell y n hnot)
  obtain ⟨hnorm, hn0⟩ := mem_firstTransferIdealWindow.mp hmem
  exact mem_firstTransferIdealWindow.mpr
    ⟨hnorm.trans (mul_le_mul_of_nonneg_left hle (J.lo_pos.le.trans J.ordered)), hn0⟩

theorem firstTransferConcreteModel_quadratic_eq (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) {H L F : ℝ} (hH : 0 < H) (hL : 0 < L)
    {U : ℝ → ℂ} (hU : SmoothSupported (halfEnlarged I) U) :
    let model := firstTransferConcreteModel c I Φ ξ (F := F) hH hL
    (∑ r : Fin model.R, model.w r * ‖finiteTestSum model.a model.x r U‖ ^ 2) =
      ∑' r : FirstTransferRowIndex,
        if firstTransferRowAdmissible c I Φ H L F r then
          ‖firstTransferModelCoefficient H L F r‖ *
            ‖firstColumn c ξ r.1.1 r.1.2.2 r.1.2.1 U (firstTransferModelScale L r)
              (r.2.2 * primaryGenerator r.2.1 ^ 2)‖ ^ 2
        else 0 := by
  dsimp only
  let rows := firstTransferModelRows c I Φ H L F
  let cols := firstTransferModelColumns I L
  let row : Fin rows.card → FirstTransferRowIndex := fun r => rows.equivFin.symm r
  have hrow (r : Fin rows.card) : firstTransferRowAdmissible c I Φ H L F (row r) :=
    (first_transfer_bilinear_row_ranges_finite c I Φ H L F).mem_toFinset.mp
      (rows.equivFin.symm r).property
  have hsupp : Function.support (fun r : FirstTransferRowIndex =>
      if firstTransferRowAdmissible c I Φ H L F r then
        ‖firstTransferModelCoefficient H L F r‖ *
          ‖firstColumn c ξ r.1.1 r.1.2.2 r.1.2.1 U (firstTransferModelScale L r)
            (r.2.2 * primaryGenerator r.2.1 ^ 2)‖ ^ 2 else 0) ⊆ (rows : Set FirstTransferRowIndex) := by
    intro r hr
    by_cases hadm : firstTransferRowAdmissible c I Φ H L F r
    · exact (first_transfer_bilinear_row_ranges_finite c I Φ H L F).mem_toFinset.mpr hadm
    · exact False.elim (hr (if_neg hadm))
  rw [first_transfer_tsum_eq_sum_fin rows _ hsupp]
  change (∑ r : Fin rows.card, ‖firstTransferModelCoefficient H L F (row r)‖ *
      ‖∑ n : Fin cols.card, firstTransferModelColumn c ξ (row r) (cols.equivFin.symm n) *
        U (normIdeal (cols.equivFin.symm n) / firstTransferModelScale L (row r))‖ ^ 2) = _
  apply Finset.sum_congr rfl
  intro r _
  rw [if_pos (hrow r)]
  have hscale := first_transfer_model_scale_bounds c I Φ H F hL (row r) (hrow r)
  rw [firstColumn_eq_sum_fin_larger_window c ξ (row r).1.1 (row r).1.2.2
    (row r).1.2.1 hU hscale.1 hscale.2]
  rfl

theorem firstTransferConcreteModel_quadratic_eq_sum_rows (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (ξ : RayCharacter c)
    {H L F : ℝ} (hH : 0 < H) (hL : 0 < L) {U : ℝ → ℂ}
    (hU : SmoothSupported (halfEnlarged I) U) :
    let model := firstTransferConcreteModel c I Φ ξ (F := F) hH hL
    (∑ r : Fin model.R, model.w r * ‖finiteTestSum model.a model.x r U‖ ^ 2) =
      ∑ r ∈ firstTransferModelRows c I Φ H L F,
        ‖firstTransferModelCoefficient H L F r‖ *
          ‖firstColumn c ξ r.1.1 r.1.2.2 r.1.2.1 U (firstTransferModelScale L r)
            (r.2.2 * primaryGenerator r.2.1 ^ 2)‖ ^ 2 := by
  dsimp only
  rw [firstTransferConcreteModel_quadratic_eq c I Φ ξ hH hL hU]
  let rows := firstTransferModelRows c I Φ H L F
  have hzero (r : FirstTransferRowIndex) (hr : r ∉ rows) :
      (if firstTransferRowAdmissible c I Φ H L F r then
        ‖firstTransferModelCoefficient H L F r‖ *
          ‖firstColumn c ξ r.1.1 r.1.2.2 r.1.2.1 U (firstTransferModelScale L r)
            (r.2.2 * primaryGenerator r.2.1 ^ 2)‖ ^ 2 else 0) = 0 := by
    apply if_neg
    intro hadm
    exact hr ((first_transfer_bilinear_row_ranges_finite c I Φ H L F).mem_toFinset.mpr hadm)
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro r hr
  have hadm : firstTransferRowAdmissible c I Φ H L F r :=
    (first_transfer_bilinear_row_ranges_finite c I Φ H L F).mem_toFinset.mp hr
  rw [if_pos hadm]

end QRHShort
