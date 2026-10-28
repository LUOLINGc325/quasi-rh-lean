import QRHShort.Estimates
import QRHShort.WeightNorm
import QRHShort.EnergySupport
import QRHShort.TransferAssembly
import QRHLean3.Iteration
import QRHLean3.Loss
import QRH.Descent
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Actual energy induction, with its remaining smoothing input explicit.
`SmoothedRowSummability` is a convergence assertion for the literal arithmetic
row sums. It is not an energy estimate or an induction hypothesis. This file
does not assert that a `RowWeight` exists or that these sums converge.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The precise convergence input needed to compare a sharp row cutoff with a
Schwartz majorant. The outer dyadic ideal sum already has finite support. -/
def SmoothedRowSummability (Φ : RowWeight) : Prop :=
  ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
    ∀ (ξ : RayCharacter c) (W : ℝ → ℂ) (H X : ℝ) (f : Ideal O),
      SmoothSupported I W → 1 ≤ H → 1 ≤ X →
      Summable (fun k : O => Φ.value (normElement k / H) *
        ‖columnSum c ξ W X k f‖ ^ 2)

theorem energy_le_smoothedEnergy_of_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ)
    {H X F : ℝ} (hH : 0 < H) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hrows : ∀ f : Ideal O, Summable (fun k : O => Φ.value (normElement k / H) *
      ‖columnSum c ξ W X k f‖ ^ 2)) :
    energy c ξ W H X F ≤ smoothedEnergy c ξ Φ.value W H X F := by
  have hrow (f : Ideal O) : rowEnergy (fun k => columnSum c ξ W X k f) H ≤
      ∑' k : O, Φ.value (normElement k / H) * ‖columnSum c ξ W X k f‖ ^ 2 := by
    apply Summable.tsum_le_tsum _ (rowEnergy_summable _ H) (hrows f)
    intro k
    have hnorm : 0 ≤ normElement k := by
      dsimp [normElement, normIdeal]
      positivity
    have hratio : 0 ≤ normElement k / H := div_nonneg hnorm hH.le
    by_cases hk : 0 < normElement k ∧ normElement k ≤ H
    · rw [if_pos hk]
      have hratio1 : normElement k / H ≤ 1 := (div_le_iff₀ hH).mpr (by simpa using hk.2)
      exact le_mul_of_one_le_left (sq_nonneg _) (Φ.majorant _ ⟨hratio, hratio1⟩)
    · rw [if_neg hk]
      exact mul_nonneg (Φ.nonnegative _ hratio) (sq_nonneg _)
  unfold energy smoothedEnergy
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (mul_nonneg hX hF))
  apply Summable.tsum_le_tsum _ (energy_outer_summable c ξ W H X F)
    (dyadic_ideal_summable (SquarefreeOutside c.S) F _)
  intro f
  split_ifs
  · exact hrow f
  · exact le_refl 0

/-- A fixed constant for the actual energy at a finite induction stage. -/
def CanonicalStageBound (c : ArithmeticContext) (I : SupportInterval)
    (κ C : ℝ) (j : ℕ) (ε : ℝ) (J : ℕ) (K : ℝ) : Prop :=
  ∀ (ξ : RayCharacter c) (W : ℝ → ℂ) (D H X F : ℝ),
    SmoothSupported I W → 2 ≤ D → QRH.ParentRange D κ C H X F →
    H ≤ D ^ ((j : ℝ) * κ) →
    energy c ξ W H X F ≤ K * weightNorm J W ^ 2 * D ^ ε * (X * F)

/-- The constant is chosen before every varying scale, while the derivative
order is chosen before the arithmetic context and support interval. -/
def CanonicalStageEstimate (κ C : ℝ) (j : ℕ) (ε : ℝ) (J : ℕ) : Prop :=
  ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
    ∃ K : ℝ, 0 ≤ K ∧ CanonicalStageBound c I κ C j ε J K

private theorem outside_norm_one_le (c : ArithmeticContext) {b : Ideal O}
    (hb : Outside c.S b) : 1 ≤ normIdeal b := by
  have hbabs : b.absNorm ≠ 0 := fun h => hb.1 (Ideal.absNorm_eq_zero_iff.mp h)
  change (1 : ℝ) ≤ (b.absNorm : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hbabs)

private theorem parent_component_bounds {D κ C H X F : ℝ}
    (hD : 1 ≤ D) (hκ : 0 ≤ κ) (hp : QRH.ParentRange D κ C H X F) :
    H ≤ X * F ∧ H ≤ D ^ C ∧ X ≤ D ^ C ∧ F ≤ D ^ C := by
  have hX0 : 0 ≤ X := zero_le_one.trans hp.X_one_le
  have hF0 : 0 ≤ F := zero_le_one.trans hp.F_one_le
  have hpow : D ^ (-κ) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hD (neg_nonpos.mpr hκ)
  have hHS : H ≤ X * F := hp.gap.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (mul_nonneg hX0 hF0))
  exact ⟨hHS, hHS.trans hp.product_le,
    (le_mul_of_one_le_right hX0 hp.F_one_le).trans hp.product_le,
    (le_mul_of_one_le_left hF0 hp.X_one_le).trans hp.product_le⟩

private theorem cube_index_long_branch (c : ArithmeticContext) {H X hc : ℝ}
    (hhc : 0 ≤ hc) (hcut : hc ^ (3 : ℕ) = min X (X ^ (2 : ℕ) / H ^ (2 : ℕ)))
    {b : Ideal O} (hb : Outside c.S b) (hlarge : hc < normIdeal b)
    (hcol : 1 < X / normIdeal b ^ (3 : ℕ)) : QRH.LongBranch H X hc (normIdeal b) :=
  ⟨hhc, outside_norm_one_le c hb, hcut, hlarge, hcol⟩

theorem cubeValues_eq_empty_of_height_le_one (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) {H X F hc : ℝ} (hH : 1 ≤ H) (hHsmall : H ≤ 1)
    (hX : 1 ≤ X) (hhc : 0 ≤ hc)
    (hcut : hc ^ (3 : ℕ) = min X (X ^ (2 : ℕ) / H ^ (2 : ℕ))) :
    cubeValues c ξ W H X F hc = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro v ⟨b, hb, hlarge, hcol, _⟩
  have hHone : H = 1 := le_antisymm hHsmall hH
  have hshort : H ^ (2 : ℕ) ≤ X := by simpa only [hHone, one_pow] using hX
  exact QRH.no_long_branch hH hX hshort (cube_index_long_branch c hhc hcut hb hlarge hcol)

/-- The actual normalized child values satisfy the preceding stage estimate.
The support interval in the induction hypothesis is precisely the enlarged
interval specified by the transfer statement. -/
theorem child_value_le_of_stage_bound (c : ArithmeticContext) (I : SupportInterval)
    {κ C D H X F hc δ B : ℝ} {j m : ℕ} (hκ : 0 < κ) (hD : 2 ≤ D)
    (hB : 0 ≤ B) (hp : QRH.ParentRange D κ C H X F)
    (hhc : 0 ≤ hc) (hcut : hc ^ (3 : ℕ) = min X (X ^ (2 : ℕ) / H ^ (2 : ℕ)))
    (hstage : H ≤ D ^ (((j : ℝ) + 1) * κ))
    (hIH : CanonicalStageBound c (enlarged I) κ C j δ m B)
    {b : Ideal O} (hb : Outside c.S b) (hlarge : hc < normIdeal b)
    (hcol : 1 < X / normIdeal b ^ (3 : ℕ))
    {r : ℝ} (hr : r ∈ childValues c I m H (X / normIdeal b ^ (3 : ℕ)) F (X * F)) :
    r ≤ B * D ^ δ := by
  rcases hr with ⟨H', X', F', ξ', U, hH', hX', hF', hrow, hratio, hprod, hU, hnorm, rfl⟩
  have hlong := cube_index_long_branch c hhc hcut hb hlarge hcol
  have htransfer : QRH.TransferBounds H X F (normIdeal b) H' X' F' :=
    ⟨hH', hX', hF', hrow, hratio, hprod⟩
  have hD1 : 1 ≤ D := by linarith
  obtain ⟨_, _, hstage', hp'⟩ := QRH.canonical_parameter_step hD1 hκ j hp hlong htransfer hstage
  have he := hIH ξ' U D H' X' F' hU hD hp' hstage'
  apply QRHLean3.normalized_energy_bound
    (mul_pos (lt_of_lt_of_le zero_lt_one hX') (lt_of_lt_of_le zero_lt_one hF'))
    hB (zero_le_one.trans hD1) (weightNorm_nonneg hU m) hnorm
  simpa only [mul_comm, mul_left_comm, mul_assoc] using he

private theorem transfer_range_of_long_branch {D κ C H X F hc b : ℝ}
    (hD : 1 ≤ D) (hκ : 0 ≤ κ) (hp : QRH.ParentRange D κ C H X F)
    (hb : QRH.LongBranch H X hc b) :
    TransferRange D C H (X / b ^ (3 : ℕ)) F (X * F) := by
  obtain ⟨hHS, hHcap, hXcap, hFcap⟩ := parent_component_bounds hD hκ hp
  obtain ⟨hL, hLX⟩ := QRH.column_range hp.X_one_le hb
  refine ⟨hp.H_one_le, hHcap, hL.le, hLX.trans hXcap, hp.F_one_le, hFcap,
    one_le_mul_of_one_le_of_one_le hp.X_one_le hp.F_one_le, hp.product_le, ?_⟩
  exact max_le hHS (mul_le_mul_of_nonneg_right hLX (zero_le_one.trans hp.F_one_le))

private theorem cutoff_exists {H X : ℝ} (hX : 0 ≤ X) :
    ∃ hc : ℝ, 0 ≤ hc ∧ hc ^ (3 : ℕ) = min X (X ^ (2 : ℕ) / H ^ (2 : ℕ)) := by
  have hmin : 0 ≤ min X (X ^ (2 : ℕ) / H ^ (2 : ℕ)) :=
    le_min hX (div_nonneg (sq_nonneg X) (sq_nonneg H))
  refine ⟨(min X (X ^ (2 : ℕ) / H ^ (2 : ℕ))) ^ ((3 : ℝ)⁻¹),
    Real.rpow_nonneg hmin _, ?_⟩
  exact Real.rpow_inv_natCast_pow hmin (by decide : (3 : ℕ) ≠ 0)


/-- Assemble the actual canonical estimate from cube reduction and transfer,
with the still outstanding existence and convergence of the smoothing weight
visible in the arguments. No estimate for a child or parent is assumed here. -/
theorem canonical_estimate_of_cube_transfer_and_rows
    (hcube : CubeEstimate) (htransfer : TransferEstimate)
    (Φ : RowWeight) (hrows : SmoothedRowSummability Φ) : CanonicalEstimate := by
  intro κ C ε hκ hC hε
  let cubeOrder : ℝ → ℕ := fun δ =>
    if hδ : 0 < δ then Classical.choose (hcube C δ hC hδ) else 1
  have hstages : ∀ (j : ℕ) (η : ℝ), 0 < η →
      CanonicalStageEstimate κ C j η (QRHLean3.derivativeOrder cubeOrder (j + 1) η) := by
    intro j
    induction j with
    | zero =>
      intro η hη
      have hδ : 0 < η / 3 := div_pos hη (by norm_num)
      have hselected := Classical.choose_spec (hcube C (η / 3) hC hδ)
      have hselectedOrder : cubeOrder (η / 3) =
          Classical.choose (hcube C (η / 3) hC hδ) := dif_pos hδ
      rw [← hselectedOrder] at hselected
      obtain ⟨_, hselected⟩ := hselected
      intro c I hrelations
      obtain ⟨K, hK, hcubeI⟩ := hselected c I hrelations
      refine ⟨K, hK, ?_⟩
      intro ξ W D H X F hW hD hp hstage
      have hD1 : 1 ≤ D := by linarith
      have hD0 : 0 ≤ D := zero_le_one.trans hD1
      have hX0 : 0 ≤ X := zero_le_one.trans hp.X_one_le
      have hF0 : 0 ≤ F := zero_le_one.trans hp.F_one_le
      have hHsmall : H ≤ 1 := by simpa only [Nat.cast_zero, zero_mul, Real.rpow_zero] using hstage
      obtain ⟨hHS, hHcap, hXcap, hFcap⟩ := parent_component_bounds hD1 hκ.le hp
      obtain ⟨hc, hhc, hcut⟩ := cutoff_exists (H := H) hX0
      have he := hcubeI ξ W D H X F hc hW hD hp.H_one_le hHcap hp.X_one_le hXcap
        hp.F_one_le hFcap hHS hhc hcut
      rw [cubeValues_eq_empty_of_height_le_one c ξ W hp.H_one_le hHsmall hp.X_one_le hhc hcut,
        QRHLean3.supZero_empty, add_zero] at he
      have hNsq := pow_le_pow_left₀ (weightNorm_nonneg hW (cubeOrder (η / 3)))
        (weightNorm_mono hW (QRHLean3.cube_order_le cubeOrder 0 η)) 2
      have hpow : D ^ (η / 3) ≤ D ^ η :=
        Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
      calc
        energy c ξ W H X F ≤ K * D ^ (η / 3) * (X * F * weightNorm (cubeOrder (η / 3)) W ^ 2) := he
        _ = (K * (X * F)) * weightNorm (cubeOrder (η / 3)) W ^ 2 * D ^ (η / 3) := by ring
        _ ≤ (K * (X * F)) * weightNorm (QRHLean3.derivativeOrder cubeOrder (0 + 1) η) W ^ 2 * D ^ η :=
          mul_le_mul (mul_le_mul_of_nonneg_left hNsq (by positivity)) hpow
            (Real.rpow_nonneg hD0 _) (by positivity)
        _ = K * weightNorm (QRHLean3.derivativeOrder cubeOrder (0 + 1) η) W ^ 2 * D ^ η * (X * F) := by ring
    | succ j ih =>
      intro η hη
      have hδ : 0 < η / 3 := div_pos hη (by norm_num)
      have hselected := Classical.choose_spec (hcube C (η / 3) hC hδ)
      have hselectedOrder : cubeOrder (η / 3) =
          Classical.choose (hcube C (η / 3) hC hδ) := dif_pos hδ
      rw [← hselectedOrder] at hselected
      obtain ⟨_, hselected⟩ := hselected
      let m := QRHLean3.derivativeOrder cubeOrder (j + 1) (η / 3)
      let J := QRHLean3.derivativeOrder cubeOrder ((j + 1) + 1) η
      have hCJ : cubeOrder (η / 3) ≤ J := QRHLean3.cube_order_le cubeOrder (j + 1) η
      have hTJ : 4 * m + 12 ≤ J := QRHLean3.transfer_order_le cubeOrder (j + 1) η
      intro c I hrelations
      obtain ⟨B, hB, hIH⟩ := ih (η / 3) hδ c (enlarged I) hrelations
      obtain ⟨A, hA, htransferI⟩ := htransfer C (η / 3) m hC hδ c I Φ hrelations
      obtain ⟨K, hK, hcubeI⟩ := hselected c I hrelations
      refine ⟨K * (1 + A * (1 + B)), by positivity, ?_⟩
      intro ξ W D H X F hW hD hp hstage
      have hD1 : 1 ≤ D := by linarith
      have hD0 : 0 ≤ D := zero_le_one.trans hD1
      have hX0 : 0 ≤ X := zero_le_one.trans hp.X_one_le
      have hF0 : 0 ≤ F := zero_le_one.trans hp.F_one_le
      have hSigma0 : 0 ≤ X * F := mul_nonneg hX0 hF0
      have hstage' : H ≤ D ^ (((j : ℝ) + 1) * κ) := by
        simpa only [Nat.cast_succ] using hstage
      obtain ⟨hHS, hHcap, hXcap, hFcap⟩ := parent_component_bounds hD1 hκ.le hp
      obtain ⟨hc, hhc, hcut⟩ := cutoff_exists (H := H) hX0
      let columns : Set (Ideal O) := {b | Outside c.S b ∧ hc < normIdeal b ∧
        1 < X / normIdeal b ^ (3 : ℕ)}
      let columnEnergy : Ideal O → ℝ := fun b => energy c ξ W H (X / normIdeal b ^ (3 : ℕ)) F
      let children : Ideal O → Set ℝ := fun b =>
        childValues c I m H (X / normIdeal b ^ (3 : ℕ)) F (X * F)
      have himage : cubeValues c ξ W H X F hc = columnEnergy '' columns := by
        ext v
        constructor
        · rintro ⟨b, hb, hlarge, hcol, rfl⟩
          exact ⟨b, ⟨hb, hlarge, hcol⟩, rfl⟩
        · rintro ⟨b, ⟨hb, hlarge, hcol⟩, rfl⟩
          exact ⟨b, hb, hlarge, hcol, rfl⟩
      have hchildren : ∀ b ∈ columns, ∀ r ∈ children b, r ≤ B * D ^ (η / 3) := by
        rintro b ⟨hb, hlarge, hcol⟩ r hr
        exact child_value_le_of_stage_bound c I hκ hD hB hp hhc hcut hstage'
          hIH hb hlarge hcol hr
      have htransferActual : ∀ b ∈ columns,
          columnEnergy b ≤ A * D ^ (η / 3) * (X * F) * weightNorm J W ^ 2 *
            (1 + QRHLean3.supZero (children b)) := by
        rintro b ⟨hb, hlarge, hcol⟩
        have hlong := cube_index_long_branch c hhc hcut hb hlarge hcol
        have hrange := transfer_range_of_long_branch hD1 hκ.le hp hlong
        have hL1 : 1 ≤ X / normIdeal b ^ (3 : ℕ) := hcol.le
        have hcompare := energy_le_smoothedEnergy_of_summable c ξ Φ W
          (lt_of_lt_of_le zero_lt_one hp.H_one_le) (zero_le_one.trans hL1) hF0
          (fun f => hrows c I hrelations ξ W H (X / normIdeal b ^ (3 : ℕ)) f hW hp.H_one_le hL1)
        have ht := htransferI ξ W D H (X / normIdeal b ^ (3 : ℕ)) F (X * F) hW hD hrange
        have hNsq := pow_le_pow_left₀ (weightNorm_nonneg hW (4 * m + 12))
          (weightNorm_mono hW hTJ) 2
        have hS0 : 0 ≤ 1 + childSup c I m H (X / normIdeal b ^ (3 : ℕ)) F (X * F) :=
          add_nonneg zero_le_one (childSup_nonneg c I m H (X / normIdeal b ^ (3 : ℕ)) F (X * F))
        exact hcompare.trans (ht.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNsq (by positivity)) hS0))
      have hcubeActual : energy c ξ W H X F ≤ K * D ^ (η / 3) *
          (X * F * weightNorm J W ^ 2 + QRHLean3.supZero (columnEnergy '' columns)) := by
        have he := hcubeI ξ W D H X F hc hW hD hp.H_one_le hHcap hp.X_one_le hXcap
          hp.F_one_le hFcap hHS hhc hcut
        rw [himage] at he
        have hNsq := pow_le_pow_left₀ (weightNorm_nonneg hW (cubeOrder (η / 3)))
          (weightNorm_mono hW hCJ) 2
        exact he.trans (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hNsq hSigma0) (le_refl _))
          (mul_nonneg hK (Real.rpow_nonneg hD0 _)))
      have hfinal := QRHLean3.nested_energy_bound hD1 hη.le hSigma0 hK hA hB
        columns columnEnergy children hchildren htransferActual hcubeActual
      simpa only [J, Nat.succ_eq_add_one, mul_comm, mul_left_comm, mul_assoc] using hfinal
  obtain ⟨j, _, hj⟩ := QRH.finite_stage_exists (C := C) hκ
  refine ⟨QRHLean3.derivativeOrder cubeOrder (j + 1) ε,
    QRHLean3.derivativeOrder_pos cubeOrder (j + 1) ε, ?_⟩
  intro c I hrelations
  obtain ⟨K, hK, hstage⟩ := hstages j ε hε c I hrelations
  refine ⟨K, hK, ?_⟩
  intro ξ W D H X F hW hD hp
  have hD1 : 1 ≤ D := by linarith
  have hHcap := (parent_component_bounds hD1 hκ.le hp).2.1
  exact hstage ξ W D H X F hW hD hp (hHcap.trans (hj D hD1))

end QRHShort
