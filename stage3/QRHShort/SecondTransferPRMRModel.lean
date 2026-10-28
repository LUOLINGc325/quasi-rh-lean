import QRHShort.SecondTransferPRMRColumns

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem second_transfer_prmr_one_le_norm {a : Ideal O} (ha : a ≠ ⊥) :
    1 ≤ normIdeal a := by
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => ha (Ideal.absNorm_eq_zero_iff.mp h))

theorem second_transfer_prmr_valid_bounds {c : ArithmeticContext}
    (I : SupportInterval) (coeffs : RayCharacter c → ℂ) {H L F Sigma : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (z : SecondTransferIndex c) (hz : z.valid I coeffs H L F Sigma) :
    normIdeal z.excluded ≤ 2 * I.hi * L ∧
    normIdeal z.twist ≤ 2 * I.hi * L ∧
    normElement z.frequency ≤ H * L / (Sigma * F) ∧
    z.rBlock ≤ ⌈2 * I.hi * L⌉₊ ∧ z.fBlock ≤ ⌈2 * I.hi * L⌉₊ := by
  rcases hz with ⟨hr, hf, _, _, _, _, _, _, hk, hrf, hrlo, _, hflo, _⟩
  have hr1 := second_transfer_prmr_one_le_norm hr.1.1
  have hf1 := second_transfer_prmr_one_le_norm hf.1.1
  have hrbound : normIdeal z.excluded ≤ 2 * I.hi * L :=
    (le_mul_of_one_le_right (zero_le_one.trans hr1) hf1).trans hrf
  have hfbound : normIdeal z.twist ≤ 2 * I.hi * L :=
    (le_mul_of_one_le_left (zero_le_one.trans hf1) hr1).trans hrf
  have hkbound : normElement z.frequency ≤ H * L / (Sigma * F) := by
    apply hk.trans
    apply div_le_div_of_nonneg_left (mul_pos hH hL).le (mul_pos hSigma hF)
    exact le_mul_of_one_le_right (mul_pos hSigma hF).le (one_le_pow₀ hr1)
  have block (b : ℕ) (hb : (2 : ℝ) ^ b ≤ 2 * I.hi * L) :
      b ≤ ⌈2 * I.hi * L⌉₊ := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hb' : (b : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast (Nat.lt_two_pow_self (n := b)).le
    exact (hb'.trans hb).trans (Nat.le_ceil _)
  exact ⟨hrbound, hfbound, hkbound, block _ (hrlo.trans hrbound),
    block _ (hflo.trans hfbound)⟩

theorem second_transfer_prmr_valid_finite (c : ArithmeticContext)
    (I : SupportInterval) (coeffs : RayCharacter c → ℂ) {H L F Sigma : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (hcoeffs : (Function.support coeffs).Finite) :
    {z : SecondTransferIndex c | z.valid I coeffs H L F Sigma}.Finite := by
  let T := 2 * I.hi * L
  let B := ⌈T⌉₊
  let A := Function.support coeffs ×ˢ
    ({r : Ideal O | normIdeal r ≤ T} ×ˢ
      ({f : Ideal O | normIdeal f ≤ T} ×ˢ
        ({k : O | normElement k ≤ H * L / (Sigma * F)} ×ˢ
          (Set.Iic B ×ˢ Set.Iic B))))
  have hA : A.Finite := hcoeffs.prod ((finite_normIdeal_le T).prod
    ((finite_normIdeal_le T).prod ((finite_normElement_le _).prod
      ((Set.finite_Iic B).prod (Set.finite_Iic B)))))
  let make : RayCharacter c × Ideal O × Ideal O × O × ℕ × ℕ → SecondTransferIndex c :=
    fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  apply (hA.image make).subset
  intro z hz
  have hb := second_transfer_prmr_valid_bounds I coeffs hH hL hF hSigma z hz
  refine ⟨(z.character, z.excluded, z.twist, z.frequency, z.rBlock, z.fBlock), ?_, ?_⟩
  · exact ⟨hz.2.2.2.1, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2⟩
  · rfl

theorem second_transfer_prmr_dilation_bounds {c : ArithmeticContext}
    (I : SupportInterval) (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ)
    (z : SecondTransferIndex c) (hz : z.valid I coeffs H L F Sigma) :
    1 ≤ z.dilation ∧ z.dilation ≤ 4 := by
  rcases hz with ⟨hr, hf, _, _, _, _, _, _, _, _, hrlo, hrhi, hflo, hfhi⟩
  have hrp : 0 < (2 : ℝ) ^ z.rBlock := by positivity
  have hfp : 0 < (2 : ℝ) ^ z.fBlock := by positivity
  have hrn : 0 ≤ normIdeal z.excluded := (normIdeal_pos hr.1.1).le
  have hfn : 0 ≤ normIdeal z.twist := (normIdeal_pos hf.1.1).le
  constructor
  · apply (le_div_iff₀ (mul_pos hrp hfp)).mpr
    simpa only [one_mul] using mul_le_mul hrlo hflo hfp.le hrn
  · apply (div_le_iff₀ (mul_pos hrp hfp)).mpr
    calc
      normIdeal z.excluded * normIdeal z.twist ≤
          (2 * (2 : ℝ) ^ z.rBlock) * (2 * (2 : ℝ) ^ z.fBlock) :=
        mul_le_mul hrhi.le hfhi.le hfn (by positivity)
      _ = _ := by ring

def secondTransferPRMRModel (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (hSigma : 0 < Sigma) (hcoeffs : (Function.support coeffs).Finite) :
    SecondTransferFiniteModel c I coeffs cI H L F Sigma := by
  let rows := (second_transfer_prmr_valid_finite c I coeffs hH hL hF hSigma hcoeffs).toFinset
  let cols := secondTransferPRMRColumns I L
  let row : Fin rows.card → SecondTransferIndex c := fun r => rows.equivFin.symm r
  let col : Fin cols.card → Ideal O := fun n => cols.equivFin.symm n
  have hrow (r : Fin rows.card) : (row r).valid I coeffs H L F Sigma :=
    (second_transfer_prmr_valid_finite c I coeffs hH hL hF hSigma hcoeffs).mem_toFinset.mp
      (rows.equivFin.symm r).property
  refine {
    R := rows.card
    N := cols.card
    row := row
    row_injective := ?_
    valid := hrow
    a := fun r n => secondTransferPRMRColumn c (row r) (col n)
    x := fun r n => normIdeal (col n) / (row r).columnScale L
    x_pos := ?_
    column_complete := ?_
    dilation_lower := fun r => (second_transfer_prmr_dilation_bounds I coeffs H L F Sigma
      (row r) (hrow r)).1
    dilation_upper := fun r => (second_transfer_prmr_dilation_bounds I coeffs H L F Sigma
      (row r) (hrow r)).2
    parameter_nonneg := ?_ }
  · intro r s h
    exact rows.equivFin.symm.injective (Subtype.ext h)
  · intro r n
    have hn := mem_boundedDivisibleIdeals.mp (cols.equivFin.symm n).property
    exact div_pos (normIdeal_pos hn.2.2) (second_transfer_prmr_columnScale_bounds _ hL).1
  · intro r V hV
    exact second_transfer_prmr_column_complete I (row r) hL hV
  · intro r
    unfold SecondTransferIndex.parameter
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcI hSigma.le)
      hF.le) (Nat.cast_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hH.le hL.le) (sq_nonneg _))

theorem second_transfer_prmr_model_exists (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (hSigma : 0 < Sigma) (hcoeffs : (Function.support coeffs).Finite) :
    Nonempty (SecondTransferFiniteModel c I coeffs cI H L F Sigma) :=
  ⟨secondTransferPRMRModel c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs⟩

theorem second_transfer_prmr_model_exists_of_range (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (coeffs : RayCharacter c → ℂ)
    {D C cI H L F Sigma : ℝ}
    (hcI : max 1 (4 * Φ.fourierCap * I.hi ^ 2) ≤ cI)
    (hrange : TransferRange D C H L F Sigma)
    (hcoeffs : (Function.support coeffs).Finite) :
    Nonempty (SecondTransferFiniteModel c I coeffs cI H L F Sigma) := by
  exact second_transfer_prmr_model_exists c I coeffs cI H L F Sigma
    (zero_le_one.trans ((le_max_left _ _).trans hcI))
    (zero_lt_one.trans_le hrange.1) (zero_lt_one.trans_le hrange.2.2.1)
    (zero_lt_one.trans_le hrange.2.2.2.2.1)
    (zero_lt_one.trans_le hrange.2.2.2.2.2.2.1) hcoeffs

end QRHShort
