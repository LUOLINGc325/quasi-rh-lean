import QRHShort.SecondTransferPRMMExclusion
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem second_transfer_prmm_index_ext {c : ArithmeticContext} {z w : SecondTransferIndex c}
    (h1 : z.character = w.character) (h2 : z.excluded = w.excluded)
    (h3 : z.twist = w.twist) (h4 : z.frequency = w.frequency)
    (h5 : z.rBlock = w.rBlock) (h6 : z.fBlock = w.fBlock) : z = w := by
  cases z
  cases w
  simp_all

/-- The complete twist and frequency rectangle has genuine finite support. -/
theorem second_transfer_prmm_rectangle_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) (V : ℝ → ℂ) (r : Ideal O) (A X T : ℝ) :
    Function.HasFiniteSupport (fun p : Ideal O × O =>
      if (SquarefreeOutside c.S p.1 ∧ T ≤ normIdeal p.1 ∧ normIdeal p.1 < 2 * T) ∧
          (0 < normElement p.2 ∧ normElement p.2 ≤ A) then
        ‖excludedColumnSum c ξ V r X p.2 p.1‖ ^ 2 else 0) := by
  apply ((finite_normIdeal_le (2 * T)).prod (finite_normElement_le A)).subset
  intro p hp
  by_cases h : (SquarefreeOutside c.S p.1 ∧ T ≤ normIdeal p.1 ∧ normIdeal p.1 < 2 * T) ∧
      (0 < normElement p.2 ∧ normElement p.2 ≤ A)
  · exact ⟨h.1.2.2.le, h.2.2⟩
  · exact False.elim (hp (if_neg h))

/-- A subset of a model's single character/exclusion/dyadic block injects into
full arithmetic energy. This uses every column, rather than an arbitrary truncation. -/
theorem second_transfer_prmm_model_block (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (model : SecondTransferFiniteModel c I coeffs cI H L F Sigma)
    (V : ℝ → ℂ) (hV : SmoothSupported (enlarged I) V)
    (S : Finset (Fin model.R)) (ξ : RayCharacter c) (r : Ideal O) (rb fb : ℕ)
    (hfixed : ∀ i ∈ S, (model.row i).character = ξ ∧ (model.row i).excluded = r ∧
      (model.row i).rBlock = rb ∧ (model.row i).fBlock = fb)
    (A : ℝ) (hfreq : ∀ i ∈ S, normElement (model.row i).frequency ≤ A)
    (hL : 0 < L) :
    (∑ i ∈ S, ‖finiteTestSum model.a model.x i V‖ ^ 2) ≤
      (L / (2 : ℝ) ^ rb) * excludedEnergy c ξ V r A
        (L / ((2 : ℝ) ^ rb * (2 : ℝ) ^ fb)) ((2 : ℝ) ^ fb) := by
  let X := L / ((2 : ℝ) ^ rb * (2 : ℝ) ^ fb)
  let T : ℝ := (2 : ℝ) ^ fb
  let w : Ideal O × O → ℝ := fun p =>
    if (SquarefreeOutside c.S p.1 ∧ T ≤ normIdeal p.1 ∧ normIdeal p.1 < 2 * T) ∧
        (0 < normElement p.2 ∧ normElement p.2 ≤ A) then
      ‖excludedColumnSum c ξ V r X p.2 p.1‖ ^ 2 else 0
  let ι : {i // i ∈ S} → Ideal O × O := fun i =>
    ((model.row i.1).twist, (model.row i.1).frequency)
  have hinj : Function.Injective ι := by
    intro i j hij
    apply Subtype.ext
    apply model.row_injective
    obtain ⟨hi1,hi2,hi3,hi4⟩ := hfixed i.1 i.2
    obtain ⟨hj1,hj2,hj3,hj4⟩ := hfixed j.1 j.2
    apply second_transfer_prmm_index_ext (hi1.trans hj1.symm) (hi2.trans hj2.symm)
      (congrArg Prod.fst hij) (congrArg Prod.snd hij) (hi3.trans hj3.symm)
      (hi4.trans hj4.symm)
  have hs : Summable w := summable_of_hasFiniteSupport
    (second_transfer_prmm_rectangle_hasFiniteSupport c ξ V r A X T)
  have hw0 (p) : 0 ≤ w p := by dsimp [w]; split_ifs <;> positivity
  have hw (i : {i // i ∈ S}) :
      w (ι i) = ‖finiteTestSum model.a model.x i.1 V‖ ^ 2 := by
    obtain ⟨hi1,hi2,hi3,hi4⟩ := hfixed i.1 i.2
    have hv := model.valid i.1
    obtain ⟨hex,htw,hrel,hcoeff,hne,hpos,hdiv,hle,hupper,hprod,hrlo,hrhi,hflo,hfhi⟩ := hv
    have ht : T ≤ normIdeal (model.row i.1).twist ∧
        normIdeal (model.row i.1).twist < 2 * T := by
      simpa only [hi4] using And.intro hflo hfhi
    have hscale : (model.row i.1).columnScale L = X := by
      simp only [SecondTransferIndex.columnScale, hi3, hi4, X]
    rw [model.column_complete i.1 V hV, hi1, hi2, hscale]
    exact if_pos ⟨⟨htw,ht.1,ht.2⟩,hpos,hfreq i.1 i.2⟩
  have heq : (∑' p, w p) = (X * T) * excludedEnergy c ξ V r A X T := by
    rw [hs.tsum_prod]
    have hrow (f : Ideal O) : (∑' k, w (f,k)) =
        if SquarefreeOutside c.S f ∧ T ≤ normIdeal f ∧ normIdeal f < 2 * T then
          rowEnergy (fun k => excludedColumnSum c ξ V r X k f) A else 0 := by
      by_cases hf : SquarefreeOutside c.S f ∧ T ≤ normIdeal f ∧ normIdeal f < 2 * T
      · simp only [w, hf, true_and, if_pos, rowEnergy]
      · simp only [w, hf, false_and, if_false, tsum_zero]
    simp_rw [hrow]
    unfold excludedEnergy
    rw [← mul_assoc, mul_inv_cancel₀ (by dsimp [X,T]; positivity : X * T ≠ 0), one_mul]
  have hcomp := tsum_comp_le_tsum_of_inj hs hw0 hinj
  have hleft : (∑' i : {i // i ∈ S}, w (ι i)) =
      ∑ i ∈ S, ‖finiteTestSum model.a model.x i V‖ ^ 2 := by
    simp only [tsum_fintype, hw]
    exact Finset.sum_coe_sort S (fun i => ‖finiteTestSum model.a model.x i V‖ ^ 2)
  change (∑' i : {i // i ∈ S}, w (ι i)) ≤ ∑' p, w p at hcomp
  rw [hleft, heq] at hcomp
  have hXT : X * T = L / (2 : ℝ) ^ rb := by
    dsimp [X,T]
    field_simp
  simpa only [hXT] using hcomp

/-- The full weighted block bound, with the exact remaining cubic divisor weight.
Only summation of these bounds over characters, ideals and dyadic blocks remains. -/
theorem second_transfer_prmm_weighted_block (he : RemoveExclusionsStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (I : SupportInterval) (m : ℕ)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (model : SecondTransferFiniteModel c I coeffs cI H L F Sigma)
    (V : ℝ → ℂ) (hV : SmoothSupported (enlarged I) V)
    (S : Finset (Fin model.R)) (ξ : RayCharacter c) (r : Ideal O) (rb fb : ℕ)
    (hfixed : ∀ i ∈ S, (model.row i).character = ξ ∧ (model.row i).excluded = r ∧
      (model.row i).rBlock = rb ∧ (model.row i).fBlock = fb)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 1 ≤ F)
    (hSigma : 0 < Sigma) (hHS : H ≤ Sigma) :
    (∑ i ∈ S, model.weight i * ‖finiteTestSum model.a model.x i V‖ ^ 2) ≤
      (cI * Sigma * normIdeal r * (divisorCount r : ℝ) ^ 3 /
        ((2 : ℝ) ^ rb) ^ 2) * ‖coeffs ξ‖ * childSup c I m H L F Sigma *
          weightNorm m V ^ 2 := by
  have hchild := childSup_nonneg c I m H L F Sigma
  have hnr : 0 ≤ normIdeal r := Nat.cast_nonneg _
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi⟩ := hS
    obtain ⟨hi1,hi2,hi3,hi4⟩ := hfixed i hi
    obtain ⟨hr,htw,hrel,hcoeff,hne,hpos,hdiv,hle,hupper,hprod,hrlo,hrhi,hflo,hfhi⟩ :=
      model.valid i
    rw [hi2] at hr hrlo hrhi hupper
    rw [hi3] at hrlo hrhi
    rw [hi4] at hflo
    let R : ℝ := (2 : ℝ) ^ rb
    let T : ℝ := (2 : ℝ) ^ fb
    let A := H * L / (Sigma * F * R ^ 2)
    have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
    have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    have hr0 := normIdeal_pos hr.1.1
    have hactive : T ≤ H * L / (Sigma * F * normIdeal r ^ 2) :=
      hflo.trans (hle.trans hupper)
    have hfreq (j : Fin model.R) (hj : j ∈ S) : normElement (model.row j).frequency ≤ A := by
      obtain ⟨hj1,hj2,hj3,hj4⟩ := hfixed j hj
      have hv := model.valid j
      have hu := hv.2.2.2.2.2.2.2.2.1
      rw [hj2] at hu
      apply hu.trans
      apply div_le_div_of_nonneg_left (mul_pos hH hL).le (by positivity)
      exact mul_le_mul_of_nonneg_left (by nlinarith : R ^ 2 ≤ normIdeal r ^ 2)
        (by positivity)
    have hb := second_transfer_prmm_model_block c I coeffs cI H L F Sigma model V hV
      S ξ r rb fb hfixed A hfreq hL
    have hexc := second_transfer_prmm_excludedEnergy_bound he c hc I m ξ V hV hr
      hH hL hF hSigma hHS hR hrlo hT hactive
    have hrows : (∑ j ∈ S, ‖finiteTestSum model.a model.x j V‖ ^ 2) ≤
        (L / R) * ((divisorCount r : ℝ) ^ 2 * childSup c I m H L F Sigma *
          (L / R) * weightNorm m V ^ 2) :=
      hb.trans (mul_le_mul_of_nonneg_left hexc (div_nonneg hL.le hR0.le))
    let b : ℝ := (cI * Sigma / L ^ 2 * normIdeal r * (divisorCount r : ℝ)) * ‖coeffs ξ‖
    have hb0 : 0 ≤ b := by dsimp [b]; positivity
    have hw (j : Fin model.R) (hj : j ∈ S) : model.weight j = b := by
      obtain ⟨hj1,hj2,hj3,hj4⟩ := hfixed j hj
      simp only [SecondTransferFiniteModel.weight, SecondTransferFiniteModel.phase,
        SecondTransferIndex.phase, hj1, hj2, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity :
          0 ≤ cI * Sigma / L ^ 2 * normIdeal r * (divisorCount r : ℝ)), b]
    calc
      _ = b * ∑ j ∈ S, ‖finiteTestSum model.a model.x j V‖ ^ 2 := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hw j hj]
      _ ≤ b * ((L / R) * ((divisorCount r : ℝ) ^ 2 * childSup c I m H L F Sigma *
          (L / R) * weightNorm m V ^ 2)) := mul_le_mul_of_nonneg_left hrows hb0
      _ = _ := by
        dsimp only [b, R]
        field_simp [hL.ne']
        <;> ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
    positivity

end QRHShort
