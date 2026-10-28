import QRHShort.CubeBoundary
import QRHShort.CubeNorm
import QRHShort.IdealHarmonic
import QRHShort.CubeScalar
import QRHShort.Estimates
import QRHLean3.Supremum

/-! Cube reduction from the completed-row estimate.

The long part may be kept as a finite sum over its two cube indices. Two
applications of weighted Cauchy--Schwarz give the same fourth power of a
reciprocal-norm logarithm as grouping by their product. This avoids an extra
divisor regrouping identity without changing the final estimate.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

private theorem cube_sum_subtype {α β : Type*} [AddCommMonoid β]
    (s : Finset α) [Fintype {a // a ∈ s}] (f : α → β) :
    (∑ a : {a // a ∈ s}, f a.val) = ∑ a ∈ s, f a :=
  (Finset.sum_subtype s (fun _ => Iff.rfl) f).symm

private theorem cube_norm_one_le {b : Ideal O} (hb : b ≠ ⊥) :
    1 ≤ normIdeal b := by
  have hn : b.absNorm ≠ 0 := fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)
  change (1 : ℝ) ≤ (b.absNorm : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

/-- A common finite set for both cube indices. -/
def cubeIndexSet (c : ArithmeticContext) (R : ℝ) : Finset (Ideal O) :=
  (boundedDivisibleIdeals 1 R).filter (Outside c.S)

@[simp] theorem mem_cubeIndexSet {c : ArithmeticContext} {R : ℝ} {b : Ideal O} :
    b ∈ cubeIndexSet c R ↔ Outside c.S b ∧ normIdeal b ≤ R := by
  simp only [cubeIndexSet, Finset.mem_filter, mem_boundedDivisibleIdeals]
  constructor
  · rintro ⟨⟨hR, _, _⟩, hb⟩
    exact ⟨hb, hR⟩
  · rintro ⟨hb, hR⟩
    exact ⟨⟨hR, one_dvd _, hb.1⟩, hb⟩

/-- Completion also vanishes when the support lies below the first ideal norm. -/
theorem completedRow_eq_zero_of_support_scale_lt_one (c : ArithmeticContext)
    (ξ : RayCharacter c) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {X : ℝ} (hX : 0 < X)
    (hsmall : I.hi * X < 1) (k : O) (f : Ideal O) :
    completedRow c ξ W X k f = 0 := by
  rw [completedRow_eq_cubeWeight_sum c ξ hW hX k f]
  calc
    _ = ∑' _b : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro b
      by_cases hb : Outside c.S b
      · have hbpos := normIdeal_pos hb.1
        have hL : 0 < X / normIdeal b ^ (3 : ℕ) := div_pos hX (pow_pos hbpos 3)
        have hLX : X / normIdeal b ^ (3 : ℕ) ≤ X :=
          div_le_self hX.le (one_le_pow₀ (cube_norm_one_le hb.1))
        have hIsmall : I.hi * (X / normIdeal b ^ (3 : ℕ)) < 1 :=
          (mul_le_mul_of_nonneg_left hLX (I.lo_pos.trans_le I.ordered).le).trans_lt hsmall
        rw [columnSum_eq_zero_of_support_scale_lt_one hW c ξ hL hIsmall k f, mul_zero]
      · simp only [cubeWeight, if_neg hb, zero_mul]
    _ = 0 := tsum_zero

/-- The same cube-index set works uniformly for every smaller positive scale. -/
theorem completedRow_eq_finite_cube_sum (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {X Y R : ℝ} (hY : 0 < Y) (hYX : Y ≤ X) (hR : 1 ≤ R)
    (hIX : I.hi * X ≤ R) (k : O) (f : Ideal O) :
    completedRow c ξ W Y k f = ∑ b ∈ cubeIndexSet c R,
      cubeWeight c ξ k f b * (Real.sqrt (Y / normIdeal b ^ (3 : ℕ)) : ℂ)⁻¹ *
        columnSum c ξ W (Y / normIdeal b ^ (3 : ℕ)) k f := by
  rw [completedRow_eq_cubeWeight_sum c ξ hW hY k f]
  apply tsum_eq_sum
  intro b hb
  by_cases hbo : Outside c.S b
  · have hbR : R < normIdeal b :=
      lt_of_not_ge (fun h => hb (mem_cubeIndexSet.mpr ⟨hbo, h⟩))
    have hbpos := normIdeal_pos hbo.1
    have hb1 := cube_norm_one_le hbo.1
    have hb3 : normIdeal b ≤ normIdeal b ^ (3 : ℕ) := by
      calc
        normIdeal b = normIdeal b * 1 := (mul_one _).symm
        _ ≤ normIdeal b * normIdeal b ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hb1) hbpos.le
        _ = normIdeal b ^ (3 : ℕ) := by ring
    have hL : 0 < Y / normIdeal b ^ (3 : ℕ) := div_pos hY (pow_pos hbpos 3)
    have hsmall : I.hi * (Y / normIdeal b ^ (3 : ℕ)) < 1 := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (pow_pos hbpos 3)).mpr
      rw [one_mul]
      exact ((mul_le_mul_of_nonneg_left hYX
        (I.lo_pos.trans_le I.ordered).le).trans hIX).trans_lt (hbR.trans_le hb3)
    rw [columnSum_eq_zero_of_support_scale_lt_one hW c ξ hL hsmall k f, mul_zero]
  · simp only [cubeWeight, if_neg hbo, zero_mul]

/-- The outer Möbius inversion is finite with precisely the same cutoff. -/
theorem columnSum_eq_finite_mobius_completedRow (c : ArithmeticContext)
    (ξ : RayCharacter c) {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {X R : ℝ} (hX : 0 < X)
    (hR : 1 ≤ R) (hIX : I.hi * X ≤ R) (k : O) (f : Ideal O) :
    (Real.sqrt X : ℂ)⁻¹ * columnSum c ξ W X k f = ∑ h ∈ cubeIndexSet c R,
      (mobius h : ℂ) * cubeWeight c ξ k f h *
        completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f := by
  rw [columnSum_eq_mobius_completedRow c ξ hW hX k f]
  apply tsum_eq_sum
  intro h hh
  by_cases hho : Outside c.S h
  · have hhR : R < normIdeal h :=
      lt_of_not_ge (fun ht => hh (mem_cubeIndexSet.mpr ⟨hho, ht⟩))
    have hhpos := normIdeal_pos hho.1
    have hh1 := cube_norm_one_le hho.1
    have hh3 : normIdeal h ≤ normIdeal h ^ (3 : ℕ) := by
      calc
        normIdeal h = normIdeal h * 1 := (mul_one _).symm
        _ ≤ normIdeal h * normIdeal h ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hh1) hhpos.le
        _ = normIdeal h ^ (3 : ℕ) := by ring
    have hL : 0 < X / normIdeal h ^ (3 : ℕ) := div_pos hX (pow_pos hhpos 3)
    have hsmall : I.hi * (X / normIdeal h ^ (3 : ℕ)) < 1 := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (pow_pos hhpos 3)).mpr
      rw [one_mul]
      exact hIX.trans_lt (hhR.trans_le hh3)
    rw [completedRow_eq_zero_of_support_scale_lt_one c ξ hW hL hsmall k f, mul_zero]
  · simp only [cubeWeight, if_neg hho, mul_zero, zero_mul]

/-- The long-column supremum is over finitely many actual ideal indices. -/
theorem cubeValues_finite (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (H X F hc : ℝ) : (cubeValues c ξ W H X F hc).Finite := by
  apply ((finite_normIdeal_le X).image
    (fun b => energy c ξ W H (X / normIdeal b ^ (3 : ℕ)) F)).subset
  rintro v ⟨b, hbo, _, hL, hv⟩
  have hbpos := normIdeal_pos hbo.1
  have hb1 := cube_norm_one_le hbo.1
  have hb3 : normIdeal b ≤ normIdeal b ^ (3 : ℕ) := by
    calc
      normIdeal b = normIdeal b * 1 := (mul_one _).symm
      _ ≤ normIdeal b * normIdeal b ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hb1) hbpos.le
      _ = normIdeal b ^ (3 : ℕ) := by ring
  have hbX : normIdeal b ^ (3 : ℕ) < X := by
    simpa only [one_mul] using (lt_div_iff₀ (pow_pos hbpos 3)).mp hL
  exact ⟨b, (hb3.trans hbX.le), hv.symm⟩

/-- Multiplying a long outer index by any nonzero cube index stays long. -/
theorem cube_long_product_mem (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (H X F hc : ℝ) {h b : Ideal O}
    (hh : Outside c.S h) (hb : Outside c.S b) (hhlong : hc < normIdeal h)
    (hL : 1 < X / normIdeal (h * b) ^ (3 : ℕ)) :
    energy c ξ W H (X / normIdeal (h * b) ^ (3 : ℕ)) F ∈
      cubeValues c ξ W H X F hc := by
  refine ⟨h * b, (outside_mul_iff c h b).mpr ⟨hh, hb⟩, ?_, hL, rfl⟩
  rw [normIdeal_mul]
  exact hhlong.trans_le (le_mul_of_one_le_right (normIdeal_pos hh.1).le
    (cube_norm_one_le hb.1))

def cubeRowSet (H : ℝ) : Finset O :=
  (finite_normElement_le H).toFinset.filter
    (fun k => 0 < normElement k ∧ normElement k ≤ H)

def cubeBand (c : ArithmeticContext) (F : ℝ) : Finset (Ideal O) :=
  (boundedDivisibleIdeals 1 (2 * F)).filter
    (fun f => SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F)

theorem rowEnergy_eq_cubeRowSet (U : O → ℂ) (H : ℝ) :
    rowEnergy U H = ∑ k ∈ cubeRowSet H, ‖U k‖ ^ 2 := by
  unfold rowEnergy cubeRowSet
  rw [Finset.sum_filter]
  apply tsum_eq_sum
  intro k hk
  have hp : ¬ (0 < normElement k ∧ normElement k ≤ H) :=
    fun h => hk ((finite_normElement_le H).mem_toFinset.mpr h.2)
  exact if_neg hp

theorem cubeBand_tsum (c : ArithmeticContext) (F : ℝ) (v : Ideal O → ℝ) :
    (∑' f : Ideal O, if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧
        normIdeal f < 2 * F then v f else 0) = ∑ f ∈ cubeBand c F, v f := by
  unfold cubeBand
  rw [Finset.sum_filter]
  apply tsum_eq_sum
  intro f hf
  have hp : ¬ (SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F) :=
    fun h => hf (mem_boundedDivisibleIdeals.mpr ⟨h.2.2.le, one_dvd _, h.1.1.1⟩)
  exact if_neg hp

/-- The normalized squared row norm shared by the short and long parts. -/
def cubeMean (c : ArithmeticContext) (H F : ℝ) (U : O → Ideal O → ℂ) : ℝ :=
  F⁻¹ * ∑ f ∈ cubeBand c F, ∑ k ∈ cubeRowSet H, ‖U k f‖ ^ 2

private theorem cubeMean_eq_subtype_sum (c : ArithmeticContext) (H F : ℝ)
    (U : O → Ideal O → ℂ) :
    cubeMean c H F U =
      ∑ r : {r // r ∈ cubeBand c F ×ˢ cubeRowSet H}, F⁻¹ * ‖U r.val.2 r.val.1‖ ^ 2 := by
  rw [cube_sum_subtype (cubeBand c F ×ˢ cubeRowSet H)
    (fun r : Ideal O × O => F⁻¹ * ‖U r.2 r.1‖ ^ 2)]
  simp only [cubeMean, Finset.sum_product, ← Finset.mul_sum]

theorem cubeMean_nonneg (c : ArithmeticContext) (H : ℝ) {F : ℝ} (hF : 0 ≤ F)
    (U : O → Ideal O → ℂ) : 0 ≤ cubeMean c H F U := by
  apply mul_nonneg (inv_nonneg.mpr hF)
  exact Finset.sum_nonneg (fun f _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))

theorem cubeMean_normColumn (c : ArithmeticContext) (ξ : RayCharacter c)
    (W : ℝ → ℂ) (H F : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    cubeMean c H F (fun k f => (Real.sqrt X : ℂ)⁻¹ * columnSum c ξ W X k f) =
      energy c ξ W H X F := by
  unfold cubeMean energy
  rw [cubeBand_tsum]
  simp_rw [rowEnergy_eq_cubeRowSet, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg X), mul_pow, inv_pow,
    Real.sq_sqrt hX]
  simp only [← Finset.mul_sum, mul_inv_rev]
  ring

theorem cubeMean_add_le (c : ArithmeticContext) (H : ℝ) {F : ℝ} (hF : 0 ≤ F)
    (U V : O → Ideal O → ℂ) :
    cubeMean c H F (fun k f => U k f + V k f) ≤
      2 * cubeMean c H F U + 2 * cubeMean c H F V := by
  have hn (k : O) (f : Ideal O) :
      ‖U k f + V k f‖ ^ 2 ≤ 2 * ‖U k f‖ ^ 2 + 2 * ‖V k f‖ ^ 2 := by
    have hs := norm_add_le (U k f) (V k f)
    nlinarith [norm_nonneg (U k f), norm_nonneg (V k f),
      norm_nonneg (U k f + V k f), sq_nonneg (‖U k f‖ - ‖V k f‖)]
  calc
    _ ≤ F⁻¹ * ∑ f ∈ cubeBand c F, ∑ k ∈ cubeRowSet H,
        (2 * ‖U k f‖ ^ 2 + 2 * ‖V k f‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hF)
      exact Finset.sum_le_sum (fun f _ => Finset.sum_le_sum (fun k _ => hn k f))
    _ = _ := by
      simp only [cubeMean, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

theorem cubeMean_recombine {ι : Type*} [Fintype ι]
    (c : ArithmeticContext) (H : ℝ) {F : ℝ} (hF : 0 ≤ F)
    (b : ι → ℝ) (z U : ι → O → Ideal O → ℂ)
    (hb : ∀ i, 0 ≤ b i) (hz : ∀ i k f, ‖z i k f‖ ≤ b i) :
    cubeMean c H F (fun k f => ∑ i, z i k f * U i k f) ≤
      (∑ i, b i) * ∑ i, b i * cubeMean c H F (U i) := by
  let S := cubeBand c F ×ˢ cubeRowSet H
  have ht := recombine_sum (ρ := {r // r ∈ S})
    (fun _ => F⁻¹) b (fun i r => z i r.val.2 r.val.1)
    (fun i r => U i r.val.2 r.val.1)
    (fun _ => inv_nonneg.mpr hF) hb (fun i r => hz i r.val.2 r.val.1)
  simpa only [S, cubeMean_eq_subtype_sum] using ht

theorem cubeMean_double_recombine {ι τ : Type*} [Fintype ι] [Fintype τ]
    (c : ArithmeticContext) (H : ℝ) {F : ℝ} (hF : 0 ≤ F)
    (a : ι → ℝ) (b : τ → ℝ)
    (z : ι → O → Ideal O → ℂ) (v U : ι → τ → O → Ideal O → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hz : ∀ i k f, ‖z i k f‖ ≤ a i)
    (hv : ∀ i j k f, ‖v i j k f‖ ≤ b j)
    {M : ℝ} (hU : ∀ i j, cubeMean c H F (U i j) ≤ M) :
    cubeMean c H F (fun k f => ∑ i, z i k f * ∑ j, v i j k f * U i j k f) ≤
      (∑ i, a i) ^ 2 * (∑ j, b j) ^ 2 * M := by
  let S := cubeBand c F ×ˢ cubeRowSet H
  have ht := cube_double_recombine (ρ := {r // r ∈ S})
    (fun _ => F⁻¹) a b (fun i r => z i r.val.2 r.val.1)
    (fun i j r => v i j r.val.2 r.val.1)
    (fun i j r => U i j r.val.2 r.val.1)
    (fun _ => inv_nonneg.mpr hF) ha hb
    (fun i r => hz i r.val.2 r.val.1) (fun i j r => hv i j r.val.2 r.val.1)
    (by
      intro i j
      simpa only [S, cubeMean_eq_subtype_sum] using hU i j)
  simpa only [S, cubeMean_eq_subtype_sum] using ht

theorem cubeMean_le_of_rowEnergy_le (c : ArithmeticContext) (H : ℝ) {F : ℝ}
    (hF : 0 < F) (U : O → Ideal O → ℂ) {V C : ℝ} (hV : 0 ≤ V)
    (hcount : ((boundedDivisibleIdeals 1 (2 * F)).card : ℝ) ≤ C * (2 * F))
    (hU : ∀ f ∈ cubeBand c F, rowEnergy (fun k => U k f) H ≤ V) :
    cubeMean c H F U ≤ 2 * C * V := by
  have hcard : ((cubeBand c F).card : ℝ) ≤ C * (2 * F) := by
    apply le_trans _ hcount
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  calc
    cubeMean c H F U = F⁻¹ * ∑ f ∈ cubeBand c F, rowEnergy (fun k => U k f) H := by
      simp only [cubeMean, rowEnergy_eq_cubeRowSet]
    _ ≤ F⁻¹ * ∑ _f ∈ cubeBand c F, V := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hF.le)
      exact Finset.sum_le_sum (fun f hf => hU f hf)
    _ = F⁻¹ * (((cubeBand c F).card : ℝ) * V) := by simp
    _ ≤ F⁻¹ * ((C * (2 * F)) * V) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hV)
        (inv_nonneg.mpr hF.le)
    _ = 2 * C * V := by field_simp [hF.ne']

theorem cubeMean_recombine_uniform {ι : Type*} [Fintype ι]
    (c : ArithmeticContext) (H : ℝ) {F : ℝ} (hF : 0 ≤ F)
    (b : ι → ℝ) (z U : ι → O → Ideal O → ℂ)
    (hb : ∀ i, 0 ≤ b i) (hz : ∀ i k f, ‖z i k f‖ ≤ b i)
    {T : ℝ} (hU : ∀ i, cubeMean c H F (U i) ≤ T) :
    cubeMean c H F (fun k f => ∑ i, z i k f * U i k f) ≤
      (∑ i, b i) ^ 2 * T := by
  calc
    _ ≤ (∑ i, b i) * ∑ i, b i * cubeMean c H F (U i) :=
      cubeMean_recombine c H hF b z U hb hz
    _ ≤ (∑ i, b i) * ∑ i, b i * T := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i _ => hb i))
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hU i) (hb i))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The exact finite cube inversion reduces the energy to uniform completed
short rows and original long columns, with only reciprocal-norm masses. -/
theorem cube_energy_split_bound (c : ArithmeticContext) (ξ : RayCharacter c)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    (H hc : ℝ) {X F R T U : ℝ} (hX : 0 < X) (hF : 0 < F)
    (hR : 1 ≤ R) (hIX : I.hi * X ≤ R) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hshort : ∀ h ∈ cubeIndexSet c R, normIdeal h ≤ hc →
      cubeMean c H F (fun k f => completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f) ≤ T)
    (hlong : ∀ h ∈ cubeIndexSet c R, hc < normIdeal h →
      ∀ b ∈ cubeIndexSet c R,
        energy c ξ W H (X / normIdeal (h * b) ^ (3 : ℕ)) F ≤ U) :
    energy c ξ W H X F ≤
      2 * (∑ b ∈ cubeIndexSet c R, (normIdeal b)⁻¹) ^ 2 * T +
      2 * (∑ b ∈ cubeIndexSet c R, (normIdeal b)⁻¹) ^ 4 * U := by
  let B := cubeIndexSet c R
  let Bs := B.filter (fun h => normIdeal h ≤ hc)
  let Bl := B.filter (fun h => hc < normIdeal h)
  let M := ∑ b ∈ B, (normIdeal b)⁻¹
  let P : O → Ideal O → ℂ := fun k f => ∑ h : {h // h ∈ Bs},
    ((mobius h.val : ℂ) * cubeWeight c ξ k f h.val) *
      completedRow c ξ W (X / normIdeal h.val ^ (3 : ℕ)) k f
  let Q : O → Ideal O → ℂ := fun k f => ∑ h : {h // h ∈ Bl},
    ((mobius h.val : ℂ) * cubeWeight c ξ k f h.val) *
      ∑ b : {b // b ∈ B}, cubeWeight c ξ k f b.val *
        ((Real.sqrt (X / normIdeal (h.val * b.val) ^ (3 : ℕ)) : ℂ)⁻¹ *
          columnSum c ξ W (X / normIdeal (h.val * b.val) ^ (3 : ℕ)) k f)
  have hn (b : Ideal O) : 0 ≤ (normIdeal b)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun b _ => hn b)
  have hmass (S : Finset (Ideal O)) (hSB : S ⊆ B) :
      0 ≤ (∑ b : {b // b ∈ S}, (normIdeal b.val)⁻¹) ∧
      (∑ b : {b // b ∈ S}, (normIdeal b.val)⁻¹) ≤ M := by
    simp only [cube_sum_subtype S (fun b => (normIdeal b)⁻¹)]
    exact ⟨Finset.sum_nonneg (fun b _ => hn b),
      Finset.sum_le_sum_of_subset_of_nonneg hSB (fun b _ _ => hn b)⟩
  have hsMass := hmass Bs (Finset.filter_subset _ _)
  have hlMass := hmass Bl (Finset.filter_subset _ _)
  have hbMass : (∑ b : {b // b ∈ B}, (normIdeal b.val)⁻¹) = M := by
    exact cube_sum_subtype B (fun b => (normIdeal b)⁻¹)
  have hP : cubeMean c H F P ≤ M ^ 2 * T := by
    have ht := cubeMean_recombine_uniform c H hF.le
      (fun h : {h // h ∈ Bs} => (normIdeal h.val)⁻¹)
      (fun h k f => (mobius h.val : ℂ) * cubeWeight c ξ k f h.val)
      (fun h k f => completedRow c ξ W (X / normIdeal h.val ^ (3 : ℕ)) k f)
      (fun h => hn h.val) (fun h k f => norm_mobius_cubeWeight_le c ξ k f h.val)
      (fun h => hshort h.val (Finset.mem_filter.mp h.property).1
        (Finset.mem_filter.mp h.property).2)
    exact ht.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hsMass.1 hsMass.2 2) hT)
  have hQ : cubeMean c H F Q ≤ M ^ 4 * U := by
    have ht := cubeMean_double_recombine c H hF.le
      (fun h : {h // h ∈ Bl} => (normIdeal h.val)⁻¹)
      (fun b : {b // b ∈ B} => (normIdeal b.val)⁻¹)
      (fun h k f => (mobius h.val : ℂ) * cubeWeight c ξ k f h.val)
      (fun _ b k f => cubeWeight c ξ k f b.val)
      (fun h b k f =>
        (Real.sqrt (X / normIdeal (h.val * b.val) ^ (3 : ℕ)) : ℂ)⁻¹ *
          columnSum c ξ W (X / normIdeal (h.val * b.val) ^ (3 : ℕ)) k f)
      (fun h => hn h.val) (fun b => hn b.val)
      (fun h k f => norm_mobius_cubeWeight_le c ξ k f h.val)
      (fun _ b k f => norm_cubeWeight_le c ξ k f b.val)
      (by
        intro h b
        have hho := (mem_cubeIndexSet.mp (Finset.mem_filter.mp h.property).1).1
        have hbo := (mem_cubeIndexSet.mp b.property).1
        have hp := normIdeal_pos ((outside_mul_iff c h.val b.val).mpr ⟨hho, hbo⟩).1
        rw [cubeMean_normColumn c ξ W H F (div_pos hX (pow_pos hp 3)).le]
        exact hlong h.val (Finset.mem_filter.mp h.property).1
          (Finset.mem_filter.mp h.property).2 b.val b.property)
    rw [hbMass] at ht
    apply ht.trans
    calc
      (∑ h : {h // h ∈ Bl}, (normIdeal h.val)⁻¹) ^ 2 * M ^ 2 * U ≤
          M ^ 2 * M ^ 2 * U :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hlMass.1 hlMass.2 2) (sq_nonneg M)) hU
      _ = M ^ 4 * U := by ring
  have hsplit (k : O) (f : Ideal O) :
      (Real.sqrt X : ℂ)⁻¹ * columnSum c ξ W X k f = P k f + Q k f := by
    rw [columnSum_eq_finite_mobius_completedRow c ξ hW hX hR hIX k f]
    have hs := Finset.sum_filter_add_sum_filter_not B
      (fun h => normIdeal h ≤ hc)
      (fun h => (mobius h : ℂ) * cubeWeight c ξ k f h *
        completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f)
    have hsplit' : (∑ h ∈ B, (mobius h : ℂ) * cubeWeight c ξ k f h *
        completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f) =
        P k f + ∑ h : {h // h ∈ Bl}, (mobius h.val : ℂ) * cubeWeight c ξ k f h.val *
          completedRow c ξ W (X / normIdeal h.val ^ (3 : ℕ)) k f := by
      dsimp only [P]
      rw [cube_sum_subtype Bs (fun h => (mobius h : ℂ) * cubeWeight c ξ k f h *
        completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f),
        cube_sum_subtype Bl (fun h => (mobius h : ℂ) * cubeWeight c ξ k f h *
          completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f)]
      simpa only [Bs, Bl, not_le] using hs.symm
    rw [hsplit']
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    have hho := (mem_cubeIndexSet.mp (Finset.mem_filter.mp h.property).1).1
    have hhp := normIdeal_pos hho.1
    have hY : 0 < X / normIdeal h.val ^ (3 : ℕ) := div_pos hX (pow_pos hhp 3)
    have hYX : X / normIdeal h.val ^ (3 : ℕ) ≤ X :=
      div_le_self hX.le (one_le_pow₀ (cube_norm_one_le hho.1))
    rw [completedRow_eq_finite_cube_sum c ξ hW hY hYX hR hIX k f]
    congr 1
    rw [cube_sum_subtype B (fun b => cubeWeight c ξ k f b *
      ((Real.sqrt (X / normIdeal (h.val * b) ^ (3 : ℕ)) : ℂ)⁻¹ *
        columnSum c ξ W (X / normIdeal (h.val * b) ^ (3 : ℕ)) k f))]
    apply Finset.sum_congr rfl
    intro b hb
    have hscale : (X / normIdeal h.val ^ (3 : ℕ)) / normIdeal b ^ (3 : ℕ) =
        X / normIdeal (h.val * b) ^ (3 : ℕ) := by
      rw [normIdeal_mul, mul_pow, div_div]
    rw [hscale]
    ring
  calc
    energy c ξ W H X F =
        cubeMean c H F (fun k f => (Real.sqrt X : ℂ)⁻¹ * columnSum c ξ W X k f) :=
      (cubeMean_normColumn c ξ W H F hX.le).symm
    _ = cubeMean c H F (fun k f => P k f + Q k f) := by
      congr 1
      funext k f
      exact hsplit k f
    _ ≤ 2 * cubeMean c H F P + 2 * cubeMean c H F Q := cubeMean_add_le c H hF.le P Q
    _ ≤ 2 * M ^ 2 * T + 2 * M ^ 4 * U := by linarith [hP, hQ]

/-- The two harmonic sums in the cube expansion cost an arbitrarily small power. -/
theorem exists_cube_mass_power_bound (I : SupportInterval) {C δ : ℝ}
    (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (c : ArithmeticContext) (D X : ℝ),
      2 ≤ D → 1 ≤ X → X ≤ D ^ C →
      (∑ b ∈ cubeIndexSet c (max 1 (I.hi * X)), (normIdeal b)⁻¹) ≤
        A * D ^ δ := by
  obtain ⟨K, hK, hsum⟩ := exists_ideal_harmonic_constant
  let B := max 1 I.hi
  let L := Real.log (2 * B) + C / δ
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hlog : 0 ≤ Real.log (2 * B) := Real.log_nonneg (by linarith)
  have hL : 0 ≤ L := add_nonneg hlog (div_nonneg (zero_le_one.trans hC) hδ.le)
  refine ⟨K * L, mul_nonneg hK.le hL, ?_⟩
  intro c D X hD hX hXC
  have hD1 : 1 ≤ D := by linarith
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hDC : 1 ≤ D ^ C := Real.one_le_rpow hD1 (zero_le_one.trans hC)
  have hDδ : 1 ≤ D ^ δ := Real.one_le_rpow hD1 hδ.le
  let R := max 1 (I.hi * X)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := zero_lt_one.trans_le hR1
  have hRupper : R ≤ B * D ^ C := by
    apply max_le
    · exact hB1.trans (le_mul_of_one_le_right hBpos.le hDC)
    · exact mul_le_mul (le_max_right 1 I.hi) hXC (zero_le_one.trans hX) hBpos.le
  have hlogR : Real.log (2 * R) ≤ L * D ^ δ := by
    calc
      Real.log (2 * R) ≤ Real.log ((2 * B) * D ^ C) := by
        apply Real.log_le_log (by positivity)
        nlinarith only [hRupper]
      _ = Real.log (2 * B) + C * Real.log D := by
        rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hDpos C).ne',
          Real.log_rpow hDpos]
      _ ≤ Real.log (2 * B) * D ^ δ + C * (D ^ δ / δ) := by
        apply add_le_add
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left hDδ hlog
        · exact mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hDpos.le hδ)
            (zero_le_one.trans hC)
      _ = L * D ^ δ := by dsimp [L]; ring
  calc
    (∑ b ∈ cubeIndexSet c R, (normIdeal b)⁻¹) ≤
        ∑ b ∈ boundedDivisibleIdeals 1 R, (normIdeal b)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun b _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ K * Real.log (2 * R) := hsum R hR1
    _ ≤ K * (L * D ^ δ) := mul_le_mul_of_nonneg_left hlogR hK.le
    _ = (K * L) * D ^ δ := by ring

/-- The arithmetic/completed-row hypotheses give the manuscript's actual cube
estimate, with the derivative order chosen before the support interval. -/
theorem cube_estimate_of_arithmetic_completed
    (ha : ArithmeticStatement) (hR : CompletedEstimate) : CubeEstimate := by
  intro C ε hC hε
  obtain ⟨J, hJ, hCompleted₀⟩ := hR (ε / 4) (C + 1) (by positivity) (by linarith)
  refine ⟨J, hJ, ?_⟩
  intro c I hcArith
  obtain ⟨KR, hKR, hCompleted⟩ := hCompleted₀ c I 1 hcArith zero_lt_one
  obtain ⟨CC, hCC, hcount⟩ := exists_ideal_norm_count_constant
  obtain ⟨KB, hKB, hBoundary⟩ := exists_energy_small_scale_base_bound I
  obtain ⟨A, hA, hMass⟩ := exists_cube_mass_power_bound I hC
    (show 0 < ε / 8 by positivity)
  let t := 6 * CC * KR
  let K := 2 * A ^ (2 : ℕ) * t + 2 * A ^ (4 : ℕ) * (KB + 1)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro ξ W D H X F hc hW hD hH hHD hX hXD hF hFD hHX hhc hcut
  have hD1 : 1 ≤ D := by linarith
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  have hDpow : D ^ C ≤ D ^ (C + 1) :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
  have hDsucc : 2 * D ^ C ≤ D ^ (C + 1) := by
    calc
      2 * D ^ C ≤ D * D ^ C :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hDpos.le C)
      _ = D ^ (C + 1) := by rw [Real.rpow_add hDpos, Real.rpow_one]; ring
  let Base := X * F * weightNorm J W ^ (2 : ℕ)
  let S := QRHLean3.supZero (cubeValues c ξ W H X F hc)
  let R := max 1 (I.hi * X)
  let M := ∑ b ∈ cubeIndexSet c R, (normIdeal b)⁻¹
  have hBase : 0 ≤ Base := by dsimp [Base]; positivity
  have hsBound : BddAbove (cubeValues c ξ W H X F hc) :=
    (cubeValues_finite c ξ W H X F hc).bddAbove
  have hS : 0 ≤ S := QRHLean3.supZero_nonneg hsBound
  have hM : 0 ≤ M := Finset.sum_nonneg
    (fun b _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hshort : ∀ h ∈ cubeIndexSet c R, normIdeal h ≤ hc →
      cubeMean c H F (fun k f => completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f) ≤
        t * D ^ (ε / 4) * Base := by
    intro h hh hhshort
    have hho := (mem_cubeIndexSet.mp hh).1
    have hhp := normIdeal_pos hho.1
    have hL := cube_short_scale_range hX hhc hcut (cube_norm_one_le hho.1) hhshort
    have hrow : ∀ f ∈ cubeBand c F,
        rowEnergy (fun k => completedRow c ξ W (X / normIdeal h ^ (3 : ℕ)) k f) H ≤
          KR * D ^ (ε / 4) * weightNorm J W ^ (2 : ℕ) * (3 * (X * F)) := by
      intro f hf
      rcases (Finset.mem_filter.mp hf).2 with ⟨hfsf, hfl, hfu⟩
      have hfnorm : normIdeal f ≤ D ^ (C + 1) :=
        hfu.le.trans ((mul_le_mul_of_nonneg_left hFD (by norm_num)).trans hDsucc)
      have hcomp := hCompleted ξ W D H (X / normIdeal h ^ (3 : ℕ)) f hW hD hfsf
        hH (hHD.trans hDpow) hL.1 (hL.2.trans (hXD.trans hDpow)) (hF.trans hfl) hfnorm
      simp only [one_mul] at hcomp
      apply hcomp.trans
      apply mul_le_mul_of_nonneg_left
        (cube_short_completed_loss hHpos hXpos hFpos.le hHX hhc hcut hhp.le hhshort hfu.le)
      positivity
    calc
      _ ≤ 2 * CC *
          (KR * D ^ (ε / 4) * weightNorm J W ^ (2 : ℕ) * (3 * (X * F))) :=
        cubeMean_le_of_rowEnergy_le c H hFpos _ (by positivity)
          (hcount (2 * F) (by positivity)) hrow
      _ = t * D ^ (ε / 4) * Base := by dsimp [t, Base]; ring
  have hlong : ∀ h ∈ cubeIndexSet c R, hc < normIdeal h →
      ∀ b ∈ cubeIndexSet c R,
        energy c ξ W H (X / normIdeal (h * b) ^ (3 : ℕ)) F ≤ KB * Base + S := by
    intro h hh hhlong b hb
    have hho := (mem_cubeIndexSet.mp hh).1
    have hbo := (mem_cubeIndexSet.mp hb).1
    have hprod := normIdeal_pos ((outside_mul_iff c h b).mpr ⟨hho, hbo⟩).1
    have hLpos : 0 < X / normIdeal (h * b) ^ (3 : ℕ) := div_pos hXpos (pow_pos hprod 3)
    by_cases hL : X / normIdeal (h * b) ^ (3 : ℕ) ≤ 1
    · have hbnd := hBoundary c ξ W J H (X / normIdeal (h * b) ^ (3 : ℕ)) F
        (X * F) hW hHpos hLpos hL hFpos hHX
      have hbnd' : energy c ξ W H (X / normIdeal (h * b) ^ (3 : ℕ)) F ≤ KB * Base := by
        convert hbnd using 1 <;> dsimp [Base] <;> ring
      exact hbnd'.trans (le_add_of_nonneg_right hS)
    · have hmem := cube_long_product_mem c ξ W H X F hc hho hbo hhlong (lt_of_not_ge hL)
      exact (QRHLean3.le_supZero hsBound hmem).trans
        (le_add_of_nonneg_left (mul_nonneg hKB hBase))
  have hsplit := cube_energy_split_bound c ξ hW H hc hXpos hFpos
    (le_max_left 1 (I.hi * X)) (le_max_right 1 (I.hi * X))
    (show 0 ≤ t * D ^ (ε / 4) * Base by positivity)
    (show 0 ≤ KB * Base + S by positivity) hshort hlong
  exact cube_loss_absorb hD1 hε hA hM ht hKB hBase hS
    (hMass c D X hD hX hXD) hsplit

end QRHShort
