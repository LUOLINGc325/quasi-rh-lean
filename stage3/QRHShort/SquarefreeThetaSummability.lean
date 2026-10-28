import QRHShort.SquarefreeReflectionPackets
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false

/-! Absolute convergence needed by the reflection-packet reindexing.
The estimates here use only ideal counting and the theta decay premise;
they do not use the prepared mean-square estimate or quadratic sieve.
-/

noncomputable section
open scoped BigOperators Topology
open Classical Filter

namespace QRHShort.SquarefreeAssembly

private theorem reflection_ideal_fiber_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (Nat.card {a : Ideal O // a.absNorm = m} : ℝ) ≤ C * m := by
  obtain ⟨R, ht⟩ : ∃ R : ℝ,
      Tendsto (fun X : ℝ => (Nat.card {a : Ideal O // (a.absNorm : ℝ) ≤ X} : ℝ) / X)
        atTop (𝓝 R) := ⟨_, NumberField.Ideal.tendsto_norm_le_div_atTop K⟩
  obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X in atTop,
      (Nat.card {a : Ideal O // (a.absNorm : ℝ) ≤ X} : ℝ) / X ≤ C := by
    refine ⟨max 1 (R + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    exact ht.eventually_le_const ((lt_add_one _).trans_le (le_max_right _ _))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hbound
  let small := (finite_normIdeal_le (max 1 T)).toFinset
  refine ⟨max C (small.card : ℝ), hC.trans_le (le_max_left _ _), ?_⟩
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcard (X : ℝ) (hmX : (m : ℝ) ≤ X) :
      (Nat.card {a : Ideal O // a.absNorm = m} : ℝ) ≤
        ((finite_normIdeal_le X).toFinset.card : ℝ) := by
    let f : {a : Ideal O // a.absNorm = m} →
        {a // a ∈ (finite_normIdeal_le X).toFinset} := fun a =>
      ⟨a.1, (finite_normIdeal_le X).mem_toFinset.mpr (by
        change (a.1.absNorm : ℝ) ≤ X
        rw [a.2]
        exact hmX)⟩
    have hf : Function.Injective f := by
      intro a b h
      have hh := congrArg Subtype.val h
      exact Subtype.ext hh
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      Nat.card_le_card_of_injective f hf)
  by_cases hTm : T ≤ (m : ℝ)
  · have hlarge : ((finite_normIdeal_le (m : ℝ)).toFinset.card : ℝ) ≤ C * m := by
      have hc := (div_le_iff₀ hm0).mp (hT m hTm)
      have he : (finite_normIdeal_le (m : ℝ)).toFinset.card =
          Nat.card {a : Ideal O // (a.absNorm : ℝ) ≤ m} := by
        change (finite_normIdeal_le (m : ℝ)).toFinset.card =
          {a : Ideal O | normIdeal a ≤ (m : ℝ)}.ncard
        exact (Set.ncard_eq_toFinset_card _ (finite_normIdeal_le (m : ℝ))).symm
      simpa only [he] using hc
    exact (hcard m le_rfl).trans (hlarge.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0.le))
  · have hsmall := hcard (max 1 T) ((not_le.mp hTm).le.trans (le_max_right _ _))
    exact hsmall.trans ((le_max_right C (small.card : ℝ)).trans
      (le_mul_of_one_le_right (hC.trans_le (le_max_left _ _)).le hm1))

theorem reflection_ideal_inv_cube_summable :
    Summable (fun a : Ideal O => (normIdeal a ^ (3 : ℕ))⁻¹) := by
  obtain ⟨C, hC, hcount⟩ := reflection_ideal_fiber_bound
  let coefficient : ℕ → ℝ := fun m =>
    (Nat.card {a : Ideal O // a.absNorm = m} : ℝ) * ((m : ℝ) ^ (3 : ℕ))⁻¹
  have hp : Summable (fun m : ℕ => 1 / (m : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hmajor : Summable (fun m : ℕ => C / ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      ((summable_nat_add_iff 1).mpr hp).mul_left C
  have hcoeff : Summable coefficient := by
    apply (summable_nat_add_iff 1).mp
    apply hmajor.of_nonneg_of_le (fun m => by dsimp [coefficient]; positivity)
    intro m
    have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    calc
      coefficient (m + 1) ≤ (C * ((m + 1 : ℕ) : ℝ)) *
          (((m + 1 : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_right (hcount _ (Nat.succ_pos m)) (by positivity)
      _ = C / ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by field_simp [hm.ne']
  apply (summable_partition (fun a : Ideal O => by
    change 0 ≤ ((a.absNorm : ℝ) ^ (3 : ℕ))⁻¹
    positivity) (s := fun m : ℕ => {a : Ideal O | a.absNorm = m})
    (fun a => ⟨a.absNorm, rfl, fun m hm => hm.symm⟩)).mpr
  constructor
  · intro m
    exact (Ideal.finite_setOfPred_absNorm_eq (S := O) m).summable
      (fun a : Ideal O => (normIdeal a ^ (3 : ℕ))⁻¹)
  · apply hcoeff.congr
    intro m
    letI : Fintype {a : Ideal O // a.absNorm = m} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := O) m).fintype
    symm
    calc
      (∑' a : {a : Ideal O // a.absNorm = m}, (normIdeal a.1 ^ (3 : ℕ))⁻¹) =
          ∑' _a : {a : Ideal O // a.absNorm = m}, ((m : ℝ) ^ (3 : ℕ))⁻¹ := by
        apply tsum_congr
        intro a
        change ((a.1.absNorm : ℝ) ^ (3 : ℕ))⁻¹ = ((m : ℝ) ^ (3 : ℕ))⁻¹
        rw [a.2]
      _ = coefficient m := by
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          coefficient, Nat.card_eq_fintype_card]

private theorem reflection_normIdeal_one_le {a : Ideal O} (ha : a ≠ ⊥) :
    1 ≤ normIdeal a := by
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => ha (Ideal.absNorm_eq_zero_iff.mp h))

/-- A geometric-by-two-ideal majorant for a cubically decaying kernel.
The coefficient array may contain arbitrary column restrictions. -/
theorem reflection_kernel_summable (F : ℝ → ℂ) (t B K : ℝ)
    (ht : 0 < t) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hF : ∀ x : ℝ, 0 < x → ‖F x‖ ≤ K * (x ^ (3 : ℕ))⁻¹)
    (β : ℕ × Ideal O × Ideal O → ℂ) (hβ : ∀ q, ‖β q‖ ≤ B) :
    Summable (fun q : ℕ × Ideal O × Ideal O =>
      ‖if q.2.1 ≠ ⊥ ∧ q.2.2 ≠ ⊥ then
        β q * F (t * (3 : ℝ) ^ q.1 * normIdeal q.2.1 * normIdeal q.2.2 ^ (3 : ℕ))
      else 0‖) := by
  have hg : Summable (fun r : ℕ => ((27 : ℝ)⁻¹) ^ r) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hi := reflection_ideal_inv_cube_summable
  have hij := hi.mul_of_nonneg hi (fun a => by unfold normIdeal; positivity)
    (fun a => by unfold normIdeal; positivity)
  have hs := hg.mul_of_nonneg hij (fun r => by positivity)
    (fun q => by dsimp; unfold normIdeal; positivity)
  apply (hs.mul_left (B * K * (t ^ (3 : ℕ))⁻¹)).of_nonneg_of_le
    (fun q => norm_nonneg _)
  intro q
  by_cases hq : q.2.1 ≠ ⊥ ∧ q.2.2 ≠ ⊥
  · rw [if_pos hq, norm_mul]
    have hn := reflection_normIdeal_one_le hq.1
    have hb := reflection_normIdeal_one_le hq.2
    have hx : 0 < t * (3 : ℝ) ^ q.1 * normIdeal q.2.1 *
        normIdeal q.2.2 ^ (3 : ℕ) := by positivity
    have hbpow : normIdeal q.2.2 ^ (3 : ℕ) ≤ normIdeal q.2.2 ^ (9 : ℕ) :=
      pow_le_pow_right₀ hb (by decide)
    have hbi := inv_le_inv₀ (by positivity : 0 < normIdeal q.2.2 ^ (9 : ℕ))
      (by positivity : 0 < normIdeal q.2.2 ^ (3 : ℕ)) |>.mpr hbpow
    have heq : (t * (3 : ℝ) ^ q.1 * normIdeal q.2.1 *
        normIdeal q.2.2 ^ (3 : ℕ)) ^ (3 : ℕ) =
        t ^ (3 : ℕ) * (27 : ℝ) ^ q.1 * normIdeal q.2.1 ^ (3 : ℕ) *
          normIdeal q.2.2 ^ (9 : ℕ) := by
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm q.1 3, pow_mul]
      norm_num
    calc
      _ ≤ B * (K * ((t * (3 : ℝ) ^ q.1 * normIdeal q.2.1 *
          normIdeal q.2.2 ^ (3 : ℕ)) ^ (3 : ℕ))⁻¹) :=
        mul_le_mul (hβ q) (hF _ hx) (norm_nonneg _) hB
      _ = B * K * (t ^ (3 : ℕ))⁻¹ * ((27 : ℝ)⁻¹) ^ q.1 *
          (normIdeal q.2.1 ^ (3 : ℕ))⁻¹ * (normIdeal q.2.2 ^ (9 : ℕ))⁻¹ := by
        rw [heq]
        simp only [mul_inv_rev, inv_pow]
        ring
      _ ≤ B * K * (t ^ (3 : ℕ))⁻¹ * ((27 : ℝ)⁻¹) ^ q.1 *
          (normIdeal q.2.1 ^ (3 : ℕ))⁻¹ * (normIdeal q.2.2 ^ (3 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_left hbi (by positivity)
      _ = _ := by ring
  · rw [if_neg hq, norm_zero]
    unfold normIdeal
    positivity

theorem smoothSupported_sqrt_mul {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) :
    SmoothSupported I (fun x => (Real.sqrt x : ℂ) * W x) := by
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      have hzero : ∀ᶠ y : ℝ in 𝓝 0, (Real.sqrt y : ℂ) * W y = 0 := by
        filter_upwards [eventually_lt_nhds I.lo_pos] with y hy
        have hyW : W y = 0 := by
          by_contra h
          exact (not_le_of_gt hy) (hW.2 h).1
        simp [hyW]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (Real.contDiffAt_sqrt hx)).mul hW.1.contDiffAt
  · intro x hx
    exact hW.2 (fun h => hx (by simp [h]))

theorem thetaWeight_inverse_cube_bound (hb : ThetaBoundsStatement)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x →
      ‖thetaWeight (fun y => (Real.sqrt y : ℂ) * W y) x‖ ≤
        K * (x ^ (3 : ℕ))⁻¹ := by
  obtain ⟨J, _, hJ⟩ := hb.2.2 3 0 (by norm_num)
  obtain ⟨K, hK, hdecay⟩ := hJ I
  let V : ℝ → ℂ := fun y => (Real.sqrt y : ℂ) * W y
  refine ⟨max 0 (K * weightNorm J V), le_max_left _ _, ?_⟩
  intro x hx
  have h := hdecay V (smoothSupported_sqrt_mul hW) x hx
  change ‖thetaWeight V x‖ ≤ K * weightNorm J V * _ at h
  have hfactor : 0 ≤ K * weightNorm J V := by
    by_contra hn
    have hmin : 0 < min (x ^ (1 / 4 : ℝ)) (x ^ (-(3 : ℝ))) :=
      lt_min (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hx _)
    exact (not_lt_of_ge (norm_nonneg _))
      (h.trans_lt (mul_neg_of_neg_of_pos (lt_of_not_ge hn) hmin))
  calc
    _ ≤ (K * weightNorm J V) * x ^ (-(3 : ℝ)) :=
      h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hfactor)
    _ ≤ max 0 (K * weightNorm J V) * x ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx.le _)
    _ = _ := by simp [Real.rpow_neg hx.le]

/-- The fixed row only needs a finite bound, so no reciprocity lemma is
used in the convergence argument. This is the finite-product estimate
also used for the original compactly supported columns. -/
private theorem reflection_sexticSymbol_bound (k : Ideal O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : O, ‖sexticSymbol k z‖ ≤ B := by
  have hprime (P : Ideal O) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : O, ‖sexticAtPrime P z‖ ≤ B := by
    refine ⟨∑ j ∈ Finset.range 6, ‖embedding (rootSix ^ j)‖,
      Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
    intro z
    unfold sexticAtPrime
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (embedding (rootSix ^ j))
  have hprod (s : Multiset (Ideal O)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : O,
      ‖(s.map (fun P => sexticAtPrime P z)).prod‖ ≤ B := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, zero_le_one, by intro z; simp⟩
    | @cons P s ih =>
      obtain ⟨A, hA, hPA⟩ := hprime P
      obtain ⟨B, hB, hSB⟩ := ih
      refine ⟨A * B, mul_nonneg hA hB, ?_⟩
      intro z
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul (hPA z) (hSB z) (norm_nonneg _) hA
  by_cases hk : k = ⊥
  · exact ⟨0, le_rfl, by intro z; simp only [sexticSymbol, if_pos hk, norm_zero, le_refl]⟩
  · obtain ⟨B, hB, hbound⟩ := hprod (UniqueFactorizationMonoid.normalizedFactors k)
    exact ⟨B, hB, by intro z; simpa only [sexticSymbol, if_neg hk] using hbound z⟩

/-- Absolute convergence of the actual frozen prepared series follows from
theta decay alone, with arbitrary bounded arrays and any nonzero row. -/
theorem preparedThetaTerm_summable_of_thetaBounds (hb : ThetaBoundsStatement)
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    (H Y a : ℝ) (hH : 0 < H) (hY : 0 < Y) (ha : 0 ≤ a)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k : Ideal O) (hk : k ≠ ⊥)
    (hA : ∀ r n b, ‖A r n b‖ ≤ a) (hc : ∀ r, ‖coeff r k‖ ≤ 1) :
    Summable (fun q => ‖preparedThetaTerm W H Y A coeff k q‖) := by
  obtain ⟨K, hK, hF⟩ := thetaWeight_inverse_cube_bound hb hW
  obtain ⟨B, hB, hsymbol⟩ := reflection_sexticSymbol_bound k
  have hkpos : 0 < normIdeal k := lt_of_lt_of_le zero_lt_one (reflection_normIdeal_one_le hk)
  let d : ℝ := (3 : ℝ) ^ (-(4 : ℝ) / 3)
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  let good (n b : Ideal O) : Prop :=
    n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3) ∧
      b ≠ ⊥ ∧ IsRelPrime b (principal 3)
  let den (r : ℕ) (n b : Ideal O) : ℝ :=
    (3 : ℝ) ^ ((((r : ℤ) - 4 : ℤ) : ℝ) / 3) * Real.sqrt (normIdeal n) * normIdeal b
  have hden (r : ℕ) (n b : Ideal O) (hn : n ≠ ⊥) (hb : b ≠ ⊥) : d ≤ den r n b := by
    have hn1 := reflection_normIdeal_one_le hn
    have hb1 := reflection_normIdeal_one_le hb
    have hsqrt : 1 ≤ Real.sqrt (normIdeal n) := by
      simpa using Real.sqrt_le_sqrt hn1
    have hp : d ≤ (3 : ℝ) ^ ((((r : ℤ) - 4 : ℤ) : ℝ) / 3) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      simp only [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    exact hp.trans ((le_mul_of_one_le_right
      (Real.rpow_nonneg (by norm_num) _) hsqrt).trans
        (le_mul_of_one_le_right (by positivity) hb1))
  let β (q : ℕ × Ideal O × Ideal O) : ℂ :=
    if good q.2.1 q.2.2 then
      coeff q.1 k * A q.1 q.2.1 q.2.2 *
        sexticSymbol k (primaryGenerator q.2.1 * primaryGenerator q.2.2) ^ (3 : ℕ) /
          (den q.1 q.2.1 q.2.2 : ℂ)
    else 0
  have hβ (q : ℕ × Ideal O × Ideal O) : ‖β q‖ ≤ a * B ^ (3 : ℕ) / d := by
    dsimp [β]
    split_ifs with hg
    · have hden' := hden q.1 q.2.1 q.2.2 hg.1 hg.2.2.2.1
      have hn : ‖coeff q.1 k * A q.1 q.2.1 q.2.2 *
          sexticSymbol k (primaryGenerator q.2.1 * primaryGenerator q.2.2) ^ (3 : ℕ)‖ ≤
          a * B ^ (3 : ℕ) := by
        simp only [norm_mul, norm_pow]
        calc
          _ ≤ (1 * a) * B ^ (3 : ℕ) :=
            mul_le_mul (mul_le_mul (hc _) (hA _ _ _) (norm_nonneg _) zero_le_one)
              (pow_le_pow_left₀ (norm_nonneg _) (hsymbol _) 3)
              (by positivity) (by positivity)
          _ = _ := by rw [one_mul]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hd.le.trans hden')]
      exact (div_le_div_of_nonneg_right hn (hd.le.trans hden')).trans
        (div_le_div_of_nonneg_left (by positivity) hd hden')
    · simpa only [norm_zero] using (div_nonneg (mul_nonneg ha (pow_nonneg hB _)) hd.le)
  let t : ℝ := H ^ (2 : ℕ) / (81 * Y * normIdeal k ^ (2 : ℕ))
  have ht : 0 < t := by dsimp [t]; positivity
  have hs := reflection_kernel_summable
    (thetaWeight (fun y => (Real.sqrt y : ℂ) * W y)) t
    (a * B ^ (3 : ℕ) / d) K ht (by positivity) hK hF β hβ
  have harg (r : ℕ) (n b : Ideal O) :
      (3 : ℝ) ^ (((r : ℤ) - 4 : ℤ) : ℝ) * normIdeal n * normIdeal b ^ (3 : ℕ) * H ^ (2 : ℕ) /
          (Y * normIdeal k ^ (2 : ℕ)) =
        t * (3 : ℝ) ^ r * normIdeal n * normIdeal b ^ (3 : ℕ) := by
    have hp : (3 : ℝ) ^ (((r : ℤ) - 4 : ℤ) : ℝ) = (3 : ℝ) ^ r / 81 := by
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
        Real.rpow_sub (by norm_num), Real.rpow_natCast]
      norm_num
    rw [hp]
    dsimp [t]
    field_simp [hY.ne', hkpos.ne']
  apply hs.congr
  intro q
  by_cases hg : good q.2.1 q.2.2
  · rw [if_pos ⟨hg.1, hg.2.2.2.1⟩]
    have hg' : q.2.1 ≠ ⊥ ∧ Squarefree q.2.1 ∧ IsRelPrime q.2.1 (principal 3) ∧
        q.2.2 ≠ ⊥ ∧ IsRelPrime q.2.2 (principal 3) := hg
    simp only [β, if_pos hg, preparedThetaTerm, if_pos hg', den, harg]
  · have hterm : preparedThetaTerm W H Y A coeff k q = 0 := by
      exact if_neg hg
    rw [hterm]
    by_cases hn : q.2.1 ≠ ⊥ ∧ q.2.2 ≠ ⊥ <;> simp [hn, β, hg]

/-- The remaining dual-column obligation is the bounded exact identity.
Its absolute-convergence clause is now a theorem above. -/
def DualThetaPacketIdentityStep : Prop :=
  ThetaBoundsStatement →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (W : ℝ → ℂ)
      (D C L X : ℝ) (Q : ℕ) (p : RawReflectionPacket),
      SmoothSupported I W → 2 ≤ D → 1 ≤ C → 1 ≤ L → 0 < X →
      p.Valid c.S D C L X Q →
      ∃ packet : Fin Q → ReflectionPacket,
        (∀ i, (packet i).Valid c.S D C L ∧ (packet i).H = p.H ∧
          (packet i).amplitude ^ 2 * ((packet i).H + (packet i).Y) ≤
            729 * (p.amplitude ^ 2 *
              (p.H + rawReflectionScale X p * rawReflectionCost p))) ∧
        (∀ k ∈ sieveRows c.S p.H,
          rawReflectionRow W X p k = ∑ i,
            preparedThetaRow W (packet i).H (packet i).Y
              (packet i).A (packet i).coeff k)

theorem dual_theta_packet_step_of_identity (hi : DualThetaPacketIdentityStep) :
    DualThetaPacketStep := by
  intro hb c I W D C L X Q p hW hD hC hL hX hp
  obtain ⟨packet, hv, hrow⟩ := hi hb c I W D C L X Q p hW hD hC hL hX hp
  refine ⟨packet, hv, ?_, hrow⟩
  intro i k hk
  obtain ⟨hH, _, hY, _, ha, hA, hc⟩ := (hv i).1
  exact preparedThetaTerm_summable_of_thetaBounds hb hW _ _ _ (by linarith) hY ha
    _ _ k ((mem_sieveRows _ _ _).mp hk).1.1.1 hA
    (fun r => hc r k (by simpa only [(hv i).2.1] using hk))

theorem squarefree_reflection_packet_step_of_identity
    (hraw : SquarefreeRawReflectionStep) (hi : DualThetaPacketIdentityStep) :
    SquarefreeReflectionPacketStep :=
  squarefree_reflection_packet_step_of_children hraw (dual_theta_packet_step_of_identity hi)

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.reflection_ideal_inv_cube_summable
#print axioms QRHShort.SquarefreeAssembly.reflection_kernel_summable
#print axioms QRHShort.SquarefreeAssembly.thetaWeight_inverse_cube_bound
#print axioms QRHShort.SquarefreeAssembly.preparedThetaTerm_summable_of_thetaBounds
#print axioms QRHShort.SquarefreeAssembly.dual_theta_packet_step_of_identity
#print axioms QRHShort.SquarefreeAssembly.squarefree_reflection_packet_step_of_identity
