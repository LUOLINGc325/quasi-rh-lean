import QRHShort.PoissonReduction
import QRHShort.SecondTransferKernel
import QRHShort.IdealCounting
import QRHShort.EnergySupport
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Literal finite block reduction and the coupled-kernel estimate for the
initial Poisson dyadic blocks. -/

noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators
namespace QRHShort.CloudBatch.DyadicBlock
open PoissonReductionProof

theorem smoothSupported_star_half (I : SupportInterval) (W : ℝ → ℂ)
    (hW : SmoothSupported I W) :
    SmoothSupported (halfEnlarged I) (fun x => star (W x)) := by
  refine ⟨?_, ?_⟩
  · have heq : (Complex.conjLIE ∘ W) = (fun x => star (W x)) := by
      funext x
      exact Complex.conjLIE_apply (W x)
    rw [← heq]
    exact Complex.conjLIE.contDiff.comp hW.1
  intro x hx
  have hw : W x ≠ 0 := by
    intro h
    apply hx
    change star (W x) = 0
    rw [h, star_zero]
  have hbox := hW.2 hw
  dsimp only [halfEnlarged]
  exact ⟨by linarith [I.lo_pos, hbox.1], by linarith [I.lo_pos, I.ordered, hbox.2]⟩

theorem weightNorm_star_le (I : SupportInterval) (W : ℝ → ℂ)
    (hW : SmoothSupported I W) (q : ℕ) :
    weightNorm q (fun x => star (W x)) ≤ weightNorm q W := by
  apply QRHLean3.supZero_le (weightNorm_nonneg hW q)
  rintro v ⟨j, hj, x, rfl⟩
  have heq : ‖iteratedDeriv j (fun x => star (W x)) x‖ = ‖iteratedDeriv j W x‖ := by
    have hcomp : (Complex.conjLIE ∘ W) = (fun x => star (W x)) := by
      funext y
      exact Complex.conjLIE_apply (W y)
    have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left W x j
    rw [hcomp] at h
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using h
  exact heq.trans_le (norm_iteratedDeriv_le_weightNorm hW hj x)

theorem initial_kernel_support (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (hW : SmoothSupported I W) {r : ℝ} (hr : 1 ≤ r) (hr4 : r ≤ 4)
    (a : ℝ) : Function.support (initialKernel Φ W r a) ⊆
      {z | ∀ i : Fin 2, z i ∈ Set.Icc (initialKernelInterval I).lo (initialKernelInterval I).hi} := by
  intro z hz
  have hw₀ : W (r * z 0) ≠ 0 := by
    intro h
    exact hz (by simp only [initialKernel, initialWeight, h, star_zero, mul_zero, zero_mul])
  have hw₁ : W (r * z 1) ≠ 0 := by
    intro h
    exact hz (by simp only [initialKernel, initialWeight, h, star_zero, mul_zero, zero_mul])
  have hcoord (x : ℝ) (hw : W (r * x) ≠ 0) :
      x ∈ Set.Icc (initialKernelInterval I).lo (initialKernelInterval I).hi := by
    have hbox := hW.2 hw
    have hx : 0 < x := (mul_pos_iff_of_pos_left (show 0 < r by linarith)).mp
      (I.lo_pos.trans_le hbox.1)
    dsimp only [initialKernelInterval]
    exact ⟨by nlinarith [hbox.1, mul_le_mul_of_nonneg_right hr4 hx.le],
      by nlinarith [hbox.2, mul_le_mul_of_nonneg_right hr hx.le]⟩
  intro i
  refine Fin.cases (hcoord _ hw₀) (fun k => ?_) i
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  exact hcoord _ hw₁

theorem initial_kernel_uniform_bound (I : SupportInterval) (Φ : RowWeight) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (r a : ℝ), SmoothSupported I W →
      1 ≤ r → r ≤ 4 → 0 ≤ a →
      SmoothBox (fun _ : Fin 2 => initialKernelInterval I) (initialKernel Φ W r a) ∧
        multiWeightNorm q (initialKernel Φ W r a) ≤ K * weightNorm q W ^ 2 := by
  obtain ⟨K, hK, hk⟩ := second_transfer_kernel_bound I Φ q
  refine ⟨K, hK, ?_⟩
  intro W r a hW hr hr4 ha
  have hs := hk (fun x => star (W x)) r a (smoothSupported_star_half I W hW) hr hr4 ha
  have heq : secondTransferKernel Φ (fun x => star (W x)) r a = initialKernel Φ W r a := rfl
  rw [heq] at hs
  refine ⟨⟨hs.1.1, initial_kernel_support I Φ W hW hr hr4 a⟩, ?_⟩
  exact hs.2.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (weightNorm_nonneg (smoothSupported_star_half I W hW) q)
      (weightNorm_nonneg hW q)).mpr (weightNorm_star_le I W hW q)) hK)

def BlockRow (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (D H B F : ℝ) (p : Ideal O × Ideal O × O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ B ≤ normIdeal p.1 ∧ normIdeal p.1 < 2 * B ∧
    SquarefreeOutside c.S p.2.1 ∧ F ≤ normIdeal p.2.1 ∧ normIdeal p.2.1 < 2 * F ∧
    IsRelPrime p.1 p.2.1 ∧ 0 < normElement p.2.2 ∧
    normElement p.2.2 ≤ initialHeight I Φ D H B

theorem block_rows_finite (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (D H B F : ℝ) :
    {p : Ideal O × Ideal O × O | BlockRow c I Φ D H B F p}.Finite := by
  apply ((finite_normIdeal_le (2 * B)).prod
    ((finite_normIdeal_le (2 * F)).prod
      (finite_normElement_le (initialHeight I Φ D H B)))).subset
  intro p hp
  exact ⟨hp.2.2.1.le, hp.2.2.2.2.2.1.le, hp.2.2.2.2.2.2.2.2⟩

def blockJoint (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ) (D H B F : ℝ)
    (p : (Ideal O × Ideal O × O) × (Ideal O × Ideal O)) : ℂ :=
  if BlockRow c I Φ D H B F p.1 then
    (normIdeal p.1.1 : ℂ) * (mobius p.1.2.1 : ℂ) *
      initialPairedTerm c ξ Φ W D H B F p.1.1 p.1.2.1 p.1.2.2 p.2
  else 0

theorem block_joint_hasFiniteSupport (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    Function.HasFiniteSupport (blockJoint c ξ I Φ W D H B F) := by
  have hpair (p : Ideal O × Ideal O × O)
      (hp : BlockRow c I Φ D H B F p) :
      (Function.support (initialPairedTerm c ξ Φ W D H B F p.1 p.2.1 p.2.2)).Finite :=
    initial_pair_finiteSupport c I Φ ξ W D H B F p.1 p.2.1 p.2.2 hW hD hB hF
      hp.1.1.1 hp.2.2.2.1.1.1
  apply ((block_rows_finite c I Φ D H B F).biUnion
    (fun p hp => (hpair p hp).image (fun n : Ideal O × Ideal O => (p, n)))).subset
  intro p hp
  have hr : BlockRow c I Φ D H B F p.1 := by
    by_contra h
    exact hp (by simp only [blockJoint, ite_eq_right h])
  have hn : initialPairedTerm c ξ Φ W D H B F p.1.1 p.1.2.1 p.1.2.2 p.2 ≠ 0 := by
    intro h
    exact hp (by simp only [blockJoint, ite_eq_left hr, h, mul_zero])
  exact Set.mem_iUnion₂.mpr ⟨p.1, hr, ⟨p.2, hn, rfl⟩⟩

theorem block_joint_summable (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    Summable (blockJoint c ξ I Φ W D H B F) :=
  summable_of_hasFiniteSupport
    (block_joint_hasFiniteSupport c ξ I Φ hW hD hB hF H)

theorem initialDyadicBlock_eq_joint (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    initialDyadicBlock c ξ I Φ W D H B F =
      (H / D ^ 2 : ℝ) * ∑' p, blockJoint c ξ I Φ W D H B F p := by
  have hs := block_joint_summable c ξ I Φ hW hD hB hF H
  have hflat : (∑' p, blockJoint c ξ I Φ W D H B F p) =
      ∑' b : Ideal O, ∑' f : Ideal O, ∑' k : O,
        ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
          blockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) := by
    rw [hs.tsum_prod, hs.prod.tsum_prod]
    apply tsum_congr
    intro b
    rw [(hs.prod.prod_factor b).tsum_prod]
    apply tsum_congr
    intro f
    apply tsum_congr
    intro k
    exact (hs.prod_factor (b, f, k)).tsum_prod
  rw [initialDyadicBlock, hflat]
  congr 1
  apply tsum_congr
  intro b
  by_cases hb : SquarefreeOutside c.S b ∧ B ≤ normIdeal b ∧ normIdeal b < 2 * B
  · rw [ite_eq_left hb, ← tsum_mul_left]
    apply tsum_congr
    intro f
    by_cases hf : SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧
        normIdeal f < 2 * F ∧ IsRelPrime b f
    · rw [ite_eq_left hf]
      simp only [← tsum_mul_left]
      apply tsum_congr
      intro k
      by_cases hk : 0 < normElement k ∧ normElement k ≤ initialHeight I Φ D H B
      · rw [ite_eq_left hk]
        simp only [← tsum_mul_left]
        apply tsum_congr
        intro n₁
        apply tsum_congr
        intro n₂
        have hr : BlockRow c I Φ D H B F (b, f, k) :=
          ⟨hb.1, hb.2.1, hb.2.2, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hk.1, hk.2⟩
        simp only [blockJoint, ite_eq_left hr]
        ring
      · have hz (n₁ n₂ : Ideal O) :
            blockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) = 0 := by
          apply ite_eq_right
          intro hr
          exact hk ⟨hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2⟩
        simp only [ite_eq_right hk, mul_zero, hz, tsum_zero]
    · have hz (k : O) (n₁ n₂ : Ideal O) :
          blockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) = 0 := by
        apply ite_eq_right
        intro hr
        exact hf ⟨hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1⟩
      simp only [ite_eq_right hf, mul_zero, hz, tsum_zero]
  · have hz (f : Ideal O) (k : O) (n₁ n₂ : Ideal O) :
        blockJoint c ξ I Φ W D H B F ((b, f, k), (n₁, n₂)) = 0 := by
      apply ite_eq_right
      intro hr
      exact hb ⟨hr.1, hr.2.1, hr.2.2.1⟩
    simp only [ite_eq_right hb, hz, tsum_zero]


theorem squarefree_factor_prod {b : Ideal O} (hb : b ≠ ⊥) (hsq : Squarefree b) :
    (∏ P ∈ primeFactors b, P) = b := by
  have hnodup := (squarefree_iff_nodup_normalizedFactors hb).mp hsq
  have hprod := associated_iff_eq.mp (prod_normalizedFactors hb)
  unfold primeFactors
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  change ((normalizedFactors b).map id).prod = b
  rw [Multiset.map_id]
  exact hprod

theorem squarefree_divisor_count {b : Ideal O} (hb : b ≠ ⊥) (hsq : Squarefree b) :
    divisorCount b ≤ 2 ^ (primeFactors b).card := by
  letI : Fintype {d : Ideal O // d ∣ b} := fintypeSubtypeDvd b hb
  have hd₀ (d : {d : Ideal O // d ∣ b}) : d.val ≠ ⊥ := ne_zero_of_dvd_ne_zero hb d.property
  have hdsq (d : {d : Ideal O // d ∣ b}) : Squarefree d.val := hsq.squarefree_of_dvd d.property
  have hsub (d : {d : Ideal O // d ∣ b}) : primeFactors d.val ⊆ primeFactors b := by
    intro P hP
    exact Multiset.mem_toFinset.mpr
      ((Multiset.subset_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors (hd₀ d) hb).mp
        d.property)) (Multiset.mem_toFinset.mp hP))
  let e : {d : Ideal O // d ∣ b} → {t : Finset (Ideal O) // t ∈ (primeFactors b).powerset} :=
    fun d => ⟨primeFactors d.val, Finset.mem_powerset.mpr (hsub d)⟩
  have he : Function.Injective e := by
    intro d d' h
    have heq : primeFactors d.val = primeFactors d'.val := congrArg Subtype.val h
    apply Subtype.ext
    calc
      d.val = ∏ P ∈ primeFactors d.val, P := (squarefree_factor_prod (hd₀ d) (hdsq d)).symm
      _ = ∏ P ∈ primeFactors d'.val, P := by rw [heq]
      _ = d'.val := squarefree_factor_prod (hd₀ d') (hdsq d')
  have hc := Fintype.card_le_of_injective e he
  simpa only [divisorCount, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powerset] using hc

theorem divisor_count_mono {a b : Ideal O} (hb : b ≠ ⊥) (hab : a ∣ b) :
    divisorCount a ≤ divisorCount b := by
  letI : Fintype {d : Ideal O // d ∣ a} := fintypeSubtypeDvd a (ne_zero_of_dvd_ne_zero hb hab)
  letI : Fintype {d : Ideal O // d ∣ b} := fintypeSubtypeDvd b hb
  let f : {d : Ideal O // d ∣ a} → {d : Ideal O // d ∣ b} :=
    fun d => ⟨d.val, d.property.trans hab⟩
  have hf : Function.Injective f := by
    intro d e h
    apply Subtype.ext
    exact congrArg (fun z : {d : Ideal O // d ∣ b} => z.val) h
  simpa only [divisorCount, Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

theorem outsideRadical_dvd_squarefree (S : Finset (Ideal O)) {b : Ideal O}
    (hb : b ≠ ⊥) (hsq : Squarefree b) : outsideRadical S b ∣ b := by
  change (∏ P ∈ (primeFactors b).filter (fun P => P ∉ S), P) ∣ b
  exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
    (dvd_of_eq (squarefree_factor_prod hb hsq))

theorem radical_divisor_square_le_four_power (S : Finset (Ideal O)) {b : Ideal O}
    (hb : b ≠ ⊥) (hsq : Squarefree b) :
    (divisorCount (outsideRadical S b) : ℝ) ^ 2 ≤ (4 : ℝ) ^ (primeFactors b).card := by
  have h₁ : (divisorCount (outsideRadical S b) : ℝ) ≤ (divisorCount b : ℝ) :=
    Nat.cast_le.mpr (divisor_count_mono hb (outsideRadical_dvd_squarefree S hb hsq))
  have h₂ : (divisorCount b : ℝ) ≤ (2 : ℝ) ^ (primeFactors b).card := by
    exact_mod_cast squarefree_divisor_count hb hsq
  calc
    _ ≤ ((2 : ℝ) ^ (primeFactors b).card) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (h₁.trans h₂) 2
    _ = _ := by rw [pow_two, ← mul_pow]; norm_num

/-- A small-power divisor bound obtained from finite small-prime support.
Only finite ideal norm balls and squarefreeness are used. -/
theorem radical_divisor_square_small_power (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset (Ideal O)) (b : Ideal O),
      b ≠ ⊥ → Squarefree b →
      (divisorCount (outsideRadical S b) : ℝ) ^ 2 ≤ C * normIdeal b ^ δ := by
  let T : ℝ := (4 : ℝ) ^ (1 / δ)
  let Q : Finset (Ideal O) := (finite_normIdeal_le T).toFinset
  have hT : 0 < T := Real.rpow_pos_of_pos (by norm_num) _
  have hTpow : T ^ δ = 4 := by
    dsimp only [T]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [one_div_mul_cancel hδ.ne', Real.rpow_one]
  refine ⟨(4 : ℝ) ^ Q.card, by positivity, ?_⟩
  intro S b hb hsq
  let P : Finset (Ideal O) := primeFactors b
  have hPnorm (p : Ideal O) (hp : p ∈ P) : 1 ≤ normIdeal p := by
    exact normIdeal_one_le (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)).ne_zero
  have hlocal (p : Ideal O) (hp : p ∈ P) :
      (4 : ℝ) ≤ (if p ∈ Q then 4 else 1) * normIdeal p ^ δ := by
    by_cases hq : p ∈ Q
    · rw [ite_eq_left hq]
      exact le_mul_of_one_le_right (by norm_num) (Real.one_le_rpow (hPnorm p hp) hδ.le)
    · rw [ite_eq_right hq, one_mul]
      have hgt : T < normIdeal p := by
        by_contra h
        exact hq ((finite_normIdeal_le T).mem_toFinset.mpr (le_of_not_gt h))
      have h := Real.rpow_le_rpow hT.le hgt.le hδ.le
      rwa [hTpow] at h
  have hsmall : (∏ p ∈ P, if p ∈ Q then (4 : ℝ) else 1) ≤ 4 ^ Q.card := by
    rw [← Finset.prod_filter, Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
    exact Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).2)
  have hnormprod : (∏ p ∈ P, normIdeal p) = normIdeal b := by
    have h := congrArg normIdeal (squarefree_factor_prod hb hsq)
    simpa only [normIdeal, map_prod, Nat.cast_prod] using h
  have hprime : (4 : ℝ) ^ P.card ≤ 4 ^ Q.card * normIdeal b ^ δ := by
    calc
      _ = ∏ _p ∈ P, (4 : ℝ) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ P, (if p ∈ Q then (4 : ℝ) else 1) * normIdeal p ^ δ :=
        Finset.prod_le_prod₀ (fun _ _ => by norm_num) hlocal
      _ = (∏ p ∈ P, if p ∈ Q then (4 : ℝ) else 1) *
          (∏ p ∈ P, normIdeal p ^ δ) := Finset.prod_mul_distrib
      _ ≤ 4 ^ Q.card * (∏ p ∈ P, normIdeal p ^ δ) :=
        mul_le_mul_of_nonneg_right hsmall
          (Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = _ := by
        rw [Real.finsetProd_rpow P normIdeal (fun p _ => Nat.cast_nonneg _) δ, hnormprod]
  exact (radical_divisor_square_le_four_power S hb hsq).trans hprime

theorem radical_divisor_square_active_bound (I : SupportInterval) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset (Ideal O)) (b : Ideal O) (D : ℝ),
      b ≠ ⊥ → Squarefree b → 0 < D → normIdeal b ≤ I.hi * D →
      (divisorCount (outsideRadical S b) : ℝ) ^ 2 ≤ C * D ^ δ := by
  obtain ⟨C, hC, hc⟩ := radical_divisor_square_small_power δ hδ
  have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
  refine ⟨C * I.hi ^ δ, mul_nonneg hC (Real.rpow_nonneg hhi.le _), ?_⟩
  intro S b D hb hsq hD hbound
  calc
    _ ≤ C * normIdeal b ^ δ := hc S b hb hsq
    _ ≤ C * (I.hi * D) ^ δ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hbound hδ.le) hC
    _ = _ := by rw [Real.mul_rpow hhi.le hD.le]; ring

theorem block_pairedTerm_scale_invariant (c : ArithmeticContext)
    (ξ : RayCharacter c) (Φ : RowWeight) (W : ℝ → ℂ)
    {D B F : ℝ} (hD : D ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (H : ℝ) (b f : Ideal O) (k : O) (n : Ideal O × Ideal O) :
    initialPairedTerm c ξ Φ W D H B F b f k n =
      initialAtom c ξ b f k n.1 * star (initialAtom c ξ b f k n.2) *
        (initialWeight W (normIdeal b * normIdeal f * normIdeal n.1 / D) *
          star (initialWeight W (normIdeal b * normIdeal f * normIdeal n.2 / D)) *
          radialFourier (fun t => (Φ.value t : ℂ))
            (H * normElement k / (normIdeal f ^ 2 * normIdeal n.1 * normIdeal n.2))) := by
  have harg (t : ℝ) : normIdeal b * normIdeal f / (B * F) * (t / (D / (B * F))) =
      normIdeal b * normIdeal f * t / D := by
    field_simp
  have hfourier : (H * normElement k / (normIdeal f ^ 2 * (D / (B * F)) ^ 2)) /
      ((normIdeal n.1 / (D / (B * F))) * (normIdeal n.2 / (D / (B * F)))) =
        H * normElement k / (normIdeal f ^ 2 * normIdeal n.1 * normIdeal n.2) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
    field_simp
  simp only [initialPairedTerm, initialKernel, Matrix.cons_val_zero,
    Matrix.cons_val_one, harg, hfourier]

theorem block_pairedTerm_norm_product_bound (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D B F : ℝ}
    (hD : 0 < D) (hB : B ≠ 0) (hF : F ≠ 0) (H : ℝ)
    (b f : Ideal O) (k : O) (n : Ideal O × Ideal O)
    (hn : initialPairedTerm c ξ Φ W D H B F b f k n ≠ 0) :
    normIdeal b * normIdeal f ≤ I.hi * D := by
  have hatom : initialAtom c ξ b f k n.1 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  have hnS : SquarefreeOutside c.S n.1 ∧ IsRelPrime n.1 b := by
    by_contra h
    exact hatom (by simp only [initialAtom, ite_eq_right h])
  have hnorm := normIdeal_one_le hnS.1.1.1
  have hw : W (normIdeal b * normIdeal f * normIdeal n.1 / D) ≠ 0 := by
    intro hz
    apply hn
    rw [block_pairedTerm_scale_invariant c ξ Φ W hD.ne' hB hF]
    simp only [initialWeight, hz, star_zero, mul_zero, zero_mul]
  have hb := (div_le_iff₀ hD).mp (hW.2 hw).2
  exact (le_mul_of_one_le_right
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hnorm).trans hb

theorem initialDyadicBlock_eq_zero_of_B_gt (c : ArithmeticContext)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ}
    (hW : SmoothSupported I W) {D B F : ℝ} (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (H : ℝ) (hlarge : I.hi * D < B) : initialDyadicBlock c ξ I Φ W D H B F = 0 := by
  rw [initialDyadicBlock_eq_joint c ξ I Φ hW hD hB hF H]
  have hzero (p : (Ideal O × Ideal O × O) × (Ideal O × Ideal O)) :
      blockJoint c ξ I Φ W D H B F p = 0 := by
    by_cases hp : BlockRow c I Φ D H B F p.1
    · have hterm : initialPairedTerm c ξ Φ W D H B F p.1.1 p.1.2.1 p.1.2.2 p.2 = 0 := by
        by_contra hn
        have hbound := block_pairedTerm_norm_product_bound c ξ I Φ hW hD
          (zero_lt_one.trans_le hB).ne' (zero_lt_one.trans_le hF).ne' H _ _ _ _ hn
        have hf₁ := normIdeal_one_le hp.2.2.2.1.1.1
        have hb₀ : 0 ≤ normIdeal p.1.1 := Nat.cast_nonneg _
        exact (not_le_of_gt hlarge) (hp.2.1.trans
          ((le_mul_of_one_le_right hb₀ hf₁).trans hbound))
      simp only [blockJoint, ite_eq_left hp, hterm, mul_zero]
    · exact ite_eq_right hp
  simp only [hzero, tsum_zero, mul_zero]

/-- A finite column window which is complete for every test in the outer
smoothing interval; the array is chosen before the test. -/
def blockColumns (I : SupportInterval) (X : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le ((initialTestInterval I).hi * X)).toFinset.filter (fun n => n ≠ ⊥)

theorem mem_blockColumns {I : SupportInterval} {X : ℝ} {n : Ideal O} :
    n ∈ blockColumns I X ↔ normIdeal n ≤ (initialTestInterval I).hi * X ∧ n ≠ ⊥ := by
  simp only [blockColumns, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem initial_column_eq_finite (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) {U : ℝ → ℂ} (hU : SmoothSupported (initialTestInterval I) U)
    {X : ℝ} (hX : 0 < X) (b f : Ideal O) (k : O) :
    excludedColumnSum c ξ U b X k f =
      ∑ n ∈ blockColumns I X, initialAtom c ξ b f k n * U (normIdeal n / X) := by
  have hfun : excludedColumnSum c ξ U b X k f =
      ∑' n : Ideal O, initialAtom c ξ b f k n * U (normIdeal n / X) := by
    unfold excludedColumnSum
    apply tsum_congr
    intro n
    simp only [initialAtom]
    split_ifs <;> simp_all
  rw [hfun]
  apply tsum_eq_sum
  intro n hn
  by_cases hn₀ : n = ⊥
  · subst n
    simp only [initialAtom, SquarefreeOutside, Outside, ne_eq, not_true_eq_false,
      false_and, ite_false, zero_mul]
  · have hzero : U (normIdeal n / X) = 0 := by
      by_contra hu
      exact hn (mem_blockColumns.mpr ⟨(div_le_iff₀ hX).mp (hU.2 hu).2, hn₀⟩)
    rw [hzero, mul_zero]

theorem block_band_weight_count :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 < B →
      (∑ b ∈ boundedDivisibleIdeals 1 (2 * B), normIdeal b) ≤ C * B ^ 2 := by
  obtain ⟨A, hA, hcount⟩ := exists_ideal_norm_count_constant
  refine ⟨4 * A, mul_nonneg (by norm_num) hA.le, ?_⟩
  intro B hB
  calc
    _ ≤ ∑ _b ∈ boundedDivisibleIdeals 1 (2 * B), 2 * B :=
      Finset.sum_le_sum (fun b hb => (mem_boundedDivisibleIdeals.mp hb).1)
    _ = (boundedDivisibleIdeals 1 (2 * B)).card * (2 * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A * (2 * B)) * (2 * B) :=
      mul_le_mul_of_nonneg_right (hcount _ (mul_pos (by norm_num) hB)) (by positivity)
    _ = _ := by ring

/-- The supplied smoothing principle transported to arbitrary finite index
types; its constant still precedes every finite array. -/
theorem finite_type_diagonal_smoothing (hs : SmoothMeanSquareStatement)
    (I Istar : SupportInterval) (J : ℕ) (hlo : Istar.lo < I.lo) (hhi : I.hi < Istar.hi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R N : Type) [Fintype R] [Fintype N]
      (a : R → N → ℂ) (x : R → N → ℝ) (w : R → ℝ) (coeff : R → ℂ)
      (M : ℝ) (K : R → BoxSpace 2 → ℂ),
      (∀ r n, 0 < x r n) → (∀ r, 0 ≤ w r) →
      (∀ r, ‖coeff r‖ ≤ w r) → 0 ≤ M →
      (∀ U : ℝ → ℂ, SmoothSupported Istar U →
        (∑ r : R, w r * ‖∑ n : N, a r n * U (x r n)‖ ^ 2) ≤ M * weightNorm J U ^ 2) →
      (∀ r, SmoothBox (fun _ : Fin 2 => I) (K r)) →
      ‖∑ r : R, coeff r * ∑ n₁ : N, ∑ n₂ : N,
        a r n₁ * star (a r n₂) * K r ![x r n₁, x r n₂]‖ ≤
        C * M * QRHLean3.supZero {v | ∃ r : R, v = multiWeightNorm (2 * J + 4) (K r)} := by
  obtain ⟨C, hC, hc⟩ := diagonal_smoothing hs I Istar J hlo hhi
  refine ⟨C, hC, ?_⟩
  intro R N instR instN a x w coeff M K hx hw hcoeff hM hcommon hkernel
  let eR : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
  let eN : Fin (Fintype.card N) ≃ N := (Fintype.equivFin N).symm
  let aF : Fin (Fintype.card R) → Fin (Fintype.card N) → ℂ := fun r n => a (eR r) (eN n)
  let xF : Fin (Fintype.card R) → Fin (Fintype.card N) → ℝ := fun r n => x (eR r) (eN n)
  have hcommonF : ∀ U : ℝ → ℂ, SmoothSupported Istar U →
      (∑ r : Fin (Fintype.card R), w (eR r) * ‖finiteTestSum aF xF r U‖ ^ 2) ≤
        M * weightNorm J U ^ 2 := by
    intro U hU
    have hcol (r : R) :
        (∑ n : Fin (Fintype.card N), a r (eN n) * U (x r (eN n))) =
          ∑ n : N, a r n * U (x r n) := eN.sum_comp (fun n : N => a r n * U (x r n))
    simp only [finiteTestSum, aF, xF]
    simp_rw [hcol]
    rw [eR.sum_comp (fun r : R => w r * ‖∑ n : N, a r n * U (x r n)‖ ^ 2)]
    exact hcommon U hU
  have hset : {v | ∃ r : Fin (Fintype.card R), v = multiWeightNorm (2 * J + 4) (K (eR r))} =
      {v | ∃ r : R, v = multiWeightNorm (2 * J + 4) (K r)} := by
    ext v
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨eR r, hr⟩
    · rintro ⟨r, hr⟩
      obtain ⟨s, rfl⟩ := eR.surjective r
      exact ⟨s, hr⟩
  have h := hc (Fintype.card R) (Fintype.card N) aF xF
    (fun r => w (eR r)) (fun r => coeff (eR r)) M (fun r => K (eR r))
    (fun r n => hx (eR r) (eN n)) (fun r => hw (eR r))
    (fun r => hcoeff (eR r)) hM hcommonF (fun r => hkernel (eR r))
  have hinner (r : R) :
      (∑ i : Fin (Fintype.card N), ∑ j : Fin (Fintype.card N),
        a r (eN i) * star (a r (eN j)) * K r ![x r (eN i), x r (eN j)]) =
        ∑ i : N, ∑ j : N, a r i * star (a r j) * K r ![x r i, x r j] := by
    calc
      _ = ∑ i : Fin (Fintype.card N), ∑ j : N,
          a r (eN i) * star (a r j) * K r ![x r (eN i), x r j] := by
        apply Finset.sum_congr rfl
        intro i _
        exact eN.sum_comp (fun j : N =>
          a r (eN i) * star (a r j) * K r ![x r (eN i), x r j])
      _ = _ := eN.sum_comp (fun i : N => ∑ j : N,
        a r i * star (a r j) * K r ![x r i, x r j])
  dsimp only [aF, xF] at h
  simp_rw [hinner] at h
  rw [eR.sum_comp (fun r : R => coeff r * ∑ i : N, ∑ j : N,
    a r i * star (a r j) * K r ![x r i, x r j]), hset] at h
  exact h


/-- Full dyadic bands, with the b-f coprimality restriction reserved for the
complex coefficient. This lets a common test use the complete excluded energy. -/
def arrayBand (c : ArithmeticContext) (B : ℝ) : Finset (Ideal O) :=
  (finite_normIdeal_le (2 * B)).toFinset.filter (fun b =>
    SquarefreeOutside c.S b ∧ B ≤ normIdeal b ∧ normIdeal b < 2 * B)

theorem mem_arrayBand {c : ArithmeticContext} {B : ℝ} {b : Ideal O} :
    b ∈ arrayBand c B ↔
      SquarefreeOutside c.S b ∧ B ≤ normIdeal b ∧ normIdeal b < 2 * B := by
  simp only [arrayBand, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.2.2.le, h⟩⟩

def arrayHeight (Y : ℝ) : Finset O :=
  (finite_normElement_le Y).toFinset.filter (fun k => 0 < normElement k)

theorem mem_arrayHeight {Y : ℝ} {k : O} :
    k ∈ arrayHeight Y ↔ 0 < normElement k ∧ normElement k ≤ Y := by
  simp only [arrayHeight, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact and_comm

abbrev ArrayRow (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (D H B F : ℝ) :=
  (arrayBand c B) × (arrayBand c F) × (arrayHeight (initialHeight I Φ D H B))

theorem tsum_arrayBand {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [T2Space α] (c : ArithmeticContext) (B : ℝ) (f : Ideal O → α) :
    (∑' b : Ideal O, if SquarefreeOutside c.S b ∧ B ≤ normIdeal b ∧
      normIdeal b < 2 * B then f b else 0) = ∑ b : arrayBand c B, f b := by
  rw [Finset.sum_coe_sort]
  rw [tsum_eq_sum (s := arrayBand c B) (fun b hb =>
    ite_eq_right (fun h => hb (mem_arrayBand.mpr h)))]
  exact Finset.sum_congr rfl (fun b hb => ite_eq_left (mem_arrayBand.mp hb))

theorem tsum_arrayHeight {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [T2Space α] (Y : ℝ) (f : O → α) :
    (∑' k : O, if 0 < normElement k ∧ normElement k ≤ Y then f k else 0) =
      ∑ k : arrayHeight Y, f k := by
  rw [Finset.sum_coe_sort]
  rw [tsum_eq_sum (s := arrayHeight Y) (fun k hk =>
    ite_eq_right (fun h => hk (mem_arrayHeight.mpr h)))]
  exact Finset.sum_congr rfl (fun k hk => ite_eq_left (mem_arrayHeight.mp hk))

theorem rowEnergy_eq_arrayHeight (column : O → ℂ) (Y : ℝ) :
    rowEnergy column Y = ∑ k : arrayHeight Y, ‖column k‖ ^ 2 :=
  tsum_arrayHeight Y (fun k => ‖column k‖ ^ 2)

/-- The actual finite arrays recover every common-test excluded column. -/
theorem array_column_eq (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) {U : ℝ → ℂ} (hU : SmoothSupported (initialTestInterval I) U)
    {X : ℝ} (hX : 0 < X) (b f : Ideal O) (k : O) :
    (∑ n : blockColumns I X,
      initialAtom c ξ b f k n * U (normIdeal n / X)) =
        excludedColumnSum c ξ U b X k f := by
  calc
    _ = ∑ n ∈ blockColumns I X,
        initialAtom c ξ b f k n * U (normIdeal n / X) :=
      Finset.sum_coe_sort _ (fun n : Ideal O =>
        initialAtom c ξ b f k n * U (normIdeal n / X))
    _ = _ := (initial_column_eq_finite c ξ I hU hX b f k).symm

/-- The finite common-test arrays are bounded by the original full energy,
with its exact height, normalization and divisor-square loss. -/
theorem array_common_test_bound (he : RemoveExclusionsStatement)
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (hc : ArithmeticRelations c) {θ δ K : ℝ} {J : ℕ}
    (hi : InitialBound c (initialTestInterval I) θ (initialGap I Φ) δ J K)
    (ξ : RayCharacter c) (U : ℝ → ℂ) (D B F : ℝ)
    (hU : SmoothSupported (initialTestInterval I) U) (hD : 2 ≤ D)
    (hB : 1 ≤ B) (hF : 1 ≤ F) :
    (∑ r : ArrayRow c I Φ D (D ^ (1 + θ)) B F,
      normIdeal r.1 * ‖∑ n : blockColumns I (D / (B * F)),
        initialAtom c ξ r.1 r.2.1 r.2.2 n * U (normIdeal n / (D / (B * F)))‖ ^ 2) ≤
      ∑ b : arrayBand c B,
        normIdeal b * ((divisorCount (outsideRadical c.S b) : ℝ) ^ 2 *
          K * weightNorm J U ^ 2 * D ^ δ * (D / B) ^ 2) := by
  have hD0 : 0 < D := by linarith
  have hX : 0 < D / (B * F) := div_pos hD0
    (mul_pos (zero_lt_one.trans_le hB) (zero_lt_one.trans_le hF))
  have hH : 0 < initialHeight I Φ D (D ^ (1 + θ)) B := by
    exact div_pos (mul_pos (lt_of_lt_of_le zero_lt_one (initialGap_one_le I Φ))
      (sq_pos_of_pos hD0)) (mul_pos (Real.rpow_pos_of_pos hD0 _)
        (sq_pos_of_pos (zero_lt_one.trans_le hB)))
  simp_rw [array_column_eq c ξ I hU hX]
  simp only [ArrayRow, Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro b _
  simp only [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hrows := excluded_initial_rows_bound he c (initialTestInterval I) hc hi ξ U
    D B F (initialHeight I Φ D (D ^ (1 + θ)) B) b
    (mem_arrayBand.mp b.property).1.1.1 hU hD hB hF hH le_rfl
  rw [tsum_arrayBand c F] at hrows
  simp_rw [rowEnergy_eq_arrayHeight] at hrows
  exact hrows


theorem array_band_weight_bound (c : ArithmeticContext) {A B : ℝ}
    (hA : ∀ B : ℝ, 0 < B →
      (∑ b ∈ boundedDivisibleIdeals 1 (2 * B), normIdeal b) ≤ A * B ^ 2)
    (hB : 0 < B) : (∑ b : arrayBand c B, normIdeal b) ≤ A * B ^ 2 := by
  rw [Finset.sum_coe_sort]
  apply le_trans _ (hA B hB)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro b hb
    have h := mem_arrayBand.mp hb
    exact mem_boundedDivisibleIdeals.mpr ⟨h.2.2.le, one_dvd _, h.1.1.1⟩
  · intro b _ _
    exact Nat.cast_nonneg _

/-- The divisor loss and the complete b-band count give a constant before
all common tests and scales. -/
theorem array_common_test_uniform (he : RemoveExclusionsStatement)
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (hc : ArithmeticRelations c) {θ δ K : ℝ} {J : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hi : InitialBound c (initialTestInterval I) θ (initialGap I Φ) δ J K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : RayCharacter c) (U : ℝ → ℂ) (D B F : ℝ),
      SmoothSupported (initialTestInterval I) U → 2 ≤ D → 1 ≤ B → 1 ≤ F →
      B ≤ I.hi * D →
      (∑ r : ArrayRow c I Φ D (D ^ (1 + θ)) B F,
        normIdeal r.1 * ‖∑ n : blockColumns I (D / (B * F)),
          initialAtom c ξ r.1 r.2.1 r.2.2 n * U (normIdeal n / (D / (B * F)))‖ ^ 2) ≤
        (C * D ^ (2 * δ) * D ^ 2) * weightNorm J U ^ 2 := by
  obtain ⟨A, hA, hcount⟩ := block_band_weight_count
  obtain ⟨Q, hQ, hdiv⟩ := radical_divisor_square_active_bound (initialTestInterval I) δ hδ
  refine ⟨A * Q * K, by positivity, ?_⟩
  intro ξ U D B F hU hD hB hF hactive
  have hD0 : 0 < D := by linarith
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hpow : D ^ δ * D ^ δ = D ^ (2 * δ) := by
    rw [← Real.rpow_add hD0]
    congr 1
    ring
  calc
    _ ≤ ∑ b : arrayBand c B,
        normIdeal b * ((divisorCount (outsideRadical c.S b) : ℝ) ^ 2 *
          K * weightNorm J U ^ 2 * D ^ δ * (D / B) ^ 2) :=
      array_common_test_bound he c I Φ hc hi ξ U D B F hU hD hB hF
    _ ≤ ∑ b : arrayBand c B,
        normIdeal b * (Q * D ^ δ * K * weightNorm J U ^ 2 * D ^ δ * (D / B) ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      have hb := mem_arrayBand.mp b.property
      have hnorm : normIdeal b ≤ (initialTestInterval I).hi * D := by
        dsimp only [initialTestInterval]
        linarith [hb.2.2]
      have hd := hdiv c.S b D hb.1.1.1 hb.1.2 hD0 hnorm
      gcongr
      exact Nat.cast_nonneg _
    _ = (∑ b : arrayBand c B, normIdeal b) *
        (Q * D ^ δ * K * weightNorm J U ^ 2 * D ^ δ * (D / B) ^ 2) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (A * B ^ 2) *
        (Q * D ^ δ * K * weightNorm J U ^ 2 * D ^ δ * (D / B) ^ 2) :=
      mul_le_mul_of_nonneg_right (array_band_weight_bound c hcount hB0) (by positivity)
    _ = _ := by
      have hcancel : B ^ 2 * (D / B) ^ 2 = D ^ 2 := by field_simp
      calc
        _ = (A * Q * K) * (D ^ δ * D ^ δ) *
            (B ^ 2 * (D / B) ^ 2) * weightNorm J U ^ 2 := by ring
        _ = _ := by rw [hpow, hcancel]


theorem array_kernel_ratio (c : ArithmeticContext) {B F : ℝ} (hB : 1 ≤ B) (hF : 1 ≤ F)
    (b : arrayBand c B) (f : arrayBand c F) :
    1 ≤ normIdeal b * normIdeal f / (B * F) ∧
      normIdeal b * normIdeal f / (B * F) ≤ 4 := by
  have hb := mem_arrayBand.mp b.property
  have hf := mem_arrayBand.mp f.property
  have hBF : 0 < B * F := mul_pos (zero_lt_one.trans_le hB) (zero_lt_one.trans_le hF)
  constructor
  · apply (le_div_iff₀ hBF).mpr
    simpa only [one_mul] using
      mul_le_mul hb.2.1 hf.2.1 (by linarith : 0 ≤ F) (Nat.cast_nonneg _)
  · apply (div_le_iff₀ hBF).mpr
    have h := mul_le_mul hb.2.2.le hf.2.2.le (Nat.cast_nonneg _) (by linarith : 0 ≤ 2 * B)
    nlinarith

theorem pairedTerm_column_membership (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D B F : ℝ} (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ)
    (b : arrayBand c B) (f : arrayBand c F) (k : O) (n₁ n₂ : Ideal O)
    (hterm : initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂) ≠ 0) :
    n₁ ∈ blockColumns I (D / (B * F)) ∧ n₂ ∈ blockColumns I (D / (B * F)) := by
  have hX : 0 < D / (B * F) := div_pos hD
    (mul_pos (zero_lt_one.trans_le hB) (zero_lt_one.trans_le hF))
  have hatoms := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).1)
  have hker := (mul_ne_zero_iff.mp hterm).2
  have hratio := array_kernel_ratio c hB hF b f
  have hbox := initial_kernel_support I Φ W hW hratio.1 hratio.2
    (H * normElement k / (normIdeal f ^ 2 * (D / (B * F)) ^ 2)) hker
  have hn₀ (n : Ideal O) (ha : initialAtom c ξ b f k n ≠ 0) : n ≠ ⊥ := by
    intro hn
    subst n
    exact ha (by simp [initialAtom, SquarefreeOutside, Outside])
  have hbound (n : Ideal O) (hn : normIdeal n / (D / (B * F)) ≤ I.hi) :
      normIdeal n ≤ (initialTestInterval I).hi * (D / (B * F)) := by
    have h := (div_le_iff₀ hX).mp hn
    dsimp only [initialTestInterval]
    have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
    nlinarith
  refine ⟨mem_blockColumns.mpr ⟨hbound n₁ ?_, hn₀ n₁ hatoms.1⟩,
    mem_blockColumns.mpr ⟨hbound n₂ ?_, hn₀ n₂ (fun hz => hatoms.2 (by rw [hz, star_zero]))⟩⟩
  · simpa only [Matrix.cons_val_zero, initialKernelInterval] using (hbox 0).2
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, initialKernelInterval] using (hbox 1).2

/-- Both literal ideal sums truncate to a fixed finite column array. -/
theorem pairedTerm_eq_array_columns (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D B F : ℝ} (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ)
    (b : arrayBand c B) (f : arrayBand c F) (k : O) :
    (∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
      initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂)) =
      ∑ n₁ : blockColumns I (D / (B * F)), ∑ n₂ : blockColumns I (D / (B * F)),
        initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂) := by
  have hout (n₁ n₂ : Ideal O) (h : n₁ ∉ blockColumns I (D / (B * F)) ∨
      n₂ ∉ blockColumns I (D / (B * F))) :
      initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂) = 0 := by
    by_contra hz
    have hm := pairedTerm_column_membership c ξ I Φ hW hD hB hF H b f k n₁ n₂ hz
    exact h.elim (fun h => h hm.1) (fun h => h hm.2)
  have hinner (n₁ : Ideal O) :
      (∑ n₂ : blockColumns I (D / (B * F)),
        initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂)) =
      ∑ n₂ ∈ blockColumns I (D / (B * F)),
        initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂) :=
    Finset.sum_coe_sort _ (fun n₂ : Ideal O =>
      initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂))
  simp_rw [hinner]
  rw [Finset.sum_coe_sort _ (fun n₁ : Ideal O =>
    ∑ n₂ ∈ blockColumns I (D / (B * F)),
      initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂))]
  rw [tsum_eq_sum (s := blockColumns I (D / (B * F))) (fun n₁ hn₁ => by
    have hz (n₂ : Ideal O) := hout n₁ n₂ (Or.inl hn₁)
    simp only [hz, tsum_zero])]
  apply Finset.sum_congr rfl
  intro n₁ _
  exact tsum_eq_sum (fun n₂ hn₂ => hout n₁ n₂ (Or.inr hn₂))

def arrayCoefficient (c : ArithmeticContext) {B F : ℝ}
    (b : arrayBand c B) (f : arrayBand c F) : ℂ :=
  if IsRelPrime b.val f.val then (normIdeal b : ℂ) * (mobius f : ℂ) else 0

theorem arrayCoefficient_norm (c : ArithmeticContext) {B F : ℝ}
    (b : arrayBand c B) (f : arrayBand c F) :
    ‖arrayCoefficient c b f‖ ≤ normIdeal b := by
  unfold arrayCoefficient
  split_ifs
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ normIdeal b from Nat.cast_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (norm_mobius_le_one f) (Nat.cast_nonneg _)).trans_eq
      (mul_one _)
  · simp only [norm_zero]
    exact Nat.cast_nonneg _

/-- The original nested block, expressed as genuine finite arrays with a
coefficient carrying exactly its b-f coprimality exclusion. -/
theorem initialDyadicBlock_eq_array (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {D B F : ℝ} (hD : 0 < D) (hB : 1 ≤ B) (hF : 1 ≤ F) (H : ℝ) :
    initialDyadicBlock c ξ I Φ W D H B F =
      (H / D ^ 2 : ℝ) * ∑ r : ArrayRow c I Φ D H B F,
        arrayCoefficient c r.1 r.2.1 *
          ∑ n₁ : blockColumns I (D / (B * F)), ∑ n₂ : blockColumns I (D / (B * F)),
            initialPairedTerm c ξ Φ W D H B F r.1 r.2.1 r.2.2 (n₁,n₂) := by
  rw [initialDyadicBlock]
  congr 1
  rw [tsum_arrayBand c B]
  simp only [ArrayRow, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have hsplit (f : Ideal O) :
      (if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F ∧
          IsRelPrime b.val f then
        (mobius f : ℂ) * ∑' k : O,
          if 0 < normElement k ∧ normElement k ≤ initialHeight I Φ D H B then
            ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
              initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂) else 0
        else 0) =
      (if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F then
        if IsRelPrime b.val f then
          (mobius f : ℂ) * ∑' k : O,
            if 0 < normElement k ∧ normElement k ≤ initialHeight I Φ D H B then
              ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
                initialPairedTerm c ξ Φ W D H B F b f k (n₁,n₂) else 0
        else 0 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hsplit]
  rw [tsum_arrayBand c F, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hbf : IsRelPrime b.val f.val
  · simp only [ite_eq_left hbf, arrayCoefficient]
    rw [tsum_arrayHeight, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    exact pairedTerm_eq_array_columns c ξ I Φ hW hD hB hF H b f k
  · simp only [ite_eq_right hbf, arrayCoefficient, zero_mul, mul_zero,
      Finset.sum_const_zero]


/-- Smoothing the literal finite arrays gives the full dyadic block estimate.
Every constant is fixed before the character, test and scale parameters. -/
theorem initialDyadicBlock_uniform (he : RemoveExclusionsStatement)
    (hs : SmoothMeanSquareStatement) (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (hc : ArithmeticRelations c)
    {θ δ K : ℝ} {J : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hi : InitialBound c (initialTestInterval I) θ (initialGap I Φ) δ J K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ) (D B F : ℝ),
      SmoothSupported I W → 2 ≤ D → 1 ≤ B → 1 ≤ F →
      ‖initialDyadicBlock c ξ I Φ W D (D ^ (1 + θ)) B F‖ ≤
        L * weightNorm (2 * J + 4) W ^ 2 * D ^ (2 * δ) * D ^ (1 + θ) := by
  obtain ⟨Cm, hCm, hcommon⟩ := array_common_test_uniform he c I Φ hc hδ hK hi
  obtain ⟨Cs, hCs, hsmooth⟩ := finite_type_diagonal_smoothing hs
    (initialKernelInterval I) (initialTestInterval I) J
    (initial_intervals_nested I).1 (initial_intervals_nested I).2
  obtain ⟨Ck, hCk, hkernel⟩ := initial_kernel_uniform_bound I Φ (2 * J + 4)
  refine ⟨Cs * Cm * Ck, by positivity, ?_⟩
  intro ξ W D B F hW hD hB hF
  have hD0 : 0 < D := by linarith
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hX : 0 < D / (B * F) := div_pos hD0 (mul_pos hB0 hF0)
  have hH : 0 < D ^ (1 + θ) := Real.rpow_pos_of_pos hD0 _
  have hfinal : 0 ≤ (Cs * Cm * Ck) * weightNorm (2 * J + 4) W ^ 2 *
      D ^ (2 * δ) * D ^ (1 + θ) := by positivity
  by_cases hactive : B ≤ I.hi * D
  swap
  · rw [initialDyadicBlock_eq_zero_of_B_gt c ξ I Φ hW hD0 hB hF _
      (lt_of_not_ge hactive), norm_zero]
    exact hfinal
  let R := ArrayRow c I Φ D (D ^ (1 + θ)) B F
  let N := blockColumns I (D / (B * F))
  let a : R → N → ℂ := fun r n => initialAtom c ξ r.1 r.2.1 r.2.2 n
  let x : R → N → ℝ := fun _ n => normIdeal n / (D / (B * F))
  let w : R → ℝ := fun r => normIdeal r.1
  let coeff : R → ℂ := fun r => arrayCoefficient c r.1 r.2.1
  let ker : R → BoxSpace 2 → ℂ := fun r => initialKernel Φ W
    (normIdeal r.1 * normIdeal r.2.1 / (B * F))
    (D ^ (1 + θ) * normElement r.2.2 /
      (normIdeal r.2.1 ^ 2 * (D / (B * F)) ^ 2))
  let M : ℝ := Cm * D ^ (2 * δ) * D ^ 2
  have hx (r : R) (n : N) : 0 < x r n := by
    exact div_pos (lt_of_lt_of_le zero_lt_one
      (normIdeal_one_le (mem_blockColumns.mp n.property).2)) hX
  have hker (r : R) :
      SmoothBox (fun _ : Fin 2 => initialKernelInterval I) (ker r) ∧
        multiWeightNorm (2 * J + 4) (ker r) ≤ Ck * weightNorm (2 * J + 4) W ^ 2 := by
    have hr := array_kernel_ratio c hB hF r.1 r.2.1
    apply hkernel W _ _ hW hr.1 hr.2
    exact div_nonneg (mul_nonneg hH.le (Nat.cast_nonneg _)) (by positivity)
  have hm : 0 ≤ M := by dsimp only [M]; positivity
  have h := hsmooth R N a x w coeff M ker hx (fun r => Nat.cast_nonneg _)
    (fun r => arrayCoefficient_norm c r.1 r.2.1) hm
    (fun U hU => hcommon ξ U D B F hU hD hB hF hactive) (fun r => (hker r).1)
  have hsup : QRHLean3.supZero {v | ∃ r : R,
      v = multiWeightNorm (2 * J + 4) (ker r)} ≤ Ck * weightNorm (2 * J + 4) W ^ 2 := by
    apply QRHLean3.supZero_le (by positivity)
    rintro v ⟨r, rfl⟩
    exact (hker r).2
  have hbound : ‖∑ r : R, coeff r * ∑ n₁ : N, ∑ n₂ : N,
      a r n₁ * star (a r n₂) * ker r ![x r n₁, x r n₂]‖ ≤
        Cs * M * (Ck * weightNorm (2 * J + 4) W ^ 2) :=
    h.trans (mul_le_mul_of_nonneg_left hsup (mul_nonneg hCs hm))
  rw [initialDyadicBlock_eq_array c ξ I Φ hW hD0 hB hF]
  change ‖((D ^ (1 + θ) / D ^ 2 : ℝ) : ℂ) *
    ∑ r : R, coeff r * ∑ n₁ : N, ∑ n₂ : N,
      a r n₁ * star (a r n₂) * ker r ![x r n₁, x r n₂]‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (D ^ (1 + θ) / D ^ 2) *
        (Cs * M * (Ck * weightNorm (2 * J + 4) W ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      dsimp only [M]
      field_simp
      <;> ring

end QRHShort.CloudBatch.DyadicBlock

namespace QRHShort.CloudBatch

theorem poisson_reduction_dyadic_block_proved :
    PoissonReductionProof.PoissonDyadicBlockInput := by
  intro he hs θ δ J _ _ hδ _ c I Φ hc K hK hi
  exact DyadicBlock.initialDyadicBlock_uniform he hs c I Φ hc hδ hK hi

end QRHShort.CloudBatch
