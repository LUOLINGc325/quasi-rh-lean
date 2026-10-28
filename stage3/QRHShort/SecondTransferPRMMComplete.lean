import QRHShort.SecondTransferPRMMRows
import QRHShort.IdealCounting
import QRHShort.SecondTransferPRMMExclusion
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import QRHShort.SecondTransferPRMPAbsorb


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def secondTransferMBand (B R : ℝ) : Finset (Ideal O) :=
  (boundedDivisibleIdeals 1 B).filter fun r =>
    Squarefree r ∧ R ≤ normIdeal r ∧ normIdeal r < 2 * R

theorem second_transfer_m_band_bound (B R T A : ℝ)
    (hR : 0 < R) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hcount : ∀ X : ℝ, 0 < X →
      ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ A * X)
    (hdiv : ∀ r ∈ boundedDivisibleIdeals 1 B, Squarefree r →
      (divisorCount r : ℝ)^3 ≤ T) :
    (∑ r ∈ secondTransferMBand B R,
      normIdeal r * (divisorCount r : ℝ)^3 / R^2) ≤ 4*A*T := by
  let S := secondTransferMBand B R
  have hsub : S ⊆ boundedDivisibleIdeals 1 (2*R) := by
    intro r hr
    obtain ⟨hrB,hsf,hlo,hhi⟩ := Finset.mem_filter.mp hr
    exact mem_boundedDivisibleIdeals.mpr
      ⟨hhi.le, one_dvd _, (mem_boundedDivisibleIdeals.mp hrB).2.2⟩
  have hcard : (S.card : ℝ) ≤ A*(2*R) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount _ (by positivity))
  have hterm (r : Ideal O) (hr : r ∈ S) :
      normIdeal r * (divisorCount r : ℝ)^3 / R^2 ≤ 2*T/R := by
    obtain ⟨hrB,hsf,hlo,hhi⟩ := Finset.mem_filter.mp hr
    calc
      _ ≤ (2*R)*T/R^2 := div_le_div_of_nonneg_right
        (mul_le_mul hhi.le (hdiv r hrB hsf) (by positivity) (by positivity)) (sq_nonneg _)
      _ = _ := by field_simp <;> ring
  calc
    _ ≤ ∑ _r ∈ S, 2*T/R := Finset.sum_le_sum hterm
    _ = (S.card : ℝ)*(2*T/R) := by simp
    _ ≤ (A*(2*R))*(2*T/R) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4*A*T := by field_simp <;> ring

/-- A model is partitioned by its actual character, excluded ideal and two
dyadic indices. The resulting bound uses the complete columns in every block. -/
theorem second_transfer_m_grouped_bound (he : RemoveExclusionsStatement)
    (c : ArithmeticContext) (hc : ArithmeticRelations c) (I : SupportInterval) (m : ℕ)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma B T A : ℝ) (N : ℕ)
    (model : SecondTransferFiniteModel c I coeffs cI H L F Sigma)
    (V : ℝ → ℂ) (hV : SmoothSupported (enlarged I) V)
    (hcoeffs : (Function.support coeffs).Finite)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 1 ≤ F)
    (hSigma : 0 < Sigma) (hHS : H ≤ Sigma) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hcount : ∀ X : ℝ, 0 < X →
      ((boundedDivisibleIdeals 1 X).card : ℝ) ≤ A * X)
    (hdiv : ∀ r ∈ boundedDivisibleIdeals 1 B, Squarefree r →
      (divisorCount r : ℝ)^3 ≤ T)
    (hnorm : ∀ i, normIdeal (model.row i).excluded ≤ B)
    (hblock : ∀ i, (model.row i).rBlock < N ∧ (model.row i).fBlock < N) :
    (∑ i, model.weight i * ‖finiteTestSum model.a model.x i V‖^2) ≤
      (4*cI*A*T*(N:ℝ)^2)*Sigma*(∑' ξ, ‖coeffs ξ‖)*
        childSup c I m H L F Sigma * weightNorm m V^2 := by
  let chars := hcoeffs.toFinset
  let ideals := boundedDivisibleIdeals 1 B
  let tag (i : Fin model.R) :=
    ((model.row i).character, ((model.row i).rBlock,
      ((model.row i).fBlock, (model.row i).excluded)))
  let G := chars ×ˢ (Finset.range N ×ˢ (Finset.range N ×ˢ ideals))
  let W (i : Fin model.R) := model.weight i * ‖finiteTestSum model.a model.x i V‖^2
  let Q := childSup c I m H L F Sigma * weightNorm m V^2
  have hQ : 0 ≤ Q := mul_nonneg (childSup_nonneg ..) (sq_nonneg _)
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin model.R)), tag i ∈ G := by
    intro i _
    have hv := model.valid i
    exact Finset.mem_product.mpr ⟨hcoeffs.mem_toFinset.mpr hv.2.2.2.1,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hblock i).1,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hblock i).2,
          mem_boundedDivisibleIdeals.mpr ⟨hnorm i, one_dvd _, hv.1.1.1⟩⟩⟩⟩
  let fiber (ξ : RayCharacter c) (rb fb : ℕ) (r : Ideal O) :=
    Finset.univ.filter fun i : Fin model.R => tag i = (ξ,(rb,(fb,r)))
  have hfixed (ξ : RayCharacter c) (rb fb : ℕ) (r : Ideal O)
      (i : Fin model.R) (hi : i ∈ fiber ξ rb fb r) :
      (model.row i).character=ξ ∧ (model.row i).excluded=r ∧
      (model.row i).rBlock=rb ∧ (model.row i).fBlock=fb := by
    have ht := (Finset.mem_filter.mp hi).2
    dsimp only [tag] at ht
    simp only [Prod.mk.injEq] at ht
    exact ⟨ht.1,ht.2.2.2,ht.2.1,ht.2.2.1⟩
  have hfiber (ξ : RayCharacter c) (rb fb : ℕ) (r : Ideal O) :
      (∑ i ∈ fiber ξ rb fb r, W i) ≤
        if Squarefree r ∧ (2:ℝ)^rb ≤ normIdeal r ∧ normIdeal r < 2*(2:ℝ)^rb
        then (cI*Sigma*(normIdeal r*(divisorCount r:ℝ)^3/((2:ℝ)^rb)^2))*‖coeffs ξ‖*Q
        else 0 := by
    split_ifs with hr
    · have hh := second_transfer_prmm_weighted_block he c hc I m coeffs cI H L F Sigma
        model V hV (fiber ξ rb fb r) ξ r rb fb (hfixed ξ rb fb r)
        hcI hH hL hF hSigma hHS
      convert hh using 1 <;> dsimp [W,Q] <;> ring
    · have hempty : fiber ξ rb fb r = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨_,hir,hib,_⟩ := hfixed ξ rb fb r i hi
        obtain ⟨hsf,_,_,_,_,_,_,_,_,_,hlo,hhi,_,_⟩ := model.valid i
        apply hr
        simpa only [hir,hib] using And.intro hsf.2 (And.intro hlo hhi)
      simp [hempty]
  have hideals (ξ : RayCharacter c) (rb fb : ℕ) :
      (∑ r ∈ ideals, ∑ i ∈ fiber ξ rb fb r, W i) ≤
        (4*cI*Sigma*A*T)*‖coeffs ξ‖*Q := by
    have hpos : 0 < (2:ℝ)^rb := by positivity
    calc
      _ ≤ ∑ r ∈ ideals,
          if Squarefree r ∧ (2:ℝ)^rb ≤ normIdeal r ∧ normIdeal r < 2*(2:ℝ)^rb
          then (cI*Sigma*(normIdeal r*(divisorCount r:ℝ)^3/((2:ℝ)^rb)^2))*‖coeffs ξ‖*Q
          else 0 := Finset.sum_le_sum (fun r _ => hfiber ξ rb fb r)
      _ = (cI*Sigma*‖coeffs ξ‖*Q)*
          (∑ r ∈ secondTransferMBand B ((2:ℝ)^rb),
            normIdeal r*(divisorCount r:ℝ)^3/((2:ℝ)^rb)^2) := by
        rw [Finset.mul_sum]
        simp only [secondTransferMBand, Finset.sum_filter, ideals]
        apply Finset.sum_congr rfl
        intro r _
        split_ifs <;> ring
      _ ≤ (cI*Sigma*‖coeffs ξ‖*Q)*(4*A*T) :=
        mul_le_mul_of_nonneg_left (second_transfer_m_band_bound B _ T A hpos hT hA
          hcount hdiv) (by positivity)
      _ = _ := by ring
  have hsplit := Finset.sum_fiberwise_of_maps_to hmaps W
  have hchars : (∑ ξ ∈ chars, ‖coeffs ξ‖) = ∑' ξ, ‖coeffs ξ‖ := by
    symm
    apply tsum_eq_sum
    intro ξ hξ
    have hh : coeffs ξ=0 := by
      by_contra hn
      exact hξ (hcoeffs.mem_toFinset.mpr hn)
    simp [hh]
  calc
    _ = ∑ ξ ∈ chars, ∑ rb ∈ Finset.range N, ∑ fb ∈ Finset.range N,
          ∑ r ∈ ideals, ∑ i ∈ fiber ξ rb fb r, W i := by
      rw [← hsplit]
      simp only [G, Finset.sum_product]
      rfl
    _ ≤ ∑ ξ ∈ chars, ∑ _rb ∈ Finset.range N, ∑ _fb ∈ Finset.range N,
          (4*cI*Sigma*A*T)*‖coeffs ξ‖*Q := by
      apply Finset.sum_le_sum
      intro ξ _
      apply Finset.sum_le_sum
      intro rb _
      exact Finset.sum_le_sum (fun fb _ => hideals ξ rb fb)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum, hchars]
      dsimp [Q]
      ring

end QRHShort



noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort

private theorem second_m_squarefree_divisor_eq_prod {r d : Ideal O}
    (hr : r ≠ 0) (hd : d ∣ r) (hsq : Squarefree d) :
    ∃ t ⊆ (normalizedFactors r).toFinset, (∏ p ∈ t, p) = d := by
  have hd0 : d ≠ 0 := by
    intro hz
    apply hr
    simpa only [hz, zero_dvd_iff] using hd
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hd0 hr).mp hd
  have hnodup := (squarefree_iff_nodup_normalizedFactors hd0).mp hsq
  refine ⟨(normalizedFactors d).toFinset, ?_, ?_⟩
  · intro p hp
    exact Multiset.mem_toFinset.mpr
      (Multiset.subset_of_le hle (Multiset.mem_toFinset.mp hp))
  · calc
      (∏ p ∈ (normalizedFactors d).toFinset, p) =
          (normalizedFactors d).toFinset.val.prod := (Finset.prod_val _).symm
      _ = (normalizedFactors d).prod := by rw [Multiset.toFinset_val, hnodup.dedup]
      _ = d := Ideal.prod_normalizedFactors_eq_self
        (by simpa only [Ideal.zero_eq_bot] using hd0)

/-- Every divisor of a squarefree ideal is obtained from a subset of its actual
prime support. In particular the literal ideal-divisor count has this bound. -/
theorem second_transfer_m_squarefree_divisorCount_le_two_pow (r : Ideal O)
    (hsf : Squarefree r) :
    divisorCount r ≤ 2^((normalizedFactors r).toFinset.card) := by
  have hr0 : r ≠ 0 := hsf.ne_zero
  have hr : r ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hr0
  have hcard : divisorCount r = (secondTransferPRMMDivisors r hr).card :=
    (second_transfer_prmm_divisors_card r hr).symm
  rw [hcard]
  calc
    (secondTransferPRMMDivisors r hr).card ≤ ((normalizedFactors r).toFinset.powerset).card := by
      apply Finset.card_le_card_of_surjOn (fun t : Finset (Ideal O) => ∏ p ∈ t, p)
      intro d hd
      have hdvd : d ∣ r := (mem_secondTransferPRMMDivisors r hr d).mp hd
      obtain ⟨t, ht, hprod⟩ := second_m_squarefree_divisor_eq_prod hr0 hdvd
        (Squarefree.squarefree_of_dvd hdvd hsf)
      exact ⟨t, Finset.mem_powerset.mpr ht, hprod⟩
    _ = _ := Finset.card_powerset _

/-- The cube of the actual divisor count is uniformly bounded by every positive
power of the ideal norm on squarefree ideals. No arithmetic law is assumed. -/
theorem second_transfer_m_squarefree_divisorCount_cube_soft_bound :
    ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧ ∀ r : Ideal O, Squarefree r →
      (divisorCount r : ℝ)^3 ≤ K*(normIdeal r)^δ := by
  intro δ hδ
  let B : ℝ := (8 : ℝ)^(δ⁻¹)
  let S : Finset (Ideal O) := (finite_normIdeal_le B).toFinset
  let f : Ideal O → ℝ := fun p => if p ∈ S then 8 else 1
  refine ⟨(8 : ℝ)^S.card, by positivity, ?_⟩
  intro r hsf
  have hr0 : r ≠ 0 := hsf.ne_zero
  have hr : r ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hr0
  let P : Finset (Ideal O) := (normalizedFactors r).toFinset
  have hN0 (p : Ideal O) : 0 ≤ normIdeal p := by
    change (0 : ℝ) ≤ (p.absNorm : ℝ)
    positivity
  have hN1 (p : Ideal O) (hp : p ∈ P) : 1 ≤ normIdeal p := by
    have hp0 : p ≠ ⊥ := by
      simpa only [Ideal.zero_eq_bot] using
        (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)).ne_zero
    change (1 : ℝ) ≤ (p.absNorm : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (fun he => hp0 (Ideal.absNorm_eq_zero_iff.mp he)))
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by norm_num) _
  have hBpow : B^δ = 8 := by
    exact Real.rpow_inv_rpow (by norm_num) hδ.ne'
  have hlocal (p : Ideal O) (hp : p ∈ P) : (8 : ℝ) ≤ f p*(normIdeal p)^δ := by
    dsimp only [f]
    split_ifs with hs
    · have hnp : 1 ≤ (normIdeal p)^δ := Real.one_le_rpow (hN1 p hp) hδ.le
      simpa using mul_le_mul_of_nonneg_left hnp (by norm_num : (0 : ℝ) ≤ 8)
    · have hbig : B ≤ normIdeal p := by
        apply le_of_lt
        apply lt_of_not_ge
        intro hle
        exact hs ((finite_normIdeal_le B).mem_toFinset.mpr hle)
      simpa only [one_mul, hBpow] using Real.rpow_le_rpow hB0 hbig hδ.le
  have hsmall : (∏ p ∈ P, f p) ≤ (8 : ℝ)^S.card := by
    calc
      (∏ p ∈ P, f p) = (8 : ℝ)^(P.filter (fun p => p ∈ S)).card := by
        dsimp only [f]
        rw [Finset.prod_ite]
        simp
      _ ≤ _ := pow_le_pow_right₀ (by norm_num)
        (Finset.card_le_card (by intro p hp; exact (Finset.mem_filter.mp hp).2))
  have hprod : (∏ p ∈ P, p) = r := by
    have hnodup := (squarefree_iff_nodup_normalizedFactors hr0).mp hsf
    calc
      (∏ p ∈ P, p) = (normalizedFactors r).toFinset.val.prod := (Finset.prod_val _).symm
      _ = (normalizedFactors r).prod := by rw [Multiset.toFinset_val, hnodup.dedup]
      _ = r := Ideal.prod_normalizedFactors_eq_self hr
  have hnormprod : (∏ p ∈ P, normIdeal p) = normIdeal r := by
    have hn : normIdeal (∏ p ∈ P, p) = ∏ p ∈ P, normIdeal p := by
      simp only [normIdeal, map_prod, Nat.cast_prod]
    rw [hprod] at hn
    exact hn.symm
  have hnormpow : (∏ p ∈ P, (normIdeal p)^δ) = (normIdeal r)^δ := by
    rw [Real.finsetProd_rpow P normIdeal (fun p _ => hN0 p) δ, hnormprod]
  have hτ : (divisorCount r : ℝ) ≤ (2 : ℝ)^P.card := by
    exact_mod_cast second_transfer_m_squarefree_divisorCount_le_two_pow r hsf
  have hcube : (divisorCount r : ℝ)^3 ≤ (8 : ℝ)^P.card := by
    calc
      _ ≤ ((2 : ℝ)^P.card)^3 := pow_le_pow_left₀ (by positivity) hτ 3
      _ = ((2 : ℝ)^3)^P.card := by rw [← pow_mul, ← pow_mul, Nat.mul_comm P.card 3]
      _ = _ := by norm_num
  apply hcube.trans
  calc
    (8 : ℝ)^P.card = ∏ _p ∈ P, (8 : ℝ) := by simp
    _ ≤ ∏ p ∈ P, f p*(normIdeal p)^δ :=
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) hlocal
    _ = (∏ p ∈ P, f p)*(∏ p ∈ P, (normIdeal p)^δ) := Finset.prod_mul_distrib
    _ ≤ (8 : ℝ)^S.card*(∏ p ∈ P, (normIdeal p)^δ) :=
      mul_le_mul_of_nonneg_right hsmall
        (Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (hN0 p) δ))
    _ = (8 : ℝ)^S.card*(normIdeal r)^δ := by rw [hnormpow]

end QRHShort



noncomputable section

namespace QRHShort

/-- Number of nonnegative dyadic exponents whose lower endpoint can lie in
the genuine outer ideal norm window. -/
def secondTransferMDyadicCount (I : SupportInterval) (L : ℝ) : ℕ :=
  Nat.floor (Real.log (secondTransferPRMPRadius I L) / Real.log 2) + 1

theorem second_transfer_m_dyadic_lt (I : SupportInterval) (L : ℝ) (n : ℕ)
    (hn : (2 : ℝ)^n ≤ secondTransferPRMPRadius I L) :
    n < secondTransferMDyadicCount I L := by
  have hB : 1 ≤ secondTransferPRMPRadius I L := le_max_left _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (secondTransferPRMPRadius I L) := Real.log_nonneg hB
  have hquot : 0 ≤ Real.log (secondTransferPRMPRadius I L) / Real.log 2 :=
    div_nonneg hlog hl2.le
  have hp := Real.le_log_of_pow_le (show (0 : ℝ) < 2 by norm_num) hn
  have hcast : (n : ℝ) ≤ Real.log (secondTransferPRMPRadius I L) / Real.log 2 :=
    (le_div_iff₀ hl2).mpr hp
  have hf := (Nat.le_floor_iff hquot).mpr hcast
  exact Nat.lt_succ_of_le hf

theorem second_transfer_m_dyadic_count_le_log (I : SupportInterval) (L : ℝ) :
    (secondTransferMDyadicCount I L : ℝ) ≤
      Real.log (2*secondTransferPRMPRadius I L) / Real.log 2 := by
  have hB : 1 ≤ secondTransferPRMPRadius I L := le_max_left _ _
  have hB0 : 0 < secondTransferPRMPRadius I L := zero_lt_one.trans_le hB
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (secondTransferPRMPRadius I L) := Real.log_nonneg hB
  have hf := Nat.floor_le (div_nonneg hlog hl2.le)
  calc
    (secondTransferMDyadicCount I L : ℝ) ≤
        Real.log (secondTransferPRMPRadius I L) / Real.log 2 + 1 := by
      simpa only [secondTransferMDyadicCount, Nat.cast_add, Nat.cast_one] using
        add_le_add hf (le_refl (1 : ℝ))
    _ = Real.log (2*secondTransferPRMPRadius I L) / Real.log 2 := by
      rw [Real.log_mul (by norm_num) hB0.ne']
      field_simp [hl2.ne']
      <;> ring

theorem second_transfer_m_dyadic_sq_le_log_cube (I : SupportInterval) (L : ℝ) :
    (secondTransferMDyadicCount I L : ℝ)^2 ≤
      Real.log (2*secondTransferPRMPRadius I L)^3 / (Real.log 2)^3 := by
  have hB : 1 ≤ secondTransferPRMPRadius I L := le_max_left _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (2*secondTransferPRMPRadius I L) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hq : 1 ≤ Real.log (2*secondTransferPRMPRadius I L) / Real.log 2 :=
    (le_div_iff₀ hl2).mpr (by simpa using hl)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (secondTransferMDyadicCount I L))
    (second_transfer_m_dyadic_count_le_log I L) 2
  have hmul := mul_le_mul_of_nonneg_right hq
    (sq_nonneg (Real.log (2*secondTransferPRMPRadius I L) / Real.log 2))
  calc
    (secondTransferMDyadicCount I L : ℝ)^2 ≤
        (Real.log (2*secondTransferPRMPRadius I L) / Real.log 2)^2 := hs
    _ ≤ (Real.log (2*secondTransferPRMPRadius I L) / Real.log 2)^3 := by nlinarith
    _ = Real.log (2*secondTransferPRMPRadius I L)^3 / (Real.log 2)^3 := by rw [div_pow]

/-- Fixed loss allocation: the outer norm power costs epsilon/2 and the
complete two-block dyadic count costs the remaining epsilon/2. The constant
is selected before D and L. -/
theorem second_transfer_m_dyadic_scale_absorb (C ε : ℝ) (I : SupportInterval)
    (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D L : ℝ, 2 ≤ D → 1 ≤ L → L ≤ D^C →
      secondTransferPRMPRadius I L ^ (ε/(2*C)) *
        (secondTransferMDyadicCount I L : ℝ)^2 ≤ K*D^ε := by
  let A : ℝ := max 1 (2*I.hi)
  let δ : ℝ := ε/(2*C)
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Kl, hKl, hlog⟩ := second_transfer_prmp_log_cube_absorb C (ε/2) I hC (by positivity)
  refine ⟨A^δ*Kl/(Real.log 2)^3, by positivity, ?_⟩
  intro D L hD hL hLD
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  have hDC : 1 ≤ D^C := Real.one_le_rpow hD1 (zero_le_one.trans hC)
  have hB : 1 ≤ secondTransferPRMPRadius I L := le_max_left _ _
  have hBD : secondTransferPRMPRadius I L ≤ A*D^C := by
    apply max_le
    · exact hDC.trans (le_mul_of_one_le_left (Real.rpow_nonneg hD0.le _) hA)
    · exact mul_le_mul (le_max_right _ _) hLD (by linarith) hA0.le
  have hCδ : C*δ = ε/2 := by
    dsimp only [δ]
    field_simp [hC0.ne']
    <;> ring
  have hpow : secondTransferPRMPRadius I L^δ ≤ A^δ*D^(ε/2) := by
    calc
      secondTransferPRMPRadius I L^δ ≤ (A*D^C)^δ :=
        Real.rpow_le_rpow (zero_le_one.trans hB) hBD hδ.le
      _ = A^δ*D^(ε/2) := by
        rw [Real.mul_rpow hA0.le (Real.rpow_nonneg hD0.le _),
          ← Real.rpow_mul hD0.le, hCδ]
  have hcount : (secondTransferMDyadicCount I L : ℝ)^2 ≤
      (Kl*D^(ε/2))/(Real.log 2)^3 :=
    (second_transfer_m_dyadic_sq_le_log_cube I L).trans
      (div_le_div_of_nonneg_right (hlog D L hD hL hLD) (by positivity))
  have hprod : D^(ε/2)*D^(ε/2) = D^ε := by
    rw [← Real.rpow_add hD0]
    congr 1
    ring
  change secondTransferPRMPRadius I L^δ *
    (secondTransferMDyadicCount I L : ℝ)^2 ≤ (A^δ*Kl/(Real.log 2)^3)*D^ε
  calc
    secondTransferPRMPRadius I L^δ * (secondTransferMDyadicCount I L : ℝ)^2 ≤
        (A^δ*D^(ε/2))*((Kl*D^(ε/2))/(Real.log 2)^3) :=
      mul_le_mul hpow hcount (sq_nonneg _) (by positivity)
    _ = (A^δ*Kl/(Real.log 2)^3)*(D^(ε/2)*D^(ε/2)) := by ring
    _ = (A^δ*Kl/(Real.log 2)^3)*D^ε := by rw [hprod]

end QRHShort



noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

/-- The original M interface, obtained by summing the complete arithmetic
blocks over all characters, excluded ideals and both dyadic indices. -/
theorem second_transfer_mean_square_proved (he : RemoveExclusionsStatement) :
    SecondTransferMeanSquareStatement := by
  intro C ε m hC hε c I Φ cI hc hcI
  have hcI0 : 0 ≤ cI := zero_le_one.trans ((le_max_left _ _).trans hcI)
  let δ : ℝ := ε/(2*C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨A,hA,hcount⟩ := exists_ideal_norm_count_constant
  obtain ⟨Kd,hKd,hdiv⟩ := second_transfer_m_squarefree_divisorCount_cube_soft_bound δ hδ
  obtain ⟨Ks,hKs,hscale⟩ := second_transfer_m_dyadic_scale_absorb C ε I hC hε
  refine ⟨4*cI*A*Kd*Ks, by positivity, ?_⟩
  intro D H L F Sigma coeffs hD hrange hcoeffs model V hV
  obtain ⟨hH,hHD,hL,hLD,hF,hFD,hSigma,hSigmaD,hmax⟩ := hrange
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hSigma0 : 0 < Sigma := zero_lt_one.trans_le hSigma
  have hHS : H ≤ Sigma := (le_max_left _ _).trans hmax
  let B := secondTransferPRMPRadius I L
  let N := secondTransferMDyadicCount I L
  have hB : 1 ≤ B := le_max_left _ _
  have hwindow (i : Fin model.R) :
      normIdeal (model.row i).excluded ≤ B ∧
      (model.row i).rBlock < N ∧ (model.row i).fBlock < N := by
    obtain ⟨hr,hf,_,_,_,_,_,_,_,hprod,hrlo,_,hflo,_⟩ := model.valid i
    have hnr := second_transfer_prmm_norm_one_le hr.1.1
    have hnf := second_transfer_prmm_norm_one_le hf.1.1
    have hrB : normIdeal (model.row i).excluded ≤ B :=
      ((le_mul_of_one_le_right (zero_le_one.trans hnr) hnf).trans hprod).trans
        (le_max_right _ _)
    have hfB : normIdeal (model.row i).twist ≤ B :=
      ((le_mul_of_one_le_left (zero_le_one.trans hnf) hnr).trans hprod).trans
        (le_max_right _ _)
    exact ⟨hrB, second_transfer_m_dyadic_lt I L _ (hrlo.trans hrB),
      second_transfer_m_dyadic_lt I L _ (hflo.trans hfB)⟩
  have hT : 0 ≤ Kd*B^δ := mul_nonneg hKd (Real.rpow_nonneg (by positivity) _)
  have hdivB (r : Ideal O) (hr : r ∈ boundedDivisibleIdeals 1 B) (hsf : Squarefree r) :
      (divisorCount r : ℝ)^3 ≤ Kd*B^δ :=
    (hdiv r hsf).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (mem_boundedDivisibleIdeals.mp hr).1 hδ.le) hKd)
  have hb := second_transfer_m_grouped_bound he c hc I m coeffs cI H L F Sigma B
    (Kd*B^δ) A N model V hV hcoeffs hcI0 hH0 hL0 hF hSigma0 hHS hT hA.le
    hcount hdivB (fun i => (hwindow i).1) (fun i => (hwindow i).2)
  apply hb.trans
  have hs := hscale D L hD hL hLD
  change B^δ*(N:ℝ)^2 ≤ Ks*D^ε at hs
  have hcoeff0 : 0 ≤ ∑' ξ, ‖coeffs ξ‖ := tsum_nonneg (fun _ => norm_nonneg _)
  have hsup0 := childSup_nonneg c I m H L F Sigma
  have hp : 0 ≤ (4*cI*A*Kd)*Sigma*(∑' ξ, ‖coeffs ξ‖)*
      childSup c I m H L F Sigma*weightNorm m V^2 := by positivity
  convert mul_le_mul_of_nonneg_left hs hp using 1 <;> ring

end QRHShort

