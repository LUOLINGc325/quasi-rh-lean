import Mathlib.Algebra.BigOperators.Field
import QRHShort.CloudThetaBoundsMellinShift
import QRHShort.CloudThetaBoundsMellinKernel
import QRHShort.SquarefreePreparedSymbols
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import QRHShort.SquarefreePreparedTruncation
import Mathlib.Data.Nat.Log
import QRHShort.SquarefreeDyadicDecay
import QRHShort.SquarefreePreparedLoss
import QRHShort.SquarefreePreparedSieve
import QRHShort.SquarefreePreparedCounting
import QRHShort.WeightNorm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Comp
import QRHShort.ThetaBoundsReduction
import Mathlib.Tactic
import QRHShort.SharedVsquarefreereflectionpackets

/-! Transparent integration of the proved prepared finite analysis and the
original six-premise squarefree assembly. Fragment bodies and frozen parent
definitions are unchanged. Only imports/axiom-print diagnostics are elided,
with anonymous file sections closed before the next fragment. -/

section
/- Source fragment: VPreparedPortableParents; SHA256 ad17bda8ef48f3be131c0bae7ec2689454eecbc4e1100ae5e794bea5d5fde0d0 -/

set_option maxHeartbeats 800000

/- Original module QRHShort.SquarefreePreparedBlocks; source SHA256 922e50c330b26cc1f7f25dc67f0539990281dd225a66226a74dfee9f40405510; declarations/proof bodies unchanged. -/
section






/-! Finite weighted recombination for arbitrary subsets of countable blocks.
The weights control the square root of each block's energy. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

theorem finite_block_energy_bound {ι ρ : Type*} (rows : Finset ρ)
    (blocks : Finset ι) (F : ι → ρ → ℂ) (w : ι → ℝ) (B : ℝ)
    (hw : ∀ p ∈ blocks, 0 < w p)
    (hF : ∀ p ∈ blocks, (∑ k ∈ rows, ‖F p k‖ ^ 2) ≤ B * w p ^ 2) :
    (∑ k ∈ rows, ‖∑ p ∈ blocks, F p k‖ ^ 2) ≤
      B * (∑ p ∈ blocks, w p) ^ 2 := by
  have hrow (k : ρ) : ‖∑ p ∈ blocks, F p k‖ ^ 2 ≤
      (∑ p ∈ blocks, w p) * ∑ p ∈ blocks, ‖F p k‖ ^ 2 / w p := by
    calc
      _ ≤ (∑ p ∈ blocks, ‖F p k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul blocks
        (fun p hp => (hw p hp).le)
        (fun p hp => div_nonneg (sq_nonneg _) (hw p hp).le)
        (fun p hp => le_of_eq (by field_simp [ne_of_gt (hw p hp)]))
  calc
    _ ≤ ∑ k ∈ rows, (∑ p ∈ blocks, w p) *
        ∑ p ∈ blocks, ‖F p k‖ ^ 2 / w p :=
      Finset.sum_le_sum (fun k _ => hrow k)
    _ = (∑ p ∈ blocks, w p) *
        ∑ p ∈ blocks, (∑ k ∈ rows, ‖F p k‖ ^ 2) / w p := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ (∑ p ∈ blocks, w p) * ∑ p ∈ blocks, B * w p := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun p hp => (hw p hp).le))
      apply Finset.sum_le_sum
      intro p hp
      calc
        _ ≤ (B * w p ^ 2) / w p := (div_le_div_iff_of_pos_right (hw p hp)).mpr (hF p hp)
        _ = B * w p := by field_simp [ne_of_gt (hw p hp)]
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The total weight, rather than the number of occupied blocks, controls
the recombination constant. -/
theorem summable_block_energy_bound {ι ρ : Type*} (rows : Finset ρ)
    (blocks : Finset ι) (F : ι → ρ → ℂ) (w : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ p, 0 < w p) (hsum : Summable w)
    (hF : ∀ p ∈ blocks, (∑ k ∈ rows, ‖F p k‖ ^ 2) ≤ B * w p ^ 2) :
    (∑ k ∈ rows, ‖∑ p ∈ blocks, F p k‖ ^ 2) ≤ B * (∑' p, w p) ^ 2 := by
  apply (finite_block_energy_bound rows blocks F w B (fun p _ => hw p) hF).trans
  apply mul_le_mul_of_nonneg_left _ hB
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => (hw p).le))
    (Summable.sum_le_tsum blocks (fun p _ => (hw p).le) hsum) 2

end QRHShort.SquarefreeAssembly

end
end
/- Original module QRHShort.SquarefreePreparedFinite; source SHA256 4fbf7f7d4b5e9815276314a045d8a99715ba50d2aa7ca8f694d4ceb6e4af2ae4; declarations/proof bodies unchanged. -/
section




/-! A dyadic decomposition of the frozen finite-truncation obligation.

The two remaining children have different mathematical content: a local
theta/Mellin/quadratic estimate, and a purely real scalar series bound.
The assembly below preserves arbitrary finite masks, and introduces neither
an axiom nor an asserted analytic estimate.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

abbrev PreparedBlockIndex := ℕ × ℕ × ℕ

/-- The first coordinate is `m + 4`; the other coordinates are the sharp
dyadic norm ranges of `n` and `b`. Bottom ideals have zero summand already. -/
def preparedBlockIndex (q : ℕ × Ideal O × Ideal O) : PreparedBlockIndex :=
  (q.1, Nat.log 2 q.2.1.absNorm, Nat.log 2 q.2.2.absNorm)

theorem normIdeal_dyadic_range (n : Ideal O) (hn : n ≠ ⊥) :
    (2 : ℝ) ^ (Nat.log 2 n.absNorm) ≤ normIdeal n ∧
      normIdeal n < 2 * (2 : ℝ) ^ (Nat.log 2 n.absNorm) := by
  have hn' : n.absNorm ≠ 0 := fun h => hn (Ideal.absNorm_eq_zero_iff.mp h)
  constructor
  · change (2 : ℝ) ^ (Nat.log 2 n.absNorm) ≤ (n.absNorm : ℝ)
    exact_mod_cast Nat.pow_log_le_self 2 hn'
  · have h : (n.absNorm : ℝ) < (2 : ℝ) ^ (Nat.log 2 n.absNorm + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) n.absNorm
    simpa only [normIdeal, pow_succ, mul_comm] using h

def preparedThetaBlock (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (k : Ideal O) : ℂ :=
  ∑ q ∈ t with preparedBlockIndex q = p, preparedThetaTerm W H Y A coeff k q

/-- The fixed factor `3^(4/3)` from `m = r - 4` is absorbed in the analytic
constant. The argument of the decay factor retains the exact factor `81`. -/
def preparedBlockWeight (H Y : ℝ) (p : PreparedBlockIndex) : ℝ :=
  (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
    (Real.sqrt H + Real.sqrt ((2 : ℝ) ^ p.2.1)) *
      (1 + (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 /
        (81 * Y)) ^ (-2 : ℝ)

theorem preparedBlockWeight_pos (H Y : ℝ) (hY : 0 < Y) (p : PreparedBlockIndex) :
    0 < preparedBlockWeight H Y p := by
  unfold preparedBlockWeight
  have hroot : 0 < Real.sqrt ((2 : ℝ) ^ p.2.1) := Real.sqrt_pos.2 (by positivity)
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hroot))
      (Real.rpow_pos_of_pos (by positivity) _)

theorem sum_preparedThetaBlock (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (k : Ideal O) :
    (∑ p ∈ t.image preparedBlockIndex, preparedThetaBlock W H Y A coeff t p k) =
      ∑ q ∈ t, preparedThetaTerm W H Y A coeff k q := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun q hq => Finset.mem_image_of_mem preparedBlockIndex hq) _

/-- Local dyadic analytic child, corresponding to (prepared-mean-square)
after absorbing `(H U)^σ` in a small power of `D` and one decay factor.
The finite mask is arbitrary within the block and is independent of `k`.
Its proof must supply the concrete Mellin separation and ideal counts. -/
def PreparedThetaDyadicEstimate : Prop :=
  ∀ ε C : ℝ, 0 < ε → 1 ≤ C → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (S : Finset (Ideal O)) (I : SupportInterval) (L : ℝ), 1 ≤ L →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (D H Y a : ℝ)
        (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ),
        SmoothSupported I W → 2 ≤ D → 1 ≤ H → H ≤ D ^ C →
        0 < Y → Y ≤ L * D ^ C → 0 ≤ a →
        (∀ r n b, ‖A r n b‖ ≤ a) →
        (∀ r k, k ∈ sieveRows S H → ‖coeff r k‖ ≤ 1) →
        ∀ (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex),
          (∑ k ∈ sieveRows S H, ‖preparedThetaBlock W H Y A coeff t p k‖ ^ 2) ≤
            (K * D ^ ε * weightNorm J W ^ 2 * a ^ 2) * preparedBlockWeight H Y p ^ 2

def PreparedThetaDyadicStep : Prop :=
  ThetaBoundsStatement → QuadraticEstimate → SmoothSeparationStatement →
    RecombinationStatement → PreparedThetaDyadicEstimate

/-- Scalar child: three geometric/dyadic sums and absorption of their small
power loss using `Y ≤ L D^C`. It has no arithmetic or analytic premises. -/
def PreparedThetaWeightBound : Prop :=
  ∀ ε C : ℝ, 0 < ε → 1 ≤ C → ∀ L : ℝ, 1 ≤ L →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ D H Y : ℝ,
      2 ≤ D → 1 ≤ H → 0 < Y → Y ≤ L * D ^ C →
        Summable (preparedBlockWeight H Y) ∧
        (∑' p, preparedBlockWeight H Y p) ^ 2 ≤ M * D ^ ε * (H + Y)

theorem prepared_theta_truncation_of_dyadic
    (hd : PreparedThetaDyadicEstimate) (hs : PreparedThetaWeightBound) :
    PreparedThetaTruncationEstimate := by
  intro ε C hε hC
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨J, hJ, hd⟩ := hd (ε / 2) C hhalf hC
  refine ⟨J, hJ, ?_⟩
  intro S I L hL
  obtain ⟨K, hK, hd⟩ := hd S I L hL
  obtain ⟨M, hM, hs⟩ := hs (ε / 2) C hhalf hC L hL
  refine ⟨K * M, mul_nonneg hK hM, ?_⟩
  intro W D H Y a A coeff hW hD hH hHC hY hYL ha hA hcoeff t
  obtain ⟨hsum, hweight⟩ := hs D H Y hD hH hY hYL
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hB : 0 ≤ K * D ^ (ε / 2) * weightNorm J W ^ 2 * a ^ 2 := by positivity
  have hblocks := summable_block_energy_bound (sieveRows S H)
    (t.image preparedBlockIndex) (preparedThetaBlock W H Y A coeff t)
    (preparedBlockWeight H Y) _ hB (preparedBlockWeight_pos H Y hY) hsum
    (fun p _ => hd W D H Y a A coeff hW hD hH hHC hY hYL ha hA hcoeff t p)
  simp_rw [sum_preparedThetaBlock] at hblocks
  calc
    _ ≤ (K * D ^ (ε / 2) * weightNorm J W ^ 2 * a ^ 2) *
        (∑' p, preparedBlockWeight H Y p) ^ 2 := hblocks
    _ ≤ (K * D ^ (ε / 2) * weightNorm J W ^ 2 * a ^ 2) *
        (M * D ^ (ε / 2) * (H + Y)) := mul_le_mul_of_nonneg_left hweight hB
    _ = (K * M) * D ^ ε * weightNorm J W ^ 2 * a ^ 2 * (H + Y) := by
      have hp : D ^ (ε / 2) * D ^ (ε / 2) = D ^ ε := by
        rw [← Real.rpow_add hDpos]
        congr 1
        ring
      calc
        _ = (K * M) * (D ^ (ε / 2) * D ^ (ε / 2)) *
            weightNorm J W ^ 2 * a ^ 2 * (H + Y) := by ring
        _ = _ := by rw [hp]

theorem prepared_theta_truncation_step_of_children
    (hd : PreparedThetaDyadicStep) (hs : PreparedThetaWeightBound) :
    PreparedThetaTruncationStep := by
  intro htheta hquadratic hseparation hrecombination
  exact prepared_theta_truncation_of_dyadic
    (hd htheta hquadratic hseparation hrecombination) hs

end QRHShort.SquarefreeAssembly

end
end
/- Original module QRHShort.SquarefreePreparedWeight; source SHA256 cc93c288bd5aa742313d0a26928a35bf2ddeb023c4ba5d782833ff9aa29a376a; declarations/proof bodies unchanged. -/
section



/-! The scalar child of the prepared finite-truncation decomposition. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

theorem prepared_weight_small_power {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ H Y : ℝ, 0 ≤ H → 0 < Y →
      Summable (preparedBlockWeight H Y) ∧
      (∑' p, preparedBlockWeight H Y p) ^ 2 ≤ B * Y ^ (2 * δ) * (H + Y) := by
  obtain ⟨K₀, hK₀, h₀⟩ := dyadicDecay_sum_bound (s := 0) (by norm_num) hδ (by linarith)
  obtain ⟨K₁, hK₁, h₁⟩ :=
    dyadicDecay_sum_bound (s := 1 / 2) (by norm_num) hδ (by linarith)
  let q : ℝ := (3 : ℝ) ^ (-1 / 3 : ℝ)
  let R : ℝ := (1 - q)⁻¹
  let K : ℝ := K₀ + K₁
  have hq₀ : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hR : 0 < R := inv_pos.mpr (sub_pos.mpr hq₁)
  have hK : 0 < K := add_pos hK₀ hK₁
  have hq := summable_geometric_of_lt_one hq₀ hq₁
  refine ⟨162 * R ^ 2 * K ^ 2 * (81 : ℝ) ^ (2 * δ), by positivity, ?_⟩
  intro H Y hH hY
  let Z : ℝ := 81 * Y
  have hZ : 0 < Z := mul_pos (by norm_num) hY
  obtain ⟨hs₀, hb₀⟩ := h₀ Z hZ
  obtain ⟨hs₁, hb₁⟩ := h₁ Z hZ
  let G : ℕ × ℕ → ℝ := fun p =>
    Real.sqrt H * dyadicDecay 0 Z p + dyadicDecay (1 / 2) Z p
  have hG : Summable G := (hs₀.mul_left (Real.sqrt H)).add hs₁
  have hG₀ (p : ℕ × ℕ) : 0 ≤ G p :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (dyadicDecay_nonneg 0 Z hZ p))
      (dyadicDecay_nonneg (1 / 2) Z hZ p)
  have hprod : Summable (fun p : PreparedBlockIndex => q ^ p.1 * G p.2) :=
    hq.mul_of_nonneg hG (fun r => pow_nonneg hq₀ r) hG₀
  have hle (p : PreparedBlockIndex) : preparedBlockWeight H Y p ≤ q ^ p.1 * G p.2 := by
    have hr : (1 : ℝ) ≤ 3 ^ p.1 := one_le_pow₀ (by norm_num)
    have hu : 0 ≤ (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 := by positivity
    have harg :
        1 + (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 / Z ≤
          1 + (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 / Z := by
      have hmul : (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 ≤
          (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hr) hu]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right hmul hZ.le)
    have hdec := Real.rpow_le_rpow_of_nonpos
      (show 0 < 1 + (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 / Z by positivity)
      harg (by norm_num : (-2 : ℝ) ≤ 0)
    have heq : (3 : ℝ) ^ (-(p.1 : ℝ) / 3) = q ^ p.1 := by
      dsimp [q]
      rw [← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      ring
    unfold preparedBlockWeight
    change _ ≤ q ^ p.1 * G p.2
    calc
      _ ≤ (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
          (Real.sqrt H + Real.sqrt ((2 : ℝ) ^ p.2.1)) *
          (1 + (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 / Z) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left hdec (by positivity)
      _ = _ := by
        rw [heq]
        dsimp [G, dyadicDecay]
        simp only [Real.rpow_zero, one_mul, Real.sqrt_eq_rpow]
        ring
  have hsum : Summable (preparedBlockWeight H Y) :=
    hprod.of_nonneg_of_le (fun p => (preparedBlockWeight_pos H Y hY p).le) hle
  have htotal : (∑' p, preparedBlockWeight H Y p) ≤
      R * (Real.sqrt H * (K₀ * Z ^ δ) + K₁ * Z ^ (1 / 2 + δ)) := by
    calc
      _ ≤ ∑' p : PreparedBlockIndex, q ^ p.1 * G p.2 :=
        Summable.tsum_le_tsum hle hsum hprod
      _ = R * (Real.sqrt H * ∑' p, dyadicDecay 0 Z p +
          ∑' p, dyadicDecay (1 / 2) Z p) := by
        rw [← hq.tsum_mul_tsum hG hprod, tsum_geometric_of_lt_one hq₀ hq₁]
        dsimp [G]
        rw [Summable.tsum_add (hs₀.mul_left _) hs₁, hs₀.tsum_mul_left]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hR.le
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by simpa using hb₀) (Real.sqrt_nonneg _)
        · exact hb₁
  have htotal' : (∑' p, preparedBlockWeight H Y p) ≤
      R * K * Z ^ δ * (Real.sqrt H + Real.sqrt Z) := by
    apply htotal.trans
    have hp : Z ^ (1 / 2 + δ) = Real.sqrt Z * Z ^ δ := by
      rw [Real.rpow_add hZ, Real.sqrt_eq_rpow]
    rw [hp]
    have h₀ : K₀ ≤ K := le_add_of_nonneg_right hK₁.le
    have h₁ : K₁ ≤ K := le_add_of_nonneg_left hK₀.le
    have hm₀ := mul_le_mul_of_nonneg_left h₀ (mul_nonneg (Real.sqrt_nonneg H)
      (Real.rpow_nonneg hZ.le δ))
    have hm₁ := mul_le_mul_of_nonneg_left h₁ (mul_nonneg (Real.sqrt_nonneg Z)
      (Real.rpow_nonneg hZ.le δ))
    calc
      _ = R * ((Real.sqrt H * Z ^ δ) * K₀ + (Real.sqrt Z * Z ^ δ) * K₁) := by ring
      _ ≤ R * ((Real.sqrt H * Z ^ δ) * K + (Real.sqrt Z * Z ^ δ) * K) :=
        mul_le_mul_of_nonneg_left (add_le_add hm₀ hm₁) hR.le
      _ = _ := by ring
  have hroot : (Real.sqrt H + Real.sqrt Z) ^ 2 ≤ 162 * (H + Y) := by
    have hsH := Real.sq_sqrt hH
    have hsZ := Real.sq_sqrt hZ.le
    dsimp [Z] at hsZ
    nlinarith only [hsH, hsZ, sq_nonneg (Real.sqrt H - Real.sqrt Z), hH, hY.le]
  have hp : (Z ^ δ) ^ 2 = (81 : ℝ) ^ (2 * δ) * Y ^ (2 * δ) := by
    rw [pow_two, ← Real.rpow_add hZ, show δ + δ = 2 * δ by ring]
    exact Real.mul_rpow (by norm_num) hY.le
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ (R * K * Z ^ δ * (Real.sqrt H + Real.sqrt Z)) ^ 2 :=
      pow_le_pow_left₀ (tsum_nonneg (fun p => (preparedBlockWeight_pos H Y hY p).le)) htotal' 2
    _ = (R * K * Z ^ δ) ^ 2 * (Real.sqrt H + Real.sqrt Z) ^ 2 := mul_pow _ _ _
    _ ≤ (R * K * Z ^ δ) ^ 2 * (162 * (H + Y)) :=
      mul_le_mul_of_nonneg_left hroot (sq_nonneg _)
    _ = (162 * R ^ 2 * K ^ 2 * (81 : ℝ) ^ (2 * δ)) * Y ^ (2 * δ) * (H + Y) := by
      simp only [mul_pow]
      rw [hp]
      ring

theorem prepared_theta_weight_bound : PreparedThetaWeightBound := by
  intro ε C hε hC L hL
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let δ : ℝ := min (ε / (2 * C)) (1 / 4)
  have hδ : 0 < δ := lt_min (div_pos hε (mul_pos (by norm_num) hCpos)) (by norm_num)
  have hcap : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hexp : C * (2 * δ) ≤ ε := by
    have h := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp (min_le_left (ε / (2 * C)) (1 / 4))
    dsimp [δ]
    nlinarith
  obtain ⟨B, hB, hbound⟩ := prepared_weight_small_power hδ hcap
  refine ⟨B * L ^ (2 * δ), by positivity, ?_⟩
  intro D H Y hD hH hY hYL
  obtain ⟨hsum, hb⟩ := hbound H Y (le_trans zero_le_one hH) hY
  have hD₀ : 0 ≤ D := le_trans (by norm_num) hD
  have hL₀ : 0 ≤ L := le_trans zero_le_one hL
  have hYpow : Y ^ (2 * δ) ≤ L ^ (2 * δ) * D ^ ε := by
    calc
      _ ≤ (L * D ^ C) ^ (2 * δ) := Real.rpow_le_rpow hY.le hYL (by positivity)
      _ = L ^ (2 * δ) * D ^ (C * (2 * δ)) := by
        rw [Real.mul_rpow hL₀ (Real.rpow_nonneg hD₀ _), ← Real.rpow_mul hD₀]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) hD) hexp)
        (Real.rpow_nonneg hL₀ _)
  refine ⟨hsum, hb.trans ?_⟩
  calc
    _ ≤ B * (L ^ (2 * δ) * D ^ ε) * (H + Y) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYpow hB.le) (by positivity)
    _ = _ := by ring

theorem prepared_theta_truncation_step_of_dyadic (hd : PreparedThetaDyadicStep) :
    PreparedThetaTruncationStep :=
  prepared_theta_truncation_step_of_children hd prepared_theta_weight_bound

end QRHShort.SquarefreeAssembly

end
end
/- Original module QRHShort.SquarefreePreparedDyadic; source SHA256 9a137128f30d67ef171313f80f2d50e5c742da0002de4512712b6e735ad4c6dc; declarations/proof bodies unchanged. -/
section





/-! The remaining analytic obligation before small-power absorption.

The extra factor `(1 + z)^(-2)` is the spare square of decay obtained by
using `A = 3` in the theta/Mellin estimate. All masks and coefficients remain
those of the frozen finite-truncation problem. No analytic input is asserted.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

def preparedBlockScale (Y : ℝ) (p : PreparedBlockIndex) : ℝ :=
  (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 / (81 * Y)

theorem preparedBlockScale_pos {Y : ℝ} (hY : 0 < Y) (p : PreparedBlockIndex) :
    0 < preparedBlockScale Y p := by
  unfold preparedBlockScale
  positivity

theorem preparedBlockScale_norm_bound {Y : ℝ} (hY : 0 < Y)
    (p : PreparedBlockIndex) :
    (2 : ℝ) ^ p.2.1 ≤ 81 * Y * preparedBlockScale Y p := by
  have hr : (1 : ℝ) ≤ 3 ^ p.1 := one_le_pow₀ (by norm_num)
  have hb : (1 : ℝ) ≤ 8 ^ p.2.2 := one_le_pow₀ (by norm_num)
  have hu : 0 ≤ (2 : ℝ) ^ p.2.1 := by positivity
  have hmul : (2 : ℝ) ^ p.2.1 ≤
      (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 := by
    calc
      _ ≤ (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 := le_mul_of_one_le_left hu hr
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hb
  calc
    _ ≤ (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 * (8 : ℝ) ^ p.2.2 := hmul
    _ = _ := by
      unfold preparedBlockScale
      field_simp [ne_of_gt hY] <;> ring

/-- The local Mellin/quadratic-sieve estimate with its original `(HU)^σ`
loss. The derivative order is uniform in every scale and finite mask. -/
def PreparedThetaDyadicRawEstimate : Prop :=
  ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (S : Finset (Ideal O)) (I : SupportInterval),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (H Y a : ℝ)
        (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ),
        SmoothSupported I W → 1 ≤ H → 0 < Y → 0 ≤ a →
        (∀ r n b, ‖A r n b‖ ≤ a) →
        (∀ r k, k ∈ sieveRows S H → ‖coeff r k‖ ≤ 1) →
        ∀ (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex),
          (∑ k ∈ sieveRows S H, ‖preparedThetaBlock W H Y A coeff t p k‖ ^ 2) ≤
            (K * weightNorm J W ^ 2 * a ^ 2) *
              ((H * (2 : ℝ) ^ p.2.1) ^ σ *
                (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
              preparedBlockWeight H Y p ^ 2

def PreparedThetaDyadicRawStep : Prop :=
  ThetaBoundsStatement → QuadraticEstimate → SmoothSeparationStatement →
    RecombinationStatement → PreparedThetaDyadicRawEstimate

theorem prepared_theta_dyadic_of_raw (hraw : PreparedThetaDyadicRawEstimate) :
    PreparedThetaDyadicEstimate := by
  intro ε C hε hC
  obtain ⟨σ, hσ, hσcap, habsorb⟩ := prepared_small_power_absorb hε hC
  obtain ⟨J, hJ, hraw⟩ := hraw σ hσ hσcap
  refine ⟨J, hJ, ?_⟩
  intro S I L hL
  obtain ⟨K, hK, hraw⟩ := hraw S I
  obtain ⟨M, hM, habsorb⟩ := habsorb L hL
  refine ⟨K * M, mul_nonneg hK hM, ?_⟩
  intro W D H Y a A coeff hW hD hH hHC hY hYL ha hA hcoeff t p
  have hloss := habsorb D H ((2 : ℝ) ^ p.2.1) Y (preparedBlockScale Y p)
    hD hH hHC (by positivity) hY hYL (preparedBlockScale_pos hY p).le
    (preparedBlockScale_norm_bound hY p)
  calc
    _ ≤ (K * weightNorm J W ^ 2 * a ^ 2) *
          ((H * (2 : ℝ) ^ p.2.1) ^ σ *
            (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
          preparedBlockWeight H Y p ^ 2 := hraw W H Y a A coeff hW hH hY ha hA hcoeff t p
    _ ≤ (K * weightNorm J W ^ 2 * a ^ 2) * (M * D ^ ε) *
          preparedBlockWeight H Y p ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hloss (by positivity)) (sq_nonneg _)
    _ = _ := by ring

theorem prepared_theta_dyadic_step_of_raw (h : PreparedThetaDyadicRawStep) :
    PreparedThetaDyadicStep := by
  intro htheta hquadratic hseparation hrecombination
  exact prepared_theta_dyadic_of_raw (h htheta hquadratic hseparation hrecombination)

theorem prepared_theta_truncation_step_of_raw (h : PreparedThetaDyadicRawStep) :
    PreparedThetaTruncationStep :=
  prepared_theta_truncation_step_of_dyadic (prepared_theta_dyadic_step_of_raw h)

theorem prepared_theta_step_of_raw (h : PreparedThetaDyadicRawStep) :
    PreparedThetaEstimateStep :=
  prepared_theta_step_of_truncation (prepared_theta_truncation_step_of_raw h)

end QRHShort.SquarefreeAssembly

end
end
/- Original module QRHShort.SquarefreePreparedColumns; source SHA256 2091ffb0fe95caa27f9da37a6ccbf2596723d8ac5660e4f5d555d07f72d3da55; declarations/proof bodies unchanged. -/
section


/-! Exact finite fibres in the auxiliary ideal `b`.  Removing a bottom
ideal loses no summand: the frozen prepared term is zero there. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

def preparedColumnTuples (t : Finset (ℕ × Ideal O × Ideal O))
    (p : PreparedBlockIndex) : Finset (ℕ × Ideal O × Ideal O) :=
  t.filter (fun q => preparedBlockIndex q = p ∧ q.2.2 ≠ ⊥)

def preparedColumnIdeals (t : Finset (ℕ × Ideal O × Ideal O))
    (p : PreparedBlockIndex) : Finset (Ideal O) :=
  (preparedColumnTuples t p).image (fun q => q.2.2)

def preparedThetaColumn (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex)
    (b k : Ideal O) : ℂ :=
  ∑ q ∈ preparedColumnTuples t p with q.2.2 = b,
    preparedThetaTerm W H Y A coeff k q

theorem preparedThetaTerm_bottom_column (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (k n : Ideal O) (r : ℕ) :
    preparedThetaTerm W H Y A coeff k (r, n, ⊥) = 0 := by
  simp [preparedThetaTerm]

theorem sum_preparedThetaColumn (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (k : Ideal O) :
    (∑ b ∈ preparedColumnIdeals t p, preparedThetaColumn W H Y A coeff t p b k) =
      preparedThetaBlock W H Y A coeff t p k := by
  have hfiber :
      (∑ b ∈ preparedColumnIdeals t p, preparedThetaColumn W H Y A coeff t p b k) =
        ∑ q ∈ preparedColumnTuples t p, preparedThetaTerm W H Y A coeff k q := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun q hq => Finset.mem_image_of_mem (fun q => q.2.2) hq) _
  rw [hfiber]
  unfold preparedColumnTuples preparedThetaBlock
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : preparedBlockIndex q = p
  · by_cases hb : q.2.2 = ⊥
    · simp [hp, hb, preparedThetaTerm]
    · simp [hp, hb]
  · simp [hp]

theorem preparedColumnIdeals_norm_range
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex}
    {b : Ideal O} (hb : b ∈ preparedColumnIdeals t p) :
    b ≠ ⊥ ∧ (2 : ℝ) ^ p.2.2 ≤ normIdeal b ∧
      normIdeal b ≤ 2 * (2 : ℝ) ^ p.2.2 := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, hp, hb⟩ := Finset.mem_filter.mp hq
  have he : Nat.log 2 q.2.2.absNorm = p.2.2 :=
    congrArg (fun p : PreparedBlockIndex => p.2.2) hp
  obtain ⟨hlo, hhi⟩ := normIdeal_dyadic_range q.2.2 hb
  rw [he] at hlo hhi
  exact ⟨hb, hlo, hhi.le⟩

end QRHShort.SquarefreeAssembly

end
end
/- Original module QRHShort.SquarefreePreparedColumnAssembly; source SHA256 de39175105b251e94187e6e4e3d1e3a3d67e25fd6e92aca37d3708fa7190b069; declarations/proof bodies unchanged. -/
section





/-! Finite recombination of prepared columns with a uniform inverse-norm bound. -/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

theorem prepared_column_energy_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (M V : ℝ) (rows : Finset (Ideal O))
      (bs : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ),
      0 ≤ M → 0 < V →
      (∀ b ∈ bs, b ≠ ⊥ ∧ V ≤ normIdeal b ∧ normIdeal b ≤ 2 * V) →
      (∀ b ∈ bs, (∑ k ∈ rows, ‖F b k‖ ^ 2) ≤
        M * (normIdeal b)⁻¹ ^ 2) →
      (∑ k ∈ rows, ‖∑ b ∈ bs, F b k‖ ^ 2) ≤ B * M := by
  obtain ⟨C, hC, hinv⟩ := prepared_inverse_norm_bound
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro M V rows bs F hM hV hbs hF
  have hsum := hinv V bs hV hbs
  have hw (b : Ideal O) (hb : b ∈ bs) : 0 < (normIdeal b)⁻¹ :=
    inv_pos.mpr ((hV.trans_le (hbs b hb).2.1))
  have hbase := finite_block_energy_bound rows bs F (fun b => (normIdeal b)⁻¹)
    M (fun b hb => hw b hb) hF
  have hsum_nonneg : 0 ≤ ∑ b ∈ bs, (normIdeal b)⁻¹ :=
    Finset.sum_nonneg (fun b hb => (hw b hb).le)
  calc
    (∑ k ∈ rows, ‖∑ b ∈ bs, F b k‖ ^ 2) ≤
        M * (∑ b ∈ bs, (normIdeal b)⁻¹) ^ 2 := hbase
    _ ≤ M * C ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact pow_le_pow_left₀ hsum_nonneg hsum 2
    _ = C ^ 2 * M := by ring

end QRHShort.SquarefreeAssembly
end
end
/- Original module QRHShort.SquarefreePreparedMellin; source SHA256 9e487a0a68821191bfb69c5f85329777230011a872797336b145eb1a899740ed; declarations/proof bodies unchanged. -/
section



/-! The sole remaining analytic input is a common, integrable two-variable
Mellin envelope for a fixed `b` fibre. Its mass retains the third power of decay.
The finite masks, concrete theta transform, and quadratic symbols are unchanged.
This file declares that input as a Prop, and proves only its implications. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace QRHShort.SquarefreeAssembly

/-- A common coefficient envelope, rather than separate bounds for each
row. The finite quadratic coefficients may depend on the Mellin variable,
but are independent of the row ideal `k`. -/
structure PreparedColumnMellinData (J : ℕ) (C : ℝ) (S : Finset (Ideal O))
    (W : ℝ → ℂ) (H Y a : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (b : Ideal O) where
  columns : Finset (Ideal O)
  envelope : BoxSpace 2 → ℝ
  coefficient : Ideal O → BoxSpace 2 → ℂ
  beta : BoxSpace 2 → Ideal O → ℂ
  admissible : ∀ n ∈ columns, n ≠ ⊥ ∧ Squarefree n ∧
    IsRelPrime n (principal 3) ∧ (2 : ℝ) ^ p.2.1 ≤ normIdeal n ∧
      normIdeal n ≤ 2 * (2 : ℝ) ^ p.2.1
  envelope_nonneg : ∀ s, 0 ≤ envelope s
  envelope_integrable : Integrable envelope
  coefficient_measurable : ∀ k ∈ sieveRows S H, Measurable (coefficient k)
  beta_measurable : ∀ n ∈ columns, Measurable (fun s => beta s n)
  coefficient_bound : ∀ k ∈ sieveRows S H, ∀ s, ‖coefficient k s‖ ≤ envelope s
  beta_bound : ∀ s n, n ∈ columns → ‖beta s n‖ ≤ 1 / Real.sqrt (normIdeal n)
  mass_bound : (∫ s, envelope s) ≤
    C * |weightNorm J W| * a * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
      (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹
  column_eq : ∀ k ∈ sieveRows S H,
    preparedThetaColumn W H Y A coeff t p b k =
      ∫ s, coefficient k s *
        ∑ n ∈ columns, beta s n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)

def PreparedThetaColumnMellinEstimate : Prop :=
  ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (S : Finset (Ideal O)) (I : SupportInterval),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℝ → ℂ) (H Y a : ℝ)
        (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ),
        SmoothSupported I W → 1 ≤ H → 0 < Y → 0 ≤ a →
        (∀ r n b, ‖A r n b‖ ≤ a) →
        (∀ r k, k ∈ sieveRows S H → ‖coeff r k‖ ≤ 1) →
        ∀ (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex)
          (b : Ideal O), b ∈ preparedColumnIdeals t p →
            Nonempty (PreparedColumnMellinData J C S W H Y a A coeff t p b)

/-- No sieve or recombination estimate is hidden in this analytic child. -/
def PreparedThetaColumnMellinStep : Prop :=
  ThetaBoundsStatement → SmoothSeparationStatement → PreparedThetaColumnMellinEstimate

/-- Recombination with a common envelope needs only a pointwise energy
bound. The weighted energy is integrable by domination, not by a default
value of the integral. -/
theorem prepared_integral_energy_bound (hr : RecombinationStatement)
    {α : Type} [MeasurableSpace α] (μ : Measure α)
    {ρ : Type} (rows : Finset ρ) (e : α → ℝ) (c F : ρ → α → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ x, 0 ≤ e x) (hei : Integrable e μ)
    (hc : ∀ k ∈ rows, Measurable (c k))
    (hF : ∀ k ∈ rows, Measurable (F k))
    (hce : ∀ k ∈ rows, ∀ x, ‖c k x‖ ≤ e x)
    (henergy : ∀ x, (∑ k ∈ rows, ‖F k x‖ ^ 2) ≤ M) :
    (∀ k ∈ rows, Integrable (fun x => c k x * F k x) μ) ∧
      (∑ k ∈ rows, ‖∫ x, c k x * F k x ∂μ‖ ^ 2) ≤ M * (∫ x, e x ∂μ) ^ 2 := by
  let E : α → ℝ := fun x => ∑ k ∈ rows, ‖F k x‖ ^ 2
  have hEm : Measurable E := by
    exact Finset.measurable_sum rows (fun k hk => (hF k hk).norm.pow_const 2)
  have hEi : Integrable (fun x => e x * E x) μ := by
    apply (hei.mul_const M).mono' (hei.aestronglyMeasurable.mul hEm.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖e x * E x‖ ≤ e x * M
    have hEx : 0 ≤ E x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.norm_of_nonneg (mul_nonneg (he x) hEx)]
    exact mul_le_mul_of_nonneg_left (henergy x) (he x)
  have hEsub (x : α) : (∑ k : {k // k ∈ rows}, ‖F k x‖ ^ 2) = E x :=
    Finset.sum_coe_sort rows (fun k => ‖F k x‖ ^ 2)
  have hIsub : (∑ k : {k // k ∈ rows}, ‖∫ x, c k x * F k x ∂μ‖ ^ 2) =
      ∑ k ∈ rows, ‖∫ x, c k x * F k x ∂μ‖ ^ 2 :=
    Finset.sum_coe_sort rows (fun k => ‖∫ x, c k x * F k x ∂μ‖ ^ 2)
  have hri := hr.2 Unit {k // k ∈ rows} α μ
    (fun _ => (1 : ℝ)) (fun _ => e)
    (fun _ k => c k) (fun _ k => F k)
    (fun _ => zero_le_one) (fun _ => he)
    (fun _ k => hc k k.property) (fun _ k => hF k k.property)
    (fun _ k => hce k k.property) (fun _ => hei)
    (fun _ => by simpa only [one_mul, hEsub] using hEi)
  have hibound : (∫ x, e x * E x ∂μ) ≤ M * (∫ x, e x ∂μ) := by
    calc
      _ ≤ ∫ x, e x * M ∂μ := integral_mono hEi (hei.mul_const M)
        (fun x => mul_le_mul_of_nonneg_left (henergy x) (he x))
      _ = _ := by rw [integral_mul_const, mul_comm]
  refine ⟨?_, ?_⟩
  · intro k hk
    exact hri.1 () ⟨k, hk⟩ zero_lt_one
  · have hh := hri.2
    simp only [one_mul, Fintype.sum_unique, hEsub, hIsub] at hh
    calc
      _ ≤ (∫ x, e x ∂μ) * (∫ x, e x * E x ∂μ) := hh
      _ ≤ (∫ x, e x ∂μ) * (M * (∫ x, e x ∂μ)) :=
        mul_le_mul_of_nonneg_left hibound (integral_nonneg he)
      _ = _ := by ring

theorem prepared_column_mass_square_bound {Q C H Y a σ w : ℝ}
    (hQ : 0 ≤ Q) (hH : 0 ≤ H) (hY : 0 < Y)
    (p : PreparedBlockIndex) (b : Ideal O) :
    (Q * (H * (2 : ℝ) ^ p.2.1) ^ σ * (H + (2 : ℝ) ^ p.2.1)) *
        (C * |w| * a * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
          (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹) ^ 2 ≤
      ((Q * C ^ 2 * w ^ 2 * a ^ 2) *
        ((H * (2 : ℝ) ^ p.2.1) ^ σ *
          (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
        preparedBlockWeight H Y p ^ 2) * (normIdeal b)⁻¹ ^ 2 := by
  have hU : 0 ≤ (2 : ℝ) ^ p.2.1 := by positivity
  have hroot : H + (2 : ℝ) ^ p.2.1 ≤
      (Real.sqrt H + Real.sqrt ((2 : ℝ) ^ p.2.1)) ^ 2 := by
    nlinarith [Real.sq_sqrt hH, Real.sq_sqrt hU,
      mul_nonneg (Real.sqrt_nonneg H) (Real.sqrt_nonneg ((2 : ℝ) ^ p.2.1))]
  have hz : 0 < 1 + preparedBlockScale Y p := by
    have := preparedBlockScale_pos hY p
    linarith
  have hdecay : ((1 + preparedBlockScale Y p) ^ (-3 : ℝ)) ^ 2 =
      (1 + preparedBlockScale Y p) ^ (-2 : ℝ) *
        ((1 + preparedBlockScale Y p) ^ (-2 : ℝ)) ^ 2 := by
    simp only [pow_two]
    rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz]
    norm_num
  have hw : preparedBlockWeight H Y p =
      (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
        (Real.sqrt H + Real.sqrt ((2 : ℝ) ^ p.2.1)) *
        (1 + preparedBlockScale Y p) ^ (-2 : ℝ) := rfl
  calc
    _ = (Q * (H * (2 : ℝ) ^ p.2.1) ^ σ *
        (C * |w| * a * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
          (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹) ^ 2) *
        (H + (2 : ℝ) ^ p.2.1) := by ring
    _ ≤ (Q * (H * (2 : ℝ) ^ p.2.1) ^ σ *
        (C * |w| * a * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
          (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹) ^ 2) *
        (Real.sqrt H + Real.sqrt ((2 : ℝ) ^ p.2.1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hroot
        (mul_nonneg (mul_nonneg hQ (Real.rpow_nonneg (mul_nonneg hH hU) _))
          (sq_nonneg _))
    _ = _ := by
      rw [hw]
      simp only [mul_pow, sq_abs]
      rw [hdecay]
      ring

/-- Pointwise quadratic large sieve plus a common Mellin envelope proves
the fixed-`b` energy bound, including its exact inverse-norm factor. -/
theorem prepared_column_bound_of_mellin_data
    (hr : RecombinationStatement) {S : Finset (Ideal O)} {σ Q : ℝ}
    (hQ : 0 ≤ Q)
    (hq : ∀ (H U a : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ),
      1 ≤ H → 1 ≤ U → 0 ≤ a →
      (∀ n ∈ columns, n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3) ∧
        U ≤ normIdeal n ∧ normIdeal n ≤ 2 * U) →
      (∀ n ∈ columns, ‖β n‖ ≤ a / Real.sqrt (normIdeal n)) →
      (∑ k ∈ sieveRows S H,
        ‖∑ n ∈ columns, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2) ≤
          Q * a ^ 2 * (H * U) ^ σ * (H + U))
    {J : ℕ} {C H Y a : ℝ} {W : ℝ → ℂ}
    {A : ℕ → Ideal O → Ideal O → ℂ} {coeff : ℕ → Ideal O → ℂ}
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex} {b : Ideal O}
    (hH : 1 ≤ H) (hY : 0 < Y)
    (data : PreparedColumnMellinData J C S W H Y a A coeff t p b) :
    (∑ k ∈ sieveRows S H, ‖preparedThetaColumn W H Y A coeff t p b k‖ ^ 2) ≤
      ((Q * C ^ 2 * weightNorm J W ^ 2 * a ^ 2) *
        ((H * (2 : ℝ) ^ p.2.1) ^ σ *
          (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
        preparedBlockWeight H Y p ^ 2) * (normIdeal b)⁻¹ ^ 2 := by
  let F : Ideal O → BoxSpace 2 → ℂ := fun k s =>
    ∑ n ∈ data.columns, data.beta s n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)
  let M : ℝ := Q * (H * (2 : ℝ) ^ p.2.1) ^ σ * (H + (2 : ℝ) ^ p.2.1)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hFi (k : Ideal O) (_ : k ∈ sieveRows S H) : Measurable (F k) := by
    exact Finset.measurable_sum data.columns (fun n hn =>
      (data.beta_measurable n hn).mul_const _)
  have hFE (s : BoxSpace 2) : (∑ k ∈ sieveRows S H, ‖F k s‖ ^ 2) ≤ M := by
    simpa only [one_pow, mul_one] using
      hq H ((2 : ℝ) ^ p.2.1) 1 data.columns (data.beta s) hH
        (one_le_pow₀ (by norm_num)) zero_le_one data.admissible (data.beta_bound s)
  obtain ⟨_, hbound⟩ := prepared_integral_energy_bound hr volume (sieveRows S H)
    data.envelope data.coefficient F hM data.envelope_nonneg data.envelope_integrable
    data.coefficient_measurable hFi data.coefficient_bound hFE
  have hmass : 0 ≤ ∫ s, data.envelope s := integral_nonneg data.envelope_nonneg
  calc
    _ = ∑ k ∈ sieveRows S H, ‖∫ s, data.coefficient k s * F k s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [data.column_eq k hk]
    _ ≤ M * (∫ s, data.envelope s) ^ 2 := hbound
    _ ≤ M * (C * |weightNorm J W| * a * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
        (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmass data.mass_bound 2) hM
    _ ≤ _ := prepared_column_mass_square_bound hQ (zero_le_one.trans hH) hY p b

theorem prepared_theta_raw_of_column_mellin
    (hm : PreparedThetaColumnMellinEstimate) (hq : QuadraticEstimate)
    (hr : RecombinationStatement) : PreparedThetaDyadicRawEstimate := by
  intro σ hσ hσcap
  obtain ⟨J, hJ, hm⟩ := hm σ hσ hσcap
  refine ⟨J, hJ, ?_⟩
  intro S I
  obtain ⟨C, hC, hm⟩ := hm S I
  obtain ⟨Q, hQ, hq⟩ := prepared_quadratic_column_bound hq S hσ
  obtain ⟨B, hB, hBbound⟩ := prepared_column_energy_bound
  refine ⟨B * (Q * C ^ 2), by positivity, ?_⟩
  intro W H Y a A coeff hW hH hY ha hA hcoeff t p
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hz : 0 < 1 + preparedBlockScale Y p := by
    have := preparedBlockScale_pos hY p
    linarith
  let M : ℝ := (Q * C ^ 2 * weightNorm J W ^ 2 * a ^ 2) *
    ((H * (2 : ℝ) ^ p.2.1) ^ σ * (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
      preparedBlockWeight H Y p ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcol (b : Ideal O) (hb : b ∈ preparedColumnIdeals t p) :
      (∑ k ∈ sieveRows S H, ‖preparedThetaColumn W H Y A coeff t p b k‖ ^ 2) ≤
        M * (normIdeal b)⁻¹ ^ 2 := by
    obtain ⟨data⟩ := hm W H Y a A coeff hW hH hY ha hA hcoeff t p b hb
    exact prepared_column_bound_of_mellin_data hr hQ hq hH hY data
  have hbound := hBbound M ((2 : ℝ) ^ p.2.2) (sieveRows S H)
    (preparedColumnIdeals t p) (preparedThetaColumn W H Y A coeff t p)
    hM (by positivity) (fun _ hb => preparedColumnIdeals_norm_range hb) hcol
  simp_rw [sum_preparedThetaColumn] at hbound
  exact hbound.trans_eq (by dsimp [M]; ring)

/-- The original frozen RawStep follows from the one remaining analytic
child, without adding or changing any premise of that frozen statement. -/
theorem prepared_theta_raw_step_of_column_mellin
    (hm : PreparedThetaColumnMellinStep) : PreparedThetaDyadicRawStep := by
  intro htheta hquadratic hseparation hrecombination
  exact prepared_theta_raw_of_column_mellin (hm htheta hseparation)
    hquadratic hrecombination

theorem prepared_theta_dyadic_step_of_column_mellin
    (hm : PreparedThetaColumnMellinStep) : PreparedThetaDyadicStep :=
  prepared_theta_dyadic_step_of_raw (prepared_theta_raw_step_of_column_mellin hm)

theorem prepared_theta_truncation_step_of_column_mellin
    (hm : PreparedThetaColumnMellinStep) : PreparedThetaTruncationStep :=
  prepared_theta_truncation_step_of_raw (prepared_theta_raw_step_of_column_mellin hm)

theorem prepared_theta_step_of_column_mellin
    (hm : PreparedThetaColumnMellinStep) : PreparedThetaEstimateStep :=
  prepared_theta_step_of_raw (prepared_theta_raw_step_of_column_mellin hm)

end QRHShort.SquarefreeAssembly

end
end
/- Original module QRHShort.SquarefreePreparedWeightTransfer; source SHA256 c167fb61628d8626d751a494a6206c7a24b32773becd8454631659682acef57a; declarations/proof bodies unchanged. -/
section





/-! Multiplication by a fixed smooth function on the positive axis preserves
the original support and costs no extra derivatives of the varying weight.
In particular this applies to the literal `sqrt(x) W(x)` in the prepared sum. -/

noncomputable section
open scoped BigOperators Topology
open Classical Filter

namespace QRHShort.SquarefreeAssembly

theorem prepared_smoothSupported_mul_positive {I : SupportInterval}
    {W g : ℝ → ℂ} (hW : SmoothSupported I W)
    (hg : ∀ x : ℝ, 0 < x → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g x) :
    SmoothSupported I (fun x => g x * W x) := by
  refine ⟨contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : 0 < x
    · exact (hg x hx).mul hW.1.contDiffAt
    · have hxl : x < I.lo := lt_of_le_of_lt (le_of_not_gt hx) I.lo_pos
      have hz : (fun y => g y * W y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [Iio_mem_nhds hxl] with y hy
        have hWy : W y = 0 := by
          by_contra hn
          exact (not_le_of_gt hy) (hW.2 hn).1
        simp only [hWy, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro x hx
    exact hW.2 (mul_ne_zero_iff.mp hx).2

theorem prepared_tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- The constant depends on the multiplier, support interval and order, and
is chosen before the varying compactly supported weight. -/
theorem prepared_weightNorm_mul_positive (I : SupportInterval) (J : ℕ)
    (g : ℝ → ℂ)
    (hg : ∀ x : ℝ, 0 < x → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ → ℂ, SmoothSupported I W →
      weightNorm J (fun x => g x * W x) ≤ C * weightNorm J W := by
  have hex (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ Set.Icc I.lo I.hi, ‖iteratedDeriv i g x‖ ≤ B := by
    have hc : ContinuousOn (fun x => ‖iteratedDeriv i g x‖)
        (Set.Icc I.lo I.hi) := by
      intro x hx
      have hd := (hg x (I.lo_pos.trans_le hx.1)).continuousAt_iteratedFDeriv
        (k := i) (by simp)
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hd.norm.continuousWithinAt
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro x hx
    exact (hB (Set.mem_image_of_mem _ hx)).trans (le_max_right _ _)
  choose B hB hb using hex
  let c (j : ℕ) : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i
  have hc (j : ℕ) : 0 ≤ c j := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (hB i))
  let C : ℝ := ∑ j ∈ Finset.range (J + 1), c j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hc j)
  refine ⟨C, hC, ?_⟩
  intro W hW
  have hV := prepared_smoothSupported_mul_positive hW hg
  have hN := weightNorm_nonneg hW J
  have hsupport : tsupport (fun x => g x * W x) ⊆ Set.Icc I.lo I.hi :=
    closure_minimal hV.2 isClosed_Icc
  apply QRHLean3.supZero_le (mul_nonneg hC hN)
  rintro r ⟨j, hj, x, rfl⟩
  by_cases hx : x ∈ Set.Icc I.lo I.hi
  · have hd : iteratedDeriv j (fun x => g x * W x) x =
        ∑ i ∈ Finset.range (j + 1),
          j.choose i * iteratedDeriv i g x * iteratedDeriv (j - i) W x := by
      exact iteratedDeriv_fun_mul ((hg x (I.lo_pos.trans_le hx.1)).of_le (by simp))
        (hW.1.contDiffAt.of_le (by simp))
    rw [hd]
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          ‖(j.choose i : ℂ) * iteratedDeriv i g x * iteratedDeriv (j - i) W x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * weightNorm J W := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [norm_mul, Complex.norm_natCast]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hb i x hx) (Nat.cast_nonneg _))
          (norm_iteratedDeriv_le_weightNorm hW ((Nat.sub_le j i).trans hj) x)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB i))
      _ = c j * weightNorm J W := (Finset.sum_mul _ _ _).symm
      _ ≤ C * weightNorm J W := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun i _ => hc i)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) hN
  · have hz : iteratedDeriv j (fun x => g x * W x) x = 0 := by
      by_contra hn
      exact hx (hsupport ((prepared_tsupport_iteratedDeriv_subset _ j)
        (subset_closure hn)))
    simpa only [hz, norm_zero] using mul_nonneg hC hN

theorem prepared_sqrt_contDiffAt {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => (Real.sqrt y : ℂ)) x :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_sqrt (ne_of_gt hx))

theorem prepared_sqrt_weight_smooth {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) :
    SmoothSupported I (fun x => (Real.sqrt x : ℂ) * W x) :=
  prepared_smoothSupported_mul_positive hW (fun _ hx => prepared_sqrt_contDiffAt hx)

theorem prepared_sqrt_weightNorm (I : SupportInterval) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ → ℂ, SmoothSupported I W →
      weightNorm J (fun x => (Real.sqrt x : ℂ) * W x) ≤ C * weightNorm J W :=
  prepared_weightNorm_mul_positive I J _ (fun _ hx => prepared_sqrt_contDiffAt hx)

/-- The order is uniform in the support interval and in the Euler derivative
up to a prescribed finite order; the transformed weight is the literal one. -/
theorem prepared_theta_euler_bounds (ht : ThetaBoundsStatement)
    (q : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ I : SupportInterval, ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : ℝ → ℂ, SmoothSupported I W → ∀ j ≤ q, ∀ x : ℝ, 0 < x →
        ‖eulerDerivative j (thetaWeight (fun y => (Real.sqrt y : ℂ) * W y)) x‖ ≤
          C * weightNorm J W * min (x ^ (1 / 4 : ℝ)) (x ^ (-A)) := by
  choose J hJ hbound using fun j => ht.2.2 A j hA
  let N : ℕ := 1 + ∑ j ∈ Finset.range (q + 1), J j
  have hJN (j : ℕ) (hj : j ≤ q) : J j ≤ N :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans (Nat.le_add_left _ _)
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro I
  choose K hK hb using fun j => hbound j I
  obtain ⟨B, hB, hbB⟩ := prepared_sqrt_weightNorm I N
  let C : ℝ := (∑ j ∈ Finset.range (q + 1), K j) * B
  refine ⟨C, mul_nonneg (Finset.sum_nonneg (fun j _ => hK j)) hB, ?_⟩
  intro W hW j hj x hx
  have hV := prepared_sqrt_weight_smooth hW
  have hnorm := (weightNorm_mono hV (hJN j hj)).trans (hbB W hW)
  have hsingle : K j ≤ ∑ i ∈ Finset.range (q + 1), K i :=
    Finset.single_le_sum (fun i _ => hK i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  calc
    _ ≤ K j * weightNorm (J j) (fun y => (Real.sqrt y : ℂ) * W y) *
        min (x ^ (1 / 4 : ℝ)) (x ^ (-A)) := hb j _ hV x hx
    _ ≤ C * weightNorm N W * min (x ^ (1 / 4 : ℝ)) (x ^ (-A)) := by
      apply mul_le_mul_of_nonneg_right _ (le_min (Real.rpow_nonneg hx.le _)
        (Real.rpow_nonneg hx.le _))
      calc
        _ ≤ K j * (B * weightNorm N W) := mul_le_mul_of_nonneg_left hnorm (hK j)
        _ ≤ (∑ i ∈ Finset.range (q + 1), K i) * (B * weightNorm N W) :=
          mul_le_mul_of_nonneg_right hsingle (mul_nonneg hB (weightNorm_nonneg hW N))
        _ = _ := by dsimp [C]; ring

/-- Uniform decay only needs a lower bound for the theta argument. In
particular the row variable need not lie in a bounded interval. -/
theorem prepared_theta_decay_of_lower_bound {z x : ℝ}
    (hz : 0 < z) (hzx : z ≤ x) :
    min (x ^ (1 / 4 : ℝ)) (x ^ (-3 : ℝ)) ≤
      8 * (1 + z) ^ (-3 : ℝ) := by
  have hx : 0 < x := hz.trans_le hzx
  have hmin : min (x ^ (1 / 4 : ℝ)) (x ^ (-3 : ℝ)) ≤ 1 := by
    by_cases hx1 : x ≤ 1
    · exact (min_le_left _ _).trans (Real.rpow_le_one hx.le hx1 (by norm_num))
    · exact (min_le_right _ _).trans
        (Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt (lt_of_not_ge hx1)) (by norm_num))
  by_cases hz1 : z ≤ 1
  · have hpow : (2 : ℝ) ^ (-3 : ℝ) ≤ (1 + z) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    have htwo : (2 : ℝ) ^ (-3 : ℝ) = (1 / 8 : ℝ) := by
      norm_num [Real.rpow_neg_natCast]
    rw [htwo] at hpow
    linarith
  · have hsum : 1 + z ≤ 2 * z := by linarith
    have hpow : (2 * z) ^ (-3 : ℝ) ≤ (1 + z) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hsum (by norm_num)
    calc
      _ ≤ x ^ (-3 : ℝ) := min_le_right _ _
      _ ≤ z ^ (-3 : ℝ) := Real.rpow_le_rpow_of_nonpos hz hzx (by norm_num)
      _ = 8 * (2 * z) ^ (-3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hz.le]
        norm_num [Real.rpow_neg_natCast] <;> ring
      _ ≤ 8 * (1 + z) ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem prepared_theta_uniform_euler_bounds (ht : ThetaBoundsStatement) (q : ℕ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ I : SupportInterval, ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : ℝ → ℂ, SmoothSupported I W → ∀ j ≤ q, ∀ z x : ℝ,
        0 < z → z ≤ x →
        ‖eulerDerivative j (thetaWeight (fun y => (Real.sqrt y : ℂ) * W y)) x‖ ≤
          C * weightNorm J W * (1 + z) ^ (-3 : ℝ) := by
  obtain ⟨J, hJ, hb⟩ := prepared_theta_euler_bounds ht q (by norm_num : (0 : ℝ) < 3)
  refine ⟨J, hJ, ?_⟩
  intro I
  obtain ⟨C, hC, hc⟩ := hb I
  refine ⟨8 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro W hW j hj z x hz hzx
  calc
    _ ≤ C * weightNorm J W * min (x ^ (1 / 4 : ℝ)) (x ^ (-3 : ℝ)) :=
      hc W hW j hj x (hz.trans_le hzx)
    _ ≤ C * weightNorm J W * (8 * (1 + z) ^ (-3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (prepared_theta_decay_of_lower_bound hz hzx)
        (mul_nonneg hC (weightNorm_nonneg hW J))
    _ = _ := by ring

end QRHShort.SquarefreeAssembly
end
end
end

section
/- Source fragment: VPreparedMellinUniform; SHA256 fd35ddad393b48426291724009151d053b953f4a472b87529f1bc03ef256c81e -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly
open ThetaBoundsProof

/-- The two actual Mellin contours have one derivative order, selected before
the support interval. This uses the already proved contour kernels directly. -/
theorem prepared_mellin_two_contours (I : SupportInterval) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ → ℂ, SmoothSupported I W →
      ∀ ρ : ℝ, (ρ = 0 ∨ ρ = 3) →
        Continuous (mellinKernel 0 (fun x => (Real.sqrt x : ℂ) * W x) ρ) ∧
        Integrable (mellinKernel 0 (fun x => (Real.sqrt x : ℂ) * W x) ρ) ∧
        (∫ s : ℝ, ‖mellinKernel 0 (fun x => (Real.sqrt x : ℂ) * W x) ρ s‖) ≤
          C * weightNorm 18 W := by
  obtain ⟨B, hB, hBbound⟩ := prepared_sqrt_weightNorm I 18
  obtain ⟨C₀, hC₀, hzero⟩ := CloudBatch.mellin_kernel_L1_bound 3 0 I 0 (by norm_num)
  obtain ⟨C₃, hC₃, hthree⟩ := CloudBatch.mellin_kernel_L1_bound 3 0 I 3 (by norm_num)
  refine ⟨max C₀ C₃ * B, mul_nonneg (hC₀.trans (le_max_left _ _)) hB, ?_⟩
  intro W hW ρ hρ
  have hV := prepared_sqrt_weight_smooth hW
  have hnorm := hBbound W hW
  have hnorm0 := weightNorm_nonneg hV 18
  have hρlo : -(1 / 4 : ℝ) ≤ ρ := by rcases hρ with rfl | rfl <;> norm_num
  refine ⟨CloudBatch.mellin_kernel_continuous hV 0 ρ hρlo, ?_⟩
  rcases hρ with rfl | rfl
  · obtain ⟨hi, hb⟩ := hzero _ hV
    refine ⟨hi, ?_⟩
    calc
      _ ≤ C₀ * weightNorm 18 (fun x => (Real.sqrt x : ℂ) * W x) := by simpa using hb
      _ ≤ max C₀ C₃ * weightNorm 18 (fun x => (Real.sqrt x : ℂ) * W x) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnorm0
      _ ≤ max C₀ C₃ * (B * weightNorm 18 W) :=
        mul_le_mul_of_nonneg_left hnorm (hC₀.trans (le_max_left _ _))
      _ = _ := by ring
  · obtain ⟨hi, hb⟩ := hthree _ hV
    refine ⟨hi, ?_⟩
    calc
      _ ≤ C₃ * weightNorm 18 (fun x => (Real.sqrt x : ℂ) * W x) := by simpa using hb
      _ ≤ max C₀ C₃ * weightNorm 18 (fun x => (Real.sqrt x : ℂ) * W x) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hnorm0
      _ ≤ max C₀ C₃ * (B * weightNorm 18 W) :=
        mul_le_mul_of_nonneg_left hnorm (hC₀.trans (le_max_left _ _))
      _ = _ := by ring

/-- Exact one-dimensional separation of the literal theta weight on either
chosen contour. No compactification of the row variable is involved. -/
theorem prepared_theta_mellin_eq {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (ρ : ℝ) (hρ : ρ = 0 ∨ ρ = 3)
    {x : ℝ} (hx : 0 < x) :
    thetaWeight (fun y => (Real.sqrt y : ℂ) * W y) x =
      ∫ s : ℝ, mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ s *
        (x : ℂ) ^ (-contourPoint ρ s) := by
  have hρlo : -(1 / 4 : ℝ) ≤ ρ := by rcases hρ with rfl | rfl <;> norm_num
  exact CloudBatch.theta_bounds_mellin_shift_proved 0 I _
    (prepared_sqrt_weight_smooth hW) ρ hρlo x hx

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VPreparedMellinPowers; SHA256 d5cb9ba215610965b90db6a85d28944517b1e719c5ee5111008ce15851ddfc8d -/

noncomputable section

namespace QRHShort.ThetaBoundsProof

/-- Positive real factors permit the literal Mellin scaling without a branch correction. -/
theorem prepared_mellin_cpow_split {T x v : ℝ}
    (hT : 0 < T) (hx : 0 < x) (hv : 0 < v) (ρ s : ℝ) :
    ((T * x / v ^ 2 : ℝ) : ℂ) ^ (-contourPoint ρ s) =
      (T : ℂ) ^ (-contourPoint ρ s) * (x : ℂ) ^ (-contourPoint ρ s) *
        (v : ℂ) ^ (2 * contourPoint ρ s) := by
  let t := contourPoint ρ s
  change ((T * x / v ^ 2 : ℝ) : ℂ) ^ (-t) =
    (T : ℂ) ^ (-t) * (x : ℂ) ^ (-t) * (v : ℂ) ^ (2 * t)
  calc
    _ = (((T * x : ℝ) : ℂ) / ((v * v : ℝ) : ℂ)) ^ (-t) := by
      congr 1
      push_cast
      ring
    _ = ((T * x : ℝ) : ℂ) ^ (-t) / ((v * v : ℝ) : ℂ) ^ (-t) :=
      Complex.div_cpow_ofReal_nonneg (mul_nonneg hT.le hx.le)
        (mul_nonneg hv.le hv.le) (-t)
    _ = ((T : ℂ) ^ (-t) * (x : ℂ) ^ (-t)) /
        ((v : ℂ) ^ (-t) * (v : ℂ) ^ (-t)) := by
      simp only [Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hT.le hx.le,
        Complex.mul_cpow_ofReal_nonneg hv.le hv.le]
    _ = _ := by
      simp only [Complex.cpow_neg, Complex.cpow_ofNat_mul, div_eq_mul_inv,
        mul_inv_rev, inv_inv, pow_two, mul_assoc]

/-- The T factor has precisely the contour's real decay. -/
theorem prepared_mellin_T_norm {T : ℝ} (hT : 0 < T) (ρ s : ℝ) :
    ‖(T : ℂ) ^ (-contourPoint ρ s)‖ = T ^ (-ρ) :=
  contour_cpow_norm hT ρ s

/-- The column factor costs at most one on x ≥ 1 and a nonnegative contour. -/
theorem prepared_mellin_x_norm_le {x ρ : ℝ} (hx : 1 ≤ x) (hρ : 0 ≤ ρ) (s : ℝ) :
    ‖(x : ℂ) ^ (-contourPoint ρ s)‖ = x ^ (-ρ) ∧
      ‖(x : ℂ) ^ (-contourPoint ρ s)‖ ≤ 1 := by
  have heq := contour_cpow_norm (lt_of_lt_of_le zero_lt_one hx) ρ s
  exact ⟨heq, heq.le.trans (Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hρ))⟩

/-- The smoothing factor costs at most one on 0 < v ≤ 1. -/
theorem prepared_mellin_v_norm_le {v ρ : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hρ : 0 ≤ ρ) (s : ℝ) :
    ‖(v : ℂ) ^ (2 * contourPoint ρ s)‖ = v ^ (2 * ρ) ∧
      ‖(v : ℂ) ^ (2 * contourPoint ρ s)‖ ≤ 1 := by
  have heq : ‖(v : ℂ) ^ (2 * contourPoint ρ s)‖ = v ^ (2 * ρ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
    congr 1
    simp [contourPoint, Complex.mul_re]
  exact ⟨heq, heq.le.trans (Real.rpow_le_one hv.le hv1 (mul_nonneg (by norm_num) hρ))⟩

/-- The two contours needed for a uniformly decaying prepared weight. -/
def preparedMellinContour (z : ℝ) : ℝ := if z ≤ 1 then 0 else 3

theorem prepared_mellin_contour_nonneg (z : ℝ) : 0 ≤ preparedMellinContour z := by
  unfold preparedMellinContour
  split_ifs <;> norm_num

/-- A choice of contour gives cubic decay, uniformly in T ≥ z > 0. -/
theorem prepared_mellin_decay {z T : ℝ} (hz : 0 < z) (hzT : z ≤ T) :
    T ^ (-preparedMellinContour z) ≤ 8 * (1 + z) ^ (-3 : ℝ) := by
  have hT : 0 < T := hz.trans_le hzT
  have hp : 0 < 1 + z := by linarith
  by_cases hz1 : z ≤ 1
  · simp only [preparedMellinContour, if_pos hz1, neg_zero, Real.rpow_zero]
    rw [Real.rpow_neg hp.le, Real.rpow_ofNat]
    change 1 ≤ 8 / (1 + z) ^ 3
    apply (le_div_iff₀ (pow_pos hp 3)).2
    have hcube := pow_le_pow_left₀ hp.le (show 1 + z ≤ 2 by linarith) 3
    norm_num at hcube
    nlinarith
  · simp only [preparedMellinContour, if_neg hz1]
    rw [Real.rpow_neg hT.le, Real.rpow_ofNat, Real.rpow_neg hp.le, Real.rpow_ofNat]
    have hmain : 1 / T ^ 3 ≤ 8 / (1 + z) ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hT 3) (pow_pos hp 3)).2
      have hcube := pow_le_pow_left₀ hp.le (show 1 + z ≤ 2 * T by linarith) 3
      nlinarith [hcube]
    simpa only [div_eq_mul_inv, one_mul] using hmain

end QRHShort.ThetaBoundsProof

end
end

section
/- Source fragment: VPreparedMellinIntegral; SHA256 dac893ee9c16b6c630506437e0f463b9816facb8b42fe1c3deda565cfb5171f5 -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly
open ThetaBoundsProof

theorem prepared_mellin_cpow_continuous {x : ℝ} (hx : 0 < x) (ρ : ℝ) :
    Continuous (fun s : ℝ => (x : ℂ) ^ (-contourPoint ρ s)) := by
  have ht : Continuous (fun s : ℝ => -contourPoint ρ s) := by
    unfold contourPoint
    fun_prop
  exact ht.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))

theorem prepared_mellin_integrand_integrable {I : SupportInterval} {W : ℝ → ℂ}
    (hW : SmoothSupported I W) (ρ : ℝ) (hρ : ρ = 0 ∨ ρ = 3)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun s : ℝ =>
      mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ s *
        (x : ℂ) ^ (-contourPoint ρ s)) := by
  obtain ⟨C, hC, hb⟩ := prepared_mellin_two_contours I
  obtain ⟨hc, hi, _⟩ := hb W hW ρ hρ
  apply (hi.norm.mul_const (x ^ (-ρ))).mono'
    (hi.aestronglyMeasurable.mul
      (prepared_mellin_cpow_continuous hx ρ).aestronglyMeasurable)
  filter_upwards [] with s
  simp only [Pi.mul_apply, norm_mul, contour_cpow_norm hx]
  exact le_rfl

/-- Finite columns separate directly on the actual Mellin contour. The row
coordinate only contributes a phase and a nonincreasing real power. -/
theorem prepared_finite_theta_mellin_eq {ι : Type*}
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    (ρ : ℝ) (hρ : ρ = 0 ∨ ρ = 3)
    (T v : ℝ) (hT : 0 < T) (hv : 0 < v)
    (columns : Finset ι) (x : ι → ℝ) (B : ι → ℂ)
    (hx : ∀ n ∈ columns, 0 < x n) :
    (∑ n ∈ columns, B n *
      thetaWeight (fun y => (Real.sqrt y : ℂ) * W y) (T * x n / v ^ 2)) =
      ∫ s : ℝ,
        (mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ s *
          (T : ℂ) ^ (-contourPoint ρ s) * (v : ℂ) ^ (2 * contourPoint ρ s)) *
          ∑ n ∈ columns, B n * (x n : ℂ) ^ (-contourPoint ρ s) := by
  have harg (n : ι) (hn : n ∈ columns) : 0 < T * x n / v ^ 2 :=
    div_pos (mul_pos hT (hx n hn)) (sq_pos_of_pos hv)
  have hi (n : ι) (hn : n ∈ columns) :
      Integrable (fun s : ℝ => B n *
        (mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ s *
          ((T * x n / v ^ 2 : ℝ) : ℂ) ^ (-contourPoint ρ s))) :=
    (prepared_mellin_integrand_integrable hW ρ hρ (harg n hn)).const_mul (B n)
  calc
    _ = ∑ n ∈ columns, ∫ s : ℝ, B n *
        (mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ s *
          ((T * x n / v ^ 2 : ℝ) : ℂ) ^ (-contourPoint ρ s)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [prepared_theta_mellin_eq hW ρ hρ (harg n hn), integral_const_mul]
    _ = ∫ s : ℝ, ∑ n ∈ columns, B n *
        (mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ s *
          ((T * x n / v ^ 2 : ℝ) : ℂ) ^ (-contourPoint ρ s)) :=
      (integral_finsetSum columns hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [prepared_mellin_cpow_split hT (hx n hn) hv]
      ring

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VPreparedRealMellinData; SHA256 aa3c194bc159e01d8f7171b81971be0024a93632327622e9ead2771a8cae54c9 -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace QRHShort.SquarefreeAssembly

/-- A genuine one-dimensional Mellin representation. The amplitude remains
in beta; the common envelope and its mass are independent of that amplitude. -/
structure RealMellinData (J : ℕ) (C : ℝ) (S : Finset (Ideal O))
    (W : ℝ → ℂ) (H Y a : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (b : Ideal O) where
  columns : Finset (Ideal O)
  envelope : ℝ → ℝ
  coefficient : Ideal O → ℝ → ℂ
  beta : ℝ → Ideal O → ℂ
  admissible : ∀ n ∈ columns, n ≠ ⊥ ∧ Squarefree n ∧
    IsRelPrime n (principal 3) ∧ (2 : ℝ) ^ p.2.1 ≤ normIdeal n ∧
      normIdeal n ≤ 2 * (2 : ℝ) ^ p.2.1
  envelope_nonneg : ∀ s, 0 ≤ envelope s
  envelope_integrable : Integrable envelope
  coefficient_measurable : ∀ k ∈ sieveRows S H, Measurable (coefficient k)
  beta_measurable : ∀ n ∈ columns, Measurable (fun s => beta s n)
  coefficient_bound : ∀ k ∈ sieveRows S H, ∀ s, ‖coefficient k s‖ ≤ envelope s
  beta_bound : ∀ s n, n ∈ columns → ‖beta s n‖ ≤ a / Real.sqrt (normIdeal n)
  mass_bound : (∫ s : ℝ, envelope s) ≤
    C * |weightNorm J W| * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
      (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹
  column_eq : ∀ k ∈ sieveRows S H,
    preparedThetaColumn W H Y A coeff t p b k =
      ∫ s : ℝ, coefficient k s *
        ∑ n ∈ columns, beta s n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)

def PreparedThetaRealMellinEstimate : Prop :=
  ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∃ J : ℕ, 1 ≤ J ∧
    ∀ (S : Finset (Ideal O)) (I : SupportInterval),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℝ → ℂ) (H Y a : ℝ)
        (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ),
        SmoothSupported I W → 1 ≤ H → 0 < Y → 0 ≤ a →
        (∀ r n b, ‖A r n b‖ ≤ a) →
        (∀ r k, k ∈ sieveRows S H → ‖coeff r k‖ ≤ 1) →
        ∀ (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex)
          (b : Ideal O), b ∈ preparedColumnIdeals t p →
            Nonempty (RealMellinData J C S W H Y a A coeff t p b)

def PreparedThetaRealMellinStep : Prop :=
  ThetaBoundsStatement → SmoothSeparationStatement → PreparedThetaRealMellinEstimate

theorem prepared_real_column_mass_square_bound {Q C H Y a σ w : ℝ}
    (hQ : 0 ≤ Q) (hH : 0 ≤ H) (hY : 0 < Y)
    (p : PreparedBlockIndex) (b : Ideal O) :
    (Q * a ^ 2 * (H * (2 : ℝ) ^ p.2.1) ^ σ * (H + (2 : ℝ) ^ p.2.1)) *
        (C * |w| * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
          (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹) ^ 2 ≤
      ((Q * C ^ 2 * w ^ 2 * a ^ 2) *
        ((H * (2 : ℝ) ^ p.2.1) ^ σ *
          (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
        preparedBlockWeight H Y p ^ 2) * (normIdeal b)⁻¹ ^ 2 := by
  have hbase := prepared_column_mass_square_bound
    (Q := Q * a ^ 2) (C := C) (H := H) (Y := Y) (a := 1) (σ := σ) (w := w)
    (mul_nonneg hQ (sq_nonneg a)) hH hY p b
  convert hbase using 1 <;> ring

/-- The amplitude contributes Q*a^2 to the pointwise energy. It is not
divided out of beta, so this statement also covers a=0. -/
theorem prepared_column_bound_of_real_mellin_data
    (hr : RecombinationStatement) {S : Finset (Ideal O)} {σ Q : ℝ}
    (hQ : 0 ≤ Q)
    (hq : ∀ (H U a : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ),
      1 ≤ H → 1 ≤ U → 0 ≤ a →
      (∀ n ∈ columns, n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3) ∧
        U ≤ normIdeal n ∧ normIdeal n ≤ 2 * U) →
      (∀ n ∈ columns, ‖β n‖ ≤ a / Real.sqrt (normIdeal n)) →
      (∑ k ∈ sieveRows S H,
        ‖∑ n ∈ columns, β n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)‖ ^ 2) ≤
          Q * a ^ 2 * (H * U) ^ σ * (H + U))
    {J : ℕ} {C H Y a : ℝ} {W : ℝ → ℂ}
    {A : ℕ → Ideal O → Ideal O → ℂ} {coeff : ℕ → Ideal O → ℂ}
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex} {b : Ideal O}
    (hH : 1 ≤ H) (hY : 0 < Y) (ha : 0 ≤ a)
    (data : RealMellinData J C S W H Y a A coeff t p b) :
    (∑ k ∈ sieveRows S H, ‖preparedThetaColumn W H Y A coeff t p b k‖ ^ 2) ≤
      ((Q * C ^ 2 * weightNorm J W ^ 2 * a ^ 2) *
        ((H * (2 : ℝ) ^ p.2.1) ^ σ *
          (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
        preparedBlockWeight H Y p ^ 2) * (normIdeal b)⁻¹ ^ 2 := by
  let F : Ideal O → ℝ → ℂ := fun k s =>
    ∑ n ∈ data.columns, data.beta s n * sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)
  let M : ℝ := Q * a ^ 2 * (H * (2 : ℝ) ^ p.2.1) ^ σ * (H + (2 : ℝ) ^ p.2.1)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hFi (k : Ideal O) (_ : k ∈ sieveRows S H) : Measurable (F k) := by
    exact Finset.measurable_sum data.columns (fun n hn =>
      (data.beta_measurable n hn).mul_const _)
  have hFE (s : ℝ) : (∑ k ∈ sieveRows S H, ‖F k s‖ ^ 2) ≤ M := by
    exact hq H ((2 : ℝ) ^ p.2.1) a data.columns (data.beta s) hH
      (one_le_pow₀ (by norm_num)) ha data.admissible (data.beta_bound s)
  obtain ⟨_, hbound⟩ := prepared_integral_energy_bound hr volume (sieveRows S H)
    data.envelope data.coefficient F hM data.envelope_nonneg data.envelope_integrable
    data.coefficient_measurable hFi data.coefficient_bound hFE
  have hmass : 0 ≤ ∫ s : ℝ, data.envelope s := integral_nonneg data.envelope_nonneg
  calc
    _ = ∑ k ∈ sieveRows S H, ‖∫ s : ℝ, data.coefficient k s * F k s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [data.column_eq k hk]
    _ ≤ M * (∫ s : ℝ, data.envelope s) ^ 2 := hbound
    _ ≤ M * (C * |weightNorm J W| * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) *
        (1 + preparedBlockScale Y p) ^ (-3 : ℝ) * (normIdeal b)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmass data.mass_bound 2) hM
    _ ≤ _ := prepared_real_column_mass_square_bound hQ hH0 hY p b

theorem prepared_theta_raw_of_real_mellin
    (hm : PreparedThetaRealMellinEstimate) (hq : QuadraticEstimate)
    (hr : RecombinationStatement) : PreparedThetaDyadicRawEstimate := by
  intro σ hσ hσcap
  obtain ⟨J, hJ, hm⟩ := hm σ hσ hσcap
  refine ⟨J, hJ, ?_⟩
  intro S I
  obtain ⟨C, hC, hm⟩ := hm S I
  obtain ⟨Q, hQ, hq⟩ := prepared_quadratic_column_bound hq S hσ
  obtain ⟨B, hB, hBbound⟩ := prepared_column_energy_bound
  refine ⟨B * (Q * C ^ 2), by positivity, ?_⟩
  intro W H Y a A coeff hW hH hY ha hA hcoeff t p
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hz : 0 < 1 + preparedBlockScale Y p := by
    have := preparedBlockScale_pos hY p
    linarith
  let M : ℝ := (Q * C ^ 2 * weightNorm J W ^ 2 * a ^ 2) *
    ((H * (2 : ℝ) ^ p.2.1) ^ σ * (1 + preparedBlockScale Y p) ^ (-2 : ℝ)) *
      preparedBlockWeight H Y p ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcol (b : Ideal O) (hb : b ∈ preparedColumnIdeals t p) :
      (∑ k ∈ sieveRows S H, ‖preparedThetaColumn W H Y A coeff t p b k‖ ^ 2) ≤
        M * (normIdeal b)⁻¹ ^ 2 := by
    obtain ⟨data⟩ := hm W H Y a A coeff hW hH hY ha hA hcoeff t p b hb
    exact prepared_column_bound_of_real_mellin_data hr hQ hq hH hY ha data
  have hbound := hBbound M ((2 : ℝ) ^ p.2.2) (sieveRows S H)
    (preparedColumnIdeals t p) (preparedThetaColumn W H Y A coeff t p)
    hM (by positivity) (fun _ hb => preparedColumnIdeals_norm_range hb) hcol
  simp_rw [sum_preparedThetaColumn] at hbound
  exact hbound.trans_eq (by dsimp [M]; ring)

theorem prepared_theta_raw_step_of_real_mellin
    (hm : PreparedThetaRealMellinStep) : PreparedThetaDyadicRawStep := by
  intro htheta hquadratic hseparation hrecombination
  exact prepared_theta_raw_of_real_mellin (hm htheta hseparation)
    hquadratic hrecombination

theorem prepared_theta_dyadic_step_of_real_mellin
    (hm : PreparedThetaRealMellinStep) : PreparedThetaDyadicStep :=
  prepared_theta_dyadic_step_of_raw (prepared_theta_raw_step_of_real_mellin hm)

theorem prepared_theta_truncation_step_of_real_mellin
    (hm : PreparedThetaRealMellinStep) : PreparedThetaTruncationStep :=
  prepared_theta_truncation_step_of_raw (prepared_theta_raw_step_of_real_mellin hm)

/-- Conditional assembly into the unchanged frozen prepared-step interface. -/
theorem prepared_theta_step_of_real_mellin
    (hm : PreparedThetaRealMellinStep) : PreparedThetaEstimateStep :=
  prepared_theta_step_of_raw (prepared_theta_raw_step_of_real_mellin hm)

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VPreparedMellinConstruction; SHA256 cde38636d7c8db33962b2ade05da8878470a8f394304324d78334f9ce7fb5747 -/

noncomputable section
open MeasureTheory Classical
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly
open ThetaBoundsProof

/-- Build the actual real Mellin data from the exact finite column identity.
All row dependence is confined to a bounded coefficient; the column array
retains its amplitude, including the case of zero amplitude. -/
theorem prepared_real_mellin_data_from_column
    {I : SupportInterval} {W : ℝ → ℂ} (hW : SmoothSupported I W)
    {C : ℝ} (hC : 0 ≤ C)
    (hkernel : ∀ ρ : ℝ, (ρ = 0 ∨ ρ = 3) →
      Continuous (mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ) ∧
      Integrable (mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ) ∧
      (∫ s : ℝ, ‖mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ s‖) ≤
        C * weightNorm 18 W)
    (S : Finset (Ideal O)) (H Y a : ℝ) (hY : 0 < Y) (ha : 0 ≤ a)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (hA : ∀ r n b, ‖A r n b‖ ≤ a)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (b : Ideal O)
    (columns : Finset (Ideal O))
    (hadmissible : ∀ n ∈ columns, n ≠ ⊥ ∧ Squarefree n ∧
      IsRelPrime n (principal 3) ∧ (2 : ℝ) ^ p.2.1 ≤ normIdeal n ∧
        normIdeal n ≤ 2 * (2 : ℝ) ^ p.2.1)
    (T scale : ℝ) (hT : preparedBlockScale Y p ≤ T)
    (hscale : 0 ≤ scale)
    (hscale_eq : scale = (3 : ℝ) ^ (4 / 3 : ℝ) *
      (3 : ℝ) ^ (-(p.1 : ℝ) / 3) * (normIdeal b)⁻¹)
    (v : Ideal O → ℝ) (hv : ∀ k ∈ sieveRows S H, 0 < v k ∧ v k ≤ 1)
    (q : Ideal O → ℂ) (hq : ∀ k ∈ sieveRows S H, ‖q k‖ ≤ 1)
    (hcolumn : ∀ k ∈ sieveRows S H,
      preparedThetaColumn W H Y A coeff t p b k =
        (scale : ℂ) * q k * ∑ n ∈ columns,
          (A p.1 n b / (Real.sqrt (normIdeal n) : ℂ) *
            sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)) *
          thetaWeight (fun y => (Real.sqrt y : ℂ) * W y)
            (T * (normIdeal n / (2 : ℝ) ^ p.2.1) / v k ^ 2)) :
    Nonempty (RealMellinData 18 (8 * (3 : ℝ) ^ (4 / 3 : ℝ) * C)
      S W H Y a A coeff t p b) := by
  let z := preparedBlockScale Y p
  let ρ := preparedMellinContour z
  let f : ℝ → ℂ := mellinKernel 0 (fun y => (Real.sqrt y : ℂ) * W y) ρ
  let x : Ideal O → ℝ := fun n => normIdeal n / (2 : ℝ) ^ p.2.1
  let beta : ℝ → Ideal O → ℂ := fun s n =>
    A p.1 n b / (Real.sqrt (normIdeal n) : ℂ) * (x n : ℂ) ^ (-contourPoint ρ s)
  let c : Ideal O → ℝ → ℂ := fun k s =>
    (scale : ℂ) * q k * f s * (T : ℂ) ^ (-contourPoint ρ s) *
      (v k : ℂ) ^ (2 * contourPoint ρ s)
  let e : ℝ → ℝ := fun s => scale * ‖f s‖ * T ^ (-ρ)
  have hz : 0 < z := preparedBlockScale_pos hY p
  have hTpos : 0 < T := hz.trans_le hT
  have hρ : ρ = 0 ∨ ρ = 3 := by
    dsimp [ρ, preparedMellinContour]
    split_ifs <;> simp
  have hρ0 : 0 ≤ ρ := prepared_mellin_contour_nonneg z
  obtain ⟨hf, hfi, hmass⟩ := hkernel ρ hρ
  have hx1 (n : Ideal O) (hn : n ∈ columns) : 1 ≤ x n :=
    (one_le_div (by positivity)).mpr (hadmissible n hn).2.2.2.1
  have hx (n : Ideal O) (hn : n ∈ columns) : 0 < x n := zero_lt_one.trans_le (hx1 n hn)
  have hpowT : 0 ≤ T ^ (-ρ) := Real.rpow_nonneg hTpos.le _
  have he : ∀ s, 0 ≤ e s := fun s =>
    mul_nonneg (mul_nonneg hscale (norm_nonneg _)) hpowT
  have hei : Integrable e := (hfi.norm.const_mul scale).mul_const (T ^ (-ρ))
  refine ⟨{
    columns := columns
    envelope := e
    coefficient := c
    beta := beta
    admissible := hadmissible
    envelope_nonneg := he
    envelope_integrable := hei
    coefficient_measurable := ?_
    beta_measurable := ?_
    coefficient_bound := ?_
    beta_bound := ?_
    mass_bound := ?_
    column_eq := ?_
  }⟩
  · intro k hk
    have hrow : Continuous (fun s : ℝ => (v k : ℂ) ^ (2 * contourPoint ρ s)) := by
      have ht : Continuous (fun s : ℝ => 2 * contourPoint ρ s) := by
        unfold contourPoint
        fun_prop
      exact ht.const_cpow (.inl (Complex.ofReal_ne_zero.mpr (hv k hk).1.ne'))
    exact ((((hf.const_mul ((scale : ℂ) * q k)).mul
      (prepared_mellin_cpow_continuous hTpos ρ)).mul hrow)).measurable
  · intro n hn
    exact ((prepared_mellin_cpow_continuous (hx n hn) ρ).const_mul
      (A p.1 n b / (Real.sqrt (normIdeal n) : ℂ))).measurable
  · intro k hk s
    have hrow := (prepared_mellin_v_norm_le (hv k hk).1 (hv k hk).2 hρ0 s).2
    dsimp [c, e]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hscale, prepared_mellin_T_norm hTpos]
    calc
      _ ≤ scale * 1 * ‖f s‖ * T ^ (-ρ) * 1 := by
        gcongr
        · exact hq k hk
      _ = _ := by ring
  · intro s n hn
    have hnorm : 0 ≤ normIdeal n :=
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ p.2.1).trans (hadmissible n hn).2.2.2.1
    have hxp := (prepared_mellin_x_norm_le (hx1 n hn) hρ0 s).2
    dsimp [beta]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (a / Real.sqrt (normIdeal n)) * 1 :=
        mul_le_mul (div_le_div_of_nonneg_right (hA _ _ _) (Real.sqrt_nonneg _))
          hxp (norm_nonneg _) (div_nonneg ha (Real.sqrt_nonneg _))
      _ = _ := mul_one _
  · have hdecay := prepared_mellin_decay hz hT
    have hweight := weightNorm_nonneg hW 18
    change (∫ s : ℝ, scale * ‖f s‖ * T ^ (-ρ)) ≤ _
    rw [integral_mul_const, integral_const_mul]
    calc
      _ ≤ (scale * (C * weightNorm 18 W)) * T ^ (-ρ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hscale) hpowT
      _ ≤ (scale * (C * weightNorm 18 W)) * (8 * (1 + z) ^ (-3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdecay (mul_nonneg hscale (mul_nonneg hC hweight))
      _ = _ := by rw [hscale_eq, abs_of_nonneg hweight]; dsimp [z]; ring
  · intro k hk
    rw [hcolumn k hk, prepared_finite_theta_mellin_eq hW ρ hρ T (v k)
      hTpos (hv k hk).1 columns x
      (fun n => A p.1 n b / (Real.sqrt (normIdeal n) : ℂ) *
        sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)) hx]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp [c, beta, f]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VPreparedMellinScales; SHA256 14f6817398c50cbf2e2ac34b7db01eb58762f406e3c9d839c5b8549cea99debf -/

noncomputable section
open Classical

namespace QRHShort.SquarefreeAssembly

/-- The row-independent Mellin scale of a prepared column. -/
def preparedMellinBase (Y : ℝ) (p : PreparedBlockIndex) (b : Ideal O) : ℝ :=
  (3 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2.1 * normIdeal b ^ 3 / (81 * Y)

/-- The row norm divided by the original height. -/
def preparedMellinRow (H : ℝ) (k : Ideal O) : ℝ := normIdeal k / H

/-- The exact scalar left after removing the square-root column factor. -/
def preparedMellinScalar (p : PreparedBlockIndex) (b : Ideal O) : ℝ :=
  ((3 : ℝ) ^ (((((p.1 : ℤ) - 4 : ℤ) : ℝ)) / 3) * normIdeal b)⁻¹

theorem prepared_mellin_base_range {Y : ℝ} (hY : 0 < Y)
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex} {b : Ideal O}
    (hb : b ∈ preparedColumnIdeals t p) :
    preparedBlockScale Y p ≤ preparedMellinBase Y p b ∧
      0 < preparedBlockScale Y p := by
  obtain ⟨_, hlo, _⟩ := preparedColumnIdeals_norm_range hb
  have hcube : (8 : ℝ) ^ p.2.2 ≤ normIdeal b ^ 3 := by
    calc
      _ = ((2 : ℝ) ^ 3) ^ p.2.2 := by norm_num
      _ = ((2 : ℝ) ^ p.2.2) ^ 3 := pow_right_comm _ _ _
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hlo 3
  refine ⟨?_, preparedBlockScale_pos hY p⟩
  unfold preparedBlockScale preparedMellinBase
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left hcube (by positivity)

theorem prepared_mellin_base_pos {Y : ℝ} (hY : 0 < Y)
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex} {b : Ideal O}
    (hb : b ∈ preparedColumnIdeals t p) : 0 < preparedMellinBase Y p b :=
  (prepared_mellin_base_range hY hb).2.trans_le (prepared_mellin_base_range hY hb).1

theorem prepared_mellin_row_range {S : Finset (Ideal O)} {H : ℝ}
    (hH : 1 ≤ H) {k : Ideal O} (hk : k ∈ sieveRows S H) :
    0 < preparedMellinRow H k ∧ preparedMellinRow H k ≤ 1 := by
  obtain ⟨hout, _, hnorm⟩ := (mem_sieveRows S H k).mp hk
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hkpos : 0 < normIdeal k := by
    change (0 : ℝ) < (k.absNorm : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hout.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  exact ⟨div_pos hkpos hHpos, (div_le_one hHpos).2 hnorm⟩

/-- The original theta argument, including the integer shift r - 4,
uses precisely the column scale and the normalized row. -/
theorem prepared_mellin_theta_argument {H Y : ℝ} (hH : 0 < H) (hY : 0 < Y)
    (p : PreparedBlockIndex) (b n : Ideal O) {k : Ideal O} (hk : k ≠ ⊥) :
    (3 : ℝ) ^ ((((p.1 : ℤ) - 4 : ℤ) : ℝ)) * normIdeal n * normIdeal b ^ 3 * H ^ 2 /
        (Y * normIdeal k ^ 2) =
      preparedMellinBase Y p b * (normIdeal n / (2 : ℝ) ^ p.2.1) /
        preparedMellinRow H k ^ 2 := by
  have hkpos : 0 < normIdeal k := by
    change (0 : ℝ) < (k.absNorm : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hk (Ideal.absNorm_eq_zero_iff.mp h))
  have hshift : (3 : ℝ) ^ ((((p.1 : ℤ) - 4 : ℤ) : ℝ)) = (3 : ℝ) ^ p.1 / 81 := by
    have he : ((((p.1 : ℤ) - 4 : ℤ) : ℝ)) = (p.1 : ℝ) - 4 := by push_cast; ring
    rw [he, Real.rpow_sub (by norm_num), Real.rpow_natCast]
    norm_num
  rw [hshift]
  unfold preparedMellinBase preparedMellinRow
  field_simp [ne_of_gt hH, ne_of_gt hY, ne_of_gt hkpos]
  <;> ring

/-- The scalar retains the exact absolute factor 3^(4/3). -/
theorem prepared_mellin_scalar_eq (p : PreparedBlockIndex) (b : Ideal O) :
    preparedMellinScalar p b =
      (3 : ℝ) ^ (4 / 3 : ℝ) * (3 : ℝ) ^ (-(p.1 : ℝ) / 3) * (normIdeal b)⁻¹ := by
  unfold preparedMellinScalar
  rw [mul_inv_rev, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have he : -(((((p.1 : ℤ) - 4 : ℤ) : ℝ)) / 3) =
      (4 / 3 : ℝ) + (-(p.1 : ℝ) / 3) := by push_cast; ring
  rw [he, Real.rpow_add (by norm_num)]
  ring

theorem prepared_mellin_scalar_pos (p : PreparedBlockIndex) {b : Ideal O}
    (hb : 0 < normIdeal b) : 0 < preparedMellinScalar p b := by
  unfold preparedMellinScalar
  positivity

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VPreparedFiniteColumns; SHA256 32e9efc9dbfcf33290ea79a3a3292b3ccab0aecbb662d68b1dc7d8d0b772e639 -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly

/-- This finite mask depends on the original tuples and column, never on a row. -/
def preparedFiniteColumnIdeals (t : Finset (ℕ × Ideal O × Ideal O))
    (p : PreparedBlockIndex) (b : Ideal O) : Finset (Ideal O) :=
  ((preparedColumnTuples t p).filter (fun q => q.2.2 = b)).image (fun q => q.2.1)

def preparedFiniteGoodColumn (t : Finset (ℕ × Ideal O × Ideal O))
    (p : PreparedBlockIndex) (b : Ideal O) : Finset (Ideal O) :=
  (preparedFiniteColumnIdeals t p b).filter
    (fun n => n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3))

private theorem prepared_column_tuple_shape
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex}
    {q : ℕ × Ideal O × Ideal O} {b : Ideal O}
    (hq : q ∈ preparedColumnTuples t p) (hb : q.2.2 = b) :
    q = (p.1, q.2.1, b) := by
  have hp := (Finset.mem_filter.mp hq).2.1
  have hr : q.1 = p.1 := by
    simpa only [preparedBlockIndex] using congrArg (fun a : PreparedBlockIndex => a.1) hp
  exact Prod.ext hr (Prod.ext rfl hb)

theorem preparedThetaColumn_eq_finite_sum (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (b k : Ideal O) :
    preparedThetaColumn W H Y A coeff t p b k =
      ∑ n ∈ preparedFiniteColumnIdeals t p b,
        preparedThetaTerm W H Y A coeff k (p.1, n, b) := by
  unfold preparedThetaColumn preparedFiniteColumnIdeals
  apply Finset.sum_bij (fun q _ => q.2.1)
  · intro q hq
    exact Finset.mem_image_of_mem _ hq
  · intro q hq q' hq' hn
    have hqShape := prepared_column_tuple_shape (Finset.mem_filter.mp hq).1
      (Finset.mem_filter.mp hq).2
    have hq'Shape := prepared_column_tuple_shape (Finset.mem_filter.mp hq').1
      (Finset.mem_filter.mp hq').2
    calc
      q = (p.1, q.2.1, b) := hqShape
      _ = (p.1, q'.2.1, b) := by rw [hn]
      _ = q' := hq'Shape.symm
  · intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨q, hq, rfl⟩
  · intro q hq
    congr 1
    exact prepared_column_tuple_shape (Finset.mem_filter.mp hq).1
      (Finset.mem_filter.mp hq).2

theorem preparedThetaTerm_eq_zero_of_bad_n (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (r : ℕ) (n b k : Ideal O)
    (hn : ¬(n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3))) :
    preparedThetaTerm W H Y A coeff k (r,n,b) = 0 := by
  unfold preparedThetaTerm
  dsimp only
  split_ifs with hh
  · exact (hn ⟨hh.1, hh.2.1, hh.2.2.1⟩).elim
  · rfl

theorem preparedThetaTerm_eq_zero_of_bad_b (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (r : ℕ) (n b k : Ideal O)
    (hb : ¬(b ≠ ⊥ ∧ IsRelPrime b (principal 3))) :
    preparedThetaTerm W H Y A coeff k (r,n,b) = 0 := by
  unfold preparedThetaTerm
  dsimp only
  split_ifs with hh
  · exact (hb ⟨hh.2.2.2.1, hh.2.2.2.2⟩).elim
  · rfl

theorem preparedThetaColumn_eq_good_sum (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (b k : Ideal O) :
    preparedThetaColumn W H Y A coeff t p b k =
      ∑ n ∈ preparedFiniteGoodColumn t p b,
        preparedThetaTerm W H Y A coeff k (p.1,n,b) := by
  rw [preparedThetaColumn_eq_finite_sum]
  unfold preparedFiniteGoodColumn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hg : n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3)
  · exact (if_pos hg).symm
  · rw [if_neg hg, preparedThetaTerm_eq_zero_of_bad_n W H Y A coeff p.1 n b k hg]

theorem preparedThetaColumn_eq_zero_of_bad_b (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex) (b k : Ideal O)
    (hb : ¬(b ≠ ⊥ ∧ IsRelPrime b (principal 3))) :
    preparedThetaColumn W H Y A coeff t p b k = 0 := by
  rw [preparedThetaColumn_eq_good_sum]
  exact Finset.sum_eq_zero (fun n _ => preparedThetaTerm_eq_zero_of_bad_b W H Y A coeff p.1 n b k hb)

theorem preparedFiniteGoodColumn_spec
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex} {b n : Ideal O}
    (hn : n ∈ preparedFiniteGoodColumn t p b) :
    (n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3)) ∧
      preparedBlockIndex (p.1,n,b) = p ∧ (p.1,n,b) ∈ t := by
  obtain ⟨hn, hgood⟩ := Finset.mem_filter.mp hn
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hn
  rcases q with ⟨r,n',b'⟩
  change n' = n at heq
  subst n'
  obtain ⟨hq, hb⟩ := Finset.mem_filter.mp hq
  change b' = b at hb
  subst b'
  obtain ⟨hqt, hp, hb0⟩ := Finset.mem_filter.mp hq
  have hr := congrArg (fun a : PreparedBlockIndex => a.1) hp
  change r = p.1 at hr
  subst r
  exact ⟨hgood, hp, hqt⟩

theorem preparedFiniteGoodColumn_norm_range
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex} {b n : Ideal O}
    (hn : n ∈ preparedFiniteGoodColumn t p b) :
    (2 : ℝ)^p.2.1 ≤ normIdeal n ∧ normIdeal n ≤ 2*(2 : ℝ)^p.2.1 := by
  obtain ⟨hgood, hp, _⟩ := preparedFiniteGoodColumn_spec hn
  have he := congrArg (fun a : PreparedBlockIndex => a.2.1) hp
  change Nat.log 2 n.absNorm = p.2.1 at he
  obtain ⟨hlo,hhi⟩ := normIdeal_dyadic_range n hgood.1
  rw [he] at hlo hhi
  exact ⟨hlo,hhi.le⟩

/-- The fixed column phase and row coefficient are outside the good-n sum.
There is no assumption on the finite mask or on the scales in this identity. -/
theorem preparedThetaColumn_eq_factored_sum (W : ℝ → ℂ) (H Y : ℝ)
    (A : ℕ → Ideal O → Ideal O → ℂ) (coeff : ℕ → Ideal O → ℂ)
    (t : Finset (ℕ × Ideal O × Ideal O)) (p : PreparedBlockIndex)
    {S : Finset (Ideal O)} {b k : Ideal O}
    (hb : b ≠ ⊥ ∧ IsRelPrime b (principal 3)) (hk : k ∈ sieveRows S H) :
    preparedThetaColumn W H Y A coeff t p b k =
      (coeff p.1 k * sexticSymbol k (primaryGenerator b)^3 /
        (((3 : ℝ)^((((p.1 : ℤ)-4 : ℤ) : ℝ)/3)*normIdeal b : ℝ) : ℂ)) *
      ∑ n ∈ preparedFiniteGoodColumn t p b,
        (A p.1 n b * sexticSymbol k (primaryGenerator n)^3 /
          (Real.sqrt (normIdeal n) : ℂ)) *
        thetaWeight (fun x => (Real.sqrt x : ℂ)*W x)
          ((3 : ℝ)^(((p.1 : ℤ)-4 : ℤ) : ℝ)*normIdeal n*normIdeal b^3*H^2 /
            (Y*normIdeal k^2)) := by
  rw [preparedThetaColumn_eq_good_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hg := (preparedFiniteGoodColumn_spec hn).1
  unfold preparedThetaTerm
  dsimp only
  rw [if_pos ⟨hg.1, hg.2.1, hg.2.2, hb.1, hb.2⟩,
    (prepared_row_cubic_symbol_factor hk n b).1]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VPreparedZeroMellinData; SHA256 f1f1962f545f37c078db43818ec88d1a0556105124c68395ca83f1a68de18426 -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace QRHShort.SquarefreeAssembly

/-- A zero column has genuine zero Mellin data, independently of a and
including a bottom auxiliary ideal. -/
theorem realMellinData_nonempty_of_column_zero
    {J : ℕ} {C : ℝ} {S : Finset (Ideal O)} {W : ℝ → ℂ} {H Y a : ℝ}
    {A : ℕ → Ideal O → Ideal O → ℂ} {coeff : ℕ → Ideal O → ℂ}
    {t : Finset (ℕ × Ideal O × Ideal O)} {p : PreparedBlockIndex} {b : Ideal O}
    (hC : 0 ≤ C) (hY : 0 < Y)
    (hzero : ∀ k ∈ sieveRows S H, preparedThetaColumn W H Y A coeff t p b k = 0) :
    Nonempty (RealMellinData J C S W H Y a A coeff t p b) := by
  have hz : 0 < 1 + preparedBlockScale Y p := by
    have := preparedBlockScale_pos hY p
    linarith
  have hNb : 0 ≤ normIdeal b := Nat.cast_nonneg _
  refine ⟨{
    columns := ∅
    envelope := fun _ => 0
    coefficient := fun _ _ => 0
    beta := fun _ _ => 0
    admissible := by simp
    envelope_nonneg := by simp
    envelope_integrable := integrable_zero _ _ _
    coefficient_measurable := by intro k hk; exact measurable_const
    beta_measurable := by simp
    coefficient_bound := by simp
    beta_bound := by simp
    mass_bound := ?_
    column_eq := ?_ }⟩
  · simp only [integral_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hC (abs_nonneg _)) (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg hz.le _))
      (inv_nonneg.mpr hNb)
  · intro k hk
    rw [hzero k hk]
    simp

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VPreparedClosure; SHA256 0e18ff21068590e68984cf9ff87e25318374355de0d4d2529f7210a87b393cb7 -/

noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort.SquarefreeAssembly

/-- The concrete theta Mellin integral provides the common envelope. Its
two contour bounds use the single derivative order 18 before S and I. -/
theorem prepared_theta_real_mellin_estimate_proved : PreparedThetaRealMellinEstimate := by
  intro σ hσ hσcap
  refine ⟨18, by decide, ?_⟩
  intro S I
  obtain ⟨C, hC, hkernel⟩ := prepared_mellin_two_contours I
  have hCfinal : 0 ≤ 8 * (3 : ℝ) ^ (4 / 3 : ℝ) * C := by positivity
  refine ⟨8 * (3 : ℝ) ^ (4 / 3 : ℝ) * C, hCfinal, ?_⟩
  intro W H Y a A coeff hW hH hY ha hA hcoeff t p b hb
  by_cases hbg : b ≠ ⊥ ∧ IsRelPrime b (principal 3)
  · let q : Ideal O → ℂ := fun k => coeff p.1 k * sexticSymbol k (primaryGenerator b) ^ 3
    have hq (k : Ideal O) (hk : k ∈ sieveRows S H) : ‖q k‖ ≤ 1 := by
      dsimp [q]
      rw [norm_mul]
      exact (mul_le_mul (hcoeff p.1 k hk) (prepared_row_cubic_symbol_factor hk 1 b).2
        (norm_nonneg _) zero_le_one).trans (by norm_num)
    have hcols (n : Ideal O) (hn : n ∈ preparedFiniteGoodColumn t p b) :
        n ≠ ⊥ ∧ Squarefree n ∧ IsRelPrime n (principal 3) ∧
          (2 : ℝ) ^ p.2.1 ≤ normIdeal n ∧ normIdeal n ≤ 2 * (2 : ℝ) ^ p.2.1 := by
      have hg := (preparedFiniteGoodColumn_spec hn).1
      have hr := preparedFiniteGoodColumn_norm_range hn
      exact ⟨hg.1, hg.2.1, hg.2.2, hr.1, hr.2⟩
    have hbpos : 0 < normIdeal b :=
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ p.2.2).trans_le
        (preparedColumnIdeals_norm_range hb).2.1
    have hcolumn (k : Ideal O) (hk : k ∈ sieveRows S H) :
        preparedThetaColumn W H Y A coeff t p b k =
          (preparedMellinScalar p b : ℂ) * q k *
            ∑ n ∈ preparedFiniteGoodColumn t p b,
              (A p.1 n b / (Real.sqrt (normIdeal n) : ℂ) *
                sexticSymbol k (primaryGenerator n) ^ (3 : ℕ)) *
              thetaWeight (fun y => (Real.sqrt y : ℂ) * W y)
                (preparedMellinBase Y p b * (normIdeal n / (2 : ℝ) ^ p.2.1) /
                  preparedMellinRow H k ^ 2) := by
      rw [preparedThetaColumn_eq_factored_sum W H Y A coeff t p hbg hk]
      have hfront :
          coeff p.1 k * sexticSymbol k (primaryGenerator b) ^ 3 /
            (((3 : ℝ) ^ (((((p.1 : ℤ) - 4 : ℤ) : ℝ)) / 3) * normIdeal b : ℝ) : ℂ) =
            (preparedMellinScalar p b : ℂ) * q k := by
        dsimp [preparedMellinScalar, q]
        push_cast
        ring
      rw [hfront]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      have hk0 := ((mem_sieveRows S H k).mp hk).1.1.1
      rw [prepared_mellin_theta_argument (zero_lt_one.trans_le hH) hY p b n hk0]
      ring
    exact prepared_real_mellin_data_from_column hW hC (hkernel W hW)
      S H Y a hY ha A coeff hA t p b (preparedFiniteGoodColumn t p b) hcols
      (preparedMellinBase Y p b) (preparedMellinScalar p b)
      (prepared_mellin_base_range hY hb).1 (prepared_mellin_scalar_pos p hbpos).le
      (prepared_mellin_scalar_eq p b) (preparedMellinRow H)
      (fun k hk => prepared_mellin_row_range hH hk) q hq hcolumn
  · exact realMellinData_nonempty_of_column_zero hCfinal hY
      (fun k _ => preparedThetaColumn_eq_zero_of_bad_b W H Y A coeff t p b k hbg)

theorem prepared_theta_real_mellin_step_proved : PreparedThetaRealMellinStep := by
  intro _ _
  exact prepared_theta_real_mellin_estimate_proved

theorem prepared_theta_dyadic_raw_step_proved : PreparedThetaDyadicRawStep := by
  intro ht hq hs hr
  exact prepared_theta_raw_of_real_mellin (prepared_theta_real_mellin_step_proved ht hs) hq hr

theorem prepared_theta_dyadic_step_proved : PreparedThetaDyadicStep :=
  prepared_theta_dyadic_step_of_raw prepared_theta_dyadic_raw_step_proved

theorem prepared_theta_truncation_step_proved : PreparedThetaTruncationStep :=
  prepared_theta_truncation_step_of_raw prepared_theta_dyadic_raw_step_proved

theorem prepared_theta_estimate_step_proved : PreparedThetaEstimateStep :=
  prepared_theta_step_of_raw prepared_theta_dyadic_raw_step_proved

end QRHShort.SquarefreeAssembly

end
end

section
/- Source fragment: VSquarefreeComplete; SHA256 ca1b7d2e673d84a8c39f9dbd1912c1c9bef77381d5321f97f2f437405226f4d4 -/

namespace QRHShort.SquarefreeAssembly

/-- The original reflection child, from the proved finite raw and dual packets. -/
theorem squarefree_reflection_step_proved : SquarefreeReflectionStep :=
  squarefree_reflection_step_of_packets
    PacketConstruction.squarefree_reflection_packet_step_proved

end QRHShort.SquarefreeAssembly

namespace QRHShort.CloudBatch

/-- The frozen V endpoint with its original six upstream premises. -/
theorem squarefree_completed_step_proved (hr : ReflectionStatement)
    (hu : ReflectionUniformityStatement) (hb : ThetaBoundsStatement)
    (hq : QuadraticEstimate) (hs : SmoothSeparationStatement)
    (hc : RecombinationStatement) : SquarefreeCompletedEstimate := by
  exact SquarefreeAssembly.squarefree_completed_uniformize
    (SquarefreeAssembly.squarefree_reflection_step_proved hr hu hb
      (SquarefreeAssembly.prepared_theta_estimate_step_proved hb hq hs hc))

end QRHShort.CloudBatch

end

