import QRHShort.Estimates
import QRHShort.PoissonStatements
import QRHShort.SmoothingStatements
import QRHShort.WeightNorm
import QRHShort.FiniteSupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
Poisson reduction, paper2.tex:1000–1247. The two remaining inputs are the
arithmetic dyadic expansion and the coupled-kernel block estimate. Neither
input is asserted here. In particular the original manuscript endpoint remains
unfinished. Scales, context transport, logarithmic losses and final assembly
are proved below, without calling any unfinished manuscript theorem.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.PoissonReductionProof

/-- The transformed weight in the initial paired Gauss expansion. -/
def initialWeight (W : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt x : ℂ)⁻¹ * star (W x)

/-- The literal two-variable kernel in paper2.tex:1190–1201. -/
def initialKernel (Φ : RowWeight) (W : ℝ → ℂ) (r a : ℝ)
    (x : BoxSpace 2) : ℂ :=
  initialWeight W (r * x 0) * star (initialWeight W (r * x 1)) *
    radialFourier (fun t => (Φ.value t : ℂ)) (a / (x 0 * x 1))

def initialKernelInterval (I : SupportInterval) : SupportInterval where
  lo := I.lo / 4
  hi := I.hi
  lo_pos := div_pos I.lo_pos (by norm_num)
  ordered := by nlinarith [I.lo_pos, I.ordered]

def initialTestInterval (I : SupportInterval) : SupportInterval where
  lo := I.lo / 8
  hi := 2 * I.hi
  lo_pos := div_pos I.lo_pos (by norm_num)
  ordered := by nlinarith [I.lo_pos, I.ordered]

def initialGap (I : SupportInterval) (Φ : RowWeight) : ℝ :=
  max 2 (Φ.fourierCap * I.hi ^ (2 : ℕ))

def initialHeight (I : SupportInterval) (Φ : RowWeight) (D H B : ℝ) : ℝ :=
  initialGap I Φ * D ^ (2 : ℕ) / (H * B ^ (2 : ℕ))

/-- The column coefficient before insertion of a common test function. -/
def initialAtom (c : ArithmeticContext) (ξ : RayCharacter c)
    (b f : Ideal O) (k : O) (n : Ideal O) : ℂ :=
  if SquarefreeOutside c.S n ∧ IsRelPrime n b then
    coefficient ξ.val n * sexticSymbol n k *
      sexticSymbol n (primaryGenerator f) ^ (4 : ℕ)
  else 0

/-- The paired coefficient and coupled kernel before either ideal sum. -/
def initialPairedTerm (c : ArithmeticContext) (ξ : RayCharacter c)
    (Φ : RowWeight) (W : ℝ → ℂ) (D H B F : ℝ)
    (b f : Ideal O) (k : O) (n : Ideal O × Ideal O) : ℂ :=
  let X := D / (B * F)
  initialAtom c ξ b f k n.1 * star (initialAtom c ξ b f k n.2) *
    initialKernel Φ W (normIdeal b * normIdeal f / (B * F))
      (H * normElement k / (normIdeal f ^ (2 : ℕ) * X ^ (2 : ℕ)))
      ![normIdeal n.1 / X, normIdeal n.2 / X]

/-- Explicit convergence obligation: compact support makes the paired ideal
sum finite. The b,f bands and k ball in the outer sums are already bounded. -/
def InitialPairFiniteSupport (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) : Prop :=
  ∀ (ξ : RayCharacter c) (W : ℝ → ℂ) (D H B F : ℝ)
    (b f : Ideal O) (k : O), SmoothSupported I W → 0 < D →
    1 ≤ B → 1 ≤ F → b ≠ ⊥ → f ≠ ⊥ →
    Function.HasFiniteSupport (initialPairedTerm c ξ Φ W D H B F b f k)

/-- Equation (initial-column-output) restricted to the dyadic b,f bands.
All four inner sums are the actual arithmetic sums, rather than scalar bounds.
Their support/convergence and the change of variables belong to the two inputs.
-/
def initialDyadicBlock (c : ArithmeticContext) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) (W : ℝ → ℂ)
    (D H B F : ℝ) : ℂ :=
  ((H / D ^ (2 : ℕ) : ℝ) : ℂ) *
    ∑' b : Ideal O, if SquarefreeOutside c.S b ∧ B ≤ normIdeal b ∧
        normIdeal b < 2 * B then
      (normIdeal b : ℂ) * ∑' f : Ideal O,
        if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧
            normIdeal f < 2 * F ∧ IsRelPrime b f then
          (mobius f : ℂ) * ∑' k : O,
            if 0 < normElement k ∧ normElement k ≤ initialHeight I Φ D H B then
              ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
                initialPairedTerm c ξ Φ W D H B F b f k (n₁, n₂)
            else 0
        else 0
    else 0

/-- One extra band includes an endpoint which is itself an exact power of two. -/
def initialDepth (I : SupportInterval) (D : ℝ) : ℕ :=
  ⌈Real.log (max 1 (I.hi * D)) / Real.log 2⌉₊ + 1

/-- The precise initial-energy bound, with its constant fixed before the scales. -/
def InitialBound (c : ArithmeticContext) (I : SupportInterval)
    (θ C δ : ℝ) (J : ℕ) (K : ℝ) : Prop :=
  ∀ (ξ : RayCharacter c) (U : ℝ → ℂ) (D B F H : ℝ),
    SmoothSupported I U → 2 ≤ D → 1 ≤ B → 1 ≤ F → 0 < H →
    H ≤ C * D ^ (2 : ℕ) / (D ^ (1 + θ) * B ^ (2 : ℕ)) →
    energy c ξ U H (D / (B * F)) F ≤
      K * weightNorm J U ^ 2 * D ^ δ * (D / B)

/-- Child 1: first Poisson, paired Gauss factors, coprimality inversion and the
bijective (g,e,v,h) ↔ (b,f,k) change of variables. The finite ray-character set
and both constants are fixed before W,D,H. This includes the zero-frequency
bound and the sharp-to-Schwartz comparison. -/
def PoissonDyadicExpansionInput : Prop :=
  PoissonStatement → PoissonZeroStatement →
  ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
    ∃ (Φ : RowWeight) (Ξ : Finset (RayCharacter c)) (A Z : ℝ),
      0 ≤ A ∧ 0 ≤ Z ∧ ∀ (W : ℝ → ℂ) (D H : ℝ),
        SmoothSupported I W → 2 ≤ D → 0 < H →
        originalMeanSquare c W D H ≤
          D * (Z * weightNorm 0 W ^ 2 * H + A *
            ∑ ξ ∈ Ξ, ∑ j ∈ Finset.range (initialDepth I D),
              ∑ l ∈ Finset.range (initialDepth I D),
                ‖initialDyadicBlock c ξ I Φ W D H ((2 : ℝ) ^ j) ((2 : ℝ) ^ l)‖)

/-- Child 2: removal of exclusions and the finite-test smoothing principle,
including the kernel derivative bound, the ideal/divisor counts, and convergence
of the displayed arithmetic sums. The factor D^(2δ) reserves δ for divisor
losses, while the initial bound itself has exponent δ. -/
def PoissonDyadicBlockInput : Prop :=
  RemoveExclusionsStatement → SmoothMeanSquareStatement →
  ∀ (θ δ : ℝ) (J : ℕ), 0 < θ → θ ≤ (1 : ℝ) / 10 → 0 < δ → 1 ≤ J →
  ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight),
    ArithmeticRelations c → ∀ K : ℝ, 0 ≤ K →
    InitialBound c (initialTestInterval I) θ (initialGap I Φ) δ J K →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ) (D B F : ℝ),
      SmoothSupported I W → 2 ≤ D → 1 ≤ B → 1 ≤ F →
      ‖initialDyadicBlock c ξ I Φ W D (D ^ (1 + θ)) B F‖ ≤
        L * weightNorm (2 * J + 4) W ^ 2 * D ^ (2 * δ) * D ^ (1 + θ)

theorem initial_intervals_nested (I : SupportInterval) :
    (initialTestInterval I).lo < (initialKernelInterval I).lo ∧
      (initialKernelInterval I).hi < (initialTestInterval I).hi := by
  dsimp [initialTestInterval, initialKernelInterval]
  constructor <;> nlinarith [I.lo_pos, I.ordered]

theorem initialGap_one_le (I : SupportInterval) (Φ : RowWeight) :
    1 ≤ initialGap I Φ := by
  exact (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)

theorem initial_scale_product {D B F : ℝ} (hF : F ≠ 0) :
    D / (B * F) * F = D / B := by
  calc
    _ = (D / B) * (F⁻¹ * F) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [inv_mul_cancel₀ hF, mul_one]

theorem initial_scale_shift {D B F t : ℝ} :
    (D / (B * F)) / t = D / (B * (F * t)) := by
  simp only [div_div, mul_assoc]

theorem initial_shift_F_one_le {F t : ℝ} (hF : 1 ≤ F) (ht : 1 ≤ t) :
    1 ≤ F * t := one_le_mul_of_one_le_of_one_le hF ht

theorem initial_scale_shift_product {D B F t : ℝ} (hF : F ≠ 0) (ht : t ≠ 0) :
    ((D / (B * F)) / t) * (F * t) = D / B := by
  rw [initial_scale_shift]
  exact initial_scale_product (mul_ne_zero hF ht)

/-- Every nonzero integral ideal has norm at least one. -/
theorem normIdeal_one_le {d : Ideal O} (hd : d ≠ ⊥) : 1 ≤ normIdeal d := by
  have hn : d.absNorm ≠ 0 := fun h => hd (Ideal.absNorm_eq_zero_iff.mp h)
  change (1 : ℝ) ≤ (d.absNorm : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

/-- Both columns in the coupled kernel are compactly supported, uniformly in
all of the Fourier parameters. This proves convergence independently of either
remaining estimate. -/
theorem initial_pair_finiteSupport (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) : InitialPairFiniteSupport c I Φ := by
  intro ξ W D H B F b f k hW hD hB hF hb hf
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hb0 : 0 < normIdeal b := zero_lt_one.trans_le (normIdeal_one_le hb)
  have hf0 : 0 < normIdeal f := zero_lt_one.trans_le (normIdeal_one_le hf)
  have hbf0 : 0 < normIdeal b * normIdeal f := mul_pos hb0 hf0
  let X := D / (B * F)
  let r := normIdeal b * normIdeal f / (B * F)
  let T := I.hi * D / (normIdeal b * normIdeal f)
  have harg (t : ℝ) : r * (t / X) = (normIdeal b * normIdeal f * t) / D := by
    dsimp [r, X]
    field_simp [hD.ne', hB0.ne', hF0.ne']
    <;> ring
  apply ((finite_normIdeal_le T).prod (finite_normIdeal_le T)).subset
  intro n hn
  have hterm : initialPairedTerm c ξ Φ W D H B F b f k n ≠ 0 := hn
  have hw₁ : W (r * (normIdeal n.1 / X)) ≠ 0 := by
    intro hz
    apply hterm
    simp only [initialPairedTerm, initialKernel, initialWeight,
      show W ((normIdeal b * normIdeal f / (B * F)) *
        (normIdeal n.1 / (D / (B * F)))) = 0 from hz,
      Matrix.cons_val_zero, star_zero, mul_zero, zero_mul]
  have hw₂ : W (r * (normIdeal n.2 / X)) ≠ 0 := by
    intro hz
    apply hterm
    simp only [initialPairedTerm, initialKernel, initialWeight,
      show W ((normIdeal b * normIdeal f / (B * F)) *
        (normIdeal n.2 / (D / (B * F)))) = 0 from hz,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_zero, mul_zero, zero_mul]
  have hbound (a : Ideal O) (hw : W (r * (normIdeal a / X)) ≠ 0) :
      normIdeal a ≤ T := by
    have hu := (hW.2 hw).2
    rw [harg] at hu
    apply (le_div_iff₀ hbf0).mpr
    calc
      normIdeal a * (normIdeal b * normIdeal f) =
          normIdeal b * normIdeal f * normIdeal a := by ring
      _ ≤ I.hi * D := (div_le_iff₀ hD).mp hu
  exact ⟨hbound n.1 hw₁, hbound n.2 hw₂⟩

/-- The exclusion shifts preserve the complete initial-energy range, including
its normalization. The new F is allowed to be arbitrarily large. -/
theorem initial_bound_shift (c : ArithmeticContext) (I : SupportInterval)
    {θ C δ K : ℝ} {J : ℕ} (hi : InitialBound c I θ C δ J K)
    (ξ : RayCharacter c) (U : ℝ → ℂ) (D B F H : ℝ) (t : ℝ)
    (hU : SmoothSupported I U) (hD : 2 ≤ D) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hH : 0 < H) (hgap : H ≤ C * D ^ (2 : ℕ) / (D ^ (1 + θ) * B ^ (2 : ℕ)))
    (ht : 1 ≤ t) :
    energy c ξ U H ((D / (B * F)) / t) (F * t) ≤
      K * weightNorm J U ^ 2 * D ^ δ * (D / B) := by
  rw [initial_scale_shift]
  exact hi ξ U D B (F * t) H hU hD hB
    (initial_shift_F_one_le hF ht) hH hgap

/-- The radical is nonzero even when the original ideal is zero: its prime
factorization is a finite product of nonzero prime ideals. -/
theorem radical_ne_bot (S : Finset (Ideal O)) (r : Ideal O) :
    outsideRadical S r ≠ ⊥ := by
  change (∏ P ∈ (primeFactors r).filter (fun P => P ∉ S), P) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero

theorem finite_radical_divisors (S : Finset (Ideal O)) (r : Ideal O) :
    {d : Ideal O | d ∣ outsideRadical S r}.Finite := by
  apply (finite_normIdeal_le (normIdeal (outsideRadical S r))).subset
  intro d hd
  have hn : (outsideRadical S r).absNorm ≠ 0 :=
    fun h => radical_ne_bot S r (Ideal.absNorm_eq_zero_iff.mp h)
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (map_dvd Ideal.absNorm hd)
  change (d.absNorm : ℝ) ≤ ((outsideRadical S r).absNorm : ℝ)
  exact_mod_cast hle

/-- The exact divisor-square loss before absorbing it into a small power of D.
This is the invocation of remove-exclusions in paper2.tex:1204–1216. -/
theorem excluded_initial_bound (he : RemoveExclusionsStatement)
    (c : ArithmeticContext) (I : SupportInterval) (hc : ArithmeticRelations c)
    {θ C δ K : ℝ} {J : ℕ} (hi : InitialBound c I θ C δ J K)
    (ξ : RayCharacter c) (U : ℝ → ℂ) (D B F H : ℝ) (r : Ideal O)
    (hr : r ≠ ⊥) (hU : SmoothSupported I U) (hD : 2 ≤ D)
    (hB : 1 ≤ B) (hF : 1 ≤ F) (hH : 0 < H)
    (hgap : H ≤ C * D ^ (2 : ℕ) / (D ^ (1 + θ) * B ^ (2 : ℕ))) :
    excludedEnergy c ξ U r H (D / (B * F)) F ≤
      (divisorCount (outsideRadical c.S r) : ℝ) ^ 2 *
        (K * weightNorm J U ^ 2 * D ^ δ * (D / B)) := by
  let s : Finset (Ideal O) := (finite_radical_divisors c.S r).toFinset
  have hs (d : Ideal O) : d ∈ s ↔ d ∣ outsideRadical c.S r := by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hcard : s.card = divisorCount (outsideRadical c.S r) := by
    letI := Fintype.subtype s hs
    rw [divisorCount, Nat.card_eq_fintype_card, Fintype.card_of_subtype s hs]
  have hx : 0 < D / (B * F) := div_pos (by linarith)
    (mul_pos (zero_lt_one.trans_le hB) (zero_lt_one.trans_le hF))
  have hrem := he c hc I ξ U r H (D / (B * F)) F hr hU hH hx hF
  have hsum : (∑' d : Ideal O, if d ∣ outsideRadical c.S r then
        energy c ξ U H ((D / (B * F)) / normIdeal d) (F * normIdeal d) else 0) ≤
      (divisorCount (outsideRadical c.S r) : ℝ) *
        (K * weightNorm J U ^ 2 * D ^ δ * (D / B)) := by
    rw [tsum_eq_sum (s := s) (fun d hd =>
      if_neg (fun h => hd ((hs d).mpr h)))]
    calc
      _ ≤ ∑ _d ∈ s, K * weightNorm J U ^ 2 * D ^ δ * (D / B) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [if_pos ((hs d).mp hd)]
        exact initial_bound_shift c I hi ξ U D B F H (normIdeal d)
          hU hD hB hF hH hgap (normIdeal_one_le
            (ne_zero_of_dvd_ne_zero (radical_ne_bot c.S r) ((hs d).mp hd)))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  calc
    _ ≤ (divisorCount (outsideRadical c.S r) : ℝ) *
        ((divisorCount (outsideRadical c.S r) : ℝ) *
          (K * weightNorm J U ^ 2 * D ^ δ * (D / B))) :=
      hrem.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
    _ = _ := by ring

/-- Undoing energy normalization gives the common-test square bound used by
the coupled-kernel smoothing step, with the preserved product D/B squared. -/
theorem excluded_initial_rows_bound (he : RemoveExclusionsStatement)
    (c : ArithmeticContext) (I : SupportInterval) (hc : ArithmeticRelations c)
    {θ C δ K : ℝ} {J : ℕ} (hi : InitialBound c I θ C δ J K)
    (ξ : RayCharacter c) (U : ℝ → ℂ) (D B F H : ℝ) (r : Ideal O)
    (hr : r ≠ ⊥) (hU : SmoothSupported I U) (hD : 2 ≤ D)
    (hB : 1 ≤ B) (hF : 1 ≤ F) (hH : 0 < H)
    (hgap : H ≤ C * D ^ (2 : ℕ) / (D ^ (1 + θ) * B ^ (2 : ℕ))) :
    (∑' f : Ideal O, if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧
        normIdeal f < 2 * F then
      rowEnergy (fun k => excludedColumnSum c ξ U r (D / (B * F)) k f) H else 0) ≤
      (divisorCount (outsideRadical c.S r) : ℝ) ^ 2 *
        K * weightNorm J U ^ 2 * D ^ δ * (D / B) ^ 2 := by
  have h := excluded_initial_bound he c I hc hi ξ U D B F H r hr hU hD hB hF hH hgap
  unfold excludedEnergy at h
  rw [initial_scale_product (ne_of_gt (zero_lt_one.trans_le hF))] at h
  have hσ : 0 < D / B := div_pos (by linarith) (zero_lt_one.trans_le hB)
  have hm := mul_le_mul_of_nonneg_left h hσ.le
  rw [← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul] at hm
  convert hm using 1 <;> ring

/-- In the diagonal application the square root of M*M is exactly M. -/
theorem diagonal_smoothing (hs : SmoothMeanSquareStatement)
    (I Istar : SupportInterval) (m : ℕ)
    (hlo : Istar.lo < I.lo) (hhi : I.hi < Istar.hi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R N : ℕ) (a : Fin R → Fin N → ℂ)
      (x : Fin R → Fin N → ℝ) (w : Fin R → ℝ) (coeff : Fin R → ℂ)
      (M : ℝ) (K : Fin R → BoxSpace 2 → ℂ),
      (∀ r n, 0 < x r n) → (∀ r, 0 ≤ w r) →
      (∀ r, ‖coeff r‖ ≤ w r) → 0 ≤ M →
      (∀ U : ℝ → ℂ, SmoothSupported Istar U →
        (∑ r : Fin R, w r * ‖finiteTestSum a x r U‖ ^ 2) ≤ M * weightNorm m U ^ 2) →
      (∀ r, SmoothBox (fun _ : Fin 2 => I) (K r)) →
      ‖∑ r : Fin R, coeff r * ∑ n₁ : Fin N, ∑ n₂ : Fin N,
        a r n₁ * star (a r n₂) * K r ![x r n₁, x r n₂]‖ ≤
        C * M * QRHLean3.supZero
          {v | ∃ r : Fin R, v = multiWeightNorm (2 * m + 4) (K r)} := by
  obtain ⟨C, hC, hh⟩ := hs I Istar m hlo hhi
  refine ⟨C, hC, ?_⟩
  intro R N a x w coeff M K hx hw hcoeff hM hcommon hkernel
  have h := hh R N N a a x x w coeff M M K hx hx hw hcoeff hM hM
    hcommon hcommon hkernel
  simpa only [Real.sqrt_mul_self hM] using h

theorem originalSum_context_eq (c c' : ArithmeticContext)
    (hν : c.nu = c'.nu) (hS : c.S = c'.S) (W : ℝ → ℂ) (D : ℝ) (u : O) :
    originalSum c W D u = originalSum c' W D u := by
  simp only [originalSum, hν, hS]

theorem originalMeanSquare_context_eq (c c' : ArithmeticContext)
    (hν : c.nu = c'.nu) (hS : c.S = c'.S) (W : ℝ → ℂ) (D H : ℝ) :
    originalMeanSquare c W D H = originalMeanSquare c' W D H := by
  simp only [originalMeanSquare, originalSum_context_eq c c' hν hS]

/-- The logarithmic number of dyadic pairs costs arbitrarily little power of D.
No arithmetic input is needed for this estimate. -/
theorem initialDepth_sq_bound (I : SupportInterval) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D : ℝ, 2 ≤ D →
      (initialDepth I D : ℝ) ^ (2 : ℕ) ≤ K * D ^ δ := by
  let a : ℝ := max 1 I.hi
  let η : ℝ := δ / 2
  let C : ℝ := a ^ η / (η * Real.log 2) + 2
  have ha : 1 ≤ a := le_max_left _ _
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hη : 0 < η := div_pos hδ (by norm_num)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C ^ (2 : ℕ), sq_nonneg _, ?_⟩
  intro D hD
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hpow : 1 ≤ D ^ η := Real.one_le_rpow hD1 hη.le
  have hx : 1 ≤ max 1 (I.hi * D) := le_max_left _ _
  have hx0 : 0 < max 1 (I.hi * D) := zero_lt_one.trans_le hx
  have hxupper : max 1 (I.hi * D) ≤ a * D := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le ha hD1
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hD0.le
  have hlogupper : Real.log (max 1 (I.hi * D)) ≤
      a ^ η * D ^ η / η := by
    calc
      _ ≤ (max 1 (I.hi * D)) ^ η / η := Real.log_le_rpow_div hx0.le hη
      _ ≤ (a * D) ^ η / η :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow hx0.le hxupper hη.le) hη.le
      _ = _ := by rw [Real.mul_rpow ha0.le hD0.le]
  have hquot : 0 ≤ Real.log (max 1 (I.hi * D)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hx) hlog.le
  have hdepth : (initialDepth I D : ℝ) ≤ C * D ^ η := by
    have hc := (Nat.ceil_lt_add_one hquot).le
    have hdiv := div_le_div_of_nonneg_right hlogupper hlog.le
    have heq : a ^ η * D ^ η / η / Real.log 2 =
        (a ^ η / (η * Real.log 2)) * D ^ η := by ring
    dsimp [initialDepth]
    push_cast
    dsimp [C]
    rw [heq] at hdiv
    nlinarith
  calc
    _ ≤ (C * D ^ η) ^ (2 : ℕ) := pow_le_pow_left₀ (Nat.cast_nonneg _) hdepth _
    _ = C ^ (2 : ℕ) * D ^ δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]
      congr 1
      congr 1
      dsimp [η]
      ring

/-- Finite character and dyadic sums preserve a uniform block bound. -/
theorem sum_blocks_le {α : Type*} (s : Finset α) (n : ℕ)
    (v : α → ℕ → ℕ → ℝ) (T : ℝ)
    (hv : ∀ a ∈ s, ∀ j ∈ Finset.range n, ∀ l ∈ Finset.range n, v a j l ≤ T) :
    (∑ a ∈ s, ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, v a j l) ≤
      (s.card : ℝ) * (n : ℝ) ^ (2 : ℕ) * T := by
  calc
    _ ≤ ∑ _a ∈ s, ∑ _j ∈ Finset.range n, ∑ _l ∈ Finset.range n, T := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum (fun l hl => hv a ha j hj l hl)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Full frozen conclusion conditional on exactly the two remaining inputs.
The original five upstream premises are explicit; no finished-looking alias of
`Manuscript.poisson_reduction_step` is introduced. -/
theorem poisson_reduction_step_of_components (ha : ArithmeticStatement)
    (hp : PoissonStatement) (hz : PoissonZeroStatement)
    (he : RemoveExclusionsStatement) (hs : SmoothMeanSquareStatement)
    (hexp : PoissonDyadicExpansionInput) (hblock : PoissonDyadicBlockInput) :
    PoissonReductionStatement := by
  intro θ hθ hθmax hinit ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨J, hJ, hi⟩ := hinit δ hδ
  refine ⟨2 * J + 4, by omega, ?_⟩
  intro c I
  obtain ⟨c', hν, hS, hc'⟩ := ha c.nu c.S c.prime_S c.above_two c.above_three c.conductor_S
  obtain ⟨Φ, Ξ, A, Z, hA, hZ, hexp'⟩ := hexp hp hz c' I hc'
  obtain ⟨K, hK, henergy⟩ := hi c' (initialTestInterval I) (initialGap I Φ) hc'
    (initialGap_one_le I Φ)
  obtain ⟨L, hL, hb⟩ := hblock he hs θ δ J hθ hθmax hδ hJ c' I Φ hc' K hK henergy
  obtain ⟨Q, hQ, hdepth⟩ := initialDepth_sq_bound I (show 0 < 2 * δ by positivity)
  let R : ℝ := A * (Ξ.card : ℝ) * Q * L
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨Z + R, add_nonneg hZ hR, ?_⟩
  intro W D hW hD
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hH : 0 < D ^ (1 + θ) := Real.rpow_pos_of_pos hD0 _
  have hnorm : weightNorm 0 W ^ (2 : ℕ) ≤ weightNorm (2 * J + 4) W ^ (2 : ℕ) :=
    pow_le_pow_left₀ (weightNorm_nonneg hW 0) (weightNorm_mono hW (by omega)) _
  have hpε : 1 ≤ D ^ ε := Real.one_le_rpow hD1 hε.le
  have hsum := sum_blocks_le Ξ (initialDepth I D)
    (fun ξ j l => ‖initialDyadicBlock c' ξ I Φ W D (D ^ (1 + θ))
      ((2 : ℝ) ^ j) ((2 : ℝ) ^ l)‖)
    (L * weightNorm (2 * J + 4) W ^ 2 * D ^ (2 * δ) * D ^ (1 + θ))
    (fun ξ _ j _ l _ => hb ξ W D _ _ hW hD
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)))
  have hzero : Z * weightNorm 0 W ^ 2 * D ^ (1 + θ) ≤
      Z * weightNorm (2 * J + 4) W ^ 2 * D ^ ε * D ^ (1 + θ) := by
    calc
      _ ≤ Z * weightNorm (2 * J + 4) W ^ 2 * D ^ (1 + θ) := by gcongr
      _ ≤ _ := by
        have hz0 : 0 ≤ Z * weightNorm (2 * J + 4) W ^ 2 := mul_nonneg hZ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hz0 hpε) hH.le
  have hblocks : A * (∑ ξ ∈ Ξ, ∑ j ∈ Finset.range (initialDepth I D),
      ∑ l ∈ Finset.range (initialDepth I D),
        ‖initialDyadicBlock c' ξ I Φ W D (D ^ (1 + θ)) ((2 : ℝ) ^ j) ((2 : ℝ) ^ l)‖) ≤
      R * weightNorm (2 * J + 4) W ^ 2 * D ^ ε * D ^ (1 + θ) := by
    calc
      _ ≤ A * ((Ξ.card : ℝ) * (initialDepth I D : ℝ) ^ 2 *
          (L * weightNorm (2 * J + 4) W ^ 2 * D ^ (2 * δ) * D ^ (1 + θ))) :=
        mul_le_mul_of_nonneg_left hsum hA
      _ ≤ A * ((Ξ.card : ℝ) * (Q * D ^ (2 * δ)) *
          (L * weightNorm (2 * J + 4) W ^ 2 * D ^ (2 * δ) * D ^ (1 + θ))) := by
        gcongr
        exact hdepth D hD
      _ = _ := by
        have hpow : D ^ (2 * δ) * D ^ (2 * δ) = D ^ ε := by
          rw [← Real.rpow_add hD0]
          congr 1
          dsimp [δ]
          ring
        dsimp [R]
        calc
          _ = (A * (Ξ.card : ℝ) * Q * L) * weightNorm (2 * J + 4) W ^ 2 *
              (D ^ (2 * δ) * D ^ (2 * δ)) * D ^ (1 + θ) := by ring
          _ = _ := by rw [hpow]
  rw [originalMeanSquare_context_eq c c' hν.symm hS.symm]
  calc
    _ ≤ D * (Z * weightNorm 0 W ^ 2 * D ^ (1 + θ) + A *
        ∑ ξ ∈ Ξ, ∑ j ∈ Finset.range (initialDepth I D),
          ∑ l ∈ Finset.range (initialDepth I D),
            ‖initialDyadicBlock c' ξ I Φ W D (D ^ (1 + θ)) ((2 : ℝ) ^ j) ((2 : ℝ) ^ l)‖) :=
      hexp' W D _ hW hD hH
    _ ≤ D * (Z * weightNorm (2 * J + 4) W ^ 2 * D ^ ε * D ^ (1 + θ) +
        R * weightNorm (2 * J + 4) W ^ 2 * D ^ ε * D ^ (1 + θ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hzero hblocks) hD0.le
    _ = (Z + R) * weightNorm (2 * J + 4) W ^ 2 * D ^ (2 + θ + ε) := by
      have hpow : D * D ^ ε * D ^ (1 + θ) = D ^ (2 + θ + ε) := by
        calc
          _ = D ^ (1 : ℝ) * D ^ ε * D ^ (1 + θ) := by rw [Real.rpow_one]
          _ = D ^ ((1 + ε) + (1 + θ)) := by
            rw [← Real.rpow_add hD0, ← Real.rpow_add hD0]
          _ = _ := by congr 1; ring
      calc
        _ = (Z + R) * weightNorm (2 * J + 4) W ^ 2 * (D * D ^ ε * D ^ (1 + θ)) := by ring
        _ = _ := by rw [hpow]

end QRHShort.PoissonReductionProof
