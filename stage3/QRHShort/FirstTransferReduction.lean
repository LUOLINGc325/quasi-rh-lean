import QRHShort.Estimates
import QRHShort.SmoothingStatements
import QRHShort.WeightNorm
import Mathlib.Tactic.Ring

/-!
First-transfer reduction, paper2.tex:2273–2354. The three remaining analytic
obligations below concern explicit arithmetic sums. The finite model is chosen
before the test function, and its quadratic domination holds for every test.
No convergence of a `tsum` follows merely from the notation used here.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The coefficient `p_y(n)` in (P), with its two column restrictions. -/
def firstTransferCoefficient (c : ArithmeticContext) (ξ : RayCharacter c)
    (C d t : Ideal O) (y : O) (n : Ideal O) : ℂ :=
  if SquarefreeOutside c.S n ∧ IsRelPrime n t then
    (mobius n : ℂ) * rayValue ξ.val n * star (sexticSymbol n y) *
      sexticSymbol n (primaryGenerator C) ^ (4 : ℕ) *
      sexticSymbol n (primaryGenerator d)
  else 0

/-- The new coefficient is exactly the coefficient of the frozen first column. -/
theorem firstColumn_eq_firstTransferCoefficient (c : ArithmeticContext)
    (ξ : RayCharacter c) (C d t : Ideal O) (U : ℝ → ℂ) (ell : ℝ) (y : O) :
    firstColumn c ξ C d t U ell y =
      ∑' n : Ideal O, firstTransferCoefficient c ξ C d t y n * U (normIdeal n / ell) := by
  unfold firstColumn
  apply tsum_congr
  intro n
  simp only [firstTransferCoefficient]
  split_ifs <;> simp_all

/-- The coupled kernel; the nonnegative parameter is
`H N(h) N(C)^2 / (L^2 N(d))`. -/
def firstTransferKernel (Φ : RowWeight) (W : ℝ → ℂ) (a : ℝ)
    (z : BoxSpace 2) : ℂ :=
  (Real.sqrt (z 0 * z 1) : ℂ)⁻¹ * W (z 0) * star (W (z 1)) *
    radialFourier (fun x => (Φ.value x : ℂ)) (a / (z 0 * z 1))

/-- The coupled kernel has the required box support, including at the axes. -/
theorem firstTransferKernel_support (I : SupportInterval) (Φ : RowWeight)
    (W : ℝ → ℂ) (hW : SmoothSupported I W) (a : ℝ) :
    Function.support (firstTransferKernel Φ W a) ⊆
      {z | ∀ i : Fin 2, z i ∈ Set.Icc I.lo I.hi} := by
  intro z hz
  have hzero : W (z 0) ≠ 0 := by
    intro h
    exact hz (by simp [firstTransferKernel, h])
  have hone : W (z 1) ≠ 0 := by
    intro h
    exact hz (by simp [firstTransferKernel, h])
  intro i
  refine Fin.cases (hW.2 hzero) (fun k => ?_) i
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  exact hW.2 hone

/-- Normalize the frequency cutoff to the compact kernel-parameter range. -/
theorem first_transfer_kernel_parameter_le {H L c d h cap : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hc : 0 < c) (hd : 0 < d)
    (hfreq : h ≤ cap * L ^ 2 * d / (H * c ^ 2)) :
    H * h * c ^ 2 / (L ^ 2 * d) ≤ cap := by
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hL) hd)).2
  have hh := (le_div_iff₀ (mul_pos hH (sq_pos_of_pos hc))).1 hfreq
  calc
    H * h * c ^ 2 = h * (H * c ^ 2) := by ring
    _ ≤ cap * L ^ 2 * d := hh
    _ = cap * (L ^ 2 * d) := by ring

/-- The nonzero-frequency expression for one ray character, before smooth
separation. Every range and exclusion is the one in paper2.tex:2309–2324. -/
def firstTransferBilinear (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ) : ℂ :=
  ∑' C : Ideal O, ∑' t : Ideal O,
    if SquarefreeOutside c.S C ∧ SquarefreeOutside c.S t ∧ IsRelPrime C t ∧
        normIdeal C * normIdeal t ≤ 2 * I.hi * L then
      ∑' d : Ideal O, if d ∣ C then
        (mobius d : ℂ) * (mobius t : ℂ) *
        (H * normIdeal C / (normIdeal d * L ^ (2 : ℕ) * F) : ℝ) *
        ∑' f : Ideal O,
          if SquarefreeOutside c.S f ∧ F ≤ normIdeal f ∧ normIdeal f < 2 * F ∧
              IsRelPrime f (C * t) then
            ∑' h : O, if h ≠ 0 ∧ IsRelPrime (principal h) t ∧
                normElement h ≤ Φ.fourierCap * I.hi ^ (2 : ℕ) * L ^ (2 : ℕ) *
                  normIdeal d / (H * normIdeal C ^ (2 : ℕ)) then
              ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
                firstTransferCoefficient c ξ C d t
                    (h * primaryGenerator f ^ (2 : ℕ)) n₁ *
                  star (firstTransferCoefficient c ξ C d t
                    (h * primaryGenerator f ^ (2 : ℕ)) n₂) *
                  firstTransferKernel Φ W
                    (H * normElement h * normIdeal C ^ (2 : ℕ) /
                      (L ^ (2 : ℕ) * normIdeal d))
                    ![normIdeal n₁ / (L / (normIdeal C * normIdeal t)),
                      normIdeal n₂ / (L / (normIdeal C * normIdeal t))]
            else 0
          else 0
      else 0
    else 0

/-- Child P: first Poisson, CRT/Gauss pairing, finite ray Fourier expansion,
and the diagonal lattice-counting bound. Its constant precedes all scales.
A proof must justify the exchanges of sums in the literal expression above. -/
def FirstTransferPoissonBound : Prop :=
  ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight),
    ArithmeticRelations c → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ξ : RayCharacter c) (W : ℝ → ℂ) (H L F : ℝ),
        SmoothSupported I W → 1 ≤ H → 1 ≤ L → 1 ≤ F →
        smoothedEnergy c ξ Φ.value W H L F ≤
          K * (H * weightNorm 0 W ^ 2 + QRHLean3.supZero
            {v | ∃ ξ₁ : RayCharacter c,
              v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖})

/-- A finite presentation of the explicit off-diagonal expression, valid for
all smooth tests. This is data, not an assertion that such data exist. -/
structure FirstTransferFiniteModel (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (H L F : ℝ) where
  R : ℕ
  N : ℕ
  a : Fin R → Fin N → ℂ
  x : Fin R → Fin N → ℝ
  w : Fin R → ℝ
  coefficient : Fin R → ℂ
  parameter : Fin R → ℝ
  x_pos : ∀ r n, 0 < x r n
  w_nonneg : ∀ r, 0 ≤ w r
  coefficient_le : ∀ r, ‖coefficient r‖ ≤ w r
  parameter_nonneg : ∀ r, 0 ≤ parameter r
  parameter_le : ∀ r, parameter r ≤ Φ.fourierCap * I.hi ^ (2 : ℕ)
  expansion : ∀ W : ℝ → ℂ, SmoothSupported I W →
    firstTransferBilinear c I Φ ξ W H L F =
      ∑ r : Fin R, coefficient r * ∑ n₁ : Fin N, ∑ n₂ : Fin N,
        a r n₁ * star (a r n₂) *
          firstTransferKernel Φ W (parameter r) ![x r n₁, x r n₂]

/-- Child M: finite-support reduction and the divisor multiplicity of
`(f,h) ↦ h f²`. The majorant is the *actual* first form, uniformly in U;
no first-transfer estimate or bound on the coupled kernel is assumed. -/
def FirstTransferFiniteReductionStatement : Prop :=
  ∀ C ε : ℝ, 1 ≤ C → 0 < ε →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) (cI : ℝ),
      ArithmeticRelations c → max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (D H L F Sigma : ℝ),
        2 ≤ D → TransferRange D C H L F Sigma →
        ∃ model : FirstTransferFiniteModel c I Φ ξ H L F,
          ∀ U : ℝ → ℂ, SmoothSupported (halfEnlarged I) U →
            (∑ r : Fin model.R, model.w r *
              ‖finiteTestSum model.a model.x r U‖ ^ 2) ≤
                K * D ^ ε * firstForm c I Φ ξ U cI H L F Sigma

/-- Child K: uniform smoothness and derivative bounds for the literal
coupled kernel on its compact parameter interval. -/
def FirstTransferKernelStatement : Prop :=
  ∀ (I : SupportInterval) (Φ : RowWeight) (q : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ → ℂ) (a : ℝ),
      SmoothSupported I W → 0 ≤ a → a ≤ Φ.fourierCap * I.hi ^ (2 : ℕ) →
      SmoothBox (fun _ : Fin 2 => I) (firstTransferKernel Φ W a) ∧
        multiWeightNorm q (firstTransferKernel Φ W a) ≤ K * weightNorm q W ^ 2

/-- The scalar image-range step: the frequency cutoff and `LF ≤ Sigma`
put `N(h) N(f)^2` inside the majorized y-range. -/
theorem first_transfer_frequency_image_le
    {A L F Sigma h f : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hF : 0 ≤ F) (hh : 0 ≤ h) (hf : 0 ≤ f)
    (hhbound : h ≤ A * L ^ 2) (hfbound : f ≤ 2 * F)
    (hrange : L * F ≤ Sigma) :
    h * f ^ 2 ≤ 4 * A * Sigma * L * F := by
  have hfsq : f ^ 2 ≤ (2 * F) ^ 2 := (sq_le_sq₀ hf (by positivity)).2 hfbound
  calc
    h * f ^ 2 ≤ (A * L ^ 2) * (2 * F) ^ 2 :=
      mul_le_mul hhbound hfsq (sq_nonneg _) (by positivity)
    _ = 4 * A * (L * F) * (L * F) := by ring
    _ ≤ 4 * A * Sigma * (L * F) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrange (by positivity)) (mul_nonneg hL hF)
    _ = _ := by ring

/-- The actual first form is nonnegative on positive scales. This uses only
nonnegativity of its summands, not any assertion of their summability. -/
theorem firstForm_nonneg (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (ξ : RayCharacter c) (U : ℝ → ℂ)
    {cI H L F Sigma : ℝ} (hcI : 0 ≤ cI) (hH : 0 ≤ H)
    (hL : 0 ≤ L) (hF : 0 ≤ F) (hSigma : 0 ≤ Sigma) :
    0 ≤ firstForm c I Φ ξ U cI H L F Sigma := by
  have hn (a : Ideal O) : 0 ≤ normIdeal a := by unfold normIdeal; positivity
  have he (a : O) : 0 ≤ normElement a := hn (principal a)
  unfold firstForm
  apply tsum_nonneg
  intro C
  apply tsum_nonneg
  intro t
  split_ifs
  · apply tsum_nonneg
    intro d
    split_ifs
    · apply mul_nonneg (div_nonneg (mul_nonneg hH (hn C))
        (mul_nonneg (mul_nonneg (hn d) (sq_nonneg L)) hF))
      apply tsum_nonneg
      intro y
      apply mul_nonneg (Φ.nonnegative _ _) (sq_nonneg _)
      exact div_nonneg (he y) (div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcI hSigma) hL) hF) (hn d))
        (mul_nonneg hH (sq_nonneg _)))
    · exact le_refl 0
  · exact le_refl 0

/-- Smooth mean square controls the concrete off-diagonal expression, given
children M and K. All constants are chosen before the character and scales. -/
theorem first_transfer_bilinear_bound
    (hfinite : FirstTransferFiniteReductionStatement)
    (hkernel : FirstTransferKernelStatement) (hsmooth : SmoothMeanSquareStatement)
    (C ε : ℝ) (j : ℕ) (hC : 1 ≤ C) (hε : 0 < ε)
    (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight) (cI : ℝ)
    (hc : ArithmeticRelations c)
    (hcI : max 1 (4 * Φ.fourierCap * I.hi ^ (2 : ℕ)) ≤ cI) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : RayCharacter c) (W : ℝ → ℂ)
      (D H L F Sigma M : ℝ), SmoothSupported I W → 2 ≤ D →
      TransferRange D C H L F Sigma → 0 ≤ M →
      (∀ U : ℝ → ℂ, SmoothSupported (halfEnlarged I) U →
        firstForm c I Φ ξ U cI H L F Sigma ≤ M * weightNorm j U ^ 2) →
      ‖firstTransferBilinear c I Φ ξ W H L F‖ ≤
        K * D ^ ε * M * weightNorm (2 * j + 4) W ^ 2 := by
  obtain ⟨Kr, hKr, hred⟩ := hfinite C ε hC hε c I Φ cI hc hcI
  obtain ⟨Kk, hKk, hker⟩ := hkernel I Φ (2 * j + 4)
  have hlo : (halfEnlarged I).lo < I.lo := by
    dsimp [halfEnlarged]; linarith [I.lo_pos]
  have hhi : I.hi < (halfEnlarged I).hi := by
    dsimp [halfEnlarged]; linarith [I.lo_pos, I.ordered]
  obtain ⟨Ks, hKs, hs⟩ := hsmooth I (halfEnlarged I) j hlo hhi
  refine ⟨Ks * Kr * Kk, mul_nonneg (mul_nonneg hKs hKr) hKk, ?_⟩
  intro ξ W D H L F Sigma M hW hD hrange hM hform
  obtain ⟨model, hmodel⟩ := hred ξ D H L F Sigma hD hrange
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hp : 0 ≤ D ^ ε := Real.rpow_nonneg hD0 _
  let M' : ℝ := Kr * D ^ ε * M
  have hM' : 0 ≤ M' := mul_nonneg (mul_nonneg hKr hp) hM
  have htest (U : ℝ → ℂ) (hU : SmoothSupported (halfEnlarged I) U) :
      (∑ r : Fin model.R, model.w r * ‖finiteTestSum model.a model.x r U‖ ^ 2) ≤
        M' * weightNorm j U ^ 2 := by
    calc
      _ ≤ Kr * D ^ ε * firstForm c I Φ ξ U cI H L F Sigma := hmodel U hU
      _ ≤ Kr * D ^ ε * (M * weightNorm j U ^ 2) :=
        mul_le_mul_of_nonneg_left (hform U hU) (mul_nonneg hKr hp)
      _ = _ := by dsimp only [M']; ring
  let kernels := fun r : Fin model.R => firstTransferKernel Φ W (model.parameter r)
  have hk (r : Fin model.R) :=
    hker W (model.parameter r) hW (model.parameter_nonneg r) (model.parameter_le r)
  have hbound := hs model.R model.N model.N model.a model.a model.x model.x
    model.w model.coefficient M' M' kernels model.x_pos model.x_pos
    model.w_nonneg model.coefficient_le hM' hM' htest htest (fun r => (hk r).1)
  rw [Real.sqrt_mul_self hM'] at hbound
  have hsup : QRHLean3.supZero
      {v | ∃ r : Fin model.R, v = multiWeightNorm (2 * j + 4) (kernels r)} ≤
        Kk * weightNorm (2 * j + 4) W ^ 2 := by
    apply QRHLean3.supZero_le (mul_nonneg hKk (sq_nonneg _))
    rintro v ⟨r, rfl⟩
    exact (hk r).2
  calc
    ‖firstTransferBilinear c I Φ ξ W H L F‖ ≤
        Ks * M' * QRHLean3.supZero
          {v | ∃ r : Fin model.R, v = multiWeightNorm (2 * j + 4) (kernels r)} := by
      rw [model.expansion W hW]
      exact hbound
    _ ≤ Ks * M' * (Kk * weightNorm (2 * j + 4) W ^ 2) :=
      mul_le_mul_of_nonneg_left hsup (mul_nonneg hKs hM')
    _ = _ := by dsimp only [M']; ring

/-- Assembly with exactly the frozen `FirstTransferEstimate` as conclusion.
Children P, M, K are explicit premises; their proofs remain separate tasks. -/
theorem first_transfer_of_components
    (hpoisson : FirstTransferPoissonBound)
    (hfinite : FirstTransferFiniteReductionStatement)
    (hkernel : FirstTransferKernelStatement) (hsmooth : SmoothMeanSquareStatement) :
    FirstTransferEstimate := by
  intro C ε j hC hε c I Φ cI hc hcI
  obtain ⟨Kp, hKp, hP⟩ := hpoisson c I Φ hc
  obtain ⟨Kb, hKb, hB⟩ :=
    first_transfer_bilinear_bound hfinite hkernel hsmooth C ε j hC hε c I Φ cI hc hcI
  refine ⟨Kp * (1 + Kb), mul_nonneg hKp (add_nonneg zero_le_one hKb), ?_⟩
  intro ξ W D H L F Sigma M hW hD hrange hM hform
  have hscales := hrange
  obtain ⟨hH, _, hL, _, hF, _, hSigma, _, hmax⟩ := hscales
  have hp1 : 1 ≤ D ^ ε := Real.one_le_rpow (le_trans (by norm_num) hD) hε.le
  have hp0 : 0 ≤ D ^ ε := zero_le_one.trans hp1
  have hSig0 : 0 ≤ Sigma := zero_le_one.trans hSigma
  have hHS : H ≤ Sigma := (le_max_left _ _).trans hmax
  have hnorm0 : weightNorm 0 W ^ 2 ≤ weightNorm (2 * j + 4) W ^ 2 :=
    (sq_le_sq₀ (weightNorm_nonneg hW _) (weightNorm_nonneg hW _)).2
      (weightNorm_mono hW (Nat.zero_le _))
  have hdiag : H * weightNorm 0 W ^ 2 ≤
      D ^ ε * Sigma * weightNorm (2 * j + 4) W ^ 2 := by
    have hscale : H ≤ D ^ ε * Sigma := calc
      H ≤ Sigma := hHS
      _ = 1 * Sigma := (one_mul _).symm
      _ ≤ D ^ ε * Sigma := mul_le_mul_of_nonneg_right hp1 hSig0
    exact mul_le_mul hscale hnorm0 (sq_nonneg _) (mul_nonneg hp0 hSig0)
  have hoff : QRHLean3.supZero
      {v | ∃ ξ₁ : RayCharacter c, v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖} ≤
        Kb * D ^ ε * M * weightNorm (2 * j + 4) W ^ 2 := by
    apply QRHLean3.supZero_le (by positivity)
    rintro v ⟨ξ₁, rfl⟩
    exact hB ξ₁ W D H L F Sigma M hW hD hrange hM (hform ξ₁)
  have hscalar : Sigma + Kb * M ≤ (1 + Kb) * (Sigma + M) := by
    nlinarith [mul_nonneg hKb hSig0]
  calc
    smoothedEnergy c ξ Φ.value W H L F ≤
        Kp * (H * weightNorm 0 W ^ 2 + QRHLean3.supZero
          {v | ∃ ξ₁ : RayCharacter c, v = ‖firstTransferBilinear c I Φ ξ₁ W H L F‖}) :=
      hP ξ W H L F hW hH hL hF
    _ ≤ Kp * (D ^ ε * Sigma * weightNorm (2 * j + 4) W ^ 2 +
          Kb * D ^ ε * M * weightNorm (2 * j + 4) W ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiag hoff) hKp
    _ = Kp * D ^ ε * (Sigma + Kb * M) * weightNorm (2 * j + 4) W ^ 2 := by ring
    _ ≤ Kp * D ^ ε * ((1 + Kb) * (Sigma + M)) * weightNorm (2 * j + 4) W ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscalar (mul_nonneg hKp hp0)) (sq_nonneg _)
    _ = (Kp * (1 + Kb)) * D ^ ε * (Sigma + M) * weightNorm (2 * j + 4) W ^ 2 := by ring

end QRHShort
