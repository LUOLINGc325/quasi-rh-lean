import QRHShort.SecondTransferPRMRPreimages


noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem second_transfer_r_de_outside (c : ArithmeticContext) {r f : Ideal O}
    (hf : Outside c.S f) (p : SecondTransferRIdealPreimage r f) :
    Outside c.S (p.d*p.e) := by
  apply second_transfer_r_outside_dvd hf
  exact ((mul_dvd_mul p.d_dvd (dvd_refl p.e)).trans (dvd_mul_right _ _)).trans
    (dvd_of_eq p.twist_eq)

theorem second_transfer_r_frequency_ideal (c : ArithmeticContext) {r f : Ideal O}
    (hf : Outside c.S f) (p : SecondTransferRIdealPreimage r f) {k h : O}
    (hh : primaryGenerator (p.d*p.e)*h=k) :
    principal k = (p.d*p.e)*principal h := by
  have hg := second_transfer_r_primary_spec c (second_transfer_r_de_outside c hf p)
  calc
    principal k = principal (primaryGenerator (p.d*p.e)*h) := congrArg principal hh.symm
    _ = principal (primaryGenerator (p.d*p.e))*principal h :=
      (Ideal.span_singleton_mul_span_singleton _ _).symm
    _ = _ := congrArg (fun a : Ideal O => a*principal h) hg

theorem second_transfer_r_w_coprime_de {r f : Ideal O} (hf : Squarefree f)
    (p : SecondTransferRIdealPreimage r f) : IsRelPrime p.w (p.d*p.e) := by
  have hs : Squarefree (p.C*p.e*p.w) := hf.squarefree_of_dvd (dvd_of_eq p.twist_eq)
  exact (IsRelPrime.of_squarefree_mul hs).symm.of_dvd_right
    (mul_dvd_mul p.d_dvd (dvd_refl p.e))

/-- The actual frequency equation and the original w-coprimality condition.
All six ideal indices retain their literal quotient relations. -/
def SecondTransferRFrequencyFiber (r f : Ideal O) (k : O) :=
  {p : SecondTransferRIdealPreimage r f × O //
    primaryGenerator (p.1.d*p.1.e)*p.2=k ∧ IsRelPrime p.1.w (principal p.2)}

def SecondTransferRDivisibleFiber (r f : Ideal O) (k : O) :=
  {p : SecondTransferRIdealPreimage r f // p.d ∣ principal k ∧
    p.e ∣ principal k ∧ IsRelPrime p.w (principal k)}

def secondTransferRFrequencyFiberEquiv (c : ArithmeticContext) {r f : Ideal O}
    (hf : SquarefreeOutside c.S f) (k : O) :
    SecondTransferRDivisibleFiber r f k ≃ SecondTransferRFrequencyFiber r f k where
  toFun p := by
    have hex := (second_transfer_r_de_frequency_preimage c hf p.1.twist_eq p.1.d_dvd k).mp
      ⟨p.2.1,p.2.2.1⟩
    let h := Classical.choose hex
    have hh : primaryGenerator (p.1.d*p.1.e)*h=k := (Classical.choose_spec hex).1
    refine ⟨(p.1,h),hh,?_⟩
    have hk := second_transfer_r_frequency_ideal c hf.1 p.1 hh
    have hw := p.2.2.2
    have hw' := (congrArg (fun a : Ideal O => IsRelPrime p.1.w a) hk).mp hw
    exact hw'.of_mul_right_right
  invFun p := by
    have hk := second_transfer_r_frequency_ideal c hf.1 p.1.1 p.2.1
    refine ⟨p.1.1,?_,?_,?_⟩
    · exact ((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans (dvd_of_eq hk.symm)
    · exact ((dvd_mul_left _ _).trans (dvd_mul_right _ _)).trans (dvd_of_eq hk.symm)
    · simpa only [hk] using ((second_transfer_r_w_coprime_de hf.2 p.1.1).mul_right p.2.2)
  left_inv p := rfl
  right_inv p := by
    apply Subtype.ext
    change (p.1.1, _) = (p.1.1, p.1.2)
    apply Prod.ext
    · rfl
    exact ((Classical.choose_spec
      ((second_transfer_r_de_frequency_preimage c hf p.1.1.twist_eq p.1.1.d_dvd k).mp
        ⟨((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans
            (dvd_of_eq (second_transfer_r_frequency_ideal c hf.1 p.1.1 p.2.1).symm),
          ((dvd_mul_left _ _).trans (dvd_mul_right _ _)).trans
            (dvd_of_eq (second_transfer_r_frequency_ideal c hf.1 p.1.1 p.2.1).symm)⟩)).2
      p.1.2 p.2.1).symm

theorem second_transfer_r_frequency_equiv_ideal (c : ArithmeticContext) {r f : Ideal O}
    (hf : SquarefreeOutside c.S f) (k : O) (p : SecondTransferRDivisibleFiber r f k) :
    ((secondTransferRFrequencyFiberEquiv c hf k p).1).1 = p.1 := rfl

theorem second_transfer_r_frequency_fiber_finite (c : ArithmeticContext)
    {r f : Ideal O} (hr : r ≠ ⊥) (hf : SquarefreeOutside c.S f) (k : O) :
    Finite (SecondTransferRFrequencyFiber r f k) := by
  letI := second_transfer_r_ideal_preimage_finite r f hr hf.2
  letI : Finite (SecondTransferRDivisibleFiber r f k) := by
    change Finite {p : SecondTransferRIdealPreimage r f // p.d ∣ principal k ∧
      p.e ∣ principal k ∧ IsRelPrime p.w (principal k)}
    infer_instance
  exact Finite.of_equiv _ (secondTransferRFrequencyFiberEquiv c hf k)

/-- Signed regrouping over the complete literal frequency preimage fiber.
The unique element lift has no multiplicity; the only multiplicity is tau(r). -/
theorem second_transfer_r_signed_frequency_fiber (c : ArithmeticContext)
    {r f : Ideal O} (hr : r ≠ ⊥) (hf : SquarefreeOutside c.S f) (k : O) :
    (∑' p : SecondTransferRFrequencyFiber r f k,
      mobius p.1.1.e * mobius p.1.1.w) =
      (divisorCount r : ℤ) * (if f ∣ principal k then 1 else 0) := by
  rw [← (secondTransferRFrequencyFiberEquiv c hf k).tsum_eq]
  simp only [second_transfer_r_frequency_equiv_ideal]
  change (∑' p : {p : SecondTransferRIdealPreimage r f // p.d ∣ principal k ∧
    p.e ∣ principal k ∧ IsRelPrime p.w (principal k)}, mobius p.1.e * mobius p.1.w) = _
  have hsub := tsum_subtype
    (s := {p : SecondTransferRIdealPreimage r f | p.d ∣ principal k ∧
      p.e ∣ principal k ∧ IsRelPrime p.w (principal k)})
    (f := fun p : SecondTransferRIdealPreimage r f => mobius p.e * mobius p.w)
  let E : {p : SecondTransferRIdealPreimage r f // p.d ∣ principal k ∧
      p.e ∣ principal k ∧ IsRelPrime p.w (principal k)} ≃
      ↥{p : SecondTransferRIdealPreimage r f | p.d ∣ principal k ∧
        p.e ∣ principal k ∧ IsRelPrime p.w (principal k)} :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  calc
    _ = ∑' p : ↥{p : SecondTransferRIdealPreimage r f | p.d ∣ principal k ∧
        p.e ∣ principal k ∧ IsRelPrime p.w (principal k)}, mobius p.1.e * mobius p.1.w :=
      E.tsum_eq (fun p => mobius p.1.e * mobius p.1.w)
    _ = ∑' p : SecondTransferRIdealPreimage r f,
        if p.d ∣ principal k ∧ p.e ∣ principal k ∧ IsRelPrime p.w (principal k)
          then mobius p.e * mobius p.w else 0 := by
      simpa only [Set.indicator_apply, Set.mem_setOf_eq] using hsub
    _ = _ := second_transfer_r_signed_ideal_preimages r f (principal k) hr hf.2

end QRHShort



noncomputable section
open Classical

namespace QRHShort.SecondTransferRNormKernel

theorem outside_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) : Outside c.S (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  intro p hp hdiv
  rcases (c.prime_S p hp).dvd_mul.mp hdiv with h | h
  · exact ha.2 p hp h
  · exact hb.2 p hp h

theorem norm_primary_mul (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) (h : O) :
    normElement (primaryGenerator a * h) = normIdeal a * normElement h := by
  have hmul : principal (primaryGenerator a * h) =
      principal (primaryGenerator a) * principal h :=
    (Ideal.span_singleton_mul_span_singleton _ _).symm
  change normIdeal (principal (primaryGenerator a * h)) = normIdeal a * normIdeal (principal h)
  rw [hmul, second_transfer_r_primary_spec c ha, normIdeal_mul]

theorem frequency_norm (c : ArithmeticContext) {C d g e : Ideal O}
    (hC : Outside c.S C) (hg : Outside c.S g) (hd : d ∣ C) (he : e ∣ g) (h : O) :
    normElement (primaryGenerator (d * e) * h) =
      normIdeal d * normIdeal e * normElement h := by
  have hdout := second_transfer_r_outside_dvd hC hd
  have heout := second_transfer_r_outside_dvd hg he
  rw [norm_primary_mul c (outside_mul c hdout heout), normIdeal_mul]

theorem excluded_norm (c : ArithmeticContext) {g e : Ideal O}
    (hg : Outside c.S g) (he : e ∣ g) (t : Ideal O) :
    normIdeal (t * quotientIdeal g e) = normIdeal t * normIdeal g / normIdeal e :=
  second_transfer_r_excluded_norm he (second_transfer_r_outside_dvd hg he).1 t

theorem twist_norm (C e w : Ideal O) :
    normIdeal (C * e * w) = normIdeal C * normIdeal e * normIdeal w := by
  rw [normIdeal_mul, normIdeal_mul]

theorem normalized_length (c : ArithmeticContext) {C t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g) (he : e ∣ g)
    (w : Ideal O) (L : ℝ) :
    (L / (normIdeal C * normIdeal t)) / normIdeal (g * w) =
      L / (normIdeal (t * quotientIdeal g e) * normIdeal (C * e * w)) := by
  by_cases hw : w = ⊥
  · subst w
    simp [normIdeal, Ideal.mul_bot]
  · have heout := second_transfer_r_outside_dvd hg he
    rw [excluded_norm c hg he, twist_norm, normIdeal_mul]
    exact second_transfer_length_identity (normIdeal_pos hC.1).ne'
      (normIdeal_pos ht.1).ne' (normIdeal_pos hg.1).ne'
      (normIdeal_pos heout.1).ne' (normIdeal_pos hw).ne'

/-- The Fourier numerator after inserting the actual Poisson scales, with
the literal frequency element and excluded ideal on the right. -/
theorem normalized_frequency (c : ArithmeticContext) {C d t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g)
    (hd : d ∣ C) (he : e ∣ g) (h : O)
    (cI H L F Sigma : ℝ) (hH : 0 < H) (hL : 0 < L) :
    (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2)) *
        normElement h * normIdeal g ^ 2 /
        (normIdeal e * (L / (normIdeal C * normIdeal t)) ^ 2) =
      cI * Sigma * F * normElement (primaryGenerator (d * e) * h) *
        normIdeal (t * quotientIdeal g e) ^ 2 / (H * L) := by
  have heout := second_transfer_r_outside_dvd hg he
  rw [frequency_norm c hC hg hd he, excluded_norm c hg he]
  exact second_transfer_frequency_identity hH.ne' hL.ne' (normIdeal_pos hC.1).ne'
    (normIdeal_pos ht.1).ne' (normIdeal_pos heout.1).ne'

theorem normalized_weight (c : ArithmeticContext) {C d t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g)
    (hd : d ∣ C) (he : e ∣ g)
    (cI H L F Sigma : ℝ) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) :
    (H * normIdeal C / (normIdeal d * L ^ 2 * F)) *
        ((cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2)) *
          normIdeal g / (normIdeal e * (L / (normIdeal C * normIdeal t)))) =
      cI * Sigma * normIdeal (t * quotientIdeal g e) / L ^ 2 := by
  have hdout := second_transfer_r_outside_dvd hC hd
  have heout := second_transfer_r_outside_dvd hg he
  rw [excluded_norm c hg he]
  exact second_transfer_weight_identity hH.ne' hL.ne' hF.ne'
    (normIdeal_pos hC.1).ne' (normIdeal_pos hdout.1).ne'
    (normIdeal_pos ht.1).ne' (normIdeal_pos heout.1).ne'

theorem kernel_identification (c : ArithmeticContext) {C d t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g)
    (hd : d ∣ C) (he : e ∣ g) (h : O) (Φ : RowWeight) (U : ℝ → ℂ)
    (cI H L F Sigma rho : ℝ) (hH : 0 < H) (hL : 0 < L) (x : BoxSpace 2) :
    secondPoissonKernel Φ U
        (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))
        (L / (normIdeal C * normIdeal t)) g e h (rho * x 0) (rho * x 1) =
      secondTransferKernel Φ U rho
        ((cI * Sigma * F * normElement (primaryGenerator (d * e) * h) *
          normIdeal (t * quotientIdeal g e) ^ 2 / (H * L)) / rho ^ 2) x := by
  rw [second_transfer_r_kernel_dilation,
    normalized_frequency c hC ht hg hd he h cI H L F Sigma hH hL]

theorem poisson_kernel_numerator_le_of_ne_zero (I : SupportInterval) (Φ : RowWeight)
    (U : ℝ → ℂ) (hU : SmoothSupported (halfEnlarged I) U)
    (Y ell : ℝ) (hY : 0 ≤ Y) (g e : Ideal O) (h : O)
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hkernel : secondPoissonKernel Φ U Y ell g e h x₁ x₂ ≠ 0) :
    Y * normElement h * normIdeal g ^ 2 / (normIdeal e * ell ^ 2) ≤
      Φ.fourierCap * (2 * I.hi) ^ 2 := by
  have hu₁ : U x₁ ≠ 0 := by
    intro hz
    exact hkernel (by simp only [secondPoissonKernel, hz, mul_zero, zero_mul])
  have hu₂ : U x₂ ≠ 0 := by
    intro hz
    exact hkernel (by simp only [secondPoissonKernel, hz, mul_zero, star_zero, zero_mul])
  have hx₁hi : x₁ ≤ 2 * I.hi := (hU.2 hu₁).2
  have hx₂hi : x₂ ≤ 2 * I.hi := (hU.2 hu₂).2
  have hhi : 0 < 2 * I.hi := mul_pos (by norm_num) (I.lo_pos.trans_le I.ordered)
  let B := Y * normElement h * normIdeal g ^ 2 / (normIdeal e * ell ^ 2)
  have hNh : 0 ≤ normElement h := Nat.cast_nonneg _
  have hNe : 0 ≤ normIdeal e := Nat.cast_nonneg _
  have hB : 0 ≤ B := div_nonneg
    (mul_nonneg (mul_nonneg hY hNh) (sq_nonneg _)) (mul_nonneg hNe (sq_nonneg _))
  have harg : Y * normElement h * normIdeal g ^ 2 /
      (normIdeal e * ell ^ 2 * x₁ * x₂) = B / (x₁ * x₂) := by
    dsimp only [B]
    rw [div_div]
    congr 1
    ring
  have hfourier : radialFourier (fun x => (Φ.value x : ℂ)) (B / (x₁ * x₂)) ≠ 0 := by
    intro hz
    apply hkernel
    simp only [secondPoissonKernel, harg, hz, mul_zero]
  have hprod : 0 < x₁ * x₂ := mul_pos hx₁ hx₂
  have hcap := (Φ.fourier_support ⟨hfourier, div_nonneg hB hprod.le⟩).2
  have hprodHi : x₁ * x₂ ≤ (2 * I.hi) ^ 2 := by
    calc
      _ ≤ (2 * I.hi) * (2 * I.hi) := mul_le_mul hx₁hi hx₂hi hx₂.le hhi.le
      _ = _ := (pow_two _).symm
  exact ((div_le_iff₀ hprod).mp hcap).trans
    (mul_le_mul_of_nonneg_left hprodHi Φ.cap_pos.le)

theorem normalized_cutoff (c : ArithmeticContext) {C d t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g)
    (hd : d ∣ C) (he : e ∣ g) (h : O) (I : SupportInterval) (Φ : RowWeight)
    (U : ℝ → ℂ) (hU : SmoothSupported (halfEnlarged I) U)
    (cI H L F Sigma : ℝ) (hcI : 0 < cI) (hH : 0 < H) (hL : 0 < L)
    (hF : 0 < F) (hSigma : 0 < Sigma)
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hkernel : secondPoissonKernel Φ U
      (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))
      (L / (normIdeal C * normIdeal t)) g e h x₁ x₂ ≠ 0) :
    normElement (primaryGenerator (d * e) * h) ≤
      (4 * Φ.fourierCap * I.hi ^ 2 / cI) * H * L /
        (Sigma * F * normIdeal (t * quotientIdeal g e) ^ 2) := by
  have hdout := second_transfer_r_outside_dvd hC hd
  have heout := second_transfer_r_outside_dvd hg he
  have hNr : 0 < normIdeal (t * quotientIdeal g e) := by
    rw [excluded_norm c hg he]
    exact div_pos (mul_pos (normIdeal_pos ht.1) (normIdeal_pos hg.1))
      (normIdeal_pos heout.1)
  have hY : 0 ≤ cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2) := by
    exact (div_pos (mul_pos (mul_pos (mul_pos (mul_pos hcI hSigma) hL) hF)
      (normIdeal_pos hdout.1)) (mul_pos hH (sq_pos_of_pos (normIdeal_pos hC.1)))).le
  have hB := poisson_kernel_numerator_le_of_ne_zero I Φ U hU _ _ hY g e h hx₁ hx₂ hkernel
  rw [normalized_frequency c hC ht hg hd he h cI H L F Sigma hH hL] at hB
  have hden : 0 < cI * Sigma * F * normIdeal (t * quotientIdeal g e) ^ 2 :=
    mul_pos (mul_pos (mul_pos hcI hSigma) hF) (sq_pos_of_pos hNr)
  have heq : (4 * Φ.fourierCap * I.hi ^ 2 / cI) * H * L /
        (Sigma * F * normIdeal (t * quotientIdeal g e) ^ 2) =
      (Φ.fourierCap * (2 * I.hi) ^ 2 * (H * L)) /
        (cI * Sigma * F * normIdeal (t * quotientIdeal g e) ^ 2) := by
    field_simp [hcI.ne', hSigma.ne', hF.ne', hNr.ne']
    <;> ring
  rw [heq]
  apply (le_div_iff₀ hden).mpr
  convert (div_le_iff₀ (mul_pos hH hL)).mp hB using 1 <;> ring

/-- The strong Fourier cutoff only implies the weaker arithmetic row cutoff. -/
theorem strong_cutoff_implies_weak {Nk Nr cI H L F Sigma K : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (hcI : 0 < cI) (hNr : 0 < Nr) (hK : K ≤ cI)
    (hcut : Nk ≤ (K / cI) * H * L / (Sigma * F * Nr ^ 2)) :
    Nk ≤ H * L / (Sigma * F * Nr ^ 2) := by
  have hratio : K / cI ≤ 1 := (div_le_one hcI).mpr hK
  have hbase : 0 ≤ H * L / (Sigma * F * Nr ^ 2) := by positivity
  apply hcut.trans
  calc
    _ = (K / cI) * (H * L / (Sigma * F * Nr ^ 2)) := by ring
    _ ≤ 1 * (H * L / (Sigma * F * Nr ^ 2)) := mul_le_mul_of_nonneg_right hratio hbase
    _ = _ := one_mul _

end QRHShort.SecondTransferRNormKernel



noncomputable section
open Classical

namespace QRHShort.SecondTransferRNormKernel

theorem norm_one_le_of_ne_bot {a : Ideal O} (ha : a ≠ ⊥) : 1 ≤ normIdeal a := by
  have hn : a.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr ha
  change (1 : ℝ) ≤ (a.absNorm : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)

/-- The quotient norm cancels exactly against the e-factor in the twist. -/
theorem excluded_twist_product_norm (c : ArithmeticContext) {C t g e : Ideal O}
    (hg : Outside c.S g) (he : e ∣ g) (w : Ideal O) :
    normIdeal (t * quotientIdeal g e) * normIdeal (C * e * w) =
      normIdeal C * normIdeal t * normIdeal (g * w) := by
  have he0 : normIdeal e ≠ 0 :=
    (normIdeal_pos (second_transfer_r_outside_dvd hg he).1).ne'
  rw [excluded_norm c hg he, twist_norm, normIdeal_mul]
  field_simp [he0]
  <;> ring

theorem raw_cutoff_iff (c : ArithmeticContext) {C t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g) (he : e ∣ g)
    (w : Ideal O) (I : SupportInterval) (L : ℝ) :
    normIdeal (g * w) ≤ (halfEnlarged I).hi * (L / (normIdeal C * normIdeal t)) ↔
      normIdeal (t * quotientIdeal g e) * normIdeal (C * e * w) ≤ 2 * I.hi * L := by
  have hden : 0 < normIdeal C * normIdeal t :=
    mul_pos (normIdeal_pos hC.1) (normIdeal_pos ht.1)
  change normIdeal (g * w) ≤ (2 * I.hi) * (L / (normIdeal C * normIdeal t)) ↔ _
  have hscale : (2 * I.hi) * (L / (normIdeal C * normIdeal t)) =
      (2 * I.hi * L) / (normIdeal C * normIdeal t) := by ring
  rw [hscale, le_div_iff₀ hden, excluded_twist_product_norm c hg he w]
  constructor <;> intro h
  · simpa only [mul_comm] using h
  · simpa only [mul_comm] using h

theorem outer_cutoff_of_uniform (c : ArithmeticContext) {C t g e w : Ideal O}
    (hg : Outside c.S g) (he : e ∣ g) (hw : w ≠ ⊥) (I : SupportInterval) (L : ℝ)
    (hcut : normIdeal (t * quotientIdeal g e) * normIdeal (C * e * w) ≤ 2 * I.hi * L) :
    normIdeal C * normIdeal t ≤ 2 * I.hi * L := by
  have hgw : 1 ≤ normIdeal (g * w) := by
    rw [normIdeal_mul]
    exact one_le_mul_of_one_le_of_one_le (norm_one_le_of_ne_bot hg.1) (norm_one_le_of_ne_bot hw)
  have hbase : 0 ≤ normIdeal C * normIdeal t :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (normIdeal C * normIdeal t) * normIdeal (g * w) :=
      le_mul_of_one_le_right hbase hgw
    _ = normIdeal (t * quotientIdeal g e) * normIdeal (C * e * w) :=
      (excluded_twist_product_norm c hg he w).symm
    _ ≤ _ := hcut

theorem outer_cutoff_of_raw (c : ArithmeticContext) {C t g e w : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g)
    (he : e ∣ g) (hw : w ≠ ⊥) (I : SupportInterval) (L : ℝ)
    (hcut : normIdeal (g * w) ≤ (halfEnlarged I).hi * (L / (normIdeal C * normIdeal t))) :
    normIdeal C * normIdeal t ≤ 2 * I.hi * L :=
  outer_cutoff_of_uniform c hg he hw I L ((raw_cutoff_iff c hC ht hg he w I L).mp hcut)

end QRHShort.SecondTransferRNormKernel

