import QRHShort.SecondTransferPRMRReindex
import QRHShort.SecondTransferPRMRModel
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem second_transfer_r_outside_mul (c : ArithmeticContext) {a b : Ideal O}
    (ha : Outside c.S a) (hb : Outside c.S b) : Outside c.S (a*b) := by
  refine ⟨mul_ne_zero ha.1 hb.1,?_⟩
  intro P hP hdiv
  exact ((c.prime_S P hP).dvd_mul.mp hdiv).elim (ha.2 P hP) (hb.2 P hP)

@[ext] structure SecondTransferRInput where
  C : Ideal O
  d : Ideal O
  t : Ideal O
  g : Ideal O
  e : Ideal O
  w : Ideal O
  h : O

def SecondTransferRInput.excluded (p : SecondTransferRInput) : Ideal O :=
  p.t*quotientIdeal p.g p.e

def SecondTransferRInput.twist (p : SecondTransferRInput) : Ideal O := p.C*p.e*p.w

def SecondTransferRInput.frequency (p : SecondTransferRInput) : O :=
  primaryGenerator (p.d*p.e)*p.h

def SecondTransferRInput.admissible (p : SecondTransferRInput) (c : ArithmeticContext) : Prop :=
  SquarefreeOutside c.S p.C ∧ SquarefreeOutside c.S p.t ∧ IsRelPrime p.C p.t ∧
  p.d ∣ p.C ∧ SquarefreeOutside c.S p.g ∧ IsRelPrime p.g (p.C*p.t) ∧
  p.e ∣ p.g ∧ SquarefreeOutside c.S p.w ∧ p.h ≠ 0 ∧
  IsRelPrime p.w (p.g*p.C*p.t*principal p.h)

def SecondTransferRInput.idealPreimage (p : SecondTransferRInput)
    {c : ArithmeticContext} (hp : p.admissible c) :
    SecondTransferRIdealPreimage p.excluded p.twist := {
  C := p.C, d := p.d, t := p.t, g := p.g, e := p.e, w := p.w,
  d_dvd := hp.2.2.2.1,
  e_dvd := hp.2.2.2.2.2.2.1,
  excluded_eq := rfl, twist_eq := rfl }

/-- The original arithmetic filters produce exactly the required coprime
squarefree regrouped ideals and a nonzero literal transformed frequency. -/
theorem second_transfer_r_input_output (c : ArithmeticContext) (p : SecondTransferRInput)
    (hp : p.admissible c) :
    SquarefreeOutside c.S p.excluded ∧ SquarefreeOutside c.S p.twist ∧
      IsRelPrime p.excluded p.twist ∧ p.frequency ≠ 0 := by
  rcases hp with ⟨hC,ht,hCt,hd,hg,hgCt,he,hw,hh,hwfull⟩
  have hct : Squarefree (p.C*p.t) := squarefree_mul_iff.mpr ⟨hCt,hC.2,ht.2⟩
  have hctg : Squarefree (p.C*p.t*p.g) := squarefree_mul_iff.mpr ⟨hgCt.symm,hct,hg.2⟩
  have hwctg : IsRelPrime p.w (p.C*p.t*p.g) := by
    have h := hwfull.of_mul_right_left
    convert h using 1 <;> ac_rfl
  have hs : Squarefree (p.C*p.t*p.g*p.w) :=
    squarefree_mul_iff.mpr ⟨hwctg.symm,hctg,hw.2⟩
  have hout := second_transfer_r_outside_mul c
    (second_transfer_r_outside_mul c (second_transfer_r_outside_mul c hC.1 ht.1) hg.1) hw.1
  have htotal : p.excluded*p.twist=p.C*p.t*p.g*p.w := by
    have hp' : p.admissible c := ⟨hC,ht,hCt,hd,hg,hgCt,he,hw,hh,hwfull⟩
    exact (second_transfer_r_ideal_total (p.idealPreimage hp')).symm
  have hs' : Squarefree (p.excluded*p.twist) := hs.squarefree_of_dvd (dvd_of_eq htotal)
  have hout' : Outside c.S (p.excluded*p.twist) :=
    second_transfer_r_outside_dvd hout (dvd_of_eq htotal)
  have hr : SquarefreeOutside c.S p.excluded :=
    ⟨second_transfer_r_outside_dvd hout' (dvd_mul_right _ _),hs'.of_mul_left⟩
  have hf : SquarefreeOutside c.S p.twist :=
    ⟨second_transfer_r_outside_dvd hout' (dvd_mul_left _ _),hs'.of_mul_right⟩
  refine ⟨hr,hf,IsRelPrime.of_squarefree_mul hs',?_⟩
  have hp' : p.admissible c := ⟨hC,ht,hCt,hd,hg,hgCt,he,hw,hh,hwfull⟩
  have hde := second_transfer_r_de_outside c hf.1 (p.idealPreimage hp')
  have hgen := second_transfer_r_primary_spec c hde
  have hgen0 : primaryGenerator (p.d*p.e) ≠ 0 := by
    intro hz
    apply hde.1
    have hprincipal : principal (primaryGenerator (p.d*p.e))=⊥ := by simp [hz,principal]
    exact hgen.symm.trans hprincipal
  exact mul_ne_zero hgen0 hh

@[ext] structure SecondTransferRLabel (c : ArithmeticContext) where
  excluded : Ideal O
  twist : Ideal O
  frequency : O
  excluded_outside : SquarefreeOutside c.S excluded
  twist_outside : SquarefreeOutside c.S twist
  coprime : IsRelPrime excluded twist
  frequency_ne_zero : frequency ≠ 0

def SecondTransferRInput.label (p : SecondTransferRInput) {c : ArithmeticContext}
    (hp : p.admissible c) : SecondTransferRLabel c := {
  excluded := p.excluded, twist := p.twist, frequency := p.frequency,
  excluded_outside := (second_transfer_r_input_output c p hp).1,
  twist_outside := (second_transfer_r_input_output c p hp).2.1,
  coprime := (second_transfer_r_input_output c p hp).2.2.1,
  frequency_ne_zero := (second_transfer_r_input_output c p hp).2.2.2 }

def SecondTransferRLabel.preimageInput {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (p : SecondTransferRFrequencyFiber z.excluded z.twist z.frequency) : SecondTransferRInput := {
  C := p.1.1.C, d := p.1.1.d, t := p.1.1.t, g := p.1.1.g,
  e := p.1.1.e, w := p.1.1.w, h := p.1.2 }

theorem second_transfer_r_preimage_admissible {c : ArithmeticContext}
    (z : SecondTransferRLabel c)
    (p : SecondTransferRFrequencyFiber z.excluded z.twist z.frequency) :
    (z.preimageInput p).admissible c := by
  obtain ⟨hC,ht,hg,hw,hCt,hgCt,hwgCt⟩ := second_transfer_r_ideal_admissible c
    z.excluded_outside z.twist_outside z.coprime p.1.1
  have hh : p.1.2 ≠ 0 := second_transfer_r_frequency_nonzero z.frequency_ne_zero p.2.1
  exact ⟨hC,ht,hCt,p.1.1.d_dvd,hg,hgCt,p.1.1.e_dvd,hw,hh,hwgCt.mul_right p.2.2⟩

/-- The complete original arithmetic range, before any analytic cutoffs,
is the disjoint union of the actual signed frequency fibers. -/
def secondTransferRRawEquiv (c : ArithmeticContext) :
    {p : SecondTransferRInput // p.admissible c} ≃
      Σ z : SecondTransferRLabel c,
        SecondTransferRFrequencyFiber z.excluded z.twist z.frequency where
  toFun p := ⟨p.1.label p.2,
    ⟨(p.1.idealPreimage p.2,p.1.h),rfl,p.2.2.2.2.2.2.2.2.2.2.of_mul_right_right⟩⟩
  invFun p := ⟨p.1.preimageInput p.2,second_transfer_r_preimage_admissible p.1 p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply SecondTransferRInput.ext <;> rfl
  right_inv p := by
    rcases p with ⟨⟨r,f,k,hr,hf,hrf,hk⟩,⟨⟨p,h⟩,heq,hw⟩⟩
    rcases p with ⟨C,d,t,g,e,w,hd,he,hr',hf'⟩
    change t * quotientIdeal g e = r at hr'
    change C * e * w = f at hf'
    change primaryGenerator (d * e) * h = k at heq
    subst r
    subst f
    subst k
    rfl

/-- A finite collection of regrouped labels has a genuinely finite complete
preimage. This supports joint reindexing, not merely separate iterated sums. -/
theorem second_transfer_r_inputs_finite_of_labels (c : ArithmeticContext)
    (S : Set (SecondTransferRLabel c)) (hS : S.Finite) :
    {p : {p : SecondTransferRInput // p.admissible c} | p.1.label p.2 ∈ S}.Finite := by
  letI : Finite S := hS.to_subtype
  letI (z : S) : Finite (SecondTransferRFrequencyFiber z.1.excluded z.1.twist z.1.frequency) :=
    second_transfer_r_frequency_fiber_finite c z.1.excluded_outside.1.1 z.1.twist_outside z.1.frequency
  let B := Σ z : S, SecondTransferRFrequencyFiber z.1.excluded z.1.twist z.1.frequency
  let make : B → {p : SecondTransferRInput // p.admissible c} :=
    fun p => (secondTransferRRawEquiv c).symm ⟨p.1.1,p.2⟩
  have hb : Finite B := inferInstance
  letI := hb
  apply (Set.finite_range make).subset
  intro p hp
  let q := (secondTransferRRawEquiv c) p
  refine ⟨⟨⟨p.1.label p.2,hp⟩,q.2⟩,?_⟩
  exact (secondTransferRRawEquiv c).symm_apply_apply p

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def SecondTransferRInput.rowScale (p : SecondTransferRInput) (cI H L F Sigma : ℝ) : ℝ :=
  cI*Sigma*L*F*normIdeal p.d/(H*normIdeal p.C^2)

def SecondTransferRInput.length (p : SecondTransferRInput) (L : ℝ) : ℝ :=
  L/(normIdeal p.C*normIdeal p.t)

def SecondTransferRInput.columnLength (p : SecondTransferRInput) (L : ℝ) : ℝ :=
  p.length L / normIdeal (p.g*p.w)

def SecondTransferRInput.cutoffs (p : SecondTransferRInput) (I : SupportInterval)
    (Φ : RowWeight) (cI H L F Sigma : ℝ) : Prop :=
  normIdeal p.C*normIdeal p.t ≤ 2*I.hi*L ∧
  normIdeal (p.g*p.w) ≤ (halfEnlarged I).hi*p.length L ∧
  normElement p.h ≤ Φ.fourierCap*(halfEnlarged I).hi^2*(p.length L)^2*normIdeal p.e /
    (p.rowScale cI H L F Sigma*normIdeal p.g^2)

abbrev SecondTransferRJointIndex (c : ArithmeticContext) :=
  SecondTransferRInput × RayCharacter c × Ideal O × Ideal O

/-- The literal joint summand, retaining every original arithmetic and
analytic cutoff of the nested Poisson expression. -/
def secondTransferRJointTerm (c : ArithmeticContext) (I : SupportInterval) (Φ : RowWeight)
    (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (v : SecondTransferRJointIndex c) : ℂ :=
  let p := v.1
  let ξ := v.2.1
  let n₁ := v.2.2.1
  let n₂ := v.2.2.2
  if p.admissible c ∧ p.cutoffs I Φ cI H L F Sigma ∧
      SquarefreeOutside c.S n₁ ∧ SquarefreeOutside c.S n₂ then
    (H*normIdeal p.C/(normIdeal p.d*L^2*F) : ℝ) *
      ((p.rowScale cI H L F Sigma : ℂ)*(mobius p.e : ℂ)*(mobius p.w : ℂ)*coeffs ξ*
        normIdeal p.g/((normIdeal p.e : ℂ)*p.length L)*
        (secondPoissonCoefficient c ξ p.C p.d p.t p.g p.e p.w p.h n₁ *
          star (secondPoissonCoefficient c ξ p.C p.d p.t p.g p.e p.w p.h n₂) *
          secondPoissonKernel Φ U (p.rowScale cI H L F Sigma) (p.length L) p.g p.e p.h
            (normIdeal n₁/p.columnLength L) (normIdeal n₂/p.columnLength L)))
  else 0

end QRHShort
end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort
namespace SecondTransferRNativeExpansion

theorem ite_tsum {ι : Type*} (P : Prop) [Decidable P] (f : ι → ℂ) :
    (if P then ∑' i, f i else 0) = ∑' i, if P then f i else 0 := by
  by_cases hP : P <;> simp [hP]

theorem ite_ite (P Q : Prop) [Decidable P] [Decidable Q] (z : ℂ) :
    (if P then (if Q then z else 0) else 0) = if P ∧ Q then z else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem guard_mul_tsum {ι : Type*} (P : Prop) [Decidable P] (a : ℂ) (f : ι → ℂ) :
    (if P then a * (∑' i, f i) else 0) = ∑' i, if P then a * f i else 0 := by
  rw [← tsum_mul_left, ite_tsum]

theorem guard_mul_mul_tsum {ι : Type*} (P : Prop) [Decidable P]
    (a b : ℂ) (f : ι → ℂ) :
    (if P then a * (b * (∑' i, f i)) else 0) =
      ∑' i, if P then (a * b) * f i else 0 := by
  rw [← mul_assoc, guard_mul_tsum]

theorem guard_mul_ite_tsum {ι : Type*} (P Q : Prop) [Decidable P] [Decidable Q]
    (a : ℂ) (f : ι → ℂ) :
    (if P then a * (if Q then ∑' i, f i else 0) else 0) =
      ∑' i, if P ∧ Q then a * f i else 0 := by
  rw [mul_ite, mul_zero, ite_ite, guard_mul_tsum]

theorem guard_mul_ite (P Q : Prop) [Decidable P] [Decidable Q] (a z : ℂ) :
    (if P then a * (if Q then z else 0) else 0) =
      if P ∧ Q then a * z else 0 := by
  rw [mul_ite, mul_zero, ite_ite]

end SecondTransferRNativeExpansion

set_option maxHeartbeats 800000 in
/-- Expansion in the original native order. This identity only moves scalar
factors and index-independent guards inside individual tsums. -/
theorem second_transfer_r_native_expansion (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ)
    (cI H L F Sigma : ℝ) :
    secondTransferDual c I Φ U coeffs cI H L F Sigma =
      ∑' C : Ideal O, ∑' t : Ideal O, ∑' d : Ideal O, ∑' g : Ideal O,
        ∑' e : Ideal O, ∑' w : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c,
          ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
            secondTransferRJointTerm c I Φ U coeffs cI H L F Sigma
              (({C := C, d := d, t := t, g := g, e := e, w := w, h := h} :
                SecondTransferRInput), ξ, n₁, n₂) := by
  unfold secondTransferDual
  apply tsum_congr
  intro C
  apply tsum_congr
  intro t
  rw [SecondTransferRNativeExpansion.ite_tsum]
  apply tsum_congr
  intro d
  rw [SecondTransferRNativeExpansion.ite_ite]
  unfold secondPoissonDual
  rw [SecondTransferRNativeExpansion.guard_mul_tsum]
  apply tsum_congr
  intro g
  rw [SecondTransferRNativeExpansion.guard_mul_ite_tsum]
  apply tsum_congr
  intro e
  rw [SecondTransferRNativeExpansion.guard_mul_ite_tsum]
  apply tsum_congr
  intro w
  rw [SecondTransferRNativeExpansion.guard_mul_ite_tsum]
  apply tsum_congr
  intro h
  rw [SecondTransferRNativeExpansion.guard_mul_ite_tsum]
  apply tsum_congr
  intro ξ
  rw [SecondTransferRNativeExpansion.guard_mul_mul_tsum]
  apply tsum_congr
  intro n₁
  rw [SecondTransferRNativeExpansion.guard_mul_ite_tsum]
  apply tsum_congr
  intro n₂
  rw [SecondTransferRNativeExpansion.guard_mul_ite]
  simp only [secondTransferRJointTerm, SecondTransferRInput.admissible,
    SecondTransferRInput.cutoffs, SecondTransferRInput.rowScale,
    SecondTransferRInput.length, SecondTransferRInput.columnLength]
  congr 1
  · apply propext
    tauto
  · exact mul_assoc _ _ _

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def SecondTransferRLabel.bounded {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (I : SupportInterval) (H L F Sigma : ℝ) : Prop :=
  normIdeal z.excluded*normIdeal z.twist ≤ 2*I.hi*L ∧
  normElement z.frequency ≤ H*L/(Sigma*F*normIdeal z.excluded^2)

theorem second_transfer_r_bounded_labels_finite (c : ArithmeticContext)
    (I : SupportInterval) (H L F Sigma : ℝ)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma) :
    {z : SecondTransferRLabel c | z.bounded I H L F Sigma}.Finite := by
  let enc (z : SecondTransferRLabel c) := (z.excluded,z.twist,z.frequency)
  let A := {r : Ideal O | normIdeal r ≤ 2*I.hi*L} ×ˢ
    ({f : Ideal O | normIdeal f ≤ 2*I.hi*L} ×ˢ
      {k : O | normElement k ≤ H*L/(Sigma*F)})
  have hA : A.Finite := (finite_normIdeal_le _).prod
    ((finite_normIdeal_le _).prod (finite_normElement_le _))
  have hm : Set.MapsTo enc {z | z.bounded I H L F Sigma} A := by
    intro z hz
    have hr := SecondTransferRNormKernel.norm_one_le_of_ne_bot z.excluded_outside.1.1
    have hf := SecondTransferRNormKernel.norm_one_le_of_ne_bot z.twist_outside.1.1
    refine ⟨(le_mul_of_one_le_right (zero_le_one.trans hr) hf).trans hz.1,
      (le_mul_of_one_le_left (zero_le_one.trans hf) hr).trans hz.1,?_⟩
    apply hz.2.trans
    exact div_le_div_of_nonneg_left (mul_pos hH hL).le (mul_pos hSigma hF)
      (le_mul_of_one_le_right (mul_pos hSigma hF).le (one_le_pow₀ hr))
  have hi : Set.InjOn enc {z | z.bounded I H L F Sigma} := by
    intro z _ w _ h
    dsimp only [enc] at h
    simp only [Prod.mk.injEq] at h
    exact SecondTransferRLabel.ext h.1 h.2.1 h.2.2
  exact Set.Finite.of_injOn hm hi hA

theorem second_transfer_r_columnLength_bounds (c : ArithmeticContext)
    (p : SecondTransferRInput) (hp : p.admissible c) {L : ℝ} (hL : 0 < L) :
    0 < p.columnLength L ∧ p.columnLength L ≤ L := by
  obtain ⟨hC,ht,_,_,hg,_,_,hw,_,_⟩ := hp
  have hct : 1 ≤ normIdeal p.C*normIdeal p.t :=
    one_le_mul_of_one_le_of_one_le
      (SecondTransferRNormKernel.norm_one_le_of_ne_bot hC.1.1)
      (SecondTransferRNormKernel.norm_one_le_of_ne_bot ht.1.1)
  have hgw : 1 ≤ normIdeal (p.g*p.w) := by
    rw [normIdeal_mul]
    exact one_le_mul_of_one_le_of_one_le
      (SecondTransferRNormKernel.norm_one_le_of_ne_bot hg.1.1)
      (SecondTransferRNormKernel.norm_one_le_of_ne_bot hw.1.1)
  have hell : 0 < p.length L := div_pos hL (zero_lt_one.trans_le hct)
  exact ⟨div_pos hell (zero_lt_one.trans_le hgw),
    (div_le_self hell.le hgw).trans (div_le_self hL.le hct)⟩

theorem second_transfer_r_kernel_support_window (c : ArithmeticContext)
    (p : SecondTransferRInput) (hp : p.admissible c)
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (cI H L F Sigma : ℝ) (hU : SmoothSupported (halfEnlarged I) U)
    (hcI : max 1 (4*Φ.fourierCap*I.hi^2) ≤ cI)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (hgw : normIdeal (p.g*p.w) ≤ (halfEnlarged I).hi*p.length L)
    (n₁ n₂ : Ideal O) (hn₁ : SquarefreeOutside c.S n₁) (hn₂ : SquarefreeOutside c.S n₂)
    (hk : secondPoissonKernel Φ U (p.rowScale cI H L F Sigma) (p.length L) p.g p.e p.h
      (normIdeal n₁/p.columnLength L) (normIdeal n₂/p.columnLength L) ≠ 0) :
    (p.label hp).bounded I H L F Sigma ∧
      n₁ ∈ boundedDivisibleIdeals 1 (2*I.hi*L) ∧
      n₂ ∈ boundedDivisibleIdeals 1 (2*I.hi*L) := by
  have hpadm := hp
  obtain ⟨hC,ht,_,hd,hg,_,he,_,_,_⟩ := hp
  have hcI0 : 0 < cI := zero_lt_one.trans_le ((le_max_left _ _).trans hcI)
  have hs := second_transfer_r_columnLength_bounds c p hpadm hL
  have hx₁ : 0 < normIdeal n₁/p.columnLength L := div_pos (normIdeal_pos hn₁.1.1) hs.1
  have hx₂ : 0 < normIdeal n₂/p.columnLength L := div_pos (normIdeal_pos hn₂.1.1) hs.1
  have hstrong := SecondTransferRNormKernel.normalized_cutoff c hC.1 ht.1 hg.1 hd he
    p.h I Φ U hU cI H L F Sigma hcI0 hH hL hF hSigma hx₁ hx₂ hk
  have hout := second_transfer_r_input_output c p hpadm
  have hr0 := normIdeal_pos hout.1.1.1
  have hweak := SecondTransferRNormKernel.strong_cutoff_implies_weak
    hH hL hF hSigma hcI0 hr0 ((le_max_right _ _).trans hcI) hstrong
  have hproduct := (SecondTransferRNormKernel.raw_cutoff_iff c hC.1 ht.1 hg.1 he
    p.w I L).mp hgw
  have hu₁ : U (normIdeal n₁/p.columnLength L) ≠ 0 := by
    intro hz
    exact hk (by simp only [secondPoissonKernel,hz,mul_zero,zero_mul])
  have hu₂ : U (normIdeal n₂/p.columnLength L) ≠ 0 := by
    intro hz
    exact hk (by simp only [secondPoissonKernel,hz,mul_zero,star_zero,zero_mul])
  have cols (n : Ideal O) (hn : SquarefreeOutside c.S n)
      (hu : U (normIdeal n/p.columnLength L) ≠ 0) :
      n ∈ boundedDivisibleIdeals 1 (2*I.hi*L) := by
    have hhi := (hU.2 hu).2
    change normIdeal n/p.columnLength L ≤ 2*I.hi at hhi
    have hI : 0 < I.hi := I.lo_pos.trans_le I.ordered
    exact mem_boundedDivisibleIdeals.mpr
      ⟨((div_le_iff₀ hs.1).mp hhi).trans (mul_le_mul_of_nonneg_left hs.2 (by positivity)),
        one_dvd _,hn.1.1⟩
  exact ⟨⟨hproduct,hweak⟩, cols n₁ hn₁ hu₁,cols n₂ hn₂ hu₂⟩

theorem second_transfer_r_joint_hasFiniteSupport (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hU : SmoothSupported (halfEnlarged I) U)
    (hcoeffs : (Function.support coeffs).Finite)
    (hcI : max 1 (4*Φ.fourierCap*I.hi^2) ≤ cI)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma) :
    Function.HasFiniteSupport (secondTransferRJointTerm c I Φ U coeffs cI H L F Sigma) := by
  let labels := {z : SecondTransferRLabel c | z.bounded I H L F Sigma}
  have hl : labels.Finite := second_transfer_r_bounded_labels_finite c I H L F Sigma
    hH hL hF hSigma
  let raw := {p : {p : SecondTransferRInput // p.admissible c} | p.1.label p.2 ∈ labels}
  have hr : raw.Finite := second_transfer_r_inputs_finite_of_labels c labels hl
  let cols := boundedDivisibleIdeals 1 (2*I.hi*L)
  have hb := (hr.image (fun p => p.1)).prod
    (hcoeffs.prod (cols.finite_toSet.prod cols.finite_toSet))
  apply hb.subset
  rintro ⟨p,ξ,n₁,n₂⟩ hv
  have hg : p.admissible c ∧ p.cutoffs I Φ cI H L F Sigma ∧
      SquarefreeOutside c.S n₁ ∧ SquarefreeOutside c.S n₂ := by
    by_contra h
    exact hv (by simp [secondTransferRJointTerm,h])
  have hξ : coeffs ξ ≠ 0 := by
    intro hz
    exact hv (by simp [secondTransferRJointTerm,hg,hz])
  have hk : secondPoissonKernel Φ U (p.rowScale cI H L F Sigma) (p.length L) p.g p.e p.h
      (normIdeal n₁/p.columnLength L) (normIdeal n₂/p.columnLength L) ≠ 0 := by
    intro hz
    exact hv (by simp [secondTransferRJointTerm,hg,hz])
  have hw := second_transfer_r_kernel_support_window c p hg.1 I Φ U cI H L F Sigma hU
    hcI hH hL hF hSigma hg.2.1.2.1 n₁ n₂ hg.2.2.1 hg.2.2.2 hk
  exact ⟨⟨⟨p,hg.1⟩,hw.1,rfl⟩,hξ,hw.2.1,hw.2.2⟩

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

abbrev SecondTransferRNativeIndex (c : ArithmeticContext) :=
  Ideal O × Ideal O × Ideal O × Ideal O × Ideal O × Ideal O × O ×
    RayCharacter c × Ideal O × Ideal O

def secondTransferRJointEquiv (c : ArithmeticContext) :
    SecondTransferRJointIndex c ≃ SecondTransferRNativeIndex c where
  toFun := fun | (⟨C,d,t,g,e,w,h⟩,ξ,n₁,n₂) => (C,t,d,g,e,w,h,ξ,n₁,n₂)
  invFun := fun | (C,t,d,g,e,w,h,ξ,n₁,n₂) => (⟨C,d,t,g,e,w,h⟩,ξ,n₁,n₂)
  left_inv := by rintro ⟨⟨C,d,t,g,e,w,h⟩,ξ,n₁,n₂⟩; rfl
  right_inv := by rintro ⟨C,t,d,g,e,w,h,ξ,n₁,n₂⟩; rfl

/-- This flattening uses joint summability at every stage. No interchange of
totalized nonsummable series is used. -/
theorem second_transfer_r_joint_tsum_eq_native (c : ArithmeticContext)
    (F : SecondTransferRJointIndex c → ℂ) (hF : Function.HasFiniteSupport F) :
    (∑' v, F v) =
      ∑' C : Ideal O, ∑' t : Ideal O, ∑' d : Ideal O, ∑' g : Ideal O,
      ∑' e : Ideal O, ∑' w : Ideal O, ∑' h : O, ∑' ξ : RayCharacter c,
      ∑' n₁ : Ideal O, ∑' n₂ : Ideal O, F (⟨C,d,t,g,e,w,h⟩,ξ,n₁,n₂) := by
  let G : SecondTransferRNativeIndex c → ℂ := F ∘ (secondTransferRJointEquiv c).symm
  have hs : Summable G :=
    (summable_of_hasFiniteSupport hF).comp_injective (secondTransferRJointEquiv c).symm.injective
  calc
    _ = ∑' v, G v := ((secondTransferRJointEquiv c).symm.tsum_eq F).symm
    _ = _ := by
      rw [hs.tsum_prod]
      apply tsum_congr; intro C
      have h1 := hs.prod_factor C
      rw [h1.tsum_prod]
      apply tsum_congr; intro t
      have h2 := h1.prod_factor t
      rw [h2.tsum_prod]
      apply tsum_congr; intro d
      have h3 := h2.prod_factor d
      rw [h3.tsum_prod]
      apply tsum_congr; intro g
      have h4 := h3.prod_factor g
      rw [h4.tsum_prod]
      apply tsum_congr; intro e
      have h5 := h4.prod_factor e
      rw [h5.tsum_prod]
      apply tsum_congr; intro w
      have h6 := h5.prod_factor w
      rw [h6.tsum_prod]
      apply tsum_congr; intro h
      have h7 := h6.prod_factor h
      rw [h7.tsum_prod]
      apply tsum_congr; intro ξ
      have h8 := h7.prod_factor ξ
      rw [h8.tsum_prod]
      rfl

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

def SecondTransferRLabel.index {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (ξ : RayCharacter c) (rb fb : ℕ) : SecondTransferIndex c :=
  ⟨ξ,z.excluded,z.twist,z.frequency,rb,fb⟩

def SecondTransferRLabel.length {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (L : ℝ) : ℝ := L/(normIdeal z.excluded*normIdeal z.twist)

def SecondTransferRLabel.parameter {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (cI H L F Sigma : ℝ) : ℝ :=
  cI*Sigma*F*normElement z.frequency*normIdeal z.excluded^2/(H*L)

def secondTransferRCanonicalPair {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ) (n₁ n₂ : Ideal O) : ℂ :=
  (cI*Sigma*normIdeal z.excluded/L^2 : ℝ)*coeffs ξ*
    (secondTransferPRMRColumn c (z.index ξ 0 0) n₁ *
      star (secondTransferPRMRColumn c (z.index ξ 0 0) n₂) *
      secondTransferKernel Φ U 1 (z.parameter cI H L F Sigma)
        ![normIdeal n₁/z.length L,normIdeal n₂/z.length L])

def SecondTransferRLabel.cutoffs {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (I : SupportInterval) (H L F Sigma : ℝ) : Prop :=
  normIdeal z.excluded*normIdeal z.twist ≤ 2*I.hi*L ∧
  normElement z.frequency ≤ H*L/(Sigma*F*normIdeal z.excluded^2)

def secondTransferRCanonicalTerm {c : ArithmeticContext} (z : SecondTransferRLabel c)
    (ξ : RayCharacter c) (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ) (n₁ n₂ : Ideal O) : ℂ :=
  if z.cutoffs I H L F Sigma then
    secondTransferRCanonicalPair z ξ I Φ U coeffs cI H L F Sigma n₁ n₂ else 0

theorem second_transfer_r_canonical_column (c : ArithmeticContext)
    (p : SecondTransferRInput) (hp : p.admissible c) (ξ : RayCharacter c) (n : Ideal O) :
    (if SquarefreeOutside c.S n then
      secondPoissonCoefficient c ξ p.C p.d p.t p.g p.e p.w p.h n else 0) =
      secondTransferPRMRColumn c ((p.label hp).index ξ 0 0) n :=
  second_transfer_r_column_identification c ξ p.C p.d p.t p.g p.e p.w p.h 0 0 n

theorem second_transfer_r_canonical_kernel (c : ArithmeticContext)
    (p : SecondTransferRInput) (hp : p.admissible c)
    (Φ : RowWeight) (U : ℝ → ℂ) (cI H L F Sigma : ℝ)
    (hH : 0 < H) (hL : 0 < L) (n₁ n₂ : Ideal O) :
    secondPoissonKernel Φ U
      (cI*Sigma*L*F*normIdeal p.d/(H*normIdeal p.C^2))
      (L/(normIdeal p.C*normIdeal p.t)) p.g p.e p.h
      (normIdeal n₁/((L/(normIdeal p.C*normIdeal p.t))/normIdeal (p.g*p.w)))
      (normIdeal n₂/((L/(normIdeal p.C*normIdeal p.t))/normIdeal (p.g*p.w))) =
    secondTransferKernel Φ U 1 ((p.label hp).parameter cI H L F Sigma)
      ![normIdeal n₁/(p.label hp).length L,normIdeal n₂/(p.label hp).length L] := by
  have hlength := SecondTransferRNormKernel.normalized_length c hp.1.1 hp.2.1.1
    hp.2.2.2.2.1.1 hp.2.2.2.2.2.2.1 p.w L
  rw [hlength]
  simpa only [one_mul, one_pow, div_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, SecondTransferRLabel.length, SecondTransferRLabel.parameter,
    SecondTransferRInput.label, SecondTransferRInput.excluded, SecondTransferRInput.twist,
    SecondTransferRInput.frequency] using
    (SecondTransferRNormKernel.kernel_identification c hp.1.1 hp.2.1.1
      hp.2.2.2.2.1.1 hp.2.2.2.1 hp.2.2.2.2.2.2.1 p.h Φ U cI H L F Sigma 1 hH hL
      ![normIdeal n₁/(p.label hp).length L,normIdeal n₂/(p.label hp).length L])

theorem second_transfer_r_canonical_weight (c : ArithmeticContext)
    (p : SecondTransferRInput) (hp : p.admissible c) (cI H L F Sigma : ℝ)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) :
    ((H*normIdeal p.C/(normIdeal p.d*L^2*F) : ℝ) : ℂ) *
      (((cI*Sigma*L*F*normIdeal p.d/(H*normIdeal p.C^2) : ℝ) : ℂ)*
        (normIdeal p.g : ℂ)/((normIdeal p.e : ℂ)*(L/(normIdeal p.C*normIdeal p.t) : ℝ))) =
    (cI*Sigma*normIdeal (p.label hp).excluded/L^2 : ℝ) := by
  exact_mod_cast SecondTransferRNormKernel.normalized_weight c hp.1.1 hp.2.1.1
    hp.2.2.2.2.1.1 hp.2.2.2.1 hp.2.2.2.2.2.2.1 cI H L F Sigma hH hL hF

/-- The complete arithmetic coefficient and literal kernel become independent
of the preimage except for its two Mobius signs. -/
theorem second_transfer_r_canonical_pair (c : ArithmeticContext)
    (p : SecondTransferRInput) (hp : p.admissible c) (ξ : RayCharacter c)
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ)
    (cI H L F Sigma : ℝ) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (n₁ n₂ : Ideal O) (hn₁ : SquarefreeOutside c.S n₁) (hn₂ : SquarefreeOutside c.S n₂) :
    ((H*normIdeal p.C/(normIdeal p.d*L^2*F) : ℝ) : ℂ) *
      (((cI*Sigma*L*F*normIdeal p.d/(H*normIdeal p.C^2) : ℝ) : ℂ)*
        (mobius p.e : ℂ)*(mobius p.w : ℂ)*coeffs ξ*normIdeal p.g /
        ((normIdeal p.e : ℂ)*(L/(normIdeal p.C*normIdeal p.t) : ℝ)) *
        (secondPoissonCoefficient c ξ p.C p.d p.t p.g p.e p.w p.h n₁ *
          star (secondPoissonCoefficient c ξ p.C p.d p.t p.g p.e p.w p.h n₂) *
          secondPoissonKernel Φ U
            (cI*Sigma*L*F*normIdeal p.d/(H*normIdeal p.C^2))
            (L/(normIdeal p.C*normIdeal p.t)) p.g p.e p.h
            (normIdeal n₁/((L/(normIdeal p.C*normIdeal p.t))/normIdeal (p.g*p.w)))
            (normIdeal n₂/((L/(normIdeal p.C*normIdeal p.t))/normIdeal (p.g*p.w))))) =
      (mobius p.e : ℂ)*(mobius p.w : ℂ)*
        secondTransferRCanonicalPair (p.label hp) ξ I Φ U coeffs cI H L F Sigma n₁ n₂ := by
  have h₁ := second_transfer_r_canonical_column c p hp ξ n₁
  have h₂ := second_transfer_r_canonical_column c p hp ξ n₂
  rw [if_pos hn₁] at h₁
  rw [if_pos hn₂] at h₂
  rw [h₁,h₂,second_transfer_r_canonical_kernel c p hp Φ U cI H L F Sigma hH hL]
  unfold secondTransferRCanonicalPair
  rw [← second_transfer_r_canonical_weight c p hp cI H L F Sigma hH hL hF]
  ring

/-- Dyadic normalization changes neither the actual two-column test nor its
Fourier argument, including all totalized zero cases. -/
theorem second_transfer_r_kernel_scale (Φ : RowWeight) (U : ℝ → ℂ)
    (rho B : ℝ) (x : BoxSpace 2) :
    secondTransferKernel Φ U rho (B/rho^2) x =
      secondTransferKernel Φ U 1 B (fun i => rho*x i) := by
  unfold secondTransferKernel
  simp only [one_mul]
  congr 2
  simp only [div_div]
  congr 1
  ring

end QRHShort

end


noncomputable section
open Classical

namespace QRHShort.SecondTransferRNormKernel

/-- The original h-window and the canonical strong frequency window agree
under the literal frequency and excluded-ideal maps. -/
theorem raw_frequency_cutoff_iff (c : ArithmeticContext) {C d t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g)
    (hd : d ∣ C) (he : e ∣ g) (h : O) (I : SupportInterval) (Φ : RowWeight)
    (cI H L F Sigma : ℝ) (hcI : 0 < cI) (hH : 0 < H) (hL : 0 < L)
    (hF : 0 < F) (hSigma : 0 < Sigma) :
    normElement h ≤
        Φ.fourierCap * (halfEnlarged I).hi ^ 2 *
          (L / (normIdeal C * normIdeal t)) ^ 2 * normIdeal e /
            ((cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2)) *
              normIdeal g ^ 2) ↔
      normElement (primaryGenerator (d * e) * h) ≤
        (4 * Φ.fourierCap * I.hi ^ 2 / cI) * H * L /
          (Sigma * F * normIdeal (t * quotientIdeal g e) ^ 2) := by
  have hdout := second_transfer_r_outside_dvd hC hd
  have heout := second_transfer_r_outside_dvd hg he
  have hNC := normIdeal_pos hC.1
  have hNd := normIdeal_pos hdout.1
  have hNt := normIdeal_pos ht.1
  have hNg := normIdeal_pos hg.1
  have hNe := normIdeal_pos heout.1
  rw [frequency_norm c hC hg hd he, excluded_norm c hg he]
  have hbound : (4 * Φ.fourierCap * I.hi ^ 2 / cI) * H * L /
        (Sigma * F * (normIdeal t * normIdeal g / normIdeal e) ^ 2) =
      (normIdeal d * normIdeal e) *
        (Φ.fourierCap * (halfEnlarged I).hi ^ 2 *
          (L / (normIdeal C * normIdeal t)) ^ 2 * normIdeal e /
            ((cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2)) *
              normIdeal g ^ 2)) := by
    dsimp only [halfEnlarged]
    field_simp [hcI.ne', hH.ne', hL.ne', hF.ne', hSigma.ne',
      hNC.ne', hNd.ne', hNt.ne', hNg.ne', hNe.ne']
    <;> ring
  rw [hbound]
  exact (mul_le_mul_iff_right₀ (mul_pos hNd hNe)).symm

/-- Failure of the strong window annihilates the literal two-column kernel.
No weaker arithmetic cutoff is needed for this pointwise statement. -/
theorem raw_kernel_eq_zero_of_not_strong (c : ArithmeticContext) {C d t g e : Ideal O}
    (hC : Outside c.S C) (ht : Outside c.S t) (hg : Outside c.S g)
    (hd : d ∣ C) (he : e ∣ g) (h : O) (I : SupportInterval) (Φ : RowWeight)
    (U : ℝ → ℂ) (hU : SmoothSupported (halfEnlarged I) U)
    (cI H L F Sigma : ℝ) (hcI : 0 < cI) (hH : 0 < H) (hL : 0 < L)
    (hF : 0 < F) (hSigma : 0 < Sigma)
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hnot : ¬ normElement (primaryGenerator (d * e) * h) ≤
      (4 * Φ.fourierCap * I.hi ^ 2 / cI) * H * L /
        (Sigma * F * normIdeal (t * quotientIdeal g e) ^ 2)) :
    secondPoissonKernel Φ U
      (cI * Sigma * L * F * normIdeal d / (H * normIdeal C ^ 2))
      (L / (normIdeal C * normIdeal t)) g e h x₁ x₂ = 0 := by
  by_contra hkernel
  exact hnot (normalized_cutoff c hC ht hg hd he h I Φ U hU
    cI H L F Sigma hcI hH hL hF hSigma hx₁ hx₂ hkernel)

end QRHShort.SecondTransferRNormKernel

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

/-- The weaker arithmetic frequency cutoff adds only terms whose actual
Fourier kernel vanishes. The original three cutoffs are all accounted for. -/
theorem second_transfer_r_joint_pointwise (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (hU : SmoothSupported (halfEnlarged I) U) (coeffs : RayCharacter c → ℂ)
    (cI H L F Sigma : ℝ) (hcI : max 1 (4*Φ.fourierCap*I.hi^2) ≤ cI)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (p : SecondTransferRInput) (hp : p.admissible c) (ξ : RayCharacter c)
    (n₁ n₂ : Ideal O) :
    secondTransferRJointTerm c I Φ U coeffs cI H L F Sigma (p,ξ,n₁,n₂) =
      (mobius p.e : ℂ)*(mobius p.w : ℂ)*
        secondTransferRCanonicalTerm (p.label hp) ξ I Φ U coeffs cI H L F Sigma n₁ n₂ := by
  have hz₁ (hn : ¬ SquarefreeOutside c.S n₁) :
      secondTransferPRMRColumn c ((p.label hp).index ξ 0 0) n₁ = 0 := by
    simp [secondTransferPRMRColumn,hn]
  have hz₂ (hn : ¬ SquarefreeOutside c.S n₂) :
      secondTransferPRMRColumn c ((p.label hp).index ξ 0 0) n₂ = 0 := by
    simp [secondTransferPRMRColumn,hn]
  by_cases hn₁ : SquarefreeOutside c.S n₁
  swap
  · simp [secondTransferRJointTerm,hn₁,secondTransferRCanonicalTerm,
      secondTransferRCanonicalPair,hz₁ hn₁]
  by_cases hn₂ : SquarefreeOutside c.S n₂
  swap
  · simp [secondTransferRJointTerm,hn₂,secondTransferRCanonicalTerm,
      secondTransferRCanonicalPair,hz₂ hn₂]
  have hknorm := second_transfer_r_canonical_kernel c p hp Φ U cI H L F Sigma hH hL n₁ n₂
  change secondPoissonKernel Φ U (p.rowScale cI H L F Sigma) (p.length L) p.g p.e p.h
      (normIdeal n₁/p.columnLength L) (normIdeal n₂/p.columnLength L) = _ at hknorm
  by_cases hk : secondPoissonKernel Φ U (p.rowScale cI H L F Sigma) (p.length L) p.g p.e p.h
      (normIdeal n₁/p.columnLength L) (normIdeal n₂/p.columnLength L) = 0
  · have hcan := hknorm.symm.trans hk
    simp [secondTransferRJointTerm,hk,secondTransferRCanonicalTerm,
      secondTransferRCanonicalPair,hcan]
  have hC := hp.1.1
  have ht := hp.2.1.1
  have hg := hp.2.2.2.2.1.1
  have hd := hp.2.2.2.1
  have he := hp.2.2.2.2.2.2.1
  have hw := hp.2.2.2.2.2.2.2.1.1
  have hcIp : 0 < cI := zero_lt_one.trans_le ((le_max_left _ _).trans hcI)
  have hell : 0 < p.length L :=
    div_pos hL (mul_pos (normIdeal_pos hC.1) (normIdeal_pos ht.1))
  have hcol : 0 < p.columnLength L :=
    div_pos hell (normIdeal_pos (mul_ne_zero hg.1 hw.1))
  have hx₁ : 0 < normIdeal n₁/p.columnLength L := div_pos (normIdeal_pos hn₁.1.1) hcol
  have hx₂ : 0 < normIdeal n₂/p.columnLength L := div_pos (normIdeal_pos hn₂.1.1) hcol
  have hstrong := SecondTransferRNormKernel.normalized_cutoff c hC ht hg hd he p.h I Φ U hU
    cI H L F Sigma hcIp hH hL hF hSigma hx₁ hx₂ hk
  have hweak : normElement (p.label hp).frequency ≤
      H*L/(Sigma*F*normIdeal (p.label hp).excluded^2) :=
    SecondTransferRNormKernel.strong_cutoff_implies_weak hH hL hF hSigma hcIp
      (normIdeal_pos (p.label hp).excluded_outside.1.1)
      ((le_max_right _ _).trans hcI) hstrong
  have hrawh : normElement p.h ≤
      Φ.fourierCap*(halfEnlarged I).hi^2*(p.length L)^2*normIdeal p.e /
        (p.rowScale cI H L F Sigma*normIdeal p.g^2) := by
    exact (SecondTransferRNormKernel.raw_frequency_cutoff_iff c hC ht hg hd he p.h
      I Φ cI H L F Sigma hcIp hH hL hF hSigma).mpr hstrong
  have hcuts : p.cutoffs I Φ cI H L F Sigma ↔ (p.label hp).cutoffs I H L F Sigma := by
    constructor
    · intro hh
      refine ⟨?_,hweak⟩
      exact (SecondTransferRNormKernel.raw_cutoff_iff c hC ht hg he p.w I L).mp hh.2.1
    · intro hh
      have hgw := (SecondTransferRNormKernel.raw_cutoff_iff c hC ht hg he p.w I L).mpr hh.1
      exact ⟨SecondTransferRNormKernel.outer_cutoff_of_raw c hC ht hg he hw.1 I L hgw,
        hgw,hrawh⟩
  have hpair := second_transfer_r_canonical_pair c p hp ξ I Φ U coeffs
    cI H L F Sigma hH hL hF n₁ n₂ hn₁ hn₂
  by_cases hcut : p.cutoffs I Φ cI H L F Sigma
  · simpa only [secondTransferRJointTerm,hp,hcut,hn₁,hn₂,and_self,ite_true,
      secondTransferRCanonicalTerm,if_pos (hcuts.mp hcut),SecondTransferRInput.rowScale,
      SecondTransferRInput.length,SecondTransferRInput.columnLength] using hpair
  · have hcut' : ¬ (p.label hp).cutoffs I H L F Sigma := fun h => hcut (hcuts.mpr h)
    simp only [secondTransferRJointTerm,hp,hcut,false_and,and_false,ite_false,
      secondTransferRCanonicalTerm,if_neg hcut',mul_zero]

end QRHShort

end


noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The integral signed fiber identity, transported through the genuine finite
fiber into the literal complex coefficients. -/
theorem second_transfer_r_signed_frequency_fiber_complex (c : ArithmeticContext)
    (z : SecondTransferRLabel c) :
    (∑' p : SecondTransferRFrequencyFiber z.excluded z.twist z.frequency,
      (mobius p.1.1.e : ℂ) * (mobius p.1.1.w : ℂ)) =
      (divisorCount z.excluded : ℂ) *
        (if z.twist ∣ principal z.frequency then 1 else 0) := by
  letI := second_transfer_r_frequency_fiber_finite c z.excluded_outside.1.1
    z.twist_outside z.frequency
  letI := Fintype.ofFinite (SecondTransferRFrequencyFiber z.excluded z.twist z.frequency)
  have h := second_transfer_r_signed_frequency_fiber c z.excluded_outside.1.1
    z.twist_outside z.frequency
  rw [tsum_fintype] at h ⊢
  have hh := congrArg (fun n : ℤ => (n : ℂ)) h
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_ite,
    Int.cast_one, Int.cast_zero] using hh

/-- Finite label support gives finite support on the entire original arithmetic
range, including all divisor choices and all literal frequency lifts. -/
theorem second_transfer_r_signed_pullback_hasFiniteSupport (c : ArithmeticContext)
    (A : SecondTransferRLabel c → ℂ) (hA : A.HasFiniteSupport) :
    (fun p : {p : SecondTransferRInput // p.admissible c} =>
      (mobius p.1.e : ℂ) * (mobius p.1.w : ℂ) * A (p.1.label p.2)).HasFiniteSupport := by
  apply (second_transfer_r_inputs_finite_of_labels c (Function.support A) hA).subset
  intro p hp
  exact fun hz => hp (by simp only [hz, mul_zero])

/-- Exact signed regrouping of the actual Poisson preimages. All reindexing
and sigma summation take place in a genuinely finite support. -/
theorem second_transfer_r_signed_regroup (c : ArithmeticContext)
    (A : SecondTransferRLabel c → ℂ) (hA : A.HasFiniteSupport) :
    (∑' p : {p : SecondTransferRInput // p.admissible c},
      (mobius p.1.e : ℂ) * (mobius p.1.w : ℂ) * A (p.1.label p.2)) =
      ∑' z : SecondTransferRLabel c,
        (divisorCount z.excluded : ℂ) *
          (if z.twist ∣ principal z.frequency then 1 else 0) * A z := by
  let E := secondTransferRRawEquiv c
  let G : (Σ z : SecondTransferRLabel c,
      SecondTransferRFrequencyFiber z.excluded z.twist z.frequency) → ℂ :=
    fun p => (mobius p.2.1.1.e : ℂ) * (mobius p.2.1.1.w : ℂ) * A p.1
  have hraw := second_transfer_r_signed_pullback_hasFiniteSupport c A hA
  have hG : G.HasFiniteSupport := by
    apply (hraw.image E).subset
    intro p hp
    refine ⟨E.symm p, ?_, E.apply_symm_apply p⟩
    change G (E (E.symm p)) ≠ 0
    simpa only [E.apply_symm_apply] using (Function.mem_support.mp hp)
  have hGs : Summable G := summable_of_hasFiniteSupport hG
  calc
    _ = ∑' p, G p := E.tsum_eq G
    _ = ∑' z, ∑' p : SecondTransferRFrequencyFiber z.excluded z.twist z.frequency,
        (mobius p.1.1.e : ℂ) * (mobius p.1.1.w : ℂ) * A z :=
      hGs.tsum_sigma
    _ = _ := by
      apply tsum_congr
      intro z
      rw [tsum_mul_right, second_transfer_r_signed_frequency_fiber_complex c z]

end QRHShort

end


noncomputable section
open Classical

namespace QRHShort

/-- The half-open dyadic interval of a real number at least one is unique. -/
theorem second_transfer_r_dyadic_exists_unique {x : ℝ} (hx : 1 ≤ x) :
    ∃! n : ℕ, (2 : ℝ)^n ≤ x ∧ x < 2*(2 : ℝ)^n := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hx (show (1 : ℝ) < 2 by norm_num)
  have hnhi' : x < 2*(2 : ℝ)^n := by simpa only [pow_succ, mul_comm] using hnhi
  refine ⟨n, ⟨hnlo, hnhi'⟩, ?_⟩
  intro m hm
  have hmn : (2 : ℝ)^m < (2 : ℝ)^(n+1) := hm.1.trans_lt hnhi
  have hnm : (2 : ℝ)^n < (2 : ℝ)^(m+1) := by
    apply hnlo.trans_lt
    simpa only [pow_succ, mul_comm] using hm.2
  exact Nat.le_antisymm
    (Nat.lt_succ_iff.mp ((pow_lt_pow_iff_right₀ (show (1 : ℝ) < 2 by norm_num)).mp hmn))
    (Nat.lt_succ_iff.mp ((pow_lt_pow_iff_right₀ (show (1 : ℝ) < 2 by norm_num)).mp hnm))

def secondTransferRDyadicBlock (x : ℝ) (hx : 1 ≤ x) : ℕ :=
  Classical.choose (second_transfer_r_dyadic_exists_unique hx).exists

theorem second_transfer_r_dyadic_block_spec (x : ℝ) (hx : 1 ≤ x) :
    (2 : ℝ)^secondTransferRDyadicBlock x hx ≤ x ∧
      x < 2*(2 : ℝ)^secondTransferRDyadicBlock x hx :=
  Classical.choose_spec (second_transfer_r_dyadic_exists_unique hx).exists

theorem second_transfer_r_dyadic_block_eq {x : ℝ} (hx : 1 ≤ x) {n : ℕ}
    (hn : (2 : ℝ)^n ≤ x ∧ x < 2*(2 : ℝ)^n) :
    secondTransferRDyadicBlock x hx = n :=
  (second_transfer_r_dyadic_exists_unique hx).unique
    (second_transfer_r_dyadic_block_spec x hx) hn

theorem second_transfer_r_ideal_blocks_unique {r f : Ideal O} (hr : r ≠ ⊥) (hf : f ≠ ⊥) :
    ∃! b : ℕ × ℕ,
      (2 : ℝ)^b.1 ≤ normIdeal r ∧ normIdeal r < 2*(2 : ℝ)^b.1 ∧
      (2 : ℝ)^b.2 ≤ normIdeal f ∧ normIdeal f < 2*(2 : ℝ)^b.2 := by
  obtain ⟨rb, hrb, hru⟩ := second_transfer_r_dyadic_exists_unique (second_transfer_prmr_one_le_norm hr)
  obtain ⟨fb, hfb, hfu⟩ := second_transfer_r_dyadic_exists_unique (second_transfer_prmr_one_le_norm hf)
  refine ⟨(rb,fb), ⟨hrb.1, hrb.2, hfb.1, hfb.2⟩, ?_⟩
  intro b hb
  exact Prod.ext (hru b.1 ⟨hb.1, hb.2.1⟩) (hfu b.2 ⟨hb.2.2.1, hb.2.2.2⟩)

abbrev SecondTransferRDyadicBase (c : ArithmeticContext) :=
  RayCharacter c × Ideal O × Ideal O × O

/-- Exactly the first ten conjuncts of the original valid-index predicate. -/
def secondTransferRDyadicBaseValid {c : ArithmeticContext} (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ) (b : SecondTransferRDyadicBase c) : Prop :=
  SquarefreeOutside c.S b.2.1 ∧ SquarefreeOutside c.S b.2.2.1 ∧
  IsRelPrime b.2.1 b.2.2.1 ∧ coeffs b.1 ≠ 0 ∧
  b.2.2.2 ≠ 0 ∧ 0 < normElement b.2.2.2 ∧ b.2.2.1 ∣ principal b.2.2.2 ∧
  normIdeal b.2.2.1 ≤ normElement b.2.2.2 ∧
  normElement b.2.2.2 ≤ H*L/(Sigma*F*normIdeal b.2.1^2) ∧
  normIdeal b.2.1*normIdeal b.2.2.1 ≤ 2*I.hi*L

def secondTransferRDyadicForget {c : ArithmeticContext} (z : SecondTransferIndex c) :
    SecondTransferRDyadicBase c := (z.character,z.excluded,z.twist,z.frequency)

theorem second_transfer_r_dyadic_forget_valid {c : ArithmeticContext} (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ) (z : SecondTransferIndex c)
    (hz : z.valid I coeffs H L F Sigma) :
    secondTransferRDyadicBaseValid I coeffs H L F Sigma (secondTransferRDyadicForget z) := by
  rcases hz with ⟨hr,hf,hcp,hcoeff,hk,hkp,hdiv,hfn,hcut,hprod,_,_,_,_⟩
  exact ⟨hr,hf,hcp,hcoeff,hk,hkp,hdiv,hfn,hcut,hprod⟩

def secondTransferRDyadicLift {c : ArithmeticContext} (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ)
    (b : {b : SecondTransferRDyadicBase c // secondTransferRDyadicBaseValid I coeffs H L F Sigma b}) :
    {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma} := by
  have hr : 1 ≤ normIdeal b.val.2.1 := second_transfer_prmr_one_le_norm b.property.1.1.1
  have hf : 1 ≤ normIdeal b.val.2.2.1 := second_transfer_prmr_one_le_norm b.property.2.1.1.1
  refine ⟨⟨b.val.1,b.val.2.1,b.val.2.2.1,b.val.2.2.2,
    secondTransferRDyadicBlock _ hr,secondTransferRDyadicBlock _ hf⟩, ?_⟩
  rcases b.property with ⟨hr',hf',hcp,hcoeff,hk,hkp,hdiv,hfn,hcut,hprod⟩
  exact ⟨hr',hf',hcp,hcoeff,hk,hkp,hdiv,hfn,hcut,hprod,
    (second_transfer_r_dyadic_block_spec _ hr).1,(second_transfer_r_dyadic_block_spec _ hr).2,
    (second_transfer_r_dyadic_block_spec _ hf).1,(second_transfer_r_dyadic_block_spec _ hf).2⟩

@[simp] theorem second_transfer_r_dyadic_forget_lift {c : ArithmeticContext} (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ)
    (b : {b : SecondTransferRDyadicBase c // secondTransferRDyadicBaseValid I coeffs H L F Sigma b}) :
    secondTransferRDyadicForget (secondTransferRDyadicLift I coeffs H L F Sigma b).val = b.val := by
  rcases b with ⟨⟨ξ,r,f,k⟩,hb⟩
  rfl

/-- Forgetting the two uniquely determined blocks is an exact equivalence,
not a change to arithmetic validity or a selected subset of its rows. -/
def secondTransferRDyadicEquiv {c : ArithmeticContext} (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ) :
    {b : SecondTransferRDyadicBase c // secondTransferRDyadicBaseValid I coeffs H L F Sigma b} ≃
      {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma} where
  toFun := secondTransferRDyadicLift I coeffs H L F Sigma
  invFun := fun z => ⟨secondTransferRDyadicForget z.val,
    second_transfer_r_dyadic_forget_valid I coeffs H L F Sigma z.val z.property⟩
  left_inv := by
    intro b
    exact Subtype.ext (second_transfer_r_dyadic_forget_lift I coeffs H L F Sigma b)
  right_inv := by
    rintro ⟨⟨ξ,r,f,k,rb,fb⟩,hz⟩
    apply Subtype.ext
    rcases hz with ⟨hr,hf,hcp,hcoeff,hk,hkp,hdiv,hfn,hcut,hprod,hrlo,hrhi,hflo,hfhi⟩
    have her := second_transfer_r_dyadic_block_eq (second_transfer_prmr_one_le_norm hr.1.1)
      (n := rb) ⟨hrlo,hrhi⟩
    have hef := second_transfer_r_dyadic_block_eq (second_transfer_prmr_one_le_norm hf.1.1)
      (n := fb) ⟨hflo,hfhi⟩
    change SecondTransferIndex.mk ξ r f k
      (secondTransferRDyadicBlock _ (second_transfer_prmr_one_le_norm hr.1.1))
      (secondTransferRDyadicBlock _ (second_transfer_prmr_one_le_norm hf.1.1)) =
        SecondTransferIndex.mk ξ r f k rb fb
    rw [her,hef]

theorem second_transfer_r_dyadic_base_finite (c : ArithmeticContext)
    (I : SupportInterval) (coeffs : RayCharacter c → ℂ) {H L F Sigma : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (hcoeffs : (Function.support coeffs).Finite) :
    {b : SecondTransferRDyadicBase c | secondTransferRDyadicBaseValid I coeffs H L F Sigma b}.Finite := by
  apply ((second_transfer_prmr_valid_finite c I coeffs hH hL hF hSigma hcoeffs).image
    secondTransferRDyadicForget).subset
  intro b hb
  let z := secondTransferRDyadicLift I coeffs H L F Sigma ⟨b,hb⟩
  exact ⟨z.val,z.property,second_transfer_r_dyadic_forget_lift I coeffs H L F Sigma ⟨b,hb⟩⟩

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

theorem second_transfer_r_label_frequency_positive {c : ArithmeticContext}
    (z : SecondTransferRLabel c) : 0 < normElement z.frequency := by
  have h : principal z.frequency ≠ ⊥ := by
    intro h
    exact z.frequency_ne_zero (Ideal.span_singleton_eq_bot.mp h)
  change (0 : ℝ) < ((principal z.frequency).absNorm : ℝ)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h)

theorem second_transfer_r_label_divisor_norm {c : ArithmeticContext}
    (z : SecondTransferRLabel c) (hdiv : z.twist ∣ principal z.frequency) :
    normIdeal z.twist ≤ normElement z.frequency := by
  have hpos : 0 < (principal z.frequency).absNorm := by
    have h := second_transfer_r_label_frequency_positive z
    change (0 : ℝ) < ((principal z.frequency).absNorm : ℝ) at h
    exact_mod_cast h
  change (z.twist.absNorm : ℝ) ≤ ((principal z.frequency).absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hdiv)

abbrev SecondTransferRActiveLabel (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ) :=
  {p : SecondTransferRLabel c × RayCharacter c //
    p.1.cutoffs I H L F Sigma ∧ p.1.twist ∣ principal p.1.frequency ∧ coeffs p.2 ≠ 0}

/-- No extra arithmetic restrictions are introduced by the positive norm and
divisor norm conjuncts of validity: they follow from the actual label. -/
def secondTransferRActiveBaseEquiv (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ) :
    SecondTransferRActiveLabel c I coeffs H L F Sigma ≃
      {b : SecondTransferRDyadicBase c // secondTransferRDyadicBaseValid I coeffs H L F Sigma b} where
  toFun p := ⟨(p.1.2,p.1.1.excluded,p.1.1.twist,p.1.1.frequency),
    p.1.1.excluded_outside,p.1.1.twist_outside,p.1.1.coprime,p.2.2.2,
    p.1.1.frequency_ne_zero,second_transfer_r_label_frequency_positive p.1.1,p.2.2.1,
    second_transfer_r_label_divisor_norm p.1.1 p.2.2.1,p.2.1.2,p.2.1.1⟩
  invFun := by
    rintro ⟨⟨ξ,r,f,k⟩,hr,hf,hcp,hcoeff,hk,hkp,hdiv,hfn,hcut,hprod⟩
    exact ⟨(⟨r,f,k,hr,hf,hcp,hk⟩,ξ),⟨hprod,hcut⟩,hdiv,hcoeff⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply SecondTransferRLabel.ext <;> rfl
    · rfl
  right_inv b := by
    rcases b with ⟨⟨ξ,r,f,k⟩,hr,hf,hcp,hcoeff,hk,hkp,hdiv,hfn,hcut,hprod⟩
    rfl

def secondTransferRActiveIndexEquiv (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ) :
    SecondTransferRActiveLabel c I coeffs H L F Sigma ≃
      {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma} :=
  (secondTransferRActiveBaseEquiv c I coeffs H L F Sigma).trans
    (secondTransferRDyadicEquiv I coeffs H L F Sigma)

theorem second_transfer_r_active_index_fields (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (H L F Sigma : ℝ)
    (p : SecondTransferRActiveLabel c I coeffs H L F Sigma) :
    let z := (secondTransferRActiveIndexEquiv c I coeffs H L F Sigma p).1
    z.character=p.1.2 ∧ z.excluded=p.1.1.excluded ∧
      z.twist=p.1.1.twist ∧ z.frequency=p.1.1.frequency := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem second_transfer_r_dyadic_kernel {c : ArithmeticContext}
    (z : SecondTransferRLabel c) (ξ : RayCharacter c) (rb fb : ℕ)
    (Φ : RowWeight) (U : ℝ → ℂ) (cI H L F Sigma : ℝ) (hL : 0 < L)
    (n₁ n₂ : Ideal O) :
    secondTransferKernel Φ U (z.index ξ rb fb).dilation
      ((z.index ξ rb fb).parameter cI H L F Sigma)
      ![normIdeal n₁/(z.index ξ rb fb).columnScale L,
        normIdeal n₂/(z.index ξ rb fb).columnScale L] =
    secondTransferKernel Φ U 1 (z.parameter cI H L F Sigma)
      ![normIdeal n₁/z.length L,normIdeal n₂/z.length L] := by
  have hparam : (z.index ξ rb fb).parameter cI H L F Sigma =
      z.parameter cI H L F Sigma/(z.index ξ rb fb).dilation^2 := by
    simp only [SecondTransferIndex.parameter,SecondTransferRLabel.parameter,
      SecondTransferRLabel.index,div_div,mul_assoc]
  have harg (n : Ideal O) :
      (z.index ξ rb fb).dilation*(normIdeal n/(z.index ξ rb fb).columnScale L) =
        normIdeal n/z.length L := by
    unfold SecondTransferIndex.dilation SecondTransferIndex.columnScale
      SecondTransferRLabel.length SecondTransferRLabel.index
    have hr := (normIdeal_pos z.excluded_outside.1.1).ne'
    have hf := (normIdeal_pos z.twist_outside.1.1).ne'
    have hrb : (2:ℝ)^rb ≠ 0 := by positivity
    have hfb : (2:ℝ)^fb ≠ 0 := by positivity
    field_simp [hL.ne',hr,hf,hrb,hfb]
    <;> ring
  rw [hparam,second_transfer_r_kernel_scale]
  congr 1
  funext i
  fin_cases i
  · change (z.index ξ rb fb).dilation*(normIdeal n₁/(z.index ξ rb fb).columnScale L) = normIdeal n₁/z.length L
    exact harg n₁
  · change (z.index ξ rb fb).dilation*(normIdeal n₂/(z.index ξ rb fb).columnScale L) = normIdeal n₂/z.length L
    exact harg n₂

theorem second_transfer_r_dyadic_phase_pair {c : ArithmeticContext}
    (z : SecondTransferRLabel c) (ξ : RayCharacter c) (rb fb : ℕ)
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ)
    (cI H L F Sigma : ℝ) (hL : 0 < L) (n₁ n₂ : Ideal O) :
    (z.index ξ rb fb).phase coeffs cI L Sigma *
      (secondTransferPRMRColumn c (z.index ξ rb fb) n₁ *
        star (secondTransferPRMRColumn c (z.index ξ rb fb) n₂) *
        secondTransferKernel Φ U (z.index ξ rb fb).dilation
          ((z.index ξ rb fb).parameter cI H L F Sigma)
          ![normIdeal n₁/(z.index ξ rb fb).columnScale L,
            normIdeal n₂/(z.index ξ rb fb).columnScale L]) =
    (divisorCount z.excluded : ℂ)*
      secondTransferRCanonicalPair z ξ I Φ U coeffs cI H L F Sigma n₁ n₂ := by
  rw [second_transfer_r_dyadic_kernel z ξ rb fb Φ U cI H L F Sigma hL]
  unfold SecondTransferIndex.phase secondTransferRCanonicalPair
  have hcol (n : Ideal O) : secondTransferPRMRColumn c (z.index ξ rb fb) n =
      secondTransferPRMRColumn c (z.index ξ 0 0) n := rfl
  rw [hcol n₁,hcol n₂]
  simp only [SecondTransferRLabel.index,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

/-- The exact joint native sum, regrouped with its signs, has precisely the
active arithmetic labels; no dyadic choice or test-dependent model occurs here. -/
theorem second_transfer_r_regroup_joint (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (hU : SmoothSupported (halfEnlarged I) U) (coeffs : RayCharacter c → ℂ)
    (cI H L F Sigma : ℝ) (hcI : max 1 (4*Φ.fourierCap*I.hi^2) ≤ cI)
    (hH : 0 < H) (hL : 0 < L) (hF : 0 < F) (hSigma : 0 < Sigma)
    (hcoeffs : (Function.support coeffs).Finite) :
    (∑' v : SecondTransferRJointIndex c,
      secondTransferRJointTerm c I Φ U coeffs cI H L F Sigma v) =
    ∑' p : SecondTransferRActiveLabel c I coeffs H L F Sigma,
      (divisorCount p.1.1.excluded : ℂ) *
        ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
          secondTransferRCanonicalPair p.1.1 p.1.2 I Φ U coeffs cI H L F Sigma n₁ n₂ := by
  let J := secondTransferRJointTerm c I Φ U coeffs cI H L F Sigma
  let R : SecondTransferRInput → ℂ := fun p =>
    ∑' ξ : RayCharacter c, ∑' n₁ : Ideal O, ∑' n₂ : Ideal O, J (p,ξ,n₁,n₂)
  let A : SecondTransferRLabel c → ℂ := fun z =>
    ∑' ξ : RayCharacter c, ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
      secondTransferRCanonicalTerm z ξ I Φ U coeffs cI H L F Sigma n₁ n₂
  have hJ : Summable J := summable_of_hasFiniteSupport
    (second_transfer_r_joint_hasFiniteSupport c I Φ U coeffs cI H L F Sigma hU
      hcoeffs hcI hH hL hF hSigma)
  have hflat : (∑' v, J v) = ∑' p, R p := by
    rw [hJ.tsum_prod]
    apply tsum_congr
    intro p
    rw [(hJ.prod_factor p).tsum_prod]
    apply tsum_congr
    intro ξ
    exact ((hJ.prod_factor p).prod_factor ξ).tsum_prod
  have hrange : Function.support R ⊆
      Set.range (Subtype.val : {p : SecondTransferRInput // p.admissible c} → SecondTransferRInput) := by
    intro p hp
    have hpadm : p.admissible c := by
      by_contra hn
      exact hp (by simp [R,J,secondTransferRJointTerm,hn])
    exact ⟨⟨p,hpadm⟩,rfl⟩
  have hsub : (∑' p : {p : SecondTransferRInput // p.admissible c},R p.1) = ∑' p,R p :=
    Subtype.val_injective.tsum_eq hrange
  have hpoint (p : {p : SecondTransferRInput // p.admissible c}) :
      R p.1 = (mobius p.1.e : ℂ)*(mobius p.1.w : ℂ)*A (p.1.label p.2) := by
    calc
      _ = ∑' ξ : RayCharacter c, ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
          (mobius p.1.e : ℂ)*(mobius p.1.w : ℂ)*
            secondTransferRCanonicalTerm (p.1.label p.2) ξ I Φ U coeffs cI H L F Sigma n₁ n₂ := by
        apply tsum_congr
        intro ξ
        apply tsum_congr
        intro n₁
        apply tsum_congr
        intro n₂
        exact second_transfer_r_joint_pointwise c I Φ U hU coeffs cI H L F Sigma hcI
          hH hL hF hSigma p.1 p.2 ξ n₁ n₂
      _ = _ := by simp only [A,tsum_mul_left]
  have hbound := second_transfer_r_bounded_labels_finite c I H L F Sigma hH hL hF hSigma
  have hA : A.HasFiniteSupport := by
    apply hbound.subset
    intro z hz
    by_contra hcut
    have hc : ¬ z.cutoffs I H L F Sigma := hcut
    exact hz (by simp only [A,secondTransferRCanonicalTerm,if_neg hc,tsum_zero])
  let G : SecondTransferRLabel c × RayCharacter c → ℂ := fun p =>
    (divisorCount p.1.excluded : ℂ)*(if p.1.twist ∣ principal p.1.frequency then 1 else 0)*
      ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
        secondTransferRCanonicalTerm p.1 p.2 I Φ U coeffs cI H L F Sigma n₁ n₂
  have hG : G.HasFiniteSupport := by
    apply (hbound.prod hcoeffs).subset
    rintro ⟨z,ξ⟩ hz
    have hcut : z.cutoffs I H L F Sigma := by
      by_contra hcut
      exact hz (by simp only [G,secondTransferRCanonicalTerm,if_neg hcut,tsum_zero,mul_zero])
    have hc : coeffs ξ ≠ 0 := by
      intro hc
      exact hz (by simp [G,secondTransferRCanonicalTerm,secondTransferRCanonicalPair,hc])
    exact ⟨hcut,hc⟩
  have hGs : Summable G := summable_of_hasFiniteSupport hG
  have hGsum : (∑' z : SecondTransferRLabel c,
      (divisorCount z.excluded : ℂ)*(if z.twist ∣ principal z.frequency then 1 else 0)*A z) =
      ∑' p,G p := by
    calc
      _ = ∑' z : SecondTransferRLabel c, ∑' ξ : RayCharacter c, G (z,ξ) := by
        apply tsum_congr
        intro z
        exact (tsum_mul_left (a := (divisorCount z.excluded : ℂ)*
          (if z.twist ∣ principal z.frequency then 1 else 0))
          (f := fun ξ : RayCharacter c => ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
            secondTransferRCanonicalTerm z ξ I Φ U coeffs cI H L F Sigma n₁ n₂)).symm
      _ = _ := hGs.tsum_prod.symm
  have hGrange : Function.support G ⊆ Set.range
      (Subtype.val : SecondTransferRActiveLabel c I coeffs H L F Sigma →
        SecondTransferRLabel c × RayCharacter c) := by
    rintro ⟨z,ξ⟩ hz
    have hcut : z.cutoffs I H L F Sigma := by
      by_contra hcut
      exact hz (by simp only [G,secondTransferRCanonicalTerm,if_neg hcut,tsum_zero,mul_zero])
    have hc : coeffs ξ ≠ 0 := by
      intro hc
      exact hz (by simp [G,secondTransferRCanonicalTerm,secondTransferRCanonicalPair,hc])
    have hdiv : z.twist ∣ principal z.frequency := by
      by_contra hdiv
      exact hz (by simp only [G,if_neg hdiv,mul_zero,zero_mul])
    exact ⟨⟨(z,ξ),hcut,hdiv,hc⟩,rfl⟩
  have hGsub : (∑' p : SecondTransferRActiveLabel c I coeffs H L F Sigma,G p.1) =
      ∑' p,G p := Subtype.val_injective.tsum_eq hGrange
  calc
    _ = ∑' p,R p := hflat
    _ = ∑' p : {p : SecondTransferRInput // p.admissible c},R p.1 := hsub.symm
    _ = ∑' p : {p : SecondTransferRInput // p.admissible c},
        (mobius p.1.e : ℂ)*(mobius p.1.w : ℂ)*A (p.1.label p.2) := tsum_congr hpoint
    _ = ∑' z : SecondTransferRLabel c,
        (divisorCount z.excluded : ℂ)*(if z.twist ∣ principal z.frequency then 1 else 0)*A z :=
      second_transfer_r_signed_regroup c A hA
    _ = ∑' p,G p := hGsum
    _ = ∑' p : SecondTransferRActiveLabel c I coeffs H L F Sigma,G p.1 := hGsub.symm
    _ = _ := by
      apply tsum_congr
      intro p
      simp only [G,secondTransferRCanonicalTerm,if_pos p.2.1,if_pos p.2.2.1,mul_one]

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

theorem second_transfer_r_equivFin_sum {α : Type*} (s : Finset α) (g : α → ℂ) :
    (∑ n : Fin s.card, g (s.equivFin.symm n)) = ∑ a ∈ s, g a := by
  exact (s.equivFin.symm.sum_comp (fun a : s => g a.val)).trans
    (Finset.sum_coe_sort s g)

theorem second_transfer_r_equivFin_sum_pair {α : Type*} (s : Finset α) (g : α → α → ℂ) :
    (∑ n₁ : Fin s.card, ∑ n₂ : Fin s.card,
      g (s.equivFin.symm n₁) (s.equivFin.symm n₂)) =
      ∑ a ∈ s, ∑ b ∈ s, g a b := by
  calc
    _ = ∑ n₁ : Fin s.card, ∑ b ∈ s, g (s.equivFin.symm n₁) b := by
      apply Finset.sum_congr rfl
      intro n₁ _
      exact second_transfer_r_equivFin_sum s (g (s.equivFin.symm n₁))
    _ = _ := second_transfer_r_equivFin_sum s (fun a => ∑ b ∈ s, g a b)

/-- The concrete model enumerates every valid index, exactly once. -/
theorem second_transfer_r_model_row_sum (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (hSigma : 0 < Sigma) (hcoeffs : (Function.support coeffs).Finite)
    (g : SecondTransferIndex c → ℂ) :
    let model := secondTransferPRMRModel c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs
    (∑ r : Fin model.R, g (model.row r)) =
      ∑' z : {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma}, g z.val := by
  let hfinite := second_transfer_prmr_valid_finite c I coeffs hH hL hF hSigma hcoeffs
  let rows := hfinite.toFinset
  change (∑ r : Fin rows.card, g (rows.equivFin.symm r)) = _
  rw [second_transfer_r_equivFin_sum rows g]
  letI : Fintype {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma} := hfinite.fintype
  rw [tsum_fintype]
  exact Finset.sum_subtype rows (fun z => hfinite.mem_toFinset) g

/-- Reindex the actual model's rows and its two actual column enumerations.
No restriction on the function W, and no analytic identity, is assumed. -/
theorem second_transfer_r_model_rows_columns_sum (c : ArithmeticContext) (I : SupportInterval)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (hSigma : 0 < Sigma) (hcoeffs : (Function.support coeffs).Finite)
    (W : SecondTransferIndex c → Ideal O → Ideal O → ℂ) :
    let model := secondTransferPRMRModel c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs
    let cols := secondTransferPRMRColumns I L
    (∑ r : Fin model.R, ∑ n₁ : Fin model.N, ∑ n₂ : Fin model.N,
      W (model.row r) (cols.equivFin.symm n₁) (cols.equivFin.symm n₂)) =
      ∑' z : {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma},
        ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, W z.val n₁ n₂ := by
  let model := secondTransferPRMRModel c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs
  let cols := secondTransferPRMRColumns I L
  change (∑ r : Fin model.R, ∑ n₁ : Fin cols.card, ∑ n₂ : Fin cols.card,
      W (model.row r) (cols.equivFin.symm n₁) (cols.equivFin.symm n₂)) = _
  calc
    _ = ∑ r : Fin model.R, ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, W (model.row r) n₁ n₂ := by
      apply Finset.sum_congr rfl
      intro r _
      exact second_transfer_r_equivFin_sum_pair cols (W (model.row r))
    _ = _ := second_transfer_r_model_row_sum c I coeffs cI H L F Sigma hcI hH hL hF hSigma
      hcoeffs (fun z => ∑ n₁ ∈ cols, ∑ n₂ ∈ cols, W z n₁ n₂)

/-- In particular the model's literal a/x/kernel expression becomes the
literal finite ideal-column sum over all original valid indices. -/
theorem second_transfer_r_model_kernel_rows (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (hSigma : 0 < Sigma) (hcoeffs : (Function.support coeffs).Finite) :
    let model := secondTransferPRMRModel c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs
    let cols := secondTransferPRMRColumns I L
    (∑ r : Fin model.R, model.phase r *
      ∑ n₁ : Fin model.N, ∑ n₂ : Fin model.N,
        model.a r n₁ * star (model.a r n₂) *
          model.kernel Φ U r ![model.x r n₁, model.x r n₂]) =
      ∑' z : {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma},
        z.val.phase coeffs cI L Sigma *
          ∑ n₁ ∈ cols, ∑ n₂ ∈ cols,
            secondTransferPRMRColumn c z.val n₁ * star (secondTransferPRMRColumn c z.val n₂) *
              secondTransferKernel Φ U z.val.dilation (z.val.parameter cI H L F Sigma)
                ![normIdeal n₁ / z.val.columnScale L, normIdeal n₂ / z.val.columnScale L] := by
  let model := secondTransferPRMRModel c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs
  let cols := secondTransferPRMRColumns I L
  let g : SecondTransferIndex c → ℂ := fun z =>
    z.phase coeffs cI L Sigma * ∑ n₁ ∈ cols, ∑ n₂ ∈ cols,
      secondTransferPRMRColumn c z n₁ * star (secondTransferPRMRColumn c z n₂) *
        secondTransferKernel Φ U z.dilation (z.parameter cI H L F Sigma)
          ![normIdeal n₁ / z.columnScale L, normIdeal n₂ / z.columnScale L]
  change (∑ r : Fin model.R, model.phase r *
      ∑ n₁ : Fin model.N, ∑ n₂ : Fin model.N,
        model.a r n₁ * star (model.a r n₂) * model.kernel Φ U r ![model.x r n₁, model.x r n₂]) =
    ∑' z : {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma}, g z.val
  calc
    _ = ∑ r : Fin model.R, g (model.row r) := by
      apply Finset.sum_congr rfl
      intro r _
      change (model.row r).phase coeffs cI L Sigma *
          (∑ n₁ : Fin cols.card, ∑ n₂ : Fin cols.card,
            secondTransferPRMRColumn c (model.row r) (cols.equivFin.symm n₁) *
              star (secondTransferPRMRColumn c (model.row r) (cols.equivFin.symm n₂)) *
              secondTransferKernel Φ U (model.row r).dilation
                ((model.row r).parameter cI H L F Sigma)
                ![normIdeal (cols.equivFin.symm n₁) / (model.row r).columnScale L,
                  normIdeal (cols.equivFin.symm n₂) / (model.row r).columnScale L]) = g (model.row r)
      exact congrArg (fun v : ℂ => (model.row r).phase coeffs cI L Sigma * v)
        (second_transfer_r_equivFin_sum_pair cols (fun n₁ n₂ =>
          secondTransferPRMRColumn c (model.row r) n₁ *
            star (secondTransferPRMRColumn c (model.row r) n₂) *
            secondTransferKernel Φ U (model.row r).dilation
              ((model.row r).parameter cI H L F Sigma)
              ![normIdeal n₁ / (model.row r).columnScale L,
                normIdeal n₂ / (model.row r).columnScale L]))
    _ = _ := second_transfer_r_model_row_sum c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs g

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

theorem second_transfer_r_pair_columns_support {c : ArithmeticContext}
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (hU : SmoothSupported (halfEnlarged I) U) (z : SecondTransferIndex c)
    {L ell rho B : ℝ} (hell : 0 < ell) (hellL : ell ≤ L) (hrho : 1 ≤ rho) :
    Function.support (fun p : Ideal O × Ideal O =>
      secondTransferPRMRColumn c z p.1 * star (secondTransferPRMRColumn c z p.2) *
        secondTransferKernel Φ U rho B ![normIdeal p.1/ell,normIdeal p.2/ell]) ⊆
      (secondTransferPRMRColumns I L : Set (Ideal O)) ×ˢ
        (secondTransferPRMRColumns I L : Set (Ideal O)) := by
  intro p hp
  change _ ≠ 0 at hp
  have hprod := (mul_ne_zero_iff.mp hp).1
  have hK := (mul_ne_zero_iff.mp hp).2
  have hc₁ := (mul_ne_zero_iff.mp hprod).1
  have hc₂ : secondTransferPRMRColumn c z p.2 ≠ 0 := by
    intro hz
    exact (mul_ne_zero_iff.mp hprod).2 (by rw [hz,star_zero])
  have hu₁ : U (rho*(normIdeal p.1/ell)) ≠ 0 := by
    intro hz
    exact hK (by simp [secondTransferKernel,hz])
  have hu₂ : U (rho*(normIdeal p.2/ell)) ≠ 0 := by
    intro hz
    exact hK (by simp [secondTransferKernel,hz])
  have column_bound (n : Ideal O) (hc : secondTransferPRMRColumn c z n ≠ 0)
      (hu : U (rho*(normIdeal n/ell)) ≠ 0) :
      n ∈ secondTransferPRMRColumns I L := by
    have hn : SquarefreeOutside c.S n ∧ IsRelPrime n z.excluded := by
      by_contra hn
      exact hc (by simp only [secondTransferPRMRColumn,if_neg hn])
    have hx : 0 ≤ normIdeal n/ell := div_nonneg (normIdeal_pos hn.1.1.1).le hell.le
    have hxhi : normIdeal n/ell ≤ 2*I.hi :=
      (le_mul_of_one_le_left hx hrho).trans (hU.2 hu).2
    have hhi : 0 < I.hi := I.lo_pos.trans_le I.ordered
    have hL : 0 < L := hell.trans_le hellL
    apply mem_boundedDivisibleIdeals.mpr
    refine ⟨?_,one_dvd _,hn.1.1.1⟩
    calc
      normIdeal n ≤ (2*I.hi)*ell := (div_le_iff₀ hell).mp hxhi
      _ ≤ (2*I.hi)*L := mul_le_mul_of_nonneg_left hellL (by positivity)
      _ ≤ (enlarged I).hi*L := by
        change 2*I.hi*L ≤ 4*I.hi*L
        nlinarith
  exact ⟨column_bound p.1 hc₁ hu₁,column_bound p.2 hc₂ hu₂⟩

theorem second_transfer_r_pair_columns_hasFiniteSupport {c : ArithmeticContext}
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (hU : SmoothSupported (halfEnlarged I) U) (z : SecondTransferIndex c)
    {L ell rho B : ℝ} (hell : 0 < ell) (hellL : ell ≤ L) (hrho : 1 ≤ rho) :
    (fun p : Ideal O × Ideal O =>
      secondTransferPRMRColumn c z p.1 * star (secondTransferPRMRColumn c z p.2) *
        secondTransferKernel Φ U rho B ![normIdeal p.1/ell,normIdeal p.2/ell]).HasFiniteSupport :=
  ((secondTransferPRMRColumns I L).finite_toSet.prod
    (secondTransferPRMRColumns I L).finite_toSet).subset
      (second_transfer_r_pair_columns_support I Φ U hU z hell hellL hrho)

theorem second_transfer_r_pair_columns_tsum {c : ArithmeticContext}
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (hU : SmoothSupported (halfEnlarged I) U) (z : SecondTransferIndex c)
    {L ell rho B : ℝ} (hell : 0 < ell) (hellL : ell ≤ L) (hrho : 1 ≤ rho) :
    (∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
      secondTransferPRMRColumn c z n₁ * star (secondTransferPRMRColumn c z n₂) *
        secondTransferKernel Φ U rho B ![normIdeal n₁/ell,normIdeal n₂/ell]) =
    ∑ n₁ ∈ secondTransferPRMRColumns I L, ∑ n₂ ∈ secondTransferPRMRColumns I L,
      secondTransferPRMRColumn c z n₁ * star (secondTransferPRMRColumn c z n₂) *
        secondTransferKernel Φ U rho B ![normIdeal n₁/ell,normIdeal n₂/ell] := by
  let f : Ideal O × Ideal O → ℂ := fun p =>
    secondTransferPRMRColumn c z p.1 * star (secondTransferPRMRColumn c z p.2) *
      secondTransferKernel Φ U rho B ![normIdeal p.1/ell,normIdeal p.2/ell]
  have hs : Summable f := summable_of_hasFiniteSupport
    (second_transfer_r_pair_columns_hasFiniteSupport I Φ U hU z hell hellL hrho)
  rw [← hs.tsum_prod]
  rw [tsum_eq_sum (s := (secondTransferPRMRColumns I L).product
    (secondTransferPRMRColumns I L))]
  · exact Finset.sum_product _ _ _
  · intro p hp
    by_contra hn
    have hm := second_transfer_r_pair_columns_support I Φ U hU z hell hellL hrho hn
    exact hp (Finset.mem_product.mpr hm)

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

/-- One actual model row, including its divisor multiplicity and both full
ideal columns, has exactly the canonical arithmetic normalization. -/
theorem second_transfer_r_active_model_row_canonical (c : ArithmeticContext)
    (I : SupportInterval) (Φ : RowWeight) (U : ℝ → ℂ)
    (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hU : SmoothSupported (halfEnlarged I) U) (hL : 0 < L)
    (p : SecondTransferRActiveLabel c I coeffs H L F Sigma) :
    let z := (secondTransferRActiveIndexEquiv c I coeffs H L F Sigma p).val
    z.phase coeffs cI L Sigma *
      (∑ n₁ ∈ secondTransferPRMRColumns I L, ∑ n₂ ∈ secondTransferPRMRColumns I L,
        secondTransferPRMRColumn c z n₁ * star (secondTransferPRMRColumn c z n₂) *
          secondTransferKernel Φ U z.dilation (z.parameter cI H L F Sigma)
            ![normIdeal n₁/z.columnScale L,normIdeal n₂/z.columnScale L]) =
      (divisorCount p.val.1.excluded : ℂ) *
        ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
          secondTransferRCanonicalPair p.val.1 p.val.2 I Φ U coeffs cI H L F Sigma n₁ n₂ := by
  let z := (secondTransferRActiveIndexEquiv c I coeffs H L F Sigma p).val
  have hz : z.valid I coeffs H L F Sigma :=
    (secondTransferRActiveIndexEquiv c I coeffs H L F Sigma p).property
  have hscale := second_transfer_prmr_columnScale_bounds z hL
  have hdilation := second_transfer_prmr_dilation_bounds I coeffs H L F Sigma z hz
  have hcolumns := second_transfer_r_pair_columns_tsum I Φ U hU z
    (L := L) (ell := z.columnScale L) (rho := z.dilation)
    (B := z.parameter cI H L F Sigma) hscale.1 hscale.2 hdilation.1
  change z.phase coeffs cI L Sigma *
      (∑ n₁ ∈ secondTransferPRMRColumns I L, ∑ n₂ ∈ secondTransferPRMRColumns I L,
        secondTransferPRMRColumn c z n₁ * star (secondTransferPRMRColumn c z n₂) *
          secondTransferKernel Φ U z.dilation (z.parameter cI H L F Sigma)
            ![normIdeal n₁/z.columnScale L,normIdeal n₂/z.columnScale L]) = _
  calc
    _ = z.phase coeffs cI L Sigma *
        (∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
          secondTransferPRMRColumn c z n₁ * star (secondTransferPRMRColumn c z n₂) *
            secondTransferKernel Φ U z.dilation (z.parameter cI H L F Sigma)
              ![normIdeal n₁/z.columnScale L,normIdeal n₂/z.columnScale L]) :=
      congrArg (fun v : ℂ => z.phase coeffs cI L Sigma*v) hcolumns.symm
    _ = ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
        z.phase coeffs cI L Sigma *
          (secondTransferPRMRColumn c z n₁ * star (secondTransferPRMRColumn c z n₂) *
            secondTransferKernel Φ U z.dilation (z.parameter cI H L F Sigma)
              ![normIdeal n₁/z.columnScale L,normIdeal n₂/z.columnScale L]) := by
      simp only [tsum_mul_left]
    _ = ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
        (divisorCount p.val.1.excluded : ℂ)*
          secondTransferRCanonicalPair p.val.1 p.val.2 I Φ U coeffs cI H L F Sigma n₁ n₂ := by
      apply tsum_congr
      intro n₁
      apply tsum_congr
      intro n₂
      exact second_transfer_r_dyadic_phase_pair p.val.1 p.val.2 z.rBlock z.fBlock
        I Φ U coeffs cI H L F Sigma hL n₁ n₂
    _ = _ := by simp only [tsum_mul_left]

/-- The original finite model RHS equals the active canonical sum, with all
valid rows and all actual ideal columns included. -/
theorem second_transfer_r_model_canonical (c : ArithmeticContext) (I : SupportInterval)
    (Φ : RowWeight) (U : ℝ → ℂ) (coeffs : RayCharacter c → ℂ) (cI H L F Sigma : ℝ)
    (hcI : 0 ≤ cI) (hH : 0 < H) (hL : 0 < L) (hF : 0 < F)
    (hSigma : 0 < Sigma) (hcoeffs : (Function.support coeffs).Finite)
    (hU : SmoothSupported (halfEnlarged I) U) :
    let model := secondTransferPRMRModel c I coeffs cI H L F Sigma hcI hH hL hF hSigma hcoeffs
    (∑ r : Fin model.R, model.phase r *
      ∑ n₁ : Fin model.N, ∑ n₂ : Fin model.N,
        model.a r n₁ * star (model.a r n₂) *
          model.kernel Φ U r ![model.x r n₁,model.x r n₂]) =
      ∑' p : SecondTransferRActiveLabel c I coeffs H L F Sigma,
        (divisorCount p.val.1.excluded : ℂ) *
          ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
            secondTransferRCanonicalPair p.val.1 p.val.2 I Φ U coeffs cI H L F Sigma n₁ n₂ := by
  let e := secondTransferRActiveIndexEquiv c I coeffs H L F Sigma
  let f : {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma} → ℂ := fun z =>
    z.val.phase coeffs cI L Sigma *
      ∑ n₁ ∈ secondTransferPRMRColumns I L, ∑ n₂ ∈ secondTransferPRMRColumns I L,
        secondTransferPRMRColumn c z.val n₁ * star (secondTransferPRMRColumn c z.val n₂) *
          secondTransferKernel Φ U z.val.dilation (z.val.parameter cI H L F Sigma)
            ![normIdeal n₁/z.val.columnScale L,normIdeal n₂/z.val.columnScale L]
  letI : Fintype {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma} :=
    (second_transfer_prmr_valid_finite c I coeffs hH hL hF hSigma hcoeffs).fintype
  have hactiveFinite : Finite (SecondTransferRActiveLabel c I coeffs H L F Sigma) :=
    Finite.of_injective e e.injective
  refine (second_transfer_r_model_kernel_rows c I Φ U coeffs cI H L F Sigma
    hcI hH hL hF hSigma hcoeffs).trans ?_
  change (∑' z : {z : SecondTransferIndex c // z.valid I coeffs H L F Sigma}, f z) = _
  calc
    _ = ∑' p : SecondTransferRActiveLabel c I coeffs H L F Sigma, f (e p) := (e.tsum_eq f).symm
    _ = _ := by
      apply tsum_congr
      intro p
      exact second_transfer_r_active_model_row_canonical c I Φ U coeffs cI H L F Sigma hU hL p

end QRHShort

end


noncomputable section
open Classical
open scoped BigOperators

namespace QRHShort

/-- Signed regrouping of the literal second Poisson expansion. The finite
model is fixed before the test, and all reindexing uses actual finite support. -/
theorem second_transfer_regroup_proved : SecondTransferRegroupStatement := by
  intro C hC c I Φ cI hc hcI D H L F Sigma coeffs hD hrange hcoeffs
  have hH : 0 < H := zero_lt_one.trans_le hrange.1
  have hL : 0 < L := zero_lt_one.trans_le hrange.2.2.1
  have hF : 0 < F := zero_lt_one.trans_le hrange.2.2.2.2.1
  have hSigma : 0 < Sigma := zero_lt_one.trans_le hrange.2.2.2.2.2.2.1
  have hcI0 : 0 ≤ cI := zero_le_one.trans ((le_max_left _ _).trans hcI)
  let model := secondTransferPRMRModel c I coeffs cI H L F Sigma hcI0 hH hL hF hSigma hcoeffs
  refine ⟨model,?_⟩
  intro U hU
  have hfinite := second_transfer_r_joint_hasFiniteSupport c I Φ U coeffs cI H L F Sigma
    hU hcoeffs hcI hH hL hF hSigma
  calc
    secondTransferDual c I Φ U coeffs cI H L F Sigma =
        ∑' v : SecondTransferRJointIndex c,
          secondTransferRJointTerm c I Φ U coeffs cI H L F Sigma v :=
      (second_transfer_r_native_expansion c I Φ U coeffs cI H L F Sigma).trans
        (second_transfer_r_joint_tsum_eq_native c _ hfinite).symm
    _ = ∑' p : SecondTransferRActiveLabel c I coeffs H L F Sigma,
        (divisorCount p.1.1.excluded : ℂ)*
          ∑' n₁ : Ideal O, ∑' n₂ : Ideal O,
            secondTransferRCanonicalPair p.1.1 p.1.2 I Φ U coeffs cI H L F Sigma n₁ n₂ :=
      second_transfer_r_regroup_joint c I Φ U hU coeffs cI H L F Sigma hcI
        hH hL hF hSigma hcoeffs
    _ = _ := (second_transfer_r_model_canonical c I Φ U coeffs cI H L F Sigma
      hcI0 hH hL hF hSigma hcoeffs hU).symm

end QRHShort

end
