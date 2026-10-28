import QRHShort.SecondTransferPRMRColumns
import QRHShort.SecondTransferPRMRPrimeAssignments
import QRHShort.PrimaryGenerator
import QRHShort.SecondTransferPRMRFactorization

noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem second_transfer_r_prime_unique_factor {f : Ideal O} (hf : Squarefree f)
    (A : Fin 4 → Ideal O) (hA : (∏ i, A i) = f)
    (p : (primeFactors f)) : ∃! i : Fin 4, (p : Ideal O) ∣ A i := by
  have hp := prime_of_normalized_factor p.1 (Multiset.mem_toFinset.mp p.2)
  have hpf : (p : Ideal O) ∣ f := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp p.2)
  have hpf' : (p : Ideal O) ∣ ∏ i, A i := by rw [hA]; exact hpf
  obtain ⟨i, _, hi⟩ := (hp.dvd_finsetProd_iff A).mp hpf'
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  have hpair : A i * A j ∣ f := by
    have hh := Finset.prod_dvd_prod_of_subset ({i,j} : Finset (Fin 4)) Finset.univ A
      (Finset.subset_univ _)
    simpa [Finset.prod_pair (Ne.symm hji), hA] using hh
  have hsq := hf.squarefree_of_dvd hpair
  exact hp.not_isUnit ((IsRelPrime.of_squarefree_mul hsq) hi hj)

theorem second_transfer_r_colorFactor_product {f : Ideal O} (hf : Squarefree f)
    (v : (primeFactors f) → Fin 4) :
    (∏ i : Fin 4, secondTransferPRMRColorFactor f v i) = f := by
  unfold secondTransferPRMRColorFactor
  rw [Finset.prod_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
  have hp : (∏ p : (primeFactors f), (p : Ideal O)) =
      (normalizedFactors f).prod := by
    rw [Finset.prod_coe_sort (primeFactors f) (fun p => p)]
    change (normalizedFactors f).toFinset.prod id = _
    rw [← Multiset.toFinset_eq ((squarefree_iff_nodup_normalizedFactors hf.ne_zero).mp hf)]
    simp only [Finset.prod_mk, Multiset.map_id]
  exact hp.trans (Ideal.prod_normalizedFactors_eq_self hf.ne_zero)

/-- Every literal four-factor ideal decomposition of a squarefree ideal has
exactly the prime coloring prescribed by its factors. -/
theorem second_transfer_r_colorFactor_surjective {f : Ideal O} (hf : Squarefree f)
    (A : Fin 4 → Ideal O) (hA : (∏ i, A i) = f) :
    ∃ v : (primeFactors f) → Fin 4, secondTransferPRMRColorFactor f v = A := by
  let v : (primeFactors f) → Fin 4 := fun p =>
    Classical.choose (ExistsUnique.exists (second_transfer_r_prime_unique_factor hf A hA p))
  have hv (p : (primeFactors f)) : (p : Ideal O) ∣ A (v p) :=
    Classical.choose_spec (ExistsUnique.exists (second_transfer_r_prime_unique_factor hf A hA p))
  have hviff (p : (primeFactors f)) (i : Fin 4) : v p=i ↔ (p : Ideal O) ∣ A i := by
    constructor
    · intro h; simpa only [h] using hv p
    · intro h
      obtain ⟨j, hj, huniq⟩ := second_transfer_r_prime_unique_factor hf A hA p
      exact (huniq _ (hv p)).trans (huniq _ h).symm
  refine ⟨v, ?_⟩
  funext i
  have hAi : A i ∣ f := hA ▸ Finset.dvd_prod_of_mem A (Finset.mem_univ i)
  have hA0 : A i ≠ 0 := ne_zero_of_dvd_ne_zero hf.ne_zero hAi
  have hAsq := hf.squarefree_of_dvd hAi
  have hCsq := second_transfer_prmr_colorFactor_squarefree f v i
  apply associated_iff_eq.mp
  apply associated_of_dvd_dvd
  · apply (second_transfer_prmr_squarefree_dvd_iff hCsq).mpr
    intro p
    have hp := prime_of_normalized_factor p.1 (Multiset.mem_toFinset.mp p.2)
    have hpm := Multiset.mem_toFinset.mp p.2
    change (p : Ideal O) ∈ normalizedFactors (secondTransferPRMRColorFactor f v i) at hpm
    rw [second_transfer_prmr_colorFactor_normalizedFactors] at hpm
    obtain ⟨q, hq, heq⟩ := Multiset.mem_map.mp hpm
    have hqi := (Finset.mem_filter.mp hq).2
    simpa only [heq] using (hviff q i).mp hqi
  · apply (second_transfer_prmr_squarefree_dvd_iff hAsq).mpr
    intro p
    have hp := prime_of_normalized_factor p.1 (Multiset.mem_toFinset.mp p.2)
    have hpA : (p : Ideal O) ∣ A i := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp p.2)
    have hpf : (p : Ideal O) ∈ primeFactors f :=
      Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hf.ne_zero).mpr ⟨hp, hpA.trans hAi⟩)
    exact (second_transfer_prmr_colorFactor_prime_dvd f v i ⟨p,hpf⟩).mpr
      ((hviff ⟨p,hpf⟩ i).mpr hpA)

def secondTransferRColorEquiv (f : Ideal O) (hf : Squarefree f) :
    ((primeFactors f) → Fin 4) ≃ {A : Fin 4 → Ideal O // (∏ i, A i) = f} :=
  Equiv.ofBijective (fun v => ⟨secondTransferPRMRColorFactor f v,
    second_transfer_r_colorFactor_product hf v⟩) ⟨
      fun v w h => second_transfer_prmr_colorFactor_injective f (congrArg Subtype.val h),
      fun A => by
        obtain ⟨v,hv⟩ := second_transfer_r_colorFactor_surjective hf A.1 A.2
        exact ⟨v, Subtype.ext hv⟩⟩

/-- The actual C,d,e,w factorization fiber occurring in the Poisson sum. -/
def SecondTransferRFactorFiber (f : Ideal O) :=
  {p : Ideal O × Ideal O × Ideal O × Ideal O // p.2.1 ∣ p.1 ∧
    p.1 * p.2.2.1 * p.2.2.2 = f}

def secondTransferRQuadFactorEquiv (f : Ideal O) (hf : f ≠ ⊥) :
    {A : Fin 4 → Ideal O // (∏ i, A i) = f} ≃ SecondTransferRFactorFiber f where
  toFun A := ⟨(A.1 0 * A.1 1, A.1 1, A.1 2, A.1 3), dvd_mul_left _ _, by
    simpa only [Fin.prod_univ_four, mul_assoc] using A.2⟩
  invFun p := ⟨![quotientIdeal p.1.1 p.1.2.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2], by
    rw [Fin.prod_univ_four]
    change (quotientIdeal p.1.1 p.1.2.1 * p.1.2.1) * p.1.2.2.1 * p.1.2.2.2 = f
    rw [mul_comm (quotientIdeal p.1.1 p.1.2.1), second_transfer_prmr_quotient_spec p.2.1]
    exact p.2.2⟩
  left_inv A := by
    apply Subtype.ext
    funext i
    have hd : A.1 1 ∣ f :=
      (Finset.dvd_prod_of_mem A.1 (Finset.mem_univ 1)).trans (dvd_of_eq A.2)
    have hA1 : A.1 1 ≠ ⊥ := ne_zero_of_dvd_ne_zero hf hd
    fin_cases i
    · change quotientIdeal (A.1 0 * A.1 1) (A.1 1) = A.1 0
      exact second_transfer_prmr_quotient_unique hA1 (mul_comm _ _)
    · rfl
    · rfl
    · rfl
  right_inv p := by
    apply Subtype.ext
    change (quotientIdeal p.1.1 p.1.2.1 * p.1.2.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2) = p.1
    rw [mul_comm (quotientIdeal p.1.1 p.1.2.1), second_transfer_prmr_quotient_spec p.2.1]

def secondTransferRPrimePreimageEquiv (f : Ideal O) (hf : Squarefree f) :
    ((primeFactors f) → Fin 4) ≃ SecondTransferRFactorFiber f :=
  (secondTransferRColorEquiv f hf).trans (secondTransferRQuadFactorEquiv f hf.ne_zero)

theorem second_transfer_r_factor_fiber_finite (f : Ideal O) (hf : Squarefree f) :
    Finite (SecondTransferRFactorFiber f) :=
  Finite.of_equiv _ (secondTransferRPrimePreimageEquiv f hf)

end QRHShort



noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

theorem second_transfer_r_colorFactor_dvd_iff (f k : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) :
    secondTransferPRMRColorFactor f v i ∣ k ↔
      ∀ p : (primeFactors f), v p=i → (p : Ideal O) ∣ k := by
  constructor
  · intro h p hp
    exact ((second_transfer_prmr_colorFactor_prime_dvd f v i p).mpr hp).trans h
  · intro h
    apply (second_transfer_prmr_squarefree_dvd_iff
      (second_transfer_prmr_colorFactor_squarefree f v i)).mpr
    intro p
    have hm := Multiset.mem_toFinset.mp p.2
    change (p : Ideal O) ∈ normalizedFactors (secondTransferPRMRColorFactor f v i) at hm
    rw [second_transfer_prmr_colorFactor_normalizedFactors] at hm
    obtain ⟨q,hq,heq⟩ := Multiset.mem_map.mp hm
    simpa only [heq] using h q (Finset.mem_filter.mp hq).2

theorem second_transfer_r_colorFactor_coprime_iff (f k : Ideal O)
    (v : (primeFactors f) → Fin 4) (i : Fin 4) :
    IsRelPrime (secondTransferPRMRColorFactor f v i) k ↔
      ∀ p : (primeFactors f), v p=i → ¬(p : Ideal O) ∣ k := by
  rw [isRelPrime_iff_no_prime_factors (second_transfer_prmr_colorFactor_ne_zero f v i)]
  constructor
  · intro h p hp hpk
    exact h ((second_transfer_prmr_colorFactor_prime_dvd f v i p).mpr hp) hpk
      (prime_of_normalized_factor p.1 (Multiset.mem_toFinset.mp p.2))
  · intro h P hP hPk hp
    have hm := (mem_normalizedFactors_iff
      (second_transfer_prmr_colorFactor_ne_zero f v i)).mpr ⟨hp,hP⟩
    rw [second_transfer_prmr_colorFactor_normalizedFactors] at hm
    obtain ⟨q,hq,heq⟩ := Multiset.mem_map.mp hm
    exact h q (Finset.mem_filter.mp hq).2 (heq ▸ hPk)

theorem second_transfer_r_color_mobius_product (f : Ideal O)
    (v : (primeFactors f) → Fin 4) :
    mobius (secondTransferPRMRColorFactor f v 2) *
      mobius (secondTransferPRMRColorFactor f v 3) =
      ∏ p : (primeFactors f), (if v p=2 then (-1:ℤ) else 1) *
        (if v p=3 then (-1:ℤ) else 1) := by
  rw [Finset.prod_mul_distrib]
  congr 1 <;> rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    second_transfer_prmr_colorFactor_mobius] <;> simp

/-- The product of local four-color weights is exactly the original signed
Mobius weight with the two divisibility restrictions and w-coprimality. -/
theorem second_transfer_r_color_signed_weight (f k : Ideal O)
    (v : (primeFactors f) → Fin 4) :
    (∏ p : (primeFactors f), secondTransferPRMRLocalSign ((p : Ideal O) ∣ k) (v p)) =
      if secondTransferPRMRColorFactor f v 1 ∣ k ∧
        secondTransferPRMRColorFactor f v 2 ∣ k ∧
        IsRelPrime (secondTransferPRMRColorFactor f v 3) k then
        mobius (secondTransferPRMRColorFactor f v 2) *
          mobius (secondTransferPRMRColorFactor f v 3) else 0 := by
  rw [second_transfer_r_colorFactor_dvd_iff, second_transfer_r_colorFactor_dvd_iff,
    second_transfer_r_colorFactor_coprime_iff]
  by_cases h : (∀ p : (primeFactors f), v p=1 → (p : Ideal O) ∣ k) ∧
      (∀ p : (primeFactors f), v p=2 → (p : Ideal O) ∣ k) ∧
      (∀ p : (primeFactors f), v p=3 → ¬(p : Ideal O) ∣ k)
  · rw [if_pos h, second_transfer_r_color_mobius_product]
    apply Finset.prod_congr rfl
    intro p _
    have h1 := h.1 p
    have h2 := h.2.1 p
    have h3 := h.2.2 p
    generalize hv : v p=i at *
    fin_cases i <;> simp_all [secondTransferPRMRLocalSign]
  · rw [if_neg h]
    by_contra hz
    apply h
    have hn (p : (primeFactors f)) :
        secondTransferPRMRLocalSign ((p : Ideal O) ∣ k) (v p) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) p (Finset.mem_univ p)
    refine ⟨?_,?_,?_⟩
    · intro p hp
      have hh := hn p
      by_contra hk
      simp [secondTransferPRMRLocalSign,hp,hk] at hh
    · intro p hp
      have hh := hn p
      by_contra hk
      simp [secondTransferPRMRLocalSign,hp,hk] at hh
    · intro p hp hk
      have hh := hn p
      simp [secondTransferPRMRLocalSign,hp,hk] at hh

/-- Signed cancellation over the complete literal C,d,e,w ideal fiber. -/
theorem second_transfer_r_signed_factor_fiber (f k : Ideal O) (hf : Squarefree f) :
    (∑' p : SecondTransferRFactorFiber f,
      if p.1.2.1 ∣ k ∧ p.1.2.2.1 ∣ k ∧ IsRelPrime p.1.2.2.2 k then
        mobius p.1.2.2.1 * mobius p.1.2.2.2 else 0) = if f ∣ k then 1 else 0 := by
  rw [← (secondTransferRPrimePreimageEquiv f hf).tsum_eq]
  rw [tsum_fintype]
  have heq := second_transfer_prmr_prime_fiber_cancellation f k hf
  rw [← heq]
  apply Finset.sum_congr rfl
  intro v _
  exact (second_transfer_r_color_signed_weight f k v).symm

end QRHShort



noncomputable section
open scoped BigOperators
open Classical UniqueFactorizationMonoid

namespace QRHShort

/-- All six literal ideal indices of a fixed regrouped Poisson fiber. -/
@[ext] structure SecondTransferRIdealPreimage (r f : Ideal O) where
  C : Ideal O
  d : Ideal O
  t : Ideal O
  g : Ideal O
  e : Ideal O
  w : Ideal O
  d_dvd : d ∣ C
  e_dvd : e ∣ g
  excluded_eq : t * quotientIdeal g e = r
  twist_eq : C * e * w = f

def secondTransferRIdealPreimageEquiv (r f : Ideal O) (hr : r ≠ ⊥) (hf : f ≠ ⊥) :
    ({t : Ideal O // t ∣ r} × SecondTransferRFactorFiber f) ≃
      SecondTransferRIdealPreimage r f where
  toFun p := {
    C := p.2.1.1
    d := p.2.1.2.1
    t := p.1.1
    g := p.2.1.2.2.1 * quotientIdeal r p.1.1
    e := p.2.1.2.2.1
    w := p.2.1.2.2.2
    d_dvd := p.2.2.1
    e_dvd := dvd_mul_right _ _
    excluded_eq := by
      have he : p.2.1.2.2.1 ≠ ⊥ := by
        intro he
        apply hf
        rw [← p.2.2.2,he,Ideal.mul_bot,Ideal.bot_mul]
      rw [second_transfer_prmr_quotient_unique he rfl]
      exact second_transfer_prmr_quotient_spec p.1.2
    twist_eq := p.2.2.2 }
  invFun p := (⟨p.t, ⟨quotientIdeal p.g p.e, p.excluded_eq.symm⟩⟩,
    ⟨(p.C,p.d,p.e,p.w),p.d_dvd,p.twist_eq⟩)
  left_inv p := rfl
  right_inv p := by
    have ht : p.t ≠ ⊥ := by
      by_contra ht
      have heq := p.excluded_eq
      rw [ht,Ideal.bot_mul] at heq
      exact hr heq.symm
    have hq : quotientIdeal r p.t = quotientIdeal p.g p.e :=
      second_transfer_prmr_quotient_unique ht p.excluded_eq
    apply SecondTransferRIdealPreimage.ext <;> try rfl
    change p.e * quotientIdeal r p.t = p.g
    rw [hq]
    exact second_transfer_prmr_quotient_spec p.e_dvd

theorem second_transfer_r_ideal_preimage_finite (r f : Ideal O)
    (hr : r ≠ ⊥) (hf : Squarefree f) :
    Finite (SecondTransferRIdealPreimage r f) := by
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd r hr
  letI := second_transfer_r_factor_fiber_finite f hf
  exact Finite.of_equiv _ (secondTransferRIdealPreimageEquiv r f hr hf.ne_zero)

/-- The tau(r) factor and the surviving f|k condition follow from the actual
six-ideal preimage fiber, with its original two Mobius signs. -/
theorem second_transfer_r_signed_ideal_preimages (r f k : Ideal O)
    (hr : r ≠ ⊥) (hf : Squarefree f) :
    (∑' p : SecondTransferRIdealPreimage r f,
      if p.d ∣ k ∧ p.e ∣ k ∧ IsRelPrime p.w k then mobius p.e * mobius p.w else 0) =
      (divisorCount r : ℤ) * (if f ∣ k then 1 else 0) := by
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd r hr
  letI := second_transfer_r_factor_fiber_finite f hf
  letI : Fintype (SecondTransferRFactorFiber f) := Fintype.ofFinite _
  rw [← (secondTransferRIdealPreimageEquiv r f hr hf.ne_zero).tsum_eq, tsum_fintype,
    Fintype.sum_prod_type]
  change (∑ _t : {t : Ideal O // t ∣ r}, ∑ p : SecondTransferRFactorFiber f,
    if p.1.2.1 ∣ k ∧ p.1.2.2.1 ∣ k ∧ IsRelPrime p.1.2.2.2 k then
      mobius p.1.2.2.1 * mobius p.1.2.2.2 else 0) = _
  have hi : (∑ p : SecondTransferRFactorFiber f,
    if p.1.2.1 ∣ k ∧ p.1.2.2.1 ∣ k ∧ IsRelPrime p.1.2.2.2 k then
      mobius p.1.2.2.1 * mobius p.1.2.2.2 else 0) = if f ∣ k then 1 else 0 := by
    have hh := second_transfer_r_signed_factor_fiber f k hf
    rw [tsum_fintype] at hh
    exact hh
  simp only [hi,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,divisorCount,
    Nat.card_eq_fintype_card]

end QRHShort



noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem second_transfer_r_primary_spec (c : ArithmeticContext) {a : Ideal O}
    (ha : Outside c.S a) : principal (primaryGenerator a) = a := by
  let z := idealGenerator a
  have hz : principal z=a := Ideal.span_singleton_generator a
  have hp : Prime (principal (omega-1)) :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have hthree : principal (omega-1) ∣ principal 3 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three
  have hn : ¬omega-1 ∣ z := by
    intro h
    apply ha.2 _ (c.above_three _ hp hthree)
    rw [← hz]
    exact Ideal.dvd_span_singleton.mpr (Ideal.mem_span_singleton.mpr h)
  obtain ⟨u,hu⟩ := exists_primary_unit_of_not_dvd z hn
  have hex : ∃ w : O, principal w=a ∧ IsPrimary w :=
    ⟨(u:O)*z,(Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz,hu⟩
  simpa only [primaryGenerator,dif_pos hex] using (Classical.choose_spec hex).1

/-- The literal frequency map has one and only one preimage exactly when
the corresponding ideal divides the frequency ideal. -/
theorem second_transfer_r_frequency_preimage (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) (k : O) :
    a ∣ principal k ↔ ∃! h : O, primaryGenerator a*h=k := by
  have hgen := second_transfer_r_primary_spec c ha
  have hne : primaryGenerator a ≠ 0 := by
    intro h
    apply ha.1
    rw [← hgen,h]
    simp [principal]
  conv_lhs =>
    rw [← hgen]
    simp only [principal,Ideal.dvd_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨h,hh⟩
    exact ⟨h,hh.symm,fun v hv => mul_left_cancel₀ hne (hv.trans hh)⟩
  · rintro ⟨h,hh,_⟩
    exact ⟨h,hh.symm⟩

theorem second_transfer_r_frequency_nonzero {a k h : O}
    (hk : k ≠ 0) (heq : a*h=k) : h ≠ 0 := by
  intro hh
  apply hk
  rw [← heq,hh,mul_zero]

/-- The two separate prime divisibilities in the signed fiber are precisely
the condition needed to invert k=primaryGenerator(d*e)*h. -/
theorem second_transfer_r_de_frequency_preimage (c : ArithmeticContext)
    {f C d e w : Ideal O} (hf : SquarefreeOutside c.S f)
    (hfactor : C*e*w=f) (hd : d ∣ C) (k : O) :
    (d ∣ principal k ∧ e ∣ principal k) ↔
      ∃! h : O, primaryGenerator (d*e)*h=k := by
  have hde : d*e ∣ f := by
    rw [← hfactor]
    exact (mul_dvd_mul hd (dvd_refl e)).trans (dvd_mul_right _ _)
  have hout : Outside c.S (d*e) :=
    ⟨ne_zero_of_dvd_ne_zero hf.1.1 hde,fun P hP hh => hf.1.2 P hP (hh.trans hde)⟩
  have hcop : IsRelPrime d e :=
    IsRelPrime.of_squarefree_mul (hf.2.squarefree_of_dvd hde)
  rw [← second_transfer_r_frequency_preimage c hout]
  exact ⟨fun h => hcop.mul_dvd h.1 h.2,
    fun h => ⟨(dvd_mul_right d e).trans h,(dvd_mul_left e d).trans h⟩⟩

end QRHShort



noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem second_transfer_r_outside_dvd {S : Finset (Ideal O)} {a b : Ideal O}
    (hb : Outside S b) (hab : a ∣ b) : Outside S a :=
  ⟨ne_zero_of_dvd_ne_zero hb.1 hab,fun P hP hPa => hb.2 P hP (hPa.trans hab)⟩

theorem second_transfer_r_ideal_total {r f : Ideal O}
    (p : SecondTransferRIdealPreimage r f) : p.C*p.t*p.g*p.w=r*f := by
  calc
    _ = p.C*p.t*(p.e*quotientIdeal p.g p.e)*p.w :=
      congrArg (fun g => p.C*p.t*g*p.w) (second_transfer_prmr_quotient_spec p.e_dvd).symm
    _ = (p.t*quotientIdeal p.g p.e)*(p.C*p.e*p.w) := by ac_rfl
    _ = _ := congrArg₂ (fun a b : Ideal O => a*b) p.excluded_eq p.twist_eq

/-- The squarefree and coprimality filters on the original six ideals are
automatic for a coprime squarefree regrouped pair, throughout the complete fiber. -/
theorem second_transfer_r_ideal_admissible (c : ArithmeticContext) {r f : Ideal O}
    (hr : SquarefreeOutside c.S r) (hf : SquarefreeOutside c.S f)
    (hrf : IsRelPrime r f) (p : SecondTransferRIdealPreimage r f) :
    SquarefreeOutside c.S p.C ∧ SquarefreeOutside c.S p.t ∧
    SquarefreeOutside c.S p.g ∧ SquarefreeOutside c.S p.w ∧
    IsRelPrime p.C p.t ∧ IsRelPrime p.g (p.C*p.t) ∧
    IsRelPrime p.w (p.g*p.C*p.t) := by
  have hout : Outside c.S (r*f) := by
    refine ⟨mul_ne_zero hr.1.1 hf.1.1,?_⟩
    intro P hP hdiv
    rcases (c.prime_S P hP).dvd_mul.mp hdiv with hh | hh
    · exact hr.1.2 P hP hh
    · exact hf.1.2 P hP hh
  have hs : Squarefree (r*f) := squarefree_mul_iff.mpr ⟨hrf,hr.2,hf.2⟩
  rw [← second_transfer_r_ideal_total p] at hout hs
  have hC : p.C ∣ p.C*p.t*p.g*p.w :=
    (dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
  have ht : p.t ∣ p.C*p.t*p.g*p.w :=
    (dvd_mul_left _ _).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
  have hg : p.g ∣ p.C*p.t*p.g*p.w :=
    (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hw : p.w ∣ p.C*p.t*p.g*p.w := dvd_mul_left _ _
  refine ⟨⟨second_transfer_r_outside_dvd hout hC,hs.squarefree_of_dvd hC⟩,
    ⟨second_transfer_r_outside_dvd hout ht,hs.squarefree_of_dvd ht⟩,
    ⟨second_transfer_r_outside_dvd hout hg,hs.squarefree_of_dvd hg⟩,
    ⟨second_transfer_r_outside_dvd hout hw,hs.squarefree_of_dvd hw⟩,
    IsRelPrime.of_squarefree_mul hs.of_mul_left.of_mul_left,
    (IsRelPrime.of_squarefree_mul hs.of_mul_left).symm,?_⟩
  have hh := (IsRelPrime.of_squarefree_mul hs).symm
  convert hh using 1 <;> ac_rfl

theorem second_transfer_r_frequency_admissible {r f : Ideal O}
    (p : SecondTransferRIdealPreimage r f) {k h : O}
    (hk : k ≠ 0) (heq : primaryGenerator (p.d*p.e)*h=k)
    (hwr : IsRelPrime p.w (p.g*p.C*p.t)) (hwk : IsRelPrime p.w (principal k)) :
    h ≠ 0 ∧ IsRelPrime p.w (p.g*p.C*p.t*principal h) := by
  have hhk : principal h ∣ principal k := by
    apply Ideal.dvd_span_singleton.mpr
    rw [← heq]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_left _ _)
  refine ⟨?_,hwr.mul_right (hwk.of_dvd_right hhk)⟩
  intro hh
  apply hk
  rw [← heq,hh,mul_zero]

end QRHShort



noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

/-- The literal transformed arithmetic coefficient is the regrouped column
at the actual excluded ideal, twist ideal, and frequency element. -/
theorem second_transfer_r_column_identification (c : ArithmeticContext)
    (ξ : RayCharacter c) (C d t g e w : Ideal O) (h : O)
    (rb fb : ℕ) (n : Ideal O) :
    (if SquarefreeOutside c.S n then secondPoissonCoefficient c ξ C d t g e w h n else 0) =
      secondTransferPRMRColumn c
        ⟨ξ,t*quotientIdeal g e,C*e*w,primaryGenerator (d*e)*h,rb,fb⟩ n := by
  by_cases hn : SquarefreeOutside c.S n <;>
    by_cases hr : IsRelPrime n (t*quotientIdeal g e) <;>
      simp [secondPoissonCoefficient,secondTransferPRMRColumn,hn,hr]

/-- The actual two-column Poisson kernel under the dyadic dilation. No
analytic replacement, positivity, or convergence convention enters this identity. -/
theorem second_transfer_r_kernel_dilation (Φ : RowWeight) (U : ℝ → ℂ)
    (Y ell rho : ℝ) (g e : Ideal O) (h : O) (x : BoxSpace 2) :
    secondPoissonKernel Φ U Y ell g e h (rho*x 0) (rho*x 1) =
      secondTransferKernel Φ U rho
        ((Y*normElement h*normIdeal g^2/(normIdeal e*ell^2))/rho^2) x := by
  unfold secondPoissonKernel secondTransferKernel
  congr 2
  simp only [div_div]
  congr 1
  ring

theorem second_transfer_r_norm_quotient {g e : Ideal O} (he : e ∣ g) :
    normIdeal e * normIdeal (quotientIdeal g e) = normIdeal g := by
  rw [← normIdeal_mul, second_transfer_prmr_quotient_spec he]

/-- The excluded ideal in the actual ideal bijection has exactly the real
quotient norm appearing in all three previously proved scalar identities. -/
theorem second_transfer_r_excluded_norm {g e : Ideal O} (he : e ∣ g)
    (he0 : e ≠ ⊥) (t : Ideal O) :
    normIdeal (t*quotientIdeal g e) = normIdeal t*normIdeal g/normIdeal e := by
  have hn : normIdeal e ≠ 0 := (normIdeal_pos he0).ne'
  rw [normIdeal_mul, ← second_transfer_r_norm_quotient he]
  field_simp
  <;> ring

end QRHShort

