import QRHShort.FirstTransferMultiplicityBounds
import QRHShort.PrimaryGenerator

/-!
Fibers of the actual map `(f,h) ↦ h * primaryGenerator f ^ 2`. For nonzero
image, the ideal coordinate determines the element coordinate uniquely. Its
square divides the principal image ideal. Restricting to squarefree ideals
therefore gives the subpolynomial multiplicity bound needed by child M.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem first_transfer_primaryGenerator_spec_outside (c : ArithmeticContext)
    {f : Ideal O} (hf : Outside c.S f) : principal (primaryGenerator f) = f := by
  let z := idealGenerator f
  have hz : principal z = f := Ideal.span_singleton_generator f
  have hp : Prime (principal (omega - 1)) :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have hthree : principal (omega - 1) ∣ principal 3 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three
  have hnot : ¬ omega - 1 ∣ z := by
    intro hdiv
    apply hf.2 _ (c.above_three _ hp hthree)
    rw [← hz]
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr hdiv
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  have hex : ∃ a : O, principal a = f ∧ IsPrimary a :=
    ⟨(u : O) * z, (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz, hu⟩
  simpa only [primaryGenerator, dif_pos hex] using (Classical.choose_spec hex).1

theorem first_transfer_principal_ne_bot {y : O} (hy : y ≠ 0) : principal y ≠ ⊥ := by
  intro h
  exact hy (Ideal.span_singleton_eq_bot.mp h)

theorem first_transfer_primaryGenerator_ne_zero (c : ArithmeticContext)
    {f : Ideal O} (hf : Outside c.S f) : primaryGenerator f ≠ 0 := by
  intro h
  apply hf.1
  rw [← first_transfer_primaryGenerator_spec_outside c hf, h]
  simp [principal]

theorem first_transfer_fiber_image_ne_zero (c : ArithmeticContext) {f : Ideal O}
    (hf : Outside c.S f) {h : O} (hh : h ≠ 0) : h * primaryGenerator f ^ 2 ≠ 0 :=
  mul_ne_zero hh (pow_ne_zero 2 (first_transfer_primaryGenerator_ne_zero c hf))

theorem first_transfer_fiber_image_norm (c : ArithmeticContext) {f : Ideal O}
    (hf : Outside c.S f) (h : O) :
    normElement (h * primaryGenerator f ^ 2) = normElement h * normIdeal f ^ 2 := by
  have hp : principal (h * primaryGenerator f ^ 2) = principal h * f ^ 2 := by
    calc
      principal (h * primaryGenerator f ^ 2) =
          principal h * principal (primaryGenerator f ^ 2) :=
        (Ideal.span_singleton_mul_span_singleton _ _).symm
      _ = principal h * principal (primaryGenerator f) ^ 2 := by
        simp only [principal, ← Ideal.span_singleton_pow]
      _ = principal h * f ^ 2 := by
        rw [first_transfer_primaryGenerator_spec_outside c hf]
  rw [normElement, hp, normIdeal_mul]
  simp only [normElement, normIdeal, map_pow, Nat.cast_pow]

theorem first_transfer_fiber_square_dvd (c : ArithmeticContext) {f : Ideal O}
    (hf : Outside c.S f) {h y : O} (himage : h * primaryGenerator f ^ 2 = y) :
    f ^ 2 ∣ principal y := by
  have hid : principal y = principal h * f ^ 2 := by
    rw [← himage]
    calc
      principal (h * primaryGenerator f ^ 2) =
          principal h * principal (primaryGenerator f ^ 2) :=
        (Ideal.span_singleton_mul_span_singleton _ _).symm
      _ = principal h * principal (primaryGenerator f) ^ 2 := by
        simp only [principal, ← Ideal.span_singleton_pow]
      _ = principal h * f ^ 2 := by
        rw [first_transfer_primaryGenerator_spec_outside c hf]
  exact ⟨principal h, hid.trans (mul_comm _ _)⟩

theorem first_transfer_fiber_dvd (c : ArithmeticContext) {f : Ideal O}
    (hf : Outside c.S f) {h y : O} (himage : h * primaryGenerator f ^ 2 = y) :
    f ∣ principal y := by
  have hself : f ∣ f ^ 2 := by
    rw [pow_two]
    exact dvd_mul_right f f
  exact hself.trans (first_transfer_fiber_square_dvd c hf himage)

def firstTransferFiber (c : ArithmeticContext) (y : O) : Set (Ideal O × O) :=
  {p | SquarefreeOutside c.S p.1 ∧ p.2 * primaryGenerator p.1 ^ 2 = y}

/-- No unit factor is lost: the chosen generator is fixed, so the element
coordinate in a nonzero-image fiber is determined by its ideal coordinate. -/
theorem first_transfer_fiber_fst_injOn (c : ArithmeticContext) {y : O} (hy : y ≠ 0) :
    Set.InjOn Prod.fst (firstTransferFiber c y) := by
  rintro ⟨f, h⟩ hfh ⟨g, k⟩ hgk hfg
  change f = g at hfg
  subst g
  apply Prod.ext
  · rfl
  have hg0 : primaryGenerator f ≠ 0 := by
    intro hz
    apply hy
    rw [← hfh.2, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
  exact mul_right_cancel₀ (pow_ne_zero 2 hg0) (hfh.2.trans hgk.2.symm)

theorem first_transfer_fiber_mapsTo_squarefreeDivisors (c : ArithmeticContext)
    {y : O} (hy : y ≠ 0) :
    Set.MapsTo Prod.fst (firstTransferFiber c y)
      (firstTransferSquarefreeDivisors (principal y) (first_transfer_principal_ne_bot hy)) := by
  intro p hp
  exact (mem_firstTransferSquarefreeDivisors _ _ _).mpr
    ⟨first_transfer_fiber_dvd c hp.1.1 hp.2, hp.1.2⟩

/-- Finiteness is proved before using the totalized natural cardinality. -/
theorem first_transfer_fiber_finite (c : ArithmeticContext) {y : O} (hy : y ≠ 0) :
    (firstTransferFiber c y).Finite :=
  Set.Finite.of_injOn (first_transfer_fiber_mapsTo_squarefreeDivisors c hy)
    (first_transfer_fiber_fst_injOn c hy) (Finset.finite_toSet _)

theorem first_transfer_fiber_card_le_squarefreeDivisors (c : ArithmeticContext)
    {y : O} (hy : y ≠ 0) :
    Nat.card (firstTransferFiber c y) ≤
      (firstTransferSquarefreeDivisors (principal y) (first_transfer_principal_ne_bot hy)).card := by
  let S := firstTransferSquarefreeDivisors (principal y) (first_transfer_principal_ne_bot hy)
  let ι : firstTransferFiber c y → S := fun p =>
    ⟨p.1.1, first_transfer_fiber_mapsTo_squarefreeDivisors c hy p.2⟩
  have hι : Function.Injective ι := by
    intro p q hpq
    apply Subtype.ext
    exact first_transfer_fiber_fst_injOn c hy p.2 q.2 (congrArg Subtype.val hpq)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_le_card_of_injective ι hι

/-- The multiplicity constant is uniform in the context and nonzero image. -/
theorem first_transfer_fiber_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ArithmeticContext) (y : O), y ≠ 0 →
      (Nat.card (firstTransferFiber c y) : ℝ) ≤ K * normElement y ^ ε := by
  obtain ⟨K, hK, hbound⟩ := first_transfer_squarefree_divisors_subpolynomial ε hε
  refine ⟨K, hK, ?_⟩
  intro c y hy
  have hcard : (Nat.card (firstTransferFiber c y) : ℝ) ≤
      ((firstTransferSquarefreeDivisors (principal y)
        (first_transfer_principal_ne_bot hy)).card : ℝ) := by
    exact_mod_cast first_transfer_fiber_card_le_squarefreeDivisors c hy
  exact hcard.trans (hbound (principal y) (first_transfer_principal_ne_bot hy))

/-- A form convenient for finite model rows with further exclusions. -/
theorem first_transfer_finite_fiber_card_le (c : ArithmeticContext) {y : O}
    (hy : y ≠ 0) (s : Finset (Ideal O × O))
    (hs : ∀ p ∈ s, SquarefreeOutside c.S p.1 ∧ p.2 * primaryGenerator p.1 ^ 2 = y) :
    s.card ≤ Nat.card (firstTransferFiber c y) := by
  let ι : s → firstTransferFiber c y := fun p => ⟨p.1, hs p.1 p.2⟩
  have hι : Function.Injective ι := by
    intro p q hpq
    apply Subtype.ext
    change (ι p).val = (ι q).val
    exact congrArg Subtype.val hpq
  letI := (first_transfer_fiber_finite c hy).fintype
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_le_card_of_injective ι hι

/-- Conversion from a polynomial image range to the requested small power
of D. This is a scalar range hypothesis, not an assumed divisor bound. -/
theorem first_transfer_fiber_bound_of_norm_le (A B ε : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ArithmeticContext) (D : ℝ) (y : O),
      0 < D → y ≠ 0 → normElement y ≤ B * D ^ A →
      (Nat.card (firstTransferFiber c y) : ℝ) ≤ K * D ^ ε := by
  have hδ : 0 < ε / A := div_pos hε hA
  obtain ⟨K, hK, hbound⟩ := first_transfer_fiber_subpolynomial (ε / A) hδ
  refine ⟨K * B ^ (ε / A), mul_pos hK (Real.rpow_pos_of_pos hB _), ?_⟩
  intro c D y hD hy hnorm
  calc
    (Nat.card (firstTransferFiber c y) : ℝ) ≤ K * normElement y ^ (ε / A) :=
      hbound c y hy
    _ ≤ K * (B * D ^ A) ^ (ε / A) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hδ.le) hK.le
    _ = (K * B ^ (ε / A)) * D ^ ε := by
      rw [Real.mul_rpow hB.le (Real.rpow_nonneg hD.le _), ← Real.rpow_mul hD.le]
      rw [show A * (ε / A) = ε by field_simp]
      ring

end QRHShort
