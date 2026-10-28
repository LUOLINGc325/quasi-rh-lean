import QRHShort.ThetaStatements
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Local identities and conductor accounting for paper2.tex:2044--2115.
The three branches are the unchanged term, the substitution n = p*n', and
the substitution b = p*b'. No infinite-series rearrangement is asserted here.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

inductive ReflectionLocalBranch where
  | unchanged | numerator | cube
  deriving DecidableEq

def reflectionLocalWeight (q : ℝ) (j : Fin 6) (b : ReflectionLocalBranch) : ℝ :=
  if j = 0 then q⁻¹ else if j = 4 then
    match b with
    | .unchanged => q⁻¹
    | .numerator => 1
    | .cube => q⁻¹
  else 1

def reflectionLocalScale (q : ℝ) (j : Fin 6) (b : ReflectionLocalBranch) : ℝ :=
  if j = 4 then
    match b with
    | .unchanged => q ^ 2
    | .numerator => q
    | .cube => q⁻¹
  else q ^ 2

def reflectionLocalCost (q : ℝ) (j : Fin 6) : ℝ :=
  if j = 0 ∨ j = 4 then q else q ^ 2

theorem reflection_local_update {q : ℝ} (hq : 1 ≤ q)
    (j : Fin 6) (b : ReflectionLocalBranch) :
    0 ≤ reflectionLocalWeight q j b ∧ reflectionLocalWeight q j b ≤ 1 ∧
    0 < reflectionLocalScale q j b ∧ reflectionLocalScale q j b ≤ q ^ 2 ∧
    reflectionLocalWeight q j b * reflectionLocalScale q j b ≤
      reflectionLocalCost q j := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hi0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have hi1 : q⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_iff₀ hq0]
    simpa using hq
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hi2 : q⁻¹ ≤ q ^ 2 := hi1.trans (hq.trans hq2)
  have hcancel : q⁻¹ * q ^ 2 = q := by field_simp [hq0.ne']
  have hisq : q⁻¹ * q⁻¹ ≤ q := by nlinarith
  by_cases h0 : j = 0
  · subst j
    change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1 ∧ 0 < q ^ 2 ∧ q ^ 2 ≤ q ^ 2 ∧ q⁻¹ * q ^ 2 ≤ q
    exact ⟨hi0.le, hi1, sq_pos_of_pos hq0, le_rfl, hcancel.le⟩
  · by_cases h4 : j = 4
    · subst j
      cases b
      · change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1 ∧ 0 < q ^ 2 ∧ q ^ 2 ≤ q ^ 2 ∧ q⁻¹ * q ^ 2 ≤ q
        exact ⟨hi0.le, hi1, sq_pos_of_pos hq0, le_rfl, hcancel.le⟩
      · change (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ 0 < q ∧ q ≤ q ^ 2 ∧ 1 * q ≤ q
        exact ⟨zero_le_one, le_rfl, hq0, hq2, (one_mul q).le⟩
      · change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1 ∧ 0 < q⁻¹ ∧ q⁻¹ ≤ q ^ 2 ∧ q⁻¹ * q⁻¹ ≤ q
        exact ⟨hi0.le, hi1, hi0, hi2, hisq⟩
    · simp only [reflectionLocalWeight, reflectionLocalScale, reflectionLocalCost,
        h0, h4, or_self, ↓reduceIte, one_mul]
      exact ⟨zero_le_one, le_rfl, sq_pos_of_pos hq0, le_rfl, le_rfl⟩

/-- The local losses multiply without increasing the squared amplitude.
The scale alone costs at most q², whereas amplitude² times scale costs
only q at exponents 0 and 4. -/
theorem reflection_local_product {ι : Type*} (P : Finset ι)
    (q : ι → ℝ) (j : ι → Fin 6) (b : ι → ReflectionLocalBranch)
    (hq : ∀ p ∈ P, 1 ≤ q p) :
    0 ≤ (∏ p ∈ P, reflectionLocalWeight (q p) (j p) (b p)) ∧
    (∏ p ∈ P, reflectionLocalWeight (q p) (j p) (b p)) ≤ 1 ∧
    0 < (∏ p ∈ P, reflectionLocalScale (q p) (j p) (b p)) ∧
    (∏ p ∈ P, reflectionLocalScale (q p) (j p) (b p)) ≤
      ∏ p ∈ P, q p ^ 2 ∧
    (∏ p ∈ P, reflectionLocalWeight (q p) (j p) (b p)) *
        (∏ p ∈ P, reflectionLocalScale (q p) (j p) (b p)) ≤
      ∏ p ∈ P, reflectionLocalCost (q p) (j p) := by
  have h := fun p hp => reflection_local_update (hq p hp) (j p) (b p)
  refine ⟨Finset.prod_nonneg (fun p hp => (h p hp).1),
    Finset.prod_le_one₀ (fun p hp => (h p hp).1) (fun p hp => (h p hp).2.1),
    Finset.prod_pos (fun p hp => (h p hp).2.2.1),
    Finset.prod_le_prod₀ (fun p hp => (h p hp).2.2.1.le)
      (fun p hp => (h p hp).2.2.2.1), ?_⟩
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀
    (fun p hp => mul_nonneg (h p hp).1 (h p hp).2.2.1.le)
    (fun p hp => (h p hp).2.2.2.2)

/-- The exponent-2 case requires at least two copies in the auxiliary
element; exponents 0 and 4 consume only one. -/
theorem reflection_local_cost_le_pow {q : ℝ} (hq : 1 ≤ q)
    (j : Fin 6) (v : ℕ) (hv : 1 ≤ v)
    (hodd : j ≠ 0 → j ≠ 4 → 2 ≤ v) :
    reflectionLocalCost q j ≤ q ^ v := by
  by_cases h : j = 0 ∨ j = 4
  · simpa [reflectionLocalCost, h] using (pow_le_pow_right₀ hq hv)
  · simpa [reflectionLocalCost, h] using
      (pow_le_pow_right₀ hq (hodd (fun h0 => h (Or.inl h0))
        (fun h4 => h (Or.inr h4))))

theorem reflection_four_exponent_two (v : ℕ)
    (h : (4 * v) % 6 = 2) : 2 ≤ v := by omega

theorem reflection_four_exponent_cases (v : ℕ) :
    (4 * v) % 6 = 0 ∨ (4 * v) % 6 = 2 ∨ (4 * v) % 6 = 4 := by omega

theorem reflection_auxiliary_prime_cost {q : ℝ} (hq : 1 ≤ q)
    (v : ℕ) (hv : 1 ≤ v) :
    reflectionLocalCost q ⟨(4 * v) % 6, Nat.mod_lt _ (by decide)⟩ ≤ q ^ v := by
  apply reflection_local_cost_le_pow hq _ v hv
  intro _ h4
  by_contra h
  have hv1 : v = 1 := by omega
  subst v
  exact h4 rfl

theorem reflection_row_prime_cost (q : ℝ) (v : ℕ) :
    reflectionLocalCost q ⟨(1 + 4 * v) % 6, Nat.mod_lt _ (by decide)⟩ = q ^ 2 := by
  have h0 : (⟨(1 + 4 * v) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change (1 + 4 * v) % 6 = 0 at hv
    omega
  have h4 : (⟨(1 + 4 * v) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) ≠ 4 := by
    intro h
    have hv := congrArg Fin.val h
    change (1 + 4 * v) % 6 = 4 at hv
    omega
  simp only [reflectionLocalCost, h0, h4, or_self, ↓reduceIte]

theorem reflection_local_product_budget {ι : Type*} (P : Finset ι)
    (q : ι → ℝ) (j : ι → Fin 6) (b : ι → ReflectionLocalBranch)
    (hq : ∀ p ∈ P, 1 ≤ q p) (A H Y : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hY : 0 ≤ Y) :
    A * (∏ p ∈ P, reflectionLocalWeight (q p) (j p) (b p)) *
        (H + Y * ∏ p ∈ P, reflectionLocalScale (q p) (j p) (b p)) ≤
      A * (H + Y * ∏ p ∈ P, reflectionLocalCost (q p) (j p)) := by
  obtain ⟨_, hw, _, _, hc⟩ := reflection_local_product P q j b hq
  have hrow : (∏ p ∈ P, reflectionLocalWeight (q p) (j p) (b p)) * H ≤ H := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw hH
  calc
    _ = A * ((∏ p ∈ P, reflectionLocalWeight (q p) (j p) (b p)) * H +
        Y * ((∏ p ∈ P, reflectionLocalWeight (q p) (j p) (b p)) *
          (∏ p ∈ P, reflectionLocalScale (q p) (j p) (b p)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hrow (mul_le_mul_of_nonneg_left hc hY)) hA

private theorem inv_sqrt_mul (q : ℝ) (hq : 0 ≤ q) :
    (Real.sqrt q : ℂ)⁻¹ * (q : ℂ) = (Real.sqrt q : ℂ) := by
  have heq : (q : ℂ) = (Real.sqrt q : ℂ) ^ 2 := by
    exact_mod_cast (Real.sq_sqrt hq).symm
  rw [heq]
  by_cases hz : (Real.sqrt q : ℂ) = 0
  · simp [hz]
  · field_simp

theorem thetaLocalFactor_four (p : Ideal O) (x : O) :
    thetaLocalFactor p 4 x = -(Real.sqrt (normIdeal p) : ℂ)⁻¹ +
      if x ∈ p then (Real.sqrt (normIdeal p) : ℂ) else 0 := by
  have hq : 0 ≤ normIdeal p := Nat.cast_nonneg _
  change (Real.sqrt (normIdeal p) : ℂ)⁻¹ *
      (-1 + if x ∈ p then (normIdeal p : ℂ) else 0) = _
  by_cases hx : x ∈ p
  · simp only [hx, ↓reduceIte, mul_add, mul_neg, mul_one]
    rw [inv_sqrt_mul _ hq]
  · simp [hx]

/-- The two divisibility indicators are disjoint, including the case p|n
and p|b. This is the pointwise input to the two series substitutions. -/
theorem thetaLocalFactor_four_split {p : Ideal O} (hp : Prime p)
    (a n b : O) (ha : a ∉ p) :
    thetaLocalFactor p 4 (a * n * b ^ 3) =
      -(Real.sqrt (normIdeal p) : ℂ)⁻¹ +
      (if n ∈ p then (Real.sqrt (normIdeal p) : ℂ) else 0) +
      (if n ∉ p ∧ b ∈ p then (Real.sqrt (normIdeal p) : ℂ) else 0) := by
  have hprime : p.IsPrime := Ideal.isPrime_of_prime hp
  have hmem : a * n * b ^ 3 ∈ p ↔ n ∈ p ∨ b ∈ p := by
    rw [hprime.mul_mem_iff_mem_or_mem, hprime.mul_mem_iff_mem_or_mem,
      hprime.pow_mem_iff_mem 3 (by decide)]
    simp [ha]
  rw [thetaLocalFactor_four]
  by_cases hn : n ∈ p <;> by_cases hb : b ∈ p <;> simp [hmem, hn, hb]

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.reflection_local_update
#print axioms QRHShort.SquarefreeAssembly.reflection_local_product
#print axioms QRHShort.SquarefreeAssembly.reflection_local_product_budget
#print axioms QRHShort.SquarefreeAssembly.reflection_local_cost_le_pow
#print axioms QRHShort.SquarefreeAssembly.thetaLocalFactor_four_split
