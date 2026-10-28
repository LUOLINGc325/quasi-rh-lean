import QRHShort.PoissonCoprimeExpansion
import QRHShort.External
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Absolute convergence of a radial Schwartz profile on the actual ring of
integers. A fourth-order Schwartz bound is dominated by the convergent ideal
zeta series at two, pulled back along principal ideals using the finite unit
group. Only the existing `hecke_continuation` external input is used.
-/

noncomputable section
open scoped BigOperators
open Classical
namespace QRHShort.PoissonProof.CoprimeExpansion

theorem finite_units : (Set.univ : Set Oˣ).Finite := by
  let η : Oˣ :=
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
      (by decide)).unit
  apply (List.finite_toSet [1, -1, η, -η, η ^ 2, -η ^ 2]).subset
  intro u _
  exact IsCyclotomicExtension.Rat.Three.Units.mem
    (IsCyclotomicExtension.zeta_spec 3 ℚ K) u

private theorem summable_principal_pullback {g : Ideal O → ℝ}
    (hg0 : ∀ a, 0 ≤ g a) (hg : Summable g) :
    Summable (fun z : O => g (principal z)) := by
  letI : Fintype Oˣ := Set.fintypeOfFiniteUniv finite_units
  have hu (z : O) : ∃ u : Oˣ, idealGenerator (principal z) * (u : O) = z := by
    have hspan : principal (idealGenerator (principal z)) = principal z :=
      Ideal.span_singleton_generator (principal z)
    exact Ideal.span_singleton_eq_span_singleton.mp hspan
  let u (z : O) : Oˣ := Classical.choose (hu z)
  have hurepr (z : O) : idealGenerator (principal z) * (u z : O) = z :=
    Classical.choose_spec (hu z)
  let ι : O → Ideal O × Oˣ := fun z => (principal z, u z)
  have hι : Function.Injective ι := by
    intro z w h
    have hp : principal z = principal w := congrArg Prod.fst h
    have hu' : u z = u w := congrArg Prod.snd h
    calc
      z = idealGenerator (principal z) * (u z : O) := (hurepr z).symm
      _ = idealGenerator (principal w) * (u w : O) := by rw [hp, hu']
      _ = w := hurepr w
  have hprod : Summable (fun p : Ideal O × Oˣ => g p.1) := by
    apply (summable_prod_of_nonneg (fun p => hg0 p.1)).mpr
    constructor
    · intro a
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        hg.mul_left (Fintype.card Oˣ : ℝ)
  exact hprod.comp_injective hι

/-- The principal Hecke character with modulus the unit ideal. -/
def trivialHeckeCharacter : HeckeCharacter where
  modulus := ⊤
  modulus_ne_bot := top_ne_bot
  residue := 1
  unit_trivial u := MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk ⊤))

theorem trivialHeckeCharacter_onIdeal {a : Ideal O} (ha : a ≠ ⊥) :
    trivialHeckeCharacter.onIdeal a = 1 := by
  rw [HeckeCharacter.onIdeal, if_neg ha]
  apply MulChar.one_apply
  have heq : Ideal.Quotient.mk (⊤ : Ideal O) (idealGenerator a) = 1 :=
    Subsingleton.elim _ _
  change IsUnit (Ideal.Quotient.mk (⊤ : Ideal O) (idealGenerator a))
  rw [heq]
  exact isUnit_one

/-- The convergent `ζ_K(2)` factor uses only the existing Hecke continuation input. -/
theorem summable_inverse_norm_sq :
    Summable (fun v : Ideal O => (normIdeal v ^ 2)⁻¹) := by
  apply Complex.summable_ofReal.mp
  have hs := (HeckeL_hasSum trivialHeckeCharacter (2 : ℂ) (by norm_num)).summable
  apply hs.congr
  intro v
  by_cases hv : v = ⊥
  · simp [heckeSeriesTerm, hv, normIdeal]
  · rw [heckeSeriesTerm, if_neg hv, trivialHeckeCharacter_onIdeal hv]
    simp only [Complex.cpow_ofNat, one_div, Complex.ofReal_inv, Complex.ofReal_pow]

theorem radial_quadratic_decay (Φ : ℝ → ℂ) (hΦ : RadialSchwartz Φ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℕ) * ‖Φ x‖ ≤ A := by
  obtain ⟨f, hf⟩ := hΦ
  obtain ⟨A, hA, hdecay⟩ := f.decay 4 0
  refine ⟨A, hA, ?_⟩
  intro x hx
  let z : ℂ := (Real.sqrt x : ℂ)
  have hsq : ‖z‖ ^ (2 : ℕ) = x := by
    rw [Complex.sq_norm]
    exact (Complex.normSq_ofReal _).trans (Real.mul_self_sqrt hx)
  have hval : ‖f z‖ = ‖Φ x‖ := by
    rw [hf z, ← Complex.sq_norm, hsq]
  have hd := hdecay z
  rw [norm_iteratedFDeriv_zero] at hd
  calc
    x ^ (2 : ℕ) * ‖Φ x‖ = (‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ) * ‖f z‖ := by rw [hsq, hval]
    _ = ‖z‖ ^ (4 : ℕ) * ‖f z‖ := by ring
    _ ≤ A := hd

theorem radial_scaled_bound (Φ : ℝ → ℂ) {A H x : ℝ}
    (hdecay : ∀ y : ℝ, 0 ≤ y → y ^ (2 : ℕ) * ‖Φ y‖ ≤ A)
    (hH : 0 < H) (hx : 0 < x) :
    ‖Φ (x / H)‖ ≤ A * H ^ (2 : ℕ) / x ^ (2 : ℕ) := by
  apply (le_div_iff₀ (pow_pos hx 2)).mpr
  calc
    ‖Φ (x / H)‖ * x ^ (2 : ℕ) =
        ((x / H) ^ (2 : ℕ) * ‖Φ (x / H)‖) * H ^ (2 : ℕ) := by
      field_simp [hH.ne']
      <;> ring
    _ ≤ A * H ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (hdecay (x / H) (div_pos hx hH).le) (sq_nonneg H)

theorem radial_norm_summable (Φ : ℝ → ℂ) (H : ℝ) (hH : 0 < H)
    (hΦ : RadialSchwartz Φ) :
    Summable (fun k : O => ‖Φ (normElement k / H)‖) := by
  obtain ⟨A, _hA, hdecay⟩ := radial_quadratic_decay Φ hΦ
  have hbase : Summable (fun k : O => (normElement k ^ (2 : ℕ))⁻¹) :=
    summable_principal_pullback (fun a => inv_nonneg.mpr (sq_nonneg (normIdeal a)))
      summable_inverse_norm_sq
  have hnz : Summable (fun k : O => if k = 0 then (0 : ℝ) else ‖Φ (normElement k / H)‖) := by
    apply (hbase.mul_left (A * H ^ (2 : ℕ))).of_norm_bounded
    intro k
    by_cases hk : k = 0
    · simp [hk, normElement, principal, normIdeal]
    · have hkI : principal k ≠ ⊥ := by
        intro hz
        exact hk (Ideal.span_singleton_eq_bot.mp hz)
      have hx : 0 < normElement k := normIdeal_pos hkI
      simpa only [if_neg hk, norm_norm, div_eq_mul_inv] using
        radial_scaled_bound Φ hdecay hH hx
  have hz : Summable (fun k : O => if k = 0 then ‖Φ 0‖ else 0) :=
    (hasSum_ite_eq 0 ‖Φ 0‖).summable
  apply (hnz.add hz).congr
  intro k
  by_cases hk : k = 0
  · simp [hk, normElement, principal, normIdeal]
  · simp only [if_neg hk, add_zero]

end QRHShort.PoissonProof.CoprimeExpansion

namespace QRHShort.PoissonProof
open CoprimeExpansion

/-- Every residue character is bounded because its quotient is finite. -/
theorem radialCharacterSummability : RadialCharacterSummabilityStatement := by
  intro χ Φ H hH hΦ
  letI : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  letI : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let C : ℝ := ∑ x : O ⧸ χ.modulus, ‖χ.character x‖
  have hbound (k : O) : ‖χ.value k‖ ≤ C := by
    exact Finset.single_le_sum (fun x _ => norm_nonneg (χ.character x))
      (Finset.mem_univ (Ideal.Quotient.mk χ.modulus k))
  apply ((radial_norm_summable Φ H hH hΦ).mul_left C).of_norm_bounded
  intro k
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound k) (norm_nonneg _)

/-- The frozen coprime expansion with its actual generators and scales. -/
theorem coprimeExpansion : CoprimeExpansionStatement :=
  coprimeExpansion_of_radialCharacterSummability radialCharacterSummability

end QRHShort.PoissonProof
