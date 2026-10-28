import QRHShort.Energy
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Finite.Lattice

/-!
The concrete ideal sums have finite support for compactly supported weights.
In the third cyclotomic field, the six-unit theorem also makes every bounded
element-norm ball finite. Thus the original mean square is genuinely summable.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

theorem finite_normIdeal_le (B : ℝ) : {a : Ideal O | normIdeal a ≤ B}.Finite := by
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) ⌈B⌉₊).subset
  intro a ha
  exact Nat.cast_le.mp ((show (a.absNorm : ℝ) ≤ B from ha).trans (Nat.le_ceil B))

theorem finite_units : (Set.univ : Set Oˣ).Finite := by
  let η : Oˣ :=
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot.isUnit
      (by decide)).unit
  apply (List.finite_toSet [1, -1, η, -η, η ^ 2, -η ^ 2]).subset
  intro u _
  exact IsCyclotomicExtension.Rat.Three.Units.mem
    (IsCyclotomicExtension.zeta_spec 3 ℚ K) u

theorem finite_principal_fiber (a : Ideal O) : {z : O | principal z = a}.Finite := by
  let g : O := Submodule.IsPrincipal.generator a
  apply (finite_units.image (fun u : Oˣ => g * (u : O))).subset
  intro z hz
  have hg : principal g = a := Ideal.span_singleton_generator a
  have hassoc : Associated g z := Ideal.span_singleton_eq_span_singleton.mp (hg.trans hz.symm)
  obtain ⟨u, hu⟩ := hassoc
  exact ⟨u, Set.mem_univ u, hu⟩

theorem finite_normElement_le (B : ℝ) : {z : O | normElement z ≤ B}.Finite := by
  have hfinite := (finite_normIdeal_le B).biUnion
    (fun a _ => finite_principal_fiber a)
  apply hfinite.subset
  intro z hz
  exact Set.mem_iUnion₂.mpr ⟨principal z, hz, rfl⟩

theorem weighted_ideal_hasFiniteSupport (a : Ideal O → ℂ) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : Function.support W ⊆ Set.Icc I.lo I.hi)
    {D : ℝ} (hD : 0 < D) :
    Function.HasFiniteSupport (fun n : Ideal O => a n * W (normIdeal n / D)) := by
  apply (finite_normIdeal_le (I.hi * D)).subset
  intro n hn
  have hw : W (normIdeal n / D) ≠ 0 := by
    intro hw
    exact hn (by simp only [hw, mul_zero])
  have hupper := (hW hw).2
  exact (div_le_iff₀ hD).mp hupper

theorem originalSum_hasFiniteSupport (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D : ℝ} (hD : 0 < D) (u : O) :
    Function.HasFiniteSupport (fun n : Ideal O => if Outside c.S n then
      (mobius n : ℂ) * c.nu.onIdeal n * sexticSymbol n u * W (normIdeal n / D)
      else 0) := by
  have hfinite : Function.HasFiniteSupport (fun n : Ideal O =>
      (if Outside c.S n then (mobius n : ℂ) * c.nu.onIdeal n * sexticSymbol n u
        else 0) * W (normIdeal n / D)) :=
    weighted_ideal_hasFiniteSupport
      (fun n => if Outside c.S n then (mobius n : ℂ) * c.nu.onIdeal n * sexticSymbol n u
        else 0) I (W := W) hW.2 (D := D) hD
  simpa only [ite_mul, zero_mul] using hfinite

theorem originalSum_summable (c : ArithmeticContext) (I : SupportInterval)
    {W : ℝ → ℂ} (hW : SmoothSupported I W) {D : ℝ} (hD : 0 < D) (u : O) :
    Summable (fun n : Ideal O => if Outside c.S n then
      (mobius n : ℂ) * c.nu.onIdeal n * sexticSymbol n u * W (normIdeal n / D)
      else 0) :=
  summable_of_hasFiniteSupport (originalSum_hasFiniteSupport c I hW hD u)

theorem originalMeanSquare_hasFiniteSupport (c : ArithmeticContext) (W : ℝ → ℂ)
    (D H : ℝ) :
    Function.HasFiniteSupport (fun u : O =>
      if 0 < normElement u ∧ normElement u ≤ H then ‖originalSum c W D u‖ ^ 2 else 0) := by
  apply (finite_normElement_le H).subset
  intro u hu
  by_contra hnorm
  apply hu
  simp only [show ¬ (0 < normElement u ∧ normElement u ≤ H) from fun h => hnorm h.2,
    if_false]

theorem originalMeanSquare_summable (c : ArithmeticContext) (W : ℝ → ℂ) (D H : ℝ) :
    Summable (fun u : O =>
      if 0 < normElement u ∧ normElement u ≤ H then ‖originalSum c W D u‖ ^ 2 else 0) :=
  summable_of_hasFiniteSupport (originalMeanSquare_hasFiniteSupport c W D H)

end QRHShort
