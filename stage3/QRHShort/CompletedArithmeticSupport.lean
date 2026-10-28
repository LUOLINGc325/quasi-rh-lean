import QRHShort.Energy
import QRHShort.SquarefreeNumeratorPowers
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Finite row support and the generator API needed by the completed estimate. -/

noncomputable section
namespace QRHShort.CompletedAssembly
open Classical
open SquarefreeReflection.RayValuePrerequisites

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


theorem rowEnergy_summable (column : O → ℂ) (H : ℝ) :
    Summable (fun k : O => if 0 < normElement k ∧ normElement k ≤ H then
      ‖column k‖ ^ 2 else 0) := by
  apply summable_of_hasFiniteSupport
  apply (finite_normElement_le H).subset
  intro k hk
  by_contra hnorm
  apply hk
  simp only [show ¬ (0 < normElement k ∧ normElement k ≤ H) from fun h => hnorm h.2,
    if_false]

theorem exists_primary_generator_of_prime {p : Ideal O} (hp : Prime p)
    (hthree : ¬ p ∣ principal 3) :
    ∃ a : O, principal a = p ∧ IsPrimary a := by
  let a := idealGenerator p
  have hgen : principal a = p := Ideal.span_singleton_generator p
  have ha0 : a ≠ 0 := by
    intro ha
    apply hp.ne_zero
    rw [← hgen, ha]
    simp [principal]
  have haprime : Prime a := by
    apply (Ideal.span_singleton_prime ha0).mp
    change (principal a).IsPrime
    rw [hgen]
    exact Ideal.isPrime_of_prime hp
  have hnot : ¬ omega - 1 ∣ a := by
    intro hdiv
    have ha3 : a ∣ (3 : O) :=
      (omega_sub_one_prime.associated_of_dvd haprime hdiv).symm.dvd.trans
        omega_sub_one_dvd_three
    apply hthree
    apply Ideal.dvd_span_singleton.mpr
    rw [← hgen]
    exact Ideal.mem_span_singleton.mpr ha3
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd a hnot
  refine ⟨(u : O) * a, ?_, hu⟩
  calc
    principal ((u : O) * a) = principal a := Ideal.span_singleton_mul_left_unit u.isUnit a
    _ = p := hgen


end QRHShort.CompletedAssembly
