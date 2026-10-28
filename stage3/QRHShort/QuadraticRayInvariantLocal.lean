import QRHShort.Arithmetic
import Mathlib.Tactic.LinearCombination

/-!
The local congruence carried by the first coordinate of `quadraticRayClass`.
This file imports only the arithmetic definitions and cached Mathlib tactics;
it does not import or assume any quadratic reciprocity statement.
-/

namespace QRHShort

/-- For the manuscript's primary convention, congruence modulo four is exactly
congruence modulo twelve.  In particular the fixed primary normalization loses
no congruence at the prime above three. -/
theorem quadraticRay_primary_modFour_eq_iff {x y : O}
    (hx : IsPrimary x) (hy : IsPrimary y) :
    Ideal.Quotient.mk (principal (4 : O)) x =
        Ideal.Quotient.mk (principal (4 : O)) y ↔
      (12 : O) ∣ x - y := by
  constructor
  · intro h
    have hx3 : (3 : O) ∣ x - 1 := Ideal.mem_span_singleton.mp hx
    have hy3 : (3 : O) ∣ y - 1 := Ideal.mem_span_singleton.mp hy
    have hthree : (3 : O) ∣ x - y := by
      convert dvd_sub hx3 hy3 using 1 <;> ring
    have hfour : (4 : O) ∣ x - y :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
    obtain ⟨u, hu⟩ := hthree
    obtain ⟨v, hv⟩ := hfour
    refine ⟨u - v, ?_⟩
    linear_combination 4 * hu - 3 * hv
  · rintro ⟨z, hz⟩
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨3 * z, ?_⟩
    rw [hz]
    ring

end QRHShort

#print axioms QRHShort.quadraticRay_primary_modFour_eq_iff
