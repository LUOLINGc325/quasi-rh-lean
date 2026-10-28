import QRHShort.FirstTransferGeneratorNormalization
import Mathlib.Algebra.Squarefree.Basic

/-!
The actual ideal-gcd decomposition of squarefree outside pairs.  Ideals have
trivial units, so the common factor is the literal normalized ideal gcd, and
the two remaining factors are unique rather than merely associated.
-/

noncomputable section
open Classical

namespace QRHShort

def firstTransferGcdPairAdmissible (c : ArithmeticContext) (p : Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S p.1 ∧ SquarefreeOutside c.S p.2

def firstTransferGcdTripleAdmissible (c : ArithmeticContext)
    (t : Ideal O × Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧ SquarefreeOutside c.S t.2.2 ∧
    IsRelPrime t.1 t.2.1 ∧ IsRelPrime t.1 t.2.2 ∧ IsRelPrime t.2.1 t.2.2

abbrev FirstTransferGcdPairs (c : ArithmeticContext) :=
  {p : Ideal O × Ideal O // firstTransferGcdPairAdmissible c p}

abbrev FirstTransferGcdTriples (c : ArithmeticContext) :=
  {t : Ideal O × Ideal O × Ideal O // firstTransferGcdTripleAdmissible c t}

/-- Reconstruction multiplies both residual ideals by their common factor. -/
def firstTransferGcdReconstruct (c : ArithmeticContext) :
    FirstTransferGcdTriples c → FirstTransferGcdPairs c := fun t =>
  ⟨(t.1.1 * t.1.2.1, t.1.1 * t.1.2.2),
    ⟨(first_transfer_outside_mul_iff c _ _).mpr ⟨t.2.1.1, t.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨t.2.2.2.2.1, t.2.1.2, t.2.2.1.2⟩⟩,
    ⟨(first_transfer_outside_mul_iff c _ _).mpr ⟨t.2.1.1, t.2.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨t.2.2.2.2.2.1, t.2.1.2, t.2.2.2.1.2⟩⟩⟩

@[simp] theorem firstTransferGcdReconstruct_val (c : ArithmeticContext)
    (t : FirstTransferGcdTriples c) :
    (firstTransferGcdReconstruct c t).1 = (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2) := rfl

/-- The reconstructed pair has exactly C as its actual ideal gcd. -/
theorem firstTransferGcdReconstruct_gcd (c : ArithmeticContext) (t : FirstTransferGcdTriples c) :
    gcd (firstTransferGcdReconstruct c t).1.1 (firstTransferGcdReconstruct c t).1.2 = t.1.1 := by
  have hunit : gcd t.1.2.1 t.1.2.2 = 1 :=
    (gcd_isUnit_iff_isRelPrime.mpr t.2.2.2.2.2.2).eq_one
  change gcd (t.1.1 * t.1.2.1) (t.1.1 * t.1.2.2) = t.1.1
  rw [gcd_mul_left, normalize_eq, hunit, mul_one]

theorem firstTransferGcdReconstruct_injective (c : ArithmeticContext) :
    Function.Injective (firstTransferGcdReconstruct c) := by
  intro t s h
  have hC : t.1.1 = s.1.1 := by
    calc
      t.1.1 = gcd (firstTransferGcdReconstruct c t).1.1
          (firstTransferGcdReconstruct c t).1.2 := (firstTransferGcdReconstruct_gcd c t).symm
      _ = gcd (firstTransferGcdReconstruct c s).1.1
          (firstTransferGcdReconstruct c s).1.2 :=
        congrArg (fun p : FirstTransferGcdPairs c => gcd p.1.1 p.1.2) h
      _ = s.1.1 := firstTransferGcdReconstruct_gcd c s
  have hpair : (t.1.1 * t.1.2.1, t.1.1 * t.1.2.2) =
      (s.1.1 * s.1.2.1, s.1.1 * s.1.2.2) := congrArg Subtype.val h
  apply Subtype.ext
  apply Prod.ext hC
  apply Prod.ext
  · apply mul_left_cancel₀ t.2.1.1.1
    simpa only [hC] using congrArg Prod.fst hpair
  · apply mul_left_cancel₀ t.2.1.1.1
    simpa only [hC] using congrArg Prod.snd hpair

/-- Extraction starts with Mathlib's literal gcd factorization; squarefreeness
forces each residual factor to be coprime to the common factor as well. -/
theorem firstTransferGcdReconstruct_surjective (c : ArithmeticContext) :
    Function.Surjective (firstTransferGcdReconstruct c) := by
  intro p
  obtain ⟨u, v, hu, hv, huv⟩ := extract_gcd p.1.1 p.1.2
  let C := gcd p.1.1 p.1.2
  have hC : SquarefreeOutside c.S C :=
    ⟨first_transfer_outside_of_dvd c p.2.1.1 (gcd_dvd_left _ _),
      p.2.1.2.squarefree_of_dvd (gcd_dvd_left _ _)⟩
  have hudiv : u ∣ p.1.1 := ⟨C, hu.trans (mul_comm _ _)⟩
  have hvdiv : v ∣ p.1.2 := ⟨C, hv.trans (mul_comm _ _)⟩
  have huout : SquarefreeOutside c.S u :=
    ⟨first_transfer_outside_of_dvd c p.2.1.1 hudiv, p.2.1.2.squarefree_of_dvd hudiv⟩
  have hvout : SquarefreeOutside c.S v :=
    ⟨first_transfer_outside_of_dvd c p.2.2.1 hvdiv, p.2.2.2.squarefree_of_dvd hvdiv⟩
  have hCu : IsRelPrime C u := IsRelPrime.of_squarefree_mul (hu ▸ p.2.1.2)
  have hCv : IsRelPrime C v := IsRelPrime.of_squarefree_mul (hv ▸ p.2.2.2)
  have huv' : IsRelPrime u v := gcd_isUnit_iff_isRelPrime.mp huv
  refine ⟨⟨(C, u, v), hC, huout, hvout, hCu, hCv, huv'⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hu.symm hv.symm

theorem firstTransferGcdReconstruct_bijective (c : ArithmeticContext) :
    Function.Bijective (firstTransferGcdReconstruct c) :=
  ⟨firstTransferGcdReconstruct_injective c, firstTransferGcdReconstruct_surjective c⟩

/-- The forward map reconstructs the pair; the inverse is its unique gcd triple. -/
def firstTransferGcdEquiv (c : ArithmeticContext) :
    FirstTransferGcdTriples c ≃ FirstTransferGcdPairs c :=
  Equiv.ofBijective (firstTransferGcdReconstruct c) (firstTransferGcdReconstruct_bijective c)

@[simp] theorem firstTransferGcdEquiv_apply (c : ArithmeticContext) (t : FirstTransferGcdTriples c) :
    firstTransferGcdEquiv c t = firstTransferGcdReconstruct c t := rfl

theorem firstTransferGcdEquiv_symm_gcd (c : ArithmeticContext) (p : FirstTransferGcdPairs c) :
    ((firstTransferGcdEquiv c).symm p).1.1 = gcd p.1.1 p.1.2 := by
  have h := firstTransferGcdReconstruct_gcd c ((firstTransferGcdEquiv c).symm p)
  change gcd (firstTransferGcdEquiv c ((firstTransferGcdEquiv c).symm p)).1.1
    (firstTransferGcdEquiv c ((firstTransferGcdEquiv c).symm p)).1.2 = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem firstTransferGcdEquiv_symm_reconstruct (c : ArithmeticContext) (p : FirstTransferGcdPairs c) :
    let t := (firstTransferGcdEquiv c).symm p
    p.1.1 = t.1.1 * t.1.2.1 ∧ p.1.2 = t.1.1 * t.1.2.2 := by
  have h := congrArg Subtype.val ((firstTransferGcdEquiv c).apply_symm_apply p)
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

end QRHShort
