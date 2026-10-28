import QRHShort.FirstTransferGcd

/-!
Replacing a selected common divisor t of a squarefree outside pair by the
unique factors a=t*x and b=t*y.  The residual ideals x and y need not be
coprime to each other; only their coprimality to t is present.
-/

noncomputable section
open Classical

namespace QRHShort

def firstTransferMobiusDivisorAdmissible (c : ArithmeticContext)
    (q : (Ideal O × Ideal O) × Ideal O) : Prop :=
  firstTransferGcdPairAdmissible c q.1 ∧ q.2 ∣ q.1.1 ∧ q.2 ∣ q.1.2

def firstTransferMobiusTripleAdmissible (c : ArithmeticContext)
    (t : Ideal O × Ideal O × Ideal O) : Prop :=
  SquarefreeOutside c.S t.1 ∧ SquarefreeOutside c.S t.2.1 ∧ SquarefreeOutside c.S t.2.2 ∧
    IsRelPrime t.2.1 t.1 ∧ IsRelPrime t.2.2 t.1

abbrev FirstTransferMobiusDivisorIndices (c : ArithmeticContext) :=
  {q : (Ideal O × Ideal O) × Ideal O // firstTransferMobiusDivisorAdmissible c q}

abbrev FirstTransferMobiusTriples (c : ArithmeticContext) :=
  {t : Ideal O × Ideal O × Ideal O // firstTransferMobiusTripleAdmissible c t}

def firstTransferMobiusImage (t : Ideal O × Ideal O × Ideal O) :
    (Ideal O × Ideal O) × Ideal O := ((t.1 * t.2.1, t.1 * t.2.2), t.1)

theorem first_transfer_mobius_image_admissible (c : ArithmeticContext)
    {t : Ideal O × Ideal O × Ideal O} (ht : firstTransferMobiusTripleAdmissible c t) :
    firstTransferMobiusDivisorAdmissible c (firstTransferMobiusImage t) := by
  refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _, dvd_mul_right _ _⟩
  · exact ⟨(first_transfer_outside_mul_iff c _ _).mpr ⟨ht.1.1, ht.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨ht.2.2.2.1.symm, ht.1.2, ht.2.1.2⟩⟩
  · exact ⟨(first_transfer_outside_mul_iff c _ _).mpr ⟨ht.1.1, ht.2.2.1.1⟩,
      squarefree_mul_iff.mpr ⟨ht.2.2.2.2.symm, ht.1.2, ht.2.2.1.2⟩⟩

theorem first_transfer_mobius_image_injOn (c : ArithmeticContext) :
    Set.InjOn firstTransferMobiusImage {t | firstTransferMobiusTripleAdmissible c t} := by
  intro t ht s _hs h
  have ht0 : t.1 ≠ 0 := ht.1.1.1
  have hts : t.1 = s.1 := congrArg Prod.snd h
  have hp : (t.1 * t.2.1, t.1 * t.2.2) = (s.1 * s.2.1, s.1 * s.2.2) :=
    congrArg Prod.fst h
  apply Prod.ext hts
  apply Prod.ext
  · apply mul_left_cancel₀ ht0
    simpa only [hts] using congrArg Prod.fst hp
  · apply mul_left_cancel₀ ht0
    simpa only [hts] using congrArg Prod.snd hp

def firstTransferMobiusReconstruct (c : ArithmeticContext) :
    FirstTransferMobiusTriples c → FirstTransferMobiusDivisorIndices c := fun t =>
  ⟨firstTransferMobiusImage t.1, first_transfer_mobius_image_admissible c t.2⟩

theorem firstTransferMobiusReconstruct_bijective (c : ArithmeticContext) :
    Function.Bijective (firstTransferMobiusReconstruct c) := by
  constructor
  · intro t s h
    apply Subtype.ext
    exact first_transfer_mobius_image_injOn c t.2 s.2 (congrArg Subtype.val h)
  · intro q
    obtain ⟨x, hx⟩ := q.2.2.1
    obtain ⟨y, hy⟩ := q.2.2.2
    have ht : SquarefreeOutside c.S q.1.2 :=
      ⟨first_transfer_outside_of_dvd c q.2.1.1.1 q.2.2.1,
        q.2.1.1.2.squarefree_of_dvd q.2.2.1⟩
    have hxdvd : x ∣ q.1.1.1 := ⟨q.1.2, hx.trans (mul_comm _ _)⟩
    have hydvd : y ∣ q.1.1.2 := ⟨q.1.2, hy.trans (mul_comm _ _)⟩
    have hxout : SquarefreeOutside c.S x :=
      ⟨first_transfer_outside_of_dvd c q.2.1.1.1 hxdvd,
        q.2.1.1.2.squarefree_of_dvd hxdvd⟩
    have hyout : SquarefreeOutside c.S y :=
      ⟨first_transfer_outside_of_dvd c q.2.1.2.1 hydvd,
        q.2.1.2.2.squarefree_of_dvd hydvd⟩
    have hxt : IsRelPrime x q.1.2 := (IsRelPrime.of_squarefree_mul (hx ▸ q.2.1.1.2)).symm
    have hyt : IsRelPrime y q.1.2 := (IsRelPrime.of_squarefree_mul (hy ▸ q.2.1.2.2)).symm
    refine ⟨⟨(q.1.2, x, y), ht, hxout, hyout, hxt, hyt⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext (Prod.ext hx.symm hy.symm) rfl

def firstTransferMobiusEquiv (c : ArithmeticContext) :
    FirstTransferMobiusTriples c ≃ FirstTransferMobiusDivisorIndices c :=
  Equiv.ofBijective (firstTransferMobiusReconstruct c) (firstTransferMobiusReconstruct_bijective c)

@[simp] theorem firstTransferMobiusEquiv_apply (c : ArithmeticContext)
    (t : FirstTransferMobiusTriples c) :
    (firstTransferMobiusEquiv c t).1 = firstTransferMobiusImage t.1 := rfl

theorem firstTransferMobiusEquiv_symm_reconstruct (c : ArithmeticContext)
    (q : FirstTransferMobiusDivisorIndices c) :
    let t := (firstTransferMobiusEquiv c).symm q
    t.1.1 = q.1.2 ∧ q.1.1.1 = t.1.1 * t.1.2.1 ∧ q.1.1.2 = t.1.1 * t.1.2.2 := by
  have h := congrArg Subtype.val ((firstTransferMobiusEquiv c).apply_symm_apply q)
  exact ⟨congrArg Prod.snd h, (congrArg (fun q : (Ideal O × Ideal O) × Ideal O => q.1.1) h).symm,
    (congrArg (fun q : (Ideal O × Ideal O) × Ideal O => q.1.2) h).symm⟩

end QRHShort
