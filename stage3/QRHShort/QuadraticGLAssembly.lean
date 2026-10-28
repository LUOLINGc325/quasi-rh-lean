import QRHShort.QuadraticOAI
import QRHShort.QuadraticSieveSupport

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort

open OAI

/-- Exact row identification required to transfer the OAI finite matrix to the
concrete Hecke-character matrix.  The remaining arithmetic issue is exposed as
this proposition, so the transfer itself is axiom-free. -/
def QuadraticOAITransferRowStatement
    (h : QuadraticRayClassInvariantStatement) : Prop :=
  ∀ (a b : Ideal O),
    FamilyIdeal (principal 6) a → Squarefree a →
    FamilyIdeal (principal 6) b → Squarefree b →
    OAI.CanonicalQuadraticSieve.quadraticRow b
        (OAI.CompletedGauss.primaryGenerator a) =
      (quadraticCharacter b).onIdeal a

/-- The concrete GL family sieve follows from the finite OAI quadratic large
sieve once the exact row bridge is supplied. -/
theorem quadraticFamilySieve_of_oai
    (h : QuadraticRayClassInvariantStatement)
    (hrow : QuadraticOAITransferRowStatement h) :
    QuadraticFamilySieve (concreteQuadraticFamily h) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := oai_finite_family_quadratic_large_sieve ε hε
  refine ⟨C, le_of_lt hC, ?_⟩
  intro M N coeffs hM hN
  let F := concreteQuadraticFamily h
  let rows : Type := {a : Ideal O // a ∈ quadraticSieveIndices F M}
  let cols : Type := {b : Ideal O // b ∈ quadraticSieveIndices F N}
  let rf : rows → Ideal O := fun a => a.1
  let cf : cols → Ideal O := fun b => b.1
  have hri : Function.Injective rf := by
    intro x y hxy
    exact Subtype.ext hxy
  have hci : Function.Injective cf := by
    intro x y hxy
    exact Subtype.ext hxy
  have hrows (i : rows) :
      FamilyIdeal (principal 6) (rf i) ∧ Squarefree (rf i) ∧
        (Ideal.absNorm (rf i) : ℝ) ≤ M := by
    exact (mem_quadraticSieveIndices F M (rf i)).mp i.2
  have hcols (j : cols) :
      FamilyIdeal (principal 6) (cf j) ∧ Squarefree (cf j) ∧
        (Ideal.absNorm (cf j) : ℝ) ≤ N := by
    exact (mem_quadraticSieveIndices F N (cf j)).mp j.2
  have hfin := hbound M N hM hN rf cf hri hci hrows hcols
    (fun j => coeffs (cf j))
  have hrow (i : rows) (j : cols) :
      OAI.CanonicalQuadraticSieve.quadraticRow (cf j)
          (OAI.CompletedGauss.primaryGenerator (rf i)) =
        (quadraticCharacter (cf j)).onIdeal (rf i) :=
    hrow (rf i) (cf j) (hrows i).1 (hrows i).2.1 (hcols j).1 (hcols j).2.1
  have hfin' :
      (∑ i : rows, ‖∑ j : cols, coeffs (cf j) *
        (quadraticCharacter (cf j)).onIdeal (rf i)‖ ^ 2) ≤
      C * (M * N) ^ ε * (M + N) *
        ∑ j : cols, ‖coeffs (cf j)‖ ^ 2 := by
    convert hfin using 1
    have hsum (i : rows) :
        (∑ j : cols, coeffs (cf j) *
          (quadraticCharacter (cf j)).onIdeal (rf i)) =
        (∑ j : cols,
          OAI.CanonicalQuadraticSieve.quadraticRow (cf j)
            (OAI.CompletedGauss.primaryGenerator (rf i)) * coeffs (cf j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hrow i j]
      ring
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsum]
  have hsumNc (f : Ideal O → ℂ) :
      (∑ n ∈ quadraticSieveIndices F N, f n) =
        ∑ j : cols, f (cf j) := by
    apply Finset.sum_subtype
    intro x
    rfl
  have hsumMr (f : Ideal O → ℝ) :
      (∑ n ∈ quadraticSieveIndices F M, f n) =
        ∑ i : rows, f (rf i) := by
    apply Finset.sum_subtype
    intro x
    rfl
  have hsumNr (f : Ideal O → ℝ) :
      (∑ n ∈ quadraticSieveIndices F N, f n) =
        ∑ j : cols, f (cf j) := by
    apply Finset.sum_subtype
    intro x
    rfl
  have hinner (a : Ideal O) :
      (∑' b : Ideal O, if FamilyIdeal F.modulus b ∧ Squarefree b ∧ normIdeal b ≤ N then
        coeffs b * (F.character b).onIdeal a else 0) =
      ∑ j : cols, coeffs (cf j) * (quadraticCharacter (cf j)).onIdeal a := by
    rw [quadraticSieve_tsum F N]
    simpa [F, concreteQuadraticFamily] using
      (hsumNc (fun n => coeffs n * (F.character n).onIdeal a))
  have houter :
      (∑' a : Ideal O, if FamilyIdeal F.modulus a ∧ Squarefree a ∧ normIdeal a ≤ M then
        ‖∑' b : Ideal O, if FamilyIdeal F.modulus b ∧ Squarefree b ∧ normIdeal b ≤ N then
          coeffs b * (F.character b).onIdeal a else 0‖ ^ 2 else 0) =
      ∑ i : rows, ‖∑ j : cols, coeffs (cf j) *
        (quadraticCharacter (cf j)).onIdeal (rf i)‖ ^ 2 := by
    rw [quadraticSieve_tsum F M]
    have htmp := hsumMr (fun n => ‖∑' b : Ideal O,
      if FamilyIdeal F.modulus b ∧ Squarefree b ∧ normIdeal b ≤ N then
        coeffs b * (F.character b).onIdeal n else 0‖ ^ 2)
    calc
      _ = ∑ i : rows, ‖∑' b : Ideal O,
          if FamilyIdeal F.modulus b ∧ Squarefree b ∧ normIdeal b ≤ N then
            coeffs b * (F.character b).onIdeal (rf i) else 0‖ ^ 2 := by
        exact htmp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hinner (rf i)]
  rw [show concreteQuadraticFamily h = F by rfl, houter]
  calc
    _ ≤ C * (M * N) ^ ε * (M + N) *
        ∑ j : cols, ‖coeffs (cf j)‖ ^ 2 := hfin'
    _ = C * (M * N) ^ ε * (M + N) *
        (∑' b : Ideal O, if FamilyIdeal F.modulus b ∧ Squarefree b ∧ normIdeal b ≤ N
          then ‖coeffs b‖ ^ 2 else 0) := by
      rw [quadraticSieve_tsum F N]
      have htmp := hsumNr (fun n => ‖coeffs n‖ ^ 2)
      exact congrArg (fun t : ℝ => C * (M * N) ^ ε * (M + N) * t) htmp.symm

/- The concrete row bridge is now supplied by `QuadraticOAI`, so the
   Goldmakher--Louvel family sieve follows without the external sieve axiom. -/
theorem concreteQuadraticFamily_sieve_of_oai
    (h : QuadraticRayClassInvariantStatement) :
    QuadraticFamilySieve (concreteQuadraticFamily h) :=
  quadraticFamilySieve_of_oai h (fun a b ha hsa hb hsb =>
    quadratic_oai_transfer_row a b ha hb hsb)

/-- The concrete quadratic family sieve with the arithmetic input discharged. -/
theorem concreteQuadraticFamily_sieve_closed :
    QuadraticFamilySieve
      (concreteQuadraticFamily
        (quadraticRayClassInvariant_of_primeRayReciprocity
          quadraticPrimeRayReciprocity)) := by
  let h := quadraticRayClassInvariant_of_primeRayReciprocity
    quadraticPrimeRayReciprocity
  exact concreteQuadraticFamily_sieve_of_oai h

end QRHShort
