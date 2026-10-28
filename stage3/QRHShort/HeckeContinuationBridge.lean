import QRHShort.HeckeContinuationSpec
import QRHShort.HeckeMultiplicative
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import OAI.NumberTheory.DirichletL.Hecke.Euler
import OAI.NumberTheory.DirichletL.Hecke.Origin

noncomputable section
open scoped BigOperators Classical

namespace QRHShort

namespace HeckeContinuationBridge

open OAI
open OAI.SevenEighths
open OAI.SevenEighths.HeckeFamily

/-- The OAI finite-period character associated to a QRH character. -/
def oaiCharacter (χ : QRHShort.HeckeCharacter) : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue χ.modulus χ.modulus_ne_bot χ.residue χ.unit_trivial

lemma oaiCharacter_modulus (χ : QRHShort.HeckeCharacter) :
    (oaiCharacter χ).modulus = χ.modulus := rfl

lemma oai_idealCoeff_eq_onIdeal (χ : QRHShort.HeckeCharacter) (I : Ideal QRHShort.O) :
    HeckeFamily.idealCoeff (oaiCharacter χ) I = χ.onIdeal I := by
  by_cases hI : I = ⊥
  · subst I
    rw [HeckeCharacter.onIdeal_bot]
    simp [HeckeFamily.idealCoeff]
  · unfold HeckeFamily.idealCoeff
    change IdealCharacter.ofResidue χ.modulus χ.residue χ.unit_trivial I = _
    rw [IdealCharacter.ofResidue_of_generator χ.modulus χ.residue χ.unit_trivial hI
      (Ideal.span_singleton_generator I)]
    simp [HeckeCharacter.onIdeal, HeckeCharacter.onElement, idealGenerator, hI]

lemma oai_idealTerm_eq_heckeSeriesTerm (χ : QRHShort.HeckeCharacter) (s : ℂ)
    (I : Ideal QRHShort.O) :
    HeckeFamily.idealTerm (oaiCharacter χ) s I = heckeSeriesTerm χ s I := by
  unfold HeckeFamily.idealTerm heckeSeriesTerm
  rw [oai_idealCoeff_eq_onIdeal]
  by_cases hI : I = ⊥ <;> simp [hI, normIdeal, HeckeCharacter.onIdeal]

/-- OAI's continued lattice supplies the QRH analytic continuation statement. -/
theorem hecke_continuation_from_oai (χ : QRHShort.HeckeCharacter) :
    ∃ L : ℂ → ℂ, HeckeContinuationSpec χ L := by
  let η : HeckeFamily.Character := oaiCharacter χ
  refine ⟨HeckeOrigin.continued η, ?_, ?_⟩
  · intro s hs
    have hsum : Summable (fun I : Ideal HeckeFamily.O =>
        HeckeFamily.idealTerm η s I) := by
      simpa only [HeckeFamily.idealTerm_eq_weighted] using
        (IdealEuler.weighted_summable (HeckeFamily.idealCoeff η)
          (HeckeFamily.idealCoeff_norm_le_one η) s hs)
    have hL : HeckeFamily.LFunction η s =
        ∑' I : Ideal HeckeFamily.O, HeckeFamily.idealTerm η s I :=
      HeckeFamily.LFunction_eq_ideal_tsum η hs
    have hsumL : HasSum (fun I : Ideal HeckeFamily.O =>
        HeckeFamily.idealTerm η s I) (HeckeFamily.LFunction η s) := by
      rw [hL]
      exact hsum.hasSum
    have hs₀ : s ≠ 0 := by
      intro h
      subst s
      norm_num at hs
    have hs₁ : s ≠ 1 := by
      intro h
      subst s
      norm_num at hs
    rw [HeckeOrigin.continued_eq η hs₀ hs₁]
    exact hsumL.congr_fun (fun I => (oai_idealTerm_eq_heckeSeriesTerm χ s I).symm)
  · by_cases hχ : χ.residue = 1
    · have hU : {s : ℂ | s ≠ 1 ∨ χ.residue ≠ 1} = {s : ℂ | s ≠ 1} := by
        ext s
        simp [hχ]
      rw [hU]
      apply (Complex.analyticOnNhd_iff_differentiableOn isOpen_compl_singleton).mpr
      intro s hs
      exact (HeckeOrigin.continued_differentiableAt η (Or.inl hs)).differentiableWithinAt
    · have hU : {s : ℂ | s ≠ 1 ∨ χ.residue ≠ 1} = Set.univ := by
        ext s
        simp [hχ]
      rw [hU]
      apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
      intro s
      exact HeckeOrigin.continued_differentiableAt η (Or.inr hχ)

end HeckeContinuationBridge

end QRHShort
